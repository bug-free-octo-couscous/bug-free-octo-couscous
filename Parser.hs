module Parser
    ( parseTerm
    , parseInterval
    , ParseError
    ) where

import CubicalLambda

import Data.Char (isAlphaNum, isAlpha, isDigit, isSpace)
import Data.List (isPrefixOf, stripPrefix)
import Control.Monad (void)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type ParseError = String

-- | Parsing environment: list of in-scope name hints, outermost-first.
--   Position 0 in the list = the most-recently-bound name (de Bruijn 0).
type Env = [Name]

--------------------------------------------------------------------------------
-- Parser type
--------------------------------------------------------------------------------

newtype Parser a = Parser { runParser :: String -> Either ParseError (a, String) }

instance Functor Parser where
    fmap f (Parser p) = Parser $ \s -> fmap (\(a, r) -> (f a, r)) (p s)

instance Applicative Parser where
    pure a = Parser $ \s -> Right (a, s)
    Parser pf <*> Parser pa = Parser $ \s -> do
        (f, s')  <- pf s
        (a, s'') <- pa s'
        return (f a, s'')

instance Monad Parser where
    return = pure
    Parser pa >>= f = Parser $ \s -> do
        (a, s') <- pa s
        runParser (f a) s'

--------------------------------------------------------------------------------
-- Primitive combinators
--------------------------------------------------------------------------------

failP :: ParseError -> Parser a
failP msg = Parser $ \_ -> Left msg

try :: Parser a -> Parser (Maybe a)
try (Parser p) = Parser $ \s ->
    case p s of
        Left _  -> Right (Nothing, s)
        Right (a, s') -> Right (Just a, s')

-- | Try the first parser; fall back to the second on failure.
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser $ \s ->
    case p s of
        Right r -> Right r
        Left _  -> q s
infixl 3 <|>

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser $ \s -> case s of
    (c:cs) | f c -> Right (c, cs)
    _            -> Left "unexpected character"

char :: Char -> Parser Char
char c = satisfy (== c) `orElse` ("expected '" ++ [c] ++ "'")

orElse :: Parser a -> ParseError -> Parser a
orElse (Parser p) msg = Parser $ \s ->
    case p s of
        Left _  -> Left msg
        Right r -> Right r

string :: String -> Parser String
string str = Parser $ \s ->
    case stripPrefix str s of
        Just rest -> Right (str, rest)
        Nothing   -> Left ("expected \"" ++ str ++ "\"")

-- | Consume zero or more spaces/tabs/newlines.
spaces :: Parser ()
spaces = Parser $ \s -> Right ((), dropWhile isSpace s)

lexeme :: Parser a -> Parser a
lexeme p = spaces *> p

-- | Try to parse a keyword; succeed only if not followed by alphanumeric/'_'.
keyword :: String -> Parser ()
keyword kw = lexeme $ Parser $ \s ->
    case stripPrefix kw s of
        Just rest@(c:_) | isAlphaNum c || c == '_' -> Left ("expected keyword " ++ kw)
        Just rest -> Right ((), rest)
        Nothing   -> Left ("expected keyword " ++ kw)

-- | Parse a Unicode prefix exactly (useful for multi-byte symbols).
symbol :: String -> Parser ()
symbol sym = void (lexeme (string sym))

-- | A name: starts with a letter or '_', continues with alnum or '_' or '\''.
name :: Parser Name
name = lexeme $ Parser $ \s ->
    case dropWhile isSpace s of
        [] -> Left "expected name"
        (c:cs)
            | isAlpha c || c == '_' ->
                let (rest, remaining) = span (\x -> isAlphaNum x || x == '_' || x == '\'') cs
                in Right (c:rest, remaining)
            | otherwise -> Left "expected name"

-- | Natural number (used for universe levels and de Bruijn indices in output,
--   but also for numeric suffixes on interval variables like i0, i2).
natural :: Parser Int
natural = lexeme $ Parser $ \s ->
    case dropWhile isSpace s of
        [] -> Left "expected number"
        cs -> case span isDigit cs of
            ("", _) -> Left "expected number"
            (ds, rest) -> Right (read ds, rest)

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

brackets :: Parser a -> Parser a
brackets p = symbol "[" *> p <* symbol "]"

angles :: Parser a -> Parser a
angles p = symbol "\8992" *> p <* symbol "\8993"
-- ⟨ = \8992, ⟩ = \8993

--------------------------------------------------------------------------------
-- Interval Parser
--------------------------------------------------------------------------------

-- | Parse an interval expression.
--   Grammar (associative, left-to-right):
--     iexpr  ::= ijoin
--     ijoin  ::= imeet ('∨' imeet)*
--     imeet  ::= ineg  ('∧' ineg)*
--     ineg   ::= '¬' ineg | iatom
--     iatom  ::= '0' | '1' | 'i' NAT | '(' iexpr ')'
parseInterval :: String -> Either ParseError I
parseInterval s = case runParser (spaces *> iExpr) s of
    Left err      -> Left err
    Right (i, "") -> Right i
    Right (_, r)  -> Left ("leftover input: " ++ r)

iExpr :: Parser I
iExpr = iJoin

iJoin :: Parser I
iJoin = do
    l <- iMeet
    rest l
  where
    rest acc = do
        mj <- try (symbol "\8744")   -- ∨
        case mj of
            Nothing -> return acc
            Just () -> do
                r <- iMeet
                rest (Join acc r)

iMeet :: Parser I
iMeet = do
    l <- iNeg
    rest l
  where
    rest acc = do
        mj <- try (symbol "\8743")   -- ∧
        case mj of
            Nothing -> return acc
            Just () -> do
                r <- iNeg
                rest (Meet acc r)

iNeg :: Parser I
iNeg =
    (symbol "\172" *> fmap Neg iNeg)   -- ¬ = \172
    <|> iAtom

iAtom :: Parser I
iAtom =
    (symbol "0" *> return I0)
    <|> (symbol "1" *> return I1)
    <|> iVar
    <|> parens iExpr
  where
    -- Match  i<nat>  as IVar n
    iVar = lexeme $ Parser $ \s ->
        case dropWhile isSpace s of
            ('i':rest) -> case span isDigit rest of
                (ds@(_:_), remaining) -> Right (IVar (read ds), remaining)
                _                     -> Left "expected interval variable i<n>"
            _ -> Left "expected interval variable"

--------------------------------------------------------------------------------
-- Term Parser
--------------------------------------------------------------------------------

-- | Parse a closed term (no free names).
parseTerm :: String -> Either ParseError Term
parseTerm s = case runParser (spaces *> termWith []) s of
    Left err      -> Left err
    Right (t, "") -> Right t
    Right (_, r)  -> Left ("leftover input: " ++ r)

-- | Main entry: parse a term given a name environment.
termWith :: Env -> Parser Term
termWith env = lamTerm env <|> piTerm env <|> appTerm env

-- | λx. body  or  ⟨x⟩ body
lamTerm :: Env -> Parser Term
lamTerm env =
    parseLam env <|> parsePLam env

parseLam :: Env -> Parser Term
parseLam env = do
    symbol "\955"   -- λ
    x <- name
    symbol "."
    body <- termWith (x : env)
    return (TAbs x body)

parsePLam :: Env -> Parser Term
parsePLam env = do
    x <- angles name
    body <- termWith (x : env)
    return (PLam x body)

-- | Π(x:A). B
piTerm :: Env -> Parser Term
piTerm env = do
    symbol "\928"   -- Π
    symbol "("
    x <- name
    symbol ":"
    aTy <- termWith env
    symbol ")"
    symbol "."
    bTy <- termWith (x : env)
    return (TPi x aTy bTy)

-- | Function application and path application, left-associative.
--   Also handles  t @ r  for path application.
appTerm :: Env -> Parser Term
appTerm env = do
    f <- atom env
    rest f
  where
    rest acc = do
        -- try path application  acc @ r
        mpapp <- try (symbol "@")
        case mpapp of
            Just () -> do
                r <- atom env
                rest (PApp acc r)
            Nothing -> do
                -- try normal application: another atom follows
                marg <- try (atom env)
                case marg of
                    Nothing  -> return acc
                    Just arg -> rest (TApp acc arg)

-- | Atomic terms (no leading lambda/Pi).
atom :: Env -> Parser Term
atom env =
    parseUniv
    <|> parseIntervalTy
    <|> parsePathTy env
    <|> parseHComp env
    <|> parseGlue env
    <|> parseGlueElem env
    <|> parseUnglue env
    <|> parseInterval_ env
    <|> parseVar env
    <|> parens (termWith env)

-- | U<n>
parseUniv :: Parser Term
parseUniv = lexeme $ Parser $ \s ->
    case dropWhile isSpace s of
        ('U':rest) -> case span isDigit rest of
            (ds@(_:_), remaining) -> Right (TUniv (read ds), remaining)
            _                     -> Left "expected universe U<n>"
        _ -> Left "expected universe"

-- | 𝕀  (the interval pseudo-type)
parseIntervalTy :: Parser Term
parseIntervalTy = symbol "\120128" *> return TIntervalTy  -- 𝕀 = \120128

-- | Path A u v
parsePathTy :: Env -> Parser Term
parsePathTy env = do
    keyword "Path"
    a <- atom env
    u <- atom env
    v <- atom env
    return (TPath a u v)

-- | hcomp A [phi] (u) u0
parseHComp :: Env -> Parser Term
parseHComp env = do
    keyword "hcomp"
    a   <- atom env
    phi <- brackets (termWith env)
    u   <- parens (termWith env)
    u0  <- atom env
    return (THComp a phi u u0)

-- | Glue A [phi] (te)
parseGlue :: Env -> Parser Term
parseGlue env = do
    keyword "Glue"
    a   <- atom env
    phi <- brackets (termWith env)
    te  <- parens (termWith env)
    return (TGlue a phi te)

-- | glue [phi] (t) a
parseGlueElem :: Env -> Parser Term
parseGlueElem env = do
    keyword "glue"
    phi <- brackets (termWith env)
    t   <- parens (termWith env)
    a   <- atom env
    return (TGlueElem phi t a)

-- | unglue [phi] (te) g
parseUnglue :: Env -> Parser Term
parseUnglue env = do
    keyword "unglue"
    phi <- brackets (termWith env)
    te  <- parens (termWith env)
    g   <- atom env
    return (TUnglue phi te g)

-- | An interval literal inline in a term position: 0, 1, i<n>.
--   These become TInterval nodes.
parseInterval_ :: Env -> Parser Term
parseInterval_ _env =
    fmap TInterval $ lexeme $
        (char '0' *> return I0)
        <|> (char '1' *> return I1)
        <|> iVarOnly
  where
    iVarOnly = Parser $ \s ->
        case dropWhile isSpace s of
            ('i':rest) -> case span isDigit rest of
                (ds@(_:_), remaining) -> Right (IVar (read ds), remaining)
                _                     -> Left "not an interval var"
            _ -> Left "not an interval"

-- | Variable: resolve a name against the environment to get a de Bruijn index.
parseVar :: Env -> Parser Term
parseVar env = do
    x <- name
    case lookup x (zip env [0..]) of
        Just i  -> return (TVar i)
        Nothing -> failP ("unbound variable: " ++ x)