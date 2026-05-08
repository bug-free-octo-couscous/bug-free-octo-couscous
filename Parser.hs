module Parser
    ( parseTerm
    , parseInterval
    , parseStatement
    , Statement(..)
    , ParseError
    ) where

import CubicalLambda

import Data.Char  (isAlphaNum, isAlpha, isDigit, isSpace)
import Data.List  (stripPrefix)
import Control.Monad (void)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type ParseError = String
type Env        = [Name]

--------------------------------------------------------------------------------
-- Parser monad
--------------------------------------------------------------------------------

newtype Parser a = Parser { runParser :: String -> Either ParseError (a, String) }

instance Functor Parser where
    fmap f (Parser p) = Parser $ \s -> case p s of
        Left err     -> Left err
        Right (a, r) -> Right (f a, r)

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
-- Primitives
--------------------------------------------------------------------------------

failP :: ParseError -> Parser a
failP msg = Parser $ \_ -> Left msg

try :: Parser a -> Parser (Maybe a)
try (Parser p) = Parser $ \s ->
    case p s of
        Left _        -> Right (Nothing, s)
        Right (a, s') -> Right (Just a, s')

(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser $ \s ->
    case p s of
        Right r -> Right r
        Left _  -> q s
infixl 3 <|>

spaces :: Parser ()
spaces = Parser $ \s -> Right ((), dropWhile isSpace s)

lexeme :: Parser a -> Parser a
lexeme p = spaces *> p

symbol :: String -> Parser ()
symbol sym = lexeme $ Parser $ \s ->
    case stripPrefix sym s of
        Just rest -> Right ((), rest)
        Nothing   -> Left ("expected " ++ show sym)

keyword :: String -> Parser ()
keyword kw = lexeme $ Parser $ \s ->
    case stripPrefix kw s of
        Nothing         -> Left ("expected keyword " ++ kw)
        Just (c:_) | isAlphaNum c || c == '_'
                        -> Left ("expected keyword " ++ kw)
        Just rest       -> Right ((), rest)

name :: Parser Name
name = lexeme $ Parser $ \s ->
    case s of
        (c:cs) | isAlpha c || c == '_' ->
            let (mid, rest) = span (\x -> isAlphaNum x || x == '_' || x == '\'') cs
            in  Right (c : mid, rest)
        _ -> Left "expected name"

parens :: Parser a -> Parser a
parens   p = symbol "(" *> p <* symbol ")"

brackets :: Parser a -> Parser a
brackets p = symbol "[" *> p <* symbol "]"

angles :: Parser a -> Parser a
angles p = symbol "{" *> p <* symbol "}"

--------------------------------------------------------------------------------
-- Interval expression parser
--------------------------------------------------------------------------------

parseInterval :: String -> Either ParseError I
parseInterval s =
    case runParser (spaces *> iExpr <* spaces) s of
        Left err      -> Left err
        Right (i, "") -> Right i
        Right (_, r)  -> Left ("leftover: " ++ r)

iExpr :: Parser I
iExpr = iJoin

iJoin :: Parser I
iJoin = do
    l <- iMeet
    go l
  where
    go acc = do
        mv <- try (symbol "or")
        case mv of
            Nothing -> return acc
            Just () -> iMeet >>= \r -> go (Join acc r)

iMeet :: Parser I
iMeet = do
    l <- iNeg
    go l
  where
    go acc = do
        mv <- try (symbol "and")
        case mv of
            Nothing -> return acc
            Just () -> iNeg >>= \r -> go (Meet acc r)

iNeg :: Parser I
iNeg = (symbol "not_" *> fmap Neg iNeg)
    <|> iAtom

iAtom :: Parser I
iAtom = (symbol "0" *> return I0)
     <|> (symbol "1" *> return I1)
     <|> iVar
     <|> parens iExpr
  where
    iVar = lexeme $ Parser $ \s ->
        case s of
            ('i':rest) -> case span isDigit rest of
                (ds@(_:_), remaining) -> Right (IVar (read ds), remaining)
                _                     -> Left "expected i{n}"
            _ -> Left "expected interval variable"

--------------------------------------------------------------------------------
-- Term parser
-- All parsers take (GlobalEnv, Env) so globals are visible everywhere,
-- including inside lambda/Pi/path-abstraction bodies.
--------------------------------------------------------------------------------

parseTerm :: String -> Either ParseError Term
parseTerm s =
    case runParser (spaces *> twG [] [] <* spaces) s of
        Left err      -> Left err
        Right (t, "") -> Right t
        Right (_, r)  -> Left ("leftover: " ++ r)

-- | Full env = local names ++ global names (most-recent global = lowest index
--   after locals).  All recursive calls go through twG/awG so globals are
--   always visible.
twG :: GlobalEnv -> Env -> Parser Term
twG g env = lamG g env <|> plamG g env <|> piG g env <|> appG g env

lamG :: GlobalEnv -> Env -> Parser Term
lamG g env = do
    symbol "lambda_"
    x    <- name
    symbol "."
    body <- twG g (x : env)
    return (TAbs x body)

plamG :: GlobalEnv -> Env -> Parser Term
plamG g env = do
    x    <- angles name
    body <- twG g (x : env)
    return (PLam x body)

piG :: GlobalEnv -> Env -> Parser Term
piG g env = do
    symbol "PI"
    symbol "("
    x   <- name
    symbol ":"
    aTy <- twG g env
    symbol ")"
    symbol "."
    bTy <- twG g (x : env)
    return (TPi x aTy bTy)

appG :: GlobalEnv -> Env -> Parser Term
appG g env = do
    f <- awG g env
    go f
  where
    go acc = do
        mpat <- try (symbol "@")
        case mpat of
            Just () -> awG g env >>= \r -> go (PApp acc r)
            Nothing -> do
                marg <- try (awG g env)
                case marg of
                    Nothing  -> return acc
                    Just arg -> go (TApp acc arg)

-- | Atom parser — same two-level split, but globals threaded through.
awG :: GlobalEnv -> Env -> Parser Term
awG g env
     =  univP
    <|> intervalTyP
    <|> intervalLitP
    <|> hcompG    g env
    <|> glueTypeG g env
    <|> glueElemG g env
    <|> unglueG   g env
    <|> pathG     g env
    <|> equivG    g env
    <|> mkEquivG  g env
    <|> equivFwdG g env
    <|> uaG       g env
    <|> transportG g env
    <|> varG g env
    <|> parens (twG g env)

univP :: Parser Term
univP = lexeme $ Parser $ \s ->
    case s of
        ('U':rest) -> case span isDigit rest of
            (ds@(_:_), rem) -> Right (TUniv (read ds), rem)
            _               -> Left "expected U<n>"
        _ -> Left "expected universe"

intervalTyP :: Parser Term
intervalTyP = (symbol "\120128" <|> keyword "TIntervalTy") *> return TIntervalTy

notIdentChar :: Char -> Bool
notIdentChar c = not (isAlphaNum c || c == '_' || c == '\'')

notIdentCont :: String -> Bool
notIdentCont []    = True
notIdentCont (c:_) = notIdentChar c

intervalLitP :: Parser Term
intervalLitP = fmap TInterval $ lexeme $ Parser $ \s ->
    case s of
        ('i':rest) -> case span isDigit rest of
            (ds@(_:_), rem) | notIdentCont rem
                -> Right (IVar (read ds), rem)
            _   -> Left "not an interval literal"
        ('0':rest) | notIdentCont rest -> Right (I0, rest)
        ('1':rest) | notIdentCont rest -> Right (I1, rest)
        _          -> Left "not an interval literal"

pathG :: GlobalEnv -> Env -> Parser Term
pathG g env = do
    keyword "Path"
    a <- awG g env
    u <- awG g env
    v <- awG g env
    return (TPath a u v)

hcompG :: GlobalEnv -> Env -> Parser Term
hcompG g env = do
    keyword "hcomp"
    a   <- awG g env
    phi <- brackets (twG g env)
    u   <- plamAtomG g env <|> parens (twG g env) <|> awG g env
    u0  <- awG g env
    return (THComp a phi u u0)

plamAtomG :: GlobalEnv -> Env -> Parser Term
plamAtomG g env = do
    x    <- angles name
    body <- awG g (x : env)
    return (PLam x body)

glueTypeG :: GlobalEnv -> Env -> Parser Term
glueTypeG g env = do
    keyword "Glue"
    a   <- awG g env
    phi <- brackets (twG g env)
    te  <- parens (twG g env) <|> awG g env
    return (TGlue a phi te)

glueElemG :: GlobalEnv -> Env -> Parser Term
glueElemG g env = do
    keyword "glue"
    phi <- brackets (twG g env)
    t   <- parens (twG g env) <|> awG g env
    a   <- awG g env
    return (TGlueElem phi t a)

unglueG :: GlobalEnv -> Env -> Parser Term
unglueG g env = do
    keyword "unglue"
    phi <- brackets (twG g env)
    te  <- parens (twG g env) <|> awG g env
    gl  <- awG g env
    return (TUnglue phi te gl)

equivG :: GlobalEnv -> Env -> Parser Term
equivG g env = do
    keyword "Equiv"
    a <- awG g env
    b <- awG g env
    return (TEquiv a b)

mkEquivG :: GlobalEnv -> Env -> Parser Term
mkEquivG g env = do
    keyword "mkEquiv"
    a   <- awG g env
    b   <- awG g env
    f   <- parens (twG g env) <|> awG g env
    gg  <- parens (twG g env) <|> awG g env
    eta <- parens (twG g env) <|> awG g env
    eps <- parens (twG g env) <|> awG g env
    return (TMkEquiv a b f gg eta eps)

equivFwdG :: GlobalEnv -> Env -> Parser Term
equivFwdG g env = do
    keyword "equivFwd"
    e <- parens (twG g env) <|> awG g env
    x <- awG g env
    return (TEquivFwd e x)

uaG :: GlobalEnv -> Env -> Parser Term
uaG g env = do
    keyword "ua"
    e <- parens (twG g env) <|> awG g env
    return (TUa e)

transportG :: GlobalEnv -> Env -> Parser Term
transportG g env = do
    keyword "transport"
    p <- parens (twG g env) <|> awG g env
    x <- awG g env
    return (TTransport p x)

-- | Resolve a name: local binders first, then globals (most-recent = index
--   len(env), second-most-recent = len(env)+1, etc.).
varG :: GlobalEnv -> Env -> Parser Term
varG g env = do
    x <- name
    let localPairs  = zip env [0..]
        globalNames = map (\(n,_,_) -> n) (reverse g)
        globalPairs = zip globalNames [length env ..]
        allPairs    = localPairs ++ globalPairs
    case lookup x allPairs of
        Just i  -> return (TVar i)
        Nothing -> failP ("unbound variable: " ++ x)

-- Keep old termWith/atomP/varP so parseTerm still works (used standalone).
termWith :: Env -> Parser Term
termWith env = twG [] env

atomP :: Env -> Parser Term
atomP env = awG [] env

varP :: Env -> Parser Term
varP = varG []

--------------------------------------------------------------------------------
-- Statements (top-level declarations)
--------------------------------------------------------------------------------

-- | A statement is either a definition or a bare term to infer/check.
data Statement
    = SDef   Name (Maybe Term) Term   -- def x [: T] = e
    | SCheck Name Term Term           -- check x : T = e  (check only, no binding)
    | STerm  Term                     -- bare term
    deriving (Show)

-- | Parse a statement given a GlobalEnv for name resolution.
parseStatement :: GlobalEnv -> String -> Either ParseError Statement
parseStatement g src =
    case runParser (spaces *> stmtP g <* spaces) src of
        Left err      -> Left err
        Right (s, "") -> Right s
        Right (_, r)  -> Left ("leftover: " ++ r)

stmtP :: GlobalEnv -> Parser Statement
stmtP g = defP g <|> checkStmtP g <|> fmap STerm (twG g [])

defP :: GlobalEnv -> Parser Statement
defP g = do
    keyword "def"
    x <- name
    mTy <- try $ do
        symbol ":"
        twG g []
    symbol "="
    val <- twG g []
    return (SDef x mTy val)

checkStmtP :: GlobalEnv -> Parser Statement
checkStmtP g = do
    keyword "check"
    x  <- name
    symbol ":"
    ty <- twG g []
    symbol "="
    val <- twG g []
    return (SCheck x ty val)

-- | termWithG kept for any external callers; now just delegates to twG.
termWithG :: GlobalEnv -> Env -> Parser Term
termWithG = twG