module Parser
    ( parseTerm
    , parseInterval
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
angles p = symbol "\10216" *> p <* symbol "\10217"

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
        mv <- try (symbol "\8744")
        case mv of
            Nothing -> return acc
            Just () -> iMeet >>= \r -> go (Join acc r)

iMeet :: Parser I
iMeet = do
    l <- iNeg
    go l
  where
    go acc = do
        mv <- try (symbol "\8743")
        case mv of
            Nothing -> return acc
            Just () -> iNeg >>= \r -> go (Meet acc r)

iNeg :: Parser I
iNeg = (symbol "\172" *> fmap Neg iNeg)
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
                _                     -> Left "expected i<n>"
            _ -> Left "expected interval variable"

--------------------------------------------------------------------------------
-- Term parser
--------------------------------------------------------------------------------

parseTerm :: String -> Either ParseError Term
parseTerm s =
    case runParser (spaces *> termWith [] <* spaces) s of
        Left err      -> Left err
        Right (t, "") -> Right t
        Right (_, r)  -> Left ("leftover: " ++ r)

termWith :: Env -> Parser Term
termWith env = lamP env <|> plamP env <|> piP env <|> appP env

lamP :: Env -> Parser Term
lamP env = do
    symbol "\955"
    x    <- name
    symbol "."
    body <- termWith (x : env)
    return (TAbs x body)

plamP :: Env -> Parser Term
plamP env = do
    x    <- angles name
    body <- termWith (x : env)
    return (PLam x body)

piP :: Env -> Parser Term
piP env = do
    symbol "\928"
    symbol "("
    x   <- name
    symbol ":"
    aTy <- termWith env
    symbol ")"
    symbol "."
    bTy <- termWith (x : env)
    return (TPi x aTy bTy)

appP :: Env -> Parser Term
appP env = do
    f <- atomP env
    go f
  where
    go acc = do
        mpat <- try (symbol "@")
        case mpat of
            Just () -> atomP env >>= \r -> go (PApp acc r)
            Nothing -> do
                marg <- try (atomP env)
                case marg of
                    Nothing  -> return acc
                    Just arg -> go (TApp acc arg)

atomP :: Env -> Parser Term
atomP env
     =  univP
    <|> intervalTyP
    <|> intervalLitP
    <|> hcompP    env
    <|> glueTypeP env
    <|> glueElemP env
    <|> unglueP   env
    <|> pathP     env
    <|> equivP    env        -- Equiv A B
    <|> mkEquivP  env        -- mkEquiv A B f g η ε
    <|> equivFwdP env        -- equivFwd e x
    <|> uaP       env        -- ua e
    <|> transportP env       -- transport p x
    <|> varP env
    <|> parens (termWith env)

univP :: Parser Term
univP = lexeme $ Parser $ \s ->
    case s of
        ('U':rest) -> case span isDigit rest of
            (ds@(_:_), rem) -> Right (TUniv (read ds), rem)
            _               -> Left "expected U<n>"
        _ -> Left "expected universe"

intervalTyP :: Parser Term
intervalTyP = symbol "\120128" *> return TIntervalTy

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

pathP :: Env -> Parser Term
pathP env = do
    keyword "Path"
    a <- atomP env
    u <- atomP env
    v <- atomP env
    return (TPath a u v)

hcompP :: Env -> Parser Term
hcompP env = do
    keyword "hcomp"
    a   <- atomP env
    phi <- brackets (termWith env)
    u   <- plamAtomP env <|> parens (termWith env) <|> atomP env
    u0  <- atomP env
    return (THComp a phi u u0)

plamAtomP :: Env -> Parser Term
plamAtomP env = do
    x    <- angles name
    body <- atomP (x : env)
    return (PLam x body)

glueTypeP :: Env -> Parser Term
glueTypeP env = do
    keyword "Glue"
    a   <- atomP env
    phi <- brackets (termWith env)
    te  <- parens (termWith env) <|> atomP env
    return (TGlue a phi te)

glueElemP :: Env -> Parser Term
glueElemP env = do
    keyword "glue"
    phi <- brackets (termWith env)
    t   <- parens (termWith env) <|> atomP env
    a   <- atomP env
    return (TGlueElem phi t a)

unglueP :: Env -> Parser Term
unglueP env = do
    keyword "unglue"
    phi <- brackets (termWith env)
    te  <- parens (termWith env) <|> atomP env
    g   <- atomP env
    return (TUnglue phi te g)

-- Equiv A B
equivP :: Env -> Parser Term
equivP env = do
    keyword "Equiv"
    a <- atomP env
    b <- atomP env
    return (TEquiv a b)

-- mkEquiv A B f g eta eps
mkEquivP :: Env -> Parser Term
mkEquivP env = do
    keyword "mkEquiv"
    a   <- atomP env
    b   <- atomP env
    f   <- parens (termWith env) <|> atomP env
    g   <- parens (termWith env) <|> atomP env
    eta <- parens (termWith env) <|> atomP env
    eps <- parens (termWith env) <|> atomP env
    return (TMkEquiv a b f g eta eps)

-- equivFwd e x
equivFwdP :: Env -> Parser Term
equivFwdP env = do
    keyword "equivFwd"
    e <- parens (termWith env) <|> atomP env
    x <- atomP env
    return (TEquivFwd e x)

-- ua e
uaP :: Env -> Parser Term
uaP env = do
    keyword "ua"
    e <- parens (termWith env) <|> atomP env
    return (TUa e)

-- transport p x
transportP :: Env -> Parser Term
transportP env = do
    keyword "transport"
    p <- parens (termWith env) <|> atomP env
    x <- atomP env
    return (TTransport p x)

varP :: Env -> Parser Term
varP env = do
    x <- name
    case lookup x (zip env [0..]) of
        Just i  -> return (TVar i)
        Nothing -> failP ("unbound variable: " ++ x)