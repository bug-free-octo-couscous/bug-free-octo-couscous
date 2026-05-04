module Main where

type Name = String
type Index = Int

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term
    | Pi  Name Term Term
    | Kind
    | Box
    deriving (Eq)

instance Show Term where
    show (Var i)     = show i
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"
    show Box         = "□"

-- 1. De Bruijn Shifting and Substitution
shift :: Int -> Int -> Term -> Term
shift d c (Var i)     = if i >= c then Var (i + d) else Var i
shift d c (App m n)   = App (shift d c m) (shift d c n)
shift d c (Lam x t e) = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)  = Pi x (shift d c t) (shift d (c + 1) b)
shift _ _ Kind        = Kind
shift _ _ Box         = Box

substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) =
    Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  =
    Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute _ _ Kind = Kind
substitute _ _ Box  = Box

-- 2. Evaluation
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'         -> App m' (reduce n)
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

betaEquals :: Term -> Term -> Bool
betaEquals t1 t2 = reduce t1 == reduce t2

-- 3. Consistency and PTS Rules
type Context = [Term]

-- This defines the "System F-omega" or "Calculus of Constructions" rules.
-- (Kind, Kind) -> Kind allows types depending on types (polymorphism)
-- (Kind, Box)  -> Box  allows operators from types to types
-- (Box, Box)   -> Box  allows operators from kinds to kinds
allowedRules :: Term -> Term -> Either String Term
allowedRules Kind Kind = Right Kind -- Type -> Type (Functions)
allowedRules Kind Box  = Right Box  -- Type -> Kind (Polymorphism)
allowedRules Box Kind  = Right Kind -- Kind -> Type (Type operators)
allowedRules Box Box   = Right Box  -- Kind -> Kind (Type constructors)
allowedRules s1 s2     = Left $ "PTS Rule violation: (" ++ show s1 ++ ", " ++ show s2 ++ ") is not allowed."

-- 4. Type Checking with Consistency
checkIsSort :: Context -> Term -> Either String Term
checkIsSort ctx t = do
    tType <- typeOf ctx t
    case reduce tType of
        Kind -> Right Kind
        Box  -> Right Box
        _    -> Left $ "Consistency Error: " ++ show t ++ " is not a Sort (Kind/Box)"

typeOf :: Context -> Term -> Either String Term
typeOf _ Box = Left "Type Error: Box is the top of the hierarchy (not typable here)"
typeOf _ Kind = Right Box

typeOf ctx (Var i)
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    s1 <- checkIsSort ctx a
    s2 <- checkIsSort (a : ctx) b
    allowedRules s1 s2

typeOf ctx (Lam x a e) = do
    _ <- checkIsSort ctx a
    b <- typeOf (a : ctx) e
    let piType = Pi x a b
    -- Ensure the resulting Pi type is consistent in our system
    _ <- typeOf ctx piType 
    return piType

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b ->
            if betaEquals a tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left $ "Type mismatch: Expected " ++ show a ++ " but got " ++ show tN
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function type"

-- 5. Main
main :: IO ()
main = do
    putStrLn "--- Consistent Type System (CoC Rules) ---"
    
    -- Example 1: Valid Identity on Types
    -- λA:*. λx:A. x
    let ctx = [] 
    let identity = Lam "A" Kind (Lam "x" (Var 0) (Var 0))
    
    putStrLn "Checking Identity: λA:*. λx:A. x"
    case typeOf ctx identity of
        Right t -> putStrLn $ "Success! Type: " ++ show (reduce t)
        Left e  -> putStrLn $ "Error: " ++ e

    -- Example 2: Attempting to use Box as a term (Should fail consistency)
    -- λA:□. A
    let badTerm = Lam "A" Box (Var 0)
    putStrLn "\nChecking Illegal Term: λA:□. A"
    case typeOf ctx badTerm of
        Right t -> putStrLn $ "Success! Type: " ++ show (reduce t)
        Left e  -> putStrLn $ "Expected Failure: " ++ e
-- current goal 
-- implement Inductive Types
