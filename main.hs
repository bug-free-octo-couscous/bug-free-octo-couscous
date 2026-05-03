import qualified Data.Set as Set

-- 1. Data Definition
type Name = String
type Index = Int

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term  -- Name is a hint for printing
    | Pi  Name Term Term  
    | Kind                -- (*)
    | Box                 -- (□)
    deriving (Eq)

instance Show Term where
    show (Var i)     = show i
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"
    show Box         = "□"

-- 2. De Bruijn Shifting and Substitution
-- shift d c t: increments all indices in t that are >= c by d
shift :: Int -> Int -> Term -> Term
shift d c (Var i)     = if i >= c then Var (i + d) else Var i
shift d c (App m n)   = App (shift d c m) (shift d c n)
shift d c (Lam x t e) = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)  = Pi x (shift d c t) (shift d (c + 1) b)
shift _ _ Kind        = Kind
shift _ _ Box         = Box

-- substitute j n m: replaces index j in m with term n
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

-- 3. Evaluation / Normalization
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        -- Beta reduction: shift -1 because the Lam binder is removed
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

-- 4. Type Checking Logic
-- Context is now a list of types; index i refers to the i-th element.
type Context = [Term]

typeOf :: Context -> Term -> Either String Term
typeOf _ Box = Left "Type Error: Box is the top of the hierarchy"
typeOf _ Kind = Right Box

typeOf ctx (Var i) 
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    sA <- typeOf ctx a
    sB <- typeOf (a : ctx) b
    if (sA == Kind || sA == Box) && (sB == Kind || sB == Box)
        then Right sB 
        else Left "Type Error: Pi components must be Types or Kinds"

typeOf ctx (Lam x a e) = do
    _ <- typeOf ctx a 
    b <- typeOf (a : ctx) e
    return (Pi x a b)

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b -> 
            if reduce a == reduce tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left "Type mismatch: Argument type does not match Pi domain"
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function type"

-- 5. Main Execution
main :: IO ()
main = do
    putStrLn "--- De Bruijn Index Type System ---"

    -- We'll put "Bool" in our context as index 0.
    -- Context: [Kind] (Meaning index 0 has type Kind)
    let ctx = [Kind] 

    -- Example 1: Polymorphic Identity λA:*. λx:A. x
    -- Nested binders: A is index 1, x is index 0.
    let polyId = Lam "A" Kind (Lam "x" (Var 0) (Var 0))
    
    putStrLn $ "Term: " ++ show polyId
    case typeOf ctx polyId of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e

    -- Example 2: Applying PolyId to index 0 (which is our "Bool")
    let appBool = App polyId (Var 0)
    putStrLn $ "\nApplying to Var 0: " ++ show appBool
    case typeOf ctx appBool of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e
