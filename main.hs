import qualified Data.Set as Set
import Control.Monad (fmap)

-- 1. Unified Data Definition
type Name = String

data Term
    = Var Name
    | App Term Term
    | Lam Name Term Term   -- Lam variable type body
    | Pi  Name Term Term   -- Pi variable domain codomain (Dependent Product)
    | Kind                 -- The type of types (*)
    deriving (Eq)

instance Show Term where
    show (Var x)     = x
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"

-- 2. Evaluation / Normalization
-- Types must be reduced to "Normal Form" to check for equality.
substitute :: Name -> Term -> Term -> Term
substitute x n (Var y)
    | x == y    = n
    | otherwise = Var y
substitute x n (App m1 m2) = App (substitute x n m1) (substitute x n m2)
substitute x n (Lam y t e)
    | x == y    = Lam y (substitute x n t) e
    | otherwise = Lam y (substitute x n t) (substitute x n e) -- Simplified (ignoring capture for brevity)
substitute x n (Pi y t b)
    | x == y    = Pi y (substitute x n t) b
    | otherwise = Pi y (substitute x n t) (substitute x n b)
substitute _ _ Kind = Kind

reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam x t e -> reduce (substitute x n e)
        m'        -> App m' (reduce n)
        
-- Higher-order reduction for types inside Pi and Lam
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

-- 3. Type Checking Logic
type Context = [(Name, Term)]

typeOf :: Context -> Term -> Either String Term
typeOf _ Kind = Left "Type Error: Kind has no type (in this simple system)"

typeOf ctx (Var x) = 
    case lookup x ctx of
        Just t  -> Right t
        Nothing -> Left $ "Unbound variable: " ++ x

-- Typing Rule for Pi: (Γ |- A : *) -> (Γ, x:A |- B : *) -> (Γ |- Πx:A.B : *)
typeOf ctx (Pi x a b) = do
    sA <- typeOf ctx a
    sB <- typeOf ((x, a) : ctx) b
    if sA == Kind && sB == Kind
        then Right Kind
        else Left "Type Error: Pi components must be Types"

-- Typing Rule for Lambda: (Γ, x:A |- e : B) -> (Γ |- λx:A.e : Πx:A.B)
typeOf ctx (Lam x a e) = do
    _  <- typeOf ctx a -- Ensure the domain is a valid type
    b  <- typeOf ((x, a) : ctx) e
    return (Pi x a b)

-- Typing Rule for App: (Γ |- m : Πx:A.B) -> (Γ |- n : A) -> (Γ |- m n : [n/x]B)
typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi x a b -> 
            -- Check if the argument type matches the Pi domain
            if reduce a == reduce tN
            then Right (reduce (substitute x n b))
            else Left $ "Type mismatch: Expected " ++ show a ++ " but got " ++ show tN
        _ -> Left "Type Error: Expected a function (Pi) type"

-- 4. Main Execution
main :: IO ()
main = do
    putStrLn "--- Dependent Type System (Pi Calculus) ---"

    -- Define 'Bool' as a variable in context for demo
    -- In a real system, you'd define Church Booleans or Inductive types.
    let bool = Var "Bool"
    let ctx = [("Bool", Kind), ("True", bool), ("False", bool)]

    -- Example 1: Identity Function λA:*. λx:A. x
    -- This is polymorphic identity!
    let polyId = Lam "A" Kind (Lam "x" (Var "A") (Var "x"))
    
    putStrLn $ "Term: " ++ show polyId
    case typeOf ctx polyId of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn e

    -- Example 2: Applying PolyId to Bool
    -- (λA:*. λx:A. x) Bool
    let appBool = App polyId bool
    putStrLn $ "\nApplying to Bool: " ++ show appBool
    case typeOf ctx appBool of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn e
