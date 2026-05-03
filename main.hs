import qualified Data.Set as Set
import Control.Monad (fmap)

-- 1. Unified Data Definition
type Name = String

data Type
    = Base String          -- e.g., "Bool", "Int"
    | Fun Type Type        -- e.g., A -> B
    deriving (Eq)

instance Show Type where
    show (Base s) = s
    show (Fun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

data Expr
    = Var Name
    | Lam Name Type Expr   -- Typed Lambda: λx:T. e
    | App Expr Expr
    deriving (Eq)

instance Show Expr where
    show (Var x)         = x
    show (Lam x t e)     = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (App m n)       = "(" ++ show m ++ " " ++ show n ++ ")"

-- 2. Type Checking Logic
type Context = [(Name, Type)]

-- Returns Right Type if valid, or Left ErrorMessage if invalid
typeOf :: Context -> Expr -> Either String Type
typeOf ctx (Var x) = 
    case lookup x ctx of
        Just t  -> Right t
        Nothing -> Left $ "Type Error: Unbound variable '" ++ x ++ "'"

typeOf ctx (Lam x t1 e) = do
    t2 <- typeOf ((x, t1) : ctx) e
    return (Fun t1 t2)

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case tM of
        Fun tArg tRes ->
            if tArg == tN 
            then Right tRes 
            else Left $ "Type Error: Type mismatch. Expected " ++ show tArg ++ " but got " ++ show tN
        _ -> Left "Type Error: Cannot apply a non-function type"

-- 3. Helper Functions for Substitution
freeVars :: Expr -> Set.Set Name
freeVars (Var x)       = Set.singleton x
freeVars (Lam x _ e)   = Set.delete x (freeVars e)
freeVars (App m n)     = Set.union (freeVars m) (freeVars n)

substitute :: Name -> Expr -> Expr -> Expr
substitute x n (Var y)
    | x == y    = n
    | otherwise = Var y
substitute x n (App m1 m2) = App (substitute x n m1) (substitute x n m2)
substitute x n (Lam y t e)
    | x == y                      = Lam y t e
    | y `Set.notMember` freeVars n = Lam y t (substitute x n e)
    | otherwise                   =
        let y' = y ++ "'"
            e' = substitute y (Var y') e
        in substitute x n (Lam y' t e')

-- 4. Evaluation Logic (Small-step Operational Semantics)
reduceStep :: Expr -> Maybe Expr
reduceStep (App (Lam x t e) n) = Just $ substitute x n e
reduceStep (App m n) =
    case reduceStep m of
        Just m' -> Just (App m' n)
        Nothing -> case reduceStep n of
            Just n' -> Just (App m n')
            Nothing -> Nothing
reduceStep (Lam x t e) = Lam x t <$> reduceStep e
reduceStep (Var _)     = Nothing

evalFull :: Expr -> Expr
evalFull e = case reduceStep e of
    Just e' -> evalFull e'
    Nothing -> e

-- 5. Main Execution
main :: IO ()
main = do
    let tyA = Base "A"
    let tyB = Base "B"

    putStrLn "--- Simply Typed Lambda Calculus ---"

    -- Example 1: Identity Function (λx:A. x) applied to a variable 'y'
    -- (λx:A. x) y
    let identity = Lam "x" tyA (Var "x")
    let testExpr = App identity (Var "y")

    -- We must provide a context where 'y' has type 'A'
    let ctx = [("y", tyA)]

    putStrLn $ "Expression: " ++ show testExpr
    case typeOf ctx testExpr of
        Left err -> putStrLn err
        Right t  -> do
            putStrLn $ "Type:       " ++ show t
            putStrLn $ "Result:     " ++ show (evalFull testExpr)

    putStrLn "\n--- Example 2: Type Mismatch ---"
    -- Attempting to apply (λx:A. x) to a variable of type B
    let badCtx = [("y", tyB)]
    case typeOf badCtx testExpr of
        Left err -> putStrLn $ "Caught: " ++ err
        Right t  -> putStrLn $ "Result: " ++ show t

    putStrLn "\n--- Example 3: Higher Order Function ---"
    -- λf:(A->B). λx:A. f x
    let higherOrder = Lam "f" (Fun tyA tyB) (Lam "x" tyA (App (Var "f") (Var "x")))
    case typeOf [] higherOrder of
        Left err -> putStrLn err
        Right t  -> putStrLn $ "Type of HO function: " ++ show t
