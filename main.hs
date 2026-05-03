import qualified Data.Set as Set
import Data.List (union, (\\))

-- 1. Data Definitions
type Name = String

data Expr
    = Var Name
    | Lam Name Expr
    | App Expr Expr
    deriving (Eq)

-- Pretty-printer for the expressions
instance Show Expr where
    show (Var x)   = x
    show (Lam x e) = "λ" ++ x ++ "." ++ show e
    show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"

-- 2. Helper Functions for Substitution
freeVars :: Expr -> Set.Set Name
freeVars (Var x)   = Set.singleton x
freeVars (Lam x e) = Set.delete x (freeVars e)
freeVars (App m n) = Set.union (freeVars m) (freeVars n)

-- Robust substitution to avoid variable capture
substitute :: Name -> Expr -> Expr -> Expr
substitute x n (Var y)
    | x == y    = n
    | otherwise = Var y
substitute x n (App m1 m2) = App (substitute x n m1) (substitute x n m2)
substitute x n (Lam y e)
    | x == y          = Lam y e
    | y `Set.notMember` freeVars n = Lam y (substitute x n e)
    | otherwise       =
        let y' = y ++ "'"
            e' = substitute y (Var y') e
        in substitute x n (Lam y' e')

-- 3. Evaluation Logic (Normal Order Reduction)
-- Returns Nothing if it's already in Normal Form
reduceStep :: Expr -> Maybe Expr
reduceStep (App (Lam x e) n) = Just $ substitute x n e -- Beta-reduction!
reduceStep (App m n) =
    case reduceStep m of
        Just m' -> Just (App m' n)
        Nothing -> case reduceStep n of
            Just n' -> Just (App m n')
            Nothing -> Nothing
reduceStep (Lam x e) = Lam x <$> reduceStep e
reduceStep (Var _)   = Nothing

-- Fully evaluate to Normal Form
evalFull :: Expr -> Expr
evalFull e = case reduceStep e of
    Just e' -> evalFull e'
    Nothing -> e

-- 4. Examples & Main
-- Church Encodings
churchTrue  = Lam "t" (Lam "f" (Var "t"))
churchFalse = Lam "t" (Lam "f" (Var "f"))
churchAnd   = Lam "p" (Lam "q" (App (App (Var "p") (Var "q")) (Var "p")))

-- Church Numerals
zero = Lam "f" (Lam "x" (Var "x"))
one  = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
succNum = Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (Var "n") (Var "f")) (Var "x")))))

main :: IO ()
main = do
    putStrLn "--- Lambda Calculus Evaluator ---"

    let identity = Lam "x" (Var "x")
    let testExpr = App identity (Var "y")

    putStrLn $ "Expression: " ++ show testExpr
    putStrLn $ "Result:     " ++ show (evalFull testExpr)

    putStrLn "\n--- Church Encoding: (True AND False) ---"
    let andTest = App (App churchAnd churchTrue) churchFalse
    putStrLn $ "Reduced: " ++ show (evalFull andTest)
    -- Should print λt.λf.f which is the definition of False

    putStrLn "\n--- Church Encoding: Successor of Zero (1) ---"
    let oneTest = App succNum zero
    putStrLn $ "Result: " ++ show (evalFull oneTest)
