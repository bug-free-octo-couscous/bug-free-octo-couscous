{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- 1. Interval Syntax & DNF
--------------------------------------------------------------------------------

data I 
    = I0 | I1 
    | IVar Int 
    | Meet I I | Join I I | Neg I
    deriving (Show, Eq, Ord)

data Literal = Pos Int | NegVar Int deriving (Eq, Ord)

instance Show Literal where
    show (Pos n)    = "i" ++ show n
    show (NegVar n) = "¬i" ++ show n

newtype DNF = DNF { getCubes :: Set (Set Literal) } deriving (Eq, Ord)

instance Show DNF where
    show (DNF cs) 
        | Set.null cs = "0"
        | Set.null (Set.findMin cs) && Set.size cs == 1 = "1"
        | otherwise = intercalate " ∨ " (map showCube (Set.toList cs))
      where
        showCube c = if Set.null c then "1" else "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"

--------------------------------------------------------------------------------
-- 2. Cubical Dependent Syntax
--------------------------------------------------------------------------------

type Name = String
type Level = Int

data Term
    = TVar Name
    | TApp Term Term
    | TAbs Name Term
    -- Universes
    | TUniv Level           -- U_n
    -- Dependent Types (Pi Types)
    | TPi Name Term Term    -- Π(x:A). B
    -- Cubical Additions
    | TInterval I
    | TCube DNF
    deriving (Eq)

instance Show Term where
    show t = case t of
        TVar x      -> x
        TApp f a    -> "(" ++ show f ++ " " ++ show a ++ ")"
        TAbs x b    -> "λ" ++ x ++ ". " ++ show b
        TUniv n     -> "U" ++ show n
        TPi x a b   -> "Π(" ++ x ++ ":" ++ show a ++ "). " ++ show b
        TInterval i -> show i
        TCube c     -> show c

--------------------------------------------------------------------------------
-- 3. Evaluation & Substitution
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution: t[x := s]
subst :: Name -> Term -> Term -> Term
subst x s term = case term of
    TVar y      | x == y    -> s
                | otherwise -> TVar y
    TApp f a                -> TApp (subst x s f) (subst x s a)
    TAbs y b    | x == y    -> TAbs y b
                | otherwise -> TAbs y (subst x s b)
    TPi y a b   | x == y    -> TPi y (subst x s a) b
                | otherwise -> TPi y (subst x s a) (subst x s b)
    TUniv n                 -> TUniv n
    TInterval i             -> TInterval i
    TCube c                 -> TCube c

-- | Normalizes terms to Weak Head Normal Form / Normal Form
eval :: Term -> Term
eval t = case t of
    TApp f a -> 
        case eval f of
            TAbs x body -> eval (subst x (eval a) body)
            f'          -> TApp f' (eval a)
    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TInterval i -> TCube (evalInterval i)
    _           -> t

--------------------------------------------------------------------------------
-- 4. Interval Algebra
--------------------------------------------------------------------------------

simplify :: Set (Set Literal) -> Set (Set Literal)
simplify cubes = Set.filter (\c -> not $ any (\other -> c /= other && other `Set.isSubsetOf` c) cubes) cubes

evalInterval :: I -> DNF
evalInterval I0          = DNF Set.empty
evalInterval I1          = DNF (Set.singleton Set.empty)
evalInterval (IVar n)    = DNF (Set.singleton (Set.singleton (Pos n)))
evalInterval (Neg i)     = dnfNeg (evalInterval i)
evalInterval (Meet i j)  = dnfMeet (evalInterval i) (evalInterval j)
evalInterval (Join i j)  = dnfJoin (evalInterval i) (evalInterval j)

dnfJoin (DNF a) (DNF b)   = DNF $ simplify (Set.union a b)
dnfMeet (DNF as) (DNF bs) = DNF $ simplify $ Set.fromList [ Set.union a b | a <- Set.toList as, b <- Set.toList bs ]
dnfNeg (DNF cubes) 
    | Set.null cubes = DNF $ Set.singleton Set.empty
    | otherwise = foldr dnfMeet (DNF $ Set.singleton Set.empty) (map negCube (Set.toList cubes))
  where
    negCube c = DNF $ Set.fromList [Set.singleton (negLit l) | l <- Set.toList c]
    negLit (Pos n) = NegVar n
    negLit (NegVar n) = Pos n

--------------------------------------------------------------------------------
-- 5. Demonstration
--------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "=== Cubical Lambda Calculus with Universes ==="

    -- 1. Identity function for a type in U0
    -- id : Π(A:U0). Π(x:A). A
    let idType = TPi "A" (TUniv 0) (TPi "x" (TVar "A") (TVar "A"))
    let idTerm = TAbs "A" (TAbs "x" (TVar "x"))
    
    putStrLn $ "\nIdentity Type: " ++ show idType
    putStrLn $ "Identity Term: " ++ show idTerm

    -- 2. Applying identity to a Universe
    -- ((λA. λx. x) U0) -> λx. x
    let testUniv = TApp idTerm (TUniv 0)
    putStrLn $ "\nApplying id to U0:"
    putStrLn $ "Result: " ++ show (eval testUniv)

    -- 3. Path-like type: A function from the interval to a universe
    -- This represents a "Line" of types: Π(i:I). U0
    let lineType = TPi "i" (TInterval (IVar 0)) (TUniv 0)
    putStrLn $ "\nLine of Types (Path in U0): " ++ show lineType

    -- 4. Cubical Normalization inside types
    -- Π(x : ¬¬i0). U0  ==> Π(x : i0). U0
    let nestedLogic = TPi "x" (TInterval (Neg (Neg (IVar 0)))) (TUniv 0)
    putStrLn $ "\nNormalized Interval in Pi-binder:"
    putStrLn $ "Input:  " ++ show nestedLogic
    putStrLn $ "Result: " ++ show (eval nestedLogic)