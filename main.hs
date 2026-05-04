{-# LANGUAGE GADTs #-}

module CubicalInterval where

import Data.Set (Set)
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- 1. Syntax (AST)
--------------------------------------------------------------------------------

data I 
    = I0 
    | I1 
    | Var Int      -- Added variables/dimensions (i, j, k...)
    | Meet I I 
    | Join I I 
    | Neg I
    deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- 2. DNF Representation (Semantics)
--------------------------------------------------------------------------------

-- A Literal is either a dimension (i) or its negation (¬i).
data Literal = Pos Int | NegVar Int deriving (Eq, Ord)

instance Show Literal where
    show (Pos n)    = "i" ++ show n
    show (NegVar n) = "¬i" ++ show n

-- A Cube is a conjunction of literals: (L1 ∧ L2 ∧ ...)
type Cube = Set Literal

-- DNF is a disjunction of cubes: (Cube1 ∨ Cube2 ∨ ...)
newtype DNF = DNF { getCubes :: Set Cube } deriving (Eq, Ord)

instance Show DNF where
    show (DNF cs) 
        | Set.null cs = "0"
        | Set.null (Set.findMin cs) && Set.size cs == 1 = "1"
        | otherwise = intercalate " ∨ " (map showCube (Set.toList cs))
      where
        showCube c 
            | Set.null c = "1"
            | otherwise  = "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"
        intercalate sep = foldr (\x acc -> if acc == "" then x else x ++ sep ++ acc) ""

--------------------------------------------------------------------------------
-- 3. DNF Algebra Operations
--------------------------------------------------------------------------------

-- | Simplifies by Subsumption: A ∨ (A ∧ B) = A
-- We remove any cube that is a superset of another cube.
simplify :: Set Cube -> Set Cube
simplify cubes = Set.filter (\c -> not $ any (isStrictSubsetOf c) cubes) cubes
  where isStrictSubsetOf a b = a /= b && a `Set.isSubsetOf` b

dnfJoin :: DNF -> DNF -> DNF
dnfJoin (DNF a) (DNF b) = DNF $ simplify (Set.union a b)

dnfMeet :: DNF -> DNF -> DNF
dnfMeet (DNF as) (DNF bs) = 
    DNF $ simplify $ Set.fromList 
    [ Set.union a b | a <- Set.toList as, b <- Set.toList bs ]

dnfNeg :: DNF -> DNF
dnfNeg (DNF cubes) 
    | Set.null cubes = dnfTrue
    | otherwise = foldr dnfMeet dnfTrue (map negCube (Set.toList cubes))
  where
    negCube c = DNF $ Set.fromList [Set.singleton (negLit l) | l <- Set.toList c]
    negLit (Pos n)    = NegVar n
    negLit (NegVar n) = Pos n
    dnfTrue = DNF $ Set.singleton Set.empty

--------------------------------------------------------------------------------
-- 4. Evaluation and Normalization
--------------------------------------------------------------------------------

eval :: I -> DNF
eval I0         = DNF Set.empty
eval I1         = DNF (Set.singleton Set.empty)
eval (Var n)    = DNF (Set.singleton (Set.singleton (Pos n)))
eval (Neg i)    = dnfNeg (eval i)
eval (Meet i j) = dnfMeet (eval i) (eval j)
eval (Join i j) = dnfJoin (eval i) (eval j)

-- | Normalizing an expression means converting it to DNF and back to Syntax
-- Or simply comparing their DNF forms.
normalize :: I -> DNF
normalize = eval

--------------------------------------------------------------------------------
-- 5. Main Execution & Tests
--------------------------------------------------------------------------------

main :: IO ()
main = do
    let i = Var 0
    let j = Var 1

    putStrLn "=== De Morgan DNF Tests ==="
    
    -- Idempotence: i ∨ i = i
    putStrLn $ "i ∨ i           -> " ++ show (normalize (Join i i))
    
    -- Absorption: i ∨ (i ∧ j) = i
    putStrLn $ "i ∨ (i ∧ j)     -> " ++ show (normalize (Join i (Meet i j)))
    
    -- De Morgan: ¬(i ∧ j) = ¬i ∨ ¬j
    putStrLn $ "¬(i ∧ j)        -> " ++ show (normalize (Neg (Meet i j)))
    
    -- Double Negation: ¬¬i = i
    putStrLn $ "¬¬i             -> " ++ show (normalize (Neg (Neg i)))
    
    -- Complex: (i ∨ 1) ∧ j = j
    putStrLn $ "(i ∨ 1) ∧ j     -> " ++ show (normalize (Meet (Join i I1) j))

    putStrLn "\n=== Cubical Connections ==="
    -- connAnd i j = i ∧ j
    let connAnd = Meet i j
    putStrLn $ "Connection And  -> " ++ show (normalize connAnd)
    
    -- connOr i j = i ∨ j
    let connOr = Join i j
    putStrLn $ "Connection Or   -> " ++ show (normalize connOr)