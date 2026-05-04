{-# LANGUAGE GADTs #-}

module CubicalInterval where

--------------------------------------------------------------------------------
-- 1. The Interval Type (De Morgan Algebra)
--------------------------------------------------------------------------------

data I 
    = I0 
    | I1 
    | Meet I I 
    | Join I I 
    | Neg I
    deriving (Show, Eq)

-- | Recursive Normalizer: Implements De Morgan Algebra identities.
normalize :: I -> I
normalize expr = case expr of
    I0       -> I0
    I1       -> I1
    Neg i    -> normNeg (normalize i)
    Meet i j -> normMeet (normalize i) (normalize j)
    Join i j -> normJoin (normalize i) (normalize j)

-- | Handle Negation logic
-- We match on specific patterns to simplify.
normNeg :: I -> I
normNeg I0          = I1
normNeg I1          = I0
normNeg (Neg i)     = i               -- Double Negation: ¬¬i = i
normNeg (Meet i j)  = Join (normNeg i) (normNeg j) -- De Morgan: ¬(i ∧ j) = ¬i ∨ ¬j
normNeg (Join i j)  = Meet (normNeg i) (normNeg j) -- De Morgan: ¬(i ∨ j) = ¬i ∧ ¬j

-- | Handle Meet (Lattice Infimum) logic
normMeet :: I -> I -> I
normMeet I0 _  = I0
normMeet _ I0  = I0
normMeet I1 j  = j
normMeet i I1  = i
normMeet i j
    | i == j    = i                   -- Idempotence: i ∧ i = i
    | isAbs i j = i                   -- Absorption: i ∧ (i ∨ j) = i
    | isAbs j i = j
    | otherwise = Meet i j
  where 
    isAbs a (Join b c) = a == b || a == c
    isAbs _ _          = False

-- | Handle Join (Lattice Supremum) logic
normJoin :: I -> I -> I
normJoin I1 _  = I1
normJoin _ I1  = I1
normJoin I0 j  = j
normJoin i I0  = i
normJoin i j
    | i == j    = i                   -- Idempotence: i ∨ i = i
    | isAbs i j = i                   -- Absorption: i ∨ (i ∧ j) = i
    | isAbs j i = j
    | otherwise = Join i j
  where
    isAbs a (Meet b c) = a == b || a == c
    isAbs _ _          = False

--------------------------------------------------------------------------------
-- 2. Paths and Connections
--------------------------------------------------------------------------------

type Path a = I -> a

-- | Symmetry (Reverses a path)
rev :: Path a -> Path a
rev p i = p (normalize (Neg i))

-- | Connections
-- These are standard in Cubical Type Theory to map paths to higher dimensions.
connAnd :: Path a -> I -> I -> a
connAnd p i j = p (normalize (Meet i j))

connOr :: Path a -> I -> I -> a
connOr p i j = p (normalize (Join i j))

--------------------------------------------------------------------------------
-- 3. Main Execution
--------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "=== De Morgan Algebra Logic Test ==="
    
    let test1 = Neg (Neg (Meet I1 I0))
    putStrLn $ "¬¬(1 ∧ 0)         -> " ++ show (normalize test1)
    
    let test2 = Neg (Meet (Neg I1) I1)
    putStrLn $ "¬(¬1 ∧ 1)         -> " ++ show (normalize test2)
    
    let test3 = Join I1 (Meet I1 I0)
    putStrLn $ "1 ∨ (1 ∧ 0)       -> " ++ show (normalize test3)
    
    let test4 = Meet (Join I0 I1) (Neg I0)
    putStrLn $ "(0 ∨ 1) ∧ ¬0      -> " ++ show (normalize test4)

    putStrLn "\n=== Path & Connection Test ==="
    -- A simple path from "A" to "B"
    let p i = if normalize i == I0 then "Point A" else "Point B"
    
    putStrLn $ "Path p at I0:      " ++ p I0
    putStrLn $ "Path p at I1:      " ++ p I1
    putStrLn $ "rev p at I0:       " ++ rev p I0
    putStrLn $ "connAnd p at (1,1): " ++ connAnd p I1 I1
    putStrLn $ "connAnd p at (1,0): " ++ connAnd p I1 I0