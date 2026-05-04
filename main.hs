{-# LANGUAGE GADTs #-}

module CubicalInterval where

--------------------------------------------------------------------------------
-- 1. The Interval Type (With Recursive Normalization)
--------------------------------------------------------------------------------

data I 
    = I0 
    | I1 
    | Meet I I 
    | Join I I 
    | Neg I
    deriving (Show, Eq)

-- | Recursive Normalizer: Collapses the De Morgan Algebra.
-- This ensures that (Neg (Neg i)) and (Meet I1 i) actually simplify.
normalize :: I -> I
normalize I0 = I0
normalize I1 = I1
normalize (Neg I0) = I1
normalize (Neg I1) = I0
normalize (Neg (Neg i)) = normalize i
normalize (Neg (Meet i j)) = normalize (Join (Neg i) (Neg j)) -- De Morgan
normalize (Neg (Join i j)) = normalize (Meet (Neg i) (Neg j)) -- De Morgan
normalize (Meet i j) = 
    let i' = normalize i
        j' = normalize j
    in case (i', j') of
        (I0, _)  -> I0
        (_, I0)  -> I0
        (I1, x)  -> x
        (x, I1)  -> x
        (a, b)   | a == b -> a
                 | otherwise -> Meet a b
normalize (Join i j) = 
    let i' = normalize i
        j' = normalize j
    in case (i', j') of
        (I1, _)  -> I1
        (_, I1)  -> I1
        (I0, x)  -> x
        (x, I0)  -> x
        (a, b)   | a == b -> a
                 | otherwise -> Join a b

--------------------------------------------------------------------------------
-- 2. Paths and Operations
--------------------------------------------------------------------------------

type Path a = I -> a

-- | Reverses a path (p⁻¹)
rev :: Path a -> Path a
rev p i = p (normalize (Neg i))

-- | Constant path
refl :: a -> Path a
refl x _ = x

-- | Path Composition (p ∙ q)
-- Connects two paths where p(1) == q(0).
-- This uses the interval dimension to "glue" them together.
trans :: Path a -> Path a -> Path a
trans p q i = case normalize i of
    I0 -> p I0
    I1 -> q I1
    _  -> q i -- In a real system, this involves a Kan composition

--------------------------------------------------------------------------------
-- 3. Squares (2D Cubes)
--------------------------------------------------------------------------------

type Square a = I -> I -> a

-- | A square where the edges are defined by specific paths.
mkSquare :: Path a -> Path a -> Path a -> Path a -> Square a
mkSquare bottom top left right i j = 
    case (normalize i, normalize j) of
        (_, I0) -> bottom i
        (_, I1) -> top i
        (I0, _) -> left j
        (I1, _) -> right j
        _       -> bottom i -- Simplistic filler

--------------------------------------------------------------------------------
-- 4. Main Execution
--------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "--- Interval Logic Test ---"
    let complex = Meet (Neg (Neg I1)) (Join I0 I1)
    putStrLn $ "Original: Meet (Neg (Neg I1)) (Join I0 I1)"
    putStrLn $ "Normalized: " ++ show (normalize complex)
    
    putStrLn "\n--- Path Operations ---"
    let p = \i -> if normalize i == I0 then "Point A" else "Point B"
    let q = \i -> if normalize i == I0 then "Point B" else "Point C"
    
    let p_rev = rev p
    putStrLn $ "Path P at I0: " ++ p I0
    putStrLn $ "Path P at I1: " ++ p I1
    putStrLn $ "Reversed P at I0: " ++ p_rev I0
    
    putStrLn "\n--- Square Boundary Check ---"
    -- A square where all edges are "Point X"
    let sq i j = "Coord(" ++ show (normalize i) ++ "," ++ show (normalize j) ++ ")"
    putStrLn $ "Square at (I0, I1): " ++ sq I0 I1
    putStrLn $ "Square at (I1, I1): " ++ sq I1 I1