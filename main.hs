{-# LANGUAGE GADTs #-}

module CubicalKan where

import Data.Map (Map)
import qualified Data.Map as Map

--------------------------------------------------------------------------------
-- 1. Dimensions and the Interval
--------------------------------------------------------------------------------

type Dim = String

data I 
    = I0 
    | I1 
    | Var Dim
    | Meet I I 
    | Join I I 
    | Neg I
    deriving (Show, Eq, Ord)

-- Recursive Normalizer (Extended for Variables)
normalize :: I -> I
normalize (Var d) = Var d
normalize I0 = I0
normalize I1 = I1
normalize (Neg I0) = I1
normalize (Neg I1) = I0
normalize (Neg (Neg i)) = normalize i
normalize (Meet i j) = 
    let (i', j') = (normalize i, normalize j) in
    case (i', j') of
        (I0, _) -> I0
        (_, I0) -> I0
        (I1, x) -> x
        (x, I1) -> x
        (a, b) | a == b -> a
               | otherwise -> Meet a b
normalize (Join i j) = 
    let (i', j') = (normalize i, normalize j) in
    case (i', j') of
        (I1, _) -> I1
        (_, I1) -> I1
        (I0, x) -> x
        (x, I0) -> x
        (a, b) | a == b -> a
               | otherwise -> Join a b
normalize (Neg (Meet i j)) = normalize (Join (Neg i) (Neg j))
normalize (Neg (Join i j)) = normalize (Meet (Neg i) (Neg j))
normalize x = x

--------------------------------------------------------------------------------
-- 2. The Kan Interface
--------------------------------------------------------------------------------

-- | A System is a map from boundary conditions (e.g., "i=0") to values.
type System a = Map (Dim, I) a

class Kan a where
    -- | Homogeneous Composition: hcomp phi sides bottom
    -- phi: the extent of the boundary
    -- sides: a function from interval to a system of points
    -- bottom: the "floor" of the cube
    hcomp :: I -> (I -> System a) -> a -> a

--------------------------------------------------------------------------------
-- 3. Implementing a Kan-ready Data Type (Points in Space)
--------------------------------------------------------------------------------

-- For this demo, let's represent a Point as a coordinate in N-dimensional space.
newtype Point = Point (Map Dim I) deriving (Show, Eq)

instance Kan Point where
    hcomp phi sides (Point bottom) = Point $ Map.mapWithKey fillCoord bottom
      where
        fillCoord dim val = 
            -- Simplistic Kan filler for the interval itself
            -- In a real system, this uses the "Connection" structure.
            normalize (Join phi (normalize val))

--------------------------------------------------------------------------------
-- 4. Path Operations via Kan
--------------------------------------------------------------------------------

type Path a = I -> a

-- | Composition (p ∙ q) using Kan hcomp
-- This creates a square where p and q are the sides, then retrieves the top.
compose :: (Kan a) => Path a -> Path a -> Path a
compose p q i = 
    let phi = Join (Neg i) i -- Boundary active at i=0 and i=1
        sides j = Map.fromList [ (("i", I0), p j)
                               , (("i", I1), q j) ]
    in hcomp phi sides (p I1)

--------------------------------------------------------------------------------
-- 5. Main Execution
--------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "--- Cubical Kan Composition ---"
    
    -- Define two points
    let ptA = Point (Map.fromList [("x", I0)])
    let ptB = Point (Map.fromList [("x", I1)])
    let ptC = Point (Map.fromList [("x", Var "k")])

    -- Define paths (linear interpolations)
    let pathP i = Point (Map.fromList [("x", i)]) -- Path from 0 to 1
    let pathQ i = Point (Map.fromList [("x", Neg i)]) -- Path from 1 to 0

    putStrLn "Testing Path P at I0 and I1:"
    print (pathP I0)
    print (pathP I1)

    putStrLn "\nComposing P and Q (Kan Composition):"
    -- Result of composition at midpoint
    let pq = compose pathP pathQ
    print (pq (Var "j"))