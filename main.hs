import CubicalLambda

import Parser

--------------------------------------------------------------------------------
-- Main – parse → infer round-trip demo
--------------------------------------------------------------------------------

tryParse :: String -> IO ()
tryParse src = do
    putStr $ "  parse  " ++ show src ++ "\n    => "
    case parseTerm src of
        Left err -> putStrLn $ "PARSE ERROR: " ++ err
        Right t  -> do
            putStrLn $ show t
            case inferClosed t of
                Right ty -> putStrLn $ "    : " ++ show ty
                Left err -> putStrLn $ "    TYPE ERROR: " ++ show err

main :: IO ()
main = do
    putStrLn "=== Cubical Lambda Parser Demo ===\n"

    -- Universes
    tryParse "U0"
    tryParse "U1"

    -- Pi type  Π(x:U0). U0
    tryParse "\928(x:U0). U0"

    -- Lambda  λx. x  (needs a check, not infer — shown as parse only)
    putStr   "  parse  \"λx. x\"\n    => "
    case parseTerm "λx. x" of
        Left e  -> putStrLn $ "PARSE ERROR: " ++ e
        Right t -> putStrLn (show t)

    -- Path type  Path U0 U0 U0
    tryParse "Path U1 U0 U0"

    -- Interval pseudo-type
    tryParse "𝕀"

    -- Nested application  (Π(f:Π(x:U0).U0). U0)
    tryParse "\928(f:\928(x:U0).U0). U0"

    -- hcomp
    putStr   "  parse  hcomp U0 [i0] (⟨i⟩ U0) U0\n    => "
    case parseTerm "hcomp U0 [i0] (\8992i\8993 U0) U0" of
        Left e  -> putStrLn $ "PARSE ERROR: " ++ e
        Right t -> putStrLn (show t)

    -- Interval expression parser
    putStrLn "\n--- Interval expressions ---"
    mapM_ (\s -> case parseInterval s of
                    Left e  -> putStrLn $ "  " ++ s ++ " => ERROR: " ++ e
                    Right i -> putStrLn $ "  " ++ s ++ " => " ++ show i)
        [ "i0"
        , "i1 \8744 i2"     -- i1 ∨ i2
        , "i0 \8743 \172i1" -- i0 ∧ ¬i1
        , "0"
        , "1"
        ]