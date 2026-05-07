import CubicalLambda
import Parser

import System.Environment (getArgs)

--------------------------------------------------------------------------------
-- Statement processing with persistent GlobalEnv
--------------------------------------------------------------------------------

globalNames :: GlobalEnv -> [Name]
globalNames genv = map (\(n,_,_) -> n) (reverse genv)

processStatement :: GlobalEnv -> Int -> String -> IO GlobalEnv
processStatement genv lineNum src = do
    putStr $ "[line " ++ show lineNum ++ "] "
    case parseStatement genv src of
        Left err -> do
            putStrLn $ "PARSE ERROR: " ++ err
            return genv

        Right (STerm t) -> do
            putStr $ "infer  " ++ showTerm (globalNames genv) t ++ "\n    => "
            case inferWithEnv genv t of
                Right ty -> putStrLn $ showTerm (globalNames genv) (eval ty)
                Left err -> putStrLn $ "TYPE ERROR: " ++ show err
            return genv

        Right (SDef x mTy val) -> do
            case mTy of
                Nothing ->
                    case inferWithEnv genv val of
                        Left err -> do
                            putStrLn $ "TYPE ERROR in def " ++ x ++ ": " ++ show err
                            return genv
                        Right ty -> do
                            let ty'  = eval (applyGlobals genv ty)
                                val' = eval (applyGlobals genv val)
                            putStrLn $ "def " ++ x ++ " : " ++ showTerm (globalNames genv) ty'
                            return ((x, ty', val') : genv)
                Just tyAnn ->
                    case checkWithEnv genv val tyAnn of
                        Left err -> do
                            putStrLn $ "TYPE ERROR in def " ++ x ++ ": " ++ show err
                            return genv
                        Right () -> do
                            let ty'  = eval (applyGlobals genv tyAnn)
                                val' = eval (applyGlobals genv val)
                            putStrLn $ "def " ++ x ++ " : " ++ showTerm (globalNames genv) ty'
                            return ((x, ty', val') : genv)

        Right (SCheck label ty val) -> do
            case checkWithEnv genv val ty of
                Left err ->
                    putStrLn $ "  ✗  " ++ label ++ ": " ++ show err
                Right () ->
                    putStrLn $ "  ✓  " ++ label
                                ++ "\n       : " ++ showTerm (globalNames genv) (eval (applyGlobals genv ty))
            return genv

--------------------------------------------------------------------------------
-- File mode
--------------------------------------------------------------------------------

processFile :: FilePath -> IO ()
processFile path = do
    contents <- readFile path
    let ls = zip [1..] (lines contents)
    putStrLn $ "=== " ++ path ++ " ===\n"
    _ <- foldl step (return []) ls
    putStrLn ""
  where
    step mEnv (n, line)
        | null (dropWhile (== ' ') line)                   = mEnv
        | take 2 (dropWhile (== ' ') line) == "--"         = mEnv
        | otherwise = do
            env <- mEnv
            processStatement env n line

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

usage :: String
usage = unlines
    [ "Usage:"
    , "  cubical <file> ...       process statements in each file"
    , ""
    , "File format:"
    , "  def x : T = e           define x with explicit type T"
    , "  def x = e               define x (type inferred)"
    , "  check label : T = e     check e : T (no binding)"
    , "  <term>                   infer type of bare term"
    , "  Lines starting with '--' are comments."
    , "  Blank lines are ignored."
    ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        []    -> putStr usage
        files -> mapM_ processFile files