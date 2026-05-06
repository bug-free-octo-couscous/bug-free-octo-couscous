import CubicalLambda
import Parser

import System.Environment (getArgs)
import System.IO          (hPutStrLn, stderr)

--------------------------------------------------------------------------------
-- Term checking
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

--------------------------------------------------------------------------------
-- File mode
-- Each non-empty, non-comment line is treated as one term.
-- Lines starting with '--' are comments and are skipped.
--------------------------------------------------------------------------------

processFile :: FilePath -> IO ()
processFile path = do
    contents <- readFile path
    let ls = zip [1..] (lines contents)
    putStrLn $ "=== " ++ path ++ " ===\n"
    mapM_ processLine ls
    putStrLn ""
  where
    processLine (_, "")          = return ()
    processLine (_, ('-':'-':_)) = return ()
    processLine (n, line)        = do
        putStr $ "[line " ++ show (n :: Int) ++ "] "
        tryParse line

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

usage :: String
usage = unlines
    [ "Usage:"
    , "  cubical <file> ...       check every term in each file"
    , ""
    , "File format:"
    , "  One term per line."
    , "  Lines starting with '--' are comments."
    , "  Blank lines are ignored."
    ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> putStr usage
        files      -> mapM_ processFile files