import Cubical.CubicalLambda
import Parser

import Data.Char          (isSpace)
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
-- File chunking
--------------------------------------------------------------------------------

-- | Remove a trailing @--@ line comment and trim trailing whitespace.
--
--   Only the outermost @--@ is matched; this is safe because the language has
--   no string literals in which @--@ could appear.
stripLineComment :: String -> String
stripLineComment = trimRight . go
  where
    go []           = []
    go ('-':'-':_)  = []
    go (c:cs)       = c : go cs
    trimRight       = reverse . dropWhile (== ' ') . reverse

-- | Split a list into sublists at every element satisfying the predicate.
--   Consecutive separators are collapsed (empty sublists are not produced).
--   The separating elements are discarded.
splitWhen :: (a -> Bool) -> [a] -> [[a]]
splitWhen _ [] = []
splitWhen p xs =
    let (pre, rest) = break p xs
        after       = dropWhile p rest
    in  pre : splitWhen p after

-- | Partition file lines into logical statement chunks.
--
--   Rules (in priority order):
--
--   1. Genuinely blank lines (whitespace only in the original text) are
--      statement separators.  Consecutive blank lines count as one separator.
--
--   2. Comment-only lines (first non-space content is @--@) contribute
--      *nothing* to any statement — they are skipped but do NOT act as
--      separators.  This means a comment may appear inside a multi-line
--      statement without splitting it.
--
--   3. All other lines are content.  Trailing @--@ comments are stripped
--      before the text is added to the statement.
--
--   Joins surviving content lines with a single space, producing one flat
--   string that 'parseStatement' already handles (it treats all whitespace
--   uniformly).
--
--   Returns @(startLineNumber, joinedText)@ for each non-empty chunk.
chunkStatements :: [(Int, String)] -> [(Int, String)]
chunkStatements rawLines =
    [ (fst (head g), unwords (map snd g))
    | chunk <- splitWhen (isBlankLine . snd) rawLines   -- split on *original* blank lines
    , let g = [ (n, stripLineComment l)                 -- strip trailing comments from content
               | (n, l) <- chunk
               , not (isCommentLine l)                  -- skip comment-only lines
               ]
    , not (null g)                                      -- skip wholly-empty chunks
    ]
  where
    -- True when the original line is entirely whitespace (statement separator).
    isBlankLine s   = all isSpace s
    -- True when the first visible token is '--' (comment-only line; skipped).
    isCommentLine s = take 2 (dropWhile isSpace s) == "--"

--------------------------------------------------------------------------------
-- File mode
--------------------------------------------------------------------------------

processFile :: FilePath -> IO ()
processFile path = do
    contents <- readFile path
    let chunks = chunkStatements (zip [1..] (lines contents))
    putStrLn $ "=== " ++ path ++ " ===\n"
    _ <- foldl step (return []) chunks
    putStrLn ""
  where
    step mEnv (startLine, src) = do
        env <- mEnv
        processStatement env startLine src

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

usage :: String
usage = unlines
    [ "Usage:"
    , "  octo <file> ...       process statements in each file"
    , ""
    , "File format:"
    , "  def x : T = e           define x with explicit type T"
    , "  def x = e               define x (type inferred)"
    , "  check label : T = e     check e : T (no binding)"
    , "  <term>                   infer type of bare term"
    , ""
    , "  Blank lines separate statements (a statement may span many lines)."
    , "  Lines whose first non-space content is '--' are comments."
    , "  Trailing '--' comments on any line are also stripped."
    ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        []    -> putStr usage
        files -> mapM_ processFile files