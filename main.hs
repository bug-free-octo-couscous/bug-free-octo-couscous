module Main where

type Name = String
type Index = Int

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term
    | Pi  Name Term Term
    | Universe Int          -- Hierarchy: Type 0, Type 1, etc.
    | Interval              -- The type I
    | I0                    -- The endpoint 0
    | I1                    -- The endpoint 1
    | PathP Term Term Term  -- PathP (A : I -> Type n) x y
    | PLam Term Term        -- Path abstraction: <name> e
    | PApp Term Term        -- Path application: e @ i
    deriving (Eq)

instance Show Term where
    show (Var i)       = show i
    show (App m n)     = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e)   = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)    = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show (Universe n)  = "Type" ++ show n
    show Interval      = "I"
    show I0            = "0"
    show I1            = "1"
    show (PathP a x y) = "PathP " ++ show a ++ " " ++ show x ++ " " ++ show y
    show (PLam _ e)    = "<_> " ++ show e
    show (PApp m i)    = show m ++ " @ " ++ show i

-- 1. De Bruijn Shifting and Substitution
shift :: Int -> Int -> Term -> Term
shift d c (Var i)       = if i >= c then Var (i + d) else Var i
shift d c (App m n)     = App (shift d c m) (shift d c n)
shift d c (Lam x t e)   = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)    = Pi x (shift d c t) (shift d (c + 1) b)
shift d c (PathP a x y) = PathP (shift d c a) (shift d c x) (shift d c y)
shift d c (PLam t e)    = PLam (shift d c t) (shift d (c + 1) e)
shift d c (PApp m i)    = PApp (shift d c m) (shift d c i)
shift _ _ t             = t

substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) =
    Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  =
    Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute j n (PathP a x y) = 
    PathP (substitute j n a) (substitute j n x) (substitute j n y)
substitute j n (PLam t e) = 
    PLam (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (PApp m i) = 
    PApp (substitute j n m) (substitute j n i)
substitute _ _ t = t

-- 2. Evaluation
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (PApp m i) =
    let i' = reduce i
    in case reduce m of
        PLam _ e -> case i' of
            I0 -> reduce (shift (-1) 0 (substitute 0 I0 e))
            I1 -> reduce (shift (-1) 0 (substitute 0 I1 e))
            _  -> PApp (reduce m) i'
        m' -> PApp m' i'
reduce (Pi x t b)    = Pi x (reduce t) (reduce b)
reduce (Lam x t e)   = Lam x (reduce t) (reduce e)
reduce (PathP a x y) = PathP (reduce a) (reduce x) (reduce y)
reduce (PLam t e)    = PLam (reduce t) (reduce e)
reduce x             = x

betaEquals :: Term -> Term -> Bool
betaEquals t1 t2 = reduce t1 == reduce t2

-- 3. Type Checking
type Context = [Term]

-- Helper to ensure a term is a Type_n and return n
checkIsUniverse :: Context -> Term -> Either String Int
checkIsUniverse ctx t = do
    tType <- typeOf ctx t
    case reduce tType of
        Universe n -> Right n
        _          -> Left $ "Expected a Type level, but got: " ++ show tType

typeOf :: Context -> Term -> Either String Term
typeOf _ (Universe n) = Right (Universe (n + 1))
typeOf _ Interval     = Right (Universe 0) -- I : Type 0
typeOf _ I0           = Right Interval
typeOf _ I1           = Right Interval

typeOf ctx (Var i)
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    lvlA <- checkIsUniverse ctx a
    lvlB <- checkIsUniverse (a : ctx) b
    -- Standard PTS rule for universes: max level
    return $ Universe (max lvlA lvlB)

typeOf ctx (Lam x a e) = do
    _ <- checkIsUniverse ctx a
    b <- typeOf (a : ctx) e
    return $ Pi x a b

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b ->
            if betaEquals a tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left $ "Type mismatch: expected " ++ show a ++ " but got " ++ show tN
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function"

typeOf ctx (PathP a x y) = do
    ta <- typeOf ctx a
    case reduce ta of
        -- a must be a mapping from Interval to some Type n
        Pi _ Interval (Universe n) -> do
            tx <- typeOf ctx x
            ty <- typeOf ctx y
            let type0 = reduce (App a I0)
            let type1 = reduce (App a I1)
            if betaEquals tx type0 && betaEquals ty type1
                then Right (Universe n)
                else Left "PathP boundary mismatch: endpoints do not match PathP types"
        _ -> Left "PathP requires a type family (I -> Type n)"

typeOf ctx (PLam a e) = do
    ta <- typeOf ctx a 
    case reduce ta of
        Pi _ Interval (Universe _) -> do
            -- Body e is checked with the interval variable at the top of context
            te <- typeOf (Interval : ctx) e
            let expectedBodyType = reduce (App (shift 1 0 a) (Var 0))
            if betaEquals te expectedBodyType
                then do
                    let start = reduce (shift (-1) 0 (substitute 0 I0 e))
                    let end   = reduce (shift (-1) 0 (substitute 0 I1 e))
                    return $ PathP a start end
                else Left "PLam body type does not match path type family"
        _ -> Left "PLam requires a path type family (I -> Type n)"

typeOf ctx (PApp m i) = do
    tm <- typeOf ctx m
    ti <- typeOf ctx i
    case (reduce tm, ti) of
        (PathP a _ _, Interval) -> Right (reduce (App a i))
        _ -> Left "PApp expects a Path and an Interval coordinate"

-- 4. Main Execution
main :: IO ()
main = do
    putStrLn "--- Hierarchical Cubical Type System Test ---"
    
    -- Context: A : Type 0
    let ctx = [Universe 0] 
    
    -- Path family: λi:I. A
    -- In De Bruijn, A is Var 1 (skipped over 'i')
    let aFamily = Lam "i" Interval (Var 1)
    
    -- Reflexivity for some x : A
    -- Context: x : A, A : Type 0
    let ctx2 = [Var 0, Universe 0]
    -- refl = <_> x
    let refl = PLam (shift 1 0 aFamily) (Var 1)
    
    putStrLn $ "Term: " ++ show refl
    case typeOf ctx2 refl of
        Right t -> do
            putStrLn $ "Type: " ++ show t
            putStrLn $ "Reduced @ 0: " ++ show (reduce (PApp refl I0))
            putStrLn $ "Reduced @ 1: " ++ show (reduce (PApp refl I1))
        Left e -> putStrLn $ "Error: " ++ e
-- current goal 
-- composition
-- glueing
-- de morgan algebra