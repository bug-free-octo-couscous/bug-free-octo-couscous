module Main where

import Data.List (find)

type Name = String
type Index = Int

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term
    | Pi  Name Term Term
    | Universe Int          
    | Interval              
    | I0                    
    | I1                    
    | PathP Term Term Term  
    | PLam Term Term        
    | PApp Term Term        
    | Glue Term Term Term   
    | Total Term Term Term  
    | Unglue Term Term      
    | IAnd Term Term        
    | IOr  Term Term        
    | INot Term             
    | Partial Term Term      
    | Side Term [(Term, Term)] 
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
    show (IAnd p q)    = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
    show (IOr p q)     = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
    show (INot p)      = "¬" ++ show p
    show (Partial p a) = "Partial " ++ show p ++ " " ++ show a
    show (Side _ bs)   = "[" ++ concatMap (\(p,t) -> show p ++ " -> " ++ show t ++ ", ") bs ++ "]"
    show (Glue a p f)  = "Glue " ++ show a ++ " " ++ show p ++ " " ++ show f
    show (Total p t a) = "total [" ++ show p ++ " -> " ++ show t ++ "] " ++ show a
    show (Unglue t p)  = "unglue " ++ show t ++ " " ++ show p

-- 1. De Bruijn Shifting and Substitution
shift :: Int -> Int -> Term -> Term
shift d c (Var i)       = if i >= c then Var (i + d) else Var i
shift d c (App m n)     = App (shift d c m) (shift d c n)
shift d c (Lam x t e)   = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)    = Pi x (shift d c t) (shift d (c + 1) b)
shift d c (PathP a x y) = PathP (shift d c a) (shift d c x) (shift d c y)
shift d c (PLam t e)    = PLam (shift d c t) (shift d (c + 1) e)
shift d c (PApp m i)    = PApp (shift d c m) (shift d c i)
shift d c (Glue a phi f)   = Glue (shift d c a) (shift d c phi) (shift d c f)
shift d c (Total phi t a)  = Total (shift d c phi) (shift d c t) (shift d c a)
shift d c (Unglue t phi)   = Unglue (shift d c t) (shift d c phi)
shift d c (Partial phi a)  = Partial (shift d c phi) (shift d c a)
shift d c (Side phi bs)    = Side (shift d c phi) [(shift d c p, shift d c t) | (p, t) <- bs]
shift d c (IAnd p q)       = IAnd (shift d c p) (shift d c q)
shift d c (IOr p q)        = IOr (shift d c p) (shift d c q)
shift d c (INot p)         = INot (shift d c p)
shift _ _ t                = t

substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) = Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  = Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute j n (PathP a x y) = PathP (substitute j n a) (substitute j n x) (substitute j n y)
substitute j n (PLam t e) = PLam (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (PApp m i) = PApp (substitute j n m) (substitute j n i)
substitute j n (Glue a p f)  = Glue (substitute j n a) (substitute j n p) (substitute j n f)
substitute j n (Total p t a) = Total (substitute j n p) (substitute j n t) (substitute j n a)
substitute j n (Unglue t p)  = Unglue (substitute j n t) (substitute j n p)
substitute j n (Partial p a) = Partial (substitute j n p) (substitute j n a)
substitute j n (Side p bs)   = Side (substitute j n p) [(substitute j n bp, substitute j n bt) | (bp, bt) <- bs]
substitute j n (IAnd p q)    = IAnd (substitute j n p) (substitute j n q)
substitute j n (IOr p q)     = IOr (substitute j n p) (substitute j n q)
substitute j n (INot p)      = INot (substitute j n p)
substitute _ _ t = t

-- 2. Evaluation
reduceFormula :: Term -> Term
reduceFormula I0 = I0
reduceFormula I1 = I1
reduceFormula (IAnd p1 p2) = case (reduceFormula p1, reduceFormula p2) of
    (I1, x) -> x
    (x, I1) -> x
    (I0, _) -> I0
    (_, I0) -> I0
    (a, b)  -> if a == b then a else IAnd a b
reduceFormula (IOr p1 p2) = case (reduceFormula p1, reduceFormula p2) of
    (I1, _) -> I1
    (_, I1) -> I1
    (I0, x) -> x
    (x, I0) -> x
    (a, b)  -> if a == b then a else IOr a b
reduceFormula (INot p) = case reduceFormula p of
    I1 -> I0
    I0 -> I1
    p' -> INot p'
reduceFormula x = x

reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (PApp m i) =
    let i' = reduce i
    in case reduce m of
        PLam _ e -> reduce (shift (-1) 0 (substitute 0 i' e))
        m'       -> PApp m' i'
reduce (Unglue t phi) =
    let t' = reduce t
        p' = reduceFormula phi
    in case p' of
        I1 -> case t' of
                Total _ (Side _ branches) _ -> 
                    case find (\(bp, _) -> reduceFormula bp == I1) branches of
                        Just (_, term) -> reduce term
                        Nothing        -> Unglue t' p'
                Total _ u _ -> reduce u
                _           -> Unglue t' p'
        I0 -> case t' of
                Total _ _ a -> reduce a
                _           -> Unglue t' p'
        _ -> Unglue t' p'
reduce (Total phi t a) = 
    let p' = reduceFormula phi
    in case p' of
        I1 -> reduce t 
        _  -> Total p' (reduce t) (reduce a)
reduce (Pi x t b)    = Pi x (reduce t) (reduce b)
reduce (Lam x t e)   = Lam x (reduce t) (reduce e)
reduce (PathP a x y) = PathP (reduce a) (reduce x) (reduce y)
reduce (PLam t e)    = PLam (reduce t) (reduce e)
reduce (Glue a p f)  = Glue (reduce a) (reduceFormula p) (reduce f)
reduce (Partial p a) = Partial (reduceFormula p) (reduce a)
reduce (Side p bs)   = Side (reduceFormula p) [(reduceFormula bp, reduce bt) | (bp, bt) <- bs]
reduce (IAnd p q)    = reduceFormula (IAnd p q)
reduce (IOr p q)     = reduceFormula (IOr p q)
reduce (INot p)      = reduceFormula (INot p)
reduce x             = x

betaEquals :: Term -> Term -> Bool
betaEquals t1 t2 = reduce t1 == reduce t2

-- 3. Type Checking
type Context = [Term]

isFormula :: Context -> Term -> Bool
isFormula ctx t = case reduce t of
    I0          -> True
    I1          -> True
    Var i       -> i < length ctx && (reduce (shift (i + 1) 0 (ctx !! i)) == Interval)
    IAnd p1 p2  -> isFormula ctx p1 && isFormula ctx p2
    IOr  p1 p2  -> isFormula ctx p1 && isFormula ctx p2
    INot p      -> isFormula ctx p
    _           -> False

checkIsUniverse :: Context -> Term -> Either String Int
checkIsUniverse ctx t = do
    tType <- typeOf ctx t
    case reduce tType of
        Universe n -> Right n
        _          -> Left $ "Expected a Type, but got: " ++ show tType

typeOf :: Context -> Term -> Either String Term
typeOf _ (Universe n) = Right (Universe (n + 1))
typeOf _ Interval     = Right (Universe 0)
typeOf _ I0           = Right Interval
typeOf _ I1           = Right Interval

typeOf ctx (Var i)
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    lvlA <- checkIsUniverse ctx a
    lvlB <- checkIsUniverse (a : ctx) b
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
        Pi _ Interval (Universe n) -> do
            tx <- typeOf ctx x
            ty <- typeOf ctx y
            if betaEquals tx (reduce (App a I0)) && betaEquals ty (reduce (App a I1))
                then Right (Universe n)
                else Left "PathP boundary mismatch"
        _ -> Left "PathP requires a type family (I -> Type)"

typeOf ctx (PLam a e) = do
    ta <- typeOf ctx a 
    case reduce ta of
        Pi _ Interval (Universe _) -> do
            te <- typeOf (Interval : ctx) e
            if betaEquals te (reduce (App (shift 1 0 a) (Var 0)))
                then return $ PathP a (shift (-1) 0 (substitute 0 I0 e)) (shift (-1) 0 (substitute 0 I1 e))
                else Left "PLam body type mismatch"
        _ -> Left "PLam requires a path type family"

typeOf ctx (PApp m i) = do
    tm <- typeOf ctx m
    ti <- typeOf ctx i
    case (reduce tm, ti) of
        (PathP a _ _, Interval) -> Right (reduce (App a i))
        _ -> Left "PApp expects a Path and an Interval coordinate"

typeOf ctx (IAnd p q) = if isFormula ctx p && isFormula ctx q then Right Interval else Left "Invalid formula"
typeOf ctx (IOr p q)  = if isFormula ctx p && isFormula ctx q then Right Interval else Left "Invalid formula"
typeOf ctx (INot p)   = if isFormula ctx p then Right Interval else Left "Invalid formula"

typeOf ctx (Partial phi a) = do
    if not (isFormula ctx phi) then Left "Partial requires a formula"
    else do
        _ <- checkIsUniverse ctx a
        return (Universe 0)

typeOf ctx (Side phi bs) = do
    if not (isFormula ctx phi) then Left "Side requires a formula"
    else case bs of
        [] -> Left "Empty side"
        ((p, t):_) -> do
            ty <- typeOf ctx t
            return (Partial phi ty)

typeOf ctx (Glue a phi f) = do
    lvlA <- checkIsUniverse ctx a
    if not (isFormula ctx phi) then Left "Cofibration must be a formula"
    else do
        tf <- typeOf ctx f
        case reduce tf of
            Partial p _ | betaEquals p phi -> Right (Universe lvlA)
            _ -> Left "Glue expected partial element matching phi"

typeOf ctx (Total phi t a) = do
    ta <- typeOf ctx a
    return $ Glue ta phi t
    
typeOf ctx (Unglue t phi) = do
    tt <- typeOf ctx t
    case reduce tt of
        Glue b _ _ -> Right b
        _ -> Left "Unglue expects a Glue type"

-- 4. Main Execution
main :: IO ()
main = do
    putStrLn "--- Cubical Type System Test ---"
    
    let ctx = [Universe 0] 
    let aFamily = Lam "i" Interval (Var 1)
    let ctx2 = [Var 0, Universe 0]
    let refl = PLam (shift 1 0 aFamily) (Var 1)
    
    putStrLn $ "Refl Term: " ++ show refl
    case typeOf ctx2 refl of
        Right t -> putStrLn $ "Refl Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e

    putStrLn "\n--- Formula Test ---"
    let f1 = IAnd I1 I0
    let f2 = IOr (IAnd I1 I1) I0
    putStrLn $ "Formula 1 (1 ∧ 0): " ++ show (reduceFormula f1)
    putStrLn $ "Formula 2 ((1 ∧ 1) ∨ 0): " ++ show (reduceFormula f2)

-- current goal 
-- composition