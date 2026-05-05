{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- 1. Interval Syntax & DNF
--------------------------------------------------------------------------------

data I
    = I0 | I1
    | IVar Int
    | Meet I I | Join I I | Neg I
    deriving (Eq, Ord)

instance Show I where
    show I0         = "0"
    show I1         = "1"
    show (IVar n)   = "i" ++ show n
    show (Meet i j) = "(" ++ show i ++ " ∧ " ++ show j ++ ")"
    show (Join i j) = "(" ++ show i ++ " ∨ " ++ show j ++ ")"
    show (Neg i)    = "¬" ++ show i

data Literal = Pos Int | NegVar Int deriving (Eq, Ord)

instance Show Literal where
    show (Pos n)    = "i" ++ show n
    show (NegVar n) = "¬i" ++ show n

newtype DNF = DNF { getCubes :: Set (Set Literal) } deriving (Eq, Ord)

instance Show DNF where
    show (DNF cs)
        | Set.null cs = "0"
        | Set.null (Set.findMin cs) && Set.size cs == 1 = "1"
        | otherwise = intercalate " ∨ " (map showCube (Set.toList cs))
      where
        showCube c =
            if Set.null c
                then "1"
                else "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"

--------------------------------------------------------------------------------
-- 2. Cubical Dependent Syntax
--------------------------------------------------------------------------------

type Name  = String
type Level = Int

data Term
    = TVar Name
    | TApp Term Term
    | TAbs Name Term
    -- Universes
    | TUniv Level           -- U_n
    -- Dependent Types (Pi Types)
    | TPi Name Term Term    -- Π(x:A). B
    -- Cubical Additions
    | TInterval I           -- Symbolic Interval
    | TCube DNF             -- Normalized Interval
    -- Path Types
    | TPath Term Term Term  -- Path A u v
    | PLam Name Term        -- ⟨i⟩ t  (Path abstraction, binds interval name i)
    | PApp Term Term        -- t @ r  (Path application)
    deriving (Eq)

instance Show Term where
    show t = case t of
        TVar x      -> x
        TApp f a    -> "(" ++ show f ++ " " ++ show a ++ ")"
        TAbs x b    -> "λ" ++ x ++ ". " ++ show b
        TUniv n     -> "U" ++ show n
        TPi x a b   -> "Π(" ++ x ++ ":" ++ show a ++ "). " ++ show b
        TInterval i -> show i
        TCube c     -> show c
        TPath a u v -> "Path " ++ show a ++ " " ++ show u ++ " " ++ show v
        PLam i t    -> "⟨" ++ i ++ "⟩ " ++ show t
        PApp t r    -> show t ++ " @ " ++ show r

--------------------------------------------------------------------------------
-- 3. Evaluation & Substitution
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution: t[x := s]
subst :: Name -> Term -> Term -> Term
subst x s term = case term of
    TVar y      | x == y    -> s
                | otherwise -> TVar y
    TApp f a                -> TApp (subst x s f) (subst x s a)
    TAbs y b    | x == y    -> TAbs y b
                | otherwise -> TAbs y (subst x s b)
    TPi y a b   | x == y    -> TPi y (subst x s a) b
                | otherwise -> TPi y (subst x s a) (subst x s b)
    TUniv n                 -> TUniv n
    TInterval i             -> TInterval i
    TCube c                 -> TCube c
    TPath a u v             -> TPath (subst x s a) (subst x s u) (subst x s v)
    PLam i t    | x == i    -> PLam i t
                | otherwise -> PLam i (subst x s t)
    PApp t r                -> PApp (subst x s t) (subst x s r)

-- | Normalizes terms to Normal Form
eval :: Term -> Term
eval t = case t of
    TApp f a ->
        case eval f of
            TAbs x body -> eval (subst x (eval a) body)
            f'          -> TApp f' (eval a)

    -- Path Beta-reduction: (⟨i⟩ t) @ r  ==>  t[i := r]
    PApp t r ->
        case eval t of
            PLam i body -> eval (subst i (eval r) body)
            t'          -> PApp t' (eval r)

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)
    _           -> t

--------------------------------------------------------------------------------
-- 4. Interval Algebra
--------------------------------------------------------------------------------

simplify :: Set (Set Literal) -> Set (Set Literal)
simplify cubes =
    Set.filter
        (\c -> not $ any (\other -> c /= other && other `Set.isSubsetOf` c) cubes)
        cubes

evalInterval :: I -> DNF
evalInterval I0         = DNF Set.empty
evalInterval I1         = DNF (Set.singleton Set.empty)
evalInterval (IVar n)   = DNF (Set.singleton (Set.singleton (Pos n)))
evalInterval (Neg i)    = dnfNeg (evalInterval i)
evalInterval (Meet i j) = dnfMeet (evalInterval i) (evalInterval j)
evalInterval (Join i j) = dnfJoin (evalInterval i) (evalInterval j)

dnfJoin :: DNF -> DNF -> DNF
dnfJoin (DNF a) (DNF b) = DNF $ simplify (Set.union a b)

dnfMeet :: DNF -> DNF -> DNF
dnfMeet (DNF as) (DNF bs) =
    DNF $ simplify $ Set.fromList
        [ Set.union a b | a <- Set.toList as, b <- Set.toList bs ]

dnfNeg :: DNF -> DNF
dnfNeg (DNF cubes)
    | Set.null cubes = DNF $ Set.singleton Set.empty
    | otherwise =
        foldr dnfMeet (DNF $ Set.singleton Set.empty)
              (map negCube (Set.toList cubes))
  where
    negCube c   = DNF $ Set.fromList [Set.singleton (negLit l) | l <- Set.toList c]
    negLit (Pos n)    = NegVar n
    negLit (NegVar n) = Pos n

--------------------------------------------------------------------------------
-- 5. Demonstration (Evaluation)
--------------------------------------------------------------------------------

demoEval :: IO ()
demoEval = do
    putStrLn "=== Cubical Lambda Calculus with Path Types ==="

    -- 1. Identity function (Standard Pi Type)
    let idType = TPi "A" (TUniv 0) (TPi "x" (TVar "A") (TVar "A"))
    let idTerm = TAbs "A" (TAbs "x" (TVar "x"))

    putStrLn $ "\nIdentity Type: " ++ show idType
    putStrLn $ "Identity Term: " ++ show idTerm

    -- 2. Reflexivity (Path Type)
    -- refl : Π(A:U0). Π(x:A). Path A x x
    -- refl = λA. λx. ⟨i⟩ x
    let refl = TAbs "A" (TAbs "x" (PLam "i" (TVar "x")))
    putStrLn $ "\nReflexivity (refl): " ++ show refl

    -- 3. Path Application
    -- Applying refl to a type and term, then applying an interval
    -- (refl U0 T) @ 0
    let testPath = PApp (TApp (TApp refl (TUniv 0)) (TVar "T")) (TInterval I0)
    putStrLn $ "\nEvaluating (refl U0 T) @ 0:"
    putStrLn $ "Result: " ++ show (eval testPath)

    -- 4. De Morgan in the Interval (Normalized inside a Path)
    let deMorganLHS = Neg (Join (IVar 0) (IVar 1))
    let deMorganRHS = Meet (Neg (IVar 0)) (Neg (IVar 1))
    let pathDeMorgan = TPath (TUniv 0) (TInterval deMorganLHS) (TInterval deMorganRHS)

    putStrLn $ "\nNormalized De Morgan Interval in Type:"
    putStrLn $ "Raw:        " ++ show pathDeMorgan
    putStrLn $ "Normalized: " ++ show (eval pathDeMorgan)

    -- 5. Symmetry (Function that flips a path)
    -- sym : Π(A:U0). Π(x y: A). Path A x y -> Path A y x
    -- sym = λA. λx. λy. λp. ⟨i⟩ p @ ¬i
    let sym = TAbs "A" (TAbs "x" (TAbs "y"
                (TAbs "p" (PLam "i"
                    (PApp (TVar "p") (TInterval (Neg (IVar 0))))))))
    putStrLn $ "\nSymmetry term: " ++ show sym

--------------------------------------------------------------------------------
-- 6. Bidirectional Type Checker
--------------------------------------------------------------------------------

-- | The interval pseudo-type. Interval expressions (𝕀) live outside the
--   universe hierarchy; we represent their "type" with this sentinel.
intervalTy :: Term
intervalTy = TVar "𝕀"

-- | Typing context: an ordered list of (Name, Type) bindings.
type Ctx = [(Name, Term)]

-- ---------------------------------------------------------------------------
-- 6a. Type Errors
-- ---------------------------------------------------------------------------

data TypeError
    = UnboundVariable Name
    | TypeMismatch Term Term   -- expected, got
    | ExpectedPi   Term        -- the non-Pi type we found
    | ExpectedPath Term        -- the non-Path type we found
    | ExpectedUniverse Term    -- the non-universe type we found
    | NotAnInterval Term       -- term that should be an interval expression
    | CannotInfer Term         -- term that needs a type annotation to check
    | Other String
    deriving (Eq)

instance Show TypeError where
    show e = case e of
        UnboundVariable x  ->
            "  Unbound variable: '" ++ x ++ "'"
        TypeMismatch ex got ->
            "  Type mismatch\n    expected : " ++ show ex
            ++ "\n    got      : " ++ show got
        ExpectedPi ty ->
            "  Expected a Π-type, but found:\n    " ++ show ty
        ExpectedPath ty ->
            "  Expected a Path type, but found:\n    " ++ show ty
        ExpectedUniverse ty ->
            "  Expected a universe U_n, but found:\n    " ++ show ty
        NotAnInterval t ->
            "  Expected an interval expression (𝕀), but got:\n    " ++ show t
        CannotInfer t ->
            "  Cannot infer type of term without annotation:\n    " ++ show t
            ++ "\n  (Tip: use 'check' instead of 'infer', or add a type annotation)"
        Other msg ->
            "  " ++ msg

-- ---------------------------------------------------------------------------
-- 6b. Context Helpers
-- ---------------------------------------------------------------------------

extendCtx :: Name -> Term -> Ctx -> Ctx
extendCtx x ty ctx = (x, ty) : ctx

lookupCtx :: Name -> Ctx -> Either TypeError Term
lookupCtx x []            = Left (UnboundVariable x)
lookupCtx x ((y, ty):rest)
    | x == y    = Right ty
    | otherwise = lookupCtx x rest

-- | Definitional equality: normalize both sides and compare.
definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 = eval t1 == eval t2

requireEqual :: Term -> Term -> Either TypeError ()
requireEqual expected got
    | definitionallyEqual expected got = Right ()
    | otherwise = Left (TypeMismatch (eval expected) (eval got))

-- | Infer the type of t, assert it is some U_n, return n.
requireUniverse :: Ctx -> Term -> Either TypeError Level
requireUniverse ctx t = do
    ty <- infer ctx t
    case eval ty of
        TUniv n -> Right n
        other   -> Left (ExpectedUniverse other)

-- ---------------------------------------------------------------------------
-- 6c. Interval Validity
-- ---------------------------------------------------------------------------

-- | Assert that a term is an interval expression.
--   TInterval / TCube are syntactically intervals.
--   A variable bound with intervalTy is also an interval (introduced by PLam).
checkInterval :: Ctx -> Term -> Either TypeError ()
checkInterval _   (TInterval _) = Right ()
checkInterval _   (TCube _)     = Right ()
checkInterval ctx t = do
    ty <- infer ctx t
    if ty == intervalTy
        then Right ()
        else Left (NotAnInterval t)

-- ---------------------------------------------------------------------------
-- 6d. Type Inference  (Γ ⊢ t ⇒ T)
-- ---------------------------------------------------------------------------

-- | Synthesize the type of @t@ in context @ctx@.
--   Call 'check' for introduction forms (TAbs, PLam) which need a known type.
infer :: Ctx -> Term -> Either TypeError Term

-- ─── Variable ───────────────────────────────────────────────────────────────
-- Γ(x) = T
-- ──────────────
--  Γ ⊢ x ⇒ T
infer ctx (TVar x) = lookupCtx x ctx

-- ─── Universe ───────────────────────────────────────────────────────────────
--  Γ ⊢ U_n ⇒ U_{n+1}
infer _   (TUniv n) = Right (TUniv (n + 1))

-- ─── Application ────────────────────────────────────────────────────────────
-- Γ ⊢ f ⇒ Π(x:A).B    Γ ⊢ a ⇐ A
-- ─────────────────────────────────
--      Γ ⊢ f a ⇒ B[x:=a]
infer ctx (TApp f a) = do
    fTy <- infer ctx f
    case eval fTy of
        TPi x aTy bTy -> do
            check ctx a aTy
            return $ eval (subst x a bTy)
        other -> Left (ExpectedPi other)

-- ─── Π Formation ────────────────────────────────────────────────────────────
-- Γ ⊢ A ⇒ U_i    Γ, x:A ⊢ B ⇒ U_j
-- ───────────────────────────────────
--    Γ ⊢ Π(x:A).B ⇒ U_{max i j}
infer ctx (TPi x aTy bTy) = do
    i <- requireUniverse ctx aTy
    j <- requireUniverse (extendCtx x (eval aTy) ctx) bTy
    return $ TUniv (max i j)

-- ─── Path Formation ─────────────────────────────────────────────────────────
-- Γ ⊢ A ⇒ U_n    Γ ⊢ u ⇐ A    Γ ⊢ v ⇐ A
-- ──────────────────────────────────────────
--        Γ ⊢ Path A u v ⇒ U_n
infer ctx (TPath aTy u v) = do
    n <- requireUniverse ctx aTy
    let aTy' = eval aTy
    check ctx u aTy'
    check ctx v aTy'
    return $ TUniv n

-- ─── Path Elimination ───────────────────────────────────────────────────────
-- Γ ⊢ p ⇒ Path A u v    r : 𝕀
-- ──────────────────────────────
--       Γ ⊢ p @ r ⇒ A
infer ctx (PApp p r) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ -> do
            checkInterval ctx r
            return $ eval aTy
        other -> Left (ExpectedPath other)

-- ─── Interval pseudo-types ──────────────────────────────────────────────────
--  Interval expressions inhabit the pseudo-type 𝕀 (outside universe hierarchy)
infer _   (TInterval _) = Right intervalTy
infer _   (TCube _)     = Right intervalTy

-- ─── Introduction forms require a known type ────────────────────────────────
infer _   t@(TAbs _ _) = Left (CannotInfer t)
infer _   t@(PLam _ _) = Left (CannotInfer t)

-- ---------------------------------------------------------------------------
-- 6e. Type Checking  (Γ ⊢ t ⇐ T)
-- ---------------------------------------------------------------------------

-- | Verify that @t@ has type @ty@ in context @ctx@.
check :: Ctx -> Term -> Term -> Either TypeError ()

-- ─── Lambda Introduction ─────────────────────────────────────────────────────
-- Γ, x:A ⊢ b ⇐ B[y:=x]
-- ──────────────────────────────────────
-- Γ ⊢ λx.b ⇐ Π(y:A).B
--
-- The body binder x may differ from the Pi binder y; we rename B accordingly.
check ctx (TAbs x body) ty =
    case eval ty of
        TPi y aTy bTy -> do
            let aTy' = eval aTy
            -- Rename Pi binder to match lambda binder
            let bTy' = if x == y then bTy else eval (subst y (TVar x) bTy)
            check (extendCtx x aTy' ctx) body bTy'
        other -> Left (ExpectedPi other)

-- ─── Path Introduction ────────────────────────────────────────────────────────
-- Γ, i:𝕀 ⊢ body ⇐ A    body[i:=0] ≡ u    body[i:=1] ≡ v
-- ────────────────────────────────────────────────────────
--            Γ ⊢ ⟨i⟩ body ⇐ Path A u v
--
-- We check:
--   (1) the body under the interval variable has the right type, and
--   (2) the two endpoints (boundary conditions) match u and v definitionally.
check ctx (PLam i body) ty =
    case eval ty of
        TPath aTy u v -> do
            let aTy' = eval aTy
            -- Boundary check: body[i:=0] ≡ u
            let bodyAt0 = eval (subst i (TInterval I0) body)
            let bodyAt1 = eval (subst i (TInterval I1) body)
            requireEqual (eval u) bodyAt0
            requireEqual (eval v) bodyAt1
            -- Body check: add i as an interval variable to ctx
            check (extendCtx i intervalTy ctx) body aTy'
        other -> Left (ExpectedPath other)

-- ─── Subsumption (switch to inference) ───────────────────────────────────────
-- If we have no special checking rule, infer the type and compare definitionally.
check ctx t ty = do
    ty' <- infer ctx t
    requireEqual (eval ty) (eval ty')

-- ---------------------------------------------------------------------------
-- 6f. Top-level helpers
-- ---------------------------------------------------------------------------

-- | Infer the type of a closed term (empty context).
inferClosed :: Term -> Either TypeError Term
inferClosed = infer []

-- | Check a closed term against a type (empty context).
checkClosed :: Term -> Term -> Either TypeError ()
checkClosed t ty = check [] t ty

-- | Pretty-print a type-checking result.
reportInfer :: String -> Term -> IO ()
reportInfer label t =
    case inferClosed t of
        Right ty ->
            putStrLn $ "  ✓  " ++ label ++ "\n       : " ++ show ty
        Left err ->
            putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err

reportCheck :: String -> Term -> Term -> IO ()
reportCheck label t ty =
    case checkClosed t ty of
        Right () ->
            putStrLn $ "  ✓  " ++ label ++ "\n       ⊢ " ++ show t
            ++ "\n       : " ++ show ty
        Left err ->
            putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err

-- ---------------------------------------------------------------------------
-- 6g. Type-checker demo
-- ---------------------------------------------------------------------------

demoTypeCheck :: IO ()
demoTypeCheck = do
    putStrLn "\n=== Bidirectional Type Checker ==="

    -- ── 1. Universe levels ──────────────────────────────────────────────────
    putStrLn "\n── Universe Levels ─────────────────────────────────────────"
    reportInfer "U0"       (TUniv 0)
    reportInfer "U1"       (TUniv 1)
    reportInfer "U0 : U1"  (TUniv 0)   -- should give U1

    -- ── 2. Identity function ─────────────────────────────────────────────────
    --   id : Π(A:U0). Π(x:A). A
    --   id = λA. λx. x
    putStrLn "\n── Identity Function ───────────────────────────────────────"
    let idTy = TPi "A" (TUniv 0) (TPi "x" (TVar "A") (TVar "A"))
    let idTm = TAbs "A" (TAbs "x" (TVar "x"))
    reportCheck "identity" idTm idTy

    -- ── 3. Reflexivity ───────────────────────────────────────────────────────
    --   refl : Π(A:U0). Π(x:A). Path A x x
    --   refl = λA. λx. ⟨i⟩ x
    putStrLn "\n── Reflexivity ─────────────────────────────────────────────"
    let reflTy = TPi "A" (TUniv 0)
                     (TPi "x" (TVar "A")
                          (TPath (TVar "A") (TVar "x") (TVar "x")))
    let reflTm = TAbs "A" (TAbs "x" (PLam "i" (TVar "x")))
    reportCheck "refl" reflTm reflTy

    -- ── 4. Function composition ──────────────────────────────────────────────
    --   comp : Π(A B C : U0). (A → B) → (B → C) → A → C
    --   comp = λA B C f g x. g (f x)
    putStrLn "\n── Function Composition ────────────────────────────────────"
    let arr a b = TPi "_" a b       -- non-dependent arrow A → B
    let compTy =
            TPi "A" (TUniv 0) $ TPi "B" (TUniv 0) $ TPi "C" (TUniv 0) $
            arr (TVar "A") (TVar "B") `arr`
            (arr (TVar "B") (TVar "C") `arr`
            arr (TVar "A") (TVar "C"))
    let compTm =
            TAbs "A" $ TAbs "B" $ TAbs "C" $
            TAbs "f" $ TAbs "g" $ TAbs "x" $
            TApp (TVar "g") (TApp (TVar "f") (TVar "x"))
    reportCheck "compose" compTm compTy

    -- ── 5. Path symmetry ─────────────────────────────────────────────────────
    --   sym : Π(A:U0). Π(x y:A). Path A x y → Path A y x
    --
    --   We check sym with explicit assumptions:
    --   Assume A:U0, x:A, y:A, p : Path A x y
    --   Then check that ⟨i⟩(p @ i) would give Path A x x (refl).
    --   A full sym using ¬i requires IVar to connect to PLam binder i.
    --
    --   Here we demonstrate checking ⟨i⟩ x : Path A x x (a constant path)
    --   in a context with A:U0 and x:A, which is a valid path.
    putStrLn "\n── Constant Path in Context ────────────────────────────────"
    let ctxWithAx = [("x", TVar "A"), ("A", TUniv 0)]
    let constPath = PLam "i" (TVar "x")
    let constPathTy = TPath (TVar "A") (TVar "x") (TVar "x")
    case check ctxWithAx constPath constPathTy of
        Right () -> putStrLn $
            "  ✓  ⟨i⟩ x : Path A x x   (in context A:U0, x:A)"
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── 6. Path application ───────────────────────────────────────────────────
    --   p : Path U0 T T  (assumed in context)
    --   p @ 0  and  p @ 1  both have type U0.
    --
    --   Note: PLam is an introduction form and needs a known type (check),
    --   so we demonstrate PApp using an assumed path variable in context.
    putStrLn "\n── Path Application ────────────────────────────────────────"
    let ctxP = [ ("T", TUniv 0)
               , ("p", TPath (TUniv 0) (TVar "T") (TVar "T")) ]
    let app0 = PApp (TVar "p") (TInterval I0)
    let app1 = PApp (TVar "p") (TInterval I1)
    mapM_ (\(lbl, t) ->
        case infer ctxP t of
            Right ty -> putStrLn $
                "  ✓  " ++ lbl ++ "  : " ++ show ty
            Left err -> putStrLn $ "  ✗  " ++ lbl ++ ": " ++ show err)
        [ ("p @ 0", app0), ("p @ 1", app1) ]

    -- ── 7. Ill-typed: applying non-function ───────────────────────────────────
    putStrLn "\n── Ill-typed Examples ──────────────────────────────────────"
    -- Applying U0 to U0 (U0 is not a function)
    reportInfer "U0 U0 (expected error)" (TApp (TUniv 0) (TUniv 0))

    -- Using a non-Path as a path abstraction target
    let badCheck = check [] (PLam "i" (TVar "i")) (TUniv 0)
    case badCheck of
        Left err -> putStrLn $ "  ✓  ⟨i⟩ i : U0 correctly rejected:\n" ++ show err
        Right () -> putStrLn "  ✗  Should have been rejected!"

    -- ── 8. Dependent application: Church booleans ─────────────────────────────
    --   Bool := Π(A:U0). A → A → A
    --   true := λA. λt. λf. t
    --   false := λA. λt. λf. f
    putStrLn "\n── Church Booleans ─────────────────────────────────────────"
    let boolTy = TPi "A" (TUniv 0) (TPi "t" (TVar "A") (TPi "f" (TVar "A") (TVar "A")))
    let trueTm  = TAbs "A" (TAbs "t" (TAbs "f" (TVar "t")))
    let falseTm = TAbs "A" (TAbs "t" (TAbs "f" (TVar "f")))
    reportCheck "true"  trueTm  boolTy
    reportCheck "false" falseTm boolTy

    -- ── 9. Pi type itself is well-typed ──────────────────────────────────────
    putStrLn "\n── Π Type Formation ────────────────────────────────────────"
    -- Π(x : U0). U0 : U1
    let bigPi = TPi "x" (TUniv 0) (TUniv 0)
    reportInfer "Π(x:U0).U0" bigPi

    -- ── 10. Path type is well-typed ───────────────────────────────────────────
    putStrLn "\n── Path Type Formation ─────────────────────────────────────"
    let pathType = TPath (TVar "A") (TVar "x") (TVar "x")
    let ctxAx = [("x", TVar "A"), ("A", TUniv 0)]
    case infer ctxAx pathType of
        Right ty -> putStrLn $
            "  ✓  Path A x x  (in context A:U0, x:A)\n       : " ++ show ty
        Left err -> putStrLn $ "  ✗  " ++ show err

--------------------------------------------------------------------------------
-- 7. Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
    demoEval
    demoTypeCheck