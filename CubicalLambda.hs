{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- Interval Syntax & DNF
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
-- Cubical Dependent Syntax
--------------------------------------------------------------------------------

type Name  = String
type Level = Int

data Term
    = TVar Int
    | TApp Term Term
    | TAbs Name Term
    | TUniv Level
    | TIntervalTy
    | TPi Name Term Term
    | TInterval I
    | TCube DNF
    -- TPath aTy u v
    -- aTy may be a function of the interval (PathP / heterogeneous path).
    -- When aTy is a PLam, p @ r has type aTy[r/i].
    | TPath Term Term Term
    | PLam Name Term
    | PApp Term Term
    | THComp Term Term Term Term
    -- Equiv A B : type of equivalences from A to B
    | TEquiv Term Term
    -- mkEquiv A B f g η ε : Equiv A B
    | TMkEquiv Term Term Term Term Term Term
    -- equivFwd e x : apply forward map of e to x
    | TEquivFwd Term Term
    -- ua e : Path U A B  (univalence map)
    | TUa Term
    -- transport p x : coerce x along path p
    | TTransport Term Term
    -- Glue A φ e
    | TGlue Term Term Term
    -- glue φ t a
    | TGlueElem Term Term Term
    -- unglue φ e g
    | TUnglue Term Term Term
    deriving (Eq)

showTerm :: [Name] -> Term -> String
showTerm env t = case t of
    TVar i      -> if i < length env then env !! i else "#" ++ show i
    TApp f a    -> "(" ++ showTerm env f ++ " " ++ showTerm env a ++ ")"
    TAbs x b    -> "λ" ++ x ++ ". " ++ showTerm (x:env) b
    TUniv n     -> "U" ++ show n
    TIntervalTy -> "𝕀"
    TPi x a b   -> "Π(" ++ x ++ ":" ++ showTerm env a ++ "). " ++ showTerm (x:env) b
    TInterval i -> show i
    TCube c     -> show c
    TPath a u v -> "Path " ++ showTerm env a ++ " " ++ showTerm env u ++ " " ++ showTerm env v
    PLam i b    -> "⟨" ++ i ++ "⟩ " ++ showTerm (i:env) b
    PApp p r    -> showTerm env p ++ " @ " ++ showTerm env r
    THComp a phi u u0 ->
        "hcomp " ++ showTerm env a
        ++ " [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env u ++ ") "
        ++ showTerm env u0
    TEquiv a b ->
        "Equiv " ++ showTerm env a ++ " " ++ showTerm env b
    TMkEquiv a b f g eta eps ->
        "mkEquiv " ++ showTerm env a ++ " " ++ showTerm env b
        ++ " " ++ showTerm env f ++ " " ++ showTerm env g
        ++ " " ++ showTerm env eta ++ " " ++ showTerm env eps
    TEquivFwd e x ->
        "equivFwd (" ++ showTerm env e ++ ") " ++ showTerm env x
    TUa e ->
        "ua (" ++ showTerm env e ++ ")"
    TTransport p x ->
        "transport (" ++ showTerm env p ++ ") " ++ showTerm env x
    TGlue a phi te ->
        "Glue " ++ showTerm env a
        ++ " [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env te ++ ")"
    TGlueElem phi t a ->
        "glue [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env t ++ ") "
        ++ showTerm env a
    TUnglue phi te g ->
        "unglue [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env te ++ ") "
        ++ showTerm env g

instance Show Term where
    show = showTerm []

--------------------------------------------------------------------------------
-- Shift / Subst / Beta
--------------------------------------------------------------------------------

shift :: Int -> Int -> Term -> Term
shift d c term = case term of
    TVar i      -> TVar (if i >= c then i + d else i)
    TApp f a    -> TApp (shift d c f) (shift d c a)
    TAbs x b    -> TAbs x (shift d (c+1) b)
    TPi x a b   -> TPi x (shift d c a) (shift d (c+1) b)
    TUniv n     -> TUniv n
    TIntervalTy -> TIntervalTy
    TInterval i -> TInterval i
    TCube cu    -> TCube cu
    TPath a u v -> TPath (shift d c a) (shift d c u) (shift d c v)
    PLam x b    -> PLam x (shift d (c+1) b)
    PApp p r    -> PApp (shift d c p) (shift d c r)
    THComp a phi u u0 ->
        THComp (shift d c a) (shift d c phi) (shift d c u) (shift d c u0)
    TEquiv a b ->
        TEquiv (shift d c a) (shift d c b)
    TMkEquiv a b f g eta eps ->
        TMkEquiv (shift d c a) (shift d c b) (shift d c f) (shift d c g)
                 (shift d c eta) (shift d c eps)
    TEquivFwd e x ->
        TEquivFwd (shift d c e) (shift d c x)
    TUa e ->
        TUa (shift d c e)
    TTransport p x ->
        TTransport (shift d c p) (shift d c x)
    TGlue a phi te ->
        TGlue (shift d c a) (shift d c phi) (shift d c te)
    TGlueElem phi t a ->
        TGlueElem (shift d c phi) (shift d c t) (shift d c a)
    TUnglue phi te g ->
        TUnglue (shift d c phi) (shift d c te) (shift d c g)

subst :: Int -> Term -> Term -> Term
subst j s term = case term of
    TVar i
        | i == j    -> s
        | otherwise -> TVar i
    TApp f a    -> TApp (subst j s f) (subst j s a)
    TAbs x b    -> TAbs x (subst (j+1) (shift 1 0 s) b)
    TPi x a b   -> TPi x (subst j s a) (subst (j+1) (shift 1 0 s) b)
    TUniv n     -> TUniv n
    TIntervalTy -> TIntervalTy
    TInterval i -> TInterval i
    TCube cu    -> TCube cu
    TPath a u v -> TPath (subst j s a) (subst j s u) (subst j s v)
    PLam x b    -> PLam x (subst (j+1) (shift 1 0 s) b)
    PApp p r    -> PApp (subst j s p) (subst j s r)
    THComp a phi u u0 ->
        THComp (subst j s a) (subst j s phi) (subst j s u) (subst j s u0)
    TEquiv a b ->
        TEquiv (subst j s a) (subst j s b)
    TMkEquiv a b f g eta eps ->
        TMkEquiv (subst j s a) (subst j s b) (subst j s f) (subst j s g)
                 (subst j s eta) (subst j s eps)
    TEquivFwd e x ->
        TEquivFwd (subst j s e) (subst j s x)
    TUa e ->
        TUa (subst j s e)
    TTransport p x ->
        TTransport (subst j s p) (subst j s x)
    TGlue a phi te ->
        TGlue (subst j s a) (subst j s phi) (subst j s te)
    TGlueElem phi t a ->
        TGlueElem (subst j s phi) (subst j s t) (subst j s a)
    TUnglue phi te g ->
        TUnglue (subst j s phi) (subst j s te) (subst j s g)

beta :: Term -> Term -> Term
beta body arg = shift (-1) 0 (subst 0 (shift 1 0 arg) body)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

dnfTop :: DNF
dnfTop = DNF (Set.singleton Set.empty)

dnfBot :: DNF
dnfBot = DNF Set.empty

isTopDNF :: Term -> Bool
isTopDNF (TCube d) = d == dnfTop
isTopDNF _         = False

isBotDNF :: Term -> Bool
isBotDNF (TCube d) = d == dnfBot
isBotDNF _         = False

eval :: Term -> Term
eval t = case t of
    TApp f a ->
        case eval f of
            TAbs _ body -> eval (beta body (eval a))
            f'          -> TApp f' (eval a)

    PApp p r ->
        let r' = eval r
        in case eval p of
            PLam _ body -> eval (beta body r')
            -- Boundary reduction for stuck paths:
            -- If r = 0 (dnfBot) or r = 1 (dnfTop) and p is a stuck path
            -- typed as  Path A u v, we can't recover u/v here without types.
            -- Leave stuck; etaEqualCtx will handle this via type-directed equality.
            p'          -> PApp p' r'

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)

    THComp aTy phi tube base ->
        let phi' = eval phi
        in if isTopDNF phi'
           then case eval tube of
                    PLam _ body -> eval (beta body (TInterval I1))
                    tube'       -> PApp tube' (TInterval I1)
           else if isBotDNF phi'
           then eval base
           else THComp (eval aTy) phi' (eval tube) (eval base)

    -- Equiv is a type former, stays as-is when fully evaluated
    TEquiv a b ->
        TEquiv (eval a) (eval b)

    TMkEquiv a b f g eta eps ->
        TMkEquiv (eval a) (eval b) (eval f) (eval g) (eval eta) (eval eps)

    -- equivFwd β: equivFwd (mkEquiv A B f g η ε) x  ≡  f x
    TEquivFwd e x ->
        let e' = eval e; x' = eval x
        in case e' of
            TMkEquiv _ _ f _ _ _ -> eval (TApp f x')
            _                    -> TEquivFwd e' x'

    -- ua stays stuck (it's a path; its endpoints compute via transport)
    TUa e -> TUa (eval e)

    -- transport β-rules
    TTransport p x ->
        let p' = eval p; x' = eval x
        in case p' of
            -- uaβ: transport (ua e) x  ≡  equivFwd e x
            TUa e -> eval (TEquivFwd e x')
            -- Path abstraction: transport (⟨i⟩ A) x
            --   • If A doesn't depend on i (endpoints equal) → trivially x
            --   • If A is a Pi-type family ⟨i⟩ (Π(a:A). B i a), apply
            --     function-wise transport (funext-transport)
            PLam iName body ->
                let b0 = eval (beta body (TInterval I0))
                    b1 = eval (beta body (TInterval I1))
                in if definitionallyEqual b0 b1
                   then x'
                   else case (b0, b1) of
                       -- Pi-type path: transport pointwise
                       (TPi argName aTy0 _, TPi _ _ bTy1) ->
                           -- result : Π(a1 : b1.dom). b1.cod (transport(⟨i⟩ b0.dom, a1) transported)
                           TAbs argName $
                               let -- transport argument back along domain path (contravariant)
                                   domPath = PLam iName (eval (beta (shift 1 0 body) (TInterval I0)))
                                   -- Actually use the raw domain at 0 for the argument type
                                   -- and transport the result forward along codomain
                                   a0 = TVar 0
                                   fa = TApp (shift 1 0 x') a0
                               in eval (TTransport
                                           (PLam iName
                                               (eval (TApp (beta (shift 2 0 body)
                                                               (TInterval I1))
                                                           (shift 2 0 (TVar 0)))))
                                           fa)
                       _ -> TTransport p' x'
            _ -> TTransport p' x'

    -- Glue β-rules
    TGlue aTy phi te ->
        let phi' = eval phi
        in if isTopDNF phi'
           then equivDom (eval te)   -- Glue A ⊤ e  ≡  dom(e)
           else if isBotDNF phi'
           then eval aTy             -- Glue A ⊥ _  ≡  A
           else TGlue (eval aTy) phi' (eval te)

    TGlueElem phi t a ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval t
           else if isBotDNF phi'
           then eval a
           else TGlueElem phi' (eval t) (eval a)

    -- unglue β-rules
    TUnglue phi te g ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval (TEquivFwd (eval te) (eval g))
           else if isBotDNF phi'
           then eval g
           else TUnglue phi' (eval te) (eval g)

    _ -> t

-- | Extract the domain type from an equivalence term.
equivDom :: Term -> Term
equivDom (TMkEquiv a _ _ _ _ _) = a
equivDom (TEquiv a _)           = a
equivDom other                  = other

--------------------------------------------------------------------------------
-- Interval Algebra
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
-- Definitional Equality with Eta-Expansion and Path Boundary Reduction
--
-- The key insight for function extensionality:
--   body of  ⟨i⟩ λx. h x @ i  at i=0  is  λx. (h x) @ 0
--   This must equal  f  (the stated left endpoint).
--   Since  h x : Path B (f x) (g x),  we know  (h x) @ 0 = f x  BY TYPING.
--   But eval() can't see this — h x is a stuck neutral.
--
-- Solution: carry the typing context (Ctx) into equality so we can look up
-- what a stuck  (p @ 0)  or  (p @ 1)  reduces to from p's type.
--
-- definitionallyEqual is the context-free entry point (used in eval-time
-- checks).  requireEqualCtx is the context-aware version used in the checker.
--------------------------------------------------------------------------------

-- | Context-free definitional equality (syntactic + eta, no path boundary).
definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 =
    let v1 = eval t1
        v2 = eval t2
    in v1 == v2 || etaEq 8 [] v1 v2

-- | Context-aware definitional equality used inside the type checker.
-- Carries Ctx so stuck path applications  p @ 0 / p @ 1  can be resolved
-- by looking up p's type and reading off the declared endpoints.
definitionallyEqualCtx :: Ctx -> Term -> Term -> Bool
definitionallyEqualCtx ctx t1 t2 =
    let v1 = eval t1
        v2 = eval t2
    in v1 == v2 || etaEq 10 ctx v1 v2

requireEqual :: Ctx -> Term -> Term -> Either TypeError ()
requireEqual ctx expected got
    | definitionallyEqualCtx ctx expected got = Right ()
    | otherwise = Left (TypeMismatch (eval expected) (eval got))

-- Endpoint check with detailed error message
requireEqualEndpt :: Ctx -> Term -> Term -> Either TypeError ()
requireEqualEndpt ctx expected got
    | definitionallyEqualCtx ctx expected got = Right ()
    | otherwise = Left (Other
        (  "endpoint mismatch (ctx_depth=" ++ show (length ctx)
        ++ ", ctx=" ++ show (map fst ctx) ++ ")"
        ++ "\n  expected=" ++ showTerm (map fst ctx) (eval expected)
        ++ "  [raw=" ++ show (eval expected) ++ "]"
        ++ "\n  got=" ++ showTerm (map fst ctx) (eval got)
        ++ "  [raw=" ++ show (eval got) ++ "]"))

-- | Try to reduce a stuck  PApp p r  using p's declared type from the context.
-- If p : Path A u v and r evaluates to I0 → return u
--                        r evaluates to I1 → return v
reducePAppByType :: Ctx -> Term -> Term -> Maybe Term
reducePAppByType ctx p r =
    case inferTy ctx p of
        Just (TPath _ u v) ->
            let r' = eval r
            in if isBotDNF r' || r' == TInterval I0
               then Just (eval u)
               else if isTopDNF r' || r' == TInterval I1
               then Just (eval v)
               else Nothing
        _ -> Nothing
  where
    -- Lightweight infer: only looks up variables and follows applications.
    -- We don't want to call the full bidirectional infer here (circular),
    -- so we handle only the cases we need.
    inferTy :: Ctx -> Term -> Maybe Term
    inferTy c (TVar i)
        | i >= 0, i < length c = Just (eval (shift (i+1) 0 (snd (c !! i))))
        | otherwise             = Nothing
    inferTy c (TApp f a) =
        case inferTy c f of
            Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
            _                  -> Nothing
    inferTy _ _ = Nothing

-- | Extract the domain type of a lambda-like term for context extension.
-- We try to infer the Pi-type of the *other* term (the neutral) so that
-- reducePAppByType can fire later. Falls back to TUniv 0 if unavailable.
inferLamDom :: Ctx -> Term -> Term -> Term
inferLamDom ctx (TAbs _ _) neutral =
    case inferNeutralTy ctx neutral of
        Just (TPi _ domTy _) -> eval domTy
        _                    -> TUniv 0
inferLamDom _ _ _ = TUniv 0

-- | Lightweight neutral type inference (no full bidirectional checker).
inferNeutralTy :: Ctx -> Term -> Maybe Term
inferNeutralTy ctx (TVar i)
    | i >= 0, i < length ctx = Just (eval (shift (i+1) 0 (snd (ctx !! i))))
    | otherwise               = Nothing
inferNeutralTy ctx (TApp f a) =
    case inferNeutralTy ctx f of
        Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
        _                  -> Nothing
inferNeutralTy _ _ = Nothing

-- | Core structural eta-equality, fuel-limited to prevent looping.
-- ctx is threaded through so path boundary reduction can fire.
etaEq :: Int -> Ctx -> Term -> Term -> Bool
etaEq 0 _ _ _ = False
etaEq fuel ctx t1 t2
    -- ── Syntactic shortcut ───────────────────────────────────────────────────
    | t1 == t2 = True

    -- ── Path boundary reduction (THE KEY FIX) ───────────────────────────────
    -- When we see  (p @ 0)  or  (p @ 1)  where p is stuck,
    -- look up p's type in ctx to retrieve the stated endpoint.
    | PApp p r <- t1
    , Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx u t2

    | PApp p r <- t2
    , Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx t1 u

    -- ── Lambda eta ───────────────────────────────────────────────────────────
    -- (λx.b1) == (λx.b2)  →  b1 == b2  in extended ctx
    | TAbs x b1 <- t1, TAbs _ b2 <- t2
    = let domTy = inferLamDom ctx t1 t2
          ctx'  = (x, domTy) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval b2)

    -- neutral == (λx.b)  →  eta-expand neutral:  (neutral x) == b
    | TAbs x b2 <- t2
    = let domTy = inferLamDom ctx t2 t1
          ctx'  = (x, domTy) : ctx
          f1x   = eval (TApp (shift 1 0 t1) (TVar 0))
      in etaEq (fuel-1) ctx' f1x (eval b2)

    -- (λx.b) == neutral  →  b == (neutral x)
    | TAbs x b1 <- t1
    = let domTy = inferLamDom ctx t1 t2
          ctx'  = (x, domTy) : ctx
          f2x   = eval (TApp (shift 1 0 t2) (TVar 0))
      in etaEq (fuel-1) ctx' (eval b1) f2x

    -- ── Path-lambda eta ──────────────────────────────────────────────────────
    -- ⟨i⟩b1 == ⟨i⟩b2  →  b1 == b2  under i
    | PLam i b1 <- t1, PLam _ b2 <- t2
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval b2)

    -- neutral == ⟨i⟩b  →  (neutral @ i) == b  under i
    | PLam i b2 <- t2
    = let ctx' = (i, TIntervalTy) : ctx
          p1i  = eval (PApp (shift 1 0 t1) (TVar 0))
      in etaEq (fuel-1) ctx' p1i (eval b2)

    -- ⟨i⟩b == neutral  →  b == (neutral @ i)  under i
    | PLam i b1 <- t1
    = let ctx' = (i, TIntervalTy) : ctx
          p2i  = eval (PApp (shift 1 0 t2) (TVar 0))
      in etaEq (fuel-1) ctx' (eval b1) p2i

    -- ── Congruence on neutral spines ─────────────────────────────────────────
    | TApp f1 a1 <- t1, TApp f2 a2 <- t2
    = etaEq (fuel-1) ctx f1 f2 && etaEq (fuel-1) ctx a1 a2

    | PApp p1 r1 <- t1, PApp p2 r2 <- t2
    = etaEq (fuel-1) ctx p1 p2 && etaEq (fuel-1) ctx r1 r2

    -- ── Type congruence ──────────────────────────────────────────────────────
    | TPi _ a1 b1 <- t1, TPi _ a2 b2 <- t2
    = etaEq (fuel-1) ctx a1 a2 && etaEq (fuel-1) ctx b1 b2

    | TPath ty1 u1 v1 <- t1, TPath ty2 u2 v2 <- t2
    = etaEq (fuel-1) ctx ty1 ty2
      && etaEq (fuel-1) ctx u1 u2
      && etaEq (fuel-1) ctx v1 v2

    | otherwise = False

--------------------------------------------------------------------------------
-- Bidirectional Type Checker
--------------------------------------------------------------------------------

intervalTy :: Term
intervalTy = TIntervalTy

type Ctx = [(Name, Term)]

data TypeError
    = UnboundVariable Name
    | TypeMismatch Term Term
    | ExpectedPi   Term
    | ExpectedPath Term
    | ExpectedUniverse Term
    | ExpectedEquiv Term
    | NotAnInterval Term
    | CannotInfer Term
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
        ExpectedEquiv ty ->
            "  Expected an Equiv type, but found:\n    " ++ show ty
        NotAnInterval t ->
            "  Expected an interval expression (𝕀), but got:\n    " ++ show t
        CannotInfer t ->
            "  Cannot infer type of term without annotation:\n    " ++ show t
            ++ "\n  (Tip: use 'check' instead of 'infer', or add a type annotation)"
        Other msg ->
            "  " ++ msg

extendCtx :: Name -> Term -> Ctx -> Ctx
extendCtx x ty ctx = (x, ty) : ctx

lookupCtx :: Int -> Ctx -> Either TypeError Term
lookupCtx i ctx
    | i < 0 || i >= length ctx =
        Left (UnboundVariable ("#" ++ show i))
    | otherwise =
        let (_, ty) = ctx !! i
        in Right (shift (i + 1) 0 ty)

requireUniverse :: Ctx -> Term -> Either TypeError Level
requireUniverse ctx t = do
    ty <- infer ctx t
    case eval ty of
        TUniv n -> Right n
        other   -> Left (ExpectedUniverse other)

checkInterval :: Ctx -> Term -> Either TypeError ()
checkInterval _   (TInterval _) = Right ()
checkInterval _   (TCube _)     = Right ()
checkInterval ctx t = do
    ty <- infer ctx t
    if ty == intervalTy
        then Right ()
        else Left (NotAnInterval t)

-- | Require term has type Equiv A B, return (A, B).
requireEquiv :: Ctx -> Term -> Either TypeError (Term, Term)
requireEquiv ctx t = do
    ty <- infer ctx t
    case eval ty of
        TEquiv a b -> Right (eval a, eval b)
        other      -> Left (ExpectedEquiv other)

--------------------------------------------------------------------------------
-- Type Inference
--------------------------------------------------------------------------------

infer :: Ctx -> Term -> Either TypeError Term

infer ctx (TVar i) = lookupCtx i ctx

infer _   (TUniv n) = Right (TUniv (n + 1))

infer ctx (TApp f a) = do
    fTy <- infer ctx f
    case eval fTy of
        TPi _ aTy bTy -> do
            check ctx a aTy
            return $ eval (beta bTy a)
        other -> Left (ExpectedPi other)

infer ctx (TPi x aTy bTy) = do
    i <- requireUniverse ctx aTy
    j <- requireUniverse (extendCtx x (eval aTy) ctx) bTy
    return $ TUniv (max i j)

-- ─── Path Type Formation ───────────────────────────────────────────────────
-- The type family aTy may be either:
--   • A plain type T            → homogeneous Path T u v
--   • A path abstraction ⟨i⟩T  → heterogeneous PathP (⟨i⟩T) u v
--     where u : T[0/i]  and  v : T[1/i]
infer ctx (TPath aTy u v) = do
    n <- requireUniverse ctx aTy
    let aTy' = eval aTy
    -- Determine the types of the endpoints by substituting 0/1 into aTy.
    -- For a plain type, beta just returns it unchanged.
    let uTy = case aTy' of
                  PLam _ body -> eval (beta body (TInterval I0))
                  plain       -> plain
        vTy = case aTy' of
                  PLam _ body -> eval (beta body (TInterval I1))
                  plain       -> plain
    check ctx u uTy
    check ctx v vTy
    return $ TUniv n

-- ─── Path Application ──────────────────────────────────────────────────────
-- FIXED: return type is aTy[r/i], not just aTy.
-- This is essential for heterogeneous paths and for transport along universe
-- paths produced by ua.
infer ctx (PApp p r) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ -> do
            checkInterval ctx r
            let r' = eval r
            -- Substitute the interval argument into the type family.
            return $ case eval aTy of
                PLam _ body -> eval (beta body r')
                plain       -> plain
        other -> Left (ExpectedPath other)

infer _   (TInterval _)  = Right intervalTy
infer _   (TCube _)      = Right intervalTy
infer _   TIntervalTy    = Right (TUniv 0)

infer _   t@(TAbs _ _) = Left (CannotInfer t)
infer _   t@(PLam _ _) = Left (CannotInfer t)

-- ─── Equiv Formation ──────────────────────────────────────────────────────
-- Γ ⊢ A : U_n    Γ ⊢ B : U_n
-- ────────────────────────────
-- Γ ⊢ Equiv A B : U_n
infer ctx (TEquiv a b) = do
    n <- requireUniverse ctx a
    m <- requireUniverse ctx b
    return $ TUniv (max n m)

-- ─── mkEquiv Introduction ──────────────────────────────────────────────────
-- Γ ⊢ f : A → B
-- Γ ⊢ g : B → A
-- Γ ⊢ η : Π(a:A). Path A a (g (f a))
-- Γ ⊢ ε : Π(b:B). Path B (f (g b)) b
-- ─────────────────────────────────────
-- Γ ⊢ mkEquiv A B f g η ε : Equiv A B
infer ctx (TMkEquiv a b f g eta eps) = do
    _n <- requireUniverse ctx a
    _m <- requireUniverse ctx b
    let a' = eval a
        b' = eval b
    check ctx f (TPi "_" a' (shift 1 0 b'))
    check ctx g (TPi "_" b' (shift 1 0 a'))
    -- η : Π(a:A). Path A a (g (f a))
    let etaTy = TPi "a" a'
                    (TPath (shift 1 0 a')
                           (TVar 0)
                           (TApp (shift 1 0 g) (TApp (shift 1 0 f) (TVar 0))))
    check ctx eta etaTy
    -- ε : Π(b:B). Path B (f (g b)) b
    let epsTy = TPi "b" b'
                    (TPath (shift 1 0 b')
                           (TApp (shift 1 0 f) (TApp (shift 1 0 g) (TVar 0)))
                           (TVar 0))
    check ctx eps epsTy
    return $ TEquiv a' b'

-- ─── equivFwd Elimination ─────────────────────────────────────────────────
-- Γ ⊢ e : Equiv A B    Γ ⊢ x : A
-- ─────────────────────────────────
-- Γ ⊢ equivFwd e x : B
infer ctx (TEquivFwd e x) = do
    (a, b) <- requireEquiv ctx e
    check ctx x a
    return b

-- ─── ua — Univalence Map ──────────────────────────────────────────────────
-- Γ ⊢ e : Equiv A B
-- ──────────────────────────────────
-- Γ ⊢ ua e : Path U_n A B
--
-- Key: ua converts an equivalence into a path in the universe.
-- Combined with transport: transport (ua e) x ≡ equivFwd e x
infer ctx (TUa e) = do
    (a, b) <- requireEquiv ctx e
    n <- requireUniverse ctx a
    return $ TPath (TUniv n) a b

-- ─── transport ────────────────────────────────────────────────────────────
-- Γ ⊢ p : Path U_n A B    Γ ⊢ x : A
-- ─────────────────────────────────────
-- Γ ⊢ transport p x : B
--
-- For a heterogeneous path ⟨i⟩T, we check x : T[0/i] and return T[1/i].
infer ctx (TTransport p x) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ ->
            let (xTy, retTy) = case eval aTy of
                    PLam _ body ->
                        ( eval (beta body (TInterval I0))
                        , eval (beta body (TInterval I1))
                        )
                    plain -> (plain, plain)
            in do
                check ctx x xTy
                return retTy
        other -> Left (ExpectedPath other)

-- ─── Glue Type Formation ──────────────────────────────────────────────────
-- Γ ⊢ A : U_n    Γ ⊢ φ : 𝕀    Γ ⊢ e : Equiv T A  (permissively: U_n)
-- ──────────────────────────────────────────────────────────────────────
-- Γ ⊢ Glue A φ e : U_n
infer ctx (TGlue aTy phi te) = do
    n  <- requireUniverse ctx aTy
    checkInterval ctx phi
    teTy <- infer ctx te
    let m = case eval teTy of
                TUniv k    -> k
                TEquiv _ _ -> n
                _          -> n
    return $ TUniv (max n m)

-- ─── Unglue Elimination ───────────────────────────────────────────────────
infer ctx (TUnglue phi te g) = do
    checkInterval ctx phi
    let phi' = eval phi
    if isTopDNF phi'
       then infer ctx (TEquivFwd te g)
       else if isBotDNF phi'
       then infer ctx g
       else do
           gTy <- infer ctx g
           case eval gTy of
               TGlue aTy _ _ -> return (eval aTy)
               other         -> Left (Other $
                   "unglue: expected argument of Glue type, got: " ++ show other)

-- ─── Glue Element Introduction ────────────────────────────────────────────
infer ctx t@(TGlueElem phi elm a) =
    let phi' = eval phi
    in if isTopDNF phi'
       then infer ctx elm
       else if isBotDNF phi'
       then infer ctx a
       else Left (CannotInfer t)

-- ─── Kan Composition ──────────────────────────────────────────────────────
-- hcomp A [φ] u u0 : A
-- where  u  is a partial element (tube) and  u0 : A  is the base.
-- When φ = ⊤, result is u @ 1.  When φ = ⊥, result is u0.
infer ctx (THComp aTy phi tube base) = do
    _n     <- requireUniverse ctx aTy
    let aTy' = eval aTy
    checkInterval ctx phi
    check ctx base aTy'
    case eval tube of
        PLam i body ->
            check (extendCtx i intervalTy ctx) body aTy'
        tube' -> do
            tubeTy <- infer ctx tube'
            case eval tubeTy of
                TPath a _ _
                    | definitionallyEqualCtx ctx a aTy' -> return ()
                other -> Left (ExpectedPath other)
    return aTy'

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

check :: Ctx -> Term -> Term -> Either TypeError ()

-- ─── Lambda introduction ──────────────────────────────────────────────────
check ctx (TAbs x body) ty =
    case eval ty of
        TPi _ aTy bTy -> do
            let aTy' = eval aTy
            check (extendCtx x aTy' ctx) body bTy
        other -> Left (ExpectedPi other)

-- ─── Path-lambda introduction ─────────────────────────────────────────────
-- check ctx (PLam i body) (Path A u v)
--
-- Endpoint coherence:  body[0/i] ≡ u   and   body[1/i] ≡ v
--
-- The comparison is done in the EXTENDED context  (i : 𝕀) : ctx  so that
-- reducePAppByType can resolve stuck  (p @ 0)  and  (p @ 1)  using the
-- types of variables that appear in body.
--
-- This is THE key fix for function extensionality:
--   body = λx. h x @ i
--   body[0/i] = λx. (h x) @ 0    (stuck — h is a variable)
--   u = f                          (also a variable)
--   In the extended ctx,  h : Π(x:A). Path B (f x) (g x)
--   so  h x : Path B (f x) (g x)  and  (h x) @ 0 = f x
--   eta-equality then gives  λx. f x  ≡  f.
check ctx (PLam i body) ty =
    case eval ty of
        TPath aTy u v -> do
            -- Context extended with the interval variable (for body check).
            let ctx' = extendCtx i intervalTy ctx
            -- Determine body type: plain types shift by 1 for ctx'.
            let bodyTy = case eval aTy of
                    p@(PLam {}) -> p
                    plain       -> shift 1 0 plain
            -- beta-reduce body at each endpoint: i is gone, result lives in ctx.
            let bodyAt0 = eval (beta body (TInterval I0))
                bodyAt1 = eval (beta body (TInterval I1))
            -- Endpoint coherence checked in ctx (not ctx'): bodyAt0/bodyAt1
            -- live in ctx after beta, and h/f/g are all visible here for
            -- reducePAppByType to fire on stuck (h x) @ 0 etc.
            requireEqualEndpt ctx (eval u) bodyAt0
            requireEqualEndpt ctx (eval v) bodyAt1
            -- Check the body itself under the interval binder.
            check ctx' body bodyTy
        other -> Left (ExpectedPath other)

-- ─── Glue element introduction ────────────────────────────────────────────
check ctx (TGlueElem phi t a) ty =
    case eval ty of
        TGlue aTy phi' te -> do
            checkInterval ctx phi
            requireEqual ctx (eval phi') (eval phi)
            let tTy = case eval te of
                          TMkEquiv domA _ _ _ _ _ -> eval domA
                          TEquiv domA _            -> eval domA
                          other                    -> other
            check ctx t tTy
            check ctx a (eval aTy)
        other -> Left (Other $
            "glue: expected Glue type, got: " ++ show other)

-- ─── Fallback: infer and compare ─────────────────────────────────────────
check ctx t ty = do
    ty' <- infer ctx t
    requireEqual ctx (eval ty) (eval ty')

--------------------------------------------------------------------------------
-- Top-level helpers
--------------------------------------------------------------------------------

inferClosed :: Term -> Either TypeError Term
inferClosed = infer []

checkClosed :: Term -> Term -> Either TypeError ()
checkClosed t ty = check [] t ty

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

--------------------------------------------------------------------------------
-- Global named environment
--------------------------------------------------------------------------------

-- | A global definition: (name, type, value).
-- Definitions are stored most-recent first.
type GlobalEnv = [(Name, Term, Term)]

-- | Build a Ctx (de Bruijn list) from a GlobalEnv for type-checking.
-- Variables are ordered innermost-first, so we reverse the env.
globalCtx :: GlobalEnv -> Ctx
globalCtx genv = map (\(n, ty, _) -> (n, ty)) (reverse genv)

-- | Wrap a term so that global definitions are in scope as let-bindings.
-- Concretely:  applyGlobals [(x,T,v), ...] t  =  (λx. t) v
-- applied in order from outermost (first defined) to innermost (last defined),
-- so the de Bruijn indices inside 't' see the most-recent def as #0.
applyGlobals :: GlobalEnv -> Term -> Term
applyGlobals genv t = foldr wrap t (reverse genv)
  where
    wrap (x, _ty, val) body = TApp (TAbs x body) val

-- | Infer the type of a term in the context of a GlobalEnv.
inferWithEnv :: GlobalEnv -> Term -> Either TypeError Term
inferWithEnv genv t = infer (globalCtx genv) t

-- | Check a term against a type in the context of a GlobalEnv.
checkWithEnv :: GlobalEnv -> Term -> Term -> Either TypeError ()
checkWithEnv genv t ty = check (globalCtx genv) t ty