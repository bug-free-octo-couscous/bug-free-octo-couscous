module Cubical.TypeChecker
    ( Ctx
    , TypeError(..)
    , infer, check
    , inferClosed, checkClosed
    , extendCtx, lookupCtx
    , requireEqual, requireEqualEndpt
    , requireUniverse, requireEquiv
    , checkInterval
    , reportInfer, reportCheck
    ) where

import Cubical.Interval (I(..), DNF(..), Literal(..))
import qualified Data.Set as Set
import Cubical.Syntax
import Cubical.Eval (eval, isTopDNF, isBotDNF)
import Cubical.Equality (definitionallyEqualCtx, definitionallyEqualCtxR, EtaResult(..))

--------------------------------------------------------------------------------
-- Context & Errors
--------------------------------------------------------------------------------

type Ctx = [(Name, Term)]

intervalTy :: Term
intervalTy = TIntervalTy

data TypeError
    = UnboundVariable Name
    | TypeMismatch Term Term
    | ExpectedPi   Term
    | ExpectedPath Term
    | ExpectedUniverse Term
    | ExpectedEquiv Term
    | NotAnInterval Term
    | CannotInfer Term
    | EtaFuelExhausted Term Term
    | Other String
    deriving (Eq)

instance Show TypeError where
    show e = case e of
        UnboundVariable x  -> "  Unbound variable: '" ++ x ++ "'"
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
        EtaFuelExhausted t1 t2 ->
            "  Eta-equality check ran out of fuel (terms may be equal but are too\n"
            ++ "  deeply nested to decide automatically).\n"
            ++ "    lhs : " ++ show t1 ++ "\n"
            ++ "    rhs : " ++ show t2
        Other msg -> "  " ++ msg

extendCtx :: Name -> Term -> Ctx -> Ctx
extendCtx x ty ctx = (x, ty) : ctx

lookupCtx :: Int -> Ctx -> Either TypeError Term
lookupCtx i ctx
    | i < 0 || i >= length ctx = Left (UnboundVariable ("#" ++ show i))
    | otherwise = Right (shift (i + 1) 0 (snd (ctx !! i)))

requireEqual :: Ctx -> Term -> Term -> Either TypeError ()
requireEqual ctx expected got =
    case definitionallyEqualCtxR ctx expected got of
        Equal     -> Right ()
        NotEqual  -> Left (TypeMismatch (eval expected) (eval got))
        Exhausted -> Left (EtaFuelExhausted (eval expected) (eval got))

requireEqualEndpt :: Ctx -> Term -> Term -> Either TypeError ()
requireEqualEndpt ctx expected got =
    case definitionallyEqualCtxR ctx expected got of
        Equal    -> Right ()
        NotEqual -> Left (Other
            (  "endpoint mismatch (ctx_depth=" ++ show (length ctx)
            ++ ", ctx=" ++ show (map fst ctx) ++ ")"
            ++ "\n  expected=" ++ showTerm (map fst ctx) (eval expected)
            ++ "  [raw=" ++ show (eval expected) ++ "]"
            ++ "\n  got=" ++ showTerm (map fst ctx) (eval got)
            ++ "  [raw=" ++ show (eval got) ++ "]"))
        Exhausted -> Left (EtaFuelExhausted (eval expected) (eval got))

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
    if ty == intervalTy then Right () else Left (NotAnInterval t)

requireEquiv :: Ctx -> Term -> Either TypeError (Term, Term)
requireEquiv ctx t = do
    ty <- infer ctx t
    case eval ty of
        TEquiv a b -> Right (eval a, eval b)
        other      -> Left (ExpectedEquiv other)

--------------------------------------------------------------------------------
-- Face-restriction helpers (used by hcomp checking)
--------------------------------------------------------------------------------

-- | @unless cond err@ — like the Prelude version but in Either.
unless :: Bool -> Either TypeError () -> Either TypeError ()
unless True  _   = Right ()
unless False act = act

-- | Apply a single DNF literal as a substitution on a term.
--   Pos n    means  iₙ = 1   (substitute IVar n ↦ I1)
--   NegVar n means  iₙ = 0   (substitute IVar n ↦ I0)
--
--   Interval variables are encoded as de Bruijn indices *inside* the interval
--   algebra (IVar k), separate from term-level de Bruijn.  They don't appear
--   in the Ctx, so no shifting of term variables is needed — we just rewrite
--   every occurrence of TInterval (IVar n) / TCube that mentions n.
applyLiteral :: Literal -> Term -> Term
applyLiteral lit = go
  where
    (n, val) = case lit of
        Pos    k -> (k, I1)
        NegVar k -> (k, I0)

    goI :: I -> I
    goI (IVar k)   | k == n = val
    goI (Meet a b)          = Meet (goI a) (goI b)
    goI (Join a b)          = Join (goI a) (goI b)
    goI (Neg  a)            = Neg  (goI a)
    goI other               = other

    go :: Term -> Term
    go t = case t of
        TInterval i    -> eval (TInterval (goI i))
        TCube (DNF cs) ->
            -- Substitute the literal into each cube by treating each Literal
            -- as an IVar expression and running it through goI, then
            -- re-normalising the whole DNF.
            let substLit (Pos    k) = goI (IVar k)
                substLit (NegVar k) = Neg (goI (IVar k))
                -- A cube is a conjunction; substitute and re-evaluate each lit.
                substCube c = foldr (\l acc -> Meet (substLit l) acc) I1
                                    (Set.toList c)
                -- The full DNF is a disjunction of substituted cubes.
                combined = foldr (\c acc -> Join (substCube c) acc) I0
                                 (Set.toList cs)
            in eval (TInterval combined)
        TApp  f a      -> eval $ TApp  (go f) (go a)
        TAbs  x b      -> TAbs  x (go b)
        TPi   x a b    -> TPi   x (go a) (go b)
        TPath a u v    -> TPath   (go a) (go u) (go v)
        PLam  i b      -> PLam  i (go b)
        PApp  p r      -> eval $ PApp  (go p) (go r)
        THComp a ph u u0 -> eval $ THComp (go a) (go ph) (go u) (go u0)
        TEquiv a b     -> TEquiv (go a) (go b)
        TMkEquiv a b f g eta eps ->
            TMkEquiv (go a) (go b) (go f) (go g) (go eta) (go eps)
        TEquivFwd e x  -> eval $ TEquivFwd (go e) (go x)
        TUa e          -> TUa (go e)
        TTransport p x -> eval $ TTransport (go p) (go x)
        TGlue a ph te  -> eval $ TGlue (go a) (go ph) (go te)
        TGlueElem ph x a -> eval $ TGlueElem (go ph) (go x) (go a)
        TUnglue ph te g  -> eval $ TUnglue (go ph) (go te) (go g)
        _              -> t   -- TVar, TUniv, TIntervalTy: no interval vars

-- | Check that @tubeAt0 ≡ base@ holds on every face of @phi@.
--
--   For each cube (conjunction of literals) in phi's DNF we:
--     1. Apply all the literal substitutions to both sides.
--     2. Require definitional equality of the results.
--
--   This precisely encodes the condition  [φ = 1] ⊢ u 0 ≡ u₀:
--   each cube is one maximal context in which φ is forced to be 1.
--
--   When phi = ⊥ (no cubes) the loop is empty and the check trivially passes.
--   When phi = ⊤ (one empty cube, no literals) the substitution is the
--   identity, recovering the unconditional check.
checkFaces :: Ctx -> Term -> Term -> Term -> Either TypeError ()
checkFaces ctx phi tubeAt0 base =
    case phi of
        TCube (DNF cubes) ->
            mapM_ checkCube (Set.toList cubes)
        _ -> requireEqualEndpt ctx tubeAt0 base   -- non-DNF phi: fall back
  where
    checkCube cube =
        let applyAll = foldr (.) id (map applyLiteral (Set.toList cube))
            lhs = eval (applyAll tubeAt0)
            rhs = eval (applyAll base)
        in requireEqualEndpt ctx lhs rhs

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

infer ctx (TPath aTy u v) = do
    n <- requireUniverse ctx aTy
    let aTy' = eval aTy
        uTy  = case aTy' of PLam _ body -> eval (beta body (TInterval I0)); p -> p
        vTy  = case aTy' of PLam _ body -> eval (beta body (TInterval I1)); p -> p
    check ctx u uTy
    check ctx v vTy
    return $ TUniv n

infer ctx (PApp p r) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ -> do
            checkInterval ctx r
            let r' = eval r
            return $ case eval aTy of
                PLam _ body -> eval (beta body r')
                plain       -> plain
        other -> Left (ExpectedPath other)

infer _   (TInterval _)  = Right intervalTy
infer _   (TCube _)      = Right intervalTy
infer _   TIntervalTy    = Right (TUniv 0)
infer _   t@(TAbs _ _)   = Left (CannotInfer t)
infer _   t@(PLam _ _)   = Left (CannotInfer t)

infer ctx (TEquiv a b) = do
    n <- requireUniverse ctx a
    m <- requireUniverse ctx b
    return $ TUniv (max n m)

infer ctx (TMkEquiv a b f g eta eps) = do
    _ <- requireUniverse ctx a
    _ <- requireUniverse ctx b
    let a' = eval a; b' = eval b
    check ctx f (TPi "_" a' (shift 1 0 b'))
    check ctx g (TPi "_" b' (shift 1 0 a'))
    check ctx eta (TPi "a" a'
        (TPath (shift 1 0 a') (TVar 0)
               (TApp (shift 1 0 g) (TApp (shift 1 0 f) (TVar 0)))))
    check ctx eps (TPi "b" b'
        (TPath (shift 1 0 b')
               (TApp (shift 1 0 f) (TApp (shift 1 0 g) (TVar 0)))
               (TVar 0)))
    return $ TEquiv a' b'

infer ctx (TEquivFwd e x) = do
    (a, b) <- requireEquiv ctx e
    check ctx x a
    return b

infer ctx (TUa e) = do
    (a, b) <- requireEquiv ctx e
    n <- requireUniverse ctx a
    return $ TPath (TUniv n) a b

infer ctx (TTransport p x) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ ->
            let (xTy, retTy) = case eval aTy of
                    PLam _ body ->
                        ( eval (beta body (TInterval I0))
                        , eval (beta body (TInterval I1)) )
                    plain -> (plain, plain)
            in do check ctx x xTy; return retTy
        other -> Left (ExpectedPath other)

infer ctx (TGlue aTy phi te) = do
    n   <- requireUniverse ctx aTy
    let aTy' = eval aTy
    checkInterval ctx phi
    teTy <- infer ctx te
    m <- case eval teTy of
        -- te is itself a universe (a type being glued directly):
        -- just take its level.
        TUniv k -> return k

        -- te : Equiv A B  — the main case.
        -- 1. Extract A and B from the equivalence type.
        -- 2. Verify B ≡ aTy (the codomain must match the base type).
        -- 3. Derive the level from A and B properly.
        TEquiv a b -> do
            let a' = eval a
                b' = eval b
            -- Coherence: the codomain of the equivalence must be the base type.
            requireEqual ctx b' aTy'
            -- Get levels of A and B by checking them as types.
            p <- requireUniverse ctx a'
            q <- requireUniverse ctx b'
            return (max p q)

        -- te : TMkEquiv a b f g eta eps inlined as a term (already evaluated):
        -- extract domain/codomain directly.
        TMkEquiv a b _ _ _ _ -> do
            let a' = eval a
                b' = eval b
            requireEqual ctx b' aTy'
            p <- requireUniverse ctx a'
            q <- requireUniverse ctx b'
            return (max p q)

        other ->
            Left (Other $
                "Glue: equivalence argument has unexpected type: "
                ++ show other)
    return $ TUniv (max n m)

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
               other -> Left (Other $
                   "unglue: expected argument of Glue type, got: " ++ show other)

infer ctx t@(TGlueElem phi elm a) =
    let phi' = eval phi
    in if isTopDNF phi' then infer ctx elm
       else if isBotDNF phi' then infer ctx a
       else Left (CannotInfer t)

infer ctx (THComp aTy phi tube base) = do
    _ <- requireUniverse ctx aTy
    let aTy' = eval aTy
    checkInterval ctx phi
    -- 1. base : A
    check ctx base aTy'
    -- 2. Tube well-typedness + boundary conditions
    --
    --    hcomp A φ u u₀ is well-typed when:
    --      (a) u : (i : 𝕀) → A                          (tube has the right type)
    --      (b) [φ = 1] ⊢ u 0 ≡ u₀                       (tube agrees with base at i=0)
    --      (c) [φ = 1] ⊢ u 1 : A                         (u@1 is well-formed; implied by (a))
    --
    --    Condition (b) is checked *per face* of φ's DNF.  Each cube in the DNF
    --    is a conjunction of literals (iₙ = 0  or  iₙ = 1).  We substitute
    --    those assignments into both u@0 and u₀ before comparing, which gives
    --    the check its correct meaning under the face restriction [φ = 1].
    --
    --    When φ = ⊥ (bot) no boundary condition is imposed at all (vacuously true).
    --    When φ = ⊤ (top) the check is unconditional, same as before.
    let phi' = eval phi
    _ <- case eval tube of
        PLam i body -> do
            -- (a) check body : A in the extended context
            let ctx'  = extendCtx i intervalTy ctx
                aTy'S = shift 1 0 aTy'
            check ctx' body aTy'S
            -- (b) for each face of φ, check u@0 ≡ u₀ under that face's substitutions
            let tubeAt0 = eval (beta body (TInterval I0))
            checkFaces ctx phi' tubeAt0 (eval base)
        tube' -> do
            -- Non-lambda tube: treat it as a Path A u v
            tubeTy <- infer ctx tube'
            case eval tubeTy of
                TPath a u v -> do
                    -- The path must lie over A
                    unless (definitionallyEqualCtx ctx (eval a) aTy') $
                        Left (TypeMismatch (eval aTy') (eval a))
                    -- Both endpoints must have type A (redundant if a ≡ A,
                    -- but makes the error local and explicit)
                    check ctx (eval u) aTy'
                    check ctx (eval v) aTy'
                    -- (b) for each face of φ, u (= tube@0) must equal base
                    checkFaces ctx phi' (eval u) (eval base)
                other -> Left (ExpectedPath other)
    return aTy'

--------------------------------------------------------------------------------
-- Type Checking
--------------------------------------------------------------------------------

check :: Ctx -> Term -> Term -> Either TypeError ()

check ctx (TAbs x body) ty =
    case eval ty of
        TPi _ aTy bTy -> check (extendCtx x (eval aTy) ctx) body bTy
        other         -> Left (ExpectedPi other)

check ctx (PLam i body) ty =
    case eval ty of
        TPath aTy u v -> do
            let ctx'    = extendCtx i intervalTy ctx
                bodyTy  = case eval aTy of p@(PLam {}) -> p; plain -> shift 1 0 plain
                bodyAt0 = eval (beta body (TInterval I0))
                bodyAt1 = eval (beta body (TInterval I1))
            requireEqualEndpt ctx (eval u) bodyAt0
            requireEqualEndpt ctx (eval v) bodyAt1
            check ctx' body bodyTy
        other -> Left (ExpectedPath other)

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
        other -> Left (Other $ "glue: expected Glue type, got: " ++ show other)

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
        Right ty -> putStrLn $ "  ✓  " ++ label ++ "\n       : " ++ show ty
        Left err -> putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err

reportCheck :: String -> Term -> Term -> IO ()
reportCheck label t ty =
    case checkClosed t ty of
        Right () ->
            putStrLn $ "  ✓  " ++ label
            ++ "\n       ⊢ " ++ show t
            ++ "\n       : " ++ show ty
        Left err ->
            putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err