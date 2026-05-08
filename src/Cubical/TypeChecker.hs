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

import Cubical.Interval (I(..))
import Cubical.Syntax
import Cubical.Eval (eval, isTopDNF, isBotDNF)
import Cubical.Equality (definitionallyEqualCtx)

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
        Other msg -> "  " ++ msg

extendCtx :: Name -> Term -> Ctx -> Ctx
extendCtx x ty ctx = (x, ty) : ctx

lookupCtx :: Int -> Ctx -> Either TypeError Term
lookupCtx i ctx
    | i < 0 || i >= length ctx = Left (UnboundVariable ("#" ++ show i))
    | otherwise = Right (shift (i + 1) 0 (snd (ctx !! i)))

requireEqual :: Ctx -> Term -> Term -> Either TypeError ()
requireEqual ctx expected got
    | definitionallyEqualCtx ctx expected got = Right ()
    | otherwise = Left (TypeMismatch (eval expected) (eval got))

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
    -- 1. base must have type A
    check ctx base aTy'
    -- 2. Check the tube and enforce the boundary condition tube @ 0 ≡ base
    _ <- case eval tube of
        PLam i body -> do
            -- The tube body lives under a fresh interval variable i : 𝕀.
            -- A must be shifted so its de Bruijn indices are valid in the
            -- extended context.
            let ctx'  = extendCtx i intervalTy ctx
                aTy'S = shift 1 0 aTy'
            check ctx' body aTy'S
            -- Boundary check: (tube @ 0) must be definitionally equal to base.
            -- tube @ 0  =  body[i := 0]
            let tubeAt0 = eval (beta body (TInterval I0))
            requireEqualEndpt ctx tubeAt0 (eval base)
        tube' -> do
            -- For a non-lambda tube we require it to be a path over A,
            -- then enforce the same boundary condition.
            tubeTy <- infer ctx tube'
            case eval tubeTy of
                TPath a u _
                    | definitionallyEqualCtx ctx a aTy' ->
                        -- u is tube @ 0; it must equal base.
                        requireEqualEndpt ctx (eval u) (eval base)
                    | otherwise ->
                        Left (TypeMismatch (eval aTy') (eval a))
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