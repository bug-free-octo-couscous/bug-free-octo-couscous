module Cubical.Equality
    ( definitionallyEqual
    , definitionallyEqualCtx
    , definitionallyEqualCtxR
    , etaEq
    , EtaResult(..)
    , reducePAppByType
    ) where

import Cubical.Interval (I(..))
import Cubical.Syntax
import Cubical.Eval (eval, isTopDNF, isBotDNF)

-- Ctx imported from TypeChecker would create a cycle, so we re-alias here.
-- The full Ctx type lives in TypeChecker; equality only needs the list shape.
type Ctx = [(Name, Term)]

--------------------------------------------------------------------------------
-- Term size (used to derive eta-expansion fuel)
--------------------------------------------------------------------------------

-- | Structural node count of a term.  Used as a lower bound on eta fuel so
-- that the fuel scales with the problem rather than being a magic constant.
termSize :: Term -> Int
termSize t = case t of
    TVar _               -> 1
    TUniv _              -> 1
    TIntervalTy          -> 1
    TInterval _          -> 1
    TCube _              -> 1
    TAbs _ b             -> 1 + termSize b
    PLam _ b             -> 1 + termSize b
    TApp f a             -> 1 + termSize f + termSize a
    PApp p r             -> 1 + termSize p + termSize r
    TPi _ a b            -> 1 + termSize a + termSize b
    TPath a u v          -> 1 + termSize a + termSize u + termSize v
    TEquiv a b           -> 1 + termSize a + termSize b
    TMkEquiv a b f g e s -> 1 + termSize a + termSize b + termSize f
                              + termSize g + termSize e + termSize s
    TEquivFwd e x        -> 1 + termSize e + termSize x
    TUa e                -> 1 + termSize e
    TTransport p x       -> 1 + termSize p + termSize x
    THComp a ph u u0     -> 1 + termSize a + termSize ph + termSize u + termSize u0
    TGlue a ph te        -> 1 + termSize a + termSize ph + termSize te
    TGlueElem ph x a     -> 1 + termSize ph + termSize x + termSize a
    TUnglue ph te g      -> 1 + termSize ph + termSize te + termSize g

-- | Starting fuel for an eta-equality check between two already-evaluated
-- terms.  We use the combined term size as the base, with a minimum floor of
-- 16 so trivially small terms still get a reasonable number of steps.
--
-- Justification: each eta-expansion step (TAbs/PLam vs neutral, or PApp
-- boundary reduction) produces a term whose size is at most the size of the
-- original plus a constant (the freshly introduced @TVar 0@ and @shift@).
-- Structural congruence steps strictly decrease size.  So the combined size
-- is a sound — though not tight — upper bound on the number of useful
-- eta-expansion steps.
initialFuel :: Term -> Term -> Int
initialFuel t1 t2 = max 16 (termSize t1 + termSize t2)

--------------------------------------------------------------------------------
-- Eta-equality result
--------------------------------------------------------------------------------

-- | Three-valued result of eta-equality.
--
-- @Equal@   — the two terms are definitionally equal.
-- @NotEqual@ — they are definitionally distinct (normal termination).
-- @Exhausted@ — fuel ran out before a verdict could be reached; the checker
--               should report this as an ambiguous/inconclusive result rather
--               than silently treating it as @NotEqual@.
data EtaResult = Equal | NotEqual | Exhausted
    deriving (Eq, Show)

-- | Combine two 'EtaResult's under conjunction (both must be 'Equal').
--   'Exhausted' is infectious: if either side exhausted fuel the overall
--   result is 'Exhausted', because we cannot claim inequality.
andResult :: EtaResult -> EtaResult -> EtaResult
andResult Equal    r         = r
andResult _        Exhausted = Exhausted
andResult Exhausted _        = Exhausted
andResult NotEqual _         = NotEqual

--------------------------------------------------------------------------------
-- Context-free definitional equality
--------------------------------------------------------------------------------

definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq (initialFuel v1 v2) [] v1 v2 == Equal

definitionallyEqualCtx :: Ctx -> Term -> Term -> Bool
definitionallyEqualCtx ctx t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq (initialFuel v1 v2) ctx v1 v2 == Equal

-- | Like 'definitionallyEqualCtx' but surfaces fuel exhaustion as a distinct
-- 'EtaResult' so callers can emit a proper error instead of a false mismatch.
definitionallyEqualCtxR :: Ctx -> Term -> Term -> EtaResult
definitionallyEqualCtxR ctx t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in if v1 == v2 then Equal
       else etaEq (initialFuel v1 v2) ctx v1 v2

--------------------------------------------------------------------------------
-- Path boundary reduction
--------------------------------------------------------------------------------

-- | If p : Path A u v and r is I0/I1, return the endpoint.
reducePAppByType :: Ctx -> Term -> Term -> Maybe Term
reducePAppByType ctx p r =
    case inferTy ctx p of
        Just (TPath _ u v) ->
            let r' = eval r
            in if isBotDNF r' || r' == TInterval I0 then Just (eval u)
               else if isTopDNF r' || r' == TInterval I1 then Just (eval v)
               else Nothing
        _ -> Nothing
  where
    inferTy c (TVar i)
        | i >= 0, i < length c = Just (eval (shift (i+1) 0 (snd (c !! i))))
        | otherwise             = Nothing
    inferTy c (TApp f a) =
        case inferTy c f of
            Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
            _                  -> Nothing
    inferTy _ _ = Nothing

--------------------------------------------------------------------------------
-- Lightweight neutral type inference (used by etaEq for lambda domains)
--------------------------------------------------------------------------------

inferNeutralTy :: Ctx -> Term -> Maybe Term
inferNeutralTy ctx (TVar i)
    | i >= 0, i < length ctx = Just (eval (shift (i+1) 0 (snd (ctx !! i))))
    | otherwise               = Nothing
inferNeutralTy ctx (TApp f a) =
    case inferNeutralTy ctx f of
        Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
        _                  -> Nothing
inferNeutralTy _ _ = Nothing

inferLamDom :: Ctx -> Term -> Term -> Term
inferLamDom ctx (TAbs _ _) neutral =
    case inferNeutralTy ctx neutral of
        Just (TPi _ domTy _) -> eval domTy
        _                    -> TUniv 0
inferLamDom _ _ _ = TUniv 0

--------------------------------------------------------------------------------
-- Core eta-equality
--------------------------------------------------------------------------------

-- | @etaEq fuel ctx t1 t2@ checks whether @t1@ and @t2@ are definitionally
-- equal under context @ctx@, using @fuel@ to bound eta-expansion steps.
--
-- == Fuel discipline
--
-- Fuel is consumed *only* by eta-expansion steps and path-boundary reductions
-- — the cases that may not decrease the syntactic size of the terms being
-- compared.  Structural congruence cases (matching constructors on both sides)
-- make strictly smaller recursive calls and therefore do *not* consume fuel;
-- decrementing fuel there would make the bound sensitive to term size in an
-- unhelpful way and would cause spurious 'Exhausted' results on large but
-- simple terms.
--
-- == Why 'EtaResult' instead of 'Bool'
--
-- Returning 'False' on fuel exhaustion is misleading: the checker cannot tell
-- whether the terms are unequal or whether it just ran out of steps.  Callers
-- that receive 'Exhausted' should surface it as an inconclusive result (e.g.
-- a dedicated 'TypeError') rather than reporting a false type mismatch.
etaEq :: Int -> Ctx -> Term -> Term -> EtaResult
etaEq 0 _ _ _ = Exhausted
etaEq fuel ctx t1 t2
    | t1 == t2  = Equal

    -- Path boundary reduction (eta-expansion step: consumes fuel)
    | PApp p r <- t1, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx u t2
    | PApp p r <- t2, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx t1 u

    -- Lambda eta (eta-expansion step: consumes fuel)
    | TAbs x b1 <- t1, TAbs _ b2 <- t2
    = etaEq (fuel-1) ((x, inferLamDom ctx t1 t2) : ctx) (eval b1) (eval b2)
    | TAbs x b2 <- t2
    = let ctx' = (x, inferLamDom ctx t2 t1) : ctx
      in etaEq (fuel-1) ctx' (eval (TApp (shift 1 0 t1) (TVar 0))) (eval b2)
    | TAbs x b1 <- t1
    = let ctx' = (x, inferLamDom ctx t1 t2) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval (TApp (shift 1 0 t2) (TVar 0)))

    -- Path-lambda eta (eta-expansion step: consumes fuel)
    | PLam i b1 <- t1, PLam _ b2 <- t2
    = etaEq (fuel-1) ((i, TIntervalTy) : ctx) (eval b1) (eval b2)
    | PLam i b2 <- t2
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval (PApp (shift 1 0 t1) (TVar 0))) (eval b2)
    | PLam i b1 <- t1
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval (PApp (shift 1 0 t2) (TVar 0)))

    -- Congruence on neutral spines (structural: no fuel consumed)
    | TApp f1 a1 <- t1, TApp f2 a2 <- t2
    = etaEq fuel ctx f1 f2 `andResult` etaEq fuel ctx a1 a2
    | PApp p1 r1 <- t1, PApp p2 r2 <- t2
    = etaEq fuel ctx p1 p2 `andResult` etaEq fuel ctx r1 r2

    -- Type congruence (structural: no fuel consumed)
    | TPi _ a1 b1 <- t1, TPi _ a2 b2 <- t2
    = etaEq fuel ctx a1 a2 `andResult` etaEq fuel ctx b1 b2
    | TPath ty1 u1 v1 <- t1, TPath ty2 u2 v2 <- t2
    = etaEq fuel ctx ty1 ty2
      `andResult` etaEq fuel ctx u1 u2
      `andResult` etaEq fuel ctx v1 v2

    | otherwise = NotEqual