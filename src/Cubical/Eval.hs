module Cubical.Eval
    ( eval
    , equivDom
    , isTopDNF, isBotDNF
    ) where

import Cubical.Interval (dnfTop, dnfBot, evalInterval, I(..))
import Cubical.Syntax

--------------------------------------------------------------------------------
-- DNF Helpers
--------------------------------------------------------------------------------

isTopDNF :: Term -> Bool
isTopDNF (TCube d) = d == dnfTop
isTopDNF _         = False

isBotDNF :: Term -> Bool
isBotDNF (TCube d) = d == dnfBot
isBotDNF _         = False

--------------------------------------------------------------------------------
-- Evaluator
--------------------------------------------------------------------------------

-- Forward declaration: definitionallyEqual lives in Equality, but eval needs
-- it for the transport trivial-path check. We break the cycle by inlining a
-- syntactic structural equality here (eval-time only; no eta).
syntacticEq :: Term -> Term -> Bool
syntacticEq = (==)

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

    TEquiv a b ->
        TEquiv (eval a) (eval b)

    TMkEquiv a b f g eta eps ->
        TMkEquiv (eval a) (eval b) (eval f) (eval g) (eval eta) (eval eps)

    TEquivFwd e x ->
        let e' = eval e; x' = eval x
        in case e' of
            TMkEquiv _ _ f _ _ _ -> eval (TApp f x')
            _                    -> TEquivFwd e' x'

    TUa e -> TUa (eval e)

    TTransport p x ->
        let p' = eval p; x' = eval x
        in case p' of

            -- ua e : Path U A B  →  transport (ua e) x  =  equivFwd e x
            TUa e -> eval (TEquivFwd e x')

            PLam iName body ->
                let b0 = eval (beta body (TInterval I0))
                    b1 = eval (beta body (TInterval I1))
                in if syntacticEq b0 b1
                   -- Trivial (constant) path: transport is identity
                   then x'

                   else case (b0, b1) of

                       -- Pi transport:
                       --   p i = Π(a : A i). B i a
                       --   transport p f = λ a1.
                       --     let a0 = transport (⟨i⟩ A (1-i)) a1
                       --     in  transport (⟨i⟩ B i (transp (⟨j⟩ A (i∧j)) a1))
                       --                  (f a0)
                       -- We approximate with the simpler one-sided version that
                       -- is correct for non-dependent codomains and gives a
                       -- reasonable stuck term otherwise.
                       (TPi argName _ _, TPi _ _ _) ->
                           TAbs argName $
                               let fa = TApp (shift 1 0 x') (TVar 0)
                               in eval (TTransport
                                           (PLam iName
                                               (eval (TApp (beta (shift 2 0 body)
                                                               (TInterval I1))
                                                           (shift 2 0 (TVar 0)))))
                                           fa)

                       -- Path transport:
                       --   p i = Path (A i) (u i) (v i)
                       --   transport p q = ⟨j⟩ transport (⟨i⟩ A i) (q @ j)
                       --
                       -- Each point q@j : A 0 is transported to A 1.
                       -- The endpoints land at (transport (⟨i⟩ A i) (u 0))
                       -- and (transport (⟨i⟩ A i) (v 0)), which definitionally
                       -- equal u 1 and v 1 when A,u,v are well-typed.
                       (TPath tyA0 _ _, TPath _ _ _) ->
                           -- Extract the type family A : 𝕀 → U from the body.
                           -- body at i has shape  TPath (A i) (u i) (v i)
                           -- so we reconstruct ⟨i⟩ A i by projecting the type
                           -- component (first arg of TPath).
                           let aFam = PLam iName $
                                   case eval (beta (shift 1 0 body) (TVar 0)) of
                                       TPath a _ _ -> a
                                       _           -> shift 1 0 tyA0
                               -- j is a fresh interval variable (de Bruijn 0
                               -- after we enter the PLam below; aFam is shifted
                               -- to account for the new binder).
                               aFamS = shift 1 0 aFam
                           in PLam "j" $
                               eval (TTransport aFamS
                                       (PApp (shift 1 0 x') (TVar 0)))

                       -- Glue degenerate cases:
                       --   phi = 0  →  Glue A [0] te  =  A,  transport as usual
                       --   phi = 1  →  Glue A [1] te  =  dom(te),  transport via equiv
                       (TGlue aTy0 phi0 te0, TGlue _ _ _) ->
                           if isBotDNF (eval phi0)
                           then eval (TTransport
                                       (PLam iName $
                                           case eval (beta (shift 1 0 body) (TVar 0)) of
                                               TGlue a _ _ -> a
                                               other       -> other)
                                       x')
                           else if isTopDNF (eval phi0)
                           then eval (TTransport
                                       (PLam iName $
                                           case eval (beta (shift 1 0 body) (TVar 0)) of
                                               TGlue _ _ te -> equivDom (eval te)
                                               other        -> other)
                                       x')
                           else TTransport p' x'   -- general Glue: stuck

                       -- Everything else: stuck
                       _ -> TTransport p' x'

            -- Non-lambda path: stuck
            _ -> TTransport p' x'

    TGlue aTy phi te ->
        let phi' = eval phi
        in if isTopDNF phi'
           then equivDom (eval te)
           else if isBotDNF phi'
           then eval aTy
           else TGlue (eval aTy) phi' (eval te)

    TGlueElem phi t a ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval t
           else if isBotDNF phi'
           then eval a
           else TGlueElem phi' (eval t) (eval a)

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