module Cubical.Env
    ( GlobalEnv
    , globalCtx
    , applyGlobals
    , inferWithEnv
    , checkWithEnv
    ) where

import Cubical.Syntax (Name, Term(..), shift, subst)
import Cubical.TypeChecker (Ctx, TypeError, infer, check)

--------------------------------------------------------------------------------
-- Global Named Environment
--------------------------------------------------------------------------------

-- | A global definition: (name, type, value).
-- Stored most-recent first.
type GlobalEnv = [(Name, Term, Term)]

-- | Build a Ctx from a GlobalEnv. Variables are ordered innermost-first,
-- so we reverse the env.
globalCtx :: GlobalEnv -> Ctx
globalCtx genv = map (\(n, ty, _) -> (n, ty)) (reverse genv)

-- | Substitute all global definitions into a term directly via de Bruijn
-- substitution, rather than wrapping in TApp/TAbs chains.
--
-- The parser assigns globals indices starting at (length localEnv).
-- At the top level localEnv is empty, so globals occupy indices 0..n-1
-- with the most-recent global at index 0.
--
-- We substitute one global at a time, outermost (highest index) first,
-- so that earlier substitutions don't disturb the indices of later ones.
-- After substituting index k, we shift the term down by 1 to close the gap.
applyGlobals :: GlobalEnv -> Term -> Term
applyGlobals genv t = foldr substGlobal t indexedVals
  where
    n            = length genv
    -- genv is most-recent first; reverse gives oldest first.
    -- Oldest global has the highest index (n-1), newest has index 0.
    vals         = map (\(_, _, v) -> v) (reverse genv)
    indexedVals  = zip [n-1, n-2 .. 0] vals

    -- Substitute the global at de Bruijn index k with its value v,
    -- then shift the whole term down by 1 to account for the removed binding.
    substGlobal (k, v) body =
        shift (-1) k (subst k (shift k 0 v) body)

-- | Infer the type of a term in the context of a GlobalEnv.
inferWithEnv :: GlobalEnv -> Term -> Either TypeError Term
inferWithEnv genv t = infer (globalCtx genv) t

-- | Check a term against a type in the context of a GlobalEnv.
checkWithEnv :: GlobalEnv -> Term -> Term -> Either TypeError ()
checkWithEnv genv t ty = check (globalCtx genv) t ty