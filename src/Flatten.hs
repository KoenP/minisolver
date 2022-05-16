module Flatten where

import Control.Monad.State
import Control.Applicative
import Debug.Trace

import Type
import Constraint
import Context
import MatchTyFam

{-
Some notes on flattening substitution.
I think the OutsideIn solver does not use unflattening during solving, it
-}
  

-- Flattening does three things:
-- 1. Applies the ambient substitution stored in mutable unification
--    variables (= zonking)
-- 2. Applies the substitution embodied in the inert set (needs to
--    know the flavour)
-- 3. Replaces type family applications with their fmv/fsk variables
--    (and emits suitable constraints in the flattening work-list)
-- TODO (postponed) for now this is just FlattenAll mode
flatten :: Flavour -> Type -> ContextM Type
flatten _ ty@(LitTy _) = return ty

-- Type variables. We'll try both the ambient substitution and, only
-- if that failed, the inert set. If either one succeeds, we
-- immediately recur.
-- This assumes that we never have a substitution a -> a, otherwise
-- this will not terminate.
-- TODO (postpoined) properly review this case once flavours are introduced.
--      *The* flavour check happens in this case.
flatten f (TyVarTy tv)
  = tryInerts f tv >>= \case
       Just ty -> flatten f ty
       Nothing -> return (TyVarTy tv)

  -- = tryAmbient f tv >>= \case
  --     Just ty -> flatten f ty
  --     Nothing -> tryInerts f tv >>= \case
  --       Just ty -> flatten f ty
  --       Nothing -> return (TyVarTy tv)

-- flatten Wanted a
-- -> flatten Wanted (AppTy List beta)
--    -> flatten Wanted List
--       -> List
--    -> flatten Wanted beta
--       -> flatten Wanted (F a)
--         -> flatten Wanted a


-- TODO (postponed): flatten_app_tys: we can as a first approximation pretend that
-- it just recurs on ty1 and ty2.  When we come back to worrying about
-- kinds, we'll revisit this.
-- This is a big simplification, introducing kinds and roles here
-- causes complications.
flatten f (AppTy t1 t2) = liftA2 AppTy (flatten f t1) (flatten f t2)

flatten f ty@(TyCon _) = return ty

-- TODO (postponed): review once flavours are introduced.
-- I've structured types slightly differently to simplify the model.
-- Type family applications are a separate node in the Type datatype.
-- They are always exactly saturated. Say that you have an oversaturated
-- tyfam F a b, and F a is saturated. In GHC this would be a
-- TyConApp applied to [a,b], here it's a AppTy (TyFamApp a) b.
-- I'm also not modeling the cache here.
flatten f (TyFamApp fam tys) = flattenTyFamApp f fam tys

-- GHC story, simplified (stopping at the first step that makes any progress):
-- 1. Try reducing without flattening arguments (wihtout cache lookup).
-- 2. Flatten the arguments, (and try to reduce by cache lookup, but I don't do this).
-- 3. Try to reduce directly (with flattened arguments).
-- 4. Make new flatten skolem alpha. Emit F as ~ alpha as work and return alpha.
-- I implement this without the cache lookup part.
flattenTyFamApp :: Flavour -> TyFam Type -> [Type]
                -> ContextM Type
flattenTyFamApp f fam args
  = case reduceTyFamAppFully fam args of
      Just ty -> return ty

      -- If that doesn't work, flatten the arguments and try again (steps 2-3).
      Nothing -> do
        flatArgs <- mapM (flatten f) args
        case reduceTyFamAppFully fam flatArgs of
          Just ty -> return ty

          -- Failed again, emit work (step 4). This work is already canonical.
          Nothing -> introduceFlattenVariable f fam flatArgs
            -- alpha <- fresh
            -- emitWork (f, CFunEqCan fam flatArgs alpha)
            -- return (TyVarTy alpha)
