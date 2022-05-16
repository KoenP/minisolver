module Canonicalise where

--------------------------------------------------------------------------------
import Control.Monad.State
import Control.Applicative
import Debug.Trace

import Type
import Constraint
import Context
import MatchTyFam
import Flatten
--------------------------------------------------------------------------------

-- Argument to canonicalise that records whether a constraint has
-- already been flattened.
data Flat = IsFlat | NotFlat


-- Entry point of the canonicaliser.
canonicalise :: Ct -> ContextM (Maybe Ct)
canonicalise (f, CNonCanonical t1 t2)
  = canonicalise' NotFlat (Eq f t1 t2)
canonicalise (f, CTyEqCan a ty)
  = canonicalise' NotFlat (Eq f (TyVarTy a) ty)
canonicalise (f, CFunEqCan fam args a)
  = canonicaliseCFunEqCan f fam args a
canonicalise ct
  = continue ct


-- TODO question: why is the notion of canonicity different in GHC compared to OutsideIn?
alreadyCanonical :: Equality -> Maybe Ct
alreadyCanonical (Eq f (TyVarTy a) ty)
  | isXiType ty && not (a `occurs` ty) = Just (f, CTyEqCan a ty)
alreadyCanonical (Eq f (TyFamApp fam args) (TyVarTy a)) -- Deviation from OutsideIn!
  | all isXiType args = Just (f, CFunEqCan fam args a)
alreadyCanonical _
  = Nothing

---------------------------------
-- Main workhorse of this module.
-- TODO (postponed): add Given/Wanted specific behaviour.
canonicalise' :: Flat -> Equality -> ContextM (Maybe Ct)
  -- Handling type variables.
canonicalise' IsFlat (Eq f (TyVarTy tv1) (TyVarTy tv2))
  | tv1 ==     tv2 = stop
  | tv1 `swap` tv2 = canonicaliseTyVarEq f tv2 (TyVarTy tv1)
  | otherwise      = canonicaliseTyVarEq f tv1 (TyVarTy tv2)
canonicalise' IsFlat eq@(Eq f (TyVarTy tv1) ty2)
  = canonicaliseTyVarEq f tv1 ty2
canonicalise' IsFlat (Eq f ty1 (TyVarTy tv2))
  = canonicaliseTyVarEq f tv2 ty1

  -- Type literals and constructors.
canonicalise' _ (Eq _ (LitTy l1) (LitTy l2)) | l1 == l2 = stop
canonicalise' _ (Eq _ (TyCon c1) (TyCon c2)) | c1 == c2 = stop

  -- Type applications.
  -- Note: Once roles are introduced, properly review this one
canonicalise' IsFlat (Eq f (AppTy s1 t1) (AppTy s2 t2)) = case f of
  Wanted -> unifyWanted s1 s2 >> unifyWanted t1 t2 >> stop
  Given  -> emitWork (Given, CNonCanonical t1 t2) -- emitWork = put on work list
            >> canonicalise' NotFlat (Eq f s1 s2) -- TODO: GHC seems to call with NotFlat, does this make sense?

  -- If all else fails, try flattening.
canonicalise' NotFlat (Eq f ty1 ty2) = do
  newEq <- liftA2 (Eq f) (flatten f ty1) (flatten f ty2)
  traceM $ "new eq = " ++ prettyEquality newEq
  -- wl <- _workList <$> get
  -- traceM $ "worklist1 = " ++ show wl
  result <- canonicalise' IsFlat newEq
  -- wl <- _workList <$> get
  -- traceM $ "worklist2 = " ++ show wl
  return result

  -- And if that didn't work, abort mission.
  -- TODO (postponed): re-check when roles are put in
canonicalise' IsFlat (Eq f ty1 ty2) = failure f ty1 ty2
---------------------------------

-- Canonicalise an equality of the shape a ~ ty.
canonicaliseTyVarEq :: Flavour -> Var -> Type -> ContextM (Maybe Ct)
canonicaliseTyVarEq f tv ty
  | tv `occurs` ty = traceM ("canontyvareq " ++ show tv ++ " " ++ prettyPType ty) >> failure f (TyVarTy tv) ty
  | otherwise      = continue (f, CTyEqCan tv ty)

canonicaliseCFunEqCan :: Flavour -> TyFam Type -> [Type] -> Var -> ContextM (Maybe Ct)
canonicaliseCFunEqCan f fam args a = do
  args' <- mapM (flatten f) args
  return (Just (f, CFunEqCan fam args' a))

-- TODO massively oversimplified and possibly wrong
unifyWanted :: Type -> Type -> ContextM ()
unifyWanted t1 t2 = emitWork (Wanted, CNonCanonical t1 t2)

type family F a
type instance F [Int] = Int
type family G a
type instance G [a] = Bool

g :: forall b. b -> G b
g = undefined

f :: forall a. (a ~ [F a]) => a -> Bool
f x = g x
