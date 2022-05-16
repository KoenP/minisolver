-- This module describes the state carried around in the constraint
-- rewriting pipeline.

module Context where

--------------------------------------------------------------------------------
import Control.Lens hiding (Context, Equality)
import Control.Monad.State
import Debug.Trace
import Data.Maybe
import Data.Either

import Type
import Constraint
import Substitution
import Inerts
--------------------------------------------------------------------------------

-- While processing constraints, we keep track of some state.
type ContextM = State Context
data Context = Context
  { _workList  :: WorkList
  , _inerts    :: InertCans Var
  , _unflatten :: Subst Var 
  , _nextFresh :: Int       -- Used to generate fresh variables.
  , _curLvl    :: TcLevel   -- TODO: no idea if this is how GHC keeps track of it
  }
makeLenses ''Context
  
runContextM :: ContextM a -> a
runContextM = flip evalState (Context (WorkList [] []) emptyInertCans mempty 0 0)

-- Edit any field of the context via an appropriate lens.
editContext :: ASetter Context Context f f -> (f -> f) -> ContextM ()
editContext lens f = modify (over lens f)

-- Add a constraint to the work list.
emitWork :: Ct -> ContextM ()
emitWork ct@(_, CFunEqCan _ _ _) = editContext (workList.tyFunEqs) (ct:)
emitWork ct                      = editContext (workList.eqs     ) (ct:)

introduceFlattenVariable :: Flavour -> TyFam Type -> [Type] -> ContextM Type
introduceFlattenVariable f fam args = do
  alpha <- fresh
  emitWork (f, CFunEqCan fam args alpha)
  editContext unflatten (extend Bland alpha (TyFamApp fam args))
  return (TyVarTy alpha)

-- Pop a work item from the stack and return it.
selectNextWorkItem :: ContextM (Maybe Ct)
selectNextWorkItem = do
  item <- fmap (popWorkList . view workList) get
  case item of
    Nothing      -> return Nothing
    Just (ct,wl) -> do { {-traceM ("next work item = " ++ prettyCt ct);-} editContext workList (const wl); return (Just ct) }

-- TODO: I added kickout, but is it correct?
addInertCan :: Ct -> ContextM ()
addInertCan (f,ct) = do
  kickoutRewritableConstraints (f,ct)
  editContext inerts (addInert f ct)
  where
    addInert :: Flavour -> Ct' -> InertCans Var -> InertCans Var
    addInert f (CTyEqCan a t)  = addInertTyEq (TyEq f a t)
    addInert f (CFunEqCan fam args a) = addInertFunEq (FunEq f fam args a)
    addInert f (CIrredCan t1 t2) = addInertIrred (t1,t2)
    -- TODO: refine the types
    addInert f ct = error
      $ "Tried to add "
      ++ show ct
      ++ " with flavour "
      ++ show f
      ++ " to inerts, but inerts can only contain TyEqs and FunEqs."

-- Unify a variable and a type. This works a bit differently from how
-- GHC does it: in GHC a variable is a mutable reference cell, and
-- unification updates the variable in-place wherever it occurs
-- (though we still need to zonk and therefore kick out). Here we just
-- add a given to the inert set.
-- TODO: it's a CONJECTURE that these two are equivalent, I should look into this more!
-- unify :: Var -> Type -> ContextM ()
-- unify a ty = addInertCan (Given, CTyEqCan a ty)

-- Kick out all constraints in the inert set that are rewritable by
-- the argument, and prepend them to the work list.
-- TODO: should check the exact order of the work list.
kickoutRewritableConstraints :: Ct -> ContextM ()
kickoutRewritableConstraints ct = do
  ics <- view inerts <$> get
  let (wl, ics') = kickoutRewritable ics ct
  traceM $ "Kicked out: " ++ show wl
  editContext inerts   (const ics')
  editContext workList (mergeWorkLists wl)

-- Apply the inert substitution if it has a binding for the relevant
-- type variable. Otherwise, return Nothing.
tryInerts :: Flavour -> Var -> ContextM (Maybe Type)
tryInerts f tv = do
  theta <- inertsToSubst . view inerts <$> get
  lvl   <- view curLvl <$> get
  let theta' = filterTcLevel lvl theta
  return $ trySubstVar theta' f tv

tryInerts' :: Flavour -> Var -> ContextM (Either Type Type)
tryInerts' f tv = inform (TyVarTy tv) <$> tryInerts f tv

{-
-- Apply the inert substitution to a type.
-- TODO all of this code might be useless (handled in flattening)
zonkType :: Flavour -> Type -> ContextM Type
zonkType f ty = (\theta -> substType theta f ty) . inertsToSubst . view inerts <$> get

tryZonkType :: Flavour -> Type -> ContextM (Maybe Type)
tryZonkType f ty = inertsRewriteType f ty >>= \case
  True  -> Just <$> zonkType f ty
  False -> return Nothing

tryZonkType' :: Flavour -> Type -> ContextM (Either Type Type)
tryZonkType' f ty = inform ty <$> tryZonkType f ty

inertsRewriteType :: Flavour -> Type -> ContextM Bool
inertsRewriteType f ty = (\theta -> substRewritesType theta f ty) .  inertsToSubst . view inerts <$> get

-- Apply the inert substitution to a constraint.
-- TODO: completely based on intuition, not GHC. Check with Richard.
zonkEq :: Equality -> ContextM Equality
zonkEq (Eq f ty1 ty2) = do
  ty1' <- zonkType f ty1
  ty2' <- zonkType f ty2
  return (Eq f ty1' ty2')
  
zonkCt :: Ct -> ContextM Ct
zonkCt (f, CNonCanonical ty1 ty2) = do
  ty1' <- zonkType f ty1
  ty2' <- zonkType f ty2
  return (f, CNonCanonical ty1' ty2')
zonkCt ct@(f, CTyEqCan a ty) = do
  a'  <- tryInerts' f a
  ty' <- tryZonkType' f ty
  case (a', ty') of
    (Left _, Left _) -> return ct
    _                -> return (f, CNonCanonical (valueOrDefault a') (valueOrDefault ty'))
zonkCt ct@(f, CFunEqCan fam args a) = do
  args' <- mapM (tryZonkType' f) args
  a'    <- tryInerts' f a
  if any isRight args' || isRight a'
    then return (f, CNonCanonical (TyFamApp fam (map valueOrDefault args')) (valueOrDefault a'))
    else return ct
zonkCt (f, CIrredCan ty1 ty2) = do
  ty1' <- zonkType f ty1
  ty2' <- zonkType f ty2
  return (f, CIrredCan ty1' ty2')
-}

-- zonktest = runContextM $ do
--   editContext inerts $ \_ -> InertCans [TyEq Given (Provided "a",0) (TyCon "Bool")] [] []
--   zonkCt (Wanted, CFunEqCan (TyFam "F" undefined) [TyCon "Int", TyVarTy (Provided "b",0)]  (Provided "b",0))

-- Lift a Maybe into an Either by adding an error message
-- to the Nothing case.
inform :: b -> Maybe a -> Either b a
inform b = maybe (Left b) Right

-- Generate a fresh variable.
fresh :: ContextM Var
fresh = do
  n <- view nextFresh <$> get
  editContext nextFresh (+1)
  lvl <- view curLvl <$> get
  return (Var (Fresh n) (Meta lvl))

-- Corresponds to the `Stop :: ... -> StopOrContinue a` constructor in GHC.
stop          :: ContextM (Maybe Ct)
stop          = return Nothing

-- Corresponds to the `ContinueWith :: a -> StopOrContinue a` constructor in GHC.
continue      :: Ct -> ContextM (Maybe Ct)
continue      = return . Just

-- Corresponds to `ContinueWith CIrredCan` in GHC.
failure :: Flavour -> Type -> Type -> ContextM (Maybe Ct)
failure f t1 t2 = continue (f, CIrredCan t1 t2)
