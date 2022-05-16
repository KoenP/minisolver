-- Top-level reactions.
-- Fig 24 p 64 in OutsideIn
-- topReactionsStage in TcInteract in GHC.

module React where

--------------------------------------------------------------------------------
import Debug.Trace

import Type
import Constraint
import Context
import Flatten
import MatchTyFam
--------------------------------------------------------------------------------

-- If we have a F tys ~ a
-- Then we look up a matching axiom F params ~ rhs
-- We unify a with a flattened theta(rhs) (where theta maps params onto tys).
topReactionsStage :: Ct -> ContextM (Maybe Ct)
topReactionsStage ct@(f, CFunEqCan fam args a)
  -- TODO: check if this rendering of occurs check is correct.
  -- I've skipped "improvement" for now.
  | any (a `occurs`) args = continue ct
  | otherwise = case reduceTyFamAppFully fam args of
      Nothing -> continue ct -- TODO add "improvement"
      Just ty -> do
         flatTy <- flatten f ty
         dischargeFunEq f a flatTy
         stop

topReactionsStage ct = continue ct -- TODO check this

-- shortCutRecution :: Var -> FunEq Var -> ContextM ()
-- shortCutRecution a (FunEq f fam args b)
--   = emitWork $ CFunEqCan f 

dischargeFunEq :: Flavour -> Var -> Type -> ContextM ()
dischargeFunEq Given a ty
  -- TODO: This is probably not right, but I don't fully understand
  -- dischargeFunEq in TcSMonad.
  = emitWork (Given, CTyEqCan a ty)
dischargeFunEq f a ty
  -- Handling this differently than GHC, I'm keeping the separate case to emphasize this.
  -- In GHC we "unflatten", really just unification.
  = emitWork (Given, CTyEqCan a ty)

{- Questions
- Why unflattening in dischargeFunEq? How to model? In general, I have difficulty mapping the unflattening story of GHC onto the unflattening story of OutsideIn.
- What's "improvement"?
-

-}
