module Interact where
-- TODO Questions
-- * Where do we handle EQDIFF (fig 22 p 61)
-- * OutsideIn has a separate simplification relation (fig 23 p 63). Is it right
--   that GHC does both interaction and simplification in its Interact stage?


--------------------------------------------------------------------------------
import Control.Lens
import Control.Monad.State
import Debug.Trace

import Type
import Context
import Constraint
import Inerts
--------------------------------------------------------------------------------

interactWithInerts :: Ct -> ContextM (Maybe Ct)
-- GHC Precondition: if the workitem is a CTyEqCan then it will not be able to
-- react with anything at this stage.
-- K: another precondition is that ct is definitely canonical now.
interactWithInerts workItem@(f, ct) = do
  ics <- _inerts <$> get
  case ct of
    -- a ~ ty
    -- a = variable
    -- ty = any type (xi?)
    CTyEqCan  a ty       -> interactTyVarEq ics (TyEq f a ty)
    CFunEqCan fam args a -> interactFunEq   ics (FunEq f fam args a)
    CIrredCan {}         -> continue workItem
    CNonCanonical {}     -> error
                            $ "non-canonical constraint in interactWithInerts: "
                            ++ show ct

interactTyVarEq :: InertCans Var -> TyEq Var -> ContextM (Maybe Ct)
interactTyVarEq ics eq | inertsCanDischarge ics eq
  -- There's an exact match in the inert set, so we consider the constraint solved.
  -- TODO case for derived emits work in GHC, not sure I interpreted this right though
  = stop 
interactTyVarEq _   (TyEq Given a ty)
  -- Our constraint is a Given, we can't simplify it by interaction with the inert set.
  -- TODO actually I don't fully understand this.
  -- TODO case dropped with representational equalities.
  = {-traceM "interact" >> -} continue (Given, CTyEqCan a ty)
interactTyVarEq _   (TyEq f     a ty)
  -- TODO I don't understand why this is in interaction, since we don't
  --      even look at the inert set.
  --      It seems to deal with the same problem as EQSAME (fig 22, p61)
  --      And perhaps also with EQFEQ?

  = do lvl <- _curLvl <$> get
       if canSolveByUnification lvl a ty
         -- This works differently from how GHC does it.
         -- Based on Richard's comment in TcInteract.
         then continue (Given, CTyEqCan a ty)
         else continue (f    , CTyEqCan a ty)

-- We can solve an equality of the form a ~ t if a is touchable.
-- We're ignoring the distinction of TyVarTvs (see note Signature
-- skolems in TcType.hs)
canSolveByUnification :: TcLevel -> Var -> Type -> Bool
canSolveByUnification lvl var _ = isTouchable lvl var
                       

-- TODO (postponed): simplified away a case for derived constraints.
-- Consider the TyEq solved if
-- * it's of the form a ~ ty and the inerts contain a ~ ty, or
-- * it's of the form a ~ b and the inerts contain b ~ a.
inertsCanDischarge :: InertCans Var -> TyEq Var -> Bool
inertsCanDischarge ics (TyEq f a ty) = c1 || c2
  where
    c1 = not $ null [() | TyEq f' a' ty' <- eqs , a' == a, ty' == ty, f' `rewrites` f]
    c2 = case ty of
      TyVarTy b -> not $ null
         [() | TyEq f' b' (TyVarTy a') <- eqs , a' == a, b' == b, f' `rewrites` f]
      _         -> False
    eqs = _inertEqs ics

data Swapped = NotSwapped | IsSwapped deriving (Eq, Show)

-- TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO
-- funEqCanDischarge should implement FEQFEQ I think.
-- I think this function implements the rule FEQFEQ in fig 22, p61,
-- that is, say we have F as ~ b and F as ~ c, then we
-- conclude F as ~ b and we unify c with b.
-- TODO: this whole function. I don't understand what's going on with
-- funEqCanDischargeF, it seems it would never apply.
-- And I also don't understand improveLocalFunEqs yet, it does not
-- seem to implement FEQFEQ.
interactFunEq :: InertCans Var -> FunEq Var -> ContextM (Maybe Ct)
interactFunEq ics (FunEq f fam args a) = continue (f, CFunEqCan fam args a)
  -- do
  -- match <- findFunEq fam args . view (inerts.inertFunEqs) <$> get
  -- case match of
  --   Just (FunEq f' fam' args' a') -> 

-- I think with just Given and Wanted, funEqCanDischarge will always return False
-- From GHC:
-- funEqCanDischargeF :: CtFlavour -> CtFlavour -> (SwapFlag, Bool)
-- funEqCanDischargeF Given           _               = (NotSwapped, False)
-- funEqCanDischargeF _               Given           = (IsSwapped,  False)
-- funEqCanDischargeF (Wanted WDeriv) _               = (NotSwapped, False)
-- funEqCanDischargeF _               (Wanted WDeriv) = (IsSwapped,  True)
-- funEqCanDischargeF (Wanted WOnly)  (Wanted WOnly)  = (NotSwapped, False)
-- funEqCanDischargeF (Wanted WOnly)  Derived         = (NotSwapped, True)
-- funEqCanDischargeF Derived         (Wanted WOnly)  = (IsSwapped,  True)
-- funEqCanDischargeF Derived         Derived         = (NotSwapped, False)
  
--------------------------------------------------------------------------------
-- Some useful GHC notes
--------------------------------------------------------------------------------
{-
Note [The Solver Invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We always add Givens first.  So you might think that the solver has
the invariant

   If the work-item is Given,
   then the inert item must Given

But this isn't quite true.  Suppose we have,
    c1: [W] beta ~ [alpha], c2 : [W] blah, c3 :[W] alpha ~ Int
After processing the first two, we get
     c1: [G] beta ~ [alpha], c2 : [W] blah
Now, c3 does not interact with the given c1, so when we spontaneously
solve c3, we must re-react it with the inert set.  So we can attempt a
reaction between inert c2 [W] and work-item c3 [G].

It *is* true that [Solver Invariant]
   If the work-item is Given,
   AND there is a reaction
   then the inert item must Given
or, equivalently,
   If the work-item is Given,
   and the inert item is Wanted/Derived
   then there is no reaction
-}
