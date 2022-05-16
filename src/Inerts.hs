module Inerts where

import Data.List
import Control.Lens

import Type
import Constraint
import Substitution

-- The inert set.
data InertCans sym = InertCans { _inertEqs    :: [TyEq sym]
                               , _inertFunEqs :: [FunEq sym] -- ?
                               , _inertIrred  :: [(PType sym,PType sym)]
                               }
  deriving Show
makeLenses ''InertCans

prettyInerts :: Show sym => InertCans sym -> String
prettyInerts (InertCans eqs funeqs irreds)
  = unlines
  ["Inert Set:"
  , unlines (map indent prettyEqs)
  ]
  where
    prettyEqs = map prettyTyEq eqs ++ map prettyFunEq funeqs ++ map prettyIrred irreds
    prettyIrred (ty1,ty2) = unwords [prettyPType ty1, "~", prettyPType ty2, "!!"]
    indent = ("  " ++)

extractResidualWanteds :: InertCans Var -> [Ct']
extractResidualWanteds (InertCans eqs funeqs irreds)
  =  [ct                | (Wanted, ct) <- map tyEqToCt  eqs   ]
  ++ [ct                | (Wanted, ct) <- map funEqToCt funeqs]
  ++ [CIrredCan ty1 ty2 | (ty1,ty2)    <- irreds              ]

emptyInertCans :: InertCans sym
emptyInertCans = InertCans [] [] []

unflattenedInerts :: Subst Var -> InertCans Var -> [Ct]
unflattenedInerts phi ics = map (substCt phi) $ inertsToCts ics

addInertTyEq :: TyEq sym -> InertCans sym -> InertCans sym
addInertTyEq eq = over inertEqs (eq:)

addInertFunEq :: FunEq sym -> InertCans sym -> InertCans sym
addInertFunEq funEq = over inertFunEqs (funEq:)

addInertIrred :: (PType sym,PType sym) -> InertCans sym -> InertCans sym
addInertIrred eq = over inertIrred (eq:)

inertsToSubst :: InertCans sym -> Subst sym
inertsToSubst (InertCans eqs funeqs _) = Subst eqs -- ++ map funEqToTyEq funeqs

inertsToCts :: InertCans Var -> [Ct]
inertsToCts (InertCans eqs funeqs irreds)
  = map tyEqToCt eqs ++ map funEqToCt funeqs ++ map irredToCt irreds
  where
    irredToCt (ty1,ty2) = (Bland, CIrredCan ty1 ty2)

noIrreds :: InertCans sym -> Bool
noIrreds = null . _inertIrred

-- kickoutConditions ([fw] a ~ t) ([fs] b ~ s)
-- rewritesTyEq fw a ([fs] b ~ s)
kickoutConditions :: TyEq Var -> TyEq Var -> Bool
kickoutConditions (TyEq fw a _) (TyEq fs b s) = not (k0 || (k1 && k2 && k3))
  -- work list item = [fw] a -> t
  -- inert set item = [fs] b -> s
  where
    k0 = not (fw `rewrites` fs)
    k1 = a /= b
    k2 = not (fs `rewrites` fs) || fs `rewrites` fw || not (a `occurs` s)
    k3 = case s of TyVarTy a' -> a /= a' -- TODO (postponed): works only for nominals
                   _          -> True

rewritesTyEq' :: Flavour -> Var -> TyEq Var -> Bool
rewritesTyEq' f a eq = kickoutConditions (TyEq f a undefined) eq

rewritesTyEq :: Flavour -> Var -> TyEq Var -> Bool
rewritesTyEq f a eq
  -- TODO Implementation is a bit of a hack
  = substRewritesTyEq (Subst [TyEq f a undefined]) eq 

-- TODO look into this
-- rewritesFunEq :: TyEq Var -> FunEq Var -> Bool
-- rewritesFunEq eq (FunEq f _ args _) = any (substRewritesType (Subst [eq]) f) args

-- TODO really check this thoroughly with Richard
-- TODO TODO TODO: ask about ct_pred stuff
kickoutRewritable' :: Flavour -> Var -> InertCans Var -> (WorkList,InertCans Var)
kickoutRewritable' f a (InertCans eqs funeqs irreds)
  = ( WorkList (map tyEqToCt workEqs) (map funEqToCt workFuneqs)
    , InertCans eqs' funeqs' irreds
    )
  where
    (workEqs   , eqs'   )
      = partition (rewritesTyEq f a) eqs

    (workFuneqs, funeqs')
      = partition (rewritesTyEq f a . funEqToTyEq) funeqs
    --  (workEqs   , eqs'   )
    --    = partition (\ct@(TyEq f' _ _   ) -> occurs a ct &&  f `rewrites` f') eqs

    --  (workFuneqs, funeqs')
    --    = partition (\ct@(FunEq f' _ _ _) -> occurs a ct &&  f `rewrites` f') funeqs

-- >>> kickoutRewritable 

-- See maybeKickout in TcSMonad.
-- Only CTyEqCans are used for rewriting, so only they cause kickout.
kickoutRewritable :: InertCans Var -> Ct -> (WorkList, InertCans Var)
kickoutRewritable ics (f, CTyEqCan a _)
  = kickoutRewritable' f a ics
kickoutRewritable ics _
  = (emptyWorkList, ics)

-- Remove duplicates from the inert set. Not essential for solving.
nubInerts :: Eq sym => InertCans sym -> InertCans sym
nubInerts (InertCans eqs funeqs irreds) = InertCans (nub eqs) (nub funeqs) (nub irreds)
