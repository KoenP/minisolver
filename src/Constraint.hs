module Constraint where

--------------------------------------------------------------------------------
import Control.Lens hiding (Equality)
import Data.List

import Type
--------------------------------------------------------------------------------


-- Q: can we have given implications? The non-existence of a
-- solveGivens function seems to imply the answer is "no"
type WantedConstraints = ([Ct'], [Implication])

data Flavour = Given
             | Wanted
             | Bland -- Bit of a hack, TODO: explain or refactor away
             deriving (Show, Eq, Ord)

flavourTag :: Flavour -> String
flavourTag Wanted = "[W]"
flavourTag Given  = "[G]"

rewrites :: Flavour -> Flavour -> Bool
_      `rewrites` Bland  = True
Bland  `rewrites` _      = True
Given  `rewrites` _      = True  -- Givens rewrite everything
Wanted `rewrites` _      = False -- Wanteds don't rewrite anything

type Ct = (Flavour, Ct')

data Ct'
  -- Equality between type variable and type.
  -- a ~ ty 
  = CTyEqCan Var Type

  -- Equality between saturated type function application and type variable.
  -- F ts ~ a 
  | CFunEqCan (TyFam Type) [Type] Var

  -- Non-canonical equality, nothing is known yet about its structure.
  -- ty1 ~ ty2
  | CNonCanonical Type Type

  -- Irreducible equality, e.g. Int ~ Bool.
  | CIrredCan Type Type
  deriving (Show, Eq, Ord)

ncs :: [(Type,Type)] -> [Ct']
ncs eqs = [CNonCanonical ty1 ty2 | (ty1,ty2) <- eqs]

prettyCt :: Ct -> String
prettyCt (f, ct) = unwords [flavourTag f, lhs , "~", rhs] ++ case ct of
  CNonCanonical _ _ -> " (NC)"
  CIrredCan     _ _ -> " !!"
  CTyEqCan      _ _ -> " (ty)"
  CFunEqCan   _ _ _ -> " (fun)"
  where
    (lhs,rhs) = case ct of
      CTyEqCan (Var a _) ty        -> (show a, prettyPType ty)
      CFunEqCan fam args (Var a _) -> (prettyPType (TyFamApp fam args), show a)
      CNonCanonical ty1 ty2        -> (prettyPType ty1, prettyPType ty2)
      CIrredCan     ty1 ty2        -> (prettyPType ty1, prettyPType ty2)

instance Occurs Var Ct' where
  a `occurs` CTyEqCan b ty         = a == b || a `occurs` ty
  a `occurs` CFunEqCan _ args b    = a == b || any (a `occurs`) args
  a `occurs` CNonCanonical ty1 ty2 = a `occurs` ty1 || a `occurs` ty2
  a `occurs` CIrredCan ty1 ty2     = a `occurs` ty1 || a `occurs` ty2

-- mapCtTypes :: (PType sym -> PType sym') -> PType sym -> PType sym'
-- mapCtTypes fun (f,ct) = (f, case ct of
--   CTyEqCan      a t        -> CTyEqCan a (fun t)
--   CFunEqCan     fam args a -> CFunEqCan fam map 
--   CNonCanonical t1 t2      -> CNonCanonical
--   CIrredCan     t1 t2      -> CIrredCan)

data TyEq  sym = TyEq Flavour sym (PType sym)
  deriving (Show, Eq)

instance Eq sym => Occurs sym (TyEq sym) where
  a `occurs` TyEq _ b ty = a == b || occurs a ty

prettyTyEq :: Show sym => TyEq sym -> String
prettyTyEq (TyEq f a ty) = unwords [flavourTag f, show a, "~", prettyPType ty]

tyEqToCt :: TyEq Var -> Ct
tyEqToCt (TyEq f a ty) = (f, CTyEqCan a ty)

data FunEq sym = FunEq Flavour (TyFam (PType sym)) [PType sym] sym
  deriving (Show, Eq)

instance Eq sym => Occurs sym (FunEq sym) where
  a `occurs` FunEq _ _ args b = a == b || any (occurs a) args

prettyFunEq :: Show sym => FunEq sym -> String
prettyFunEq (FunEq f fam args a) = unwords
  [flavourTag f, prettyPType (TyFamApp fam args), "~", show a]

funEqToTyEq :: FunEq sym -> TyEq sym
funEqToTyEq (FunEq f fam args a) = TyEq f a (TyFamApp fam args)

funEqToCt :: FunEq Var -> Ct
funEqToCt (FunEq f fam args a) = (f, CFunEqCan fam args a)

findFunEq :: Eq sym
          => TyFam (PType sym) -> [PType sym] -> [FunEq sym] -> Maybe (FunEq sym)
findFunEq fam args funeqs = find match funeqs
  where match (FunEq _ fam' args' _) = fam == fam' && args == args'

-- A generic equality, with information about its flavour or role
-- (that part is TODO).
data Equality = Eq Flavour Type Type
  deriving Show

prettyEquality :: Equality -> String
prettyEquality (Eq f ty1 ty2)
  = unwords [flavourTag f, prettyPType ty1, "~", prettyPType ty2]

-- Final step to apply to inerts after unflattening: discharge the
-- reflexivity constraints.
dischargeWithRefl :: [Ct] -> [Ct]
dischargeWithRefl = filter $ \case
  (_, CNonCanonical ty1 ty2) | ty1 == ty2 -> False
  _                                       -> True

--------------------------------------------------------------------------------
-- IMPLICATIONS
--------------------------------------------------------------------------------
data Implication = Implic { ic_tclvl  :: TcLevel
                          , ic_skols  :: [Var]
                          , ic_given  :: [Ct']
                          , ic_wanted :: [Ct']
                          }

--------------------------------------------------------------------------------
-- WORK LIST
--------------------------------------------------------------------------------

-- A todo list for constraints that still have to be rewritten.
data WorkList = WorkList { _eqs :: [Ct], _tyFunEqs :: [Ct] } deriving Show
makeLenses ''WorkList

emptyWorkList :: WorkList
emptyWorkList = WorkList [] []

popWorkList :: WorkList -> Maybe (Ct, WorkList)
popWorkList (WorkList (eq:eqs) tfEqs)        = Just (eq  , WorkList eqs tfEqs)
popWorkList (WorkList []       (tfEq:tfEqs)) = Just (tfEq, WorkList []  tfEqs)
popWorkList _                                = Nothing

mapWorkList :: (Ct -> Ct) -> WorkList -> WorkList
mapWorkList f (WorkList eqs funeqs) = WorkList (map f eqs) (map f funeqs)

mergeWorkLists :: WorkList -> WorkList -> WorkList
mergeWorkLists (WorkList eqs1 funeqs1) (WorkList eqs2 funeqs2)
  = WorkList (eqs1 ++ eqs2) (funeqs1 ++ funeqs2)

prettyWorkList :: WorkList -> String
prettyWorkList (WorkList eqs funeqs)
  = unlines $ ("Work List:":) $ map (indent . prettyCt) (eqs ++ funeqs)
  where
    indent = ("  "++)
