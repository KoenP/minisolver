module Substitution where

--------------------------------------------------------------------------------
import Data.Monoid
import Data.Maybe
import Control.Lens

import Type
import Constraint
--------------------------------------------------------------------------------

-- A substitution is a map from type variables onto types.
-- We always apply substitutions fully, so if we have theta =
-- [a -> b], [b -> c], then theta a = c.
-- Applying substitutions is well-defined iff they contain no cycles.
newtype Subst sym = Subst { unSubst :: [TyEq sym] }
  deriving (Show, Eq)

-- It can be applied on a type variable.
trySubstVar :: Eq sym => Subst sym -> Flavour -> sym -> Maybe (PType sym)
trySubstVar (Subst theta) f a
  = listToMaybe [t | TyEq f' a' t <- theta, a == a', f' `rewrites` f]

substRewritesVar :: Eq sym => Subst sym -> Flavour -> sym -> Bool
substRewritesVar theta f a = isJust $ trySubstVar theta f a

substVar :: Eq sym => Subst sym -> Flavour -> sym -> PType sym
substVar theta f sym = fromMaybe (TyVarTy sym) (trySubstVar theta f sym)

-- It can be applied on a type.
substType :: Eq sym => Subst sym -> Flavour -> PType sym -> PType sym
substType theta f = mapTyVars (substVar theta f)

substRewritesType :: Eq sym => Subst sym -> Flavour -> PType sym -> Bool
substRewritesType theta f = foldType (substRewritesVar theta f) or

-- Remove entries from a substitution based on a predicate.
filterSubst :: (TyEq sym -> Bool) -> Subst sym -> Subst sym
filterSubst p (Subst theta) = Subst $ filter p theta

-- Retain only those entries from a substitution that are not skolem
-- and have a matching TcLevel.
filterTcLevel :: TcLevel -> Subst Var -> Subst Var
filterTcLevel lvl theta = filterSubst p theta
  where p (TyEq _ (Var _ Skolem)      _) = False
        p (TyEq _ (Var _ (Meta lvl')) _) = lvl == lvl'

-- Convenience function to apply a substitution to a constraint.
substCt :: Subst Var -> Ct -> Ct
substCt theta (f, CTyEqCan a ty       )
  = (f, CNonCanonical (substVar theta f a) (substType theta f ty))
substCt theta (f, CFunEqCan fam args a)
  = (f, CNonCanonical (TyFamApp fam (map (substType theta f) args)) (substVar theta f a))
substCt theta (f, CNonCanonical ty1 ty2)
  = (f, CNonCanonical (substType theta f ty1) (substType theta f ty2))
substCt theta (f, CIrredCan ty1 ty2)
  = (f, CIrredCan (substType theta f ty1) (substType theta f ty2))

-- Convenience function to apply a substitution to the rhs of an a ~ t equality.
substTyEq :: Eq sym => Subst sym -> TyEq sym -> TyEq sym
substTyEq theta (TyEq f a t) = TyEq f a (substType theta f t)

substRewritesTyEq :: Eq sym => Subst sym -> TyEq sym -> Bool
substRewritesTyEq theta (TyEq f a t)
  = substRewritesVar theta f a || substRewritesType theta f t

-- Add a single entry to a substitution
extend :: Eq sym => Flavour -> sym -> PType sym -> Subst sym -> Subst sym
extend f a t = (Subst [TyEq f a t] <>)

-- Substitutions compose.
instance Eq sym => Semigroup (Subst sym) where
  Subst theta1 <> Subst theta2
    = untilFixpoint selfApply $ Subst (theta1 ++ theta2)

-- Apply a substitution to itself, once on every entry.
selfApply :: Eq sym => Subst sym -> Subst sym
selfApply theta = Subst $ map (substTyEq theta) (unSubst theta)

-- Repeatedly apply a function to a value, until it stops changing.
-- Warning: termination depends entirely on whether the function has a fixpoint
-- for the particular starting value.
untilFixpoint :: Eq a => (a -> a) -> a -> a
untilFixpoint f x = fst $ head $ dropWhile (uncurry (/=)) (ys `zip` tail ys)
  where
    ys = iterate f x

-- And we have an identity substitution.
instance Eq sym => Monoid (Subst sym) where
  mempty = Subst []
