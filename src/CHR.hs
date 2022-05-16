module CHR where

import qualified Type as T
import Constraint (TyEq, Flavour)
import Substitution (Subst, substType)
import qualified Substitution as S

data Var = FlatVar Int | TVar T.Var 
    deriving (Show, Eq)

type Type = T.PType Var

data Constraint = Eq Flavour Type Type
    deriving (Show, Eq)

data Rule = Rule { _kHeads :: [Constraint] 
                 , _rHeads :: [Constraint]
                 , _guards :: [Constraint] -> [Constraint] -> Bool
                 , _rhs    :: [Constraint]
                 }

substConstraint :: Subst Var -> Constraint -> Constraint
substConstraint theta (Eq f t1 t2) 
    = Eq f (substType theta f t1) (substType theta f t2)