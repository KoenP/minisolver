module Test where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Data.Fix hiding ((~>))
import Data.Either
import Data.Maybe
import Control.Lens hiding (Equality, Context)

data Lit = Lit deriving (Show, Eq)

type Symbol = String

type Type sym = Fix (Type' sym)

data Type' sym t = Var sym | InVar (Invariable t)
  deriving (Show, Eq, Functor)
  
data Invariable t
  = LitTy' Lit
  | AppTy' t t -- Differs from GHC: Includes generative tycons and funtys but not tyfams
  | TyCon' Symbol -- TODO not sure what data this constructor should carry, for now just symbol
  -- I'm making a lot of assumptions and deviations about type family
  -- applications.  I think it's justified for this model to assume
  -- that certain well-formedness properties always hold (think of it
  -- as a preprocessing step that I assumed already happened).  
  -- The only thing we need to know about a type family is what its
  -- axioms are, so I figured I can just store these in the node
  -- itself instead of storing a symbol and then looking that up in
  -- the context. Furthermore, I'm also assuming that type family
  -- applications are always exactly saturated.
  | TyFamApp' [FamilyAxiom t] [t]
  deriving (Show, Eq, Functor)

pattern TyVarTy tv    = Fix (Var tv)
pattern AppTy s t     = Fix (InVar (AppTy' s t))
pattern LitTy l       = Fix (InVar (LitTy' l))
pattern TyCon s       = Fix (InVar (TyCon' s))
pattern TyFamApp f ts = Fix (InVar (TyFamApp' f ts))

foldType :: (sym -> a) -> (Invariable a -> a) -> Type sym -> a
foldType fVar fInVar = cata $ \case
  Var   a -> fVar a
  InVar t -> fInVar t

mapTyVars :: (sym -> Type sym') -> Type sym -> Type sym'
mapTyVars f = foldType f (Fix . InVar)

mapSymbols :: (sym -> sym') -> Type sym -> Type sym'
mapSymbols f = mapTyVars (TyVarTy . f)

--------------------------------------------------------------------------------

-- type instance F Int [a] = a
data FamilyAxiom t = FamilyAxiom [t] t
  deriving (Show, Eq, Functor)

-- Type families have locally quantified variables.
data Scope = Local | Global
  deriving (Show, Eq)

matchAxiom :: Eq s => FamilyAxiom (Type s) -> [Type s] -> Maybe (Type s)
matchAxiom (FamilyAxiom params rhs) args
  = case runUnify $ sequence $ zipWith doUnify params' args' of
      Left  _     -> Nothing
      Right theta -> Just (untagVars $ theta `substType` rhs')
  where
    -- Make sure the variables introduced by the tyfam are fresh.
    params' = map (tagVars Local) params
    rhs'    = tagVars Local rhs
    args'   = map (tagVars Global) args
    tagVars tag = mapSymbols (tag,)
    untagVars = mapSymbols snd

type Scoped = Type (Scope,Symbol)
type UnifyState = Subst (Scope,Symbol)

runUnify :: Eq s
         => ExceptT (Type s,Type s) (State (Subst s)) a
         -> Either (Type s,Type s) (Subst s)
runUnify u = uncurry ($>) (runExceptT u `runState` mempty)
  where ($>) = flip (<$)

ok :: Monad m => m ()
ok = return ()
    
-- TODO everything about this is just guesswork
doUnify :: (MonadError (Type s,Type s) m, MonadState (Subst s) m, Eq s)
        => Type s -> Type s -> m ()
doUnify (LitTy l1)        (LitTy l2)
  | l1 == l2  = ok
  | otherwise = throwError (LitTy l1,LitTy l2)

doUnify (TyCon t1)        (TyCon t2)
  | t1 == t2  = ok
  | otherwise = throwError (TyCon t1,TyCon t2)

doUnify (TyVarTy sym)     t                 = doUnifyVar sym t
doUnify t                 (TyVarTy sym)     = doUnifyVar sym t

doUnify (AppTy t11 t12)   (AppTy t21 t22)   = doUnify t11 t21 >> doUnify t12 t22

-- TODO I need to figure out how GHC deals with these nested type
-- family applications.  I think information from later in the
-- recursion can affect whether a tyfamapp reduces or not.
-- Say we have
-- type instance F Int = Bool
-- (F a, a) = (Bool, Int)
-- Then we can only reduce F a after we found the substitution for a.
-- I think this might not really matter here though...
doUnify (TyFamApp axs ts) t                 = throwError (TyFamApp axs ts,t)
doUnify t                 (TyFamApp axs ts) = throwError (t,TyFamApp axs ts)

doUnify t1                t2                = throwError (t1,t2)


doUnifyVar :: (MonadError (Type s,Type s) m, MonadState (Subst s) m, Eq s)
           => s -> Type s -> m ()
doUnifyVar sym t = do
  theta <- get
  case trySubstVar theta sym of
    Nothing -> modify ((sym ~> t) <>)
    Just t' -> doUnify t' t
--------------------------------------------------------------------------------
-- SUBSTITUTIONS
--------------------------------------------------------------------------------

-- A substitution is a map from type variables onto types.
-- We always substitute fully, that is,
-- if theta = [b -> c] <> [a -> b] (regardless of order), then theta a = c.
-- Applying substitutions is well-defined iff they contain no cycles.
newtype Subst sym = Subst { unSubst :: [(sym, Type sym)] }
  deriving (Show, Eq)


testSubst = ("a" ~> TyVarTy "b")
  <> ("b" ~> AppTy (TyVarTy "c") (TyVarTy "c"))
  <> ("c" ~> LitTy Lit)

-- It can be applied on a type variable.
trySubstVar :: Eq sym => Subst sym -> sym -> Maybe (Type sym)
trySubstVar (Subst theta) sym = sym `lookup` theta

substVar :: Eq sym => Subst sym -> sym -> Type sym
substVar theta sym = fromMaybe (TyVarTy sym) (trySubstVar theta sym)

-- It can be applied on a type.
substType :: Eq sym => Subst sym -> Type sym -> Type sym
substType theta = mapTyVars (substVar theta)

-- Construct a simple substitution by mapping a symbol onto a type.
(~>) :: sym -> Type sym -> Subst sym
sym ~> ty = Subst [(sym,ty)]

-- Substitutions compose.
instance Eq sym => Semigroup (Subst sym) where
  Subst theta1 <> Subst theta2
    = untilFixpoint selfApply $ Subst (theta1 ++ theta2)

selfApply :: Eq sym => Subst sym -> Subst sym
selfApply theta = Subst $ map (over _2 (substType theta)) (unSubst theta)

untilFixpoint :: Eq a => (a -> a) -> a -> a
untilFixpoint f x = fst $ head $ dropWhile (uncurry (/=)) (ys `zip` tail ys)
  where
    ys = iterate f x

-- And we have an identity substitution.
instance Eq sym => Monoid (Subst sym) where
  mempty = Subst []

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
  
-- F [a] = Int
axiom1 = FamilyAxiom [AppTy (TyCon "List") (TyVarTy "a")] (TyCon "Int")
types1 = [ AppTy (TyCon "List") (TyVarTy "b") ]
types2 = [ AppTy (TyCon "List") (TyCon "Bool") ]

-- F [a] = a
axiom2 = FamilyAxiom [AppTy (TyCon "List") (TyVarTy "a")] (TyVarTy "a")
types3 = [ AppTy (TyCon "List") (TyVarTy "b") ]
types4 = [ AppTy (TyCon "List") (TyCon "Bool") ]
types5 = [ AppTy (TyCon "Maybe") (TyCon "Bool") ]

type family F a b

type instance F a a = Int

foo :: F Int Int
foo = 3

-- F a Int = a
-- F 

-- Examples with type family F a b
-- 1. A tyfam can have "linked" arguments; simple substitution won't
--    cut it, we need a prolog-like unification algorithm
-- > F a a = a       
-- 
-- 2. But unification doesn't go both ways.
-- > F a a = Int
-- > foo :: F Bool Bool
--    -> here Bool should *not* be unified with a
--
-- So perhaps the best approach is to rewrite F a a = Int to F a b =
-- Int and emit an equality a ~ b?
-- Or should this be locally solved?
