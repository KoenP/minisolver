module MatchTyFam where

--------------------------------------------------------------------------------
import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Data.Maybe

import Type
import Substitution
import Constraint
--------------------------------------------------------------------------------

data Unifiable = Unifiable | NotUnifiable
  deriving (Show, Eq)

type UnifyState = Subst (Unifiable,Symbol)


-- Fully reduces a type family application, that is, it applies a
-- single-step reduction and then checks if the result is another type
-- family application. If it is, it tries to reduce that recursively,
-- otherwise it stops. Returns Nothing if the tyfam application was
-- not reduced at all.
-- TODO: what to do with nested type family applications?
-- Assumes *without checking* that the application is *exactly* saturated.
reduceTyFamAppFully :: Eq sym => TyFam (PType sym) -> [PType sym] -> Maybe (PType sym)
reduceTyFamAppFully fam@(TyFam _ axs) args = case reduceTyFamAppStep fam args of
  Nothing                    -> Nothing
  Just (TyFamApp fam'@(TyFam _ axs') args')
    -> reduceTyFamAppFully fam' args' <|> Just (TyFamApp fam args')
  Just t                     -> Just t
  
-- Try to perform a single type family reduction.
-- Assumes *without checking* that the application is *exactly* saturated.
reduceTyFamAppStep :: Eq sym => TyFam (PType sym) -> [PType sym] -> Maybe (PType sym)
reduceTyFamAppStep fam@(TyFam _ axs) args
  = safeHead
  . catMaybes
  . map (\ax -> matchAxiom ax args)
  $ axs
  where
    safeHead (x:_) = Just x
    safeHead []    = Nothing

  -- listToMaybe [ t | ax <- axs, let Just t = matchAxiom ax args ]

matchAxiom :: Eq s => FamilyAxiom (PType s) -> [PType s] -> Maybe (PType s)
matchAxiom (FamilyAxiom params rhs) args
  = case runUnify $ sequence $ zipWith doUnify params' args' of
      Left  _     -> Nothing
      Right theta -> Just (untagVars $ substType theta Bland rhs')
  where
    -- Make sure the variables introduced by the tyfam are fresh.
    params'     = map (tagVars Unifiable) params
    rhs'        = tagVars Unifiable rhs
    args'       = map (tagVars NotUnifiable) args
    tagVars tag = mapSymbols (tag,)
    untagVars   = mapSymbols snd

-- runUnify :: Eq s
--          => ExceptT (Type s,Type s) (State (Subst s)) a
--          -> Either (Type s,Type s) (Subst s)
runUnify u = uncurry ($>) (runExceptT u `runState` mempty)
  where ($>) = flip (<$)

okIfSame :: (Eq a, MonadError (e,e) m) => (a -> e) -> a -> a -> m ()
okIfSame report x y | x == y    = return ()
                    | otherwise = throwError (report x, report y)
    
-- TODO This can use some cleanup
doUnify :: (MonadError (PType (Unifiable,s),PType (Unifiable,s)) m
           , MonadState (Subst (Unifiable,s)) m
           , Eq s)
        => PType (Unifiable,s) -> PType (Unifiable,s) -> m ()
doUnify (LitTy l1)                   (LitTy l2)
  = okIfSame LitTy l1 l2

doUnify (TyCon t1)                   (TyCon t2)
  = okIfSame TyCon t1 t2

doUnify (TyVarTy (Unifiable,a))      t
  = doUnifyVar a t

doUnify t                            (TyVarTy (Unifiable,a))
  = doUnifyVar a t
    -- TODO: Not sure if this case should ever occur.

doUnify (TyVarTy a@(NotUnifiable,_)) (TyVarTy b@(NotUnifiable,_))
  = okIfSame TyVarTy a b

doUnify (AppTy t11 t12)   (AppTy t21 t22)
  = doUnify t11 t21 >> doUnify t12 t22

-- TODO I need to figure out how GHC deals with these nested type
-- family applications.  I think information from later in the
-- recursion can affect whether a tyfamapp reduces or not.
-- Say we have
-- type instance F Int = Bool
-- (F a, a) = (Bool, Int)
-- Then we can only reduce F a after we found the substitution for a.
-- I don't expect us to deal with that here though.
doUnify (TyFamApp axs ts) t
  = throwError (TyFamApp axs ts,t)

doUnify t                 (TyFamApp axs ts)
  = throwError (t,TyFamApp axs ts)

doUnify t1                t2
  = throwError (t1,t2)


doUnifyVar :: ( MonadError (PType (Unifiable,s),PType (Unifiable,s)) m
              , MonadState (Subst (Unifiable,s)) m
              , Eq s)
           => s -> PType (Unifiable,s) -> m ()
doUnifyVar a t = do
  theta <- get
  case trySubstVar theta Bland (Unifiable,a) of
    Nothing -> modify (extend Bland (Unifiable,a) t)
    Just t' -> doUnify t' t

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- Examples with type family F a b
-- 1. A tyfam can have "linked" arguments; simple substitution won't
--    cut it, we need a prolog-like unification algorithm
-- > F a a = a       
-- 
-- 2. But unification doesn't go both ways.
-- > F a a = Int
-- > foo :: F Bool Bool
--    -> here Bool should *not* be unified with a
