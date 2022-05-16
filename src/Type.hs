module Type where

import Data.Fix hiding ((~>))
import Data.Char
import Data.List
import Control.Applicative

-- TYPE ------------------------------------------------------------------------

type Type = PType Var

-- Types parameterized on which representation they use for type variable
-- symbols.
type PType sym = Fix (Type' sym)

prettyPType :: Show sym => PType sym -> String
prettyPType = cata $ \case
  VarTy tv                              -> show tv
  InVarTy (AppTy' s t)                  -> concat ["(", s, " ", t ,")"]
  InVarTy (LitTy' l)                    -> show l
  InVarTy (TyCon' s)                    -> s
  InVarTy (TyFamApp' (TyFam name _) ts) -> concat ["(", name, " ", concat (intersperse " " ts) ,")"]


-- Open recursive version of Type.
-- While experimenting it was useful to have the distinction between tyvar
-- and non-tyvar nodes live at a separate level, but I might merge them again
-- if it turns out to be unnecessary.
data Type' sym t = VarTy sym | InVarTy (Invariable t)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

  
-- The nodes in the Type AST which are not type variables.
data Invariable t
  = LitTy' Lit
  | AppTy' t t -- Differs from GHC: Includes generative tycons and funtys but not tyfams
  | TyCon' TyConSym 

  -- I'm making a lot of assumptions and deviations about type family
  -- applications.  I think it's justified for this model to assume
  -- that certain well-formedness properties always hold (think of it
  -- as a preprocessing step that I assumed already happened).  
  -- The only thing we need to know about a type family is what its
  -- axioms are, so I figured I can just store these in the node
  -- itself instead of storing a symbol and then looking that up in
  -- the context. Furthermore, I'm also assuming that type family
  -- applications are always exactly saturated.
  | TyFamApp' (TyFam t) [t]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- Type families.
-- I think I can consider the construction of type family axioms to
-- have happened before the program I'm writing, so I just assume
-- they're all well-formed.
data TyFam t = TyFam String [FamilyAxiom t] deriving (Ord, Functor, Foldable, Traversable)

instance Show (TyFam t) where
  show (TyFam name _) = name

instance Eq (TyFam t) where
  TyFam name1 _ == TyFam name2 _ = name1 == name2

-- F a b ~ t is rendered as `FamilyAxiom [TyVarTy "a", TyVarTy "b"] t`
data FamilyAxiom t = FamilyAxiom [t] t
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- Literals; TODO check which ones I need.
data Lit = Lit
  deriving (Show, Eq, Ord)

-- Symbols representing type constructors.
type TyConSym = String

-- Some shorthands for nodes in the Type AST.
pattern TyVarTy tv    = Fix (VarTy tv)
pattern AppTy s t     = Fix (InVarTy (AppTy' s t))
pattern LitTy l       = Fix (InVarTy (LitTy' l))
pattern TyCon s       = Fix (InVarTy (TyCon' s))
pattern TyFamApp f ts = Fix (InVarTy (TyFamApp' f ts))

appTy :: PType sym -> [PType sym] -> PType sym
appTy t1 ts = foldl AppTy t1 ts

-- Structured recursion on Types.
foldType :: (sym -> a) -> (Invariable a -> a) -> PType sym -> a
foldType fVar fInVar = cata $ \case
  VarTy   a -> fVar a
  InVarTy t -> fInVar t

foldTypeM :: Monad m => (sym -> m a) -> (Invariable a -> m a) -> PType sym -> m a
foldTypeM fVar fInVar = cataM $ \case
  VarTy   a -> fVar a
  InVarTy t -> fInVar t

-- Transform each of the tyvar nodes, keeping the rest of the AST structure.
mapTyVars :: (sym -> PType sym') -> PType sym -> PType sym'
mapTyVars f = foldType f (Fix . InVarTy)

-- Apply a function to each of the tyvar symbols in the AST.
mapSymbols :: (sym -> sym') -> PType sym -> PType sym'
mapSymbols f = mapTyVars (TyVarTy . f)

-- Check whether the symbol occurs freely in the type.
class Eq sym => Occurs sym e | e -> sym where
  occurs :: sym -> e -> Bool

instance Eq sym => Occurs sym (PType sym) where
  occurs a = foldType (==a) or

isXiType :: PType sym -> Bool
isXiType = foldType (const True) $ \case
  TyFamApp' _ _ -> False
  ty            -> and ty

-- SYMBOL ----------------------------------------------------------------------

-- Might not be the most sensible representation: I don't think
-- skolems have TcLevels.
type TcLevel = Int
data Touchability = Skolem | Meta TcLevel deriving (Eq, Ord, Show)
data Var = Var Symbol Touchability deriving (Eq, Ord)

instance Show Var where
  show (Var a Skolem)   = concat ["|", show a, "|"]
  show (Var a (Meta n)) = show a ++ if n > 0 then '@':show n else ""

-- A symbol is either a user-provided string or a generated integer.
data Symbol = Provided String | Fresh Int
  deriving Eq

isSkolem, isMeta :: Var -> Bool
isSkolem (Var _ Skolem) = True
isSkolem _              = False
isMeta = not . isSkolem

-- in GHC there's more subtlety here around flattening, haven't looked
-- into that yet
isTouchable :: TcLevel -> Var -> Bool
isTouchable ctxLevel (Var _ (Meta varLevel)) = ctxLevel == varLevel
isTouchable _        _                       = False

instance Ord Symbol where
  compare (Provided s) (Provided t) = compare s t
  compare (Fresh    n) (Fresh    m) = compare n m
  compare (Provided _) (Fresh    _) = GT
  compare (Fresh    _) (Provided _) = LT

-- String representation:
-- Just the string without quotes for Provided variables
-- Underscore followed by decimal integer for Fresh variables
instance Show Symbol where
  show (Provided s) = s
  show (Fresh n)    = '_' : show n

instance Read Symbol where
  readsPrec p ('_':s) = [ (Fresh n,rem) | (n,rem) <- readsPrec p s ]
  readsPrec p (x  :s) | isLower x = [(Provided variable, remainder)]
    where
      validChar = liftA2 (||) isAlphaNum (== '_')
      variable  = x : takeWhile validChar s
      remainder = dropWhile validChar s
  readsPrec _ _       = []

-- Check whether two type variables should be swapped.
-- TODO, for now just alphabetically
swap :: Var -> Var -> Bool
swap (Var a _) (Var b _) = a `swapSymbol` b
  
swapSymbol :: Symbol -> Symbol -> Bool
swapSymbol = (>)
