module Inference where

--------------------------------------------------------------------------------
import Data.Fix

import qualified Type
import Type hiding (Symbol)
--------------------------------------------------------------------------------

type TypedTerm ty = Fix TypedTermF

type Term ty = Fix TermF

data TypedTermF tm = Typed (TermF tm) Type

data TermF tm = VarTm Symbol
              | AppTm tm tm
              | AbsTm Symbol tm
              | CaseTm tm [(Pattern, tm)]
  deriving (Eq, Ord, Functor, Foldable)

data Pattern = Pattern Constructor [Symbol]
  deriving (Eq, Ord)

data Constructor = Constructor 
  deriving (Eq, Ord)

type Symbol = String
