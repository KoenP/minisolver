module Tests where

import Prelude hiding (maybe, bool)
import Test.QuickCheck
import Control.Monad.State
import Data.Fix
import Data.List
import Control.Lens hiding (Context)
import Control.DeepSeq

import Main
import Canonicalise
import Flatten
import MatchTyFam
import Type
import Inerts
import Substitution
import Constraint
import Context
import Debug.Trace


pair :: Type -> Type -> Type 
pair t1 t2 = AppTy (AppTy (TyCon "Pair") t1) t2
list  = AppTy (TyCon "List")
maybe = AppTy (TyCon "Maybe")
int   = TyCon "Int"
bool  = TyCon "Bool"

metaVar a = (Var (Provided a) (Meta 0))
metaTy  a = TyVarTy (metaVar a)
  
varA  = metaTy "a"
varB  = metaTy "b"
varC  = metaTy "c"
varAlpha = metaTy "alpha"
varBeta  = metaTy "beta"
varGamma = metaTy "gamma"

-- directedUnification :: IO ()
-- directedUnification
--   = expectSuccess cts [("a", (/= int))]
--   where
--     cts = [(TyFamApp fam [varA], int)]
--     fam = TyFam "F" [ax]
--     ax  = FamilyAxiom [int] int
-- 
--     
-- chainedTypeFamilies :: IO ()
-- chainedTypeFamilies
--   -- b ~ Int
--   -- = contextTrace [] (ncs cts, [])
--   = expectSuccess cts [("b", (==int))]
--   where
--     -- b ~ F [Bool]
--     cts = [(varB, TyFamApp fam [list bool])]
-- 
--     -- F [a]  = F a
--     -- F Bool = Int
--     fam = TyFam "F" [ax1, ax2]
-- 
--     ax1 = FamilyAxiom [list varA] (TyFamApp fam [varA])
--     ax2 = FamilyAxiom [bool     ] int

--------------------------------------------------------------------------------

data Test = Test { _testName           :: String
                 , _testGivens         :: [(Type,Type)]
                 , _testSimpleWanteds  :: [(Type,Type)]
                 , _testImplications   :: [Implication]
                 , _testExpectedInerts :: Maybe ([Ct] -> Bool)
                 }

-- Get the residuals from the final inert set.
filterResiduals :: [Ct] -> [Ct']
filterResiduals cts = [ct | (Wanted,ct) <- cts]

-- Convenience function for constructing a _testExpectedInerts field
-- that checks whether the inerts match an exact list, but order
-- doesn't matter.
matchInerts :: [Ct] -> Maybe ([Ct] -> Bool)
matchInerts expectedInerts
  = Just $ \finalInerts -> sort expectedInerts == sort finalInerts

-- Convenience function for constructing a _testExpectedInerts field
-- that checks whether the residual wanteds exactly match what we expect
-- (order doesn't matter).
expectResiduals :: [Ct'] -> Maybe ([Ct] -> Bool)
expectResiduals expectedResiduals
  = Just $ \finalInerts -> sort expectedResiduals == sort (filterResiduals finalInerts)

-- Convenience function for constructing a _testExpectedInerts field
-- that checks whether there are no residual wanteds left.
noResiduals :: Maybe ([Ct] -> Bool)
noResiduals = Just (null . filterResiduals)

unwrapTest :: Test -> ([Ct'], WantedConstraints)
unwrapTest (Test _ givens simples implics _)
  = (map (uncurry CNonCanonical) givens, (map (uncurry CNonCanonical) simples, implics))

-- Step through a test in the console.
debug :: Test -> IO ()
debug test = let (gs,ws) = unwrapTest test in contextTrace getLine gs ws

printFinalInerts :: Test -> IO ()
printFinalInerts = mapM_ (putStrLn . prettyCt) . snd . runTest

-- Run a test to obtain the history of contexts and the final inert set.
runTest :: Test -> ([Context], [Ct])
runTest test = let (gs,ws) = unwrapTest test in simplifyTop gs ws

-- Run a test to obtain the residual constraints
testResiduals :: Test -> [Ct']
testResiduals = (\(_,cts) -> [ct | (Wanted, ct) <- cts]) . runTest

-- A list of residual wanteds is solved if all its residual wanteds are CTyEqCans
-- with no skolems on the lhs.
-- TODO I'm not sure this makes sense. Currently unused though.
isSolved :: [Ct'] -> Bool
isSolved residuals
  = all (\case { CTyEqCan a _ -> isMeta a; _ -> False }) residuals

-- >>> [cts | test <- allTests, let (_,cts) = runTest test]
-- Prelude.undefined
-- CallStack (from HasCallStack):
--   error, called at libraries/base/GHC/Err.hs:80:14 in base:GHC.Err
--   undefined, called at /home/koen/werk/equality-solver/minisolver/src/Tests.hs:397:15 in fake_uid:Tests

-- Run a test and check whether its result matches the expected result.
-- Maybe (a -> Bool) -> a -> Maybe Bool
checkTest :: Test -> Maybe Bool
checkTest test = let result = snd (runTest test)
                 in fmap ($ result) (_testExpectedInerts test) 

allTests :: [Test]
allTests = [ page35_ex1 
           --, page4
           , page35_ex2 
           , example_7_1 
           , reactingGivens 
           , reactingWanteds 
           , page63 
           , needsReaction 
           -- , peytonJonesEtAl
           ]

testReport :: IO ()
testReport
  = let report = [_testName test ++ ": " ++ show (checkTest test) | test <- allTests]
    in report `deepseq` (putStrLn "" >> mapM_ putStrLn report)

--------------------------------------------------------------------------------

kickout :: Test
{-
WI: [G] b ~ U
IS: [W] a ~ T b

[G] b ~ U rewrites [W] a ~ T b

\neg(K2) does not hold because not [W] \geq [W]

But this example will never occur because givens are always fully
processed before wanteds (except in implications, but then the
bindings in the inert set are untouchable).

What about an example with two given constraints?

WI: [G] b ~ U
IS: [G] a ~ T b

This can occur, afaict. Again \neg(K2) does not hold, because
[G] \geq [G], which violates the second subcondition.

So we only get kickouts when the work item's lhs exactly matches
either the lhs or the rhs of an inert set item.

I think if the match is on the rhs, you might even be able to not
kickout but just adjust the item on the spot.
-}
kickout = Test "kickout"
    [ (varA, AppTy (TyCon "T") (varB))
    , (varB, TyCon "U")
    ]
    []
    []
    Nothing

page4 :: Test
{- Non-numbered example on page 4 of OutsideIn(X).

> data T :: * -> * where
>   T1 :: Int -> T Bool
>   T2 :: T a

> test (T1 n) _ = n > 0
> test T2     r = r
-}
page4 = Test "page4" givens wanteds [] Nothing
  where
    givens  = undefined
    wanteds = undefined

page35_ex1 :: Test
{-
Type checking \x -> case x of { T1 n -> n > 0 }.
Here T1 :: forall a. (Bool ~ a) => Int -> T a

Fresh unification variables:
case x of { T1 n -> n > 0 } :: alpha
x :: beta

[W] beta ~ T gamma   (gamma fresh)
[I] gamma ~ Bool => alpha ~ Bool
-}
page35_ex1 = Test
  "page35_ex1"
  []
  [(varB, AppTy (TyCon "T") varGamma)]
  [Implic 0 [] [CNonCanonical varGamma bool] [CNonCanonical varAlpha bool]]
  Nothing

{-
Type checking \x -> case x of { T1 n -> n > 0; T2 -> True }.
Here T1 :: forall a. (Bool ~ a) => Int -> T a

[W] beta ~ T gamma   (gamma fresh)
[I] gamma ~ Bool => alpha ~ Bool
[W] alpha ~ Bool
-}
page35_ex2 :: Test
page35_ex2 = Test
  "page35_ex2"
  []
  [(varBeta, conT varGamma), (varAlpha, bool)]
  [Implic 0 [] [CNonCanonical varGamma bool] [CNonCanonical varAlpha bool]]
  (matchInerts [ (Given, CNonCanonical varAlpha bool)
               , (Given, CNonCanonical varBeta (conT varGamma))
               ])
  where
    conT = AppTy (TyCon "T")

example_7_1 :: Test
  -- The OutsideIn story (no notion of inert set):
  -- 
  -- [G] a   ~ [F a]
  -- [W] G a ~ Bool
  --
  -- > [G] a ~ [F a]  canonicalizes to  ([G] a ~ [beta]) and ([G] F a ~ beta)
  --
  -- [G] a   ~ [beta]
  -- [G] F a ~ beta
  -- [W] G a ~ Bool
  --
  -- > [G] a ~ [beta] and [G] F a ~ beta interact and are replaced by
  -- > ([G] a ~ [beta]) and ([G] F [beta] ~ beta)
  --
  -- [G] a        ~ [beta]
  -- [G] F [beta] ~ beta
  -- [W] G a      ~ Bool
  --
  -- > [G] a ~ [beta] simplifies [W] G a ~ Bool, replacing the latter by
  -- > [W] G [beta] ~ Bool
  --
  -- [G] a        ~ [beta]
  -- [G] F [beta] ~ beta
  -- [W] G [beta] ~ Bool
  --
  -- > G [beta] ~ Bool reacts with top-level axiom G [a] ~ Bool
  --
  -- [G] a        ~ [beta]
  -- [G] F [beta] ~ beta
  -- [W] Bool ~ Bool
  --
  -- > [W] Bool ~ Bool is discharged with refl, and the constraint set is solved.

  -- Used to have an issue:
  -- EQFEQ step is not happening
  -- With [G] a ~ [beta] in inert set,
  -- and F a ~ beta as work item,
  -- F a ~ beta is not being rewritten.
example_7_1 = Test "example_7_1" givens wanteds [] noResiduals
  where
    -- [G] a ~ [F a]
    givens =
      [ (varA, list (TyFamApp f [varA]))
      ]

    -- [W] G a ~ Bool
    wanteds =
      [ (TyFamApp g [varA], bool)
      ]

    -- type instance F [Int] = Int
    -- type instance G [a]   = Bool
    f = TyFam "F" [FamilyAxiom [list int]  int]
    g = TyFam "G" [FamilyAxiom [list varA] bool]

reactingGivens :: Test
{-
  Example given on page 62
  [G] F a ~ Int
  [G] F a ~ a
  [W] F Int ~ a

  > Interaction rule FEQFEQ with xis <- a, xi1 <- Int, xi2 <- a

  [G] F a ~ Int
  [G] a ~ Int   (implicitly canonicalized from Int ~ a)
  [W] F Int ~ a

  > Interaction rule EQFEQ with tv <- a, xi1 <- Int, xis <- a, xi <- Int

  [G] a ~ Int
  [G] F Int ~ Int
  [W] F Int ~ a

  > Simplification rule SFEQFEQ with xis <- Int, xi1 <- Int, xi2 <- a

  [G] a ~ Int
  [G] F Int ~ Int
  [W] a ~ Int

  > Wanted can be discharged (SEQSAME and then canonicalization)

PROBLEM -> fixed
  Non-canonical constraint F a ~ a
  (actually it's canonical but at that point we don't realise it)
  gets flattened into F a ~ _1,
  emitting _1 ~ a.
  ! I'm not sure this is supposed to happen.
  -> I think GHC does this actually.

  Processing _1 ~ a kicks F a ~ _1 out of the inert set.
  ! At first I expected this, but maybe this is not supposed to happen because
  F a ~ _1 will not be rewritten by it...

  But _1 ~ a subsequently does not rewrite F a ~ _1
  (canonicaliseCFunEqCan doesn't rewrite the RHS).
  ! I'm not sure this is supposed to happen.
  -> I think GHC does this too.

  So F a ~ _1 just kicks _1 ~ a out of the inert set, causing an infinite loop.
  This is expected.
-}
reactingGivens = Test "reactingGivens" givens wanteds [] noResiduals
  where
    givens  = [(TyFamApp f [varA], TyCon "Int"), (TyFamApp f [varA], varA)]
    wanteds = [(TyFamApp f [TyCon "Int"], varA)]

    f = TyFam "F" []

reactingWanteds :: Test
reactingWanteds = Test "reactingWanteds" [] wanteds [] noResiduals
  where
    wanteds = [ (TyFamApp f [varGamma], varGamma)
              , (TyFamApp f [varGamma], int)
              ]

    f = TyFam "F" [FamilyAxiom [int] int]


page61 :: Test
-- a ~ b, b ~ c, c ~ b
page61 = Test "page61" givens wanteds [] noResiduals
  where
    givens  = [(varA, varB), (varB, varC), (varC, varB)]
    wanteds = []

page63 :: Test
-- [G] F a ~ Int
-- [W] F a ~ Int
page63 = Test "page63" givens wanteds [] noResiduals
  where
    givens  = [(TyFamApp f [varA], int)]
    wanteds = [(TyFamApp f [varA], int)]
    f = TyFam "F" []

needsReaction :: Test
needsReaction = Test "needsReaction" givens wanteds [] Nothing
  where
    givens = [(TyFamApp f [varA], int), (varA, int)]
    wanteds = []
    f = TyFam "F" [FamilyAxiom [int] int]

-- peytonJonesEtAl :: Test
{-
TODO maybe try this one?

data Eq a b where { Refl :: forall a. Eq a a }

test :: forall a b. Eq a b -> Int
test x = let funny_id = \z -> case x of Refl -> z
         in funny_id 3

x :: Eq a b (skolems)
let funny_id = ... in funny_id 3 :: beta
\z -> case x of Refl -> z :: gamma -> delta
z (param) :: gamma
z (occurrence) :: delta
case x of Refl -> z :: delta

beta ~ Int
a ~ b => delta ~ gamma
-}
-- peytonJonesEtAl = Test "peytonJonesEtAl" givens wanteds implics Nothing
--   where
--     givens  = undefined
--     wanteds = undefined
--     implics = undefined
