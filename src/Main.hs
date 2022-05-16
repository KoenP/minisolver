module Main where

{-
TODO
* Add implication constraints
* Add tc levels
* Add tests
* Variable swapping?
* What is the ambient substitution again?

TODO
!!! Unflatten after solving the simple wanteds (see GHC note in interac  | isTouchableMetaTyVar tclvl tv
t)
-}


import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Data.Either
import Data.Maybe
import Data.Char
import Control.Lens hiding (Equality, Context)
import Debug.Trace

import Type
import Constraint
import Canonicalise
import Interact
import React
import Context
import Substitution
import Inerts

main :: IO ()
main = undefined

contextTrace :: IO a -> [Ct'] -> WantedConstraints -> IO ()
contextTrace interrupt givens wanteds = mapM_ (\str -> putStr str >> interrupt) (trace ++ [hor, final])
  where
    trace = [ "At level " ++ show lvl ++ "\n" ++ prettyInerts ics ++ prettyWorkList wl ++ "\n" ++ hor
            | ctx <- contexts
            , let wl  = view workList ctx
            , let ics = view inerts   ctx
            , let lvl = view curLvl   ctx
            ]
    (contexts, finalInerts) = simplifyTop givens wanteds
    hor = "----------------------------\n"

    final =
      let
        ctx = last contexts
        ics = view inerts ctx
        phi = view unflatten ctx
      in 
        "final inerts = \n" ++ unlines (map (("  "++) . prettyCt) finalInerts) 

--      "final inerts = \n" ++ (prettyInerts $ view inerts $ last contexts) -- ++ show (map (substCt phi) $ inertsToCts $ _inerts $ last contexts) ++ "\n"
    phi = _unflatten $ last contexts

-- Mirrors simplifyTop in TcSimplify.
-- In OutsideIn(X), this corresponds to the solv signature in fig 14, p40.
-- The way the inputs are passed works a bit differently though.
--
-- \mathcal{Q} in the paper are the top-level axioms.
-- For now, the only top-level axioms in the implementation are type
-- family instances. These instances are inlined in the TyFamApp constructor
-- for the `Type` type.
--
-- The function returns a full trace of the context after every work
-- item processed, as well as the final inert set (as a list of constraints).
-- In the final inert set, some equations may be marked as non-canonical when
-- they are, in fact, canonical (at this point the distinction doesn't
-- matter though).

simplifyTop :: [Ct'] -> WantedConstraints -> ([Context], [Ct])
simplifyTop givens wcs = runContextM $ do
  -- First we "solve" the givens (simplify as much as possible and add
  -- them to the inert set).
  trace1 <- solveGivens givens
  -- traceM $ "trace1 worklists = " ++ show (map _workList trace1)

  -- Then we solve the simple wanteds.
  (trace2, residuals) <- solveWanteds wcs
  
  -- To return the result, we extract the relevant state.
  -- We add the residual wanteds from nested implications (TODO not what GHC does, is this OK?).
  mapM_ (addInertCan . (Wanted,)) residuals
  -- editContext inerts nubInerts

  finalCtx :: Context <- get
  -- Context _ inerts subst _ _ <- get
  let finalInerts = dischargeWithRefl
        . unflattenedInerts (view unflatten finalCtx)
        . view inerts
        $ finalCtx
  
  return (trace1 ++ trace2 ++ [finalCtx], finalInerts) -- (inerts,subst)

solveLoop :: ContextM [Context]
solveLoop = do
    ctx <- get
    -- traceM $ "solveLoop worklist = " ++ show (_workList ctx)
    selectNextWorkItem >>= \case
      Nothing -> return []
      Just ct -> do
        --ct' <- zonkCt ct
        --traceM $ "zonked = " ++ prettyCt ct'
        runSolverPipeline ct
        ctxs <- solveLoop
        return (ctx : ctxs)

solveGivens :: [Ct'] -> ContextM [Context]
solveGivens givens = do
  mapM_ emitWork . reverse . map (Given,) $ givens -- TODO double-check order
  solveLoop

solveWanteds :: WantedConstraints -> ContextM ([Context], [Ct'])
solveWanteds (simpleWanteds,implics) = do
  trace1              <- solveSimpleWanteds simpleWanteds
  (trace2, residuals) <- solveNestedImplications implics
  return (trace1 ++ trace2, residuals)

solveSimpleWanteds :: [Ct'] -> ContextM [Context]
solveSimpleWanteds simpleWanteds = do
  mapM_ emitWork . reverse . map (Wanted,) $ simpleWanteds
  solveLoop

data FloatedEqs

-- Cfr TcSimplify.hs:1619
solveNestedImplications :: [Implication] -> ContextM ([Context], [Ct'])
solveNestedImplications
  = fmap ((\(ctxss, rwss) -> (concat ctxss, concat rwss)) . unzip)
  . mapM solveImplication
  -- TODO wat doe ik met residual wanteds? 
  where
    solveImplication :: Implication -> ContextM ([Context], [Ct'])
    -- TODO isSolvedStatus?
    -- POSTPONED: floating constraints
    solveImplication (Implic tclvl skols givens wanteds) = do
      ics <- view inerts <$> get
      lvl <- view curLvl <$> get
      return $ runContextM $ do
        editContext inerts $ const ics
        editContext curLvl $ const (lvl+1)
        trace1 <- solveGivens givens
        trace2 <- solveSimpleWanteds wanteds
        let residuals = extractResidualWanteds $ view inerts $ last trace2
        return (trace1 ++ trace2, residuals)

        -- TODO unflatten givens

      -- Empty worklist precondition is automatically satisfied.
      -- Given-only inerts?
      
      
runSolverPipeline :: Ct -> ContextM ()
runSolverPipeline item
  = runPipeline pipeline (Just item)

pipeline :: [(String, Ct -> ContextM (Maybe Ct))]
pipeline = [ ("After canonicalisation: ", canonicalise)
           , ("After interaction: ", interactWithInerts)
           , ("After reaction: ", topReactionsStage)
           ]

runPipeline :: [(String, Ct -> ContextM (Maybe Ct))] -> Maybe Ct -> ContextM () 
runPipeline _          Nothing   = return ()
runPipeline []         (Just ct) = addInertCan ct
runPipeline ((s,f):fs) (Just ct) = do
  ct' <- f ct
  traceM $ s ++ case ct' of Nothing -> "(stop)"; Just ct'' -> prettyCt ct''
  runPipeline fs ct'

-- Should I model TcLevel literally or with untouchables like in the paper?
-- Check my understanding of solveNestedImplications.
-- solveImplication precondition: given-only inerts: really model it this way?
-- How should I test things?


  
-- Note [TcLevel and untouchable type variables]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- * Each unification variable (MetaTv)
--   and each Implication
--   has a level number (of type TcLevel)
-- 
-- * INVARIANTS.  In a tree of Implications,
-- 
--     (ImplicInv) The level number (ic_tclvl) of an Implication is
--                 STRICTLY GREATER THAN that of its parent
-- 
--     (SkolInv)   The level number of the skolems (ic_skols) of an
--                 Implication is equal to the level of the implication
--                 itself (ic_tclvl)
-- 
--     (GivenInv)  The level number of a unification variable appearing
--                 in the 'ic_given' of an implication I should be
--                 STRICTLY LESS THAN the ic_tclvl of I
-- 
--     (WantedInv) The level number of a unification variable appearing
--                 in the 'ic_wanted' of an implication I should be
--                 LESS THAN OR EQUAL TO the ic_tclvl of I
--                 See Note [WantedInv]
-- 
-- * A unification variable is *touchable* if its level number
--   is EQUAL TO that of its immediate parent implication,
--   and it is a TauTv or TyVarTv (but /not/ FlatMetaTv or FlatSkolTv)
-- 
-- Note [WantedInv]
-- ~~~~~~~~~~~~~~~~
-- Why is WantedInv important?  Consider this implication, where
-- the constraint (C alpha[3]) disobeys WantedInv:
-- 
--    forall[2] a. blah => (C alpha[3])
--                         (forall[3] b. alpha[3] ~ b)
-- 
-- We can unify alpha:=b in the inner implication, because 'alpha' is
-- touchable; but then 'b' has excaped its scope into the outer implication.
