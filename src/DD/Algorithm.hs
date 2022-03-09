{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
----------------------------------------------------------------------- |
-- Module      :   DD.Algorithm
-- Copyright   :   (c) Andreas Hager, 2022
-- License     :   Apache-2.0
-- Maintainer  :
-- Stability   :
-- Portability :
---------------------------------------------------------------------

module DD.Algorithm (solve, decisionDisjunction) where

import           CDCL.Types (SATResult (..))
import           DD.Types
import qualified Debug.Trace as D

-- | This function calls the solver. It returns
--   a list of literanls encoded as Integer.
solve :: [[Integer]] -> SATResult
solve t = case result of
            SAT l -> Satisfiable (map fromIntegral l)
            UNSAT -> Unsatisfiable
            where result = decisionDisjunction t

decisionDisjunction :: [[Integer]] -> DDResult
decisionDisjunction clauseList = getSolution result
    where term = parseTerm clauseList
          result = decisionDisjunction' term

decisionDisjunction' :: Term -> Term
decisionDisjunction' term = if isSolved term || isUnfullfillable term
    then term 
    else
        --D.trace ("Next Term for var " ++ show var ++ ": " ++ show nextTerm) 
        decisionDisjunction' nextTerm
            where 
                var = getNextVar term
                nextTerm = buildNextTerm term var
            

