module DDSpec where
import           DD.Algorithm 
                    ( solve
                    , decisionDisjunction)
import           DD.Types (DDResult (..))
import           CDCL.Types (SATResult (..))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Test.Hspec

import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Data.Coerce
import qualified Picosat as PicoSAT

spec :: Spec
spec = do
    describe "Compare DD with picoSAT solver" $ do
        it "compare SAT / UNSAT result term reduced to empty list" $ do
          let problem = [[1, 2], [- 1]]
              csol = decisionDisjunction (map (map fromIntegral) problem)
          psol <- PicoSAT.solve problem
          (case (psol, csol) of
             (PicoSAT.Solution _, SAT _) -> True
             t                          -> error ("Should be Sat, but got: " ++ show t)) `shouldBe` True
        it "compare SAT / UNSAT results" $ do
          property $ \clauses -> prop_picoSATcomparison clauses
    describe "DD should provide a variable assignment" $ do
        it "[[1, 2], [- 1]] is SAT with assignment" $ do
            let problem = [[1, 2], [- 1]]
                solution = solve problem

                resultAssignment = (case solution of
                  Satisfiable list -> list
                  _                -> error "Unsatisfiable but expected (Satisfiable [2, -1])")
            resultAssignment`shouldBe` [2, -1]
        it "[[1, 2, 3], [- 1, - 2], [1]] is SAT with assignment" $ do
            let problem = [[1, 2, 3], [- 1, - 2], [1]]
                solution = solve problem

                resultAssignment = (case solution of
                  Satisfiable list -> list
                  _                -> error "Unsatisfiable but expected (Satisfiable [3, -2, 1])")
            resultAssignment`shouldBe` [3, -2, 1]

prop_picoSATcomparison :: [[NonZero Int]] -> Property
prop_picoSATcomparison cl = withMaxSuccess 1000 ( monadicIO ( do
  let clauses = coerce cl
  picoSol <- run (PicoSAT.solve clauses)
  let ddSol = decisionDisjunction (map (map fromIntegral) clauses)
  ( case (picoSol, ddSol) of
      (PicoSAT.Unsatisfiable, UNSAT) -> pure $ collect "UNSAT"   True
      (PicoSAT.Unknown, _)           -> pure $ collect "Unknown" False
      (PicoSAT.Solution _, SAT _)    -> pure $ collect "SAT"     True
      _                              -> error ("Found counterexample : " ++ show clauses) )))
