module ConstraintSolveSpec (constraintSolveTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Type.Inference
import Type.Inference qualified as T
import Control.Monad.Except
import Control.Monad.State

constraintSolveTests :: TestTree
constraintSolveTests =
  testGroup
    "Constraint Solving"
    [ basicTests
    , recordTests
    ]

doSolve :: [Constraint] -> Either TypeError Substitution
doSolve cs = evalState unifyState IdSub
  where
    unifyState = runExceptT (solve cs)

-- ============================================================================
-- HUnit Tests
-- ============================================================================

basicTests :: TestTree
basicTests =
  testGroup
    "Simple (T1, T2) constraints"
    [ testCase "Equal Primitives return Identity" $ do
        let constraint = Equals (Int, Int)
        case doSolve [constraint] of
          Left err -> assertFailure $ show err
          Right sub -> do
            sub @?= IdSub
    ]

recordTests :: TestTree
recordTests =
  testGroup
    "Solving Row constraints for Records"
    [ testCase "{ x: Int, y: Bool } == { y: Bool, x: Int} should give ID" $ do
        let r1 = T.Record (Row ("x", T.Int) (Row ("y", T.Bool) EmptyRow))
        let r2 = T.Record (Row ("y", T.Bool) (Row ("x", T.Int) EmptyRow))
        case doSolve [Equals (r1, r2)] of
          Left err -> assertFailure $ show err
          Right sub -> do
            sub @?= IdSub,
      testCase "Equal Records constrain matching label types" $ do
        let r n = T.Record (Row ("x", T.Var n) EmptyRow)

        case doSolve [Equals (r "v1", r "v2")] of
          Left err -> assertFailure $ show err
          Right sub -> do
            sub @?= Single (T.Var "v1", T.Var "v2"),

      testCase "Equal Records constrain types of matching labels" $ do
        let r n = T.Record (Row ("x", T.Int) (T.Var n))

        case doSolve [Equals (r "a", r "b")] of
          Left err -> assertFailure $ show err
          Right sub -> do
            sub @?= Single (T.Var "a", T.Var "b")

            -- [(Var "a", Var "b")] . (| thing :: a |) -> (| thing :: b |)
    ]

-- ============================================================================
-- Property Tests
-- ============================================================================

-- reflexiveRelation => [] Substitution Ex: (Int, Int) -> []
--
