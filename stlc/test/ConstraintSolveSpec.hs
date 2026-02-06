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
    , effectConstraintTests
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
        let constraint = Equals (T.tInt, T.tInt)
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
        let r1 = T.Record (Row ("x", T.tInt) (Row ("y", T.tBool) EmptyRow))
        let r2 = T.Record (Row ("y", T.tBool) (Row ("x", T.tInt) EmptyRow))
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
        let r n = T.Record (Row ("x", T.tInt) (T.Var n))

        case doSolve [Equals (r "a", r "b")] of
          Left err -> assertFailure $ show err
          Right sub -> do
            sub @?= Single (T.Var "a", T.Var "b")

            -- [(Var "a", Var "b")] . (| thing :: a |) -> (| thing :: b |)
    ]

effectConstraintTests :: TestTree
effectConstraintTests =
  testGroup
    "Effect Constraint Solving (Stubs)"
    [ testCase "STUB: Effect variable unifies with EmptyRow" $ do
        let constraint = Equals (T.Var "e1", EmptyRow)
        case doSolve [constraint] of
          Left err -> assertFailure $ show err
          Right sub -> sub @?= Single (T.Var "e1", EmptyRow),

      testCase "STUB: Simple Effect unification" $ do

        let constraint = Equals (T.Var "e1", T.Var "e2")
        case doSolve [constraint] of
          Left err -> assertFailure $ show err
          Right sub -> sub @?= Single (T.Var "e1", T.Var "e2"),

      testCase "STUB: Two effect variables unify" $ do
        let constraint = Equals (T.Var "e1", T.Var "e2")
        case doSolve [constraint] of
          Left err -> assertFailure $ show err
          Right sub -> sub @?= Single (T.Var "e1", T.Var "e2"),

      testCase "STUB: Arrow effects unify when arrows unify" $ do
        let a1 = Arrow T.tInt (T.Var "e1") T.tInt
        let a2 = Arrow T.tInt (T.Var "e2") T.tInt
        case doSolve [Equals (a1, a2)] of
          Left err -> assertFailure $ show err
          Right sub ->
            assertBool "Should have effect substitution" (sub /= IdSub)
    ]

-- ============================================================================
-- Property Tests
-- ============================================================================

-- reflexiveRelation => [] Substitution Ex: (Int, Int) -> []
--
