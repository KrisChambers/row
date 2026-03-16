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
    , rowMergeTests
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


rowMergeTests :: TestTree
rowMergeTests =
  testGroup
    "Row Merging"
    [
    -- Merge EmptyRow rRight rFinal  =>  rFinal = rRight
    testCase "Merge: empty left produces right side" $ do
      let cs = [Merge EmptyRow (Row ("x", tInt) EmptyRow) (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("x", tInt) EmptyRow,

    -- Merge rLeft EmptyRow rFinal  =>  rFinal = rLeft
    testCase "Merge: empty right produces left side" $ do
      let cs = [Merge (Row ("y", tBool) EmptyRow) EmptyRow (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("y", tBool) EmptyRow,

    testCase "Merge: both empty produces EmptyRow" $ do
      let cs = [Merge EmptyRow EmptyRow (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= EmptyRow,

    -- Both closed: mergeRow concatenates left in front of right
    testCase "Merge: two closed rows concatenate" $ do
      let left  = Row ("x", tInt) EmptyRow
      let right = Row ("y", tBool) EmptyRow
      let cs = [Merge left right (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("x", tInt) (Row ("y", tBool) EmptyRow),

    testCase "Merge: row variable of open left row becomes open variable for result" $ do
      let left  = Row ("x", tInt) (Var "tail")  -- open row
      let right = Row ("y", tBool) EmptyRow
      let cs = [Merge left right (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("x", tInt) (Row ("y", tBool) (Var "tail")),

    testCase "Merge: row variable of open right row becomes open variable for result" $ do
      let left  = Row ("x", tInt) EmptyRow
      let right = Row ("y", tBool) (Var "tail")  -- open row
      let cs = [Merge left right (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("x", tInt) (Row ("y", tBool) (Var "tail")),

    -- The Merge handler solves `cs` first, then applies the substitution to rLeft/rRight
    testCase "Merge: defers to solve variables from other constraints first" $ do
      let cs = [ Equals (Var "a", Row ("x", tInt) EmptyRow) , Merge (Var "a") (Row ("y", tBool) EmptyRow) (Var "r") ]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= Row ("x", tInt) (Row ("y", tBool) EmptyRow),

    testCase "Merge: both sides are variables resolved to EmptyRow" $ do
      let cs = [ Equals (Var "a", EmptyRow) , Equals (Var "b", EmptyRow) , Merge (Var "a") (Var "b") (Var "r") ]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r") @?= EmptyRow,


    testCase "Merge: multi-field closed rows" $ do
      let left  = Row ("x", tInt) (Row ("y", tBool) EmptyRow)
      let right = Row ("z", tInt) EmptyRow
      let cs = [Merge left right (Var "r")]
      case doSolve cs of
        Left err -> assertFailure $ show err
        Right sub -> apply sub (Var "r")
          @?= Row ("x", tInt) (Row ("y", tBool) (Row ("z", tInt) EmptyRow)),

    -- This should produce an error
    testCase "Merge: both open rows produces a UnificationError" $ do
        let left  = Row ("x", tInt) (Var "t1")
        let right = Row ("y", tBool) (Var "t2")
        let cs = [Merge left right (Var "r")]
        case doSolve cs of
          Left err -> return ()
          Right _ -> assertFailure "We are not handling the case where we have 2 open rows"
  ]
