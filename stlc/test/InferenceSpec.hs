{-# OPTIONS_GHC -Wno-orphans #-}

module InferenceSpec (inferenceTests) where

import Data.List (isInfixOf)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Parser (Expr (..), Literal (..), Op (..))
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Inference
import Type.Inference qualified as T

inferenceTests :: TestTree
inferenceTests =
  testGroup
    "Constraint Generation"
    [ literalTests,
      variableTests,
      lambdaTests,
      applicationTests,
      conditionalTests,
      binaryOpTests,
      letBindingTests,
      propertyTests,
      recordTests,
      toHeadTests,
      rowEqualityTests
    ]

doInfer :: TypeEnv -> Expr -> Either TypeError (Type, [Constraint])
doInfer env expr = runInfer (infer env expr) 0 0

-- ============================================================================
-- HUnit Tests
-- ============================================================================

literalTests :: TestTree
literalTests =
  testGroup
    "Literals"
    [ testCase "Integer literal: type=Int, constraints=[]" $ do
        let expr = Lit (LitInt 42)
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool True)
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Bool
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean False literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool False)
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Bool
            cs @?= []
          Left err -> assertFailure $ show err
    ]

variableTests :: TestTree
variableTests =
  testGroup
    "Variables"
    [ testCase "Lookup monomorphic Int: type=Int, constraints=[]" $ do
        let env = Map.fromList [("x", Forall Set.empty T.Int)]
        let expr = P.Var "x"
        case doInfer env expr of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Lookup monomorphic Arrow: type preserved, constraints=[]" $ do
        let env = Map.fromList [("f", Forall Set.empty $ Arrow T.Int T.Bool)]
        let expr = P.Var "f"
        case doInfer env expr of
          Right (t, cs) -> do
            t @?= Arrow T.Int T.Bool
            cs @?= []
          Left err -> assertFailure $ show err,
     --  testCase "Lookup polymorphic (forall a. a -> a): instantiates fresh vars" $ do
     --    let polyId = Scheme (Set.fromList [T.Var "a"]) (Arrow (T.Var "a") (T.Var "a"))
     --    let env = Map.fromList [("id", polyId)]
     --    let expr = P.Var "id"
     --    case doInfer env expr of
     --      Right (t, cs) -> do
     --        cs @?= []
     --        case t of
     --          Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
     --          _ -> assertFailure $ "Expected Arrow (Var _) (Var _), got: " ++ show t
     --      Left err -> assertFailure $ show err,
      testCase "Undefined variable: returns InferenceError" $ do
        let expr = P.Var "undefined_var"
        case doInfer emptyEnv expr of
          Left (InferenceError msg) ->
            assertBool "Error should mention variable" ("undefined_var" `isInfixOf` msg)
          Left err -> assertFailure $ "Wrong error type: " ++ show err
          Right _ -> assertFailure "Should have failed"
    ]

lambdaTests :: TestTree
lambdaTests =
  testGroup
    "Lambda"
    [ testCase "Identity (\\x -> x): Arrow v1 v1, constraints=[]" $ do
        let expr = Lambda "x" Nothing (P.Var "x")
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Const (\\x -> \\y -> x): Arrow v1 (Arrow v2 v1)" $ do
        let expr = Lambda "x" Nothing (Lambda "y" Nothing (P.Var "x"))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) (Arrow (T.Var v2) (T.Var v3)) -> do
                v1 @?= v3
                assertBool "y different from x" (v2 /= v1)
              _ -> assertFailure $ "Expected nested Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Lambda with Int body (\\x -> 42): Arrow v1 Int, constraints=[]" $ do
        let expr = Lambda "x" Nothing (Lit (LitInt 42))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var _) T.Int -> return ()
              _ -> assertFailure $ "Expected Arrow _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Lambda constrains body (\\x -> x + 1): has (v1, Int) constraint" $ do
        let expr = Lambda "x" Nothing (BinOp Add (P.Var "x") (Lit (LitInt 1)))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            case t of
              Arrow param T.Int -> do
                let hasParamConstraint =
                      any
                        ( \(Equals (a, b)) ->
                            (a == param && b == T.Int) || (a == T.Int && b == param)
                        )
                        cs
                assertBool "Should constrain param to Int" hasParamConstraint
              _ -> assertFailure $ "Expected Arrow _ Int, got: " ++ show t
          Left err -> assertFailure $ show err
    ]

applicationTests :: TestTree
applicationTests =
  testGroup
    "Application"
    [ testCase "(\\x -> x) 42: produces function unification constraint" $ do
        let expr = App (Lambda "x" Nothing (P.Var "x")) (Lit (LitInt 42))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have at least one constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x where f:Int->Bool, x:Int: constraint links f to arg->result" $ do
        let env = Map.fromList [("f", Forall Set.empty $ Arrow T.Int T.Bool), ("x", Forall Set.empty T.Int)]
        let expr = App (P.Var "f") (P.Var "x")
        case doInfer env expr of
          Right (t, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have function constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x y (curried): produces multiple constraints" $ do
        let env =
              Map.fromList
                [ ("f", Forall Set.empty $ Arrow T.Int (Arrow T.Int T.Int)),
                  ("x", Forall Set.empty T.Int),
                  ("y", Forall Set.empty T.Int)
                ]
        let expr = App (App (P.Var "f") (P.Var "x")) (P.Var "y")
        case doInfer env expr of
          Right (_, cs) -> do
            assertBool "Should have >= 2 constraints" (length cs >= 2)
          Left err -> assertFailure $ show err,
      testCase "Application with undefined arg: propagates error" $ do
        let env = Map.fromList [("f", Forall Set.empty $ Arrow T.Int T.Int)]
        let expr = App (P.Var "f") (P.Var "undefined_arg")
        case doInfer env expr of
          Left (InferenceError _) -> return ()
          Left err -> assertFailure $ "Wrong error: " ++ show err
          Right _ -> assertFailure "Should have failed"
    ]

conditionalTests :: TestTree
conditionalTests =
  testGroup
    "Conditionals"
    [ testCase "if true then 1 else 2: has (Bool,Bool) and (Int,Int) constraints" $ do
        let expr = If (Lit (LitBool True)) (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Int
            assertBool "Has condition constraint" (Equals (T.Bool, T.Bool) `elem` cs)
            assertBool "Has branch constraint" (Equals (T.Int, T.Int) `elem` cs)
          Left err -> assertFailure $ show err,
      testCase "if x then 1 else 2 (x:Var): constrains x to Bool" $ do
        let env = Map.fromList [("x", Forall Set.empty $ T.Var "vx")]
        let expr = If (P.Var "x") (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer env expr of
          Right (_, cs) -> do
            let hasBoolConstraint =
                  any
                    ( \(Equals (a, b)) ->
                        (a == T.Bool && b == T.Var "vx")
                          || (a == T.Var "vx" && b == T.Bool)
                    )
                    cs
            assertBool "Should constrain condition to Bool" hasBoolConstraint
          Left err -> assertFailure $ show err,
      testCase "if true then x else y: constrains branches to unify" $ do
        let env = Map.fromList [("x", Forall Set.empty $ T.Var "vx"), ("y", Forall Set.empty $ T.Var "vy")]
        let expr = If (Lit (LitBool True)) (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, cs) -> do
            t @?= T.Var "vx"
            let hasBranchConstraint =
                  any
                    ( \(Equals (a, b)) ->
                        (a == T.Var "vx" && b == T.Var "vy")
                          || (a == T.Var "vy" && b == T.Var "vx")
                    )
                    cs
            assertBool "Should constrain branches equal" hasBranchConstraint
          Left err -> assertFailure $ show err
    ]

binaryOpTests :: TestTree
binaryOpTests =
  testGroup
    "Binary Operations"
    [ testCase "1 + 2: type=Int, constraints=[(Int,Int),(Int,Int)]" $ do
        let expr = BinOp Add (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= [Equals (T.Int, T.Int), Equals (T.Int, T.Int)]
          Left err -> assertFailure $ show err,
      testCase "x + y (x,y:Var): constrains both to Int" $ do
        let env = Map.fromList [("x", Forall Set.empty $ T.Var "vx"), ("y",Forall Set.empty $  T.Var "vy")]
        let expr = BinOp Add (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, cs) -> do
            t @?= T.Int
            assertBool "x constrained to Int" $
              Equals (T.Var "vx", T.Int) `elem` cs || Equals (T.Int, T.Var "vx") `elem` cs
            assertBool "y constrained to Int" $
              Equals (T.Var "vy", T.Int) `elem` cs || Equals (T.Int, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "5 - 3: type=Int, constraints for Int operands" $ do
        let expr = BinOp Subtract (Lit (LitInt 5)) (Lit (LitInt 3))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= [Equals (T.Int, T.Int), Equals (T.Int, T.Int)]
          Left err -> assertFailure $ show err,
      testCase "true && false: type=Bool, constraints=[(Bool,Bool),(Bool,Bool)]" $ do
        let expr = BinOp And (Lit (LitBool True)) (Lit (LitBool False))
        case doInfer emptyEnv expr of
          Right (t, cs) -> do
            t @?= T.Bool
            cs @?= [Equals (T.Bool, T.Bool), Equals (T.Bool, T.Bool)]
          Left err -> assertFailure $ show err,
      testCase "x && y (x,y:Var): constrains both to Bool" $ do
        let env = Map.fromList [("x",Forall Set.empty $  T.Var "vx"), ("y",Forall Set.empty $  T.Var "vy")]
        let expr = BinOp And (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, cs) -> do
            t @?= T.Bool
            assertBool "x constrained to Bool" $
              Equals (T.Var "vx", T.Bool) `elem` cs || Equals (T.Bool, T.Var "vx") `elem` cs
            assertBool "y constrained to Bool" $
              Equals (T.Var "vy", T.Bool) `elem` cs || Equals (T.Bool, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "true || false: type=Bool" $ do
        let expr = BinOp Or (Lit (LitBool True)) (Lit (LitBool False))
        case doInfer emptyEnv expr of
          Right (t, _) -> t @?= T.Bool
          Left err -> assertFailure $ show err
    ]

letBindingTests :: TestTree
letBindingTests =
  testGroup
    "Let Bindings"
    [ testCase "let x = 42 in x: type resolves to Int" $ do
        let expr = Let "x" (Lit (LitInt 42)) (P.Var "x")
        case doInfer emptyEnv expr of
          Right (t, _) -> do
            case t of
              T.Int -> return ()
              -- Scheme _ T.Int -> return ()
              _ -> assertFailure $ "Expected Int or Scheme _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let f = \\x -> x in f: generalizes to polymorphic scheme" $ do
        let expr = Let "f" (Lambda "x" Nothing (P.Var "x")) (P.Var "f")
        case doInfer emptyEnv expr of
          Right (t, _) -> do
            case t of
              -- Scheme vars (Arrow _ _) ->
              --   assertBool "Should have bound vars" (not (Set.null vars))
              Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Scheme or Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let id = \\x -> x in id 42: polymorphic use" $ do
        let expr =
              Let
                "id"
                (Lambda "x" Nothing (P.Var "x"))
                (App (P.Var "id") (Lit (LitInt 42)))
        case doInfer emptyEnv expr of
          Right (t, _) -> do
            case t of
              T.Var _ -> return ()
              T.Int -> return ()
              _ -> assertFailure $ "Expected Var or Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let x = y in x (y:Int in env): produces constraints" $ do
        let env = Map.fromList [("y",Forall Set.empty  T.Int)]
        let expr = Let "x" (P.Var "y") (P.Var "x")
        case doInfer env expr of
          Right (_, cs) -> do
            assertBool "Should have constraints" (not (null cs))
          Left err -> assertFailure $ show err
    ]

recordTests :: TestTree
recordTests =
  testGroup
    "Record rows"
    [ testCase "{ x = 0, y = 0 } resolves to a Record type { x: Int, y: Int }" $ do
        let expr = P.Record (P.RecordCstr [("x", Lit (LitInt 0)), ("y", Lit (LitInt 0))])
        case doInfer emptyEnv expr of
          Right (t, _) -> do
            case t of
              T.Record row -> case row of
                Row (l1, t1) (Row (l2, t2) EmptyRow) -> do
                  l1 @?= "y"
                  l2 @?= "x"
                  t1 @?= T.Int
                  t2 @?= T.Int
                _ -> assertFailure "Expected Row type with labels 'x' and 'y'"
              _ -> assertFailure ""
          Left err -> assertFailure $ show err,
      testCase "Simple record extension { r with l = 5 } should give a type { l : Int | p }" $ do
        let expr = P.Record $ P.RecordExtension (P.Record $ P.RecordCstr []) "l" (P.Lit $ LitInt 5)
        case doInfer emptyEnv expr of
          Right (t, c) -> do
            case t of
              T.Record (Row (l, lt) r) -> do
                l @?= "l"
                lt @?= T.Int
                r @?= T.Var "r1"
              _ -> assertFailure $ "Expected an empty record but got: " ++ reportInferResult t c
          Left err -> assertFailure $ show err,
      testCase "Extend a non_empty record: { 2dOrigin with z = 0 }" $ do
        let origin2d = T.Record (T.Row ("x", T.Int) (T.Row ("y", T.Int) EmptyRow))
        let env = Map.insert "origin2d" (Forall Set.empty origin2d) emptyEnv
        let expr = P.Record (P.RecordExtension (P.Var "origin2d") "z" (P.Lit $ LitInt 0))
        case doInfer env expr of
          Left err -> assertFailure $ show err
          Right (t, c) -> do
            case t of
              T.Record (Row (l, lt) r) -> do
                l @?= "z"
                lt @?= T.Int
                r @?= T.Var "r1"
                c @?= [Equals (T.Record r, origin2d)]
              _ -> assertFailure $ "Expected an empty record but got: " ++ reportInferResult t c
    ]

reportInferResult :: Type -> [Constraint] -> String
reportInferResult t c = prefix ++ "Type: " ++ show t ++ prefix ++ "Constraints: " ++ show c
  where
    prefix = "\n\t"

toHeadTests :: TestTree
toHeadTests =
  testGroup
    "toHead row reordering"
    [ testCase "Empty row returns empty row" $ do
        toHead EmptyRow "x" @?= EmptyRow,
      testCase "Var returns unchanged" $ do
        toHead (T.Var "r") "x" @?= T.Var "r",
      testCase "Label already at head returns unchanged" $ do
        let row = Row ("x", T.Int) (Row ("y", T.Bool) EmptyRow)
        toHead row "x" @?= row,
      testCase "Swaps adjacent element to head" $ do
        let row = Row ("a", T.Int) (Row ("x", T.Bool) EmptyRow)
        toHead row "x" @?= Row ("x", T.Bool) (Row ("a", T.Int) EmptyRow),
      testCase "Duplicate labels: finds first occurrence (x::Int before x::Bool)" $ do
        let row = Row ("a", T.Int) (Row ("x", T.Int) (Row ("x", T.Bool) EmptyRow))
        let expected = Row ("x", T.Int) (Row ("a", T.Int) (Row ("x", T.Bool) EmptyRow))
        toHead row "x" @?= expected,
      testCase "Label deeper in row is brought forward" $ do
        let row = Row ("a", T.Int) (Row ("b", T.Bool) (Row ("x", T.Int) EmptyRow))
        let result = toHead row "x"
        case result of
          Row ("b", _) (Row ("x", T.Int) _) -> return ()
          _ -> assertFailure $ "Expected 'x' to be moved forward, got: " ++ show result,
      testCase "Single element row with matching label returns unchanged" $ do
        let row = Row ("x", T.Int) EmptyRow
        toHead row "x" @?= row,
      testCase "Row ending in Var returns unchanged when label not found" $ do
        let row = Row ("a", T.Int) (T.Var "r")
        toHead row "x" @?= row
    ]

rowEqualityTests :: TestTree
rowEqualityTests =
  testGroup
    "Row equality"
    [ -- Basic equality
      testCase "EmptyRow equals EmptyRow" $ do
        EmptyRow @?= EmptyRow,
      testCase "Var equals same Var" $ do
        T.Var "r" @?= T.Var "r",
      testCase "Var does not equal different Var" $ do
        assertBool "Var r /= Var s" (T.Var "r" /= T.Var "s"),
      testCase "Single element row equals itself" $ do
        let row = Row ("x", T.Int) EmptyRow
        row @?= row,
      -- Reordering (distinct labels)
      testCase "Rows with distinct labels: reordering is equal {x:Int,y:Bool} == {y:Bool,x:Int}" $ do
        let row1 = Row ("x", T.Int) (Row ("y", T.Bool) EmptyRow)
        let row2 = Row ("y", T.Bool) (Row ("x", T.Int) EmptyRow)
        row1 @?= row2,
      testCase "Three element row reordering {a:Int,b:Bool,c:Int} == {c:Int,a:Int,b:Bool}" $ do
        let row1 = Row ("a", T.Int) (Row ("b", T.Bool) (Row ("c", T.Int) EmptyRow))
        let row2 = Row ("c", T.Int) (Row ("a", T.Int) (Row ("b", T.Bool) EmptyRow))
        row1 @?= row2,
      -- Inequality cases
      testCase "Different labels are not equal {x:Int} /= {y:Int}" $ do
        let row1 = Row ("x", T.Int) EmptyRow
        let row2 = Row ("y", T.Int) EmptyRow
        assertBool "{x:Int} /= {y:Int}" (row1 /= row2),
      testCase "Same label different types not equal {x:Int} /= {x:Bool}" $ do
        let row1 = Row ("x", T.Int) EmptyRow
        let row2 = Row ("x", T.Bool) EmptyRow
        assertBool "{x:Int} /= {x:Bool}" (row1 /= row2),
      testCase "Different lengths not equal {x:Int,y:Bool} /= {x:Int}" $ do
        let row1 = Row ("x", T.Int) (Row ("y", T.Bool) EmptyRow)
        let row2 = Row ("x", T.Int) EmptyRow
        assertBool "different lengths" (row1 /= row2),
      -- Duplicate labels (order matters within same label)
      testCase "Duplicate labels same order are equal {x:Int,x:Bool} == {x:Int,x:Bool}" $ do
        let row1 = Row ("x", T.Int) (Row ("x", T.Bool) EmptyRow)
        let row2 = Row ("x", T.Int) (Row ("x", T.Bool) EmptyRow)
        row1 @?= row2,
      testCase "Duplicate labels swapped are NOT equal {x:Int,x:Bool} /= {x:Bool,x:Int}" $ do
        let row1 = Row ("x", T.Int) (Row ("x", T.Bool) EmptyRow)
        let row2 = Row ("x", T.Bool) (Row ("x", T.Int) EmptyRow)
        assertBool "{x:Int,x:Bool} /= {x:Bool,x:Int}" (row1 /= row2),
      testCase "Reorder non-duplicate doesn't cross duplicate {a:Int,x:Int,x:Bool} == {x:Int,a:Int,x:Bool}" $ do
        let row1 = Row ("a", T.Int) (Row ("x", T.Int) (Row ("x", T.Bool) EmptyRow))
        let row2 = Row ("x", T.Int) (Row ("a", T.Int) (Row ("x", T.Bool) EmptyRow))
        row1 @?= row2,
      -- Mixed with Var
      testCase "Row with same Var tail are equal" $ do
        let row1 = Row ("x", T.Int) (T.Var "r")
        let row2 = Row ("x", T.Int) (T.Var "r")
        row1 @?= row2,
      testCase "Row with different Var tail are not equal" $ do
        let row1 = Row ("x", T.Int) (T.Var "r")
        let row2 = Row ("x", T.Int) (T.Var "s")
        assertBool "different Var tails" (row1 /= row2),
      testCase "{ x : Int, y: Int} should not equal { x: v1 | r1 }" $ do
        let row1 = T.Record $ Row ("y", T.Int) (Row ("x", T.Int) EmptyRow)
        let row2 = T.Record $ Row ("x", T.Var "v1") (T.Var "r1")
        assertBool "different types" (row1 /= row2)
    ]

-- ============================================================================
-- QuickCheck Properties
-- ============================================================================

genLiteral :: Gen Expr
genLiteral =
  oneof
    [ Lit . LitInt <$> arbitrary,
      Lit . LitBool <$> arbitrary
    ]

genVarName :: Gen String
genVarName = elements ["x", "y", "z", "a", "b", "c"]

genExpr :: Int -> Gen Expr
genExpr 0 = oneof [genLiteral, P.Var <$> genVarName]
genExpr n =
  frequency
    [ (3, genLiteral),
      (3, P.Var <$> genVarName),
      (2, Lambda <$> genVarName <*> pure Nothing <*> genExpr (n - 1)),
      (2, App <$> genExpr (n - 1) <*> genExpr (n - 1)),
      (1, BinOp <$> genOp <*> genExpr (n - 1) <*> genExpr (n - 1)),
      (1, If <$> genExpr (n - 1) <*> genExpr (n - 1) <*> genExpr (n - 1)),
      (1, Let <$> genVarName <*> genExpr (n - 1) <*> genExpr (n - 1))
    ]
  where
    genOp = elements [Add, Subtract, And, Or]

instance Arbitrary Expr where
  arbitrary = sized $ \n -> genExpr (min n 3)
  shrink (Lambda v _ e) = e : [Lambda v Nothing e' | e' <- shrink e]
  shrink (App e1 e2) = e1 : e2 : [App e1' e2' | (e1', e2') <- shrink (e1, e2)]
  shrink (BinOp op e1 e2) = e1 : e2 : [BinOp op e1' e2' | (e1', e2') <- shrink (e1, e2)]
  shrink (If c t f) = c : t : f : [If c' t' f' | (c', t', f') <- shrink (c, t, f)]
  shrink (Let v e1 e2) = e1 : e2 : [Let v e1' e2' | (e1', e2') <- shrink (e1, e2)]
  shrink _ = []

genRowLabel :: Gen String
genRowLabel = elements ["a", "b", "c", "x", "y", "z"]

genSimpleType :: Gen Type
genSimpleType = elements [T.Int, T.Bool]

genRow :: Int -> Gen Type
genRow 0 = frequency [(3, pure EmptyRow), (1, T.Var <$> genRowLabel)]
genRow n =
  frequency
    [ (1, pure EmptyRow),
      (1, T.Var <$> genRowLabel),
      (4, (\l t r -> Row (l, t) r) <$> genRowLabel <*> genSimpleType <*> genRow (n - 1))
    ]

instance Arbitrary Type where
  arbitrary = sized $ \n -> genRow (min n 4)
  shrink EmptyRow = []
  shrink (T.Var _) = [EmptyRow]
  shrink (Row (_, _) r) = r : EmptyRow : shrink r

standardEnv :: TypeEnv
standardEnv =
  Map.fromList
    [ ("x",Forall Set.empty T.Int),
      ("y",Forall Set.empty T.Bool),
      ("z",Forall Set.empty $ Arrow T.Int T.Int),
      ("a",Forall Set.empty $ T.Var "va"),
      ("b",Forall Set.empty $ T.Var "vb"),
      ("c",Forall Set.empty $ T.Var "vc")
    ]

propertyTests :: TestTree
propertyTests =
  testGroup
    "Properties"
    [ testProperty "Literals produce no constraints" prop_literalsNoConstraints,
      testProperty "Lambda always returns Arrow type" prop_lambdaReturnsArrow,
      testProperty "Application produces at least one constraint" prop_appProducesConstraint,
      testProperty "BinOp result type matches operation" prop_binOpResultType,
      testProperty "Conditionals constrain condition to Bool" prop_conditionBool,
      testProperty "Constraint count bounded by 3x expression size" prop_constraintBound,
      testProperty "Row equality is reflexive" prop_rowEqReflexive
    ]

prop_literalsNoConstraints :: Property
prop_literalsNoConstraints = forAll genLiteral $ \expr ->
  case doInfer emptyEnv expr of
    Right (_, cs) -> cs === []
    Left _ -> property False

prop_lambdaReturnsArrow :: Property
prop_lambdaReturnsArrow = forAll (genExpr 2) $ \bodyExpr ->
  forAll genVarName $ \paramName ->
    let expr = Lambda paramName Nothing bodyExpr
     in case doInfer standardEnv expr of
          Right (t, _) -> case t of
            Arrow _ _ -> property True
            _ -> property False
          Left _ -> property True

prop_appProducesConstraint :: Property
prop_appProducesConstraint =
  forAll (genExpr 1) $ \e1 ->
    forAll (genExpr 1) $ \e2 ->
      let expr = App e1 e2
       in case doInfer standardEnv expr of
            Right (_, cs) -> not (null cs) === True
            Left _ -> property True

prop_binOpResultType :: Property
prop_binOpResultType =
  forAll (elements [Add, Subtract, And, Or]) $ \op ->
    forAll (genExpr 1) $ \e1 ->
      forAll (genExpr 1) $ \e2 ->
        let expr = BinOp op e1 e2
            expectedType = if op `elem` [Add, Subtract] then T.Int else T.Bool
         in case doInfer standardEnv expr of
              Right (t, _) -> t === expectedType
              Left _ -> property True

prop_conditionBool :: Property
prop_conditionBool =
  forAll (genExpr 1) $ \cond ->
    forAll (genExpr 1) $ \tr ->
      forAll (genExpr 1) $ \fl ->
        let expr = If cond tr fl
         in case doInfer standardEnv expr of
              Right (_, cs) -> property $ any hasBoolConstraint cs
              Left _ -> property True
  where
    hasBoolConstraint (Equals (T.Bool, _)) = True
    hasBoolConstraint (Equals (_, T.Bool)) = True
    hasBoolConstraint _ = False

prop_constraintBound :: Property
prop_constraintBound = forAll (genExpr 2) $ \expr ->
  let exprSize = countNodes expr
   in case doInfer standardEnv expr of
        Right (_, cs) -> property (length cs <= exprSize * 3)
        Left _ -> property True
  where
    countNodes (Lit _) = 1
    countNodes (P.Var _) = 1
    countNodes (Lambda _ _ e) = 1 + countNodes e
    countNodes (App e1 e2) = 1 + countNodes e1 + countNodes e2
    countNodes (BinOp _ e1 e2) = 1 + countNodes e1 + countNodes e2
    countNodes (If c t f) = 1 + countNodes c + countNodes t + countNodes f
    countNodes (Let _ e1 e2) = 1 + countNodes e1 + countNodes e2

prop_rowEqReflexive :: Property
prop_rowEqReflexive = forAll (genRow 3) $ \r ->
  r === r
