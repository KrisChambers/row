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
      propertyTests
    ]

-- ============================================================================
-- HUnit Tests
-- ============================================================================

literalTests :: TestTree
literalTests =
  testGroup
    "Literals"
    [ testCase "Integer literal: type=Int, constraints=[]" $ do
        let expr = Lit (LitInt 42)
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool True)
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Bool
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean False literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool False)
        case runInfer (infer emptyEnv expr) 0 of
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
        let env = Map.fromList [("x", T.Int)]
        let expr = P.Var "x"
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Lookup monomorphic Arrow: type preserved, constraints=[]" $ do
        let env = Map.fromList [("f", Arrow T.Int T.Bool)]
        let expr = P.Var "f"
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            t @?= Arrow T.Int T.Bool
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Lookup polymorphic (forall a. a -> a): instantiates fresh vars" $ do
        let polyId = Scheme (Set.fromList [T.Var "a"]) (Arrow (T.Var "a") (T.Var "a"))
        let env = Map.fromList [("id", polyId)]
        let expr = P.Var "id"
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Arrow (Var _) (Var _), got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Undefined variable: returns InferenceError" $ do
        let expr = P.Var "undefined_var"
        case runInfer (infer emptyEnv expr) 0 of
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
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Const (\\x -> \\y -> x): Arrow v1 (Arrow v2 v1)" $ do
        let expr = Lambda "x" Nothing (Lambda "y" Nothing (P.Var "x"))
        case runInfer (infer emptyEnv expr) 0 of
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
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var _) T.Int -> return ()
              _ -> assertFailure $ "Expected Arrow _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Lambda constrains body (\\x -> x + 1): has (v1, Int) constraint" $ do
        let expr = Lambda "x" Nothing (BinOp Add (P.Var "x") (Lit (LitInt 1)))
        case runInfer (infer emptyEnv expr) 0 of
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
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have at least one constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x where f:Int->Bool, x:Int: constraint links f to arg->result" $ do
        let env = Map.fromList [("f", Arrow T.Int T.Bool), ("x", T.Int)]
        let expr = App (P.Var "f") (P.Var "x")
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have function constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x y (curried): produces multiple constraints" $ do
        let env =
              Map.fromList
                [ ("f", Arrow T.Int (Arrow T.Int T.Int)),
                  ("x", T.Int),
                  ("y", T.Int)
                ]
        let expr = App (App (P.Var "f") (P.Var "x")) (P.Var "y")
        case runInfer (infer env expr) 0 of
          Right (_, cs) -> do
            assertBool "Should have >= 2 constraints" (length cs >= 2)
          Left err -> assertFailure $ show err,
      testCase "Application with undefined arg: propagates error" $ do
        let env = Map.fromList [("f", Arrow T.Int T.Int)]
        let expr = App (P.Var "f") (P.Var "undefined_arg")
        case runInfer (infer env expr) 0 of
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
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            assertBool "Has condition constraint" (Equals (T.Bool, T.Bool) `elem` cs)
            assertBool "Has branch constraint" (Equals (T.Int, T.Int) `elem` cs)
          Left err -> assertFailure $ show err,
      testCase "if x then 1 else 2 (x:Var): constrains x to Bool" $ do
        let env = Map.fromList [("x", T.Var "vx")]
        let expr = If (P.Var "x") (Lit (LitInt 1)) (Lit (LitInt 2))
        case runInfer (infer env expr) 0 of
          Right (_, cs) -> do
            let hasBoolConstraint =
                  any
                    ( \(Equals (a, b)) -> (a == T.Bool && b == T.Var "vx")
                  || (a == T.Var "vx" && b == T.Bool)
                    )
                    cs
            assertBool "Should constrain condition to Bool" hasBoolConstraint
          Left err -> assertFailure $ show err,
      testCase "if true then x else y: constrains branches to unify" $ do
        let env = Map.fromList [("x", T.Var "vx"), ("y", T.Var "vy")]
        let expr = If (Lit (LitBool True)) (P.Var "x") (P.Var "y")
        case runInfer (infer env expr) 0 of
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
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= [Equals(T.Int, T.Int), Equals(T.Int, T.Int)]
          Left err -> assertFailure $ show err,
      testCase "x + y (x,y:Var): constrains both to Int" $ do
        let env = Map.fromList [("x", T.Var "vx"), ("y", T.Var "vy")]
        let expr = BinOp Add (P.Var "x") (P.Var "y")
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            assertBool "x constrained to Int" $
              Equals (T.Var "vx", T.Int) `elem` cs || Equals (T.Int, T.Var "vx") `elem` cs
            assertBool "y constrained to Int" $
              Equals (T.Var "vy", T.Int) `elem` cs || Equals (T.Int, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "5 - 3: type=Int, constraints for Int operands" $ do
        let expr = BinOp Subtract (Lit (LitInt 5)) (Lit (LitInt 3))
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Int
            cs @?= [Equals (T.Int, T.Int), Equals (T.Int, T.Int)]
          Left err -> assertFailure $ show err,
      testCase "true && false: type=Bool, constraints=[(Bool,Bool),(Bool,Bool)]" $ do
        let expr = BinOp And (Lit (LitBool True)) (Lit (LitBool False))
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, cs) -> do
            t @?= T.Bool
            cs @?= [Equals (T.Bool, T.Bool), Equals (T.Bool, T.Bool)]
          Left err -> assertFailure $ show err,
      testCase "x && y (x,y:Var): constrains both to Bool" $ do
        let env = Map.fromList [("x", T.Var "vx"), ("y", T.Var "vy")]
        let expr = BinOp And (P.Var "x") (P.Var "y")
        case runInfer (infer env expr) 0 of
          Right (t, cs) -> do
            t @?= T.Bool
            assertBool "x constrained to Bool" $
              Equals (T.Var "vx", T.Bool) `elem` cs || Equals (T.Bool, T.Var "vx") `elem` cs
            assertBool "y constrained to Bool" $
              Equals (T.Var "vy", T.Bool) `elem` cs || Equals (T.Bool, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "true || false: type=Bool" $ do
        let expr = BinOp Or (Lit (LitBool True)) (Lit (LitBool False))
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, _) -> t @?= T.Bool
          Left err -> assertFailure $ show err
    ]

letBindingTests :: TestTree
letBindingTests =
  testGroup
    "Let Bindings"
    [ testCase "let x = 42 in x: type resolves to Int" $ do
        let expr = Let "x" (Lit (LitInt 42)) (P.Var "x")
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, _) -> do
            case t of
              T.Int -> return ()
              Scheme _ T.Int -> return ()
              _ -> assertFailure $ "Expected Int or Scheme _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let f = \\x -> x in f: generalizes to polymorphic scheme" $ do
        let expr = Let "f" (Lambda "x" Nothing (P.Var "x")) (P.Var "f")
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, _) -> do
            case t of
              Scheme vars (Arrow _ _) ->
                assertBool "Should have bound vars" (not (Set.null vars))
              Arrow (T.Var v1) (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Scheme or Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let id = \\x -> x in id 42: polymorphic use" $ do
        let expr =
              Let
                "id"
                (Lambda "x" Nothing (P.Var "x"))
                (App (P.Var "id") (Lit (LitInt 42)))
        case runInfer (infer emptyEnv expr) 0 of
          Right (t, _) -> do
            case t of
              T.Var _ -> return ()
              T.Int -> return ()
              _ -> assertFailure $ "Expected Var or Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let x = y in x (y:Int in env): produces constraints" $ do
        let env = Map.fromList [("y", T.Int)]
        let expr = Let "x" (P.Var "y") (P.Var "x")
        case runInfer (infer env expr) 0 of
          Right (_, cs) -> do
            assertBool "Should have constraints" (not (null cs))
          Left err -> assertFailure $ show err
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

standardEnv :: TypeEnv
standardEnv =
  Map.fromList
    [ ("x", T.Int),
      ("y", T.Bool),
      ("z", Arrow T.Int T.Int),
      ("a", T.Var "va"),
      ("b", T.Var "vb"),
      ("c", T.Var "vc")
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
      testProperty "Constraint count bounded by 3x expression size" prop_constraintBound
    ]

prop_literalsNoConstraints :: Property
prop_literalsNoConstraints = forAll genLiteral $ \expr ->
  case runInfer (infer emptyEnv expr) 0 of
    Right (_, cs) -> cs === []
    Left _ -> property False

prop_lambdaReturnsArrow :: Property
prop_lambdaReturnsArrow = forAll (genExpr 2) $ \bodyExpr ->
  forAll genVarName $ \paramName ->
    let expr = Lambda paramName Nothing bodyExpr
     in case runInfer (infer standardEnv expr) 0 of
          Right (t, _) -> case t of
            Arrow _ _ -> property True
            _ -> property False
          Left _ -> property True

prop_appProducesConstraint :: Property
prop_appProducesConstraint =
  forAll (genExpr 1) $ \e1 ->
    forAll (genExpr 1) $ \e2 ->
      let expr = App e1 e2
       in case runInfer (infer standardEnv expr) 0 of
            Right (_, cs) -> not (null cs) === True
            Left _ -> property True

prop_binOpResultType :: Property
prop_binOpResultType =
  forAll (elements [Add, Subtract, And, Or]) $ \op ->
    forAll (genExpr 1) $ \e1 ->
      forAll (genExpr 1) $ \e2 ->
        let expr = BinOp op e1 e2
            expectedType = if op `elem` [Add, Subtract] then T.Int else T.Bool
         in case runInfer (infer standardEnv expr) 0 of
              Right (t, _) -> t === expectedType
              Left _ -> property True

prop_conditionBool :: Property
prop_conditionBool =
  forAll (genExpr 1) $ \cond ->
    forAll (genExpr 1) $ \tr ->
      forAll (genExpr 1) $ \fl ->
        let expr = If cond tr fl
         in case runInfer (infer standardEnv expr) 0 of
              Right (_, cs) -> property $ any hasBoolConstraint cs
              Left _ -> property True
  where
    hasBoolConstraint (Equals (T.Bool, _)) = True
    hasBoolConstraint (Equals (_, T.Bool)) = True
    hasBoolConstraint _ = False

prop_constraintBound :: Property
prop_constraintBound = forAll (genExpr 2) $ \expr ->
  let exprSize = countNodes expr
   in case runInfer (infer standardEnv expr) 0 of
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
