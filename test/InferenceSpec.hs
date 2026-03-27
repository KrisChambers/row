{-# OPTIONS_GHC -Wno-orphans #-}

module InferenceSpec (inferenceTests) where

import Data.List (isInfixOf, isPrefixOf)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Debug.Trace qualified as Tr
import Parser (Expr (..), Literal (..), Op (..))
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Inference
import Type.Inference qualified as T
import Control.Monad.Except
import Control.Monad.State

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
      declTests,
      propertyTests,
      recordTests,
      helperTests,
      rowEqualityTests,
      effectStubTests,
      effectDeclTests,
      instantiateEffectInfoTests,
      rowApplication
    ]

doInfer :: T.TypeEnv -> Expr -> Either TypeError (Type, Type, [Constraint])
doInfer env expr = runInfer (infer env expr) 0 0

doInferDecl :: T.TypeEnv -> P.Decl -> Either TypeError T.TypeEnv
doInferDecl env decl = runInfer (addDeclToEnv env decl) 0 0


doSolve :: [Constraint] -> Either TypeError Substitution
doSolve cs = evalState unifyState IdSub
  where
    unifyState = runExceptT (solve cs)

-- ============================================================================
-- HUnit Tests
-- ============================================================================

literalTests :: TestTree
literalTests =
  testGroup
    "Literals"
    [ testCase "Integer literal: type=Int, constraints=[]" $ do
        let expr = Lit (LitInt 42)
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tInt
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool True)
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tBool
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Boolean False literal: type=Bool, constraints=[]" $ do
        let expr = Lit (LitBool False)
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tBool
            cs @?= []
          Left err -> assertFailure $ show err
    ]

variableTests :: TestTree
variableTests =
  testGroup
    "Variables"
    [ testCase "Lookup monomorphic Int: type=Int, constraints=[]" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty tInt)]}
        let expr = P.Var "x"
        case doInfer env expr of
          Right (t, e, cs) -> do
            t @?= tInt
            cs @?= []
          Left err -> assertFailure $ show err,
      testCase "Lookup monomorphic Arrow: type preserved, constraints=[]" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("f", Forall Set.empty $ Arrow tInt EmptyRow tBool)]}
        let expr = P.Var "f"
        case doInfer env expr of
          Right (t, e, cs) -> do
            t @?= Arrow tInt (T.Var "e1") tBool
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
        case doInfer T.prelude expr of
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
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) _ (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Const (\\x -> \\y -> x): Arrow v1 (Arrow v2 v1)" $ do
        let expr = Lambda "x" Nothing (Lambda "y" Nothing (P.Var "x"))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var v1) _ (Arrow (T.Var v2) _ (T.Var v3)) -> do
                v1 @?= v3
                assertBool "y different from x" (v2 /= v1)
              _ -> assertFailure $ "Expected nested Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Lambda with Int body (\\x -> 42): Arrow v1 Int, constraints=[]" $ do
        let expr = Lambda "x" Nothing (Lit (LitInt 42))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            cs @?= []
            case t of
              Arrow (T.Var _) _ tInt -> return ()
              _ -> assertFailure $ "Expected Arrow _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "Lambda constrains body (\\x -> x + 1): has (v1, Int) constraint" $ do
        let expr = Lambda "x" Nothing (BinOp Add (P.Var "x") (Lit (LitInt 1)))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            case t of
              Arrow param _ tr | tr == tInt -> do
                let hasParamConstraint =
                      any
                        ( \(Equals (a, b)) ->
                            (a == param && b == tInt) || (a == tInt && b == param)
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
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have at least one constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x where f:Int->Bool, x:Int: constraint links f to arg->result" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("f", Forall Set.empty $ Arrow tInt EmptyRow tBool), ("x", Forall Set.empty tInt)]}
        let expr = App (P.Var "f") (P.Var "x")
        case doInfer env expr of
          Right (t, e, cs) -> do
            case t of
              T.Var _ -> return ()
              _ -> assertFailure $ "Expected fresh Var, got: " ++ show t
            assertBool "Should have function constraint" (not (null cs))
          Left err -> assertFailure $ show err,
      testCase "f x y (curried): produces multiple constraints" $ do
        let env =
              prelude
                { envVars =
                    Map.union (envVars prelude) $
                      Map.fromList
                        [ ("f", Forall Set.empty $ Arrow tInt EmptyRow (Arrow tInt EmptyRow tInt)),
                          ("x", Forall Set.empty tInt),
                          ("y", Forall Set.empty tInt)
                        ]
                }
        let expr = App (App (P.Var "f") (P.Var "x")) (P.Var "y")
        case doInfer env expr of
          Right (_, e, cs) -> do
            assertBool "Should have >= 2 constraints" (length cs >= 2)
          Left err -> assertFailure $ show err,
      testCase "Application with undefined arg: propagates error" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("f", Forall Set.empty $ Arrow tInt EmptyRow tInt)]}
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
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tInt
            assertBool "Has condition constraint" (Equals (tBool, tBool) `elem` cs)
            assertBool "Has branch constraint" (Equals (tInt, tInt) `elem` cs)
          Left err -> assertFailure $ show err,
      testCase "if x then 1 else 2 (x:Var): constrains x to Bool" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty $ T.Var "vx")]}
        let expr = If (P.Var "x") (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer env expr of
          Right (_, e, cs) -> do
            let hasBoolConstraint =
                  any
                    ( \(Equals (a, b)) ->
                        (a == tBool && b == T.Var "vx")
                          || (a == T.Var "vx" && b == tBool)
                    )
                    cs
            assertBool "Should constrain condition to Bool" hasBoolConstraint
          Left err -> assertFailure $ show err,
      testCase "if true then x else y: constrains branches to unify" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty $ T.Var "vx"), ("y", Forall Set.empty $ T.Var "vy")]}
        let expr = If (Lit (LitBool True)) (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, e, cs) -> do
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
    [ testCase "1 + 2: type=Int, constraints=[(Int,Int),(Int,Int), .. effects]" $ do
        let expr = BinOp Add (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tInt
            cs @?= [Equals (tInt, tInt), Equals (tInt, tInt), Equals (T.Var "e1", T.Var "e3"), Equals (T.Var "e2", T.Var "e3")]
          Left err -> assertFailure $ show err,
      testCase "x + y (x,y:Var): constrains both to Int" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty $ T.Var "vx"), ("y", Forall Set.empty $ T.Var "vy")]}
        let expr = BinOp Add (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, e, cs) -> do
            t @?= tInt
            assertBool "x constrained to Int" $
              Equals (T.Var "vx", tInt) `elem` cs || Equals (tInt, T.Var "vx") `elem` cs
            assertBool "y constrained to Int" $
              Equals (T.Var "vy", tInt) `elem` cs || Equals (tInt, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "5 - 3: type=Int, constraints for Int operands" $ do
        let expr = BinOp Subtract (Lit (LitInt 5)) (Lit (LitInt 3))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tInt
            cs @?= [Equals (tInt, tInt), Equals (tInt, tInt), Equals (T.Var "e1", T.Var "e3"), Equals (T.Var "e2", T.Var "e3")]
          Left err -> assertFailure $ show err,
      testCase "true && false: type=Bool, constraints=[(Bool,Bool),(Bool,Bool)]" $ do
        let expr = BinOp And (Lit (LitBool True)) (Lit (LitBool False))
        case doInfer T.prelude expr of
          Right (t, e, cs) -> do
            t @?= tBool
            cs @?= [Equals (tBool, tBool), Equals (tBool, tBool), Equals (T.Var "e1", T.Var "e3"), Equals (T.Var "e2", T.Var "e3")]
          Left err -> assertFailure $ show err,
      testCase "x && y (x,y:Var): constrains both to Bool" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty $ T.Var "vx"), ("y", Forall Set.empty $ T.Var "vy")]}
        let expr = BinOp And (P.Var "x") (P.Var "y")
        case doInfer env expr of
          Right (t, e, cs) -> do
            t @?= tBool
            assertBool "x constrained to Bool" $
              Equals (T.Var "vx", tBool) `elem` cs || Equals (tBool, T.Var "vx") `elem` cs
            assertBool "y constrained to Bool" $
              Equals (T.Var "vy", tBool) `elem` cs || Equals (tBool, T.Var "vy") `elem` cs
          Left err -> assertFailure $ show err,
      testCase "true || false: type=Bool" $ do
        let expr = BinOp Or (Lit (LitBool True)) (Lit (LitBool False))
        case doInfer T.prelude expr of
          Right (t, e, _) -> t @?= tBool
          Left err -> assertFailure $ show err
    ]

letBindingTests :: TestTree
letBindingTests =
  testGroup
    "Let Bindings"
    [ testCase "let x = 42 in x: type resolves to Int" $ do
        let expr = Let "x" (Lit (LitInt 42)) (P.Var "x")
        case doInfer T.prelude expr of
          Right (t, e, _) -> do
            if t == tInt
              then return ()
              else assertFailure $ "Expected Int or Scheme _ Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let f = \\x -> x in f: generalizes to polymorphic scheme" $ do
        let expr = Let "f" (Lambda "x" Nothing (P.Var "x")) (P.Var "f")
        case doInfer T.prelude expr of
          Right (t, e, _) -> do
            case t of
              -- Scheme vars (Arrow _ _) ->
              --   assertBool "Should have bound vars" (not (Set.null vars))
              Arrow (T.Var v1) _ (T.Var v2) -> v1 @?= v2
              _ -> assertFailure $ "Expected Scheme or Arrow, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let id = \\x -> x in id 42: polymorphic use" $ do
        let expr =
              Let
                "id"
                (Lambda "x" Nothing (P.Var "x"))
                (App (P.Var "id") (Lit (LitInt 42)))
        case doInfer T.prelude expr of
          Right (t, e, _) -> do
            case t of
              T.Var _ -> return ()
              T.TCon {} | t == tInt -> return ()
              _ -> assertFailure $ "Expected Var or Int, got: " ++ show t
          Left err -> assertFailure $ show err,
      testCase "let x = y in x (y:Int in env): produces constraints" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("y", Forall Set.empty tInt)]}
        let expr = Let "x" (P.Var "y") (P.Var "x")
        case doInfer env expr of
          Right (_, e, cs) -> do
            assertBool "Should have constraints" (not (null cs))
          Left err -> assertFailure $ show err
    ]

declTests :: TestTree
declTests =
  testGroup
    "Declaration Tests (addDeclToEnv)"
    [ -- Basic value bindings
      testCase "let x = 42: adds x:Int to env" $ do
        let decl = P.LetDecl "x" Nothing (Lit (LitInt 42))
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "x" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tInt
              Nothing -> assertFailure "x not found in env"
          Left err -> assertFailure $ show err,
      testCase "let flag = true: adds flag:Bool to env" $ do
        let decl = P.LetDecl "flag" Nothing (Lit (LitBool True))
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "flag" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tBool
              Nothing -> assertFailure "flag not found in env"
          Left err -> assertFailure $ show err,
      testCase "let u = (): adds u:() to env" $ do
        let decl = P.LetDecl "u" Nothing (P.Var "()")
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "u" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tUnit
              Nothing -> assertFailure "u not found in env"
          Left err -> assertFailure $ show err,
      -- Lambda bindings
      testCase "let id = \\x -> x: adds polymorphic identity" $ do
        let decl = P.LetDecl "id" Nothing (Lambda "x" Nothing (P.Var "x"))
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "id" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be polymorphic" (not (Set.null vars))
                case t of
                  Arrow (T.Var v1) _ (T.Var v2) -> v1 @?= v2
                  _ -> assertFailure $ "Expected Arrow type, got: " ++ show t
              Nothing -> assertFailure "id not found in env"
          Left err -> assertFailure $ show err,
      testCase "let const = \\x -> \\y -> x: adds polymorphic const" $ do
        let decl = P.LetDecl "const" Nothing (Lambda "x" Nothing (Lambda "y" Nothing (P.Var "x")))
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "const" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be polymorphic" (not (Set.null vars))
                case t of
                  Arrow (T.Var v1) _ (Arrow _ _ (T.Var v2)) -> v1 @?= v2
                  _ -> assertFailure $ "Expected nested Arrow type, got: " ++ show t
              Nothing -> assertFailure "const not found in env"
          Left err -> assertFailure $ show err,
      testCase "let f = \\x -> x + 1: adds f: Int -> Int" $ do
        let decl = P.LetDecl "f" Nothing (Lambda "x" Nothing (BinOp Add (P.Var "x") (Lit (LitInt 1))))
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "f" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic (Int -> Int)" (Set.null vars)
                case t of
                  Arrow t1 _ t2 -> do
                    t1 @?= tInt
                    t2 @?= tInt
                  _ -> assertFailure $ "Expected Arrow type, got: " ++ show t
              Nothing -> assertFailure "f not found in env"
          Left err -> assertFailure $ show err,
      -- Referencing environment
      testCase "let x = y (y:Int in env): x gets Int type" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("y", Forall Set.empty tInt)]}
        let decl = P.LetDecl "x" Nothing (P.Var "y")
        case doInferDecl env decl of
          Right env' -> do
            case Map.lookup "x" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tInt
              Nothing -> assertFailure "x not found in env"
          Left err -> assertFailure $ show err,
      testCase "let z = f 42 (f:Int->Bool in env): z gets Bool type" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("f", Forall Set.empty $ Arrow tInt EmptyRow tBool)]}
        let decl = P.LetDecl "z" Nothing (App (P.Var "f") (Lit (LitInt 42)))
        case doInferDecl env decl of
          Right env' -> do
            case Map.lookup "z" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tBool
              Nothing -> assertFailure "z not found in env"
          Left err -> assertFailure $ show err,
      -- Shadowing
      testCase "let x = 42 shadows x:Bool: x becomes Int" $ do
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.fromList [("x", Forall Set.empty tBool)]}
        let decl = P.LetDecl "x" Nothing (Lit (LitInt 42))
        case doInferDecl env decl of
          Right env' -> do
            case Map.lookup "x" (envVars env') of
              Just (Forall vars t) -> do
                assertBool "Should be monomorphic" (Set.null vars)
                t @?= tInt
              Nothing -> assertFailure "x not found in env"
          Left err -> assertFailure $ show err,
      -- Error cases
      testCase "let x = unknownVar: returns UnboundVariable error" $ do
        let decl = P.LetDecl "x" Nothing (P.Var "unknownVar")
        case doInferDecl T.prelude decl of
          Left (InferenceError msg) ->
            assertBool "Error should mention variable" ("unknownVar" `isInfixOf` msg)
          Left err -> assertFailure $ "Wrong error type: " ++ show err
          Right _ -> assertFailure "Should have failed",
      testCase "data Thing = One | Two" $ do
        let decl = P.DataDecl [] "Thing" [("One", []), ("Two", [])]
        case doInferDecl T.prelude decl of
          Right env' -> do
            let testLookup name envMap test = do
                  case Map.lookup name envMap of
                    Just value -> test value
                    Nothing -> assertFailure $ "Could not find " ++ name ++ " in the environment"
            let expectedType = T.TCon "Thing"

            -- Check things are properly assemed in the term -> Type map

            testLookup "One" (envVars env') $ \(Forall vars t) -> do
                  assertBool "Should be a type value" (Set.null vars)
                  t @?= expectedType

            testLookup "Two" (envVars env') $ \(Forall vars t) -> do
                assertBool "Should be a type value" (Set.null vars)
                t @?= expectedType


            -- Check that type info is properly stored

            testLookup "Thing" (envTypes env') $ \(T.TypeInfo params kind) -> do
                params @?= []
                kind @?= T.KType

            -- And check constructor information is added
            testLookup "One" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "Thing"
                scheme @?= T.Forall (Set.empty) (expectedType)

            -- And check constructor information is added
            testLookup "Two" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "Thing"
                scheme @?= T.Forall (Set.empty) (expectedType)


          Left err ->
            assertFailure $ show err,

      testCase "data Thing a = One a | Two a" $ do
        let decl = P.DataDecl ["a"] "Thing" [("One", [P.TVar "a"]), ("Two", [P.TVar "a"])]
        case doInferDecl T.prelude decl of
          Right env' -> do
            let testLookup name envMap test = do
                  case Map.lookup name envMap of
                    Just value -> test value
                    Nothing -> assertFailure $ "Could not find " ++ name ++ " in the environment"
            let expectedType = Arrow (T.Var "a") EmptyRow (T.TApp (T.TCon "Thing") (T.Var "a"))

            -- Check things are properly assemed in the term -> Type map

            testLookup "One" (envVars env') $ \(Forall vars t) -> do
                  assertBool "One should have a single param" ("a" `elem` vars)
                  t @?= expectedType

            testLookup "Two" (envVars env') $ \(Forall vars t) -> do
                assertBool "Two should have a single param" ("a" `elem` vars)
                t @?= expectedType


            -- Check that type info is properly stored

            testLookup "Thing" (envTypes env') $ \(T.TypeInfo params kind) -> do
                params @?= ["a"]
                kind @?= T.KArrow T.KType T.KType

            -- And check constructor information is added
            testLookup "One" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "Thing"
                scheme @?= T.Forall (Set.fromList ["a"]) expectedType

            -- And check constructor information is added
            testLookup "Two" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "Thing"
                scheme @?= T.Forall (Set.fromList ["a"]) expectedType


          Left err ->
            assertFailure $ show err,

      testCase "data List a = Nil | Cons a (List a)" $ do
        let decl = P.DataDecl ["a"] "List" [("Nil", []), ("Cons", [P.TVar "a", P.TCon "List" [P.TVar "a"]])]
        case doInferDecl T.prelude decl of
          Right env' -> do
            let varA = T.Var "a"
            let listOfA = T.TApp (T.TCon "List") varA
            let testLookup name envMap test = do
                  case Map.lookup name envMap of
                    Just value -> test value
                    Nothing -> assertFailure $ "Could not find " ++ name ++ " in the environment"

            testLookup "Nil" (envVars env') $ \(Forall vars t) -> do
                  assertBool "Nil should be a value" (Set.null vars)
                  t @?= listOfA

            testLookup "Cons" (envVars env') $ \(Forall vars t) -> do
                assertBool "Cons should have a single param" ("a" `elem` vars)
                t @?= (T.Arrow varA EmptyRow $ T.Arrow listOfA EmptyRow listOfA)


            -- Check that type info is properly stored

            testLookup "List" (envTypes env') $ \(T.TypeInfo params kind) -> do
                params @?= ["a"]
                kind @?= T.KArrow T.KType T.KType

            -- And check constructor information is added
            testLookup "Nil" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "List"
                scheme @?= T.Forall (Set.fromList ["a"]) listOfA

            -- And check constructor information is added
            testLookup "Two" (envCstors env') $ \(T.CtorInfo typeName scheme) -> do
                typeName @?= "Thing"
                scheme @?= T.Forall (Set.fromList ["a"]) (T.Arrow varA EmptyRow $ T.Arrow listOfA EmptyRow listOfA)


          Left err ->
            assertFailure $ show err
    ]

recordTests :: TestTree
recordTests =
  testGroup
    "Record rows"
    [ testCase "{ x = 0, y = 0 } resolves to a Record type { x: Int, y: Int }" $ do
        let expr = P.Record (P.RecordCstr [("x", Lit (LitInt 0)), ("y", Lit (LitInt 0))])
        case doInfer T.prelude expr of
          Right (t, e, _) -> do
            case t of
              T.Record row -> case row of
                Row (l1, t1) (Row (l2, t2) EmptyRow) -> do
                  l1 @?= "y"
                  l2 @?= "x"
                  t1 @?= tInt
                  t2 @?= tInt
                _ -> assertFailure "Expected Row type with labels 'x' and 'y'"
              _ -> assertFailure ""
          Left err -> assertFailure $ show err,
      testCase "Simple record extension { r with l = 5 } should give a type { l : Int | p }" $ do
        let expr = P.Record $ P.RecordExtension (P.Record $ P.RecordCstr []) "l" (P.Lit $ LitInt 5)
        case doInfer T.prelude expr of
          Right (t, e, c) -> do
            case t of
              T.Record (Row (l, lt) r) -> do
                l @?= "l"
                lt @?= tInt
                r @?= T.Var "r1"
              _ -> assertFailure $ "Expected an empty record but got: " ++ reportInferResult t c
          Left err -> assertFailure $ show err,
      testCase "Extend a non_empty record: { 2dOrigin with z = 0 }" $ do
        let origin2d = T.Record (T.Row ("x", tInt) (T.Row ("y", tInt) EmptyRow))
        let env = prelude {envVars = Map.union (envVars prelude) $ Map.insert "origin2d" (Forall Set.empty origin2d) (envVars prelude)}
        let expr = P.Record (P.RecordExtension (P.Var "origin2d") "z" (P.Lit $ LitInt 0))
        case doInfer env expr of
          Left err -> assertFailure $ show err
          Right (t, _e, c) -> do
            case t of
              T.Record (Row (l, lt) r) -> do
                l @?= "z"
                lt @?= tInt
                r @?= T.Var "r1"
                -- Check that the record constraint is present (effect constraints may also be present)
                assertBool "Should have record constraint" $
                  Equals (T.Record r, origin2d) `elem` c
              _ -> assertFailure $ "Expected an empty record but got: " ++ reportInferResult t c
    ]

reportInferResult :: Type -> [Constraint] -> String
reportInferResult t c = prefix ++ "Type: " ++ show t ++ prefix ++ "Constraints: " ++ show c
  where
    prefix = "\n\t"

helperTests :: TestTree
helperTests =
  testGroup
    "Helper Functions"
    [ --createCstrInfoTests,
      toHeadTests
    ]

-- createCstrInfoTests :: TestTree
-- createCstrInfoTests =
--   testGroup
--     "createCstrInfo"
--     [ testCase "Empty list returns tUnit" $ do
--         createTestCstr [] @?= Forall mempty thingCstr,
--       testCase "Single type creates Arrow to tUnit" $ do
--         createTestCstr [tInt] @?= Forall mempty (Arrow tInt EmptyRow tUnit),
--       testCase "Two types creates nested Arrow" $ do
--         createTestCstr [tInt, tBool] @?= Forall mempty (Arrow tInt EmptyRow (Arrow tBool EmptyRow tUnit)),
--       testCase "Three types creates 3-level nested Arrow" $ do
--        createTestCstr [tInt, tBool, tString] @?= Arrow tInt EmptyRow (Arrow tBool EmptyRow (Arrow tString EmptyRow tUnit)),
--       testCase "Mixed types with type variables" $ do
--         T.createCstrInfo thingCstr [T.Var "a", tInt] @?= Arrow (T.Var "a") EmptyRow (Arrow tInt EmptyRow tUnit),
--       testCase "All arrows use EmptyRow for effects" $ do
--         let result = T.createCstrInfo thingCstr [tInt, tBool]
--         case result of
--           Arrow _ e1 (Arrow _ e2 tUnit) -> do
--             e1 @?= EmptyRow
--             e2 @?= EmptyRow
--           _ -> assertFailure $ "Expected nested Arrow with EmptyRow effects, got: " ++ show result
--     ]
--     where
--       createTestCstr params = T.createCstrInfo thingCstr params
--       thingCstr = T.TCon "Thing" []

toHeadTests :: TestTree
toHeadTests =
  testGroup
    "toHead row reordering"
    [ testCase "Empty row returns empty row" $ do
        toHead EmptyRow "x" @?= EmptyRow,
      testCase "Var returns unchanged" $ do
        toHead (T.Var "r") "x" @?= T.Var "r",
      testCase "Label already at head returns unchanged" $ do
        let row = Row ("x", tInt) (Row ("y", tBool) EmptyRow)
        toHead row "x" @?= row,
      testCase "Swaps adjacent element to head" $ do
        let row = Row ("a", tInt) (Row ("x", tBool) EmptyRow)
        toHead row "x" @?= Row ("x", tBool) (Row ("a", tInt) EmptyRow),
      testCase "Duplicate labels: finds first occurrence (x::Int before x::Bool)" $ do
        let row = Row ("a", tInt) (Row ("x", tInt) (Row ("x", tBool) EmptyRow))
        let expected = Row ("x", tInt) (Row ("a", tInt) (Row ("x", tBool) EmptyRow))
        toHead row "x" @?= expected,
      testCase "Label deeper in row is brought forward" $ do
        let row = Row ("a", tInt) (Row ("b", tBool) (Row ("x", tInt) EmptyRow))
        let result = toHead row "x"
        case result of
          Row ("b", _) (Row ("x", rt) _) | rt == tInt -> return ()
          _ -> assertFailure $ "Expected 'x' to be moved forward, got: " ++ show result,
      testCase "Single element row with matching label returns unchanged" $ do
        let row = Row ("x", tInt) EmptyRow
        toHead row "x" @?= row,
      testCase "Row ending in Var returns unchanged when label not found" $ do
        let row = Row ("a", tInt) (T.Var "r")
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
        let row = Row ("x", tInt) EmptyRow
        row @?= row,
      -- Reordering (distinct labels)
      testCase "Rows with distinct labels: reordering is equal {x:Int,y:Bool} == {y:Bool,x:Int}" $ do
        let row1 = Row ("x", tInt) (Row ("y", tBool) EmptyRow)
        let row2 = Row ("y", tBool) (Row ("x", tInt) EmptyRow)
        row1 @?= row2,
      testCase "Three element row reordering {a:Int,b:Bool,c:Int} == {c:Int,a:Int,b:Bool}" $ do
        let row1 = Row ("a", tInt) (Row ("b", tBool) (Row ("c", tInt) EmptyRow))
        let row2 = Row ("c", tInt) (Row ("a", tInt) (Row ("b", tBool) EmptyRow))
        row1 @?= row2,
      -- Inequality cases
      testCase "Different labels are not equal {x:Int} /= {y:Int}" $ do
        let row1 = Row ("x", tInt) EmptyRow
        let row2 = Row ("y", tInt) EmptyRow
        assertBool "{x:Int} /= {y:Int}" (row1 /= row2),
      testCase "Same label different types not equal {x:Int} /= {x:Bool}" $ do
        let row1 = Row ("x", tInt) EmptyRow
        let row2 = Row ("x", tBool) EmptyRow
        assertBool "{x:Int} /= {x:Bool}" (row1 /= row2),
      testCase "Different lengths not equal {x:Int,y:Bool} /= {x:Int}" $ do
        let row1 = Row ("x", tInt) (Row ("y", tBool) EmptyRow)
        let row2 = Row ("x", tInt) EmptyRow
        assertBool "different lengths" (row1 /= row2),
      -- Duplicate labels (order matters within same label)
      testCase "Duplicate labels same order are equal {x:Int,x:Bool} == {x:Int,x:Bool}" $ do
        let row1 = Row ("x", tInt) (Row ("x", tBool) EmptyRow)
        let row2 = Row ("x", tInt) (Row ("x", tBool) EmptyRow)
        row1 @?= row2,
      testCase "Duplicate labels swapped are NOT equal {x:Int,x:Bool} /= {x:Bool,x:Int}" $ do
        let row1 = Row ("x", tInt) (Row ("x", tBool) EmptyRow)
        let row2 = Row ("x", tBool) (Row ("x", tInt) EmptyRow)
        assertBool "{x:Int,x:Bool} /= {x:Bool,x:Int}" (row1 /= row2),
      testCase "Reorder non-duplicate doesn't cross duplicate {a:Int,x:Int,x:Bool} == {x:Int,a:Int,x:Bool}" $ do
        let row1 = Row ("a", tInt) (Row ("x", tInt) (Row ("x", tBool) EmptyRow))
        let row2 = Row ("x", tInt) (Row ("a", tInt) (Row ("x", tBool) EmptyRow))
        row1 @?= row2,
      -- Mixed with Var
      testCase "Row with same Var tail are equal" $ do
        let row1 = Row ("x", tInt) (T.Var "r")
        let row2 = Row ("x", tInt) (T.Var "r")
        row1 @?= row2,
      testCase "Row with different Var tail are not equal" $ do
        let row1 = Row ("x", tInt) (T.Var "r")
        let row2 = Row ("x", tInt) (T.Var "s")
        assertBool "different Var tails" (row1 /= row2),
      testCase "{ x : Int, y: Int} should not equal { x: v1 | r1 }" $ do
        let row1 = T.Record $ Row ("y", tInt) (Row ("x", tInt) EmptyRow)
        let row2 = T.Record $ Row ("x", T.Var "v1") (T.Var "r1")
        assertBool "different types" (row1 /= row2)
    ]

{-
let foo =
  perform Console.print "Hello, World"

let main =
  handle foo () using
    | Console.print k s ->
-}

effectStubTests :: TestTree
effectStubTests =
  testGroup
    "Effect Stub Tests"
    [ testCase "Literal generates an effect variable" $ do
        let expr = Lit (LitInt 42)
        case doInfer T.prelude expr of
          Right (_t, e, _cs) -> do
            case e of
              T.Var name -> assertBool "Effect var should start with 'e'" ("e" `isPrefixOf` name)
              _ -> assertFailure $ "Expected effect variable, got: " ++ show e
          Left err -> assertFailure $ show err,
      testCase "Lambda body effect flows to arrow effect" $ do
        let expr = Lambda "x" Nothing (P.Var "x")
        case doInfer T.prelude expr of
          Right (t, _lambdaEffect, _cs) -> do
            case t of
              Arrow _param arrowEffect _ret ->
                case arrowEffect of
                  T.Var name -> assertBool "Arrow effect should be variable" ("e" `isPrefixOf` name)
                  _ -> assertFailure $ "Expected effect var in arrow, got: " ++ show arrowEffect
              _ -> assertFailure "Expected Arrow type"
          Left err -> assertFailure $ show err,
      testCase "Application generates effect constraints" $ do
        let expr = App (Lambda "x" Nothing (P.Var "x")) (Lit (LitInt 42))
        case doInfer T.prelude expr of
          Right (_t, _e, cs) -> do
            let hasEffectConstraint = any isEffectConstraint cs
            assertBool "Should have effect-related constraint" hasEffectConstraint
          Left err -> assertFailure $ show err,
      testCase "Binary operations have EmptyRow effect" $ do
        let expr = BinOp Add (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer T.prelude expr of
          Right (_t, e, _cs) -> e @?= T.Var "e3"
          Left err -> assertFailure $ show err,
      testCase "Conditionals have EmptyRow effect" $ do
        let expr = If (Lit (LitBool True)) (Lit (LitInt 1)) (Lit (LitInt 2))
        case doInfer T.prelude expr of
          Right (_t, e, _cs) -> e @?= EmptyRow
          Left err -> assertFailure $ show err,
      testCase "STUB: Let binding infers without error" $ do
        let expr = Let "x" (Lit (LitInt 42)) (P.Var "x")
        case doInfer T.prelude expr of
          Right (_, e, _) -> do
            e @?= T.Var "e1" -- This isn't all that great
          Left err -> assertFailure $ show err,
      testCase "Record construction has effect" $ do
        let expr = P.Record (P.RecordCstr [("x", Lit (LitInt 0))])
        case doInfer T.prelude expr of
          Right (_t, e, _cs) ->
            case e of
              T.Var _ -> return ()
              EmptyRow -> return ()
              _ -> assertFailure $ "Unexpected effect: " ++ show e
          Left err -> assertFailure $ show err
    ]
  where
    isEffectConstraint (Equals (T.Var name, _)) = "e" `isPrefixOf` name
    isEffectConstraint (Equals (_, T.Var name)) = "e" `isPrefixOf` name
    isEffectConstraint _ = False

effectDeclTests :: TestTree
effectDeclTests =
  testGroup
    "Effect Declaration Tests"
    [ testCase "EffectDecl adds effect to envEffects" $ do
        -- Define: effect Log { log : Int -> () }
        let logOp = P.TFun P.TInt (P.TCon "()" []) P.EEmptyRow
        let decl = P.EffectDecl "Log" [] [("log", logOp)]
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "Log" (envEffects env') of
              Just info -> do
                assertBool "Has log op" $ Map.member "log" (effectInfoOps info)
              Nothing -> assertFailure "Log effect not found"
          Left err -> assertFailure $ show err,
      testCase "EffectDecl with parameter adds polymorphic effect" $ do
        -- Define: effect State a { get : () -> a, put : a -> () }
        let getOp = P.TFun (P.TCon "()" []) (P.TVar "a") P.EEmptyRow -- () -> a
        let putOp = P.TFun (P.TVar "a") (P.TCon "()" []) P.EEmptyRow -- a -> ()
        let decl = P.EffectDecl "State" ["a"] [("get", getOp), ("put", putOp)]
        case doInferDecl T.prelude decl of
          Right env' -> do
            case Map.lookup "State" (envEffects env') of
              Just info -> do
                effectInfoParams info @?= ["a"]
                assertBool "Has get op" $ Map.member "get" (effectInfoOps info)
                assertBool "Has put op" $ Map.member "put" (effectInfoOps info)
              Nothing -> assertFailure "State effect not found"
          Left err -> assertFailure $ show err,
      testCase "Lambda with Perform has effect variable in arrow type" $ do
        let consoleEffect = P.EffectDecl "Console" [] [("print", P.TFun (P.TCon "String" []) (P.TCon "()" []) P.EEmptyRow)]
        env <- either (assertFailure . show) return $ inferDecl [consoleEffect]
        let expr = Lambda "x" Nothing (P.Perform "Console" "print" (P.Var "x"))
        case doInfer env expr of
          Right (t, _e, _cs) -> do
            case t of
              Arrow _arg effect _ret ->
                -- Effect should be a variable that will unify to Console
                case effect of
                  T.Var name -> assertBool "Effect var starts with e" ("e" `isPrefixOf` name)
                  T.Row (name, rt) rtail -> assertBool "Should be an open Console effect" (name == "Console" && rtail /= EmptyRow)
                  _ -> assertFailure $ "Expected effect variable in arrow, got: " ++ show effect
              _ -> assertFailure $ "Expected Arrow, got: " ++ show t
          Left err -> assertFailure $ show err
    ]

instantiateEffectInfoTests :: TestTree
instantiateEffectInfoTests =
  testGroup
    "instantiateEffectInfo Tests"
    [ testCase "Instantiates polymorphic EffectInfo to monomorphic" $ do
        -- Create an EffectInfo with a parameter "a"
        let getOp = Forall (Set.fromList ["a"]) (Arrow tUnit EmptyRow (T.Var "a"))
        let putOp = Forall (Set.fromList ["a"]) (Arrow (T.Var "a") EmptyRow tUnit)
        let info = EffectInfo
              { effectInfoParams = ["a"]
              , effectInfoOps = Map.fromList [("get", getOp), ("put", putOp)]
              }
        -- Run instantiateEffectInfo
        case runInfer (instantiateEffectInfo info) 0 0 of
          Right newInfo -> do
            -- Parameters should be empty after instantiation
            effectInfoParams newInfo @?= []
            -- Operations should exist
            assertBool "Has get op" $ Map.member "get" (effectInfoOps newInfo)
            assertBool "Has put op" $ Map.member "put" (effectInfoOps newInfo)
            -- The type variables should be replaced with fresh ones (not "a")
            case Map.lookup "get" (effectInfoOps newInfo) of
              Just (Forall vars (Arrow _ _ retType)) -> do
                Set.null vars @?= True
                case retType of
                  T.Var name -> assertBool "Return type should be fresh var (not 'a')" (name /= "a")
                  _ -> assertFailure $ "Expected Var return type, got: " ++ show retType
              _ -> assertFailure "get operation not found or wrong type"
          Left err -> assertFailure $ show err,
      testCase "Instantiates effect with no parameters" $ do
        -- Create an EffectInfo with no parameters
        let logOp = Forall Set.empty (Arrow tInt EmptyRow tUnit)
        let info = EffectInfo
              { effectInfoParams = []
              , effectInfoOps = Map.fromList [("log", logOp)]
              }
        case runInfer (instantiateEffectInfo info) 0 0 of
          Right newInfo -> do
            -- Should remain parameter-less
            effectInfoParams newInfo @?= []
            -- Operation should be unchanged (no variables to instantiate)
            case Map.lookup "log" (effectInfoOps newInfo) of
              Just (Forall vars (Arrow arg _ ret)) -> do
                Set.null vars @?= True
                arg @?= tInt
                ret @?= tUnit
              _ -> assertFailure "log operation not found or wrong type"
          Left err -> assertFailure $ show err
    ]


rowApplication :: TestTree
rowApplication =
  testGroup
    "Row application to a function"
    [ testCase "Full: f { l = 0, s = True } = 1" $ do
        let body = P.If
              (P.Record $ P.RecordAccess (P.Var "r") "s")
              (P.BinOp P.Add (P.Record $ P.RecordAccess (P.Var "r") "l") (P.Lit $ P.LitInt 1))
              (P.BinOp P.Add (P.Record $ P.RecordAccess (P.Var "r") "l") (P.Lit $ P.LitInt 2))
        let f = P.Lambda "r" Nothing body
        let arg = P.Record $ P.RecordCstr [("l", P.Lit $ P.LitInt 0), ("s", P.Lit $ P.LitBool True)]

        let expr = P.App f arg

        case doInfer T.prelude expr of
          Right (t, _, c) -> case doSolve c of
              Right s -> do
                apply s t @?= tInt
              Left err -> assertFailure $ show err
          Left err -> assertFailure $ show err,

      testCase "Partial: f { l = 0 } = ?" $ do
        let body = P.If
              (P.Record $ P.RecordAccess (P.Var "r") "s")
              (P.BinOp P.Add (P.Record $ P.RecordAccess (P.Var "r") "l") (P.Lit $ P.LitInt 1))
              (P.BinOp P.Add (P.Record $ P.RecordAccess (P.Var "r") "l") (P.Lit $ P.LitInt 2))
        let f = P.Lambda "r" Nothing body
        let arg = P.Record $ P.RecordCstr [("l", P.Lit $ P.LitInt 0)]

        let expr = P.App f arg

        case doInfer T.prelude expr of
          Right (t, _, c) -> case doSolve c of
              Right s -> do
                apply s t @?= tInt
              Left err -> assertFailure $ show err
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

genRowLabel :: Gen String
genRowLabel = elements ["a", "b", "c", "x", "y", "z"]

genSimpleType :: Gen Type
genSimpleType = elements [tInt, tBool]

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
  prelude
    { envVars =
        Map.union (envVars prelude) $
          Map.fromList
            [ ("x", Forall Set.empty tInt),
              ("y", Forall Set.empty tBool),
              ("z", Forall Set.empty $ Arrow tInt EmptyRow tInt),
              ("a", Forall Set.empty $ T.Var "va"),
              ("b", Forall Set.empty $ T.Var "vb"),
              ("c", Forall Set.empty $ T.Var "vc")
            ]
    }

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
  case doInfer T.prelude expr of
    Right (_, e, cs) -> cs === []
    Left _ -> property False

prop_lambdaReturnsArrow :: Property
prop_lambdaReturnsArrow = forAll (genExpr 2) $ \bodyExpr ->
  forAll genVarName $ \paramName ->
    let expr = Lambda paramName Nothing bodyExpr
     in case doInfer standardEnv expr of
          Right (t, e, _) -> case t of
            Arrow _ _ _ -> property True
            _ -> property False
          Left _ -> property True

prop_appProducesConstraint :: Property
prop_appProducesConstraint =
  forAll (genExpr 1) $ \e1 ->
    forAll (genExpr 1) $ \e2 ->
      let expr = App e1 e2
       in case doInfer standardEnv expr of
            Right (_, e, cs) -> not (null cs) === True
            Left _ -> property True

prop_binOpResultType :: Property
prop_binOpResultType =
  forAll (elements [Add, Subtract, And, Or]) $ \op ->
    forAll (genExpr 1) $ \e1 ->
      forAll (genExpr 1) $ \e2 ->
        let expr = BinOp op e1 e2
            expectedType = if op `elem` [Add, Subtract] then tInt else tBool
         in case doInfer standardEnv expr of
              Right (t, e, _) -> t === expectedType
              Left _ -> property True

prop_conditionBool :: Property
prop_conditionBool =
  forAll (genExpr 1) $ \cond ->
    forAll (genExpr 1) $ \tr ->
      forAll (genExpr 1) $ \fl ->
        let expr = If cond tr fl
         in case doInfer standardEnv expr of
              Right (_, e, cs) -> property $ any hasBoolConstraint cs
              Left _ -> property True
  where
    hasBoolConstraint (Equals (tBool, _)) = True
    hasBoolConstraint (Equals (_, tBool)) = True
    hasBoolConstraint _ = False

prop_constraintBound :: Property
prop_constraintBound = forAll (genExpr 2) $ \expr ->
  let exprSize = countNodes expr
   in case doInfer standardEnv expr of
        Right (_, e, cs) -> property (length cs <= exprSize * 3)
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
