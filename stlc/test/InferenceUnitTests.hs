module InferenceUnitTests (allTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Type.Inference (Type)
import Type.Inference qualified as T (Type(..), inferType)
import Parser (Expr(..), Literal(..), Op(..))

-- Helper to assert type inference succeeds with expected type
assertInfersType :: String -> Expr -> Type -> Assertion
assertInfersType testName expr expected =
    case T.inferType expr of
                Left err -> assertFailure $ testName ++ ": Inference failed with error: " ++ show err
                Right t -> assertEqual testName expected t

-- Helper to assert type inference fails
assertInferenceError :: String -> Expr -> Assertion
assertInferenceError testName expr =
    case T.inferType expr of
            Left _ -> return ()
            Right t -> assertFailure $ testName ++ ": Expected inference to fail, but got: " ++ show t

-- Tests for variable type inference
test_variable_inference :: TestTree
test_variable_inference = testGroup "Variable Inference"
    [ testCase "undefined variable gives error" $
        assertInferenceError "undefined variable" (Var "undefined_var")
    , testCase "let-bound Int variable has type Int" $
        assertInfersType "let-bound Int" (Let "x" (Lit (LitInt 42)) (Var "x")) T.Int
    , testCase "let-bound Bool variable has type Bool" $
        assertInfersType "let-bound Bool" (Let "b" (Lit (LitBool True)) (Var "b")) T.Bool
    , testCase "nested let shadows outer variable" $
        assertInfersType "nested let" (Let "x" (Lit (LitInt 1)) (Let "x" (Lit (LitBool False)) (Var "x"))) T.Bool
    ]

test_lambda_expression :: TestTree
test_lambda_expression = testGroup "Lambda Inference"
    [ testCase "Infer identity function type" $
        assertInfersType "identity" (Lambda "x" Nothing (Var "x")) (T.Arrow (T.Var "v1") (T.Var "v1"))
    , testCase "Infers correct type of arrow variable forced from body" $
        assertInfersType "arrow from body" (Lambda "x" Nothing (BinOp Add (Var "x") (Lit $ LitInt 2))) (T.Arrow T.Int T.Int)
    ]

allTests :: TestTree
allTests = testGroup "Inference Unit Tests"
    [ test_variable_inference
    , test_lambda_expression
    ]

generateConstraints :: TestTree
generateConstraints = testGroup "Simple Constraint Generation"
    [ ]
