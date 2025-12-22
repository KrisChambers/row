module InferenceUnitTests (unitTestInference) where

import Test.HUnit
import Type.Inference (Type)
import Type.Inference qualified as T (Type(..), infer_type)
import Parser (Expr(..), Literal(..), Op(..))

-- Helper to assert type inference succeeds with expected type
assertInfersType :: String -> Expr -> Type -> Assertion
assertInfersType testName expr expected =
    case T.infer_type expr of
                Left err -> assertFailure $ testName ++ ": Inference failed with error: " ++ show err
                Right result -> assertEqual testName expected result

-- Helper to assert type inference fails
assertInferenceError :: String -> Expr -> Assertion
assertInferenceError testName expr =
    case T.infer_type expr of
            Left _ -> return ()
            Right t -> assertFailure $ testName ++ ": Expected inference to fail, but got: " ++ show t

-- Tests for variable type inference
test_variable_inference :: Test
test_variable_inference = TestList
    [ TestCase $ assertInferenceError
        "undefined variable gives error"
       (Var "undefined_var")
    , TestCase $ assertInfersType
        "let-bound Int variable has type Int"
        (Let "x" (Lit (LitInt 42)) (Var "x"))
        T.Int
    , TestCase $ assertInfersType
        "let-bound Bool variable has type Bool"
        (Let "b" (Lit (LitBool True)) (Var "b"))
        T.Bool
    , TestCase $ assertInfersType
        "nested let shadows outer variable"
        (Let "x" (Lit (LitInt 1)) (Let "x" (Lit (LitBool False)) (Var "x")))
        T.Bool
    ]

test_lambda_expression :: Test
test_lambda_expression = TestList
    [ TestCase $ assertInfersType
        "Infer identity function type"
        (Lambda "x" Nothing (Var "x"))
        (T.Arrow (T.Var "v1") (T.Var "v1"))
    , TestCase $ assertInfersType
        "Infers correct type of arrow variable forced from body"
        (Lambda "x" Nothing (BinOp Add (Var "x") (Lit $ LitInt 2)))
        (T.Arrow T.Int T.Int)
    ]



allTests :: Test
allTests = TestList
    [ TestLabel "Variable inference tests" test_variable_inference
    , TestLabel "Lambda inference tests" test_lambda_expression
    ]

unitTestInference :: IO Counts
unitTestInference = do
    putStrLn "\n --- Running Inference Unit Tests ---"
    runTestTT allTests
