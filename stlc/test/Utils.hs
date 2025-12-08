module Utils (
    assertParseSuccess,
    assertParses,
    assertParseFailure
    ) where

import Control.Monad.State
import Interpreter
import Parser
import Type.Inference
import Test.HUnit
import Text.Parsec
import Type.Inference


-- Helper function to test successful parsing
assertParseSuccess :: (Eq a, Show a) => String -> Parser a -> String -> a -> Assertion
assertParseSuccess testName parser input expected =
    case parse parser "" input of
        Left err -> assertFailure $ ">> " ++ testName ++ ": Parse failed with error: " ++ show err
        Right result -> assertEqual testName expected result

assertParses :: (Eq a, Show a) => String -> Parser a -> String -> Assertion
assertParses testName parser input =
    case parse parser "" input of
        Left err -> assertFailure $ ">> " ++ testName ++ ": Parse failed with error: " ++ show err
        Right _ -> return ()

-- Helper function to test parse failure
assertParseFailure :: (Show a) => String -> Parser a -> String -> Assertion
assertParseFailure testName parser input =
    case parse parser "" input of
        Left _ -> return ()
        Right result -> assertFailure $ testName ++ ": Expected parse to fail, but got: " ++ show result

-- Helper function to test successful parsing
assertValueEq :: (Eq a, Show a) => String -> Expr -> Value -> Assertion
assertValueEq testName expr expected =
    case eval_expr expr of
        Left err -> assertFailure $ ">> " ++ testName ++ ": Parse failed with error: " ++ show err
        Right result -> assertEqual testName expected result


-- assertInfersType :: (Eq a, Show a) => String -> Infer a -> String -> a
-- assertInfersType testName parser input expected =
--     case result of
--         _ -> 0
--     where
--         result = w env expr
--         env = emptyEnv

