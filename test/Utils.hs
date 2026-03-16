module Utils (
    assertParseSuccess,
    assertParses,
    assertParseFailure
    ) where

import Parser
import Test.Tasty.HUnit
import Text.Parsec


-- Helper function to test successful parsing
assertParseSuccess :: (Eq a, Show a) => Parser a -> String -> a -> Assertion
assertParseSuccess parser input expected =
    case parse parser "" input of
        Left err -> assertFailure $ "Parse failed with error: " ++ show err
        Right result -> assertEqual "" expected result

assertParses :: (Eq a, Show a) => Parser a -> String -> Assertion
assertParses parser input =
    case parse parser "" input of
        Left err -> assertFailure $ "Parse failed with error: " ++ show err
        Right _ -> return ()

-- Helper function to test parse failure
assertParseFailure :: (Show a) => Parser a -> String -> Assertion
assertParseFailure parser input =
    case parse parser "" input of
        Left _ -> return ()
        Right result -> assertFailure $ "Expected parse to fail, but got: " ++ show result
