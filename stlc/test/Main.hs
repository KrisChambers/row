module Main (main) where

import InferenceProperties (test_inference_properties)
import ParseProperties (test_parser_properties)
import ParseUnitTests (unitTest)
import InferenceUnitTests (unitTestInference)
import TestRunner (runFileTests)

import Test.HUnit (Counts(..), errors, failures)
import System.Exit (exitFailure, exitSuccess)



main :: IO ()
main = do
    putStrLn "\n --- Running Unit Tests ---"
    _ <- unitTest

    putStrLn "\n --- Running program Tests ---"
    -- Run file-based tests
    _ <- runFileTests

    return ()




