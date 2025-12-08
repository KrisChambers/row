module Main (main) where

import InferenceProperties (test_inference_properties)
import ParseProperties (test_parser_properties)
import ParseUnitTests (unitTest)

import Test.HUnit (Counts(..), errors, failures)
import System.Exit (exitFailure, exitSuccess)



main :: IO ()
main = do
    -- Run property-based tests
    test_parser_properties

    test_inference_properties

    -- Run unit tests
    counts <- unitTest

    return ()

    -- Report results and exit with appropriate code
    --putStrLn $ "\n=== Test Summary ==="
    --putStrLn $ "Cases: " ++ show (cases counts)
    --putStrLn $ "Tried: " ++ show (tried counts)
    --putStrLn $ "Errors: " ++ show (errors counts)
    --putStrLn $ "Failures: " ++ show (failures counts)

    --if errors counts + failures counts == 0
    --    then do
    --        putStrLn "\nAll tests passed!"
    --        exitSuccess
    --    else do
    --        putStrLn "\nSome tests failed!"
    --        exitFailure





