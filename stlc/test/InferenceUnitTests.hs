module InferenceUnitTests (unitTestInference) where

import Test.HUnit
import Type.Inference
import FullPrograms (full_programs)


allTests :: Test
allTests = TestList []

test_full_programs :: Test
test_full_programs = TestList
    [
    ]

unitTestInference :: IO Counts
unitTestInference = do
    putStrLn "\n --- Running Unit Tests ---"
    runTestTT allTests
