module Main (main) where

import Test.Tasty

import qualified ParseUnitTests
import qualified InferenceUnitTests
import ParseProperties (test_parser_properties)
import InferenceProperties (test_inference_properties)
import TestRunner (runFileTests)

main :: IO ()
main = do
    fileTests <- runFileTests
    defaultMain $ testGroup "All Tests"
        [ testGroup "Parser"
            [ ParseUnitTests.allTests
            , test_parser_properties
            ]
        , testGroup "Type Inference"
            [ InferenceUnitTests.allTests
            , test_inference_properties
            ]
        , fileTests
        ]
