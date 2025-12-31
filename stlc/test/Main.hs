module Main (main) where

import Test.Tasty
import TestRunner (runFileTests)
import InferenceSpec (inferenceTests)

main :: IO ()
main = do
    fileTests <- runFileTests
    defaultMain $ testGroup "All Tests"
        [ fileTests
        , inferenceTests
        ]
