module Main (main) where

import Test.Tasty
import TestRunner (runFileTests)
import InferenceSpec (inferenceTests)
import ConstraintSolveSpec (constraintSolveTests)
import ExpressionTypeTests (expressionTypeTests)

main :: IO ()
main = do
    fileTests <- runFileTests
    defaultMain $ testGroup "All Tests"
        [ fileTests
        , inferenceTests
        , constraintSolveTests
        , expressionTypeTests
        ]
