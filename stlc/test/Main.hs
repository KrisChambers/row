module Main (main) where

import Test.Tasty
import TestRunner (runFileTests)
import InferenceSpec (inferenceTests)
import ConstraintSolveSpec (constraintSolveTests)
import ExpressionTypeTests (expressionTypeTests)
import ParseTest (parseTests)

main :: IO ()
main = do
    fileTests <- runFileTests
    defaultMain $ testGroup "All Tests"
        [ parseTests
        , fileTests
        , inferenceTests
        , constraintSolveTests
        , expressionTypeTests
        ]
