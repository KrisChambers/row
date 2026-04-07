module Main (main) where

import ConstraintSolveSpec (constraintSolveTests)
import EffectTests (effectTests)
import ExpressionTypeTests (expressionTypeTests)
import InferenceSpec (inferenceTests)
import InterpreterTests (interpreterTests)
import ParseTest (parseTests)
import Test.Tasty
import TestRunner (runFileTests)

main :: IO ()
main = do
  fileTests <- runFileTests
  defaultMain $
    testGroup
      "All Tests"
      [ parseTests
      , fileTests
      , inferenceTests
      , constraintSolveTests
      , expressionTypeTests
      , effectTests
      , interpreterTests
      ]
