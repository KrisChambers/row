module ParseTest (parseTests) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (isInfixOf)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Inference
import Type.Inference qualified as T
import Text.Parsec (parse)

parseTests :: TestTree
parseTests =
  testGroup
    "Basic Parsing"
    [ recordTests
    ]

-- doInfer :: TypeEnv -> Expr -> Either TypeError (Type, [Constraint])
-- doInfer env expr = runInfer (infer env expr) 0 0

recordTests :: TestTree
recordTests =
  testGroup
    "Record Parsing"
    [ testCase "Simple Record construction" $ do
        let input = "let p = { x = 0 } in p"
        case parse P.parse_expr "" input of
          Left err -> assertFailure $ show err
          Right e -> do
            e @?= P.Let "p" (P.Record (P.RecordCstr [("x", P.Lit $ P.LitInt 0)])) (P.Var "p")
    ]
