module ExpressionTypeTests (expressionTypeTests) where

import Data.List (isInfixOf)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Parser (Expr (..), Literal (..), Op (..), RecordExpr (..))
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Inference
import Type.Inference qualified as T
import Control.Monad.Except
import Control.Monad.State

expressionTypeTests :: TestTree
expressionTypeTests =
  testGroup
    "Infering Types of Expressions"
    [ recordTests
    ]

recordTests :: TestTree
recordTests =
  testGroup
    "Record Construction"
    [ testCase "Infers the empty record" $ do
        let expr = P.Record (RecordCstr [])
        case inferType expr of
          Left err -> assertFailure $ show err
          Right t -> do
            t @?= T.Record EmptyRow
    , testCase "Infers { x = 0, y = 0 } :: (| x : Int, y: Int |)" $ do
      let expr = P.Record (RecordCstr [("x", P.Lit (LitInt 0)), ("y", P.Lit (LitInt 0) )])
      case inferType expr of
        Left err -> assertFailure $ show err
        Right t -> do
          t @?= T.Record (Row "y" T.Int (Row "x" T.Int EmptyRow))
    , testCase "Infers { x = 0 }.x as Int" $ do
      let r = P.Record (RecordCstr [("x", P.Lit (LitInt 0)), ("y", P.Lit (LitInt 0) )])
      let expr = P.Record (RecordAccess r "x")

      case inferType expr of
        Left err -> assertFailure $ show err
        Right t -> do
          t @?= T.Int

    , testCase "Infers row type in \r -> r.name" $ do
      let expr = P.Lambda "r" Nothing (P.Record (RecordAccess (P.Var "r") "name" ))

      case inferType expr of
        Left err -> assertFailure $ show err
        Right t -> do
          t @?= T.Int
    ]
