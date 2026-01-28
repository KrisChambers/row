module ExpressionTypeTests (expressionTypeTests) where

import Parser (Literal (..), RecordExpr (..))
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Type.Inference
import Type.Inference qualified as T

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
          Right (t, _e) -> do
            t @?= T.Record EmptyRow,
      testCase "Infers { x = 0, y = 0 } :: (| x : Int, y: Int |)" $ do
        let expr = P.Record (RecordCstr [("x", P.Lit (LitInt 0)), ("y", P.Lit (LitInt 0))])
        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            t @?= T.Record (Row ("y", T.tInt) (Row ("x", T.tInt) EmptyRow)),
      testCase "Infers { x = 0 }.x as Int" $ do
        let r = P.Record (RecordCstr [("x", P.Lit (LitInt 0)), ("y", P.Lit (LitInt 0))])
        let expr = P.Record (RecordAccess r "x")

        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            t @?= T.tInt,
      testCase "Infers proper arrow type for \\r -> r.name" $ do
        let expr = P.Lambda "r" Nothing (P.Record (RecordAccess (P.Var "r") "name"))

        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            -- expr : { name : a | r } -> a ! eff
            case t of
              T.Arrow (T.Record (T.Row ("name", T.Var _) (T.Var _))) _eff (T.Var _) -> return ()
              _ -> assertFailure $ "Expected Arrow { name : a | r } -> a, got: " ++ show t,
      testCase "Infers correct type of extension { orgin2d with z = 0 } where origin2d = { x = 0, y = 0}" $ do
        let expr = P.Let "origin2d" (P.Record (P.RecordCstr [("x", P.Lit $ LitInt 0), ("y", P.Lit $ LitInt 0)])) (P.Record (P.RecordExtension (P.Var "origin2d") "z" (P.Lit (LitInt 0))))
        let expected_t = T.Record (Row ("z", T.tInt) (T.Row ("y", T.tInt) (T.Row ("x", T.tInt) EmptyRow)))

        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            t @?= expected_t

    ]
