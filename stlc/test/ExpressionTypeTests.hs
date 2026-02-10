module ExpressionTypeTests (expressionTypeTests) where

import Parser (Literal (..), RecordExpr (..))
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Type.Inference
import Type.Inference qualified as T
import Data.Map ((!?))
import Data.Set qualified as Set

expressionTypeTests :: TestTree
expressionTypeTests =
  testGroup
    "Infering Types of Expressions"
    [ recordTests
    -- , effectTests
    , effectDeclTest
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

effectDeclTest :: TestTree
effectDeclTest =
  let
    eState = P.EffectDecl "State a" ["a"] [
        ("get", P.TFun (P.TCon "()" []) (P.TCon "a" []) P.EEmptyRow),
        ("set", P.TFun (P.TCon "a" []) (P.TCon "()" []) P.EEmptyRow)
      ]
    eConsole = P.EffectDecl "Console" [] [
      ("print", P.TFun (P.TCon "String" []) (P.TCon "()" []) P.EEmptyRow)
      ]

  in testGroup
    "Effect declarations in Infered Types"
    [ testCase "Infers that foo has the Console effect" $ do
        let decl = P.LetDecl  "foo" Nothing (P.Lambda "x" Nothing (
              P.Perform "Console" "print" $ P.Lit $ P.LitString "Hello, Foo"
              ))

        let expected = T.Arrow
                  (T.Var "v2")
                  (T.Row ("Console", tUnit) T.EmptyRow)
                  tUnit

        env <- either (assertFailure . show) return $ inferDecl [ eState, eConsole, decl ]

        case envVars env !? "foo" of
          Nothing -> assertFailure "Failed"
          Just (Forall _ expr) -> do
            expr @?= expected
    ]

effectTests :: TestTree
effectTests =
  testGroup
    "Effect Row inference"
    [ testCase "Infers that foo has effect Console" $ do
        let expr = P.Let "foo" (
                P.Perform "Console" "print" $ P.Lit $ P.LitString "Hello, World"
              ) (P.Var "foo")
        case inferType expr of
          Left err -> assertFailure $ show err
          Right (_t, e) -> do
            e @?= Row ("Console", T.tUnit) EmptyRow,
      testCase "Function performing effect has Console effect in arrow type" $ do
        -- let greet = \name -> perform Console.print name in greet
        let expr = P.Let "greet"
              (P.Lambda "name" Nothing (P.Perform "Console" "print" (P.Var "name")))
              (P.Var "greet")
        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            -- Type should be: String -> () ! Console
            case t of
              Arrow argT (Row ("Console", _) _) retT -> do
                argT @?= tString
                retT @?= tUnit
              _ -> assertFailure $ "Expected Arrow String -> () ! Console, got: " ++ show t,
      testCase "Effectful function returns unit type" $ do
        -- \_ -> perform Console.print "hello"
        let expr = P.Lambda "x" Nothing (P.Perform "Console" "print" (P.Lit $ LitString "hello"))
        case inferType expr of
          Left err -> assertFailure $ show err
          Right (t, _e) -> do
            case t of
              Arrow _argT effect retT -> do
                retT @?= tUnit
                effect @?= Row ("Console", T.tUnit) EmptyRow
              _ -> assertFailure $ "Expected Arrow type, got: " ++ show t
    ]
