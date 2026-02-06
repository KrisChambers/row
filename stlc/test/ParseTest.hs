module ParseTest (parseTests) where

import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Text.Parsec (parse)

parseTests :: TestTree
parseTests =
  testGroup
    "Basic Parsing"
    [ recordTests,
      typeTests,
      effectDeclarationTests,
      letDeclarationTests
    ]

test :: (Eq a, Show a) => P.Parser a -> String -> a -> Assertion
test parser input expected = do
  case parse parser "" input of
    Left err -> assertFailure $ show err
    Right e -> do
      e @?= expected

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


typeTests :: TestTree
typeTests =
  testGroup
    "Parsing Annotated Types"
    [ testCase "Simple type variable" $ do
        testInput
          "a"
          $ P.TVar "a",
      testCase "Simple type constructor, Int" $ do
        testInput
          "Int"
          $ P.TCon "Int" [],
      testCase "Simple Function Type" $ do
        testInput
          "Int -> Int"
          $ P.TFun (P.TCon "Int" []) (P.TCon "Int" []) P.EEmptyRow,
      testCase "Closed Record Types: Empty Record" $ do
        testInput
          "{ }"
        $ P.TRecord P.REmptyRow,
      testCase "Closed Record Types: Single entry" $ do
        testInput
          "{ foo : Int }"
        $ P.TRecord $ P.RRowExtension "foo" (P.TCon "Int" []) P.REmptyRow,
      testCase "Closed Record Types: Multi entry" $ do
        testInput
          "{ foo : Int, bar: String }"
        $ P.TRecord $ P.RRowExtension "bar" (P.TCon "String" []) (P.RRowExtension "foo" (P.TCon "Int" []) P.REmptyRow)
        -- TODO (KC): need to handle open effect types
    ]
  where
    testInput = test P.typ

effectDeclarationTests :: TestTree
effectDeclarationTests =
  testGroup
    "Parsing effect Declarations"
    [ testCase "Simple Declaration" $ do
        let input = "effect Test { test : () -> String }"
        let expected = P.EffectDecl "Test" [] [("test", P.TFun (P.TCon "()" []) (P.TCon "String" []) P.EEmptyRow)]
        case parse P.effect_declaration "" input of
          Left err -> assertFailure $ show err
          Right e -> do
            e @?= expected,
      testCase "Effect with type Param" $ do
        let input = "effect Test a { test : () -> a }"
        let expected = P.EffectDecl "Test" ["a"] [("test", P.TFun (P.TCon "()" []) (P.TVar "a") P.EEmptyRow)]
        case parse P.effect_declaration "" input of
          Left err -> assertFailure $ show err
          Right e -> do
            e @?= expected,
      testCase "Effect with multiple ops" $ do
        let input = "effect Test a b { test : () -> a, fix : b -> () }"
        let expected =
              P.EffectDecl
                "Test"
                ["a", "b"]
                [ ("test", P.TFun (P.TCon "()" []) (P.TVar "a") P.EEmptyRow),
                  ("fix", P.TFun (P.TVar "b") (P.TCon "()" []) P.EEmptyRow)
                ]
        case parse P.effect_declaration "" input of
          Left err -> assertFailure $ show err
          Right e -> do
            e @?= expected
    ]

letDeclarationTests :: TestTree
letDeclarationTests =
  testGroup
    "Parsing Let Declarations"
    [ testCase "Simple let assignment for id function" $ do
        testInput
          "let id = \\x -> x"
          $ P.LetDecl "id" Nothing (P.Lambda "x" Nothing (P.Var "x")),
      testCase "Simple constant assignment" $ do
        testInput
          "let c = 1"
          $ P.LetDecl "c" Nothing (P.Lit $ P.LitInt 1)
    , testCase "Record Creation" $ do
        testInput
          "let person = { age = 1 }"
          $ P.LetDecl "person" Nothing (P.Record $ P.RecordCstr [("age", P.Lit $ P.LitInt 1 )])
    , testCase "Record Access" $ do
        testInput
          "let getAge = \\x -> x.age"
          $ P.LetDecl "getAge" Nothing (P.Lambda "x" Nothing (P.Record $ P.RecordAccess (P.Var "x") "age"))
    ]
  where
    testInput = test P.let_declaration
