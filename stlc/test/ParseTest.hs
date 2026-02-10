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
      letDeclarationTests,
      dataDeclarationTests
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
        testInput
          "let p = { x = 0 } in p"
          $ P.Let "p" (P.Record (P.RecordCstr [("x", P.Lit $ P.LitInt 0)])) (P.Var "p")
    ]
    where
      testInput = test P.parse_expr

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
      testCase "Closed Record Types: Empty Record"
        $ do
          testInput
            "{ }"
        $ P.TRecord P.REmptyRow,
      testCase "Closed Record Types: Single entry"
        $ do
          testInput
            "{ foo : Int }"
        $ P.TRecord
        $ P.RRowExtension "foo" (P.TCon "Int" []) P.REmptyRow,
      testCase "Closed Record Types: Multi entry"
        $ do
          testInput
            "{ foo : Int, bar: String }"
        $ P.TRecord
        $ P.RRowExtension "bar" (P.TCon "String" []) (P.RRowExtension "foo" (P.TCon "Int" []) P.REmptyRow)
        -- TODO (KC): need to handle open effect types
    ]
  where
    testInput = test P.typ

effectDeclarationTests :: TestTree
effectDeclarationTests =
  testGroup
    "Parsing effect Declarations"
    [ testCase "Simple Declaration" $ do
        testInput
          "effect Test { test : () -> String }"
          $ P.EffectDecl "Test" [] [("test", P.TFun (P.TCon "()" []) (P.TCon "String" []) P.EEmptyRow)],
      testCase "Effect with type Param" $ do
        testInput
          "effect Test a { test : () -> a }"
          $ P.EffectDecl "Test" ["a"] [("test", P.TFun (P.TCon "()" []) (P.TVar "a") P.EEmptyRow)],
      testCase "Effect with multiple ops" $ do
        testInput
          "effect Test a b { test : () -> a, fix : b -> () }"
          $ P.EffectDecl
            "Test"
            ["a", "b"]
            [ ("test", P.TFun (P.TCon "()" []) (P.TVar "a") P.EEmptyRow),
              ("fix", P.TFun (P.TVar "b") (P.TCon "()" []) P.EEmptyRow)
            ]
    ]
  where
    testInput = test P.effect_declaration

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
          $ P.LetDecl "c" Nothing (P.Lit $ P.LitInt 1),
      testCase "Record Creation" $ do
        testInput
          "let person = { age = 1 }"
          $ P.LetDecl "person" Nothing (P.Record $ P.RecordCstr [("age", P.Lit $ P.LitInt 1)]),
      testCase "Record Access" $ do
        testInput
          "let getAge = \\x -> x.age"
          $ P.LetDecl "getAge" Nothing (P.Lambda "x" Nothing (P.Record $ P.RecordAccess (P.Var "x") "age"))
    ]
  where
    testInput = test P.let_declaration

-- data Stuff
--   = Stuff1 { x : Int, y: Int }
--   | Stuff2 { name: String, age : String }


dataDeclarationTests :: TestTree
dataDeclarationTests =
  testGroup
    "Parsing Data Declarations"
    [ testCase "Simple data declaration" $ do
        testInput
          "data Test = STest String"
          $ P.DataDecl "Test" [("STest", [P.TCon "String" []])],
      testCase "Multiple Constructors" $ do
        testInput
          "data Test = STest String | ITest Int"
          $ P.DataDecl "Test" [
              ("STest", [P.TCon "String" []]),
              ("ITest", [P.TCon "Int" []])
              ],
      testCase "Constructors that take CLOSED Record Types" $ do
        testInput
          "data Test = STest { x: String } | ITest { y: Int }"
          $ P.DataDecl "Test" [
              ("STest", [P.TRecord $ P.RRowExtension "x" (P.TCon "String" []) P.REmptyRow]),
              ("ITest", [P.TRecord $ P.RRowExtension "y" (P.TCon "Int" []) P.REmptyRow])
          ]
    ]
  where
    testInput = test P.data_declaration
