module ParseTest (parseTests) where

import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit
import Text.Parsec (parse)

parseTests :: TestTree
parseTests =
  testGroup
    "Basic Parsing"
    [ recordTests
--  ,   declTests
    ]


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

-- declTests :: TestTree
-- declTests = testGroup "Declaration Parsing"
--   [ testCase "Simple Let declaration" $ do
--       let input = "let p = 1 in p"
--       case parse P.decls "" input of
--         Left err -> assertFailure $ show err
--         Right [] -> assertFailure $ show "OOPS"
--         Right (e:es) -> do
--           e @?= P.LetDecl "p" Nothing (P.Lit (P.LitInt 1))
--     ]

