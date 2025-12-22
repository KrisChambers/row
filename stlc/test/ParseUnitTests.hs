module ParseUnitTests (allTests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Text.Parsec as P
import Parser
import FullPrograms(full_programs)
import Utils

-- Tests for basic parsers
test_semicolon :: TestTree
test_semicolon = testGroup "Semicolon"
    [ testCase "parses ';'" $ assertParseSuccess semicolon ";" ()
    , testCase "fails on 'a'" $ assertParseFailure semicolon "a"
    , testCase "fails on ':'" $ assertParseFailure semicolon ":"
    ]

test_keyword :: TestTree
test_keyword = testGroup "Keyword"
    [ testCase "parses 'let'" $ assertParseSuccess (keyword "let") "let" ()
    , testCase "parses 'if'" $ assertParseSuccess (keyword "if") "if" ()
    , testCase "fails on wrong word" $ assertParseFailure (keyword "let") "if"
    ]

test_arrow :: TestTree
test_arrow = testGroup "Arrow"
    [ testCase "parses '->'" $ assertParseSuccess arrow "->" ()
    , testCase "fails on '-'" $ assertParseFailure arrow "-"
    , testCase "fails on '>'" $ assertParseFailure arrow ">"
    , testCase "fails on '=>'" $ assertParseFailure arrow "=>"
    ]

test_identifier :: TestTree
test_identifier = testGroup "Identifier"
    [ testCase "parses 'x'" $ assertParseSuccess identifier "x" "x"
    , testCase "parses 'a1'" $ assertParseSuccess identifier "a1" "a1"
    , testCase "parses 'x_'" $ assertParseSuccess identifier "x_" "x_"
    , testCase "fails on '1x'" $ assertParseFailure identifier "1x"
    , testCase "fails on '_x'" $ assertParseFailure identifier "_x"
    ]

-- Tests for literal parsers
test_literal_int :: TestTree
test_literal_int = testGroup "Literal Int"
    [ testCase "parses '0'" $ assertParseSuccess literal_int "0" (LitInt 0)
    , testCase "parses '42'" $ assertParseSuccess literal_int "42" (LitInt 42)
    , testCase "parses '123'" $ assertParseSuccess literal_int "123" (LitInt 123)
    , testCase "parses '999'" $ assertParseSuccess literal_int "999" (LitInt 999)
    , testCase "fails on 'abc'" $ assertParseFailure literal_int "abc"
    ]

test_literal_bool :: TestTree
test_literal_bool = testGroup "Literal Bool"
    [ testCase "parses 'true'" $ assertParseSuccess literal_bool "true" (LitBool True)
    , testCase "parses 'false'" $ assertParseSuccess literal_bool "false" (LitBool False)
    , testCase "fails on 'True'" $ assertParseFailure literal_bool "True"
    , testCase "fails on 'FALSE'" $ assertParseFailure literal_bool "FALSE"
    , testCase "fails on 't'" $ assertParseFailure literal_bool "t"
    ]

test_literal :: TestTree
test_literal = testGroup "Literal"
    [ testCase "parses bool true" $ assertParseSuccess literal "true" (Lit (LitBool True))
    , testCase "parses bool false" $ assertParseSuccess literal "false" (Lit (LitBool False))
    , testCase "parses int 0" $ assertParseSuccess literal "0" (Lit (LitInt 0))
    , testCase "parses int 42" $ assertParseSuccess literal "42" (Lit (LitInt 42))
    ]

-- Tests for variable parser
test_variable :: TestTree
test_variable = testGroup "Variable"
    [ testCase "parses 'x'" $ assertParseSuccess variable "x" (Var "x")
    , testCase "parses 'y1'" $ assertParseSuccess variable "y1" (Var "y1")
    , testCase "parses 'z_'" $ assertParseSuccess variable "z_" (Var "z_")
    , testCase "fails on '1x'" $ assertParseFailure variable "1x"
    ]

-- Tests for expression parser
test_parse_expr :: TestTree
test_parse_expr = testGroup "Expression"
    [ testCase "parses literal true" $ assertParseSuccess parse_expr "true" (Lit (LitBool True))
    , testCase "parses literal false" $ assertParseSuccess parse_expr "false" (Lit (LitBool False))
    , testCase "parses literal int 42" $ assertParseSuccess parse_expr "42" (Lit (LitInt 42))
    ]

test_parse_lambda :: TestTree
test_parse_lambda = testGroup "Lambda"
    [ testCase "parses \\x -> x" $ assertParseSuccess parse_lambda "\\x -> x" (Lambda "x" Nothing (Var "x"))
    , testCase "parses nested lambdas" $ assertParseSuccess parse_lambda "\\x -> \\y -> \\z -> x" (
            Lambda "x" Nothing (Lambda "y" Nothing (Lambda "z" Nothing (Var "x")))
        )
    ]

test_parse_let :: TestTree
test_parse_let = testGroup "Let"
    [ testCase "parses let x = 1 in x" $ assertParseSuccess parse_let "let x = 1 in x" (Let "x" (Lit (LitInt 1)) (Var "x"))
    , testCase "parses let binding" $ assertParseSuccess parse_let "let x = 1 in x" (Let "x" (Lit (LitInt 1)) (Var "x"))
    ]

test_parse_binary_expr :: TestTree
test_parse_binary_expr = testGroup "Binary Expression"
    [ testCase "parses 5 + 5" $ assertParseSuccess parse_binary_expr "5 + 5" (BinOp Add (Lit (LitInt 5)) (Lit (LitInt 5)))
    , testCase "parses (5 - 2) + (3 - 2)" $ assertParseSuccess parse_binary_expr "(5 - 2) + (3 - 2)" (BinOp Add (BinOp Subtract (Lit (LitInt 5)) (Lit (LitInt 2))) (BinOp Subtract (Lit (LitInt 3)) (Lit (LitInt 2))))
    , testCase "parses true && true" $ assertParseSuccess parse_binary_expr "true && true" (BinOp And (Lit (LitBool True)) (Lit (LitBool True)))
    , testCase "parses 5 + 5 + 5" $ assertParseSuccess parse_binary_expr "5 + 5 + 5" (BinOp Add (BinOp Add (Lit (LitInt 5)) (Lit (LitInt 5))) (Lit (LitInt 5)))
    ]

test_parse_if_expr :: TestTree
test_parse_if_expr = testGroup "If Expression"
    [ testCase "parses if true then false else true" $ assertParseSuccess parse_if "if true then false else true" (If (Lit (LitBool True)) (Lit (LitBool False)) (Lit (LitBool True)))
    ]

test_parse_application :: TestTree
test_parse_application = testGroup "Application"
    [ testCase "parses f a" $ assertParseSuccess parse_application "f a" (App (Var "f") (Var "a"))
    , testCase "parses (\\x -> x) 5" $ assertParseSuccess parse_application "(\\x -> x) 5" (App (Lambda "x" Nothing (Var "x")) (Lit (LitInt 5)))
    ]

test_full_programs :: TestTree
test_full_programs = testGroup "Full Programs"
    [ testCase description $ assertParses parse_program program_source | (description, program_source) <- full_programs
    ]

-- Combine all tests
allTests :: TestTree
allTests = testGroup "Parser Unit Tests"
    [ test_semicolon
    , test_keyword
    , test_arrow
    , test_identifier
    , test_literal_int
    , test_literal_bool
    , test_literal
    , test_variable
    , test_parse_expr
    , test_parse_lambda
    , test_parse_let
    , test_parse_binary_expr
    , test_parse_if_expr
    , test_parse_application
    , test_full_programs
    ]
