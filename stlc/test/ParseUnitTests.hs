module ParseUnitTests (unitTest) where

import Test.HUnit
import qualified Text.Parsec as P
import Parser
import FullPrograms(full_programs)
import Utils

-- Tests for basic parsers
test_semicolon :: Test
test_semicolon = TestList
    [ TestCase $ assertParseSuccess "semicolon parses ';'" semicolon ";" ()
    , TestCase $ assertParseFailure "semicolon fails on 'a'" semicolon "a"
    , TestCase $ assertParseFailure "semicolon fails on ':'" semicolon ":"
    ]

test_keyword :: Test
test_keyword = TestList
    [ TestCase $ assertParseSuccess "keyword parses 'let'" (keyword "let") "let" ()
    , TestCase $ assertParseSuccess "keyword parses 'if'" (keyword "if") "if" ()
    , TestCase $ assertParseFailure "keyword fails on wrong word" (keyword "let") "if"
    ]

test_arrow :: Test
test_arrow = TestList
    [ TestCase $ assertParseSuccess "arrow parses '->'" arrow "->" ()
    , TestCase $ assertParseFailure "arrow fails on '-'" arrow "-"
    , TestCase $ assertParseFailure "arrow fails on '>'" arrow ">"
    , TestCase $ assertParseFailure "arrow fails on '=>'" arrow "=>"
    ]

test_identifier :: Test
test_identifier = TestList
    [ TestCase $ assertParseSuccess "identifier parses 'x'" identifier "x" "x"
    , TestCase $ assertParseSuccess "identifier parses 'a1'" identifier "a1" "a1"
    , TestCase $ assertParseSuccess "identifier parses 'x_'" identifier "x_" "x_"
    , TestCase $ assertParseFailure "identifier fails on '1x'" identifier "1x"
    , TestCase $ assertParseFailure "identifier fails on '_x'" identifier "_x"
    ]

-- Tests for literal parsers
test_literal_int :: Test
test_literal_int = TestList
    [ TestCase $ assertParseSuccess "literal_int parses '0'" literal_int "0" (LitInt 0)
    , TestCase $ assertParseSuccess "literal_int parses '42'" literal_int "42" (LitInt 42)
    , TestCase $ assertParseSuccess "literal_int parses '123'" literal_int "123" (LitInt 123)
    , TestCase $ assertParseSuccess "literal_int parses '999'" literal_int "999" (LitInt 999)
    , TestCase $ assertParseFailure "literal_int fails on 'abc'" literal_int "abc"
    ]

test_literal_bool :: Test
test_literal_bool = TestList
    [ TestCase $ assertParseSuccess "literal_bool parses 'true'" literal_bool "true" (LitBool True)
    , TestCase $ assertParseSuccess "literal_bool parses 'false'" literal_bool "false" (LitBool False)
    , TestCase $ assertParseFailure "literal_bool fails on 'True'" literal_bool "True"
    , TestCase $ assertParseFailure "literal_bool fails on 'FALSE'" literal_bool "FALSE"
    , TestCase $ assertParseFailure "literal_bool fails on 't'" literal_bool "t"
    ]

test_literal :: Test
test_literal = TestList
    [ TestCase $ assertParseSuccess "literal parses bool true" literal "true" (Lit (LitBool True))
    , TestCase $ assertParseSuccess "literal parses bool false" literal "false" (Lit (LitBool False))
    , TestCase $ assertParseSuccess "literal parses int 0" literal "0" (Lit (LitInt 0))
    , TestCase $ assertParseSuccess "literal parses int 42" literal "42" (Lit (LitInt 42))
    ]

-- Tests for variable parser
test_variable :: Test
test_variable = TestList
    [ TestCase $ assertParseSuccess "variable parses 'x'" variable "x" (Var "x")
    , TestCase $ assertParseSuccess "variable parses 'y1'" variable "y1" (Var "y1")
    , TestCase $ assertParseSuccess "variable parses 'z_'" variable "z_" (Var "z_")
    , TestCase $ assertParseFailure "variable fails on '1x'" variable "1x"
    ]

-- Tests for expression parser
test_parse_expr :: Test
test_parse_expr = TestList
    [ TestCase $ assertParseSuccess "parse_expr parses literal true" parse_expr "true" (Lit (LitBool True))
    , TestCase $ assertParseSuccess "parse_expr parses literal false" parse_expr "false" (Lit (LitBool False))
    , TestCase $ assertParseSuccess "parse_expr parses literal int 42" parse_expr "42" (Lit (LitInt 42))
    ]

test_parse_lambda :: Test
test_parse_lambda = TestList
    [ TestCase $ assertParseSuccess "parse_lambda parses \\x -> x" parse_lambda "\\x -> x" (Lambda "x" Nothing (Var "x"))
    ]

test_parse_let :: Test
test_parse_let = TestList
    [ TestCase $ assertParseSuccess "parse_let parses let x = 1 in x" parse_let "let x = 1 in x" (Let "x" (Lit (LitInt 1)) (Var "x"))
    , TestCase $ assertParseSuccess "parse_let parses let x = 1 in 1" parse_let "let x = 1 in x" (Let "x" (Lit (LitInt 1)) (Var "x"))
    ]

test_parse_binary_expr :: Test
test_parse_binary_expr = TestList
    [ TestCase $ assertParseSuccess "parse_binary_expr parses 5 + 5" parse_binary_expr "5 + 5" (BinOp Add (Lit (LitInt 5)) (Lit (LitInt 5)) )
    , TestCase $ assertParseSuccess "parse_binary_expr parses (5 - 2) + (3 - 2)" parse_binary_expr "(5 - 2) + (3 - 2)" (BinOp Add (BinOp Subtract (Lit (LitInt 5)) (Lit (LitInt 2)) ) (BinOp Subtract (Lit (LitInt 3)) (Lit (LitInt 2))))
    , TestCase $ assertParseSuccess "parse_binary_expr parses true && true" parse_binary_expr "true && true" (BinOp And (Lit (LitBool True)) (Lit (LitBool True)) )
    , TestCase $ assertParseSuccess "parse_binary_expr parses 5 + 5 + 5" parse_binary_expr "5 + 5 + 5" (BinOp Add (BinOp Add (Lit (LitInt 5)) (Lit (LitInt 5)) ) (Lit (LitInt 5)))
    ]

test_parse_if_expr :: Test
test_parse_if_expr = TestList
    [ TestCase $ assertParseSuccess "parse_if parses `if True then False else True`" parse_if "if true then false else true" (If (Lit (LitBool True)) (Lit (LitBool False)) (Lit (LitBool True)))
    ]

test_parse_application :: Test
test_parse_application = TestList
    [ TestCase $ assertParseSuccess "parse_application parses `f a`" parse_application "f a" (App (Var "f") (Var "a"))
    , TestCase $ assertParseSuccess "parse_application parses `(\\x -> x) 5`" parse_application "(\\x -> x) 5" (App (Lambda "x" Nothing (Var "x")) (Lit (LitInt 5)))
    ]

-- Combine all tests
allTests :: Test
allTests = TestList
    [ TestLabel "Semicolon tests" test_semicolon
    , TestLabel "Keyword tests" test_keyword
    , TestLabel "Arrow tests" test_arrow
    , TestLabel "Identifier tests" test_identifier
    , TestLabel "Literal int tests" test_literal_int
    , TestLabel "Literal bool tests" test_literal_bool
    , TestLabel "Literal tests" test_literal
    , TestLabel "Variable tests" test_variable
    , TestLabel "Expression tests" test_parse_expr
    , TestLabel "Lambda tests" test_parse_lambda
    , TestLabel "Let tests" test_parse_let
    , TestLabel "Binary Exp tests" test_parse_binary_expr
    , TestLabel "If Exp tests" test_parse_if_expr
    , TestLabel "Application tests" test_parse_application
    , TestLabel "Full Program Tests" test_full_programs
    ]

-- Main entry point for unit tests
unitTest :: IO Counts
unitTest = do
    putStrLn "\n --- Running Unit Tests ---"
    runTestTT allTests

test_full_programs :: Test
test_full_programs = TestList
    [ TestCase $ assertParses description parse_program program_source | (description, program_source) <- full_programs
    ]

