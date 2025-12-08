module InterpreterUnitTests () where

import Test.HUnit
import qualified Text.Parsec as P
import Parser
-- import FullPrograms(full_programs)
import Utils

import Interpreter

test_literal :: Test
test_literal = TestList
    [ TestCase $ assert

allTests :: Test
    [ TestLabel "Literal tests" test_literal
    ]
