module ParseProperties (test_parser_properties) where

import Test.QuickCheck
import Parser
import qualified Text.Parsec as P

genIdentifier :: Gen String
genIdentifier = arbitrary  :: Gen String

genIntLiteralString :: Gen String
genIntLiteralString = do
    n <- arbitrary :: Gen Integer
    return $ show $ abs n

genBoolLiteralString :: Gen String
genBoolLiteralString = elements ["true", "false"]

genLiteralString :: Gen String
genLiteralString = oneof [genIntLiteralString, genBoolLiteralString]

--- Helper to convert a literal to it's string representation
literalToString :: Literal -> String
literalToString (LitInt n) = show n
literalToString (LitBool True) = "true"
literalToString (LitBool False) = "false"

instance Arbitrary Literal where
    arbitrary = oneof
        [ LitInt . abs <$> arbitrary
        , LitBool <$> arbitrary
        ]

--- Property: parsing should succeed for valid literals
prop_literal_parses_valid_input :: Property
prop_literal_parses_valid_input = forAll genLiteralString $ \input ->
    case P.parse literal "" input of
        Left _ -> counterexample ("Failed to parse: " ++ input) False
        Right _ -> property False



--- Property: Parsing . pretty-printing == id
prop_literal_roundtrip :: Literal -> Bool
prop_literal_roundtrip lit =
    let input = literalToString lit
        result = P.parse literal "" input
    in case result of
        Left _ -> False
        Right (Lit parsed) -> parsed == lit
        Right _ -> False

-- Property: Integer literals parse to correct values
prop_int_literal_has_correct_value :: Property
prop_int_literal_has_correct_value = forAll (arbitrary :: Gen Integer) $ \n ->
    let input = show (abs n)
        result = P.parse literal_int "" input
    in case result of
        Left err -> counterexample ("Parse error: " ++ show err) False
        Right (LitInt parsed) -> property $ parsed == abs n
        Right other -> counterexample ("Wrong literal type: " ++ show other) False

-- Property: boolean literals parse as correct values
prop_bool_literal_correct_value :: Bool -> Bool
prop_bool_literal_correct_value b =
    let input = if b then "true" else "false"
        result = P.parse literal_bool "" input
    in case result of
        Right (LitBool parsed) -> parsed == b
        _ -> False

--- Property: Invalid inputs should fail to parse
prop_invalid_literals_fail :: Property
prop_invalid_literals_fail = forAll genInvalidLiteral $ \input ->
    case P.parse literal "" input of
        Left _ -> property True
        Right _ -> counterexample ("Expected to fail when parsing: " ++ input) False
    where
        genInvalidLiteral = elements
            [   "True"
            ,   "False"
            ,   "TRUE"
            ,   "fals"
            ,   "123abc"
            ,   "-123"
            ,   "1.5"
            ,   ""
            ]

prop_leading_zeros_are_handled :: Property
prop_leading_zeros_are_handled = forAll(choose (0, 999) :: Gen Integer) $ \n ->
    let input = "0" ++ show n
        result = P.parse literal_int "" input
    in case result of
        Left _ -> counterexample "Failed to parse with leading zero" False
        Right _ -> property True


test_parser_properties :: IO()
test_parser_properties = do
    putStrLn "\nTesting literal parsing..."

    putStrLn "\nTesting valid inputs..."
    quickCheck prop_literal_parses_valid_input

    putStrLn "\nTesting invalid literals fail..."
    quickCheck prop_invalid_literals_fail

    putStrLn "\nTest integer literals parsed correctly"
    quickCheck prop_int_literal_has_correct_value

    putStrLn "\nTesting leading zeros are handled..."
    quickCheck prop_leading_zeros_are_handled

    putStrLn ""

