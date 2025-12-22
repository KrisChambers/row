{-# LANGUAGE OverloadedStrings #-}

module TestSpec
    ( TestSpec(..)
    , Phase(..)
    , Expect(..)
    , loadTestSpec
    ) where

import Toml (TomlCodec, (.=))
import qualified Toml
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Data.Bifunctor (first)

data Phase = Parse | TypeCheck | Eval
    deriving (Show, Eq)

data Expect = Success | Failure
    deriving (Show, Eq)

data TestSpec = TestSpec
    { tsName          :: Text
    , tsPhase         :: Phase
    , tsExpect        :: Expect
    , tsExpectedType  :: Maybe Text
    , tsExpectedValue :: Maybe Text
    , tsErrorContains :: Maybe Text
    } deriving (Show, Eq)

phaseFromText :: Text -> Either Text Phase
phaseFromText t
    | t == "parse"     = Right Parse
    | t == "typecheck" = Right TypeCheck
    | t == "eval"      = Right Eval
    | otherwise        = Left $ "Invalid phase: " <> t

phaseToText :: Phase -> Text
phaseToText Parse     = "parse"
phaseToText TypeCheck = "typecheck"
phaseToText Eval      = "eval"

expectFromText :: Text -> Either Text Expect
expectFromText t
    | t == "success" = Right Success
    | t == "failure" = Right Failure
    | otherwise      = Left $ "Invalid expect: " <> t

expectToText :: Expect -> Text
expectToText Success = "success"
expectToText Failure = "failure"

testSpecCodec :: TomlCodec TestSpec
testSpecCodec = TestSpec
    <$> Toml.text "name" .= tsName
    <*> Toml.textBy phaseToText phaseFromText "phase" .= tsPhase
    <*> Toml.textBy expectToText expectFromText "expect" .= tsExpect
    <*> Toml.dioptional (Toml.text "expected_type") .= tsExpectedType
    <*> Toml.dioptional (Toml.text "expected_value") .= tsExpectedValue
    <*> Toml.dioptional (Toml.text "error_contains") .= tsErrorContains

loadTestSpec :: FilePath -> IO (Either String TestSpec)
loadTestSpec path = do
    content <- TIO.readFile path
    pure $ first show $ Toml.decode testSpecCodec content
