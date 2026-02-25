module TestRunner (runFileTests) where

import System.Directory (listDirectory, doesDirectoryExist, doesFileExist)
import System.FilePath ((</>), takeExtension, dropExtension)
import Test.Tasty
import Test.Tasty.HUnit
import Data.List (isInfixOf)
import qualified Data.Text as T

import qualified Parser as P
import qualified Type.Inference as TI
import qualified Interpreter as I
import TestSpec
import Debug.Trace qualified as Tr
import Control.Monad (when)
import Report (prettyPrint)

findAllFiles :: FilePath -> IO [FilePath]
findAllFiles dir = do
    exists <- doesDirectoryExist dir
    if not exists
        then pure []
        else do
            entries <- listDirectory dir
            let fullPaths = map (dir </>) entries
            results <- mapM processEntry fullPaths
            pure $ concat results
  where
    processEntry path = do
        isDir <- doesDirectoryExist path
        if isDir
            then findAllFiles path
            else pure [path]

discoverTests :: FilePath -> IO [(FilePath, FilePath)]
discoverTests dir = do
    files <- findAllFiles dir
    let langFiles = filter ((== ".lang") . takeExtension) files
    pairs <- mapM (findPair files) langFiles
    pure $ concat pairs
  where
    findPair _ langPath = do
        let testPath = dropExtension langPath ++ ".test"
        testExists <- doesFileExist testPath
        if testExists
            then pure [(langPath, testPath)]
            else pure []

runTest :: TestSpec -> String -> FilePath -> TestTree
runTest spec source langPath = testCase (T.unpack (tsName spec) ++ " (" ++ langPath ++ ")") $ do
    case tsPhase spec of
        Parse     -> checkParse spec source
        TypeCheck -> checkTypeCheck spec source
        Eval      -> checkEval spec source

checkParse :: TestSpec -> String -> Assertion
checkParse spec source = case P.parse_all source of
    Left err ->
        if tsExpect spec == Failure
            then checkErrorContains (tsErrorContains spec) (show err)
            else assertFailure $ "Parse failed: " ++ show err
    Right _ ->
        if tsExpect spec == Success
            then pure ()
            else assertFailure "Expected failure but parsing succeeded"

checkTypeCheck :: TestSpec -> String -> Assertion
checkTypeCheck spec source = case P.parse_all source of
    Left err -> assertFailure $ "Parse failed: " ++ show err
    Right decl -> case TI.inferDecl decl of
        Left err ->
            if tsExpect spec == Failure
                then checkErrorContains (tsErrorContains spec) (show err)
                else assertFailure $ "Type error: " ++ show err
        Right env ->
            if tsExpect spec == Success
                then case tsExpectedType spec of
                    Nothing -> pure ()
                    Just expected -> assertEqual "Type mismatch" (T.unpack expected) ("NOT IMPLEMENTED")
                else assertFailure "Expected failure but type check succeeded"

data Error = ParseError String | TypeError String | EvalError String
  deriving(Show)


fromError :: (Show a) => Either a b -> Either Error b
fromError (Left err) = Left $ ParseError $ show err
fromError (Right v) = Right v

-- The one thing we can't do with this now is tsExpect spec == False
checkEval :: TestSpec -> String -> Assertion -- (IO something?)
checkEval spec source = case result of
        Left err -> assertFailure $ show err
        Right (_decls, _typeEnv, tMain, value) ->
            if tsExpect spec == Success
                then do
                    case tsExpectedType spec of
                            Nothing -> pure ()
                            Just expected -> do
                                assertEqual ("Type mismatch \n\n" ++ show source) (T.unpack expected) (show tMain)
                    case tsExpectedValue spec of
                        Nothing -> pure ()
                        Just expected -> assertEqual "Value mismatch" (T.unpack expected) (show value)
                else assertFailure "Expected failure but eval succeeded"
      where
          result = do
              decls <- fromError . P.parse_all $ source
              typeEnv <- fromError . TI.inferDecl $ decls
              _ <- when (tsName spec == T.pack "Simple effect") $ do
                   Tr.traceM $ "\n\nDECLS" ++ (show $ decls) ++ "\n\n"
                   Tr.traceM $ "\nEnvVars" ++ (show $ TI.envVars typeEnv) ++ "\n\n"
              tMain <- case TI.lookupType typeEnv "main" of
                          Nothing -> Left $ ParseError "Missing main function"
                          Just t -> Right t
              value <- fromError . I.evalDecls $ decls
              return (decls, typeEnv, tMain, value)


checkErrorContains :: Maybe T.Text -> String -> Assertion
checkErrorContains Nothing _ = pure ()
checkErrorContains (Just substr) err =
    assertBool ("Error should contain '" ++ T.unpack substr ++ "' but got: " ++ err)
               (T.unpack substr `isInfixOf` err)

buildTestTree :: FilePath -> IO TestTree
buildTestTree dir = do
    pairs <- discoverTests dir
    if null pairs
        then pure $ testGroup "File-based tests" []
        else do
            tests <- mapM loadAndRunTest pairs
            pure $ testGroup "File-based tests" tests
  where
    loadAndRunTest (langPath, testPath) = do
        source <- readFile langPath
        specResult <- loadTestSpec testPath
        case specResult of
            Left err -> pure $ testCase langPath $
                assertFailure $ "Failed to load test spec: " ++ err
            Right spec -> pure $ runTest spec source langPath

runFileTests :: IO TestTree
runFileTests = buildTestTree "test_programs"
