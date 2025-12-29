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
    Right expr -> case TI.inferType expr of
        Left err ->
            if tsExpect spec == Failure
                then checkErrorContains (tsErrorContains spec) (show err)
                else assertFailure $ "Type error: " ++ show err
        Right typ ->
            if tsExpect spec == Success
                then case tsExpectedType spec of
                    Nothing -> pure ()
                    Just expected -> assertEqual "Type mismatch" (T.unpack expected) (show typ)
                else assertFailure "Expected failure but type check succeeded"

checkEval :: TestSpec -> String -> Assertion
checkEval spec source = case P.parse_all source of
    Left err -> assertFailure $ "Parse failed: " ++ show err
    Right expr -> case TI.inferType expr of
        Left err -> assertFailure $ "Type error: " ++ show err
        Right typ -> case I.eval_expr expr of
            Left err ->
                if tsExpect spec == Failure
                    then checkErrorContains (tsErrorContains spec) (show err)
                    else assertFailure $ "Eval error: " ++ show err
            Right value ->
                if tsExpect spec == Success
                    then do
                        case tsExpectedValue spec of
                            Nothing -> pure ()
                            Just expected -> assertEqual "Value mismatch" (T.unpack expected) (show value)
                        case tsExpectedType spec of
                                Nothing -> pure ()
                                Just expected -> assertEqual ("Type mismatch \n\n" ++ show source ++ "\n\n" ++ show expr) (T.unpack expected) (show typ)
                    else assertFailure "Expected failure but eval succeeded"

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
