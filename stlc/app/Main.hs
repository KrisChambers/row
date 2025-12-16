module Main where

import Parser (parse_all)
import Type.Inference (infer_type)
import Interpreter (eval_expr)
import System.Environment (getArgs)
import System.Exit (exitFailure)

--- Read in a file and evaluate it
main :: IO ()
main = do
    putStrLn ""
    args <- getArgs
    case args of
        [filePath] -> do
            contents <- readFile filePath
            expr <- case parse_all contents of
                    Left err -> failCli err
                    Right expr -> return $ expr

            putStrLn $ show expr

            _ <- case infer_type expr of
                    Left err -> failCli err
                    Right _ -> return ()

            result <- case eval_expr expr of
                    Left err -> failCli err
                    Right result -> return $ result

            putStrLn $ show result
        _ -> failCli "Usage: lang-ground-stlc <file>"

failCli :: forall a b. Show a => a ->  IO b
failCli err = do
    putStrLn $ show err
    exitFailure
