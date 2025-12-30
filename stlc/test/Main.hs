module Main (main) where

import Test.Tasty
import TestRunner (runFileTests)

main :: IO ()
main = do
    fileTests <- runFileTests
    defaultMain $ testGroup "All Tests" [ fileTests]
