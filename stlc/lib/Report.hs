module Report (Report(..)) where

class Report a where
  prettyPrint :: a -> String
