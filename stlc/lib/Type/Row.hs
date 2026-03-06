module Type.Row (
  Row (..),
  merge,
  close,
  RowOperationError,
  toHead
) where

import Report (Report (..))

data Row a = Row a (Row a) | EmptyRow | Var String
  deriving(Show)

rowStart :: String
rowStart = "〈"
rowEnd :: String
rowEnd = "〉"

instance Show a => Report (Row a) where
  prettyPrint EmptyRow = rowStart ++ rowEnd
  prettyPrint (Var b) = rowStart ++ b ++ rowEnd
  prettyPrint (Row b r') = rowStart ++ show b ++ separator ++ " " ++ prettyPrint r'
     where
      separator = case r' of
        EmptyRow -> ""
        Var v -> v
        Row {} -> ","


-- Rows are equivalent up to reordering
instance Eq a => Eq (Row a) where
  (==) EmptyRow EmptyRow = True
  (==) (Row a r) r' =
    case toHead r' a of
      Row b s -> b == a  && r == s
      _ -> False
  (==) EmptyRow _ = False
  (==) (Var a) (Var b) = a == b
  (==) (Var _) _ = False

-- Since we are using "scoped" labels instead of lacks constraints
toHead :: Eq a => Row a -> a -> Row a
toHead r l = case r of
  Row _ (Var _) -> r
  Row label (Row nextLabel  rowTail) ->
    if label == l
      then r
      else
        if nextLabel == l
          then Row nextLabel (Row label rowTail)
          else Row nextLabel newTail
    where
      newTail = toHead (Row label rowTail) l
  _ -> r

data RowOperationError =
  MergeError String

merge :: Row a -> Row a -> Either RowOperationError (Row a)
merge r1 r2 = case (r1, r2) of
  (Row l rt, r) -> do
    rowTail <- merge rt r
    return $ Row l rowTail
  (Var _, Row l rt) -> do
    rowTail <- merge r1 rt
    return $ Row l rowTail
  (EmptyRow, r) -> Right r
  (r, EmptyRow) -> Right r
  (Var _, Var _) -> Left . MergeError $ "Can not merge two open rows"
  -- (a, b) -> Left . UnificationError $ "Can only merge rows not (" ++ show a ++ ", " ++ show b ++ ")"

close :: Row a -> Row a
close EmptyRow = EmptyRow
close (Var _) = EmptyRow
close (Row b r') = Row b $ close r'
