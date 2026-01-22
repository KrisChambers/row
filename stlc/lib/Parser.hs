{- HLINT ignore "Use camelCase" -}
module Parser
  ( -- Ast
    TypeAnn,
    Op (Add, And, Subtract, Or),
    Expr (Lit, Var, Lambda, App, If, BinOp, Let, Record),
    RecordExpr (RecordCstr, RecordAccess, RecordExtension),
    Literal (LitInt, LitBool),
    Parser,
    -- Basic parsers
    literal,
    literal_int,
    literal_bool,
    identifier,
    keyword,
    semicolon,
    delimiter,
    arrow,
    -- Composite parsers
    variable,
    parse_type,
    parse_lambda_parameter,
    parse_lambda,
    parse_expr,
    parse_let,
    parse_binary_expr,
    parse_if,
    parse_application,
    parse_program,
    parse_all,
  )
where

import Control.Monad (void)
import Data.Functor (($>))

import Report (Report (..))
import Text.Parsec
import Text.Parsec.String (Parser)

data TypeAnn = Int | Bool | Fn TypeAnn TypeAnn
  deriving (Show, Eq, Ord)

data Literal = LitInt Integer | LitBool Bool
  deriving (Show, Eq, Ord)

instance Report Literal where
  prettyPrint x =
    case x of
      LitInt i -> show i
      LitBool i -> show i

data Op = Add | Subtract | And | Or
  deriving (Show, Eq, Ord)

instance Report Op where
  prettyPrint op =
    case op of
      Add -> "+"
      Subtract -> "*"
      And -> "&&"
      Or -> "||"

data RecordExpr = RecordCstr [(String, Expr)] | RecordAccess Expr String | RecordExtension Expr String Expr
  deriving (Show, Eq, Ord)

instance Report RecordExpr where
  prettyPrint (RecordCstr ls) = "{" ++ labelLines ++ "\n\t}"
    where
      labelLines = foldl (\acc (l, assign) -> acc ++ "\n\t" ++ l ++ " = " ++ show assign) "" ls
  prettyPrint (RecordAccess expr lbl) = prettyPrint expr ++ "." ++ lbl
  prettyPrint (RecordExtension expr1 name expr2) = "{" ++ prettyPrint expr1 ++ " with " ++ name ++ " = " ++ prettyPrint expr2 ++ "}"

data Expr
  = Var String
  | Lambda String (Maybe TypeAnn) Expr
  | App Expr Expr
  | If Expr Expr Expr
  | Lit Literal
  | BinOp Op Expr Expr
  | Let String Expr Expr
  | Record RecordExpr
  deriving (Show, Eq, Ord)

instance Report Expr where
  prettyPrint expr =
    case expr of
      Var name -> name
      Lambda var _type body -> "\\" ++ var ++ prettyPrint body
      App f arg -> "( " ++ prettyPrint f ++ " ) (" ++ prettyPrint arg ++ ")"
      If cond t f -> "if ( " ++ prettyPrint cond ++ ") then ( " ++ prettyPrint t ++ " ) else ( " ++ prettyPrint f ++ " )"
      Lit l -> prettyPrint l
      BinOp op l r -> "( " ++ prettyPrint l ++ ") " ++ prettyPrint op ++ " ( " ++ prettyPrint r ++ " )"
      Let var assign body -> "let " ++ var ++ " = " ++ prettyPrint assign ++ " in " ++ prettyPrint body
      Record rexpr -> prettyPrint rexpr

parse_all :: String -> Either ParseError Expr
parse_all = parse parse_program ""

parse_program :: Parser Expr
parse_program = do
  lets <- sepBy parse_top_level_let definition_delimiter <* (opt_space >> eof)

  let get_let_info expr = case expr of
        Let name value _ -> (name, value)
        _ -> error "Invalid"

  let assignments = map get_let_info lets

  let last_var =
        if any (\(name, _) -> name == "main") assignments
          then Var "main"
          else error "Missing main"

  -- let last_var = fst $ last assignments
  let accumulate acc (name, expr) = Let name expr acc
  let result = foldl' accumulate last_var (reverse assignments)

  return result

definition_delimiter :: Parser ()
definition_delimiter = try newline_delimiter <|> semicolon

semicolon :: Parser ()
semicolon = void (char ';')

start_rec :: Parser ()
start_rec = void (char '{')

end_rec :: Parser ()
end_rec = void (char '}')

access_rec :: Parser ()
access_rec = void (char '.')

newline_delimiter :: Parser ()
newline_delimiter = newline >> opt_space >> newline >> return ()

-- [ We use double newlines or ';' to delimit two top level functions]
delimiter :: Parser ()
delimiter = skipMany ((newline >> spaces >> (newline $> ())) <|> semicolon)

keyword :: String -> Parser ()
keyword name = void (string name)

opt_space :: Parser ()
opt_space = void (many space)

identifier :: Parser String
identifier = do
  prefix <- letter
  remaining <- try (many1 alphaNum <|> string "_") <|> return ""

  let ident = prefix : remaining
  if ident `elem` ["let", "in", "if", "then", "else", "true", "false"]
    then fail ("unexpected keyword: " ++ ident)
    else return ident

literal_bool :: Parser Literal
literal_bool =
  (string "true" $> LitBool True)
    <|> (string "false" $> LitBool False)

literal_int :: Parser Literal
literal_int = fmap (\x -> LitInt (read x :: Integer)) (many1 digit)

literal :: Parser Expr
literal = try (fmap Lit (literal_bool <|> literal_int)) <|> variable

variable :: Parser Expr
variable = fmap Var identifier

parse_expr :: Parser Expr
parse_expr =
  try parse_let
    <|> try parse_record_creation
    <|> try parse_if
    <|> try parse_lambda
    <|> try parse_binary_expr
    <|> try parse_application
    <|> try parse_record_access
    <|> try literal

parse_type :: Parser (Maybe TypeAnn)
parse_type =
  let wrapped = try (char '(') *> parse_type <* char '('
      int = string "Int" >> return (Just Int)
      bool = string "Bool" >> return (Just Bool)
   in try (wrapped <|> int <|> bool) >> return Nothing

parse_lambda_parameter :: Parser (String, Maybe TypeAnn)
parse_lambda_parameter = do
  var <- many space >> identifier <* many space
  -- var_type <- parse_type
  let var_type = Nothing

  return (var, var_type)

arrow :: Parser ()
arrow = char '-' >> char '>' >> return ()

parse_lambda :: Parser Expr
parse_lambda = do
  _ <- opt_space >> char '\\'
  (param, tparam) <- parse_lambda_parameter
  _ <- arrow
  expr <- opt_space >> parse_expr
  return $ Lambda param tparam expr

parse_let_assignment :: Parser (String, Expr)
parse_let_assignment = do
  var <- opt_space >> identifier <* (opt_space >> char '=')
  expr <- opt_space >> parse_expr

  return (var, expr)

parse_let_assignment_list :: Parser [(String, Expr)]
parse_let_assignment_list = parse_let_assignment `sepBy1` try (opt_space >> char ',')

parse_let :: Parser Expr
parse_let = do
  assignments <- opt_space >> keyword "let" >> parse_let_assignment_list
  in_expr <- opt_space >> keyword "in" >> opt_space >> parse_expr

  let build acc (var, e) = Let var e acc

  return $ foldl build in_expr (reverse assignments)

parse_top_level_let :: Parser Expr
parse_top_level_let = do
  (name, expr) <- opt_space >> keyword "let" >> opt_space >> parse_let_assignment

  return $ Let name expr (Var name)

parse_binary_arg :: Parser Expr
parse_binary_arg =
  let complex = opt_space >> char '(' >> opt_space >> parse_expr <* (opt_space >> char ')')
   in try complex <|> literal

parse_binary_op :: Parser Op
parse_binary_op =
  (try (string "||") >> return Or)
    <|> (try (string "&&") >> return And)
    <|> (try (char '+') >> return Add)
    <|> (try (char '-') >> return Subtract)

parse_binary_expr :: Parser Expr
parse_binary_expr = do
  first <- opt_space >> parse_binary_arg

  let next_arg = do
        opt <- opt_space >> parse_binary_op
        arg <- opt_space >> parse_binary_arg
        return (opt, arg)
  rest <- many1 (try next_arg)

  let build l (op, r) = BinOp op l r

  return $ foldl build first rest

parse_if :: Parser Expr
parse_if = do
  cond <- many space >> keyword "if" >> many space >> parse_expr
  true_branch <- many space >> keyword "then" >> many space >> parse_expr
  false_branch <- many space >> keyword "else" >> many space >> parse_expr

  return $ If cond true_branch false_branch

parse_atomic_term :: Parser Expr
parse_atomic_term = try (char '(' >> parse_expr <* char ')') <|> literal

parse_application :: Parser Expr
parse_application = do
  first <- opt_space >> parse_atomic_term
  rest <- many1 (try (opt_space >> parse_atomic_term))

  return $ foldl App first rest

parse_record_extension :: Parser Expr
parse_record_extension = do
  e1 <- opt_space >> variable <* opt_space <* keyword "with"
  l <- opt_space >> identifier <* opt_space <* char '='
  e2 <- opt_space >> parse_expr

  return $ Record $ RecordExtension e1 l e2

parse_record_label_definition :: Parser (String, Expr)
parse_record_label_definition =
  (,)
    <$> (identifier <* opt_space <* char '=')
    <*> (opt_space >> parse_expr)

parse_record_cstr_body :: Parser [(String, Expr)]
parse_record_cstr_body = do
  first <- opt_space >> parse_record_label_definition
  rest <- many $ try $ opt_space >> char ',' >> opt_space >> parse_record_label_definition

  return $ first : rest

parse_record_cstr :: Parser Expr
parse_record_cstr = do Record . RecordCstr <$> parse_record_cstr_body

-- TODO (kc): This needs to not use parse_expr without some tag before it.
parse_record_access :: Parser Expr
parse_record_access = do
  expr <- opt_space >> variable <* char '.'
  Record . RecordAccess expr <$> identifier

parse_record_creation :: Parser Expr
parse_record_creation =
  start_rec
    >> ( try parse_record_cstr
           <|> try parse_record_extension
       )
      <* opt_space
      <* end_rec
