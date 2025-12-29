module Parser (
    -- Ast
    TypeAnn,
    Op (Add, And, Subtract, Or),
    Expr (Lit, Var, Lambda, App, If, BinOp, Let),
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
    parse_all

) where

import Text.Parsec
import Text.Parsec.String(Parser)
import Debug.Trace qualified as Tr

data TypeAnn = Int | Bool | Fn TypeAnn TypeAnn
    deriving(Show, Eq, Ord)

data Literal = LitInt Integer | LitBool Bool
    deriving(Show, Eq, Ord)

data Op = Add | Subtract | And | Or
    deriving(Show, Eq, Ord)

data Expr =
    Var String
    | Lambda String (Maybe TypeAnn) Expr
    | App Expr Expr
    | If Expr Expr Expr
    | Lit Literal
    | BinOp Op Expr Expr
    | Let String Expr Expr
    deriving (Show, Eq, Ord)


parse_all :: String -> Either ParseError Expr
parse_all s = parse parse_program "" s

parse_program :: Parser Expr
parse_program = do
    lets <- sepBy parse_top_level_let definition_delimiter

    let get_let_info expr = case expr of
            Let name value _ -> (name, value)
            _ -> error ("Invalid")


    let assignments = map get_let_info lets

    let last_var = if any (\ (name, _) -> name == "main") assignments
        then Var "main"
        else error ("Missing main")

    -- let last_var = fst $ last assignments
    let accumulate = \acc (name, expr) -> Let name expr acc
    let result = foldl' accumulate last_var (reverse assignments)

    return result


definition_delimiter :: Parser ()
definition_delimiter = try(newline_delimiter) <|> semicolon

semicolon :: Parser ()
semicolon = char ';' >> return ()

newline_delimiter :: Parser ()
newline_delimiter = newline >> opt_space >> newline >> return ()

-- [ We use double newlines or ';' to delimit two top level functions]
delimiter :: Parser ()
delimiter = skipMany ((newline >> spaces >> newline *> return ()) <|> semicolon)

keyword :: String -> Parser ()
keyword name = string name >> return ()

opt_space :: Parser ()
opt_space = many space >> return ()

identifier :: Parser String
identifier = do
    prefix <- letter
    remaining <- try(many1 alphaNum <|> string "_") <|> return ""

    let ident = [prefix] ++ remaining
    if ident `elem` ["let", "in", "if", "then", "else", "true", "false"]
        then fail ("unexpected keyword: " ++ ident)
        else return ident

literal_bool :: Parser Literal
literal_bool = string "true" *> return (LitBool True)
    <|> string "false" *> return (LitBool False)

literal_int :: Parser Literal
literal_int = fmap (\x -> LitInt (read x :: Integer)) (many1 digit)

literal :: Parser Expr
literal = try(fmap Lit (literal_bool <|> literal_int)) <|> variable

variable :: Parser Expr
variable = fmap Var identifier

parse_expr :: Parser Expr
parse_expr =
    (
        try(parse_let) <|>
        try(parse_if) <|>
        try(parse_lambda) <|>
        try(parse_binary_expr) <|>
        try(parse_application) <|>
        try(literal)
        )

parse_type :: Parser (Maybe TypeAnn)
parse_type =
    let wrapped = try(char '(') *> parse_type  <* char '('
        int = string "Int" >> return (Just Int)
        bool = string "Bool" >> return (Just Bool)
    in
        try(wrapped <|> int <|> bool) >> return Nothing

parse_lambda_parameter :: Parser (String, Maybe TypeAnn)
parse_lambda_parameter = do
    var <- many space >> identifier <* many space
    --var_type <- parse_type
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

    return $ (var, expr)

parse_let_assignment_list :: Parser [(String, Expr)]
parse_let_assignment_list = parse_let_assignment `sepBy1` (try(opt_space >> char ','))

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
    in
        try(complex) <|> literal

parse_binary_op :: Parser Op
parse_binary_op =
    (   (try(string "||") >> return Or)
    <|> (try(string "&&") >> return And)
    <|> (try(char '+') >> return Add)
    <|> (try(char '-') >> return Subtract)
    )

parse_binary_expr :: Parser Expr
parse_binary_expr = do
    let initial =  opt_space >> parse_binary_arg
    let addOp = do
            op <- opt_space >> parse_binary_op
            return (\x y -> BinOp op x y)

    initial `chainl1` addOp

parse_if :: Parser Expr
parse_if = do
    cond <- many space >> keyword "if" >> many space >> parse_expr
    true_branch <- many space >> keyword "then" >> many space >> parse_expr
    false_branch <- many space >> keyword "else" >> many space >> parse_expr

    return $ If cond true_branch false_branch

parse_atomic_term :: Parser Expr
parse_atomic_term = try(char '(' >> parse_expr <* char ')') <|> literal

parse_application :: Parser Expr
parse_application = do
    first <- opt_space >> parse_atomic_term
    rest <- many1 (try(opt_space >> parse_atomic_term))

    return $ foldl App first rest


