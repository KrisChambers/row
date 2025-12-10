module Interpreter (eval, eval_expr, Env, EvaluationError, Value(RInt, RBool, RFunc)) where

import Parser
import Data.Map qualified as Map
import Data.Map(Map)
import Control.Monad.State
import Control.Monad.Except

--- Represents a runtime value
data Value =
    RInt Integer
    | RBool Bool
    | RFunc String Expr
    deriving (Show, Eq)

--- Mapping of variables to runtime values
type Env = Map String Value

data EvaluationError =
    Error String
    | MissingValue String
    deriving(Show)

type Eval a = ExceptT EvaluationError (State Env) a

valueOf :: String -> Eval Value
valueOf name = do
    env <- get
    let value = Map.lookup name env

    liftMaybe (MissingValue $ show name) value

setValue :: String -> Value -> Eval ()
setValue name value = do
    env <- get
    put $ Map.insert name value env

isolated :: Eval Value -> Eval Value
isolated action = do
    original <- get
    action <* put original `catchError` \e -> do
        put original
        throwError e


liftMaybe :: MonadError e m => e -> Maybe a -> m a
liftMaybe err = maybe (throwError err) return


eval_expr :: Expr -> Either EvaluationError Value
eval_expr expr = evalState s Map.empty
    where
        s = runExceptT $ eval expr

evalWithEnv :: Env -> Expr -> Either EvaluationError Value
evalWithEnv env expr = evalState (runExceptT $ eval expr) env

--- >>> evalWithEnv (Map.fromList [("a", RInt 1)]) (Var "a")
-- Right (RInt 1)
eval :: Expr -> Eval Value
eval (Var a) = valueOf a

--- >>> evalWithEnv (Map.fromList []) (Lambda "x" Nothing (Lit $ LitInt 1))
-- Right (RFunc "x" (Lit (LitInt 1)))
eval (Lambda name _ body) = do
    let value = RFunc name body
    return value

--- >>> evalWithEnv (Map.fromList []) (BinOp Add (Lit $ LitInt 1) (Lit $ LitInt 1))
-- Right (RInt 2)
eval (BinOp op left right) = do
    lvalue <- eval left
    rvalue <- eval right

    liftMaybe (Error "oops") $ case (op, lvalue, rvalue) of
        (Add, RInt l, RInt r) -> Just $ RInt (l + r)
        (Subtract, RInt l, RInt r) -> Just $  RInt (l - r)
        (And, RBool l, RBool r) -> Just $ RBool (l && r)
        (Or, RBool l, RBool r) -> Just $ RBool (l || r)
        _ -> Nothing

--- >>> evalWithEnv (Map.fromList []) (Lit $ LitBool True)
-- Right (RBool True)
eval (Lit (LitBool b)) = return $ RBool b

--- >>> evalWithEnv (Map.fromList []) (Lit $ LitInt 1)
-- Right (RInt 1)
eval (Lit (LitInt i)) = return $ RInt i

--- >>> evalWithEnv (Map.fromList []) (Let "foo" (Lit $ LitInt 1) (BinOp Add (Var "foo") (Lit $ LitInt 1)))
-- Right (RInt 2)
eval (Let name assign body) = do
    env <- get
    assign_value <- eval assign
    put $ Map.insert name assign_value env

    eval body

--- >>> evalWithEnv (Map.fromList []) (If (Lit $ LitBool True) (Lit $ LitInt 1) (Lit $ LitInt 2))
-- Right (RInt 1)
eval (If cond l_expr r_expr) = eval cond >>= \case
        RBool True -> eval l_expr
        RBool False -> eval r_expr

        _ -> throwError (Error "Oops")

--- >>> evalWithEnv (Map.fromList [("add", (RFunc "x" (BinOp Add (Var "x") (Lit $ LitInt 2) )))]) (App (Var "add") (Lit $ LitInt 3))
-- Right (RInt 5)
eval (App f arg) = do
    f_value <- eval f
    arg_v <- eval arg

    let get_return_action = do
            case f_value of
                RFunc name expr -> do
                    setValue name arg_v
                    eval expr

                _ -> throwError (Error "oops")

    isolated get_return_action
