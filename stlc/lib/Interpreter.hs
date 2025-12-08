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

eval_expr :: Expr -> Except EvaluationError Value
eval_expr expr = runState (runExceptT eval expr) Map.empty

eval :: Expr -> Eval Value
eval (Var a) = valueOf a

eval (Lambda name _ body) = do
    env <- get
    let value = RFunc name body
    return value

eval (BinOp op left right) = do
    lvalue <- eval left
    rvalue <- eval right

    liftMaybe (Error "oops") $ case (op, lvalue, rvalue) of
        (Add, RInt l, RInt r) -> Just $ RInt (l + r)
        (Subtract, RInt l, RInt r) -> Just $  RInt (l - r)
        (And, RBool l, RBool r) -> Just $ RBool (l && r)
        (Or, RBool l, RBool r) -> Just $ RBool (l || r)
        _ -> Nothing

eval (Lit (LitBool b)) = return $ RBool b
eval (Lit (LitInt i)) = return $ RInt i

eval (Let name assign body) = do
    env <- get
    assign_value <- eval assign
    put $ Map.insert name assign_value env

    eval body

eval (If cond l_expr r_expr) = eval cond >>= \case
        RBool True -> eval l_expr
        RBool False -> eval r_expr

        _ -> throwError (Error "Oops")

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









