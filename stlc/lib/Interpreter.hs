module Interpreter (eval, evalExpr, Env, EvaluationError, Value (RInt, RBool, RFunc)) where

import Control.Monad (ap, when, (>=>))
import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map, (!), (!?))
import Data.Map qualified as Map
import Debug.Trace qualified as Tr
import Parser

enableTrace :: Bool
enableTrace = False

traceM :: (Applicative f) => String -> f ()
traceM s = when enableTrace $ Tr.traceM s

{- BUG (kc):
 -      There is a scoping bug
 -          let flip = \f -> \x -> y -> f y x;
 -          let sub = \x -> \y -> x - y;
 -          let flippedSub = flip sub
 -          let main = flippedSub 5 10
 -
 -      This should be 10 - 5 = 5
 -      But we are getting -5
 -
 -      It is fixed if we use
 -          let sub = \a -> \b -> a - b;
 -
 -}

--- Represents a runtime value
data Value
  = RInt Integer
  | RBool Bool
  | RFunc String Expr Env
  | RUnit
  | RString String
  | RRecord [(String, Value)]
  deriving (-- | RClosure (Value -> Eval' Value)
            Eq)

instance Show Value where
  show = \case
    RFunc var expr _ -> "\\" ++ var ++ " -> (" ++ show expr ++ ")"
    RUnit -> "()"
    RRecord [] -> "{ }"
    RRecord lbls -> "{ " ++ foldr1 (\lbl acc -> lbl ++ ", " ++ acc) labels ++ " }"
      where
        labels = map (\(l, v) -> l ++ ": " ++ show v) lbls
    RInt v -> show v
    RBool v -> show v
    RString v -> v

data Eval' a
  = Done a
  | Perform' String String [Value] (Value -> Eval' a)

--          ^E     ^op     ^args   ^continuation

instance Functor Eval' where
  fmap f (Done a) = Done (f a)
  fmap f (Perform' ef op args k) = Perform' ef op args (fmap f . k)

instance Applicative Eval' where
  pure = Done
  (<*>) = ap

instance Monad Eval' where
  Done a >>= f = f a
  Perform' eff op args k >>= f = Perform' eff op args (k >=> f)

--- Mapping of variables to runtime values
type Env = Map String Value

data EvaluationError
  = Error String
  | MissingValue String
  deriving (Show)

type Eval a = ExceptT EvaluationError (State Env) a

-- valueOf :: String -> Eval Value
-- valueOf name = do
--   env <- get
--   return $ env ! name
--
-- setValue :: String -> Value -> Eval ()
-- setValue name value = do
--   env <- get
--   put $ Map.insert name value env

isolated :: Eval Value -> Eval Value
isolated action = do
  original <- get
  action
    <* put original `catchError` \e -> do
      put original
      throwError e

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err = maybe (throwError err) return

evalExpr :: Expr -> Either EvaluationError Value
evalExpr expr = evalState s Map.empty
  where
    s = runExceptT $ eval Map.empty expr

--- Evaluates an expression through term substitutions
eval :: Env -> Expr -> Eval Value
eval env (Var a) = return $ env ! a
eval env (Lambda name _ body) = return $ RFunc name body env
eval env (BinOp op left right) = do
  lvalue <- eval env left
  rvalue <- eval env right

  liftMaybe (Error "oops") $ case (lvalue, rvalue) of
    (RInt l, RInt r) -> case op of
      Add -> Just $ RInt $ l + r
      Subtract -> Just $ RInt $ l - r
      _ -> Nothing
    (RBool l, RBool r) -> case op of
      And -> Just $ RBool $ l && r
      Or -> Just $ RBool $ l || r
      _ -> Nothing
    _ -> Nothing
eval _ (Lit l) = return $ case l of
  LitBool b -> RBool b
  LitInt i -> RInt i
  LitString s -> RString s
  LitUnit -> RUnit
eval env (Let name assign body) = do
  assign_value <- eval env assign
  eval (Map.insert name assign_value env) body
eval env (If cond l_expr r_expr) =
  eval env cond >>= \case
    RBool True -> eval env l_expr
    RBool False -> eval env r_expr
    _ -> throwError (Error "Type Error: Conditon must be a boolean")
eval env (App f arg) = do
  -- We need to handle the App rule of evaluation properly
  -- (\x.e1) e2 |- e1[x->e2]

  f_value <- eval env f
  arg_v <- eval env arg

  let get_return_action = do
        case f_value of
          RFunc name body env' -> do
            -- put env -- Set the evaluation environment
            -- setValue name arg_v -- bind arg_v to the function name
            eval (Map.insert name arg_v env') body
          _ -> throwError . Error $ "Can not apply" ++ show f_value ++ " to " ++ show arg_v

  isolated get_return_action

eval env (Record (RecordCstr ls)) = do
  let eval_map (l, e) = do
        expr <- eval env e
        return (l, expr)

  rows <- mapM eval_map ls
  return $ RRecord rows
eval env (Record (RecordExtension e1 l e2)) = do
  v1 <- eval env e1
  v2 <- eval env e2

  case v1 of
    RRecord lbls -> do
      return $ RRecord $ (l, v2) : lbls
    _ -> throwError $ Error "Extending records"
eval env (Record (RecordAccess e b)) = do
  r <- eval env e

  case r of
    RRecord lbls -> do
      case Map.lookup b (Map.fromList lbls) of
        Nothing -> throwError (Error $ "Could not find a value for " ++ show b)
        Just v -> return v
    _ -> throwError $ Error "Accessing Records"
eval env (Perform eff op expr) = do
  v <- eval env expr
  throwError $ Error "Not Implemented"
eval env (Handle expr hdlrs) = do
  throwError $ Error "Not Implemented"
