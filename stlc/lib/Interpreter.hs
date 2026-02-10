module Interpreter (eval, evalExpr, Env, EvaluationError, Value (RInt, RBool, RFunc)) where

import Control.Monad (ap, when, (>=>))
import Control.Monad.Except
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
  | REffClosure (Value -> Eval Value)

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
    REffClosure _ -> "?CLOSURE?"

data Eval a
  = Done a
  | Err String
  | Perform' String String [Value] (Value -> Eval a)

--          ^E     ^op     ^args   ^continuation

instance Functor Eval where
  fmap f (Done a) = Done (f a)
  fmap f (Perform' ef op args k) = Perform' ef op args (fmap f . k)
  fmap f (Err s) = Err s

instance Applicative Eval where
  pure = Done
  (<*>) = ap

instance Monad Eval where
  Done a >>= f = f a
  Perform' eff op args k >>= f = Perform' eff op args (k >=> f)
  Err s >>= f = Err s

--- Mapping of variables to runtime values
type Env = Map String Value

data EvaluationError
  = Error String
  | MissingValue String
  deriving (Show)

-- isolated :: Eval Value -> Eval Value
-- isolated action = do
--   original <- get
--   action
--     <* put original `catchError` \e -> do
--       put original
--       throwError e

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err = maybe (throwError err) return

evalExpr :: Expr -> Either EvaluationError Value
evalExpr expr = case s of
  Done v -> Right v
  Perform' {} -> Left $ Error "Missing handler?"
  Err err -> Left $ Error err
  where
    s = eval Map.empty expr

--- Evaluates an expression through term substitutions
eval :: Env -> Expr -> Eval Value
eval env (Var a) = return $ env ! a
eval env (Lambda name _ body) = return $ RFunc name body env
eval env (BinOp op left right) = do
  lvalue <- eval env left
  rvalue <- eval env right

  case (lvalue, rvalue) of
    (RInt l, RInt r) -> case op of
      Add -> Done $ RInt $ l + r
      Subtract -> Done $ RInt $ l - r
      _ -> Err $ "Not implemented : Binary operation " ++ show op
    (RBool l, RBool r) -> case op of
      And -> Done $ RBool $ l && r
      Or -> Done $ RBool $ l || r
      _ -> Err $ "Not implemented : Binary operation " ++ show op
    _ -> Err $ "Invalid operands ( " ++ show lvalue ++ ", " ++ show rvalue ++ " ) for operation " ++ show op
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
    _ -> Err "Type Error: Conditon must be a boolean"
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
          _ -> Err $ "Can not apply" ++ show f_value ++ " to " ++ show arg_v

  get_return_action
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
    _ -> Err "Extending records"
eval env (Record (RecordAccess e b)) = do
  r <- eval env e

  case r of
    RRecord lbls -> do
      case Map.lookup b (Map.fromList lbls) of
        Nothing -> Err $ "Could not find a value for " ++ show b
        Just v -> return v
    _ -> Err "Accessing Records"
eval env (Perform eff op expr) = do
  v <- eval env expr
  Perform' eff op [v] pure
eval env (Handle expr hdlr) = do
  intercept env hdlr (eval env expr)

intercept :: Env -> Handler -> Eval Value -> Eval Value
intercept env hdlr (Done v) =
  let (x, rBody) = retClause hdlr
   in eval (Map.insert x v env) rBody
intercept env hdlr (Perform' eff op params k) =
  case opClause hdlr !? (eff, op) of
    Nothing -> Perform' eff op params (\v -> intercept env hdlr (k v))
    Just (OpClause args continue body) ->
      let _resume = REffClosure (\v -> intercept env hdlr (k v))
          env' = bindMany args params $ bind continue _resume env
       in eval env' body
intercept _ _ err = err

bind :: (Ord k) => k -> a -> Map k a -> Map k a
bind = Map.insert

bindMany :: (Ord k) => [k] -> [a] -> Map k a -> Map k a
bindMany keys values m = foldr (\(k, v) acc -> bind k v acc) m (zip keys values)
