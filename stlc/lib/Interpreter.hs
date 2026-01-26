module Interpreter (eval, evalExpr, Env, EvaluationError, Value(RInt, RBool, RFunc)) where

import Parser
import Data.Map qualified as Map
import Data.Map(Map)
import Control.Monad.State
import Control.Monad.Except
import Debug.Trace qualified as Tr

enableTrace :: Bool
enableTrace = False

traceM :: Applicative f => String -> f ()
traceM s = if enableTrace then Tr.traceM s else pure ()

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
data Value =
    RInt Integer
    | RBool Bool
    | RFunc String Expr
    | RRecord [(String, Value)]
    deriving (Show, Eq)

--- Mapping of variables to runtime values
type Env = Map String Expr

data EvaluationError =
    Error String
    | MissingValue String
    deriving(Show)

type Eval a = ExceptT EvaluationError (State Env) a

valueOf :: String -> Eval (Maybe Expr)
valueOf name = do
    env <- get
    return $ Map.lookup name env

setValue :: String -> Expr -> Eval ()
setValue name value = do
    env <- get
    put $ Map.insert name value env

isolated :: Eval Expr -> Eval Expr
isolated action = do
    original <- get
    action <* put original `catchError` \e -> do
        put original
        throwError e


liftMaybe :: MonadError e m => e -> Maybe a -> m a
liftMaybe err = maybe (throwError err) return


evalExpr :: Expr -> Either EvaluationError Expr
evalExpr expr = evalState s Map.empty
    where
        s = runExceptT $ eval expr


--- Handles substitutions of a variable with it's associated values in the environment
--- This seems like it might be a little redundant with eval
substitute :: Expr -> Eval Expr
substitute (Var a) = do
    a_value <- valueOf a

    return $ case a_value of
            Just expr -> expr
            Nothing -> Var a

substitute (Lambda name _ body) = substitute body >>= \x -> return $ Lambda name Nothing x
substitute (BinOp op l r) = do
        l_s <- substitute l
        r_s <- substitute r

        return $ BinOp op l_s r_s
substitute (Lit l) = return $ Lit l
substitute (App l r) = do
    l_s <- substitute l
    r_s <- substitute r

    return $ App l_s r_s
substitute (If cond t f) = do
    cond_s <- substitute cond
    t_s <- substitute t
    f_s <- substitute f

    return $ If cond_s t_s f_s
substitute (Let name assign body) = do
    assign_s <- substitute assign
    body_s <- substitute body

    return $ Let name assign_s body_s

substitute (Record (RecordCstr lbls)) = do
    let sub_labels (l, e) = (l,) <$> substitute e

    new_lbls <- mapM sub_labels lbls

    return $ Record $ RecordCstr new_lbls

substitute (Record (RecordExtension base l e)) = do
    base' <- substitute base
    e' <- substitute e

    return $ Record $ RecordExtension  base' l e'

substitute (Record (RecordAccess e l)) = do
    e' <- substitute e

    return $ Record $ RecordAccess e' l

--- Evaluates an expression through term substitutions
eval :: Expr -> Eval Expr
eval (Var a) = valueOf a >>= liftMaybe (Error $ "Missing value: " ++ show a)

eval (Lambda name _ body) = return $ Lambda name Nothing body

eval (BinOp op left right) = do
    lvalue <- eval left
    rvalue <- eval right

    liftMaybe (Error "oops") $ case (lvalue, rvalue) of
        (Lit (LitInt l), Lit (LitInt r)) -> case op of
                    Add -> Just $ Lit $ LitInt $ l + r
                    Subtract -> Just $ Lit $ LitInt $ l - r
                    _ -> Nothing
        (Lit (LitBool l), Lit (LitBool r)) -> case op of
                    And -> Just $ Lit $ LitBool $ l && r
                    Or -> Just $ Lit $ LitBool $ l || r
                    _ -> Nothing
        _ -> Nothing

eval (Lit (LitBool b)) = return $ Lit $ LitBool b

eval (Lit (LitInt i)) = return $ Lit $ LitInt i

eval (Let name assign body) = do
    traceM $ "\n" ++ name ++ " = " ++ show assign  ++ " in " ++ show body
    env <- get
    assign_value <- eval assign
    put $ Map.insert name assign_value env

    eval body

eval (If cond l_expr r_expr) = eval cond >>= \case
        Lit ( LitBool True) -> eval l_expr
        Lit ( LitBool False) -> eval r_expr

        _ -> throwError (Error "Oops")

eval (App f arg) = do
    -- We need to handle the App rule of evaluation properly
    -- (\x.e1) e2 |- e1[x->e2]

    f_value <- eval f
    traceM $ "\n" ++ "FUNC := " ++  show f_value
    arg_v <- eval arg
    traceM $ "ARG := " ++ show arg_v

    let get_return_action = do
            case f_value of
                Lambda name Nothing expr -> do
                    setValue name arg_v
                    traceM $ "ARG ASSIGN := " ++ show name ++ " = " ++ show arg_v

                    expr_s <- substitute expr
                    traceM $ "SUB EXPR := " ++ show expr_s
                    eval expr_s

                _ -> throwError (Error "oops")

    result <- isolated get_return_action
    traceM $ "RESULT := " ++  show result

    return result

eval (Record (RecordCstr ls)) = do
    let eval_map (l, e) = do
          expr <- eval e
          return (l, expr)

    rows <- mapM eval_map ls
    return $ Record $ RecordCstr rows

eval (Record (RecordExtension e1 l e2)) = do
  v1 <- eval e1
  v2 <- eval e2

  case v1 of
        Record (RecordCstr lbls) -> do
            return $ Record (RecordCstr $ (l, v2):lbls)
        _ -> throwError $ Error "Extending records"

eval (Record (RecordAccess e b))= do
  r <- eval e

  case r of
    Record (RecordCstr lbls) -> do
      case Map.lookup b (Map.fromList lbls) of
            Nothing -> throwError (Error $ "Could not find a value for " ++ show b)
            Just v -> return v
    _ -> throwError $ Error "Accessing Records"

