module Interpreter (eval, eval_expr, Env, EvaluationError, Value(RInt, RBool, RFunc)) where

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

--- Represents a runtime value
data Value =
    RInt Integer
    | RBool Bool
    | RFunc String Expr
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


eval_expr :: Expr -> Either EvaluationError Expr
eval_expr expr = evalState s Map.empty
    where
        s = runExceptT $ eval expr

evalWithEnv :: Env -> Expr -> Either EvaluationError Expr
evalWithEnv env expr = evalState (runExceptT $ eval expr) env

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

--- >>> evalWithEnv (Map.fromList [("a", RInt 1)]) (Var "a")
-- Couldn't match expected type `Expr' with actual type `Value'
-- In the expression: RInt 1
-- In the expression: ("a", RInt 1)
-- In the first argument of `fromList', namely `[("a", RInt 1)]'
eval :: Expr -> Eval Expr
eval (Var a) = valueOf a >>= liftMaybe (Error $ "Missing value: " ++ show a)

--- >>> evalWithEnv (Map.fromList []) (Lambda "x" Nothing (Lit $ LitInt 1))
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
eval (Lambda name _ body) = return $ Lambda name Nothing body

--- >>> evalWithEnv (Map.fromList []) (BinOp Add (Lit $ LitInt 1) (Lit $ LitInt 1))
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
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

--- >>> evalWithEnv (Map.fromList []) (Lit $ LitBool True)
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
eval (Lit (LitBool b)) = return $ Lit $ LitBool b

--- >>> evalWithEnv (Map.fromList []) (Lit $ LitInt 1)
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
eval (Lit (LitInt i)) = return $ Lit $ LitInt i

--- >>> evalWithEnv (Map.fromList []) (Let "foo" (Lit $ LitInt 1) (BinOp Add (Var "foo") (Lit $ LitInt 1)))
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
eval (Let name assign body) = do
    traceM $ "\n" ++ name ++ " = " ++ show assign  ++ " in " ++ show body
    env <- get
    assign_value <- eval assign
    put $ Map.insert name assign_value env

    eval body

--- >>> evalWithEnv (Map.fromList []) (If (Lit $ LitBool True) (Lit $ LitInt 1) (Lit $ LitInt 2))
-- *** Exception: /home/kris/personal/lang-ground/stlc/lib/Interpreter.hs:79:12: error: [GHC-83865]
--     • Couldn't match expected type ‘Expr’ with actual type ‘Value’
--     • In the first argument of ‘return’, namely ‘value’
--       In a stmt of a 'do' block: return value
--       In the expression:
--         do body_value <- eval body
--            let value = RFunc name body_value
--            return value
-- (deferred type error)
eval (If cond l_expr r_expr) = eval cond >>= \case
        Lit ( LitBool True) -> eval l_expr
        Lit ( LitBool False) -> eval r_expr

        _ -> throwError (Error "Oops")

--- >>> evalWithEnv (Map.fromList [("add", (RFunc "x" (Lambda "y" Nothing (BinOp Add (Var "x") (Var "y") ))))]) (App (Var "add") (Lit $ LitInt 3))
-- Couldn't match expected type `Expr' with actual type `Value'
-- In the expression:
--   RFunc "x" (Lambda "y" Nothing (BinOp Add (Var "x") (Var "y")))
-- In the expression:
--   ("add",
--    (RFunc "x" (Lambda "y" Nothing (BinOp Add (Var "x") (Var "y")))))
-- In the first argument of `fromList', namely
--   `[("add",
--      (RFunc "x" (Lambda "y" Nothing (BinOp Add (Var "x") (Var "y")))))]'
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

