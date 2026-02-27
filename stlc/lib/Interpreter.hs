module Interpreter (eval, evalDecls, evalExpr, Env, EvaluationError, Value (RInt, RBool, RFunc)) where

import Control.Monad (ap, when, (>=>))
import Data.Char (toLower)
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
    RRecord [] -> "{}"
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
  fmap _ (Err s) = Err s

instance Applicative Eval where
  pure = Done
  (<*>) = ap

instance Monad Eval where
  Done a >>= f = f a
  Perform' eff op args k >>= f = Perform' eff op args (k >=> f)
  Err s >>= _ = Err s

--- Mapping of variables to runtime values
data Env = Env
  { envValues :: Map String Value
  , envDecl :: Map String Expr
  }

emptyEnv :: Env
emptyEnv = Env { envValues = Map.empty, envDecl = Map.empty }

fromDecl :: [Decl] -> Env
fromDecl ds =
    let
      _fromDecl ((LetDecl name t expr):xs) env = _fromDecl xs (Map.insert name expr env)
      _fromDecl (_:xs) env = _fromDecl xs env
      _fromDecl [] env = env
    in
      Env { envValues = Map.empty, envDecl = _fromDecl ds Map.empty }


data EvaluationError
  = Error String
  | MissingValue String
  deriving (Show)

evalExpr :: Expr -> Either EvaluationError Value
evalExpr expr = case s of
  Done v -> Right v
  Perform' {} -> Left $ Error "Missing handler?"
  Err err -> Left $ Error err
  where
    s = eval emptyEnv expr

evalDecls :: [Decl] -> Either EvaluationError Value
evalDecls decls = case evalMain of
      Done v -> Right v
      Perform' {} -> Left $ Error "Missing handler?"
      Err err -> Left $ Error err
    where
      evalMain = case findMain decls of
            Nothing -> Err $ "Missing main function"
            Just mainExpr -> eval initialEnv $ tryExecute mainExpr
      initialEnv = fromDecl decls
      findMain ((LetDecl name _ expr):xs) =
          if map toLower name == "main"
            then Just expr
            else findMain xs
      findMain (_:xs) = findMain xs
      findMain [] = Nothing
      tryExecute expr = case expr of
            Lambda {} -> App expr $ Lit LitUnit
            _ -> expr


-- evalDecl :: Env -> Decl -> Either EvaluationError Value
-- evalDecl env decl =
  {- Our type environment has:
   -  1. Type declarations
   -  2. Effect Declarations
   -  3. Let Declarations (expressions to be evaluated)
   -
   - We are only really concerned about the let declarations
   - right now, Effects essentially have some names?
   - So this needs to be kind of like Type inference,
   - Env will need to have a map of name -> Value?
   -
   - Ex:
   -
   - let x = 2 => x := RInt 2  -- Constants
   - let id = \x -> x =>  id := RFunc "x" (Var x) <env>
   -
   - Problem: How do we construct the environment here?
   -
   - let main = \_ -> thing 2 + luckyNumber
   -
   - let thing = \x -> luckyNum + x
   - let luckyNumber = 42
   -
   - 1. The let decl -> (name, expr)
   - 2. Create a dag where n1 < n2 iff n1 \in freeVars e2?`
   - 3. This won't work for recursion (cycles).
   -
   - 1. Process main()
   - 2. evaluate thing 2
   -    - look up thing
   -      - doesn't exist in values
   -        - evaluate thing
   -          - lookup luckyNumber
   -            - doesn't exist in values
   -              - decl <- getDecl "luckyNumber"
   -              - evalDecl decl
   -
   -                - eval env luckyNumberDecl >-> env
   -              - env["luckyNumber"] := RInt 42
   -            - return $ env.lookup["luckyNumber"]
   -          - Add

   -
   -
   -}



--- Evaluates an expression through term substitutions
eval :: Env -> Expr -> Eval Value
eval env (Var a) = case envValues env !? a of
  Just v -> return v
  Nothing -> do
    eval env (envDecl env ! a)
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
  eval (bind name assign_value env) body
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
        {-
         - NOTE (kc):
         -
         - I am separating these since one is when the value is just from a lambda definition somewhere
         - The other is the result of an effectual computation.
         - Both are capturing the environment
         -
         - RFunc is explict (storing env in the constructor)
         - REffClosure is constructed as a lambda \v -> intercept env hdlr (k v)
         -
         - These could be consolidated
         - On Lambda name _ body -> REffClosure (\v -> eval (bind name v env) body)
         - RFunc name body env -> REffClosure (\v -> eval (bind name v env') body)
         -}
        case f_value of
          RFunc name body env' -> do
            eval (bind name arg_v env') body
          REffClosure k -> do
            k arg_v

          _ -> Err $ "Can not apply " ++ show f_value ++ " to " ++ show arg_v

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
   in eval (bind x v env) rBody
intercept env hdlr (Perform' eff op params k) =
  case opClause hdlr !? (eff, op) of
    Nothing -> Perform' eff op params (\v -> intercept env hdlr (k v))
    Just (OpClause args continue body) ->
      let _resume = REffClosure (\v -> intercept env hdlr (k v))
          env' = bindMany args params $ bind continue _resume env
       in eval env' body
intercept _ _ err = err

bind :: String -> Value -> Env -> Env
bind k v env = env { envValues = Map.insert k v (envValues env) }

bindMany :: [String] -> [Value] -> Env -> Env
bindMany keys values m = foldr (\(k, v) acc -> bind k v acc) m (zip keys values)
