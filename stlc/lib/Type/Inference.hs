{- HLINT ignore "Use newtype instead of data" -}
-- TODO (kc): Turning this off until we start implementing new Constraints
module Type.Inference
  ( TypeEnv,
    Type (Int, Bool, Var, Arrow, Scheme, Record),
    Row (EmptyRow, RowVar, Row),
    TypeError (..),
    Substitution (IdSub, Single, Composed),
    Constraint (..),
    Infer,
    infer,
    instantiate,
    generalize,
    freeVars,
    inferType,
    emptyEnv,
    runInfer,
    toHead,
    solve,
    apply
  )
where

import Control.Monad (when)
import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace qualified as Tr
import Parser (Expr, Literal (LitBool, LitInt), Op (Add, And, Or, Subtract))
import Parser qualified as Expr (Expr (..))
import Parser qualified as RecordExpr (Expr (..), RecordExpr (..))
import Report (Report (..))

enableTrace :: Bool
enableTrace = False

traceM :: (Applicative f) => String -> f ()
traceM message = when enableTrace $ Tr.traceM message

--- Basic Types
data Type = Int | Bool | Var String | Arrow Type Type | Scheme (Set Type) Type | Record Row
  deriving (Show, Ord, Eq)

data Row = EmptyRow | RowVar String | Row String Type Row
  deriving (Show, Ord)

toHead :: Row -> String -> Row
toHead r l = case r of
  EmptyRow -> r
  RowVar _ -> r
  Row _ _ EmptyRow -> r
  Row _ _ (RowVar _) -> r
  Row label t (Row nextLabel nextType rowTail) ->
    if label == l
      then r
      else
        if nextLabel == l
          then Row nextLabel nextType (Row label t rowTail)
          else Row nextLabel nextType newTail
    where
      newTail = toHead (Row label t rowTail) l

instance Eq Row where
  (==) EmptyRow EmptyRow = True
  (==) (RowVar a) (RowVar b) = a == b
  (==) (Row a t r) r' =
    case toHead r' a of
      Row b u s -> b == a && t == u && r == s
      _ -> False
  (==) _ _ = False

instance Report Row where
  prettyPrint EmptyRow = "EMPTY"
  prettyPrint (RowVar v) = v
  prettyPrint (Row label t rTail) = label ++ " : " ++ prettyPrint t ++ " " ++ rowTail
    where
      rowTail = case rTail of
        EmptyRow -> ""
        RowVar v -> v
        Row {} -> ", " ++ prettyPrint rTail

instance Report Type where
  prettyPrint t =
    case t of
      Int -> "Int"
      Bool -> "Bool"
      Var name -> name
      Arrow d r -> prettyPrint d ++ " -> " ++ prettyPrint r
      Scheme vars typ -> "forall " ++ show (Set.toList vars) ++ " . " ++ prettyPrint typ
      Record row -> "{" ++ prettyPrint row ++ "}"

data TypeError
  = InferenceError String
  | InvalidType String
  | UnificationError String
  deriving (Show)

{- Represents that two types should be equal -}
-- type Constraint = (Type, Type)
data Constraint = Equals (Type, Type)
  deriving (Show, Eq)

-- | A substitution.
-- - We make this a Monoid to more easily handling [Substitution] -> Substituion through composing Substitutions
data Substitution = IdSub | Single (Type, Type) | Composed [(Type, Type)]
  deriving (Show, Eq)

instance Semigroup Substitution where
  (<>) :: Substitution -> Substitution -> Substitution
  (<>) IdSub s = s
  (<>) s IdSub = s
  (<>) (Single s1) (Single s2) = Composed (s1 : [s2])
  (<>) (Single s1) (Composed rest) = Composed (s1 : rest)
  (<>) (Composed initial) (Single s1) = Composed (initial ++ [s1])
  (<>) (Composed first) (Composed final) = Composed (first ++ final)

instance Monoid Substitution where
  mempty = IdSub

type TypeEnv = Map String Type

emptyEnv :: TypeEnv
emptyEnv = Map.empty

data InferState = InferState
  { var :: Int,
    row :: Int
  }

--
-- Inference needs to keep track of fresh ids for type variables to generate constraints
type Infer a = ExceptT TypeError (State InferState) a

-- Unification
type Unify a = ExceptT TypeError (State Substitution) a

-- | Run an inference computation with a starting state for fresh vars
runInfer :: Infer a -> Int -> Int -> Either TypeError a
runInfer m v r = evalState (runExceptT m) inferState
  where
    inferState = InferState {var = v, row = r}

puts :: (MonadState s m) => (s -> p -> s) -> p -> m ()
puts setter value = modify (`setter` value)

nextFreshVar :: Infer Type
nextFreshVar = do
  let setVar s v = s {var = v}

  n <- gets var
  let a = n + 1
  _ <- puts setVar a
  return $ Var ("v" ++ show a)

nextFreshRow :: Infer Row
nextFreshRow = do
  let setRow s v = s {row = v}

  n <- gets row
  let a = n + 1
  _ <- puts setRow a

  return $ RowVar ("r" ++ show a)

extendWithVar :: TypeEnv -> String -> Infer (TypeEnv, Type)
extendWithVar env name = do
  fresh <- nextFreshVar

  let new_env = Map.insert name fresh env

  return (new_env, fresh)

-- The type of some binary function
binaryType :: Type
binaryType = Scheme (Set.fromList [Var "binary_var"]) (Arrow t_var (Arrow t_var t_var))
  where
    t_var = Var "binary_var"

freeVars :: Type -> Set Type
freeVars t = case t of
  Var _ -> Set.fromList [t]
  Arrow t1 t2 -> Set.union (freeVars t1) (freeVars t2)
  Scheme vars _ -> vars
  Int -> Set.empty
  Bool -> Set.empty
  Record EmptyRow -> Set.empty
  Record (RowVar n) -> Set.fromList [Var n]
  Record (Row _ lt row) -> Set.union (freeVars lt) (freeVars (Record row))

infer :: TypeEnv -> Expr -> Infer (Type, [Constraint])
infer env = \case
  -- NOTE (kc): This fails with an error if there is a scoping problem.
  --            This is a bug so it is fine
  Expr.Var name -> do
    assoc_t <- case env !? name of
      Just t -> pure t
      Nothing -> throwError $ InferenceError $ "Type Environment does not contain a type for variable: " ++ name

    -- We throw everything through instantiate.
    t <- instantiate assoc_t
    return (t, [])
  Expr.Lambda var_name _ expr -> do
    (new_env, u) <- extendWithVar env var_name
    (t, cst) <- infer new_env expr
    return (Arrow u t, cst)
  Expr.App e1 e2 -> do
    (t_e1, cs_e1) <- infer env e1
    (t_e2, cs_e2) <- infer env e2

    fresh <- nextFreshVar
    let t = Arrow t_e2 fresh

    let constraints = cs_e1 ++ cs_e2 ++ [Equals (t_e1, t)]

    return (fresh, constraints)
  Expr.Lit x -> return $ case x of
    LitInt _ -> (Int, [])
    LitBool _ -> (Bool, [])
  Expr.Let var_name assign body -> do
    -- Generate a type var a for variable name
    (new_env, a) <- extendWithVar env var_name
    -- generate type and constraints for the assign expression
    (assign_t, assign_cs) <- infer new_env assign
    let result = evalState (runExceptT $ solve assign_cs) IdSub

    {- NOTE (kc):
     - Since let bindings are polymorphic we run into a problem here
     - infer -> (t, cs).
     - t is a scheme, is the free variables of t are in cs
     - then instantiate t, really needs to instantiate (t, cs)
     -
     - It is not as simple as getting a fresh var and doing
     - a rewrite for each fresh var on the constraints.
     -
     -   Suppose we have : \forall a. a -> Int, C = { a == Int }
     -   instantiate : b -> b, C = { b == Int }
     -
     -   Really what we want is: b -> b, C = { b == Int, a == Int }
     -
     -   If we get rid of the constraints on a then the schema type
     -   has changed for uses deeper in the tree.
     -
     - Effectively having Type Schemas, means we have associated
     - Constraint Schemas.
     -
     - For now we are just solving the constraints in the let binding
     - we may look at generating more constraints
    -}

    -- generalize the let binding
    assign_t_gen <- case result of
      Left err -> do
        throwError err
      Right s -> return $ generalize $ apply s assign_t

    -- add the type scheme to the environment
    let env' = Map.insert var_name assign_t_gen new_env
    -- generate type and constraints for body
    (body_t, body_cs) <- infer env' body
    let constraints = body_cs ++ assign_cs ++ [Equals (a, assign_t_gen)]

    return (body_t, constraints)
  Expr.If cond tr fl -> do
    (cond_t, cond_cs) <- infer env cond
    (tr_t, tr_cs) <- infer env tr
    (fl_t, fl_cs) <- infer env fl

    return (tr_t, cond_cs ++ tr_cs ++ fl_cs ++ [Equals (Bool, cond_t), Equals (tr_t, fl_t)])
  Expr.BinOp op l r -> do
    (l_t, _l_cs) <- infer env l
    (r_t, _r_cs) <- infer env r

    let int_cs = (Int, [Equals (l_t, Int), Equals (r_t, Int)])
    let bool_cs = (Bool, [Equals (l_t, Bool), Equals (r_t, Bool)])

    return $ case op of
      Add -> int_cs
      Subtract -> int_cs
      And -> bool_cs
      Or -> bool_cs
  Expr.Record (RecordExpr.RecordCstr assignments) -> do
    let do_infer (l, e) = do
          result <- infer env e
          return (l, result)

    c <- mapM do_infer assignments
    let row = foldl (\acc (l, (t, _)) -> Row l t acc) EmptyRow c
    let constraints = foldl (\acc (_, (_, cst)) -> acc ++ cst) [] c
    return (Record row, constraints)
  Expr.Record (RecordExpr.RecordAccess expr label) -> do
    -- A |- e : { l :: T | r }
    -- -----------------------
    --      A |- e.l :: T

    fresht <- nextFreshVar
    (expr_t, c) <- infer env expr
    freshRow <- nextFreshRow

    let expected_t = Record $ Row label fresht freshRow

    return (fresht, c ++ [Equals (expected_t, expr_t)])
  Expr.Record (RecordExpr.RecordExtension l r) -> do
    -- TODO: What is the sequent rule again?
    return (Record EmptyRow, [])

generalize :: Type -> Type
generalize t = case t of
  Arrow _ _ -> Scheme (freeVars t) t
  Int -> t
  Bool -> t
  Var _ -> t
  Scheme _ _ -> t
  Record _ -> t

initialEnv :: TypeEnv
initialEnv = Map.fromList [("binary", binaryType)]

-- TODO (kc): This needs some tests.
apply :: Substitution -> Type -> Type
apply sub t = case sub of
  IdSub -> t
  Composed [] -> t
  Single (a, b) -> applyToType (a, b) t
  Composed cs -> foldr applyToType t cs
  where
    applyToType (a, b) typ
      | typ == a = b
      | otherwise = case typ of
          Arrow t1 t2 -> Arrow (applyToType (a, b) t1) (applyToType (a, b) t2)
          Record r -> Record (applyToRow (a,b) r)
          _ -> typ

    applyToRow (a, b) = \case
        EmptyRow -> EmptyRow
        RowVar v -> case (a, b) of
          (Var n, Record r') | v == n -> r'
          _ -> RowVar v
        Row l lt r' -> Row l (applyToType (a,b) lt) (applyToRow (a,b) r')

-- TODO (kc): We need to be able to pull out the top level lets here. This will help with some testing
inferType :: Expr -> Either TypeError Type
inferType expr =
  let env = initialEnv
      infer_except = runExceptT (infer env expr)
      initial_state = InferState {var = 0, row = 0}
   in case evalState infer_except initial_state of
        Left err -> Left err
        Right (t, cs) ->
          let except = runExceptT (solve cs)
              result = evalState except IdSub
           in case result of
                Left e -> Left e
                Right sub -> Right $ apply sub t

{- NOTE (kc):
 - These substitutions will get big and this is inefficient
 -
 - Note: If a variable V1 -> T and V2 -> T then we can think of V1 and V2 as being in the same connected component represented as T.
 -      In our graph of types every connected component will be represented by a Primitive type (or maybe a scheme?).
 -      So to not make this suck we will want to use a union find algorithm here which will reduce the number of rewrites necessary
 -}

--- This maps t1 to t2 for some constraint c
(-->) :: Type -> Type -> Constraint -> Constraint
(-->) t1 t2 (Equals (ta, tb)) = Equals (substitute ta, substitute tb)
  where
    substitute typ
      | typ == t1 = t2
      | otherwise = case typ of
          Arrow a b -> Arrow (substitute a) (substitute b)
          _ -> typ

-- (-->) _t1 _t2 _ = error "TODO: Only equality constraints are defined so far"

--- Applies t1 --> t2 over a list of constraints
(->>) :: Type -> Type -> [Constraint] -> [Constraint]
(->>) t1 t2 = map (t1 --> t2)

solve :: [Constraint] -> Unify Substitution
solve [] = return IdSub
solve (c : cs) =
  case c of
    Equals (t1, t2) ->
      if t1 == t2
        then solve cs
        else case (t1, t2) of
          (Var _, t)
            | t1 `notElem` freeVars t ->
                solve (t1 ->> t2 $ cs) >>= \s -> return $ s <> Single (t1, t2)
          (t, Var _)
            | t2 `notElem` freeVars t ->
                solve (t2 ->> t1 $ cs) >>= \s -> return $ s <> Single (t2, t1)
          (Arrow t11 t12, Arrow t21 t22) -> solve $ cs ++ [Equals (t11, t21), Equals (t12, t22)]
          (Record (RowVar p), Record r)  -> solve (Equals (Var p, Record r):cs)
          (Record r, Record (RowVar p)) -> solve (Equals (Var p, Record r):cs)
          (Record (Row l t r), Record row) -> case toHead row l of
              Row _ t' r' -> solve $ cs ++ [Equals (t, t'), Equals (Record r, Record r')]
              _ -> throwError $ InferenceError $ "Could not unify rows: " ++ show t1 ++ " and " ++ show t2
          _ -> throwError $ InferenceError $ "Could not unify " ++ show t1 ++ " and " ++ show t2



-- _ -> throwError $ InferenceError $ "TODO: Implement solver for non equality constraint " ++ show c

-- TODO (kc): Need some unit tests
getFreshVarMap :: Set Type -> Infer (Map Type Type)
getFreshVarMap vars = do
  let getValue v = do
        new_var <- nextFreshVar
        return (v, new_var)

  Map.fromList <$> mapM getValue (Set.toList vars)

-- TODO (kc): Need some unit tests
instantiate :: Type -> Infer Type
instantiate (Scheme vars base) = do
  new_vars <- getFreshVarMap vars

  return $ apply (Composed $ Map.toList new_vars) base
instantiate t = pure t
