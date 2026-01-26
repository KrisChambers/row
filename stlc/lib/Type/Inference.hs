{- HLINT ignore "Use newtype instead of data" -}
-- TODO (kc): Turning this off until we start implementing new Constraints
module Type.Inference
  ( TypeEnv,
    Type (Int, Bool, Var, Arrow, Record),
    Scheme (Forall),
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
    apply,
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Parser (Expr, Literal (LitBool, LitInt), Op (Add, And, Or, Subtract))
import Parser qualified as Expr (Expr (..))
import Parser qualified as RecordExpr (RecordExpr (..))
import Report (Report (..))
import Data.Bifunctor (bimap)

-- import Control.Monad (when)
-- import Debug.Trace qualified as Tr
-- enableTrace :: Bool
-- enableTrace = False
--
-- traceM :: (Applicative f) => String -> f ()
-- traceM message = when enableTrace $ Tr.traceM message

--- Basic Types
-- t := Int
--    | Bool
--    | a
--    | t -> t ! e
--    | forall a,.. . t
--    | { l1 : t, ... ln: tn }
data Type = Int | Bool | Var String | Arrow Type Type | Record Row
  deriving (Show, Ord, Eq)

data Row = EmptyRow | RowVar String | Row String Type Row
  deriving (Show, Ord)

data Effect = EmptyEffect | EffectVar String | EffectRow Type Effect

data Scheme = Forall (Set String) Type

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
      Record row -> "{" ++ prettyPrint row ++ "}"

instance Report Scheme where
  prettyPrint (Forall vars t) = "forall " ++ show vars ++ " . " ++ prettyPrint t

instance Report Effect where
  prettyPrint e =
    case e of
      EmptyEffect -> "{}"
      EffectVar v -> "{" ++ v ++ "}"
      EffectRow t r -> "{" ++ prettyPrint t ++ separator ++ prettyPrint r ++ "}"
        where
          separator = case r of
            EmptyEffect -> ""
            EffectVar _ -> "| "
            EffectRow _ _ -> ","

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

type TypeEnv = Map String Scheme

emptyEnv :: TypeEnv
emptyEnv = Map.empty

-- TypeEnv only stores schemes and accessing these always instantiates them. But primitives (?) (non-arrows?)
-- never have any scheme variables.

extend :: TypeEnv -> String -> Infer (TypeEnv, Type)
extend env name = do
  v <- nextFreshVar
  let fresh = Var v

  let new_env = Map.insert name (Forall Set.empty fresh) env

  return (new_env, fresh)

data InferState = InferState
  { var :: Int,
    row :: Int,
    effect :: Int
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
    inferState = InferState {var = v, row = r, effect = 0}

puts :: (MonadState s m) => (s -> p -> s) -> p -> m ()
puts setter value = modify (`setter` value)

nextFreshVar :: Infer String
nextFreshVar = do
  let setVar s v = s {var = v}

  n <- gets var
  let a = n + 1
  _ <- puts setVar a
  return $ "v" ++ show a

nextFreshRow :: Infer Row
nextFreshRow = do
  let setRow s v = s {row = v}

  n <- gets row
  let a = n + 1
  _ <- puts setRow a

  return $ RowVar ("r" ++ show a)

-- extend :: name -> Type -> Infer(TypeEnv, Type) : This need to store a (Forall [] t)
-- instantiate :: Scheme -> Type (This needs to generate new stuff


-- The type of some binary function
binaryType :: Scheme
binaryType = Forall (Set.fromList ["binary_var"]) (Arrow t_var (Arrow t_var t_var))
  where
    t_var = Var "binary_var"

freeVars :: Type -> Set String
freeVars t = case t of
  Var name -> Set.fromList [name]
  Arrow t1 t2 -> Set.union (freeVars t1) (freeVars t2)
  Int -> Set.empty
  Bool -> Set.empty
  Record EmptyRow -> Set.empty
  Record (RowVar n) -> Set.fromList [n]
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
    (new_env, u) <- extend env var_name
    (t, cst) <- infer new_env expr
    return (Arrow u t, cst)
  Expr.App e1 e2 -> do
    (t_e1, cs_e1) <- infer env e1
    (t_e2, cs_e2) <- infer env e2

    fresh <- nextFreshVar >>= \s -> return $ Var s
    let t = Arrow t_e2 fresh

    let constraints = cs_e1 ++ cs_e2 ++ [Equals (t_e1, t)]

    return (fresh, constraints)
  Expr.Lit x -> return $ case x of
    LitInt _ -> (Int, [])
    LitBool _ -> (Bool, [])
  Expr.Let var_name assign body -> do
    -- Generate a type var a for variable name
    (new_env, a) <- extend env var_name
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
    assign_t_i <- instantiate assign_t_gen
    let constraints = body_cs ++ assign_cs ++ [Equals (a, assign_t_i)]

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

    fresht <- nextFreshVar >>= \s -> return $ Var s
    (expr_t, c) <- infer env expr
    freshRow <- nextFreshRow

    let expected_t = Record $ Row label fresht freshRow

    return (fresht, c ++ [Equals (expected_t, expr_t)])
  Expr.Record (RecordExpr.RecordExtension base name ext) -> do
    --        A |- e1 : {p}     A |- e2 :: T
    -- --------------------------------------------------
    --      A |- { e1 with l = e2 } : { l :: T | p }
    --
    --  Input : e1, e2, l
    --  Output : T, p

    (base_t, cl) <- infer env base
    freshRow <- nextFreshRow
    (ext_t, cr) <- infer env ext

    let result_t = Record (Row name ext_t freshRow)
    let expected_t = Record freshRow

    -- In more general systems this would generate a Lacks l p constraint
    -- With microsofts proposal we have a simplified inference since we allow "scoped" labels
    return (result_t, cl ++ cr ++ [Equals (expected_t, base_t)])

generalize :: Type -> Scheme
generalize t = Forall vars t
  where
    vars = case t of
      Arrow {} -> freeVars t
      _ -> Set.empty

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
          Record r -> Record (applyToRow (a, b) r)
          _ -> typ

    applyToRow (a, b) = \case
      EmptyRow -> EmptyRow
      RowVar v -> case (a, b) of
        (Var n, Record r') | v == n -> r'
        _ -> RowVar v
      Row l lt r' -> Row l (applyToType (a, b) lt) (applyToRow (a, b) r')

-- t1 -> t2 {} , s1 -> s2 {e} -->
-- applyToEffect (a, b) = \case
--   EmptyEffect -> EmptyEffect
--   EffectVar v -> case (a,b) of
--     (Var n, Arrow _ _ e') |  n == v -> e'
--     _ -> EffectVar v
--   EffectRow t e -> EffectRow (applyToType (a,b) t) (applyToEffect (a,b) e)

-- TODO (kc): We need to be able to pull out the top level lets here. This will help with some testing
inferType :: Expr -> Either TypeError Type
inferType expr =
  let env = initialEnv
      infer_except = runExceptT (infer env expr)
      initial_state = InferState {var = 0, row = 0, effect = 0}
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
          Arrow a b -> Arrow (substitute a) (substitute b) -- (substitute e)
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
          (Var n, t)
            | n `notElem` freeVars t ->
                solve (t1 ->> t2 $ cs) >>= \s -> return $ s <> Single (t1, t2)
          (t, Var n)
            | n `notElem` freeVars t ->
                solve (t2 ->> t1 $ cs) >>= \s -> return $ s <> Single (t2, t1)
          (Arrow t11 t12, Arrow t21 t22) -> solve $ cs ++ [Equals (t11, t21), Equals (t12, t22)]
          (Record (RowVar p), Record r) -> solve (Equals (Var p, Record r) : cs)
          (Record r, Record (RowVar p)) -> solve (Equals (Var p, Record r) : cs)
          (Record (Row l t r), Record row) -> case toHead row l of
            Row _ t' r' -> solve $ cs ++ [Equals (t, t'), Equals (Record r, Record r')]
            _ -> throwError $ InferenceError $ "Could not unify rows: " ++ show t1 ++ " and " ++ show t2
          _ -> throwError $ InferenceError $ "Could not unify " ++ show t1 ++ " and " ++ show t2

-- TODO (kc): Need some unit tests
getFreshVarMap :: Set String -> Infer (Map String String)
getFreshVarMap vars = do
  let getValue v = do
        new_var <- nextFreshVar
        return (v, new_var)

  Map.fromList <$> mapM getValue (Set.toList vars)

-- TODO (kc): Need some unit tests
instantiate :: Scheme -> Infer Type
instantiate (Forall vars base) = do
  new_vars <- getFreshVarMap vars

  let vs = map (bimap Var Var) $ Map.toList new_vars

  return $ apply (Composed vs) base
