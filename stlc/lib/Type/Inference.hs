{- HLINT ignore "Use newtype instead of data" -}
-- TODO (kc): Turning this off until we start implementing new Constraints
module Type.Inference
  ( TypeEnv,
    Type (TCon, Var, Arrow, Record, EmptyRow, Row),
    Scheme (Forall),
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
    tInt,
    tBool
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
-- import Parser qualified as P (Expr, Literal (LitBool, LitInt), Op (Add, And, Or, Subtract))
import Parser qualified as Expr (Expr (..))
import Parser qualified as RecordExpr (RecordExpr (..))
import Parser qualified as P
-- import Report (Report (..))
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
--    | { l1 : t, ... ln: tn }
data Type = Var String | Arrow Type Type Type | Record Type | EmptyRow | Row (String, Type) Type | TCon String [Type]
  deriving (Show, Ord)

data Scheme = Forall (Set String) Type

data TypeInfo = TypeInfo
    -- Ex : Functor a -> ["a"]
  { typeInfoParams :: [String]
    -- *, or * -> *, ?
  , typeInfoKind :: String
  }

data EffectInfo = EffectInfo
  { effectInfoParams :: [String]
  , effectInfoOps :: Map String Scheme
  }

-- Contains constructor information.
-- The name of the type the constructor belongs
-- The type scheme for the constructor
data CtorInfo = CtorInfo
  { ctorInfoTypeName :: String
  , ctorInfoScheme :: Scheme
  }


data TEnv = TEnv
  { envTypes :: Map String TypeInfo
  , envEffects :: Map String EffectInfo
  , envVars :: Map String Scheme
  , envCstors :: Map String CtorInfo
  }

tBool :: Type
tBool = TCon "Bool" []

tInt :: Type
tInt = TCon "Int" []

tUnit :: Type
tUnit = TCon "()" []


prelude :: TEnv
prelude = TEnv
  { envTypes = Map.fromList
      [ ("Int", TypeInfo [] "*")
      , ("Bool", TypeInfo [] "*")
      ]
  , envEffects = Map.empty
  , envVars = Map.empty
  , envCstors = Map.fromList
      [ ("True", CtorInfo "Bool" (Forall Set.empty tBool))
      , ("False", CtorInfo "Bool" (Forall Set.empty tBool))
      , ("()", CtorInfo "()" (Forall Set.empty tUnit))
      ]
  }


toHead :: Type -> String -> Type
toHead r l = case r of
  Row _ (Var _) -> r
  Row (label, t) (Row (nextLabel, nextType) rowTail) ->
    if label == l
      then r
      else
        if nextLabel == l
          then Row (nextLabel, nextType) (Row (label, t) rowTail)
          else Row (nextLabel, nextType) newTail
    where
      newTail = toHead (Row (label, t) rowTail) l
  _ -> r

instance Eq Type where
  -- (==) Int Int = True
  -- (==) Bool Bool = True
  (==) (Var a) (Var b) = a == b
  (==) (Arrow a1 e1 r1) (Arrow a2 e2 r2) = a1 == a2 && r1 == r2 && e1 == e2
  (==) (Record r1) (Record r2) = r1 == r2
  (==) EmptyRow EmptyRow = True
  (==) (Row (a, t) r) r' =
    case toHead r' a of
      Row (b, u) s -> b == a && t == u && r == s
      _ -> False
  (==) (TCon n1 ts1) (TCon n2 ts2) = n1 == n2 && typesEqual
      where
        typesEqual = foldr accumulator True $ zip ts1 ts2
        accumulator (t1, t2) a = a && t1 == t2
  (==) _ _ = False

-- instance Report Type where
--   prettyPrint t =
--     case t of
--       Int -> "Int"
--       Bool -> "Bool"
--       Var name -> name
--       Arrow d e r -> prettyPrint d ++ " -> " ++ prettyPrint r ++ " ! " ++ prettyPrint e
--       Record row -> "{" ++ prettyPrint row ++ "}"
--       EmptyRow -> ""
--       Row (l, lt) rtail -> l ++ " : " ++ prettyPrint lt ++ separator ++ " " ++ prettyPrint rtail
--          where
--           separator = case rtail of
--             EmptyRow -> ""
--             Var v -> v
--             Row {} -> ","
--             _ -> "ERROR"


-- instance Report Scheme where
--   prettyPrint (Forall vars t) = "forall " ++ show vars ++ " . " ++ prettyPrint t

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

-- TODO (kc): prelude replaces this
emptyEnv :: TypeEnv
emptyEnv = Map.empty

-- TypeEnv only stores schemes and accessing these always instantiates them. But primitives (?) (non-arrows?)
-- never have any scheme variables.

extend :: TypeEnv -> String -> Infer (TypeEnv, Type)
extend env name = do
  v <- fresh TVar >>= newvar

  let new_env = Map.insert name (Forall Set.empty v) env

  return (new_env, v)

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

data UnificationVariable = TVar | RVar | EVar

fresh :: UnificationVariable -> Infer String
fresh varType = do
  let setV s v = case varType of
        TVar -> s { var = v }
        RVar -> s { row = v }
        EVar -> s { effect = v }

  let prefix = case varType of
        TVar -> "v"
        RVar -> "r"
        EVar -> "e"

  n <- gets var >>= \n' -> return $ n' + 1
  _ <- puts setV n

  return $ prefix ++ show n

-- The type of some binary function
binaryType :: Scheme
binaryType = Forall (Set.fromList ["binary_var"]) (Arrow t_var EmptyRow (Arrow t_var EmptyRow t_var))
  where
    t_var = Var "binary_var"

freeVars :: Type -> Set String
freeVars t = case t of
  Var name -> Set.fromList [name]
  Arrow t1 e t2 -> Set.union (Set.union (freeVars t1) (freeVars t2)) (freeVars e)
  Record row -> freeVars row
  Row (_, lt) rtail -> Set.union (freeVars lt) (freeVars rtail)
  TCon _ ts -> foldr (\a b-> Set.union b $ freeVars a) Set.empty ts
  EmptyRow -> Set.empty

newvar :: Monad m => String -> m Type
newvar s = return $ Var s

-- The return here is (Type, Effect, Constraints)
infer :: TypeEnv -> P.Expr -> Infer (Type, Type, [Constraint])
infer env = \case
  -- NOTE (kc): This fails with an error if there is a scoping problem.
  --            This is a bug so it is fine
  Expr.Var name -> do
    assoc_t <- case env !? name of
      Just t -> pure t
      Nothing -> throwError $ InferenceError $ "Type Environment does not contain a type for variable: " ++ name

    -- We throw everything through instantiate.
    t <- instantiate assoc_t
    e <- fresh EVar >>= newvar
    return (t, e, [])
  Expr.Lambda var_name _ expr -> do
    (new_env, u) <- extend env var_name
    (t, e, cst) <- infer new_env expr
    e' <- fresh EVar >>= newvar
    return (Arrow u e t, e', cst)
  Expr.App e1 e2 -> do
    fresh_t <- fresh TVar >>= newvar
    fresh_e <- fresh EVar >>= newvar

    (t_e1, fe, cs_e1) <- infer env e1
    (t_e2, arg_e, cs_e2) <- infer env e2

    let t = Arrow t_e2 fresh_e fresh_t
    let constraints = cs_e1 ++ cs_e2 ++ [Equals (t_e1, t), Equals (fresh_e, fe), Equals (fresh_e, arg_e)]

    return (fresh_t, fresh_e, constraints)
  Expr.Lit x -> do
    fresh_t <- fresh EVar >>= newvar
    return $ case x of
        P.LitInt _ -> (tInt, fresh_t, [])
        P.LitBool _ -> (tBool, fresh_t, [])
  Expr.Let var_name assign body -> do
    -- Generate a type var a for variable name
    (new_env, a) <- extend env var_name
    -- generate type and constraints for the assign expression
    (assign_t, e, assign_cs) <- infer new_env assign

    -- We follow the exmaples in the original paper by Leijen [Type Directed Compilation of Row-Typed Algebraic Effects]
    --  He mentions that requiring the infered effect `e` here to be EmptyRow (in other words assign is total)
    --  Helps ensure soundness of the type system if we want to look into polymorphic reference cells at some point
    --  (which I think we might).
    --
    let result = evalState (runExceptT $ solve $ assign_cs ++ [Equals (e, EmptyRow)]) IdSub

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
    (body_t, body_e, body_cs) <- infer env' body
    assign_t_i <- instantiate assign_t_gen
    let constraints = body_cs ++ assign_cs ++ [Equals (a, assign_t_i)]

    return (body_t, body_e, constraints)
  Expr.If cond tr fl -> do
    (cond_t, cond_e, cond_cs) <- infer env cond
    (tr_t, tr_e, tr_cs) <- infer env tr
    (fl_t, fl_e, fl_cs) <- infer env fl

    -- TODO (kc): Should there be restrictions on the bodies / conditons?
    return (tr_t, EmptyRow, cond_cs ++ tr_cs ++ fl_cs ++ [Equals (tBool, cond_t), Equals (tr_t, fl_t)])
  Expr.BinOp op l r -> do
    (l_t, _, _l_cs) <- infer env l
    (r_t, _, _r_cs) <- infer env r

    -- we are assuming here that our built in binary operations are more or less total and can be used in any
    -- effect context

    let int_cs = (tInt, EmptyRow, [Equals (l_t, tInt), Equals (r_t, tInt)])
    let bool_cs = (tBool, EmptyRow, [Equals (l_t, tBool), Equals (r_t, tBool)])

    return $ case op of
      P.Add -> int_cs
      P.Subtract -> int_cs
      P.And -> bool_cs
      P.Or -> bool_cs
  Expr.Record (RecordExpr.RecordCstr assignments) -> do
    let do_infer (l, e) = do
          result <- infer env e
          return (l, result)

    record_e <- fresh EVar >>= newvar


    c <- mapM do_infer assignments
    let row = foldl (\acc (l, (t, _, _)) -> Row (l, t) acc) EmptyRow c
    let constraints = foldl (\acc (_, (_, row_e, cst)) -> acc ++ cst ++ [Equals(record_e, row_e)]) [] c
    return (Record row, record_e, constraints)
  Expr.Record (RecordExpr.RecordAccess expr label) -> do
    -- A |- e : { l :: T | r }
    -- -----------------------
    --      A |- e.l :: T

    fresht <- fresh TVar >>= newvar
    (expr_t, record_e, c) <- infer env expr
    freshRow <- fresh RVar >>= newvar

    let expected_t = Record $ Row (label, fresht) freshRow

    return (fresht, record_e, c ++ [Equals (expected_t, expr_t)])
  Expr.Record (RecordExpr.RecordExtension base name ext) -> do
    --        A |- e1 : {p}     A |- e2 :: T
    -- --------------------------------------------------
    --      A |- { e1 with l = e2 } : { l :: T | p }
    --
    --  Input : e1, e2, l
    --  Output : T, p

    (base_t, base_e, cl) <- infer env base
    freshRow <- fresh RVar >>= newvar
    (ext_t, ext_e, cr) <- infer env ext

    let result_t = Record (Row (name, ext_t) freshRow)
    let expected_t = Record freshRow

    -- In more general systems this would generate a Lacks l p constraint
    -- With microsofts proposal we have a simplified inference since we allow "scoped" labels
    return (result_t, ext_e, cl ++ cr ++ [Equals (expected_t, base_t), Equals (base_e, ext_e) ])

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
          Arrow t1 e t2 -> Arrow (applyToType (a, b) t1) (applyToType (a, b) e) (applyToType (a, b) t2)
          Record r -> Record (applyToType (a, b) r)
          Row (l, lt) r' -> Row (l, applyToType (a, b) lt) (applyToType (a,b) r')
          _ -> typ

-- TODO (kc): We need to be able to pull out the top level lets here. This will help with some testing
inferType :: P.Expr -> Either TypeError (Type, Type)
inferType expr =
  let env = initialEnv
      infer_except = runExceptT (infer env expr)
      initial_state = InferState {var = 0, row = 0, effect = 0}
   in case evalState infer_except initial_state of
        Left err -> Left err
        Right (t, e, cs) -> -- TODO : Does the e need to be thrown through the substitutions and returned?
          let except = runExceptT (solve cs)
              result = evalState except IdSub
           in case result of
                Left err -> Left err
                Right sub -> Right (apply sub t, apply sub e)

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
          Arrow a e b -> Arrow (substitute a) (substitute e) (substitute b)
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
          (Arrow t11 e1 t12, Arrow t21 e2 t22) -> solve $ cs ++ [Equals (t11, t21), Equals (t12, t22), Equals (e1, e2)]
          (Record (Var p), Record r) -> solve (Equals (Var p, r) : cs)
          (Record r, Record (Var p)) -> solve (Equals (Var p, r) : cs)
          (Record (Row (l, t) r), Record row) -> case toHead row l of
            Row (_, t') r' -> solve $ cs ++ [Equals (t, t'), Equals (Record r, Record r')]
            _ -> throwError $ InferenceError $ "Could not unify rows: " ++ show t1 ++ " and " ++ show t2
          _ -> throwError $ InferenceError $ "Could not unify " ++ show t1 ++ " and " ++ show t2

-- TODO (kc): Need some unit tests
getFreshVarMap :: Set String -> Infer (Map String String)
getFreshVarMap vars = do
  let getValue v = do
        new_var <- fresh TVar
        return (v, new_var)

  Map.fromList <$> mapM getValue (Set.toList vars)

-- TODO (kc): Need some unit tests
instantiate :: Scheme -> Infer Type
instantiate (Forall vars base) = do
  new_vars <- getFreshVarMap vars

  let vs = map (bimap Var Var) $ Map.toList new_vars

  return $ apply (Composed vs) base
