{- HLINT ignore "Use newtype instead of data" -} -- TODO (kc): Turning this off until we start implementing new Constraints
module Type.Inference
  ( TypeEnv,
    Type (Int, Bool, Var, Arrow, Scheme),
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
import Report (Report(..))

enableTrace :: Bool
enableTrace = False

traceM :: (Applicative f) => String -> f ()
traceM message = when enableTrace $ Tr.traceM message

--- Basic Types
data Type = Int | Bool | Var String | Arrow Type Type | Scheme (Set Type) Type
  deriving (Show, Ord, Eq)

instance Report Type where
  prettyPrint t =
    case t of
      Int -> "Int"
      Bool -> "Bool"
      Var name -> name
      Arrow d r -> prettyPrint d ++ " -> " ++ prettyPrint r
      Scheme vars typ -> "forall " ++ show (Set.toList vars) ++ " . " ++ prettyPrint typ

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
  deriving (Show)

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

-- Inference needs to keep track of fresh ids for type variables to generate constraints
type Infer a = ExceptT TypeError (State Int) a

-- Unification
type Unify a = ExceptT TypeError (State Substitution) a

-- | Run an inference computation with a starting state for fresh vars
runInfer :: Infer a -> Int -> Either TypeError a
runInfer m = evalState (runExceptT m)

nextFreshVar :: Infer String
nextFreshVar = do
  n <- get
  let a = n + 1
  _ <- put a
  return $ "v" ++ show a

extendWithVar :: TypeEnv -> String -> Infer (TypeEnv, Type)
extendWithVar env name = do
  cur <- get

  let n = cur + 1
      t = Var ("v" ++ show n)
      new_env = Map.insert name t env
  put n
  return (new_env, t)

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

    name <- nextFreshVar
    let fresh = Var name
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

generalize :: Type -> Type
generalize t = case t of
  Arrow _ _ -> Scheme (freeVars t) t
  _ -> t

initialEnv :: TypeEnv
initialEnv = Map.fromList [("binary", binaryType)]

-- TODO (kc): This needs some tests.
apply :: Substitution -> Type -> Type
apply sub t = case sub of
  IdSub -> t
  Composed [] -> t
  Single (a, b) -> apply_sub (a, b) t
  Composed cs -> foldr apply_sub t cs
  where
    apply_sub (a, b) typ
      | typ == a = b
      | otherwise = case typ of
          Arrow t1 t2 -> Arrow (apply_sub (a, b) t1) (apply_sub (a, b) t2)
          _ -> typ

-- TODO (kc): We need to be able to pull out the top level lets here. This will help with some testing
inferType :: Expr -> Either TypeError Type
inferType expr =
  let env = initialEnv
      infer_except = runExceptT (infer env expr)
   in -- Tr.trace ("\n\n" ++ show cs ++ "\n\n") $
      case evalState infer_except 0 of
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

(-->) :: Type -> Type -> Constraint -> Constraint
(-->) t1 t2 (Equals (ta, tb)) = Equals (substitute ta, substitute tb)
  where
    substitute typ
      | typ == t1 = t2
      | otherwise = case typ of
          Arrow a b -> Arrow (substitute a) (substitute b)
          _ -> typ
(-->) _t1 _t2 _ = error "TODO: Only equality constraints are defined so far"

(->>) :: Type -> Type -> [Constraint] -> [Constraint]
(->>) t1 t2 = map (t1 --> t2)

solve :: [Constraint] -> Unify Substitution
solve [] = return IdSub
solve (c: cs) =
  case c of
    Equals (t1, t2) -> if t1 == t2
      then solve cs
      else case (t1, t2) of
        (Var _, t)
          | t1 `notElem` freeVars t ->
              solve (t1 ->> t2 $ cs) >>= \s -> return $ s <> Single (t1, t2)
        (t, Var _)
          | t2 `notElem` freeVars t ->
              solve (t2 ->> t1 $ cs) >>= \s -> return $ s <> Single (t2, t1)
        (Arrow t11 t12, Arrow t21 t22) -> solve $ cs ++ [Equals (t11, t21), Equals (t12, t22)]
        _ -> throwError $ InferenceError $ "Could not unify " ++ show t1 ++ " and " ++ show t2
    _ -> throwError $ InferenceError $ "TODO: Implement solver for non equality constraint " ++ show c

-- TODO (kc): Need some unit tests
getFreshVarMap :: Set Type -> Infer (Map Type Type)
getFreshVarMap vars = do
  let getValue v = do
        new_var <- nextFreshVar
        return (v, Var new_var)

  Map.fromList <$> mapM getValue (Set.toList vars)

-- TODO (kc): Need some unit tests
instantiate :: Type -> Infer Type
instantiate (Scheme vars base) = do
  new_vars <- getFreshVarMap vars

  return $ apply (Composed $ Map.toList new_vars) base
instantiate t = pure t
