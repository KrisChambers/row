{- HLINT ignore "Use newtype instead of data" -}
-- TODO (kc): Turning this off until we start implementing new Constraints
module Type.Inference
  (
    lookupType,
    Type (TCon, Var, Arrow, Record, EmptyRow, Row),
    Scheme (Forall),
    TypeError (..),
    Substitution (IdSub, Single, Composed),
    Constraint (..),
    Infer,
    TypeEnv(..),
    EffectInfo(..),
    TypeInfo(..),
    Kind(..),
    CtorInfo(..),
    prelude,
    infer,
    instantiate,
    instantiateEffectInfo,
    generalize,
    freeVars,
    inferType,
    runInfer,
    toHead,
    solve,
    apply,
    tInt,
    tBool,
    tUnit,
    tString,
    addDeclToEnv,
    inferDecl,
    createCstrInfo
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map, (!?), (!))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Parser qualified as Expr (Expr (..))
import Parser qualified as RecordExpr (RecordExpr (..))
import Parser qualified as P
import Report (Report (..))
import Data.Bifunctor (bimap)
import Debug.Trace qualified as Tr
import Control.Monad (foldM, when)


data Type = Var String | Arrow Type Type Type | Record Type | EmptyRow | Row (String, Type) Type | TCon String [Type]
  deriving (Show, Ord)

data Scheme = Forall (Set String) Type
  deriving (Show, Eq)

data Kind = KType | KArrow Kind Kind
  deriving (Show, Eq)

data TypeInfo = TypeInfo
    -- Ex : Functor a -> ["a"]
  { typeInfoParams :: [String]
    -- *, or * -> *, ?
  , typeInfoKind :: Kind
  }
  deriving (Show)

data EffectInfo = EffectInfo
  { effectInfoParams :: [String]
  , effectInfoOps :: Map String Scheme
  }
  deriving (Show, Eq)


effectScheme :: EffectInfo -> Scheme
effectScheme (EffectInfo params ops) = Forall (Set.fromList params) (Record opsRows)
  where
    opsRows = foldr (\(lbl, Forall _ t) b -> Row (lbl, t) b) EmptyRow (Map.toList ops)

schemeToInfo :: Scheme -> EffectInfo
schemeToInfo (Forall params (Record r)) = EffectInfo
  { effectInfoParams = Set.toList params
  , effectInfoOps = Map.fromList rowOps
  }
  where
    rowOps = toList r
    toList EmptyRow = []
    toList (Row (name, t) r') = (name, Forall params t):(toList r')
    toList _ = error "Oops"
schemeToInfo _ = error "Oops"

instantiateEffectInfo :: EffectInfo -> Infer EffectInfo
instantiateEffectInfo info = do
  let scheme = effectScheme info
  schemeT <- instantiate scheme
  let newInfo = schemeToInfo (Forall mempty schemeT)
  return newInfo

{-
 effect State a {
   get : () -> a
   put : a -> ()
 }

 turns into:

 "State" -> {
   "param" = ["a"],
   "ops" = {
     "get" = forall a. () -> a
     "set" = forall a. a -> ()
   }
  }
-}

-- Contains constructor information.
-- The name of the type the constructor belongs
-- The type scheme for the constructor
data CtorInfo = CtorInfo
  { ctorInfoTypeName :: String
  , ctorInfoScheme :: Scheme
  }
  deriving (Show)

data TypeEnv = TypeEnv
  { envTypes :: Map String TypeInfo
  , envEffects :: Map String EffectInfo
  , envVars :: Map String Scheme
  , envCstors :: Map String CtorInfo
  }

instance Show TypeEnv where
  show t = "\n{" ++ (foldr (\a b -> b ++ "\n" ++ a) "" components) ++ "\n}"
    where
      components = [showTypes, showEffects, showVars, showCstrs]
      showTypes = foldr (\(name, info) b -> b ++ "\n\t" ++ name ++ " : " ++ show info) "\t" (Map.toList $ envTypes t)
      showEffects = foldr (\(name, info) b -> b ++ "\n\t" ++ name ++" : " ++ show info) "\t" (Map.toList $ envEffects t)
      showVars = foldr (\(name, info) b -> b ++ "\n\t" ++ name ++ " : " ++show info) "\t" (Map.toList $ envVars t)
      showCstrs = foldr (\(name, info) b -> b ++ "\n\t" ++ name ++ " : " ++show info) "\t" (Map.toList $ envCstors t)

lookupType :: TypeEnv -> String -> Maybe Scheme
lookupType env varName = Map.lookup varName $ envVars env

extendVars :: TypeEnv -> String -> Scheme -> TypeEnv
extendVars env name scheme = env { envVars = Map.insert name scheme (envVars env) }

extendEffects :: TypeEnv -> String -> EffectInfo -> TypeEnv
extendEffects env name info = env { envEffects = Map.insert name info (envEffects env) }

extendTypes :: TypeEnv -> String -> TypeInfo -> TypeEnv
extendTypes env name info = env { envTypes = Map.insert name info (envTypes env) }

extendCstors :: TypeEnv -> String -> CtorInfo -> TypeEnv
extendCstors env name info = env { envCstors = Map.insert name info (envCstors env) }

{-
  I have confused myself a bit

  For some type X we will have constructors
    XInt Int, XFloat Float, XBool Bool

    Each constructor defines a scheme
    XInt : forall . Int -> X
    XFloat : forall . Float -> X
    XBool : forall . Bool -> X


    So when I encounter a definition:
      data X
        = XInt Int
        | XFloat Float
        | XBool Bool

    Something needs to represent X.
    Currently, I have been treating this as a type constructor, but X is not a type constructor.
    It is a new type in our system, which have constructors that create an instance of it.

    So for this to work something needs to represent X in our types. We have been getting
    away with using something like `TCon "X" []`.


    lang := let myint = XInt 1

    expr := Let "myint" (App (Var "XInt") (Lit 1))

    1. Let "myint"
        1.1 myint : a
        1.2 infer (App "XInt" 1)
          2.1 lookup XInt in variable environment? to get XInt = Int -> X
          2.2 1 : Int
          2.3 App XInt 1 : X


    2.1 :: I think this would be an application of the tagging <l = T> as T?



  Records + Row polymorphism is providing us with Sum Types

  We want Variants as well (tagged unions)

  Ex: data Maybe a = None | Some a

  Subtly this is conflating 2 things.
  1. Variants (the | on the right; Something can be one of these things)
  2. Type Operators (Maybe :: KType => KType)

  Maybe a :: * => * (Ex: Maybe Int :: Int -> Maybe Int, This is type operator application)

  So our context will have term level bindings (some term t has type T)
  and will also have operator bindings (some type variable X has kind K, I think this is our TypeINFO?)

  When looking at a type declaration
  1. Generate TypeInfo := data Maybe a -> TypeInfo ["a"] KArrow KType KType
  2. Generate variant info?


  I think we need to look into what would be reasonable here.
  Restricted Type operator stuff would be nice. It may overlap with how we are doing effects







-}

tBool :: Type
tBool = TCon "Bool" []

tInt :: Type
tInt = TCon "Int" []

tUnit :: Type
tUnit = TCon "()" []

tString :: Type
tString = TCon "String" []

prelude :: TypeEnv
prelude = TypeEnv
  { envTypes = Map.fromList
      [ ("Int", TypeInfo [] KType) -- Note: We are not dealing with higher kinds right now, this seems like it won't be in our way.
      , ("Bool", TypeInfo [] KType)
      , ("String", TypeInfo [] KType)
      , ("()", TypeInfo [] KType)
      ]
  , envEffects = Map.empty
  -- Map.fromList
  --   [ ("Console", EffectInfo [] $ Map.fromList
  --       [ ("print", Forall Set.empty $ Arrow tString eConsole tUnit),
  --         ("read", Forall Set.empty $ Arrow tUnit eConsole tString)
  --       ])
  --   ]
  , envVars = Map.fromList [("()", Forall Set.empty tUnit)]
  , envCstors = Map.fromList
      [ ("True", CtorInfo "Bool" (Forall Set.empty tBool))
      , ("False", CtorInfo "Bool" (Forall Set.empty tBool))
      , ("()", CtorInfo "()" (Forall Set.empty tUnit))
      ]
  }

-- Transform a Syntactic type in an expression to a Type used by inference.
transformType :: String -> [String] -> P.Type -> Type
transformType effectName eparams = \case
  P.TVar name -> Var name
  P.TInt -> tInt
  P.TBool -> tBool
  P.TCon name params -> TCon name $ map (transformType effectName eparams) params
  P.TFun arg rtrn effect -> Arrow (transformType effectName eparams arg) scopeEffect (transformType effectName eparams rtrn)
  P.TRecord row -> Record $ recordRow row
  where
    effectRow = \case
        P.EEmptyRow -> EmptyRow
        P.ERowExtension label eTail -> Row (label, tUnit) $ effectRow eTail
        P.EVar name -> Var name
    recordRow = \case
        P.REmptyRow -> EmptyRow
        P.RRowExtension label t rTail -> Row (label, transformType effectName eparams t) $ recordRow rTail
        P.RVar name -> Var name
    scopeEffect = Row (effectName, transformedParams) EmptyRow
    transformedParams = if length eparams > 0
        then Var "a"
        else tUnit

inferDecl :: [P.Decl] -> Either TypeError TypeEnv
inferDecl ds =
  let inferDecls decls = do
        withEffects <- foldM addDeclToEnv prelude $ effects decls
        foldM addDeclToEnv withEffects $ lets decls
      infer_except = runExceptT (inferDecls ds)
      initial_state = InferState {var = 0, row = 0, effect = 0}
      isEffect = \case
        P.EffectDecl {} -> True
        _ -> False
      effects = filter isEffect
      lets = filter (not . isEffect)
   in evalState infer_except initial_state

addDeclToEnv :: TypeEnv -> P.Decl -> Infer TypeEnv
addDeclToEnv env = \case
    P.LetDecl name t expr -> do
      (new_env, a) <- extend env name
      (tExpr, eExpr, cExpr) <- infer new_env expr
      let constraints = (Equals (a, tExpr)):cExpr

      let result = evalState (runExceptT $ solve constraints) IdSub

      sub <- case result of
            Left err -> do
              throwError $ UnificationError $ "Error unifying " ++ name ++ "\n" ++ prettyPrint expr ++ " :: " ++ show err
            Right s -> return s

      let eExprGen = generalize . apply sub $ tExpr

      -- when ("MyConsole" `isInfixOf` show result) $ do
      --     let tester = generalize(apply sub $ Arrow (Var "v2") (Var "e6") tUnit)
      --     Tr.traceM "\n---- Final ----\n"
      --     Tr.traceM $ show tester
      --     Tr.traceM "\n---- Sub ----\n"
      --     Tr.traceM $ show sub
      --     Tr.traceM "\n---- Before ----\n"
      --     Tr.traceM $ show tExpr
      --     Tr.traceM "\n---- Result ----\n"
      --     Tr.traceM $ show eExprGen

      let env' = extendVars new_env name eExprGen

      return env'
    P.EffectDecl name params ops -> do
      let typedOps = map (\(n, t) -> (n, generalize $ transformType name params t )) ops
      -- when (name == "MyConsole") $ do
      --   Tr.traceM $ "\n"
      --   Tr.traceM $ "\n" ++ show name ++ " : " ++ show ops
      --   Tr.traceM $ "\n\n"
      let info = EffectInfo {
        effectInfoParams = params,
        effectInfoOps = Map.fromList typedOps
      }
      let opVars = map (\(op, scheme) -> (name ++ "." ++ op, scheme)) typedOps
      let new_env = foldr (\(n, scheme) env' -> extendVars env' n scheme) env opVars
      return $ extendEffects new_env name info
    P.DataDecl params name cstrs -> do
      kind <- case length params of
            0 -> do return KType
            1 -> do return $ KArrow KType KType
            _ -> throwError $ InferenceError "Not handling anything beyond * -> *"

      -- Helpers to get Type inference Types (These need different names)
      let mapTypes ts = map (transformType "" []) ts
      let cstrTypes = map (\(cstrName, ts) -> (cstrName, mapTypes ts)) cstrs

      -- This is describing the type on the level of kinds
      let typeInfo = TypeInfo params kind
      let typeCstr = TCon name $ map Var params
      -- Constructors here refer to data constructors (so taking terms to types)
      -- The info has the type scheme of the constructors
      -- For example: Nil for List a would have type forall a. List a. While Cons : forall a. a -> List a -> List a
      let cstorInfo = map (\(cstorName, args) -> (cstorName, CtorInfo name $ createCstrInfo typeCstr args )) cstrTypes

      let new_env = env {
        -- We add the kinding info about the type
        envTypes = Map.insert name typeInfo (envTypes env),
        -- The data constructors are added as terms.
        envVars = foldr (\(cName, (CtorInfo _ b)) acc -> Map.insert cName b acc) (envVars env) cstorInfo,
        -- The constructor metadata information is kept so we can identify the associated type
        envCstors = foldr (\(cName, cInfo) acc -> Map.insert cName cInfo acc) (envCstors env) cstorInfo
      }

      return new_env

createCstrInfo :: Type -> [Type] -> Scheme
createCstrInfo cstredType ts = generalize $ foldr (\tp a -> Arrow tp EmptyRow a) cstredType ts

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
  (==) (Var _) _ = False
  (==) (Arrow {}) _ = False
  (==) (Record _) _ = False
  (==) EmptyRow _ = False
  (==) (TCon {}) _ = False

instance Report Type where
  prettyPrint t =
    case t of
      TCon name params -> name ++ foldr (\a b -> b ++ " " ++ prettyPrint a) "" params
      Var name -> name
      Arrow d e r -> prettyPrint d ++ " -> " ++ prettyPrint r ++ " ! " ++ prettyPrint e
      Record row -> "{" ++ prettyPrint row ++ "}"
      EmptyRow -> ""
      Row (l, lt) rtail -> l ++ label_type ++ separator ++ " " ++ prettyPrint rtail
         where
          label_type = if lt /= tUnit
              then " : " ++ prettyPrint lt
              else ""
          separator = case rtail of
            EmptyRow -> ""
            Var v -> v
            Row {} -> ","
            _ -> "ERROR"


-- instance Report Scheme where
--   prettyPrint (Forall vars t) = "forall " ++ show vars ++ " . " ++ prettyPrint t

data TypeError
  = InferenceError String
  | InvalidType String
  | UnificationError String

instance Show TypeError where
  show (InferenceError s) = s
  show (InvalidType s) = s
  show (UnificationError s) = s

{- Type Constraints -}
data Constraint
  = Equals (Type, Type)
  | Merge Type Type Type
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


extend :: TypeEnv -> String -> Infer (TypeEnv, Type)
extend env name = do
  v <- fresh TVar >>= newvar
--  e <- fresh EVar >>= newvar

  let new_env = Map.insert name (Forall Set.empty v) (envVars env)

  return (env { envVars = new_env },  v)

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

  let getter = case varType of
        TVar -> var
        RVar -> row
        EVar -> effect

  let prefix = case varType of
        TVar -> "v"
        RVar -> "r"
        EVar -> "e"

  let nextVar = do
        n <- gets getter >>= \a -> return $ a + 1
        _ <- puts setV n
        return  n

  n <- nextVar

  return $ prefix ++ show n


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
    {-
      Г, x : T |-
     ───────────── [ VAR ]
      Г |- x : T
    -}
    assoc_t <- case envVars env !? name of
      Just t -> pure t
      Nothing -> throwError $ InferenceError $ "Type Environment does not contain a type for variable: " ++ name

    -- We throw everything through instantiate.
    t <- instantiate assoc_t
    e <- fresh EVar >>= newvar
    return (t, e, [])

  Expr.Lambda var_name _ expr -> do
    {-
      Г |- x : T1   Г |- e : T2
     ────────────────────────── [ ABS ]
        Г |- \x. e : T1 -> T2
    -}
    (new_env, u) <- extend env var_name
    (t, e, cst) <- infer new_env expr
    e' <- fresh EVar >>= newvar
    return (Arrow u e t, e', cst)

  Expr.App e1 e2 -> do
    {-
      Г |- e1 : T1 -> T   Г |- e2 : T1
     ────────────────────────────────── [ APP ]
              Г |- e1 e2 : T
    -}
    fresh_t <- fresh TVar >>= newvar
    fresh_e <- fresh EVar >>= newvar

    (t_e1, fe, cs_e1) <- infer env e1
    (t_e2, arg_e, cs_e2) <- infer env e2
    let t = Arrow t_e2 fresh_e fresh_t
    let constraints = cs_e1 ++ cs_e2 ++ [Equals (t_e1, t), Equals (fresh_e, fe), Equals (fresh_e, arg_e)]

    -- when ("MyConsole" `isInfixOf` show e1) $ do
    --   let remainingWidth value minL = if length value < minL
    --         then minL - (length value)
    --         else minL
    --   let getSpaces value = take paddingSize $ repeat ' '
    --         where paddingSize = remainingWidth value 20
    --   let ppMap m = Map.foldrWithKey (\k v s -> s ++ k ++ (getSpaces k) ++ ":= " ++  show v ++ "\n" ) "" m
    --   let sep name = "\n----" ++ insert ++ "--\n"
    --         where insert = case name of
    --                 "" -> ""
    --                 x -> " " ++ x ++ " "

    --   Tr.traceM $ sep "ENV" ++ ppMap (envVars env)
    --   Tr.traceM $ sep "VARS" ++ show e1 ++ " : " ++ show t_e1
    --   Tr.traceM $ show e2 ++ " : " ++ show t_e2 ++ sep ""
    --   Tr.traceM $ sep "CONSTRAINTS" ++ show constraints

    return (fresh_t, fresh_e, constraints)
  Expr.Lit x -> do
    fresh_t <- fresh EVar >>= newvar
    return $ case x of
        P.LitInt _ -> (tInt, fresh_t, [])
        P.LitBool _ -> (tBool, fresh_t, [])
        P.LitString _ -> (tString, fresh_t, [])
        P.LitUnit -> (tUnit, fresh_t, [])
  Expr.Let var_name assign body -> do
    {-
      Г |- [x -> e1]e2 : T    Г |- e1 : T1
     ─────────────────────────────────────── [ LETPOLY ]
            Г |- let x = e1 in e2 : T
    -}
    e_result <- fresh EVar >>= newvar

    -- Generate a type var a for variable name
    (new_env, a) <- extend env var_name
    -- generate type and constraints for the assign expression
    (assign_t, assign_e, assign_cs) <- infer new_env assign

    -- We follow the examples in the paper by Leijen [Type Directed Compilation of Row-Typed Algebraic Effects]
    --  He mentions that requiring the infered effect `e` here to be EmptyRow (in other words assign is total)
    --  Helps ensure soundness of the type system if we want to look into polymorphic reference cells at some point.
    --  So why not.
    --
    --  Note.. We need to think about this a little bit..
    --    The way of doing effects seems to be to deal with sequential computations. At least that seems kind of implicit in their design.
    --    In a typical let name = expr in ... name is generalized.
    --      Requiring everything in a let assignment have effect < > would mean that we can only generalize over total functions.
    --      The paper outlines an Open / Close type operation that may be useful to consider for simplifying types
    --        This effectively makes all total functions able to be "opened" to accept any thing
    --


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
     - This seems pretty standard and keeps constraint generation under control
    -}

    -- generalize the let binding
    assign_t_gen <- case result of
      Left err -> do
        throwError err
      Right s -> return $ generalize $ apply s assign_t

    -- TODO: I think that this effectively overwrites the extension of var_name set to a
    -- add the type scheme to the environment
    let env' = new_env { envVars = Map.insert var_name assign_t_gen (envVars new_env) }
    -- generate type and constraints for body
    (body_t, body_e, body_cs) <- infer env' body
    assign_t_i <- instantiate assign_t_gen
    let constraints = body_cs ++ assign_cs ++ [Equals (a, assign_t_i), Equals(e_result, body_e), Equals(e_result, assign_e)]


    return (body_t, e_result, constraints)
  Expr.If cond tr fl -> do
    {-
     Г |- f : T   Г |- t : T   Г |- b : Bool
    ──────────────────────────────────────────  [ IF ]
            Г |- if b then t else f
    -}
    (cond_t, cond_e, cond_cs) <- infer env cond
    (tr_t, tr_e, tr_cs) <- infer env tr
    (fl_t, fl_e, fl_cs) <- infer env fl

    -- TODO (kc): Should there be restrictions on the bodies / conditons?
    return (tr_t, EmptyRow, cond_cs ++ tr_cs ++ fl_cs ++ [Equals (tBool, cond_t), Equals (tr_t, fl_t)])
  Expr.BinOp op l r -> do
    (l_t, l_e, _l_cs) <- infer env l
    (r_t, r_e, _r_cs) <- infer env r

    result_e <- fresh EVar >>= newvar

    -- we are assuming here that our built in binary operations are more or less total and can be used in any
    -- effect context

    let eCst = [ Equals (l_e, result_e), Equals (r_e, result_e)]

    let int_cs = (tInt, result_e, [Equals (l_t, tInt), Equals (r_t, tInt)] ++ eCst)
    let bool_cs = (tBool, result_e, [Equals (l_t, tBool), Equals (r_t, tBool)] ++ eCst)
    --return (binT, l_e, c)

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
    let constraints = foldl (\acc (_, (_, row_e, cst)) -> acc ++ cst ++ [Equals (record_e, row_e)]) [] c
    return (Record row, record_e, constraints)
  Expr.Record (RecordExpr.RecordAccess expr label) -> do
    {-
        Г |- e : { l : T | r }
    ──────────────────────────────  [ RCRD-SELECT ]
           Г |- e.l : T
    -}

    fresht <- fresh TVar >>= newvar
    (expr_t, record_e, c) <- infer env expr
    freshRow <- fresh RVar >>= newvar

    let expected_t = Record $ Row (label, fresht) freshRow

    return (fresht, record_e, c ++ [Equals (expected_t, expr_t)])
  Expr.Record (RecordExpr.RecordExtension base name ext) -> do
    {-
                Г |- e1 : { p }    Г |- e2 : T
    ────────────────────────────────────────────────────  [ RCRD-EXTD ]
           Г |- { e1 with l = e2 } : { l : T | p }

      INPUT : e1, e2, l
      OUTPUT : T, p
    -}


    (base_t, base_e, cl) <- infer env base
    freshRow <- fresh RVar >>= newvar
    (ext_t, ext_e, cr) <- infer env ext

    let result_t = Record (Row (name, ext_t) freshRow)
    let expected_t = Record freshRow

    -- In more general systems this would generate a Lacks l p constraint
    -- With microsofts results we have a simplified inference since we allow "scoped" labels
    return (result_t, ext_e, cl ++ cr ++ [Equals (expected_t, base_t), Equals (base_e, ext_e) ])

  Expr.Perform effect op arg  -> do
    {-
        Σ |- E  ? I think this is really just application...
    ────────────────────────────────────────────────────  [ PERFORM ]
                   Г |- perform E.op : T ! E
    -}
    -- effectInfo <- case envEffects env !? effect of
    --       Nothing -> throwError $ InferenceError $ "Key " ++ effect ++ " is not an effect"
    --       Just a -> return a
    let name = effect ++ "." ++ op
    let appExpr = Expr.App (Expr.Var name) arg
    e_result <- fresh EVar >>= newvar

    -- (new_env, op_t) <- extend env name

    (t, e, cs) <- infer env appExpr

    -- defined_type <- case effectInfoOps effectInfo !? op of
    --       Nothing -> throwError $ InferenceError $ "Could not find op " ++ op
    --       Just s -> instantiate s

    return (t, e_result, (Equals(e, e_result):cs))

     -- opType <- instantiate (effectInfoOps effectInfo ! op)

     -- fresh_t <- fresh TVar >>= newvar
     -- fresh_e <- fresh EVar >>= newvar
     -- -- At this point we are just throwing an error if there is no effect info

     -- (tArg, eArg, cArg) <- infer env arg

     -- let t = Arrow tArg fresh_e fresh_t

     -- -- I think this needs to be something like
     -- -- (tArg, eArg, cArg) <- infer env arg
     -- -- We need a constraint here that says opType = tArg -> {fresh_e} fresh_t?
     -- -- effect on the arrow, args, resulting effect, all need to be the same?
     -- -- I think perform is just a special application?

     -- eTail <- fresh EVar >>= newvar

     -- let effect_t = Row (effect, tUnit) eTail
     -- let effect_c = [
     --         Equals (t, opType),-- opType should be a functin type
     --         Equals (fresh_e, eArg), -- Effect of the args matches fresh, which will match effect of opType based on how we construct t
     --         Equals (fresh_e, effect_t) -- This is the resulting effect
     --       ]

     -- return (fresh_t, effect_t, cArg ++ effect_c)
  Expr.Handle expr hdlr -> do
    {-
        Γ ⊢ e : A ! (| Op | E |)                                                    -- the expresion is of type A with effect rows containng Op
        Γ, x : A, e_ret : C ! E                                                     --
        Γ, x_op : T_in, k_op : (T_out → C ! E) ⊢ e_op : C ! E                       -- Every op in the effect has the same result Type. There is something off here with k
      ───────────────────────────────────────────────────────────────────────────
        Γ ⊢ handle e with { return x -> e_ret, Op(x_op,k_op) -> e_op } : C ! E
    -}

    -- First we need to infer what the computation type is we are handling.
    (bodyT, bodyE, bodyC) <- infer env expr

    -- This is the resulting type of the handler
    resultT <- fresh TVar >>= newvar

    -- This is the rest of the effect rows. We want (| Op | hdlrRest |)
    -- This should also be the resulting effect
    hdlrRest <- fresh EVar >>= newvar

    let (retVar, retExpr) = P.retClause hdlr
    (env', retVarT) <- extend env retVar
    (retT, retE, retC) <- infer env' retExpr

    let return_constraints = (Equals (retVarT, bodyT)):retC -- type of x is Int

    --let aaa = envEffects env
    --let info = aaa ! "MyState"
    --let ops = effectInfoOps info
    --let getS = ops ! "get"

    ---- Need to generate constraints for the arguments and return type based on the schema for handler operations
    ---- Ex: get : () -> a  Needs to be instantiated with a type variable va



    opsC <- getOpConstraints env (Map.elems $ P.opClause hdlr)

    let type_constraints = foldr (++) [] $ map (\(t,e,cs) -> cs ++ [Equals (t, resultT), Equals(e, hdlrRest)]) opsC
    let effect_constraints = []

    return (resultT, hdlrRest, bodyC ++ return_constraints ++ type_constraints ++ effect_constraints ++ [Equals (retT, resultT), Equals (retE, hdlrRest)])

prettyPrintList :: Show a => [a] -> String
prettyPrintList xs = foldr (\x agg -> agg ++ "\n\t," ++ show x) "[" xs

getOpConstraints :: TypeEnv -> [P.OpClause] -> Infer [(Type, Type, [Constraint])]
getOpConstraints _ [] = return []
getOpConstraints env (c:cs) = do
    x <- getClauseConstraints env c
    xs <- getOpConstraints env cs

    return $ x:xs

getClauseConstraints :: TypeEnv -> P.OpClause -> Infer (Type, Type, [Constraint])
getClauseConstraints env (P.OpClause args k body) = do
    argT <- fresh TVar >>= newvar
    resT <- fresh TVar >>= newvar
    effect <- fresh EVar >>= newvar
    let kT = Arrow argT effect resT

    let extendMany envv ps = case ps of
          ((n, t): xs) -> extendMany (extendVars envv n (Forall Set.empty t)) xs
          [] -> envv

    argsT <- mapM (\s -> (s,) <$> (fresh TVar >>= newvar)) args


    let env' = extendMany env ((k, kT):argsT)

    infer env' body

    {-
  Γ ⊢ e : A ! {Op} ∪ E
  Γ, x:A ⊢ e_ret : C ! E
  Γ, x:T_in, k:(T_out → C ! E) ⊢ e_op : C ! E
  ─────────────────────────────────────────────
  Γ ⊢ with e { return x→e_ret, Op(x,k)→e_op } : C ! E

  output: C and E
  input: e, ops...

  fresh return_type -- The output of the handler needs to be consistent across op clauses.

  infer e -> A ! <r1> (r is an effect row variable)
      constraint r1 = <Op | r2>

  infer return_body -> C ! a
      constraint return_type = C
      constraint a = r2

  for each op clause
    1. find it's definition's type : ex: get : () -> a
    2. infer each arg x and constrain the type to be = the positional param type from the defintion?
    3. infer the continuation type, constrain to be a function a -> return_type ! r2
     -}



    -- for each operation clause
    --    the type of the args match that of the effect operation
    --    the type of the continuation is a function k: OutputOfOperation -> output of handler?
    --    The body must have the handler's result type C



    -- Need to look at the OpClauses in b to get the effects
    -- b is essentially a special arrow type except it is removing things..?
    -- This should remove the effect that is being handled.



generalize :: Type -> Scheme
generalize t = Forall vars closed_t
  where
    closed_t = closeType t
    vars = case t of
      Arrow {} -> freeVars closed_t
      _ -> Set.empty

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

-- TODO (kc): Needs to change to provide some sort of LetDecl -> Type map?
inferType :: P.Expr -> Either TypeError (Type, Type)
inferType expr =
  let env = prelude -- initialEnv
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
(-->) t1 t2 constraint = case constraint of
    (Equals (ta, tb)) -> Equals (substitute ta, substitute tb)
    (Merge r1 r2 r3) -> Merge (substitute r1) (substitute r2) (substitute r3)
  where
    substitute typ
      | typ == t1 = t2
      | otherwise = case typ of
          Arrow a e b -> Arrow (substitute a) (substitute e) (substitute b)
          Row (l, t) r' -> Row (l, substitute t) (substitute r')
          Record a -> Record $ substitute a
          _ -> typ

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
          (Record a, Record b) -> solve (Equals (a, b):cs)
          --(Record (Var p), Record r) -> solve (Equals (Var p, r) : cs)
          --(Record r, Record (Var p)) -> solve (Equals (Var p, r) : cs)
          (Row (l, t) r, row) -> case toHead row l of
                Row (_, t') r' -> solve $ cs ++ [Equals (t, t'), Equals(r, r')]
                _ -> throwError $ InferenceError $ "Could not unify rows: " ++ prettyPrint t1 ++ " and " ++ prettyPrint t2
          _ -> throwError $ InferenceError $ "Could not unify " ++ prettyPrint t1 ++ " and " ++ prettyPrint t2
    Merge rLeft rRight rFinal -> do
        -- We need to deal with the merge constraint after other constraints
        -- This is mainly since if rLeft and rRight are variables then we need to solve them first
        s <- solve cs
        let
          rLeftT = apply s rLeft
          rRightT = apply s rRight

        if rLeftT == EmptyRow
          then solve $ cs ++ [Equals (rFinal, rRightT)]
        else if rRightT == EmptyRow
          then solve $ cs ++ [Equals (rFinal, rLeftT)]
        else case mergeRow rLeftT rRightT of
          Left err -> throwError err
          Right merged -> solve $ cs ++ [Equals (rFinal, merged)]

mergeRow :: Type -> Type -> Either TypeError Type
mergeRow r1 r2 = case (r1, r2) of
  (Row l rt, r) -> do
    rowTail <- mergeRow rt r
    return $ Row l rowTail
  (Var _, Row l rt) -> do
    rowTail <- mergeRow r1 rt
    return $ Row l rowTail
  (EmptyRow, r) -> Right r
  (r, EmptyRow) -> Right r
  (Var _, Var _) -> Left . UnificationError $ "Can not merge two open rows"
  (a, b) -> Left . UnificationError $ "Can only merge rows not (" ++ show a ++ ", " ++ show b ++ ")"

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

  let instantiated = apply (Composed vs) base

  openType instantiated

openType :: Type -> Infer Type
openType = \case
  EmptyRow -> fresh EVar >>= newvar
  Row s next -> openType next >>= \new -> return $ Row s new
  Arrow t1 e t2 -> openType e >>= \new -> return $ Arrow t1 new t2
  -- Record r -> openType r >>= \new -> return $ Record new
  t -> return t

closeType :: Type -> Type
closeType = \case
  Var name | (head name) == 'e' -> EmptyRow
  Row s (Var _) -> Row s EmptyRow
  Arrow t1 e t2 -> Arrow t1 (closeType e) t2
  -- Record r -> Record $ closeType r
  t -> t


