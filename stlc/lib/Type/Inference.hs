module Type.Inference (
    TypeEnv,
    Type (Int, Bool, Var, Arrow, Scheme),
    TypeError,
    Substitution (Single, Composed),
    Infer,
    instantiate,
    -- unify,
    generalize,
    -- w,
    freeVars,
    inferType,
    emptyEnv,
) where

import Parser (Expr, Literal(LitBool, LitInt), Op(Add, Subtract , Or, And))
import Parser qualified as Expr (Expr (..))
import Control.Monad (when)
import Control.Monad.State
import Control.Monad.Except
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Map qualified as Map
import Data.Map(Map, (!))
import Debug.Trace qualified as Tr

enableTrace :: Bool
enableTrace = False

traceM :: Applicative f => String -> f ()
traceM message = when enableTrace $ Tr.traceM message

--- Basic Types
data Type = Int | Bool | Var String | Arrow Type Type | Scheme (Set Type) Type
    deriving (Show, Ord, Eq)

data TypeError =
    InferenceError String |
    InvalidType String |
    UnificationError String
    deriving (Show)

{- Represents that two types should be equal -}
type Constraint = (Type, Type)

{- | A substitution.
 - We make this a Monoid to more easily handling [Substitution] -> Substituion through composing Substitutions
-}
data Substitution = IdSub | Single (Type, Type) | Composed [(Type, Type)]
    deriving (Show)

instance Semigroup Substitution where
  (<>) :: Substitution -> Substitution -> Substitution
  (<>) IdSub s = s
  (<>) s IdSub = s
  (<>) (Single s1) (Single s2) = Composed (s1:[s2])
  (<>) (Single s1) (Composed rest) = Composed (s1:rest)
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
        new_env =  Map.insert name t env
    put  n
    return  (new_env, t)

-- The type of some binary function
binaryType :: Type
binaryType = Scheme (Set.fromList [Var "binary_var"]) ( Arrow t_var (Arrow t_var t_var))
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
        -- We throw everything through instantiate.
        t <- instantiate $ env ! name
        return (t, [])

    Expr.Lambda var_name _ expr -> do
        -- Tr.traceM $ "LAMBDA EXPR :: " ++ prettyPrint (Expr.Lambda var_name Nothing expr)
        (new_env, u) <- extendWithVar env var_name
        -- Tr.traceM $ "LAMBDA PARAM :: " ++ var_name ++ " : " ++ prettyPrintType u
        (t, cst) <- infer new_env expr
        -- Tr.traceM $ "LAMBDA BODY :: " ++ prettyPrint expr ++ " : " ++ prettyPrintType t
        -- Tr.traceM $ "LAMBDA INFERED TYPE :: " ++ prettyPrintType (Arrow u t)
        return (Arrow u t, cst)

    Expr.App e1 e2 -> do

        --Tr.traceM $ "APP EXPR : " ++ prettyPrint (Expr.App e1 e2)
        (t_e1, cs_e1) <- infer env e1
        -- Tr.traceM $ "APP FUNC : " ++ prettyPrint e1 ++ " : " ++ prettyPrintType t_e1
        (t_e2, cs_e2) <- infer env e2
        -- Tr.traceM $ "APP ARG : " ++ prettyPrint e2 ++ " : " ++ prettyPrintType t_e2

        name <- nextFreshVar
        let fresh = Var name
        let t = Arrow t_e2 fresh

        -- Tr.traceM $ "APP FRESH VAR : " ++ name
        -- Tr.traceM $ "APP EXPECTED FUNCTION TYPE : " ++ prettyPrintType t

        let constraints = cs_e1 ++ cs_e2 ++ [(t_e1, t)]

        -- Tr.traceM $ "APP CONSTRAINTS : " ++ show constraints

        return (fresh, constraints)

    Expr.Lit x -> return $ case x of
                    LitInt _ -> (Int, [])
                    LitBool _ -> (Bool, [])

    Expr.Let var_name assign body -> do
            -- Tr.traceM "\n\n"
            -- Tr.traceM $ "LET EXPR :: " ++ prettyPrint (Expr.Let var_name assign body)
            -- Generate a type var a for variable name
            (new_env, a) <- extendWithVar env var_name
            -- Tr.traceM $ "LET VAR TYPE :: " ++ var_name ++ " : " ++ prettyPrintType a
            -- generate type and constraints for the assign expression
            (assign_t, assign_cs) <- infer new_env assign
            -- Tr.traceM $ "LET ASSIGN MONO TYPE :: " ++ prettyPrint assign ++ " : "  ++ prettyPrintType assign_t

            -- -- Tr.traceM $ "\nCONSTRAINTS\n" ++ show assign_cs
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
                        Tr.traceM "Error occureed while solving constraints\n"
                        Tr.traceM $ show env
                        Tr.traceM $ "LET VAR :: " ++ var_name ++ " : " ++ prettyPrintType assign_t
                        Tr.traceM $ show assign_cs


                        throwError err
                    Right s -> return $ generalize $ apply s assign_t
            -- Tr.traceM $ "LET ASSIGN POLY TYPE :: " ++ prettyPrint assign ++ " : "  ++ prettyPrintType assign_t_gen

            -- add the type scheme to the environment
            let env' = Map.insert var_name assign_t_gen new_env
            -- generate type and constraints for body
            -- Tr.traceM $ "LET BODY EXPR : " ++ prettyPrint body
            (body_t, body_cs) <- infer env' body
            -- Tr.traceM $ "LET BODY TYPE : " ++ prettyPrintType body_t

            -- Tr.traceM $ "LET FINAL_TYPE : " ++ prettyPrintType body_t

            -- Tr.traceM $ "LET CONSTRAINTS : " ++ show  body_t
            let constraints = body_cs ++ assign_cs ++ [(a, assign_t_gen)]

            return (body_t, constraints)


    Expr.If cond tr fl -> do
        (cond_t, cond_cs) <- infer env cond
        (tr_t, tr_cs) <- infer env tr
        (fl_t, fl_cs) <- infer env fl

        return (tr_t, cond_cs ++ tr_cs ++ fl_cs ++ [(Bool, cond_t), (tr_t, fl_t)])

    Expr.BinOp op l r -> do
        (l_t, l_cs) <- infer env l
        (r_t, r_cs) <- infer env r

        let int_cs =(Int, [(l_t, Int),(r_t, Int)])
        let bool_cs =(Bool, [(l_t, Bool), (r_t, Bool)])

        return $ case op of
                Add -> int_cs
                Subtract -> int_cs
                And -> bool_cs
                Or -> bool_cs


-- | Implementation of Algorithm W for hindley milner type inference.
-- >>> evalState (runExceptT (w (Map.insert "a" Int initialEnv) (Expr.Var "a"))) 0
-- Right (IdSub,Int)
-- w :: TypeEnv -> Expr -> Infer (Substitution, Type)
-- w env (Expr.Var name) =  fmap (IdSub, ) $ liftMaybe (InferenceError ("Could not find type for term " ++ show name)) (env !? name)
--
-- w env (Expr.Lambda var_name _ expr) = do
--     (new_env, u) <- extendWithVar env var_name
--     traceM $ "\nNEW_ENV :\n" ++ prettyPrintEnv new_env
--     (s, t) <- w new_env expr
--     traceM $ "TYPED " ++ prettyPrint expr ++ " : " ++ prettyPrintType t
--     return $ (s, Arrow (apply s u) t)
--
--
-- w env (Expr.App e1 e2) = do
--     (s1, t1) <- w env e1 -- Get the type of e1
--
--     let new_env = Map.map (apply s1) env -- Apply the substitution determined by getting the type of e1 to the environment
--     (s2, t2) <- w new_env e2 -- Get the type of e2 with the new environment
--
--     f <- nextFreshVar
--     let fresh = Var f
--     it2 <- instantiate t2
--
--     let arrow_t = Arrow it2 fresh -- We want to create a type t2 -> u :: A type that takes something of type t2 to some new type u
--
--     it1 <- instantiate t1
--     let s = s1 <> s2
--     let f_t1 = apply s it1 -- Instantiate the types and apply any substitutions to t1
--     let f_arrow_t = apply s arrow_t -- NOTE(kc): Probably don't need this
--
--     s3 <- (unify f_t1 f_arrow_t) >>= liftMaybe (UnificationError ("Could not unify " ++ show f_t1 ++ " and " ++ show f_arrow_t)) -- Then we try and unify t1 and t2 -> u
--     let ss = s3 <> s
--
--     return $ (ss , apply ss fresh)
--
-- w _ (Expr.Lit x) = do
--     let lit_type = case x of
--             LitBool _ -> Bool
--             LitInt _ -> Int
--     return $ (IdSub, lit_type)
--
-- w env (Expr.Let var_name e1 e2) = do
--     (new_env, a) <- extendWithVar env var_name
--     traceM $ "\nLET ASSIGNMENT VAR :: " ++ show a
--     (s1, t1) <- w new_env e1
--     traceM $ "LET ASSIGNMENT " ++ prettyPrint e1 ++ " :: " ++ prettyPrintType t1
--
--     let gen_t1 = generalize t1
--     inst_t1 <- instantiate t1
--     s2 <- (unify inst_t1 (apply s1 a)) >>= handleUnificationError ("Could not unify " ++ show inst_t1 ++ " and " ++ show a)
--
--     let subed_te = Map.map (apply (s2 <> s1)) new_env
--     let te_with_var = Map.insert var_name gen_t1 subed_te
--     (s3, t3) <- w te_with_var e2
--
--     return $ (s3 <> s2 <> s1, generalize t3)
--
-- w env (Expr.BinOp op e1 e2) = do
--     let desugared = Expr.App (Expr.App (Expr.Var "binary") e1) e2
--     let expected_t = case op of
--             Add -> Int
--             Subtract -> Int
--             And -> Bool
--             Or -> Bool
--
--     (s1, t1) <- w env e1
--     (s2, t2) <- w (Map.map (apply s1) env) e2
--     let s = s1 <> s2
--
--     s3 <- (unify (apply s t1) expected_t) >>= handleUnificationError ("Could not unify " ++ show t1 ++ " and " ++ show expected_t)
--     s4 <- (unify (apply s t2) expected_t) >>= handleUnificationError ("Could not unify " ++ show t2 ++ " and " ++ show expected_t)
--
--     let s' = s4 <> s3 <> s
--
--     (s5, t) <- w (Map.map (apply s') env) desugared
--     let s'' = s5 <> s'
--
--     s6 <- (unify (apply s t) expected_t) >>= handleUnificationError  "Could not unify"
--     return $ (s6 <> s'', expected_t)
--
-- w env (Expr.If ec et ef) = do
--     (s0, tc) <- w env ec
--     !_ <- traceM $ "IF CONDITION :: " ++ show tc
--     s1 <- (unify tc Bool) >>= handleUnificationError "Type of conditional must unify with Bool"
--     !_ <- traceM $ "IF CONDITION BOOL SUBSTITUTION = " ++ show s1
--     let te = Map.map (apply s1) env
--     (s2, t1) <- w te et
--     (s3, t2) <- w te ef
--
--     i1 <- instantiate t1
--     i2 <- instantiate t2
--
--     s4 <- (unify (apply s3 i1) (apply s3 i2)) >>= handleUnificationError "Invalid Type"
--
--     return $ (s4 <> s3 <> s2 <> s1 <> s0, t2)


-- unify :: Type -> Type -> Infer (Maybe Substitution)
-- unify t1 t2 = do
--     case (t1, t2) of
--         (Int, Int) -> do return $ Just IdSub
--
--         (Bool, Bool) -> do return $ Just IdSub
--
--         (Var n1, Var n2) -> do
--             fresh_var <- nextFreshVar
--             let s1 = createSub (Var n1) fresh_var
--             let s2 = createSub (Var n2) fresh_var
--
--             return $ Just $ s1 <> s2
--
--         (t, Var x) -> if not (x `elem` freeVars t)
--             then return $ Just $ createSub t x
--             else return $ Nothing
--
--         (Var x, t) -> if not (x `elem` freeVars t)
--             then return $ Just $ createSub t x
--             else return $ Nothing
--
--         (Arrow t11 t12, Arrow t21 t22) -> do
--             ms1 <- unify t11 t21
--             case ms1 of
--                 Nothing -> return Nothing
--                 Just s1 -> do
--                     ms2 <- unify (apply s1 t12) (apply s1 t22)
--                     return $ fmap (s1 <>) ms2
--
--         _ -> return  Nothing


generalize :: Type -> Type
generalize t = case t of
    Arrow _ _ -> Scheme (freeVars t) t
    _ -> t

--liftEither :: Monad m => Either e a -> ExceptT e m a
--liftEither = ExceptT . return

-- liftMaybe :: MonadError e m => e -> Maybe a -> m a
-- liftMaybe err = maybe (throwError err) return

-- handleResult :: MonadError e m => Either e a -> m a
-- handleResult = either throwError return


-- handleUnificationError :: MonadError TypeError m => String -> Maybe a -> m a
-- handleUnificationError err = liftMaybe (UnificationError err)

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
        apply_sub (a,b) typ
            | typ == a = b
            | otherwise = case typ of
                    Arrow t1 t2 -> Arrow (apply_sub (a, b) t1) (apply_sub (a, b) t2)
                    _ -> typ



-- TODO (kc): We need to be able to pull out the top level lets here. This will help with some testing
inferType :: Expr -> Either TypeError Type
inferType expr =
    let
        env = initialEnv
        infer_except = runExceptT (infer env expr)
    in
        -- Tr.trace ("\n\n" ++ show cs ++ "\n\n") $
        case evalState infer_except 0 of
            Left err -> Left err
            Right (t, cs) -> let
                                except = runExceptT (solve cs)
                                result = evalState except IdSub
                             in
                                case result of
                                    Left e -> Left e
                                    Right sub -> Right $ apply sub t


prettyPrint :: Expr -> String
prettyPrint = \case
    Expr.Var name -> show name
    Expr.Lambda name _ body -> "\\" ++ name ++ " -> " ++ prettyPrint body
    Expr.App e1 e2 -> "( " ++ prettyPrint e1 ++ " ) ( " ++ prettyPrint e2 ++ " )"
    Expr.BinOp op left right -> "( " ++ prettyPrint left ++ " ) " ++ opStr ++ " ( " ++ prettyPrint right ++ " )"
        where
            opStr = case op of
                Add -> "+"
                Subtract -> "-"
                And -> "&&"
                Or -> "||"
    Expr.If cond tru fls -> "If " ++ prettyPrint cond ++ " then " ++ prettyPrint tru ++ " else " ++ prettyPrint fls
    Expr.Let var assign body -> "let " ++ var ++ " = " ++ prettyPrint assign ++ "\nin\n\t" ++ prettyPrint body
    Expr.Lit lit -> show lit

prettyPrintEnv :: TypeEnv -> String
prettyPrintEnv env =
    let
        newline = "\n"
        printPair name typ = name ++ " >> " ++ prettyPrintType typ
        ln = Prelude.map (uncurry printPair) (Map.toList env)
        folder a s = a ++ newline ++ s
    in
        if Map.null env
            then ""
            else foldl' folder (head ln) (tail ln)

prettyPrintSub :: Substitution -> String
prettyPrintSub IdSub = ""
prettyPrintSub (Single (a,b)) = prettyPrintType a ++ " |-> " ++ prettyPrintType b
prettyPrintSub (Composed elems) = "SUB: \n\t" ++ prettyPrintElements ++ "\n"
    where
        prettyPrintElements = foldr (\t a -> a ++ printMap t ++ "\n\t") "" elems
        printMap (s, u) = show s ++ " |-> " ++ show u

prettyPrintType :: Type -> String
prettyPrintType = \case
    Var name -> show name
    Arrow a b -> "(" ++ prettyPrintType a ++ ") -> (" ++ prettyPrintType b ++ ")"
    Scheme vars t -> "forall " ++ var_list ++ ". " ++ prettyPrintType t
        where
            list_folder a b = a ++ ", " ++ b
            vs = map show $ Set.elems vars
            var_list = if Set.null vars
                then ""
                else foldl' list_folder (head vs) (tail vs)
    t -> show t

{- NOTE (kc):
 - These substitutions will get big and this is inefficient
 -
 - Note: If a variable V1 -> T and V2 -> T then we can think of V1 and V2 as being in the same connected component represented as T.
 -      In our graph of types every connected component will be represented by a Primitive type (or maybe a scheme?).
 -      So to not make this suck we will want to use a union find algorithm here which will reduce the number of rewrites necessary
 -}

(-->) :: Type -> Type -> (Type, Type) -> (Type, Type)
(-->) t1 t2 (ta, tb) = (substitute ta, substitute tb)
    where
        substitute typ
            | typ == t1 = t2
            | otherwise = case typ of
                Arrow a b -> Arrow (substitute a) (substitute b)
                _ -> typ

(->>) :: Type -> Type -> [Constraint] -> [Constraint]
(->>) t1 t2 = map (t1 --> t2)


solve :: [Constraint] -> Unify Substitution
solve [] = return IdSub
solve ((t1, t2):cs) =
    if t1 == t2
        then solve cs
    else case (t1, t2) of
        (Var _, t) | t1 `notElem` freeVars t ->
            solve (t1 ->> t2 $ cs) >>= \s -> return $ s <> Single (t1, t2)
        (t, Var _) | t2 `notElem` freeVars t ->
            solve (t2 ->> t1 $ cs) >>= \s -> return $ s <> Single (t2, t1)
        (Arrow t11 t12, Arrow t21 t22) -> solve $ cs ++ [(t11, t21), (t12, t22)]
        _ ->  throwError $ InferenceError $ "Could not unify " ++ show t1 ++ " and " ++ show t2


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

