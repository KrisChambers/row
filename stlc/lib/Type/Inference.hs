module Type.Inference (
    TypeEnv,
    Type (Int, Bool, Var, Arrow, Scheme),
    TypeError,
    Substitution (Single, Composed),
    Infer,
    instantiate,
    unify,
    generalize,
    w,
    free_vars,
    infer_type,
    emptyEnv
) where

import Parser (Expr, Literal(LitBool, LitInt), Op(Add, Subtract , Or, And))
import Parser qualified as Expr (Expr (..))
import Control.Monad.State
import Control.Monad.Except
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Map qualified as Map
import Data.Map(Map, (!?))
import Debug.Trace qualified as Tr

enableTrace :: Bool
enableTrace = True

traceM :: Applicative f => String -> f ()
traceM message = if enableTrace then Tr.traceM message else pure ()

data Type = Int | Bool | Var String | Arrow Type Type | Scheme (Set String) Type
    deriving (Show, Ord, Eq)

data TypeError =
    InferenceError String |
    InvalidType String |
    UnificationError String
    deriving (Show)

{- | A substitution.
 - We make this a Monoid to more easily handling [Substitution] -> Substituion through composing Substitutions
-}
data Substitution = IdSub | Single (Type, String) | Composed [Substitution]
    deriving (Show)

instance Semigroup Substitution where
  (<>) :: Substitution -> Substitution -> Substitution
  (<>) IdSub s = s
  (<>) s IdSub = s
  (<>) (Single s1) (Single s2) = Composed ((Single s1):[Single s2])
  (<>) (Single s1) (Composed rest) = Composed ((Single s1): rest)
  (<>) (Composed initial) (Single s1) = Composed (initial ++ [Single s1])
  (<>) (Composed first) (Composed final) = Composed (first ++ final)

instance Monoid Substitution where
  mempty = IdSub

createSub :: Type -> String -> Substitution
createSub t s = Single (t, s)

apply :: Substitution -> Type -> Type
apply IdSub a = a
apply (Single (t, var_name)) a = case a of
    Int -> a
    Bool -> a
    Var name -> if name == var_name
        then t
        else a
    Arrow t1 t2 -> Arrow (apply (Single (t, var_name)) t1) (apply (Single (t, var_name)) t2)
    _ -> a
apply (Composed xs) a = Prelude.foldl (\typ sub -> apply sub typ) a xs

type TypeEnv = Map String Type
emptyEnv :: TypeEnv
emptyEnv = Map.empty

-- Inference needs to keep track of fresh names and the environment
type Infer a = ExceptT TypeError (State Int) a

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

    put $ n
    return $ (new_env, t)

-- The type of some binary function
binaryType :: Type
binaryType = Scheme (Set.fromList ["binary_var"]) ( Arrow t_var (Arrow t_var t_var))
    where
        t_var = Var "binary_var"

free_vars :: Type -> Set String
free_vars t = case t of
    Var a -> Set.fromList [ a ]
    Arrow t1 t2 -> Set.union (free_vars t1) (free_vars t2)
    Scheme vars _ -> vars
    Int -> Set.empty
    Bool -> Set.empty

unify :: Type -> Type -> Infer (Maybe Substitution)
unify t1 t2 = do
    case (t1, t2) of
        (Int, Int) -> do return $ Just IdSub

        (Bool, Bool) -> do return $ Just IdSub

        (Var n1, Var n2) -> do
            fresh_var <- nextFreshVar
            let s1 = createSub (Var n1) fresh_var
            let s2 = createSub (Var n2) fresh_var

            return $ Just $ s1 <> s2

        (t, Var x) -> if not (x `elem` free_vars t)
            then return $ Just $ createSub t x
            else return $ Nothing

        (Var x, t) -> if not (x `elem` free_vars t)
            then return $ Just $ createSub t x
            else return $ Nothing

        (Arrow t11 t12, Arrow t21 t22) -> do
            ms1 <- unify t11 t21
            case ms1 of
                Nothing -> return Nothing
                Just s1 -> do
                    ms2 <- unify (apply s1 t12) (apply s1 t22)
                    return $ fmap (s1 <>) ms2

        _ -> return  Nothing


generalize :: Type -> Type
generalize t = case t of
    Arrow _ _ -> Scheme (free_vars t) t
    _ -> t

--liftEither :: Monad m => Either e a -> ExceptT e m a
--liftEither = ExceptT . return

liftMaybe :: MonadError e m => e -> Maybe a -> m a
liftMaybe err = maybe (throwError err) return

-- handleResult :: MonadError e m => Either e a -> m a
-- handleResult = either throwError return


handleUnificationError :: MonadError TypeError m => String -> Maybe a -> m a
handleUnificationError err = liftMaybe (UnificationError err)

initialEnv :: TypeEnv
initialEnv = Map.fromList [("binary", binaryType)]

-- TODO (kc): We need to be able to pull out the top level lets here.
infer_type :: Expr -> Either TypeError Type
infer_type expr =
    let
        env = initialEnv
        except = runExceptT (w env expr)
        result = evalState except 0
    in
        case result of
            Left e -> Left e
            Right (_, t) -> Right t

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
    Expr.Let var assign body -> "let \n\t" ++ var ++ " = " ++ prettyPrint assign ++ "\nin\n\t" ++ prettyPrint body
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


prettyPrintType :: Type -> String
prettyPrintType = \case
    Var name -> show name
    Arrow a b -> "(" ++ prettyPrintType a ++ ") -> (" ++ prettyPrintType b ++ ")"
    Scheme vars t -> "forall " ++ var_list ++ ". " ++ prettyPrintType t
        where
            list_folder a b = a ++ ", " ++ b
            vs = Set.elems vars
            var_list = if Set.null vars
                then ""
                else foldl' list_folder (head vs) (tail vs)
    t -> show t

-- | Implementation of Algorithm W for hindley milner type inference.
-- >>> evalState (runExceptT (w (Map.insert "a" Int initialEnv) (Expr.Var "a"))) 0
-- Right (IdSub,Int)
w :: TypeEnv -> Expr -> Infer (Substitution, Type)
w env (Expr.Var name) =  fmap (IdSub, ) $ liftMaybe (InferenceError ("Could not find type for term " ++ show name)) (env !? name)

w env (Expr.Lambda var_name _ expr) = do
    (new_env, u) <- extendWithVar env var_name
    traceM $ "\nNEW_ENV :\n" ++ prettyPrintEnv new_env
    (s, t) <- w new_env expr
    traceM $ "TYPED " ++ prettyPrint expr ++ " : " ++ prettyPrintType t
    return $ (s, Arrow (apply s u) t)


w env (Expr.App e1 e2) = do
    (s1, t1) <- w env e1 -- Get the type of e1

    let new_env = Map.map (apply s1) env -- Apply the substitution determined by getting the type of e1 to the environment
    (s2, t2) <- w new_env e2 -- Get the type of e2 with the new environment

    f <- nextFreshVar
    let fresh = Var f
    it2 <- instantiate t2

    let arrow_t = Arrow it2 fresh -- We want to create a type t2 -> u :: A type that takes something of type t2 to some new type u

    it1 <- instantiate t1
    let s = s1 <> s2
    let f_t1 = apply s it1 -- Instantiate the types and apply any substitutions to t1
    let f_arrow_t = apply s arrow_t -- NOTE(kc): Probably don't need this

    s3 <- (unify f_t1 f_arrow_t) >>= liftMaybe (UnificationError ("Could not unify " ++ show f_t1 ++ " and " ++ show f_arrow_t)) -- Then we try and unify t1 and t2 -> u
    let ss = s3 <> s

    return $ (ss , apply ss fresh)

w _ (Expr.Lit x) = do
    let lit_type = case x of
            LitBool _ -> Bool
            LitInt _ -> Int
    return $ (IdSub, lit_type)

w env (Expr.Let var_name e1 e2) = do
    (new_env, a) <- extendWithVar env var_name
    traceM $ "\nLET ASSIGNMENT VAR :: " ++ show a
    (s1, t1) <- w new_env e1
    traceM $ "LET ASSIGNMENT " ++ prettyPrint e1 ++ " :: " ++ prettyPrintType t1

    let gen_t1 = generalize t1
    inst_t1 <- instantiate t1
    s2 <- (unify inst_t1 (apply s1 a)) >>= handleUnificationError ("Could not unify " ++ show inst_t1 ++ " and " ++ show a)

    let subed_te = Map.map (apply (s2 <> s1)) new_env
    let te_with_var = Map.insert var_name gen_t1 subed_te
    (s3, t3) <- w te_with_var e2

    return $ (s3 <> s2 <> s1, generalize t3)

w env (Expr.BinOp op e1 e2) = do
    let desugared = Expr.App (Expr.App (Expr.Var "binary") e1) e2
    let expected_t = case op of
            Add -> Int
            Subtract -> Int
            And -> Bool
            Or -> Bool

    (s1, t1) <- w env e1
    (s2, t2) <- w (Map.map (apply s1) env) e2
    let s = s1 <> s2

    s3 <- (unify (apply s t1) expected_t) >>= handleUnificationError ("Could not unify " ++ show t1 ++ " and " ++ show expected_t)
    s4 <- (unify (apply s t2) expected_t) >>= handleUnificationError ("Could not unify " ++ show t2 ++ " and " ++ show expected_t)

    let s' = s4 <> s3 <> s

    (s5, t) <- w (Map.map (apply s') env) desugared
    let s'' = s5 <> s'

    s6 <- (unify (apply s t) expected_t) >>= handleUnificationError  "Could not unify"
    return $ (s6 <> s'', expected_t)

w env (Expr.If ec et ef) = do
    (s0, tc) <- w env ec
    s1 <- (unify tc Bool) >>= handleUnificationError "Type of conditional must unify with Bool"
    let te = Map.map (apply s1) env
    (s2, t1) <- w te et
    (s3, t2) <- w te ef

    i1 <- instantiate t1
    i2 <- instantiate t2

    s4 <- (unify (apply s3 i1) (apply s3 i2)) >>= handleUnificationError "Invalid Type"

    return $ (s4 <> s3 <> s2 <> s1 <> s0, t2)

getFreshVarMap :: Set String -> Infer (Map String String)
getFreshVarMap vars = do
    let getValue = \v -> do
            new_var <- nextFreshVar
            return $ (new_var, v)

    fmap Map.fromList $ mapM getValue (Set.toList vars)

instantiate :: Type -> Infer Type
instantiate (Scheme vars base) = do
    new_vars <- getFreshVarMap vars
    let s = foldMap (uncurry (createSub.Var)) $ Map.toList new_vars

    return $ apply s base
instantiate t = pure t

