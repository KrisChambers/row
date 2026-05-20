module InterpreterTests (interpreterTests) where

import Data.Map ((!?))
import Debug.Trace qualified as Tr
import Interpreter (Env (..), Value (..), eval, evalDecls, fromDecl)
import Parser qualified as P
import Test.Tasty
import Test.Tasty.HUnit

interpreterTests :: TestTree
interpreterTests =
  testGroup
    "Infering Types of Expressions"
    [ envBuilding
    , variantUseTest
    , caseEvaluation
    , binOp
    ]

eList :: P.Decl
eList = P.DataDecl ["a"] "List" [("Nil", []), ("Cons", [P.TVar "a", P.TCon "List" [P.TVar "a"]])]

eMain :: P.Expr -> P.Decl
eMain expr = P.LetDecl "main" Nothing expr

caseEvaluation :: TestTree
caseEvaluation =
  testGroup
    "Flat pattern matching with case statements"
    [ testCase "Simple List [1]" $ do
        let expr =
              eMain $
                P.Case
                  (cons (litInt 1) nil)
                  [ P.CaseArm "Nil" [] (litBool False)
                  , P.CaseArm "Cons" ["value"] (litBool True)
                  ]
        case evalDecls [eList, expr] of
          Left a -> assertFailure $ show a
          Right b -> do
            b @?= RBool True
    , testCase "Longer List [1, 2]" $ do
        let expr =
              eMain $
                P.Case
                  (cons (litInt 1) (cons (litInt 2) nil))
                  [ P.CaseArm "Nil" [] (litBool False)
                  , P.CaseArm "Cons" ["value", "rest"] (P.Var "rest")
                  ]
        case evalDecls [eList, expr] of
          Left a -> assertFailure $ show a
          Right b -> do
            b @?= RVariant "Cons" [RInt 2, RVariant "Nil" []]
    ]
 where
  cons value = P.App (P.App (P.Var "Cons") value)
  nil = P.Var "Nil"
  litInt = P.Lit . P.LitInt
  litBool = P.Lit . P.LitBool

variantUseTest :: TestTree
variantUseTest =
  testGroup
    "Evaluating Variants"
    [ testCase "Simple List [1]" $ do
        let expr = eMain $ P.App (P.App (P.Var "Cons") (P.Lit $ P.LitInt 1)) (P.Var "Nil")

        case evalDecls [eList, expr] of
          Left a -> assertFailure $ show a
          Right b -> do
            b @?= RVariant "Cons" [RInt 1, RVariant "Nil" []]
    ]

envBuilding :: TestTree
envBuilding =
  testGroup
    "Generating an evaluation context from declarations"
    [ testCase "Check main and data constructors exist" $ do
        let env = fromDecl [eMain (P.Lit $ P.LitInt 1), eList]

        let decls = envDecl env
        let vars = envValues env

        let expect name from failMessage = case from !? name of
              Nothing -> assertFailure failMessage
              Just _ -> return ()

        expect "main" decls "Expected main declaration in environment"
        expect "Cons" vars $ "Expected Cons data constructor in environment: \n\n" ++ show vars
    ]

vstr :: String -> P.Expr
vstr s = P.Lit $ P.LitString s

vint :: Integer -> P.Expr
vint i = P.Lit $ P.LitInt i

plus :: P.Expr -> P.Expr -> P.Expr
plus l r = P.BinOp P.Add l r

equals :: P.Expr -> P.Expr -> P.Expr
equals l r = P.BinOp P.Equals l r

binOp :: TestTree
binOp =
  testGroup
    "Evaluating binary operations on values"
    [ testCase "String Equality" $ do
        let expr = eMain $ vstr "S" `equals` vstr "S"

        case evalDecls [expr] of
          Left a -> assertFailure $ show a
          Right b -> do
            b @?= RBool True
    ]
