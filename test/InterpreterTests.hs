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
    ]

eList :: P.Decl
eList = P.DataDecl ["a"] "List" [("Nil", []), ("Cons", [P.TVar "a", P.TCon "List" [P.TVar "a"]])]

eMain :: P.Expr -> P.Decl
eMain expr = P.LetDecl "main" Nothing expr

caseEvaluation :: TestTree
caseEvaluation =
  testGroup
    "Case evaluation Tests"
    [ testCase "Simple List [1]" $ do
        let expr = eMain $ P.Case (P.App (P.App (P.Var "Cons") (P.Lit $ P.LitInt 1)) (P.Var "Nil")) [
                P.CaseArm "Nil" [] (P.Lit $ P.LitBool False), P.CaseArm "Cons" ["value"] (P.Lit $ P.LitBool True)
              ]

        case evalDecls [eList, expr] of
          Left a -> assertFailure $ show a
          Right b -> do
            b @?= RBool True
    ]

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
