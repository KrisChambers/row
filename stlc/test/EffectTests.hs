module EffectTests (effectTests) where

import Data.Map qualified as Map
import Interpreter (evalExpr)
import Parser
import Test.Tasty
import Test.Tasty.HUnit

-- Put some possible handle syntax idea in here. These may be old if i decided otherwise...

int :: Integer -> Expr
int n = Lit (LitInt n)

unit :: Expr
unit = Lit LitUnit

var :: String -> Expr
var = Var

lam :: String -> Expr -> Expr
lam x body = Lambda x Nothing body

app :: Expr -> Expr -> Expr
app = App

lett :: String -> Expr -> Expr -> Expr
lett = Let

add :: Expr -> Expr -> Expr
add = BinOp Add

perf :: String -> String -> Expr -> Expr
perf = Perform

-- | Build a Handle expression with a return clause and operation clauses.
--
--   @hdl body ("x", retBody) [(("Eff","op"), (["arg"], "k", opBody))]@
hdl :: Expr -> (String, Expr) -> [((String, String), ([String], String, Expr))] -> Expr
hdl body ret ops =
  Handle body $
    Handler
      { retClause = ret
      , opClause = Map.fromList [(key, OpClause args k bdy) | (key, (args, k, bdy)) <- ops]
      }

assertEval :: String -> Expr -> String -> Assertion
assertEval label expr expected =
  case evalExpr expr of
    Right v -> assertEqual label expected (show v)
    Left err -> assertFailure $ label ++ ": " ++ show err

effectTests :: TestTree
effectTests =
  testGroup
    "Effect Evaluation"
    [ returnClauseTests
    , singleEffectTests
    , multipleOperationTests
    , nestedHandlerTests
    , effectPureMixTests
    , stateLikeTests
    ]


returnClauseTests :: TestTree
returnClauseTests =
  testGroup
    "Return clause"
    [ testCase "identity return clause" $ do
        -- handle 42 with | return x -> x
        let expr = hdl (int 42) ("x", var "x") []
        assertEval "identity" expr "42"
    , testCase "return clause transforms value" $ do
        -- handle 42 with | return x -> x + 1
        let expr = hdl (int 42) ("x", add (var "x") (int 1)) []
        assertEval "transform" expr "43"
    , testCase "return clause on boolean" $ do
        -- handle true with | return x -> x
        let expr = hdl (Lit (LitBool True)) ("x", var "x") []
        assertEval "bool" expr "True"
    ]

singleEffectTests :: TestTree
singleEffectTests =
  testGroup
    "Single effect handling"
    [ testCase "handle perform, discard continuation" $ do
        -- handle (perform E.op ()) with | E.op _ k -> 99 | return x -> x
        let expr =
              hdl
                (perf "E" "op" unit)
                ("x", var "x")
                [( ("E", "op"), (["_arg"], "k", int 99) )]
        assertEval "discard k" expr "99"
    , testCase "handle perform, resume with value" $ do
        -- handle (perform E.op ()) with | E.op _ k -> k 10 | return x -> x
        let expr =
              hdl
                (perf "E" "op" unit)
                ("x", var "x")
                [( ("E", "op"), (["_arg"], "k", app (var "k") (int 10)) )]
        assertEval "resume" expr "10"
    , testCase "resume feeds into subsequent computation" $ do
        -- handle (let v = perform E.op () in v + 1) with | E.op _ k -> k 10 | return x -> x
        let expr =
              hdl
                (lett "v" (perf "E" "op" unit) (add (var "v") (int 1)))
                ("x", var "x")
                [( ("E", "op"), (["_arg"], "k", app (var "k") (int 10)) )]
        assertEval "resume + compute" expr "11"
    , testCase "return clause transforms resumed result" $ do
        -- handle (perform E.op ()) with | E.op _ k -> k 10 | return x -> x + 100
        let expr =
              hdl
                (perf "E" "op" unit)
                ("x", add (var "x") (int 100))
                [( ("E", "op"), (["_arg"], "k", app (var "k") (int 10)) )]
        assertEval "resume + return transform" expr "110"
    ]


multipleOperationTests :: TestTree
multipleOperationTests =
  testGroup
    "Multiple operations"
    [ testCase "handler with two distinct operations" $ do
        -- handle (let a = perform E.foo () in let b = perform E.bar () in a + b)
        -- with | E.foo _ k -> k 3 | E.bar _ k -> k 7 | return x -> x
        let expr =
              hdl
                ( lett "a" (perf "E" "foo" unit) $
                    lett "b" (perf "E" "bar" unit) $
                      add (var "a") (var "b")
                )
                ("x", var "x")
                [ (("E", "foo"), (["_arg"], "k", app (var "k") (int 3)))
                , (("E", "bar"), (["_arg"], "k", app (var "k") (int 7)))
                ]
        assertEval "two ops" expr "10"
    , testCase "same operation performed twice" $ do
        -- handle (let a = perform E.op () in let b = perform E.op () in a + b)
        -- with | E.op _ k -> k 5 | return x -> x
        let expr =
              hdl
                ( lett "a" (perf "E" "op" unit) $
                    lett "b" (perf "E" "op" unit) $
                      add (var "a") (var "b")
                )
                ("x", var "x")
                [( ("E", "op"), (["_arg"], "k", app (var "k") (int 5)) )]
        assertEval "twice same op" expr "10"
    ]


nestedHandlerTests :: TestTree
nestedHandlerTests =
  testGroup
    "Nested handlers"
    [ testCase "inner handles A, outer handles B" $ do
        -- handle (
        --   handle (let a = perform A.op () in let b = perform B.op () in a + b)
        --   with | A.op _ k -> k 10 | return x -> x
        -- ) with | B.op _ k -> k 20 | return x -> x
        let inner =
              hdl
                ( lett "a" (perf "A" "op" unit) $
                    lett "b" (perf "B" "op" unit) $
                      add (var "a") (var "b")
                )
                ("x", var "x")
                [(("A", "op"), (["_arg"], "k", app (var "k") (int 10)))]
        let expr =
              hdl
                inner
                ("x", var "x")
                [(("B", "op"), (["_arg"], "k", app (var "k") (int 20)))]
        assertEval "layered A+B" expr "30"
    , testCase "inner handler passes unhandled effect outward" $ do
        -- handle (
        --   handle (perform B.op ())
        --   with | A.op _ k -> k 0 | return x -> x
        -- ) with | B.op _ k -> k 42 | return x -> x
        let inner =
              hdl
                (perf "B" "op" unit)
                ("x", var "x")
                [(("A", "op"), (["_arg"], "k", app (var "k") (int 0)))]
        let expr =
              hdl
                inner
                ("x", var "x")
                [(("B", "op"), (["_arg"], "k", app (var "k") (int 42)))]
        assertEval "passthrough" expr "42"
    , testCase "nested handlers both transform return" $ do
        -- handle (handle 5 with | return x -> x + 10) with | return x -> x + 100
        let inner = hdl (int 5) ("x", add (var "x") (int 10)) []
        let expr = hdl inner ("x", add (var "x") (int 100)) []
        assertEval "nested return transforms" expr "115"
    , testCase "three layers of handlers" $ do
        -- handle (handle (handle
        --   (let a = perform A.op () in
        --    let b = perform B.op () in
        --    let c = perform C.op () in a + b + c)
        --   with | A.op _ k -> k 1 | return x -> x)
        --   with | B.op _ k -> k 2 | return x -> x)
        --   with | C.op _ k -> k 3 | return x -> x
        let body =
              lett "a" (perf "A" "op" unit) $
                lett "b" (perf "B" "op" unit) $
                  lett "c" (perf "C" "op" unit) $
                    add (add (var "a") (var "b")) (var "c")
        let layer1 = hdl body ("x", var "x") [(("A", "op"), (["_"], "k", app (var "k") (int 1)))]
        let layer2 = hdl layer1 ("x", var "x") [(("B", "op"), (["_"], "k", app (var "k") (int 2)))]
        let expr = hdl layer2 ("x", var "x") [(("C", "op"), (["_"], "k", app (var "k") (int 3)))]
        assertEval "three layers" expr "6"
    ]


effectPureMixTests :: TestTree
effectPureMixTests =
  testGroup
    "Effect + pure mix"
    [ testCase "let bindings around handle" $ do
        -- let a = 1 in let b = (handle (perform E.op ()) with | E.op _ k -> k 10 | return x -> x) in a + b
        let handled =
              hdl
                (perf "E" "op" unit)
                ("x", var "x")
                [(("E", "op"), (["_arg"], "k", app (var "k") (int 10)))]
        let expr = lett "a" (int 1) $ lett "b" handled $ add (var "a") (var "b")
        assertEval "let around handle" expr "11"
    , testCase "lambda inside handler body (discard k)" $ do
        -- handle (perform E.op ()) with | E.op _ k -> (\x -> x + 1) 41 | return x -> x
        let expr =
              hdl
                (perf "E" "op" unit)
                ("x", var "x")
                [(("E", "op"), (["_arg"], "k", app (lam "x" (add (var "x") (int 1))) (int 41)))]
        assertEval "lambda in handler" expr "42"
    , testCase "handle pure let-chain" $ do
        -- handle (let a = 1 in let b = 2 in a + b) with | return x -> x + 10
        let expr =
              hdl
                (lett "a" (int 1) $ lett "b" (int 2) $ add (var "a") (var "b"))
                ("x", add (var "x") (int 10))
                []
        assertEval "pure under handler" expr "13"
    ]


stateLikeTests :: TestTree
stateLikeTests =
  testGroup
    "State-like effects"
    [ testCase "state get handler returns value via closure" $ do
        -- The handler for get wraps continuation in a lambda that threads state:
        --   handle (perform S.get ())
        --   with | S.get _ k  -> \s -> (k s) s
        --        | return x   -> \s -> x
        -- Then apply result to initial state 7
        --
        -- Expected: the perform S.get yields the state, return clause wraps it,
        -- final application passes state=7 through
        let expr =
              app
                ( hdl
                    (perf "S" "get" unit)
                    ("x", lam "s" (var "x"))
                    [ ( ("S", "get")
                      , ( ["_arg"]
                        , "k"
                        , lam "s" (app (app (var "k") (var "s")) (var "s"))
                        )
                      )
                    ]
                )
                (int 7)
        assertEval "state get" expr "7"
    , testCase "state set then get" $ do
        -- handle (let _ = perform S.set 10 in perform S.get ())
        -- with | S.get _ k  -> \s -> (k s) s
        --      | S.set v k  -> \s -> (k ()) v
        --      | return x   -> \s -> x
        -- Apply to initial state 0
        let expr =
              app
                ( hdl
                    ( lett "_" (perf "S" "set" (int 10)) $
                        perf "S" "get" unit
                    )
                    ("x", lam "s" (var "x"))
                    [ ( ("S", "get")
                      , ( ["_arg"]
                        , "k"
                        , lam "s" (app (app (var "k") (var "s")) (var "s"))
                        )
                      )
                    , ( ("S", "set")
                      , ( ["v"]
                        , "k"
                        , lam "s" (app (app (var "k") unit) (var "v"))
                        )
                      )
                    ]
                )
                (int 0)
        assertEval "state set then get" expr "10"
    ]
