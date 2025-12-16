module FullPrograms (full_programs) where

full_programs :: [(String, String)]
full_programs =
    [ ("polymorphic function used for multiple types", unlines [
            "let id = \\x -> x\n",
            "let a = id 5\n",
            "let b = if (id True) then (id 10) else (id 20)\n",
            "let c = id False"
        ])
    , ("nested poymorphic let bindings", "\n\
        \let f = \\x -> x\n\
        \let g = \\y -> f y\n\
        \let h = \\z -> g z\n\
        \let test1 = h 42\n\
        \let test2 = h True\n"
      )
    , ("apply polymorphic argument to function", unlines [
        "let apply = \\f -> \\x -> f x\n",
        "let id = \\y -> y\n",
        "let result = (apply id) 5"
      ])
    , ("church boolean encodings", unlines [
        "let ctrue = \\a -> \\b -> a\n",
        "let cfalse = \\a -> \\b -> b\n",
        "let and = \\a -> \\b -> a b cfalse\n",
        "let final = and ctrue cfalse"

      ])
    , ("flip function", unlines [
        "let flip = \\f -> \\x -> \\y ->  f y x;",
        "let sub = \\a -> \\b -> a - b\n",
        "let flipped_sub = flip sub\n",
        "let final = flipped_sub 5 10"
      ])
    , ("test apply function", unlines [
            "let apply = \\f -> \\x -> f x;",
            "let id = \\y -> y;",
            "let result = (apply id) 5"
      ])
    , ("test const function", unlines [
        "let const = \\f -> \\x -> f \n",
        "let s = const 42\n",
        "let result1 = s true\n",
        "let result1 = s false\n"
      ])
    , ("test three-level composition", unlines [
        "let compose = \\f -> \\g -> \\h -> \\x -> f ( g (h x) )",
        "let inc = \\n -> n + 1\n",
        "let final = compos3 inc inc inc"
      ])
    , ("nested conditionals with polymorphism", unlines [
        "let id = \\x -> x\n",
        "let choose = \\b -> if b then id else id\n",
        "let f = choose True\n",
        "let final = f 42"
      ])
    ]
