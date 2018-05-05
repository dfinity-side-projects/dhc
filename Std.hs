module Std (stdBoost) where

import Boost
import DHC
import WasmOp

sp, hp, bp :: Int
[sp, hp, bp] = [0, 1, 2]

stdBoost :: Boost
stdBoost = Boost
  -- No Wasm Imports
  []
  -- Prelude functions.
  (unlines
  [ "data Bool = False | True"
  , "data Maybe a = Nothing | Just a"
  , "data Either a b = Left a | Right b"
  , "fst p = case p of (x, y) -> x"
  , "snd p = case p of (x, y) -> y"
  , "f . g = \\x -> f (g x)"
  , "flip f = \\x y -> f y x"
  , "fromJust m = case m of {Just x -> x}"
  -- TODO: Add `class` and `instance` keywords to clean up the following:
  , "maybe_pure x = Just x"
  , "maybe_monad x f = case x of { Nothing -> Nothing; Just a -> f a }"
  , "io_pure x rw = (x, rw)"
  , "io_monad f g rw = let {p = f rw} in case p of (a, rw1) -> g a rw1"
  , "f >> g = f >>= \\_ -> g"
  , "list_eq_instance d a b = case a of { [] -> case b of {[] -> True; w -> False}; (x:xs) -> case b of { [] -> False; (y:ys)-> (d x y) && list_eq_instance d xs ys } }"
  , "bool f t b = case b of {False -> f; True ->t}"
  , "when b t = bool (pure ()) t b"
  , "f $ x = f x"
  , "id x = x"
  ])
  -- Haskell functions defined in wasm.
  [ ("+", (TC "Int" :-> TC "Int" :-> TC "Int", intAsm I64_add))
  , ("-", (TC "Int" :-> TC "Int" :-> TC "Int", intAsm I64_sub))
  , ("*", (TC "Int" :-> TC "Int" :-> TC "Int", intAsm I64_mul))
  , ("div", (TC "Int" :-> TC "Int" :-> TC "Int", intAsm I64_div_s))
  , ("mod", (TC "Int" :-> TC "Int" :-> TC "Int", intAsm I64_rem_s))
  , ("<", (TC "Int" :-> TC "Int" :-> TC "Bool", cmpAsm I64_lt_s))
  , (">", (TC "Int" :-> TC "Int" :-> TC "Bool", cmpAsm I64_gt_s))
  , ("<=", (TC "Int" :-> TC "Int" :-> TC "Bool", cmpAsm I64_le_s))
  , (">=", (TC "Int" :-> TC "Int" :-> TC "Bool", cmpAsm I64_ge_s))
  , ("&&", (TC "Bool" :-> TC "Bool" :-> TC "Bool", boolAsm I32_and))
  , ("||", (TC "Bool" :-> TC "Bool" :-> TC "Bool", boolAsm I32_or))
  , ("++", (TC "String" :-> TC "String" :-> TC "String", catAsm))
  , ("slice", (TC "Int" :-> TC "String" :-> TApp (TC "()") (TApp (TC "String") (TC "String")), sliceAsm))
  , ("undefined", (a, [Unreachable, End]))

  -- Programmers cannot call the following directly.
  -- We keep their types around for various checks.
  , ("Int-==", (TC "Int" :-> TC "Int" :-> TC "Bool", cmpAsm I64_eq))
  , ("String-==", (TC "String" :-> TC "String" :-> TC "Bool", strEqAsm))
  ]
  -- Internal wasm helpers.
  [ ("#memcpyhp", (([I32, I32], []), memcpyhpAsm))
  , ("#notmemcmp", (([I32, I32, I32], [I32]), notmemcmpAsm))
  ]
  where
    a = GV "a"

intAsm :: QuasiWasm -> [QuasiWasm]
intAsm op =
  [ Custom $ ReduceArgs 2
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_load 2 4
  , I64_load 3 8
  , Get_global sp  -- sp = sp + 8
  , I32_const 8
  , I32_add
  , Set_global sp
  , Get_global sp  -- PUSH [[sp] + 8]
  , I32_load 2 0
  , I64_load 3 8
  , op
  , Custom $ CallSym "#pushint"
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
cmpAsm :: QuasiWasm -> [QuasiWasm]
cmpAsm op =
  [ Custom $ ReduceArgs 2
  , Get_global hp  -- [hp] = TagSum
  , tag_const TagSum
  , I32_store 2 0
  -- [hp + 4] = [[sp + 4] + 8] == [[sp + 8] + 8]
  , Get_global hp  -- PUSH hp
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_load 2 4
  , I64_load 3 8
  , Get_global sp  -- PUSH [[sp + 8] + 8]
  , I32_load 2 8
  , I64_load 3 8
  , op
  , I32_store 2 4
  , Get_global sp  -- [sp + 8] = hp
  , Get_global hp
  , I32_store 2 8
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
boolAsm :: QuasiWasm -> [QuasiWasm]
boolAsm op =
  [ Custom $ ReduceArgs 2
  , Get_global hp  -- [hp] = TagSum
  , tag_const TagSum
  , I32_store 2 0
  -- [hp + 4] = [[sp + 4] + 4] `op` [[sp + 8] + 4]
  , Get_global hp
  , Get_global sp
  , I32_load 2 4
  , I32_load 2 4
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 4
  , op
  , I32_store 2 4
  , Get_global sp  -- [sp + 8] = hp
  , Get_global hp
  , I32_store 2 8
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
catAsm :: [QuasiWasm]
catAsm =
  [ Custom $ ReduceArgs 2
  , Get_global sp  -- PUSH sp
  , Get_global hp  -- PUSH hp
  , Get_global hp  -- [hp] = TagString
  , tag_const TagString
  , I32_store 2 0
  , Get_global hp -- [hp + 4] = hp + 16
  , Get_global hp
  , I32_const 16
  , I32_add
  , I32_store 2 4
  , Get_global hp -- [hp + 8] = 0
  , I32_const 0
  , I32_store 2 8
  , Get_global hp -- [hp + 12] = [[sp + 4] + 12] + [[sp + 8] + 12]
  , Get_global sp
  , I32_load 2 4
  , I32_load 2 12
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 12
  , I32_add
  , I32_store 2 12
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , Get_global sp  -- memcpyhp ([[sp + 4] + 4] + [[sp + 4] + 8]) [[sp + 4] + 12]
  , I32_load 2 4
  , I32_load 2 4
  , Get_global sp
  , I32_load 2 4
  , I32_load 2 8
  , I32_add
  , Get_global sp
  , I32_load 2 4
  , I32_load 2 12
  , Custom$ CallSym "#memcpyhp"
  , Get_global sp  -- memcpyhp ([[sp + 8] + 4] + [[sp + 8] + 8]) [[sp + 8] + 12]
  , I32_load 2 8
  , I32_load 2 4
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 8
  , I32_add
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 12
  , Custom $ CallSym "#memcpyhp"
  , I32_store 2 8  -- [sp + 8] = old_hp  ; Via POPs.
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , I32_const 0  -- Align hp.
  , Get_global hp
  , I32_sub
  , I32_const 3
  , I32_and
  , Get_global hp
  , I32_add
  , Set_global hp
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
memcpyhpAsm :: [QuasiWasm]
memcpyhpAsm =
  [ Loop Nada  -- while (local1 != 0) {
    [ Get_local 1
    , I32_eqz
    , Br_if 1
    , Get_local 1  -- local1 = local1 - 1
    , I32_const 1
    , I32_sub
    , Set_local 1
    , Get_global hp  -- [hp].8 = [local0].8
    , Get_local 0
    , I32_load8_u 0 0
    , I32_store8 0 0
    , Get_local 0  -- local0 = local0 + 1
    , I32_const 1
    , I32_add
    , Set_local 0
    , Get_global hp  -- hp = hp + 1
    , I32_const 1
    , I32_add
    , Set_global hp
    , Br 0
    ]
  , End
  ]
strEqAsm :: [QuasiWasm]
strEqAsm =
  [ Custom $ ReduceArgs 2
  , Get_global sp  -- PUSH sp
  , Get_global hp  -- PUSH hp
  , Get_global hp  -- [hp] = TagSum
  , tag_const TagSum
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = 0
  , I32_const 0
  , I32_store 2 4
  , Get_global sp  -- bp = [[sp + 4] + 12]
  , I32_load 2 4
  , I32_load 2 12
  , Set_global bp

  , Block Nada
    [ Get_global sp  -- if bp /= [[sp + 8] + 12] then break
    , I32_load 2 8
    , I32_load 2 12
    , Get_global bp
    , I32_ne
    , Br_if 0

    , Get_global hp  -- PUSH hp
    , Get_global sp  -- notmemcmp ([[sp + 4] + 4] + [[sp + 4] + 8]) ([[sp + 8] + 4] + [[sp + 8] + 8]) bp
    , I32_load 2 4
    , I32_load 2 4
    , Get_global sp
    , I32_load 2 4
    , I32_load 2 8
    , I32_add
    , Get_global sp
    , I32_load 2 8
    , I32_load 2 4
    , Get_global sp
    , I32_load 2 8
    , I32_load 2 8
    , I32_add
    , Get_global bp
    , Custom $ CallSym "#notmemcmp"
    , I32_store 2 4  -- [hp + 4] = result  ; Via POP.
    ]
  , I32_store 2 8  -- [sp + 8] = old_hp  ; Via POPs.
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
notmemcmpAsm :: [QuasiWasm]
notmemcmpAsm =
  [ Loop Nada  -- while (local2 != 0) {
    [ Get_local 2
    , I32_eqz
    , If Nada [ I32_const 1 , Return ] []
    , Get_local 2  -- local2 = local2 - 1
    , I32_const 1
    , I32_sub
    , Set_local 2
    , Get_local 0  -- [local0].8 /= [local1].8 ?
    , I32_load8_u 0 0
    , Get_local 1
    , I32_load8_u 0 0
    , I32_ne
    , If Nada [ I32_const 0 , Return ] []
    , Get_local 0  -- local0 = local0 + 1
    , I32_const 1
    , I32_add
    , Set_local 0
    , Get_local 1  -- local1 = local1 + 1
    , I32_const 1
    , I32_add
    , Set_local 1
    , Br 0
    ]
  , Unreachable
  , End
  ]
sliceAsm :: [QuasiWasm]
sliceAsm =
  [ Custom $ ReduceArgs 2
  -- TODO: Handle lengths out of range.
  , Get_global sp  -- bp = [[sp + 4] + 8]
  , I32_load 2 4
  , I32_load 2 8
  , Set_global bp
  , Get_global hp  -- [hp] = TagSum | (2 << 8)
  , I32_const $ fromIntegral $ fromEnum TagSum + 256 * 2
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = 0
  , I32_const 0
  , I32_store 2 4
  , Get_global hp  -- [hp + 8] = hp + 16
  , Get_global hp
  , I32_const 16
  , I32_add
  , I32_store 2 8
  , Get_global hp  -- [hp + 12] = hp + 32
  , Get_global hp
  , I32_const 32
  , I32_add
  , I32_store 2 12
  , Get_global hp  -- [hp + 16] = TagString
  , tag_const TagString
  , I32_store 2 16
  , Get_global hp  -- [hp + 20] = [[sp + 8] + 4]
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 4
  , I32_store 2 20
  , Get_global hp  -- [hp + 24] = [[sp + 8] + 8]
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 8
  , I32_store 2 24
  , Get_global hp  -- [hp + 28] = bp
  , Get_global bp
  , I32_store 2 28
  , Get_global hp  -- [hp + 32] = TagString
  , tag_const TagString
  , I32_store 2 32
  , Get_global hp  -- [hp + 36] = [[sp + 8] + 4]
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 4
  , I32_store 2 36
  , Get_global hp  -- [hp + 40] = [[sp + 8] + 8] + bp
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 8
  , Get_global bp
  , I32_add
  , I32_store 2 40
  , Get_global hp  -- [hp + 44] = [[sp + 8] + 12] - bp
  , Get_global sp
  , I32_load 2 8
  , I32_load 2 12
  , Get_global bp
  , I32_sub
  , I32_store 2 44
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global sp  -- [sp + 4] = hp
  , Get_global hp
  , I32_store 2 4
  , Get_global hp  -- hp = hp + 48
  , I32_const 48
  , I32_add
  , Set_global hp
  , I32_const 12  -- UpdatePopEval 2
  , Custom $ CallSym "#updatepopeval"
  , End
  ]
