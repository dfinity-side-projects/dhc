-- DHC Boost that provides 2 functions:
--
--   putStr :: String -> IO ()
--   putInt :: Int -> IO ()
--
-- and expects the host to provide 2 syscalls:
--
--  system.putStr (pointer : I32, length : I32) -> ()
--  system.putInt (n : I64) -> ()
--
-- The JavaScript edition expects a variant of system.putInt:
--
--  system.putInt (lo : I32, hi : I32) -> ()
module Demo (demoBoost, jsDemoBoost) where

import Ast
import Boost
import WasmOp

sp :: Int
sp = 0

demoBoost :: Boost
demoBoost = Boost
  [ (("system", "putStr"), ([I32, I32], []))
  , (("system", "putInt"), ([I64], []))
  ]
  []
  [ ("putStr", (TC "String" :-> io (TC "()"), putStrAsm))
  , ("putInt", (TC "Int" :-> io (TC "()"),
    [ Custom $ ReduceArgs 1
    , Get_global sp  -- system.putInt [[sp + 4] + 8].64
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I64_load 3 0
    , Custom $ CallSym "system.putInt"
    , Get_global sp  -- sp = sp + 12
    , I32_const 12
    , I32_add
    , Set_global sp
    , Custom $ CallSym "#nil42"
    , End
    ]))
  ]
  []
  where io = TApp (TC "IO")

-- The JavaScript edition of the host splits an int64 into low and high 32-bit
-- words, since current JavaScript engines lack support for 64-bit integers.
jsDemoBoost :: Boost
jsDemoBoost = Boost
  [ (("system", "putStr"), ([I32, I32], []))
  , (("system", "putInt"), ([I32, I32], []))
  ]
  []
  [ ("putStr", (TC "String" :-> io (TC "()"), putStrAsm))
  , ("putInt", (TC "Int" :-> io (TC "()"),
    [ Custom $ ReduceArgs 1
    , Get_global sp  -- system.putInt [[sp + 4] + 8] [[sp + 4] + 12]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I32_load 2 0
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 12
    , I32_add
    , I32_load 2 0
    , Custom $ CallSym "system.putInt"
    , Get_global sp  -- sp = sp + 12
    , I32_const 12
    , I32_add
    , Set_global sp
    , Custom $ CallSym "#nil42"
    , End
    ]))
  ]
  []
  where io = TApp (TC "IO")

putStrAsm :: [QuasiWasm]
putStrAsm =
  [ Custom $ ReduceArgs 1
  , Get_global sp  -- system.putStr ([[sp + 4] + 4] [[sp + 4] + 8]) [[sp + 4] + 12]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Get_global sp
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_add
  , Get_global sp
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 12
  , I32_add
  , I32_load 2 0
  , Custom $ CallSym "system.putStr"
  , Get_global sp  -- sp = sp + 12
  , I32_const 12
  , I32_add
  , Set_global sp
  , Custom $ CallSym "#nil42"
  , End
  ]
