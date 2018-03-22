-- A simple syscall scheme.
--
-- We expect a single import function:
--   dhc.system : I32 -> I32 -> I32 -> ()
-- which expects the syscall number, heap pointer, and stack pointer.

module SoloSyscall (genSyscall, genSyscallFromType) where

import Data.Int
import Boost
import DHC
import WasmOp

sp, hp :: Int
[sp, hp] = [0, 1]

genSyscallFromType :: Int64 -> Type -> (Type, [QuasiWasm])
genSyscallFromType n t = (t, genSyscall (isIO t) n $ fromIntegral $ arityFromType t)

isIO :: Type -> Bool
isIO (_ :-> u) = isIO u
isIO (TC "IO" `TApp` _) = True
isIO _ = False

-- | Generates the WebAssembly for `dhc.system n sp hp` where `n` is the
-- syscall number and `m` is the number of arguments the syscall expects.
-- We evaluate `m` arguments on the heap to WHNF.
-- For pure syscalls we return the result.
-- For impure syscalls we return the tuple (result, #RealWorld).
-- TODO: Get rid of #RealWorld token.
genSyscall :: Bool -> Int64 -> Int64 -> [QuasiWasm]
genSyscall impure svc argCount =
  [ Custom $ ReduceArgs $ fromIntegral argCount
  , I32_const $ fromIntegral svc
  , Get_global sp
  , Get_global hp
  , Custom $ CallSym "dhc.system"
  -- Our convention:
  --   [sp] = result ; [sp - 4] = hp_new
  -- Return (result, #RealWorld).
  ] ++ if impure then
      [ Get_global sp  -- hp = [sp - 4]
      , I32_const 4
      , I32_sub
      , I32_load 2 0
      , Set_global hp
      , Get_global hp  -- [hp] = TagSum | (2 << 8)
      , I32_const $ fromIntegral $ fromEnum TagSum + 256 * 2
      , I32_store 2 0
      , Get_global hp  -- [hp + 4] = 0
      , I32_const 4
      , I32_add
      , I32_const 0
      , I32_store 2 0
      , Get_global hp  -- [hp + 8] = [sp]
      , I32_const 8
      , I32_add
      , Get_global sp
      , I32_load 2 0
      , I32_store 2 0
      , Get_global hp  -- [hp + 12] = 42
      , I32_const 12
      , I32_add
      , I32_const 42
      , I32_store 2 0
      , Get_global sp  -- [sp + 8*argCount + 8] = hp
      , I32_const $ 8*fromIntegral argCount + 8
      , I32_add
      , Get_global hp
      , I32_store 2 0
      , Get_global hp  -- hp = hp + 16
      , I32_const 16
      , I32_add
      , Set_global hp
      , Get_global sp  -- sp = sp + 8*argCount + 4
      , I32_const $ 8*fromIntegral argCount + 4
      , I32_add
      , Set_global sp
      , End
      ]
    else
      [ Get_global sp  -- hp = [sp - 4]
      , I32_const 4
      , I32_sub
      , I32_load 2 0
      , Set_global hp
      -- TODO: Make it lazy with an indirection.
      , Get_global sp  -- [sp + 8*argCount + 4] = [sp]
      , I32_const $ 8*fromIntegral argCount + 4
      , I32_add
      , Get_global sp
      , I32_load 2 0
      , I32_store 2 0
      , Get_global sp  -- sp = sp + 8*argCount
      , I32_const $ 8*fromIntegral argCount
      , I32_add
      , Set_global sp
      , End
      ]
