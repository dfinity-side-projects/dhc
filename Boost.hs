{-# LANGUAGE CPP #-}
module Boost
  ( QuasiWasm
  , QuasiWasmHelper(..)
  , tag_const, Tag(..)
  , Boost(..)
#ifdef __HASTE__
  , (<>)
#endif
  ) where

import Ast
import WasmOp

-- | Data on the heap is 64-bit aligned. The first 8 bits hold a tag.
--
-- The following tables describe the field at a given offset of an object
-- on the heap. All fields are 32 bits wide except the value field of a 64-bit
-- integer type.
--
-- Int64s:
--    0 TagInt
--    8 64-bit value
--
-- Ports:
--    0 TagRef
--    4 32-bit value
--
-- Coproduct (sum) types:
--    0 TagSum | (arity << 8)
--    4 Enum
--    8, 12.. Heap addresses of components.
--
-- Application `f x`:
--    0 TagAp
--    4 Unused
--    8 f
--   12 x
--
-- Global function:
--    0 TagGlobal | (arity << 8)
--    4 Function index
--
-- Indirection:
--    0 TagInd
--    4 Heap address of target
--
-- String:
--    0 TagString
--    4 address
--    8 offset
--    12 length
--
-- For example, `Just 42` is represented by:
--
--   [TagSum, 1, p], where p points to [TagInt, 0, 42]
--
-- where each list item is a 32-bit integer.

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagRef | TagSum | TagString deriving Enum

tag_const :: Tag -> CustomWasmOp a
tag_const = I32_const . fromIntegral . fromEnum

-- | A few helpers for inline assembly.
type QuasiWasm = CustomWasmOp QuasiWasmHelper
data QuasiWasmHelper =
    CallSym String  -- Find function index and call it.
  | ReduceArgs Int  -- Copy arguments from heap and reduce them to WHNF.
  deriving Show

type WasmImport = ((String, String), ([WasmType], [WasmType]))

-- | A Boost is a custom collection of extra declarations and functions that
-- are added to a binary.
data Boost = Boost
  -- Wasm import declarations.
  { boostImports :: [WasmImport]
  -- Haskell definitions.
  , boostPrelude :: String
  -- Primitive Haskell functions.
  , boostPrims :: [(String, (Type, [QuasiWasm]))]
  -- Internal wasm functions, indexed by strings for CallSym.
  , boostWasm :: [(String, (([WasmType], [WasmType]), [QuasiWasm]))]
  }

#ifdef __HASTE__
(<>) :: Boost -> Boost -> Boost
Boost a b c d <> Boost x y z w = Boost (a ++ x) (b ++ y) (c ++ z) (d ++ w)
#else
instance Semigroup Boost where
  Boost a b c d <> Boost x y z w = Boost (a <> x) (b <> y) (c <> z) (d <> w)

instance Monoid Boost where
  mempty = Boost [] [] [] []
  mappend = (<>)
#endif
