{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Asm (wasm, typedAstToBin, compileMk1, Ins(..)) where
import Control.Arrow
import qualified Data.Map as M
#ifdef __HASTE__
import "mtl" Control.Monad.State
import qualified Data.ByteString as SBS
#else
import Control.Monad.State
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
#endif
import Data.Char
import Data.Int
import Data.List
import Data.Maybe

import DHC hiding (Call, Type)
import WasmOp

#ifdef __HASTE__
type ShortByteString = SBS.ByteString
#endif

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal String
  | PushString ShortByteString
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePop Int | UpdateInd Int | Alloc Int
  | Casejump [(Maybe Int, [Ins])] | Trap deriving Show

nPages :: Int
nPages = 8

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
--    4 length
--    8 bytes
--
-- For example, `Just 42` is represented by:
--
--   [TagSum, 1, p], where p points to [TagInt, 0, 42]
--
-- where each list item is a 32-bit integer.
--
-- Globals are resolved in a giant `br_table`. This is ugly, but avoids
-- run-time type-checking.

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagSum | TagString deriving Enum

encWasmOp :: WasmOp -> [Int]
encWasmOp op = case op of
  Get_local n -> 0x20 : leb128 n
  Set_local n -> 0x21 : leb128 n
  Tee_local n -> 0x22 : leb128 n
  Get_global n -> 0x23 : leb128 n
  Set_global n -> 0x24 : leb128 n
  I64_const n -> 0x42 : sleb128 n
  I32_const n -> 0x41 : sleb128 n
  Call n -> 0x10 : leb128 n
  I64_load m n -> [0x29, m, n]
  I64_store m n -> [0x37, m, n]
  I32_load m n -> [0x28, m, n]
  I32_load8_u m n -> [0x2d, m, n]
  I32_load16_u m n -> [0x2f, m, n]
  I32_store m n -> [0x36, m, n]
  I32_store8 m n -> [0x3a, m, n]
  Br n -> 0xc : leb128 n
  Br_if n -> 0xd : leb128 n
  Br_table bs a -> 0xe : leb128 (length bs) ++ concatMap leb128 (bs ++ [a])
  If _ as -> [0x4, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  Block _ as -> [2, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  Loop _ as -> [3, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  _ -> maybe (error $ "unsupported: " ++ show op) pure $ lookup op rZeroOps

intAsm :: WasmOp -> [WasmOp]
intAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
  [ Get_global hp  -- [hp] = TagInt
  , tag_const TagInt
  , I32_store 2 0
  -- [hp + 8] = [[sp + 4] + 8] `op` [[sp + 8] + 8]
  , Get_global hp  -- PUSH hp + 8
  , I32_const 8
  , I32_add
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , Get_global sp  -- PUSH [[sp + 8] + 8]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , op
  , I64_store 3 0
  , Get_global sp  -- [sp + 8] = hp
  , I32_const 8
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

cmpAsm :: WasmOp -> [WasmOp]
cmpAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
  [ Get_global hp  -- [hp] = TagSum
  , tag_const TagSum
  , I32_store 2 0
  -- [hp + 4] = [[sp + 4] + 8] == [[sp + 8] + 8]
  , Get_global hp  -- PUSH hp + 4
  , I32_const 4
  , I32_add
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , Get_global sp  -- PUSH [[sp + 8] + 8]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , op
  , I32_store 2 0
  , Get_global sp  -- [sp + 8] = hp
  , I32_const 8
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

boolAsm :: WasmOp -> [WasmOp]
boolAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
  [ Get_global hp  -- [hp] = TagSum
  , tag_const TagSum
  , I32_store 2 0
  -- [hp + 4] = [[sp + 4] + 4] `op` [[sp + 8] + 4]
  , Get_global hp
  , I32_const 4
  , I32_add
  , Get_global sp
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Get_global sp
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , op
  , I32_store 2 0
  , Get_global sp  -- [sp + 8] = hp
  , I32_const 8
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

catAsm :: [WasmOp]
catAsm = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
  [ Get_global sp  -- PUSH sp + 8
  , I32_const 8
  , I32_add
  , Get_global hp  -- PUSH hp
  , Get_global hp  -- [hp] = TagString
  , tag_const TagString
  , I32_store 2 0

  , Get_global hp -- [hp + 4] = [[sp + 4] + 4] + [[sp + 8] + 4]
  , I32_const 4
  , I32_add
  , Get_global sp
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Get_global sp
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_add
  , I32_store 2 0
  , Get_global sp  -- bp = [[sp + 4] + 4]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Set_global bp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , Get_global bp  -- PUSH bp
  , Loop Nada
    [ Get_global bp  -- bp = bp - 1
    , I32_const 1
    , I32_sub
    , Set_global bp

    , Get_global hp  -- [hp + i] = [[sp + 4] + 8 + i] | i <- [0..bp - 1]
    , Get_global bp
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , Get_global bp
    , I32_add
    , I32_load8_u 0 0
    , I32_store8 0 0

    , Get_global bp
    , Br_if 0
    ]
  , Get_global hp  -- hp = hp + old_bp  ; Via POP.
  , I32_add
  , Set_global hp
  , Get_global sp  -- bp = [[sp + 8] + 4]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Set_global bp
  , Get_global bp  -- PUSH bp
  , Loop Nada
    [ Get_global bp  -- bp = bp - 1
    , I32_const 1
    , I32_sub
    , Set_global bp
    , Get_global hp  -- [hp + i] = [[sp + 8] + 8 + i] | i <- [0..bp - 1]
    , Get_global bp
    , I32_add
    , Get_global sp
    , I32_const 8
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , Get_global bp
    , I32_add
    , I32_load8_u 0 0
    , I32_store8 0 0
    , Get_global bp
    , Br_if 0
    ]
  , Get_global hp  -- hp = hp + old_bp  ; Via POP.
  , I32_add
  , Set_global hp
  , I32_store 2 0  -- [sp + 8] = old_hp  ; Via POPs.
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
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

-- Primitive functions.
data Prim = Prim
  { primName :: String
  , primArity :: Int
  , primAsm :: [WasmOp]
  }

syscallAsm :: [WasmOp]
syscallAsm =
  -- Example:
  --
  --   putStr ("He" ++ "llo")
  --
  -- becomes:
  --
  --   (#syscall 1 21) ("He" ++ "llo") #RealWorld
  --
  -- After removing the innermost spine, we have:
  --
  --   1, 21, (#syscall 1 21),  (... :@ ("He" ++ "llo")), (... :@ #RealWorld)
  --
  -- That is, the last two arguments are still on a spine, and we retain
  -- a pointer to `#syscall 1 21`. Normally, this pointer enables sharing
  -- (laziness) but we ignore it in this case because it's a syscall with
  -- a potential side effect.
  [ Get_global sp  -- sp = sp + 12
  , I32_const 12
  , I32_add
  , Set_global sp
  , Get_global sp  -- [[sp - 4] + 8] is now the syscall number.
  , I32_const 4
  , I32_sub
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , Get_global sp  -- local0 = [[sp - 8] + 8], the number of arguments.
  , I32_const 8
  , I32_sub
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , Tee_local 0  -- local1 = local0
  , Set_local 1

  , Block Nada
    [ Loop Nada  -- Encode all arguments.
      [ Get_local 0  -- Break if local0 == 0.
      , I32_eqz
      , Br_if 1
      -- Debone next argument...
      , Get_global sp
      , Get_global sp
      , Get_local 1  -- [sp] = [[sp + 4*local1] + 12]
      , I32_const 4
      , I32_mul
      , I32_add
      , I32_load 2 0
      , I32_const 12
      , I32_add
      , I32_load 2 0
      , I32_store 2 0
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
      -- ... then evaluate. TODO: Reduce to normal form.
      , Call 1
      , Get_local 0
      , I32_const 1
      , I32_sub
      , Set_local 0
      , Br 0
      ]
    ]
  -- Example stack now holds:
  --   "Hello", ("He" ++ "llo"), (... :@ #RealWorld)
  , Get_global sp  -- #syscall(syscall_number, sp, hp)
  , Get_global hp
  , Call 0
  -- Because the syscall cannot modify sp or hp, our convention is that
  --   [sp] = result ; [sp - 4] = hp_new
  -- We update the globals here, in WebAssembly.
  -- Clobber the stack: no sharing in the IO monad.
  , Get_global sp  -- hp = [sp - 4]
  , I32_const 4
  , I32_sub
  , I32_load 2 0
  , Set_global hp
  , Get_global sp  -- [sp + 8*argCount] = [sp]
  , Get_local 1
  , I32_const 8
  , I32_mul
  , I32_add
  , Get_global sp
  , I32_load 2 0
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 8*argCount - 4
  , Get_local 1
  , I32_const 8
  , I32_mul
  , I32_add
  , I32_const 4
  , I32_sub
  , Set_global sp
  -- Return (result, #RealWorld).
  , Get_global sp  -- [sp + 8] = 42
  , I32_const 8
  , I32_add
  , I32_const 42
  , I32_store 2 0
  ] ++ concatMap fromIns [Copro 0 2] ++
  [ End
  ]

prims :: [Prim]
prims = fmap mkPrim
  [ ("+", intAsm I64_add)
  , ("-", intAsm I64_sub)
  , ("*", intAsm I64_mul)
  , ("div", intAsm I64_div_s)
  , ("mod", intAsm I64_rem_s)
  , ("Int-==", cmpAsm I64_eq)
  , ("<", cmpAsm I64_lt_s)
  , (">", cmpAsm I64_gt_s)
  , ("<=", cmpAsm I64_le_s)
  , (">=", cmpAsm I64_ge_s)
  , ("&&", boolAsm I32_and)
  , ("||", boolAsm I32_or)
  , ("++", catAsm)
  , ("#syscall", [Call 2, End])
  ]
  where mkPrim (s, as) = Prim { primName = s, primArity = 2, primAsm = as }

wasm :: String -> Either String [Int]
wasm prog = uncurry insToBin <$> compileMk1 prog

compileMk1 :: String -> Either String (GlobalTable, [(String, [Ins])])
compileMk1 haskell = astToIns <$> hsToAst webDemoSys haskell

webDemoSys :: Syscalls
webDemoSys = M.fromList
  [ ("putStr", (21, TC "String" :-> io (TC "()")))
  , ("putInt", (22, TC "Int" :-> io (TC "()")))
  ]
  where io = TApp (TC "IO")

-- | Arity and index of each global, both predefined primitives and
-- user-defined functions.
type GlobalTable = M.Map String (Int, Int)

astToIns :: [(String, Ast)] -> (GlobalTable, [(String, [Ins])])
astToIns ds = (funs, map (\(s, d) -> (s, evalState (mk1 d) [])) ds) where
  ps = zipWith (\p i -> (primName p, (primArity p, i))) prims [0..]
  funs = M.fromList $ ps ++ zipWith (\(name, Lam as _) i -> (name, (length as, i))) ds [length prims..]

typedAstToBin :: [(String, (Ast, Type))] -> [Int]
typedAstToBin = uncurry insToBin . astToIns . liftLambdas . (second fst <$>)

tag_const :: Tag -> WasmOp
tag_const = I32_const . fromIntegral . fromEnum

-- | Returns arity and index of given global function.
getGlobal :: GlobalTable -> String -> (Int, Int)
getGlobal funs v = case M.lookup v funs of
  Nothing -> error $ "no such global: " ++ v
  Just (i, j) -> (i, j)

insToBin :: GlobalTable -> [(String, [Ins])] -> [Int]
insToBin funs m = concat
  [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.
  , sect 1  -- Type section.
    [ encSig [I32, I32, I32] []  -- Type of syscall.
    , encSig [] []  -- Most functions have type () -> ().
    , encSig [] [I32]  -- Next two are for getters and setters.
    , encSig [I32] []
    ]
  -- Import section.
  -- [0, 0] = external_kind Function, index 0.
  , sect 2 [encStr "i" ++ encStr "f" ++ [0, 0]]
  , sect 3 $ (pure . fst . fst <$> fs) ++ [[1]]  -- Function section.
  , sect 5 [[0, nPages]]  -- Memory section (0 = no-maximum).
  , sect 6  -- Global section (1 = mutable).
    [ [encType I32, 1, 0x41] ++ leb128 (65536*nPages - 4) ++ [0xb]  -- SP
    , [encType I32, 1, 0x41, 0, 0xb]  -- HP
    , [encType I32, 1, 0x41, 0, 0xb]  -- BP
    ]
  -- Export section.
  , sect 7
    -- 0 = external_kind Function, n = function index.
    [ encStr "main" ++ [0, length fs + 1]
    , encStr "getsp" ++ [0, 3]
    , encStr "setsp" ++ [0, 4]
    , encStr "gethp" ++ [0, 5]
    , encStr "sethp" ++ [0, 6]
    -- 2 = external_kind Memory, 0 = memory index
    , encStr "mem" ++ [2, 0]
    ]
  , sect 10 $ encProcedure <$> (fs ++  -- Code section.
    [((1, 0),
      -- The magic constant 42 represents the RealWorld.
      [ Get_global sp  -- [sp] = 42
      , I32_const 42
      , I32_store 2 0
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
      ]
      ++ concatMap (fromInsWith $ getGlobal funs) [PushGlobal "main", MkAp]
      ++ [ Call 1, End ]
    )])
  ] where
  -- Function 0: import function which we send our outputs.
  -- Function 1: Eval (reduce to weak head normal form).
  -- Function 2: syscall
  -- Function 3: getsp
  -- Function 4: setsp
  -- Function 5: gethp
  -- Function 6: sethp
  -- Afterwards, the primitive functions, then the functions in the program.
  predefs =
    [ ((1, 0), evalAsm (length prims + length m))
    , ((1, 2), syscallAsm)
    , ((2, 0), [Get_global sp, End])
    , ((3, 0), [Get_local 0, Set_global sp, End])
    , ((2, 0), [Get_global hp, End])
    , ((3, 0), [Get_local 0, Set_global hp, End])
    ]
  fs = predefs ++ fmap ((,) (1, 0)) ((primAsm <$> prims) ++ ((++ [End]) . concatMap (fromInsWith $ getGlobal funs) . snd <$> m))
  sect t xs = t : lenc (varlen xs ++ concat xs)
  encStr s = lenc $ ord <$> s
  encProcedure ((_, 0), body) = lenc $ 0:concatMap encWasmOp body
  encProcedure ((_, locCount), body) = lenc $ ([1, locCount, encType I32] ++) $ concatMap encWasmOp body
  encType I32 = 0x7f
  encType I64 = 0x7e
  encType _ = error "TODO"
  -- | Encodes function signature.
  encSig ins outs = 0x60 : lenc (encType <$> ins) ++ lenc (encType <$> outs)
  evalAsm n =
    [ Block Nada
      [ Loop Nada
        [ Get_global sp  -- bp = [sp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Set_global bp
        , Block Nada
          [ Block Nada
            [ Get_global bp
            , I32_load8_u 0 0
            , Br_table [0, 1, 3] 4  -- case [bp].8u; branch on Tag
            ]  -- 0: Ap
          , Get_global sp  -- [sp] = [bp + 8]
          , Get_global bp
          , I32_const 8
          , I32_add
          , I32_load 2 0
          , I32_store 2 0
          , Get_global sp  -- sp = sp - 4
          , I32_const 4
          , I32_sub
          , Set_global sp
          , Br 1
          ]  -- 1: Ind.
        , Get_global sp  -- [sp + 4] = [bp + 4]
        , I32_const 4
        , I32_add
        , Get_global bp
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_store 2 0
        , Br 0
        ]  -- 2: Eval loop.
      ]  -- 3: Global
    , Get_global bp  -- save bp, sp
    , Get_global sp
    , Get_global sp  -- bp = sp + 4 + 4 * ([bp].16u >> 8)
    , I32_const 4
    , I32_add
    , Get_global bp
    , I32_load16_u 1 0
    , I32_const 8
    , I32_shr_u
    , I32_const 4
    , I32_mul
    , I32_add
    , Set_global bp

    , Loop Nada  -- Remove spine.
      [ Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      , Get_global sp  -- if sp /= bp then
      , Get_global bp
      , I32_ne
      , If Nada
        [ Get_global sp  -- [sp] = [[sp + 4] + 12]
        , Get_global sp
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_const 12
        , I32_add
        , I32_load 2 0
        , I32_store 2 0
        , Br 1
        ]  -- If
      ]  -- Loop
    , Set_global sp
    , Set_global bp
    ] ++ nest n ++ [End]
    where
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ length predefs + k, Br $ n - k]

leb128 :: Int -> [Int]
leb128 n | n < 64    = [n]
         | n < 128   = [128 + n, 0]
         | otherwise = 128 + (n `mod` 128) : leb128 (n `div` 128)

-- TODO: FIX!
sleb128 :: Integral a => a -> [Int]
sleb128 n | n < 64    = [fromIntegral n]
          | n < 128   = [128 + fromIntegral n, 0]
          | otherwise = 128 + (fromIntegral n `mod` 128) : sleb128 (n `div` 128)

varlen :: [a] -> [Int]
varlen xs = leb128 $ length xs

lenc :: [Int] -> [Int]
lenc xs = varlen xs ++ xs

sp :: Int
sp = 0
hp :: Int
hp = 1
bp :: Int
bp = 2

fromIns :: Ins -> [WasmOp]
fromIns = fromInsWith (error . show)

fromInsWith :: (String -> (Int, Int)) -> Ins -> [WasmOp]
fromInsWith lookupGlobal instruction = case instruction of
  Trap -> [ Unreachable ]
  Eval -> [ Call 1 ]  -- (Tail call.)
  PushInt n ->
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = TagInt
    , tag_const TagInt
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = n
    , I32_const 8
    , I32_add
    , I64_const n
    , I64_store 3 0
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  -- TODO: Prepopulate heap instead of this expensive code.
  PushString sbs -> let
    s = SBS.unpack sbs
    delta = (4 - (SBS.length sbs `mod` 4)) `mod` 4
    in
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = TagString
    , tag_const TagString
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = SBS.length sbs
    , I32_const 4
    , I32_add
    , I32_const $ fromIntegral $ SBS.length sbs
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    ] ++ concat
    [ [ Get_global hp
      , I32_const $ fromIntegral c
      , I32_store8 0 0
      , Get_global hp
      , I32_const 1
      , I32_add
      , Set_global hp
      ] | c <- s] ++
    [ Get_global hp
    , I32_const $ fromIntegral delta
    , I32_add
    , Set_global hp
    ]
  Push n ->
    [ Get_global sp  -- [sp] = [sp + 4(n + 1)]
    , Get_global sp
    , I32_const $ 4*(fromIntegral n + 1)
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    ]
  MkAp ->
    [ Get_global hp  -- [hp] = TagAp
    , tag_const TagAp
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = [sp + 4]
    , I32_const 8
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global hp  -- [hp + 12] = [sp + 8]
    , I32_const 12
    , I32_add
    , Get_global sp
    , I32_const 8
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- [sp + 8] = hp
    , I32_const 8
    , I32_add
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  PushGlobal fun | (n, g) <- lookupGlobal fun ->
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = TagGlobal | (n << 8)
    , I32_const $ fromIntegral $ fromEnum TagGlobal + 256*n
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = g
    , I32_const 4
    , I32_add
    , I32_const $ fromIntegral g
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  Slide 0 -> []
  Slide n ->
    [ Get_global sp  -- [sp + 4*(n + 1)] = [sp + 4]
    , I32_const $ 4*(fromIntegral n + 1)
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- sp = sp + 4*n
    , I32_const $ 4*fromIntegral n
    , I32_add
    , Set_global sp
    ]
  Alloc n -> concat (replicate n
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global hp  -- [hp] = TagInd
    , tag_const TagInd
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    ])
  UpdateInd n ->
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global sp  -- [[sp + 4*(n + 1)] + 4] = [sp]
    , I32_const $ fromIntegral $ 4*(n + 1)
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , Get_global sp
    , I32_load 2 0
    , I32_store 2 0
    ]
  UpdatePop n ->
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Get_global sp  -- sp = sp + 4*(n + 1)
    , I32_const $ fromIntegral $ 4*(n + 1)
    , I32_add
    , Set_global sp
    , Get_global sp  -- [[sp + 4]] = Ind
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , tag_const TagInd
    , I32_store 2 0
    , Get_global sp  -- [[sp + 4] + 4] = bp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , Get_global bp
    , I32_store 2 0
    ]
  Copro m n ->
    [ Get_global hp  -- [hp] = TagSum | (n << 8)
    , I32_const $ fromIntegral $ fromEnum TagSum + 256 * n
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = m
    , I32_const 4
    , I32_add
    , I32_const $ fromIntegral m
    , I32_store 2 0
    ] ++ concat [
      [ Get_global hp  -- [hp + 4 + 4*i] = [sp + 4*i]
      , I32_const $ fromIntegral $ 4 + 4*i
      , I32_add
      , Get_global sp
      , I32_const $ fromIntegral $ 4*i
      , I32_add
      , I32_load 2 0
      , I32_store 2 0 ] | i <- [1..n]] ++
    [ Get_global sp  -- sp = sp + 4*n
    , I32_const $ fromIntegral $ 4*n
    , I32_add
    , Set_global sp
    , Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- hp = hp + 8 + ceil(n / 2) * 8
    , I32_const $ fromIntegral $ 8 + 8 * ((n + 1) `div` 2)
    , I32_add
    , Set_global hp
    ]
  Casejump alts0 -> let
    -- TODO: This compiles Int case statements incorrectly.
      (underscore, unsortedAlts) = partition (isNothing . fst) alts0
      alts = sortOn fst unsortedAlts
      catchall = if null underscore then [Trap] else snd $ head underscore
      tab = zip (fromJust . fst <$> alts) [0..]
      m = maximum $ fromJust . fst <$> alts
      nest j (ins:rest) = pure $ Block Nada $ nest (j + 1) rest ++ concatMap (fromInsWith lookupGlobal) ins ++ [Br j]
      nest _ [] = pure $ Block Nada
        [ Get_global bp  -- [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [fromIntegral $ fromMaybe (length alts) $ lookup i tab | i <- [0..m]] $ m + 1
        ]
    in if null alts then concatMap (fromInsWith lookupGlobal) catchall else
    -- [sp + 4] should be:
    -- 0: TagSum
    -- 4: "Enum"
    -- 8, 12, ...: fields
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Block Nada $ nest 1 (reverse $ snd <$> alts) ++ concatMap (fromInsWith lookupGlobal) catchall
    ]

  Split 0 -> [Get_global sp, I32_const 4, I32_add, Set_global sp]
  Split n ->
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    ] ++ concat [
      [ Get_global sp  -- [sp - 4*(n - i)] = [bp + 4 + 4*i]
      , I32_const $ fromIntegral $ 4*(n - i)
      , I32_sub
      , Get_global bp
      , I32_const $ fromIntegral $ 4 + 4*i
      , I32_add
      , I32_load 2 0
      , I32_store 2 0
      ] | i <- [1..n]] ++
    [ Get_global sp  -- sp = sp - 4*n
    , I32_const $ fromIntegral $ 4*n
    , I32_sub
    , Set_global sp
    ]

mk1 :: Ast -> State [(String, Int)] [Ins]
mk1 ast = case ast of
  Lam as b -> do
    modify' $ \bs -> zip as [length bs..] ++ bs
    (++ [UpdatePop $ length as, Eval]) <$> mk1 b
  I n -> pure [PushInt n]
  S s -> pure [PushString s]
  t :@ u -> do
    mu <- mk1 u
    bump 1
    mt <- mk1 t
    bump (-1)
    pure $ case last mt of
      Copro _ _ -> mu ++ mt
      _ -> concat [mu, mt, [MkAp]]
  Var v -> do
    m <- get
    pure $ case lookup v m of
      Just k -> [Push k]
      Nothing -> [PushGlobal v]
  Pack n m -> pure [Copro n m]
  Cas expr alts -> do
    me <- mk1 expr
    xs <- forM alts $ \(p, body) -> do
      orig <- get  -- Save state.
      (f, b) <- case fromApList p of
        [I n] -> do  -- TODO: Rewrite as equality check.
          bump 1
          (,) (Just $ fromIntegral n) . (++ [Slide 1]) <$> mk1 body
        (Pack n _:vs) -> do
          bump $ length vs
          modify' (zip (map (\(Var v) -> v) vs) [0..] ++)
          bod <- mk1 body
          pure (Just $ fromIntegral n, Split (length vs) : bod ++ [Slide (length vs)])
        [Var s] -> do
          bump 1
          modify' $ \bs -> (s, 0):bs
          (,) Nothing . (++ [Slide 1]) <$> mk1 body
        _ -> undefined
      put orig  -- Restore state.
      pure (f, b)
    pure $ me ++ [Eval, Casejump xs]
  Let ds body -> let n = length ds in do
    orig <- get  -- Save state.
    bump n
    modify' (zip (fst <$> ds) [n-1,n-2..0] ++)
    dsAsm <- mapM mk1 $ snd <$> ds
    b <- mk1 body
    put orig  -- Restore state.
    pure $ Alloc n : concat (zipWith (++) dsAsm (pure . UpdateInd <$> [n-1,n-2..0])) ++ b ++ [Slide n]
  _ -> error $ "TODO: compile: " ++ show ast
  where
    bump n = modify' $ map $ second (+n)

fromApList :: Ast -> [Ast]
fromApList (a :@ b) = fromApList a ++ [b]
fromApList a = [a]
