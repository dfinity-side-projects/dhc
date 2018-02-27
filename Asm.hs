{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Asm (hsToWasm, Ins(..),
  WasmType(Ref),  -- Re-export from WasmOp.
  hsToGMachineWebDemo, hsToWasmWebDemo) where
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
import qualified Data.Bimap as BM
import Data.Char
import Data.Int
import Data.List
import Data.Maybe

import DHC
import WasmOp

#ifdef __HASTE__
type ShortByteString = SBS.ByteString
#endif

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal String
  | PushString ShortByteString
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePop Int | UpdateInd Int | Alloc Int
  | Casejump [(Maybe Int, [Ins])] | Trap
  deriving Show

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
-- Ports:
--    0 TagPort
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

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagPort | TagSum | TagString deriving Enum

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

-- | Tuple of:
--   1. List of exported functions.
--   2. Arity of each user-defined function, whether exported or not.
--   3. List of wdecl functions.
-- Hopefully, the third item will soon supersede the other two.
type GlobalTable = ([String], M.Map String Int, [(String, ([WasmType], [WasmType]))])

hsToWasmWebDemo :: String -> Either String [Int]
hsToWasmWebDemo prog = snd <$> hsToWasm webDemoSys prog

hsToGMachineWebDemo :: String -> Either String (GlobalTable, [(String, [Ins])])
hsToGMachineWebDemo haskell = astToIns <$> hsToAst webDemoSys haskell

-- | Returns
--   ( arities of synchronous exports
--   , types of asynchronous exports
--   , WebAssembly binary
--   )
hsToWasm :: Syscalls -> String -> Either String (([(String, Int)], [(String, ([WasmType], [WasmType]))]), [Int])
hsToWasm sys prog = insToBin . astToIns <$> hsToAst sys prog

webDemoSys :: Syscalls
webDemoSys = (M.fromList
  [ ("putStr", (21, TC "String" :-> io (TC "()")))
  , ("putInt", (22, TC "Int" :-> io (TC "()")))
  ], \_ _ -> Nothing)
  where io = TApp (TC "IO")

astToIns :: AstPlus -> (GlobalTable, [(String, [Ins])])
astToIns (AstPlus es ws storage ds ts) = ((es, funs, wrapme), second compile <$> ds) where
  compile d = evalState (mk1 storage d) []
  wrapme = wasmize <$> ws
  wasmize w = (w, wasmType [] $ fst $ fromJust $ lookup w ts)
  wasmType acc t = case t of
    a :-> b -> wasmType (translateType a : acc) b
    r -> (,) (reverse acc) $ case r of
      TC "()" -> []
      TApp (TC "IO") _ -> []
      _ -> [translateType r]
  -- For JS demos.
  -- translateType (TC "Int") = I32
  translateType (TC "Int") = I64
  translateType (TC "Port") = Ref "Port"
  translateType (TC "Databuf") = Ref "Databuf"
  translateType t = error $ "no corresponding wasm type: " ++ show t
  funs = M.fromList $ ((\(name, Ast (Lam as _)) -> (name, length as)) <$> ds)

tag_const :: Tag -> WasmOp
tag_const = I32_const . fromIntegral . fromEnum

insToBin :: (GlobalTable, [(String, [Ins])]) -> (([(String, Int)], [(String, ([WasmType], [WasmType]))]), [Int])
insToBin ((exs, funs, wrapme), gmachine) = ((((\s -> (s, fst $ getGlobal s)) <$> exs), wrapme), wasm) where
  wasm = concat
    [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.
    , sect 1 $ uncurry encSig . snd <$> BM.assocs typeMap  -- Type section.
    , sect 2 $ importFun <$> imps  -- Import section.
    , sect 3 $ pure . fst . fst . snd <$> wasmFuns  -- Function section.
    , sect 5 [[0, nPages]]  -- Memory section (0 = no-maximum).
    , sect 6  -- Global section (1 = mutable).
      [ [encType I32, 1, 0x41] ++ leb128 (65536*nPages - 4) ++ [0xb]  -- SP
      , [encType I32, 1, 0x41, 0, 0xb]  -- HP
      , [encType I32, 1, 0x41, 0, 0xb]  -- BP
      ]
    , sect 7 $  -- Export section.
      [ encStr "mem" ++ [2, 0]  -- 2 = external_kind Memory, 0 = memory index.
      , exportFun "main" "#main"
      , exportFun "getsp" "#getsp"
      , exportFun "setsp" "#setsp"
      , exportFun "gethp" "#gethp"
      , exportFun "sethp" "#sethp"
      ]
      -- The "contract" functions are exported with "_" prepended.
      ++ [exportFun ('_':s) s | s <- exs]
      -- The "wdecl" functions are exported with "w_" prepended.
      ++ [exportFun ('w':'_':s) ('@':s) | (s, _) <- wrapme]
    , sect 10 $ encProcedure . snd <$> wasmFuns  -- Code section.
    ]
  imps = [("dhc", "system", [I32, I32, I32], [])]
  -- 0 = external_kind Function.
  importFun (m, f, i, o) = encStr m ++ encStr f ++ [0, typeNo i o]
  typeNo ins outs = typeMap BM.!> (ins, outs)
  typeMap = BM.fromList $ zip [0..] $ nub $
    [ ([I32, I32, I32], [])  -- Syscall type.
    , ([], [])  -- Most internal functions have type () -> ().
    , ([], [I32])  -- gethp, getsp.
    , ([I32], [])  -- sethp, setsp.
    ] ++ (snd <$> wrapme)  -- wdecl functions.
  exportFun name internal = encStr name ++ [0, wasmFunNo internal]
  -- Only two primitives need local variables.
  localCount "#syscall" = 2
  localCount "#syscallPure" = 2
  localCount _ = 0
  -- Returns arity and 0-indexed number of given global function.
  getGlobal s = case M.lookup s funs of
    Just arity -> (arity, wasmFunNo s - firstPrim)
    Nothing -> (arityFromType $ snd $ preludeMinimal M.! s, wasmFunNo s - firstPrim)
  firstPrim = wasmFunNo $ fst $ head prims
  wasmFuns =
    [ ("#eval", ((typeNo [] [], 0), evalAsm))
    , ("#getsp", ((typeNo [] [I32], 0), [Get_global sp, End]))
    , ("#setsp", ((typeNo [I32] [], 0), [Get_local 0, Set_global sp, End]))
    , ("#gethp", ((typeNo [] [I32], 0), [Get_global hp, End]))
    , ("#sethp", ((typeNo [I32] [], 0), [Get_local 0, Set_global hp, End]))
    ]
    -- Primitive functions.
    -- The assembly for "#eval" requires that the primitive functions
    -- directly precede those defined in the program.
    ++ ((\(s, p) -> (s, ((typeNo [] [], localCount s), p))) <$> prims)
    -- Functions from the program.
    ++ ((\(f, g) -> (f, ((typeNo [] [], 0), (++ [End]) $ concatMap fromIns g))) <$> gmachine)
    -- Outer "main" function. It calls the internal "main" function (which
    -- is "_main" if exported).
    ++ [("#main", ((typeNo [] [], 0),
        -- The magic constant 42 represents the RealWorld.
        [ Get_global sp  -- [sp] = 42
        , I32_const 42
        , I32_store 2 0
        , Get_global sp  -- sp = sp - 4
        , I32_const 4
        , I32_sub
        , Set_global sp
        ]
        ++ concatMap fromIns [PushGlobal "main", MkAp, Eval]
        ++ [End]
      ))]
    -- Wrappers for functions in "wdecl" section.
    ++ (wrap <$> wrapme)
  wasmFunMap = M.fromList $ zip (fst <$> wasmFuns) [0..]
  -- Function 0: import function which we send our outputs.
  wasmFunNo s = (wasmFunMap M.! s) + length imps
  refToI32 (Ref _) = I32
  refToI32 t = t
  wrap (f, (ins, outs)) = (,) ('@':f) $ (,) (typeNo ins outs, 0) $
    -- Anticipate UpdatePop.
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    ]
    -- Input arguments are local variables.
    -- We move these to our stack in reverse order.
    ++ concat (reverse $ zipWith wdeclIn (refToI32 <$> ins) [0..])
    ++ [Call $ wasmFunNo f]
    -- Push the result to the WebAssembly stack.
    ++ concatMap wdeclOut (refToI32 <$> outs)
    ++ [End]
  wdeclIn I64 i =
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
    , Get_global hp  -- [hp + 8] = local i
    , I32_const 8
    , I32_add
    , Get_local i
    , I64_store 3 0
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  wdeclIn I32 i =
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = TagPort
    , tag_const TagPort
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = local i
    , I32_const 4
    , I32_add
    , Get_local i
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    ]
  {- For JS demos.
  wdeclIn I32 i =
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
    , Get_global hp  -- [hp + 12] = 0
    , I32_const 12
    , I32_add
    , I32_const 0
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = local i
    , I32_const 8
    , I32_add
    , Get_local i
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  -}
  wdeclIn _ _ = error "TODO"
  wdeclOut I64 =
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global sp  -- PUSH [[sp] + 8]
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I64_load 3 0
    ]
  wdeclOut I32 =
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global sp  -- PUSH [[sp] + 8]
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I32_load 2 0
    ]
  wdeclOut _ = error "TODO"
  sect t xs = t : lenc (varlen xs ++ concat xs)
  encStr s = lenc $ ord <$> s
  encProcedure ((_, 0), body) = lenc $ 0:concatMap encWasmOp body
  encProcedure ((_, locCount), body) = lenc $ ([1, locCount, encType I32] ++) $ concatMap encWasmOp body
  encType I32 = 0x7f
  encType I64 = 0x7e
  encType (Ref _) = encType I32
  encType _ = error "TODO"
  -- | Encodes function signature.
  encSig ins outs = 0x60 : lenc (encType <$> ins) ++ lenc (encType <$> outs)
  evalAsm =
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
      n = length prims + length gmachine
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ firstPrim + k - 1, Br $ n - k]

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
    ] ++ concatMap fromIns [UpdatePop 2, Eval] ++ [End]

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
    ] ++ concatMap fromIns [UpdatePop 2, Eval] ++ [End]

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
    ] ++ concatMap fromIns [UpdatePop 2, Eval] ++ [End]

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
    , Block Nada
      [ Loop Nada
        [ Get_global bp  -- if (bp == 0) break;
        , I32_eqz
        , Br_if 1

        , Get_global bp  -- bp = bp - 1
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
        , Br 0
        ]
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
    , Block Nada
      [ Loop Nada
        [ Get_global bp  -- if (bp == 0) break;
        , I32_eqz
        , Br_if 1
        , Get_global bp  -- bp = bp - 1
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
        , Br 0
        ]
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
    ] ++ concatMap fromIns [UpdatePop 2, Eval] ++ [End]

  strEqAsm :: [WasmOp]
  strEqAsm = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
    [ Get_global sp  -- PUSH sp + 8
    , I32_const 8
    , I32_add
    , Get_global hp  -- PUSH hp
    , Get_global hp  -- [hp] = TagSum
    , tag_const TagSum
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = 0
    , I32_const 4
    , I32_add
    , I32_const 0
    , I32_store 2 0

    , Get_global sp  -- bp = [[sp + 4] + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp

    , Block Nada
      [ Get_global sp  -- if bp /= [[sp + 8] + 4] then break
      , I32_const 8
      , I32_add
      , I32_load 2 0
      , I32_const 4
      , I32_add
      , I32_load 2 0
      , Get_global bp
      , I32_ne
      , Br_if 0

      , Loop Nada
        [ Block Nada
          [ Get_global bp  -- if bp == 0 then break.
          , I32_eqz
          , Br_if 0
          , Get_global bp  -- bp = bp - 1
          , I32_const 1
          , I32_sub
          , Set_global bp

          , Get_global sp  -- [[sp + 4] + 8 + bp].8u /= [[sp + 8] + 8 + bp].8u
          , I32_const 4
          , I32_add
          , I32_load 2 0
          , I32_const 8
          , I32_add
          , Get_global bp
          , I32_add
          , I32_load8_u 0 0
          , Get_global sp
          , I32_const 8
          , I32_add
          , I32_load 2 0
          , I32_const 8
          , I32_add
          , Get_global bp
          , I32_add
          , I32_load8_u 0 0
          , I32_ne
          , Br_if 2  -- Break if unequal characters found.
          , Br 1  -- Keep looping.
          ]
        ]
      , Get_global hp  -- [hp + 4] = 1
      , I32_const 4
      , I32_add
      , I32_const 1
      , I32_store 2 0
      ]
    , I32_store 2 0  -- [sp + 8] = old_hp  ; Via POPs.
    , Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    ] ++ concatMap fromIns [UpdatePop 2, Eval] ++ [End]

  syscallPureAsm :: [WasmOp]
  syscallPureAsm =
    -- Example:
    --
    --   beaconAt 123
    --
    -- becomes:
    --
    --   (#syscallPure 1 999) (Var "beaconAt" :@ 123)
    --
    -- The number of arguments to "beaconAt" is 1.
    -- The syscall number is 999.
    --
    -- After removing the innermost spine, we have:
    --
    --   1, 999, (#syscallPure 1 999), (Var "beaconAt" :@ 123)
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
        , Call $ wasmFunNo "#eval"
        , Get_local 0
        , I32_const 1
        , I32_sub
        , Set_local 0
        , Br 0
        ]
      ]
    -- Example stack now holds:
    --   123, 123
    , Get_global sp  -- #syscall(syscall_number, sp, hp)
    , Get_global hp
    , Call 0
    -- Because the syscall cannot modify sp or hp, our convention is that
    --   [sp] = result ; [sp - 4] = hp_new
    -- We update the globals here, in WebAssembly.
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
    -- No update (normal evaluation, not lazy). Hopefully this syscall is cheap!
    , End
    ]

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
    --   1, 21, (#syscall 1 21), (... :@ ("He" ++ "llo")), (... :@ #RealWorld)
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
        , Call $ wasmFunNo "#eval"
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
    -- Our convention:
    --   [sp] = result ; [sp - 4] = hp_new
    -- We update the globals here, in WebAssembly.
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

  -- Primitive functions.
  prims :: [(String, [WasmOp])]
  prims =
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
    , ("String-==", strEqAsm)
    , ("#syscall", syscallAsm)
    , ("#syscallPure", syscallPureAsm)
    ]

  fromIns :: Ins -> [WasmOp]
  fromIns instruction = case instruction of
    Trap -> [ Unreachable ]
    Eval -> [ Call $ wasmFunNo "#eval" ]  -- (Tail call.)
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
    PushGlobal fun | (n, g) <- getGlobal fun ->
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
      , Get_global hp  -- hp = hp + 16
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
      (underscore, unsortedAlts) = partition (isNothing . fst) alts0
      alts = sortOn fst unsortedAlts
      catchall = if null underscore then [Trap] else snd $ head underscore
      tab = zip (fromJust . fst <$> alts) [0..]
      m = maximum $ fromJust . fst <$> alts
      nest j (ins:rest) = pure $ Block Nada $ nest (j + 1) rest ++ concatMap fromIns ins ++ [Br j]
      nest _ [] = pure $ Block Nada
        [ Get_global bp  -- [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [fromIntegral $ fromMaybe (length alts) $ lookup i tab | i <- [0..m]] $ m + 1
        ]
      in if null alts then concatMap fromIns catchall else
      -- [sp + 4] should be:
      -- 0: TagSum
      -- 4: "Enum"
      -- 8, 12, ...: fields
      [ Get_global sp  -- bp = [sp + 4]
      , I32_const 4
      , I32_add
      , I32_load 2 0
      , Set_global bp
      , Block Nada $ nest 1 (reverse $ snd <$> alts) ++ concatMap fromIns catchall
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

mk1 :: [String] -> Ast -> State [(String, Int)] [Ins]
mk1 storage (Ast ast) = case ast of
  -- | Thanks to lambda lifting, `Lam` can only occur at the top level.
  Lam as b -> do
    put $ zip as [0..]
    (++ [UpdatePop $ length as, Eval]) <$> rec b
  I n -> pure [PushInt n]
  S s -> pure [PushString s]
  t :@ u -> do
    mu <- rec u
    bump 1
    mt <- rec t
    bump (-1)
    pure $ case last mt of
      Copro _ _ -> mu ++ mt
      _ -> concat [mu, mt, [MkAp]]
  Var "undefined" -> pure [Trap]
  Var v -> do
    m <- get
    pure $ case lookup v m of
      Just k -> [Push k]
      Nothing -> if v `elem` storage then [PushString $ SBS.pack $ fromIntegral . ord <$> v] else [PushGlobal v]
  Pack n m -> pure [Copro n m]
  Cas expr alts -> do
    me <- rec expr
    xs <- forM alts $ \(p, body) -> do
      orig <- get  -- Save state.
      (f, b) <- case fromApList p of
        (Ast (Pack n _):vs) -> do
          bump $ length vs
          modify' (zip (map (\(Ast (Var v)) -> v) vs) [0..] ++)
          bod <- rec body
          pure (Just $ fromIntegral n, Split (length vs) : bod ++ [Slide (length vs)])
        [Ast (Var s)] -> do
          bump 1
          modify' $ \bs -> (s, 0):bs
          (,) Nothing . (++ [Slide 1]) <$> rec body
        _ -> undefined
      put orig  -- Restore state.
      pure (f, b)
    pure $ me ++ [Eval, Casejump xs]
  Let ds body -> let n = length ds in do
    orig <- get  -- Save state.
    bump n
    modify' (zip (fst <$> ds) [n-1,n-2..0] ++)
    dsAsm <- mapM rec $ snd <$> ds
    b <- rec body
    put orig  -- Restore state.
    pure $ Alloc n : concat (zipWith (++) dsAsm (pure . UpdateInd <$> [n-1,n-2..0])) ++ b ++ [Slide n]
  _ -> error $ "TODO: compile: " ++ show ast
  where
    bump n = modify' $ map $ second (+n)
    rec = mk1 storage

fromApList :: Ast -> [Ast]
fromApList (Ast (a :@ b)) = fromApList a ++ [b]
fromApList a = [a]
