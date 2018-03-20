{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Asm (hsToWasm, Ins(..),
  DfnWasm(..),
  WasmType(Ref),  -- Re-export from WasmOp.
  tag_const, Tag(..), hsToIns,
  QuasiWasm, QuasiWasmHelper(..),
  GlobalTable, Boost(..), catBoost) where

import Control.Arrow
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
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import DHC
import WasmOp

#ifdef __HASTE__
type ShortByteString = SBS.ByteString
#endif

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal String
  | PushRef Int32
  | PushString ShortByteString
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePop Int | UpdateInd Int | Alloc Int
  | Casejump [(Maybe Int, [Ins])] | Trap
  | PushCallIndirect [WasmType]
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

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagRef | TagSum | TagString deriving Enum

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
  Call_indirect n -> 0x11 : leb128 n ++ [0]
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
--  1. List of exported functions. Hopefully will be removed soon.
--  2. Arity of each user-defined function, whether exported or not.
--     Eval uses this to remove the spine correctly.
--  3. List of wdecl functions.
--  4. Types needed by call_indirect ops.
--  5. (Initial HP value, Addresses of string constants).
--  6. Persistent global count.
-- TODO: NAME THESE FIELDS ALREADY!
type GlobalTable =
  ( [String]
  , M.Map String Int
  , [(String, ([WasmType], [WasmType]))]
  , [[WasmType]]
  , (Int, Map ShortByteString Int)
  , Int
  )

type WasmImport = ((String, String), ([WasmType], [WasmType]))

-- | A few helpers for inline assembly.
type QuasiWasm = CustomWasmOp QuasiWasmHelper
data QuasiWasmHelper =
    CallSym String  -- Find function index and call it.
  -- Find type index and call_indirect it.
  | CallIndirectType [WasmType] [WasmType]
  | ReduceArgs Int  -- Copy arguments from heap and reduce them to WHNF.
  deriving Show

-- | A Boost is a custom collection of extra declarations and functions that
-- are added to a binary.
data Boost = Boost
  -- Wasm import declarations.
  { boostImports :: [WasmImport]
  -- Primitive Haskell functions.
  , boostHs :: [(String, (Type, [QuasiWasm]))]
  -- Internal wasm functions, indexed by strings for CallSym.
  , boostWasm :: [(String, (([WasmType], [WasmType]), [QuasiWasm]))]
  }

catBoost :: Boost -> Boost -> Boost
catBoost (Boost a b c) (Boost x y z) = Boost (a ++ x) (b ++ y) (c ++ z)

data DfnWasm = DfnWasm
  { legacyArities :: [(String, Int)]  -- Arities of legacy exports.
  , wasmBinary :: [Int]
  }

hsToWasm :: Boost -> ExternType -> String -> Either String DfnWasm
hsToWasm boost ext prog = insToBin boost . astToIns <$> hsToAst (boostTypes boost) ext prog

hsToIns :: Boost -> ExternType -> String -> Either String (GlobalTable, [(String, [Ins])])
hsToIns boost ext prog = astToIns <$> hsToAst (boostTypes boost) ext prog

boostTypes :: Boost -> Map String (Maybe (Int, Int), Type)
boostTypes b = M.fromList $ second (((,) Nothing) . fst) <$> boostHs b

data CompilerState = CompilerState
  -- Bindings are local. They start empty and finish empty.
  -- During compilation, they hold the stack position of the bound variables.
  { bindings :: [(String, Int)]
  -- Each call_indirect indexes into the type section of the binary.
  -- We record the types used by the binary so we can collect and look them
  -- up when generating assembly.
  -- TODO: It'd be better to fold over CompilerState during compile to
  -- incrementally update these fields.
  , callIndirectTypes :: [[WasmType]]
  , stringConstants :: [ShortByteString]
  }

align4 :: Int -> Int
align4 n = (n + 3) `div` 4 * 4

mkStrConsts :: [ShortByteString] -> (Int, Map ShortByteString Int)
mkStrConsts ss = f (0, []) ss where
  f (p, ds) [] = (p, M.fromList ds)
  f (k, ds) (s:rest) = f (k + 8 + align4 (SBS.length s), ((s, k):ds)) rest

astToIns :: AstPlus -> (GlobalTable, [(String, [Ins])])
astToIns (AstPlus es ws storage ps ds ts) = ((es, funs, wasmDecl <$> ws, ciTypes, strConsts, length ps), ins) where
  compilerOut = second (compile storage ps) <$> ds
  ciTypes = foldl' union [] $ callIndirectTypes . snd . snd <$> compilerOut
  ins = second fst <$> compilerOut
  strConsts = mkStrConsts $ union (SBS.pack . fmap (fromIntegral . ord) <$> storage) $ nub $ concat $ stringConstants . snd . snd <$> compilerOut
  wasmDecl w = (w, wasmType [] $ fst $ fromJust $ lookup w ts)
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
  translateType (TC "Actor") = Ref "Actor"
  translateType t = error $ "no corresponding wasm type: " ++ show t
  funs = M.fromList $ ((\(name, Ast (Lam as _)) -> (name, length as)) <$> ds)

tag_const :: Tag -> CustomWasmOp a
tag_const = I32_const . fromIntegral . fromEnum

insToBin :: Boost -> (GlobalTable, [(String, [Ins])]) -> DfnWasm
insToBin (Boost imps morePrims moreFuns) ((exs, funs, wrapme, ciTypes, (hp0, strConsts), persistCount), gmachine) = DfnWasm
  { legacyArities = ((\s -> (s, fst $ getGlobal s)) <$> exs)
  , wasmBinary = wasm
  } where
  wasm = concat
    [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.
    , sect 1 $ uncurry encSig . snd <$> BM.assocs typeMap  -- Type section.
    , sect 2 $ importFun <$> imps  -- Import section.
    , sect 3 $ pure . fst . fst . snd <$> wasmFuns  -- Function section.
    , sect 4 [[encType AnyFunc, 0] ++ leb128 256]  -- Table section (0 = no-maximum).
    , sect 5 [[0, nPages]]  -- Memory section (0 = no-maximum).
    , sect 6 $  -- Global section (1 = mutable).
      [ [encType I32, 1, 0x41] ++ leb128 (65536*nPages - 4) ++ [0xb]  -- SP
      , [encType I32, 1, 0x41] ++ leb128 hp0 ++ [0xb]  -- HP
      , [encType I32, 1, 0x41, 0, 0xb]  -- BP
      ]
      -- Persistent globals.
      ++ replicate persistCount [encType I32, 1, 0x41, 0, 0xb]
    , sect 7 $  -- Export section.
      [ encStr "memory" ++ [2, 0]  -- 2 = external_kind Memory, 0 = memory index.
      , encStr "table" ++ [1, 0]  -- 1 = external_kind Table, 0 = memory index.
      , exportFun "#main" "#main"
      , exportFun "#getsp" "#getsp"
      , exportFun "#setsp" "#setsp"
      , exportFun "#gethp" "#gethp"
      , exportFun "#sethp" "#sethp"
      ]
      -- The "contract" functions are exported with "_" prepended.
      ++ [exportFun ('_':s) s | s <- exs]
      -- The "wdecl" functions are exported verbatim.
      ++ [exportFun s ('@':s) | (s, _) <- wrapme]
      -- The call_indirect functions for each type.
      ++ [exportFun s s | (s, _) <- ciFuns]
    , sect 10 $ encProcedure . snd <$> wasmFuns  -- Code section.
    , sect 11 $ encStrConsts <$> M.assocs strConsts  -- Data section.
    , 0 : lenc (encStr "dfn" ++ (ord <$> show wrapme))  -- Custom section.
    ]
  encStrConsts (s, offset) = concat
    [ [0, 0x41, offset, 0xb]
    , leb128 $ 8 + SBS.length s
    , [fromEnum TagString, 0, 0, 0]
    , take 4 $ leb128 (SBS.length s) ++ repeat 0
    , fromIntegral <$> SBS.unpack s
    ]
  -- 0 = external_kind Function.
  importFun ((m, f), ty) = encStr m ++ encStr f ++ [0, uncurry typeNo ty]
  typeNo ins outs = typeMap BM.!> (ins, outs)
  typeMap = BM.fromList $ zip [0..] $ nub $
    (snd <$> imps) ++  -- Types of imports
    (snd <$> wrapme) ++  -- wdecl functions.
    (flip (,) [] <$> ciTypes) ++  -- call_indirect types.
    (fst . snd <$> internalFuns)  -- Types of internal functions.
  exportFun name internalName = encStr name ++ [0, wasmFunNo internalName]
  -- TODO: Remove "#nfsyscall".
  localCount "#nfsyscall" = 2
  localCount _ = 0
  -- Returns arity and 0-indexed number of given global function.
  getGlobal s = case M.lookup s funs of
    Just arity -> (arity, wasmFunNo s - firstPrim)
    Nothing -> (arityFromType $ fromMaybe (error $ "BUG! bad global: " ++ s) $ M.lookup s primsType, wasmFunNo s - firstPrim)
  firstPrim = wasmFunNo $ fst $ head prims
  internalFuns =
    [ ("#eval", (([], []), evalAsm))
    , ("#mkap", (([], []), mkApAsm))
    , ("#pushint", (([I64], []), pushIntAsm))
    , ("#pushref", (([I32], []), pushRefAsm))
    , ("#push", (([I32], []), pushAsm))
    , ("#pushglobal", (([I32, I32], []), pushGlobalAsm))
    , ("#updatepop", (([I32], []), updatePopAsm))
    , ("#updateind", (([I32], []), updateIndAsm))
    , ("#alloc", (([I32], []), allocAsm))
    , ("#getsp", (([], [I32]), [Get_global sp, End]))
    , ("#setsp", (([I32], []), [Get_local 0, Set_global sp, End]))
    , ("#gethp", (([], [I32]), [Get_global hp, End]))
    , ("#sethp", (([I32], []), [Get_local 0, Set_global hp, End]))
    , ("#pairwith42", (([I32], []), pairWith42Asm))
    , ("#nil42", (([], []), nil42Asm))
    , ("#setpersist", (([I32, I32], []), setPersistAsm persistCount))
    , ("#getpersist", (([I32], [I32]), getPersistAsm persistCount))
    -- Outer "#main" function. It calls the internal "main" function.
    , ("#main", (([], []),
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
      ++ [End]))
    ] ++ (second (second $ concatMap deQuasi) <$> moreFuns)
  wasmFuns =
    (second (first (\(ins, outs) -> (typeNo ins outs, 0))) <$> internalFuns)
    -- Primitive functions.
    -- The assembly for "#eval" requires that the primitive functions
    -- directly precede those defined in the program.
    ++ ((\(s, p) -> (s, ((typeNo [] [], localCount s), p))) <$> prims)
    -- Functions from the program.
    ++ ((\(f, g) -> (f, ((typeNo [] [], 0), (++ [End]) $ concatMap fromIns g))) <$> gmachine)
    -- Wrappers for call_indirect calls.
    ++ ciFuns
    -- Wrappers for functions in "wdecl" section.
    ++ (wrap <$> wrapme)

  ciFuns = wrapCallIndirect <$> ciTypes
  -- When sending a message with only one item, we have a bare argument
  -- instead of an argument tuple
  wrapCallIndirect [t] = (show [t], ((typeNo [] [], 0),
    -- Evaluate single argument.
    concatMap fromIns [ Push 1, Eval ] ++
    (case t of
      I64 ->
        [ Get_global sp  -- PUSH [[sp + 4] + 8].64
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_const 8
        , I32_add
        , I64_load 3 0
        ]
      _ ->
        [ Get_global sp  -- PUSH [[sp + 4] + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_const 4
        , I32_add
        , I32_load 2 0
        ]
    ) ++
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    ] ++
    -- Get slot.
    concatMap fromIns [ Push 0, Eval ] ++
    [ Get_global sp  -- PUSH [[sp + 4] + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Call_indirect $ typeNo [t] []
    , Get_global sp  -- sp = sp + 16
    , I32_const 16
    , I32_add
    , Set_global sp
    , Call $ wasmFunNo "#nil42"
    , End
    ]))
  wrapCallIndirect ty = (show ty, ((typeNo [] [], 0),
    -- Evaluate argument tuple.
    concatMap fromIns [ Push 1, Eval ] ++
    concat [
      [ Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
      , Get_global sp  -- [sp + 4] = [[sp + 8] + k]
      , I32_const 4
      , I32_add
      , Get_global sp
      , I32_const 8
      , I32_add
      , I32_load 2 0
      , I32_const k
      , I32_add
      , I32_load 2 0
      , I32_store 2 0
      , Call $ wasmFunNo "#eval"  -- Evaluate.
      ] ++ (case t of
        I64 ->
          [ Get_global sp  -- PUSH [[sp + 4] + 8].64
          , I32_const 4
          , I32_add
          , I32_load 2 0
          , I32_const 8
          , I32_add
          , I64_load 3 0
          ]
        _ ->
          [ Get_global sp  -- PUSH [[sp + 4] + 4]
          , I32_const 4
          , I32_add
          , I32_load 2 0
          , I32_const 4
          , I32_add
          , I32_load 2 0
          ]
      ) ++
      [ Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      ] | (t, k) <- zip ty [8, 12..]] ++
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    ] ++
    -- Get slot.
    concatMap fromIns [ Push 0, Eval ] ++
    [ Get_global sp  -- PUSH [[sp + 4] + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Call_indirect $ typeNo ty []
    , Get_global sp  -- sp = sp + 16
    , I32_const 16
    , I32_add
    , Set_global sp
    , Call $ wasmFunNo "#nil42"
    , End
    ]))

  wasmFunMap = M.fromList $ zip (((\(m, f) -> m ++ "." ++ f) . fst <$> imps) ++ (fst <$> wasmFuns)) [0..]
  -- wasmFunNo = (wasmFunMap M.!)
  wasmFunNo s = fromMaybe (error s) $ M.lookup s wasmFunMap

  refToI32 (Ref _) = I32
  refToI32 t = t
  wrap (f, (ins, outs)) = (,) ('@':f) $ (,) (typeNo ins outs, 0) $
    -- Given a function call represented as a tree t on the stack, the
    -- G-machine ordinarily:
    --
    --   1. Removes the spine, so the arguments lie on the stack. The node
    --   t is preserved, and follows the arguments.
    --   2. Calls the wasm top-level function. The result is pushed on the
    --   stack.
    --   3. The call in step 2 finishes by overwriting t with an indirection
    --   node (lazy update).
    --
    -- Here, we simulate step 1, so we provide a destination for the
    -- lazy update in step 3. (It's never used; we should optimize away
    -- unnecessary updates one day.)
    --
    -- All functions that receive messages are IO (otherwise why bother
    -- sending?) and the IO monad requires special treatment.
    -- Top-level IO functions return functions that expect a #RealWorld
    -- argument. (In contrast, the return and bind functions expect a
    -- #RealWorld dummy argument,)
    --
    -- Thus the top of the stack must be an Ap node whose right child
    -- is #RealWorld. (Morally, the left child should be the function call t
    -- but our spine removal is indifferent. Our stack dumping routine can
    -- get confused though.)

    -- Start with a spined #RealWorld.
    [ Get_global hp  -- [hp] = TagAp
    , tag_const TagAp
    , I32_store 2 0
    , Get_global hp  -- [hp + 12] = 42
    , I32_const 12
    , I32_add
    , I32_const 42
    , I32_store 2 0
    , Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    -- Anticipate UpdatePop.
    , Get_global sp  -- [sp] = hp
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
    [ Get_local i
    , Call $ wasmFunNo "#pushint"
    ]
  wdeclIn I32 i =
    [ Get_local i
    , Call $ wasmFunNo "#pushref"  -- Evaluate.
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
    -- For JS demo. Returns first 32 bits of an Int.
    {-
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
    -}
  wdeclOut _ = error "TODO"
  sect t xs = t : lenc (varlen xs ++ concat xs)
  encStr s = lenc $ ord <$> s
  encProcedure ((_, 0), body) = lenc $ 0:concatMap encWasmOp body
  encProcedure ((_, locCount), body) = lenc $ ([1, locCount, encType I32] ++) $ concatMap encWasmOp body
  encType I32 = 0x7f
  encType I64 = 0x7e
  encType (Ref _) = encType I32
  encType AnyFunc = 0x70
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
    , Set_global sp  -- restore bp, sp
    , Set_global bp
    ] ++ nest n ++ [End]
    where
      n = length prims + length gmachine + length ciFuns
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ firstPrim + k - 1, Return]

  getPersistAsm :: Int -> [WasmOp]
  getPersistAsm 0 = [ I32_const 0, End ]
  getPersistAsm count =
    nest count ++ [End]
    where
      nest 1 =
        [ Block Nada
          [ Get_local 0   -- branch on local0 (persistent global index)
          , Br_table [0..count - 1] (count - 1)
          ]
        , Get_global 3
        , Return
        ]
      nest j =
        [ Block Nada $ nest (j - 1)
        , Get_global $ 2 + j
        , Return
        ]
  setPersistAsm :: Int -> [WasmOp]
  setPersistAsm 0 = [End]
  setPersistAsm count =
    [ Get_local 1   -- PUSH local1 (I32 to store)
    ] ++ nest count ++ [End]
    where
      nest 1 =
        [ Block Nada
          [ Get_local 0   -- branch on local0 (persistent global index)
          , Br_table [0..count - 1] (count - 1)
          ]
        , Set_global 3
        , Return
        ]
      nest j =
        [ Block Nada $ nest (j - 1)
        , Set_global $ 2 + j
        , Return
        ]
  intAsm :: WasmOp -> [WasmOp]
  intAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
    [ Get_global sp  -- PUSH [[sp + 4] + 8]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I64_load 3 0
    , Get_global sp  -- sp = sp + 8
    , I32_const 8
    , I32_add
    , Set_global sp
    , Get_global sp  -- PUSH [[sp] + 8]
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I64_load 3 0
    , op
    , Call $ wasmFunNo "#pushint"
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

  -- Primitive functions.
  primsMinimal :: [(String, [WasmOp])]
  primsMinimal =
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
    , ("Databuf-toAny", concatMap deQuasi idLazyAsm)
    , ("Databuf-fromAny", concatMap deQuasi idLazyAsm)
    , ("Port-toAny", concatMap deQuasi idLazyAsm)
    , ("Port-fromAny", concatMap deQuasi idLazyAsm)
    , ("Int-toAny", concatMap deQuasi intToAnyAsm)
    , ("Int-fromAny", concatMap deQuasi intFromAnyAsm)
    , ("set_any", concatMap deQuasi setAnyAsm)
    , ("get_any", concatMap deQuasi getAnyAsm)
    ]
  pairWith42Asm :: [WasmOp]
  pairWith42Asm =  -- [sp + 4] = (local0, #RealWorld)
    [ Get_global hp  -- [hp] = TagSum | (2 << 8)
    , I32_const $ fromIntegral $ fromEnum TagSum + 256 * 2
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = 0
    , I32_const 4
    , I32_add
    , I32_const 0
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = bp
    , I32_const 8
    , I32_add
    , Get_local 0
    , I32_store 2 0
    , Get_global hp  -- [hp + 12] = 42
    , I32_const 12
    , I32_add
    , I32_const 42
    , I32_store 2 0
    , Get_global sp  -- [sp + 4] = hp
    , I32_const 4
    , I32_add
    , Get_global hp
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    , End
    ]
  -- | [sp + 4] = ((), #RealWorld)
  -- TODO: Optimize by placing this special value at a known location in memory.
  nil42Asm :: [WasmOp]
  nil42Asm =
    [ Get_global hp  -- [hp].64 = TagSum
    , I64_const $ fromIntegral $ fromEnum TagSum
    , I64_store 3 0
    , Get_global hp  -- PUSH hp
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    , Call $ wasmFunNo "#pairwith42"
    , End
    ]
  deQuasi :: QuasiWasm -> [WasmOp]
  deQuasi (Custom x) = case x of
    CallSym s -> [Call $ wasmFunNo s]
    CallIndirectType ins outs -> [Call_indirect $ typeNo ins outs]
    ReduceArgs n -> concat $ replicate n $ concatMap fromIns [Push (n - 1), Eval]

  deQuasi (Block t body) = [Block t $ concatMap deQuasi body]
  deQuasi (Loop  t body) = [Loop  t $ concatMap deQuasi body]
  deQuasi (If    t body) = [If    t $ concatMap deQuasi body]
  deQuasi (op) = [error "missing deQuasi case?" <$> op]

  prims = primsMinimal ++ (second (concatMap deQuasi . snd) <$> morePrims)
  primsType = M.fromList $ [(s, snd $ preludeMinimal M.! s) | s <- fst <$> primsMinimal]
    ++ (second fst <$> morePrims)

  fromIns :: Ins -> [WasmOp]
  fromIns instruction = case instruction of
    Trap -> [ Unreachable ]
    Eval -> [ Call $ wasmFunNo "#eval" ]  -- (Tail call.)
    PushInt n -> [ I64_const n, Call $ wasmFunNo "#pushint" ]
    PushRef n -> [ I32_const n, Call $ wasmFunNo "#pushref" ]
    Push n -> [ I32_const $ fromIntegral $ 4*(n + 1), Call $ wasmFunNo "#push" ]
    MkAp -> [ Call $ wasmFunNo "#mkap" ]
    PushGlobal fun | (n, g) <- getGlobal fun ->
      [ I32_const $ fromIntegral $ fromEnum TagGlobal + 256*n
      , I32_const $ fromIntegral g
      , Call $ wasmFunNo "#pushglobal"
      ]
    PushString sbs ->
      [ Get_global sp  -- [sp] = address of string const
      , I32_const $ fromIntegral $ strConsts M.! sbs
      , I32_store 2 0
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
      ]
    PushCallIndirect ty ->
      [ Get_global sp  -- [sp] = hp
      , Get_global hp
      , I32_store 2 0
      -- 3 arguments: slot, argument tuple, #RealWorld.
      , Get_global hp  -- [hp] = TagGlobal | (3 << 8)
      , I32_const $ fromIntegral $ fromEnum TagGlobal + 256*3
      , I32_store 2 0
      , Get_global hp  -- [hp + 4] = wrapCallIndirect (show ty)
      , I32_const 4
      , I32_add
      , I32_const $ fromIntegral $ wasmFunNo (show ty) - firstPrim
      , I32_store 2 0
      , Get_global hp  -- hp = hp + 16
      , I32_const 16
      , I32_add
      , Set_global hp
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
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
    Alloc n -> [ I32_const $ fromIntegral n, Call $ wasmFunNo "#alloc" ]
    UpdateInd n ->
      [ I32_const $ fromIntegral $ 4*(n + 1), Call $ wasmFunNo "#updateind" ]
    UpdatePop n ->
      [ I32_const $ fromIntegral $ 4*(n + 1)
      , Call $ wasmFunNo "#updatepop"
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

sp, hp, bp :: Int
[sp, hp, bp] = [0, 1, 2]

compile :: [String] -> [String] -> Ast -> ([Ins], CompilerState)
compile storage ps d = runState (mk1 storage ps d) $ CompilerState [] [] []

mk1 :: [String] -> [String] -> Ast -> State CompilerState [Ins]
mk1 storage pglobals (Ast ast) = case ast of
  -- | Thanks to lambda lifting, `Lam` can only occur at the top level.
  Lam as b -> do
    putBindings $ zip as [0..]
    (++ [UpdatePop $ length as, Eval]) <$> rec b
  I n -> pure [PushInt n]
  S s -> do
    st <- get
    put st { stringConstants = s:stringConstants st }
    pure [PushString s]
  t :@ u -> do
    mu <- rec u
    bump 1
    mt <- rec t
    bump (-1)
    pure $ case last mt of
      Copro _ _ -> mu ++ mt
      _ -> concat [mu, mt, [MkAp]]
  Far ty -> do
    st <- get
    put $ st { callIndirectTypes = callIndirectTypes st `union` [ty] }
    pure [PushCallIndirect ty]
  Var "undefined" -> pure [Trap]
  Var v -> do
    m <- getBindings
    pure $ case lookup v m of
      Just k -> [Push k]
      -- Storage maps become PushString instructions.
      _ | v `elem` storage -> [PushString $ SBS.pack $ fromIntegral . ord <$> v]
      -- Persistent globals become PushRef instructions.
      _ | Just i <- elemIndex v pglobals -> [PushRef $ fromIntegral i]
      _ -> [PushGlobal v]
  Pack n m -> pure [Copro n m]
  Cas expr alts -> do
    me <- rec expr
    xs <- forM alts $ \(p, body) -> do
      orig <- getBindings
      (f, b) <- case fromApList p of
        (Ast (Pack n _):vs) -> do
          bump $ length vs
          modifyBindings (zip (map (\(Ast (Var v)) -> v) vs) [0..] ++)
          bod <- rec body
          pure (Just $ fromIntegral n, Split (length vs) : bod ++ [Slide (length vs)])
        [Ast (Var s)] -> do
          bump 1
          modifyBindings ((s, 0):)
          (,) Nothing . (++ [Slide 1]) <$> rec body
        _ -> undefined
      putBindings orig
      pure (f, b)
    pure $ me ++ [Eval, Casejump xs]
  Let ds body -> let n = length ds in do
    orig <- getBindings
    bump n
    modifyBindings (zip (fst <$> ds) [n-1,n-2..0] ++)
    dsAsm <- mapM rec $ snd <$> ds
    b <- rec body
    putBindings orig
    pure $ Alloc n : concat (zipWith (++) dsAsm (pure . UpdateInd <$> [n-1,n-2..0])) ++ b ++ [Slide n]
  _ -> error $ "TODO: compile: " ++ show ast
  where
    bump n = modifyBindings $ fmap $ second (+n)
    modifyBindings f = putBindings =<< f <$> getBindings
    getBindings = bindings <$> get
    putBindings b = do
      st <- get
      put st { bindings = b }
    rec = mk1 storage pglobals

fromApList :: Ast -> [Ast]
fromApList (Ast (a :@ b)) = fromApList a ++ [b]
fromApList a = [a]

mkApAsm :: [WasmOp]
mkApAsm =
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
  , End
  ]
pushIntAsm :: [WasmOp]
pushIntAsm =
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
  , Get_global hp  -- [hp + 8] = local_0
  , I32_const 8
  , I32_add
  , Get_local 0
  , I64_store 3 0
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , End
  ]
pushRefAsm :: [WasmOp]
pushRefAsm =
  [ Get_global sp  -- [sp] = hp
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp - 4
  , I32_const 4
  , I32_sub
  , Set_global sp
  , Get_global hp  -- [hp] = TagRef
  , tag_const TagRef
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = local_0
  , I32_const 4
  , I32_add
  , Get_local 0
  , I32_store 2 0
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , End
  ]
pushAsm :: [WasmOp]
pushAsm =
  [ Get_global sp  -- [sp] = [sp + local_0]
  , Get_global sp
  , Get_local 0  -- Should be 4*(n + 1).
  , I32_add
  , I32_load 2 0
  , I32_store 2 0
  , Get_global sp  -- sp = sp - 4
  , I32_const 4
  , I32_sub
  , Set_global sp
  , End
  ]
pushGlobalAsm :: [WasmOp]
pushGlobalAsm =
  [ Get_global sp  -- [sp] = hp
  , Get_global hp
  , I32_store 2 0
  , Get_global hp  -- [hp] = local_0 (should be TagGlobal | (n << 8))
  , Get_local 0
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = local_1 (should be local function index)
  , I32_const 4
  , I32_add
  , Get_local 1
  , I32_store 2 0
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , Get_global sp  -- sp = sp - 4
  , I32_const 4
  , I32_sub
  , Set_global sp
  , End
  ]
updatePopAsm :: [WasmOp]
updatePopAsm =
  [ Get_global sp  -- bp = [sp + 4]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Set_global bp
  , Get_global sp  -- sp = sp + local_0
  , Get_local 0  -- Should be 4*(n + 1).
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
  , End
  ]
allocAsm :: [WasmOp]
allocAsm =
  [ Loop Nada
    [ Get_local 0  -- Break when local0 == 0
    , I32_eqz
    , Br_if 1
    , Get_local 0  -- local0 = local0 - 1
    , I32_const 1
    , I32_sub
    , Set_local 0
    , Get_global sp  -- [sp] = hp
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
    , Br 0
    ]
  , End
  ]
updateIndAsm :: [WasmOp]
updateIndAsm =
  [ Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  -- local0 should be 4*(n + 1)
  , Get_global sp  -- [[sp + local0] + 4] = [sp]
  , Get_local 0
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , Get_global sp
  , I32_load 2 0
  , I32_store 2 0
  , End
  ]
setAnyAsm :: [QuasiWasm]
setAnyAsm =
  [ Custom $ ReduceArgs 2
  , Get_global sp  -- PUSH [[sp + 4] + 4]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Get_global sp  -- PUSH [[sp + 8] + 4]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Custom $ CallSym "#setpersist"
  , Get_global sp  -- sp = sp + 20
  , I32_const 20
  , I32_add
  , Set_global sp
  , Custom $ CallSym "#nil42"
  , End
  ]
getAnyAsm :: [QuasiWasm]
getAnyAsm =
  [ Custom $ ReduceArgs 1
  , Get_global hp  -- [hp] = TagRef
  , tag_const TagRef
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = ...
  , I32_const 4
  , I32_add
  , Get_global sp  -- #getpersist [[sp + 4] + 4]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , Custom $ CallSym "#getpersist"
  , I32_store 2 0  -- ...result of #getpersist.
  , Get_global hp  -- PUSH hp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , Get_global sp  -- sp = sp + 12
  , I32_const 12
  , I32_add
  , Set_global sp
  , Custom $ CallSym "#pairwith42"
  , End
  ]
idLazyAsm :: [QuasiWasm]
idLazyAsm =
  [ Custom $ ReduceArgs 1
  , I32_const 8
  , Custom $ CallSym "#updatepop"
  , Custom $ CallSym "#eval"
  , End
  ]
intToAnyAsm :: [QuasiWasm]
intToAnyAsm =
  [ Custom $ ReduceArgs 1
  , Get_global sp  -- PushRef $ memory.externalize ([sp + 4] + 8) 8
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I32_const 8
  , Custom $ CallSym "memory.externalize"
  , Custom $ CallSym "#pushref"
  -- UpdatePop 2, not 1, because PushRef creates an extra stack item.
  , I32_const 12  -- UpdatePop 2, Eval, End
  , Custom $ CallSym "#updatepop"
  , Custom $ CallSym "#eval"
  , End
  ]
intFromAnyAsm :: [QuasiWasm]
intFromAnyAsm =
  [ Custom $ ReduceArgs 1
  , Get_global hp  -- [hp] = TagInt
  , tag_const TagInt
  , I32_store 2 0
  , Get_global hp  -- memory.internalize (hp + 8) 8 [[sp + 4] + 4] 0
  , I32_const 8
  , I32_add
  , I32_const 8
  , Get_global sp
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 0
  , Custom $ CallSym "memory.internalize"
  , Get_global sp  -- [sp + 4] = hp
  , I32_const 4
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , I32_const 8  -- UpdatePop 1, Eval, End
  , Custom $ CallSym "#updatepop"
  , Custom $ CallSym "#eval"
  , End
  ]
