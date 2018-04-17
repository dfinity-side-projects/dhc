{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE NamedFieldPuns #-}
module Asm
  ( hsToWasm
  , Ins(..)
  , WasmType(Ref)  -- Re-export from WasmOp.
  , hsToIns
  , hsToGMachine
  , enc32
  ) where

import Control.Arrow
#ifdef __HASTE__
import "mtl" Control.Monad.State
#else
import Control.Monad.State
import Data.ByteString.Short (ShortByteString, unpack)
import qualified Data.ByteString.Short as SBS
import Data.Semigroup
#endif
import qualified Data.Bimap as BM
import Data.Char
import Data.Int
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import Boost
import DHC
import Std
import WasmOp

#ifdef __HASTE__
sbslen :: String -> Int
sbslen = length
unpack :: String -> [Int]
unpack = fmap ord
type ShortByteString = String
#else
sbslen :: ShortByteString -> Int
sbslen = SBS.length
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

data WasmMeta = WasmMeta
  -- Arity of each user-defined function, whether exported or not.
  -- Eval uses this to remove the spine correctly.
  { arities :: Map String Int
  , exports :: [(String, [WasmType])]  -- List of wdecl functions.
  , callTypes :: [[WasmType]]  -- Types needed by call_indirect ops.
  , initialHP :: Int  -- Initial HP.
  , strAddrs :: Map ShortByteString Int  -- String constant addresses.
  , storeCount :: Int  -- Global store count.
  }

hsToGMachine :: Boost -> String -> Either String (Map String Int, [(String, [Ins])])
hsToGMachine boost hs = first arities <$> hsToIns boost hs

hsToWasm :: Boost -> String -> Either String [Int]
hsToWasm boost s = insToBin s b . astToIns <$> hsToAst b qq s where
  b = stdBoost <> boost
  qq "here" h = Right h
  qq "wasm" prog = case hsToWasm boost prog of
    Left err -> Left err
    Right ints -> Right $ chr <$> ints
  qq _ _ = Left "bad scheme"

hsToIns :: Boost -> String -> Either String (WasmMeta, [(String, [Ins])])
hsToIns boost s = astToIns <$> hsToAst (stdBoost <> boost) qq s where
  qq "here" h = Right h
  qq _ _ = Left "bad scheme"

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
  f (k, ds) (s:rest) = f (k + 16 + align4 (sbslen s), ((s, k):ds)) rest

astToIns :: Clay -> (WasmMeta, [(String, [Ins])])
astToIns cl = (WasmMeta funs (wasmDecl <$> wdecls cl) ciTypes initHP addrs $ length $ stores cl, ins) where
  compilerOut = second (compile $ stores cl) <$> supers cl
  ciTypes = foldl' union [] $ callIndirectTypes . snd . snd <$> compilerOut
  ins = second fst <$> compilerOut
  (initHP, addrs) = mkStrConsts $ nub $ concat $ stringConstants . snd . snd <$> compilerOut
  wasmDecl w = (w, wasmType [] $ fst $ fromJust $ lookup w $ funTypes cl)
  wasmType acc t = case t of
    a :-> b -> wasmType (translateType a : acc) b
    TApp (TC "IO") (TC "()") -> reverse acc
    -- TODO: Beef up type inference and make the following an error
    -- because it will be unreachable.
    _ -> reverse acc
  translateType (TC "Int") = I64
  translateType (TC "Port") = Ref "Port"
  translateType (TC "Databuf") = Ref "Databuf"
  translateType (TC "Actor") = Ref "Actor"
  translateType t = error $ "no corresponding wasm type: " ++ show t
  funs = M.fromList $ ((\(name, Ast (Lam as _)) -> (name, length as)) <$> supers cl)

enc32 :: Int -> [Int]
enc32 n = (`mod` 256) . (div n) . (256^) <$> [(0 :: Int)..3]

encMartinTypes :: [WasmType] -> [Int]
encMartinTypes ts = 0x60 : lenc (map f ts) ++ [0] where
  f I32 = 0x7f
  f I64 = 0x7e
  f F32 = 0x7d
  f F64 = 0x7c
  f AnyFunc = 0x70
  f (Ref "Actor") = 0x6f
  f (Ref "Port") = 0x6e
  f (Ref "Databuf") = 0x6d
  f (Ref "Elem") = 0x6c
  f (Ref "Link") = 0x6b
  f (Ref "Id") = 0x6a
  f _ = error "bad type"

insToBin :: String -> Boost -> (WasmMeta, [(String, [Ins])]) -> [Int]
insToBin src (Boost imps _ boostPrims boostFuns) (wm@WasmMeta {exports, strAddrs, storeCount}, gmachine) = wasm where
  encMartinTM :: String -> Int -> [Int]
  encMartinTM f t = leb128 (wasmFunNo ('@':f) - length imps) ++ leb128 t
  wasm = concat
    [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.

    -- Custom sections for Martin's Primea.
    , sectCustom "types" $ encMartinTypes . snd <$> exports
    , sectCustom "typeMap" $ zipWith encMartinTM (fst <$> exports) [0..]

    , sect 1 $ uncurry encSig . snd <$> BM.assocs typeMap  -- Type section.
    , sect 2 $ importFun <$> imps  -- Import section.
    , sect 3 $ pure . fst . fst . snd <$> wasmFuns  -- Function section.
    , sect 4 [[encType AnyFunc, 0] ++ leb128 256]  -- Table section (0 = no-maximum).
    , sect 5 [0 : leb128 nPages]  -- Memory section (0 = no-maximum).
    , sect 6 $  -- Global section (1 = mutable).
      [ [encType I32, 1, 0x41] ++ sleb128 memTop ++ [0xb]  -- SP
      , [encType I32, 1, 0x41] ++ sleb128 (initialHP wm) ++ [0xb]  -- HP
      , [encType I32, 1, 0x41, 0, 0xb]  -- BP
      ]
      -- Global stores.
      -- Extra global records if `main` has been run yet.
      ++ replicate (1 + storeCount) [encType I32, 1, 0x41, 0, 0xb]
    , sect 7 $  -- Export section.
      -- The "wdecl" functions are exported verbatim.
      [exportFun s ('@':s) | (s, _) <- exports] ++
      [ encStr "memory" ++ [2, 0]  -- 2 = external_kind Memory, 0 = memory index.
      , encStr "table" ++ [1, 0]  -- 1 = external_kind Table, 0 = memory index.
      ]
    , sect 10 $ encProcedure . snd <$> wasmFuns  -- Code section.
    , sect 11 $ encStrConsts <$> M.assocs strAddrs  -- Data section.
    , sectCustom "dfndbg" [ord <$> show (sort $ swp <$> (M.assocs $ wasmFunMap))]
    , sectCustom "dfnhs" [ord <$> src]
    ]
  swp (a, b) = (b, a)
  memTop = 65536*nPages - 4
  encStrConsts (s, offset) = concat
    [ [0, 0x41] ++ sleb128 offset ++ [0xb]
    , leb128 $ 16 + sbslen s
    , [fromEnum TagString, 0, 0, 0]
    , enc32 $ offset + 16
    , enc32 0
    , enc32 $ sbslen s
    , fromIntegral <$> unpack s
    ]
  -- 0 = external_kind Function.
  importFun ((m, f), ty) = encStr m ++ encStr f ++ [0, uncurry typeNo ty]
  typeNo ins outs = typeMap BM.!> (ins, outs)
  typeMap = BM.fromList $ zip [0..] $ nub $
    (snd <$> imps) ++  -- Types of imports
    (flip (,) [] . snd <$> exports) ++  -- wdecl functions.
    (flip (,) [] <$> callTypes wm) ++  -- call_indirect types.
    (fst . snd <$> internalFuns)  -- Types of internal functions.
  exportFun name internalName = encStr name ++ (0 : leb128 (wasmFunNo internalName))
  -- TODO: Remove "#nfsyscall".
  localCount "#nfsyscall" = 2
  localCount _ = 0
  -- Returns arity and 0-indexed number of given global function.
  getGlobal s = case M.lookup s $ arities wm of
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
    , ("#pairwith42", (([I32], []), pairWith42Asm))
    , ("#nil42", (([], []), nil42Asm))
    , ("#setstore", (([I32, I32], []), setStoreAsm storeCount))
    , ("#getstore", (([I32], [I32]), getStoreAsm storeCount))
    ] ++ (second (second $ concatMap deQuasi) <$> boostFuns)
  wasmFuns =
    (second (first (\(ins, outs) -> (typeNo ins outs, 0))) <$> internalFuns)
    -- Primitive functions.
    -- The assembly for "#eval" requires that the primitive functions
    -- directly precede those defined in the program.
    ++ ((\(s, p) -> (s, ((typeNo [] [], localCount s), p))) <$> prims)
    -- Functions from the program.
    ++ (fromGMachine <$> gmachine)
    -- Wrappers for call_indirect calls.
    ++ ciFuns
    -- Wrappers for functions in "wdecl" section.
    ++ (wrap <$> exports)

  fromGMachine (f, g) = (f, ((typeNo [] [], 0), (if f == "main"
    then ([I32_const 1, Set_global mainCalled] ++)
    else id) $ (++ [End]) $ concatMap fromIns g))

  ciFuns = wrapCallIndirect <$> callTypes wm
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
  wasmFunNo s = fromMaybe (error s) $ M.lookup s wasmFunMap

  refToI32 (Ref _) = I32
  refToI32 t = t
  wrap (f, ins) = (,) ('@':f) $ (,) (typeNo ins [], 0) $
    -- Wraps a DHC function.
    -- When a wasm function f(arg0, arg1, ...) is called,
    -- the arguments are placed in local variables.
    -- This wrapper builds:
    --
    --   f :@ arg0 :@ arg 1 :@ ... :@ #RealWorld
    --
    -- on the heap, places a pointer to his on the stack, then calls Eval.
    --
    -- Additionally, if a `main` function exists, then for each non-`main`
    -- function, check a global flag and run `main` if it is false.
    -- The `main` function should set this global flag to true.
    (if f /= "main" && M.member "main" wasmFunMap then
    [ Get_global mainCalled  -- if (!mainCalled) mainCalled = 1, main;
    , I32_eqz
    , If Nada (
      [ I32_const $ fromIntegral memTop  -- sp = top of memory
      , Set_global sp
      , Get_global sp  -- [sp] = 42
      , I32_const 42
      , I32_store 2 0
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp

      --, Call $ wasmFunNo "main"
      ] ++ concatMap fromIns [PushGlobal "main", MkAp, Eval])
    ]
    else []) ++

    [ I32_const $ fromIntegral memTop  -- sp = top of memory
    , Set_global sp
    , Get_global sp  -- [sp] = 42
    , I32_const 42
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    ] ++
    -- Input arguments are local variables.
    -- We move these to our stack in reverse order.
    concat (reverse $ zipWith wdeclIn (refToI32 <$> ins) [0..]) ++
    -- Build the spine.
    concatMap fromIns (PushGlobal f : replicate (length ins + 1) MkAp) ++
    [ Call $ wasmFunNo "#eval"
    , End
    ]
  wdeclIn I64 i =
    [ Get_local i
    , Call $ wasmFunNo "#pushint"
    ]
  wdeclIn I32 i =
    [ Get_local i
    , Call $ wasmFunNo "#pushref"
    ]
  wdeclIn _ _ = error "TODO"
  sect t xs = t : lenc (varlen xs ++ concat xs)
  sectCustom s xs = 0 : lenc (encStr s ++ varlen xs ++ concat xs)
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
      -- Globals are resolved in a giant `br_table`. This is ugly, but avoids
      -- run-time type-checking.
      n = length prims + length gmachine + length ciFuns
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ firstPrim + k - 1, Return]

  getStoreAsm :: Int -> [WasmOp]
  getStoreAsm 0 = [ I32_const 0, End ]
  getStoreAsm count =
    nest count ++ [End]
    where
      nest 1 =
        [ Block Nada
          [ Get_local 0   -- branch on local0 (global store index)
          , Br_table [0..count - 1] (count - 1)
          ]
        , Get_global storeOffset
        , Return
        ]
      nest j =
        [ Block Nada $ nest (j - 1)
        , Get_global $ storeOffset + j - 1
        , Return
        ]
  setStoreAsm :: Int -> [WasmOp]
  setStoreAsm 0 = [End]
  setStoreAsm count =
    [ Get_local 1   -- PUSH local1 (I32 to store)
    ] ++ nest count ++ [End]
    where
      nest 1 =
        [ Block Nada
          [ Get_local 0   -- branch on local0 (global store index)
          , Br_table [0..count - 1] (count - 1)
          ]
        , Set_global $ storeOffset
        , Return
        ]
      nest j =
        [ Block Nada $ nest (j - 1)
        , Set_global $ storeOffset + j - 1
        , Return
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
    ReduceArgs n -> concat $ replicate n $ concatMap fromIns [Push (n - 1), Eval]

  deQuasi (Block t body) = [Block t $ concatMap deQuasi body]
  deQuasi (Loop  t body) = [Loop  t $ concatMap deQuasi body]
  deQuasi (If    t body) = [If    t $ concatMap deQuasi body]
  deQuasi (op) = [error "missing deQuasi case?" <$> op]

  prims = second (concatMap deQuasi . snd) <$> boostPrims
  primsType = M.fromList $ second fst <$> boostPrims

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
    PushString s ->
      [ Get_global sp  -- [sp] = address of string const
      , I32_const $ fromIntegral $ strAddrs M.! s
      , I32_store 2 0
      , Get_global sp  -- sp = sp - 4
      , I32_const 4
      , I32_sub
      , Set_global sp
      ]
    PushCallIndirect ty ->
      -- 3 arguments: slot, argument tuple, #RealWorld.
      [ I32_const $ fromIntegral $ fromEnum TagGlobal + 256*3
      , I32_const $ fromIntegral $ wasmFunNo (show ty) - firstPrim
      , Call $ wasmFunNo "#pushglobal"
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
leb128 n | n < 128   = [n]
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

sp, hp, bp, mainCalled, storeOffset :: Int
[sp, hp, bp, mainCalled, storeOffset] = [0, 1, 2, 3, 4]

compile :: [String] -> Ast -> ([Ins], CompilerState)
compile ps d = runState (mk1 ps d) $ CompilerState [] [] []

mk1 :: [String] -> Ast -> State CompilerState [Ins]
mk1 pglobals (Ast ast) = case ast of
  -- Thanks to lambda lifting, `Lam` can only occur at the top level.
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
  CallSlot ty -> do
    st <- get
    put $ st { callIndirectTypes = callIndirectTypes st `union` [ty] }
    pure [PushCallIndirect ty]
  Var v -> do
    m <- getBindings
    pure $ case lookup v m of
      Just k -> [Push k]
      -- Global stores become PushRef instructions.
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
    rec = mk1 pglobals

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
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
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
