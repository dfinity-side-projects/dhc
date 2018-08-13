{-# LANGUAGE CPP #-}
module Encode
  ( encodeWasm
  , ProtoWasm(..)
  , leb128
  , sleb128
  , enc32
  , encType
  , WasmFun(..)
  ) where

import Control.Arrow
#ifdef __HASTE__
import qualified Data.Set as IS
import qualified Data.Map.Strict as IM
#else
import Data.IntMap.Strict (restrictKeys)
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
#endif
import Data.Bits
import Data.Char
import Data.List
import WasmOp

#ifdef __HASTE__
type IntMap = IM.Map Int
type IntSet = IS.Set Int
restrictKeys :: IntMap a -> IntSet -> IntMap a
restrictKeys m s = IM.filterWithKey (\k _ -> IS.member k s) m
#endif

type FuncType = ([WasmType], [WasmType])

wasmHeader :: [Int]
wasmHeader = [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.

encWasmOp :: (FuncType -> Int) -> WasmOp -> [Int]
encWasmOp findSig op = case op of
  Get_local n -> 0x20 : leb128 n
  Set_local n -> 0x21 : leb128 n
  Tee_local n -> 0x22 : leb128 n
  Get_global n -> 0x23 : leb128 n
  Set_global n -> 0x24 : leb128 n
  I64_const n -> 0x42 : sleb128 n
  I32_const n -> 0x41 : sleb128 n
  Call n -> 0x10 : leb128 n
  Call_indirect sig -> 0x11 : leb128 (findSig sig) ++ [0]
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
  If t as [] -> [0x4, encType t] ++ concatMap rec as ++ [0xb]
  If t as bs -> concat
    [ [0x4, encType t]
    , concatMap rec as
    , [0x5]
    , concatMap rec bs
    , [0xb]
    ]
  Block t as -> [2, encType t] ++ concatMap rec as ++ [0xb]
  Loop t as -> [3, encType t] ++ concatMap rec as ++ [0xb]
  _ -> maybe (error $ "unsupported: " ++ show op) pure $ lookup op rZeroOps
  where rec = encWasmOp findSig

enc32 :: Int -> [Int]
enc32 n = (`mod` 256) . div n . (256^) <$> [(0 :: Int)..3]

encMartinType :: WasmType -> Int
encMartinType t = case t of
  Ref "Actor" -> 0x6f
  Ref "Module" -> 0x6e
  Ref "Port" -> 0x6d
  Ref "Databuf" -> 0x6c
  Ref "Elem" -> 0x6b
  _ -> encType t

encType :: WasmType -> Int
encType t = case t of
  I32 -> 0x7f
  I64 -> 0x7e
  F32 -> 0x7d
  F64 -> 0x7c
  AnyFunc -> 0x70
  Nada -> 0x40
  _ -> error $ "bad type:" ++ show t

standardSig :: FuncType -> FuncType
standardSig (a, b) = (standardType <$> a, standardType <$> b)

standardType :: WasmType -> WasmType
standardType t = case t of
  Ref _ -> I32
  _ -> t

leb128 :: Int -> [Int]
leb128 n | n < 128   = [n]
         | otherwise = 128 + (n `mod` 128) : leb128 (n `div` 128)

sleb128 :: (Bits a, Integral a) => a -> [Int]
sleb128 n | n < 0     = fromIntegral <$> f (n .&. 127) (shiftR n 7)
          | n < 64    = [fromIntegral n]
          | n < 128   = [128 + fromIntegral n, 0]
          | otherwise = 128 + (fromIntegral n `mod` 128) : sleb128 (n `div` 128)
          where
          f x (-1) | x < 64    = [x .|. 128, 127]
                   | otherwise = [x]
          f x y    = (x .|. 128):f (y .&. 127) (shiftR y 7)

encCustom :: String -> [[Int]] -> [Int]
encCustom s xs = 0 : lenc (encStr s ++ varlen xs ++ concat xs)

encStr :: String -> [Int]
encStr s = lenc $ ord <$> s

varlen :: [a] -> [Int]
varlen xs = leb128 $ length xs

lenc :: [Int] -> [Int]
lenc xs = varlen xs ++ xs

data ProtoWasm = ProtoWasm
  { sectImports :: [((String, String), FuncType)]
  , sectFunctions :: [WasmFun]
  , tableSize :: Int
  , sectGlobals :: [[Int]]
  , sectExports :: [(String, Int)]
  , sectElements :: [(Int, [Int])]
  , sectPersist :: [(Int, WasmType)]
  , sectDfn :: [(Int, [WasmType])]
  , sectsCustom :: [(String, [[Int]])]
  , sectsGeneric :: [(Int, [[Int]])]
  }

encodeWasm :: ProtoWasm -> [Int]
encodeWasm fatP = concat
  [ wasmHeader
  -- Custom sections using Martin's annotations.
  , encCustom "types" $ encMartinTypes . snd <$> sectDfn p
  -- Martin subtracts the number of imports from the function index.
  , encCustom "typeMap" $ zipWith (++) (leb128 . (+(-length (sectImports p))) . fst <$> sectDfn p) $ leb128 <$> [0..]
  -- Encodes persistent globals.
  , encCustom "persist" . fmap encMartinGlobal . sortOn fst $ sectPersist p
  , encSect 1 $ encSig <$> sigs  -- Type section.
  , encSect 2 $ importFun <$> sectImports p  -- Import section.
  , encSect 3 $ pure . findSig . typeSig <$> sectFunctions p  -- Function section.
  -- Table section.
  -- Selects "no-maximum" (0).
  , if tableSize p == 0 then [] else encSect 4 [[encType AnyFunc, 0] ++ leb128 (tableSize p)]
  , concat $ getSect 5
  , encSect 6 $ sectGlobals p  -- Global section.
  , encSect 7 $  -- Export section.
    -- The "public" functions.
    [encStr s ++ (0 : leb128 n) | (s, n) <- sectExports p] ++
    [ encStr "memory" ++ [2, 0]  -- 2 = external_kind Memory, 0 = memory index.
    , encStr "table" ++ [1, 0]  -- 1 = external_kind Table, 0 = memory index.
    ]
  -- Export all globals. Forbidden by the spec, but our engine can handle it.
#ifndef __HASTE__
    ++ [ encStr ("global" ++ show n) ++ (3:leb128 n) | n <- [0..length (sectGlobals p) - 1]]
#endif
  , concat $ getSect 8
  -- Element section.
  , if null $ sectElements p then [] else
    encSect 9 $ encTableChunk <$> sectElements p
  , encSect 10 $ encProcedure <$> sectFunctions p
  , concat $ getSect 11
  , concatMap (uncurry encCustom) $ sectsCustom p
  ]
  where
  p = trim fatP
  encTableChunk (offset, entries) =
    [ 0  -- Table 0 (only one in MVP).
    , 0x41] ++ leb128 offset ++ [0xb]
    ++ leb128 (length entries)
    ++ concatMap leb128 entries
  getSect k
    | Just ns <- lookup k $ sectsGeneric p = [encSect k ns]
    | otherwise = []
  sigs = nub $ fmap standardSig $
    (snd <$> sectImports p) ++  -- Types of imports.
    (typeSig <$> sectFunctions p) ++  -- Types of functions.
    concatMap (concatMap ciType . funBody) (sectFunctions p) -- Types of Call_indirect types.
  ciType (Call_indirect t) = [t]
  ciType (Block _ xs) = concatMap ciType xs
  ciType (Loop _ xs) = concatMap ciType xs
  ciType (If _ xs ys) = concatMap ciType $ xs ++ ys
  ciType _ = []
  encSig (ins, outs) = 0x60 : lenc (encType <$> ins) ++ lenc (encType <$> outs)
  findSig :: FuncType -> Int
  findSig sig
    | Just n <- sigIndex = n
    | otherwise = error $ "BUG! missing sig in type section: " ++ show sig
    where sigIndex = elemIndex (standardSig sig) sigs
  importFun ((m, f), ty) = encStr m ++ encStr f ++ [0, findSig ty]
  encMartinTypes ts = 0x60 : lenc (encMartinType <$> ts) ++ [0]
  encMartinGlobal (i, t) = [3] ++ leb128 i ++ leb128 (encMartinType t)
  encProcedure wf = lenc $ leb128 (length $ localVars wf) ++
    concatMap (\t -> [1, encType $ standardType t]) (localVars wf) ++
    concatMap (encWasmOp findSig) (funBody wf)
  encSect t xs = t : lenc (varlen xs ++ concat xs)

-- Trim unreachable wasm code.
trim :: ProtoWasm -> ProtoWasm
trim p = p
  { sectImports = liveImps
  , sectFunctions = IM.elems liveFuns
  , sectExports = second (liveRenames IM.!) <$> sectExports p
  , sectElements = filter (not . null . snd) $ second (map (liveRenames IM.!)) <$> sectElements p
  , sectDfn = first (liveRenames IM.!) <$> sectDfn p
  }
  where
  nonImports = IM.fromList $ zip [length $ sectImports p..] $ sectFunctions p
  liveCalls = followCalls ((snd <$> sectExports p) `union` concatMap snd (sectElements p)) $ funBody <$> nonImports
  liveRenames = IM.fromList $ zip (IS.elems liveCalls) [0..]
  liveImps = map snd $ filter ((`IM.member` liveRenames) . fst) $ zip [0..] $ sectImports p
  liveFuns = (\wf -> wf { funBody = renumberCalls liveRenames $ funBody wf }) <$> restrictKeys nonImports (IM.keysSet liveRenames)
