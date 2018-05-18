{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
#ifdef __HASTE__
{-# LANGUAGE PackageImports #-}
#endif
module Asm
  ( hsToWasm
  , Ins(..)
  , WasmType(..)  -- Re-export from WasmOp.
  , hsToIns
  , hsToGMachine
  , tpGlobalIndex
  ) where

import Control.Arrow
#ifdef __HASTE__
import "mtl" Control.Monad.State
import Data.Map.Strict (Map)
#else
import Control.Monad.State
import Data.ByteString.Short (ShortByteString, unpack)
import qualified Data.ByteString.Short as SBS
import Data.Map.Strict (Map, restrictKeys)
import Data.Semigroup
#endif
import Data.Bits
import Data.Char
import Data.Int
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

import Boost
import DHC
import Encode
import Std
import WasmOp

#ifdef __HASTE__
sbslen :: String -> Int
sbslen = length
unpack :: String -> [Int]
unpack = fmap ord
type ShortByteString = String
restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s = M.filterWithKey (\k _ -> S.member k s) m
#else
sbslen :: ShortByteString -> Int
sbslen = SBS.length
#endif

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal String
  | PushRef Int32
  | PushString ShortByteString
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePopEval Int | UpdateInd Int | Alloc Int
  | Casejump [(Maybe Int, [Ins])] | Trap
  | PushCallIndirect [Type]
  | WasmPush [Ins] Type
  | WasmCallIndirect [Type]
  deriving Show

nPages :: Int
nPages = 8

data WasmMeta = WasmMeta
  -- Arity of each user-defined function, whether exported or not.
  -- Eval uses this to remove the spine correctly.
  { arities :: Map String Int
  -- Public and private functions that can become references.
  -- We also hang on to the type of each argument as well as a function
  -- to decode it from a heap object.
  , exports :: [(String, [(Type, [Ins])])]
  , elements :: [(String, [(Type, [Ins])])]
  , callTypes :: [[Type]]  -- Types needed by call_indirect ops.
  , strEndHP :: Int  -- Heap address immediately past the string constants.
  , strAddrs :: Map ShortByteString Int  -- String constant addresses.
  , storeTypes :: [Type]  -- Global store types.
  , callEncoders :: Map String [Ins]  -- Helpers for call_indirect that encode messages.
  }

hsToGMachine :: Boost -> String -> Either String (Map String Int, Map String [Ins])
hsToGMachine boost hs = first arities <$> hsToIns boost hs

hsToWasm :: Boost -> String -> Either String [Int]
hsToWasm boost s = insToBin s b . astToIns <$> hsToAst b qq s where
  b = stdBoost <> boost
  qq "here" h = Right h
  qq "wasm" prog = case hsToWasm boost prog of
    Left err -> Left err
    Right ints -> Right $ chr <$> ints
  qq _ _ = Left "bad scheme"

hsToIns :: Boost -> String -> Either String (WasmMeta, Map String [Ins])
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
  , callIndirectTypes :: [[Type]]
  , stringConstants :: [ShortByteString]
  -- Compilation may generate auxiliary helpers.
  , helpers :: [(String, [Ins])]
  }

align4 :: Int -> Int
align4 n = (n + 3) `div` 4 * 4

mkStrConsts :: [ShortByteString] -> (Int, Map ShortByteString Int)
mkStrConsts = f (0, []) where
  f (p, ds) [] = (p, M.fromList ds)
  f (k, ds) (s:rest) = f (k + 16 + align4 (sbslen s), (s, k):ds) rest

astToIns :: Clay -> (WasmMeta, Map String [Ins])
astToIns cl = (WasmMeta
  { arities = funs
  , exports = compileDecoders <$> publics cl
  , elements = compileDecoders <$> secrets cl
  , callTypes = ciTypes
  , strEndHP = hp1
  , strAddrs = addrs
  , storeTypes = snd <$> stores cl
  , callEncoders = M.fromList $ concatMap helpers cs
  }, fst <$> compilerOut) where
  compilerOut = (compile $ fst <$> stores cl) <$> supers cl
  cs = snd <$> M.elems compilerOut
  ciTypes = foldl' union [] $ callIndirectTypes <$> cs
  (hp1, addrs) = mkStrConsts $ nub $ concatMap stringConstants cs
  funs = M.union ((\(Ast (Lam as _)) -> length as) <$> supers cl) $
    M.fromList $ concatMap (\n -> [("#set-" ++ show n, 1), ("#get-" ++ show n, 0)]) [0..length (stores cl) - 1]
  -- Argument decoders only use a certain subset of functions.
  compileDecoders = second $ fmap $ second (fst . compile [])

toDfnType :: Type -> WasmType
toDfnType t = case t of
  TApp (TC "()") _ -> Ref "Elem"
  TApp (TC "[]") _ -> Ref "Elem"
  TC "Int" -> I64
  TC "I32" -> I32
  TC "Bool" -> I32
  TC "String" -> Ref "Databuf"
  TC s | elem s ["Port", "Databuf", "Actor", "Module"] -> Ref s
  _ -> error $ "BUG! type check failed to catch: " ++ show t

followGCalls :: [String] -> Set String -> Map String [Ins] -> Set String
followGCalls fs prims m = execState (go fs) $ S.fromList fs where
  go (f:rest) = if S.member f prims
    then modify $ S.insert f
    else do
      maybe (pure ()) tr $ M.lookup f m
      go rest
  go [] = pure ()
  tr (w:rest) = do
    case w of
      PushGlobal v -> do
        s <- get
        when (S.notMember v s) $ do
          put $ S.insert v s
          go [v]
      PushCallIndirect ty -> go [show ty]
      WasmPush enc _ -> tr enc
      Casejump alts -> mapM_ tr $ snd <$> alts
      _ -> pure ()
    tr rest
  tr [] = pure ()

-- | Join two i32s into a single i64.
mk64 :: Int -> Int -> Int64
mk64 a b = fromIntegral a + shift (fromIntegral b) 32

insToBin :: String -> Boost -> (WasmMeta, Map String [Ins]) -> [Int]
insToBin src boost@(Boost imps _ _ boostFuns) (wm@WasmMeta {exports, elements, strAddrs, storeTypes}, gmachine) = wasm where
  wasm = encodeWasm $ foldl' (flip ($)) (protoWasm imps $ snd <$> wasmFuns)
    [ sectElements [(0, wasmFunNo . ('@':) . fst <$> ees)]
    , sectExports [(s, wasmFunNo ('@':s)) | (s, _) <- exports]
    , sectsMartin $ ((wasmFunNo . ('@':)) *** map (toDfnType . fst)) <$> ees
    , sectPersist $ zip [mainCalled..] $ toDfnType <$> TC "I32":storeTypes
    , sectTable 256
    , sect 5 [0 : leb128 nPages]  -- Memory section (0 = no-maximum).
    , sect 6 $  -- Global section (1 = mutable).
      [ [encType I32, 1, 0x41] ++ sleb128 memTop ++ [0xb]  -- SP
      , [encType I32, 1, 0x41] ++ sleb128 (strEndHP wm) ++ [0xb]  -- HP
      , [encType I32, 1, 0x41, 0, 0xb]  -- BP
      , [encType I32, 1, 0x41] ++ sleb128 (length ees) ++ [0xb]  -- TP
      ]
      -- Global stores.
      -- First one records if `main` has been run yet.
      ++ map declareGlobal (TC "I32":storeTypes)
    , sect 11 $ encStrConsts <$> M.assocs strAddrs  -- Data section.
    , sectCustom "dfndbg" [ord <$> show (sort $ swp <$> M.assocs wasmFunMap)]
    , sectCustom "dfnhs" [ord <$> src]
    ]
  ees = exports ++ elements
  declareGlobal (TC "Int") = [encType I64, 1, 0x42, 0, 0xb]
  declareGlobal _ = [encType I32, 1, 0x41, 0, 0xb]
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
  -- Returns arity and 0-indexed number of given global function.
  getGlobal s = case M.lookup s $ M.insert "main" 0 $ arities wm of
    Just arity -> (arity, wasmFunNo s - firstPrim)
    Nothing -> (arityFromType $ fromMaybe (error $ "BUG! bad global: " ++ s) $ M.lookup s primsType, wasmFunNo s - firstPrim)
  firstPrim = wasmFunNo $ fst $ head evalFuns
  cdq = concatMap deQuasi
  internalFuns =
    [ ("#eval", (([], []), evalAsm))
    , ("#mkap", (([], []), mkApAsm))
    , ("#push32", (([I32], []), push32Asm))  -- Low-level push.
    , ("#pushint", (([I64], []), cdq pushIntAsm))
    , ("#pushref", (([I32], []), cdq pushRefAsm))
    , ("#pushglobal", (([I64], []), cdq pushGlobalAsm))
    , ("#updatepopeval", (([I32], []), cdq updatePopEvalAsm))
    , ("#updateind", (([I32], []), updateIndAsm))
    , ("#alloc", (([I32], []), cdq allocAsm))
    , ("#pairwith42", (([I32], []), pairWith42Asm))
    , ("#nil42", (([], []), cdq nil42Asm))
    ] ++ (second (second cdq) <$> boostFuns)
  noInOut = ([], []) :: ([WasmType], [WasmType])
  wasmFuns :: [(String, WasmFun)]
  wasmFuns =
    (second (\((ins, outs), a) -> WasmFun (ins, outs) [] a) <$> internalFuns)
    ++ evalFuns
    -- Wrappers for functions in "public" and "secret" section.
    ++ (wrap <$> ees)
  evalFuns = concat  -- Functions that "#eval" can call.
    -- Primitive functions.
    -- The assembly for "#eval" requires that the primitive functions
    -- directly precede those defined in the program.
    [ M.assocs $ WasmFun noInOut [] . cdq . snd <$> livePrims
    -- Global get and set functions that interact with the DHC stack.
    , concat (zipWith mkStoreAsm storeTypes [0..])
    -- Functions from the program, except `main`.
    , M.assocs $ fromGMachine <$> M.delete "main" liveGs
    -- The `main` function. Any supplied `main` function is appended to
    -- some standard setup code.
    , [("main", WasmFun noInOut [] $ preMainAsm ++ concatMap fromIns (fromMaybe [] $ M.lookup "main" liveGs) ++ [End])]
    -- Wrappers for call_indirect ops.
    , M.assocs $ WasmFun noInOut [] . (++ [End]) . concatMap fromIns <$> callEncoders wm
    ]

  -- The "***" is a hack to force it to follow the instructions for all
  -- argument encoders and decoders.
  liveGIds = followGCalls ("***":"main":(fst <$> ees)) (M.keysSet prims) $ gmachine `M.union` M.singleton "***" (concatMap snd (concatMap snd ees) ++ concat (M.elems $ callEncoders wm))
  liveGs = restrictKeys gmachine liveGIds
  livePrims = restrictKeys prims liveGIds

  fromGMachine g = WasmFun noInOut [] $ (++ [End]) $ concatMap fromIns g
  preMainAsm =
    [ I32_const 1  -- mainCalled = 1
    , Set_global mainCalled
    ]
  wasmFunMap = M.fromList $ zip (((\(m, f) -> m ++ "." ++ f) . fst <$> imps) ++ (fst <$> wasmFuns)) [0..]
  wasmFunNo s = fromMaybe (error s) $ M.lookup s wasmFunMap

  wrap (f, ps) = let (inTypes, decoders) = unzip ps in
    (,) ('@':f) $ WasmFun (toWasmType <$> inTypes, []) [] $
    -- Wraps a DHC function.
    -- When a wasm function f(arg0, arg1, ...) is called,
    -- the arguments are placed in local variables.
    -- This wrapper builds:
    --
    --   f :@ arg0 :@ arg 1 :@ ... :@ #RealWorld
    --
    -- on the heap, places a pointer to his on the stack, then calls Eval.
    --
    -- Additionally, for each non-`main` function, first call `main`
    -- if a certain global flag is false.
    -- The `main` function always exists and sets this global flag.
    (if f /= "main" then
    [ Get_global mainCalled  -- if (!mainCalled) mainCalled = 1, main;
    , I32_eqz
    , If Nada (
      [ I32_const $ fromIntegral memTop  -- sp = top of memory
      , Set_global sp
      , I32_const 42  -- #push32 42
      , Call $ wasmFunNo "#push32"
      ] ++ concatMap fromIns [PushGlobal "main", MkAp, Eval]) []
    ]
    else []) ++

    [ I32_const $ fromIntegral memTop  -- sp = top of memory
    , Set_global sp
    , I32_const 42  -- #push32 42
    , Call $ wasmFunNo "#push32"
    ] ++
    -- Input arguments are local variables.
    -- We move these to our stack in reverse order.
    concat (reverse $ zipWith3 fromWire inTypes decoders [0..]) ++
    -- Build the spine.
    concatMap fromIns (PushGlobal f : replicate (length inTypes + 1) MkAp) ++
    [ Call $ wasmFunNo "#eval"
    , End
    ]
  fromWire t dec i =
    [ Get_local i
    , case toWasmType t of
      I64 -> Call $ wasmFunNo "#pushint"
      _   -> Call $ wasmFunNo "#pushref"
    ] ++ concatMap fromIns dec ++
    [ Call $ wasmFunNo "#mkap" ]
  evalAsm =
    [ Block Nada
      [ Loop Nada
        [ Get_global sp  -- bp = [sp + 4]
        , I32_load 2 4
        , Set_global bp
        , Block Nada
          [ Block Nada
            [ Get_global bp
            , I32_load8_u 0 0
            , Br_table [0, 1, 3] 4  -- case [bp].8u; branch on Tag
            ]  -- 0: Ap
          , Get_global bp  -- #push32 [bp + 8]
          , I32_load 2 8
          , Call $ wasmFunNo "#push32"
          , Br 1
          ]  -- 1: Ind.
        , Get_global sp  -- [sp + 4] = [bp + 4]
        , Get_global bp
        , I32_load 2 4
        , I32_store 2 4
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
        , I32_load 2 4
        , I32_load 2 12
        , I32_store 2 0
        , Br 1
        ] []  -- If
      ]  -- Loop
    , Set_global sp  -- restore bp, sp
    , Set_global bp
    ] ++ nest n ++ [End]
    where
      -- Eval functions are resolved in a giant `br_table`. This is ugly, but
      -- avoids run-time type-checking.
      n = length evalFuns
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_load 2 4
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ firstPrim + k - 1, Return]

  mkStoreAsm :: Type -> Int -> [(String, WasmFun)]
  mkStoreAsm t n =
    [ ("#set-" ++ show n, WasmFun noInOut [] $
      [ Get_global sp  -- Push 0, Eval.
      , I32_load 2 4
      , Call $ wasmFunNo "#push32"
      , Call $ wasmFunNo "#eval"
      ] ++ (case t of
        TC "Int" ->
          [ Get_global sp  -- Set_global n [[sp + 4] + 8].64
          , I32_load 2 4
          , I64_load 3 8
          , Set_global $ storeOffset + n
          ]
        _ ->
          [ Get_global sp  -- Set_global n [[sp + 4] + 4]
          , I32_load 2 4
          , I32_load 2 4
          , Set_global $ storeOffset + n
          ]
      ) ++
      [ Get_global sp  -- sp = sp + 12
      , I32_const 12
      , I32_add
      , Set_global sp
      , Call $ wasmFunNo "#nil42"
      , End
      ])
    , ("#get-" ++ show n, WasmFun noInOut [] $
      [ Get_global hp  -- PUSH hp
      ] ++ (case t of
        TC "Int" ->
          [ Get_global hp  -- [hp] = TagInt
          , tag_const TagInt
          , I32_store 2 0
          , Get_global hp  -- [hp + 8] = Get_global n
          , Get_global $ storeOffset + n
          , I64_store 3 8
          , Get_global hp  -- hp = hp + 16
          , I32_const 16
          , I32_add
          , Set_global hp
          ]
        _ ->
          [ Get_global hp  -- [hp] = TagRef
          , tag_const TagRef
          , I32_store 2 0
          , Get_global hp  -- [hp + 4] = Get_global n
          , Get_global $ storeOffset + n
          , I32_store 2 4
          , Get_global hp  -- hp = hp + 8
          , I32_const 8
          , I32_add
          , Set_global hp
          ]
      ) ++
      [ Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      , Call $ wasmFunNo "#pairwith42"
      , End
      ])
    ]
  deQuasi :: QuasiWasm -> [WasmOp]
  deQuasi (Custom x) = case x of
    CallSym s -> [Call $ wasmFunNo s]
    ReduceArgs n -> concat $ replicate n $ concatMap fromIns [Push (n - 1), Eval]

  deQuasi (Block t body) = [Block t $ cdq body]
  deQuasi (Loop  t body) = [Loop  t $ cdq body]
  deQuasi (If    t a b)  = [If    t (cdq a) $ cdq b]
  deQuasi op = [error "missing deQuasi case?" <$> op]

  prims = M.fromList $ boostPrims boost
  primsType = fst <$> prims

  fromIns :: Ins -> [WasmOp]
  fromIns instruction = case instruction of
    Trap -> [ Unreachable ]
    Eval -> [ Call $ wasmFunNo "#eval" ]  -- (Tail call.)
    PushInt n -> [ I64_const n, Call $ wasmFunNo "#pushint" ]
    PushRef n -> [ I32_const n, Call $ wasmFunNo "#pushref" ]
    Push n ->
      [ Get_global sp
      , I32_load 2 $ fromIntegral $ 4*(n + 1)
      , Call $ wasmFunNo "#push32"
      ]
    MkAp -> [ Call $ wasmFunNo "#mkap" ]
    PushGlobal fun | (n, g) <- getGlobal fun ->
      [ I64_const $ mk64 (fromEnum TagGlobal + shift n 8) g
      , Call $ wasmFunNo "#pushglobal"
      ]
    PushString s ->
      -- #push32 (address of string const)
      [ I32_const $ fromIntegral $ strAddrs M.! s
      , Call $ wasmFunNo "#push32"
      ]
    PushCallIndirect ty ->
      -- 3 arguments: slot, argument tuple, #RealWorld.
      [ I64_const $ mk64 (fromEnum TagGlobal + shift 3 8) $ wasmFunNo (show ty) - firstPrim
      , Call $ wasmFunNo "#pushglobal"
      ]
    Slide 0 -> []
    Slide n ->
      [ Get_global sp  -- [sp + 4*(n + 1)] = [sp + 4]
      , Get_global sp
      , I32_load 2 4
      , I32_store 2 $ 4*(fromIntegral n + 1)
      , Get_global sp  -- sp = sp + 4*n
      , I32_const $ 4*fromIntegral n
      , I32_add
      , Set_global sp
      ]
    Alloc n -> [ I32_const $ fromIntegral n, Call $ wasmFunNo "#alloc" ]
    UpdateInd n ->
      [ I32_const $ fromIntegral $ 4*(n + 1), Call $ wasmFunNo "#updateind" ]
    UpdatePopEval n ->
      [ I32_const $ fromIntegral $ 4*(n + 1)
      , Call $ wasmFunNo "#updatepopeval"
      ]
    Copro m n ->
      [ Get_global hp  -- [hp] = (TagSum | (n << 8) | (m << 32)).64
      , I64_const $ mk64 (fromEnum TagSum + shift n 8) m
      , I64_store 3 0
      ] ++ concat [
        [ Get_global hp  -- [hp + 4 + 4*i] = [sp + 4*i]
        , Get_global sp
        , I32_load 2 $ fromIntegral $ 4*i
        , I32_store 2 $ fromIntegral $ 4 + 4*i
        ] | i <- [1..n]] ++
      [ Get_global sp  -- sp = sp + 4*n
      , I32_const $ fromIntegral $ 4*n - 4
      , I32_add
      , Set_global sp
      , Get_global sp  -- [sp + 4] = hp
      , Get_global hp
      , I32_store 2 4
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
        [ Get_global bp  -- Br_table [bp + 4]
        , I32_load 2 4
        , Br_table [fromIntegral $ fromMaybe (length alts) $ lookup i tab | i <- [0..m]] $ m + 1
        ]
      in if null alts then concatMap fromIns catchall else
      -- [sp + 4] should be:
      -- 0: TagSum
      -- 4: "Enum"
      -- 8, 12, ...: fields
      [ Get_global sp  -- bp = [sp + 4]
      , I32_load 2 4
      , Set_global bp
      , Block Nada $ nest 1 (reverse $ snd <$> alts) ++ concatMap fromIns catchall
      ]

    Split 0 -> [Get_global sp, I32_const 4, I32_add, Set_global sp]
    Split n ->
      [ Get_global sp  -- bp = [sp + 4]
      , I32_load 2 4
      , Set_global bp
      , Get_global sp  -- sp = sp - 4*(n - 1)
      , I32_const $ fromIntegral $ 4*(n - 1)
      , I32_sub
      , Set_global sp
      ] ++ concat [
        [ Get_global sp  -- [sp + 4*i] = [bp + 4 + 4*i]
        , Get_global bp
        , I32_load 2 $ fromIntegral $ 4 + 4*i
        , I32_store 2 $ fromIntegral $ 4*i
        ] | i <- [1..n]]
    WasmPush encoder (TC "Int") ->
      concatMap fromIns (encoder ++ [MkAp, Eval]) ++
      [ Get_global sp  -- PUSH [[sp + 4] + 8].64
      , I32_load 2 4
      , I64_load 3 8
      , Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      ]
    WasmPush encoder _ ->
      concatMap fromIns (encoder ++ [MkAp, Eval]) ++
      [ Get_global sp  -- PUSH [[sp + 4] + 4]
      , I32_load 2 4
      , I32_load 2 4
      , Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      ]
    WasmCallIndirect inTypes ->
      -- 3 arguments: slot, argument tuple, #RealWorld.
      -- Assumes all message arguments have already been pushed.
      [ Get_global sp  -- PUSH [[sp + 4] + 4]
      , I32_load 2 4
      , I32_load 2 4
      , Call_indirect (toWasmType <$> inTypes, [])
      , Get_global sp  -- sp = sp + 16
      , I32_const 16
      , I32_add
      , Set_global sp
      , Call $ wasmFunNo "#nil42"
      ]

sp, hp, bp, tpGlobalIndex, mainCalled, storeOffset :: Int
[sp, hp, bp, tpGlobalIndex, mainCalled, storeOffset] = [0..5]

compile :: [String] -> Ast -> ([Ins], CompilerState)
compile ps d = runState (mk1 ps d) $ CompilerState [] [] [] []

mk1 :: [String] -> Ast -> State CompilerState [Ins]
mk1 pglobals (Ast ast) = case ast of
  -- Thanks to lambda lifting, `Lam` can only occur at the top level.
  Lam as b -> do
    putBindings $ zip as [0..]
    (++ [UpdatePopEval $ length as]) <$> rec b
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
  CallSlot ty encoders -> do
    st <- get
    put st { callIndirectTypes = callIndirectTypes st `union` [ty] }
    ms <- forM encoders rec
    addHelper ty ms
    pure [PushCallIndirect ty]
  Var v -> do
    m <- getBindings
    pure $ case lookup v m of
      Just k -> [Push k]
      _ | Just i <- elemIndex v pglobals ->
        -- Stores become (set n, get n) tuples.
        [ PushGlobal $ "#get-" ++ show i
        , PushGlobal $ "#set-" ++ show i
        , Copro 0 2
        ]
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
    getBindings = gets bindings
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
  , Get_global sp
  , I32_load 2 4
  , I32_store 2 8
  , Get_global hp  -- [hp + 12] = [sp + 8]
  , Get_global sp
  , I32_load 2 8
  , I32_store 2 12
  , Get_global sp  -- [sp + 8] = hp
  , Get_global hp
  , I32_store 2 8
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
push32Asm :: [WasmOp]
push32Asm =
  [ Get_global sp  -- [sp] = local_0
  , Get_local 0
  , I32_store 2 0
  , Get_global sp  -- sp = sp - 4
  , I32_const 4
  , I32_sub
  , Set_global sp
  , End
  ]
pushIntAsm :: [QuasiWasm]
pushIntAsm =
  [ Get_global hp  -- #push32 hp
  , Custom $ CallSym "#push32"
  , Get_global hp  -- [hp] = TagInt
  , tag_const TagInt
  , I32_store 2 0
  , Get_global hp  -- [hp + 8] = local_0
  , Get_local 0
  , I64_store 3 8
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , End
  ]
pushRefAsm :: [QuasiWasm]
pushRefAsm =
  [ Get_global hp  -- #push32 hp
  , Custom $ CallSym "#push32"
  , Get_global hp  -- [hp] = TagRef
  , tag_const TagRef
  , I32_store 2 0
  , Get_global hp  -- [hp + 4] = local_0
  , Get_local 0
  , I32_store 2 4
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , End
  ]
pushGlobalAsm :: [QuasiWasm]
pushGlobalAsm =
  [ Get_global hp  -- #push32 hp
  , Custom $ CallSym "#push32"
  , Get_global hp  -- [hp] = local_0.64  -- TagGlobal | (n << 8) | (funNo << 32)
  , Get_local 0
  , I64_store 3 0
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , End
  ]
updatePopEvalAsm :: [QuasiWasm]
updatePopEvalAsm =
  [ Get_global sp  -- bp = [sp + 4]
  , I32_load 2 4
  , Set_global bp
  , Get_global sp  -- sp = sp + local_0
  , Get_local 0  -- Should be 4*(n + 1).
  , I32_add
  , Set_global sp
  , Get_global sp  -- [[sp + 4]] = Ind
  , I32_load 2 4
  , tag_const TagInd
  , I32_store 2 0
  , Get_global sp  -- [[sp + 4] + 4] = bp
  , I32_load 2 4
  , Get_global bp
  , I32_store 2 4
  , Custom $ CallSym "#eval"
  , End
  ]
allocAsm :: [QuasiWasm]
allocAsm =
  [ Loop Nada
    [ Get_local 0  -- Break when local0 == 0
    , I32_eqz
    , Br_if 1
    , Get_local 0  -- local0 = local0 - 1
    , I32_const 1
    , I32_sub
    , Set_local 0
    , Get_global hp  -- #push32 hp
    , Custom $ CallSym "#push32"
    , Get_global hp  -- [hp] = TagInd
    , tag_const TagInd
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
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
  , Get_global sp
  , I32_load 2 0
  , I32_store 2 4
  , End
  ]

pairWith42Asm :: [WasmOp]
pairWith42Asm =  -- [sp + 4] = (local0, #RealWorld)
  [ Get_global hp  -- [hp] = (TagSum | (2 << 8)).64
  , I64_const $ fromIntegral $ fromEnum TagSum + 256 * 2
  , I64_store 3 0
  , Get_global hp  -- [hp + 8] = local0
  , Get_local 0
  , I32_store 2 8
  , Get_global hp  -- [hp + 12] = 42
  , I32_const 42
  , I32_store 2 12
  , Get_global sp  -- [sp + 4] = hp
  , Get_global hp
  , I32_store 2 4
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  , End
  ]
-- | [sp + 4] = ((), #RealWorld)
-- TODO: Optimize by placing this special value at a known location in memory.
nil42Asm :: [QuasiWasm]
nil42Asm =
  [ Get_global hp  -- [hp].64 = TagSum
  , I64_const $ fromIntegral $ fromEnum TagSum
  , I64_store 3 0
  , Get_global hp  -- PUSH hp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  , Custom $ CallSym "#pairwith42"
  , End
  ]

toWasmType :: Type -> WasmType
toWasmType (TC "Int") = I64
toWasmType _ = I32

addHelper :: [Type] -> [[Ins]] -> State CompilerState ()
addHelper ty ms = do
  st <- get
  put st { helpers = (show ty, f):helpers st }
  where
  f = case (ty, ms) of
    ([t], [encoder]) ->
      -- When sending a message with only one item, we have a bare argument
      -- instead of an argument tuple
      -- Evaluate single argument.
      [ Push 1
      , WasmPush encoder t
      , Push 0  -- Slot.
      , Eval
      , WasmCallIndirect ty
      ]
    _ ->
      -- Evaluate argument tuple.
      [ Push 1
      , Eval
      , Split $ length ms
      ] ++ zipWith WasmPush ms ty ++
      [ Push 0  -- Slot.
      , Eval
      , WasmCallIndirect ty
      ]
