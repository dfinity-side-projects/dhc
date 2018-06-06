{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}

module Hero.Hero
  ( Wasm(dfnExports, haskell)
  , CustomWasmOp(I32_const, I64_const), WasmOp
  , HeroVM
  , parseWasm
  , runWasm
  , runWasmIndex
  , runWasmSlot
  , mkHeroVM
  , setArgsVM
  , setTable
  , globalVM
  , getNumVM, putNumVM
  , stateVM, putStateVM
  , ripWasm
  ) where

#ifdef __HASTE__
import qualified Data.Map.Strict as IM
#else
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
#endif
import Data.Bits
import Data.Char (ord)
import Data.Int
import Data.List
import Data.Maybe
import Data.Word

import Hero.Parse
import WasmOp

#ifdef __HASTE__
type IntMap = IM.Map Int
#endif

type VMFun a = HeroVM a -> [WasmOp] -> IO ([WasmOp], HeroVM a)

data HeroVM a = HeroVM
  { globs :: IntMap WasmOp
  , locs  :: [IntMap WasmOp]
  , stack :: [WasmOp]
  , insts :: [[WasmOp]]
  , mem   :: IntMap Int
  , sigs  :: IntMap ([WasmType], [WasmType])
  , table :: IntMap (VMFun a)
  , wasm  :: Wasm
  , state :: a
  -- Returns functions corresponding to module imports.
  , sys :: ((String, String) -> VMFun a)
  }

stateVM :: HeroVM a -> a
stateVM vm = state vm

putStateVM :: a -> HeroVM a -> HeroVM a
putStateVM a vm = vm {state = a}

-- | Reads an integer of a given width from linear memory.
getNumVM :: Integral n => Int -> Int32 -> HeroVM a -> n
getNumVM w addr vm = getNum w addr $ mem vm

-- | Writes an integer of a given width to linear memory.
putNumVM :: Integral n => Int -> Int32 -> n -> HeroVM a -> HeroVM a
putNumVM w addr n vm@(HeroVM {mem}) = vm { mem = putNum w addr n mem }

-- | Reads global variables.
globalVM :: HeroVM a -> [(Int, WasmOp)]
globalVM vm = IM.assocs $ globs vm

getNum :: Integral n => Int -> Int32 -> IntMap Int -> n
--getNum w addr mem = sum $ zipWith (*) (fromIntegral <$> bs) ((256^) <$> [(0 :: Int)..]) where bs = fmap (mem IM.!) ((fromIntegral addr +) <$> [0..w-1])
getNum w addr mem = sum $ zipWith (*) (fromIntegral <$> bs) ((256^) <$> [(0 :: Int)..]) where bs = fmap (\a -> fromMaybe 0 $ IM.lookup a mem) ((fromIntegral addr +) <$> [0..w-1])

putNum :: Integral n => Int -> Int32 -> n -> IntMap Int -> IntMap Int
putNum w addr n mem = foldl' f mem [0..w-1] where
  f m k = IM.insert (fromIntegral addr + k) (getByte k) m
  getByte k = fromIntegral n `div` (256^k) `mod` 256

-- TODO: Check this works as expected on negative inputs.
rem32 :: Int32 -> Int32 -> Int32
rem32 a b = fromIntegral $ rem ((fromIntegral a) :: Word32) $ fromIntegral (fromIntegral b :: Word32)

rem32U :: Int32 -> Int32 -> Int32
rem32U a b = fromIntegral $ mod ((fromIntegral a) :: Word32) $ fromIntegral (fromIntegral b :: Word32)

rotateL32 :: Word32 -> Word32 -> Int32
rotateL32 a b = fromIntegral $ rotateL a $ fromIntegral (b `mod` 32)

rotateR32 :: Word32 -> Word32 -> Int32
rotateR32 a b = fromIntegral $ rotateR a $ fromIntegral (b `mod` 32)

shiftL32 :: Word32 -> Word32 -> Int32
shiftL32 a b = fromIntegral $ shiftL a $ fromIntegral (b `mod` 32)

shiftR32U :: Word32 -> Word32 -> Int32
shiftR32U a b = fromIntegral $ shiftR a $ fromIntegral (b `mod` 32)

shiftR32S :: Int32 -> Int32 -> Int32
shiftR32S a b = fromIntegral $ shiftR a $ fromIntegral (b `mod` 32)

shiftR64U :: Int64 -> Int64 -> Int64
shiftR64U a b = fromIntegral $ shiftR ((fromIntegral a) :: Word64) $ fromIntegral ((fromIntegral b :: Word64) `mod` 64)

shiftR64S :: Int64 -> Int64 -> Int64
shiftR64S a b = fromIntegral $ shiftR ((fromIntegral a) :: Int64) $ fromIntegral ((fromIntegral b :: Int64) `mod` 64)

shiftL64 :: Int64 -> Int64 -> Int64
shiftL64 a b = shiftL a $ fromIntegral ((fromIntegral b :: Word64) `mod` 64)

rotateR64 :: Int64 -> Int64 -> Int64
rotateR64 a b = rotateR a $ fromIntegral ((fromIntegral b :: Word64) `mod` 64)

drop' :: Int -> [a] -> [a]
drop' n as | n > length as = error "BAD DROP"
           | otherwise = drop n as

take' :: Int -> [a] -> [a]
take' n as | n > length as = error "BAD TAKE"
           | otherwise = take n as

initLocal :: WasmType -> WasmOp
initLocal I32 = I32_const 0
initLocal I64 = I64_const 0
initLocal _ = error "TODO"

run :: HeroVM a -> IO ([WasmOp], HeroVM a)
run vm@HeroVM {insts, stack} | null insts = pure (stack, vm)
run vm@HeroVM {insts} | null $ head insts = case tail insts of
  ((Loop _ _:rest):t) -> run vm {insts = rest:t}
  _                   -> run vm {insts = tail insts}
run vm@HeroVM{globs, locs, stack, insts, mem} = case head $ head insts of
  Call_indirect (inSig, _) -> do
    let
      -- TODO: Dynamic type-check.
      inCount = length inSig
      (I32_const i:params) = take' (inCount + 1) stack
    (results, vm1) <- (table vm IM.! fromIntegral i) (step $ drop' (inCount + 1) stack) (reverse params)
    run $ setArgsVM results vm1
  Call i -> let
    Wasm {imports, functions} = wasm vm
    fCount = length imports
    in if i < fCount then do
      let
        (importName, (ins, _)) = imports!!i
        k = length ins
      (results, vm1) <- sys vm importName (step $ drop' k stack) (reverse $ take' k stack)
      run $ setArgsVM results vm1
    else do
      let
        WasmFun {typeSig, localVars, funBody} = functions IM.! i
        locals = initLocal <$> localVars
        k = length $ fst typeSig
      -- The `End` opcode is reintroduced at the ends of function calls, so
      -- we know when to pop locals, and when to stop popping instructions
      -- for `Return`.
      run vm { stack = drop' k stack, locs = IM.fromList (zip [0..] $ reverse (take' k stack) ++ locals):locs, insts = funBody:(End:head i1):tail i1 }
  Return -> run vm { insts = dropWhile ((End /=) . head) insts }
  End -> run vm { locs = tail locs, insts = i1 }
  Set_local i -> run vm {locs = IM.insert i (head stack) (head locs):tail locs, stack = tail stack, insts = i1}
  Get_local i -> if i >= IM.size (head locs) then error $ "BUG! bad local: " ++ show(i, locs) else run $ step $ head locs IM.! i:stack
  Tee_local i -> run vm {locs = IM.insert i (head stack) (head locs):tail locs, insts = i1}
  Set_global i -> run vm {globs = IM.insert i (head stack) globs, stack = tail stack, insts = i1}
  Get_global i -> if i >= IM.size globs then error $ "BUG! bad global: " ++ show (i, globs)
    else run $ step $ globs IM.! i:stack
  c@(I32_const _) -> run $ step $ c:stack
  c@(I64_const _) -> run $ step $ c:stack
  I32_xor -> binOp32 xor
  I32_and -> binOp32 (.&.)
  I32_or -> binOp32 (.|.)
  I32_add -> binOp32 (+)
  I32_sub -> binOp32 (-)
  I32_mul -> binOp32 (*)
  I32_div_s -> binOp32 div  -- TODO: Is this right for negative inputs?
  I32_rem_u -> binOp32 rem32U
  I32_rem_s -> binOp32 rem32
  I32_shl -> binOp32U shiftL32
  I32_rotl -> binOp32U rotateL32
  I32_rotr -> binOp32U rotateR32
  I32_shr_u -> binOp32U shiftR32U
  I32_shr_s -> binOp32 shiftR32S
  I32_ge_s -> binOp32 $ ((fromIntegral . fromEnum) .) . (>=)
  I32_gt_s -> binOp32 $ ((fromIntegral . fromEnum) .) . (>)
  I32_le_s -> binOp32 $ ((fromIntegral . fromEnum) .) . (<=)
  I32_lt_s -> binOp32 $ ((fromIntegral . fromEnum) .) . (<)
  I32_gt_u -> binOp32U $ ((fromIntegral . fromEnum) .) . (>)
  I32_ge_u -> binOp32U $ ((fromIntegral . fromEnum) .) . (>=)
  I32_lt_u -> binOp32U $ ((fromIntegral . fromEnum) .) . (<)
  I32_le_u -> binOp32U $ ((fromIntegral . fromEnum) .) . (<=)
  I32_ne -> binOp32 $ ((fromIntegral . fromEnum) .) . (/=)
  I32_eq -> binOp32 $ ((fromIntegral . fromEnum) .) . (==)
  I32_eqz -> let
    (I32_const a:t) = stack
    in run $ step $ (I32_const $ fromIntegral $ fromEnum $ a == 0):t
  I64_le_s -> boolBinOp64 (<=)
  I64_lt_s -> boolBinOp64 (<)
  I64_ge_s -> boolBinOp64 (>=)
  I64_gt_s -> boolBinOp64 (>)
  I64_eq -> boolBinOp64 (==)
  I64_add -> binOp64 (+)
  I64_sub -> binOp64 (-)
  I64_mul -> binOp64 (*)
  I64_xor -> binOp64 xor
  I64_and -> binOp64 (.&.)
  I64_or -> binOp64 (.|.)
  I64_shr_u -> binOp64 shiftR64U
  I64_shr_s -> binOp64 shiftR64S
  I64_shl -> binOp64 shiftL64
  I64_rotr -> binOp64 rotateR64
  I64_extend_s_i32 -> let
    I32_const a = head stack
    c = I64_const $ fromIntegral a
    in run $ step (c:tail stack)
  I64_extend_u_i32 -> let
    I32_const a = head stack
    c = I64_const $ fromIntegral (fromIntegral a :: Word32)
    in run $ step (c:tail stack)
  I32_wrap_i64 -> let
    I64_const a = head stack
    c = I32_const $ fromIntegral a
    in run $ step (c:tail stack)
  I32_load8_u  _ o -> load32 1 o
  I32_load16_u _ o -> load32 2 o
  I32_load     _ o -> load32 4 o
  I32_store8   _ o -> store32 1 o
  I32_store16  _ o -> store32 2 o
  I32_store    _ o -> store32 4 o
  I64_store _ o -> do
    let
      I32_const addr = stack!!1
      I64_const n = head stack
    let mem' = putNum 8 (addr + fromIntegral o) n mem
    run (step $ drop 2 stack) { mem = mem'}
  I64_load _ o -> do
    let I32_const addr = head stack
        c = I64_const $ getNum 8 (addr + fromIntegral o) mem
    run $ step (c:tail stack)

  If _ t f -> let I32_const n = head stack in if n /= 0
    then run vm {stack = tail stack, insts = t:i1}
    else run vm {stack = tail stack, insts = f:i1}
  Block _ bl -> run vm {insts = bl:i1}
  Loop _ bl -> run vm {insts = bl:insts}
  Br k -> run vm {insts = drop (k + 1) insts}
  Br_if k -> let (I32_const n:t) = stack in if n /= 0
    then run vm {stack = t, insts = drop (k + 1) insts}
    else run vm {stack = t, insts = i1}
  Br_table as d -> do
    let
      n = fromIntegral n' where I32_const n' = head stack
      k = if n < 0 || n >= length as then d else as!!n
    run vm {stack = tail stack, insts = drop (k + 1) insts}
  Unreachable -> putStrLn "IT'S A TRAP!" >> pure ([], vm)
  Drop -> run $ step $ tail stack
  Select -> do
    let
      [I32_const c, f, t] = take' 3 stack
      r = if c /= 0 then t else f
    run $ step $ r:drop 3 stack
  _ -> error $ "TODO: " ++ show (head $ head insts)
  where
    step newStack = vmNext { stack = newStack }
    vmNext = vm { insts = i1 }
    i1 = tail (head insts):tail insts
    binOp32 f = run $ step (c:drop 2 stack) where
      (I32_const b:I32_const a:_) = stack
      c = I32_const $ f a b
    binOp32U f = run $ step (c:drop 2 stack) where
      (I32_const b:I32_const a:_) = stack
      c = I32_const $ f (toU32 a) (toU32 b) where
        toU32 n = (fromIntegral n :: Word32)
    binOp64 f = run $ step (c:drop 2 stack) where
      (I64_const b:I64_const a:_) = stack
      c = I64_const $ f a b
    boolBinOp64 f = run $ step (c:drop 2 stack) where
      (I64_const b:I64_const a:_) = stack
      c = I32_const $ fromIntegral $ fromEnum $ f a b
    load32 sz off = run $ step (I32_const (getNum sz (addr + fromIntegral off) mem):tail stack)
      where I32_const addr = head stack
    store32 sz off = do
      let (I32_const n:I32_const addr:_) = stack
          mem' = putNum sz (addr + fromIntegral off) n mem
      run (step $ drop 2 stack) { mem = mem'}

-- | Runs a function at a given index.
runWasmIndex :: Int -> [WasmOp] -> HeroVM a -> IO ([WasmOp], HeroVM a)
runWasmIndex n args vm = run (setArgsVM args vm) { insts = [[Call n]] }

-- | Runs an export with arguments in a HeroVM.
runWasm :: [Char] -> [WasmOp] -> HeroVM a -> IO ([WasmOp], HeroVM a)
runWasm f args vm = runWasmIndex n args vm where
  n = fromMaybe (error $ "bad export: " ++ f) $ lookup f $ exports $ wasm vm

-- | Runs a given slot.
runWasmSlot :: Int -> ([WasmType], [WasmType]) -> [WasmOp] -> HeroVM a -> IO ([WasmOp], HeroVM a)
runWasmSlot k t args vm = run (setArgsVM (args ++ [I32_const (fromIntegral k)]) vm) { insts = [[Call_indirect t]] }

-- | Builds a HeroVM for given Wasm binary, imports and persistent globals.
mkHeroVM :: a -> ((String, String) -> VMFun a) -> Wasm -> [(Int, WasmOp)] -> HeroVM a
mkHeroVM st imps w gs = HeroVM
  { sys = imps
  , globs = initGlobals
  , locs = []
  , stack = []
  , insts = []
  , mem = IM.fromList $ concatMap strToAssocs $ dataSection w
  , sigs = IM.fromList $ zip [0..] $ types w
  , table = IM.fromList $ concatMap mkElems $ elemSection w
  , wasm = w
  , state = st
  } where
  initGlobals = IM.fromList $ (zip [0..] $ head . snd <$> globals w) ++ gs
  strToAssocs ([I32_const n], s) = zip [fromIntegral n..] $ ord <$> s
  strToAssocs _ = error "BUG!"
  mkElems (offset, ns) = zip [offset..] $ wrapCall <$> ns
  wrapCall n = \vm args -> runWasmIndex n args vm

-- | Place arguments on WebAssembly stack.
setArgsVM :: [WasmOp] -> HeroVM a -> HeroVM a
setArgsVM ls vm = vm { stack = reverse ls ++ stack vm }

setTable :: Int32 -> VMFun a -> HeroVM a -> HeroVM a
setTable slot fun vm = vm { table = IM.insert (fromIntegral slot) fun $ table vm }
