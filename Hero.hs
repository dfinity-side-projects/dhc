{-# LANGUAGE NamedFieldPuns #-}

module Hero (Wasm, HeroVM, parseWasm, runWasm, getNumVM, putNumVM, pushVM, WasmOp(I32_const)) where

import Data.Bits
import Data.Int
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List
import Data.Word

import Network.DFINITY.Parse

data HeroVM = HeroVM
  { globs :: IntMap WasmOp
  , locs  :: [IntMap WasmOp]
  , stack :: [WasmOp]
  , insts :: [[WasmOp]]
  , mem   :: IntMap Int
  } deriving Show

pushVM :: WasmOp -> HeroVM -> HeroVM
pushVM op vm = vm { stack = op:stack vm }

getNumVM :: Integral n => Int -> Int32 -> HeroVM -> n
getNumVM w addr vm = getNum w addr $ mem vm

putNumVM :: Integral n => Int -> Int32 -> n -> HeroVM -> HeroVM
putNumVM w addr n vm@(HeroVM {mem}) = vm { mem = putNum w addr n mem }

getNum :: Integral n => Int -> Int32 -> IntMap Int -> n
getNum w addr mem = sum $ zipWith (*) (fromIntegral <$> bs) ((256^) <$> [(0 :: Int)..]) where bs = fmap (mem IM.!) ((fromIntegral addr +) <$> [0..w-1])

putNum :: Integral n => Int -> Int32 -> n -> IntMap Int -> IntMap Int
putNum w addr n mem = foldl' f mem [0..w-1] where
  f m k = IM.insert (fromIntegral addr + k) (getByte k) m
  getByte k = fromIntegral $ n `div` (256^k) `mod` 256

shiftR32U :: Int32 -> Int32 -> Int32
shiftR32U a b = fromIntegral $ shiftR ((fromIntegral a) :: Word32) $ fromIntegral ((fromIntegral b :: Word32) `mod` 32)

shiftR64U :: Int64 -> Int64 -> Int64
shiftR64U a b = fromIntegral $ shiftR ((fromIntegral a) :: Word64) $ fromIntegral ((fromIntegral b :: Word64) `mod` 64)

-- The `End` opcode is reintroduced at the ends of function calls, so that we
-- know when to pop locals.
runWasm :: Monad m => [HeroVM -> [WasmOp] -> m HeroVM] -> Wasm -> [Char] -> m ()
runWasm fns Wasm {imports, exports, code, globals} s = let
  fCount = length fns
  run HeroVM {insts} | null insts = pure ()
  run vm@HeroVM {insts} | null $ head insts = case tail insts of
    ((Loop _ _:rest):t) -> run vm {insts = rest:t}
    _                   -> run vm {insts = tail insts}
  run vm@HeroVM{globs, locs, stack, insts, mem} = case head $ head insts of
    Call i -> if i < fCount then do
        let k = length $ fst $ snd $ imports!!i
        vm' <- (fns!!i) vm { stack = drop k stack, insts = i1 } $ take k stack
        run vm'
      else do
        let (locals, body) = code!!(i - fCount)
        run vm { locs = IM.fromList (zip [0..] locals):locs, insts = body:(End: head i1):tail i1 }
    End -> run vm { locs = tail locs, insts = i1 }
    Set_local i -> run vm {locs = IM.insert i (head stack) (head locs):tail locs, stack = tail stack, insts = i1}
    Get_local i -> run vm {stack = head locs IM.! i:stack, insts = i1}
    Tee_local i -> run vm {locs = IM.insert i (head stack) (head locs):tail locs, insts = i1}
    Set_global i -> run vm {globs = IM.insert i (head stack) globs, stack = tail stack, insts = i1}
    Get_global i -> run vm {stack = globs IM.! i:stack, insts = i1}
    c@(I32_const _) -> run vm {stack = c:stack, insts = i1}
    c@(I64_const _) -> run vm {stack = c:stack, insts = i1}
    I32_and -> binOp32 (.&.)
    I32_add -> binOp32 (+)
    I32_sub -> binOp32 (-)
    I32_mul -> binOp32 (*)
    I32_shr_u -> binOp32 shiftR32U
    I32_ne -> binOp32 $ ((fromIntegral . fromEnum) .) . (/=)
    I32_eqz -> let
      (I32_const a:t) = stack
      in run vm {stack = (I32_const $ fromIntegral $ fromEnum $ a == 0):t, insts = i1}
    I64_gt_s -> let
      (I64_const b:I64_const a:_) = stack
      c = I32_const $ fromIntegral $ fromEnum $ a > b
      in run vm {stack = c:drop 2 stack, insts = i1}
    I64_eq -> let
      (I64_const b:I64_const a:_) = stack
      c = I32_const $ fromIntegral $ fromEnum $ a == b
      in run vm {stack = c:drop 2 stack, insts = i1}
    I64_add -> binOp64 (+)
    I64_sub -> binOp64 (-)
    I64_mul -> binOp64 (*)
    I64_shr_u -> binOp64 shiftR64U
    I32_wrap_i64 -> let
      I64_const a = head stack
      c = I32_const $ fromIntegral a
      in run vm {stack = c:tail stack, insts = i1}
    I32_load8_u _ _ -> do
      let I32_const addr = head stack
          c = I32_const $ getNum 1 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_load16_u _ _ -> do
      let I32_const addr = head stack
          c = I32_const $ getNum 2 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_load _ _ -> do
      let I32_const addr = head stack
          c = I32_const $ getNum 4 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_store _ _ -> let (I32_const n:I32_const addr:_) = stack in do
      let mem' = putNum 4 addr n mem
      run vm {stack = drop 2 stack, insts = i1, mem = mem'}
    I32_store8 _ _ -> let (I32_const n:I32_const addr:_) = stack in do
      let mem' = putNum 1 addr n mem
      run vm {stack = drop 2 stack, insts = i1, mem = mem'}
    I64_store _ _ -> do
      let
        I32_const addr = stack!!1
        I64_const n = head stack
      let mem' = putNum 8 addr n mem
      run vm {stack = drop 2 stack, insts = i1, mem = mem'}
    I64_load _ _ -> do
      let I32_const addr = head stack
          c = I64_const $ getNum 8 addr mem
      run vm {stack = c:tail stack, insts = i1}
    If _ bl -> let I32_const n = head stack in if n == 1
      then run vm {stack = tail stack, insts = bl:i1}
      else run vm {stack = tail stack, insts = i1}
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
    _ -> error $ "TODO: " ++ show (head $ head insts)
    where
      i1 = tail (head insts):tail insts
      binOp32 f = run vm {stack = c:drop 2 stack, insts = i1} where
        (I32_const b:I32_const a:_) = stack
        c = I32_const $ f a b
      binOp64 f = run vm {stack = c:drop 2 stack, insts = i1} where
        (I64_const b:I64_const a:_) = stack
        c = I64_const $ f a b
  Just fI = lookup s exports
  in run $ HeroVM (IM.fromList $ zip [0..] $ head . snd <$> globals)
      [] [] [[Call fI]] IM.empty
