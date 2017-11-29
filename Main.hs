module Main where

import Control.Monad
import Data.Bits
import qualified Data.ByteString as B
import Data.Int
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Word

import Network.DFINITY.Parser

main :: IO ()
main = do
  s <- B.getContents
  case parseWasm s of
    Left err -> putStrLn $ "parse error: " ++ show err
    Right out -> execute [fun0] emptyMem putMem getMem out "e"
  where
    fun0 [I32_const x, I32_const y] = putStrLn $ show (y, x)
    emptyMem = IM.empty
    putMem = \a k v -> pure $ IM.insert k v a
    getMem = \a k -> pure $ a IM.! k

data VM a = VM
  { globs :: IntMap Op
  , stack :: [Op]
  , insts :: [[Op]]
  , mem   :: a
  } deriving Show

getNum :: (Integral n, Monad m) =>
  (a -> Int -> m Word8) -> Int -> Int32 -> a -> m n
getNum get w addr mem = do
  bs <- mapM (get mem) ((fromIntegral addr +) <$> [0..w-1])
  pure $ sum $ zipWith (*) (fromIntegral <$> bs) ((256^) <$> [0..])

putNum :: (Integral n, Monad m) =>
  (a -> Int -> Word8 -> m a) -> Int -> Int32 -> n -> a -> m a
putNum put w addr n mem = foldM f mem [0..w-1] where
  f m k = put m (fromIntegral addr + k) $ getByte k
  getByte k = fromIntegral $ n `div` (256^k) `mod` 256

execute :: Monad m =>
  [[Op] -> m ()] -> a -> (a -> Int -> Word8 -> m a) -> (a -> Int -> m Word8)
  -> Wasm -> [Char] -> m ()
execute fns initMem put get Wasm {imports, exports, code, globals} s = let
  fCount = length fns
  run VM {insts} | null insts = pure ()
  run vm@VM {insts} | null $ head insts = case tail insts of
    ((Loop _ _:rest):t) -> run vm {insts = rest:t}
    _                   -> run vm {insts = tail insts}
  run vm@VM{globs, stack, insts, mem} = case head $ head insts of
    Call i -> if i < fCount then do
        let k = length $ fst $ snd $ imports!!i
        fns!!i $ take k stack
        run vm { stack = drop k stack, insts = i1 }
      else do
        run vm { insts = snd (code!!(i - fCount)):i1 }
    Set_global i -> run vm {globs = IM.insert i (head stack) globs, stack = tail stack, insts = i1}
    Get_global i -> run vm {stack = globs IM.! i:stack, insts = i1}
    c@(I32_const _) -> run vm {stack = c:stack, insts = i1}
    c@(I64_const _) -> run vm {stack = c:stack, insts = i1}
    I32_add -> binOp32 (+)
    I32_sub -> binOp32 (-)
    I32_mul -> binOp32 (*)
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
    I64_shr_u -> binOp64 $ \a b -> fromIntegral $
      shiftR (fromIntegral a :: Word64) (fromIntegral b)
    I32_wrap_i64 -> let
      I64_const a = head stack
      c = I32_const $ fromIntegral a
      in run vm {stack = c:tail stack, insts = i1}
    I32_load _ _ -> do
      let I32_const addr = head stack
      c <- I32_const <$> getNum get 4 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_store _ _ -> let (I32_const n:I32_const addr:_) = stack in do
      mem' <- putNum put 4 addr n mem
      run vm {stack = drop 2 stack, insts = i1, mem = mem'}
    I64_store _ _ -> do
      let
        I32_const addr = stack!!1
        I64_const n = head stack
      mem' <- putNum put 8 addr n mem
      run vm {stack = drop 2 stack, insts = i1, mem = mem'}
    I64_load _ _ -> do
      let I32_const addr = head stack
      c <- I64_const <$> getNum get 8 addr mem
      run vm {stack = c:tail stack, insts = i1}
    Block _ bl -> run vm {insts = bl:i1}
    Loop _ bl -> run vm {insts = bl:insts}
    Br k -> run vm {insts = drop (k + 1) insts}
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
  in if fI < fCount then void $ fns!!fI $ [] else do
    run $ VM (IM.fromList $ zip [0..] $ head . snd <$> globals)
      [] [snd $ code!!(fI - fCount)] initMem
