{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
import Control.Monad
import Data.Bits
import qualified Data.ByteString as B
import Data.Int
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List
import Data.Word

import Parse

main :: IO ()
main = do
  s <- B.getContents
  case parseWasm s of
    Left err -> putStrLn $ "parse error: " ++ show err
    Right out -> execute [fun0] out "e"
  where
    fun0 [I32_const x, I32_const y] = putStrLn $ show (y, x)

data VM = VM
  { globs :: IntMap Op
  , stack :: [Op]
  , insts :: [[Op]]
  , mem :: IntMap Word8
  } deriving Show

putNum :: Integral a => Int -> Int32 -> a -> IntMap Word8 -> IntMap Word8
putNum w addr n mem = foldl' f mem [0..w-1] where
  f m k = IM.insert (fromIntegral addr + k) (getByte k) m
  getByte k = fromIntegral $ n `div` (256^k) `mod` 256

getNum :: Int -> Int32 -> IntMap Word8 -> Integer
getNum w addr m = sum
  [fromIntegral (m IM.! (fromIntegral addr + k)) * 256^k | k <- [0..w-1]]

execute :: Monad m => [[Op] -> m ()] -> Wasm -> [Char] -> m ()
execute fns Wasm {imports, exports, code, globals} s = let
  fCount = length fns
  run VM {insts} | null insts = pure ()
  run vm@VM {insts} | null $ head insts = case tail insts of
    ((Loop _ _:rest):t) -> run vm {insts = rest:t}
    _                   -> run vm {insts = tail insts}
  run vm@VM{globs, stack, insts, mem} = case head $ head insts of
    Call i -> if i < fCount then do
        let
          Import _ _ (params, _) = imports!!i
          k = length params
        fns!!i $ take k stack
        run vm { stack = drop k stack, insts = i1 }
      else do
        let Body _ os = code!!(i - fCount)
        run vm { insts = os:i1 }
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
      let
        I32_const addr = head stack
        c = I32_const $ fromIntegral $ getNum 4 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_store _ _ -> let (I32_const n:I32_const addr:_) = stack in
      run vm {stack = drop 2 stack, insts = i1, mem = putNum 4 addr n mem}
    I64_store _ _ -> do
      let
        I32_const addr = stack!!1
        I64_const n = head stack
      run vm {stack = drop 2 stack, insts = i1, mem = putNum 8 addr n mem}
    I64_load _ _ -> do
      let
        I32_const addr = head stack
        c = I64_const $ fromIntegral $ getNum 8 addr mem
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
    let Body _ os = code!!(fI - fCount)
    run $ VM (IM.fromList $ zip [0..] $ head . snd <$> globals) [] [os] IM.empty
