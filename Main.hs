module Main where

import Control.Monad
import qualified Data.ByteString as B
import Data.Char
import Data.Int

import Hero

main :: IO ()
main = do
  s <- B.getContents
  case parseWasm s of
    Left err -> putStrLn $ "parse error: " ++ show err
    Right out -> (print out >>) $ void $ runWasm syscall out "#main"

syscall :: (String, String) -> HeroVM -> [WasmOp] -> IO HeroVM
syscall ("dhc", "system") vm [I32_const n, I32_const sp, I32_const hp]
  | n == 21 = do
    when (getTag /= 6) $ error "BUG! want String"
    let slen = getNumVM 4 (addr + 4) vm
    putStr $ [chr $ getNumVM 1 (addr + 8 + i) vm | i <- [0..slen - 1]]
    pure
      $ putNumVM 4 hp (5 :: Int)
      $ putNumVM 4 (hp + 4) (0 :: Int)
      $ putNumVM 4 sp hp
      $ putNumVM 4 (sp - 4) (hp + 8)
      vm
  | n == 22 = do
    when (getTag /= 3) $ error "BUG! want Int"
    putStr $ show (getNumVM 8 (addr + 8) vm :: Int)
    pure
      $ putNumVM 4 hp (5 :: Int)
      $ putNumVM 4 (hp + 4) (0 :: Int)
      $ putNumVM 4 sp hp
      $ putNumVM 4 (sp - 4) (hp + 8)
      vm
  | otherwise = error $ "BUG! bad syscall " ++ show n
  where
    addr = getNumVM 4 (sp + 4) vm :: Int32
    getTag = getNumVM 1 addr vm :: Int
syscall _ _ _ = error "BUG! bad syscall "
