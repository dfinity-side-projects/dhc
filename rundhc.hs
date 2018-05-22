import Data.Char
import qualified Data.ByteString as B
import Hero.Hero

main :: IO ()
main = putStr =<< runDemo =<< B.getContents

runDemo :: B.ByteString -> IO String
runDemo asm = stateVM . snd <$> runWasm "main" [] (mkHeroVM "" syscall wasm [])
  where
  wasm = either error id $ parseWasm asm
  syscall ("system", "putStr") vm [I32_const ptr, I32_const len] = pure ([],
    putStateVM (stateVM vm ++ [chr $ getNumVM 1 (ptr + i) vm | i <- [0..len - 1]]) vm)
  syscall ("system", "putInt") vm [I32_const lo, I32_const hi] = pure ([],
    putStateVM (stateVM vm ++ show (fromIntegral lo + fromIntegral hi * 2^(32 :: Integer) :: Integer)) vm)
  syscall a _ b = error $ show ("BUG! bad syscall", a, b)
