import qualified Data.ByteString as B
import Test.HUnit
import Hero.Hero

main :: IO Counts
main = runTestTT test42

test42 :: Test
test42 = TestCase $ assertEqual "i32.const 42" "42" =<< runTiny fortyTwo

runTiny :: B.ByteString -> IO String
runTiny asm = getState . snd <$> runWasm [] (getExport "e" vm0) [] "" vm0
  where
  vm0 = mkHeroVM syscall wasm
  wasm = either error id $ parseWasm asm
  syscall ("i", "f") vm [I32_const a] = pure ([],
    putState (getState vm ++ show a) vm)
  syscall a _ b = error $ show ("BUG! bad syscall", a, b)

fortyTwo :: B.ByteString
-- Minimal wasm that exports a function returning the 32-bit integer 42.
-- See https://crypto.stanford.edu/~blynn/lambda/wasm.html
fortyTwo = B.pack
  [0,97,115,109,1,0,0,0,1,8,2,96,1,127,0,96,0,0,2,7,1,1,105,1
  ,102,0,0,3,2,1,1,7,5,1,1,101,0,1,10
  ,8  -- Length of code section.
  ,1
  ,6  -- Length of function.
  ,0
  -- If the following is changed, then the above lengths should match.
  ,65,42  -- 0x41, 42 means i32.const 42.
  ,16,0,11]
