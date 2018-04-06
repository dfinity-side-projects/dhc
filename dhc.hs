-- Takes Haskell source given on standard input and compiles it to
-- WebAssembly which is dumped to standard output.

import qualified Data.ByteString as B
import Asm
import Demo

main :: IO ()
main = do
  s <- getContents
  case hsToWasm demoBoost s of
    Left err -> error err
    Right bin -> B.putStr $ B.pack $ fromIntegral <$> wasmBinary bin
