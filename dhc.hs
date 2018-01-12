-- Takes Haskell source given on standard input and compiles it to
-- WebAssembly which is dumped to standard output.

import qualified Data.ByteString as B
import Asm

main :: IO ()
main = do
  s <- getContents
  case wasm s of
    Left err -> error err
    Right asm -> B.putStr $ B.pack $ fromIntegral <$> asm
