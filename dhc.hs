-- Takes Haskell source given on standard input and compiles it to
-- WebAssembly which is dumped to standard output.

import qualified Data.ByteString as B
import WebDemo

main :: IO ()
main = do
  s <- getContents
  case hsToWasmWebDemo s of
    Left err -> error err
    Right asm -> B.putStr $ B.pack $ fromIntegral <$> asm
