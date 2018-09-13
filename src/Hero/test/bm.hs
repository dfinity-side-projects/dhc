-- Benchmark parsing.
import Criterion.Main
import qualified Data.ByteString as B
import Hero.Parse
import WasmOp

main :: IO ()
main = do
  s <- B.getContents
  defaultMain $ pure $ bench "parse" $ (`whnf` s) $ functions . either error id . parseWasm
