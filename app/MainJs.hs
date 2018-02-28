import GHCJS.Marshal (fromJSVal, toJSVal)
import GHCJS.Foreign.Callback (Callback, syncCallback1')
import GHCJS.Types (JSVal)

import Asm


hsToWasm' :: JSVal -> IO JSVal
hsToWasm' input = do
  Just str <- fromJSVal input
  case hsToWasmWebDemo str of
    Left err -> toJSVal err
    Right asm -> toJSVal asm

foreign import javascript unsafe "compile = $1"
  set_callback :: Callback a -> IO ()

main :: IO ()
main = do
  callback <- syncCallback1' hsToWasm'
  set_callback callback
