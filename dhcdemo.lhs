= DHC Demo =

The following compiles Haskell to WebAssembly and runs it.

Only a tiny fragment of the language is supported. There is almost no syntax
sugar.

System calls:

------------------------------------------------------------------------------
putStr :: String -> IO ()
putInt :: Int -> IO ()
------------------------------------------------------------------------------

There is no garbage collection.

https://github.com/dfinity/dhc[Source].

[pass]
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
<script type="text/javascript">
var dv;
function load8(addr) { return dv.getUint8(addr); }
function load32(addr) { return dv.getUint32(addr, true); }
function store32(addr, x) { dv.setUint32(addr, x, true); }
function runWasmInts(a){WebAssembly.instantiate(new Uint8Array(a),
{i:{f:(n,sp,hp) => { return Haste.syscall(n,sp,hp); } }}).then(x => {
expo = x.instance.exports;
dv = new DataView(expo.mem.buffer);
document.getElementById('out').innerHTML ="";
expo.main()});
}
</script>
<script src="dhcdemo.js">
</script>
<p><textarea id="src" rows="25" cols="80">
-- Gratuitous mutual recursion.
factorial n = case n == 0 of True  -> 1
                             False -> n * factorial2 (n - 1)
factorial2 n = case n == 0 of True  -> 1
                              False -> n * factorial (n - 1)
foldr f n xs = case xs of [] -> n
                          (a:as) -> f a (foldr f n as)
uncurry f p = case p of (a, b) -> f a b
sum = foldr (+) 0
enumFromTo a b = case a > b of True  -> []
                               False -> a : enumFromTo (a + 1) b
map f = foldr (\x xs -> f x:xs) []
tenTimes x = 10 * x
f $ x = f x
f rec n = case n == 0 of True -> 0
                         False -> rec (n - 1) + 2*n - 1
main = do
  putStr "recursion with fix: "
  let {fixedf = f fixedf} in putInt $ fixedf 100
  putStr "\n5! + (10 + 20 + 30 + 40 + 50) = "
  putInt $ uncurry (+) (factorial 5, sum $ map tenTimes [1..5])
</textarea></p>
<button id="go">Compile & Run!</button>
<p><textarea id="asm" readonly rows="5" cols="80">
</textarea></p>
<pre id="out"></pre>
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//////////////////////////////////////////////////////////////////////////////
\begin{code}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad
import Data.Char
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Asm

append :: Elem -> String -> IO ()
append e s = do
  v <- getProp e "innerHTML"
  setProp e "innerHTML" $ v ++ s

syscall :: Elem -> Int -> Int -> Int -> IO ()
syscall e n sp hp
  | n == 21 = do
    addr <- load32 $ sp + 4
    tag <- load8 addr
    when (tag /= 5) $ error $ "BUG! want string (tag 5), got " ++ show tag
    slen <- load32 $ addr + 4
    s <- mapM load8 [addr + 8 + i | i <- [0..slen - 1]]
    append e $ chr <$> s
    store32 hp 4
    store32 (hp + 4) 0
    store32 sp hp
    store32 (sp - 4) $ hp + 8
  | n == 22 = do
    addr <- load32 $ sp + 4
    tag <- load8 addr
    when (tag /= 3) $ error $ "BUG! want int (tag 3), got " ++ show tag
    x <- load32 $ addr + 12
    y <- load32 $ addr + 8
    let b = 2^(32 :: Int) :: Integer
    append e $ case x of
      0 -> show y ++ if y >= 0 then "" else
        " (unsigned = " ++ show (fromIntegral y + b) ++ ")"
      _ -> show $ fromIntegral x * b + ((fromIntegral y + b) `mod` b)
    store32 hp 4
    store32 (hp + 4) 0
    store32 sp hp
    store32 (sp - 4) $ hp + 8
  | otherwise =  error "bad syscall"
  where
    load8 = ffi "load8" :: Int -> IO Int
    load32 = ffi "load32" :: Int -> IO Int
    store32 = ffi "store32" :: Int -> Int -> IO ()

main :: IO ()
main = withElems ["src", "asm", "go", "out"] $ \[src, asmEl, goB, outE] -> do
  export "syscall" $ syscall outE
  void $ goB `onEvent` Click $ const $ do
    setProp asmEl "value" ""
    s <- getProp src "value"
    case wasm s of
      Left err -> setProp asmEl "value" err
      Right asm -> do
        setProp asmEl "value" $ show asm
        ffi "runWasmInts" asm :: IO ()
\end{code}
//////////////////////////////////////////////////////////////////////////////
