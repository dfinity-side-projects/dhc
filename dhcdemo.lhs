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
function runWasmInts(a){WebAssembly.instantiate(new Uint8Array(a),
{system:{putInt:(lo,hi) => { Haste.sysPutInt(lo,hi); },
putStr:(a,n) => { Haste.sysPutStr(a,n) } }}).then(x => {
expo = x.instance.exports;
dv = new DataView(expo.memory.buffer);
document.getElementById('out').innerHTML ="";
expo['main']()});
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
import Demo

append :: Elem -> String -> IO ()
append e s = do
  v <- getProp e "innerHTML"
  setProp e "innerHTML" $ v ++ s

sysPutStr :: Elem -> Int -> Int -> IO ()
sysPutStr e a n = append e =<< mapM (fmap chr . load8 . (a +)) [0..n - 1]
  where load8 = ffi "load8" :: Int -> IO Int

sysPutInt :: Elem -> Int -> Int -> IO ()
sysPutInt e y x = append e $ case x of
  0 -> show y ++ if y >= 0 then "" else
    " (unsigned = " ++ show (fromIntegral y + b) ++ ")"
  _ -> show $ fromIntegral x * b + ((fromIntegral y + b) `mod` b)
  where b = 2^(32 :: Int) :: Integer

main :: IO ()
main = withElems ["src", "asm", "go", "out"] $ \[src, asmEl, goB, outE] -> do
  export "sysPutStr" $ sysPutStr outE
  export "sysPutInt" $ sysPutInt outE
  void $ goB `onEvent` Click $ const $ do
    setProp asmEl "value" ""
    s <- ("wdecl (main)\n" ++) <$> getProp src "value"
    case hsToWasm jsDemoBoost s of
      Left err -> setProp asmEl "value" err
      Right asm -> do
        setProp asmEl "value" $ show asm
        ffi "runWasmInts" asm :: IO ()
\end{code}
//////////////////////////////////////////////////////////////////////////////
