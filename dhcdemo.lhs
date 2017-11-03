= DHC Demo =

The following compiles Haskell to WebAssembly and runs it.

It expects a pure function named `run`, which it reduces to weak head
normal form. If the result is an integer, then we print this integer. If
the result is algebraic data type, then we print the index of the data
constructor; for example, `False` and `Nothing` are 0, `True` and `Just`
are 1.

Only a tiny fragment of the language is supported. There is almost no syntax
sugar.

There is no garbage collection nor lazy evaluation.

[pass]
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
<script type="text/javascript">
function runWasmInts(a){WebAssembly.instantiate(new Uint8Array(a),
{i:{f:(x,y) => Haste.outputcb(x,y)}}).then(x => x.instance.exports.e());}
</script>
<script src="dhcdemo.js">
</script>
<p><textarea id="src" rows="25" cols="80">
factorial n = (case n == 0 of True -> 1; False -> n * factorial (n - 1));
foldr f n xs = (case xs of [] -> n; 
                           (a:as) -> f a (foldr f n as));
uncurry f p = (case p of (a, b) -> f a b);
sum = foldr (+) 0;
enumFromTo a b = (case a > b of True -> []; False -> a : enumFromTo (a + 1) b);
run = uncurry (+) (factorial 5, sum [1..5])
</textarea></p>
<button id="go">Compile & Run!</button>
<p><textarea id="asm" readonly rows="5" cols="80">
</textarea></p>
<div id="out"></div>
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

//////////////////////////////////////////////////////////////////////////////
\begin{code}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Asm

printInts :: Elem -> Int -> Int -> IO ()
printInts e x y = setProp e "innerHTML" $ case x of
  0 -> show y ++ if y >= 0 then "" else
    " (unsigned = " ++ show (fromIntegral y + b) ++ ")"
  _ -> show $ fromIntegral x * b + ((fromIntegral y + b) `mod` b)
  where b = 2^(32 :: Int) :: Integer

main :: IO ()
main = withElems ["src", "asm", "go", "out"] $ \[src, asmEl, goB, outE] -> do
  export "outputcb" $ printInts outE
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
