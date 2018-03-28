-- Provides a function that runs a DHC program that expects 2 functions:
--
--   putStr :: String -> IO ()
--   putInt :: Int -> IO ()
--
-- For testing. Could be turned into a runhaskell-like tool with:
--
--   main = putStr =<< runWebDHC =<< getContents

module WebHero (runWebDHC) where

import qualified Data.ByteString as B
import Data.Char

import Asm
import Ast
import Boost
import Hero
import WasmOp

runWebDHC :: String -> IO String
runWebDHC src = case hsToWasm boost (\_ _ -> Nothing) src of
  Left err -> error err
  Right (DfnWasm _ ints) -> let
    Right wasm = parseWasm $ B.pack $ fromIntegral <$> ints
    in stateVM . snd <$> (runWasm syscall "#main" $ mkHeroVM "" wasm [])

syscall :: (String, String) -> HeroVM String -> [WasmOp] -> IO (HeroVM String)
syscall ("system", "putStr") vm [I32_const ptr, I32_const len] = pure
  $ putStateVM (stateVM vm ++
    [chr $ getNumVM 1 (ptr + i) vm | i <- [0..len - 1]]) vm
syscall ("system", "putInt") vm [I64_const i] = pure
  $ putStateVM (stateVM vm ++ show i) vm
syscall _ _ _ = error "BUG! bad syscall "

sp :: Int
sp = 0

boost :: Boost
boost = Boost
  [ (("system", "putStr"), ([I32, I32], []))
  , (("system", "putInt"), ([I64], []))
  ]
  []
  [ ("putStr", (TC "String" :-> io (TC "()"),
    [ Custom $ ReduceArgs 1
    , Get_global sp  -- system.putStr ([[sp + 4] + 4] [[sp + 4] + 8]) [[sp + 4] + 12]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I32_load 2 0
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 12
    , I32_add
    , I32_load 2 0
    , Custom $ CallSym "system.putStr"
    , Get_global sp  -- sp = sp + 12
    , I32_const 12
    , I32_add
    , Set_global sp
    , Custom $ CallSym "#nil42"
    , End
    ]))
  , ("putInt", (TC "Int" :-> io (TC "()"),
    [ Custom $ ReduceArgs 1
    , Get_global sp  -- system.putInt [[sp + 4] + 8].64
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 8
    , I32_add
    , I64_load 3 0
    , Custom $ CallSym "system.putInt"
    , Get_global sp  -- sp = sp + 12
    , I32_const 12
    , I32_add
    , Set_global sp
    , Custom $ CallSym "#nil42"
    , End
    ]))
  ]
  []
  where io = TApp (TC "IO")
