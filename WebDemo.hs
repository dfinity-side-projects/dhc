module WebDemo (hsToGMachineWebDemo, hsToWasmWebDemo) where

import Control.Arrow
import Asm
import DHC
import SoloSyscall
import WasmOp

webDemoSys :: ExternType
webDemoSys = \_ _ -> Nothing

webDemoBoost :: Boost
webDemoBoost = Boost [(("dhc", "system"), ([I32, I32, I32], []))] $
  second (uncurry genSyscallFromType) <$>
  [ ("putStr", (21, TC "String" :-> io (TC "()")))
  , ("putInt", (22, TC "Int" :-> io (TC "()")))
  ]
  where io = TApp (TC "IO")

hsToWasmWebDemo :: String -> Either String [Int]
hsToWasmWebDemo prog = wasmBinary <$> hsToWasm webDemoBoost webDemoSys prog

hsToGMachineWebDemo :: String -> Either String (GlobalTable, [(String, [Ins])])
hsToGMachineWebDemo haskell = hsToIns webDemoBoost webDemoSys haskell
