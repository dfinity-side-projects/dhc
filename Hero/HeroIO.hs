-- HeroIO is a wasm engine with a more natural interface for setting
-- table entries to IO functions.
--
-- On principle, I'd like to keep a pure wasm engine,
-- which is why HeroIO is distinct from Hero.

module Hero.HeroIO
  ( HeroIO
  , decode
  , invoke
  , getMemory
  , putMemory
  , getSlot
  , setSlot
  , getExport
  , globals
  ) where

import Data.Int
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Word (Word8)
import Hero.Hero (Hero)
import qualified Hero.Hero as Hero
import WasmOp

newtype HeroAux = HeroAux { heroAux :: [WasmOp] -> HeroIO -> IO ([WasmOp], HeroIO) }

type HeroIO = (((String, String) -> HeroAux, IntMap HeroAux), Hero)

decode :: ((String, String) -> [WasmOp] -> HeroIO -> IO ([WasmOp], HeroIO)) -> Hero.Wasm -> HeroIO
decode imps w = ((HeroAux . imps, IM.empty), Hero.decode w)

getMemory :: Int32 -> HeroIO -> Word8
getMemory k (_, h) = Hero.getMemory k h

putMemory :: Int32 -> Word8 -> HeroIO -> HeroIO
putMemory k v (x, h) = (x, Hero.putMemory k v h)

getSlot :: Int32 -> HeroIO -> Int
getSlot k (_, h) = Hero.getSlot k h

getExport :: String -> HeroIO -> Int
getExport k (_, h) = Hero.getExport k h

globals :: HeroIO -> [(Int, WasmOp)]
globals (_, h) = Hero.globals h

setSlot :: Int32 -> ([WasmOp] -> HeroIO -> IO ([WasmOp], HeroIO)) -> HeroIO -> HeroIO
setSlot n f ((imps, x), vm) = ((imps, IM.insert k (HeroAux f) x), Hero.setSlot n k vm)
  where k = IM.size x

invoke
  :: [(Int, WasmOp)]  -- Globals.
  -> Int              -- Function.
  -> [WasmOp]         -- Arguments.
  -> HeroIO           -- VM.
  -> IO ([WasmOp], HeroIO)
invoke gs f as h = Hero.invoke (heroAux . fst (fst h), resolve) gs f as h

resolve :: Int -> [WasmOp] -> HeroIO -> IO ([WasmOp], HeroIO)
resolve k args h = (heroAux $ snd (fst h) IM.! k) args h
