{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import Data.Char
import Data.Word
import Text.Parsec.ByteString
import Text.Parsec
import Text.Printf

data Type = I32 | I64 | F32 | F64 | Func | AnyFunc | Nada deriving (Show, Eq)
data ExternalKind = Function | Table | Memory | Global
data FuncType = FuncType [Type] [Type] deriving Show
data Import = Import String String FuncType deriving Show
data Body = Body [Type] [String] deriving Show
data Wasm = Wasm {
  types :: [FuncType],
  imports :: [Import],
  decls :: [Int],
  memory :: [(Int, Maybe Int)],
  globals :: [((Type, Bool), [String])],
  exports :: [(String, Int)],
  start :: Maybe Int,
  code :: [Body] } deriving Show

emptyWasm :: Wasm
emptyWasm = Wasm [] [] [] [] [] [] Nothing []

zeroOperandOps :: [(Int, String)]
zeroOperandOps = cmpOps ++ ariOps ++ crops where
  -- Copied from webpage and piped through a script:
  cmpOps = [(0x45, "i32.eqz"), (0x46, "i32.eq"), (0x47, "i32.ne"), (0x48, "i32.lt_s"), (0x49, "i32.lt_u"), (0x4a, "i32.gt_s"), (0x4b, "i32.gt_u"), (0x4c, "i32.le_s"), (0x4d, "i32.le_u"), (0x4e, "i32.ge_s"), (0x4f, "i32.ge_u"), (0x50, "i64.eqz"), (0x51, "i64.eq"), (0x52, "i64.ne"), (0x53, "i64.lt_s"), (0x54, "i64.lt_u"), (0x55, "i64.gt_s"), (0x56, "i64.gt_u"), (0x57, "i64.le_s"), (0x58, "i64.le_u"), (0x59, "i64.ge_s"), (0x5a, "i64.ge_u"), (0x5b, "f32.eq"), (0x5c, "f32.ne"), (0x5d, "f32.lt"), (0x5e, "f32.gt"), (0x5f, "f32.le"), (0x60, "f32.ge"), (0x61, "f64.eq"), (0x62, "f64.ne"), (0x63, "f64.lt"), (0x64, "f64.gt"), (0x65, "f64.le"), (0x66, "f64.ge")]
  ariOps = [(0x67, "i32.clz"), (0x68, "i32.ctz"), (0x69, "i32.popcnt"), (0x6a, "i32.add"), (0x6b, "i32.sub"), (0x6c, "i32.mul"), (0x6d, "i32.div_s"), (0x6e, "i32.div_u"), (0x6f, "i32.rem_s"), (0x70, "i32.rem_u"), (0x71, "i32.and"), (0x72, "i32.or"), (0x73, "i32.xor"), (0x74, "i32.shl"), (0x75, "i32.shr_s"), (0x76, "i32.shr_u"), (0x77, "i32.rotl"), (0x78, "i32.rotr"), (0x79, "i64.clz"), (0x7a, "i64.ctz"), (0x7b, "i64.popcnt"), (0x7c, "i64.add"), (0x7d, "i64.sub"), (0x7e, "i64.mul"), (0x7f, "i64.div_s"), (0x80, "i64.div_u"), (0x81, "i64.rem_s"), (0x82, "i64.rem_u"), (0x83, "i64.and"), (0x84, "i64.or"), (0x85, "i64.xor"), (0x86, "i64.shl"), (0x87, "i64.shr_s"), (0x88, "i64.shr_u"), (0x89, "i64.rotl"), (0x8a, "i64.rotr"), (0x8b, "f32.abs"), (0x8c, "f32.neg"), (0x8d, "f32.ceil"), (0x8e, "f32.floor"), (0x8f, "f32.trunc"), (0x90, "f32.nearest"), (0x91, "f32.sqrt"), (0x92, "f32.add"), (0x93, "f32.sub"), (0x94, "f32.mul"), (0x95, "f32.div"), (0x96, "f32.min"), (0x97, "f32.max"), (0x98, "f32.copysign"), (0x99, "f64.abs"), (0x9a, "f64.neg"), (0x9b, "f64.ceil"), (0x9c, "f64.floor"), (0x9d, "f64.trunc"), (0x9e, "f64.nearest"), (0x9f, "f64.sqrt"), (0xa0, "f64.add"), (0xa1, "f64.sub"), (0xa2, "f64.mul"), (0xa3, "f64.div"), (0xa4, "f64.min"), (0xa5, "f64.max"), (0xa6, "f64.copysign")]
  crops = [(0xa7, "i32.wrap/i64"), (0xa8, "i32.trunc_s/f32"), (0xa9, "i32.trunc_u/f32"), (0xaa, "i32.trunc_s/f64"), (0xab, "i32.trunc_u/f64"), (0xac, "i64.extend_s/i32"), (0xad, "i64.extend_u/i32"), (0xae, "i64.trunc_s/f32"), (0xaf, "i64.trunc_u/f32"), (0xb0, "i64.trunc_s/f64"), (0xb1, "i64.trunc_u/f64"), (0xb2, "f32.convert_s/i32"), (0xb3, "f32.convert_u/i32"), (0xb4, "f32.convert_s/i64"), (0xb5, "f32.convert_u/i64"), (0xb6, "f32.demote/f64"), (0xb7, "f64.convert_s/i32"), (0xb8, "f64.convert_u/i32"), (0xb9, "f64.convert_s/i64"), (0xba, "f64.convert_u/i64"), (0xbb, "f64.promote/f32"), (0xbc, "i32.reinterpret/f32"), (0xbd, "i64.reinterpret/f64"), (0xbe, "f32.reinterpret/i32"), (0xbf, "f64.reinterpret/i64")]

wasm :: Parser Wasm
wasm = do
  let
    rep getInt task = getInt >>= (`replicateM` task)

    varuint = f 1 0 where
      f :: Int -> Int -> Parser Int
      f m acc = do
        d <- ord <$> anyChar
        if d > 127 then f (m * 128) $ (d - 128) * m + acc else pure $ d*m + acc

    varint = varuint  -- TODO: Negative values.

    varuint1 = varuint
    varuint7 = ord <$> anyChar
    varuint32 = varuint

    varint7 = varint
    varint32 = varint
    varint64 = varint

    uint64 :: Parser Word64
    uint64 = do
      cs <- map ord <$> replicateM 8 anyChar
      let
        f _ acc [] = acc
        f m acc (d:ds) = f (m * 256) (acc + fromIntegral d * m) ds
      pure $ f 1 0 cs

    lstr = rep varuint32 anyChar

    allType = do
      t <- varuint7
      case lookup t [(0x7f, I32), (0x7e, I64), (0x7d, F32), (0x7c, F64), (0x70, AnyFunc), (0x60, Func), (0x40, Nada)] of
        Just ty -> pure ty
        Nothing -> error "bad type"

    valueType = do
      t <- allType
      when (t `notElem` [I32, I64, F32, F64]) $ error "bad value_type"
      pure t

    blockType = do
      t <- allType
      when (t `notElem` [I32, I64, F32, F64, Nada]) $ error "bad value_type"
      pure t

    externalKind = do
      k <- varuint7
      pure $ case k of
        0 -> Function
        1 -> Table
        2 -> Memory
        3 -> Global
        _ -> error "bad external_kind"

    funcType = do
      form <- varint7
      when (form /= 0x60) $ fail "expected func type"
      paramTypes <- rep varuint32 valueType
      returnTypes <- rep varuint1 valueType
      pure $ FuncType paramTypes returnTypes

    functionCount w = length (imports w) + length (decls w)

    sectType w = do
      t <- rep varuint32 funcType
      pure w { types = t }

    sectImport w = do
      ms <- rep varuint32 $ do
        moduleStr <- lstr
        fieldStr <- lstr
        k <- externalKind
        case k of
          Function -> do
            t <- varuint32
            when (t > length (types w)) $ fail "type out of range"
            pure $ Import moduleStr fieldStr (types w !! t)
      pure w { imports = ms }

    sectExport w = do
      es <- rep varuint32 $ do
        fieldStr <- lstr
        k <- externalKind
        t <- varuint32
        when (t > functionCount w) $ fail "function index out of range"
        case k of
          Function -> pure (fieldStr, t)
      pure w { exports = es }

    sectFunction w = do
      -- TODO: Check type indices are in range.
      sigs <- rep varuint32 varuint32
      pure w { decls = sigs }

    sectStart w = do
      i <- varuint32
      when (i > functionCount w) $ fail "function index out of range"
      pure w { start = Just i }

    sectTable w = undefined

    sectMemory w = do
      n <- varuint32
      when (n > 1) $ fail "MVP allows at most one memory"
      if n == 0 then pure w else do
        flags <- varuint1
        initial <- varuint32
        if flags > 0 then do
          m <- varuint32
          pure w { memory = [(initial, Just m)] }
        else pure w { memory = [(initial, Nothing)] }

    globalType = do
      ty <- valueType
      muta <- varuint1
      pure (ty, muta > 0)

    sectGlobal w = do
      gs <- rep varuint32 $ do
        gt <- globalType
        x <- codeBlock 0
        pure (gt, x)
      pure w { globals = gs }

    sectCode w = do
      bodies <- rep varuint32 $ do
        _ <- varuint32
        locals <- concat <$> rep varuint32 (rep varuint32 valueType)
        ops <- codeBlock 0
        pure $ Body locals ops
      pure w { code = bodies}

    codeBlock :: Int -> Parser [String]
    codeBlock lvl = do
      opcode <- varuint7
      s <- if
        | Just s <- lookup opcode $ zeroOperandOps ++ [(0x00, "unreachable"), (0x01, "nop"), (0x05, "else"), (0x0b, "end"), (0x0f, "return")] -> pure s
        | Just s <- lookup opcode [(0x02, "block"), (0x03, "loop"), (0x04, "if")] -> do
          bt <- blockType
          pure $ s ++ " " ++ show bt
        | Just s <- lookup opcode [(0x20, "get_local"), (0x21, "set_local"), (0x22, "tee_local"), (0x23, "get_global"), (0x24, "set_global")] -> do
          v <- varuint32
          pure $ s ++ " " ++ show v
        | Just s <- lookup opcode [(0x28, "i32.load"), (0x29, "i64.load"), (0x2a, "f32.load"), (0x2b, "f64.load"), (0x2c, "i32.load8_s"), (0x2d, "i32.load8_u"), (0x2e, "i32.load16_s"), (0x2f, "i32.load16_u"), (0x30, "i64.load8_s"), (0x31, "i64.load8_u"), (0x32, "i64.load16_s"), (0x33, "i64.load16_u"), (0x34, "i64.load32_s"), (0x35, "i64.load32_u"), (0x36, "i32.store"), (0x37, "i64.store"), (0x38, "f32.store"), (0x39, "f64.store"), (0x3a, "i32.store8"), (0x3b, "i32.store16"), (0x3c, "i64.store8"), (0x3d, "i64.store16"), (0x3e, "i64.store32")] -> do
          flags <- varuint32
          offset <- varuint32
          pure $ s ++ " " ++ show flags ++ " " ++ show offset
        | Just s <- lookup opcode [(0x0c, "br"), (0x0d, "br_if")] -> do
          v <- varuint32
          pure $ s ++ " " ++ show v
        | otherwise -> case opcode of
          0x0e -> do
            n <- varuint32
            tgts <- replicateM n varuint32
            defTgt <- varuint32
            pure $ "br_table " ++ show tgts ++ " " ++ show defTgt
          0x41 -> do
            i32 <- varint32
            pure $ "i32.const " ++ show i32
          0x42 -> do
            i64 <- varint64
            pure $ "i64.const " ++ show i64
          0x44 -> do
            u64 <- uint64
            pure $ "f64.const " ++ printf "%016x" u64
          0x10 -> do
            i <- varuint32
            pure $ "call " ++ show i
          _ -> fail ("bad opcode " ++ show opcode)
      if
        | s == "end" -> if lvl == 0
          then pure [s]
          else (s:) <$> codeBlock (lvl - 1)
        | head (words s) `elem` ["if", "block", "loop"] -> (s:) <$> codeBlock (lvl + 1)
        | otherwise -> (s:) <$> codeBlock lvl

    sect w = do
      n <- varuint7
      m <- varuint32
      s <- B8.pack <$> replicateM m anyChar  -- Ugh.
      let
        f = case n of
          1 -> sectType
          2 -> sectImport
          3 -> sectFunction
          4 -> sectTable
          5 -> sectMemory
          6 -> sectGlobal
          7 -> sectExport
          8 -> sectStart
          10 -> sectCode
          _ -> pure
      either (fail . show) pure $ parse (f w >>= (eof >>) . pure) "" s

    accumSect w | not $ null $ code w = pure w
    accumSect w = (eof >> pure w) <|> (sect w >>= accumSect)

  void $ string "\000asm\001\000\000\000"  -- Header and version.
  accumSect emptyWasm  -- Sections.

main :: IO ()
main = do
  s <- B.getContents
  case parse wasm "" s of
    Left err -> putStrLn $ "parse error: " ++ show err
    Right out -> print out
