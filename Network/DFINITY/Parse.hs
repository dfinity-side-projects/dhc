{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Network.DFINITY.Parse (parseWasm, Wasm(..)) where

import Control.Monad
import qualified Data.ByteString.Char8 as B8
import Data.ByteString.Char8 (ByteString)
import Data.Char
import Data.Int
import Data.Maybe
import WasmOp

data ExternalKind = Function | Table | Memory | Global
type FuncType = ([WasmType], [WasmType])
type Body = ([WasmOp], [WasmOp])
type Import = ((String, String), FuncType)

data Wasm = Wasm
  { types :: [FuncType]
  , imports :: [Import]
  , decls :: [FuncType]
  , tableSize :: Int
  , memory :: [(Int, Maybe Int)]
  , globals :: [((WasmType, Bool), [WasmOp])]
  , exports :: [(String, Int)]
  , start :: Maybe Int
  , elemSection :: [(Int, [Int])]
  , code :: [Body]
  , dataSection :: [([WasmOp], String)]
  , dfnExports :: [(String, [WasmType])]
  , martinTypes :: [[WasmType]]
  , martinTypeMap :: [(Int, Int)]
  , martinGlobals :: [(Int, WasmType)]
  , persist :: [(Int, WasmType)]
  , haskell :: String
  } deriving Show

emptyWasm :: Wasm
emptyWasm = Wasm [] [] [] 0 [] [] [] Nothing [] [] [] [] [] [] [] [] ""

data ByteParser a = ByteParser (ByteString -> Either String (a, ByteString))

instance Functor     ByteParser where fmap = liftM
instance Applicative ByteParser where {pure  = return; (<*>) = ap}
instance Monad       ByteParser where
  ByteParser f >>= g = ByteParser $ (good =<<) . f
    where good (r, t) = let ByteParser gg = g r in gg t
  return a = ByteParser $ \s -> Right (a, s)

next :: ByteParser Char
next = ByteParser f where
  f s | B8.null s = Left "unexpected EOF"
      | otherwise = Right (B8.head s, B8.tail s)

repNext :: Int -> ByteParser ByteString
repNext n = ByteParser f where
  f s | B8.length s < n = Left "missing bytes or size too large"
      | otherwise = Right $ B8.splitAt n s

isEof :: ByteParser Bool
isEof = ByteParser f where f s = Right (B8.null s, s)

bad :: String -> ByteParser a
bad = ByteParser . const . Left

byteParse :: ByteParser a -> ByteString -> Either String a
byteParse (ByteParser f) s = f s >>= (\(w, t) ->
  if B8.null t then Right w else Left "expected EOF")

remainder :: ByteParser ByteString
remainder = ByteParser $ \s -> Right (s, "")

initLocal :: WasmType -> WasmOp
initLocal I32 = I32_const 0
initLocal _ = error "TODO"

wasm :: ByteParser Wasm
wasm = do
  let
    rep getInt task = getInt >>= (`replicateM` task)

    varuint = fromIntegral <$> f 1 0 where
      f :: Integer -> Integer -> ByteParser Integer
      f m acc = do
        d <- fromIntegral . ord <$> next
        if d > 127 then f (m * 128) $ (d - 128) * m + acc else pure $ d*m + acc

    varint = f 1 0 where
      f :: Integer -> Integer -> ByteParser Integer
      f m acc = do
        d <- fromIntegral . ord <$> next
        if d > 127 then f (m * 128) $ (d - 128) * m + acc else pure $
          if d >= 64 then d*m + acc - 128*m else d*m + acc

    varuint1 = varuint
    varuint7 = ord <$> next
    varuint32 = varuint

    varint7 :: ByteParser Int
    varint7 = do
      c <- ord <$> next
      when (c >= 128) $ error "bad varint7"
      pure $ if c >= 64 then c - 128 else c

    varint32 :: ByteParser Int32
    varint32 = fromIntegral <$> varint

    varint64 :: ByteParser Int64
    varint64 = fromIntegral <$> varint

    lstr = rep varuint32 next

    allType = do
      t <- varuint7
      case lookup t [(0x7f, I32), (0x7e, I64), (0x7d, F32), (0x7c, F64), (0x70, AnyFunc), (0x60, Func), (0x40, Nada)] of
        Just ty -> pure ty
        Nothing -> bad $ "bad type: " ++ show t

    valueType = do
      t <- allType
      when (t `notElem` [I32, I64, F32, F64]) $ bad "bad value_type"
      pure t

    blockType = do
      t <- allType
      when (t `notElem` [I32, I64, F32, F64, Nada]) $ bad "bad value_type"
      pure t

    elemType = do
      t <- allType
      when (t /= AnyFunc) $ bad "bad elem_type"

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
      when (form /= -32) $ bad "expected func type"
      paramTypes <- rep varuint32 valueType
      returnTypes <- rep varuint1 valueType
      pure (paramTypes, returnTypes)

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
            when (t > length (types w)) $ bad "type out of range"
            pure ((moduleStr, fieldStr), types w !! t)
          _ -> error "TODO"
      pure w { imports = ms }

    sectExport w = do
      es <- rep varuint32 $ do
        fieldStr <- lstr
        k <- externalKind
        t <- varuint32
        case k of
          Function -> do
            when (t > functionCount w) $ bad "function index out of range"
            pure $ Just (fieldStr, t)
          Global -> pure Nothing
          Memory -> pure Nothing
          Table -> pure Nothing
      pure w { exports = catMaybes es }

    sectFunction w = do
      sigs <- rep varuint32 $ do
        t <- varuint32
        when (t > length (types w)) $ bad "type out of range"
        pure $ types w !! t
      pure w { decls = sigs }

    sectTable w = do
      n <- varuint32
      when (n > 1) $ bad "MVP allows at most one table"
      if n == 0 then pure w else do
        elemType
        flags <- varuint1
        m <- varuint32
        when (flags == 1) $ void varuint32  -- TODO: Record maximum.
        pure w { tableSize = m }

    sectMemory w = do
      n <- varuint32
      when (n > 1) $ bad "MVP allows at most one memory"
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
        x <- codeBlock
        pure (gt, x)
      pure w { globals = gs }

    sectStart w = do
      i <- varuint32
      when (i > functionCount w) $ bad "function index out of range"
      pure w { start = Just i }

    sectElement w = do
      es <- rep varuint32 $ do
        index <- varuint32
        when (index /= 0) $ bad "MVP allows at most one table"
        [I32_const offset] <- codeBlock
        ns <- rep varuint32 $ do
          i <- varuint32
          when (i > functionCount w) $ bad "function index out of range"
          pure $ fromIntegral i
        pure (fromIntegral offset, ns)
      pure w { elemSection = es }

    sectCode w = do
      bodies <- rep varuint32 $ do
        _ <- varuint32  -- Size.
        locals <- concat <$> rep varuint32 (do
          n <- varuint32
          t <- initLocal <$> valueType
          pure $ replicate n t)
        ops <- codeBlock
        pure (locals, ops)
      pure w { code = bodies}

    sectData w = do
      ds <- rep varuint32 $ do
        index <- varuint32
        when (index /= 0) $ bad "MVP allows at most one memory"
        offset <- codeBlock
        (,) offset <$> lstr
      pure w { dataSection = ds }

    martinFuncType = do
      form <- varint7
      when (form /= -32) $ bad "expected func type"
      paramTypes <- rep varuint32 martinValueType
      z <- varuint1
      when (z /= 0) $ bad "must have no return value"
      pure paramTypes

    martinValueType = do
      t <- varuint7
      maybe (bad $ "bad type: " ++ show t) pure $ lookup t
        [ (0x7f, I32)
        , (0x7e, I64)
        , (0x7d, F32)
        , (0x7c, F64)
        , (0x70, AnyFunc)
        , (0x6f, Ref "Actor")
        , (0x6e, Ref "Module")
        , (0x6d, Ref "Port")
        , (0x6c, Ref "Databuf")
        , (0x6b, Ref "Elem")
        ]

    sectCustom w = do
      name <- lstr
      case name of
        "types" -> do
          t <- rep varuint32 martinFuncType
          pure w { martinTypes = t }
        "typeMap" -> do
          tm <- rep varuint32 $ (,) <$> varuint32 <*> varuint32
          pure w { martinTypeMap = tm }
        "persist" -> do
          g <- rep varuint32 $ do
            tmp <- varuint7
            when (tmp /= 3) $ bad "expect 3"
            (,) <$> varuint32 <*> martinValueType
          pure w { martinGlobals = g }
        "dfndbg" -> remainder >> pure w
        "dfnhs" -> do
          void $ varuint32  -- Should be 1.
          s <- remainder
          pure w { haskell = B8.unpack s }
        _ -> remainder >> pure w

    codeBlock :: ByteParser [WasmOp]
    codeBlock = do
      opcode <- varuint7
      s <- if
        | Just s <- lookup opcode $ zeroOperandOps -> pure s
        | Just s <- lookup opcode [(0x02, Block), (0x03, Loop), (0x04, If)] -> do
          bt <- blockType
          bl <- codeBlock
          pure $ s bt bl
        | Just s <- lookup opcode [(0x20, Get_local), (0x21, Set_local), (0x22, Tee_local), (0x23, Get_global), (0x24, Set_global)] -> do
          v <- varuint32
          pure $ s v
        | Just s <- lookup opcode [(0x28, I32_load), (0x29, I64_load), (0x2a, F32_load), (0x2b, F64_load), (0x2c, I32_load8_s), (0x2d, I32_load8_u), (0x2e, I32_load16_s), (0x2f, I32_load16_u), (0x30, I64_load8_s), (0x31, I64_load8_u), (0x32, I64_load16_s), (0x33, I64_load16_u), (0x34, I64_load32_s), (0x35, I64_load32_u), (0x36, I32_store), (0x37, I64_store), (0x38, F32_store), (0x39, F64_store), (0x3a, I32_store8), (0x3b, I32_store16), (0x3c, I64_store8), (0x3d, I64_store16), (0x3e, I64_store32)] -> do
          flags <- varuint32
          offset <- varuint32
          pure $ s flags offset
        | Just s <- lookup opcode [(0x0c, Br), (0x0d, Br_if)] -> do
          v <- varuint32
          pure $ s v
        | otherwise -> case opcode of
          0x0e -> do
            n <- varuint32
            tgts <- replicateM n varuint32
            defTgt <- varuint32
            pure $ Br_table tgts defTgt
          0x41 -> do
            i32 <- varint32
            pure $ I32_const i32
          0x42 -> do
            i64 <- varint64
            pure $ I64_const i64
          0x10 -> do
            i <- varuint32
            pure $ Call i
          0x11 -> do
            i <- varuint32
            0 <- varuint1
            pure $ Call_indirect i
          _ -> bad ("bad opcode " ++ show opcode)
      if
        | End <- s -> pure []
        | otherwise -> (s:) <$> codeBlock

    sect w = isEof >>= \b -> if b then pure w else do
      n <- varuint7
      m <- varuint32
      s <- repNext m
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
          9 -> sectElement
          10 -> sectCode
          11 -> sectData
          0 -> sectCustom
          _ -> pure
      case byteParse (f w) s of
        Left err -> bad err
        Right w1 -> sect w1

  header <- repNext 8  -- Header and version.
  if header /= "\000asm\001\000\000\000" then
    bad "bad header or version"
  else sect emptyWasm  -- Sections.

parseWasm :: B8.ByteString -> Either String Wasm
parseWasm b = do
  w@Wasm{imports, exports, martinTypeMap, martinTypes} <- byteParse wasm b
  pure w { dfnExports = catMaybes $ (\(s, k) -> (,) s . (martinTypes!!) <$> lookup (k - length imports) martinTypeMap) <$> exports }
