{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Hero.Parse (parseWasm, Wasm(..), ripWasm, elTable) where

#ifdef __HASTE__
import qualified Data.Map.Strict as IM
import qualified Data.Set as IS
#else
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
#endif
import Control.Arrow
import Control.Monad
import qualified Data.ByteString as B
import Data.ByteString (ByteString)
import Data.Char
import Data.Int
import Data.Maybe
import Data.Word
import WasmOp

#ifdef __HASTE__
type IntMap = IM.Map Int
#endif

data ExternalKind = Function | Table | Memory | Global
type FuncType = ([WasmType], [WasmType])

data Wasm = Wasm
  { types :: [FuncType]
  , imports :: [((String, String), FuncType)]
  , decls :: [FuncType]
  , tableSize :: Int
  , memory :: [(Int, Maybe Int)]
  , globalSection :: [((WasmType, Bool), [WasmOp])]
  , exports :: [(String, Int)]
  , start :: Maybe Int
  , elemSection :: [(Int, [Int])]
  , functions :: IntMap WasmFun
  , dataSection :: [([WasmOp], [Word8])]
  , dfnExports :: [(String, [WasmType])]
  , martinTypes :: [[WasmType]]
  , martinTypeMap :: [(Int, Int)]
  , permaGlobals :: [(Int, WasmType)]
  , persist :: [(Int, WasmType)]
  , haskell :: String
  } deriving Show

emptyWasm :: Wasm
emptyWasm = Wasm [] [] [] 0 [] [] [] Nothing [] IM.empty [] [] [] [] [] [] ""

data ByteParser a = ByteParser (ByteString -> Either String (a, ByteString))

instance Functor     ByteParser where fmap = liftM
instance Applicative ByteParser where {pure = return; (<*>) = ap}
instance Monad       ByteParser where
  ByteParser f >>= g = ByteParser $ (good =<<) . f
    where good (r, t) = let ByteParser gg = g r in gg t
  return a = ByteParser $ \s -> Right (a, s)

next :: ByteParser Word8
next = ByteParser f where
  f s | B.null s = Left "unexpected EOF"
      | otherwise = Right (B.head s, B.tail s)

repNext :: Int -> ByteParser ByteString
repNext n = ByteParser f where
  f s | B.length s < n = Left "missing bytes or size too large"
      | otherwise = Right $ B.splitAt n s

isEof :: ByteParser Bool
isEof = ByteParser f where f s = Right (B.null s, s)

bad :: String -> ByteParser a
bad = ByteParser . const . Left

byteParse :: ByteParser a -> ByteString -> Either String a
byteParse (ByteParser f) s = f s >>= (\(w, t) ->
  if B.null t then Right w else Left "expected EOF")

remainder :: ByteParser ByteString
remainder = ByteParser $ \s -> Right (s, "")

wasm :: ByteParser Wasm
wasm = do
  let
    rep getInt task = getInt >>= (`replicateM` task)

    varuint = fromIntegral <$> f 1 0 where
      f :: Integer -> Integer -> ByteParser Integer
      f m acc = do
        d <- fromIntegral <$> next
        if d > 127 then f (m * 128) $ (d - 128) * m + acc else pure $ d*m + acc

    varint = f 1 0 where
      f :: Integer -> Integer -> ByteParser Integer
      f m acc = do
        d <- fromIntegral <$> next
        if d > 127 then f (m * 128) $ (d - 128) * m + acc else pure $
          if d >= 64 then d*m + acc - 128*m else d*m + acc

    varuint1 = varuint
    varuint7 = next
    varuint32 = varuint

    varint7 :: ByteParser Int
    varint7 = do
      c <- fromIntegral <$> next
      when (c >= 128) $ error "bad varint7"
      pure $ if c >= 64 then c - 128 else c

    varint32 :: ByteParser Int32
    varint32 = fromIntegral <$> varint

    varint64 :: ByteParser Int64
    varint64 = fromIntegral <$> varint

    lstr :: ByteParser String
    lstr = rep varuint32 $ chr . fromIntegral <$> next

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
        x <- codeBlock w
        pure (gt, x)
      pure w { globalSection = gs }

    sectStart w = do
      i <- varuint32
      when (i > functionCount w) $ bad "function index out of range"
      pure w { start = Just i }

    sectElement w = do
      es <- rep varuint32 $ do
        index <- varuint32
        when (index /= 0) $ bad "MVP allows at most one table"
        ~[I32_const offset] <- codeBlock w
        ns <- rep varuint32 $ do
          i <- varuint32
          when (i > functionCount w) $ bad "function index out of range"
          pure $ fromIntegral i
        pure (fromIntegral offset, ns)
      pure w { elemSection = es }

    sectCode w = do
      fs <- rep varuint32 $ do
        _ <- varuint32  -- Size.
        locals <- concat <$> rep varuint32 (replicate <$> varuint32 <*> valueType)
        ops <- codeBlock w
        pure (locals, ops)
      pure w { functions = IM.fromList $ zip [length (imports w)..]
        $ zipWith (\a (b, c) -> WasmFun a b c) (decls w) fs }

    sectData w = do
      ds <- rep varuint32 $ do
        index <- varuint32
        when (index /= 0) $ bad "MVP allows at most one memory"
        offset <- codeBlock w
        (,) offset <$> rep varuint32 next
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
        , (0x70, Ref "Any")  -- AnyFunc in standard wasm.
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
          pure w { permaGlobals = g }
        "dfndbg" -> remainder >> pure w
        "dfnhs" -> do
          void $ varuint32  -- Should be 1.
          s <- remainder
          pure w { haskell = chr . fromIntegral <$> B.unpack s }
        _ -> remainder >> pure w

    codeBlock :: Wasm -> ByteParser [WasmOp]
    codeBlock w = do
      opcode <- fromIntegral <$> varuint7
      s <- if
        | Just s <- lookup opcode $ zeroOperandOps -> pure s
        | Just s <- lookup opcode [(0x02, Block), (0x03, Loop)] -> do
          bt <- blockType
          bl <- codeBlock w
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
          0x04 -> do
            bt <- blockType
            bl <- codeBlock w
            case last bl of
              Else -> do
                bl2 <- codeBlock w
                pure $ If bt (init bl) bl2
              _ -> pure $ If bt bl []
          0x05 -> pure Else
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
            ~ 0 <- varuint1
            when (i >= length (types w)) $ bad "Call_indirect index out of range"
            pure $ Call_indirect $ types w !! i
          _ -> bad ("bad opcode " ++ show opcode)
      if
        | Else <- s -> pure [Else]
        | End <- s -> pure []
        | otherwise -> (s:) <$> codeBlock w

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

parseWasm :: B.ByteString -> Either String Wasm
parseWasm b = do
  w@Wasm{imports, exports, martinTypeMap, martinTypes} <- byteParse wasm b
  let
    findType k
      | Just mt <- lookup (k - length imports) martinTypeMap = martinTypes!!mt
      -- Outputs make no sense for dfn, but we support them so we can use this
      -- code more generally.
      | k < length imports = fst $ snd $ imports !! k
      | otherwise = fst $ decls w !! (k - length imports)
  pure w { dfnExports = second findType <$> exports }

ripWasm :: [String] -> Wasm -> ([(String, Int)], [(Int, WasmFun)])
ripWasm es w = (zip es idxs, fMap)
  where
  Just idxs = mapM (`lookup` exports w) es
  reachable = IS.elems $ followCalls idxs $ funBody <$> functions w
  fMap = (\i -> (i, functions w IM.! i)) <$> reachable

-- Returns elements of table as
-- association list of slot to (function index, function type).
elTable :: Wasm -> [(Int, (Int, [WasmType]))]
elTable (Wasm {martinTypes, martinTypeMap, elemSection, imports})
  = second (\n -> (n, maybe (error "BUG! missing type")
    (martinTypes!!) $ lookup (n  - length imports) martinTypeMap)) <$> es where
  es = concatMap (\(offset, ns) -> zip [offset..] ns) elemSection
