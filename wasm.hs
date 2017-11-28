{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import Data.Char
import Data.Int
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List
import Data.Word
import Text.Parsec.ByteString
import Text.Parsec

data Type = I32 | I64 | F32 | F64 | Func | AnyFunc | Nada deriving (Show, Eq)
data ExternalKind = Function | Table | Memory | Global
type FuncType = ([Type], [Type])
data Import = Import String String FuncType deriving Show
data Body = Body [Type] [Op] deriving Show
data Wasm = Wasm {
  types :: [FuncType],
  imports :: [Import],
  decls :: [Int],
  memory :: [(Int, Maybe Int)],
  globals :: [((Type, Bool), [Op])],
  exports :: [(String, Int)],
  start :: Maybe Int,
  code :: [Body] } deriving Show

emptyWasm :: Wasm
emptyWasm = Wasm [] [] [] [] [] [] Nothing []

data Op = I32_eqz | I32_eq | I32_ne | I32_lt_s | I32_lt_u | I32_gt_s | I32_gt_u | I32_le_s | I32_le_u | I32_ge_s | I32_ge_u | I64_eqz | I64_eq | I64_ne | I64_lt_s | I64_lt_u | I64_gt_s | I64_gt_u | I64_le_s | I64_le_u | I64_ge_s | I64_ge_u | F32_eq | F32_ne | F32_lt | F32_gt | F32_le | F32_ge | F64_eq | F64_ne | F64_lt | F64_gt | F64_le | F64_ge | I32_clz | I32_ctz | I32_popcnt | I32_add | I32_sub | I32_mul | I32_div_s | I32_div_u | I32_rem_s | I32_rem_u | I32_and | I32_or | I32_xor | I32_shl | I32_shr_s | I32_shr_u | I32_rotl | I32_rotr | I64_clz | I64_ctz | I64_popcnt | I64_add | I64_sub | I64_mul | I64_div_s | I64_div_u | I64_rem_s | I64_rem_u | I64_and | I64_or | I64_xor | I64_shl | I64_shr_s | I64_shr_u | I64_rotl | I64_rotr | F32_abs | F32_neg | F32_ceil | F32_floor | F32_trunc | F32_nearest | F32_sqrt | F32_add | F32_sub | F32_mul | F32_div | F32_min | F32_max | F32_copysign | F64_abs | F64_neg | F64_ceil | F64_floor | F64_trunc | F64_nearest | F64_sqrt | F64_add | F64_sub | F64_mul | F64_div | F64_min | F64_max | F64_copysign | I32_wrap_i64 | I32_trunc_s_f32 | I32_trunc_u_f32 | I32_trunc_s_f64 | I32_trunc_u_f64 | I64_extend_s_i32 | I64_extend_u_i32 | I64_trunc_s_f32 | I64_trunc_u_f32 | I64_trunc_s_f64 | I64_trunc_u_f64 | F32_convert_s_i32 | F32_convert_u_i32 | F32_convert_s_i64 | F32_convert_u_i64 | F32_demote_f64 | F64_convert_s_i32 | F64_convert_u_i32 | F64_convert_s_i64 | F64_convert_u_i64 | F64_promote_f32 | I32_reinterpret_f32 | I64_reinterpret_f64 | F32_reinterpret_i32 | F64_reinterpret_i64
  | I32_load Int Int | I64_load Int Int | F32_load Int Int | F64_load Int Int | I32_load8_s Int Int | I32_load8_u Int Int | I32_load16_s Int Int | I32_load16_u Int Int | I64_load8_s Int Int | I64_load8_u Int Int | I64_load16_s Int Int | I64_load16_u Int Int | I64_load32_s Int Int | I64_load32_u Int Int | I32_store Int Int | I64_store Int Int | F32_store Int Int | F64_store Int Int | I32_store8 Int Int | I32_store16 Int Int | I64_store8 Int Int | I64_store16 Int Int | I64_store32 Int Int
  | Unreachable | Nop | Else | End | Return
  | Block Type [Op] | Loop Type [Op] | If Type [Op]
  | Get_local Int | Set_local Int | Tee_local Int | Get_global Int | Set_global Int
  | I32_const Int32 | I64_const Int64 | F32_const Float | F64_const Double
  | Br_table [Int] Int
  | Br Int | Br_if Int
  | Call Int deriving Show

zeroOperandOps :: [(Int, Op)]
zeroOperandOps = cmpOps ++ ariOps ++ crops where
  cmpOps = [(0x45, I32_eqz), (0x46, I32_eq), (0x47, I32_ne), (0x48, I32_lt_s), (0x49, I32_lt_u), (0x4a, I32_gt_s), (0x4b, I32_gt_u), (0x4c, I32_le_s), (0x4d, I32_le_u), (0x4e, I32_ge_s), (0x4f, I32_ge_u), (0x50, I64_eqz), (0x51, I64_eq), (0x52, I64_ne), (0x53, I64_lt_s), (0x54, I64_lt_u), (0x55, I64_gt_s), (0x56, I64_gt_u), (0x57, I64_le_s), (0x58, I64_le_u), (0x59, I64_ge_s), (0x5a, I64_ge_u), (0x5b, F32_eq), (0x5c, F32_ne), (0x5d, F32_lt), (0x5e, F32_gt), (0x5f, F32_le), (0x60, F32_ge), (0x61, F64_eq), (0x62, F64_ne), (0x63, F64_lt), (0x64, F64_gt), (0x65, F64_le), (0x66, F64_ge)]
  ariOps = [(0x67, I32_clz), (0x68, I32_ctz), (0x69, I32_popcnt), (0x6a, I32_add), (0x6b, I32_sub), (0x6c, I32_mul), (0x6d, I32_div_s), (0x6e, I32_div_u), (0x6f, I32_rem_s), (0x70, I32_rem_u), (0x71, I32_and), (0x72, I32_or), (0x73, I32_xor), (0x74, I32_shl), (0x75, I32_shr_s), (0x76, I32_shr_u), (0x77, I32_rotl), (0x78, I32_rotr), (0x79, I64_clz), (0x7a, I64_ctz), (0x7b, I64_popcnt), (0x7c, I64_add), (0x7d, I64_sub), (0x7e, I64_mul), (0x7f, I64_div_s), (0x80, I64_div_u), (0x81, I64_rem_s), (0x82, I64_rem_u), (0x83, I64_and), (0x84, I64_or), (0x85, I64_xor), (0x86, I64_shl), (0x87, I64_shr_s), (0x88, I64_shr_u), (0x89, I64_rotl), (0x8a, I64_rotr), (0x8b, F32_abs), (0x8c, F32_neg), (0x8d, F32_ceil), (0x8e, F32_floor), (0x8f, F32_trunc), (0x90, F32_nearest), (0x91, F32_sqrt), (0x92, F32_add), (0x93, F32_sub), (0x94, F32_mul), (0x95, F32_div), (0x96, F32_min), (0x97, F32_max), (0x98, F32_copysign), (0x99, F64_abs), (0x9a, F64_neg), (0x9b, F64_ceil), (0x9c, F64_floor), (0x9d, F64_trunc), (0x9e, F64_nearest), (0x9f, F64_sqrt), (0xa0, F64_add), (0xa1, F64_sub), (0xa2, F64_mul), (0xa3, F64_div), (0xa4, F64_min), (0xa5, F64_max), (0xa6, F64_copysign)]
  crops = [(0xa7, I32_wrap_i64), (0xa8, I32_trunc_s_f32), (0xa9, I32_trunc_u_f32), (0xaa, I32_trunc_s_f64), (0xab, I32_trunc_u_f64), (0xac, I64_extend_s_i32), (0xad, I64_extend_u_i32), (0xae, I64_trunc_s_f32), (0xaf, I64_trunc_u_f32), (0xb0, I64_trunc_s_f64), (0xb1, I64_trunc_u_f64), (0xb2, F32_convert_s_i32), (0xb3, F32_convert_u_i32), (0xb4, F32_convert_s_i64), (0xb5, F32_convert_u_i64), (0xb6, F32_demote_f64), (0xb7, F64_convert_s_i32), (0xb8, F64_convert_u_i32), (0xb9, F64_convert_s_i64), (0xba, F64_convert_u_i64), (0xbb, F64_promote_f32), (0xbc, I32_reinterpret_f32), (0xbd, I64_reinterpret_f64), (0xbe, F32_reinterpret_i32), (0xbf, F64_reinterpret_i64)]

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

    sectTable _ = undefined

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
        x <- codeBlock
        pure (gt, x)
      pure w { globals = gs }

    sectCode w = do
      bodies <- rep varuint32 $ do
        _ <- varuint32
        locals <- concat <$> rep varuint32 (rep varuint32 valueType)
        ops <- codeBlock
        pure $ Body locals ops
      pure w { code = bodies}

    codeBlock :: Parser [Op]
    codeBlock = do
      opcode <- varuint7
      s <- if
        | Just s <- lookup opcode $ zeroOperandOps ++ [(0x00, Unreachable), (0x01, Nop), (0x05, Else), (0x0b, End), (0x0f, Return)] -> pure s
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
            pure $ I32_const $ fromIntegral i32
          0x42 -> do
            i64 <- varint64
            pure $ I64_const $ fromIntegral i64
          0x10 -> do
            i <- varuint32
            pure $ Call i
          _ -> fail ("bad opcode " ++ show opcode)
      if
        | End <- s -> pure []
        | otherwise -> (s:) <$> codeBlock

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
    Right out -> execute [fun0] out "e"
  where
    fun0 [I32_const x, I32_const y] = putStrLn $ show (y, x)

data VM = VM
  { globs :: IntMap Op
  , stack :: [Op]
  , insts :: [[Op]]
  , mem :: IntMap Word8
  } deriving Show

putNum :: Integral a => Int -> Int32 -> a -> IntMap Word8 -> IntMap Word8
putNum w addr n mem = foldl' f mem [0..w-1] where
  f m k = IM.insert (fromIntegral addr + k) (getByte k) m
  getByte k = fromIntegral $ n `div` (256^k) `mod` 256

getNum :: Int -> Int32 -> IntMap Word8 -> Integer
getNum w addr m = sum
  [fromIntegral (m IM.! (fromIntegral addr + k)) * 256^k | k <- [0..w-1]]

execute :: Monad m => [[Op] -> m ()] -> Wasm -> [Char] -> m ()
execute fns Wasm {imports, exports, code, globals} s = let
  fCount = length fns
  run VM {insts} | null insts = pure ()
  run vm@VM {insts} | null $ head insts = case tail insts of
    ((Loop _ _:rest):t) -> run vm {insts = rest:t}
    _                   -> run vm {insts = tail insts}
  run vm@VM{globs, stack, insts, mem} = case head $ head insts of
    Call i -> if i < fCount then do
        let
          Import _ _ (params, _) = imports!!i
          k = length params
        fns!!i $ take k stack
        run vm { stack = drop k stack, insts = i1 }
      else do
        let Body _ os = code!!(i - fCount)
        run vm { insts = os:i1 }
    Set_global i -> run vm {globs = IM.insert i (head stack) globs, stack = tail stack, insts = i1}
    Get_global i -> run vm {stack = globs IM.! i:stack, insts = i1}
    c@(I32_const _) -> run vm {stack = c:stack, insts = i1}
    c@(I64_const _) -> run vm {stack = c:stack, insts = i1}
    I32_add -> binOp32 (+)
    I32_sub -> binOp32 (-)
    I32_mul -> binOp32 (*)
    I64_gt_s -> let
      (I64_const b:I64_const a:_) = stack
      c = I32_const $ fromIntegral $ fromEnum $ a > b
      in run vm {stack = c:drop 2 stack, insts = i1}
    I64_eq -> let
      (I64_const b:I64_const a:_) = stack
      c = I32_const $ fromIntegral $ fromEnum $ a == b
      in run vm {stack = c:drop 2 stack, insts = i1}
    I64_add -> binOp64 (+)
    I64_sub -> binOp64 (-)
    I64_mul -> binOp64 (*)
    I64_shr_u -> binOp64 $ \a b -> fromIntegral $
      shiftR (fromIntegral a :: Word64) (fromIntegral b)
    I32_wrap_i64 -> let
      I64_const a = head stack
      c = I32_const $ fromIntegral a
      in run vm {stack = c:tail stack, insts = i1}
    I32_load _ _ -> do
      let
        I32_const addr = head stack
        c = I32_const $ fromIntegral $ getNum 4 addr mem
      run vm {stack = c:tail stack, insts = i1}
    I32_store _ _ -> let (I32_const n:I32_const addr:_) = stack in
      run vm {stack = drop 2 stack, insts = i1, mem = putNum 4 addr n mem}
    I64_store _ _ -> do
      let
        I32_const addr = stack!!1
        I64_const n = head stack
      run vm {stack = drop 2 stack, insts = i1, mem = putNum 8 addr n mem}
    I64_load _ _ -> do
      let
        I32_const addr = head stack
        c = I64_const $ fromIntegral $ getNum 8 addr mem
      run vm {stack = c:tail stack, insts = i1}
    Block _ bl -> run vm {insts = bl:i1}
    Loop _ bl -> run vm {insts = bl:insts}
    Br k -> run vm {insts = drop (k + 1) insts}
    Br_table as d -> do
      let
        n = fromIntegral n' where I32_const n' = head stack
        k = if n < 0 || n >= length as then d else as!!n
      run vm {stack = tail stack, insts = drop (k + 1) insts}
    _ -> error $ "TODO: " ++ show (head $ head insts)
    where
      i1 = tail (head insts):tail insts
      binOp32 f = run vm {stack = c:drop 2 stack, insts = i1} where
        (I32_const b:I32_const a:_) = stack
        c = I32_const $ f a b
      binOp64 f = run vm {stack = c:drop 2 stack, insts = i1} where
        (I64_const b:I64_const a:_) = stack
        c = I64_const $ f a b
  Just fI = lookup s exports
  in if fI < fCount then void $ fns!!fI $ [] else do
    let Body _ os = code!!(fI - fCount)
    run $ VM (IM.fromList $ zip [0..] $ head . snd <$> globals) [] [os] IM.empty
