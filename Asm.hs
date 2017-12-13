{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Asm (wasm, typedAstToBin, compileMk1, Ins(..), primCount) where
import Control.Arrow
import "mtl" Control.Monad.State
import qualified Data.Map as M
import Data.Char
import Data.Int
import Data.List
import Data.Maybe

import DHC hiding (Call, Type)
import WasmOp

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal Int Int
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePop Int | UpdateInd Int | Alloc Int
  | Casejump [(Maybe Int, [Ins])] | Trap deriving Show

nPages :: Int
nPages = 8

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagSum deriving Enum

type WasmOp = Op

encWasmOp :: WasmOp -> [Int]
encWasmOp op = case op of
  Get_global n -> 0x23 : leb128 n
  Set_global n -> 0x24 : leb128 n
  I64_const n -> 0x42 : sleb128 n
  I32_const n -> 0x41 : sleb128 n
  Call n -> 0x10 : leb128 n
  I64_load m n -> [0x29, m, n]
  I64_store m n -> [0x37, m, n]
  I32_load m n -> [0x28, m, n]
  I32_load8_u m n -> [0x2d, m, n]
  I32_load16_u m n -> [0x2f, m, n]
  I32_store m n -> [0x36, m, n]
  Br n -> 0xc : leb128 n
  Br_table bs a -> 0xe : leb128 (length bs) ++ concatMap leb128 (bs ++ [a])
  If _ as -> [0x4, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  Block _ as -> [2, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  Loop _ as -> [3, 0x40] ++ concatMap encWasmOp as ++ [0xb]
  _ -> maybe (error $ "unsupported: " ++ show op) pure $ lookup op rZeroOps

intAsm :: WasmOp -> [WasmOp]
intAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
  [ Get_global hp  -- [hp] = Int
  , I32_const $ fromIntegral $ fromEnum TagInt
  , I32_store 2 0
  -- [hp + 8] = [[sp + 4] + 8] `op` [[sp + 8] + 8]
  , Get_global hp  -- PUSH hp + 8
  , I32_const 8
  , I32_add
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , Get_global sp  -- PUSH [[sp + 8] + 8]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , op
  , I64_store 3 0
  , Get_global sp  -- [sp + 8] = hp
  , I32_const 8
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 16
  , I32_const 16
  , I32_add
  , Set_global hp
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

cmpAsm :: WasmOp -> [WasmOp]
cmpAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval ] ++
  [ Get_global hp  -- [hp] = Int
  , I32_const $ fromIntegral $ fromEnum TagSum
  , I32_store 2 0
  -- [hp + 4] = [[sp + 4] + 8] == [[sp + 8] + 8]
  , Get_global hp  -- PUSH hp + 4
  , I32_const 4
  , I32_add
  , Get_global sp  -- PUSH [[sp + 4] + 8]
  , I32_const 4
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , Get_global sp  -- PUSH [[sp + 8] + 8]
  , I32_const 8
  , I32_add
  , I32_load 2 0
  , I32_const 8
  , I32_add
  , I64_load 3 0
  , op
  , I32_store 2 0
  , Get_global sp  -- [sp + 8] = hp
  , I32_const 8
  , I32_add
  , Get_global hp
  , I32_store 2 0
  , Get_global sp  -- sp = sp + 4
  , I32_const 4
  , I32_add
  , Set_global sp
  , Get_global hp  -- hp = hp + 8
  , I32_const 8
  , I32_add
  , Set_global hp
  ] ++ fromIns (UpdatePop 2) ++ [Call 1, End]

-- Primitive functions.
data Prim = Prim
  { primName :: String
  , arity :: Int
  , primAsm :: [WasmOp]
  }

prims :: [Prim]
prims = mkPrim <$>
  [ ("+", intAsm I64_add)
  , ("-", intAsm I64_sub)
  , ("*", intAsm I64_mul)
  , ("div", intAsm I64_div_s)
  , ("mod", intAsm I64_rem_s)
  , ("Int-==", cmpAsm I64_eq)
  , ("<", cmpAsm I64_lt_s)
  , (">", cmpAsm I64_gt_s)
  ]
  where mkPrim (s, as) = Prim { primName = s, arity = 2, primAsm = as }

primCount :: Int
primCount = length prims

wasm :: String -> Either String [Int]
wasm prog = insToBin <$> compileMk1 prog

compileMk1 :: String -> Either String [(String, [Ins])]
compileMk1 haskell = astToIns <$> compileMinimal haskell

astToIns :: [(String, Ast)] -> [(String, [Ins])]
astToIns ds = map (\(s, d) -> (s, evalState (mk1 funs d) [])) ds where
  ps = zipWith (\p i -> (primName p, (arity p, i))) prims [0..]
  funs = M.fromList $ ps ++ zipWith (\(name, Lam as _) i -> (name, (length as, i))) ds [primCount..]

typedAstToBin :: [(String, (Ast, Type))] -> [Int]
typedAstToBin = insToBin . astToIns . liftLambdas . (second fst <$>)

tag_const :: Tag -> Op
tag_const = I32_const . fromIntegral . fromEnum

insToBin :: [(String, [Ins])] -> [Int]
insToBin m = concat
  [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.
  , sect 1 [encSig [I32, I32] [], encSig [] []]  -- Type section.
  -- Import section.
  -- [0, 0] = external_kind Function, index 0.
  , sect 2 [encStr "i" ++ encStr "f" ++ [0, 0]]
  , sect 3 $ replicate (length fs + 1) [1]  -- Function section.
  , sect 5 [[0, nPages]]  -- Memory section (0 = no-maximum).
  , sect 6  -- Global section (1 = mutable).
    [ [encType I32, 1, 0x41] ++ leb128 (65536*nPages - 4) ++ [0xb]  -- SP
    , [encType I32, 1, 0x41, 0, 0xb]  -- HP
    , [encType I32, 1, 0x41, 0, 0xb]  -- BP
    ]
  -- Export section.
  -- [0, n] = external_kind Function, index n.
  , sect 7 [encStr "e" ++ [0, length fs + 1]]
  , sect 10 $ encProcedure <$> (fs ++  -- Code section.
    [fromIns (PushGlobal 0 $ primCount + (fromJust $ elemIndex "run" $ fst <$> m)) ++
    [ Call 1
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Block Nada
      [ Block Nada
        [ Get_global bp
        , I32_load 2 0
        , Br_table [2, 2, 2, 0, 1] 2  -- Branch on Tag.
        ]  -- Int.
      , Get_global bp  -- High bits.
      , I32_const 8
      , I32_add
      , I64_load 3 0
      , I64_const 32
      , I64_shr_u
      , I32_wrap_i64
      , Get_global bp  -- Low bits.
      , I32_const 8
      , I32_add
      , I64_load 3 0
      , I32_wrap_i64
      , Call 0
      , Br 1
      ]  -- Sum (enum).
    , I32_const 0
    , Get_global bp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Call 0
    , End
    ]])
  ] where
  -- Function 0: import function which we send our outputs.
  -- Function 1: Eval.
  -- Afterwards, the primitive functions, then the functions in the program.
  fs = evalAsm (primCount + length m) : (primAsm <$> prims)
    ++ ((++ [End]) . concatMap fromIns . snd <$> m)
  sect t xs = t : lenc (varlen xs ++ concat xs)
  encStr s = lenc $ ord <$> s
  encProcedure = lenc . (0:) . concatMap encWasmOp
  encType I32 = 0x7f
  encType I64 = 0x7e
  -- | Encodes function signature.
  encSig ins outs = 0x60 : lenc (encType <$> ins) ++ lenc (encType <$> outs)
  evalAsm n =
    [ Block Nada
      [ Loop Nada
        [ Get_global sp  -- bp = [sp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Set_global bp
        , Block Nada
          [ Block Nada
            [ Get_global bp
            , I32_load8_u 0 0
            , Br_table [0, 1, 3] 4  -- case [bp].8u; branch on Tag
            ]  -- 0: Ap
          , Get_global sp  -- [sp] = [bp + 8]
          , Get_global bp
          , I32_const 8
          , I32_add
          , I32_load 2 0
          , I32_store 2 0
          , Get_global sp  -- sp = sp - 4
          , I32_const 4
          , I32_sub
          , Set_global sp
          , Br 1
          ]  -- 1: Ind.
        , Get_global sp  -- [sp + 4] = [bp + 4]
        , I32_const 4
        , I32_add
        , Get_global bp
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_store 2 0
        , Br 0
        ]  -- 2: Eval loop.
      ]  -- 3: Global
    , Get_global bp  -- save bp, sp
    , Get_global sp
    , Get_global sp  -- bp = sp + 4 + 4 * ([bp].16u >> 8)
    , I32_const 4
    , I32_add
    , Get_global bp
    , I32_load16_u 1 0
    , I32_const 8
    , I32_shr_u
    , I32_const 4
    , I32_mul
    , I32_add
    , Set_global bp

    , Loop Nada
      [ Get_global sp  -- sp = sp + 4
      , I32_const 4
      , I32_add
      , Set_global sp
      , Get_global sp  -- if sp /= bp then
      , Get_global bp
      , I32_ne
      , If Nada
        [ Get_global sp  -- [sp] = [[sp + 4] + 12]
        , Get_global sp
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , I32_const 12
        , I32_add
        , I32_load 2 0
        , I32_store 2 0
        , Br 1
        ]  -- If
      ]  -- Loop
    , Set_global sp
    , Set_global bp
    ] ++ nest n ++ [End]
    where
      nest 0 =
        [ Get_global bp  -- case [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [0..n-1] n
        ]
      nest k = [Block Nada $ nest $ k - 1, Call $ 1 + k, Br $ n - k]

leb128 :: Int -> [Int]
leb128 n | n < 64    = [n]
         | n < 128   = [128 + n, 0]
         | otherwise = 128 + (n `mod` 128) : leb128 (n `div` 128)

-- TODO: FIX!
sleb128 :: Integral a => a -> [Int]
sleb128 n | n < 64    = [fromIntegral n]
          | n < 128   = [128 + fromIntegral n, 0]
          | otherwise = 128 + (fromIntegral n `mod` 128) : sleb128 (n `div` 128)

varlen :: [a] -> [Int]
varlen xs = leb128 $ length xs

lenc :: [Int] -> [Int]
lenc xs = varlen xs ++ xs

sp :: Int
sp = 0
hp :: Int
hp = 1
bp :: Int
bp = 2

fromIns :: Ins -> [WasmOp]
fromIns instruction = case instruction of
  Trap -> [ Unreachable ]
  Eval -> [ Call 1 ]  -- (Tail call.)
  PushInt n ->
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = Int
    , tag_const TagInt
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = n
    , I32_const 8
    , I32_add
    , I64_const n
    , I64_store 3 0
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  Push n ->
    [ Get_global sp  -- [sp] = [sp + 4(n + 1)]
    , Get_global sp
    , I32_const $ 4*(fromIntegral n + 1)
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    ]
  MkAp ->
    [ Get_global hp  -- [hp] = Ap
    , tag_const TagAp
    , I32_store 2 0
    , Get_global hp  -- [hp + 8] = [sp + 4]
    , I32_const 8
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global hp  -- [hp + 12] = [sp + 8]
    , I32_const 12
    , I32_add
    , Get_global sp
    , I32_const 8
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- [sp + 8] = hp
    , I32_const 8
    , I32_add
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global hp  -- hp = hp + 16
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  PushGlobal n g ->
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- [hp] = Global | (n << 8)
    , I32_const $ fromIntegral $ fromEnum TagGlobal + 256*n
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = n
    , I32_const 4
    , I32_add
    , I32_const $ fromIntegral g
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 16
    , I32_add
    , Set_global hp
    ]
  Slide 0 -> []
  Slide n ->
    [ Get_global sp  -- [sp + 4*(n + 1)] = [sp + 4]
    , I32_const $ 4*(fromIntegral n + 1)
    , I32_add
    , Get_global sp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_store 2 0
    , Get_global sp  -- sp = sp + 4*n
    , I32_const $ 4*fromIntegral n
    , I32_add
    , Set_global sp
    ]
  Alloc n -> concat (replicate n
    [ Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global hp  -- [hp] = Ind
    , tag_const TagInd
    , I32_store 2 0
    , Get_global hp  -- hp = hp + 8
    , I32_const 8
    , I32_add
    , Set_global hp
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    ])
  UpdateInd n ->
    [ Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    , Get_global sp  -- [[sp + 4*(n + 1)] + 4] = [sp]
    , I32_const $ fromIntegral $ 4*(n + 1)
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , Get_global sp
    , I32_load 2 0
    , I32_store 2 0
    ]
  UpdatePop n ->
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Get_global sp  -- sp = sp + 4*(n + 1)
    , I32_const $ fromIntegral $ 4*(n + 1)
    , I32_add
    , Set_global sp
    , Get_global sp  -- [[sp + 4]] = Ind
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , tag_const TagInd
    , I32_store 2 0
    , Get_global sp  -- [[sp + 4] + 4] = bp
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , I32_const 4
    , I32_add
    , Get_global bp
    , I32_store 2 0
    ]
  Copro m n ->
    [ Get_global hp  -- [hp] = Sum
    , tag_const TagSum
    , I32_store 2 0
    , Get_global hp  -- [hp + 4] = m
    , I32_const 4
    , I32_add
    , I32_const $ fromIntegral m
    , I32_store 2 0
    ] ++ concat [
      [ Get_global hp  -- [hp + 4 + 4*i] = [sp + 4*i]
      , I32_const $ fromIntegral $ 4 + 4*i
      , I32_add
      , Get_global sp
      , I32_const $ fromIntegral $ 4*i
      , I32_add
      , I32_load 2 0
      , I32_store 2 0 ] | i <- [1..n]] ++
    [ Get_global sp  -- sp = sp + 4*n
    , I32_const $ fromIntegral $ 4*n
    , I32_add
    , Set_global sp
    , Get_global sp  -- [sp] = hp
    , Get_global hp
    , I32_store 2 0
    , Get_global sp  -- sp = sp - 4
    , I32_const 4
    , I32_sub
    , Set_global sp
    , Get_global hp  -- hp = hp + 8 + ceil(n / 2) * 8
    , I32_const $ fromIntegral $ 8 + 8 * ((n + 1) `div` 2)
    , I32_add
    , Set_global hp
    ]
  Casejump alts0 -> let
    -- TODO: This compiles Int case statements incorrectly.
      (underscore, unsortedAlts) = partition (isNothing . fst) alts0
      alts = sortOn fst unsortedAlts
      catchall = if null underscore then [Trap] else snd $ head underscore
      tab = zip (fromJust . fst <$> alts) [0..]
      m = maximum $ fromJust . fst <$> alts
      nest j (ins:rest) = pure $ Block Nada $ nest (j + 1) rest ++ concatMap fromIns ins ++ [Br j]
      nest _ [] = pure $ Block Nada
        [ Get_global bp  -- [bp + 4]
        , I32_const 4
        , I32_add
        , I32_load 2 0
        , Br_table [fromIntegral $ fromMaybe (length alts) $ lookup i tab | i <- [0..m]] $ m + 1
        ]
    in if null alts then concatMap fromIns catchall else
    -- [sp + 4] should be:
    -- 0: TagSum
    -- 4: "Enum"
    -- 8, 12, ...: fields
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Block Nada $ nest 1 (reverse $ snd <$> alts) ++ concatMap fromIns catchall
    ]

  Split 0 -> [Get_global sp, I32_const 4, I32_add, Set_global sp]
  Split n ->
    [ Get_global sp  -- bp = [sp + 4]
    , I32_const 4
    , I32_add
    , I32_load 2 0
    , Set_global bp
    , Get_global sp  -- sp = sp + 4
    , I32_const 4
    , I32_add
    , Set_global sp
    ] ++ concat [
      [ Get_global sp  -- [sp - 4*(n - i)] = [bp + 4 + 4*i]
      , I32_const $ fromIntegral $ 4*(n - i)
      , I32_sub
      , Get_global bp
      , I32_const $ fromIntegral $ 4 + 4*i
      , I32_add
      , I32_load 2 0
      , I32_store 2 0
      ] | i <- [1..n]] ++
    [ Get_global sp  -- sp = sp - 4*n
    , I32_const $ fromIntegral $ 4*n
    , I32_sub
    , Set_global sp
    ]

mk1 :: M.Map String (Int, Int) -> Ast -> State [(String, Int)] [Ins]
mk1 funs ast = case ast of
  Lam as b -> do
    modify' $ \bs -> zip as [length bs..] ++ bs
    (++ [UpdatePop $ length as, Eval]) <$> rec b
  I n -> pure [PushInt n]
  t :@ u -> do
    mu <- rec u
    bump 1
    mt <- rec t
    bump (-1)
    pure $ case last mt of
      Copro _ _ -> mu ++ mt
      _ -> concat [mu, mt, [MkAp]]
  Var v -> do
    m <- get
    pure $ case lookup v m of
      Just k -> [Push k]
      Nothing -> case M.lookup v funs of
        Nothing -> error $ "no such global: " ++ v
        Just (i, j) -> [PushGlobal i j]
  Pack n m -> pure [Copro n m]
  Cas expr alts -> do
    me <- rec expr
    xs <- forM alts $ \(p, body) -> do
      orig <- get  -- Save state.
      (f, b) <- case fromApList p of
        [I n] -> do  -- TODO: Rewrite as equality check.
          bump 1
          (,) (Just $ fromIntegral n) . (++ [Slide 1]) <$> rec body
        (Pack n _:vs) -> do
          bump $ length vs
          modify' (zip (map (\(Var v) -> v) vs) [0..] ++)
          bod <- rec body
          pure (Just $ fromIntegral n, Split (length vs) : bod ++ [Slide (length vs)])
        [Var s] -> do
          bump 1
          modify' $ \bs -> (s, 0):bs
          (,) Nothing . (++ [Slide 1]) <$> rec body
        _ -> undefined
      put orig  -- Restore state.
      pure (f, b)
    pure $ me ++ [Eval, Casejump xs]
  Let ds body -> let n = length ds in do
    orig <- get  -- Save state.
    bump n
    modify' (zip (fst <$> ds) [n-1,n-2..0] ++)
    dsAsm <- mapM rec $ snd <$> ds
    b <- rec body
    put orig  -- Restore state.
    pure $ Alloc n : concat (zipWith (++) dsAsm (pure . UpdateInd <$> [n-1,n-2..0])) ++ b ++ [Slide n]
  _ -> error $ "TODO: compile: " ++ show ast
  where
    rec = mk1 funs
    bump n = modify' $ map $ second (+n)

fromApList :: Ast -> [Ast]
fromApList (a :@ b) = fromApList a ++ [b]
fromApList a = [a]
