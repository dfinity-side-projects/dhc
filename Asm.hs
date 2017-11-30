-- Wasm for UpdatePop, NInd, 
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
module Asm (wasm) where
import Control.Arrow
import "mtl" Control.Monad.State
import qualified Data.Map as M
import Data.Char
import Data.Int
import Data.List
import Data.Maybe

import DHC

-- | G-Machine instructions.
data Ins = Copro Int Int | PushInt Int64 | Push Int | PushGlobal Int Int
  | MkAp | Slide Int | Split Int | Eval
  | UpdatePop Int
  | Casejump [(Maybe Int64, [Ins])] | Trap deriving Show

data WasmType = TypeI32 | TypeI64

data WasmOp = GetGlobal Int | SetGlobal Int
  | I64Store | I64Load | I64Add | I64Sub | I64Mul | I64Const Int64
  | I32Store | I32Load | I32Load8u | I32Load16u
  | I32ShrU | I32Mul | I32Add | I32Sub | I32Const Int | I32NE
  | I32WrapI64
  | I64Xor | I64Eqz | I64ShrU | I64DivS | I64RemS
  | I64Eq | I64Ne | I64LTS | I64GTS
  | If
  | Block | Loop | Br Int | BrTable [Int] | WasmCall Int | Unreachable | End
  deriving Show

nPages :: Int
nPages = 8

data Tag = TagAp | TagInd | TagGlobal | TagInt | TagSum deriving Enum

encWasmOp :: WasmOp -> [Int]
encWasmOp op = case op of
  GetGlobal n -> 0x23 : leb128 n
  SetGlobal n -> 0x24 : leb128 n
  If -> [0x4, 0x40]
  I32NE -> [0x47]
  I32Add -> [0x6a]
  I32Sub -> [0x6b]
  I32Mul -> [0x6c]
  I32ShrU -> [0x76]
  I64Add -> [0x7c]
  I64Sub -> [0x7d]
  I64Mul -> [0x7e]
  I64DivS -> [0x7f]
  I64RemS -> [0x81]
  I64ShrU -> [0x88]
  I64Const n -> 0x42 : sleb128 n
  I32Const n -> 0x41 : sleb128 n
  I32WrapI64 -> [0xa7]
  I64Xor -> [0x85]
  I64Eqz -> [0x50]
  I64Eq -> [0x51]
  I64Ne -> [0x52]
  I64LTS -> [0x53]
  I64GTS -> [0x55]
  WasmCall n -> 0x10 : leb128 n
  Unreachable -> [0x0]
  End -> [0xb]
  Block -> [2, 0x40]
  Loop -> [3, 0x40]
  Br n -> 0xc : leb128 n
  I64Load -> [0x29, 3, 0]
  I64Store -> [0x37, 3, 0]
  I32Load -> [0x28, 2, 0]
  I32Load8u -> [0x2d, 0, 0]
  I32Load16u -> [0x2f, 1, 0]
  I32Store -> [0x36, 2, 0]
  BrTable bs -> 0xe : leb128 (length bs - 1) ++ concatMap leb128 bs

wasm :: String -> Either String [Int]
wasm prog = do
  m <- compileMk1 prog
  let
    -- Primitive functions. Must be kept in sync with `funs` table below.
    prims =
      [ intAsm I64Add
      , intAsm I64Sub
      , intAsm I64Mul
      , intAsm I64DivS
      , intAsm I64RemS
      , cmpAsm I64Eq
      , cmpAsm I64LTS
      , cmpAsm I64GTS
      ]
    -- Function 0: import function which we send our outputs.
    -- Function 1: Eval.
    -- Afterwards, the primitive functions, then the functions in the program.
    fs = evalAsm (length prims + length m) : prims
      ++ ((++ [End]) . concatMap fromIns . snd <$> m)
    sect t xs = t : lenc (varlen xs ++ concat xs)
  pure $ concat
    [ [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]  -- Magic string, version.
    , sect 1 [encSig [TypeI32, TypeI32] [], encSig [] []]  -- Type section.
    -- Import section.
    -- [0, 0] = external_kind Function, index 0.
    , sect 2 [encStr "i" ++ encStr "f" ++ [0, 0]]
    , sect 3 $ replicate (length fs + 1) [1]  -- Function section.
    , sect 5 [[0, nPages]]  -- Memory section (0 = no-maximum).
    , sect 6  -- Global section (1 = mutable).
      [ [encType TypeI32, 1, 0x41] ++ leb128 (65536*nPages - 4) ++ [0xb]  -- SP
      , [encType TypeI32, 1, 0x41, 0, 0xb]  -- HP
      , [encType TypeI32, 1, 0x41, 0, 0xb]  -- BP
      ]
    -- Export section.
    -- [0, n] = external_kind Function, index n.
    , sect 7 [encStr "e" ++ [0, length fs + 1]]
    , sect 10 $ encProcedure <$> (fs ++  -- Code section.
      --[[ WasmCall $ 2 + length prims + (fromJust $ elemIndex "run" $ fst <$> m)
      [fromIns (PushGlobal 0 $ length prims + (fromJust $ elemIndex "run" $ fst <$> m)) ++
      [ WasmCall 1
      , GetGlobal sp
      , I32Const 4
      , I32Add
      , I32Load
      , SetGlobal bp
      , Block
      , Block
      , GetGlobal bp
      , I32Load
      , BrTable [2, 2, 2, 0, 1, 2]  -- Branch on Tag.
      , End  -- Int.
      , GetGlobal bp  -- High bits.
      , I32Const 8
      , I32Add
      , I64Load
      , I64Const 32
      , I64ShrU
      , I32WrapI64
      , GetGlobal bp  -- Low bits.
      , I32Const 8
      , I32Add
      , I64Load
      , I32WrapI64
      , WasmCall 0
      , Br 1
      , End  -- Sum (enum).
      , I32Const 0
      , GetGlobal bp
      , I32Const 4
      , I32Add
      , I32Load
      , WasmCall 0
      , End
      ]])
    ]
  where
  encStr s = lenc $ ord <$> s
  encProcedure = lenc . (0:) . concatMap encWasmOp
  encType TypeI32 = 0x7f
  encType TypeI64 = 0x7e
  -- | Encodes function signature.
  encSig ins outs = 0x60 : lenc (encType <$> ins) ++ lenc (encType <$> outs)
  intAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval] ++
    [ GetGlobal hp  -- [hp] = Int
    , I32Const $ fromEnum TagInt
    , I32Store
    -- [hp + 8] = [[sp + 4] + 8] `op` [[sp + 8] + 8]
    , GetGlobal hp  -- PUSH hp + 8
    , I32Const 8
    , I32Add
    , GetGlobal sp  -- PUSH [[sp + 4] + 8]
    , I32Const 4
    , I32Add
    , I32Load
    , I32Const 8
    , I32Add
    , I64Load
    , GetGlobal sp  -- PUSH [[sp + 8] + 8]
    , I32Const 8
    , I32Add
    , I32Load
    , I32Const 8
    , I32Add
    , I64Load
    , op
    , I64Store
    , GetGlobal sp  -- [sp + 8] = hp
    , I32Const 8
    , I32Add
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp + 4
    , I32Const 4
    , I32Add
    , SetGlobal sp
    , GetGlobal hp  -- hp = hp + 16
    , I32Const 16
    , I32Add
    , SetGlobal hp
    ] ++ fromIns (UpdatePop 2) ++ [WasmCall 1, End]

  cmpAsm op = concatMap fromIns [Push 1, Eval, Push 1, Eval ] ++
    [ GetGlobal hp  -- [hp] = Int
    , I32Const $ fromEnum TagSum
    , I32Store
    -- [hp + 4] = [[sp + 4] + 8] == [[sp + 8] + 8]
    , GetGlobal hp  -- PUSH hp + 4
    , I32Const 4
    , I32Add
    , GetGlobal sp  -- PUSH [[sp + 4] + 8]
    , I32Const 4
    , I32Add
    , I32Load
    , I32Const 8
    , I32Add
    , I64Load
    , GetGlobal sp  -- PUSH [[sp + 8] + 8]
    , I32Const 8
    , I32Add
    , I32Load
    , I32Const 8
    , I32Add
    , I64Load
    , op
    , I32Store
    , GetGlobal sp  -- [sp + 8] = hp
    , I32Const 8
    , I32Add
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp + 4
    , I32Const 4
    , I32Add
    , SetGlobal sp
    , GetGlobal hp  -- hp = hp + 8
    , I32Const 8
    , I32Add
    , SetGlobal hp
    ] ++ fromIns (UpdatePop 2) ++ [WasmCall 1, End]

  evalAsm n =
    [ Block
    , Loop
    , GetGlobal sp  -- bp = [sp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , SetGlobal bp
    , Block
    , Block
    , GetGlobal bp
    , I32Load8u
    , BrTable [0, 1, 3, 4]  -- case [bp].8u; branch on Tag
    , End  -- 0: Ap
    , GetGlobal sp  -- [sp] = [bp + 8]
    , GetGlobal bp
    , I32Const 8
    , I32Add
    , I32Load
    , I32Store
    , GetGlobal sp  -- sp = sp - 4
    , I32Const 4
    , I32Sub
    , SetGlobal sp
    , Br 1
    , End  -- 1: Ind.
    , GetGlobal sp  -- [sp + 4] = [bp + 4]
    , I32Const 4
    , I32Add
    , GetGlobal bp
    , I32Const 4
    , I32Add
    , I32Load
    , I32Store
    , Br 0
    , End  -- 2: Eval loop.
    , End  -- 3: Global

    , GetGlobal bp  -- save bp, sp
    , GetGlobal sp
    , GetGlobal sp  -- bp = sp + 4 + 4 * ([bp].16u >> 8)
    , I32Const 4
    , I32Add
    , GetGlobal bp
    , I32Load16u
    , I32Const 8
    , I32ShrU
    , I32Const 4
    , I32Mul
    , I32Add
    , SetGlobal bp

    , Loop
    , GetGlobal sp  -- sp = sp + 4
    , I32Const 4
    , I32Add
    , SetGlobal sp
    , GetGlobal sp  -- if sp /= bp then
    , GetGlobal bp
    , I32NE
    , If
    , GetGlobal sp  -- [sp] = [[sp + 4] + 12]
    , GetGlobal sp
    , I32Const 4
    , I32Add
    , I32Load
    , I32Const 12
    , I32Add
    , I32Load
    , I32Store
    , Br 1
    , End  -- If
    , End  -- Loop

    , SetGlobal sp
    , SetGlobal bp
    ] ++ replicate n Block ++
    [ GetGlobal bp  -- case [bp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , BrTable [0..n]
    ] ++ concat [[End, WasmCall $ 1 + i, Br (n - i)] | i <- [1..n]] ++
    [ End  -- 4: Other. It's already WHNF.
    ]

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
  Eval -> [ WasmCall 1 ]  -- (Tail call.)
  PushInt n ->
    [ GetGlobal sp  -- [sp] = hp
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp - 4
    , I32Const 4
    , I32Sub
    , SetGlobal sp
    , GetGlobal hp  -- [hp] = Int
    , I32Const $ fromEnum TagInt
    , I32Store
    , GetGlobal hp  -- [hp + 8] = n
    , I32Const 8
    , I32Add
    , I64Const n
    , I64Store
    , GetGlobal hp  -- hp = hp + 16
    , I32Const 16
    , I32Add
    , SetGlobal hp
    ]
  Push n ->
    [ GetGlobal sp  -- [sp] = [sp + 4(n + 1)]
    , GetGlobal sp
    , I32Const $ 4*(fromIntegral n + 1)
    , I32Add
    , I32Load
    , I32Store
    , GetGlobal sp  -- sp = sp - 4
    , I32Const 4
    , I32Sub
    , SetGlobal sp
    ]
  MkAp ->
    [ GetGlobal hp  -- [hp] = Ap
    , I32Const $ fromEnum TagAp
    , I32Store
    , GetGlobal hp  -- [hp + 8] = [sp + 4]
    , I32Const 8
    , I32Add
    , GetGlobal sp
    , I32Const 4
    , I32Add
    , I32Load
    , I32Store
    , GetGlobal hp  -- [hp + 12] = [sp + 8]
    , I32Const 12
    , I32Add
    , GetGlobal sp
    , I32Const 8
    , I32Add
    , I32Load
    , I32Store
    , GetGlobal sp  -- [sp + 8] = hp
    , I32Const 8
    , I32Add
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp + 4
    , I32Const 4
    , I32Add
    , SetGlobal sp
    , GetGlobal hp  -- hp = hp + 16
    , I32Const 16
    , I32Add
    , SetGlobal hp
    ]
  PushGlobal n g ->
    [ GetGlobal sp  -- [sp] = hp
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp - 4
    , I32Const 4
    , I32Sub
    , SetGlobal sp
    , GetGlobal hp  -- [hp] = Global | (n << 8)
    , I32Const $ fromEnum TagGlobal + 256*n
    , I32Store
    , GetGlobal hp  -- [hp + 4] = n
    , I32Const 4
    , I32Add
    , I32Const g
    , I32Store
    , GetGlobal hp  -- hp = hp + 8
    , I32Const 16
    , I32Add
    , SetGlobal hp
    ]
  Slide 0 -> []
  Slide n ->
    [ GetGlobal sp  -- [sp + 4*(n + 1)] = [sp + 4]
    , I32Const $ 4*(fromIntegral n + 1)
    , I32Add
    , GetGlobal sp
    , I32Const 4
    , I32Add
    , I32Load
    , I32Store
    , GetGlobal sp  -- sp = sp + 4*n
    , I32Const $ 4*fromIntegral n
    , I32Add
    , SetGlobal sp
    ]
  UpdatePop n ->
    [ GetGlobal sp  -- bp = [sp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , SetGlobal bp
    , GetGlobal sp  -- sp = sp + 4*(n + 1)
    , I32Const $ 4*(n + 1)
    , I32Add
    , SetGlobal sp
    , GetGlobal sp  -- [[sp + 4]] = Ind
    , I32Const 4
    , I32Add
    , I32Load
    , I32Const $ fromEnum TagInd
    , I32Store
    , GetGlobal sp  -- [[sp + 4] + 4] = bp
    , I32Const 4
    , I32Add
    , I32Load
    , I32Const 4
    , I32Add
    , GetGlobal bp
    , I32Store
    ]
  Copro m n ->
    [ GetGlobal hp  -- [hp] = Sum
    , I32Const $ fromEnum TagSum
    , I32Store
    , GetGlobal hp  -- [hp + 4] = m
    , I32Const 4
    , I32Add
    , I32Const m
    , I32Store
    ] ++ concat [
      [ GetGlobal hp  -- [hp + 4 + 4*i] = [sp + 4*i]
      , I32Const $ 4 + 4*i
      , I32Add
      , GetGlobal sp
      , I32Const $ 4*i
      , I32Add
      , I32Load
      , I32Store ] | i <- [1..n]] ++
    [ GetGlobal sp  -- sp = sp + 4*n
    , I32Const $ 4*n
    , I32Add
    , SetGlobal sp
    , GetGlobal sp  -- [sp] = hp
    , GetGlobal hp
    , I32Store
    , GetGlobal sp  -- sp = sp - 4
    , I32Const 4
    , I32Sub
    , SetGlobal sp
    , GetGlobal hp  -- hp = hp + 8 + ceil(n / 2) * 8
    , I32Const $ 8 + 8 * ((n + 1) `div` 2)
    , I32Add
    , SetGlobal hp
    ]
  Casejump alts0 -> let
    -- TODO: This compiles Int case statements incorrectly.
      (underscore, unsortedAlts) = partition (isNothing . fst) alts0
      alts = sortOn fst unsortedAlts
      catchall = if null underscore then [Trap] else snd $ head underscore
      tab = zip (fromJust . fst <$> alts) [0..]
      m = 1 + (maximum $ fromJust . fst <$> alts)
    -- [sp + 4] should be:
    -- 0: TagSum
    -- 4: "Enum"
    -- 8, 12, ...: fields
    in [ GetGlobal sp  -- bp = [sp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , SetGlobal bp

    , Block]
    ++ replicate (length alts + 1) Block ++
    [ GetGlobal bp  -- [bp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , BrTable [fromIntegral $ fromMaybe (length alts) $ lookup i tab | i <- [0..m]]]
    ++ concat (zipWith (++) [End : concatMap fromIns ins | (_, ins) <- alts]
      (pure . Br <$> reverse [1..length alts]))
      ++ (End : concatMap fromIns catchall ++ [End])
  Split 0 -> [GetGlobal sp, I32Const 4, I32Add, SetGlobal sp]
  Split n ->
    [ GetGlobal sp  -- bp = [sp + 4]
    , I32Const 4
    , I32Add
    , I32Load
    , SetGlobal bp
    , GetGlobal sp  -- sp = sp + 4
    , I32Const 4
    , I32Add
    , SetGlobal sp
    ] ++ concat [
      [ GetGlobal sp  -- [sp - 4*(n - i)] = [bp + 4 + 4*i]
      , I32Const $ 4*(n - i)
      , I32Sub
      , GetGlobal bp
      , I32Const $ 4 + 4*i
      , I32Add
      , I32Load
      , I32Store
      ] | i <- [1..n]] ++
    [ GetGlobal sp  -- sp = sp - 4*n
    , I32Const $ 4*n
    , I32Sub
    , SetGlobal sp
    ]

mk1 :: M.Map String (Int, Int) -> Ast -> State [(String, Int)] [Ins]
mk1 funs ast = case ast of
  Super as b -> do
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
      Nothing -> [uncurry PushGlobal $ funs M.! v]
  Pack n m -> pure [Copro n m]
  Cas expr alts -> do
    me <- rec expr
    xs <- forM alts $ \(p, body) -> do
      orig <- get
      (f, b) <- case fromApList p of
        [I n] -> do
          bump 1
          (,) (Just n) . (++ [Slide 1]) <$> rec body
        (Pack n _:vs) -> do
          bump $ length vs
          modify' $ \bs -> zip (map (\(Var v) -> v) vs) [0..] ++ bs
          bod <- rec body
          pure (Just $ fromIntegral n, Split (length vs) : bod ++ [Slide (length vs)])
        [Var s] -> do
          bump 1
          modify' $ \bs -> (s, 0):bs
          (,) Nothing . (++ [Slide 1]) <$> rec body
        _ -> undefined
      put orig
      pure (f, b)
    pure $ me ++ [Eval, Casejump xs]
  _ -> error $ "TODO: compile: " ++ show ast
  where
    rec = mk1 funs
    bump n = modify' $ map $ second (+n)

fromApList :: Ast -> [Ast]
fromApList (a :@ b) = fromApList a ++ [b]
fromApList a = [a]

data Node = NInt Int64 | NAp Int Int | NGlobal Int Int | NInd Int | NCon Int [Int] deriving Show

primFuns :: [(String, (Int, Int))]
primFuns = zip ["+", "-", "*", "div", "mod", "Int-==", "<", ">"]
  $ (,) 2 <$> [0..]

compileMk1 :: String -> Either String [(String, [Ins])]
compileMk1 haskell = do
  ds <- compileMinimal haskell
  let funs = M.fromList $ primFuns ++ zipWith (\(name, (Super as _, _)) i -> (name, (length as, i))) ds [length primFuns..]
  pure $ map (\(s, (d, _)) -> (s, evalState (mk1 funs d) [])) ds

-- | Test that interprets G-Machine instructions.
testmk1 :: IO ()
testmk1 = go (Right <$> [PushGlobal 0 runIndex, Eval]) [] M.empty where
  drop' n as | n > length as = error "BUG!"
             | otherwise     = drop n as
  Right m = compileMk1 "g n = (case n of 0 -> 1; n -> n * g(n - 1)); f x = x * x; run = f (f 3); run1 = case Just 3 of Just n -> n + 1"
  runIndex = fromJust (elemIndex "run" $ fst <$> m) + length primFuns
  go (fOrIns:rest) s h = either primFun exec fOrIns where
    k = M.size h
    heapAdd x = M.insert k x h
    intInt f = go rest (k:srest) $ heapAdd $ NInt $ f x y where
      (s0:s1:srest) = s
      NInt x = h M.! s0
      NInt y = h M.! s1
    primFun 0 = intInt (+)
    primFun 1 = intInt (-)
    primFun 2 = intInt (*)
    primFun _ = error "unsupported"
    exec ins = case ins of
      Trap -> print "UNREACHABLE"
      PushInt n -> go rest (k:s) $ heapAdd $ NInt n
      Push n -> go rest (s!!n:s) h
      PushGlobal a b -> go rest (k:s) $ heapAdd $ NGlobal a b
      MkAp -> let (s0:s1:srest) = s in go rest (k:srest) $ heapAdd $ NAp s0 s1
      UpdatePop n -> go rest (drop' (n + 1) s) $ M.insert (s!!(n + 1)) (NInd $ head s) h
      Slide n -> let (s0:srest) = s in go rest (s0:drop' n srest) h
      Copro n l -> go rest (k:drop' l s) $ heapAdd $ NCon n $ take l s
      Split _ -> let
        (s0:srest) = s
        NCon _ as = h M.! s0
        in go rest (as ++ srest) h
      Eval -> case h M.! head s of
        NInd i -> go (Right Eval:rest) (i:tail s) h
        NAp a _ -> go (Right Eval:rest) (a:s) h
        NGlobal n g -> let
          p = if g >= 8 then Right <$> snd (m!!(g - 8)) else
            (Right <$> [Push 1, Eval, Push 1, Eval]) ++
            [Left g, Right $ UpdatePop 2, Right Eval]
          debone i = r where NAp _ r = h M.! i
          in go (p ++ rest) ((debone <$> take n (tail s)) ++ drop' n s) h
        _ -> go rest s h
      Casejump alts -> let
        x = case h M.! head s of
          NInt n -> n
          NCon n _ -> fromIntegral n
          _ -> undefined
        body = case lookup (Just x) alts of
          Just b -> b
          _ -> fromJust $ lookup Nothing alts
        in go ((Right <$> body) ++ rest) s h
  go [] [r] h = case h M.! r of
    NInt n -> print n
    NCon n _ -> print ("PACK", n)
    _ -> error "expect NInt or NCon on stack"
  go [] s _ = error $ "bad stack: " ++ show s
