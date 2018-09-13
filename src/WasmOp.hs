{-# LANGUAGE CPP #-}
#ifdef __HASTE__
{-# LANGUAGE PackageImports #-}
#endif
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
module WasmOp
  ( WasmType(..), CustomWasmOp(..), WasmOp, zeroOperandOps, rZeroOps
  , followCalls, renumberCalls, WasmFun(..)
  ) where
#ifdef __HASTE__
import "mtl" Control.Monad.State
import qualified Data.Set as IS
import qualified Data.Map.Strict as IM
#else
import Control.Monad.State
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
#endif
import Data.Binary (Binary)
import Data.Int
import Data.Void
import GHC.Generics (Generic)

#ifdef __HASTE__
type IntMap = IM.Map Int
type IntSet = IS.Set Int
#endif

data WasmType = I32 | I64 | F32 | F64 | Func | AnyFunc | Nada
  | Ref String  -- Custom types used by Dfinity.
  deriving (Read, Show, Eq, Ord, Generic)
instance Binary WasmType

data WasmFun = WasmFun
  { typeSig :: ([WasmType], [WasmType])
  , localVars :: [WasmType]
  , funBody :: [WasmOp]
  } deriving Show

-- Much of this file was generated from:
--   http://webassembly.org/docs/binary-encoding/

data CustomWasmOp a = Custom a
  | I32_eqz | I32_eq | I32_ne | I32_lt_s | I32_lt_u | I32_gt_s | I32_gt_u | I32_le_s | I32_le_u | I32_ge_s | I32_ge_u | I64_eqz | I64_eq | I64_ne | I64_lt_s | I64_lt_u | I64_gt_s | I64_gt_u | I64_le_s | I64_le_u | I64_ge_s | I64_ge_u | F32_eq | F32_ne | F32_lt | F32_gt | F32_le | F32_ge | F64_eq | F64_ne | F64_lt | F64_gt | F64_le | F64_ge | I32_clz | I32_ctz | I32_popcnt | I32_add | I32_sub | I32_mul | I32_div_s | I32_div_u | I32_rem_s | I32_rem_u | I32_and | I32_or | I32_xor | I32_shl | I32_shr_s | I32_shr_u | I32_rotl | I32_rotr | I64_clz | I64_ctz | I64_popcnt | I64_add | I64_sub | I64_mul | I64_div_s | I64_div_u | I64_rem_s | I64_rem_u | I64_and | I64_or | I64_xor | I64_shl | I64_shr_s | I64_shr_u | I64_rotl | I64_rotr | F32_abs | F32_neg | F32_ceil | F32_floor | F32_trunc | F32_nearest | F32_sqrt | F32_add | F32_sub | F32_mul | F32_div | F32_min | F32_max | F32_copysign | F64_abs | F64_neg | F64_ceil | F64_floor | F64_trunc | F64_nearest | F64_sqrt | F64_add | F64_sub | F64_mul | F64_div | F64_min | F64_max | F64_copysign | I32_wrap_i64 | I32_trunc_s_f32 | I32_trunc_u_f32 | I32_trunc_s_f64 | I32_trunc_u_f64 | I64_extend_s_i32 | I64_extend_u_i32 | I64_trunc_s_f32 | I64_trunc_u_f32 | I64_trunc_s_f64 | I64_trunc_u_f64 | F32_convert_s_i32 | F32_convert_u_i32 | F32_convert_s_i64 | F32_convert_u_i64 | F32_demote_f64 | F64_convert_s_i32 | F64_convert_u_i32 | F64_convert_s_i64 | F64_convert_u_i64 | F64_promote_f32 | I32_reinterpret_f32 | I64_reinterpret_f64 | F32_reinterpret_i32 | F64_reinterpret_i64
  | I32_load Int Int | I64_load Int Int | F32_load Int Int | F64_load Int Int | I32_load8_s Int Int | I32_load8_u Int Int | I32_load16_s Int Int | I32_load16_u Int Int | I64_load8_s Int Int | I64_load8_u Int Int | I64_load16_s Int Int | I64_load16_u Int Int | I64_load32_s Int Int | I64_load32_u Int Int | I32_store Int Int | I64_store Int Int | F32_store Int Int | F64_store Int Int | I32_store8 Int Int | I32_store16 Int Int | I64_store8 Int Int | I64_store16 Int Int | I64_store32 Int Int
  | Unreachable | Nop | Else | End | Return
  | Block WasmType [CustomWasmOp a] | Loop WasmType [CustomWasmOp a] | If WasmType [CustomWasmOp a] [CustomWasmOp a]
  | Get_local Int | Set_local Int | Tee_local Int | Get_global Int | Set_global Int
  | I32_const Int32 | I64_const Int64 | F32_const Float | F64_const Double
  | Br_table [Int] Int
  | Br Int | Br_if Int
  | Call Int
  | Call_indirect ([WasmType], [WasmType])
  | Drop | Select
  deriving (Show, Eq, Functor)

type WasmOp = CustomWasmOp Void

zeroOperandOps :: [(Int, WasmOp)]
zeroOperandOps = cmpOps ++ ariOps ++ crops ++ others ++ parametrics where
  cmpOps = [(0x45, I32_eqz), (0x46, I32_eq), (0x47, I32_ne), (0x48, I32_lt_s), (0x49, I32_lt_u), (0x4a, I32_gt_s), (0x4b, I32_gt_u), (0x4c, I32_le_s), (0x4d, I32_le_u), (0x4e, I32_ge_s), (0x4f, I32_ge_u), (0x50, I64_eqz), (0x51, I64_eq), (0x52, I64_ne), (0x53, I64_lt_s), (0x54, I64_lt_u), (0x55, I64_gt_s), (0x56, I64_gt_u), (0x57, I64_le_s), (0x58, I64_le_u), (0x59, I64_ge_s), (0x5a, I64_ge_u), (0x5b, F32_eq), (0x5c, F32_ne), (0x5d, F32_lt), (0x5e, F32_gt), (0x5f, F32_le), (0x60, F32_ge), (0x61, F64_eq), (0x62, F64_ne), (0x63, F64_lt), (0x64, F64_gt), (0x65, F64_le), (0x66, F64_ge)]
  ariOps = [(0x67, I32_clz), (0x68, I32_ctz), (0x69, I32_popcnt), (0x6a, I32_add), (0x6b, I32_sub), (0x6c, I32_mul), (0x6d, I32_div_s), (0x6e, I32_div_u), (0x6f, I32_rem_s), (0x70, I32_rem_u), (0x71, I32_and), (0x72, I32_or), (0x73, I32_xor), (0x74, I32_shl), (0x75, I32_shr_s), (0x76, I32_shr_u), (0x77, I32_rotl), (0x78, I32_rotr), (0x79, I64_clz), (0x7a, I64_ctz), (0x7b, I64_popcnt), (0x7c, I64_add), (0x7d, I64_sub), (0x7e, I64_mul), (0x7f, I64_div_s), (0x80, I64_div_u), (0x81, I64_rem_s), (0x82, I64_rem_u), (0x83, I64_and), (0x84, I64_or), (0x85, I64_xor), (0x86, I64_shl), (0x87, I64_shr_s), (0x88, I64_shr_u), (0x89, I64_rotl), (0x8a, I64_rotr), (0x8b, F32_abs), (0x8c, F32_neg), (0x8d, F32_ceil), (0x8e, F32_floor), (0x8f, F32_trunc), (0x90, F32_nearest), (0x91, F32_sqrt), (0x92, F32_add), (0x93, F32_sub), (0x94, F32_mul), (0x95, F32_div), (0x96, F32_min), (0x97, F32_max), (0x98, F32_copysign), (0x99, F64_abs), (0x9a, F64_neg), (0x9b, F64_ceil), (0x9c, F64_floor), (0x9d, F64_trunc), (0x9e, F64_nearest), (0x9f, F64_sqrt), (0xa0, F64_add), (0xa1, F64_sub), (0xa2, F64_mul), (0xa3, F64_div), (0xa4, F64_min), (0xa5, F64_max), (0xa6, F64_copysign)]
  crops = [(0xa7, I32_wrap_i64), (0xa8, I32_trunc_s_f32), (0xa9, I32_trunc_u_f32), (0xaa, I32_trunc_s_f64), (0xab, I32_trunc_u_f64), (0xac, I64_extend_s_i32), (0xad, I64_extend_u_i32), (0xae, I64_trunc_s_f32), (0xaf, I64_trunc_u_f32), (0xb0, I64_trunc_s_f64), (0xb1, I64_trunc_u_f64), (0xb2, F32_convert_s_i32), (0xb3, F32_convert_u_i32), (0xb4, F32_convert_s_i64), (0xb5, F32_convert_u_i64), (0xb6, F32_demote_f64), (0xb7, F64_convert_s_i32), (0xb8, F64_convert_u_i32), (0xb9, F64_convert_s_i64), (0xba, F64_convert_u_i64), (0xbb, F64_promote_f32), (0xbc, I32_reinterpret_f32), (0xbd, I64_reinterpret_f64), (0xbe, F32_reinterpret_i32), (0xbf, F64_reinterpret_i64)]
  others = [(0x00, Unreachable), (0x01, Nop), (0x0b, End), (0x0f, Return)]
  parametrics = [(0x1a, Drop), (0x1b, Select)]

rZeroOps :: [(WasmOp, Int)]
rZeroOps = (\(a, b) -> (b, a)) <$> zeroOperandOps

followCalls :: [Int] -> IntMap [WasmOp] -> IntSet
followCalls ns m = execState (go ns) $ IS.fromList ns where
  go :: [Int] -> State IntSet ()
  go (n:rest) = do
    maybe (pure ()) tr $ IM.lookup n m
    go rest
  go [] = pure ()
  tr (w:rest) = do
    case w of
      Call i -> do
        s <- get
        when (IS.notMember i s) $ do
          put $ IS.insert i s
          go [i]
      Loop _ b -> tr b
      Block _ b -> tr b
      If _ t f -> do
        tr t
        tr f
      _ -> pure ()
    tr rest
  tr [] = pure ()

renumberCalls :: IntMap Int -> [WasmOp] -> [WasmOp]
renumberCalls m ws = case ws of
  [] -> []
  (w:rest) -> ren w:rec rest
  where
  rec = renumberCalls m
  ren w = case w of
    Call i -> Call $ m IM.! i
    Loop t b -> Loop t $ rec b
    Block t b -> Block t $ rec b
    If t a b -> If t (rec a) (rec b)
    x -> x
