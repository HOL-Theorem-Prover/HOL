(* ------------------------------------------------------------------------- *)
(* A real simpset (includes Peano arithmetic and pairs).                     *)
(* ------------------------------------------------------------------------- *)

structure realSimps :> realSimps = 
struct

open Drule realTheory;

val arith_ss = 
  simpLib.++
    (simpLib.++(boolSimps.bool_ss, pairSimps.PAIR_ss),numSimps.ARITH_ss);

val real_SS = simpLib.SIMPSET
  {ac = [],
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = [REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LID, REAL_MUL_RID, 
            REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NEGNEG, REAL_LE_NEG2,
            REAL_LE_REFL, REAL_SUB_REFL, REAL_SUB_RZERO, REAL_LE_01,
            REAL_SUB_ADD2, REAL_MUL_SUB2_CANCEL, REAL_NEG_HALF,
            REAL_LE_SUB_CANCEL2, REAL_LT_HALF1, REAL_HALF_BETWEEN, REAL_LT_01,
            REAL_MUL_SUB1_CANCEL, REAL_NEG_THIRD, REAL_DIV_DENOM_CANCEL2,
            REAL_DIV_DENOM_CANCEL3, REAL_OVER1, REAL_THIRDS_BETWEEN,
            REAL_DIV_ADD, REAL_DIV_INNER_CANCEL2, REAL_DIV_INNER_CANCEL3,
            REAL_INJ, REAL_ADD, REAL_LE, REAL_LT, REAL_MUL, REAL_LT_INV_EQ,
            REAL_POS_POS, REAL_POS_INFLATE, REAL_MIN_REFL, REAL_MIN_LE,
            REAL_DIV_OUTER_CANCEL2, REAL_DIV_OUTER_CANCEL3, REAL_DIV_REFL2,
            REAL_DIV_REFL3, REAL_MAX_REFL, REAL_LE_MAX, REAL_ADD_SUB,
            REAL_SUB_ADD, REAL_ADD_SUB_ALT, REAL_POS_EQ_ZERO,
            REAL_POS_LE_ZERO, REAL_MIN_ADD, REAL_MIN_SUB, REAL_MAX_ADD,
            REAL_MAX_SUB, REAL_LE_RADD, REAL_SUB_RNEG, REAL_NEG_SUB,
            REAL_SUB_SUB2]};

val real_ss = simpLib.++ (arith_ss, real_SS);

val real_ac_SS = simpLib.SIMPSET {
  ac = [(SPEC_ALL REAL_ADD_ASSOC, SPEC_ALL REAL_ADD_SYM),
        (SPEC_ALL REAL_MUL_ASSOC, SPEC_ALL REAL_MUL_SYM)],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [],
  congs = []};

val real_ac_ss = simpLib.++ (real_ss, real_ac_SS);

end;
