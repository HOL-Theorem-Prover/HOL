(* ========================================================================= *)
(* Tools for reasoning about positive reals (posreals).                      *)
(* ========================================================================= *)

structure posrealTools :> posrealTools =
struct

open HolKernel Parse boolLib simpLib posrealTheory;

val ERR = mk_HOL_ERR "posrealTools";

(* ------------------------------------------------------------------------- *)
(* Two useful case-splits on posreals                                        *)
(* pcases:  finite and infinite                                              *)
(* pcases3: finite non-zero and infinite                                     *)
(* ------------------------------------------------------------------------- *)

local
  val posreal = Type `:posreal`;

  fun pcase_split x =
    STRIP_ASSUME_TAC (SPEC x posreal_cases)
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC boolSimps.bool_ss [th]);

  fun pcase3_split x =
    STRIP_ASSUME_TAC (SPEC x posreal_trich)
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC boolSimps.bool_ss [th]);
in
  fun pcases goal =
    let val v = genvar posreal in X_GEN_TAC v THEN pcase_split v end goal;

  val pcases_on = Q_TAC pcase_split;

  fun pcases3 goal =
    let val v = genvar posreal in X_GEN_TAC v THEN pcase3_split v end goal;

  val pcases3_on = Q_TAC pcase3_split;
end;

(* ------------------------------------------------------------------------- *)
(* Useful rewrites for basic posreal arithmetic.                             *)
(* ------------------------------------------------------------------------- *)

val posreal_SS = simpLib.SSFRAG
  {ac = [], name = SOME "posreal",
   congs = [],
   convs = [],
   dprocs = [],
   filter = NONE,
   rewrs = [(* addition *)
            add_lzero, add_rzero, add_linfty, add_rinfty,
            (* subtraction *)
            sub_lzero, sub_rzero,
            (* less than or equal *)
            le_refl, le_zero, zero_le, le_infty, infty_le, le_addl,
            le_addr, addl_le, addr_le,
            (* less than *)
            lt_addl, lt_addr, addl_lt, addr_lt,
            (* multiplication *)
            mul_lzero, mul_rzero, mul_lone, mul_rone,
            (* reciprocal *)
            inv_zero, inv_one, inv_infty, inv_eq_zero, inv_antimono, inv_inj,
            inv_one_le, inv_le_one, inv_eq_infty, inv_eq_one, inv_inv,
            (* division *)
            div_rone,
            (* cancellations *)
            (* halves *)
            half_between,
            (* thirds *)
            thirds_between,
            (* injecting from the naturals *)
            posreal_of_num_inj, posreal_of_num_not_infty, posreal_of_num_le,
            posreal_of_num_lt, posreal_of_num_add, posreal_of_num_sub,
            posreal_of_num_mul,
            (* injecting from the reals *)
            preal_not_infty,
            (* min *)
            min_le1, min_le2, min_refl, min_linfty, min_rinfty,
            min_lzero, min_rzero,
            (* max *)
            le_max1, le_max2, max_refl, max_linfty, max_rinfty,
            max_lzero, max_rzero,
            (* bound1 *)
            bound1_basic, bound1_infty]};

val posreal_ss = simpLib.++ (realSimps.real_ss, posreal_SS);

(* ------------------------------------------------------------------------- *)
(* A calculator for rational posreals.                                       *)
(* ------------------------------------------------------------------------- *)

val dest_preal_div = dest_binop ``preal_div`` (ERR "dest_preal_div" "");

val posreal_of_num_tm = ``posreal_of_num``;

fun numeral_factor_conv k tm =
  let
    val _ = k <> Arbnum.zero orelse raise ERR "numeral_factor_conv" "k = 0"
    val n = numSyntax.dest_numeral tm
    val (nq,nr) = Arbnum.divmod (n,k)
    val _ = nr = Arbnum.zero orelse raise ERR "numeral_factor_conv" "k | n"
    val k' = numSyntax.mk_numeral k
    val nq' = numSyntax.mk_numeral nq
    val mul_tm = numSyntax.mk_mult (k',nq')
  in
    GSYM (reduceLib.MUL_CONV mul_tm)
  end;

fun rat_cancel_conv k =
  LAND_CONV (RAND_CONV (numeral_factor_conv k)) THENC
  RAND_CONV (RAND_CONV (numeral_factor_conv k)) THENC
  LAND_CONV (REWR_CONV (GSYM posreal_of_num_mul)) THENC
  RAND_CONV (REWR_CONV (GSYM posreal_of_num_mul)) THENC
  REWR_CONV rat_cancel;

fun rat_reduce_conv tm =
  let
    val (a,b) = dest_preal_div tm
    val m = numSyntax.dest_numeral (rand a)
    val _ = m <> Arbnum.zero orelse raise ERR "rat_reduce_conv" "0 numerator"
    val n = numSyntax.dest_numeral (rand b)
    val _ = n <> Arbnum.zero orelse raise ERR "rat_reduce_conv" "0 denominator"
    val g = Arbnum.gcd (m,n)
  in
    if g = Arbnum.one then raise ERR "rat_reduce_conv" "reduced"
    else rat_cancel_conv g tm
  end;

val rat_reduce_pat =
  Term `preal_div (posreal_of_num (NUMERAL x)) (posreal_of_num (NUMERAL y))`;

val posreal_reduce_SS = simpLib.SSFRAG
  {ac = [],
   congs = [],
   name = SOME "posreal_reduce",
   convs = [{name = "rat_reduce_conv (posreals)", conv = K (K rat_reduce_conv),
             trace = 2, key = SOME ([],rat_reduce_pat)}],
   dprocs = [],
   filter = NONE,
   rewrs = [(* equality *)
            posreal_of_num_not_infty, posreal_of_num_inj, eq_rat, eq_ratl,
            rat_eq_infty,
            (* addition *)
            posreal_of_num_add, add_rat, add_ratl, add_ratr, add_linfty,
            add_rinfty,
            (* subtraction *)
            posreal_of_num_sub, sub_rat, sub_ratl, sub_ratr, sub_linfty_rat,
            sub_linfty_num, sub_rinfty_rat, sub_rinfty_num,
            (* less than or equal *)
            le_rat, le_ratl, le_ratr, le_infty, infty_le,
            posreal_of_num_le,
            (* less than *)
            posreal_of_num_lt,
            (* multiplication *)
            posreal_of_num_mul, mul_rat, mul_ratl, mul_ratr, mul_linfty_rat,
            mul_linfty_num, mul_rinfty_rat, mul_rinfty_num, mul_infty_infty,
            (* reciprocal *)
            (* division *)
            div_rat, div_ratl, div_ratr, div_rzero_num, div_rzero_rat,
            div_lzero, div_rinfty, div_linfty_num, div_linfty_rat, div_rone,
            (* cancellations *)
            (* min *)
            min_linfty, min_rinfty, min_num, min_ratl, min_ratr, min_rat,
            (* max *)
            max_linfty, max_rinfty, max_num, max_ratl, max_ratr, max_rat,
            (* bound1 *)
            bound1_infty, bound1_num, bound1_rat]};

val posreal_reduce_ss =
  simpLib.++
  (simpLib.++ (boolSimps.bool_ss, numSimps.REDUCE_ss), posreal_reduce_SS);

(* ------------------------------------------------------------------------- *)
(* AC normalizer for multiplication.                                         *)
(* ------------------------------------------------------------------------- *)

val dest_mul = dest_binop ``preal_mul`` (ERR "dest_mul" "");
val is_mul = can dest_mul;

local
  fun terminate is_op rid tm =
    (if is_op tm then RAND_CONV (terminate is_op rid)
     else REWR_CONV (GSYM rid)) tm;

  fun dest_inv inv tm =
    if is_comb tm andalso rator tm = inv then (false, rand tm) else (true, tm);

  fun bubble is_op swap inv tm =
    (if not (is_op tm) orelse not (is_op (rand tm)) then ALL_CONV else
       let
         val (a1,b1) = dest_comb tm
         val (s1,t1) = dest_inv inv (rand a1)
         val (s2,t2) = dest_inv inv (rand (rator b1))
         val finished =
           case compare (t1,t2) of LESS => true
           | EQUAL => not (s1 = false andalso s2 = true)
           | GREATER => false
       in
         if finished then ALL_CONV
         else REWR_CONV swap THENC RAND_CONV (bubble is_op swap inv)
       end) tm;

  fun sort is_op swap inv tm =
    (if not (is_op tm) then ALL_CONV
     else RAND_CONV (sort is_op swap inv) THENC bubble is_op swap inv) tm;

  fun permute is_op assoc rid swap inv =
    SIMP_CONV boolSimps.bool_ss [assoc]
    THENC terminate is_op rid
    THENC sort is_op swap inv;
in
  fun permute_conv is_op assoc rid swap inv tm =
    (if is_op tm then permute is_op assoc rid swap inv else NO_CONV) tm;
end;

val permute_mul_conv =
  permute_conv is_mul mul_assoc mul_rone mul_swap ``preal_inv``;

end;
