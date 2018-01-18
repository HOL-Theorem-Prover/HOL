structure ratReduce :> ratReduce =
struct

open HolKernel boolLib Abbrev ratSyntax ratTheory

val zero = mk_rat_of_num (numSyntax.mk_numeral Arbnum.zero)
val one = mk_rat_of_num (numSyntax.mk_numeral Arbnum.one)

val neg1 = mk_rat_ainv one
val neg1neg1 = mk_rat_div(neg1, neg1)

val ratmul_thms = CONJUNCTS RAT_MUL_NUM_CALCULATE
val ratmul_convs = map REWR_CONV ratmul_thms
val rateq_thms = CONJUNCTS RAT_EQ_NUM_CALCULATE
val rateq_convs = map REWR_CONV rateq_thms
val ratadd_thms = CONJUNCTS RAT_ADD_NUM_CALCULATE
val ratadd_convs = map REWR_CONV ratadd_thms

fun expose_num t =
  if is_rat_ainv t then expose_num (rand t)
  else if is_rat_of_num t then expose_num (rand t)
  else t
fun expose_num_conv c t =
  if is_rat_ainv t then RAND_CONV (expose_num_conv c) t
  else if is_rat_of_num t then RAND_CONV (expose_num_conv c) t
  else c t

val NOT_F = last (CONJUNCTS boolTheory.NOT_CLAUSES)
val T_AND = hd (CONJUNCTS (SPEC_ALL boolTheory.AND_CLAUSES))
val T_IMP = hd (CONJUNCTS (SPEC_ALL boolTheory.IMP_CLAUSES))

fun ERROR f msg c t =
  c t handle HOL_ERR _ => raise mk_HOL_ERR "ratReduce" f msg

val prove_two_nonzero_preconds =
    ERROR "prove_two_nonzero_preconds" "denominators not both non-zero"
      (LAND_CONV (BINOP_CONV
                    (RAND_CONV
                       (FIRST_CONV rateq_convs THENC
                        EVERY_CONJ_CONV reduceLib.REDUCE_CONV) THENC
                     REWR_CONV NOT_F) THENC
                  REWR_CONV T_AND) THENC
       REWR_CONV T_IMP)

(* given term of form
     (n1 / d1) * (n2 / d2)
   where n's and d's are either &n, or -&n, returns theorem saying
     |- t = n' / d'
   with n' and d' similarly literal-shaped. No normalisation is done on result
*)
fun coremul_conv t =
  let
    val (t1,t2) = dest_rat_mul t
    val th0 = PART_MATCH (lhand o lhs o rand) RAT_DIVDIV_MUL t1
    val th1 = PART_MATCH (rand o lhs o rand) th0 t2
  in
    CONV_RULE (RAND_CONV
                 (RAND_CONV
                    (BINOP_CONV
                       (FIRST_CONV ratmul_convs THENC
                        expose_num_conv reduceLib.REDUCE_CONV))) THENC
               prove_two_nonzero_preconds)
              th1
  end

val rataddmul_rwc = PURE_REWRITE_CONV (ratadd_thms @ ratmul_thms)

fun coreadd_conv t =
  let
    val (t1,t2) = dest_rat_add t
    val th0 = PART_MATCH (lhand o lhs o rand) RAT_DIVDIV_ADD t1
    val th1 = PART_MATCH (rand o lhs o rand) th0 t2
  in
    CONV_RULE (RAND_CONV
                 (RAND_CONV
                    (BINOP_CONV
                       (rataddmul_rwc THENC
                        expose_num_conv reduceLib.REDUCE_CONV))) THENC
               prove_two_nonzero_preconds)
              th1
  end

val denom1_conv = REWR_CONV (GSYM RAT_DIV_1)
fun maybe_denom1_conv t =
  if is_rat_div t then ALL_CONV t
  else denom1_conv t

val neg1_neq0 =
    (RAND_CONV (FIRST_CONV rateq_convs THENC
                EVERY_CONJ_CONV reduceLib.REDUCE_CONV) THENC
     REWR_CONV NOT_F) (mk_neg(mk_eq(neg1,zero))) |> EQT_ELIM
val mul_n1n1_id = MATCH_MP (GEN_ALL RAT_DIV_INV) neg1_neq0

(* ensures that a fraction has positive denominator by multiplying with -1/-1
   if necessary *)
fun posdenom_conv t =
  let
    val (n,d) = ratSyntax.dest_rat_div t
  in
    if is_rat_ainv d then
      REWR_CONV (GSYM RAT_MUL_RID) THENC
      RAND_CONV (REWR_CONV (GSYM mul_n1n1_id)) THENC
      coremul_conv
    else ALL_CONV
  end t

fun binop_prenorm c =
  BINOP_CONV (maybe_denom1_conv THENC posdenom_conv) THENC c

val xn = mk_var("x", numSyntax.num)
val nb1_x = mk_rat_of_num (mk_comb(numSyntax.numeral_tm, numSyntax.mk_bit1 xn))
val nb2_x = mk_rat_of_num (mk_comb(numSyntax.numeral_tm, numSyntax.mk_bit2 xn))

fun mk_div_eq1 t =
  TAC_PROOF(([], mk_eq(mk_rat_div(t,t), one)),
            MATCH_MP_TAC RAT_DIV_INV >>
            REWRITE_TAC [RAT_EQ_NUM_CALCULATE] >>
            REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
                         arithmeticTheory.BIT2,
                         arithmeticTheory.BIT1, numTheory.NOT_SUC,
                         arithmeticTheory.ADD_CLAUSES])

val div_eq_1 = map mk_div_eq1 [nb1_x, nb2_x]

val elim_neg0_conv = LAND_CONV (REWR_CONV RAT_AINV_0)

fun elim_common_factor t = let
  open Arbint
  val (n,d) = dest_rat_div t
  val n_i = int_of_term n
in
  if n_i = zero then REWR_CONV RAT_DIV_0 t
  else let
      val d_i = int_of_term d
      val _ = d_i > zero orelse
              raise mk_HOL_ERR "realSimps" "elim_common_factor"
                               "denominator must be positive"
      val g = fromNat (Arbnum.gcd (toNat (abs n_i), toNat (abs d_i)))
      val _ = g <> one orelse
              raise mk_HOL_ERR "ratReduce" "elim_common_factor"
                               "No common factor"
      val frac_1 = mk_rat_div(term_of_int g, term_of_int g)
      val frac_new_t =
          mk_rat_div(term_of_int (n_i div g), term_of_int (d_i div g))
      val mul_t = mk_rat_mul(frac_new_t, frac_1)
      val eqn1 = coremul_conv mul_t
      val frac_1_eq_1 = FIRST_CONV (map REWR_CONV div_eq_1) frac_1
      val eqn2 =
          TRANS (SYM eqn1)
                (AP_TERM(mk_comb(rat_mul_tm, frac_new_t)) frac_1_eq_1)
    in
      CONV_RULE (RAND_CONV (REWR_CONV RAT_MUL_RID THENC
                            TRY_CONV (REWR_CONV RAT_DIV_1)))
                eqn2
    end
end

val RAT_MUL_CONV =
    binop_prenorm coremul_conv THENC TRY_CONV elim_neg0_conv THENC
    TRY_CONV elim_common_factor THENC
    EVERY_CONV (map (TRY_CONV o REWR_CONV) [RAT_DIV_1, RAT_DIV_0])

(* given fraction; finds gcd of numerator and denominator (as Arbnum.num) *)
fun find_gcd t =
  let
    val (n,d) = dest_rat_div t
    val num1 = numSyntax.dest_numeral (expose_num n)
    val num2 = numSyntax.dest_numeral (expose_num d)
  in
    Arbnum.gcd(num1,num2)
  end

val RAT_ADD_CONV =
    binop_prenorm coreadd_conv THENC TRY_CONV elim_neg0_conv THENC
    TRY_CONV elim_common_factor THENC
    EVERY_CONV (map (TRY_CONV o REWR_CONV) [RAT_DIV_1, RAT_DIV_0])

end (* struct *)
