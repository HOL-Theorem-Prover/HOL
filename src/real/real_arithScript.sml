Theory real_arith
Ancestors
  realax
Libs
  Normalizer RealArith0

(* ------------------------------------------------------------------------- *)
(* Bootstrapping REAL_ARITH: trivial abs-elim and only integer constants.    *)
(* ------------------------------------------------------------------------- *)

fun term_lt u t = (Term.compare(u,t) = LESS)

val (REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
      REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV) =
  SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
    (is_realintconst,
     REAL_INT_ADD_CONV,REAL_INT_MUL_CONV,REAL_INT_POW_CONV) term_lt

val rule = GEN_REAL_ARITH0
    (term_of_rat (* only real integers are involved here *),
     REAL_INT_EQ_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
     REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
     NO_CONV,NO_CONV,REAL_LINEAR_PROVER)

(* eliminates abs, max and min by definitions *)
and deabs_conv = REWRITE_CONV[real_abs, real_max, real_min];

fun REAL_ARITH0 tm = let
  val th1 = QCONV deabs_conv tm
  in EQ_MP (SYM th1) (rule(rand(concl th1))) end;

Theorem ABSMAXMIN_ELIM_CONV1_pth[unlisted] = REAL_ARITH0 “
  (~(&1) * abs(x) >= r <=> ~(&1) * x >= r /\ &1 * x >= r) /\
  (~(&1) * abs(x) + a >= r <=> a + ~(&1) * x >= r /\ a + &1 * x >= r) /\
  (a + ~(&1) * abs(x) >= r <=> a + ~(&1) * x >= r /\ a + &1 * x >= r) /\
  (a + ~(&1) * abs(x) + b >= r <=>
   a + ~(&1) * x + b >= r /\ a + &1 * x + b >= r) /\
  (a + b + ~(&1) * abs(x) >= r <=>
   a + b + ~(&1) * x >= r /\ a + b + &1 * x >= r) /\
  (a + b + ~(&1) * abs(x) + c >= r <=>
   a + b + ~(&1) * x + c >= r /\ a + b + &1 * x + c >= r) /\
  (~(&1) * max x y >= r <=> ~(&1) * x >= r /\ ~(&1) * y >= r) /\
  (~(&1) * max x y + a >= r <=>
   a + ~(&1) * x >= r /\ a + ~(&1) * y >= r) /\
  (a + ~(&1) * max x y >= r <=> a + ~(&1) * x >= r /\ a + ~(&1) * y >= r) /\
  (a + ~(&1) * max x y + b >= r <=>
   a + ~(&1) * x + b >= r /\ a + ~(&1) * y + b >= r) /\
  (a + b + ~(&1) * max x y >= r <=>
   a + b + ~(&1) * x >= r /\ a + b + ~(&1) * y >= r) /\
  (a + b + ~(&1) * max x y + c >= r <=>
   a + b + ~(&1) * x + c >= r /\ a + b + ~(&1) * y + c >= r) /\
  (&1 * min x y >= r <=> &1 * x >= r /\ &1 * y >= r) /\
  (&1 * min x y + a >= r <=> a + &1 * x >= r /\ a + &1 * y >= r) /\
  (a + &1 * min x y >= r <=> a + &1 * x >= r /\ a + &1 * y >= r) /\
  (a + &1 * min x y + b >= r <=>
   a + &1 * x + b >= r /\ a + &1 * y + b >= r) /\
  (a + b + &1 * min x y >= r <=>
   a + b + &1 * x >= r /\ a + b + &1 * y >= r) /\
  (a + b + &1 * min x y + c >= r <=>
   a + b + &1 * x + c >= r /\ a + b + &1 * y + c >= r) /\
  (min x y >= r <=> x >= r /\ y >= r) /\
  (min x y + a >= r <=> a + x >= r /\ a + y >= r) /\
  (a + min x y >= r <=> a + x >= r /\ a + y >= r) /\
  (a + min x y + b >= r <=> a + x + b >= r /\ a + y + b >= r) /\
  (a + b + min x y >= r <=> a + b + x >= r /\ a + b + y >= r) /\
  (a + b + min x y + c >= r <=> a + b + x + c >= r /\ a + b + y + c >= r) /\
  (~(&1) * abs(x) > r <=> ~(&1) * x > r /\ &1 * x > r) /\
  (~(&1) * abs(x) + a > r <=> a + ~(&1) * x > r /\ a + &1 * x > r) /\
  (a + ~(&1) * abs(x) > r <=> a + ~(&1) * x > r /\ a + &1 * x > r) /\
  (a + ~(&1) * abs(x) + b > r <=>
   a + ~(&1) * x + b > r /\ a + &1 * x + b > r) /\
  (a + b + ~(&1) * abs(x) > r <=>
   a + b + ~(&1) * x > r /\ a + b + &1 * x > r) /\
  (a + b + ~(&1) * abs(x) + c > r <=>
   a + b + ~(&1) * x + c > r /\ a + b + &1 * x + c > r) /\
  (~(&1) * max x y > r <=> ~(&1) * x > r /\ ~(&1) * y > r) /\
  (~(&1) * max x y + a > r <=> a + ~(&1) * x > r /\ a + ~(&1) * y > r) /\
  (a + ~(&1) * max x y > r <=> a + ~(&1) * x > r /\ a + ~(&1) * y > r) /\
  (a + ~(&1) * max x y + b > r <=>
   a + ~(&1) * x + b > r /\ a + ~(&1) * y  + b > r) /\
  (a + b + ~(&1) * max x y > r <=>
   a + b + ~(&1) * x > r /\ a + b + ~(&1) * y > r) /\
  (a + b + ~(&1) * max x y + c > r <=>
   a + b + ~(&1) * x + c > r /\ a + b + ~(&1) * y  + c > r) /\
  (min x y > r <=> x > r /\ y > r) /\
  (min x y + a > r <=> a + x > r /\ a + y > r) /\
  (a + min x y > r <=> a + x > r /\ a + y > r) /\
  (a + min x y + b > r <=> a + x + b > r /\ a + y  + b > r) /\
  (a + b + min x y > r <=> a + b + x > r /\ a + b + y > r) /\
  (a + b + min x y + c > r <=> a + b + x + c > r /\ a + b + y + c > r)”;

