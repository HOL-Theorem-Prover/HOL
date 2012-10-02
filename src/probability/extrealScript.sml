(* ------------------------------------------------------------------------- *)
(* Measure Theory defined on the extended reals and includes Borel spaces    *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)

(*
val () = app load ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory",
       	     	   "extra_pred_setTheory", "extra_realTheory", "realLib",
		   "pairTheory", "seqTheory", "transcTheory", "util_probTheory"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib
     combinTheory pred_setTheory res_quanTools
     arithmeticTheory realTheory realLib real_sigmaTheory pairTheory
      seqTheory transcTheory util_probTheory;

(* val () = quietdec := false; *)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "extreal"                                       *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "extreal";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);


(* ********************************************* *)
(*              Type Definiton                   *)
(* ********************************************* *)
val _ = Hol_datatype`extreal = NegInf | PosInf | Normal of real`;

val extreal_of_num_def = Define `extreal_of_num n = Normal (&n)`;

val real_def = Define `real x = (if ((x = NegInf) \/ (x = PosInf)) then 0:real
                                else (@r. x = Normal r))`;

val real_normal = store_thm
("real_normal",``!x. real (Normal x) = x``,
 RW_TAC std_ss [real_def]);

val normal_real = store_thm
("normal_real",``!x. x <> NegInf /\ x <> PosInf ==> (Normal (real x) = x)``,
  RW_TAC std_ss [real_def]
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss []
  ++ Cases_on `x`
  ++ METIS_TAC []);

(* ********************************************* *)
(*     Definitions of Arithmetic Operations      *)
(* ********************************************* *)
val extreal_add_def = Define`
   (extreal_add (Normal x) (Normal y) = (Normal (x + y))) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf)`;

val extreal_sub_def = Define
  `(extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf a = PosInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub NegInf NegInf = PosInf) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub c NegInf = PosInf)`;

val extreal_le_def = Define
  `(extreal_le (Normal x) (Normal y) = (x <= y)) /\
   (extreal_le NegInf a = T) /\
   (extreal_le b PosInf = T) /\
   (extreal_le c NegInf = F) /\
   (extreal_le PosInf d = F)`;

val extreal_lt_def = Define `extreal_lt x y = ~extreal_le y x`;

val extreal_mul_def = Define
  `(extreal_mul NegInf NegInf = PosInf) /\
   (extreal_mul NegInf PosInf = NegInf) /\
   (extreal_mul PosInf NegInf = NegInf) /\
   (extreal_mul PosInf PosInf = PosInf) /\
   (extreal_mul (Normal x) NegInf =
   		(if x = 0 then (Normal 0) else (if 0 < x then NegInf else PosInf))) /\
   (extreal_mul NegInf (Normal y) =
   		(if y = 0 then (Normal 0) else (if 0 < y then NegInf else PosInf))) /\
   (extreal_mul (Normal x) PosInf =
   		(if x = 0 then (Normal 0) else (if 0 < x then PosInf else NegInf))) /\
   (extreal_mul PosInf (Normal y) =
   		(if y = 0 then (Normal 0) else (if 0 < y then PosInf else NegInf))) /\
   (extreal_mul (Normal x) (Normal y) = Normal (x * y))`;

val extreal_inv_def = Define
  `(extreal_inv NegInf = Normal 0) /\
   (extreal_inv PosInf = Normal 0) /\
   (extreal_inv (Normal x) = Normal (inv x))`;

val extreal_ainv_def = Define
  `(extreal_ainv NegInf = PosInf) /\
   (extreal_ainv PosInf = NegInf) /\
   (extreal_ainv (Normal x) = Normal (- x))`;

val extreal_div_def = Define `extreal_div x y = extreal_mul x (extreal_inv y)`;

val extreal_abs_def = Define
  `(extreal_abs (Normal x) = Normal (abs x)) /\
   (extreal_abs _ = PosInf)`;

val extreal_logr_def = Define
  `(extreal_logr b (Normal x) = Normal (logr b x)) /\
   (extreal_logr b PosInf = PosInf) /\
   (extreal_logr b NegInf = NegInf)`;

val extreal_lg_def = Define `extreal_lg x = extreal_logr 2 x`;

val extreal_exp_def = Define
  `(extreal_exp (Normal x) = Normal (exp x)) /\
   (extreal_exp PosInf = PosInf) /\
   (extreal_exp NegInf = Normal 0)`;

val extreal_pow_def = Define
  `(extreal_pow (Normal a) n = Normal (a pow n)) /\
   (extreal_pow PosInf n = if n=0 then Normal 1 else PosInf) /\
   (extreal_pow NegInf n = if n=0 then Normal 1 else (if (EVEN n) then PosInf else NegInf))`;

val extreal_sqrt_def = Define
  `(extreal_sqrt (Normal x) = Normal (sqrt x)) /\
   (extreal_sqrt PosInf = PosInf)`;

val _ = add_numeral_form (#"x", SOME "extreal_of_num");
val _ = overload_on ("+",   Term `extreal_add`);
val _ = overload_on ("-",   Term `extreal_sub`);
val _ = overload_on ("*",   Term `extreal_mul`);
val _ = overload_on ("/",   Term `extreal_div`);
val _ = overload_on ("<=",  Term `extreal_le`);
val _ = overload_on ("<",   Term `extreal_lt`);
val _ = overload_on ("~",   Term `extreal_ainv`);
val _ = overload_on ("numeric_negate",   Term `extreal_ainv`);
val _ = overload_on ("inv", Term `extreal_inv`);
val _ = overload_on ("abs",   Term `extreal_abs`);
val _ = overload_on ("logr",   Term `extreal_logr`);
val _ = overload_on ("lg",   Term `extreal_lg`);
val _ = overload_on ("exp",   Term `extreal_exp`);
val _ = overload_on ("pow", Term `extreal_pow`);
val _ = overload_on ("sqrt", Term `extreal_sqrt`);


(* ********************************************* *)
(*       Useful Theorems on Real Numbers         *)
(* ********************************************* *)

val REAL_LT_LMUL_0_NEG = store_thm
 ("REAL_LT_LMUL_0_NEG",``!x y:real. 0 < x * y /\ x < 0 ==> y < 0``,
 RW_TAC real_ss []
 ++ SPOSE_NOT_THEN ASSUME_TAC
 ++ FULL_SIMP_TAC real_ss [REAL_NOT_LT, GSYM REAL_NEG_GT0]
 ++ METIS_TAC [REAL_MUL_LNEG, REAL_LT_IMP_LE, REAL_LE_MUL,
    	       REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_RMUL_0_NEG = store_thm
 ("REAL_LT_RMUL_0_NEG",``!x y:real. 0 < x * y /\ y < 0 ==> x < 0``,
 RW_TAC real_ss []
 ++ SPOSE_NOT_THEN ASSUME_TAC
 ++ FULL_SIMP_TAC real_ss [REAL_NOT_LT,GSYM REAL_NEG_GT0]
 ++ METIS_TAC [REAL_MUL_RNEG, REAL_LT_IMP_LE, REAL_LE_MUL, REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_LMUL_NEG_0 = store_thm
 ("REAL_LT_LMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < x ==> y < 0``,
 RW_TAC real_ss []
 ++ METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0 = store_thm
 ("REAL_LT_RMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < y ==> x < 0``,
 RW_TAC real_ss []
 ++ METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_RMUL_0]);

val REAL_LT_LMUL_NEG_0_NEG = store_thm
 ("REAL_LT_LMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ x < 0 ==> 0 < y``,
 RW_TAC real_ss []
 ++ METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0_NEG = store_thm
 ("REAL_LT_RMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ y < 0 ==> 0 < x``,
 RW_TAC real_ss []
 ++ METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_RMUL_0]);

val REAL_LT_RDIV_EQ_NEG = store_thm
 ("REAL_LT_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y /z < x <=> x * z < y)``,
  RW_TAC real_ss []
  ++ `0<-z` by RW_TAC real_ss [REAL_NEG_GT0]
  ++ `z<>0` by (METIS_TAC [REAL_LT_IMP_NE])
  ++EQ_TAC
  >> (RW_TAC real_ss []
      ++ `y/z*(-z) < x*(-z)` by METIS_TAC [GSYM REAL_LT_RMUL]
      ++ FULL_SIMP_TAC real_ss []
      ++ METIS_TAC [REAL_DIV_RMUL, REAL_LT_NEG])
  ++ RW_TAC real_ss []
  ++ `-y < x*(-z)` by FULL_SIMP_TAC real_ss [REAL_LT_NEG]
  ++ `-y * inv(-z) < x` by METIS_TAC [GSYM REAL_LT_LDIV_EQ, real_div]
  ++ METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val REAL_LE_RDIV_EQ_NEG = store_thm
 ("REAL_LE_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y /z <= x <=> x * z <= y)``,
  RW_TAC real_ss []
  ++ `0 < -z` by RW_TAC real_ss [REAL_NEG_GT0]
  ++ `z <> 0` by (METIS_TAC [REAL_LT_IMP_NE])
  ++EQ_TAC
  >> (RW_TAC real_ss []
      ++ `y / z * (-z) <= x * (-z)` by METIS_TAC [GSYM REAL_LE_RMUL]
      ++ FULL_SIMP_TAC real_ss []
      ++ METIS_TAC [REAL_DIV_RMUL,REAL_LE_NEG])
  ++ RW_TAC real_ss []
  ++ `-y <= x * (-z)` by FULL_SIMP_TAC real_ss [REAL_LE_NEG]
  ++ `-y * inv (-z) <= x` by METIS_TAC [GSYM REAL_LE_LDIV_EQ, real_div]
  ++ METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val POW_POS_EVEN = store_thm
 ("POW_POS_EVEN",``!x:real. x < 0 ==> ((0 < x pow n) = (EVEN n))``,
  Induct_on `n`
  >> RW_TAC std_ss [pow,REAL_LT_01,EVEN]
  ++ RW_TAC std_ss [pow,EVEN]
  ++ EQ_TAC
  >> METIS_TAC [REAL_LT_ANTISYM, REAL_LT_RMUL_0_NEG, REAL_MUL_COMM]
  ++ RW_TAC std_ss []
  ++ `x pow n <= 0` by METIS_TAC [real_lt]
  ++ `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  ++ `x pow n < 0` by METIS_TAC [REAL_LT_LE]
  ++ METIS_TAC [REAL_NEG_GT0, REAL_NEG_MUL2, REAL_LT_MUL]);

val POW_NEG_ODD = store_thm
 ("POW_NEG_ODD",``!x:real. x < 0 ==> ((x pow n < 0) = (ODD n))``,
  Induct_on `n`
  >> RW_TAC std_ss [pow,GSYM real_lte,REAL_LE_01]
  ++ RW_TAC std_ss [pow,ODD]
  ++ EQ_TAC
  >> METIS_TAC [REAL_LT_RMUL_NEG_0_NEG, REAL_MUL_COMM, REAL_LT_ANTISYM]
  ++ RW_TAC std_ss []
  ++ `0 <= x pow n` by METIS_TAC [real_lt]
  ++ `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  ++ `0 < x pow n` by METIS_TAC [REAL_LT_LE]
  ++ METIS_TAC [REAL_NEG_GT0, REAL_MUL_LNEG, REAL_LT_MUL]);

val LOGR_MONO_LE = store_thm
 ("LOGR_MONO_LE",``!x:real y b. 0 < x /\ 0 < y /\ 1 < b ==> (logr b x <= logr b y <=> x <= y)``,
  RW_TAC std_ss [logr_def,real_div]
  ++ `0 < ln b` by METIS_TAC [REAL_LT_01, LN_1, REAL_LT_TRANS, LN_MONO_LT]
  ++ METIS_TAC [REAL_LT_INV_EQ, REAL_LE_RMUL, LN_MONO_LE]);

val LOGR_MONO_LE_IMP = store_thm
 ("LOGR_MONO_LE_IMP",``!x:real y b. 0 < x /\ x <= y /\ 1 <= b ==> (logr b x <= logr b y)``,
  RW_TAC std_ss [logr_def,real_div]
  ++ `0 <= ln b` by METIS_TAC [REAL_LT_01, LN_1, REAL_LTE_TRANS, LN_MONO_LE]
  ++ METIS_TAC [REAL_LE_INV_EQ, REAL_LE_RMUL_IMP, LN_MONO_LE, REAL_LTE_TRANS]);

val mono_increasing_def = Define
   `mono_increasing (f:num->real) = !m n. m <= n ==> f m <= f n`;

val mono_increasing_suc = store_thm
  ("mono_increasing_suc", ``!(f:num->real). mono_increasing f <=> !n. f n <= f (SUC n)``,
    RW_TAC std_ss [mono_increasing_def]
    ++ EQ_TAC
    >> RW_TAC real_ss []
    ++ RW_TAC std_ss []
    ++ Know `?d. n = m + d` >> PROVE_TAC [LESS_EQ_EXISTS]
    ++ RW_TAC std_ss []
    ++ Induct_on `d` >> RW_TAC real_ss []
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `m + d`)
    ++ METIS_TAC [REAL_LE_TRANS, ADD_CLAUSES, LESS_EQ_ADD]);

val mono_decreasing_def = Define
   `mono_decreasing (f:num->real) = !m n. m <= n ==> f n <= f m`;

val mono_decreasing_suc = store_thm
  ("mono_decreasing_suc", ``!(f:num->real). mono_decreasing f <=> !n. f (SUC n) <= f n``,
    RW_TAC std_ss [mono_decreasing_def]
    ++ EQ_TAC
    >> RW_TAC real_ss []
    ++ RW_TAC std_ss []
    ++ Know `?d. n = m + d` >> PROVE_TAC [LESS_EQ_EXISTS]
    ++ RW_TAC std_ss []
    ++ Induct_on `d` >> RW_TAC real_ss []
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!n. f (SUC n) <= f n` (MP_TAC o Q.SPEC `m + d`)
    ++ METIS_TAC [REAL_LE_TRANS, ADD_CLAUSES, LESS_EQ_ADD]);

val mono_increasing_converges_to_sup = store_thm
  ("mono_increasing_converges_to_sup",
   ``!f r. mono_increasing f /\ f --> r ==>
	   (r = sup (IMAGE f UNIV))``,
   RW_TAC std_ss [mono_increasing_def]
   ++ Suff `f --> sup (IMAGE f UNIV)`
   >> METIS_TAC [SEQ_UNIQ]
   ++ RW_TAC std_ss [SEQ]
   ++ (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON
   ++ SIMP_TAC std_ss [REAL_LT_HALF1]
   ++ `!y x z. IMAGE f UNIV x = x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
   ++ POP_ORW
   ++ Know `(?z. !x. x IN IMAGE f UNIV ==> x <= z)`
   >> (Q.EXISTS_TAC `r` ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
	    ++ MATCH_MP_TAC SEQ_MONO_LE
	    ++ RW_TAC std_ss [DECIDE ``!n:num. n <= n + 1``])
   ++ SIMP_TAC std_ss [] ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV, GSYM ABS_BETWEEN, GREATER_EQ]
   ++ Q.EXISTS_TAC `x'`
   ++ RW_TAC std_ss [REAL_LT_SUB_RADD]
   >> (MATCH_MP_TAC REAL_LET_TRANS ++ Q.EXISTS_TAC `f x' + e / 2`
       ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LET_TRANS
       ++ Q.EXISTS_TAC `f n + e / 2` ++ RW_TAC std_ss [REAL_LE_ADD2, REAL_LE_REFL]
       ++ MATCH_MP_TAC REAL_LT_IADD ++ RW_TAC std_ss [REAL_LT_HALF2])
   ++ MATCH_MP_TAC REAL_LET_TRANS ++ Q.EXISTS_TAC `sup (IMAGE f UNIV)`
   ++ RW_TAC std_ss [REAL_LT_ADDR]
   ++ Suff `!y. (\y. y IN IMAGE f UNIV) y ==> y <= sup (IMAGE f UNIV)`
   >> METIS_TAC [IN_IMAGE, IN_UNIV]
   ++ SIMP_TAC std_ss [IN_DEF]
   ++ MATCH_MP_TAC REAL_SUP_UBOUND_LE
   ++ `!y x z. IMAGE f UNIV x = x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
   ++ POP_ORW
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   ++ Q.EXISTS_TAC `r`
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC SEQ_MONO_LE
   ++ RW_TAC std_ss [DECIDE ``!n:num. n <= n + 1``]);

(* ********************************************* *)
(*     Properties of Extended Real Numbers       *)
(* ********************************************* *)

val extreal_cases = store_thm
  ("extreal_cases",
   ``!x. (x = NegInf) \/ (x = PosInf) \/ (?r. x = Normal r)``,
   Cases ++ RW_TAC std_ss []);

val extreal_eq_zero = store_thm
  ("extreal_eq_zero",
   ``!x. (Normal x = 0) = (x = 0)``,
   RW_TAC std_ss [extreal_of_num_def]);

val extreal_not_infty = store_thm
  ("extreal_not_infty",
   ``!x. (Normal x <> NegInf) /\ (Normal x <> PosInf)``,
   RW_TAC std_ss []);

val num_not_infty = store_thm
  ("num_not_infty",
   ``!n. (&n <> NegInf) /\ (&n <> PosInf)``,
   RW_TAC std_ss [extreal_of_num_def]);

val extreal_11 = store_thm
  ("extreal_11",``!a a'. (Normal a = Normal a') <=> (a = a')``,
  RW_TAC std_ss []);

(* ********************************************* *)
(*     Properties of Arithmetic Operations       *)
(* ********************************************* *)

val mul_rzero = store_thm
  ("mul_rzero",
   ``!x. x * 0 = 0``,
  Cases
  ++ RW_TAC real_ss [extreal_mul_def,extreal_of_num_def,REAL_MUL_RZERO]);

val mul_lzero = store_thm
  ("mul_lzero",
   ``!x. 0 * x = 0``,
  Cases
  ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LZERO]);

val mul_rone = store_thm
  ("mul_rone",
   ``!x. x * 1 = x``,
  Cases
  ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_RID]);

val mul_lone = store_thm
  ("mul_lone",
   ``!x. 1 * x = x``,
  Cases
  ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LID]);

val entire = store_thm
  ("entire",``!x y. (x * y = 0) <=> (x = 0) \/ (y = 0)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_mul_def, num_not_infty, extreal_of_num_def,
     	    	    extreal_11, REAL_ENTIRE]);

(***************)
(*    Order    *)
(***************)

val extreal_lt_eq = store_thm
("extreal_lt_eq",``!x y. Normal x < Normal y = x < y``,
  METIS_TAC [extreal_lt_def, extreal_le_def, real_lt]);

val le_refl = store_thm
("le_refl",``!x:extreal. x <= x``,
  Cases ++ RW_TAC std_ss [extreal_le_def, REAL_LE_REFL]);

val lt_refl = store_thm
("lt_refl",``!x:extreal. ~(x < x)``,
  RW_TAC std_ss [extreal_lt_def, le_refl]);

val le_infty = store_thm
 ("le_infty",``(!x. NegInf <= x /\ x <= PosInf) /\
 	       (!x. (x <= NegInf) = (x = NegInf)) /\
	       (!x. (PosInf <= x) = (x = PosInf))``,
  RW_TAC std_ss []
  ++ Cases_on `x`
  ++ RW_TAC std_ss [extreal_le_def]);

val lt_infty = store_thm
 ("lt_infty",``!x y. NegInf < Normal y /\ Normal y < PosInf /\
                     NegInf < PosInf /\ ~(x < NegInf) /\ ~(PosInf < x) /\
                    (x <> PosInf = x < PosInf) /\ (x <> NegInf = NegInf < x)``,
  Cases
  ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,lt_refl]);

val lt_imp_le = store_thm
  ("lt_imp_le",``!x y:extreal. x < y ==> x <= y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [lt_refl,le_refl,extreal_lt_def,extreal_le_def]
  ++ METIS_TAC [real_lt,REAL_LT_IMP_LE]);

val lt_imp_ne = store_thm
  ("lt_imp_ne",``!x y:extreal. x < y ==> x <> y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
  ++ METIS_TAC [real_lt, REAL_LT_IMP_NE]);

val le_trans = store_thm
  ("le_trans",``!x y z:extreal. x <= y /\ y <= z ==> x <= z``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def,le_refl]
  ++ METIS_TAC [REAL_LE_TRANS]);

val lt_trans = store_thm
  ("lt_trans",``!x y z:extreal. x < y /\ y < z ==> x < z``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_def, lt_refl, extreal_le_def, le_refl, GSYM real_lt]
  ++ METIS_TAC [REAL_LT_TRANS]);

val let_trans = store_thm
  ("let_trans",``!x y z:extreal. x <= y /\ y < z ==> x < z``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
  ++ METIS_TAC [real_lt,REAL_LET_TRANS]);

val le_antisym = store_thm
  ("le_antisym",``!x y:extreal. (x <= y /\ y <= x) = (x = y)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, le_refl, REAL_LE_ANTISYM]);

val lt_antisym = store_thm
  ("lt_antisym",``!x y. ~(x < y /\ y < x)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [lt_infty, extreal_lt_eq]
  ++ METIS_TAC [REAL_LT_ANTISYM, DE_MORGAN_THM]);

val lte_trans = store_thm
  ("lte_trans",``!x y z:extreal. x < y /\ y <= z ==> x < z``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
  ++ METIS_TAC [real_lt, REAL_LTE_TRANS]);

val le_total = store_thm
  ("le_total",``!x y. x <= y \/ y <= x``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, REAL_LE_TOTAL]);

val lt_total = store_thm
  ("lt_total",``!x y. (x = y) \/ x < y \/ y < x``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_lt_def, GSYM real_lt, REAL_LT_TOTAL]);

val le_01 = store_thm
  ("le_01",``0 <= 1``,
  RW_TAC std_ss [extreal_of_num_def, extreal_le_def, REAL_LE_01]);

val lt_01 = store_thm
  ("lt_01",``0 < 1``,
  METIS_TAC [extreal_of_num_def, extreal_lt_def, extreal_le_def,
  	     REAL_LT_01, real_lt]);

val ne_01 = store_thm
  ("ne_01",``0 <> 1``,
  RW_TAC std_ss [extreal_of_num_def, REAL_10]);

val le_02 = store_thm
  ("le_02",``0 <= 2``,
  RW_TAC real_ss [extreal_of_num_def, extreal_le_def]);

val lt_02 = store_thm
  ("lt_02",``0 < 2``,
  RW_TAC real_ss [extreal_of_num_def, extreal_lt_def, extreal_le_def]);

val ne_02 = store_thm
  ("ne_02",``0 <> 2``,
  RW_TAC real_ss [extreal_of_num_def]);

val le_num = store_thm
  ("le_num",``!n:num. 0 <= &n``,
  RW_TAC real_ss [extreal_of_num_def, extreal_le_def]);

val lt_le = store_thm
  ("lt_le",``!x y. x < y = (x <= y /\ x <> y)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LT_LE]);

val le_lt = store_thm
  ("le_lt",``!x y. (x <= y) = x < y \/ (x = y)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LE_LT]);

val le_neg = store_thm
  ("le_neg",``!x y. -x <= -y <=> y <= x``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def, lt_infty, le_infty,
     	    	    REAL_LE_NEG]);

val lt_neg = store_thm
 ("lt_neg",``!x y. -x < -y <=> y < x``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def,  lt_infty,le_infty,
     	    	    REAL_LT_NEG]);

val le_add = store_thm
  ("le_add",``!x y:extreal. 0 <= x /\ 0 <= y ==> 0 <= x + y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_of_num_def, REAL_LE_ADD]);

val lt_add = store_thm
  ("lt_add",``!x y:extreal. 0 < x /\ 0 < y ==> 0 < x + y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  ++ METIS_TAC [real_lt,REAL_LT_ADD]);

val let_add = store_thm
  ("let_add",``!x y:extreal. 0 <= x /\ 0 < y ==> 0 < x + y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  ++ METIS_TAC [real_lt,REAL_LET_ADD]);

val lte_add = store_thm
  ("lte_add",``!x y:extreal. 0 < x /\ 0 <= y ==> 0 < x + y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  ++ METIS_TAC [real_lt,REAL_LTE_ADD]);

val le_add2 = store_thm
  ("le_add2",``!w x y z. w <= x /\ y <= z ==> w + y <= x + z``,
  Cases ++ Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_add_def, le_infty, le_refl]
  ++ METIS_TAC [REAL_LE_ADD2]);

val lt_add2 = store_thm
  ("lt_add2",``!w x y z. w < x /\ y < z ==> w + y < x + z``,
   REPEAT Cases
   ++ RW_TAC std_ss [extreal_add_def, extreal_lt_eq, lt_infty, REAL_LT_ADD2]);

val let_add2 = store_thm
  ("let_add2",``!w x y z. w <> NegInf /\ w <> PosInf /\ w <= x /\ y < z ==> w + y < x + z``,
  Cases ++ Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty,le_refl]
  ++ METIS_TAC [real_lt, REAL_LET_ADD2]);

val let_add2_alt = store_thm
  ("let_add2_alt",``!w x y z. x <> NegInf /\ x <> PosInf /\ w <= x /\ y < z ==> w + y < x + z``,
  Cases ++ Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
  ++ METIS_TAC [real_lt, REAL_LET_ADD2]);

val le_addr = store_thm
  ("le_addr",``!x y. x <> NegInf /\ x <> PosInf ==> (x <= x + y = (0 <= y))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
     	    	    extreal_not_infty, REAL_LE_ADDR]);

val le_addr_imp = store_thm
  ("le_addr_imp",``!x y. 0 <= y ==> x <= x + y``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
     	    	    extreal_not_infty, REAL_LE_ADDR]);

val le_ladd = store_thm
  ("le_ladd",``!x y z. x <> NegInf /\ x <> PosInf ==> (x + y <= x + z = y <= z)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD]);

val le_radd = store_thm
  ("le_radd",``!x y z. x <> NegInf /\ x <> PosInf ==> (y + x <= z + x = y <= z)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD]);

val le_radd_imp = store_thm
("le_radd_imp",``!x y z. y <= z ==> y + x <= z + x``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD, le_infty, le_refl]);

val le_ladd_imp = store_thm
("le_ladd_imp",``!x y z. y <= z ==> x + y <= x + z``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD, le_infty, le_refl]);

val lt_ladd = store_thm
  ("lt_ladd",``!x y z. x <> NegInf /\ x <> PosInf ==> (x + y < x + z = y < z)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_LADD]);

val lt_radd = store_thm
  ("lt_radd",``!x y z. x <> NegInf /\ x <> PosInf ==> (y + x < z + x = y < z)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_RADD]);

val lt_addl = store_thm
  ("lt_addl",``!x y. y <> NegInf /\ y <> PosInf ==> (y < x + y = (0 < x))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                    le_infty, extreal_of_num_def, extreal_not_infty]
  ++ METIS_TAC [REAL_ADD_COMM, REAL_LE_SUB_LADD,
                real_sub, REAL_NEG_GE0, REAL_LE_ADDL]);

val le_lneg = store_thm
  ("le_lneg",``!x y. (-x <= y) <=> (0 <= x + y)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_ainv_def, extreal_le_def, extreal_add_def,
                    extreal_sub_def, le_infty, extreal_of_num_def,
                    extreal_not_infty, REAL_LE_LNEG]);

val le_mul = store_thm
  ("le_mul",``!x y:extreal. 0 <= x /\ 0 <= y ==> 0 <= x * y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt]
  ++ METIS_TAC [REAL_LT_LE, real_lte]);

val let_mul = store_thm
  ("let_mul", ``!x y. 0 <= x /\ 0 < y ==> 0 <= x * y``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq, lt_infty,
                     le_infty, le_refl, extreal_of_num_def]
  ++ METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]);

val lte_mul = store_thm
  ("lte_mul", ``!x y. 0 < x /\ 0 <= y ==> 0 <= x * y``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq,
                     lt_infty, le_infty, le_refl, extreal_of_num_def]
  ++ METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]);

val le_mul_neg = store_thm
  ("le_mul_neg",``!x y. x <= 0 /\ y <= 0 ==> 0 <= x * y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt]
  ++ METIS_TAC
  [REAL_LE_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_MUL_RZERO, REAL_LE_MUL]);

val mul_le = store_thm
  ("mul_le",``!x y. 0 <= x /\ y <= 0 ==> x * y <= 0``,
  (Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt])
  >> METIS_TAC [REAL_LT_LE, real_lt]
  ++ `0 <= -r'` by METIS_TAC [REAL_LE_NEG, REAL_NEG_0]
  ++ METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG]);

val lt_mul = store_thm
  ("lt_mul",``!x y:extreal. 0 < x /\ 0 < y ==> 0 < x * y``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    REAL_LT_MUL, lt_infty]);

val lt_mul_neg = store_thm
  ("lt_mul_neg",``!x y. x < 0 /\ y < 0 ==> 0 < x * y``,
  REPEAT Cases ++ RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, lt_infty, extreal_mul_def]
  ++ METIS_TAC [REAL_LT_LE, real_lt, REAL_LT_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_LT_MUL]);

val mul_lt = store_thm
  ("mul_lt",``!x y:extreal. 0 < x /\ y < 0 ==> x * y < 0``,
  (Cases ++ Cases
  ++ RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, REAL_LT_MUL, lt_infty])
  >> METIS_TAC [REAL_LT_LE, real_lt]
  ++ `0 < -r'` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0]
  ++ METIS_TAC [REAL_MUL_RNEG, REAL_LT_MUL, REAL_LT_NEG, REAL_NEG_0]);

val mul_let = store_thm
  ("mul_let",``!x y. 0 <= x /\ y < 0 ==> x * y <= 0``,
 Cases ++ Cases
  ++ RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, le_refl, le_infty,
     	    	     lt_infty, extreal_le_def]
  ++ METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG, REAL_NEG_NEG,
     	        REAL_LE_NEG, real_lt, REAL_LT_LE]);

val mul_lte = store_thm
  ("mul_lte",``!x y. 0 < x /\ y <= 0 ==> x * y <= 0``,
 Cases ++ Cases
  ++ RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, le_refl, le_infty,
     	    	     lt_infty, extreal_le_def]
  ++ METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG, REAL_NEG_NEG,
     	        REAL_LE_NEG, real_lt, REAL_LT_LE]);

val le_rmul_imp = store_thm
  ("le_rmul_imp",``!x y z. 0 < z /\ x <= y ==> x * z <= y * z``,
  RW_TAC std_ss []
  ++ Cases_on `z = 0` >> RW_TAC std_ss [mul_rzero,le_refl]
  ++ `0 < z` by METIS_TAC [lt_le]
  ++ Cases_on `x` ++ Cases_on `y` ++ Cases_on `z`
  ++ RW_TAC real_ss [extreal_le_def,extreal_lt_eq,extreal_mul_def,REAL_LE_REFL,REAL_LT_REFL,
                     le_infty,lt_infty,extreal_of_num_def,REAL_LT_IMP_LE,GSYM real_lte,GSYM real_lt]
  ++ METIS_TAC [real_lt,REAL_LT_LE,REAL_LTE_TRANS,lt_infty,extreal_lt_eq,extreal_le_def,extreal_of_num_def,REAL_LE_RMUL]);

val le_lmul_imp = store_thm
  ("le_lmul_imp",``!x y z. 0 <= z /\ x <= y ==> z * x <= z * y``,
  RW_TAC std_ss []
  ++ Cases_on `z = 0` >> RW_TAC std_ss [mul_lzero,le_refl]
  ++ `0 < z` by METIS_TAC [lt_le]
  ++ Cases_on `x` ++ Cases_on `y` ++ Cases_on `z`
  ++ RW_TAC real_ss [extreal_le_def,extreal_lt_eq,extreal_mul_def,REAL_LE_REFL,REAL_LT_REFL,
                     le_infty,lt_infty,extreal_of_num_def,REAL_LT_IMP_LE,GSYM real_lte,GSYM real_lt]
  ++ METIS_TAC [real_lt,REAL_LT_LE,REAL_LTE_TRANS,lt_infty,extreal_lt_eq,extreal_le_def,extreal_of_num_def,REAL_LE_LMUL]);

val lt_rmul = store_thm
  ("lt_rmul",``!x y z. 0 < z /\ z <> PosInf ==> (x * z < y * z <=> x < y)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_lt_eq,extreal_mul_def,le_infty,lt_infty,extreal_of_num_def,REAL_LT_REFL,REAL_LT_RMUL]);

val lt_lmul = store_thm
  ("lt_lmul",``!x y z. 0 < x /\ x <> PosInf ==> (x * y < x * z <=> y < z)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_lt_eq,extreal_mul_def,le_infty,lt_infty,extreal_of_num_def,REAL_LT_REFL,REAL_LT_LMUL]);

val lt_mul2 = store_thm
  ("lt_mul2",``!x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\
              x1 <> PosInf /\ y1 <> PosInf /\ x1 < x2 /\ y1 < y2
              ==> x1 * y1 < x2 * y2``,
  RW_TAC std_ss []
  ++ `0 < x2 /\ 0 < y2` by METIS_TAC [let_trans]
  ++ Cases_on `x1` ++ Cases_on `y1`
  ++ Cases_on `x2` ++ Cases_on `y2`
  ++ FULL_SIMP_TAC real_ss [extreal_lt_eq,extreal_le_def,extreal_mul_def,le_infty,lt_infty,extreal_of_num_def,extreal_not_infty,REAL_LT_MUL2,real_lte]
  ++ METIS_TAC [extreal_not_infty,lt_infty]);

val abs_pos = store_thm
 ("abs_pos",``!x. 0 <= abs x``,
  Cases ++ RW_TAC std_ss [extreal_abs_def,ABS_POS,extreal_le_def,extreal_of_num_def,le_infty]);

val abs_refl = store_thm
 ("abs_refl",``!x. (abs x = x) = (0 <= x)``,
  Cases ++ RW_TAC std_ss [extreal_abs_def,le_infty,extreal_of_num_def,extreal_le_def,ABS_REFL]);

val abs_bounds = store_thm
  ("abs_bounds",``!x k. abs x <= k <=> -k <= x /\ x <= k``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_abs_def,extreal_le_def,lt_infty,
                    le_infty,extreal_ainv_def,ABS_BOUNDS]);

val abs_bounds_lt = store_thm
  ("abs_bounds_lt",``!x k. abs x < k <=> -k < x /\ x < k``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_abs_def,extreal_lt_eq,
                    lt_infty,le_infty,extreal_ainv_def]
  ++ REAL_ARITH_TAC);

(***************)
(*   Addition  *)
(***************)

val add_comm = store_thm
  ("add_comm",``!x y:extreal. x + y = y + x``,
  Cases ++ Cases_on `y`
  ++ RW_TAC std_ss [extreal_add_def,REAL_ADD_COMM]);

val add_assoc = store_thm
  ("add_assoc",``!x y z. x + (y + z) = x + y + z``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def,REAL_ADD_ASSOC]);

val add_not_infty = store_thm
  ("add_not_infty",
   ``!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf) /\
           (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)``,
  Cases ++ Cases ++ RW_TAC std_ss [extreal_add_def]);

val add_rzero = store_thm
  ("add_rzero",
   ``!x. x + 0 = x``,
  Cases ++ METIS_TAC [extreal_add_def,extreal_of_num_def,REAL_ADD_RID]);

val add_lzero = store_thm
  ("add_lzero",
   ``!x. 0 + x = x``,
  Cases ++ METIS_TAC [extreal_add_def,extreal_of_num_def,REAL_ADD_LID]);

val add_infty = store_thm
  ("add_infty",``(!x. (x + PosInf = PosInf) /\
                 (PosInf + x = PosInf)) /\
                 (!x. x <> PosInf ==> ((x + NegInf = NegInf) /\
                 (NegInf + x = NegInf)))``,
  RW_TAC std_ss [] ++ Cases_on `x`
  ++ RW_TAC std_ss [extreal_add_def,extreal_not_infty]);

val EXTREAL_EQ_LADD = store_thm
  ("EXTREAL_EQ_LADD",``!x y z. x <> NegInf /\ x <> PosInf
           ==> ((x + y = x + z) = (y = z))``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_add_def,REAL_EQ_LADD]);

(*********************)
(*   Substraction    *)
(*********************)

val sub_rzero = store_thm
  ("sub_rzero", ``!x. x - 0 = x``,
  Cases ++ METIS_TAC [extreal_sub_def,extreal_of_num_def,REAL_SUB_RZERO]);

val sub_lzero = store_thm
  ("sub_lzero", ``!x. 0 - x = -x``,
  Cases
  ++ METIS_TAC [extreal_ainv_def,extreal_sub_def,
                extreal_of_num_def,REAL_SUB_LZERO]);

val sub_le_imp = store_thm
  ("sub_le_imp",``!x y z. x <> NegInf /\ x <> PosInf /\ y <= z + x
  		       ==> y - x <= z``,
   REPEAT Cases
   ++ RW_TAC std_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     REAL_LE_SUB_RADD]);

val sub_le_imp2 = store_thm
  ("sub_le_imp2",``!x y z. y <> NegInf /\ y <> PosInf /\ y <= z + x
                     ==> y - x <= z``,
   REPEAT Cases
   ++ RW_TAC std_ss [extreal_le_def,extreal_add_def,
                     extreal_sub_def,REAL_LE_SUB_RADD]);

val le_sub_imp = store_thm
  ("le_sub_imp",``!x y z. y + x <= z ==> y <= z - x``,
  REPEAT Cases
   ++ RW_TAC std_ss [extreal_le_def,extreal_add_def,
                     extreal_sub_def,REAL_LE_SUB_LADD]);

val lt_sub_imp = store_thm
  ("lt_sub_imp",``!x y z. y + x < z ==> y < z - x``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,
                    extreal_add_def,extreal_sub_def]
  ++ METIS_TAC [real_lt,REAL_LT_ADD_SUB]);

val sub_lt_imp = store_thm
  ("sub_lt_imp",
   ``!x y z. x <> NegInf /\ x <> PosInf /\ y < z + x ==> y - x < z``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,extreal_sub_def]
  ++ METIS_TAC [real_lt,REAL_LT_SUB_RADD]);

val sub_lt_imp2 = store_thm
  ("sub_lt_imp2",
   ``!x y z. z <> NegInf /\ z <> PosInf /\ y < z + x ==> y - x < z``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,extreal_sub_def]
  ++ METIS_TAC [real_lt,REAL_LT_SUB_RADD]);

val sub_zero_lt = store_thm
  ("sub_zero_lt", ``!x y. x < y ==> 0 < y - x``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     extreal_lt_eq,lt_infty,extreal_of_num_def,
                     extreal_not_infty,REAL_SUB_LT]);

val sub_zero_lt2 = store_thm
  ("sub_zero_lt2", ``!x y. x <> NegInf /\ x <> PosInf /\ 0 < y - x ==> x < y``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     extreal_lt_eq,lt_infty,extreal_of_num_def,
                     extreal_not_infty,REAL_SUB_LT]);

val sub_lt_zero = store_thm
("sub_lt_zero", ``!x y. x < y ==> x - y < 0``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     extreal_lt_eq,lt_infty,extreal_of_num_def,
                     extreal_not_infty,REAL_LT_SUB_RADD]);

val sub_lt_zero2 = store_thm
("sub_lt_zero2", ``!x y. y <> NegInf /\ y <> PosInf /\ x - y < 0
                      ==> x < y``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     extreal_lt_eq,lt_infty,extreal_of_num_def,
                     extreal_not_infty,REAL_LT_SUB_RADD]);

val sub_zero_le = store_thm
("sub_zero_le", ``!x y. x <= y = 0 <= y - x``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     lt_infty,extreal_of_num_def,extreal_not_infty,REAL_SUB_LE]);

val sub_le_zero = store_thm
("sub_le_zero", ``!x y. y <> NegInf /\ y <> PosInf
                    ==> (x <= y = x - y <= 0)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,
                     lt_infty,extreal_of_num_def,extreal_not_infty,REAL_LE_SUB_RADD]);

val le_sub_eq = store_thm
  ("le_sub_eq",``!x y z. x <> NegInf /\ x <> PosInf  ==>
       (y <= z - x = y + x <= z)``,
   METIS_TAC [le_sub_imp, sub_lt_imp, extreal_lt_def]);

val le_sub_eq2 = store_thm
 ("le_sub_eq2",``!x y z. z <> NegInf /\ z <> PosInf /\ x <> NegInf /\ y <> NegInf ==>
       (y <= z - x = y + x <= z)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,lt_infty,
                     extreal_of_num_def,extreal_not_infty,REAL_LE_SUB_LADD]);

val sub_le_eq = store_thm
  ("sub_le_eq",``!x y z. x <> NegInf /\ x <> PosInf
                  ==> (y - x <= z = y <= z + x)``,
   METIS_TAC [sub_le_imp, lt_sub_imp, extreal_lt_def]);

val sub_le_eq2 = store_thm
 ("sub_le_eq2",``!x y z. y <> NegInf /\ y <> PosInf /\ x <> NegInf /\ z <> NegInf
                   ==> (y - x <= z = y <= z + x)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def,lt_infty,
                     extreal_of_num_def,extreal_not_infty,REAL_LE_SUB_RADD]);

val sub_le_switch = store_thm
  ("sub_le_switch",``!x y z. x <> NegInf /\ x <> PosInf /\ z <> NegInf /\ z <> PosInf
                           ==> (y - x <= z = y - z <= x)``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_sub_def,extreal_le_def,le_infty,lt_infty]
  ++ REAL_ARITH_TAC);

val sub_le_switch2 = store_thm
  ("sub_le_switch2",``!x y z. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf
                            ==> (y - x <= z = y - z <= x)``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_sub_def,extreal_le_def,le_infty,lt_infty]
  ++ REAL_ARITH_TAC);

val lt_sub = store_thm
  ("lt_sub",``!x y z. z <> NegInf /\ z <> PosInf
                 ==> (y + x < z = y < z - x)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,
                   extreal_sub_def,le_infty]
 ++ METIS_TAC [REAL_LE_SUB_RADD]);

val sub_add2 = store_thm
  ("sub_add2",``!x y. x <> NegInf /\ x <> PosInf
                  ==> (x + (y - x) = y)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_le_def,extreal_add_def,
                    extreal_sub_def,REAL_SUB_ADD2]);

val add_sub = store_thm
  ("add_sub",``!x y. y <> NegInf /\ y <> PosInf
                 ==> (x + y - y = x)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,
                   extreal_sub_def,REAL_ADD_SUB_ALT]);

val add_sub2 = store_thm
  ("add_sub2",``!x y. y <> NegInf /\ y <> PosInf
                  ==> (y + x - y = x)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,
                   extreal_sub_def,REAL_ADD_SUB]);

val sub_add = store_thm
  ("sub_add",``!x y. y <> NegInf /\ y <> PosInf
                ==> ((x - y) + y = x)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_lt_def,extreal_le_def,extreal_add_def,
                   extreal_sub_def,REAL_SUB_ADD]);

val extreal_sub_add = store_thm
  ("extreal_sub_add",``!x y. (x - y = x + -y)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_ainv_def,extreal_sub_def,
                   extreal_add_def,real_sub]);

val sub_0 = store_thm
  ("sub_0",``!x y. (x - y = 0) ==> (x = y)``,
 REPEAT Cases
 ++ RW_TAC std_ss [extreal_sub_def,num_not_infty,
                   REAL_SUB_0,extreal_of_num_def,extreal_11]);

val neg_neg = store_thm
  ("neg_neg",``!x. --x = x``,
 Cases ++ RW_TAC std_ss [extreal_ainv_def,REAL_NEG_NEG]);

val neg_0 = store_thm
  ("neg_0",``-0 = 0``,
 RW_TAC real_ss [extreal_ainv_def,extreal_of_num_def]);

val neg_eq0 = store_thm
  ("neg_eq0", ``!x. (-x = 0) <=> (x = 0)``,
  Cases ++ RW_TAC std_ss [extreal_ainv_def,
                         extreal_of_num_def,REAL_NEG_EQ0]);

val eq_neg = store_thm
  ("eq_neg", ``!x y. (-x = -y) <=> (x = y)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_ainv_def,REAL_EQ_NEG]);

val neg_minus1 = store_thm
  ("neg_minus1",``!x. -x = -1 * x``,
  Cases ++ RW_TAC real_ss [extreal_ainv_def,extreal_of_num_def,extreal_mul_def]);

val sub_rneg = store_thm
  ("sub_rneg",``!x y. x - - y = x + y``,
  REPEAT Cases ++ RW_TAC std_ss [extreal_sub_def,extreal_add_def,extreal_ainv_def,REAL_SUB_RNEG]);

val sub_lneg = store_thm
  ("sub_lneg",``!x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==> (-x - y = -(x + y))``,
 REPEAT Cases ++ RW_TAC std_ss [extreal_sub_def,extreal_add_def,extreal_ainv_def,REAL_SUB_LNEG]);

val neg_sub = store_thm
  ("neg_sub",``!x y. (x <> NegInf /\ x <> PosInf) \/ (y <> NegInf /\ y <> PosInf) ==> (-(x - y) = y - x)``,
  REPEAT Cases ++ RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB]);

val sub_not_infty = store_thm
  ("sub_not_infty",
   ``!x y. (x <> NegInf /\ y <> PosInf ==> x - y <> NegInf) /\
           (x <> PosInf /\ y <> NegInf ==> x - y <> PosInf)``,
  REPEAT Cases ++ RW_TAC std_ss [extreal_sub_def]);

val le_lsub_imp = store_thm
  ("le_lsub_imp",``!x y z. y <= z ==> x - z <= x - y``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl]
  ++ METIS_TAC [real_sub,REAL_LE_ADD2,REAL_LE_NEG,REAL_LE_REFL]);

val eq_sub_ladd_normal = store_thm
  ("eq_sub_ladd_normal",``!x y z. (x = y - Normal z) <=> (x + Normal z = y)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def,REAL_EQ_SUB_LADD]);

val eq_sub_radd = store_thm
  ("eq_sub_radd",``!x y z. y <> NegInf /\ y <> PosInf ==> ((x - y = z) <=> (x = z + y))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def,REAL_EQ_SUB_RADD]);

val eq_sub_ladd = store_thm
  ("eq_sub_ladd",``!x y z. z <> NegInf /\ z <> PosInf ==> ((x = y - z) <=> (x + z = y))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def,REAL_EQ_SUB_LADD]);

val eq_sub_switch = store_thm
  ("eq_sub_switch",``!x y z. (x = Normal z - y) <=> (y = Normal z - x)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_le_def,extreal_sub_def,le_infty,le_refl,extreal_add_def]
  ++ REAL_ARITH_TAC);

val eq_add_sub_switch = store_thm
  ("eq_add_sub_switch",``!a b c d.  b <> NegInf /\ b <> PosInf /\  c <> NegInf /\ c <> PosInf ==> ((a + b = c + d) <=> (a - c = d - b))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def]
  ++ REAL_ARITH_TAC);

val sub_refl = store_thm
  ("sub_refl",``!x. (x <> NegInf) /\ (x <> PosInf) ==> (x - x = 0)``,
  Cases ++ RW_TAC real_ss [extreal_sub_def,extreal_of_num_def]);

(*********************)
(*   Multiplication  *)
(*********************)

val mul_comm = store_thm
("mul_comm",``!x y:extreal. x * y = y * x``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_mul_def,REAL_MUL_COMM]);

val mul_assoc = store_thm
("mul_assoc",``!x y z:extreal. x * (y * z) = x * y * z``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC real_ss [extreal_mul_def,REAL_MUL_ASSOC,REAL_MUL_LZERO,
                     REAL_MUL_RZERO,REAL_ENTIRE,REAL_LT_LMUL_0,REAL_POS_NZ,DE_MORGAN_THM]
  ++ FULL_SIMP_TAC real_ss [DE_MORGAN_THM,REAL_NOT_LT,REAL_LT_LMUL_0,GSYM REAL_LT_LE]
  ++ METIS_TAC [REAL_LT_LMUL_0_NEG, REAL_LT_RMUL_0_NEG, REAL_LT_RMUL_NEG_0,
                REAL_LT_LE,REAL_LT_GT, REAL_ENTIRE,REAL_LT_LMUL_NEG_0,
                REAL_LT_LMUL_NEG_0_NEG,REAL_LT_RMUL_0, REAL_LT_LMUL_0,
                REAL_LT_RMUL_NEG_0_NEG]);

val mul_not_infty = store_thm
  ("mul_not_infty",
   ``(!c y. 0 <= c /\ y <> NegInf ==> Normal (c) * y <> NegInf) /\
     (!c y. 0 <= c /\ y <> PosInf ==> Normal (c) * y <> PosInf) /\
     (!c y. c <= 0 /\ y <> NegInf ==> Normal (c) * y <> PosInf) /\
     (!c y. c <= 0 /\ y <> PosInf ==> Normal (c) * y <> NegInf)``,
  RW_TAC std_ss [] ++ Cases_on `y`
  ++ RW_TAC std_ss [extreal_mul_def,extreal_le_def]
  ++ METIS_TAC [real_lte,REAL_LE_ANTISYM]);

val mul_not_infty2 = store_thm
  ("mul_not_infty2",
   ``!x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf
      ==> (x * y <> NegInf) /\ (x * y <> PosInf)``,
  REPEAT Cases ++ RW_TAC std_ss [extreal_mul_def,extreal_not_infty]);

val add_ldistrib_pos = store_thm
  ("add_ldistrib_pos",
   ``!x y z. 0 <= y /\ 0 <= z ==> (x * (y + z) = x * y + x * z)``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_mul_def,extreal_le_def,
                     extreal_of_num_def,real_lt,REAL_LT_ANTISYM,
                     REAL_LE_ANTISYM,REAL_ADD_LID,REAL_ADD_RID,REAL_LT_LE]
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt,GSYM real_lte]
  ++ METIS_TAC [REAL_LE_ANTISYM,REAL_LT_ADD,REAL_LT_IMP_LE,REAL_LT_IMP_NE,
                REAL_LT_LE,REAL_ADD_LDISTRIB]);
val add_ldistrib_neg = store_thm
  ("add_ldistrib_neg",
   ``!x y z. y <= 0 /\ z <= 0 ==> (x * (y + z) = x * y + x * z)``,
  Cases ++ Cases ++ Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_mul_def,extreal_le_def,
                     extreal_of_num_def,real_lt,REAL_LT_ANTISYM,
                     REAL_LE_ANTISYM,REAL_ADD_LID,REAL_ADD_RID,REAL_LT_LE]
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt,GSYM real_lte,REAL_ADD_LDISTRIB]
  ++ Cases_on `0 < r` >> RW_TAC std_ss []
  ++ Cases_on `0 < r'` >> RW_TAC std_ss []
  ++ `r < 0 /\ r' < 0` by METIS_TAC [real_lte,REAL_LT_LE]
  ++ METIS_TAC [REAL_LT_ADD2,REAL_ADD_LID,REAL_LT_IMP_NE,REAL_LT_ANTISYM]);

val add_ldistrib_normal = store_thm
  ("add_ldistrib_normal",
   ``!x y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf)
         ==> (Normal x * (y + z) = Normal x * y + Normal x * z)``,
  RW_TAC std_ss [] ++ Cases_on `y` ++ Cases_on `z`
  ++ RW_TAC std_ss [extreal_add_def]
  ++ Cases_on `x=0`
  >> METIS_TAC [extreal_of_num_def,mul_lzero,add_lzero]
  ++ RW_TAC std_ss [extreal_mul_def,extreal_add_def,REAL_ADD_LDISTRIB]);

val add_ldistrib_normal2 = store_thm
  ("add_ldistrib_normal2",
   ``!x y z. 0 <= x ==> (Normal x * (y + z) = Normal x * y + Normal x * z)``,
  STRIP_TAC ++ REPEAT Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_mul_def,REAL_ADD_LDISTRIB]
  ++ METIS_TAC [REAL_LE_LT,real_lte,real_lt]);

val add_rdistrib_normal = store_thm
  ("add_rdistrib_normal",
   ``!x y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf) ==>
          ((y + z) * Normal x = y * Normal x + z * Normal x)``,
  RW_TAC std_ss [] ++ Cases_on `y` ++ Cases_on `z`
  ++ RW_TAC std_ss [extreal_add_def]
  ++ Cases_on `x=0`
  >> METIS_TAC [extreal_of_num_def,mul_rzero,add_rzero]
  ++ RW_TAC std_ss [extreal_mul_def,extreal_add_def,REAL_ADD_RDISTRIB]);

val add_rdistrib_normal2 = store_thm
  ("add_rdistrib_normal2",
   ``!x y z. 0 <= x ==> ((y + z) * Normal x = y * Normal x + z * Normal x)``,
  STRIP_TAC ++ REPEAT Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_mul_def,REAL_ADD_RDISTRIB]
  ++ METIS_TAC [REAL_LE_LT,real_lte,real_lt]);

val add_ldistrib = store_thm
  ("add_ldistrib",
   ``!x y z. (0 <= y /\ 0 <= z) \/ (y <= 0 /\ z <= 0)
    ==> (x * (y + z) = x * y + x * z)``,
 METIS_TAC [add_ldistrib_pos,add_ldistrib_neg]);

val add_rdistrib = store_thm
  ("add_rdistrib",
   ``!x y z. (0 <= y /\ 0 <= z) \/ (y <= 0 /\ z <= 0)
    ==> ((y + z) * x = y * x + z * x)``,
  METIS_TAC [add_ldistrib, mul_comm]);

val mul_lneg = store_thm
  ("mul_lneg", ``!x y. -x * y = -(x * y)``,
  Cases ++ Cases
  ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,REAL_MUL_LNEG,REAL_NEG_EQ0]
  ++ METIS_TAC [REAL_NEG_GT0,REAL_LT_REFL,REAL_LT_TRANS,real_lte,REAL_LE_ANTISYM]);

val mul_rneg = store_thm
  ("mul_rneg", ``!x y. x * -y = -(x * y)``,
  Cases ++ Cases
  ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,REAL_MUL_RNEG,REAL_NEG_EQ0]
  ++ METIS_TAC [REAL_NEG_GT0,REAL_LT_REFL,REAL_LT_TRANS,real_lte,REAL_LE_ANTISYM]);

val neg_mul2 = store_thm
  ("neg_mul2", ``!x y. -x * -y = x * y``,
  REPEAT Cases ++ RW_TAC real_ss [extreal_mul_def,extreal_ainv_def,REAL_NEG_EQ0]
  ++ METIS_TAC [REAL_LT_NEG,REAL_NEG_0,REAL_LT_ANTISYM,real_lt,REAL_LE_ANTISYM]);

val add2_sub2 = store_thm
  ("add2_sub2", ``!a b c d. (b <> PosInf /\ d <> PosInf) \/ (b <> NegInf /\ d <> NegInf)
     ==> (a - b + (c - d) = (a + c - (b + d)))``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def]
  ++ REAL_ARITH_TAC);

val sub_ldistrib = store_thm
  ("sub_ldistrib", ``!x y z. x <> NegInf /\ x <> PosInf /\
                             y <> NegInf /\ y <> PosInf /\
                             z <> NegInf /\ z <> PosInf
                       ==> (x * (y - z) = x * y - x * z)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_sub_def,
                     extreal_mul_def,REAL_SUB_LDISTRIB]);

val sub_rdistrib = store_thm
  ("sub_rdistrib", ``!x y z. x <> NegInf /\ x <> PosInf /\
                             y <> NegInf /\ y <> PosInf /\
                             z <> NegInf /\ z <> PosInf
                      ==> ((x - y) * z = x * z - y * z)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_sub_def,extreal_mul_def,REAL_SUB_RDISTRIB]);

(*********************)
(*   Division        *)
(*********************)

val extreal_div_eq = store_thm
("extreal_div_eq",``!x y. Normal x / Normal y = Normal (x / y)``,
  REPEAT Cases
  ++ RW_TAC std_ss [extreal_div_def,extreal_inv_def,extreal_mul_def,real_div]);

val inv_one = store_thm
("inv_one",``inv 1 = 1``,
  RW_TAC std_ss [extreal_inv_def,extreal_of_num_def,REAL_10,REAL_INV1]);

val inv_1over = store_thm
("inv_1over",``!x. inv x = 1 / x``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_inv_def,extreal_div_def,extreal_mul_def,
                     extreal_of_num_def,REAL_10,REAL_INV1]);

val div_one = store_thm
("div_one",``!x. x / 1 = x``,
   RW_TAC std_ss [extreal_div_def,mul_rone,inv_one]);

val inv_pos = store_thm
  ("inv_pos",``!x. 0 < x /\ x <> PosInf ==> (0 < 1 / x)``,
  Cases
  ++ RW_TAC real_ss [extreal_div_def,extreal_inv_def,extreal_of_num_def,extreal_lt_def,
                     extreal_mul_def,extreal_le_def,lt_infty,le_infty]
  ++ FULL_SIMP_TAC real_ss [real_lte]);

val rinv_uniq = store_thm
 ("rinv_uniq",``!x y. (x * y = 1) ==> (y = inv x)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_inv_def,extreal_mul_def,
                     extreal_of_num_def,REAL_RINV_UNIQ]);

val linv_uniq = store_thm
 ("linv_uniq",``!x y. (x * y = 1) ==> (x = inv y)``,
  RW_TAC std_ss [rinv_uniq,mul_comm]);

val le_rdiv = store_thm
  ("le_rdiv",``!x y z. 0 < x ==> (y * Normal x <= z = y <= z / Normal x)``,
  STRIP_TAC ++ REPEAT Cases
  ++ RW_TAC std_ss [extreal_mul_def,extreal_div_def,extreal_inv_def,extreal_le_def,
                    le_infty,extreal_of_num_def,extreal_not_infty,REAL_LT_REFL,REAL_INV_EQ_0,
                    REAL_INV_POS]
  ++ METIS_TAC [REAL_LE_RDIV_EQ,real_div]);

val le_ldiv = store_thm
  ("le_ldiv",``!x y z. 0 < x ==> (y <= z * Normal x = y / Normal x <= z)``,
  STRIP_TAC ++ REPEAT Cases
  ++ RW_TAC std_ss [extreal_mul_def,extreal_div_def,extreal_inv_def,extreal_le_def,
                    le_infty,extreal_of_num_def,extreal_not_infty,REAL_LT_REFL,REAL_INV_EQ_0,
                    REAL_INV_POS]
  ++ METIS_TAC [REAL_LE_LDIV_EQ,real_div]);

val lt_rdiv = store_thm
  ("lt_rdiv", ``!x y z. 0 < z ==> (x < y / Normal z <=> x * Normal z < y)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [REAL_INV_EQ_0,REAL_INV_POS,extreal_lt_eq,REAL_LT_RDIV_EQ,GSYM real_div,
                    REAL_LT_REFL,lt_refl,lt_infty,le_infty,extreal_div_def,extreal_inv_def,
                    extreal_div_eq,extreal_mul_def]);

val lt_ldiv = store_thm
  ("lt_ldiv",``!x y z. 0 < z ==> (x / Normal z < y = x < y * Normal z)``,
  Cases ++ Cases
  ++ RW_TAC std_ss [REAL_INV_EQ_0,REAL_INV_POS,extreal_lt_eq,REAL_LT_LDIV_EQ,GSYM real_div,
                    REAL_LT_REFL,lt_refl,lt_infty,le_infty,extreal_div_def,extreal_inv_def,
                    extreal_div_eq,extreal_mul_def]);

val lt_rdiv_neg = store_thm
  ("lt_rdiv_neg", ``!x y z. z < 0 ==> (y / Normal z < x <=> x * Normal z < y)``,
  (Cases ++ Cases ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [REAL_INV_POS,REAL_LE_LT,GSYM real_lte,REAL_INV_EQ_0,REAL_INV_POS,
                    extreal_lt_eq,REAL_LT_RDIV_EQ_NEG,GSYM real_div,REAL_LT_REFL,lt_refl,
                    lt_infty,le_infty,extreal_div_def,extreal_inv_def,extreal_div_eq,
                    extreal_mul_def,REAL_LT_REFL])
  ++ METIS_TAC [REAL_LT_REFL,REAL_LT_ANTISYM,real_lte,REAL_LT_IMP_LE,REAL_LT_INV_EQ]);

val div_add = store_thm
  ("div_add",``!x y z.  x <> NegInf /\ y <> NegInf /\ z <> 0
                     ==> (x / z + y / z = (x + y) / z)``,
  REPEAT Cases
  ++ RW_TAC real_ss [extreal_add_def,extreal_div_def,extreal_mul_def,extreal_inv_def,
                     extreal_of_num_def]
  ++ RW_TAC real_ss [extreal_add_def,REAL_RDISTRIB]);

val le_inv = store_thm
 ("le_inv",``!x. 0 <= x ==> 0 <= inv x``,
  Cases
  ++ RW_TAC real_ss [extreal_inv_def,extreal_of_num_def,extreal_le_def,
                     le_infty,REAL_LE_INV]);

(***************************)
(*         x pow n         *)
(***************************)

val pow_0 = store_thm
  ("pow_0",``!x. x pow 0 = 1``,
  Cases ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,pow]);

val pow_1 = store_thm
  ("pow_1",``!x. x pow 1 = x``,
  Cases ++ RW_TAC std_ss [extreal_pow_def,POW_1]);

val pow_2 = store_thm
  ("pow_2",``!x. x pow 2 = x * x``,
  Cases ++ RW_TAC std_ss [extreal_pow_def,extreal_mul_def,POW_2]);

val pow_zero = store_thm
  ("pow_zero",``!n x. (x pow (SUC n) = 0) = (x = 0)``,
  STRIP_TAC ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,POW_ZERO_EQ]);

val pow_zero_imp = store_thm
 ("pow_zero_imp",``!n x. (x pow n = 0) ==> (x = 0)``,
  STRIP_TAC ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,REAL_LT_01,REAL_LT_IMP_NE]
  ++ METIS_TAC [POW_ZERO]);

val le_pow2 = store_thm
  ("le_pow2",``!x. 0 <= x pow 2``,
  Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,REAL_LE_POW2]);

val pow_pos_le = store_thm
  ("pow_pos_le",``!x. 0 <= x ==> !n. 0 <= x pow n``,
  Cases ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,POW_POS]
  ++ METIS_TAC [le_infty,le_01,extreal_of_num_def]);

val pow_pos_lt = store_thm
  ("pow_pos_lt",``!x n. 0 < x ==> 0 < x pow n``,
  Cases ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,
                    extreal_le_def,extreal_lt_eq,POW_POS_LT,REAL_LT_01,
                    lt_infty,extreal_not_infty]
  ++ METIS_TAC [pow,REAL_LT_01]);

val pow_le = store_thm
  ("pow_le",``!n x y. 0 <= x /\ x <= y ==> x pow n <= y pow n``,
  STRIP_TAC ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,POW_LE,
                    lt_infty,le_infty,extreal_not_infty,REAL_LE_REFL,pow]);

val pow_lt = store_thm
  ("pow_lt",``!n x y. 0 <= x /\ x < y ==> x pow SUC n < y pow SUC n``,
  STRIP_TAC ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,REAL_POW_LT2,
                    lt_infty,le_infty,extreal_not_infty,extreal_lt_eq]);

val pow_lt2 = store_thm
  ("pow_lt2",``!n x y. n <> 0 /\ 0 <= x /\ x < y
                 ==> x pow n < y pow n``,
  STRIP_TAC ++ Cases ++ Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,REAL_POW_LT2,
                    lt_infty,le_infty,extreal_not_infty,extreal_lt_eq]);

val pow_le_mono = store_thm
  ("pow_le_mono",``!x n m. 1 <= x /\ n <= m ==> x pow n <= x pow m``,
  Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,
                    lt_infty,le_infty,extreal_not_infty,REAL_LE_REFL]
  ++ Cases_on `n = m` >> RW_TAC std_ss [REAL_LE_REFL]
  ++ `n < m` by METIS_TAC [LESS_OR_EQ]
  ++ `?p. m = p + n` by METIS_TAC [LESS_ADD]
  ++ FULL_SIMP_TAC std_ss []
  ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
  ++ Induct_on `p` >> RW_TAC real_ss [REAL_LE_REFL]
  ++ RW_TAC real_ss [GSYM ADD_SUC,pow]
  ++ `0 <= r` by METIS_TAC [REAL_LE_01,REAL_LE_TRANS]
  ++ `0 <= r pow n` by METIS_TAC [POW_POS]
  ++ ONCE_REWRITE_TAC [ADD_COMM]
  ++ (MP_TAC o Q.SPECL [`1:real`,`r`,`r pow n`,`r pow (p + n)`]) REAL_LE_MUL2
  ++ RW_TAC real_ss []);

val pow_pos_even = store_thm
  ("pow_pos_even",``!x. x < 0 ==> ((0 < x pow n) = (EVEN n))``,
  Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_not_infty,
                    le_infty,lt_infty,extreal_lt_eq,REAL_LT_01,POW_POS_EVEN]);

val pow_neg_odd = store_thm
  ("pow_neg_odd",``!x. x < 0 ==> ((x pow n < 0) = (ODD n))``,
  Cases
  ++ RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_not_infty,
                    le_infty,lt_infty,extreal_lt_eq,extreal_le_def,REAL_LT_01,EVEN_ODD,
                    extreal_lt_def,extreal_le_def,REAL_LE_01,POW_NEG_ODD,GSYM real_lt]);

val add_pow2 = store_thm
  ("add_pow2",``!x y.
       ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)``,
  Cases ++ Cases
  ++ RW_TAC real_ss [extreal_pow_def,extreal_mul_def,extreal_add_def,extreal_of_num_def,pow_2]
  ++ RW_TAC real_ss [REAL_ADD_LDISTRIB,REAL_ADD_RDISTRIB,REAL_ADD_ASSOC,POW_2,GSYM REAL_DOUBLE]
  ++ Suff `r * r' + r' * r + r' * r' = r' * r' + r * r' + r * r'` >> METIS_TAC [REAL_EQ_LADD,REAL_ADD_ASSOC]
  ++ METIS_TAC [REAL_EQ_LADD,REAL_ADD_COMM,REAL_EQ_RADD,REAL_ADD_ASSOC,REAL_MUL_COMM]);

val pow_add = store_thm
  ("pow_add",``!x n m. x pow (n + m) = x pow n * x pow m``,
  Cases
  ++ RW_TAC real_ss [extreal_pow_def,POW_ADD,extreal_of_num_def,
                     extreal_mul_def,mul_rone,mul_lone]
  ++ METIS_TAC  [ADD_CLAUSES,EVEN_ADD]);

val pow_mul = store_thm
  ("pow_mul",``!n x y. (x * y) pow n = x pow n * y pow n``,
  Cases >> RW_TAC std_ss [pow_0,mul_lone]
  ++ Cases ++ Cases
  ++ RW_TAC real_ss [extreal_mul_def,extreal_pow_def,pow_zero,
                     POW_ZERO_EQ,POW_POS_LT,POW_MUL]
  ++ FULL_SIMP_TAC real_ss [GSYM real_lte]
  ++ METIS_TAC [POW_POS_EVEN,POW_NEG_ODD,REAL_LT_LE,POW_POS_LT,
                real_lt,POW_ZERO_EQ,EVEN_ODD]);

val pow_minus1 = store_thm
  ("pow_minus1",``!n. -1 pow (2 * n) = 1``,
  RW_TAC std_ss [extreal_of_num_def,extreal_ainv_def,extreal_pow_def,POW_MINUS1]);

val pow_not_infty = store_thm
  ("pow_not_infty",``!n x. x <> NegInf /\ x <> PosInf
                ==> x pow n <> NegInf /\ x pow n <> PosInf``,
  Cases
  ++ METIS_TAC [extreal_pow_def,extreal_not_infty,extreal_cases]);

(***************************)
(*         SQRT            *)
(***************************)

val sqrt_pos_le = store_thm
  ("sqrt_pos_le",``!x. 0 <= x ==> 0 <= sqrt x``,
  Cases ++ RW_TAC std_ss [extreal_sqrt_def,extreal_of_num_def,extreal_le_def,SQRT_POS_LE]);

val sqrt_pos_lt = store_thm
  ("sqrt_pos_lt",``!x. 0 < x ==> 0 < sqrt x``,
  Cases
  ++ RW_TAC std_ss [extreal_sqrt_def,extreal_of_num_def,extreal_le_def,extreal_lt_eq,
                    lt_infty,SQRT_POS_LT]);

val pow2_sqrt = store_thm
  ("pow2_sqrt",``!x. 0 <= x ==> (sqrt (x pow 2) = x)``,
  Cases
  ++ RW_TAC real_ss [extreal_sqrt_def,extreal_pow_def,POW_2_SQRT,extreal_of_num_def,
                     extreal_le_def]);

val sqrt_pow2 = store_thm
  ("sqrt_pow2",``!x. (sqrt x pow 2 = x) <=> 0 <= x``,
  Cases
  ++ RW_TAC real_ss [extreal_sqrt_def,extreal_pow_def,SQRT_POW2,
                     extreal_of_num_def,extreal_le_def]
  ++ METIS_TAC [le_pow2,lt_infty,extreal_of_num_def,
                extreal_not_infty,lte_trans]);

val sqrt_mono_le = store_thm
  ("sqrt_mono_le",``!x y. 0 <= x /\ x <= y ==> sqrt x <= sqrt y``,
  Cases ++ Cases
  ++ RW_TAC real_ss [SQRT_MONO_LE,extreal_sqrt_def,extreal_pow_def,POW_2_SQRT,
                     extreal_of_num_def,extreal_le_def,le_infty,extreal_not_infty]);

(***************************)
(*         Log             *)
(***************************)
val logr_not_infty = store_thm
  ("logr_not_infty",``!x b. (x <> NegInf /\ x <> PosInf)
           ==> logr b x <> NegInf /\ logr b x <> PosInf``,
  Cases ++ RW_TAC std_ss [extreal_logr_def,extreal_not_infty]);

(***************************)
(*         Various         *)
(***************************)

val half_between = store_thm
  ("half_between",
   ``(0 < 1/2 /\ 1/2 < 1) /\ (0 <= 1/2 /\ 1/2 <= 1)``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   ++ CONJ_TAC >> PROVE_TAC [lt_imp_le]
   ++ RW_TAC real_ss [extreal_div_def,extreal_inv_def, mul_lone,
                      extreal_lt_def, extreal_le_def, extreal_of_num_def,
                      extreal_not_infty,GSYM real_lt,REAL_INV_1OVER]);

val thirds_between = store_thm
  ("thirds_between",
   ``((0 < 1/3 /\ 1/3 < 1) /\ (0 < 2/3 /\ 2/3 < 1)) /\
     ((0 <= 1/3 /\ 1/3 <= 1) /\ (0 <= 2/3 /\ 2/3 <= 1))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   ++ CONJ_TAC >> PROVE_TAC [lt_imp_le]
   ++ RW_TAC real_ss [extreal_div_def,extreal_inv_def, mul_lone,
                      extreal_lt_def, extreal_le_def, extreal_of_num_def,
                      extreal_not_infty,GSYM real_lt,extreal_mul_def,REAL_INV_1OVER]);

val half_cancel = store_thm
  ("half_cancel",``2 * (1 / 2) = 1``,
   RW_TAC real_ss [extreal_of_num_def,extreal_mul_def,extreal_div_eq,
                   EVAL ``2 <> 0:real``,REAL_MUL_RINV,real_div]);

val third_cancel = store_thm
  ("third_cancel",``3 * (1 / 3) = 1``,
   RW_TAC real_ss [extreal_of_num_def,extreal_mul_def,extreal_div_eq,
                   EVAL ``3 <> 0:real``,REAL_MUL_RINV,real_div]);

val fourth_cancel = store_thm
  ("fourth_cancel",``4 * (1 / 4) = 1``,
   RW_TAC real_ss [extreal_of_num_def,extreal_mul_def,extreal_div_eq,
                   EVAL ``4 <> 0:real``,REAL_MUL_RINV,real_div]);

val quotient_normal = store_thm
  ("quotient_normal", ``!n m. &n / &m = Normal (&n / &m)``,
  RW_TAC std_ss [extreal_div_eq,extreal_of_num_def]);

val ext_mono_increasing_def = Define
   `ext_mono_increasing f = (!m n:num. m <= n ==> f m <= f n)`;

val ext_mono_increasing_suc = store_thm
  ("ext_mono_increasing_suc", ``!f. ext_mono_increasing f <=> !n. f n <= f (SUC n)``,
  RW_TAC std_ss [ext_mono_increasing_def]
  ++ EQ_TAC
  ++ RW_TAC real_ss []
  ++ Know `?d. n = m + d` >> PROVE_TAC [LESS_EQ_EXISTS]
  ++ RW_TAC std_ss []
  ++ Induct_on `d` >> RW_TAC std_ss [add_rzero,le_refl]
  ++ RW_TAC std_ss []
  ++ Q.PAT_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `m + d`)
  ++ METIS_TAC [le_trans,ADD_CLAUSES,LESS_EQ_ADD]);

val ext_mono_decreasing_def = Define
   `ext_mono_decreasing f = (!m n:num. m <= n ==> f n <= f m)`;

val ext_mono_decreasing_suc = store_thm
  ("ext_mono_decreasing_suc", ``!f. ext_mono_decreasing f <=> !n. f (SUC n) <= f n``,
  RW_TAC std_ss [ext_mono_decreasing_def]
  ++ EQ_TAC
  ++ RW_TAC real_ss []
  ++ Know `?d. n = m + d` >> PROVE_TAC [LESS_EQ_EXISTS]
  ++ RW_TAC std_ss []
  ++ Induct_on `d` >> RW_TAC std_ss [add_rzero,le_refl]
  ++ RW_TAC std_ss []
  ++ Q.PAT_ASSUM `!n. f (SUC n) <= f n` (MP_TAC o Q.SPEC `m + d`)
  ++ METIS_TAC [le_trans,ADD_CLAUSES,LESS_EQ_ADD]);

val _ = overload_on ("mono_increasing", Term `ext_mono_increasing`);
val _ = overload_on ("mono_decreasing", Term `ext_mono_decreasing`);

val EXTREAL_ARCH = store_thm
 ("EXTREAL_ARCH", ``!x. 0 < x ==> !y. y <> PosInf ==> ?n. y < &n * x``,
  Cases
  << [RW_TAC std_ss [lt_infty],
      RW_TAC std_ss [lt_infty] ++ Q.EXISTS_TAC `1` ++ RW_TAC std_ss [mul_lone,lt_infty],
      RW_TAC std_ss [lt_infty]
      ++ Cases_on `y = NegInf`
      >> (Q.EXISTS_TAC `1` ++ RW_TAC std_ss [mul_lone,lt_infty])
      ++ `?z. y = Normal z` by METIS_TAC [extreal_cases,lt_infty]
      ++ `0 < r` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
      ++ `?n. z < &n * r` by METIS_TAC [REAL_ARCH]
      ++ Q.EXISTS_TAC `n`
      ++ RW_TAC real_ss [extreal_lt_eq,REAL_LE_MUL,extreal_of_num_def,extreal_mul_def]]);

val SIMP_REAL_ARCH = store_thm
  ("SIMP_REAL_ARCH",
  ``!x:real. ?n. x <= &n``,
	REWRITE_TAC [REAL_LE_LT] THEN
	FULL_SIMP_TAC std_ss [EXISTS_OR_THM] THEN
	RW_TAC std_ss [] THEN
	DISJ1_TAC THEN
	MP_TAC (Q.SPEC `1` REAL_ARCH) THEN
	REWRITE_TAC [REAL_LT_01, REAL_MUL_RID] THEN
	RW_TAC std_ss []);

val SIMP_REAL_ARCH_NEG = store_thm
  ("SIMP_REAL_ARCH_NEG",
  ``!x:real. ?n. - &n <= x``,
  RW_TAC std_ss []
  ++ `?n. -x <= &n` by PROVE_TAC [SIMP_REAL_ARCH]
  ++ Q.EXISTS_TAC `n`
  ++ PROVE_TAC [REAL_LE_NEG,REAL_NEG_NEG]);

val SIMP_EXTREAL_ARCH = store_thm
 ("SIMP_EXTREAL_ARCH",
  ``!x. x <> PosInf ==> ?n. x <= &n``,
  Cases
  ++ RW_TAC std_ss [le_infty]
  ++ `?n. r <= &n` by RW_TAC std_ss [SIMP_REAL_ARCH]
  ++ Q.EXISTS_TAC `n`
  ++ RW_TAC real_ss [extreal_of_num_def,extreal_le_def]);

val REAL_ARCH_POW = store_thm
  ("REAL_ARCH_POW", ``!x:real. ?n. x < 2 pow n``,
  METIS_TAC [POW_2_LT,SIMP_REAL_ARCH,REAL_LET_TRANS]);

val EXTREAL_ARCH_POW = store_thm
  ("EXTREAL_ARCH_POW", ``!x. x <> PosInf ==> ?n. x < (2 pow n)``,
  Cases ++ RW_TAC std_ss [lt_infty,extreal_lt_eq,REAL_ARCH_POW,
                          extreal_pow_def,extreal_of_num_def]);

val EXTREAL_ARCH_POW_INV = store_thm
  ("EXTREAL_ARCH_POW_INV", ``!e. 0 < e ==> ?n. Normal ((1 / 2) pow n) < e``,
  Cases >> RW_TAC std_ss [lt_infty]
  >> METIS_TAC [lt_infty,extreal_not_infty]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
  ++  MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
  ++ RW_TAC std_ss [abs, REAL_HALF_BETWEEN, REAL_LT_IMP_LE, SEQ]
  ++ POP_ASSUM (MP_TAC o Q.SPEC `r`)
  ++ RW_TAC std_ss [REAL_SUB_RZERO, REAL_POW_LT,
                    REAL_HALF_BETWEEN,REAL_LT_IMP_LE,GREATER_EQ]
  ++ PROVE_TAC [LESS_EQ_REFL]);

val REAL_LE_MUL_EPSILON = store_thm
  ("REAL_LE_MUL_EPSILON",
   ``!x y:real. (!z. 0 < z /\ z < 1 ==> z * x <= y) ==>
		x <= y``,
    REPEAT STRIP_TAC
    ++ Cases_on `x = 0`
    >> (Q.PAT_ASSUM `!z. P z` (MP_TAC o Q.SPEC `1/2`)
        ++ RW_TAC real_ss [REAL_HALF_BETWEEN])
    ++ Cases_on `0 < x`
    >> (MATCH_MP_TAC REAL_LE_EPSILON
	++ RW_TAC std_ss [GSYM REAL_LE_SUB_RADD]
	++ Cases_on `e < x`
	>> (MATCH_MP_TAC REAL_LE_TRANS
            ++ Q.EXISTS_TAC `(1-(e/x))*x`
            ++ CONJ_TAC
            >> (RW_TAC real_ss [REAL_SUB_RDISTRIB]
                ++ METIS_TAC [REAL_DIV_RMUL, REAL_LE_REFL])
            ++ Q.PAT_ASSUM `!z. P z` MATCH_MP_TAC
            ++ RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_SUB_LADD,
                               REAL_LT_1, REAL_LT_IMP_LE])
	++ FULL_SIMP_TAC std_ss [REAL_NOT_LT]
        ++ MATCH_MP_TAC REAL_LE_TRANS
	++ Q.EXISTS_TAC `0`
	++ RW_TAC real_ss [REAL_LE_SUB_RADD]
	++ MATCH_MP_TAC REAL_LE_TRANS
	++ Q.EXISTS_TAC `(1/2)*x`
	++ RW_TAC real_ss [REAL_LE_MUL, REAL_LT_IMP_LE])
    ++ MATCH_MP_TAC REAL_LE_TRANS
    ++ Q.EXISTS_TAC `(1/2)*x`
    ++ RW_TAC real_ss []
    ++ RW_TAC std_ss [Once (GSYM REAL_LE_NEG), GSYM REAL_MUL_RNEG]
    ++ Suff `1/2 * ~x <= 1 * ~x` >> RW_TAC real_ss []
    ++ METIS_TAC [REAL_NEG_GT0, REAL_LT_TOTAL,
                  REAL_LE_REFL, REAL_HALF_BETWEEN, REAL_LE_RMUL]);

val le_epsilon = store_thm
  ("le_epsilon",``!x y. (!e. 0 < e /\ e <> PosInf
                     ==> x <= y + e) ==> x <= y``,
  (REPEAT Cases ++ RW_TAC std_ss [le_infty])
  << [Q.EXISTS_TAC `1`
      ++ RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      Q.EXISTS_TAC `1`
      ++ RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      Q.EXISTS_TAC `1`
      ++ RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def,
      	 	        extreal_le_def],
      `!e. 0 < e  ==> Normal r <= Normal r' + Normal e`
         by (RW_TAC std_ss []
             ++ Q.PAT_ASSUM `!e. P e` MATCH_MP_TAC
	     ++ METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_lt_eq])
      ++ `!e. 0 < e ==> Normal r <= Normal (r' + e)`
         by (RW_TAC real_ss [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD]
             ++ `Normal r <= Normal r' + Normal e` by METIS_TAC [REAL_LT_IMP_LE]
             ++ `Normal r' + Normal e = Normal (r' + e)`
                  by METIS_TAC [extreal_add_def, REAL_LT_IMP_LE]
             ++ FULL_SIMP_TAC std_ss []
	     ++ METIS_TAC [REAL_LE_ADD, extreal_le_def, REAL_LT_IMP_LE])
      ++ `!e. 0 < e ==>  r <= r' + e`
       by METIS_TAC [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD, extreal_add_def, REAL_LE_ADD]
      ++ `!e. 0 < e ==>  r <= r' + e` by METIS_TAC [extreal_le_def]
      ++ METIS_TAC [REAL_LE_EPSILON,extreal_le_def]]);

val le_mul_epsilon = store_thm
("le_mul_epsilon",``!x y:extreal. (!z. 0 <= z /\ z < 1 ==> z * x <= y) ==> x <= y``,
  ASSUME_TAC half_between
  ++ `1 / 2 <> 0` by METIS_TAC [lt_imp_ne]
  ++ (REPEAT Cases ++ RW_TAC std_ss [le_infty])
  << [Q.EXISTS_TAC `1 / 2`
      ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases],
      Q.EXISTS_TAC `1 / 2`
      ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                         le_infty,extreal_not_infty],
      Q.EXISTS_TAC `1 / 2`
      ++ RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                         le_infty,extreal_not_infty],
      `!z. 0 <= z /\ z < 1 = ?z1. 0 <= z1 /\ z1 < 1 /\ (z = Normal z1)`
         by (RW_TAC std_ss []
             ++ EQ_TAC
	     >> (RW_TAC std_ss []
                 ++ Cases_on `z`
		 << [METIS_TAC [extreal_of_num_def, le_infty, extreal_not_infty],
		     METIS_TAC [extreal_of_num_def, lt_infty, extreal_not_infty],
		     METIS_TAC [extreal_le_def, extreal_lt_eq, extreal_of_num_def]])
	     ++ METIS_TAC [extreal_lt_eq, extreal_le_def, extreal_of_num_def])
      ++ RW_TAC std_ss []
      ++ `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1) * Normal r <= Normal r'`
         by METIS_TAC [extreal_lt_eq,extreal_le_def,extreal_of_num_def]
      ++ `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1 * r) <= Normal r'`
         by METIS_TAC [extreal_mul_def]
      ++ Suff `r <= r'` >> METIS_TAC [extreal_le_def]
      ++ MATCH_MP_TAC REAL_LE_MUL_EPSILON
      ++ METIS_TAC [extreal_le_def,REAL_LT_LE]]);


(***************************)
(*   SUM over Finite Set   *)
(***************************)

val EXTREAL_SUM_IMAGE_DEF = new_definition(
  "EXTREAL_SUM_IMAGE_DEF",
  ``EXTREAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0:extreal)``);

val EXTREAL_SUM_IMAGE_THM = store_thm
  ("EXTREAL_SUM_IMAGE_THM",
  ``!f. (EXTREAL_SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (EXTREAL_SUM_IMAGE f (e INSERT s) =
                f e + EXTREAL_SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC
  >> SIMP_TAC (srw_ss()) [ITSET_THM, EXTREAL_SUM_IMAGE_DEF]
  ++ SIMP_TAC (srw_ss()) [EXTREAL_SUM_IMAGE_DEF]
  ++ Q.ABBREV_TAC `g = \e acc. f e + acc`
  ++ Suff `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)`
  >> (Q.UNABBREV_TAC `g` ++ SRW_TAC [] [])
  ++ MATCH_MP_TAC COMMUTING_ITSET_RECURSES
  ++ Q.UNABBREV_TAC `g`
  ++ RW_TAC real_ss []
  ++ METIS_TAC [add_assoc,add_comm]);

val EXTREAL_SUM_IMAGE_NOT_NEG_INF = store_thm
  ("EXTREAL_SUM_IMAGE_NOT_NEG_INF",``!f s. FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==>
          EXTREAL_SUM_IMAGE f s <> NegInf``,
  Suff `!s. FINITE s ==> (\s. !f. (!x. x IN s ==> f x <> NegInf)
          ==> EXTREAL_SUM_IMAGE f s <> NegInf) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, num_not_infty]
  ++ METIS_TAC [add_not_infty, IN_INSERT, DELETE_NON_ELEMENT]);


val EXTREAL_SUM_IMAGE_NOT_POS_INF = store_thm
  ("EXTREAL_SUM_IMAGE_NOT_POS_INF",``!f s. FINITE s /\ (!x. x IN s ==> f x <> PosInf)
              ==> EXTREAL_SUM_IMAGE f s <> PosInf``,
  Suff `!s. FINITE s ==> (\s. !f. (!x. x IN s ==> f x <> PosInf)
          ==> EXTREAL_SUM_IMAGE f s <> PosInf) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, num_not_infty]
  ++ METIS_TAC [add_not_infty, IN_INSERT, DELETE_NON_ELEMENT]);

val EXTREAL_SUM_IMAGE_NOT_INFTY = store_thm
  ("EXTREAL_SUM_IMAGE_NOT_INFTY",``
   !f s. (FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==> EXTREAL_SUM_IMAGE f s <> NegInf) /\
         (FINITE s /\ (!x. x IN s ==> f x <> PosInf) ==> EXTREAL_SUM_IMAGE f s <> PosInf)``,
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_NEG_INF,EXTREAL_SUM_IMAGE_NOT_POS_INF]);

val absorption = #1 (EQ_IMP_RULE (SPEC_ALL ABSORPTION));
val delete_non_element = #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT));

val EXTREAL_SUM_IMAGE_SING = store_thm(
  "EXTREAL_SUM_IMAGE_SING", ``!f e. EXTREAL_SUM_IMAGE f {e} = f e``,
SRW_TAC [][EXTREAL_SUM_IMAGE_THM, add_rzero]);

val EXTREAL_SUM_IMAGE_POS = store_thm
  ("EXTREAL_SUM_IMAGE_POS",
   ``!f s. FINITE s /\ (!x. x IN s ==> 0 <= f x)
          ==> 0 <= EXTREAL_SUM_IMAGE f s``,
  Suff `!s. FINITE s ==> (\s. !f. (!x. x IN s ==> 0 <= f x)
          ==> 0 <= EXTREAL_SUM_IMAGE f s) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, le_refl]
  ++ METIS_TAC [le_add, IN_INSERT, DELETE_NON_ELEMENT]);

val EXTREAL_SUM_IMAGE_SPOS = store_thm
  ("EXTREAL_SUM_IMAGE_SPOS",
   ``!f s. FINITE s /\ (~(s = {})) /\ (!x. x IN s ==> 0 < f x)
            ==> 0 < EXTREAL_SUM_IMAGE f s``,
  Suff `!s. FINITE s ==> (\s. !f. (~(s = {}))/\ (!x. x IN s ==> 0 < f x)
           ==> 0 < EXTREAL_SUM_IMAGE f s) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, le_refl, DELETE_NON_ELEMENT]
  ++ Cases_on `s = {}`
  >> METIS_TAC [EXTREAL_SUM_IMAGE_THM, add_rzero, IN_SING]
  ++ METIS_TAC [lt_add,IN_INSERT]);

val EXTREAL_SUM_IMAGE_IF_ELIM = store_thm
  ("EXTREAL_SUM_IMAGE_IF_ELIM",
   ``!s P f. FINITE s /\ (!x. x IN s ==> P x) ==>
	(EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s = EXTREAL_SUM_IMAGE f s)``,
  Suff `!s. FINITE s ==>
	(\s. !P f. (!x. x IN s ==> P x) ==>
		(EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s =
 		 EXTREAL_SUM_IMAGE f s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT]);

val EXTREAL_SUM_IMAGE_FINITE_SAME = store_thm
  ("EXTREAL_SUM_IMAGE_FINITE_SAME",
   ``!s. FINITE s ==>
	 !f p. p IN s /\ (!q. q IN s ==> (f p = f q))
             ==> (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)``,
  Suff `!s. FINITE s ==>
	 (\s. !f p. p IN s /\ (!q. q IN s ==> (f p = f q))
            ==> (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, mul_lzero, CARD_INSERT,ADD1]
  ++ RW_TAC std_ss [extreal_of_num_def, GSYM extreal_add_def, GSYM REAL_ADD]
  ++ `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, DELETE_NON_ELEMENT]

  ++ `0 <= (&CARD s) /\ 0 <= 1` by METIS_TAC [extreal_of_num_def, le_num, le_01]
  ++ RW_TAC std_ss [add_rdistrib,mul_lone]
  ++  Suff `EXTREAL_SUM_IMAGE f s = & (CARD s) * f e`
  >> METIS_TAC [add_comm,IN_INSERT]
  ++ (MP_TAC o Q.SPECL [`s`]) SET_CASES ++ RW_TAC std_ss []
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, mul_lzero]
  ++ `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
  ++ Q.PAT_ASSUM `!f p. b` MATCH_MP_TAC ++ METIS_TAC [IN_INSERT]);

val EXTREAL_SUM_IMAGE_FINITE_CONST = store_thm
  ("EXTREAL_SUM_IMAGE_FINITE_CONST", ``!P. FINITE P ==>
	!f x. (!y. f y = x)  ==> (EXTREAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`P`]) EXTREAL_SUM_IMAGE_FINITE_SAME
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   ++ RW_TAC std_ss []
   ++ (MP_TAC o Q.SPECL [`P`]) SET_CASES
   ++ RW_TAC std_ss [] >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, mul_lzero]
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [IN_INSERT]);

val EXTREAL_SUM_IMAGE_ZERO = store_thm
  ("EXTREAL_SUM_IMAGE_ZERO",
   ``!s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. 0) s = 0)``,
  RW_TAC std_ss []
  ++ Suff `EXTREAL_SUM_IMAGE (\x. 0) s = &CARD s * 0`
  >> METIS_TAC [mul_rzero]
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_FINITE_CONST
  ++ METIS_TAC [extreal_of_num_def]);

val EXTREAL_SUM_IMAGE_0 = store_thm
  ("EXTREAL_SUM_IMAGE_0",
   ``!f s. FINITE s /\ (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)``,
  Suff `!s. FINITE s ==>
	 (\s. !f.  (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT]
  ++ METIS_TAC [IN_INSERT,add_lzero]);

val EXTREAL_SUM_IMAGE_IN_IF = store_thm
  ("EXTREAL_SUM_IMAGE_IN_IF",
   ``!s. FINITE s ==>
	!f. EXTREAL_SUM_IMAGE f s =
            EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s``,
  Suff `!s. FINITE s ==>
		(\s. !f. EXTREAL_SUM_IMAGE f s =
                         EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [IN_INSERT,EXTREAL_SUM_IMAGE_THM]
  ++ `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ POP_ORW
  ++ `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s`
        by METIS_TAC [IN_INSERT]
  ++ POP_ORW
  ++ Q.PAT_ASSUM `!f. P` (MP_TAC o Q.SPEC `(\x. if (x = e) \/ x IN s then f x else 0)`)
  ++ RW_TAC std_ss []);

val EXTREAL_SUM_IMAGE_CMUL = store_thm
  ("EXTREAL_SUM_IMAGE_CMUL",
   ``!s. FINITE s ==>
	!f c. (0 <= c) \/ (!x. x IN s ==> 0 <= f x)
           ==> (EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s =
                Normal (c) * (EXTREAL_SUM_IMAGE f s))``,
  Suff `!s. FINITE s ==>
	(\s. !f c. (0 <= c) \/ (!x. x IN s ==> 0 <= f x)
            ==> (EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s =
                 Normal (c) * (EXTREAL_SUM_IMAGE f s))) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, mul_rzero, DELETE_NON_ELEMENT]
  >> METIS_TAC [extreal_le_def, add_ldistrib_normal2]
  ++ METIS_TAC [EXTREAL_SUM_IMAGE_POS, IN_INSERT, add_ldistrib]);

val EXTREAL_SUM_IMAGE_CMUL2 = store_thm
  ("EXTREAL_SUM_IMAGE_CMUL2",
   ``!s f c. FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==>
	(EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s =
         Normal (c) * (EXTREAL_SUM_IMAGE f s))``,
  Suff `!s. FINITE s ==>
	(\s. !f c. (!x. x IN s ==> f x <> NegInf)
         ==> (EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s =
              Normal (c) * (EXTREAL_SUM_IMAGE f s))) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, mul_rzero, DELETE_NON_ELEMENT]
  ++ Cases_on `c = 0` >> RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, add_lzero,
                                        EXTREAL_SUM_IMAGE_0]
  ++ Cases_on `0 < c`
  >> METIS_TAC [extreal_le_def, add_ldistrib_normal2, REAL_LT_IMP_LE, IN_INSERT]
  ++ `c < 0` by METIS_TAC [REAL_LT_TOTAL]
  ++ `EXTREAL_SUM_IMAGE f s <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT]
  ++ METIS_TAC [extreal_le_def, add_ldistrib_normal, REAL_LT_IMP_LE, IN_INSERT]);

val EXTREAL_SUM_IMAGE_IMAGE = store_thm
  ("EXTREAL_SUM_IMAGE_IMAGE",
   ``!s. FINITE s ==>
	!f'. INJ f' s (IMAGE f' s) ==> (!f. EXTREAL_SUM_IMAGE f (IMAGE f' s) =
           EXTREAL_SUM_IMAGE (f o f') s)``,
  Suff `!s. FINITE s ==>
	(\s.!f'. INJ f' s (IMAGE f' s) ==> (!f. EXTREAL_SUM_IMAGE f (IMAGE f' s) =
           EXTREAL_SUM_IMAGE (f o f') s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, IMAGE_EMPTY, IMAGE_INSERT, INJ_DEF]
  ++ `FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]
  ++ `~ (f' e IN IMAGE f' s)`
       by (RW_TAC std_ss [IN_IMAGE] ++ REVERSE (Cases_on `x IN s`)
           >> ASM_REWRITE_TAC [] ++ METIS_TAC [IN_INSERT])
  ++ `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ ASM_REWRITE_TAC []
  ++ `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
  ++ `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
  ++ FULL_SIMP_TAC std_ss []);

val EXTREAL_SUM_IMAGE_DISJOINT_UNION = store_thm
  ("EXTREAL_SUM_IMAGE_DISJOINT_UNION",
   ``!s s'. FINITE s /\ FINITE s' /\ DISJOINT s s' ==>
		(!f. EXTREAL_SUM_IMAGE f (s UNION s') =
                     EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')``,
  Suff `!s. FINITE s ==> (\s. !s'. FINITE s' ==>
		(\s'. DISJOINT s s' ==>
			(!f. EXTREAL_SUM_IMAGE f (s UNION s') =
                             EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')) s') s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_SUM_IMAGE_THM,add_lzero]
  ++ FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
  ++ ONCE_REWRITE_TAC [DISJOINT_SYM]
  ++ RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [DISJOINT_SYM]
  ++ ONCE_REWRITE_TAC [UNION_COMM] ++ RW_TAC std_ss [INSERT_UNION]
  ++ ONCE_REWRITE_TAC [UNION_COMM] ++ ONCE_REWRITE_TAC [INSERT_COMM]
  ++ `FINITE (s UNION s')` by RW_TAC std_ss [FINITE_UNION]
  ++ `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION]
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, add_assoc]);

val EXTREAL_SUM_IMAGE_EQ_CARD = store_thm
  ("EXTREAL_SUM_IMAGE_EQ_CARD",
   ``!s. FINITE s ==>
	(EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = (&(CARD s)))``,
  Suff `!s. FINITE s ==>
	(\s. EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = (&(CARD s))) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, IN_INSERT, DELETE_NON_ELEMENT,CARD_INSERT]
  ++ `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ REVERSE (RW_TAC std_ss [ADD1, extreal_of_num_def, GSYM REAL_ADD, GSYM extreal_add_def])
  ++ RW_TAC std_ss [GSYM extreal_of_num_def]
  ++ Suff `EXTREAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
		EXTREAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
  >> METIS_TAC [add_comm]


  ++ (MP_TAC o Q.SPECL [`s`,`e INSERT s`,`(\x. 1)`]) EXTREAL_SUM_IMAGE_IF_ELIM
  ++ `!x. x IN s ==> (e INSERT s) x` by METIS_TAC [IN_INSERT, SPECIFICATION]
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.SPEC `(\x. 1)` o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss []
  ++ `(\x. if (x = e) \/ x IN s then 1 else 0) = (\x. if (e INSERT s) x then 1 else 0)`
      by (RW_TAC std_ss [FUN_EQ_THM]
        ++ METIS_TAC [SPECIFICATION, IN_INSERT])
  ++ RW_TAC std_ss []);

val EXTREAL_SUM_IMAGE_INV_CARD_EQ_1 = store_thm
  ("EXTREAL_SUM_IMAGE_INV_CARD_EQ_1",
   ``!s. (~(s = {})) /\ FINITE s ==>
		(EXTREAL_SUM_IMAGE (\x. if x IN s then inv (& (CARD s)) else 0) s = 1)``,
  REPEAT STRIP_TAC
  ++ `(\x. if x IN s then inv (& (CARD s)) else 0) =
      (\x. inv (& (CARD s)) * (\x. if x IN s then 1 else 0) x)`
	by (RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC real_ss [mul_rzero, mul_rone])
  ++ POP_ORW
  ++ `inv (&CARD s) = Normal (inv (&CARD s))`
        by (FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
            ++ METIS_TAC [CARD_EQ_0,FINITE_EMPTY])
  ++ POP_ORW
  ++ `0r <= &CARD s` by RW_TAC real_ss []
  ++ `0r <= inv (&CARD s)` by METIS_TAC [REAL_LE_INV]
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL,EXTREAL_SUM_IMAGE_EQ_CARD]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def]
  ++ `&CARD s <> 0r` by (FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
                         ++ METIS_TAC [CARD_EQ_0, FINITE_EMPTY])
  ++ METIS_TAC [REAL_MUL_LINV, CARD_EQ_0, FINITE_EMPTY]);

val EXTREAL_SUM_IMAGE_INTER_NONZERO = store_thm
  ("EXTREAL_SUM_IMAGE_INTER_NONZERO",
   ``!s. FINITE s ==>
	!f. EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
            EXTREAL_SUM_IMAGE f s``,
  Suff `!s. FINITE s ==> (\s. !f. EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
                                  EXTREAL_SUM_IMAGE f s) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, INTER_EMPTY, INSERT_INTER]
  ++ Cases_on `e IN (\p. f p <> 0)`
  >> (RW_TAC std_ss []
      ++ `~(e IN (s INTER (\p. ~(f p = 0))))` by RW_TAC std_ss [IN_INTER]
      ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT,INTER_FINITE]
      ++ FULL_SIMP_TAC std_ss [IN_INSERT])
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, add_lzero, IN_ABS]);

val EXTREAL_SUM_IMAGE_INTER_ELIM = store_thm
  ("EXTREAL_SUM_IMAGE_INTER_ELIM",
   ``!s. FINITE s ==>
	 !f s'. (!x. ~(x IN s') ==> (f x = 0)) ==>
		(EXTREAL_SUM_IMAGE f (s INTER s') = EXTREAL_SUM_IMAGE f s)``,
  Suff `!s. FINITE s ==>
	(\s. !f s'. (!x. ~(x IN s') ==> (f x = 0)) ==>
		(EXTREAL_SUM_IMAGE f (s INTER s') = EXTREAL_SUM_IMAGE f s)) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [INTER_EMPTY, INSERT_INTER, EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
  ++ Cases_on `e IN s'`
  >> (`~ (e IN (s INTER s'))` by RW_TAC std_ss [IN_INTER, DELETE_NON_ELEMENT]
      ++ FULL_SIMP_TAC std_ss [INTER_FINITE, EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
      ++ FULL_SIMP_TAC std_ss [IN_INSERT]
      ++ METIS_TAC [IN_INTER, DELETE_NON_ELEMENT])
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ METIS_TAC [DELETE_NON_ELEMENT, add_lzero]);

val EXTREAL_SUM_IMAGE_ZERO_DIFF = store_thm
 ("EXTREAL_SUM_IMAGE_ZERO_DIFF",``!s. FINITE s ==> !f t. (!x. x IN t ==> (f x = 0))
               ==> (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f (s DIFF t))``,
  RW_TAC std_ss []
  ++ `s = (s DIFF t) UNION (s INTER t)` by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
                                            ++ METIS_TAC [])
  ++ `FINITE (s DIFF t) /\ FINITE (s INTER t)` by METIS_TAC [INTER_FINITE, FINITE_DIFF]
  ++ `DISJOINT (s DIFF t) (s INTER t)` by (RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY,
                                           EXTENSION, IN_DIFF] ++ METIS_TAC [])
  ++ `EXTREAL_SUM_IMAGE f (s INTER t) = 0` by METIS_TAC [EXTREAL_SUM_IMAGE_0, IN_INTER]
  ++ METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION, add_rzero]);

  val EXTREAL_SUM_IMAGE_MONO = store_thm
  ("EXTREAL_SUM_IMAGE_MONO",
   ``!s. FINITE s ==> !f f'. (!x. x IN s ==> f x <= f' x) ==>
		EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s``,
   Suff `!s. FINITE s ==>
		(\s. !f f'. (!x. x IN s ==> f x <= f' x) ==>
		EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s) s`
   >> METIS_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, le_refl, DELETE_NON_ELEMENT]
   ++ METIS_TAC [le_add2,IN_INSERT]);

val EXTREAL_SUM_IMAGE_MONO_SET = store_thm
  ("EXTREAL_SUM_IMAGE_MONO_SET",
   ``!f s t. (FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> 0 <= f x)) ==>
            EXTREAL_SUM_IMAGE f s  <= EXTREAL_SUM_IMAGE f t``,
  RW_TAC std_ss []
  ++ `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  ++ `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  ++ `DISJOINT s (t DIFF s)`
      by (`DISJOINT s (t DIFF s)` by RW_TAC std_ss [DISJOINT_DEF, IN_DIFF, EXTENSION,
      	 	      	      	     GSPECIFICATION, NOT_IN_EMPTY, IN_INTER]
          ++ METIS_TAC [])
  ++ `EXTREAL_SUM_IMAGE f t = EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f (t DIFF s)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
  ++ POP_ORW
  ++ METIS_TAC [le_add2, le_refl, add_rzero, EXTREAL_SUM_IMAGE_POS, IN_DIFF]);

val EXTREAL_SUM_IMAGE_EQ = store_thm
  ("EXTREAL_SUM_IMAGE_EQ",
   ``!s. FINITE s ==>
	   !f f'. (!x. x IN s ==> (f x = f' x)) ==>
		(EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==> (\s. !f f'. (!x. x IN s ==> (f x = f' x)) ==>
		(EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)) s`
  >> PROVE_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT]
  ++ METIS_TAC []);

val EXTREAL_SUM_IMAGE_POS_MEM_LE = store_thm
  ("EXTREAL_SUM_IMAGE_POS_MEM_LE",
   ``!f s. FINITE s  /\ (!x. x IN s ==> 0 <= f x) ==>
	    (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)``,
  Suff `!s. FINITE s ==>
	(\s. !f. (!x. x IN s ==> 0 <= f x) ==>
	    (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, NOT_IN_EMPTY]
  ++ METIS_TAC [EXTREAL_SUM_IMAGE_POS, le_add2, add_rzero, le_refl, IN_INSERT, add_lzero]);

val EXTREAL_SUM_IMAGE_ADD = store_thm
  ("EXTREAL_SUM_IMAGE_ADD",
   ``!s. FINITE s ==> !f f'.
	(EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
         EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==>
	(\s. !f f'. (EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
                     EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, add_lzero, DELETE_NON_ELEMENT]
  ++ METIS_TAC [add_comm,add_assoc]);

val EXTREAL_SUM_IMAGE_SUB = store_thm
  ("EXTREAL_SUM_IMAGE_SUB",
   ``!s. FINITE s ==> !f f'. (!x. x IN s ==> f' x <> NegInf) \/ (!x. x IN s ==> f' x <> PosInf)
            ==> (EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
		 EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==>
	(\s. !f f'. (!x. x IN s ==> f' x <> NegInf) \/ (!x. x IN s ==> f' x <> PosInf) ==>
		(EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
		 EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT,sub_rzero]
  ++ `EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
             EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s` by METIS_TAC [IN_INSERT]
  ++ POP_ORW
  ++ METIS_TAC [add2_sub2,IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]);

val EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE = store_thm
  ("EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE",
   ``!s s' f. FINITE s /\ FINITE s' ==>
	(EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
	 EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))``,
  Suff `!s. FINITE s ==>  (\s. !s' f. FINITE s' ==>
	(EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
	 EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [CROSS_EMPTY, EXTREAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
  ++ `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
            ++ Cases_on `x`
	    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
	    ++ METIS_TAC [])
  ++ POP_ORW
  ++ `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
	by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION,
				  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
	    ++ STRIP_TAC ++ Cases_on `x`
	    ++ RW_TAC std_ss [FST, SND]
	    ++ METIS_TAC [])
  ++ `FINITE (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [IMAGE_FINITE]
  ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
  ++ `INJ (\x. (e,x)) s' (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [INJ_DEF, IN_IMAGE]
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IMAGE,o_DEF]
  ++ FULL_SIMP_TAC std_ss [IN_INSERT,IN_IMAGE,IN_UNION]
  ++ METIS_TAC [FUN_EQ_THM]);

val EXTREAL_SUM_IMAGE_NORMAL = store_thm
  ("EXTREAL_SUM_IMAGE_NORMAL",
   ``!f s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. Normal (f x)) s =
                         Normal (SIGMA f s))``,
  Suff `!s. FINITE s ==> (\s. !f. EXTREAL_SUM_IMAGE (\x. Normal (f x)) s = Normal (SIGMA f s) ) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,extreal_of_num_def,REAL_SUM_IMAGE_THM,
                    GSYM extreal_add_def,DELETE_NON_ELEMENT]);

val EXTREAL_SUM_IMAGE_IN_IF_ALT = store_thm
("EXTREAL_SUM_IMAGE_IN_IF_ALT",``!s f z. FINITE s
         ==> (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s)``,
  Suff `!s. FINITE s ==> (\s. !f z. EXTREAL_SUM_IMAGE f s =
             EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT]
  ++ REVERSE (RW_TAC std_ss [])
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ Suff `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN e INSERT s then f x else z) s`
  >> RW_TAC std_ss []
  ++ `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s`
       by METIS_TAC [IN_INSERT]
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [IN_INSERT]);

val EXTREAL_SUM_IMAGE_CROSS_SYM = store_thm
 ("EXTREAL_SUM_IMAGE_CROSS_SYM", ``!f s1 s2. FINITE s1 /\ FINITE s2 ==>
   (EXTREAL_SUM_IMAGE (\(x,y). f (x,y)) (s1 CROSS s2) = EXTREAL_SUM_IMAGE (\(y,x). f (x,y)) (s2 CROSS s1))``,
  RW_TAC std_ss []
  ++ `s2 CROSS s1 = IMAGE (\a. (SND a, FST a)) (s1 CROSS s2)`
	by (RW_TAC std_ss [IN_IMAGE, IN_CROSS,EXTENSION] ++ METIS_TAC [FST,SND,PAIR])
  ++ POP_ORW
  ++ `INJ (\a. (SND a, FST a)) (s1 CROSS s2) (IMAGE (\a. (SND a, FST a)) (s1 CROSS s2))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS]
           ++ METIS_TAC [FST,SND,PAIR])
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, FINITE_CROSS, o_DEF]
  ++ `(\(x,y). f (x,y)) = (\a. f a)`
       by (RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `a`
	   ++ RW_TAC std_ss [])
  ++ RW_TAC std_ss []);

val EXTREAL_SUM_IMAGE_COUNT = store_thm
("EXTREAL_SUM_IMAGE_COUNT",``!f. (EXTREAL_SUM_IMAGE f (count 2) = f 0 + f 1) /\
       (EXTREAL_SUM_IMAGE f (count 3) = f 0 + f 1 + f 2) /\
       (EXTREAL_SUM_IMAGE f (count 4) = f 0 + f 1 + f 2 + f 3) /\
       (EXTREAL_SUM_IMAGE f (count 5) = f 0 + f 1 + f 2 + f 3 + f 4)``,
  RW_TAC std_ss []
  ++ `count 2 = {0;1}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
  ++ `count 3 = {0;1;2}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
  ++ `count 4 = {0;1;2;3}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
  ++ `count 5 = {0;1;2;3;4}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
  ++ `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{2:num} DELETE 1 = {2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{3:num} DELETE 2 = {3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{4:num} DELETE 3 = {4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{2:num; 3} DELETE 1 = {2;3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{3:num; 4} DELETE 2 = {3;4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{2:num; 3; 4} DELETE 1 = {2;3;4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
  ++ `{1:num; 2} DELETE 0 = {1;2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
  ++ `{1:num; 2; 3} DELETE 0 = {1;2;3}` by RW_TAC real_ss [EXTENSION, IN_DELETE,IN_SING,IN_INSERT]
  ++ `{1:num; 2; 3; 4} DELETE 0 = {1;2;3;4}`
      by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
  ++ FULL_SIMP_TAC real_ss [FINITE_SING, FINITE_INSERT, EXTREAL_SUM_IMAGE_THM,
     		   	    EXTREAL_SUM_IMAGE_SING, add_assoc, IN_INSERT, NOT_IN_EMPTY]
  ++ DECIDE_TAC);

val _ = overload_on ("SIGMA", ``EXTREAL_SUM_IMAGE``);


(* ------------------------------------------------------------------------- *)
(* Supremums and infimums (these are always defined on extended reals)       *)
(* ------------------------------------------------------------------------- *)

val extreal_sup_def = Define
  `extreal_sup p =
   if !x. (!y. p y ==> y <= x) ==> (x = PosInf) then PosInf
   else (if !x. p x ==> (x = NegInf) then NegInf
             else Normal (sup (\r. p (Normal r))))`;

val extreal_inf_def = Define
  `extreal_inf p = -extreal_sup (IMAGE numeric_negate p)`;

val _ = overload_on ("sup", Term `extreal_sup`);
val _ = overload_on ("inf", Term `extreal_inf`);

val le_sup_imp = store_thm
  ("le_sup_imp",
   ``!p x. p x ==> x <= sup p``,
  RW_TAC std_ss [extreal_sup_def, le_infty, le_refl]
  ++ FULL_SIMP_TAC std_ss []
  ++ Cases_on `x`
  << [RW_TAC std_ss [le_infty],
      `x' < PosInf` by (Cases_on `x'` ++ RW_TAC std_ss [lt_infty])
      ++ METIS_TAC [let_trans,lt_refl],
      RW_TAC std_ss [extreal_le_def]
      ++ MATCH_MP_TAC REAL_IMP_LE_SUP
      ++ CONJ_TAC >> METIS_TAC []
      ++ REVERSE CONJ_TAC >> (Q.EXISTS_TAC `r` ++ RW_TAC real_ss [])
      ++ Cases_on `x'`
      << [METIS_TAC [le_infty],
         RW_TAC std_ss [],
         Q.EXISTS_TAC `r'`
         ++ RW_TAC std_ss []
         ++ METIS_TAC [extreal_le_def]]]);

val sup_le = store_thm
  ("sup_le",
   ``!p x. sup p <= x = (!y. p y ==> y <= x)``,
  RW_TAC std_ss [extreal_sup_def,le_infty]
  >> (EQ_TAC >> RW_TAC std_ss [le_infty] ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss []
  ++ Cases_on `x`
  << [METIS_TAC [le_infty,extreal_not_infty],
      METIS_TAC [le_infty],
      Cases_on `x'`
      << [METIS_TAC [le_infty],
	  RW_TAC std_ss [],
	  RW_TAC std_ss [extreal_le_def]
          ++ EQ_TAC
	  >> (RW_TAC std_ss []
              ++ Cases_on `y`
	      << [METIS_TAC [le_infty],
		  METIS_TAC [le_infty,extreal_not_infty],
		  RW_TAC std_ss [extreal_le_def]
                  ++ MATCH_MP_TAC REAL_LE_TRANS
		  ++ Q.EXISTS_TAC `sup (\r. p (Normal r))`
		  ++ RW_TAC std_ss []
		  ++ MATCH_MP_TAC REAL_IMP_LE_SUP
		  ++ CONJ_TAC >> METIS_TAC []
		  ++ REVERSE CONJ_TAC >> (Q.EXISTS_TAC `r''` ++ RW_TAC real_ss [])
		  ++ Q.EXISTS_TAC `r'`
                  ++ RW_TAC std_ss []
                  ++ METIS_TAC [extreal_le_def]])
	   ++ RW_TAC std_ss []
	   ++ MATCH_MP_TAC REAL_IMP_SUP_LE
	   ++ RW_TAC std_ss []
	   >> (Cases_on `x''` << [RW_TAC std_ss [],
	      		      	  METIS_TAC [le_infty, extreal_not_infty],
				  METIS_TAC []])
           ++ METIS_TAC [extreal_le_def]]]);

val le_sup = store_thm
  ("le_sup",
   ``!p x. x <= sup p = !y. (!z. p z ==> z <= y) ==> x <= y``,
   RW_TAC std_ss [extreal_sup_def,le_infty]
   >> (EQ_TAC >> RW_TAC std_ss [le_infty] ++ METIS_TAC [le_infty, le_refl])
   ++ FULL_SIMP_TAC std_ss []
   ++ Cases_on `x'`
   << [METIS_TAC [le_infty],
       METIS_TAC [le_infty],
       Cases_on `x`
       << [METIS_TAC [le_infty],
           METIS_TAC [le_infty, extreal_not_infty],
	   RW_TAC std_ss [extreal_le_def]
           ++ EQ_TAC
	   >> (RW_TAC std_ss []
	       ++ Cases_on `y`
	       << [METIS_TAC [le_infty],
		   METIS_TAC [le_infty],
		   RW_TAC std_ss [extreal_le_def]
	           ++ MATCH_MP_TAC REAL_LE_TRANS
                   ++ Q.EXISTS_TAC `sup (\r. p (Normal r))`
                   ++ RW_TAC std_ss []
                   ++ MATCH_MP_TAC REAL_IMP_SUP_LE
		   ++ RW_TAC std_ss []
		   >> (Cases_on `x''` << [RW_TAC std_ss [],
                                          METIS_TAC [le_infty, extreal_not_infty],
                                          METIS_TAC []])
		   ++ METIS_TAC [extreal_le_def]])
	   ++ RW_TAC std_ss [extreal_le_def]
	   ++ (MP_TAC o Q.SPECL [`(\r. p (Normal r))`,`r'`]) REAL_LE_SUP
	   ++ MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
	   ++ CONJ_TAC
	   >> (RW_TAC std_ss []
	       >> METIS_TAC [extreal_cases, le_infty, extreal_not_infty]
	       ++ METIS_TAC [extreal_le_def])
	       ++ RW_TAC std_ss []
               ++ Q.PAT_ASSUM `!y. (!z. p z ==> z <= y) ==> Normal r' <= y`
                    (MATCH_MP_TAC o REWRITE_RULE [extreal_le_def] o Q.SPEC `Normal y`)
	       ++ Cases
	       << [METIS_TAC [le_infty],
		   METIS_TAC [le_infty, extreal_not_infty],
		   METIS_TAC [extreal_le_def]]]]);

val sup_eq = store_thm
  ("sup_eq", ``!p x. (sup p = x) =
                (!y. p y ==> y <= x) /\ !y. (!z. p z ==> z <= y) ==> x <= y``,
   METIS_TAC [le_antisym, le_sup, sup_le]);

val sup_const = store_thm
  ("sup_const",
   ``!x. sup (\y. y = x) = x``,
   RW_TAC real_ss [sup_eq, le_refl]);

val sup_const_alt = store_thm
("sup_const_alt", ``!p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (sup p = z)``,
  RW_TAC std_ss [sup_eq,le_refl]
  ++ POP_ASSUM MATCH_MP_TAC
  ++ RW_TAC std_ss []);

val sup_const_over_set = store_thm
 ("sup_const_over_set",``!s k. s <> {} ==> (sup (IMAGE (\x. k) s) = k)``,
  RW_TAC std_ss [sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE] ++ RW_TAC std_ss [le_refl])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE]
  ++ METIS_TAC [CHOICE_DEF]);

val sup_num = store_thm
  ("sup_num",
   ``sup (\x. ?n : num. x = & n) = PosInf``,
  RW_TAC std_ss [GSYM le_infty,le_sup]
  ++ Cases_on `y`
  << [POP_ASSUM (MP_TAC o Q.SPEC `0`)
      ++ RW_TAC real_ss [le_infty, extreal_of_num_def, extreal_not_infty],
      RW_TAC std_ss [le_refl],
      RW_TAC std_ss [le_infty, extreal_not_infty]
      ++ MP_TAC (Q.SPEC `r` REAL_BIGNUM)
      ++ PURE_REWRITE_TAC [real_lt]
      ++ STRIP_TAC
      ++ Q.PAT_ASSUM `!z. P z` (MP_TAC o Q.SPEC `&n`)
      ++ RW_TAC std_ss [extreal_of_num_def] >> METIS_TAC []
      ++ METIS_TAC [extreal_le_def]]);

val sup_le_sup_imp = store_thm
  ("sup_le_sup_imp",
   ``!p q. (!x. p x ==> ?y. q y /\ x <= y) ==> sup p <= sup q``,
   RW_TAC std_ss [sup_le] ++ METIS_TAC [le_trans, le_sup_imp]);

val sup_mono = store_thm
("sup_mono",
   ``!p q. (!n:num. p n <= q n) ==> sup (IMAGE p UNIV) <= sup (IMAGE q UNIV)``,
  RW_TAC std_ss [sup_le,le_sup]
  ++ Q.PAT_ASSUM `IMAGE p UNIV y` (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `q x`
  ++ RW_TAC std_ss []
  ++ Q.PAT_ASSUM `!z. Q ==> z <= y'` MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val sup_suc = store_thm
  ("sup_suc",
   ``!f. (!m n. m <= n ==> f m <= f n) ==>
     (sup (IMAGE (\n. f (SUC n)) UNIV) = sup (IMAGE f UNIV))``,
   RW_TAC std_ss [sup_eq,sup_le,le_sup]
   >> (POP_ASSUM MATCH_MP_TAC
       ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
       ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
       ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
       ++ METIS_TAC [])
   ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
   ++ Cases_on `x`
   >> (MATCH_MP_TAC le_trans
       ++ Q.EXISTS_TAC `f 1`
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MATCH_MP_TAC
       ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
       ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
       ++ `SUC 0 = 1` by RW_TAC real_ss []
       ++ METIS_TAC [])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   ++ METIS_TAC []);

val sup_seq = store_thm
 ("sup_seq", ``!f l. mono_increasing f ==>
        ((f --> l)  = (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (RW_TAC std_ss [sup_eq]
      >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          ++ RW_TAC std_ss [extreal_le_def]
          ++ METIS_TAC [mono_increasing_suc, SEQ_MONO_LE, ADD1])
      ++ `!n. Normal (f n) <= y`
            by (RW_TAC std_ss []
                ++ POP_ASSUM MATCH_MP_TAC
 	        ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 	        ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 	        ++ METIS_TAC [])
      ++ Cases_on `y`
      << [METIS_TAC [le_infty, extreal_not_infty],
          METIS_TAC [le_infty],
          METIS_TAC [SEQ_LE_IMP_LIM_LE,extreal_le_def]])
  ++ RW_TAC std_ss [extreal_sup_def]
  ++ `(\r. IMAGE (\n. Normal (f n)) UNIV (Normal r)) = IMAGE f UNIV`
       by (RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]
           ++ EQ_TAC
           ++ (RW_TAC std_ss []
               ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV])
	   ++ RW_TAC std_ss []
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_UNIV, IN_IMAGE]
	   ++ METIS_TAC [])
  ++ POP_ORW
  ++ FULL_SIMP_TAC std_ss []
  ++ `!n. Normal (f n) <= x`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!y. P` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
	   ++ METIS_TAC [])
  ++ `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  ++ `?z. x = Normal z` by METIS_TAC [extreal_cases]
  ++ `!n. f n <= z` by FULL_SIMP_TAC std_ss [extreal_le_def]
  ++ RW_TAC std_ss [SEQ]
  ++ (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON
  ++ SIMP_TAC std_ss [REAL_LT_HALF1]
  ++ `!y x z. IMAGE f UNIV x = x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
  ++ POP_ORW
  ++ Know `(?z. !x. x IN IMAGE f UNIV ==> x <= z)`
  >> (Q.EXISTS_TAC `z`
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ `?x. x IN IMAGE f UNIV` by RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  ++ RW_TAC std_ss []
  ++ `?x. x IN IMAGE f univ(:num) /\ sup (IMAGE f univ(:num)) <= x + e / 2` by METIS_TAC []
  ++ RW_TAC std_ss [GSYM ABS_BETWEEN, GREATER_EQ]
  ++ FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ Q.EXISTS_TAC `x''''''`
  ++ RW_TAC std_ss [REAL_LT_SUB_RADD]
  >> (MATCH_MP_TAC REAL_LET_TRANS ++ Q.EXISTS_TAC `f x'''''' + e / 2`
      ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LET_TRANS
      ++ Q.EXISTS_TAC `f n + e / 2`
      ++ REVERSE CONJ_TAC >> METIS_TAC [REAL_LET_ADD2,REAL_LT_HALF2,REAL_LE_REFL]
      ++ RW_TAC std_ss [REAL_LE_RADD]
      ++ METIS_TAC [mono_increasing_def])
   ++ MATCH_MP_TAC REAL_LET_TRANS ++ Q.EXISTS_TAC `sup (IMAGE f UNIV)`
   ++ RW_TAC std_ss [REAL_LT_ADDR]
   ++ Suff `!y. (\y. y IN IMAGE f UNIV) y ==> y <= sup (IMAGE f UNIV)`
   >> METIS_TAC [IN_IMAGE, IN_UNIV]
   ++ SIMP_TAC std_ss [IN_DEF]
   ++ MATCH_MP_TAC REAL_SUP_UBOUND_LE
   ++ `!y x z. IMAGE f UNIV x = x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
   ++ POP_ORW
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   ++ Q.EXISTS_TAC `z'`
   ++ RW_TAC std_ss []);

val sup_lt_infty = store_thm
 ("sup_lt_infty", ``!p. (sup p < PosInf) ==> (!x. p x ==> x < PosInf)``,
  METIS_TAC [le_sup_imp,let_trans]);

val sup_max = store_thm
 ("sup_max", ``!p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)``,
  RW_TAC std_ss [sup_eq]);

val sup_add_mono = store_thm
 ("sup_add_mono", ``!f g. (!n. 0 <= f n) /\ (!n. f n <= f (SUC n)) /\
                          (!n. 0 <= g n) /\ (!n. g n <= g (SUC n)) ==>
                    (sup (IMAGE (\n. f n + g n) UNIV) = sup (IMAGE f UNIV) + sup (IMAGE g UNIV))``,
  RW_TAC std_ss [sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ MATCH_MP_TAC le_add2
      ++ RW_TAC std_ss [le_sup]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ METIS_TAC [SPECIFICATION,IN_IMAGE,IN_UNIV])
  ++ Cases_on `y = PosInf` >> RW_TAC std_ss [le_infty]
  ++ Cases_on `sup (IMAGE f UNIV) = 0`
  >> (RW_TAC std_ss [sup_le, add_lzero]
      ++ FULL_SIMP_TAC std_ss [sup_eq]
      ++ `!n. f n = 0` by METIS_TAC [EXTENSION,IN_IMAGE,IN_UNIV,SPECIFICATION,le_antisym]
      ++ Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      ++ RW_TAC std_ss [add_lzero]
      ++ METIS_TAC [])
  ++ Cases_on `sup (IMAGE g UNIV) = 0`
  >> (RW_TAC std_ss [sup_le, add_rzero]
      ++ FULL_SIMP_TAC std_ss [sup_eq]
      ++ `!n. g n = 0` by METIS_TAC [EXTENSION,IN_IMAGE,IN_UNIV,SPECIFICATION,le_antisym]
      ++ Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      ++ RW_TAC std_ss [add_rzero]
      ++ METIS_TAC [])
  ++ `!n. f n + g n <= y`
       by (RW_TAC std_ss []
	   ++ Q.PAT_ASSUM `!z. Q z ==> P z` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `!n. g n <= f n + g n` by METIS_TAC [add_lzero,le_add2,le_refl]
  ++ `!n. f n <= f n + g n` by METIS_TAC [add_rzero,le_add2,le_refl]
  ++ `!n. g n <> PosInf` by METIS_TAC [le_trans,lt_infty,let_trans]
  ++ `!n. g n <> NegInf` by METIS_TAC [le_trans,le_infty,lt_infty,lte_trans,
                                       extreal_of_num_def,extreal_not_infty]
  ++ `!n. f n <> PosInf` by METIS_TAC [le_trans,lt_infty,let_trans]
  ++ `!n. f n <> NegInf` by METIS_TAC [le_trans,le_infty,lt_infty,lte_trans,extreal_of_num_def,
                                       extreal_not_infty]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `sup (IMAGE (\n. (sup (IMAGE f UNIV)) + g n) UNIV)`
  ++ REVERSE (RW_TAC std_ss [sup_le])
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Suff `sup (IMAGE f UNIV) <= y - g n` >> RW_TAC std_ss [le_sub_eq]
      ++ RW_TAC std_ss [sup_le]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ MATCH_MP_TAC le_sub_imp
      ++ RW_TAC std_ss []
      ++ Cases_on `x <= n`
      >> (MATCH_MP_TAC le_trans
          ++ Q.EXISTS_TAC `f n + g n`
          ++ CONJ_TAC >> METIS_TAC [le_radd,ext_mono_increasing_def,ext_mono_increasing_suc]
	  ++ Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
          ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `f x + g x`
      ++ CONJ_TAC >> METIS_TAC [le_ladd,ext_mono_increasing_def,ext_mono_increasing_suc,
                                le_refl,NOT_LEQ,le_trans]
      ++ Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ `sup (IMAGE f UNIV) <> NegInf`
        by (RW_TAC std_ss [sup_eq,le_infty]
            ++ Q.EXISTS_TAC `f (CHOICE (UNIV:num->bool))`
	    ++ RW_TAC std_ss []
	    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	    ++ METIS_TAC [IN_UNIV,IN_IMAGE])
  ++ `sup (IMAGE g UNIV) <> NegInf`
        by (RW_TAC std_ss [sup_eq,le_infty]
            ++ Q.EXISTS_TAC `g (CHOICE (UNIV:num->bool))`
	    ++ RW_TAC std_ss []
	    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	    ++ METIS_TAC [IN_UNIV,IN_IMAGE])
  ++ Cases_on `sup (IMAGE f UNIV) = PosInf`
  >> (`sup (IMAGE (\n. sup (IMAGE f UNIV) + g n) UNIV) = PosInf`
        by (RW_TAC std_ss [extreal_add_def,sup_eq,le_infty]
          ++ POP_ASSUM (MP_TAC o Q.SPEC `PosInf + g (CHOICE (UNIV:num->bool))`)
	  ++ RW_TAC std_ss []
	  ++ `PosInf + g (CHOICE univ(:num)) <= y'`
               by (POP_ASSUM MATCH_MP_TAC
		   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
		   ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
		   ++ METIS_TAC [])
          ++ METIS_TAC [extreal_add_def,extreal_cases,le_infty])
      ++ METIS_TAC [le_infty])
  ++ RW_TAC std_ss [add_comm]
  ++ Suff `sup (IMAGE g UNIV) <=
           sup (IMAGE (\n. g n + sup (IMAGE f UNIV)) UNIV) - sup (IMAGE f UNIV)`
  >> METIS_TAC [le_sub_eq,add_comm]
  ++ RW_TAC std_ss [sup_le]
  ++ MATCH_MP_TAC le_sub_imp
  ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [le_sup]
  ++ Q.PAT_ASSUM `IMAGE g UNIV y'` (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val sup_sum_mono = store_thm
 ("sup_sum_mono", ``!f s. FINITE s /\ (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
                                      (!i:num. i IN s ==> (!n. f i n <= f i (SUC n)))
                   ==>  (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
                         SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)``,
  Suff `!s. FINITE s ==> (\s. !f. (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
                        (!i:num. i IN s ==> (!n. f i n <= f i (SUC n))) ==>
                      (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
                       SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,UNIV_NOT_EMPTY,sup_const_over_set,DELETE_NON_ELEMENT]
  ++ `sup (IMAGE (\n. f e n + (\n. SIGMA (\i. f i n) s) n) UNIV) =
      sup (IMAGE (f e) UNIV) + sup (IMAGE (\n. SIGMA (\i. f i n) s) UNIV)`
        by ((MATCH_MP_TAC o Q.SPECL [`f e`, `(\n. SIGMA (\i. f i n) s)`] o
               INST_TYPE [alpha |-> ``:num``]) sup_add_mono
            ++ FULL_SIMP_TAC std_ss [IN_INSERT,EXTREAL_SUM_IMAGE_POS,
                                     EXTREAL_SUM_IMAGE_MONO])
  ++ METIS_TAC [IN_INSERT]);

val sup_le_mono = store_thm
 ("sup_le_mono",``!f z. (!n. f n <= f (SUC n)) /\ z < sup (IMAGE f UNIV)
                    ==> ?n. z <= f n``,
  RW_TAC std_ss []
  ++ SPOSE_NOT_THEN ASSUME_TAC
  ++ FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
  ++ `!x. x IN (IMAGE f UNIV) ==> x <= z`
       by METIS_TAC [IN_IMAGE,IN_UNIV,lt_imp_le]
  ++ METIS_TAC [sup_le,SPECIFICATION,extreal_lt_def]);

val sup_cmul = store_thm
 ("sup_cmul",``!f c. 0 <= c ==> (sup (IMAGE (\n. (Normal c) * f n) UNIV) =
                                 (Normal c) * sup (IMAGE f UNIV))``,
  RW_TAC std_ss []
  ++ Cases_on `c = 0` >> RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def,UNIV_NOT_EMPTY,
                                         sup_const_over_set]
  ++ `0 < c` by METIS_TAC [REAL_LT_LE]
  ++ RW_TAC std_ss [sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Cases_on `sup (IMAGE f UNIV) = PosInf`
      >> RW_TAC std_ss [extreal_mul_def,le_infty]
      ++ Cases_on `f n = NegInf`
      >> RW_TAC std_ss [extreal_mul_def,le_infty]
      ++ `f n <= sup (IMAGE f UNIV)`
          by (MATCH_MP_TAC le_sup_imp
              ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	      ++ METIS_TAC [])
      ++ `f n <> PosInf /\ sup (IMAGE f UNIV) <> NegInf`
          by METIS_TAC [let_trans,lte_trans,lt_infty]
      ++ `?r. f n = Normal r` by METIS_TAC [extreal_cases]
      ++ `?r. sup (IMAGE f UNIV) = Normal r` by METIS_TAC [extreal_cases]
      ++ RW_TAC std_ss [extreal_mul_def,extreal_le_def]
      ++ METIS_TAC [REAL_LE_LMUL,extreal_le_def])
  ++ `!n. Normal c * f n <= y`
        by (RW_TAC std_ss []
            ++ POP_ASSUM MATCH_MP_TAC
	    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	    ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	    ++ METIS_TAC [])
  ++ `!n. f n <= y / (Normal c)` by METIS_TAC [le_rdiv,mul_comm]
  ++ ONCE_REWRITE_TAC [mul_comm]
  ++ RW_TAC std_ss [le_rdiv,sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val sup_lt = store_thm
("sup_lt",``!P y.  (?x. P x /\ y < x) <=> y < sup P``,
  RW_TAC std_ss []
  ++ EQ_TAC >> METIS_TAC [le_sup_imp,lte_trans]
  ++ RW_TAC std_ss []
  ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
  ++ METIS_TAC [sup_le,extreal_lt_def]);

val sup_lt_epsilon = store_thm
("sup_lt_epsilon",``!P e. (0 < e) /\ (?x. P x /\ x <> NegInf) /\ (sup P <> PosInf)
                        ==> (?x. P x /\ sup P < x + e)``,
  RW_TAC std_ss []
  ++ Cases_on `e = PosInf`
  >> (Q.EXISTS_TAC `x`
      ++ RW_TAC std_ss []
      ++ METIS_TAC [extreal_add_def,lt_infty,extreal_cases])
  ++ `e <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans,
                                 extreal_of_num_def,extreal_not_infty]
  ++ `sup P <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans]
  ++ `sup P < sup P + e`
     by (Cases_on `sup P` ++ Cases_on `e`
         ++ RW_TAC std_ss [extreal_cases,extreal_add_def,extreal_lt_def,extreal_le_def,GSYM real_lt]
         ++ METIS_TAC [REAL_LT_ADDR,extreal_lt_def,extreal_le_def,extreal_of_num_def,real_lt])
  ++ `sup P - e < sup P` by METIS_TAC [sub_lt_imp]
  ++ `?x. P x /\ (sup P - e) < x` by METIS_TAC [sup_lt]
  ++ Q.EXISTS_TAC `x'`
  ++ RW_TAC std_ss []
  ++ `x' <> PosInf` by METIS_TAC [le_sup_imp,let_trans,lt_infty]
  ++ `?r. sup P = Normal r` by METIS_TAC [extreal_cases]
  ++ `?r. e = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_sub_def]
  ++ `x' <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lt_trans]
  ++ `?r. x' = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_add_def,extreal_lt_def,extreal_le_def,GSYM real_lt,
                           REAL_LT_SUB_RADD]);

val inf_le_imp = store_thm
  ("inf_le_imp",
   ``!p x. p x ==> inf p <= x``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE]
  ++ METIS_TAC [SPECIFICATION]);

val le_inf = store_thm
  ("le_inf",
   ``!p x. x <= inf p = (!y. p y ==> x <= y)``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,sup_le]
  ++ EQ_TAC
  >> (RW_TAC std_ss []
      ++ `-y IN (IMAGE numeric_negate p)`
           by (RW_TAC std_ss [IN_IMAGE]
               ++ METIS_TAC [SPECIFICATION])
      ++ METIS_TAC [le_neg,SPECIFICATION])
  ++ RW_TAC std_ss []
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE]
  ++ METIS_TAC [le_neg,SPECIFICATION]);

val inf_le = store_thm
  ("inf_le",
   ``!p x. (inf p <= x) = (!y. (!z. p z ==> y <= z) ==> y <= x)``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  ++ EQ_TAC
  >> (RW_TAC std_ss []
      ++ `!z. IMAGE numeric_negate p z ==> y <= -z`
            by (RW_TAC std_ss []
                ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
                ++ RW_TAC std_ss [IN_IMAGE]
		++ METIS_TAC [neg_neg,SPECIFICATION])
      ++ `!z. IMAGE numeric_negate p z ==> z <= -y`
           by METIS_TAC [le_neg,neg_neg]
      ++ `(!z. IMAGE numeric_negate p z ==> z <= -y) ==> -x <= -y`
           by METIS_TAC []
      ++ METIS_TAC [le_neg])
  ++ RW_TAC std_ss []
  ++ `!z. p z ==> -z <= y`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!z. IMAGE numeric_negate p z ==> z <= y` MATCH_MP_TAC
           ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE]
	   ++ METIS_TAC [SPECIFICATION])
  ++ `!z. p z ==> -y <= z` by METIS_TAC [le_neg,neg_neg]
  ++ METIS_TAC [le_neg,neg_neg]);

val inf_eq = store_thm
("inf_eq", ``!p x. (inf p = x) =
                       (!y. p y ==> x <= y) /\
                       (!y. (!z. p z ==> y <= z) ==> y <= x)``,
  METIS_TAC [le_antisym,inf_le,le_inf]);

val inf_const = store_thm
("inf_const", ``!x. inf (\y. y = x) = x``,
   RW_TAC real_ss [inf_eq, le_refl]);

val inf_const_alt = store_thm
("inf_const_alt", ``!p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (inf p = z)``,
  RW_TAC std_ss [inf_eq,le_refl]
  ++ POP_ASSUM MATCH_MP_TAC
  ++ RW_TAC std_ss []);

val inf_const_over_set = store_thm
 ("inf_const_over_set",``!s k. s <> {} ==> (inf (IMAGE (\x. k) s) = k)``,
  RW_TAC std_ss [inf_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE] ++ RW_TAC std_ss [le_refl])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE]
  ++ METIS_TAC [CHOICE_DEF]);

val inf_suc = store_thm
  ("inf_suc",
   ``!f. (!m n. m <= n ==> f n <= f m) ==>
     (inf (IMAGE (\n. f (SUC n)) UNIV) = inf (IMAGE f UNIV))``,
  RW_TAC std_ss [inf_eq,inf_le,le_inf]
  >> (POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `f (SUC x)`
  ++ RW_TAC real_ss []
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val inf_seq = store_thm
 ("inf_seq", ``!f l. mono_decreasing f ==>
         ((f --> l)  = (inf (IMAGE (\n. Normal (f n)) UNIV) = Normal l))``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (RW_TAC std_ss [inf_eq]
      >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          ++ RW_TAC std_ss [extreal_le_def]
          ++ METIS_TAC [mono_decreasing_suc,SEQ_LE_MONO,ADD1])
      ++ `!n. y <= Normal (f n)`
            by (RW_TAC std_ss []
                ++ POP_ASSUM MATCH_MP_TAC
 	        ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 	        ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
 	        ++ METIS_TAC [])
      ++ Cases_on `y`
      << [METIS_TAC [le_infty],
          METIS_TAC [le_infty,extreal_not_infty],
          METIS_TAC [LE_SEQ_IMP_LE_LIM,extreal_le_def]])
  ++ RW_TAC std_ss [extreal_inf_def,extreal_sup_def,extreal_ainv_def,extreal_not_infty]
  ++ `(\r. IMAGE numeric_negate (IMAGE (\n. Normal (f n)) univ(:num)) (Normal r)) =
       IMAGE (\n. - f n) UNIV`
       by (RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV]
           ++ EQ_TAC
           >> (RW_TAC std_ss []
               ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	       ++ METIS_TAC [extreal_ainv_def,extreal_11])
	   ++ RW_TAC std_ss []
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
	   ++ METIS_TAC [extreal_ainv_def,extreal_11])
  ++ POP_ORW
  ++ FULL_SIMP_TAC std_ss []
  ++ `!n. -Normal (f n) <= x`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!y. P` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
	   ++ METIS_TAC [])
  ++ `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  ++ `?z. x = Normal z` by METIS_TAC [extreal_cases]
  ++ `!n. -(f n) <= z` by METIS_TAC [extreal_le_def,extreal_ainv_def]
  ++ Suff `(\n. -f n) --> sup (IMAGE (\n. -f n) univ(:num))`
  >> METIS_TAC [SEQ_NEG,REAL_NEG_NEG]
  ++ `mono_increasing (\n. -f n)`
        by FULL_SIMP_TAC std_ss [mono_increasing_def,mono_decreasing_def,REAL_LE_NEG]
  ++ Suff `?r. (\n. -f n) --> r`
  >> METIS_TAC [mono_increasing_converges_to_sup]
  ++ RW_TAC std_ss [GSYM convergent]
  ++ MATCH_MP_TAC SEQ_ICONV
  ++ FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  ++ MATCH_MP_TAC SEQ_BOUNDED_2
  ++ Q.EXISTS_TAC `-f 0`
  ++ Q.EXISTS_TAC `z`
  ++ RW_TAC std_ss []);

val inf_lt_infty = store_thm
 ("inf_lt_infty", ``!p. (NegInf < inf p) ==> (!x. p x ==> NegInf < x)``,
  METIS_TAC [inf_le_imp,lte_trans]);

val inf_min = store_thm
 ("inf_min", ``!p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)``,
  RW_TAC std_ss [inf_eq]);

val inf_cminus = store_thm
 ("inf_cminus", ``!f c. Normal c - inf (IMAGE f UNIV) =
                        sup (IMAGE (\n. Normal c - f n) UNIV)``,
  RW_TAC std_ss [sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ `inf (IMAGE f UNIV) <= f n`
           by (MATCH_MP_TAC inf_le_imp
	       ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	       ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	       ++ METIS_TAC [])
      ++ METIS_TAC [le_lsub_imp])
  ++ `!n. Normal c - f n <= y`
        by (RW_TAC std_ss []
            ++ Q.PAT_ASSUM `!z. P` MATCH_MP_TAC
	    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	    ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	    ++ METIS_TAC [])
  ++ RW_TAC std_ss [extreal_inf_def,sub_rneg]
  ++ Suff `sup (IMAGE numeric_negate (IMAGE f UNIV)) <= y - Normal c`
  >> METIS_TAC [le_sub_eq,extreal_not_infty,add_comm]
  ++ RW_TAC std_ss [sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ RW_TAC std_ss [le_sub_eq,GSYM add_comm]
  ++ Cases_on `y = PosInf` >> RW_TAC std_ss [le_infty]
  ++ METIS_TAC [extreal_sub_add]);


(* ------------------------------------------------------------------------- *)
(* Suminf over extended reals. Definition and properties                     *)
(* ------------------------------------------------------------------------- *)

val ext_suminf_def = Define
           `ext_suminf f = sup (IMAGE (\n. SIGMA f (count n)) UNIV)`;

val ext_suminf_add = store_thm
("ext_suminf_add",``!f g. (!n. 0 <= f n /\ 0 <= g n)
        ==> (ext_suminf (\n. f n + g n) = ext_suminf f + ext_suminf g)``,
  RW_TAC std_ss [ext_suminf_def,sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV,SPECIFICATION]
      ++ `!n. f n <> NegInf /\ g n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
      ++ RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_ADD]
      ++ MATCH_MP_TAC le_add2
      ++ RW_TAC std_ss [le_sup]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ `!n. SIGMA (\n. f n + g n) (count n) <= y`
       by (RW_TAC std_ss []
           ++ POP_ASSUM MATCH_MP_TAC
  	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `!n. f n <> NegInf /\ g n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  ++ `!n. SIGMA (\n. f n + g n) (count n) = SIGMA f (count n) + SIGMA g (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_ADD,FINITE_COUNT]
  ++ `!n. SIGMA f (count n) + SIGMA g (count n) <= y` by FULL_SIMP_TAC std_ss []
  ++ `!n m. SIGMA f (count n) + SIGMA g (count m) <= y`
       by (RW_TAC std_ss []
           ++ Cases_on `n <= m`
           >> (MATCH_MP_TAC le_trans
	       ++ Q.EXISTS_TAC `SIGMA f (count m) + SIGMA g (count m)`
               ++ RW_TAC std_ss []
	       ++ MATCH_MP_TAC le_radd_imp
	       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	       ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT]
	       ++ DECIDE_TAC)
	   ++ MATCH_MP_TAC le_trans
	   ++ Q.EXISTS_TAC `SIGMA f (count n) + SIGMA g (count n)`
           ++ RW_TAC std_ss []
	   ++ MATCH_MP_TAC le_ladd_imp
	   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	   ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT]
	   ++ DECIDE_TAC)
  ++ Cases_on `y = PosInf` >> RW_TAC std_ss [le_infty]
  ++ `!n. SIGMA f (count n) <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,FINITE_COUNT]
  ++ `!n. SIGMA g (count n) <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,FINITE_COUNT]
  ++ `y <> NegInf` by METIS_TAC [lt_infty,add_not_infty,lte_trans]
  ++ FULL_SIMP_TAC std_ss [GSYM le_sub_eq2]
  ++ `!m. sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y - SIGMA g (count m)`
       by (RW_TAC std_ss [sup_le]
           ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ FULL_SIMP_TAC std_ss [])
  ++ `sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <> NegInf`
         by (RW_TAC std_ss [lt_infty,GSYM sup_lt]
             ++ Q.EXISTS_TAC `SIGMA f (count 1)`
	     ++ REVERSE (RW_TAC std_ss [])
	     >> FULL_SIMP_TAC std_ss [lt_infty]
	     ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	     ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	     ++ METIS_TAC [])
  ++ `!m.  SIGMA g (count m) + sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y`
        by METIS_TAC [le_sub_eq2,add_comm]
  ++ `!m.  SIGMA g (count m) <= y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
        by METIS_TAC [le_sub_eq2]
  ++ `!m. sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <=
          y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by (RW_TAC std_ss [sup_le]
           ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ FULL_SIMP_TAC std_ss [])
  ++ `sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <> NegInf`
         by (RW_TAC std_ss [lt_infty,GSYM sup_lt]
             ++ Q.EXISTS_TAC `SIGMA g (count 1)`
	     ++ REVERSE (RW_TAC std_ss [])
	     >> FULL_SIMP_TAC std_ss [lt_infty]
	     ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	     ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	     ++ METIS_TAC [])
  ++ METIS_TAC [le_sub_eq2,add_comm]);

val ext_suminf_cmul = store_thm
 ("ext_suminf_cmul",``!f c. 0 <= c /\ (!n. 0 <= f n)
              ==> (ext_suminf (\n. c * f n) = c * ext_suminf f)``,
  RW_TAC std_ss [ext_suminf_def]
  ++ `c <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  ++ `!n. f n <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  ++ REVERSE (Cases_on `c` ++ (RW_TAC std_ss []))
  >> (`!n. SIGMA (\n. Normal r * f n) (count n) = Normal r * SIGMA f (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL,FINITE_COUNT]
      ++ POP_ORW
      ++ METIS_TAC [sup_cmul,extreal_le_def,extreal_of_num_def])
  ++ Cases_on `!n. f n = 0`
  >> (RW_TAC std_ss [extreal_mul_def,extreal_of_num_def,EXTREAL_SUM_IMAGE_0,FINITE_COUNT]
      ++ `sup (IMAGE (\n. Normal 0) univ(:num)) = 0`
           by (MATCH_MP_TAC sup_const_alt
               ++ RW_TAC std_ss []
	       >> (Q.EXISTS_TAC `Normal 0`
                   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV])
	       ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	       ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV,extreal_of_num_def])
      ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def])
  ++ FULL_SIMP_TAC std_ss []
  ++ `0 < f n` by METIS_TAC [lt_le]
  ++ `0 < sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by (RW_TAC std_ss [GSYM sup_lt]
           ++ Q.EXISTS_TAC `SIGMA f (count (SUC n))`
	   ++ RW_TAC std_ss []
	   >> (ONCE_REWRITE_TAC [GSYM SPECIFICATION]
               ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	       ++ METIS_TAC [])
	   ++ `f n <= SIGMA f (count (SUC n))`
                 by METIS_TAC [COUNT_SUC,IN_INSERT,FINITE_COUNT,EXTREAL_SUM_IMAGE_POS_MEM_LE]
           ++ METIS_TAC [lte_trans])
  ++ `PosInf * f n <= SIGMA (\n. PosInf * f n) (count (SUC n))`
      by (`!n. 0 <= PosInf * f n` by METIS_TAC [le_infty,le_mul]
          ++ `n IN count (SUC n)` by METIS_TAC [COUNT_SUC,IN_INSERT]
	  ++ (MP_TAC o REWRITE_RULE [FINITE_COUNT] o Q.ISPECL [`(\n:num. PosInf * f n)`,
                 `count (SUC n)`]) EXTREAL_SUM_IMAGE_POS_MEM_LE
	  ++ RW_TAC std_ss [])
  ++ `!x. 0 < x ==> (PosInf * x = PosInf)`
       by (Cases_on `x`
           << [METIS_TAC [lt_infty],RW_TAC std_ss [extreal_mul_def],
               RW_TAC real_ss [extreal_lt_eq,extreal_of_num_def,extreal_mul_def]])
  ++ `PosInf * f n = PosInf`
       by ((Cases_on `f n` ++ FULL_SIMP_TAC std_ss [extreal_mul_def])
           >> METIS_TAC []
	   ++ METIS_TAC [extreal_lt_eq,extreal_of_num_def])
  ++ `SIGMA (\n. PosInf * f n) (count (SUC n)) = PosInf` by METIS_TAC [le_infty]
  ++ `SIGMA (\n. PosInf * f n) (count (SUC n)) <=
         sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num))`
        by (MATCH_MP_TAC le_sup_imp
            ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	    ++ METIS_TAC [])
  ++ `sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num)) = PosInf`
       by METIS_TAC [le_infty]
  ++ METIS_TAC []);

val ext_suminf_cmul_alt = store_thm
 ("ext_suminf_cmul_alt",``!f c. 0 <= c /\ ((!n. f n <> NegInf) \/ (!n. f n <> PosInf))
       ==> (ext_suminf (\n. (Normal c) * f n) = (Normal c) * ext_suminf f)``,
  RW_TAC std_ss [ext_suminf_def]
  ++ `!n. SIGMA (\n. Normal c * f n) (count n) = (Normal c) * SIGMA f (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL,FINITE_COUNT]
  ++ POP_ORW
  ++ RW_TAC std_ss [sup_cmul]);

val ext_suminf_lt_infty = store_thm
 ("ext_suminf_lt_infty",``!f. (!n. 0 <= f n) /\ ext_suminf f <> PosInf
        ==> (!n. f n < PosInf)``,
  RW_TAC std_ss [ext_suminf_def]
  ++ `!n. SIGMA f (count n) < PosInf`
       by (RW_TAC std_ss []
	   ++ `!n. SIGMA f (count n) IN IMAGE (\n. SIGMA f (count n)) UNIV`
                 by (RW_TAC std_ss [IN_IMAGE,IN_UNIV] ++ METIS_TAC [])
	   ++ METIS_TAC [lt_infty,sup_lt_infty,SPECIFICATION])
  ++ Suff `f n <= SIGMA f (count (SUC n))` >> METIS_TAC [let_trans]
  ++ `FINITE (count (SUC n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `n IN (count (SUC n))` by RW_TAC real_ss [IN_COUNT]
  ++ METIS_TAC [EXTREAL_SUM_IMAGE_POS_MEM_LE]);

val ext_suminf_suminf = store_thm
("ext_suminf_suminf",``!r. (!n. 0 <= r n) /\ (ext_suminf (\n. Normal (r n)) <> PosInf)
                          ==>  (ext_suminf (\n. Normal (r n)) = Normal (suminf r))``,

  RW_TAC std_ss [ext_suminf_def]
  ++ `!n. FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL]
  ++ `(\n. Normal (SIGMA r (count n))) = (\n. Normal ((\n. SIGMA r (count n)) n))` by METIS_TAC []
  ++ POP_ORW
  ++ `mono_increasing (\n. SIGMA r (count n))`
      by (RW_TAC std_ss [mono_increasing_def,GSYM extreal_le_def]
          ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
	  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
          ++ RW_TAC std_ss [extreal_le_def,extreal_of_num_def,SUBSET_DEF,IN_COUNT]
	  ++ DECIDE_TAC)
  ++ RW_TAC std_ss [GSYM sup_seq]
  ++ FULL_SIMP_TAC std_ss [suminf,sums,REAL_SUM_IMAGE_EQ_sum]
  ++ RW_TAC std_ss []
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [sup_eq,le_infty]
  ++ `!n. SIGMA (\n. Normal (r n)) (count n) <= y`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!z. P ==> Q` MATCH_MP_TAC
           ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `!n. 0 <= SIGMA (\n. Normal (r n)) (count n)`
       by (RW_TAC std_ss []
           ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
           ++ METIS_TAC [extreal_le_def,extreal_of_num_def])
  ++ `y <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  ++ `?z. y = Normal z` by METIS_TAC [extreal_cases]
  ++ `!n. SIGMA r (count n) <= z` by METIS_TAC [extreal_le_def,EXTREAL_SUM_IMAGE_NORMAL]
  ++ RW_TAC std_ss [GSYM convergent]
  ++ MATCH_MP_TAC SEQ_ICONV
  ++ FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  ++ MATCH_MP_TAC SEQ_BOUNDED_2
  ++ METIS_TAC [REAL_SUM_IMAGE_POS]);

val ext_suminf_mono = store_thm
 ("ext_suminf_mono",``!f g. (!n. g n <> NegInf /\ g n <= f n)
                      ==> (ext_suminf g <= ext_suminf f)``,
  RW_TAC std_ss [ext_suminf_def,sup_le,le_sup]
  ++ Q.PAT_ASSUM `IMAGE f s y` (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `SIGMA f (count n)`
  ++ RW_TAC std_ss []
  >> (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
              EXTREAL_SUM_IMAGE_MONO)
      ++ RW_TAC std_ss []
      ++ DISJ1_TAC
      ++ METIS_TAC [lt_infty,lte_trans])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val ext_suminf_sub = store_thm
("ext_suminf_sub",``!f g. (!n. 0 <= g n /\ g n <= f n) /\
                           ext_suminf f <> PosInf ==>
      (ext_suminf (\i. f i - g i) = ext_suminf f - ext_suminf g)``,
  RW_TAC std_ss []
  ++ `ext_suminf g <= ext_suminf f`
      by (RW_TAC std_ss [ext_suminf_def,sup_le,le_sup]
          ++ Q.PAT_ASSUM `IMAGE (\n. SIGMA g (count n)) univ(:num) y`
                   (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          ++ MATCH_MP_TAC le_trans
	  ++ Q.EXISTS_TAC `SIGMA f (count n)`
	  ++ RW_TAC std_ss []
	  >> (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
                    EXTREAL_SUM_IMAGE_MONO)
              ++ RW_TAC std_ss []
	      ++ DISJ1_TAC
	      ++ METIS_TAC [lt_infty,lte_trans,num_not_infty,le_trans])
	  ++ POP_ASSUM MATCH_MP_TAC
	  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
  ++ `ext_suminf g <> PosInf` by METIS_TAC [lt_infty,let_trans]
  ++ `!n. f n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,le_trans,lt_infty]
  ++ `!n. g n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,lt_infty]
  ++ `!n. f n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty,le_trans]
  ++ `!n. g n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  ++ `?p. !n. f n = Normal (p n)`
       by (Q.EXISTS_TAC `(\n. @r. f n = Normal r)`
           ++ RW_TAC std_ss []
           ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `?q. !n. g n = Normal (q n)`
       by (Q.EXISTS_TAC `(\n. @r. g n = Normal r)`
           ++ RW_TAC std_ss []
           ++ SELECT_ELIM_TAC
	   ++ METIS_TAC [extreal_cases])
  ++ `f = (\n. Normal (p n))` by METIS_TAC []
  ++ `g = (\n. Normal (q n))` by METIS_TAC []
  ++ FULL_SIMP_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [extreal_sub_def,extreal_le_def,
                           extreal_not_infty,extreal_of_num_def]
  ++ `!n. p n - q n <= p n` by METIS_TAC [REAL_LE_SUB_RADD,REAL_ADD_COMM,REAL_LE_ADDR]
  ++ `ext_suminf (\i. Normal (p i - q i)) <> PosInf`
      by (`!n. Normal (p n - q n) <= Normal (p n)` by METIS_TAC [extreal_le_def]
          ++ `ext_suminf (\i. Normal (p i - q i)) <= ext_suminf (\n. Normal (p n))`
                by (MATCH_MP_TAC ext_suminf_mono ++ RW_TAC std_ss [extreal_not_infty])
          ++ METIS_TAC [lt_infty,let_trans])
  ++ `!n. 0 <= p n` by METIS_TAC [REAL_LE_TRANS]
  ++ `!n. 0 <= p n - q n` by METIS_TAC [REAL_SUB_LE]
  ++ RW_TAC std_ss [ext_suminf_suminf,extreal_sub_def]
  ++ FULL_SIMP_TAC std_ss [ext_suminf_def,sup_eq,le_infty]
  ++ `!n. SIGMA (\n. Normal (p n)) (count n) <= y`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!z. Q ==> (z <= y)` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `!n. SIGMA (\n. Normal (q n)) (count n) <= y'`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!z. Q ==> (z <= y')` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `!n. SIGMA (\n. Normal (p n - q n)) (count n) <= y''`
       by (RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!z. Q ==> (z <= y'')` MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ Q.PAT_ASSUM `!z. Q ==> (z <= y)` (K ALL_TAC)
  ++ Q.PAT_ASSUM `!z. Q ==> (z <= y')` (K ALL_TAC)
  ++ Q.PAT_ASSUM `!z. Q ==> (z <= y'')` (K ALL_TAC)
  ++ Q.PAT_ASSUM `sup a <= sup b` (K ALL_TAC)
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL,FINITE_COUNT]
  ++ `0 <= y` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                            extreal_of_num_def,le_trans]
  ++ `0 <= y'` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                             extreal_of_num_def,le_trans]
  ++ `0 <= SIGMA (\n. p n - q n) (count n)`
       by (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           ++ RW_TAC std_ss [FINITE_COUNT])
  ++ `0 <= y''` by METIS_TAC [extreal_le_def,extreal_of_num_def,le_trans]
  ++ `y <> NegInf /\ y' <> NegInf /\ y'' <> NegInf`
       by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  ++ `?z. y = Normal z` by METIS_TAC [extreal_cases]
  ++ `?z'. y' = Normal z'` by METIS_TAC [extreal_cases]
  ++ `?z''. y'' = Normal z''` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_not_infty]
  ++ RW_TAC std_ss [suminf,sums]
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [GSYM convergent]
      ++ MATCH_MP_TAC SEQ_ICONV
      ++ RW_TAC std_ss [GREATER_EQ,real_ge]
      >> (MATCH_MP_TAC SEQ_BOUNDED_2
          ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
	  ++ Q.EXISTS_TAC `0` ++ Q.EXISTS_TAC `z''`
	  ++ RW_TAC std_ss []
	  ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
	  ++ RW_TAC std_ss [FINITE_COUNT])
      ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      ++ FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      ++ RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      ++ DECIDE_TAC)
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [GSYM convergent]
      ++ MATCH_MP_TAC SEQ_ICONV
      ++ RW_TAC std_ss [GREATER_EQ,real_ge]
      >> (MATCH_MP_TAC SEQ_BOUNDED_2
          ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
	  ++ Q.EXISTS_TAC `0` ++ Q.EXISTS_TAC `z`
	  ++ RW_TAC std_ss []
	  ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
	  ++ RW_TAC std_ss [FINITE_COUNT])
      ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      ++ FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      ++ RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      ++ DECIDE_TAC)
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [GSYM convergent]
      ++ MATCH_MP_TAC SEQ_ICONV
      ++ RW_TAC std_ss [GREATER_EQ,real_ge]
      >> (MATCH_MP_TAC SEQ_BOUNDED_2
          ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
	  ++ Q.EXISTS_TAC `0` ++ Q.EXISTS_TAC `z'`
	  ++ RW_TAC std_ss []
	  ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
	  ++ RW_TAC std_ss [FINITE_COUNT])
      ++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      ++ FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      ++ RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      ++ DECIDE_TAC)
  ++ Suff `(\n. sum (0,n) (\i. p i - q i)) --> (x' - x'')` >> METIS_TAC [SEQ_UNIQ]
  ++ FULL_SIMP_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
  ++ `(\n. SIGMA (\i. p i - q i) (count n)) =
      (\n. (\n. SIGMA p (count n)) n - (\n.  SIGMA q (count n)) n)`
        by (RW_TAC std_ss [FUN_EQ_THM,real_sub]
	    ++ `-SIGMA q (count n') = SIGMA (\x. - q x) (count n')`
                by METIS_TAC [REAL_NEG_MINUS1,REAL_SUM_IMAGE_CMUL,FINITE_COUNT]
	    ++ RW_TAC std_ss [REAL_SUM_IMAGE_ADD,FINITE_COUNT])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_SUB
  ++ RW_TAC std_ss []);

val ext_suminf_sum = store_thm
("ext_suminf_sum",``!f n. (!n. 0 <= f n) /\ (!m. n <= m ==> (f m = 0))
             ==> (ext_suminf f = SIGMA f (count n))``,
  RW_TAC std_ss [ext_suminf_def,sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Cases_on `n' <= n`
      >> (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
          ++ RW_TAC real_ss [SUBSET_DEF,IN_COUNT,FINITE_COUNT])
      ++ `count n SUBSET (count n')` by METIS_TAC [IN_COUNT,NOT_LESS_EQUAL,SUBSET_DEF,LESS_TRANS]
      ++ `count n' = (count n) UNION (count n' DIFF (count n))` by METIS_TAC [UNION_DIFF]
      ++ POP_ORW
      ++ `DISJOINT (count n) (count n' DIFF count n)` by METIS_TAC [DISJOINT_DIFF]
      ++ `!n. f n <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lte_trans]
      ++ RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_DISJOINT_UNION]
      ++ `FINITE (count n' DIFF count n)` by METIS_TAC [FINITE_COUNT,FINITE_DIFF]
      ++ (MP_TAC o  REWRITE_RULE [FINITE_COUNT] o Q.ISPECL [`count n`,`count n' DIFF count n`])
                EXTREAL_SUM_IMAGE_DISJOINT_UNION
      ++ RW_TAC std_ss []
      ++ POP_ASSUM (MP_TAC o Q.SPEC `f`)
      ++ RW_TAC std_ss []
      ++ Suff `SIGMA f (count n' DIFF count n) = 0`
      >> RW_TAC std_ss [add_rzero,le_refl]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
      ++ RW_TAC std_ss [IN_COUNT,IN_DIFF]
      ++ METIS_TAC [NOT_LESS])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val _ = overload_on ("suminf", Term `ext_suminf`);

(* ------------------------------------------------------------------------- *)
(* Minimum and maximum                                                       *)
(* ------------------------------------------------------------------------- *)

val extreal_min_def = Define
  `extreal_min (x :extreal) y = if x <= y then x else y`;

val extreal_max_def = Define
  `extreal_max (x : extreal) y = if x <= y then y else x`;

val _ = overload_on ("min", Term `extreal_min`);
val _ = overload_on ("max", Term `extreal_max`);

val min_le = store_thm
  ("min_le",
   ``!z x y. min x y <= z = x <= z \/ y <= z``,
   RW_TAC std_ss [extreal_min_def]
   ++ PROVE_TAC [le_total, le_trans]);

val min_le1 = store_thm
  ("min_le1",
   ``!x y. min x y <= x``,
   PROVE_TAC [min_le, le_refl]);

val min_le2 = store_thm
  ("min_le2",
   ``!x y. min x y <= y``,
   PROVE_TAC [min_le, le_refl]);

val le_min = store_thm
  ("le_min",
   ``!z x y. z <= min x y = z <= x /\ z <= y``,
   RW_TAC std_ss [extreal_min_def]
   ++ PROVE_TAC [le_total, le_trans]);

val min_le2_imp = store_thm
  ("min_le2_imp",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2``,
   RW_TAC std_ss [le_min]
   ++ RW_TAC std_ss [min_le]);

val min_refl = store_thm
  ("min_refl",
   ``!x. min x x = x``,
   RW_TAC std_ss [extreal_min_def, le_refl]);

val min_comm = store_thm
  ("min_comm",
   ``!x y. min x y = min y x``,
   RW_TAC std_ss [extreal_min_def]
   ++ PROVE_TAC [le_antisym, le_total]);

val min_infty = store_thm
  ("min_infty",
   ``!x. (min x PosInf = x) /\ (min PosInf x = x)
         /\ (min NegInf x = NegInf) /\ (min x NegInf = NegInf)``,
   RW_TAC std_ss [extreal_min_def, le_infty]);

val le_max = store_thm
  ("le_max", ``!z x y. z <= max x y = z <= x \/ z <= y``,
   RW_TAC std_ss [extreal_max_def]
   ++ PROVE_TAC [le_total, le_trans]);

val le_max1 = store_thm
  ("le_max1",
   ``!x y. x <= max x y``,
   PROVE_TAC [le_max, le_refl]);

val le_max2 = store_thm
  ("le_max2",
   ``!x y. y <= max x y``,
   PROVE_TAC [le_max, le_refl]);

val max_le = store_thm
  ("max_le",
   ``!z x y. max x y <= z = x <= z /\ y <= z``,
   RW_TAC std_ss [extreal_max_def]
   ++ PROVE_TAC [le_total, le_trans]);

val max_le2_imp = store_thm
  ("max_le2_imp",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2``,
   RW_TAC std_ss [max_le]
   ++ RW_TAC std_ss [le_max]);

val max_refl = store_thm
  ("max_refl",
   ``!x. max x x = x``,
   RW_TAC std_ss [extreal_max_def, le_refl]);

val max_comm = store_thm
  ("max_comm",
   ``!x y. max x y = max y x``,
   RW_TAC std_ss [extreal_max_def]
   ++ PROVE_TAC [le_antisym, le_total]);

val max_infty = store_thm
  ("max_infty",
   ``!x. (max x PosInf = PosInf) /\ (max PosInf x = PosInf) /\
         (max NegInf x = x) /\ (max x NegInf = x)``,
   RW_TAC std_ss [extreal_max_def, le_infty]);


(* ================================================================= *)
(*   Rational Numbers as a subset of extended real numbers           *)
(* ================================================================= *)

val Q_set_def = Define `Q_set = {x| ?a b. (x = (&a/(&b))) /\ (0 < &b)} UNION
                                {x | ?a b. (x = -(&a/(&b))) /\ (0 < &b)}`;

val Q_not_infty = store_thm
  ("Q_not_infty",``!x. x IN Q_set ==> ?y. x = Normal y``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  ++ `&b <> 0:real` by METIS_TAC [extreal_of_num_def,extreal_lt_eq,REAL_LT_IMP_NE]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_div_eq,extreal_ainv_def]);

val Q_COUNTABLE = store_thm
  ("Q_COUNTABLE", ``countable Q_set``,
  RW_TAC std_ss [Q_set_def]
  ++ MATCH_MP_TAC COUNTABLE_UNION
  ++ CONJ_TAC
  >> (RW_TAC std_ss [countable_def]
      ++ MP_TAC NUM_2D_BIJ_NZ_INV
      ++ RW_TAC std_ss []
      ++ Q.EXISTS_TAC `(\(a,b). &a/(&b)) o f`
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
      ++ PAT_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
      ++ RW_TAC std_ss []
      ++ FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,DIFF_DEF,
       			        GSPECIFICATION,GSYM REAL_LT_NZ]
      ++ `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
      ++ Q.EXISTS_TAC `y`
      ++ RW_TAC real_ss [])
  ++ RW_TAC std_ss [countable_def]
  ++ MP_TAC NUM_2D_BIJ_NZ_INV
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `(\(a,b). -(&a/(&b))) o f`
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
  ++ PAT_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,
	  		    DIFF_DEF,GSPECIFICATION,GSYM REAL_LT_NZ]
  ++ `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
  ++ Q.EXISTS_TAC `y`
  ++ RW_TAC real_ss []);

val NUM_IN_Q = store_thm
  ("NUM_IN_Q", ``!n:num. (&n IN Q_set) /\ (-&n IN Q_set)``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  >> (DISJ1_TAC
      ++ Q.EXISTS_TAC `n` ++ Q.EXISTS_TAC `1`
      ++ RW_TAC std_ss [div_one,lt_01])
  ++ DISJ2_TAC
  ++ Q.EXISTS_TAC `n` ++ Q.EXISTS_TAC `1`
  ++ RW_TAC std_ss [div_one,lt_01]);

val Q_INFINITE = store_thm
  ("Q_INFINITE", ``~(FINITE Q_set)``,
  `{x | ?n:num. x = (&n)} SUBSET Q_set`
     by (RW_TAC std_ss [SUBSET_DEF,EXTENSION,GSPECIFICATION]
         ++ METIS_TAC [NUM_IN_Q])
  ++ Suff `~(FINITE {x | ?n:num. x = (&n)})`
  >> METIS_TAC [INFINITE_SUBSET,INFINITE_DEF]
  ++ RW_TAC std_ss [GSYM INFINITE_DEF]
  ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:num``] INFINITE_INJ)
  ++ Q.EXISTS_TAC `(\n. &n)`
  ++ Q.EXISTS_TAC `UNIV`
  ++ RW_TAC real_ss [INFINITE_NUM_UNIV, INJ_DEF,INFINITE_DEF,GSPECIFICATION]
  >> METIS_TAC []
  ++ FULL_SIMP_TAC real_ss [extreal_11,extreal_of_num_def]);

val OPP_IN_Q = store_thm
  ("OPP_IN_Q", ``!x. x IN Q_set ==> -x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION]
  >> (DISJ2_TAC
      ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `b`
      ++ RW_TAC real_ss [])
  ++ DISJ1_TAC
  ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `b`
  ++ RW_TAC real_ss [neg_neg]);

val INV_IN_Q = store_thm
  ("INV_IN_Q", ``!x. (x IN Q_set) /\ (x <> 0) ==> 1/x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  >> (Cases_on `0:real < &a`
      >> (DISJ1_TAC
          ++ `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
          ++ `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11]
          ++ Q.EXISTS_TAC `b` ++ Q.EXISTS_TAC `a`
   	  ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11]
	  ++ `1:real / (&a / &b) = (1 / 1) / (&a / &b)` by RW_TAC real_ss []
  	  ++ ASM_SIMP_TAC std_ss []
  	  ++ RW_TAC real_ss [div_rat,extreal_lt_eq])
     ++ DISJ2_TAC
     ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
     ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11]
     ++ `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE]
     ++ FULL_SIMP_TAC real_ss [])
  ++ Cases_on `0:real < &a`
  >> (DISJ2_TAC
      ++ `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
      ++ `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11,extreal_ainv_def,REAL_NEG_EQ0]
      ++ Q.EXISTS_TAC `b` ++ Q.EXISTS_TAC `a`
      ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11,extreal_ainv_def]
      ++ RW_TAC std_ss [extreal_lt_eq,extreal_ainv_def,extreal_div_eq,real_div,REAL_INV_MUL]
      ++ `inv (&b) <> 0:real` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,REAL_INV_EQ_0,REAL_POS_NZ]
      ++ RW_TAC real_ss [GSYM REAL_NEG_INV,REAL_NEG_EQ0,REAL_EQ_NEG,REAL_ENTIRE]
      ++ RW_TAC real_ss [REAL_INV_MUL,REAL_INV_INV,REAL_MUL_COMM])
  ++ DISJ2_TAC
  ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11,extreal_ainv_def]
  ++ `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE,REAL_NEG_EQ0]
  ++ FULL_SIMP_TAC real_ss []);

val CMUL_IN_Q = store_thm
  ("CMUL_IN_Q", ``!z:num x. x IN Q_set ==> (&z * x IN Q_set) /\ (-&z * x IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
  [DISJ1_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ1_TAC
   ++ Q.EXISTS_TAC `z*a` ++ Q.EXISTS_TAC `b`
   ++  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC]]);

val ADD_IN_Q = store_thm
  ("ADD_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x+y IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
  [DISJ1_TAC
   ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Q.EXISTS_TAC `(a*b' + a'*b)`
   ++ Q.EXISTS_TAC `b*b'`
   ++ RW_TAC std_ss [extreal_div_eq,extreal_add_def,extreal_11,extreal_lt_eq]
   ++ RW_TAC real_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL],

   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ Cases_on `&a*(&b')-(&a'* (&b)) = 0:real`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `0`
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def,GSYM real_sub]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_DIV_LZERO,REAL_MUL_COMM])
   ++ Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `(a * b' - a' * b)`
       ++ Q.EXISTS_TAC `b * b'`
       ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
       ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
       ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       ++ `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       ++ `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       ++ FULL_SIMP_TAC real_ss [REAL_SUB])
   ++ DISJ2_TAC
   ++ Q.EXISTS_TAC `(a' * b - a * b')`
   ++ Q.EXISTS_TAC `b * b'`
   ++  `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
   ++ `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] ++ FULL_SIMP_TAC real_ss [])
   ++ `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]
   ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub]
   ++ RW_TAC std_ss [GSYM mult_ints]
   ++ FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],

   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Cases_on `&a * (&b')-(&a' * (&b)) = 0:real`
   >> (DISJ1_TAC
       ++ Q.EXISTS_TAC `0`
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       ++ ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0]
       ++ RW_TAC std_ss [REAL_NEG_ADD,REAL_NEG_NEG]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,REAL_DIV_LZERO,REAL_SUB_0])
   ++ Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `(a * b' - a' * b)`
       ++ Q.EXISTS_TAC `b * b'`
       ++ RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub]
       ++ RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       ++ `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       ++ `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       ++ FULL_SIMP_TAC real_ss [REAL_SUB,neg_rat])
   ++ DISJ1_TAC
   ++ Q.EXISTS_TAC `(a' * b - a * b')`
   ++ Q.EXISTS_TAC `b * b'`
   ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,extreal_lt_eq]
   ++ `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] ++ FULL_SIMP_TAC real_ss [])
   ++ `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]
   ++ `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11]
   ++ RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM mult_ints]
   ++ FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   DISJ2_TAC
   ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   ++ Q.EXISTS_TAC `(a * b' + a' * b)`
   ++ Q.EXISTS_TAC `b*b'`
   ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11,extreal_lt_eq]
   ++ REWRITE_TAC [GSYM mult_ints,GSYM add_ints]
   ++ RW_TAC std_ss [REAL_SUB_LNEG,GSYM real_sub,REAL_EQ_NEG]
   ++ RW_TAC std_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL]]);

val SUB_IN_Q = store_thm
  ("SUB_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x - y IN Q_set)``,
  RW_TAC std_ss []
  ++ `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
  ++ `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
  ++ RW_TAC std_ss [extreal_sub_def]
  ++ METIS_TAC [OPP_IN_Q,ADD_IN_Q,extreal_add_def,extreal_sub_def,real_sub,extreal_ainv_def]);

val MUL_IN_Q = store_thm
  ("MUL_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x * y IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] <<
 [DISJ1_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a * a'`
  ++ Q.EXISTS_TAC `b * b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ1_TAC
  ++ `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  ++ `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  ++ Q.EXISTS_TAC `a*a'`
  ++ Q.EXISTS_TAC `b*b'`
  ++ RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  ++ FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT]]);

val DIV_IN_Q = store_thm
  ("DIV_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) /\ (y <> 0) ==> (x / y IN Q_set)``,
  RW_TAC std_ss []
  ++ `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
  ++ `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
  ++ RW_TAC std_ss [extreal_div_def,extreal_inv_def,extreal_mul_def]
  ++ `Normal (inv y1) IN Q_set` by METIS_TAC [INV_IN_Q,REAL_INV_1OVER,INV_IN_Q,extreal_div_eq,extreal_inv_def,extreal_of_num_def]
  ++  METIS_TAC [MUL_IN_Q,extreal_mul_def]);

val rat_not_infty = store_thm
("rat_not_infty",``!r. r IN Q_set ==> r <> NegInf /\ r <> PosInf``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  ++ `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  ++ RW_TAC std_ss [extreal_div_eq,extreal_ainv_def]);

val ceiling_def = Define
        `ceiling (Normal x) = LEAST (n:num). x <= &n`;

val CEILING_LBOUND = store_thm
  ("CEILING_LBOUND",``!x. Normal x <= &(ceiling (Normal x))``,
  RW_TAC std_ss [ceiling_def]
  ++ numLib.LEAST_ELIM_TAC
  ++ REWRITE_TAC [SIMP_REAL_ARCH]
  ++ METIS_TAC [extreal_of_num_def,extreal_le_def]);

val CEILING_UBOUND = store_thm
  ("CEILING_UBOUND", ``!x. (0 <= x) ==> &(ceiling( Normal x)) < (Normal x) + 1``,
  RW_TAC std_ss [ceiling_def,extreal_of_num_def,extreal_add_def,extreal_lt_eq]
  ++ numLib.LEAST_ELIM_TAC
  ++ REWRITE_TAC [SIMP_REAL_ARCH]
  ++ RW_TAC real_ss []
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt]
  ++ PAT_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`)
  ++ RW_TAC real_ss []
  ++ Cases_on `n = 0` >> METIS_TAC [REAL_LET_ADD2,REAL_LT_01,REAL_ADD_RID]
  ++ `0 < n` by RW_TAC real_ss []
  ++ `&(n - 1) < x:real` by RW_TAC real_ss []
  ++ `0 <= n-1` by RW_TAC real_ss []
  ++ `0:real <= (&(n-1))` by RW_TAC real_ss []
  ++ `0 < x` by METIS_TAC [REAL_LET_TRANS]
  ++ Cases_on `n = 1` >> METIS_TAC [REAL_LE_REFL,REAL_ADD_RID,REAL_LTE_ADD2,REAL_ADD_COMM]
  ++ `0 <> n-1` by RW_TAC real_ss []
  ++ `&n - 1 < x` by RW_TAC real_ss [REAL_SUB]
  ++ FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]);

val Q_DENSE_IN_R_LEMMA = store_thm
  ("Q_DENSE_IN_R_LEMMA",``!x y. (0 <= x) /\ (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
  (REPEAT Cases ++ RW_TAC std_ss [le_infty,lt_infty,extreal_of_num_def,extreal_not_infty])
  >> (Q.EXISTS_TAC `(&ceiling (Normal r)) + 1`
      ++ RW_TAC std_ss [extreal_of_num_def,extreal_add_def,lt_infty,extreal_lt_eq]
      >> METIS_TAC [ADD_IN_Q,NUM_IN_Q,extreal_add_def,extreal_of_num_def]
      ++ METIS_TAC [extreal_lt_eq,let_trans,REAL_LT_ADDR,REAL_LT_01,extreal_le_def,CEILING_LBOUND,extreal_of_num_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  ++ Cases_on `1 < r' - r`
  >> (Q.EXISTS_TAC `Normal (&(ceiling (Normal r')) - 1)`
      ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
      ++ RW_TAC std_ss [extreal_lt_eq]
      >> METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
      ++ METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def])
  ++ `0 < r' - r` by RW_TAC real_ss [REAL_SUB_LT]
  ++ (MP_TAC o Q.SPEC `1`) (((UNDISCH o Q.SPEC `r' - r`) REAL_ARCH))
  ++ RW_TAC real_ss []
  ++ Suff `?r2. r2 IN Q_set /\ &n * Normal (r) < r2 /\ r2 < &n * Normal (r')`
  >> (RW_TAC real_ss []
      ++ `0 < n` by ( RW_TAC real_ss [] ++ SPOSE_NOT_THEN ASSUME_TAC ++ `n = 0` by RW_TAC real_ss [] ++ FULL_SIMP_TAC real_ss [])
      ++ `0 < (&n)` by RW_TAC real_ss [extreal_lt_eq,extreal_of_num_def]
      ++ Q.EXISTS_TAC `r2 / (&n)`
      ++ RW_TAC real_ss [DIV_IN_Q,NUM_IN_Q,lt_imp_ne]
      >> (`?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
          ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
	  ++ FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
      ++ `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
      ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
      ++ FULL_SIMP_TAC real_ss [REAL_LT_LDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
   ++ `1 < &n * r' - &n * r` by FULL_SIMP_TAC real_ss [REAL_SUB_LDISTRIB]
   ++ Q.EXISTS_TAC `&(ceiling (&n * Normal (r'))) - 1`
   ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
   ++ RW_TAC std_ss [extreal_of_num_def,extreal_mul_def,extreal_sub_def,extreal_lt_eq,extreal_le_def]
   >> METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
   ++ `0:real <= &n` by RW_TAC real_ss []
   ++ `0:real <= &n * r'` by METIS_TAC [REAL_LE_MUL,REAL_LET_TRANS,REAL_LT_IMP_LE]
   ++ METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def,extreal_mul_def]);

val Q_DENSE_IN_R = store_thm
  ("Q_DENSE_IN_R",``!x y. (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
 RW_TAC std_ss []
 ++ Cases_on `0<=x` >> RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]
 ++ FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
 ++ `y <> NegInf` by METIS_TAC [lt_infty]
 ++ (Cases_on `y` ++ RW_TAC std_ss [])
 >> (Q.EXISTS_TAC `0` ++ METIS_TAC [NUM_IN_Q,extreal_of_num_def,extreal_not_infty,lt_infty])
 ++ `x <> PosInf` by METIS_TAC [lt_infty,lt_trans,extreal_not_infty,extreal_of_num_def]
 ++ Cases_on `x = NegInf`
 >> (Cases_on `0<=r`
     >> (Q.EXISTS_TAC `&ceiling (Normal r)- 1`
         ++ RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq]
         >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
         ++ METIS_TAC [CEILING_UBOUND,REAL_LT_SUB_RADD,extreal_of_num_def,extreal_lt_eq,extreal_add_def])
     ++ Q.EXISTS_TAC `- &ceiling (Normal (-r)) - 1`
     ++ RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq,extreal_ainv_def]
     >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def,OPP_IN_Q,extreal_ainv_def]
     ++ (MP_TAC o Q.SPEC `-r`) CEILING_LBOUND
     ++ RW_TAC std_ss [extreal_of_num_def,extreal_le_def]
     ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_LE_NEG])
     ++ RW_TAC std_ss [REAL_NEG_NEG]
     ++ METIS_TAC [REAL_LT_SUB_RADD,REAL_LET_TRANS,REAL_LT_ADDR,REAL_LT_01])
 ++ `?r. x = Normal r` by METIS_TAC [extreal_cases]
 ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
 ++ `Normal (-r') <= &(ceiling (Normal (-r')))` by RW_TAC real_ss [CEILING_LBOUND]
 ++ `-Normal (r') <= &ceiling (Normal (-r'))` by METIS_TAC [extreal_ainv_def]
 ++ `0 <= Normal (r') + &(ceiling (Normal (-r')))` by METIS_TAC [le_lneg,extreal_of_num_def,extreal_add_def,extreal_not_infty]
 ++ `&(ceiling (Normal (-r'))) <> NegInf /\ &(ceiling (Normal (-r'))) <> PosInf`
     by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 ++ `Normal (r') + &(ceiling (Normal (-r'))) < Normal (r) + &(ceiling (Normal (-r')))`
    by METIS_TAC [extreal_lt_eq,lt_radd]
 ++ Suff `?r2. (r2 IN Q_set) /\ (Normal r' + &ceiling (Normal (-r')) < r2) /\ (r2<Normal r + &ceiling (Normal (-r')))`
 >> (RW_TAC std_ss []
     ++ Q.EXISTS_TAC `r2 - &ceiling (Normal (-r'))`
     ++ CONJ_TAC >> METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_of_num_def]
     ++ `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
     ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def]
     ++ RW_TAC std_ss [GSYM REAL_LT_ADD_SUB,REAL_LT_SUB_RADD])
 ++ RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]);

val COUNTABLE_ENUM_Q = store_thm
  ("COUNTABLE_ENUM_Q",
   ``!c. countable c = (c = {}) \/ (?f:extreal->'a. c = IMAGE f Q_set)``,
  RW_TAC std_ss []
  ++ REVERSE EQ_TAC
  >> (NTAC 2 (RW_TAC std_ss [COUNTABLE_EMPTY])
      ++ RW_TAC std_ss [COUNTABLE_IMAGE,Q_COUNTABLE])
  ++ REVERSE (RW_TAC std_ss [COUNTABLE_ALT])
  >> (DISJ2_TAC
      ++ `countable Q_set` by RW_TAC std_ss [Q_COUNTABLE]
      ++ `~(FINITE Q_set)` by RW_TAC std_ss [Q_INFINITE]
      ++ (MP_TAC o Q.SPEC `Q_set`) (INST_TYPE [alpha |-> ``:extreal``] COUNTABLE_ALT)
      ++ RW_TAC std_ss []
      ++ (MP_TAC o Q.SPECL [`enumerate Q_set`,`UNIV`,`Q_set`]) (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:extreal``] BIJ_INV)
      ++ (MP_TAC o Q.SPECL [`enumerate c`,`UNIV`,`c`]) (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:'a``] BIJ_INV)
      ++ RW_TAC std_ss []
      ++ Q.EXISTS_TAC `(enumerate c) o g'`
      ++ RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION]
      ++ EQ_TAC
      >> (RW_TAC std_ss []
          ++ Q.EXISTS_TAC `enumerate Q_set (g x)`
          >> METIS_TAC [BIJ_DEF,INJ_DEF]
          ++ METIS_TAC [BIJ_DEF,INJ_DEF])
      ++ RW_TAC std_ss []
      ++ METIS_TAC [BIJ_DEF,INJ_DEF])
  ++ POP_ASSUM MP_TAC
  ++ Q.SPEC_TAC (`c`, `c`)
  ++ HO_MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss []
  >> (DISJ2_TAC
      ++ Q.EXISTS_TAC `K e`
      ++ RW_TAC std_ss [EXTENSION, IN_SING, IN_IMAGE, IN_UNIV, K_THM]
      ++ EQ_TAC
      >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `0` ++ METIS_TAC [NUM_IN_Q])
      ++ RW_TAC std_ss [])
  ++  DISJ2_TAC
  ++ ASSUME_TAC (Q.SPECL [`f:extreal->'a`,`Q_set`,`IMAGE f Q_set`] (INST_TYPE [alpha |-> ``:extreal``,``:'b`` |-> ``:'a``] INFINITE_INJ))
  ++ `~(INJ f Q_set (IMAGE f Q_set))` by METIS_TAC [INFINITE_DEF,MONO_NOT,Q_INFINITE]
  ++ FULL_SIMP_TAC std_ss [INJ_DEF] >> METIS_TAC [IN_IMAGE]
  ++ Q.EXISTS_TAC `(\u. if u=x then e else f u)`
  ++ `Q_set = (Q_set DIFF {x}) UNION {x}` by (RW_TAC std_ss [DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION,IN_SING] ++ METIS_TAC [])
  ++ `(IMAGE (\u. if u = x then e else f u) Q_set) = (IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x})) UNION (IMAGE (\u. if u = x then e else f u) {x})` by METIS_TAC [IMAGE_UNION]
  ++ `IMAGE (\u. if u = x then e else f u) {x} = {e}` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  ++ `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f Q_set` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_UNION,IN_SING]
  ++ `(IMAGE f Q_set) = (IMAGE f (Q_set DIFF {x})) UNION (IMAGE f {x})` by METIS_TAC [IMAGE_UNION]
  ++ `IMAGE f {x} = {f y}` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  ++ `IMAGE f Q_set = (IMAGE f (Q_set DIFF {x})) UNION {f y}` by METIS_TAC []
  ++ `{f y} SUBSET IMAGE f (Q_set DIFF {x})` by ( RW_TAC std_ss [SUBSET_DEF,IN_IMAGE,IN_SING] ++ Q.EXISTS_TAC `y` ++ RW_TAC std_ss [IN_DIFF,IN_SING])
  ++ `IMAGE f Q_set = IMAGE f (Q_set DIFF {x})` by METIS_TAC [SUBSET_UNION_ABSORPTION,UNION_COMM]
  ++ `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f (Q_set DIFF {x})`
     by (RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_SING]
       	        ++ EQ_TAC
                >> (RW_TAC std_ss []
         	    ++ Q.EXISTS_TAC `u`
       		    ++ RW_TAC std_ss [])
       		++ RW_TAC std_ss []
       		++ Q.EXISTS_TAC `x''`
       		++ RW_TAC std_ss [])
  ++ METIS_TAC [INSERT_SING_UNION,UNION_COMM]);

val CROSS_COUNTABLE_UNIV = store_thm
 ("CROSS_COUNTABLE_UNIV", ``countable (UNIV:num->bool CROSS UNIV:num->bool)``,
  RW_TAC std_ss [countable_def]
  ++ `?(f :num -> num # num). BIJ f UNIV (UNIV CROSS UNIV)` by METIS_TAC [NUM_2D_BIJ_INV]
  ++ Q.EXISTS_TAC `f`
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,CROSS_DEF,IN_UNIV]);

val CROSS_COUNTABLE_LEMMA1 = store_thm
  ("CROSS_COUNTABLE_LEMMA1", ``!s. countable s /\ FINITE s /\ countable t
                           ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ Q.PAT_ASSUM `FINITE s` MP_TAC
  ++ Q.SPEC_TAC (`s`, `s`)
  ++ HO_MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [] >> METIS_TAC [CROSS_EMPTY,COUNTABLE_EMPTY]
  ++ RW_TAC std_ss [CROSS_EQNS]
  ++ MATCH_MP_TAC COUNTABLE_UNION
  ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [COUNTABLE_IMAGE]);

val CROSS_COUNTABLE_LEMMA2 = store_thm
  ("CROSS_COUNTABLE_LEMMA2", ``!s. countable s /\ countable t /\ FINITE t
                           ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ `s CROSS t = IMAGE (\a. (SND a,FST a)) (t CROSS s)`
  	by (RW_TAC std_ss [CROSS_DEF,IMAGE_DEF,EXTENSION,GSPECIFICATION]
	    ++ EQ_TAC
            >> (RW_TAC std_ss []
	        ++ Q.EXISTS_TAC `(SND x,FST x)`
	        ++ RW_TAC std_ss [])
            ++ RW_TAC std_ss [] >> RW_TAC std_ss []
            ++ RW_TAC std_ss [])
  ++ METIS_TAC [COUNTABLE_IMAGE,CROSS_COUNTABLE_LEMMA1]);

val CROSS_COUNTABLE = store_thm
 ("CROSS_COUNTABLE", ``!s. countable s /\ countable t ==> countable (s CROSS t)``,
  RW_TAC std_ss []
  ++ Cases_on `FINITE s` >> METIS_TAC [CROSS_COUNTABLE_LEMMA1]
  ++ Cases_on `FINITE t` >> METIS_TAC [CROSS_COUNTABLE_LEMMA2]
  ++ `BIJ (enumerate s) UNIV s` by METIS_TAC [COUNTABLE_ALT]
  ++ `BIJ (enumerate t) UNIV t` by METIS_TAC [COUNTABLE_ALT]
  ++ Q.ABBREV_TAC `f = enumerate s`
  ++ Q.ABBREV_TAC `g = enumerate t`
  ++ `s CROSS t = IMAGE (\(x,y). (f x,g y)) (UNIV CROSS UNIV)`
	by (Q.UNABBREV_TAC `f` ++ Q.UNABBREV_TAC `g`
	    ++ RW_TAC std_ss [CROSS_DEF,IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_UNIV]
	    ++ EQ_TAC
            >> (RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV]
		++ `?n1. (enumerate s) n1 = FST x` by METIS_TAC []
		++ `?n2. (enumerate t) n2 = SND x` by METIS_TAC []
		++ Q.EXISTS_TAC `(n1, n2)`
		++  RW_TAC std_ss [])
	    ++ RW_TAC std_ss []
	    >> (Cases_on `x'`
		++ RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV])
     	    ++ Cases_on `x'`
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_UNIV])
  ++ METIS_TAC [CROSS_COUNTABLE_UNIV,COUNTABLE_IMAGE]);

val open_interval_def = Define
    `open_interval a b = {x | a < x /\ x < b}`;

val open_intervals_set_def = Define
    `open_intervals_set = {open_interval a b | a IN UNIV /\ b IN UNIV}`;

val rational_intervals_def = Define
	`rational_intervals = {open_interval a b | a IN Q_set /\ b IN Q_set}`;

val COUNTABLE_RATIONAL_INTERVALS = store_thm
 ("COUNTABLE_RATIONAL_INTERVALS", ``countable rational_intervals``,
 `rational_intervals = IMAGE (\(a,b). open_interval a b) (Q_set CROSS Q_set)`
     by (RW_TAC std_ss [rational_intervals_def,IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_CROSS]
         ++ EQ_TAC
         >> (RW_TAC std_ss []
 	     ++ Q.EXISTS_TAC `x'`
 	     ++ Cases_on `x'`
 	     ++ FULL_SIMP_TAC std_ss [PAIR_EQ])
	 ++ RW_TAC std_ss []
	 ++ Q.EXISTS_TAC `x'`
	 ++ Cases_on `x'`
	 ++ FULL_SIMP_TAC std_ss [PAIR_EQ,EXTENSION])
  ++ METIS_TAC [CROSS_COUNTABLE,Q_COUNTABLE,COUNTABLE_IMAGE]);

val _ = export_theory();
