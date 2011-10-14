(*Interactive use only...

load "translateTheory";
load "intLib";
load "translateLib";
load "signedintTheory";
load "integerTheory";
quietdec := true;
use "extendTranslateScript.sml" handle _ => quietdec := false;
quietdec := false;
*)

open Term Type Thm Theory Tactic Tactical Drule Rewrite boolSyntax;
open Lib bossLib Conv Parse
open sexpTheory arithmeticTheory integerTheory intLib boolTheory
     (*hol_defaxiomsTheory*) translateLib translateTheory;

val fix_def=hol_defaxiomsTheory.fix_def;
val zip_def = hol_defaxiomsTheory.zip_def;
val nfix_def=hol_defaxiomsTheory.nfix_def;
val not_def = hol_defaxiomsTheory.not_def;
val ifix_def = hol_defaxiomsTheory.ifix_def;
val endp_def = hol_defaxiomsTheory.endp_def;
val atom_def = hol_defaxiomsTheory.atom_def;
val zp_def = hol_defaxiomsTheory.zp_def;
val eql_def = hol_defaxiomsTheory.eql_def;

(*****************************************************************************)
(* Start new theory "extendTranslate"                                        *)
(*****************************************************************************)

val _ = new_theory "extendTranslate";

(*****************************************************************************)
(* CHOOSEP_TAC : performs the following for ints & nums:                     *)
(*                                                                           *)
(*      A u {|= integerp a} |- G                                             *)
(*  -------------------------------- CHOOSEP_TAC                             *)
(*  A [int a' / a] |- G [int a' / a]                                         *)
(*                                                                           *)
(*****************************************************************************)

val CHOOSEP_TAC =
    translateLib.CHOOSEP_TAC
    [DECENC_BOOL,DECENC_INT,DECENC_NAT,INT_OF_SEXP_TO_INT,NAT_OF_SEXP_TO_NAT];

(*****************************************************************************)
(* Lemmas to assist proof                                                    *)
(*****************************************************************************)

val FIX_INT = store_thm("FIX_INT",
    ``fix (int a) = int a``,
    RW_TAC arith_ss [fix_def,int_def,acl2_numberp_def,cpx_def,ite_def,
    	   TRUTH_REWRITES]);

(*****************************************************************************)
(* Exponentiation for int and num using acl2 function EXPT                   *)
(*****************************************************************************)

val NUM_OF_ABS = save_thm("NUM_OF_ABS",
    EQ_MP (GSYM (Q.SPEC `ABS p` INT_OF_NUM)) (SPEC_ALL INT_ABS_POS));

val (acl2_expt_def,acl2_expt_ind) =
    (REWRITE_RULE [GSYM ite_def] ## I)
    (sexp.acl2_defn "ACL2::EXPT"
        (`acl2_expt r i =
	 if zip i = nil then
	    (ite (equal (fix r) (int 0)) (int 0)
            	 (if less (int 0) i = nil
		     then (mult (reciprocal r) (acl2_expt r (add i (int 1))))
		     else (mult r (acl2_expt r (add i (unary_minus (int 1)))))))
	 else int 1`,
    WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (SND a))))` THEN
    RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [zip_def,TRUTH_REWRITES,ite_def,GSYM int_def] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES,SEXP_TO_INT_OF_INT] THEN
    ONCE_REWRITE_TAC [GSYM integerTheory.INT_LT] THEN
    REWRITE_TAC [NUM_OF_ABS] THEN
    ARITH_TAC));

val INT_EXPT = store_thm("INT_EXPT",
    ``!b a. int (a ** b) = acl2_expt (int a) (nat b)``,
    Induct THEN ONCE_REWRITE_TAC [acl2_expt_def] THEN
    RW_TAC int_ss [GSYM INT_THMS,nat_def,ite_def,TRUTH_REWRITES,zip_def,
    	   INTEGERP_INT,GSYM int_def,int_exp,FIX_INT,
	   INT_ADD_CALCULATE] THEN
    FULL_SIMP_TAC int_ss [int_gt,INT_LT_CALCULATE] THEN
    RW_TAC int_ss [INT_MULT,nat_def]);

val NAT_EXPT = store_thm("NAT_EXPT",
    ``!b a. nat (a ** b) = acl2_expt (nat a) (nat b)``,
    RW_TAC std_ss [nat_def,INT_EXPT,GSYM INT_EXP]);

(*****************************************************************************)
(* Integer division and modulus                                              *)
(*****************************************************************************)

val (nniq_def,nniq_induction) =
    Defn.tprove(Defn.Hol_defn "nniq"
    `nniq (a:int) (b:int) = (if b <= 0i then 0i else
    	  (if a < b then 0 else 1 + nniq (a - b) b))`,
    WF_REL_TAC `measure (\a.Num (FST a))` THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
    `0 <= a /\ 0 <= a - b` by ARITH_TAC THEN
    RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN ARITH_TAC);

val (acl2_nniq_def,acl2_nniq_ind) =
    (REWRITE_RULE [GSYM ite_def] ## I)
    (sexp.acl2_defn "ACL2::NONNEGATIVE-INTEGER-QUOTIENT"
    (`acl2_nniq i j =
         if (equal (nfix j) (int 0)) = nil then (
	    if less (ifix i) j = nil
	       then (add (int 1) (acl2_nniq (add i (unary_minus j)) j))
	       else (int 0))
            else (int 0)`,
    WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (FST a))))` THEN
    RW_TAC std_ss [equal_def,TRUTH_REWRITES,nfix_def,not_def,
    	    andl_def,ite_def,nat_def,ifix_def] THEN
    FULL_SIMP_TAC int_ss [] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES,INT_CONG] THEN
    REWRITE_TAC	[GSYM integerTheory.INT_LT,NUM_OF_ABS,SEXP_TO_INT_OF_INT] THEN
    ARITH_TAC));

val _ = overload_on("acl2_nniq",
		fst (strip_comb (lhs (snd (strip_forall
		    (concl acl2_nniq_def))))));

val INT_NNIQ = store_thm("INT_NNIQ",
    ``int (nniq a b) = acl2_nniq (int a) (int b)``,
    completeInduct_on `Num (ABS a)` THEN FIX_CI_TAC THEN
    ONCE_REWRITE_TAC [nniq_def,acl2_nniq_def] THEN
    RW_TAC std_ss [nfix_def,ifix_def,nat_def,GSYM INT_THMS,andl_def,equal_def,
    	   ite_def,TRUTH_REWRITES,INTEGERP_INT,not_def] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [INT_CONG,int_gt,INT_NOT_LT,INT_THMS] THEN
    TRY (CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN ARITH_TAC) THEN
    REPEAT AP_TERM_TAC THEN REWRITE_TAC [GSYM INT_THMS] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    RW_TAC std_ss [GSYM integerTheory.INT_LT,NUM_OF_ABS] THEN ARITH_TAC);

val acl2_nniq_correct =
    REWRITE_RULE [SEXP_TO_INT_OF_INT] (AP_TERM ``sexp_to_int`` INT_NNIQ);

val acl2_nniq_rewrite = GSYM INT_NNIQ;

val int_nat_lem = store_thm("int_nat_lem",
    ``0i <= a ==> ?a'. a = & a'``,
    STRIP_TAC THEN Q.EXISTS_TAC `Num a` THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC [INT_OF_NUM]);

val nniq_eq_lem = prove(
    ``~(b = 0) ==> (nniq (& a) (& b) = int_div (& a) (& b))``,
    completeInduct_on `a` THEN ONCE_REWRITE_TAC [nniq_def] THEN
    RW_TAC int_ss [int_div,LESS_DIV_EQ_ZERO,
    	   INT_SUB_CALCULATE,INT_ADD_CALCULATE] THEN
    MATCH_MP_TAC (DECIDE ``0 < b /\ (a = b - 1n) ==> (a + 1 = b)``) THEN
    CONJ_TAC THEN1 (
    	RW_TAC arith_ss [X_LT_DIV]) THEN
    METIS_TAC [DIV_SUB,MULT_CLAUSES,NOT_LESS,DECIDE ``0 < a = ~(a = 0n)``]);

val NNIQ_EQ_DIV = store_thm("NNIQ_EQ_DIV",
    ``0 <= a /\ 0 <= b /\ ~(b = 0) ==> (nniq a b = int_div a b)``,
    STRIP_TAC THEN IMP_RES_TAC int_nat_lem THEN
    REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN MATCH_MP_TAC nniq_eq_lem THEN
    ARITH_TAC);

val acl2_floor_def = sexp.acl2Define "ACL2::FLOOR"
    `acl2_floor a b =
      let q = mult a (reciprocal b) in
      let n = numerator q in
      let d = denominator q in
    	  ite (equal d (int 1)) n
	      (ite (not (less n (int 0)))
	      	   (acl2_nniq n d)
		   (add (unary_minus (acl2_nniq (unary_minus n) d))
		        (unary_minus (int 1))))`;


val acl2_truncate_def = sexp.acl2Define "ACL2::TRUNCATE"
    `acl2_truncate a b =
      let q = mult a (reciprocal b) in
      let n = numerator q in
      let d = denominator q in
    	  ite (equal d (int 1)) n
	      (ite (not (less n (int 0)))
	      	   (acl2_nniq n d)
		   (unary_minus (acl2_nniq (unary_minus n) d)))`;

val INT_SGN_SQUARE = store_thm("INT_SGN_SQUARE",
    ``~(a = 0) ==> (SGN (a * a) = 1)``,
    RW_TAC int_ss [intExtensionTheory.SGN_def,INT_MUL_SIGN_CASES] THEN
    ARITH_TAC);

val INT_ABS_SQUARE = store_thm("INT_ABS_SQUARE",
    ``ABS (b * b) = b * b``,
    RW_TAC int_ss [INT_ABS,INT_MUL_SIGN_CASES] THEN ARITH_TAC);

val rat_mul_lem = prove(``0 < c * b /\ 0 < c ==>
    (abs_rat (abs_frac (a * b,c * b)) = abs_rat (abs_frac (a,c)))``,
    RW_TAC int_ss [ratTheory.RAT_EQ_CALCULATE,fracTheory.NMR,
    	   fracTheory.DNM] THEN
    ARITH_TAC);

open dividesTheory gcdTheory;

val both_divides = prove(``(a * b = c) ==> divides a c /\ divides b c``,
    METIS_TAC [divides_def,MULT_COMM]);

val coprime_equal = prove(
    ``(gcd a d = 1) /\ (gcd b c = 1) /\ (a * b = c * d)
    	   ==> (a = c) /\ (b = d)``,
	DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP both_divides) THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP both_divides o GSYM) THEN
	METIS_TAC [L_EUCLIDES,GCD_SYM,MULT_COMM,DIVIDES_ANTISYM]);

val num_abs_nz = prove(``0 < b \/ ~(b = 0) ==> ~(Num (ABS b) = 0)``,
	DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_ABS_POS] THEN
	ARITH_TAC);

val r1 = prove(``a < 0 ==> (a = ~& (Num ~a))``,
    METIS_TAC [INT_NEG_GT0,INT_OF_NUM,INT_LT_IMP_LE,INT_NEG_EQ]);
val r2 = prove(``0 < a ==> (a = & (Num a))``,
    METIS_TAC [INT_NEG_GT0,INT_OF_NUM,INT_LT_IMP_LE]);

val FACTOR_GCD2 = prove(
    ``!n m. ~(n = 0) /\ ~(m = 0) ==>
    	 ?p q. (n = p * gcd n m) /\ (m = q * gcd n m) /\
	       (gcd p q = 1) /\ ~(gcd n m = 0)``,
	RW_TAC std_ss [FACTOR_OUT_GCD,GCD_EQ_0]);

fun find_gcd term =
	if can (match_term ``gcd a b``) term then [term] else
	(op@ o (find_gcd ## find_gcd)) (dest_comb term) handle _ => [];

fun GCD_FACTOR_GOAL (assums,goal) =
let	val match =  PART_MATCH (fst o dest_eq o dest_neg o last o strip_conj o snd o strip_exists o snd o dest_imp o snd o strip_forall) FACTOR_GCD2 in
(MAP_EVERY (fn x => (STRIP_ASSUME_TAC (SIMP_RULE std_ss (map ASSUME assums) (match x)))) (mk_set (find_gcd goal))) (assums,goal)
end;




val reduce_thm =
 store_thm
   ("reduce_thm",
    ``0 < b /\ 0 < y /\
    ((0 < a /\ 0 < x) \/ (x < 0 /\ a < 0)) /\ (x * b = a * y) ==>
    (int_div x (& (gcd (Num (ABS x)) (Num (ABS y)))) =
     int_div a (& (gcd (Num (ABS a)) (Num (ABS b)))))  /\
    (int_div y (& (gcd (Num (ABS x)) (Num (ABS y)))) =
     int_div b (& (gcd (Num (ABS a)) (Num (ABS b)))))``,
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC int_ss [num_abs_nz,GCD_EQ_0,INT_DIV_0] THEN
    EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN
     		 ASSUME_TAC th handle _ => ALL_TAC) THEN
    EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN
    		 ASSUME_TAC th handle _ => ALL_TAC) THEN
    FULL_SIMP_TAC std_ss [INT_NEG_LT0,GSYM INT_NEG_GT0,INT_LT_CALCULATE,
    		  GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,
		  DECIDE ``0 < a = ~(a = 0n)``,INT_ABS_NEG,NUM_OF_INT,
		  INT_ABS_NUM,INT_NEG_MUL2,INT_MUL,INT_EQ_CALCULATE] THEN
    GCD_FACTOR_GOAL THEN
    ASSUM_LIST (fn list => GEN_REWRITE_TAC
    	       (BINOP_CONV o LAND_CONV o DEPTH_CONV) (bool_rewrites) list) THEN
    RW_TAC std_ss [INT_DIV_RMUL,GSYM INT_MUL,INT_NEG_LMUL,INT_EQ_CALCULATE,
    	   ARITH_PROVE ``~(a = 0) ==> ~(& a = 0i)``] THEN
    PAT_ASSUM ``a * b = c * d:num`` MP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [
        prove(``(a * b * (c * d) = e * d * (g * b)) =
    		(b * (d * (a * c)) = b * (d * (e * g:num)))``,
        HO_MATCH_MP_TAC
	    (PROVE [] ``(a = c) /\ (b = d) ==> (f a b = f c d)``) THEN
        CONJ_TAC THEN
        CONV_TAC (AC_CONV (MULT_ASSOC,MULT_COMM)))] THEN
    RW_TAC std_ss [EQ_MULT_LCANCEL] THEN
    MAP_FIRST (fn x => x THEN
    	      	       REPEAT CONJ_TAC THEN
		       MAP_FIRST FIRST_ASSUM [
		           ACCEPT_TAC,
		           ACCEPT_TAC o ONCE_REWRITE_RULE [GCD_SYM],
			   ACCEPT_TAC o GSYM]) [
        MATCH_MP_TAC (GEN_ALL (DISCH_ALL (CONJUNCT1
	    (UNDISCH coprime_equal)))) THEN
        MAP_EVERY Q.EXISTS_TAC [`q`,`q'`],
	MATCH_MP_TAC (GEN_ALL (DISCH_ALL (CONJUNCT2
	    (UNDISCH coprime_equal)))) THEN
	MAP_EVERY Q.EXISTS_TAC [`p`,`p'`]]);

val div_id_lem = prove(``0 < a ==> (int_div a (& (Num (ABS a))) = 1i)``,
     STRIP_TAC THEN `0 <= a` by ARITH_TAC THEN IMP_RES_TAC int_nat_lem THEN
    RW_TAC int_ss [INT_ABS_NUM] THEN MATCH_MP_TAC INT_DIV_ID THEN
    ARITH_TAC);

val div_zero_lem = prove(``0 < a ==> (int_div 0 (& (Num (ABS a))) = 0i)``,
    STRIP_TAC THEN `0 <= a` by ARITH_TAC THEN IMP_RES_TAC int_nat_lem THEN
    RW_TAC int_ss [INT_ABS_NUM] THEN MATCH_MP_TAC INT_DIV_0 THEN
    ARITH_TAC);

val int_sign_lem = prove(``0i < a /\ 0 < b /\ (x * a = y * b) /\ ~(x = 0) ==>
     (0 < x /\ 0 < y \/ y < 0 /\ x < 0)``,
     STRIP_TAC THEN `0 < x \/ x < 0` by ARITH_TAC THEN Cases_on `y = 0` THEN
     FULL_SIMP_TAC int_ss [] THEN `0 < y \/ y < 0` by ARITH_TAC THEN
     RW_TAC int_ss [] THEN
     METIS_TAC [INT_MUL_SIGN_CASES,
     	       ARITH_PROVE ``0 < a /\ b < 0 ==> ~(a = b:int)``]);

val REDUCE_CONG = store_thm("REDUCE_CONG",
    ``0 < b ==>
    	(reduce (rep_frac (rep_rat (abs_rat (abs_frac (a,b))))) =
	reduce (a,b))``,
    RAT_CONG_TAC THEN
    ONCE_REWRITE_TAC [GSYM fracTheory.FRAC] THEN POP_ASSUM MP_TAC THEN
    Cases_on `a = 0` THEN
    RW_TAC int_ss [fst (EQ_IMP_RULE (SPEC_ALL (CONJUNCT2
    	   (BETA_RULE fracTheory.frac_tybij)))),fracTheory.FRAC_DNMPOS,
	   fracTheory.DNM,fracTheory.NMR] THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [complex_rationalTheory.reduce_def] THEN
    FULL_SIMP_TAC int_ss [GCD_0L,div_id_lem,div_zero_lem,
    		  fracTheory.FRAC_DNMPOS] THEN
    MAP_FIRST MATCH_MP_TAC (map DISCH_ALL (CONJUNCTS (UNDISCH reduce_thm))) THEN
    RW_TAC int_ss [fracTheory.FRAC_DNMPOS,int_sign_lem] THEN
    MATCH_MP_TAC (GEN_ALL int_sign_lem) THEN
    METIS_TAC [fracTheory.FRAC_DNMPOS]);

val num_nz = prove(``0 < a ==> ~(Num a = 0)``,
	ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),
	       INT_LT_IMP_LE] THEN ARITH_TAC);

val gcd_less_eq = prove(``!a b. 0 < b ==> (gcd a b <= b)``,
    completeInduct_on `a` THEN
    ONCE_REWRITE_TAC [gcdTheory.GCD_EFFICIENTLY] THEN
    RW_TAC arith_ss [] THEN
    Cases_on `a <= b` THEN FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL] THENL [
        PAT_ASSUM ``!a.P`` (MP_TAC o SPEC ``b MOD a``) THEN
	RW_TAC arith_ss [DIVISION,DECIDE ``~(a = 0n) ==> 0 < a``] THEN
	POP_ASSUM (MP_TAC o SPEC ``a:num``) THEN RW_TAC arith_ss [],
	ONCE_REWRITE_TAC [gcdTheory.GCD_EFFICIENTLY] THEN
	RW_TAC arith_ss [] THEN
	`a MOD b < a` by (MATCH_MP_TAC LESS_TRANS THEN
	        Q.EXISTS_TAC `b` THEN RW_TAC arith_ss [DIVISION]) THEN
        PAT_ASSUM ``!a.P`` (MP_TAC o SPEC ``a MOD b``) THEN
	RW_TAC arith_ss []]);

val gcd_less_eq_mod = prove(``~(a = 0) /\ ~(b = 0) /\ ~(a MOD b = 0) ==>
    		    gcd (a * b) (b ** 2) <= b * a MOD b``,
    ONCE_REWRITE_TAC [GCD_SYM] THEN
    ONCE_REWRITE_TAC [gcdTheory.GCD_EFFICIENTLY] THEN RW_TAC arith_ss [] THEN
    RW_TAC arith_ss [GSYM (SIMP_RULE arith_ss []
    	   (Q.SPECL [`b`,`a`,`b`] MOD_COMMON_FACTOR))] THEN
    MATCH_MP_TAC (ONCE_REWRITE_RULE [GCD_SYM] gcd_less_eq) THEN
    METIS_TAC [MULT_EQ_0,DECIDE ``0 < a = ~(a = 0n)``]);

val DIVIDES_MOD = store_thm("DIVIDES_MOD",
    ``~(a = 0) ==> (divides a b = (b MOD a = 0))``,
    STRIP_TAC THEN EQ_TAC THEN
    RW_TAC int_ss [compute_divides] THEN
    RW_TAC int_ss [ZERO_MOD,MOD_1,DECIDE ``~(a = 0n) ==> 0 < a``]);

val MOD_GCD = store_thm("MOD_GCD",
    ``~(b = 0) \/ ~(a = 0) ==> (a MOD gcd a b = 0)``,
    STRIP_TAC THEN `~(gcd a b = 0)` by METIS_TAC [GCD_EQ_0] THEN
    RW_TAC int_ss [GSYM DIVIDES_MOD] THEN
    METIS_TAC [GCD_IS_GCD,is_gcd_def]);

val ab_INT_TAC =
    `0 <= b \/ 0 <= ~b` by ARITH_TAC THEN
    `0 <= a \/ 0 <= ~a` by ARITH_TAC THEN
    IMP_RES_TAC int_nat_lem THEN
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV
    		   (REWR_CONV (ARITH_PROVE ``(~a = b) = (a = ~b:int)``))));

val a_INT_TAC =
    `0 <= a \/ 0 <= ~a` by ARITH_TAC THEN
    IMP_RES_TAC int_nat_lem THEN
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV
    		   (REWR_CONV (ARITH_PROVE ``(~a = b) = (a = ~b:int)``)))) THEN
    POP_ASSUM SUBST_ALL_TAC;


val reduced_dnm_pos = store_thm("reduced_dnm_pos",
    ``~(b = 0) ==> 0 < SND (reduce (a * b, b * b))``,
    STRIP_TAC THEN ab_INT_TAC THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss)
    	   [complex_rationalTheory.reduce_def,INT_ABS_NEG,INT_ABS_NUM,
	    INT_MUL_CALCULATE] THEN
    `~(a'' * a'' = 0)` by (REWRITE_TAC [MULT_EQ_0] THEN ARITH_TAC) THEN
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (RAND_CONV
    		   (LAND_CONV (SIMP_CONV arith_ss []))))) THEN
    RW_TAC int_ss [int_div,GCD_EQ_0,X_LT_DIV,
    	   DECIDE ``~(a = 0n) ==> 0 < a``] THEN
    METIS_TAC [gcd_less_eq,DECIDE ``~(a = 0n) ==> 0 < a``]);

val nmrdnm_rewrite = store_thm("nmrdnm_rewrite",
    ``~(b = 0) ==>
      (numerator (mult (int a) (reciprocal (int b))) =
    		int (FST (reduce(a * b, b * b)))) /\
      (denominator (mult (int a) (reciprocal (int b))) =
      		int (SND (reduce(a * b, b * b))))``,
    STRIP_TAC THEN
    `0 < b * b /\ 0 < b * b * (b * b)` by
        (RW_TAC int_ss [INT_MUL_SIGN_CASES] THEN ARITH_TAC) THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss)
       [mult_def,reciprocal_def,numerator_def,denominator_def,
        int_def,cpx_def,sexpTheory.rat_def,complex_rationalTheory.com_0_def,
	translateTheory.rat_def,
	ratTheory.rat_0_def,fracTheory.frac_0_def,ratTheory.RAT_EQ_CALCULATE,
	fracTheory.NMR,fracTheory.DNM,
	complex_rationalTheory.COMPLEX_RECIPROCAL_def,
	ratTheory.RAT_MUL_CALCULATE,fracTheory.FRAC_MULT_CALCULATE,
	ratTheory.RAT_DIV_CALCULATE,fracTheory.FRAC_DIV_CALCULATE,
	ratTheory.RAT_ADD_CALCULATE,fracTheory.FRAC_ADD_CALCULATE,
	complex_rationalTheory.COMPLEX_MULT_def,fracTheory.frac_mul_def,
	ratTheory.RAT_AINV_CALCULATE,fracTheory.FRAC_AINV_CALCULATE,
	ratTheory.RAT_SUB_CALCULATE,fracTheory.FRAC_SUB_CALCULATE,
	INT_SGN_SQUARE,INT_ABS_SQUARE,rat_mul_lem,
	complex_rationalTheory.reduced_nmr_def,
	complex_rationalTheory.reduced_dnm_def,REDUCE_CONG]);

val NEZEROLT = DECIDE ``~(a = 0) ==> 0n < a``;

val div_gcd_lemma = prove(
    ``~(b = 0) ==> (int_div (~ & a) (& (gcd a b)) = ~& (a DIV gcd a b))``,
    RW_TAC int_ss [int_div,GCD_EQ_0,GCD_0L,DECIDE ``~(0 < a) = (a = 0n)``,
    	   ZERO_DIV,NEZEROLT] THEN METIS_TAC [MOD_GCD]);

val div_num_lemma = prove(
    ``~(b = 0) ==> (int_div (~& a) (& b) =
    	  if (a MOD b = 0) then ~(& (a DIV b)):int else ~& (a DIV b + 1))``,
    RW_TAC int_ss [int_div,ZERO_DIV,ZERO_MOD] THEN
    TRY (METIS_TAC [ZERO_MOD,NEZEROLT]) THEN
    ARITH_TAC);

val thms = [DIVISION,ADD_0,MOD_GCD,MULT_EQ_0,GCD_SYM,
     	       GCD_EQ_0,SIMP_CONV arith_ss [] ``a * a:num``,
	       DECIDE ``0 < a = ~(a = 0n)``,
	       DIV_DIV_DIV_MULT,MULT_DIV];

val GCD_LEMMAS = prove(``~(a'' = 0) ==>
    (0 < gcd (a' * a'') (a'' ** 2)) /\
    (0 < a'' ** 2 DIV gcd (a' * a'') (a'' ** 2)) /\
    (a'' ** 2 DIV gcd (a' * a'') (a'' ** 2) * gcd (a' * a'') (a'' ** 2) =
     a'' ** 2) /\
    (a' * a'' DIV a'' ** 2 = a' DIV a'')``,
    RW_TAC int_ss thms THEN METIS_TAC thms);

val reduce_divide_lemma = store_thm("reduce_divide_lemma",
    ``~(b = 0) ==>
    (int_div a b = int_div (FST (reduce (a * b,b * b)))
    	       	   	   (SND (reduce (a * b,b * b))))``,
    STRIP_TAC THEN ab_INT_TAC THEN
    REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss)
  	   [complex_rationalTheory.reduce_def,INT_ABS_NUM,
	    INT_MUL_CALCULATE,INT_ABS_NEG] THEN
    FULL_SIMP_TAC int_ss [INT_DIV_CALCULATE] THEN
    IMP_RES_TAC GCD_LEMMAS THEN
    REPEAT (PAT_ASSUM ``!a.P`` (ASSUME_TAC o Q.SPEC `a'`)) THEN
    FULL_SIMP_TAC int_ss [INT_DIV_CALCULATE,DIV_DIV_DIV_MULT,
    		  div_gcd_lemma,MULT_EQ_0] THEN
    RW_TAC int_ss [div_num_lemma,GSYM int_sub,DIV_DIV_DIV_MULT] THEN
    POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [DIV_MOD_MOD_DIV,
        GSYM (SIMP_RULE arith_ss [] (Q.SPECL [`q`,`p`,`q`] MOD_COMMON_FACTOR)),
	ZERO_DIV,DECIDE ``~(a = 0) = 0n < a``,X_LT_DIV,gcd_less_eq_mod] THEN
    MATCH_MP_TAC gcd_less_eq_mod THEN ASM_REWRITE_TAC [] THEN
    CCONTR_TAC THEN FULL_SIMP_TAC int_ss [GCD_0L] THEN METIS_TAC [ZERO_MOD]);

val GCD_MULT = store_thm("GCD_MULT",
    ``!n a. ~(n = 0) /\ ~(a = 0) ==> (gcd (n * a) a = a)``,
    Induct THEN RW_TAC int_ss [ADD1,LEFT_ADD_DISTRIB,GCD_ADD_L] THEN
    Cases_on `n = 0` THEN FULL_SIMP_TAC int_ss [GCD_0L,GCD_0R] THEN
    METIS_TAC [GCD_SYM]);

val reduce_mod_lemma = prove(``FST (reduce (a * b,b * b)) < 0 /\ ~(b = 0) /\
   ~(SND (reduce (a * b, b * b)) = 1) ==>
       ~(Num (~FST (reduce (a * b, b * b))) MOD
         Num (SND (reduce (a * b, b* b))) = 0)``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [complex_rationalTheory.reduce_def] THEN
    ab_INT_TAC THEN REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [INT_MUL_CALCULATE,INT_ABS_NUM,INT_DIV,GCD_EQ_0,
    		  INT_ABS_NEG] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [int_div,GCD_EQ_0,GCD_0L,GCD_0R,ZERO_DIV,NEZEROLT] THEN
    TRY (METIS_TAC [MOD_GCD,MULT_EQ_0,GCD_SYM]) THEN
    IMP_RES_TAC GCD_LEMMAS THEN
    REPEAT (PAT_ASSUM ``!a.P`` (ASSUME_TAC o Q.SPEC `a'`)) THEN
    RW_TAC int_ss [DIV_MOD_MOD_DIV,GCD_EQ_0,NEZEROLT,X_LT_DIV,
    	   DECIDE ``~(a = 0) = 0n < a``,ONCE_REWRITE_RULE [MULT_COMM]
    	   	  (GSYM (SIMP_RULE arith_ss []
	   	     (Q.SPECL [`n`,`p`,`n`] MOD_COMMON_FACTOR))),NEZEROLT] THEN
    MATCH_MP_TAC gcd_less_eq_mod THEN
    RW_TAC int_ss [GSYM DIVIDES_MOD] THEN
    CCONTR_TAC THEN FULL_SIMP_TAC int_ss [divides_def] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `q = 0` THEN FULL_SIMP_TAC int_ss [] THEN
    `gcd (a'' ** 2 * q) (a'' ** 2) = a'' ** 2` by
    	 RW_TAC int_ss [ONCE_REWRITE_RULE [MULT_COMM] GCD_MULT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [DIVMOD_ID]);

val div_lem = prove(
    ``x < 0 /\ 0 < y /\ ~(y = 0) /\ ~(Num ~x MOD Num y = 0)
    	==> (int_div x y = ~(int_div (~x) y) + ~1)``,
     RW_TAC int_ss [int_div] THEN ARITH_TAC);

val INT_DIV = store_thm("INT_DIV",
    ``~(b = 0) ==> (int (int_div a b) = acl2_floor (int a) (int b))``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [nmrdnm_rewrite,acl2_floor_def,
    	   GSYM INT_THMS,ite_def,TRUTH_REWRITES,acl2_nniq_rewrite,
	   reduce_divide_lemma] THEN
    RW_TAC int_ss [INT_DIV_1] THEN
    MAP_EVERY Q.ABBREV_TAC [`A = FST (reduce (a * b, b * b))`,
                            `B = SND (reduce (a * b, b * b))`] THENL
        (map (fn x => x by (MATCH_MP_TAC NNIQ_EQ_DIV THEN
	     METIS_TAC [reduced_dnm_pos,INT_LE_LT,int_ge,
	     	        INT_NOT_LE,INT_NEG_GE0])))
	     [`nniq (~A) B = int_div (~A) B`,`nniq A B = int_div A B`] THEN
    POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [INT_CONG] THEN
    MATCH_MP_TAC div_lem THEN
    METIS_TAC [reduce_mod_lemma,int_ge,INT_NOT_LE,INT_LE_LT,
    	      INT_NEG_GE0,reduced_dnm_pos]);

val INT_QUOT_DIV = store_thm("INT_QUOT_DIV",
    ``!a b. ~(b = 0) ==>
    	 (a quot b =
	  if (0 <= a = 0 <= b) then int_div a b else ~(int_div (~a) b))``,
    REPEAT GEN_TAC THEN ab_INT_TAC THEN REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
    RW_TAC int_ss [INT_DIV_CALCULATE,ZERO_DIV,NEZEROLT] THEN
    RW_TAC arith_ss [ZERO_DIV,NEZEROLT]);

val reduce_pos_lem = prove(
    ``~(b = 0) /\ ~(a = 0) ==>
    	  ((0 <= a = 0 <= b) = FST (reduce (a * b, b * b)) >= 0)``,
    STRIP_TAC THEN ab_INT_TAC THEN
    FULL_SIMP_TAC int_ss [] THEN
    `0 < gcd (a' * a'') (a'' ** 2)` by RW_TAC int_ss [GCD_LEMMAS] THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss)
           [complex_rationalTheory.reduce_def,int_ge,
	    INT_ABS_NUM,INT_MUL_CALCULATE,INT_ABS_NEG] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [GCD_0L,GCD_0R,INT_DIV_CALCULATE,
	  	   DECIDE ``0 < a ==> ~(a = 0n)``] THEN
    RW_TAC int_ss [int_div,DECIDE ``~(a = 0) = (0n < a)``,
    	   X_LT_DIV,gcd_less_eq] THEN
    METIS_TAC [gcd_less_eq,GCD_SYM,NEZEROLT,MULT_EQ_0,MOD_GCD]);

val reduce_zero_lem = prove(``~(a = 0) ==> (FST (reduce (0,a)) = 0)``,
    RW_TAC (int_ss ++ boolSimps.LET_ss)
  	  [complex_rationalTheory.reduce_def,GCD_0L] THEN
    MATCH_MP_TAC INT_DIV_0 THEN
    METIS_TAC [INT_OF_NUM,INT_ABS_POS,
    	      ARITH_PROVE ``(& a = 0i) = (a = 0n)``,INT_ABS_EQ0]);

val nniq_zero_lem = prove(``nniq 0 a = 0``,
    ONCE_REWRITE_TAC [nniq_def] THEN
    RW_TAC int_ss [] THEN ARITH_TAC);

val reduce_neg_lemma = prove(``~(b = 0) ==>
       (FST (reduce (~a * b, b * b)) = ~FST (reduce (a * b, b* b))) /\
       (SND (reduce (~a * b, b * b)) = SND (reduce (a * b, b* b)))``,
    FULL_SIMP_TAC (int_ss ++ boolSimps.LET_ss)
  		 [complex_rationalTheory.reduce_def,INT_ABS_SQUARE,
		  INT_MUL_CALCULATE,INT_ABS_NEG] THEN
    ab_INT_TAC THEN REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [INT_MUL_CALCULATE,INT_ABS_NUM,INT_ABS_NEG,GCD_0L,
  		integerTheory.INT_DIV,GCD_EQ_0,MULT_EQ_0,NEZEROLT] THEN
    RW_TAC int_ss [int_div,GCD_EQ_0,MULT_EQ_0,NEZEROLT,GCD_0L,ZERO_DIV] THEN
    METIS_TAC [MOD_GCD,GCD_SYM,MULT_EQ_0,NEZEROLT]);

val INT_QUOT = store_thm("INT_QUOT",
    ``~(b = 0) ==> (int (a quot b) = acl2_truncate (int a) (int b))``,
    Cases_on `a = 0` THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [
    	   INT_QUOT_0,nmrdnm_rewrite,acl2_truncate_def,
    	   GSYM INT_THMS,ite_def,TRUTH_REWRITES,acl2_nniq_rewrite,
	   INT_QUOT_DIV,reduce_zero_lem,nniq_zero_lem,
	   reduce_divide_lemma,reduce_neg_lemma] THEN
    RW_TAC int_ss [INT_DIV_1] THEN
    TRY (METIS_TAC [reduce_pos_lem]) THEN
    MAP_EVERY Q.ABBREV_TAC [`A = FST (reduce (a * b, b * b))`,
                            `B = SND (reduce (a * b, b * b))`] THENL
        (map (fn x => x by (MATCH_MP_TAC NNIQ_EQ_DIV THEN
	     METIS_TAC [reduced_dnm_pos,INT_LE_LT,int_ge,
	     	        INT_NOT_LE,INT_NEG_GE0])))
	     [`nniq A B = int_div A B`,`nniq (~A) B = int_div (~A) B`] THEN
    POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [INT_CONG] THEN
    MATCH_MP_TAC div_lem THEN
    METIS_TAC [reduce_mod_lemma,int_ge,INT_NOT_LE,INT_LE_LT,
    	      INT_NEG_GE0,reduced_dnm_pos]);


val acl2_mod_def = sexp.acl2Define "ACL2::MOD"
    `acl2_mod x y = add x (unary_minus (mult (acl2_floor x y) y))`;

val acl2_rem_def = sexp.acl2Define "ACL2::REM"
    `acl2_rem x y = add x (unary_minus (mult (acl2_truncate x y) y))`;

val INT_MOD = store_thm("INT_MOD",
    ``~(b = 0i) ==> (int (a % b) = acl2_mod (int a) (int b))``,
    RW_TAC int_ss [acl2_mod_def,GSYM INT_DIV,GSYM INT_THMS,int_mod,int_sub]);

val INT_REM = store_thm("INT_REM",
    ``~(b = 0i) ==> (int (a rem b) = acl2_rem (int a) (int b))``,
    RW_TAC int_ss [acl2_rem_def,GSYM INT_QUOT,GSYM INT_THMS,int_rem,int_sub]);

(*****************************************************************************)
(* Natural number division and modulus                                       *)
(*****************************************************************************)

val NAT_DIV = store_thm("NAT_DIV",
    ``~(b = 0) ==> (nat (a DIV b) = acl2_floor (nat a) (nat b))``,
    RW_TAC int_ss [nat_def,GSYM INT_DIV]);

val NAT_MOD = store_thm("NAT_MOD",
    ``~(b = 0) ==> (nat (a MOD b) = acl2_mod (nat a) (nat b))``,
    RW_TAC int_ss [nat_def,GSYM INT_MOD]);

(*****************************************************************************)
(* The following proofs are legacy proofs, used in other theories, but no    *)
(* longer required here.                                                     *)
(*****************************************************************************)

open fracTheory ratTheory intExtensionTheory complex_rationalTheory;

val rat_of_int_def = Define
    `rat_of_int x =
    if 0 <= x then & (Num (ABS x))
       	      else rat_ainv (& (Num (ABS x)))`;

val rat_of_int_neg = store_thm("rat_of_int_neg",
    ``rat_of_int ~x = ~rat_of_int x``,
    RW_TAC std_ss [rat_of_int_def] THEN TRY (`x = 0` by ARITH_TAC) THEN
    RW_TAC int_ss [RAT_AINV_0,RAT_AINV_AINV,INT_ABS_NEG]);

val sexp_int_rat = prove(``int a = rat (rat_of_int a)``,
    RW_TAC int_ss [int_def,translateTheory.rat_def,rat_of_int_def,cpx_def,
    	   sexpTheory.rat_def,
    	   rat_0_def,frac_0_def,RAT_OF_NUM_CALCULATE,
	   RAT_AINV_CALCULATE,FRAC_AINV_CALCULATE,ratTheory.RAT_EQ,NMR,DNM,
	   INT_ABS_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN
    ARITH_TAC);

val rat_of_int_div_pos1 = prove(
    ``0 < b /\ 0 <= a ==>
    	(rat_div (rat_of_int a) (rat_of_int b) = abs_rat (abs_frac (a,b)))``,
    RW_TAC std_ss [rat_of_int_def,INT_LE_LT] THEN
    RW_TAC int_ss [INT_ABS_CALCULATE_POS,INT_ABS_CALCULATE_0,
    	   RAT_OF_NUM_CALCULATE,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN
    `~(frac_nmr (abs_frac (b,1)) = 0)` by RW_TAC int_ss [NMR,INT_LT_IMP_NE] THEN
    RW_TAC int_ss [RAT_DIV_CALCULATE,FRAC_DIV_CALCULATE,INT_LT_IMP_NE,
    	   INT_ABS_CALCULATE_POS,SGN_def] THEN
    CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN ARITH_TAC);

val rat_of_int_div_pos = store_thm("rat_of_int_div_pos",
    ``0 < b ==> (rat_div (rat_of_int a) (rat_of_int b) =
    	    	 abs_rat (abs_frac (a,b)))``,
    Cases_on `0 <= a` THEN RW_TAC std_ss [rat_of_int_div_pos1] THEN
    `?c. (a = ~c) /\ 0 <= c` by
        (Q.EXISTS_TAC `~a` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
    RW_TAC int_ss [rat_of_int_neg,GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_LMUL,
    	   	  GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV,RAT_DIV_MULMINV] THEN
    RW_TAC int_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos1]);

val rat_of_int_nz = prove(``~(b = 0) ==> ~(rat_of_int b = 0)``,
    RW_TAC int_ss [rat_of_int_def,INT_ABS_POS,NMR,DNM,RAT_AINV_CALCULATE,
    	   snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),ratTheory.RAT_EQ,
	   RAT_OF_NUM_CALCULATE,FRAC_AINV_CALCULATE] THEN
    ARITH_TAC);

val rat_of_int_div_neg = store_thm("rat_of_int_div_neg",
    ``b < 0 ==> (rat_div (rat_of_int a) (rat_of_int b) =
    	    	 abs_rat (abs_frac (~a,~b)))``,
    DISCH_TAC THEN
    `?c. (b = ~c) /\ 0 < c` by
    	 (Q.EXISTS_TAC `~b` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
    RW_TAC int_ss [rat_of_int_neg,RAT_DIV_MULMINV,GSYM RAT_AINV_RMUL,
    	   GSYM RAT_AINV_MINV,rat_of_int_nz,INT_LT_IMP_NE,
	   GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV] THEN
    RW_TAC std_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos]);

val int_sign_clauses_pos =
    prove(``!b. 0i < b ==> !a. (0 < a * b = 0 < a) /\ (!a. a * b < 0 = a < 0)``,
    REWRITE_TAC [INT_MUL_SIGN_CASES] THEN ARITH_TAC);

val int_sign_clauses_neg =
    prove(``!b. b < 0i ==>
    		  !a. (0 < a * ~b = 0 < a) /\ (!a. a * ~b < 0 = a < 0)``,
    REWRITE_TAC [INT_MUL_SIGN_CASES,ARITH_PROVE ``b < 0 = 0i < ~b``] THEN
    ARITH_TAC);

val neg_reduce_rat = store_thm("neg_reduce_rat",
   ``b < 0 ==> (reduce (rep_frac (rep_rat
       	       	       (rat_div (rat_of_int a) (rat_of_int b)))) =
       	        reduce (~a,~b))``,
    RW_TAC int_ss [rat_of_int_div_neg,rat_of_int_div_pos] THEN
    RAT_CONG_TAC THEN
    POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [NMR,DNM,snd(EQ_IMP_RULE(SPEC_ALL INT_NEG_GT0))] THEN
    (SUBGOAL_THEN ``rep_frac x = (frac_nmr x,frac_dnm x)`` SUBST_ALL_TAC THEN1
        RW_TAC std_ss [frac_nmr_def,frac_dnm_def]) THEN
        `(0 < frac_nmr x /\ a < 0) \/ (frac_nmr x < 0 /\ 0 < a) \/
	 ((frac_nmr x = 0) /\ (a = 0))` by
	  (`(0 < ~a * frac_dnm x /\ 0 < frac_nmr x * ~b) \/
	    ((~a * frac_dnm x = 0) /\ (frac_nmr x * ~b = 0)) \/
	    (~a * frac_dnm x < 0 /\ frac_nmr x * ~b < 0)` by ARITH_TAC THEN
	    ASSUME_TAC (SPEC ``x:frac`` FRAC_DNMPOS) THEN
	    RULE_ASSUM_TAC (REWRITE_RULE (map UNDISCH
	    		   [SPEC ``b:int`` int_sign_clauses_neg,
			    SPEC ``frac_dnm x`` int_sign_clauses_pos])) THEN
        FULL_SIMP_TAC int_ss [] THEN ARITH_TAC) THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] THEN
    RW_TAC int_ss [INT_DIV_0,num_abs_nz,INT_NEG_GT0,
    	   GCD_0L,GCD_0R,FRAC_DNMPOS] THEN
    FIRST [MATCH_MP_TAC (DISCH_ALL (CONJUNCT1
    	  		(UNDISCH_ALL (SPEC_ALL reduce_thm)))),
           MATCH_MP_TAC (DISCH_ALL (CONJUNCT2
	   		(UNDISCH_ALL (SPEC_ALL reduce_thm)))),ALL_TAC] THEN
    RW_TAC int_ss [FRAC_DNMPOS,INT_NEG_GT0,INT_ABS_CALCULATE_POS,INT_LT_IMP_LE,
    	   snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_NE,INT_DIV_ID]);

val pos_reduce_rat = store_thm("pos_reduce_rat",
   ``0 < b ==> (reduce (rep_frac (rep_rat
       	       	       (rat_div (rat_of_int a) (rat_of_int b)))) =
       	        reduce (a,b))``,
    RW_TAC int_ss [rat_of_int_div_pos] THEN
    RAT_CONG_TAC THEN
    POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [NMR,DNM,snd(EQ_IMP_RULE(SPEC_ALL INT_NEG_GT0))] THEN
    (SUBGOAL_THEN ``rep_frac x = (frac_nmr x,frac_dnm x)`` SUBST_ALL_TAC THEN1
        RW_TAC std_ss [frac_nmr_def,frac_dnm_def]) THEN
	`(0 < frac_nmr x /\ 0 < a) \/ (frac_nmr x < 0 /\ a < 0) \/
	 ((frac_nmr x = 0) /\ (a = 0))` by
	     (`(0 < a * frac_dnm x /\ 0 < frac_nmr x * b) \/
	       ((a * frac_dnm x = 0) /\ (frac_nmr x * b = 0)) \/
	       (a * frac_dnm x < 0 /\ frac_nmr x * b < 0)` by ARITH_TAC THEN
	       ASSUME_TAC (SPEC ``x:frac`` FRAC_DNMPOS) THEN
	       RULE_ASSUM_TAC (REWRITE_RULE (map UNDISCH
	       		      [SPEC ``b:int`` int_sign_clauses_pos,
			       SPEC ``frac_dnm x`` int_sign_clauses_pos])) THEN
        FULL_SIMP_TAC int_ss [] THEN ARITH_TAC) THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] THEN
    RW_TAC int_ss [INT_DIV_0,num_abs_nz,INT_NEG_GT0,
    	   	  GCD_0L,GCD_0R,FRAC_DNMPOS] THEN
    FIRST [MATCH_MP_TAC (DISCH_ALL (CONJUNCT1
    	  		(UNDISCH_ALL (SPEC_ALL reduce_thm)))),
           MATCH_MP_TAC (DISCH_ALL (CONJUNCT2
	   		(UNDISCH_ALL (SPEC_ALL reduce_thm)))),ALL_TAC] THEN
    RW_TAC int_ss [FRAC_DNMPOS,INT_ABS_CALCULATE_POS,INT_DIV_ID,INT_LT_IMP_LE,
    	   snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_NE,INT_NEG_GT0]);

val mod_common = store_thm("mod_common",
    ``0 < b /\ 0 < c ==> ((a MOD b = 0) = ((a * c) MOD (b * c) = 0))``,
    REPEAT STRIP_TAC THEN EQ_TAC THEN
    RW_TAC arith_ss [CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM))
    	   (GSYM MOD_COMMON_FACTOR)]);

val int_div_common = store_thm("int_div_common",
    ``~(b = 0) /\ ~(c = 0i) ==> (int_div (a * & b) (c * & b) = int_div a c)``,
    REPEAT STRIP_TAC THEN
    `(a < 0 \/ (a = 0) \/ 0 < a) /\ (c < 0 \/ 0 < c)` by ARITH_TAC THEN
    EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN
    		ASSUME_TAC th handle _ => ALL_TAC) THEN
    EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN
    		ASSUME_TAC th handle _ => ALL_TAC) THEN
    FULL_SIMP_TAC std_ss [INT_NEG_LT0,GSYM INT_NEG_GT0,
    		  INT_LT_CALCULATE,GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,
		  DECIDE ``0 < a = ~(a = 0n)``,INT_ABS_NEG,NUM_OF_INT,
		  INT_ABS_NUM,INT_NEG_MUL2,INT_MUL,
		  INT_EQ_CALCULATE,INT_DIV_NEG,INT_NEGNEG,integerTheory.INT_DIV,
		  ZERO_DIV,INT_DIV_0,INT_NEG_0] THEN
    RW_TAC int_ss [int_div] THEN
    FULL_SIMP_TAC arith_ss [GSYM DIV_DIV_DIV_MULT,
    		  DECIDE ``~(0 < a) = (a = 0n)``,ZERO_DIV,
		  ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] THEN
    CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
    MAP_FIRST MATCH_MP_TAC [DECIDE ``(a = b) ==> (~a ==> ~b)``,
    	      		    DECIDE ``(a = b) ==> (a ==> b)``] THEN
    MATCH_MP_TAC (GSYM (ONCE_REWRITE_RULE [MULT_COMM] mod_common)) THEN
    DECIDE_TAC);


val mod_zero_mult = store_thm("mod_zero_mult",
    ``0 < b ==> ((a MOD b = 0) = (b = 1) \/ (?c. a = b * c))``,
    REPEAT STRIP_TAC THEN EQ_TAC THEN
    Cases_on `b = 1n` THEN RW_TAC arith_ss [] THENL [
    	     ASSUM_LIST (fn list => SUBST_ALL_TAC (SIMP_RULE arith_ss list
	     		(DISCH_ALL (CONJUNCT1 (SPEC ``a:num`` (UNDISCH
				   (SPEC ``b:num`` DIVISION))))))) THEN
             Q.EXISTS_TAC `a DIV b` THEN REFL_TAC,
	     ONCE_REWRITE_TAC [MULT_COMM] THEN MATCH_MP_TAC MOD_EQ_0 THEN
	     FIRST_ASSUM ACCEPT_TAC]);

val gcd_mod = store_thm("gcd_mod",
    ``~(p = q) /\ 1 < q /\ ~(p = 0) /\ ~(q = 0) /\ (gcd p q = 1) ==>
    	  ~(p MOD q = 0)``,
    RW_TAC arith_ss [mod_zero_mult] THEN
    CCONTR_TAC THEN FULL_SIMP_TAC arith_ss [] THEN POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ONCE_REWRITE_RULE [GCD_SYM]
    		   GCD_EFFICIENTLY]) THEN
    POP_ASSUM MP_TAC THEN RW_TAC arith_ss [MOD_EQ_0,GCD_0R]);

(****************************************************************************)
(* SGN : int -> int using acl2 function SIGNUM                              *)
(****************************************************************************)

val acl2_zerop_def = sexp.acl2Define "COMMON-LISP::ZEROP"
    `acl2_zerop x = equal x (int 0)`;

val _ = overload_on("acl2_zerop",
      	fst (strip_comb (lhs (snd (strip_forall (concl acl2_zerop_def))))));

val acl2_minusp_def = sexp.acl2Define "COMMON-LISP::MINUSP"
    `acl2_minusp x = less x (int 0)`;

val _ = overload_on("acl2_minusp",
      	fst (strip_comb (lhs (snd (strip_forall (concl acl2_minusp_def))))));

val acl2_signum_def = sexp.acl2Define "ACL2::SIGNUM"
    `acl2_signum x = ite (equal x (int 0)) (int 0)
    	      	    (ite (less x (int 0)) (int ~1) (int 1))`;

val INT_SGN = store_thm("INT_SGN",``int (SGN x) = acl2_signum (int x)``,
    RW_TAC int_ss [ite_def,GSYM INT_THMS,SGN_def,acl2_signum_def,
    	   TRUTH_REWRITES,bool_def,INT_CONG] THEN
    ARITH_TAC);

(*****************************************************************************)
(* even and odd for natural numbers using acl2 functions evenp and oddp      *)
(*****************************************************************************)

val acl2_evenp_def = sexp.acl2Define "ACL2::EVENP"
    `acl2_evenp x = integerp (mult x (reciprocal (int 2)))`;

val acl2_oddp_def = sexp.acl2Define "ACL2::ODDP"
    `acl2_oddp x = not (acl2_evenp x)`;

val nat_rat = prove(``!a. nat a = rat (& a)``,
    RW_TAC std_ss [nat_def,int_def,translateTheory.rat_def,cpx_def,
    	   sexpTheory.rat_def,rat_0_def,frac_0_def,rat_0,RAT_OF_NUM_CALCULATE]);

val int_rat_n = prove(``!a. int (& a) = rat (& a)``,
    RW_TAC std_ss [nat_rat,GSYM nat_def]);

val rat_2_nz = prove(``~(0 = 2:rat)``,
    RW_TAC int_ss [RAT_EQ_CALCULATE,RAT_OF_NUM_CALCULATE,NMR,DNM]);

val NAT_EVEN = prove(``bool (EVEN a) = acl2_evenp (nat a)``,
    Cases_on `EVEN a` THEN ASM_REWRITE_TAC [] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM ODD_EVEN]) THEN
    IMP_RES_TAC EVEN_ODD_EXISTS THEN
    RW_TAC int_ss [GSYM nat_def,acl2_evenp_def,nat_rat,
    	   GSYM RAT_DIV,rat_2_nz] THEN
    RW_TAC int_ss [translateTheory.rat_def,integerp_def,
    	   IS_INT_EXISTS,bool_def,TRUTH_REWRITES] THEN
    POP_ASSUM MP_TAC THEN RW_TAC int_ss [RAT_LDIV_EQ,rat_2_nz] THENL [
    	   Q.EXISTS_TAC `& m`,
	   `0 <= c \/ 0 <= ~c` by ARITH_TAC THEN IMP_RES_TAC int_nat_lem THEN
    	   RULE_ASSUM_TAC (CONV_RULE (TRY_CONV
    		   (REWR_CONV (ARITH_PROVE ``(~a = b) = (a = ~b:int)``)))) THEN
           POP_ASSUM SUBST_ALL_TAC] THEN
    RW_TAC int_ss [GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,
    	   GSYM RAT_OF_NUM_CALCULATE,RAT_MUL_NUM_CALCULATE,
	   RAT_EQ_NUM_CALCULATE] THEN
    ARITH_TAC);

val NAT_ODD = prove(``bool (ODD a) = acl2_oddp (nat a)``,
    RW_TAC std_ss [acl2_oddp_def,GSYM NAT_EVEN,bool_def,TRUTH_REWRITES,not_def,
    	   ite_def,EVEN_ODD]);

val int_mul_lem = prove(``(?c. i * 8 = c * 16) = ~(i % 2 = 1)``,
    `!c. (i * 8 = c * 16) = (i = c * 2)` by ARITH_TAC THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    EQ_TAC THEN STRIP_TAC THENL [
    	   ALL_TAC,
	   Q.EXISTS_TAC `int_div i 2`] THEN
    FULL_SIMP_TAC int_ss [] THEN
    ARITH_TAC);


val EVENP_INTMOD = store_thm("EVENP_INTMOD",
    ``(|= acl2_evenp (int i)) = ~(i % 2 = 1)``,
    RW_TAC int_ss [acl2_evenp_def,reciprocal_def,int_def,sexpTheory.cpx_def,
    	   mult_def,complex_rationalTheory.com_0_def,sexpTheory.rat_def,
	   ratTheory.rat_0_def,fracTheory.frac_0_def,ratTheory.RAT_EQ_CALCULATE,
	   fracTheory.NMR,fracTheory.DNM,
	   complex_rationalTheory.COMPLEX_RECIPROCAL_def,
	   complex_rationalTheory.COMPLEX_MULT_def,ratTheory.RAT_DIV_CALCULATE,
	   ratTheory.RAT_MUL_CALCULATE,fracTheory.frac_mul_def,
	   ratTheory.RAT_ADD_CALCULATE,fracTheory.frac_add_def,
	   fracTheory.frac_div_def,fracTheory.frac_minv_def,
	   fracTheory.frac_sgn_def,RAT_AINV_CALCULATE,fracTheory.frac_ainv_def,
	   RAT_SUB_CALCULATE,fracTheory.frac_sub_def,EVAL ``SGN 4``] THEN
    RW_TAC int_ss [integerp_def,TRUTH_REWRITES,IS_INT_EXISTS,
       	   ratTheory.rat_0_def,fracTheory.frac_0_def,ratTheory.RAT_EQ_CALCULATE,
	   fracTheory.NMR,fracTheory.DNM,GSYM INT_MUL_ASSOC,int_mul_lem]);

(*****************************************************************************)
(* Arithmetic shift left for int and num using acl2 function ASH             *)
(*****************************************************************************)

val acl2_ash_def = sexp.acl2Define "ACL2::ASH"
    `acl2_ash i c = acl2_floor (mult (ifix i) (acl2_expt (int 2) c)) (int 1)`;

val INT_ASH = store_thm("INT_ASH",
    ``int (i * 2 ** c) = acl2_ash (int i) (nat c)``,
    RW_TAC int_ss [acl2_ash_def,GSYM INT_EXPT,ifix_def,nat_def,
    	   INTEGERP_INT,ite_def,TRUTH_REWRITES,GSYM INT_THMS,GSYM INT_DIV]);

val NAT_ASH = store_thm("NAT_ASH",
    ``nat (i * 2 ** c) = acl2_ash (nat i) (nat c)``,
    RW_TAC std_ss [nat_def,GSYM INT_EXP,GSYM integerTheory.INT_MUL,INT_ASH]);

(*****************************************************************************)
(* Maximum and minimum theories for int and num,                             *)
(* using acl2 functions max and min                                          *)
(*****************************************************************************)

val acl2_max_def =
    sexp.acl2Define "ACL2::MAX" `acl2_max x y = ite (less y x) x y`;
val acl2_min_def =
    sexp.acl2Define "ACL2::MIN" `acl2_min x y = ite (less x y) x y`;

val NAT_MAX = store_thm("NAT_MAX",
    ``nat (MAX x y) = acl2_max (nat x) (nat y)``,
    RW_TAC int_ss [MAX_DEF,acl2_max_def,ite_def,TRUTH_REWRITES,NAT_CONG] THEN
    FULL_SIMP_TAC int_ss [GSYM NAT_THMS,TRUTH_REWRITES]);

val NAT_MIN = store_thm("NAT_MIN",
    ``nat (MIN x y) = acl2_min (nat x) (nat y)``,
    RW_TAC int_ss [MIN_DEF,acl2_min_def,ite_def,TRUTH_REWRITES,NAT_CONG] THEN
    FULL_SIMP_TAC int_ss [GSYM NAT_THMS,TRUTH_REWRITES]);

val INT_MAX = store_thm("INT_MAX",
    ``int (int_max x y) = acl2_max (int x) (int y)``,
    RW_TAC int_ss [acl2_max_def,INT_MAX,GSYM INT_THMS,ite_def,
    	   TRUTH_REWRITES,INT_CONG] THEN ARITH_TAC);

val INT_MIN = store_thm("INT_MIN",
    ``int (int_min x y) = acl2_min (int x) (int y)``,
    RW_TAC int_ss [acl2_min_def,INT_MIN,GSYM INT_THMS,ite_def,
    	   TRUTH_REWRITES,INT_CONG] THEN ARITH_TAC);

(*****************************************************************************)
(* ABS:int -> int, using acl2 function ABS                                   *)
(*****************************************************************************)

val acl2_abs_def =
    sexp.acl2Define "ACL2::ABS"
    `acl2_abs x = ite (less x (int 0)) (unary_minus x) x`;

val INT_ABS = store_thm("INT_ABS",
    ``int (ABS x) = acl2_abs (int x)``,
    RW_TAC int_ss [INT_ABS,acl2_abs_def,GSYM INT_THMS,ite_def,
    	   TRUTH_REWRITES,INT_CONG] THEN ARITH_TAC);

(*****************************************************************************)
(* List theorems:                                                            *)
(*                                                                           *)
(* acl2 functions: binary-append, revappend, reverse, take, nthcdr, butlast, *)
(*                 nth, last, strip_cars, strip_cdrs, pairlis$               *)
(*                                                                           *)
(*****************************************************************************)

open listTheory;

val CAR_NIL = store_thm("CAR_NIL",``car nil = nil``,
    RW_TAC int_ss [car_def,nil_def]);

val CDR_NIL = store_thm("CDR_NIL",``cdr nil = nil``,
    RW_TAC int_ss [cdr_def,nil_def]);

val CONSP_NIL = store_thm("CONSP_NIL",``consp nil = nil``,
    RW_TAC int_ss [consp_def,nil_def]);

val (acl2_append_def,acl2_append_ind) =
    sexp.acl2_defn "ACL2::BINARY-APPEND"
    (`acl2_append x y =
    		  ite (consp x) (cons (car x) (acl2_append (cdr x) y)) y`,
    WF_REL_TAC `measure (sexp_size o FST)` THEN
    Cases THEN RW_TAC arith_ss [cdr_def,nil_def,consp_def,sexp_size_def]);

val _ = overload_on("acl2_append",
    fst (strip_comb (lhs (snd (strip_forall (concl acl2_append_def))))));

val APPEND_NIL = store_thm("APPEND_NIL",
    ``!x. acl2_append nil x = x``,
    Cases THEN ONCE_REWRITE_TAC [acl2_append_def] THEN
    RW_TAC int_ss [ite_def,endp_def,atom_def,TRUTH_REWRITES,
    	   not_def]);

val LIST_APPEND = store_thm("LIST_APPEND",
    ``!x y f. list f (x ++ y) = acl2_append (list f x) (list f y)``,
    completeInduct_on `LENGTH x + LENGTH y` THEN Cases THEN
    ONCE_REWRITE_TAC [acl2_append_def] THEN
    REWRITE_TAC [list_def,APPEND,LENGTH,
    		APPEND_NIL,CAR_NIL,CDR_NIL,CONSP_NIL,consp_def,ite_def,
		TRUTH_REWRITES,car_def,cdr_def,sexp_11] THEN
    FIX_CI_TAC THEN RW_TAC int_ss [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    CCONTR_TAC THEN FULL_SIMP_TAC int_ss [ADD_CLAUSES] THEN
    PROVE_TAC [prim_recTheory.LESS_SUC_REFL]);

val (acl2_revappend_def,acl2_revappend_ind) =
    (PURE_REWRITE_RULE [GSYM ite_def] ## I)
    (sexp.acl2_defn "ACL2::REVAPPEND"
        (`acl2_revappend x y =
	    if (consp x = nil) then y
	       else acl2_revappend (cdr x) (cons (car x) y)`,
    WF_REL_TAC `measure (sexp_size o FST)` THEN
    Cases THEN RW_TAC arith_ss [cdr_def,nil_def,consp_def,sexp_size_def]));

val REVAPPEND_NIL = store_thm("REVAPPEND_NIL",
    ``!x. acl2_revappend nil x = x``,
    Cases THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN
    RW_TAC int_ss [ite_def,endp_def,atom_def,TRUTH_REWRITES,
    	   not_def]);

val LIST_REV = store_thm("LIST_REV",
    ``!x y f. list f (REV x y) = acl2_revappend (list f x) (list f y)``,
    Induct THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN
    RW_TAC int_ss [list_def,REV_DEF,consp_def,car_def,cdr_def,CONSP_NIL,
    	   CAR_NIL,CDR_NIL,REVAPPEND_NIL,ite_def,TRUTH_REWRITES]);

val acl2_reverse_def =
    sexp.acl2Define "COMMON-LISP::REVERSE" `acl2_reverse x =
        ite (stringp x)
          (coerce (acl2_revappend (coerce x (csym "LIST")) nil) (csym "STRING"))
          (acl2_revappend x nil)`;

val _ = overload_on ("acl2_reverse",
    fst (strip_comb (lhs (snd (strip_forall (concl acl2_reverse_def))))));

val LIST_REVERSE = store_thm("LIST_REVERSE",
    ``!l. list f (REVERSE l) = acl2_reverse (list f l)``,
    RW_TAC int_ss [REVERSE_REV,LIST_REV,acl2_reverse_def,list_def,ite_def] THEN
    Cases_on `l` THEN FULL_SIMP_TAC int_ss [stringp_def,list_def,nil_def]);

val ZP_RECURSE_LEMMA = store_thm("ZP_RECURSE_LEMMA",
    ``!i. (zp i = nil) ==>
          sexp_to_nat (add (unary_minus (nat 1)) i) < sexp_to_nat i``,
    RW_TAC int_ss [zp_def,ite_def,TRUTH_REWRITES,GSYM int_def] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,nat_def,TRUTH_REWRITES] THEN
    FULL_SIMP_TAC int_ss [int_ge,INT_NOT_LE] THEN
    `?i. (i' = &i) /\ 0 < i` by
    	 METIS_TAC [INT_OF_NUM,integerTheory.INT_LT,INT_LT_IMP_LE] THEN
    RW_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE,GSYM nat_def,
    	   SEXP_TO_NAT_OF_NAT]);

val (acl2_firstnac_def,firstnac_ind) =
    sexp.acl2_defn "ACL2::FIRST-N-AC"
    (`acl2_firstnac i l ac =
      ite (zp i)
      	  (acl2_reverse ac)
	  (acl2_firstnac (add (unary_minus (nat 1)) i)
	  		 (cdr l) (cons (car l) ac))`,
    WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
    METIS_TAC [ZP_RECURSE_LEMMA]);

val _ = overload_on ("acl2_firstnac",
    fst (strip_comb (lhs (snd (strip_forall (concl acl2_firstnac_def))))));

val acl2_take_def =
    sexp.acl2Define "ACL2::TAKE" `acl2_take n l = acl2_firstnac n l nil`;

val _ = overload_on ("acl2_take",
    fst (strip_comb (lhs (snd (strip_forall (concl acl2_take_def))))));

val REVERSE_NIL = store_thm("REVERSE_NIL",
    ``acl2_reverse nil = nil``,
    RW_TAC int_ss [acl2_reverse_def,REVAPPEND_NIL,ite_def,
    	   REWRITE_CONV [nil_def] ``stringp nil``,TRUTH_REWRITES,stringp_def]);

fun mk_rev x =
    GSYM (SIMP_RULE std_ss [list_def] (Q.SPECL [x,`[]`,`I`]
    	 (INST_TYPE [alpha |-> ``:sexp``] LIST_REV)));

fun mk_list x = GSYM (SIMP_CONV std_ss [list_def] ``list f ^(x)``);

val FIRST_NAC_LEMMA = store_thm("FIRST_NAC_LEMMA",
    ``!b a f h x. a <= LENGTH b ==> (
        cons (f h) (acl2_firstnac (nat a) (list f b) (list f x)) =
             acl2_firstnac (nat a) (list f b) (list f (x ++ [h])))``,
    Induct THEN (Cases ORELSE (GEN_TAC THEN Cases)) THEN
    ONCE_REWRITE_TAC [acl2_firstnac_def] THEN
    RW_TAC int_ss [GSYM NAT_EQUAL_0,TRUTH_REWRITES,ite_def,GSYM LIST_REVERSE,
    	   REVERSE_APPEND,REVERSE_DEF,APPEND,list_def,car_def,cdr_def,LENGTH,
	   nat_def,GSYM INT_THMS,INT_ADD_CALCULATE] THEN
    RW_TAC int_ss [GSYM nat_def,mk_list ``a::b``,APPEND]);

val LIST_FIRSTN = store_thm("LIST_FIRSTN",
    ``!l n. (n <= LENGTH l) ==>
    	 (list f (FIRSTN n l) = acl2_take (nat n) (list f l))``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC int_ss [acl2_take_def,rich_listTheory.FIRSTN,LENGTH,list_def] THEN
    ONCE_REWRITE_TAC [acl2_firstnac_def] THEN
    CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV acl2_firstnac_def))) THEN
    RW_TAC int_ss [car_def,cdr_def,ite_def,TRUTH_REWRITES,REVERSE_NIL,
    	   GSYM NAT_EQUAL_0,nat_def,GSYM INT_THMS,ADD1,
	   INT_SUB_CALCULATE,INT_ADD_CALCULATE,
	   REWRITE_RULE [nat_def] (GSYM NAT_EQUAL_0)] THEN
    Cases_on `l` THEN
    RW_TAC int_ss [acl2_reverse_def,stringp_def,ite_def,TRUTH_REWRITES,
    	   mk_rev `[x]`,REV_DEF,list_def,car_def,cdr_def,CAR_NIL,CDR_NIL,
	   GSYM nat_def] THEN
    FULL_SIMP_TAC int_ss [LENGTH,mk_list ``[h']``,mk_list ``[h';h]``] THEN
    MATCH_MP_TAC (SIMP_RULE std_ss [APPEND]
    		 (Q.SPECL [`b`,`a`,`f`,`h`,`[h']`] FIRST_NAC_LEMMA)) THEN
    DECIDE_TAC);


val SEXP_ADD_COMM = store_thm("SEXP_ADD_COMM",
    ``!a b. add a b = add b a``,
    Cases THEN Cases THEN RW_TAC int_ss [add_def,COMPLEX_ADD_def] THEN
    Cases_on `c` THEN Cases_on `c'` THEN
    PROVE_TAC [RAT_ADD_COMM,COMPLEX_ADD_def]);

val (acl2_nthcdr_def,nthcdr_ind) =
    sexp.acl2_defn "ACL2::NTHCDR"
        (`acl2_nthcdr n l =
	  ite (zp n) l (acl2_nthcdr (add n (unary_minus (nat 1))) (cdr l))`,
    WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
    METIS_TAC [ZP_RECURSE_LEMMA,SEXP_ADD_COMM]);

val LIST_BUTFIRSTN = store_thm("LIST_BUTFIRSTN",
    ``!n l. n <= LENGTH l ==>
    	 (list f (BUTFIRSTN n l) = acl2_nthcdr (nat n) (list f l))``,
    Induct_on `l` THEN Cases_on `n` THEN
    ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN
    RW_TAC arith_ss [rich_listTheory.BUTFIRSTN,list_def,LENGTH,TRUTH_REWRITES,
    	   GSYM NAT_EQUAL_0,ite_def,GSYM NAT_PRE,cdr_def]);

val acl2_butlast_def =
    sexp.acl2Define "ACL2::BUTLAST"
    `acl2_butlast l n =
    let lng = len l in
    	ite (less n lng) (acl2_take (add lng (unary_minus n)) l) nil`;

val LIST_BUTLASTN = store_thm("LIST_BUTLASTN",
    ``!n l. n <= LENGTH l ==>
    	 (list f (BUTLASTN n l) = acl2_butlast (list f l) (nat n))``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [rich_listTheory.BUTLASTN_FIRSTN,
    	   LIST_FIRSTN,acl2_butlast_def,GSYM LIST_LENGTH,nat_def,GSYM INT_THMS,
	   ite_def,TRUTH_REWRITES,INT_ADD_CALCULATE] THEN
    SUBGOAL_THEN ``LENGTH l - n = 0`` SUBST_ALL_TAC THEN1 ARITH_TAC THEN
    RW_TAC int_ss [acl2_take_def] THEN
    ONCE_REWRITE_TAC [acl2_firstnac_def] THEN
    RW_TAC int_ss [zp_def,ite_def,TRUTH_REWRITES,GSYM INT_THMS,
    	   INTEGERP_INT,GSYM int_def,not_def,REVERSE_NIL]);

val LIST_LASTN = store_thm("LIST_LASTN",
    ``!n l. n <= LENGTH l ==>
    	 (list f (LASTN n l) = acl2_nthcdr (nat (LENGTH l - n)) (list f l))``,
    RW_TAC arith_ss [rich_listTheory.LASTN_BUTFIRSTN,LIST_BUTFIRSTN]);

val (acl2_nth_def,nth_ind) =
    sexp.acl2_defn "ACL2::NTH"
    (`acl2_nth n l =
    	  ite (consp l)
	      (ite (zp n) (car l)
	      	   (acl2_nth (add (unary_minus (nat 1)) n) (cdr l))) nil`,
    WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
    METIS_TAC [ZP_RECURSE_LEMMA,SEXP_ADD_COMM]);

val LIST_EL = store_thm("LIST_EL",
    ``!n l. n < LENGTH l ==>
    	 (encode (EL n l) = acl2_nth (nat n) (list encode l))``,
    Induct_on `n` THEN Cases_on `l` THEN ONCE_REWRITE_TAC [acl2_nth_def] THEN
    FULL_SIMP_TAC arith_ss [EL,HD,TL,car_def,cdr_def,list_def,LENGTH,
        ite_def,TRUTH_REWRITES,GSYM NAT_EQUAL_0,consp_def,nat_def,GSYM INT_THMS,
	INT_ADD_CALCULATE]);

val (acl2_make_list_ac_def,acl2_make_list_ac_ind) =
    sexp.acl2_defn "ACL2::MAKE-LIST-AC"
    (`acl2_make_list_ac n val ac =
        ite (zp n) ac (acl2_make_list_ac (add (int ~1) n) val (cons val ac))`,
    WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (FST a))))` THEN
    RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [zp_def,TRUTH_REWRITES,ite_def,GSYM int_def] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES,SEXP_TO_INT_OF_INT] THEN
    ONCE_REWRITE_TAC [GSYM integerTheory.INT_LT] THEN
    REWRITE_TAC [NUM_OF_ABS] THEN
    ARITH_TAC);

 val LIST_GENLIST_LEMMA = store_thm("LIST_GENLIST_LEMMA",
     ``!n v f L. list f (GENLIST (K v) n ++ L) =
      	   acl2_make_list_ac (nat n) (f v) (list f L)``,
     Induct THEN
     ONCE_REWRITE_TAC [acl2_make_list_ac_def] THEN
     RW_TAC int_ss [rich_listTheory.GENLIST,nat_def,zp_def,ite_def,
     	    TRUTH_REWRITES,GSYM INT_THMS,GSYM int_def,not_def,list_def,
	    rich_listTheory.SNOC_REVERSE_CONS,REVERSE_DEF,APPEND,
	    GSYM APPEND_ASSOC,
	    REVERSE_REVERSE,ADD1,INT_ADD_CALCULATE,INTEGERP_INT] THEN
     CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN ARITH_TAC);

val LIST_GENLIST = save_thm("LIST_GENLIST",
    REWRITE_RULE [listTheory.APPEND_NIL,list_def]
    		 (GEN_ALL (Q.SPECL [`n`,`v`,`f`,`[]`] LIST_GENLIST_LEMMA)));
(*

The following theorems have not yet been converted...

val acl2_subseq_def = acl2Define "ACL2::SUBSEQ-LIST"
	`acl2_subseq lst start end = acl2_take (nfix (add end (unary_minus start))) (acl2_nthcdr start lst)`;

val LIST_SEG = prove(``n + s <= LENGTH l ==> (list f (SEG n s l) = acl2_subseq (list f l) (nat s) (nat (n + s)))``,
	RW_TAC arith_ss [SEG_FIRSTN_BUTFISTN,acl2_subseq_def,LIST_BUTFIRSTN,LENGTH_BUTFIRSTN,LIST_FIRSTN] THEN
	RW_TAC int_ss [GSYM NAT_SUB]);

val len_cons = prove(``len (cons a b) = add (int 1) (len b)``,
	RW_TAC std_ss [ONCE_REWRITE_CONV [len_def] ``len (cons a b)``,ite_def,TRUTH_REWRITES,consp_def,cdr_def,nat_def]);

val zp_rewrite = prove(``(|= zp (nat n)) = (n = 0)``,
	RW_TAC int_ss [zp_def,integerp_def,GSYM int_def,nat_def,GSYM INT_LT,GSYM BOOL_NOT,ite_def,
		TRUTH_REWRITES,INTEGERP_INT]);

val len_nth =
	prove(``!n l. (|= not (less (len l) (nat n))) ==> (len (acl2_nthcdr (nat n) l) = add (len l) (unary_minus (nat n)))``,
	Induct_on `l` THEN REPEAT STRIP_TAC THEN
	TRY (ONCE_REWRITE_TAC [len_def] THEN ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [len_def]) THEN
		FULL_SIMP_TAC arith_ss [ite_def,TRUTH_REWRITES,consp_def,GSYM NAT_LT,GSYM BOOL_NOT,cdr_def] THEN
		SUBGOAL_THEN ``n = 0n`` SUBST_ALL_TAC THEN1 DECIDE_TAC THEN
		RW_TAC int_ss [nat_def,GSYM INT_SUB,zp_def,GSYM int_def,INTEGERP_INT,GSYM INT_LT,ite_def,
			TRUTH_REWRITES,GSYM BOOL_NOT,consp_def] THEN NO_TAC) THEN
	ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN FULL_SIMP_TAC std_ss [len_cons,ite_def,TRUTH_REWRITES,zp_rewrite,cdr_def] THEN
	RW_TAC int_ss [nat_def,GSYM INT_ADD,len_cons,GSYM INT_UNARY_MINUS] THEN
	ASSUME_TAC (SPEC ``l':sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM INT_ADD,nat_def,GSYM INT_LT,GSYM BOOL_NOT,TRUTH_REWRITES,
		integerTheory.INT_SUB,GSYM int_sub] THEN
	`~(x < n - 1)` by ARITH_TAC THEN RES_TAC THEN
	POP_ASSUM SUBST_ALL_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM INT_SUB] THEN AP_TERM_TAC THEN
	Cases_on `n` THEN FULL_SIMP_TAC int_ss [ADD1] THEN ARITH_TAC);


val subseq_lem1 =
	prove(``a <= b /\ (|= not (less (len l) (nat b))) ==> |= not (less (len (acl2_nthcdr (nat a) l)) (nat (b - a)))``,
		REPEAT STRIP_TAC THEN
		`|= not (less (len l) (nat a))` by
			(ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN
			FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM BOOL_NOT,nat_def,TRUTH_REWRITES]) THEN
		RW_TAC arith_ss [len_nth] THEN
		ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN
		FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM BOOL_NOT,nat_def,TRUTH_REWRITES,GSYM INT_SUB,NOT_LESS,
			integerTheory.INT_SUB]);

val acl2_nthcdr_nil = prove(``acl2_nthcdr n nil = nil``,
	Cases_on `|= natp n` THENL [
		CHOOSEP_TAC THEN FULL_SIMP_TAC std_ss [NATP_NAT] THEN Induct_on `n'`,
		ALL_TAC] THEN
	ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN
	RW_TAC int_ss [ite_def,zp_rewrite,TRUTH_REWRITES,nat_def,GSYM INT_SUB,ADD1,integerTheory.INT_SUB,
		cdr_def,AP_TERM ``cdr`` nil_def] THEN
	FULL_SIMP_TAC std_ss [TRUTH_REWRITES,nat_def,natp_def,zp_def,ite_def,GSYM int_def,ANDL_REWRITE,not_def] THEN
	Cases_on `|= integerp n` THEN TRY CHOOSEP_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM INT_EQUAL,TRUTH_REWRITES,GSYM BOOL_NOT] THEN
	DISJ1_TAC THEN ARITH_TAC);

val subseq_lem2 = prove(``!l s. ~(|= not (less (len l) (nat s))) ==> (len (acl2_nthcdr (nat s) l) = nat 0)``,
	Induct_on `l` THEN REPEAT STRIP_TAC THEN
	TRY (ONCE_REWRITE_TAC [len_def] THEN ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [len_def]) THEN
		FULL_SIMP_TAC arith_ss [ite_def,TRUTH_REWRITES,consp_def,GSYM NAT_LT,GSYM BOOL_NOT,cdr_def,
			zp_rewrite,acl2_nthcdr_nil] THEN NO_TAC) THEN
	ONCE_REWRITE_TAC [acl2_nthcdr_def] THEN
	FULL_SIMP_TAC int_ss [nat_def,len_cons,ite_def,TRUTH_REWRITES,zp_rewrite,GSYM INT_SUB,cdr_def] THEN
	ASSUME_TAC (SPEC ``l':sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN RW_TAC std_ss [] THEN
	FULL_SIMP_TAC int_ss [nat_def,GSYM INT_ADD,GSYM INT_LT,GSYM BOOL_NOT,TRUTH_REWRITES,integerTheory.INT_SUB] THEN
	`x < s - 1` by ARITH_TAC THEN RES_TAC THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (ARITH_PROVE ``1 + &x < 0i ==> F``)));

val LISTP_SUBSEQ = prove(``(|= not (less (len l) e)) /\ (|= listp f l) /\ (|= natp s) /\ (|= natp e) ==>
				|= listp f (acl2_subseq l s e)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	REWRITE_TAC [acl2_subseq_def] THEN
	MATCH_MP_TAC LISTP_TAKE THEN
	RW_TAC std_ss [LISTP_NTHCDR,NATP_NFIX] THEN
	FULL_SIMP_TAC std_ss [NATP_NAT] THEN
	RW_TAC int_ss [nat_def,GSYM INT_SUB,nfix_def,ANDL_REWRITE,INTEGERP_INT,ite_def,
		TRUTH_REWRITES,integerTheory.INT_SUB,GSYM INT_LT,GSYM BOOL_NOT,INT_NOT_LT,INT_LE_SUB_LADD] THENL [
		Cases_on `|= not (less (len l) (nat s'))` THENL [
			RW_TAC std_ss [GSYM nat_def,len_nth] THEN
			ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN CHOOSEP_TAC,
			RW_TAC std_ss [GSYM nat_def,subseq_lem2]] THEN
		FULL_SIMP_TAC int_ss [nat_def,GSYM INT_SUB,GSYM INT_LT,GSYM BOOL_NOT,TRUTH_REWRITES] THEN ARITH_TAC,
		RW_TAC std_ss [GSYM nat_def] THEN
		METIS_TAC [subseq_lem1]]);

val (acl2_last_def,acl2_last_ind) =
	acl2_defn "ACL2::LAST"
		(`acl2_last l = ite (consp (cdr l)) (acl2_last (cdr l)) l`,
		WF_REL_TAC `measure sexp_size` THEN Cases THEN
		RW_TAC arith_ss [consp_def,car_def,cdr_def,sexp_size_def,nil_def]);

val LIST_LAST = prove(``!l. ~(l = []) ==> (encode (LAST l) = car (acl2_last (list encode l)))``,
	Induct THEN ONCE_REWRITE_TAC [acl2_last_def] THEN
	TRY (Cases_on `l`) THEN
	RW_TAC std_ss [car_def,list_def,LAST_DEF,ite_def,consp_def,cdr_def,TRUTH_REWRITES] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss []);

val LISTP_LAST = prove(``!l. (|= listp p l) ==> |= listp p (acl2_last l)``,
	Induct THEN ONCE_REWRITE_TAC [acl2_last_def] THEN
	RW_TAC std_ss [listp_def,TRUTH_REWRITES,ite_def,consp_def,car_def,cdr_def]);

val LIST_FRONT = prove(``!l. ~(l = []) ==> (list f (FRONT l) = acl2_butlast (list f l) (nat 1))``,
	Induct THEN
	RW_TAC arith_ss [prove(``!l. ~(l = []) ==> 1 <= LENGTH l``,Cases THEN RW_TAC arith_ss [ADD1,LENGTH]),
		GSYM LIST_BUTLASTN,BUTLASTN_1]);

val LIST_LEN = prove(``nat (LEN l n) = add (nat n) (len (list f l))``,
	RW_TAC std_ss [LEN_LENGTH_LEM,GSYM LIST_LENGTH,GSYM NAT_ADD,ADD_COMM]);


val LIST_REV = prove(``list f (REV l1 l2) = acl2_revappend (list f l1) (list f l2)``,
	RW_TAC std_ss [revappend_append,REV_REVERSE_LEM,LIST_APPEND,LIST_REVERSE]);


val (strip_cars_def,strip_cars_ind) =
	acl2_defn "ACL2::STRIP-CARS"
		(`strip_cars x = ite (consp x) (cons (caar x) (strip_cars (cdr x))) nil`,
		WF_REL_TAC `measure sexp_size` THEN
		Cases THEN
		RW_TAC arith_ss [consp_def,car_def,cdr_def,sexp_size_def]);

val (strip_cdrs_def,strip_cdrs_ind) =
	acl2_defn "ACL2::STRIP-CDRS"
		(`strip_cdrs x = ite (consp x) (cons (cdar x) (strip_cdrs (cdr x))) nil`,
		WF_REL_TAC `measure sexp_size` THEN
		Cases THEN
		RW_TAC arith_ss [consp_def,car_def,cdr_def,sexp_size_def]);

val LIST_UNZIP = prove(``pair (list f) (list g) (UNZIP l) =
				cons (strip_cars (list (pair f g) l)) (strip_cdrs (list (pair f g) l))``,
	Induct_on `l` THEN TRY Cases THEN
	ONCE_REWRITE_TAC [strip_cdrs_def,strip_cars_def] THEN
	RW_TAC std_ss [pair_def,list_def,UNZIP,consp_def,ite_def,TRUTH_REWRITES,AP_TERM ``consp`` nil_def,
		caar_def,cdar_def,car_def,cdr_def] THEN
	FULL_SIMP_TAC std_ss [pair_def,sexp_11]);

val LISTP_STRIP_CARS = prove(``(|= listp (pairp f g) l) ==> (|= listp f (strip_cars l))``,
	Induct_on `l` THEN ONCE_REWRITE_TAC [strip_cars_def] THEN
	RW_TAC std_ss [listp_def,TRUTH_REWRITES,equal_def,consp_def,caar_def,AP_TERM ``listp f`` nil_def,
		GSYM nil_def,car_def,cdr_def,ite_def] THEN
	Cases_on `l` THEN FULL_SIMP_TAC std_ss [pairp_def,TRUTH_REWRITES,car_def,ite_def]);

val LISTP_STRIP_CDRS = prove(``(|= listp (pairp f g) l) ==> (|= listp g (strip_cdrs l))``,
	Induct_on `l` THEN ONCE_REWRITE_TAC [strip_cdrs_def] THEN
	RW_TAC std_ss [listp_def,TRUTH_REWRITES,equal_def,consp_def,cdar_def,AP_TERM ``listp f`` nil_def,
		GSYM nil_def,car_def,cdr_def,ite_def] THEN
	Cases_on `l` THEN FULL_SIMP_TAC std_ss [pairp_def,TRUTH_REWRITES,cdr_def,ite_def]);


val (pairlist_def,pairlist_ind) =
	acl2_defn "ACL2::PAIRLIS$"
		(`pairlist x y = ite (consp x) (cons (cons (car x) (car y)) (pairlist (cdr x) (cdr y))) nil`,
		WF_REL_TAC `measure (sexp_size o FST)` THEN
		Cases THEN
		RW_TAC arith_ss [consp_def,car_def,cdr_def,sexp_size_def]);

val LIST_ZIP = prove(``!l1 l2. (LENGTH l1 = LENGTH l2) ==>
			(list (pair f g) (ZIP (l1,l2)) = pairlist (list f l1) (list g l2))``,
	Induct_on `l1` THEN Cases_on `l2` THEN
	ONCE_REWRITE_TAC [pairlist_def] THEN
	RW_TAC std_ss [ZIP,list_def,consp_def,car_def,cdr_def,ite_def,TRUTH_REWRITES,LENGTH,pair_def]);

val LISTP_PAIRLIST = prove(``!x y. (|= equal (len x) (len y)) /\ (|= listp f x) /\ (|= listp g y) ==>
				(|= listp (pairp f g) (pairlist x y))``,
	Induct_on `x` THEN Cases_on `y` THEN ONCE_REWRITE_TAC [len_def] THEN
	ONCE_REWRITE_TAC [pairlist_def] THEN
	RW_TAC std_ss [TRUTH_REWRITES,ite_def,consp_def,car_def,cdr_def,equal_def,listp_def,
		AP_TERM ``listp f`` nil_def,GSYM nil_def,pairp_def,len_cons] THEN
	FULL_SIMP_TAC std_ss [len_cons] THEN
	REPEAT (PAT_ASSUM ``!y:sexp. P y`` (STRIP_ASSUME_TAC o SPEC ``s0:sexp``)) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN
	ASSUME_TAC (SPEC ``x':sexp`` NATP_LEN) THEN
	ASSUME_TAC (SPEC ``s0:sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN
	RW_TAC arith_ss [NATP_NAT,GSYM NAT_ADD,NAT_CONG,GSYM nat_def,equal_def,TRUTH_REWRITES]);

(*****************************************************************************)
(* String theorems: string-append                                            *)
(*****************************************************************************)

val acl2_strcat_def = acl2Define "ACL2::STRING-APPEND" `acl2_strcat s1 s2 = coerce (acl2_append (coerce s1 (sym "COMMON-LISP" "LIST")) (coerce s2 (sym "COMMON-LISP" "LIST"))) (sym "COMMON-LISP" "STRING")`;

val STRING_STRCAT = prove(``str (STRCAT s1 s2) = acl2_strcat (str s1) (str s2)``,
	RW_TAC std_ss [acl2_strcat_def,coerce_rewrite,GSYM LIST_APPEND,stringTheory.STRCAT]);

val list_chr_cong = prove(``(list chr a = list chr b) = (a = b)``,
	measureInduct_on `LENGTH (a ++ b)` THEN Cases THEN Cases THEN
	RW_TAC std_ss [list_def,APPEND,nil_def] THEN
	POP_ASSUM (STRIP_ASSUME_TAC o SPEC (listSyntax.mk_append(mk_var("t",``:char list``),``t':char list``))) THEN
	FULL_SIMP_TAC arith_ss [LENGTH,LENGTH_APPEND]);

val length_lemma1 = prove(``!a b c. LENGTH a < LENGTH b ==> ~(a = b ++ c)``,
	Induct_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [LENGTH,APPEND]);

val length_lemma2 = prove(``!a b c. ~(a = FIRSTN (LENGTH a) b) ==> ~(b = a ++ c)``,
	Induct_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [LENGTH,APPEND,rich_listTheory.FIRSTN] THEN METIS_TAC []);

val STRING_PREFIX = prove(``bool (isPREFIX s1 s2) = ite (not (less (length (str s2)) (length (str s1))))
							(equal (coerce (str s1) (sym "COMMON-LISP" "LIST")) (acl2_take (length (str s1)) (coerce (str s2) (sym "COMMON-LISP" "LIST")))) nil``,
	RW_TAC std_ss [coerce_rewrite,GSYM STRING_LENGTH,GSYM NAT_LT,ite_def,TRUTH_REWRITES,equal_def,bool_def,
		prove(``!a. (bool a = t) = a``,Cases THEN RW_TAC std_ss [bool_def,TRUTH_REWRITES]),stringTheory.STRLEN_THM,GSYM LIST_FIRSTN,NOT_LESS,
		DECIDE ``~(a <= b) ==> b <= a:num``,list_chr_cong,stringTheory.isPREFIX_STRCAT,GSYM BOOL_NOT,stringTheory.STRCAT] THEN
	GEN_REWRITE_TAC (STRIP_QUANT_CONV o ONCE_DEPTH_CONV) bool_rewrites [GSYM stringTheory.IMPLODE_EXPLODE] THEN
	REWRITE_TAC [stringTheory.EXPLODE_IMPLODE,stringTheory.IMPLODE_11] THEN
	TRY (Q.EXISTS_TAC `IMPLODE (BUTFIRSTN (LENGTH (EXPLODE s1)) (EXPLODE s2))`) THEN
	METIS_TAC [length_lemma1,NOT_LESS_EQUAL,length_lemma2,rich_listTheory.APPEND_FIRSTN_BUTFIRSTN,stringTheory.EXPLODE_IMPLODE]);

val LISTP_EXPLODE = prove(``!x. |= listp characterp (coerce x (sym "COMMON-LISP" "LIST"))``,
	Cases THEN RW_TAC std_ss [coerce_def,coerce_string_to_list_def,LISTP_NIL,list_rewrite,LISTP_LIST,CHARACTERP_CHAR]);

val STRINGP_IMPLODE = prove(``!x. |= stringp (coerce x (sym "COMMON-LISP" "STRING"))``,
	Cases THEN RW_TAC std_ss [coerce_def,coerce_list_to_string_def,STRINGP_STRING]);

val NATP_LENGTH = prove(``!x. |= natp (length x)``,
	Cases_on `|= stringp x` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES,length_def,NATP_LEN]);

val STRINGP_STRCAT = prove(``!s1 s2. |= stringp (acl2_strcat s1 s2)``,
	RW_TAC std_ss [acl2_strcat_def,STRINGP_IMPLODE]);
*)

(*****************************************************************************)
(* FCPs                                                                      *)
(*****************************************************************************)

open fcpTheory;

val fcp_encode_def =
    Define `fcp_encode f (:'b) (x:'a ** 'b) = list f (V2L x)`;
val fcp_decode_def =
    Define `fcp_decode f (:'b) x =
	    if LENGTH (sexp_to_list I x) = dimindex(:'b)
	       then L2V (sexp_to_list f x):('a ** 'b)
	       else FCP i. f nil`;

val fcp_detect_def =
    Define `fcp_detect f (:'b) x =
    	    listp f x /\ (LENGTH (sexp_to_list I x) = dimindex(:'b))`;

val fcp_fix_def =
    Define `fcp_fix f (:'b) x =
    	    if LENGTH (sexp_to_list I x) = dimindex(:'b)
	       then fix_list f x
	       else fix_list f (fcp_encode I (:'b) ((FCP i.nil):sexp ** 'b))`;

val ENCDECMAP_FCP = store_thm("ENCDECMAP_FCP",
    ``fcp_decode g (:'b) o fcp_encode f (:'b) = FCP_MAP (g o f)``,
    REWRITE_TAC [FUN_EQ_THM,fcp_encode_def,fcp_decode_def,combinTheory.o_THM,
    		REWRITE_RULE [FUN_EQ_THM,combinTheory.o_THM] ENCDECMAP_LIST,
		LENGTH_MAP,LENGTH_V2L,FCP_MAP]);

val ENCDETALL_FCP = store_thm("ENCDETALL_FCP",
    ``fcp_detect g (:'b) o fcp_encode f (:'b) = FCP_EVERY (g o f)``,
    REWRITE_TAC [FUN_EQ_THM,fcp_encode_def,fcp_decode_def,combinTheory.o_THM,
    		REWRITE_RULE [FUN_EQ_THM,combinTheory.o_THM] ENCDETALL_LIST,
		fcp_detect_def,FCP_EVERY,FCP_MAP,LENGTH_MAP,LENGTH_V2L,
		REWRITE_RULE [FUN_EQ_THM,combinTheory.o_THM] ENCDECMAP_LIST]);

local
open rich_listTheory
val length_s2l = prove(
    ``!x. LENGTH (sexp_to_list f x) = LENGTH (sexp_to_list g x)``,
    Induct THEN ASM_REWRITE_TAC [sexp_to_list_def,LENGTH]);
val map_fcp_lem = prove(
    ``!n x' x''.
    	 (!i. i < n ==> (EL i x' = ((FCP i. x):'a ** 'b) ' i)) /\
	 (!i. i < n ==> (EL i x'' = ((FCP i. f x):'c ** 'b) ' i)) /\
	 n <= dimindex(:'b) /\ (LENGTH x' = n) /\ (LENGTH x'' = n)
	 ==> (MAP f x' = x'')``,
    REWRITE_TAC [LISTS_EQ] THEN Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [EL,TL,HD,MAP,LENGTH,FCP_BETA,LENGTH_MAP] THEN
    Cases_on `i` THEN FULL_SIMP_TAC arith_ss [EL,HD,TL,EL_MAP] THENL [
        REPEAT (PAT_ASSUM ``!i. P ==> Q`` (MP_TAC o Q.SPEC `0`)),
	REPEAT (PAT_ASSUM ``!i. P ==> Q`` (MP_TAC o Q.SPEC `SUC n`))] THEN
    RW_TAC arith_ss [EL,HD,TL,FCP_BETA]);
in
val MAP_V2L = store_thm("MAP_V2L",
    ``MAP f (V2L ((FCP i. x):'a ** 'b)) = V2L ((FCP i. f x):'c ** 'b)``,
    RW_TAC arith_ss [V2L_def] THEN SELECT_ELIM_TAC THEN
    RW_TAC arith_ss [exists_v2l_thm] THEN SELECT_ELIM_TAC THEN
    RW_TAC arith_ss [exists_v2l_thm,map_fcp_lem] THEN
    MATCH_MP_TAC map_fcp_lem THEN
    Q.EXISTS_TAC `dimindex(:'b)` THEN RW_TAC arith_ss []);
val DECENCFIX_FCP = store_thm("DECENCFIX_FCP",
    ``fcp_encode f (:'b) o fcp_decode g (:'b) = fcp_fix (f o g) (:'b)``,
    REPEAT (CHANGED_TAC (
    	    RW_TAC std_ss [FUN_EQ_THM,fcp_encode_def,fcp_decode_def,
	    	   fcp_fix_def,fcp_detect_def,combinTheory.o_THM])) THEN1
        METIS_TAC [combinTheory.o_THM,V2L_L2V,length_s2l,DECENCFIX_LIST,
		  ENCDECMAP_LIST,LENGTH_MAP,LENGTH_V2L] THEN
    REWRITE_TAC [GSYM DECENCFIX_LIST,combinTheory.o_THM,
    		REWRITE_RULE [combinTheory.o_THM,FUN_EQ_THM] ENCDECMAP_LIST,
		MAP_V2L,
		ENCDECMAP_FCP,combinTheory.I_THM,combinTheory.I_o_ID])
end;

val HD_BUTFIRST_EL = store_thm("HD_BUTFIRST_EL",
    ``!b a. a < LENGTH b ==> (HD (BUTFIRSTN a b) = EL a b)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [rich_listTheory.BUTFIRSTN,LENGTH,HD,TL,EL]);

val FCP_INDEX = store_thm("FCP_INDEX",
    ``a < dimindex(:'b) ==>
    	(fcp_encode f (:'b) m = M) /\ (nat a = A) ==>
		    (f (m ' a) = car (acl2_nthcdr A M))``,
    RW_TAC arith_ss [fcp_encode_def] THEN
    `a < LENGTH (V2L m) /\ (LENGTH (BUTFIRSTN a (V2L m)) = dimindex(:'b) - a)`
         by RW_TAC arith_ss [LENGTH_V2L,rich_listTheory.LENGTH_BUTFIRSTN] THEN
    Tactical.REVERSE (SUBGOAL_THEN
    	     ``(?x y. BUTFIRSTN a (V2L m) = x::y)`` ASSUME_TAC) THEN
    REPEAT (CHANGED_TAC (RW_TAC arith_ss [GSYM LIST_HD,GSYM LIST_BUTFIRSTN,
    	   			HD_BUTFIRST_EL,EL_V2L])) THEN
    Cases_on `BUTFIRSTN a (V2L m)` THEN FULL_SIMP_TAC int_ss [LENGTH] THEN
    METIS_TAC []);


 val (acl2_update_nth_def,acl2_update_nth_ind) =
     sexp.acl2_defn "ACL2::UPDATE-NTH"
     (`acl2_update_nth key val l =
        ite (zp key) (cons val (cdr l))
          (cons (car l) (acl2_update_nth (add (int ~1) key) val (cdr l)))`,
     WF_REL_TAC `measure (Num o ABS o sexp_to_int o FST)` THEN
     RW_TAC int_ss [zp_def,ite_def,TRUTH_REWRITES,GSYM int_def] THEN
     CHOOSEP_TAC THEN
     REWRITE_TAC [GSYM integerTheory.INT_LT,NUM_OF_ABS] THEN
     FULL_SIMP_TAC int_ss [GSYM INT_THMS,not_def,ite_def,TRUTH_REWRITES,
     		   INTEGERP_INT,SEXP_TO_INT_OF_INT] THEN
     FULL_SIMP_TAC int_ss [int_ge,INT_NOT_LE] THEN
     MAP_EVERY IMP_RES_TAC [INT_LT_IMP_LE,int_nat_lem] THEN
     POP_ASSUM SUBST_ALL_TAC THEN
     RW_TAC int_ss [INT_ADD_CALCULATE,INT_ABS_NUM,INT_ABS_NEG] THEN
     ARITH_TAC);

val update_def = Define `
    (update (SUC n) y (x::xs) = x::update n y xs) /\
    (update 0 y (x::xs) = y::xs) /\
    (update _ y [] = [])`;

val LIST_UPDATE = store_thm("LIST_UPDATE",
    ``!x y z. x < LENGTH z ==>
    	 (list f (update x y z) = acl2_update_nth (nat x) (f y) (list f z))``,
    Induct THEN GEN_TAC THEN Cases THEN
    ONCE_REWRITE_TAC [acl2_update_nth_def] THEN
    RW_TAC int_ss [update_def,list_def,ite_def,TRUTH_REWRITES,zp_def,
    	   nat_def,INTEGERP_INT,GSYM int_def,GSYM INT_THMS,not_def,cdr_def,
	   car_def,CAR_NIL,CDR_NIL,ADD1,INT_ADD_CALCULATE,LENGTH] THEN
    FULL_SIMP_TAC int_ss [int_gt]);

local
open wordsTheory;
val length_update = prove(``!y a b. LENGTH (update a b y) = LENGTH y``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [update_def,LENGTH]);
val el_lem = prove(``!i. ~(0 = i) ==> (EL i (a::x) = EL i (b::x))``,
    Cases THEN RW_TAC arith_ss [EL,TL]);
val el_update1 = prove(``!a b y. a < LENGTH y ==> (EL a (update a b y) = b)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [LENGTH,update_def,EL,HD,TL]);
val el_update2 = prove(
    ``!a b c y. c < LENGTH y /\ ~(c = a) ==> (EL c (update a b y) = EL c y)``,
    Induct THEN REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [update_def,EL,LENGTH,HD,TL]);
val update_lem = prove(``!n x y a b.
    (LENGTH x = n) /\ (LENGTH y = n) /\
    (n <= dimindex (:'b)) /\
    (!i. i < n ==> (EL i x = (a :+ b) (m:'a ** 'b) ' i)) /\
    (!i. i < n ==> (EL i y = (m:'a ** 'b) ' i)) ==>
    (x = update a b y)``,
    REWRITE_TAC [LISTS_EQ] THEN Induct THEN
    REPEAT (Cases ORELSE GEN_TAC) THEN
    RW_TAC arith_ss [update_def,EL,LENGTH,length_update] THEN
    Cases_on `i` THEN
    RW_TAC arith_ss [EL,FCP_UPDATE_def,FCP_BETA,
    	   DIMINDEX_GT_0,HD,TL,el_update1] THENL [
        REPEAT (PAT_ASSUM ``!(x:num).P`` (MP_TAC o Q.SPEC `SUC n`)),
	REPEAT (PAT_ASSUM ``!(x:num).P`` (MP_TAC o Q.SPEC `0`)),
	ALL_TAC] THEN
     RW_TAC arith_ss [EL,TL,HD] THEN
     MAP_FIRST (fn t =>
        t by
             (REPEAT (PAT_ASSUM ``!(x:num).P`` (MP_TAC o Q.SPEC `SUC n`)) THEN
	 RW_TAC arith_ss [EL,TL]) THEN
     	 POP_ASSUM SUBST_ALL_TAC THEN
     	 CONV_TAC SYM_CONV THEN MATCH_MP_TAC el_update2 THEN
     	 RW_TAC arith_ss [])
     [`(m:'a ** 'b) ' (SUC n) = EL n t''`,`(m:'a ** 'b) ' (SUC n) = EL n t'`]);
in
val UPDATE_V2L = store_thm("UPDATE_V2L",
    ``!a b m. V2L ((a :+ b) m) = update a b (V2L m)``,
    REPEAT GEN_TAC THEN
    CONV_TAC (LAND_CONV (REWRITE_CONV [fcpTheory.V2L_def])) THEN
    SELECT_ELIM_TAC THEN RW_TAC arith_ss [fcpTheory.exists_v2l_thm] THEN
    REWRITE_TAC [fcpTheory.V2L_def] THEN SELECT_ELIM_TAC THEN
    RW_TAC arith_ss [fcpTheory.exists_v2l_thm] THEN
    MATCH_MP_TAC update_lem THEN
    Q.EXISTS_TAC `dimindex(:'b)` THEN RW_TAC arith_ss [])
end

val ENCMAPENC_FCP = store_thm("ENCMAPENC_FCP",
    ``fcp_encode g (:'b) o FCP_MAP f = fcp_encode (g o f) (:'b)``,
    RW_TAC std_ss [fcp_encode_def,FCP_MAP,combinTheory.o_THM,FUN_EQ_THM,
    	   GSYM (REWRITE_RULE [combinTheory.o_THM,FUN_EQ_THM] ENCMAPENC_LIST)]
	   THEN
    METIS_TAC [V2L_L2V,LENGTH_MAP,LENGTH_V2L]);

val MAP_COMPOSE_FCP = store_thm("MAP_COMPOSE_FCP",
    ``FCP_MAP f o FCP_MAP g = FCP_MAP (f o g)``,
    RW_TAC int_ss [FCP_MAP,combinTheory.o_THM,FUN_EQ_THM,
    	   GSYM rich_listTheory.MAP_MAP_o] THEN
    METIS_TAC [V2L_L2V,LENGTH_MAP,LENGTH_V2L]);

val FIXID_FCP = store_thm("FIXID_FCP",
    ``(!x. p x ==> (f x = x)) ==>
      !x. fcp_detect p (:'b) x ==> (fcp_fix f (:'b) x = x)``,
    RW_TAC int_ss [fcp_fix_def,fcp_detect_def] THEN
    MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO]
    		 (CONV_RULE RIGHT_IMP_FORALL_CONV FIXID_LIST)) THEN
    PROVE_TAC []);

val DETDEAD_FCP = store_thm("DETDEAD_FCP",
    ``~fcp_detect p (:'b) nil``,
    RW_TAC int_ss [fcp_detect_def,sexp_to_list_def,nil_def,LENGTH,
    	   wordsTheory.DIMINDEX_GT_0,DECIDE ``~(0 = a) = 0n < a``]);

val GENERAL_DETECT_FCP = store_thm("GENERAL_DETECT_FCP",
    ``fcp_detect f (:'b) x ==> fcp_detect (K T) (:'b) x``,
    RW_TAC int_ss [fcp_detect_def] THEN
    IMP_RES_TAC GENERAL_DETECT_LIST);

val FCP_UPDATE = store_thm("FCP_UPDATE",
    ``!a b m. a < dimindex (:'b) ==>
    	 (fcp_encode f (:'b) ((a :+ b) (m:'a ** 'b)) =
	  acl2_update_nth (nat a) (f b) (fcp_encode f (:'b) m))``,
    RW_TAC int_ss [fcp_encode_def,GSYM LIST_UPDATE,LENGTH_V2L,UPDATE_V2L]);

val MAPID_FCP = store_thm("MAPID_FCP",
    ``FCP_MAP I = I``,
    RW_TAC int_ss [FUN_EQ_THM,combinTheory.o_THM,combinTheory.I_THM,FCP_MAP,
    	   quotient_listTheory.LIST_MAP_I,V2L_def,L2V_def] THEN
    SELECT_ELIM_TAC THEN
    RW_TAC int_ss [exists_v2l_thm,CART_EQ,FCP_BETA]);

val ALLID_FCP = store_thm("ALLID_FCP",
    ``FCP_EVERY (K T) = K T``,
    RW_TAC int_ss [FUN_EQ_THM,combinTheory.o_THM,combinTheory.K_THM,FCP_EVERY,
    	   V2L_def,L2V_def,translateTheory.ALLID_LIST]);

val EL_GENLIST = store_thm("EL_GENLIST",
    ``!n. i < n ==> (EL i (GENLIST (K x) n) = x)``,
    Induct THEN
    RW_TAC int_ss [rich_listTheory.GENLIST,rich_listTheory.SNOC_REVERSE_CONS,
    	   REVERSE_DEF,REVERSE_REVERSE] THEN
    `LENGTH (GENLIST (K x) n) = n` by
    	    METIS_TAC [LESS_EQ_REFL,rich_listTheory.LENGTH_GENLIST] THEN
    `i < LENGTH (GENLIST (K x) n) \/ LENGTH (GENLIST (K x) n) <= i` by
       	    DECIDE_TAC THEN
    RW_TAC int_ss [rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] THEN
    `i - n = 0` by FULL_SIMP_TAC arith_ss [ADD1] THEN
    RW_TAC int_ss [EL,HD]);

val V2L_VALUE = store_thm("V2L_VALUE",
    ``(V2L ((FCP i. v) : 'a ** 'b)) = GENLIST (K v) (dimindex (:'b))``,
    RW_TAC std_ss [EL_GENLIST,LISTS_EQ,EL_V2L,rich_listTheory.LENGTH_GENLIST,
    	   LENGTH_V2L,FCP_BETA]);

val FCP_VALUE = store_thm("FCP_VALUE",
    ``fcp_encode f (:'b) (FCP i. v)
    		 = acl2_make_list_ac (nat (dimindex (:'b))) (f v) nil``,
    RW_TAC int_ss [fcp_encode_def,V2L_VALUE,LIST_GENLIST]);

(*****************************************************************************)
(* FCP words                                                                 *)
(*****************************************************************************)

open signedintTheory;

(*****************************************************************************)
(* Coding function definitions                                               *)
(*****************************************************************************)

val word_encode_def =
    Define `word_encode (:'b) (x:'b word) = int (sw2i x)`;
val word_decode_def =
    Define `word_decode (:'b) x = (i2sw (sexp_to_int x)) : 'b word`;
val word_detect_def =
    Define `word_detect (:'b) x =
    	   ((sexp_to_bool o  integerp) x) /\
	   sexp_to_int x < 2 ** (dimindex (:'b) - 1) /\
	   ~(2 ** (dimindex (:'b) - 1)) <= sexp_to_int x`;
val word_fix_def =
    Define `word_fix (:'b) x = int (extend (sexp_to_int x) (dimindex (:'b)))`;

(*****************************************************************************)
(* Coding function proofs                                                    *)
(*****************************************************************************)

val word_detect_thm =
    REWRITE_RULE [combinTheory.o_THM,sexp_to_bool_def] word_detect_def;

val ENCDECMAP_WORD = store_thm("ENCDECMAP_WORD",
    ``word_decode (:'b) o word_encode (:'b) = I``,
    RW_TAC int_ss [word_encode_def,word_decode_def,combinTheory.o_THM,
    	   FUN_EQ_THM,SEXP_TO_INT_OF_INT,i2sw_sw2i,wordsTheory.sw2sw_id]);

val DECENCFIX_WORD = store_thm("DECENCFIX_WORD",
    ``word_encode (:'b) o word_decode (:'b) = word_fix (:'b)``,
    RW_TAC int_ss [word_encode_def,word_decode_def,word_fix_def,
    	   combinTheory.o_THM,FUN_EQ_THM,sw2i_i2sw]);

val ENCDETALL_WORD = store_thm("ENCDETALL_WORD",
    ``word_detect (:'b) o word_encode (:'b) = K T``,
    RW_TAC int_ss [combinTheory.o_THM,FUN_EQ_THM,combinTheory.K_THM,
    	   word_detect_thm,word_encode_def,INTEGERP_INT,SEXP_TO_INT_OF_INT,
	   sw2i_def,TOP_BIT_LE] THEN
    RW_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE,DIMINDEX_DOUBLE,
    	   w2n_lt_full]);

val FIXID_WORD = store_thm("FIXID_WORD",
    ``!x. word_detect (:'b) x ==> (word_fix (:'b) x = x)``,
    RW_TAC int_ss [word_detect_thm,word_fix_def] THEN
    Q.ABBREV_TAC `i = sexp_to_int x` THEN
    `0 <= i \/ 0 <= ~i` by ARITH_TAC THEN IMP_RES_TAC int_nat_lem THEN
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV
    		   (REWR_CONV (ARITH_PROVE ``(~a = b) = (a = ~b:int)``)))) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [EXTEND_POS_EQ,EXTEND_NEG_EQ,EXTEND_NEG_NEG,
    		  LESS_OR_EQ,wordsTheory.DIMINDEX_GT_0] THEN
    METIS_TAC [INT_OF_SEXP_TO_INT]);

val DETDEAD_WORD = store_thm("DETDEAD_WORD",
    ``!x. ~word_detect (:'b) nil``,
    RW_TAC int_ss [word_detect_thm,DETDEAD_INT,GSYM sexp_to_bool_def]);

val WORD_CONG = store_thm("WORD_CONG",
    ``(word_encode (:'a) a = word_encode (:'a) b) = (a = b)``,
    RW_TAC int_ss [word_encode_def,INT_CONG,GSYM sw2i_eq]);

val WORD_FLATTEN = save_thm("WORD_FLATTEN",
     REWRITE_RULE [GSYM (REWRITE_CONV [combinTheory.o_THM,sexp_to_bool_def]
     		  		      ``(sexp_to_bool o integerp) v``)]
     		  (AP_TERM ``bool`` (SPEC_ALL word_detect_thm)));

(*****************************************************************************)
(* Auxiliary rewrites                                                        *)
(*****************************************************************************)

val INT_SW2I = save_thm("INT_SW2I",GSYM word_encode_def);


(*****************************************************************************)
(* ACL2 definitions: and, not, ior etc...                                    *)
(*****************************************************************************)

val INT_DIV2_LT = store_thm("INT_DIV2_LT",
    ``~(i = 0) /\ ~(i = ~1) ==> (ABS (int_div i 2) < ABS i)``,
    STRIP_TAC THEN
    `0 <= i \/ 0 <= ~i` by ARITH_TAC THEN IMP_RES_TAC int_nat_lem THEN
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV
    		   (REWR_CONV (ARITH_PROVE ``(~a = b) = (a = ~b:int)``)))) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [INT_ABS_NEG,INT_DIV_CALCULATE,INT_ABS_NUM,DIV_LT_X,
   		  int_div] THEN
    REPEAT (CHANGED_TAC (RW_TAC int_ss [INT_ABS_NEG,INT_ABS_NUM,
    	  INT_ADD_CALCULATE,DECIDE ``a + 1 < b = a < b - 1n``,DIV_LT_X,
	  LEFT_SUB_DISTRIB])) THEN
    `~(a' = 2)` by (CCONTR_TAC THEN FULL_SIMP_TAC int_ss []) THEN
    DECIDE_TAC);


val (acl2_logand_def,acl_logand_ind) = sexp.acl2_defn "ACL2::binary_logand"
    (`acl2_logand i j =
        ite (zip i) (cpx 0 1 0 1)
          (ite (zip j) (cpx 0 1 0 1)
             (ite (eql i (cpx (~1) 1 0 1)) j
                (ite (eql j (cpx (~1) 1 0 1)) i
                   ((\x j i.
                       add x
                         (ite (acl2_evenp i) (cpx 0 1 0 1)
                            (ite (acl2_evenp j) (cpx 0 1 0 1) (cpx 1 1 0 1))))
                      (mult (cpx 2 1 0 1)
                         (acl2_logand (acl2_floor i (cpx 2 1 0 1))
                            (acl2_floor j (cpx 2 1 0 1)))) j i))))`,
    WF_REL_TAC `measure (Num o ABS o sexp_to_int o FST)` THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC int_ss [zip_def,ite_def,TRUTH_REWRITES,
    		  GSYM int_def,eql_def] THEN
    CHOOSEP_TAC THEN RES_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES,SEXP_TO_INT_OF_INT,
    		  GSYM (MATCH_MP INT_DIV (ARITH_PROVE ``~(2 = 0i)``))] THEN
    REWRITE_TAC [GSYM integerTheory.INT_LT,NUM_OF_ABS] THEN
    PROVE_TAC [INT_DIV2_LT]);

val acl2_lognot_def = sexp.acl2Define "COMMON-LISP::LOGNOT"
    `acl2_lognot i = add (unary_minus (ifix i)) (int ~1)`;

val acl2_lognand_def = sexp.acl2Define "COMMON-LISP::LOGNAND"
    `acl2_lognand i j = acl2_lognot (acl2_logand i j)`;

val acl2_logior_def = sexp.acl2Define "ACL2::BINARY-LOGIOR"
    `acl2_logior i j =
     acl2_lognot (acl2_logand (acl2_lognot i) (acl2_lognot j))`;

val acl2_logorc1_def = sexp.acl2Define "COMMON-LISP::LOGORC1"
    `acl2_logorc1 i j = acl2_logior (acl2_lognot i) j`;

val acl2_logorc2_def = sexp.acl2Define "COMMON-LISP::LOGORC2"
    `acl2_logorc2 i j = acl2_logior i (acl2_lognot j)`;

val acl2_logandc1_def = sexp.acl2Define "COMMON-LISP::LOGANDC1"
    `acl2_logandc1 i j = acl2_logand (acl2_lognot i) j`;

val acl2_logandc2_def = sexp.acl2Define "COMMON-LISP::LOGANDC2"
    `acl2_logandc2 i j = acl2_logand i (acl2_lognot j)`;

val acl2_logeqv_def = sexp.acl2Define "ACL2::BINARY-LOGEQV"
    `acl2_logeqv i j = acl2_logand (acl2_logorc1 i j) (acl2_logorc1 j i)`;

val acl2_logxor_def = sexp.acl2Define "ACL2::BINARY-LOGXOR"
    `acl2_logxor i j = acl2_lognot (acl2_logeqv i j)`;

val acl2_lognor_def = sexp.acl2Define "COMMON-LISP::LOGNOR"
    `acl2_lognor i j = acl2_lognot (acl2_logior i j)`;

val acl2_logbitp_def = sexp.acl2Define "COMMON-LISP::LOGBITP"
    `acl2_logbitp i j =
     acl2_oddp (acl2_floor (ifix j) (acl2_expt (nat 2) (nfix i)))`;

val INT_IAND = store_thm("INT_IAND",
    ``!i j. int (iand i j) = acl2_logand (int i) (int j)``,
    completeInduct_on `Num (ABS i)` THEN
    ONCE_REWRITE_TAC [iand_def,acl2_logand_def] THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [] THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [GSYM int_def,GSYM INT_THMS,ite_def,
    	   TRUTH_REWRITES,zip_def,eql_def,INTEGERP_INT,GSYM INT_DIV,
	   EVENP_INTMOD] THEN RES_TAC THEN
    REWRITE_TAC [AP_TERM ``int`` (ARITH_PROVE ``(2 * a) = (2 * a + 0i)``)] THEN
    REWRITE_TAC [INT_THMS] THEN
    FIX_CI_TAC THEN
    REPEAT (FIRST_ASSUM MATCH_MP_TAC ORELSE
    	    AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    EQUAL_EXISTS_TAC THEN
    REWRITE_TAC [GSYM integerTheory.INT_LT,NUM_OF_ABS] THEN
    RW_TAC int_ss [INT_DIV2_LT]);

val INT_INOT = store_thm("INT_INOT",
    ``!i. int (inot x) = acl2_lognot (int x)``,
    RW_TAC int_ss [inot_def,acl2_lognot_def,INT_IFIX,
    	   GSYM INT_THMS,INT_CONG] THEN
    ARITH_TAC);

(*****************************************************************************)
(* Logical propagation theorems:                                             *)
(*****************************************************************************)

val WORD_AND = store_thm("WORD_AND",
    ``!a b. word_encode (:'a) (a && b : 'a word) =
    	    acl2_logand (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [word_encode_def,INT_IAND,sw2i_and]);

val WORD_NOT = store_thm("WORD_NOT",
    ``!a. word_encode (:'a) (~ a) = acl2_lognot (word_encode (:'a) a)``,
    RW_TAC int_ss [word_encode_def,GSYM INT_INOT,sw2i_not]);

val WORD_NAND = store_thm("WORD_NAND",
    ``!a b. word_encode (:'a) (~(a && b)) =
    	    acl2_lognand (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_lognand_def,WORD_AND,WORD_NOT]);

val word_or_and = store_thm("word_or_and",
    ``!a b. a !! b = ~(~a && ~b)``,
    RW_TAC int_ss [wordsTheory.WORD_DE_MORGAN_THM,wordsTheory.WORD_NOT_NOT]);

val WORD_OR = store_thm("WORD_OR",
    ``!a b. word_encode (:'a) (a !! b) =
    	    acl2_logior (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [word_or_and,WORD_NOT,WORD_AND,acl2_logior_def]);

val WORD_ORC1 = store_thm("WORD_ORC1",
    ``!a b. word_encode (:'a) (~a !! b) =
    	    acl2_logorc1 (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logorc1_def,WORD_OR,WORD_NOT]);

val WORD_ORC2 = store_thm("WORD_ORC2",
    ``!a b. word_encode (:'a) (a !! ~b) =
    	    acl2_logorc2 (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logorc2_def,WORD_OR,WORD_NOT]);

val WORD_ANDC1 = store_thm("WORD_ANDC1",
    ``!a b. word_encode (:'a) (~a && b) =
    	    acl2_logandc1 (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logandc1_def,WORD_AND,WORD_NOT]);

val WORD_ANDC2 = store_thm("WORD_ANDC2",
    ``!a b. word_encode (:'a) (a && ~b) =
    	    acl2_logandc2 (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logandc2_def,WORD_AND,WORD_NOT]);

val WORD_NXOR = store_thm("WORD_NXOR",
    ``!a b. word_encode (:'a) (~(a ?? b)) =
    	    acl2_logeqv (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logeqv_def,GSYM WORD_AND,GSYM WORD_ORC1,GSYM WORD_ORC2,
    	   WORD_CONG,wordsTheory.WORD_XOR,wordsTheory.WORD_DE_MORGAN_THM,
	   wordsTheory.WORD_NOT_NOT]);

val WORD_XOR = store_thm("WORD_XOR",
    ``!a b. word_encode (:'a) (a ?? b) =
    	    acl2_logxor (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_logxor_def,GSYM WORD_NXOR,GSYM WORD_NOT,WORD_CONG,
    	   wordsTheory.WORD_NOT_NOT]);

val WORD_NOR = store_thm("WORD_NOR",
    ``!a b. word_encode (:'a) (~(a !! b)) =
    	    acl2_lognor (word_encode (:'a) a) (word_encode (:'a) b)``,
    RW_TAC int_ss [acl2_lognor_def,WORD_NOT,WORD_OR]);

val ODDP_ABS = store_thm("ODDP_ABS",
    ``!a. acl2_oddp (int (ABS a)) = acl2_oddp (int a)``,
    GEN_TAC THEN a_INT_TAC THEN
    RW_TAC int_ss [INT_ABS_NUM,INT_ABS_NEG,GSYM nat_def,GSYM NAT_ODD] THEN
    Cases_on `ODD a'` THEN
    RW_TAC int_ss [acl2_oddp_def,ite_def,TRUTH_REWRITES,not_def,EVENP_INTMOD,
    	   bool_def] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [int_mod,int_div,INT_ADD_CALCULATE,INT_MUL_CALCULATE,
    	   INT_SUB_CALCULATE,bitTheory.ODD_MOD2_LEM,LEFT_ADD_DISTRIB] THEN
    RW_TAC int_ss [INT_MUL_CALCULATE,INT_ADD_CALCULATE] THEN
    IMP_RES_TAC NOT_MOD THEN
    FULL_SIMP_TAC int_ss [bitTheory.DIV_MULT_THM2]);

val WORD_BIT = store_thm("WORD_BIT",
    ``!a b. b < dimindex (:'a) ==> (bool (a ' b) =
    	    acl2_logbitp (nat b) (word_encode (:'a) (a:'a word)))``,
    RW_TAC int_ss [sw2i_bit,acl2_logbitp_def,ibit_def,NAT_ODD,NAT_NFIX,
    	   GSYM NAT_EXPT] THEN
    RW_TAC int_ss [nat_def,NUM_OF_ABS,INT_ABS,INT_DIV,word_encode_def,
    	   INT_IFIX] THEN
    RW_TAC int_ss [GSYM INT_DIV,GSYM INT_ABS,ODDP_ABS]);

val WORD_ASR = store_thm("WORD_ASR",
    ``!a b. word_encode (:'a) (a >> b) =
    	    acl2_floor (word_encode (:'a) a) (int (2 ** b))``,
    RW_TAC int_ss [sw2i_asr,word_encode_def,GSYM INT_DIV]);

val WORD_LSL = store_thm("WORD_LSL",
    ``!a b. word_encode (:'a) (a << b) =
    	 int (extend (sw2i a * 2 ** b) (dimindex (:'a)))``,
    RW_TAC int_ss [word_encode_def,sw2i_lsl]);

val WORD_MSB = store_thm("WORD_MSB",
    ``!a. bool (word_msb a) = bool (sw2i a < 0)``,
    RW_TAC int_ss [sw2i_msb]);

(*****************************************************************************)
(* Word arithmetic:                                                          *)
(*****************************************************************************)

val WORD_ADD = store_thm("WORD_ADD",
    ``!a b. word_encode (:'a) (a + b) =
    	    int (extend (sw2i a + sw2i b) (dimindex (:'a)))``,
    RW_TAC int_ss [sw2i_add,word_encode_def]);

val WORD_SUB = store_thm("WORD_SUB",
    ``!a b. word_encode (:'a) (a - b) =
    	    int (extend (sw2i a - sw2i b) (dimindex (:'a)))``,
    RW_TAC int_ss [sw2i_sub,word_encode_def]);

val WORD_NEG = store_thm("WORD_NEG",
    ``!a. word_encode (:'a) (- a) =
    	  int (extend (~ (sw2i a)) (dimindex (:'a)))``,
    RW_TAC int_ss [word_encode_def,sw2i_twocomp]);

val WORD_MUL = store_thm("WORD_MUL",
    ``!a b. word_encode (:'a) (a * b) =
    	    int (extend (sw2i a * sw2i b) (dimindex (:'a)))``,
    RW_TAC int_ss [sw2i_mul,word_encode_def]);

val WORD_DIV = store_thm("WORD_DIV",
    ``!a b. ~(b = 0w) ==>
    	    (word_encode (:'a) (word_sdiv a b) =
	        int (extend (sw2i a quot sw2i b) (dimindex (:'a))))``,
    RW_TAC int_ss [sw2i_div,word_encode_def]);

val WORD_T = store_thm("WORD_T",
    ``word_encode (:'a) UINT_MAXw = int (~1)``,
    RW_TAC int_ss [word_encode_def,sw2i_word_T]);

val WORD_LT = store_thm("WORD_LT",
    ``bool (a < b) = bool (sw2i a < sw2i b)``,
    RW_TAC int_ss [INT_LT,INT_SW2I,sw2i_lt]);

val WORD_LE = store_thm("WORD_LE",
    ``bool (a <= b) = bool (sw2i a <= sw2i b)``,
    RW_TAC int_ss [INT_LE,INT_SW2I,sw2i_le]);

val WORD_GT = store_thm("WORD_GT",
    ``bool (a > b) = bool (b < a : 'a word)``,
    RW_TAC int_ss [wordsTheory.WORD_GREATER]);

val WORD_GE = store_thm("WORD_GE",
    ``bool (a >= b) = bool (b <= a : 'a word)``,
    RW_TAC int_ss [wordsTheory.WORD_GREATER_EQ]);

(*****************************************************************************)
(* Conversion operations:                                                    *)
(*****************************************************************************)

val WORD_N2W = store_thm("WORD_N2W",
    ``word_encode (:'a) (n2w a) = int (extend (& a) (dimindex (:'a)))``,
    RW_TAC int_ss [word_encode_def,sw2i_n2w]);

val NAT_W2N = store_thm("NAT_W2N",
    ``nat (w2n a) = nat (i2n (sw2i (a:'a word)) (dimindex (:'a)))``,
    `dimindex (:'a) - 1 + 1 = dimindex (:'a)` by
    	  METIS_TAC [wordsTheory.DIMINDEX_GT_0,
	  	     DECIDE ``0 < a ==> (a - 1 + 1n = a)``] THEN
    RW_TAC int_ss [NAT_CONG,sw2i_def,I2N_NUM,w2n_lt_full,INT_SUB_CALCULATE,
    	   INT_ADD_CALCULATE,BIT_RWR,ADD1] THEN
    RW_TAC int_ss [i2n_def,w2n_lt_full] THEN
    RW_TAC int_ss [INT_ADD_CALCULATE,INT_SUB_CALCULATE] THEN
    `w2n a = 2 ** dimindex (:'a) - 1` by
    	 (MATCH_MP_TAC (DECIDE ``a < b /\ b <= a + 1 ==> (a = b - 1n)``) THEN
	  RW_TAC int_ss [w2n_lt_full]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC (SUB_EQUAL_0::
    		 map (SIMP_RULE bool_ss
		      [bitTheory.ZERO_LT_TWOEXP] o Q.SPEC `2 ** b`)
		 [DECIDE ``!b. 0 < b ==> (b - (b - 1) = 1n)``,ZERO_MOD]) THEN
    RW_TAC int_ss [INT_ADD_CALCULATE] THEN
    FULL_SIMP_TAC int_ss [NOT_LESS_EQUAL,DECIDE ``a < 1 = ~(0n < a)``]);

(*****************************************************************************)
(* Logical integer operations:                                               *)
(*****************************************************************************)

val NAT_IFIX = store_thm("NAT_IFIX",
    ``!a. ifix (nat a) = nat a``,
    RW_TAC int_ss [nat_def,INT_IFIX]);

local
open bitTheory
in
val NAT_BIT = store_thm("NAT_BIT",
    ``!a b. bool (BIT a b) = acl2_logbitp (nat a) (nat b)``,
    RW_TAC int_ss [acl2_logbitp_def,GSYM NAT_EXPT,GSYM NAT_DIV,NAT_NFIX,
    	   NAT_IFIX,GSYM NAT_ODD,BOOL_CONG] THEN
    RW_TAC int_ss [BIT_def,BITS_THM,ADD1,ODD_MOD2_LEM])
end

val _ = export_theory();
