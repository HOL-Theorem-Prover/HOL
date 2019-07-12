(***************************************************************************
 *
 *  Theory of rational numbers.
 *
 *  Jens Brandt, November 2005
 *
 ***************************************************************************)

open HolKernel boolLib Parse BasicProvers bossLib;

(* interactive mode
app load [
        "integerTheory", "intLib",
        "intExtensionTheory", "intExtensionLib",
        "ringLib", "integerRingLib",
        "fracTheory", "fracLib", "ratUtils", "jbUtils",
        "quotient", "schneiderUtils"];
*)

open
        arithmeticTheory
        integerTheory intLib
        intExtensionTheory intExtensionLib
        ringLib integerRingLib
        fracTheory fracLib ratUtils jbUtils
        quotient schneiderUtils;

val arith_ss = old_arith_ss

val _ = new_theory "rat";
val _ = ParseExtras.temp_loose_equality()

val ERR = mk_HOL_ERR "ratScript"

(*--------------------------------------------------------------------------*
 *  rat_equiv: definition and proof of equivalence relation
 *--------------------------------------------------------------------------*)

(* definition of equivalence relation *)
val rat_equiv_def = Define `rat_equiv f1 f2 = (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)`;

(* RAT_EQUIV_REF: |- !a:frac. rat_equiv a a *)
val RAT_EQUIV_REF = store_thm("RAT_EQUIV_REF", ``!a:frac. rat_equiv a a``,
       STRIP_TAC THEN
       REWRITE_TAC[rat_equiv_def] );

(* RAT_EQUIV_SYM: |- !a b. rat_equiv a b = rat_equiv b a *)
val RAT_EQUIV_SYM = store_thm("RAT_EQUIV_SYM",
  ``!a b. rat_equiv a b = rat_equiv b a``,
       REPEAT STRIP_TAC THEN
       REWRITE_TAC[rat_equiv_def] THEN
       MATCH_ACCEPT_TAC EQ_SYM_EQ) ;

val INT_ENTIRE' = CONV_RULE (ONCE_DEPTH_CONV (LHS_CONV SYM_CONV)) INT_ENTIRE ;
val FRAC_DNMNZ = GSYM (MATCH_MP INT_LT_IMP_NE (SPEC_ALL FRAC_DNMPOS)) ;
val FRAC_DNMNN = let val th = MATCH_MP INT_LT_IMP_LE (SPEC_ALL FRAC_DNMPOS)
    in MATCH_MP (snd (EQ_IMP_RULE (SPEC_ALL INT_NOT_LT))) th end ;
fun ifcan f x = f x handle _ => x ;

val RAT_EQUIV_NMR_Z_IFF = store_thm ("RAT_EQUIV_NMR_Z_IFF",
  ``!a b. rat_equiv a b ==> ((frac_nmr a = 0) = (frac_nmr b = 0))``,
  REWRITE_TAC[rat_equiv_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  FULL_SIMP_TAC std_ss [INT_MUL_LZERO, INT_MUL_RZERO,
    INT_ENTIRE, INT_ENTIRE', FRAC_DNMNZ]) ;

val RAT_EQUIV_NMR_GTZ_IFF = store_thm ("RAT_EQUIV_NMR_GTZ_IFF",
  ``!a b. rat_equiv a b ==> ((frac_nmr a > 0) = (frac_nmr b > 0))``,
  REWRITE_TAC[rat_equiv_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (ifcan (AP_TERM ``int_lt 0i``)) THEN
  FULL_SIMP_TAC std_ss [int_gt, INT_MUL_SIGN_CASES, FRAC_DNMPOS, FRAC_DNMNN ]) ;

val RAT_EQUIV_NMR_LTZ_IFF = store_thm ("RAT_EQUIV_NMR_LTZ_IFF",
  ``!a b. rat_equiv a b ==> ((frac_nmr a < 0) = (frac_nmr b < 0))``,
  REWRITE_TAC[rat_equiv_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (ifcan (AP_TERM ``int_gt 0i``)) THEN
  FULL_SIMP_TAC std_ss [int_gt, INT_MUL_SIGN_CASES, FRAC_DNMPOS, FRAC_DNMNN ]) ;

val RAT_NMR_Z_IFF_EQUIV = store_thm ("RAT_NMR_Z_IFF_EQUIV",
  ``!a b. (frac_nmr a = 0) ==> (rat_equiv a b = (frac_nmr b = 0))``,
  REWRITE_TAC[rat_equiv_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  REV_FULL_SIMP_TAC std_ss [INT_MUL_LZERO, INT_MUL_RZERO,
    INT_ENTIRE, INT_ENTIRE', FRAC_DNMNZ]) ;

val times_dnmb = MATCH_MP INT_EQ_RMUL_EXP (Q.SPEC `b` FRAC_DNMPOS) ;

val box_equals = prove (``(a = b) ==> (c = a) /\ (d = b) ==> (c = d)``,
  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN ASM_SIMP_TAC bool_ss []) ;

val RAT_EQUIV_TRANS = store_thm("RAT_EQUIV_TRANS",
  ``!a b c. rat_equiv a b /\ rat_equiv b c ==> rat_equiv a c``,
  REPEAT GEN_TAC THEN Cases_on `frac_nmr b = 0`
  THENL [ STRIP_TAC THEN
    RULE_ASSUM_TAC (ifcan (MATCH_MP RAT_EQUIV_NMR_Z_IFF)) THEN
      FULL_SIMP_TAC std_ss [RAT_NMR_Z_IFF_EQUIV],
    REWRITE_TAC[rat_equiv_def] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [times_dnmb] THEN
      FIRST_X_ASSUM (fn th => ONCE_REWRITE_TAC [MATCH_MP INT_EQ_LMUL2 th]) THEN
      POP_ASSUM_LIST (fn [thbc, thab] => ASSUME_TAC
        (MK_COMB (AP_TERM ``int_mul`` thab, thbc))) THEN
      POP_ASSUM (fn th => MATCH_MP_TAC (MATCH_MP box_equals th)) THEN
      CONJ_TAC THEN CONV_TAC (AC_CONV (INT_MUL_ASSOC,INT_MUL_SYM)) ] ) ;

val RAT_EQUIV_TRANS' = REWRITE_RULE [GSYM AND_IMP_INTRO] RAT_EQUIV_TRANS ;

fun e2tac tthm = FIRST_X_ASSUM (fn th1 =>
  let val tha1 = MATCH_MP tthm th1 ;
  in FIRST_X_ASSUM (fn th2 => ACCEPT_TAC (MATCH_MP tha1 th2)) end) ;

val RAT_EQUIV = store_thm("RAT_EQUIV",
  ``!f1 f2. rat_equiv f1 f2 = (rat_equiv f1 = rat_equiv f2)``,
  REPEAT GEN_TAC THEN EQ_TAC
  THENL [
    REWRITE_TAC[FUN_EQ_THM] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN_LT
      NTH_GOAL (ONCE_REWRITE_TAC [RAT_EQUIV_SYM]) 1 THEN
      DISCH_TAC THEN e2tac RAT_EQUIV_TRANS',
    DISCH_TAC THEN ASM_SIMP_TAC bool_ss [RAT_EQUIV_REF]]) ;

(*--------------------------------------------------------------------------*
 *  RAT_EQUIV_ALT
 *
 *  |- !a. rat_equiv a =
 *          \x. (?b c. 0<b /\ 0<c /\
 *                  (frac_mul a (abs_frac(b,b)) = frac_mul x (abs_frac(c,c)) ))
 *
 *  alternative representation of equivalence relation
 *--------------------------------------------------------------------------*)

fun feqconv thm = let val thm' = UNDISCH_ALL (SPEC_ALL thm) ;
  in DEPTH_CONV (REWR_CONV_A thm') end ;
fun feqtac thm = VALIDATE (POP_ASSUM (ASSUME_TAC o CONV_RULE (feqconv thm))) ;

fun msprod th = let val [thbc, thab] = CONJUNCTS th
  in MK_COMB (AP_TERM ``int_mul`` (MATCH_MP EQ_SYM thab), thbc) end ;

val RAT_EQUIV_ALT = store_thm("RAT_EQUIV_ALT",
  ``!a. rat_equiv a = \x. (?b c. 0<b /\ 0<c /\
    (frac_mul a (abs_frac(b,b)) = frac_mul x (abs_frac(c,c)) ))``,
  SIMP_TAC bool_ss [FUN_EQ_THM, rat_equiv_def, frac_mul_def] THEN
  REPEAT GEN_TAC THEN EQ_TAC
  THENL [ DISCH_TAC THEN
    EXISTS_TAC ``frac_dnm x`` THEN EXISTS_TAC ``frac_dnm a`` THEN
      ASM_SIMP_TAC bool_ss [FRAC_DNMPOS, NMR, DNM] THEN
      VALIDATE (CONV_TAC (feqconv FRAC_EQ)) THEN
      TRY (irule INT_MUL_POS_SIGN >> conj_tac >> irule FRAC_DNMPOS) THEN
      CONJ_TAC
      (* ASM_SIMP_TAC bool_ss [] does nothing - why ??? *)
      THENL [ POP_ASSUM ACCEPT_TAC, ASM_SIMP_TAC bool_ss [INT_MUL_COMM] ],
      REPEAT STRIP_TAC THEN
        REV_FULL_SIMP_TAC bool_ss [NMR, DNM] THEN feqtac FRAC_EQ THEN
        TRY (irule INT_MUL_POS_SIGN THEN
          ASM_SIMP_TAC bool_ss [FRAC_DNMPOS]) THEN
        POP_ASSUM (ASSUME_TAC o msprod) THEN
        FIRST_X_ASSUM (fn th =>
          ONCE_REWRITE_TAC [MATCH_MP INT_EQ_RMUL_EXP th]) THEN
        FIRST_X_ASSUM (fn th =>
          ONCE_REWRITE_TAC [MATCH_MP INT_EQ_RMUL_EXP th]) THEN
        POP_ASSUM (fn th => MATCH_MP_TAC (MATCH_MP box_equals th)) THEN
          CONJ_TAC THEN CONV_TAC (AC_CONV (INT_MUL_ASSOC,INT_MUL_SYM)) ] ) ;

(*--------------------------------------------------------------------------*
 * type definition
 *--------------------------------------------------------------------------*)

(* following also stored as rat_QUOTIENT *)
val rat_def = save_thm("rat_def",
  define_quotient_type "rat" "abs_rat" "rep_rat" RAT_EQUIV);

val QUOTIENT_def = DB.fetch "quotient" "QUOTIENT_def";
val rat_thm = REWRITE_RULE[QUOTIENT_def] rat_def ; (* was rat_def *)
val rat_type_thm = save_thm ("rat_type_thm",
  REWRITE_RULE[QUOTIENT_def, RAT_EQUIV_REF] rat_def) ;

val rat_equiv_reps = store_thm ("rat_equiv_reps",
  ``rat_equiv (rep_rat r1) (rep_rat r2) = (r1 = r2)``,
  REWRITE_TAC [rat_type_thm]) ;

val rat_equiv_rep_abs = store_thm ("rat_equiv_rep_abs",
  ``rat_equiv (rep_rat (abs_rat f)) f``,
  REWRITE_TAC [rat_type_thm]) ;

(*--------------------------------------------------------------------------*
 * operations
 *--------------------------------------------------------------------------*)

(* numerator, denominator, sign of a fraction *)
val rat_nmr_def = Define `rat_nmr r = frac_nmr (rep_rat r)`;
val rat_dnm_def = Define `rat_dnm r = frac_dnm (rep_rat r)`;
val rat_sgn_def = Define `rat_sgn r = frac_sgn (rep_rat r)`;

(* additive, multiplicative inverse of a fraction *)
val rat_0_def = Define `rat_0 = abs_rat( frac_0 )`;
val rat_1_def = Define `rat_1 = abs_rat( frac_1 )`;

(* neutral elements *)
val rat_ainv_def = Define `rat_ainv r1 = abs_rat( frac_ainv (rep_rat r1))`;
val rat_minv_def = Define `rat_minv r1 = abs_rat( frac_minv (rep_rat r1))`;

(* basic arithmetics *)
val rat_add_def = zDefine `rat_add r1 r2 = abs_rat( frac_add (rep_rat r1) (rep_rat r2) )`;
val rat_sub_def = zDefine `rat_sub r1 r2 = abs_rat( frac_sub (rep_rat r1) (rep_rat r2) )`;
val rat_mul_def = zDefine `rat_mul r1 r2 = abs_rat( frac_mul (rep_rat r1) (rep_rat r2) )`;
val rat_div_def = zDefine `rat_div r1 r2 = abs_rat( frac_div (rep_rat r1) (rep_rat r2) )`;

(* order relations *)
val rat_les_def = Define `rat_les r1 r2 = (rat_sgn (rat_sub r2 r1) = 1)`;
val rat_gre_def = Define `rat_gre r1 r2 = rat_les r2 r1`;
val rat_leq_def = Define `rat_leq r1 r2 = rat_les r1 r2 \/ (r1=r2)`;
val rat_geq_def = Define `rat_geq r1 r2 = rat_leq r2 r1`;



(* construction of rational numbers, support of numerals *)
val rat_cons_def = Define `rat_cons (nmr:int) (dnm:int) = abs_rat (abs_frac(SGN nmr * SGN dnm * ABS nmr, ABS dnm))`;

val rat_of_num_def = Define ` (rat_of_num 0 = rat_0) /\ (rat_of_num (SUC 0) = rat_1) /\ (rat_of_num (SUC (SUC n)) = rat_add (rat_of_num (SUC n)) rat_1)`;
val _ = add_numeral_form(#"q", SOME "rat_of_num");

val rat_0 = store_thm("rat_0", ``0q = abs_rat( frac_0 )``,
        PROVE_TAC[rat_of_num_def, rat_0_def] );

val rat_1 = store_thm("rat_1", ``1q = abs_rat( frac_1 )``,
        SUBST_TAC[ARITH_PROVE ``1=SUC 0``] THEN RW_TAC arith_ss [rat_of_num_def, rat_1_def] );

(*--------------------------------------------------------------------------
 *  parser rules
 *--------------------------------------------------------------------------*)

val _ = set_fixity "//" (Infixl 600)

val _ = overload_on ("+",  ``rat_add``);
val _ = overload_on ("-",  ``rat_sub``);
val _ = overload_on ("*",  ``rat_mul``);
val _ = overload_on (GrammarSpecials.decimal_fraction_special, ``rat_div``);
val _ = overload_on ("/",  ``rat_div``);
val _ = overload_on ("<",  ``rat_les``);
val _ = overload_on ("<=", ``rat_leq``);
val _ = overload_on (">",  ``rat_gre``);
val _ = overload_on (">=", ``rat_geq``);
val _ = overload_on ("~",  ``rat_ainv``);
val _ = overload_on ("numeric_negate",  ``rat_ainv``);
val _ = overload_on ("//",  ``rat_cons``);

local open ratPP in end
val _ = add_ML_dependency "ratPP"
val _ = add_user_printer ("rat.decimalfractions",
                          ``&(NUMERAL x):rat / &(NUMERAL y):rat``)

(*--------------------------------------------------------------------------
 *  RAT: thm
 *  |- !r. abs_rat ( rep_rat r ) = r
 *--------------------------------------------------------------------------*)

val RAT = store_thm("RAT", ``!r. abs_rat ( rep_rat r ) = r``,
        ACCEPT_TAC (CONJUNCT1 rat_thm)) ;

(*--------------------------------------------------------------------------
 *  some lemmas
 *--------------------------------------------------------------------------*)

val RAT_ABS_EQUIV = store_thm("RAT_ABS_EQUIV",
  ``!f1 f2. (abs_rat f1 = abs_rat f2) = rat_equiv f1 f2``,
        REWRITE_TAC [rat_type_thm]) ;

val REP_ABS_EQUIV = prove(``!a. rat_equiv a (rep_rat (abs_rat a))``,
        REWRITE_TAC [rat_type_thm]) ;

val RAT_ABS_EQUIV' = GSYM RAT_ABS_EQUIV ;
val REP_ABS_EQUIV' = ONCE_REWRITE_RULE [RAT_EQUIV_SYM] REP_ABS_EQUIV ;

val REP_ABS_DFN_EQUIV = prove(``!x. frac_nmr x * frac_dnm (rep_rat(abs_rat x)) = frac_nmr (rep_rat(abs_rat x)) * frac_dnm x``,
        GEN_TAC THEN
        REWRITE_TAC[GSYM rat_equiv_def] THEN
        REWRITE_TAC[REP_ABS_EQUIV] );

val RAT_IMP_EQUIV = prove(``!r1 r2. (r1 = r2) ==> rat_equiv r1 r2``,
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[RAT_EQUIV_REF]) ;

(*==========================================================================
 * equivalence of rational numbers
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_EQ: thm
 *  |- !f1 f2. (abs_rat f1 = abs_rat f2)
 *      = (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)
 *--------------------------------------------------------------------------*)

val RAT_EQ = store_thm("RAT_EQ",
``!f1 f2. (abs_rat f1 = abs_rat f2) =
          (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [RAT_ABS_EQUIV, rat_equiv_def] );

(*--------------------------------------------------------------------------
 *  RAT_EQ_ALT: thm
 *  |- ! r1 r2. (r1=r2) = (rat_nmr r1 * rat_dnm r2 = rat_nmr r2 * rat_dnm r1)
 *--------------------------------------------------------------------------*)

val RAT_EQ_ALT = store_thm("RAT_EQ_ALT", ``! r1 r2. (r1=r2) = (rat_nmr r1 * rat_dnm r2 = rat_nmr r2 * rat_dnm r1)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_nmr_def, rat_dnm_def] THEN
        REWRITE_TAC[GSYM rat_equiv_def] THEN
        REWRITE_TAC[rat_type_thm] );

(*==========================================================================
 *  congruence theorems
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_NMREQ0_CONG: thm
 *  |- !f1. (frac_nmr (rep_rat (abs_rat f1)) = 0) = (frac_nmr f1 = 0)
 *
 *  RAT_NMRLT0_CONG: thmRAT_NMREQ0_CONG
 *  |- !f1. (frac_nmr (rep_rat (abs_rat f1)) < 0) = (frac_nmr f1 < 0)
 *
 *  RAT_NMRGT0_CONG: thmRAT_NMREQ0_CONG
 *  |- !f1. (frac_nmr (rep_rat (abs_rat f1)) > 0) = (frac_nmr f1 > 0)
 *
 *--------------------------------------------------------------------------*)

val RAT_NMREQ0_CONG = store_thm("RAT_NMREQ0_CONG",
  ``!f1. (frac_nmr (rep_rat (abs_rat f1)) = 0) = (frac_nmr f1 = 0)``,
  GEN_TAC THEN MATCH_ACCEPT_TAC
    (MATCH_MP RAT_EQUIV_NMR_Z_IFF (SPEC_ALL REP_ABS_EQUIV'))) ;

val RAT_NMRLT0_CONG = store_thm("RAT_NMRLT0_CONG",
  ``!f1. (frac_nmr (rep_rat (abs_rat f1)) < 0) = (frac_nmr f1 < 0)``,
  GEN_TAC THEN MATCH_ACCEPT_TAC
    (MATCH_MP RAT_EQUIV_NMR_LTZ_IFF (SPEC_ALL REP_ABS_EQUIV'))) ;

val RAT_NMRGT0_CONG = store_thm("RAT_NMRGT0_CONG",
  ``!f1. (frac_nmr (rep_rat (abs_rat f1)) > 0) = (frac_nmr f1 > 0)``,
  GEN_TAC THEN MATCH_ACCEPT_TAC
    (MATCH_MP RAT_EQUIV_NMR_GTZ_IFF (SPEC_ALL REP_ABS_EQUIV'))) ;

(*--------------------------------------------------------------------------
 *  RAT_SGN_CONG: thm
 *  |- !f1. frac_sgn (rep_rat (abs_rat f1)) = frac_sgn f1
 *--------------------------------------------------------------------------*)

val RAT_SGN_CONG = store_thm("RAT_SGN_CONG", ``!f1. frac_sgn (rep_rat (abs_rat f1)) = frac_sgn f1``,
        GEN_TAC THEN
        REWRITE_TAC[frac_sgn_def, SGN_def] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG, RAT_NMRLT0_CONG] );

(*--------------------------------------------------------------------------
 *  RAT_AINV_CONG: thm
 *  |- !x. abs_rat (frac_ainv (rep_rat (abs_rat x))) = abs_rat (frac_ainv x)
 *--------------------------------------------------------------------------*)

val RAT_AINV_CONG = store_thm("RAT_AINV_CONG", ``!x. abs_rat (frac_ainv (rep_rat (abs_rat x))) = abs_rat (frac_ainv x)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[RAT_ABS_EQUIV] THEN
        REWRITE_TAC[rat_equiv_def,frac_ainv_def] THEN
        SIMP_TAC bool_ss [NMR, DNM, FRAC_DNMPOS] THEN
        REWRITE_TAC[INT_MUL_CALCULATE,INT_EQ_NEG] THEN
        REWRITE_TAC[GSYM rat_equiv_def] THEN
        ONCE_REWRITE_TAC[RAT_EQUIV_SYM] THEN
        REWRITE_TAC[REP_ABS_EQUIV] );

(*--------------------------------------------------------------------------
 *  RAT_MINV_CONG: thm
 *  |- !x. ~(frac_nmr x=0) ==>
 *     (abs_rat (frac_minv (rep_rat (abs_rat x))) = abs_rat (frac_minv x))
 *--------------------------------------------------------------------------*)

val FRAC_MINV_EQUIV = store_thm ("FRAC_MINV_EQUIV",
  ``~(frac_nmr y=0) ==> rat_equiv x y ==>
    rat_equiv (frac_minv x) (frac_minv y)``,
  DISCH_TAC THEN DISCH_THEN (fn th => MP_TAC th THEN ASSUME_TAC th) THEN
  POP_ASSUM (ASSUME_TAC o MATCH_MP RAT_EQUIV_NMR_Z_IFF) THEN
  REWRITE_TAC[frac_minv_def, rat_equiv_def, frac_sgn_def] THEN
  VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
  (TRY (irule INT_ABS_NOT0POS THEN ASM_SIMP_TAC bool_ss [])) THEN
  REWRITE_TAC[SGN_def] THEN REPEAT IF_CASES_TAC THEN
  ASM_SIMP_TAC int_ss [INT_ABS,
    GSYM INT_NEG_MINUS1, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL] THEN
  SIMP_TAC bool_ss [INT_MUL_COMM]) ;

val RAT_MINV_CONG = store_thm("RAT_MINV_CONG",
  ``!x. ~(frac_nmr x=0) ==>
    (abs_rat (frac_minv (rep_rat (abs_rat x))) = abs_rat (frac_minv x))``,
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC FRAC_MINV_EQUIV THEN
  ASSUME_TAC (Q.SPEC `x` REP_ABS_EQUIV') THEN
  RES_TAC THEN ASM_SIMP_TAC bool_ss [RAT_ABS_EQUIV]) ;

(*--------------------------------------------------------------------------
 *  RAT_ADD_CONG1: thm
 *  |- !x y. abs_rat (frac_add (rep_rat (abs_rat x)) y) = abs_rat (frac_add x y)
 *
 *  RAT_ADD_CONG2: thm
 *  |- !x y. abs_rat (frac_add x (rep_rat (abs_rat y))) = abs_rat (frac_add x y)
 *
 *  RAT_ADD_CONG: thm
 *  |- !x y. abs_rat (frac_add (rep_rat (abs_rat x)) y) = abs_rat (frac_add x y) /\
 *     !x y. abs_rat (frac_add x (rep_rat (abs_rat y))) = abs_rat (frac_add x y)
 *--------------------------------------------------------------------------*)

val FRAC_ADD_EQUIV1 = store_thm ("FRAC_ADD_EQUIV1",
  ``rat_equiv x x' ==> rat_equiv (frac_add x y) (frac_add x' y)``,
  REWRITE_TAC[frac_add_def, rat_equiv_def] THEN
  VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
  TRY (irule INT_MUL_POS_SIGN >> conj_tac >> irule FRAC_DNMPOS) THEN
  REWRITE_TAC[INT_RDISTRIB] THEN DISCH_TAC THEN
  MK_COMB_TAC THENL [AP_TERM_TAC, ALL_TAC]
  THENL [
    RULE_ASSUM_TAC (AP_TERM ``int_mul (frac_dnm y * frac_dnm y)``) THEN
      POP_ASSUM (fn th => MATCH_MP_TAC (MATCH_MP box_equals th)) THEN CONJ_TAC,
    ALL_TAC ] THEN
  CONV_TAC (AC_CONV (INT_MUL_ASSOC,INT_MUL_SYM)) ) ;

val RAT_ADD_CONG1 = store_thm("RAT_ADD_CONG1",
  ``!x y. abs_rat (frac_add (rep_rat (abs_rat x)) y) = abs_rat (frac_add x y)``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss [RAT_ABS_EQUIV] THEN
  irule FRAC_ADD_EQUIV1 THEN irule REP_ABS_EQUIV') ;

val RAT_ADD_CONG2 = store_thm("RAT_ADD_CONG2", ``!x y. abs_rat (frac_add x (rep_rat (abs_rat y))) = abs_rat (frac_add x y)``,
        ONCE_REWRITE_TAC[FRAC_ADD_COMM] THEN
        REWRITE_TAC[RAT_ADD_CONG1]);

val RAT_ADD_CONG = save_thm("RAT_ADD_CONG", CONJ RAT_ADD_CONG1 RAT_ADD_CONG2);

(*--------------------------------------------------------------------------
 *  RAT_MUL_CONG1: thm
 *  |- !x y. abs_rat (frac_mul (rep_rat (abs_rat x)) y) = abs_rat (frac_mul x y)
 *
 *  RAT_MUL_CONG2: thm
 *  |- !x y. abs_rat (frac_mul x (rep_rat (abs_rat y))) = abs_rat (frac_mul x y)
 *
 *  RAT_MUL_CONG: thm
 *  |- !x y. abs_rat (frac_mul (rep_rat (abs_rat x)) y) = abs_rat (frac_mul x y) /\
 *     !x y. abs_rat (frac_mul x (rep_rat (abs_rat y))) = abs_rat (frac_mul x y)
 *--------------------------------------------------------------------------*)

val FRAC_MUL_EQUIV1 = store_thm ("FRAC_MUL_EQUIV1",
  ``rat_equiv x x' ==> rat_equiv (frac_mul x y) (frac_mul x' y)``,
  REWRITE_TAC[frac_mul_def, rat_equiv_def] THEN
  VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
  TRY (irule INT_MUL_POS_SIGN >> conj_tac >> irule FRAC_DNMPOS) >> DISCH_TAC >>
  RULE_ASSUM_TAC (AP_TERM ``int_mul (frac_nmr y * frac_dnm y)``) THEN
  POP_ASSUM (fn th => MATCH_MP_TAC (MATCH_MP box_equals th)) THEN
  CONJ_TAC THEN CONV_TAC (AC_CONV (INT_MUL_ASSOC,INT_MUL_SYM)) ) ;

val FRAC_MUL_EQUIV2 = save_thm ("FRAC_MUL_EQUIV2",
  ONCE_REWRITE_RULE [FRAC_MUL_COMM] FRAC_MUL_EQUIV1) ;

val RAT_MUL_CONG1 = store_thm("RAT_MUL_CONG1",
  ``!x y. abs_rat (frac_mul (rep_rat (abs_rat x)) y) = abs_rat (frac_mul x y)``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss [RAT_ABS_EQUIV] THEN
  irule FRAC_MUL_EQUIV1 THEN irule REP_ABS_EQUIV') ;

val RAT_MUL_CONG2 = store_thm("RAT_MUL_CONG2", ``!x y. abs_rat (frac_mul x (rep_rat (abs_rat y))) = abs_rat (frac_mul x y)``,
        ONCE_REWRITE_TAC[FRAC_MUL_COMM] THEN
        RW_TAC int_ss[RAT_MUL_CONG1]);

val RAT_MUL_CONG = save_thm("RAT_MUL_CONG", CONJ RAT_MUL_CONG1 RAT_MUL_CONG2);

(*--------------------------------------------------------------------------
 *  RAT_SUB_CONG1: thm
 *  |- !x y. abs_rat (frac_sub (rep_rat (abs_rat x)) y) = abs_rat (frac_sub x y)
 *
 *  RAT_SUB_CONG2: thm
 *  |- !x y. abs_rat (frac_sub x (rep_rat (abs_rat y))) = abs_rat (frac_sub x y)
 *
 *  RAT_SUB_CONG: thm
 *  |- !x y. abs_rat (frac_sub (rep_rat (abs_rat x)) y) = abs_rat (frac_sub x y) /\
 *     !x y. abs_rat (frac_sub x (rep_rat (abs_rat y))) = abs_rat (frac_sub x y)
 *--------------------------------------------------------------------------*)

val RAT_SUB_CONG1 = store_thm("RAT_SUB_CONG1", ``!x y. abs_rat (frac_sub (rep_rat (abs_rat x)) y) = abs_rat (frac_sub x y)``,
        REWRITE_TAC[frac_sub_def] THEN
        REWRITE_TAC[RAT_ADD_CONG]);

val RAT_SUB_CONG2 = store_thm("RAT_SUB_CONG2", ``!x y. abs_rat (frac_sub x (rep_rat (abs_rat y))) = abs_rat (frac_sub x y)``,
        ONCE_REWRITE_TAC[GSYM FRAC_AINV_SUB] THEN
        ONCE_REWRITE_TAC[GSYM RAT_AINV_CONG] THEN
        REWRITE_TAC[RAT_SUB_CONG1] );

val RAT_SUB_CONG = save_thm("RAT_SUB_CONG", CONJ RAT_SUB_CONG1 RAT_SUB_CONG2);

(*--------------------------------------------------------------------------
 *  RAT_DIV_CONG1: thm
 *  |- !x y. ~(frac_nmr y = 0) ==>
 *           (abs_rat (frac_div (rep_rat (abs_rat x)) y) = abs_rat (frac_div x y))
 *
 *  RAT_DIV_CONG2: thm
 *  |- !x y. ~(frac_nmr y = 0) ==>
             (abs_rat (frac_div x (rep_rat (abs_rat y))) = abs_rat (frac_div x y))
 *
 *  RAT_DIV_CONG: thm
 *  |- !x y. ~(frac_nmr y = 0) ==>
 *           (abs_rat (frac_div (rep_rat (abs_rat x)) y) = abs_rat (frac_div x y)) /\
 *     !x y. ~(frac_nmr y = 0) ==>
             (abs_rat (frac_div x (rep_rat (abs_rat y))) = abs_rat (frac_div x y))
 *--------------------------------------------------------------------------*)

val RAT_DIV_CONG1 = store_thm("RAT_DIV_CONG1",
  ``!x y. ~(frac_nmr y = 0) ==>
    (abs_rat (frac_div (rep_rat (abs_rat x)) y) = abs_rat (frac_div x y))``,
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[frac_div_def] THEN
        REWRITE_TAC[RAT_MUL_CONG] );

val RAT_DIV_CONG2 = store_thm("RAT_DIV_CONG2",
  ``!x y. ~(frac_nmr y = 0) ==>
    (abs_rat (frac_div x (rep_rat (abs_rat y))) = abs_rat (frac_div x y))``,
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[frac_div_def, RAT_ABS_EQUIV] THEN
        irule FRAC_MUL_EQUIV2 THEN
        IMP_RES_THEN MATCH_MP_TAC FRAC_MINV_EQUIV THEN
        irule rat_equiv_rep_abs) ;

val RAT_DIV_CONG = save_thm("RAT_DIV_CONG", CONJ RAT_DIV_CONG1 RAT_DIV_CONG2 );

(*==========================================================================
 *  numerator and denominator
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_NMRDNM_EQ: thm
 *  |- (abs_rat(abs_frac(frac_nmr f1,frac_dnm f1)) = 1q) = (frac_nmr f1 = frac_dnm f1)
 *--------------------------------------------------------------------------*)

val RAT_NMRDNM_EQ = store_thm("RAT_NMRDNM_EQ",``(abs_rat(abs_frac(frac_nmr f1,frac_dnm f1)) = 1q) = (frac_nmr f1 = frac_dnm f1)``,
        SIMP_TAC bool_ss [rat_equiv_def, RAT_ABS_EQUIV,
          rat_1, frac_1_def, NMR, DNM, FRAC_DNMPOS, INT_LT_01,
          INT_MUL_LID, INT_MUL_RID]) ;

(*==========================================================================
 *  calculation
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_AINV_CALCULATE: thm
 *  |- !f1. rat_ainv (abs_rat(f1)) = abs_rat( frac_ainv f1 )
 *--------------------------------------------------------------------------*)

val RAT_AINV_CALCULATE = store_thm("RAT_AINV_CALCULATE", ``!f1. rat_ainv (abs_rat(f1)) = abs_rat( frac_ainv f1 )``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_ainv_def] THEN
        PROVE_TAC[RAT_AINV_CONG] );

(*--------------------------------------------------------------------------
 *  RAT_MINV_CALCULATE: thm
 *  |- !f1. rat_ainv (abs_rat(f1)) = abs_rat( frac_ainv f1 )
 *--------------------------------------------------------------------------*)

val RAT_MINV_CALCULATE = store_thm("RAT_MINV_CALCULATE", ``!f1. ~(0 = frac_nmr f1) ==> (rat_minv (abs_rat(f1)) = abs_rat( frac_minv f1 ))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_minv_def] THEN
        PROVE_TAC[RAT_MINV_CONG] );

(*--------------------------------------------------------------------------
 *  RAT_ADD_CALCULATE: thm
 *  |- !f1 f2. rat_add (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_add f1 f2 )
 *--------------------------------------------------------------------------*)

val RAT_ADD_CALCULATE = store_thm(
  "RAT_ADD_CALCULATE",
  “!f1 f2. rat_add (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_add f1 f2 )”,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_add_def] THEN PROVE_TAC[RAT_ADD_CONG] );

(*--------------------------------------------------------------------------
 *  RAT_SUB_CALCULATE: thm
 *  |- !f1 f2. rat_sub (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_sub f1 f2 )
 *--------------------------------------------------------------------------*)

val RAT_SUB_CALCULATE = store_thm(
  "RAT_SUB_CALCULATE",
  “!f1 f2. rat_sub (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_sub f1 f2 )”,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_sub_def] THEN PROVE_TAC[RAT_SUB_CONG] );

(*--------------------------------------------------------------------------
 *  RAT_MUL_CALCULATE: thm
 *  |- !f1 f2. rat_mul (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_mul f1 f2 )
 *--------------------------------------------------------------------------*)

val RAT_MUL_CALCULATE = store_thm(
  "RAT_MUL_CALCULATE",
  “!f1 f2. rat_mul (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_mul f1 f2 )”,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_mul_def] THEN PROVE_TAC[RAT_MUL_CONG]);

(* ----------------------------------------------------------------------
    RAT_DIV_CALCULATE: thm
    |- !f1 f2.
         frac_nmr f2 <> 0 ==>
         (rat_div (abs_rat f1) (abs_rat f2) = abs_rat(frac_div f1 f2))
   ---------------------------------------------------------------------- *)

val RAT_DIV_CALCULATE = store_thm(
  "RAT_DIV_CALCULATE",
  “!f1 f2. frac_nmr f2 <> 0 ==>
           (rat_div (abs_rat(f1)) (abs_rat(f2)) = abs_rat( frac_div f1 f2 ))”,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_div_def] THEN PROVE_TAC[RAT_DIV_CONG]);

(*--------------------------------------------------------------------------
 *  RAT_EQ_CALCULATE: thm
 *  |- !f1 f2. (abs_rat f1 = abs_rat f2) = (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)
 *--------------------------------------------------------------------------*)

val RAT_EQ_CALCULATE = store_thm(
  "RAT_EQ_CALCULATE",
  “!f1 f2. (abs_rat f1 = abs_rat f2) <=>
           (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)”,
  PROVE_TAC[RAT_ABS_EQUIV, rat_equiv_def] );


(* ----------------------------------------------------------------------
    RAT_LES_CALCULATE: thm
    |- !f1 f2. (abs_rat f1 < abs_rat f2) =
               (frac_nmr f1 * frac_dnm f2 < frac_nmr f2 * frac_dnm f1)
   ---------------------------------------------------------------------- *)

val RAT_LES_CALCULATE = store_thm(
  "RAT_LES_CALCULATE",
  “!f1 f2. (abs_rat f1 < abs_rat f2) =
           (frac_nmr f1 * frac_dnm f2 < frac_nmr f2 * frac_dnm f1)”,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rat_les_def, rat_sgn_def, RAT_SUB_CALCULATE, RAT_SGN_CONG] THEN
  REWRITE_TAC[frac_sgn_def, frac_sub_def, frac_add_def, frac_ainv_def] THEN
  FRAC_POS_TAC
    “frac_dnm f2 * frac_dnm (abs_frac (~frac_nmr f1,frac_dnm f1))” THEN
  FRAC_NMRDNM_TAC THEN
  REWRITE_TAC[INT_SGN_CLAUSES, int_gt] THEN
  `~frac_nmr f1 * frac_dnm f2 = ~(frac_nmr f1 * frac_dnm f2)` by ARITH_TAC THEN
  ASM_REWRITE_TAC[INT_LT_ADDNEG, INT_ADD_LID] );

val RAT_LEQ_CALCULATE = store_thm("RAT_LEQ_CALCULATE",
  ``!f1 f2. (abs_rat f1 <= abs_rat f2) =
    (frac_nmr f1 * frac_dnm f2 <= frac_nmr f2 * frac_dnm f1)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rat_leq_def, RAT_LES_CALCULATE, INT_LE_LT, RAT_EQ_CALCULATE]) ;

val RAT_OF_NUM_CALCULATE = store_thm(
  "RAT_OF_NUM_CALCULATE",
  ``!n1. rat_of_num n1 = abs_rat( abs_frac( &n1, 1) )``,
  recInduct (DB.fetch "-" "rat_of_num_ind") THEN
  RW_TAC arith_ss [rat_of_num_def, rat_0_def, frac_0_def, rat_1_def, frac_1_def,
                   RAT_ADD_CALCULATE, frac_add_def] THEN
  FRAC_POS_TAC ``1i`` THEN
  RW_TAC int_ss
    [NMR, DNM, ARITH_PROVE “int_of_num (SUC n) + 1 = int_of_num (SUC (SUC n))”]
);

val RAT_OF_NUM_LEQ = store_thm("RAT_OF_NUM_LEQ[simp]",
  ``rat_of_num a <= rat_of_num b = a <= b``,
  SIMP_TAC std_ss [RAT_OF_NUM_CALCULATE, RAT_LEQ_CALCULATE,
    NMR, DNM, INT_LT_01, INT_MUL_RID, INT_LE]);

val RAT_OF_NUM_LES = store_thm("RAT_OF_NUM_LES[simp]",
  ``rat_of_num a < rat_of_num b = a < b``,
  SIMP_TAC std_ss [RAT_OF_NUM_CALCULATE, RAT_LES_CALCULATE,
    NMR, DNM, INT_LT_01, INT_MUL_RID, INT_LT]);

(*--------------------------------------------------------------------------
 *  rat_calculate_table : (term * thm) list
 *--------------------------------------------------------------------------*)

val rat_calculate_table = [
        ( ``rat_0``,    rat_0_def ),
        ( ``rat_1``,    rat_1_def ),
        ( ``rat_ainv``, RAT_AINV_CALCULATE ),
        ( ``rat_minv``, RAT_MINV_CALCULATE ),
        ( ``rat_add``,  RAT_ADD_CALCULATE ),
        ( ``rat_sub``,  RAT_SUB_CALCULATE ),
        ( ``rat_mul``,  RAT_MUL_CALCULATE ),
        ( ``rat_div``,  RAT_DIV_CALCULATE )
];

(*--------------------------------------------------------------------------
 *  RAT_CALC_CONV : conv
 *
 *    r1
 *   ---------------------
 *    |- r1 = abs_rat(f1)
 *--------------------------------------------------------------------------*)

fun RAT_CALC_CONV (t1:term) =
let
        val thm = REFL t1;
        val (top_rator, top_rands) = strip_comb t1;
        val calc_table_entry =
            List.find (fn x => fst(x) ~~ top_rator) rat_calculate_table;
in
        (* do nothing if term is already in the form abs_rat(...) *)
        if top_rator ~~ ``abs_rat`` then
                thm
        (* if it is a numeral, simply rewrite it *)
        else if (top_rator ~~ ``rat_of_num``) then
                SUBST [``x:rat`` |-> SPEC (rand t1) (RAT_OF_NUM_CALCULATE)] ``^t1 = x:rat`` thm
        (* if there is an entry in the calculation table, calculate it *)
        else if (isSome calc_table_entry) then
                let
                        val arg_thms = map RAT_CALC_CONV top_rands;
                        val arg_fracs = map (fn x => rand(rhs(concl x))) arg_thms;
                        val arg_vars = map (fn x => genvar ``:rat``) arg_thms;

                        val subst_list = map (fn x => fst(x) |-> snd(x)) (ListPair.zip (arg_vars,arg_thms));
                        (* subst_term: t1 = top_rator arg_vars[1] ... arg_vars[n] *)
                        val subst_term =  mk_eq (t1 , list_mk_comb (top_rator,arg_vars))

                        val thm1 = SUBST subst_list subst_term thm;
                        val (thm1_lhs, thm1_rhs) = dest_eq(concl thm1);
                        val thm1_lhs_var = genvar ``:rat``;

                        val calc_thm = snd (valOf( calc_table_entry ));
                in
                        SUBST [thm1_lhs_var |-> UNDISCH_ALL (SPECL arg_fracs calc_thm)] ``^thm1_lhs = ^thm1_lhs_var`` thm1
                end
        (* otherwise: applying r = abs_rat(rep_rat r)) always works *)
        else
                SUBST [``x:rat`` |-> SPEC t1 (GSYM RAT)] ``^t1 = x:rat`` thm
end;

(*--------------------------------------------------------------------------
 *  RAT_CALCTERM_TAC : term -> tactic
 *
 *  calculates the value of t1:rat
 *--------------------------------------------------------------------------*)

fun RAT_CALCTERM_TAC (t1:term) (asm_list,goal) =
        let
                val calc_thm = RAT_CALC_CONV t1;
                val (calc_asms, calc_concl) = dest_thm calc_thm;
        in
                (
                        MAP_EVERY ASSUME_TAC (map (fn x => TAC_PROOF ((asm_list,x), RW_TAC intLib.int_ss [FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_NOTPOS0_NEG,INT_NOT0_MUL,INT_GT0_IMP_NOT0,INT_ABS_NOT0POS])) calc_asms) THEN
                        SUBST_TAC[calc_thm]
                ) (asm_list,goal)
        end
handle HOL_ERR _ => raise ERR "RAT_CALCTERM_TAC" "";


(*--------------------------------------------------------------------------
 *  RAT_CALC_TAC : tactic
 *
 *  calculates the value of all subterms (of type ``:rat``)
 *  assumptions that were needed for the simplification are added to the goal
 *--------------------------------------------------------------------------*)

fun RAT_CALC_TAC (asm_list,goal) =
        let
                        (* extract terms of type ``:rat`` *)
                val rat_terms = extract_rat goal;
                        (* build conversions *)
                val calc_thms = map RAT_CALC_CONV rat_terms;
                        (* split list into assumptions and conclusions *)
                val (calc_asmlists, calc_concl) = ListPair.unzip (map (fn x => dest_thm x) calc_thms);
                        (* merge assumptions lists *)
                val calc_asms = op_U aconv calc_asmlists;
                        (* function to prove an assumption, TODO: fracLib benutzen *)
                val gen_thm = (fn x => TAC_PROOF ((asm_list,x), RW_TAC intLib.int_ss [] ));
                        (* try to prove assumptions *)
                val prove_list = List.map (total gen_thm) calc_asms;
                        (* combine assumptions and their proofs *)
                val list1 = ListPair.zip (calc_asms,prove_list);
                        (* partition assumptions into proved assumptions and assumptions to be proved *)
                val list2 = partition (fn x => isSome (snd x)) list1;
                val asms_toprove = map fst (snd list2);
                val asms_proved = map (fn x => valOf (snd x)) (fst list2);
                        (* generate new subgoal goal *)
                val subst_goal = snd (dest_eq (snd (dest_thm (ONCE_REWRITE_CONV calc_thms goal))));
                val subgoal = (list_mk_conj (asms_toprove @ [subst_goal]) );
                val mp_thm = TAC_PROOF
                        (
                                (asm_list, mk_imp (subgoal,goal))
                        ,
                                STRIP_TAC THEN
                                MAP_EVERY ASSUME_TAC asms_proved THEN
                                ONCE_REWRITE_TAC calc_thms THEN
                                PROVE_TAC []
                        );
        in
                        ( [(asm_list,subgoal)], fn (thms:thm list) => MP mp_thm (hd thms) )
        end
handle HOL_ERR _ => raise ERR "RAT_CALC_TAC" "";

(*--------------------------------------------------------------------------
 *  RAT_CALCEQ_TAC : tactic
 *--------------------------------------------------------------------------*)

val RAT_CALCEQ_TAC =
        RAT_CALC_TAC THEN
        FRAC_CALC_TAC THEN
        REWRITE_TAC[RAT_EQ] THEN
        FRAC_NMRDNM_TAC THEN
        INT_RING_TAC;


(*==========================================================================
 *  numerator of rational number: sign reduction
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_EQ0_NMR: thm
   |- !r1. (r1 = 0q) = (rat_nmr r1 = 0)
 *--------------------------------------------------------------------------*)

val RAT_EQ0_NMR = store_thm("RAT_EQ0_NMR", ``!r1. (r1 = 0q) = (rat_nmr r1 = 0)``,
        GEN_TAC THEN
        REWRITE_TAC[rat_nmr_def] THEN
        SUBST_TAC[SPEC ``r1:rat`` (GSYM RAT)] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG] THEN
        REWRITE_TAC[rat_0, frac_0_def, RAT_ABS_EQUIV, rat_equiv_def] THEN
        FRAC_POS_TAC ``1i`` THEN
        FRAC_NMRDNM_TAC );

(*--------------------------------------------------------------------------
   RAT_0LES_NMR: thm
   |- !r1. (0q < r1) = (0 < rat_nmr r1)

   RAT_0LES_NMR: thm
   |- !r1. (r1 < 0q) = (rat_nmr r1 < 0i)
 *--------------------------------------------------------------------------*)

val RAT_0LES_NMR = store_thm("RAT_0LES_NMR", ``!r1. rat_les 0q r1 = 0i < rat_nmr r1``,
        GEN_TAC THEN
        REWRITE_TAC[rat_0, rat_nmr_def, rat_les_def, rat_sgn_def, frac_0_def, frac_sgn_def, SGN_def] THEN
        RAT_CALC_TAC THEN
        FRAC_POS_TAC ``1i`` THEN
        FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
        SUBST_TAC[FRAC_CALC_CONV ``frac_sub (rep_rat r1) (abs_frac (0,1))``] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG,RAT_NMRLT0_CONG,RAT_NMRGT0_CONG] THEN
        FRAC_NMRDNM_TAC THEN
        RW_TAC int_ss [RAT, FRAC, INT_SUB_RZERO] THEN
        PROVE_TAC[INT_LT_ANTISYM, INT_LT_TOTAL] );

val RAT_LES0_NMR = store_thm("RAT_LES0_NMR", ``!r1. rat_les r1 0q = rat_nmr r1 < 0i``,
        GEN_TAC THEN
        REWRITE_TAC[rat_0, rat_nmr_def, rat_les_def, rat_sgn_def, frac_0_def, frac_sgn_def, SGN_def] THEN
        RAT_CALC_TAC THEN
        FRAC_POS_TAC ``1i`` THEN
        FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
        SUBST_TAC[FRAC_CALC_CONV ``frac_sub (abs_frac (0,1)) (rep_rat r1)``] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG,RAT_NMRLT0_CONG,RAT_NMRGT0_CONG] THEN
        FRAC_NMRDNM_TAC THEN
        RW_TAC int_ss [RAT, FRAC, INT_SUB_LZERO] THEN
        PROVE_TAC[INT_LT_ANTISYM, INT_LT_TOTAL, INT_NEG_LT0, INT_NEG_EQ, INT_NEG_0] );

(*--------------------------------------------------------------------------
   RAT_0LES_NMR: thm
   |- !r1. (0q <= r1) = (0i <= rat_nmr r1)

   RAT_0LES_NMR: thm
   |- !r1. (r1 <= 0q) = (rat_nmr r1 <= 0i)
 *--------------------------------------------------------------------------*)

val RAT_0LEQ_NMR = store_thm("RAT_0LEQ_NMR", ``!r1. rat_leq 0q r1 = 0i <= rat_nmr r1``,
        GEN_TAC THEN
        REWRITE_TAC[rat_leq_def, INT_LE_LT] THEN
        NEW_GOAL_TAC ``!a b c d. ((a=c) /\ (b=d)) ==> (a \/ b = c \/ d)`` THEN
        PROVE_TAC[RAT_0LES_NMR, RAT_EQ0_NMR, rat_nmr_def] );

val RAT_LEQ0_NMR = store_thm("RAT_LEQ0_NMR", ``!r1. rat_leq r1 0q = rat_nmr r1 <= 0i``,
        GEN_TAC THEN
        REWRITE_TAC[rat_leq_def, INT_LE_LT] THEN
        NEW_GOAL_TAC ``!a b c d. ((a=c) /\ (b=d)) ==> (a \/ b = c \/ d)`` THEN
        PROVE_TAC[RAT_LES0_NMR, RAT_EQ0_NMR, rat_nmr_def] );

(*==========================================================================
 *  field properties
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_ADD_ASSOC: thm
   |- !a b c. rat_add a (rat_add b c) = rat_add (rat_add a b) c

   RAT_MUL_ASSOC: thm
   |- !a b c. rat_mul a (rat_mul b c) = rat_mul (rat_mul a b) c
 *--------------------------------------------------------------------------*)

val RAT_ADD_ASSOC = store_thm("RAT_ADD_ASSOC", ``!a b c. rat_add a (rat_add b c) = rat_add (rat_add a b) c``,
        REWRITE_TAC[rat_add_def] THEN
        REWRITE_TAC[RAT_ADD_CONG] THEN
        REWRITE_TAC[FRAC_ADD_ASSOC] );

val RAT_MUL_ASSOC = store_thm("RAT_MUL_ASSOC", ``!a b c. rat_mul a (rat_mul b c) = rat_mul (rat_mul a b) c``,
        REWRITE_TAC[rat_mul_def] THEN
        REWRITE_TAC[RAT_MUL_CONG] THEN
        REWRITE_TAC[FRAC_MUL_ASSOC] );

(*--------------------------------------------------------------------------
   RAT_ADD_COMM: thm
   |- !a b. rat_add a b = rat_add b a

   RAT_MUL_COMM: thm
   |- !a b. rat_mul a b = rat_mul b a
 *--------------------------------------------------------------------------*)

val RAT_ADD_COMM = store_thm("RAT_ADD_COMM", ``!a b. rat_add a b = rat_add b a``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_add_def] THEN
        AP_TERM_TAC THEN
        MATCH_ACCEPT_TAC FRAC_ADD_COMM) ;

val RAT_MUL_COMM = store_thm("RAT_MUL_COMM", ``!a b. rat_mul a b = rat_mul b a``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_mul_def] THEN
        AP_TERM_TAC THEN
        MATCH_ACCEPT_TAC FRAC_MUL_COMM) ;

(*--------------------------------------------------------------------------
   RAT_ADD_RID: thm
   |- !a. rat_add a 0q = a

   RAT_ADD_LID: thm
   |- !a. rat_add 0q a = a

   RAT_MUL_RID: thm
   |- !a. rat_mul a 1q = a

   RAT_MUL_LID: thm
   |- !a. rat_mul 1q a = a
 *--------------------------------------------------------------------------*)

val RAT_ADD_RID = store_thm("RAT_ADD_RID[simp]", ``!a. rat_add a 0q = a``,
        REWRITE_TAC[rat_add_def,rat_0] THEN
        REWRITE_TAC[RAT_ADD_CONG] THEN
        REWRITE_TAC[FRAC_ADD_RID] THEN
        REWRITE_TAC[CONJUNCT1 rat_thm]);

val RAT_ADD_LID = store_thm("RAT_ADD_LID[simp]", ``!a. rat_add 0q a = a``,
        ONCE_REWRITE_TAC[RAT_ADD_COMM] THEN
        REWRITE_TAC[RAT_ADD_RID] );

val RAT_MUL_RID = store_thm("RAT_MUL_RID[simp]", ``!a. rat_mul a 1q = a``,
        REWRITE_TAC[rat_mul_def,rat_1] THEN
        REWRITE_TAC[RAT_MUL_CONG] THEN
        REWRITE_TAC[FRAC_MUL_RID] THEN
        REWRITE_TAC[CONJUNCT1 rat_thm]);

val RAT_MUL_LID = store_thm("RAT_MUL_LID[simp]", ``!a. rat_mul 1q a = a``,
        ONCE_REWRITE_TAC[RAT_MUL_COMM] THEN
        REWRITE_TAC[RAT_MUL_RID] );

(*--------------------------------------------------------------------------
   RAT_ADD_RINV: thm
   |- !a. rat_add a (rat_ainv a) = 0q

   RAT_ADD_LINV: thm
   |- !a. rat_add (rat_ainv a) a = 0q

   RAT_MUL_RINV: thm
   |- !a. ~(a=0q) ==> (rat_mul a (rat_minv a) = 1q)

   RAT_MUL_LINV: thm
   |- !a. ~(a = 0q) ==> (rat_mul (rat_minv a) a = 1q)
 *--------------------------------------------------------------------------*)

val RAT_ADD_RINV = store_thm("RAT_ADD_RINV",
   ``!a. rat_add a (rat_ainv a) = 0q``,
        GEN_TAC THEN
        REWRITE_TAC[rat_add_def,rat_ainv_def,rat_0,RAT_ADD_CONG] THEN
        REWRITE_TAC[frac_add_def,frac_ainv_def,frac_0_def] THEN
        SIMP_TAC bool_ss [NMR, DNM, FRAC_DNMPOS] THEN
        REWRITE_TAC[RAT_ABS_EQUIV,rat_equiv_def] THEN
        VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
        simp[INT_MUL_POS_SIGN, FRAC_DNMPOS] THEN
        REWRITE_TAC [INT_MUL_LZERO, INT_MUL_RID, INT_LT_01,
          GSYM INT_NEG_LMUL, INT_ADD_RINV]) ;

val RAT_ADD_LINV = store_thm("RAT_ADD_LINV",
   ``!a. rat_add (rat_ainv a) a = 0q``,
        ONCE_REWRITE_TAC[RAT_ADD_COMM] THEN
        REWRITE_TAC[RAT_ADD_RINV] );

val RAT_MUL_RINV = store_thm("RAT_MUL_RINV",
   ``!a. ~(a=0q) ==> (rat_mul a (rat_minv a) = 1q)``,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rat_mul_def, rat_minv_def, rat_1, RAT_MUL_CONG] THEN
  REWRITE_TAC[frac_mul_def, frac_minv_def, frac_1_def] THEN
  REWRITE_TAC[RAT_ABS_EQUIV, rat_equiv_def] THEN
  VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
  TRY (irule INT_MUL_POS_SIGN >> conj_tac) THEN
  TRY (irule FRAC_DNMPOS) THEN
  TRY (irule INT_LT_01) THEN
  TRY (irule INT_ABS_NOT0POS) THEN
  ASM_REWRITE_TAC [GSYM RAT_EQ0_NMR, GSYM rat_nmr_def] THEN
  REWRITE_TAC[INT_MUL_LID, INT_MUL_RID, frac_sgn_def,
    ABS_EQ_MUL_SGN, rat_nmr_def] THEN
  CONV_TAC (AC_CONV (INT_MUL_ASSOC, INT_MUL_COMM))) ;

val RAT_MUL_LINV = store_thm("RAT_MUL_LINV",
   ``!a. ~(a = 0q) ==> (rat_mul (rat_minv a) a = 1q)``,
        ONCE_REWRITE_TAC[RAT_MUL_COMM] THEN
        RW_TAC int_ss[RAT_MUL_RINV] );

(*--------------------------------------------------------------------------
   RAT_RDISTRIB: thm
   |- !a b c. rat_mul (rat_add a b) c = rat_add (rat_mul a c) (rat_mul b c)

   RAT_LDISTRIB: thm
   |- !a b c. rat_mul c (rat_add a b) = rat_add (rat_mul c a) (rat_mul c b)
 *--------------------------------------------------------------------------*)

val RAT_RDISTRIB = store_thm("RAT_RDISTRIB",
  ``!a b c. rat_mul (rat_add a b) c = rat_add (rat_mul a c) (rat_mul b c)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_mul_def,rat_add_def] THEN
        REWRITE_TAC[RAT_MUL_CONG, RAT_ADD_CONG] THEN
        REWRITE_TAC[frac_mul_def,frac_add_def] THEN
        VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
        simp[INT_MUL_POS_SIGN, FRAC_DNMPOS] THEN
        REWRITE_TAC[RAT_ABS_EQUIV, rat_equiv_def] THEN
        VALIDATE (CONV_TAC (feqconv NMR THENC feqconv DNM)) THEN
        simp[INT_MUL_POS_SIGN, FRAC_DNMPOS] THEN
        REWRITE_TAC[INT_RDISTRIB] THEN BINOP_TAC THEN
        CONV_TAC (AC_CONV (INT_MUL_ASSOC, INT_MUL_COMM))) ;

val RAT_LDISTRIB = store_thm("RAT_LDISTRIB",
  ``!a b c. rat_mul c (rat_add a b) = rat_add (rat_mul c a) (rat_mul c b)``,
        ONCE_REWRITE_TAC[RAT_MUL_COMM] THEN
        REWRITE_TAC[RAT_RDISTRIB] );

(*--------------------------------------------------------------------------
   RAT_1_NOT_0: thm
   |- ~ (1q=0q)
 *--------------------------------------------------------------------------*)

val RAT_1_NOT_0 = store_thm("RAT_1_NOT_0", ``~ (1q=0q)``,
        REWRITE_TAC[rat_0, rat_1] THEN
        REWRITE_TAC[frac_1_def, frac_0_def] THEN
        REWRITE_TAC[RAT_ABS_EQUIV, rat_equiv_def] THEN
        FRAC_POS_TAC ``1i`` THEN
        RW_TAC int_ss[NMR,DNM] );

(*==========================================================================
 *  arithmetic rules
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_MUL_LZERO: thm
   |- !r1. rat_mul 0q r1 = 0q

   RAT_MUL_RZERO: thm
   |- !r1. rat_mul r1 0q = 0q
 *--------------------------------------------------------------------------*)

val RAT_MUL_LZERO = store_thm(
  "RAT_MUL_LZERO[simp]", “!r1. rat_mul 0q r1 = 0q”,
  GEN_TAC THEN RAT_CALCEQ_TAC);

val RAT_MUL_RZERO = store_thm(
  "RAT_MUL_RZERO[simp]",
  “!r1. rat_mul r1 0q = 0q”,
  PROVE_TAC[RAT_MUL_LZERO, RAT_MUL_COMM] );

(*--------------------------------------------------------------------------
   RAT_SUB_ADDAINV: thm
   |- !r1 r2. rat_sub r1 r2 = rat_add r1 (rat_ainv r2)

   RAT_DIV_MULMINV: thm
   |- !r1 r2. rat_div r1 r2 = rat_mul r1 (rat_minv r2)
 *--------------------------------------------------------------------------*)

val RAT_SUB_ADDAINV = store_thm( "RAT_SUB_ADDAINV",``!r1 r2. rat_sub r1 r2 = rat_add r1 (rat_ainv r2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_sub_def, rat_add_def, rat_ainv_def] THEN
        REWRITE_TAC[frac_sub_def] THEN
        REWRITE_TAC[RAT_ADD_CONG] );

val RAT_DIV_MULMINV = store_thm("RAT_DIV_MULMINV",
  ``!r1 r2. rat_div r1 r2 = rat_mul r1 (rat_minv r2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rat_div_def, rat_mul_def, rat_minv_def] THEN
  REWRITE_TAC[frac_div_def] THEN
  REWRITE_TAC[RAT_MUL_CONG] );

val RAT_DIV_0 = Q.store_thm(
  "RAT_DIV_0[simp]",
  ‘rat_div 0 x = 0’,
  simp[RAT_DIV_MULMINV]);


(*--------------------------------------------------------------------------
   RAT_AINV_0: thm
   |- rat_ainv 0q = 0q

   RAT_AINV_AINV: thm
   |- !r1. rat_ainv (rat_ainv r1) = r1

   RAT_AINV_ADD: thm
   |- ! r1 r2. rat_ainv (rat_add r1 r2) = rat_add (rat_ainv r1) (rat_ainv r2)

   RAT_AINV_SUB: thm
   |- ! r1 r2. rat_ainv (rat_sub r1 r2) = rat_sub r2 r1

   RAT_AINV_RMUL: thm
   |- !r1 r2. rat_ainv (rat_mul r1 r2) = rat_mul r1 (rat_ainv r2)

   RAT_AINV_LMUL: thm
   |- !r1 r2. rat_ainv (rat_mul r1 r2) = rat_mul (rat_ainv r1) r2

   RAT_AINV_MINV: thm
   |- !r1. ~(r1=0q) ==> (rat_ainv (rat_minv r1) = rat_minv (rat_ainv r1))
 *--------------------------------------------------------------------------*)

val RAT_AINV_0 = store_thm("RAT_AINV_0[simp]", ``rat_ainv 0q = 0q``,
        REWRITE_TAC[rat_0,rat_ainv_def] THEN
        RW_TAC int_ss[RAT_AINV_CONG] THEN
        RW_TAC int_ss[FRAC_AINV_0] );

val RAT_AINV_AINV = store_thm("RAT_AINV_AINV[simp]",
  ``!r1. rat_ainv (rat_ainv r1) = r1``,
        GEN_TAC THEN
        REWRITE_TAC[rat_ainv_def] THEN
        RW_TAC int_ss[RAT_AINV_CONG, FRAC_AINV_AINV, rat_thm] );

val RAT_AINV_ADD = store_thm("RAT_AINV_ADD", ``! r1 r2. rat_ainv (rat_add r1 r2) = rat_add (rat_ainv r1) (rat_ainv r2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_add_def,rat_ainv_def] THEN
        REWRITE_TAC[RAT_ADD_CONG, RAT_AINV_CONG] THEN
        RW_TAC int_ss[FRAC_AINV_ADD] );

val RAT_AINV_SUB = store_thm("RAT_AINV_SUB", ``! r1 r2. rat_ainv (rat_sub r1 r2) = rat_sub r2 r1``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        REWRITE_TAC[RAT_AINV_ADD] THEN
        REWRITE_TAC[RAT_AINV_AINV] THEN
        PROVE_TAC[RAT_ADD_COMM] );

val RAT_AINV_RMUL = store_thm("RAT_AINV_RMUL", ``!r1 r2. rat_ainv (rat_mul r1 r2) = rat_mul r1 (rat_ainv r2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_ainv_def, rat_mul_def] THEN
        REWRITE_TAC[RAT_MUL_CONG, RAT_AINV_CONG] THEN
        PROVE_TAC[FRAC_AINV_RMUL] );

val RAT_AINV_LMUL = store_thm("RAT_AINV_LMUL", ``!r1 r2. rat_ainv (rat_mul r1 r2) = rat_mul (rat_ainv r1) r2``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_ainv_def, rat_mul_def] THEN
        REWRITE_TAC[RAT_MUL_CONG, RAT_AINV_CONG] THEN
        PROVE_TAC[FRAC_AINV_LMUL] );

(*--------------------------------------------------------------------------
   RAT_EQ_AINV
   |- !r1 r2. (~r1 = ~r2) = (r1=r2)

   RAT_AINV_EQ
   |- !r1 r2. (~r1 = r2) = (r1 = ~r2)
 *--------------------------------------------------------------------------*)

val RAT_AINV_EQ = store_thm("RAT_AINV_EQ",
  ``!r1 r2. (rat_ainv r1 = r2) = (r1 = rat_ainv r2)``,
        REPEAT GEN_TAC THEN
        EQ_TAC THEN
        STRIP_TAC THEN
        BasicProvers.VAR_EQ_TAC THEN
        REWRITE_TAC[RAT_AINV_AINV] );

val RAT_EQ_AINV = store_thm("RAT_EQ_AINV[simp]",
  ``!r1 r2. (rat_ainv r1 = rat_ainv r2) = (r1=r2)``,
        REWRITE_TAC[RAT_AINV_EQ, RAT_AINV_AINV] ) ;

val RAT_AINV_MINV = store_thm("RAT_AINV_MINV",
  “!r1. r1 <> 0q ==> (rat_ainv (rat_minv r1) = rat_minv (rat_ainv r1))”,
  REPEAT STRIP_TAC THEN
  COPY_ASM_NO 0 THEN
  APPLY_ASM_TAC 0 (REWRITE_TAC[rat_nmr_def, RAT_EQ0_NMR]) THEN
  SUBST_TAC[GSYM RAT_AINV_0] THEN
  ONCE_REWRITE_TAC[GSYM RAT_AINV_EQ] THEN
  REWRITE_TAC[rat_nmr_def, RAT_EQ0_NMR] THEN
  REWRITE_TAC[rat_ainv_def, rat_minv_def] THEN
  REWRITE_TAC[RAT_NMREQ0_CONG] THEN
  STRIP_TAC THEN
  RW_TAC int_ss[RAT_AINV_CONG, RAT_MINV_CONG] THEN
  COPY_ASM_NO 1 THEN
  ONCE_REWRITE_TAC[GSYM INT_EQ_NEG] THEN
  ONCE_REWRITE_TAC[INT_NEG_0] THEN
  STRIP_TAC THEN
  FRAC_CALC_TAC THEN
  REWRITE_TAC[RAT_EQ] THEN
  FRAC_NMRDNM_TAC THEN
  RW_TAC int_ss[INT_ABS, SGN_def] THEN
  TRY (INT_RING_TAC THEN NO_TAC) THEN
  METIS_TAC[integerTheory.INT_LT_REFL, integerTheory.INT_LT_TRANS,
            integerTheory.INT_NOT_LT, integerTheory.INT_LE_ANTISYM,
            integerTheory.INT_MUL_RZERO]);

(*--------------------------------------------------------------------------
   RAT_SUB_RDISTRIB: thm
   |- !a b c. rat_mul (rat_sub a b) c = rat_sub (rat_mul a c) (rat_mul b c)

   RAT_SUB_LDISTRIB: thm
   |- !a b c. rat_mul c (rat_sub a b) = rat_sub (rat_mul c a) (rat_mul c b)
 *--------------------------------------------------------------------------*)

val RAT_SUB_RDISTRIB = store_thm("RAT_SUB_RDISTRIB", ``!a b c. rat_mul (rat_sub a b) c = rat_sub (rat_mul a c) (rat_mul b c)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        REWRITE_TAC[RAT_AINV_LMUL] THEN
        PROVE_TAC[RAT_RDISTRIB] );

val RAT_SUB_LDISTRIB = store_thm("RAT_SUB_LDISTRIB", ``!a b c. rat_mul c (rat_sub a b) = rat_sub (rat_mul c a) (rat_mul c b)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        REWRITE_TAC[RAT_AINV_RMUL] THEN
        PROVE_TAC[RAT_LDISTRIB] );

(*--------------------------------------------------------------------------
   RAT_SUB_LID: thm
   |- !r1. rat_sub 0q r1 = rat_ainv r1

   RAT_SUB_RID: thm
   |- !r1. rat_sub r1 0q = r1
 *--------------------------------------------------------------------------*)

val RAT_SUB_LID = store_thm("RAT_SUB_LID[simp]",
  ``!r1. rat_sub 0q r1 = rat_ainv r1``,
        GEN_TAC THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        REWRITE_TAC[RAT_ADD_LID] );

val RAT_SUB_RID = store_thm("RAT_SUB_RID[simp]",
  ``!r1. rat_sub r1 0q = r1``,
        GEN_TAC THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        REWRITE_TAC[RAT_AINV_0] THEN
        RW_TAC int_ss[RAT_ADD_RID] );

(*--------------------------------------------------------------------------
   RAT_SUB_ID: thm
   |- ! r. r - r = 0q
 *--------------------------------------------------------------------------*)

val RAT_SUB_ID = store_thm("RAT_SUB_ID[simp]",
  ``! r. rat_sub r r = 0q``,
        RW_TAC bool_ss [RAT_SUB_ADDAINV, RAT_ADD_RINV]);

(*--------------------------------------------------------------------------
   RAT_EQ_SUB0: thm
   |- !r1 r2. (rat_sub r1 r2 = 0q) = (r1 = r2)
 *--------------------------------------------------------------------------*)

val RAT_EQ_SUB0 = store_thm("RAT_EQ_SUB0", ``!r1 r2. (rat_sub r1 r2 = 0q) = (r1 = r2)``,
        REPEAT GEN_TAC THEN
        SUBST_TAC[SPEC ``r1:rat`` (GSYM RAT), SPEC ``r2:rat`` (GSYM RAT)] THEN
        REWRITE_TAC[RAT_SUB_CALCULATE, rat_0] THEN
        FRAC_CALC_TAC THEN
        REWRITE_TAC[RAT_ABS_EQUIV, rat_equiv_def] THEN
        FRAC_NMRDNM_TAC THEN
        RW_TAC int_ss[INT_MUL_CALCULATE, GSYM INT_SUB_CALCULATE, INT_SUB_0, INT_MUL_RID, INT_MUL_LZERO] );

(*--------------------------------------------------------------------------
   RAT_EQ_0SUB: thm
   |- !r1 r2. (0q = rat_sub r1 r2) = (r1 = r2)
 *--------------------------------------------------------------------------*)

val RAT_EQ_0SUB = store_thm("RAT_EQ_0SUB", ``!r1 r2. (0q = rat_sub r1 r2) = (r1 = r2)``,
        PROVE_TAC[RAT_EQ_SUB0] );

(*--------------------------------------------------------------------------
 *  signum function
 *--------------------------------------------------------------------------*)

(*--------------------------------------------------------------------------
 *  RAT_SGN_CALCULATE: thm
 *  |- rat_sgn (abs_rat( f1 ) = frac_sgn f1
 *--------------------------------------------------------------------------*)

val RAT_SGN_CALCULATE = store_thm("RAT_SGN_CALCULATE", ``rat_sgn (abs_rat( f1 )) = frac_sgn f1``,
        REWRITE_TAC[rat_sgn_def, rat_0] THEN
        REWRITE_TAC[RAT_SGN_CONG] THEN
        REWRITE_TAC[frac_sgn_def, frac_0_def] THEN
        FRAC_NMRDNM_TAC THEN
        REWRITE_TAC[SGN_def] );

(*--------------------------------------------------------------------------
   RAT_SGN_CLAUSES: thm
   |- !r1.
        ((rat_sgn r1 = ~1) = (r1 < 0q)) /\
        ((rat_sgn r1 = 0i) = (r1 = 0q) ) /\
        ((rat_sgn r1 = 1i) = (r1 > 0q))
 *--------------------------------------------------------------------------*)

val RAT_SGN_CLAUSES = store_thm("RAT_SGN_CLAUSES",
  ``!r1. ((rat_sgn r1 = ~1) = (rat_les r1 0q)) /\
         ((rat_sgn r1 = 0i) = (r1 = 0q)) /\
         ((rat_sgn r1 = 1i) = (rat_gre r1 0q))``,
  GEN_TAC THEN
  REWRITE_TAC[rat_sgn_def, rat_les_def, rat_gre_def] THEN
  REWRITE_TAC[RAT_SUB_ADDAINV, RAT_ADD_LID, RAT_SUB_RID] THEN
  RAT_CALC_TAC THEN
  REWRITE_TAC[RAT_SGN_CONG] THEN
  REPEAT CONJ_TAC THENL
  [
          EQ_TAC THEN
          STRIP_TAC THEN
          PROVE_TAC[FRAC_SGN_AINV, INT_NEG_EQ]
  ,
          REWRITE_TAC[frac_sgn_def, frac_0_def] THEN
          REWRITE_TAC[RAT_EQ] THEN
          FRAC_NMRDNM_TAC THEN
          PROVE_TAC[INT_SGN_CLAUSES]
  ] );

(*--------------------------------------------------------------------------
   RAT_SGN_0: thm
   |- rat_sgn 0q = 0i
 *--------------------------------------------------------------------------*)

val RAT_SGN_0 = store_thm("RAT_SGN_0[simp]",
  ``rat_sgn 0q = 0i``,
  REWRITE_TAC[rat_sgn_def, rat_0] THEN REWRITE_TAC[RAT_SGN_CONG] THEN
  REWRITE_TAC[frac_sgn_def, frac_0_def] THEN
  FRAC_NMRDNM_TAC THEN REWRITE_TAC[SGN_def] );

(*--------------------------------------------------------------------------
   RAT_SGN_AINV: thm
   |- !r1. ~rat_sgn ~r1 = rat_sgn r1
 *--------------------------------------------------------------------------*)

val RAT_SGN_AINV = store_thm("RAT_SGN_AINV", ``!r1. ~rat_sgn (rat_ainv r1) = rat_sgn r1``,
        GEN_TAC THEN
        REWRITE_TAC[rat_sgn_def, rat_ainv_def] THEN
        REWRITE_TAC[RAT_SGN_CONG] THEN
        PROVE_TAC[FRAC_SGN_AINV] );

(*--------------------------------------------------------------------------
   RAT_SGN_MUL: thm
   |- !r1 r2. rat_sgn (r1 * r2) = rat_sgn r1 * rat_sgn r2
 *--------------------------------------------------------------------------*)

val RAT_SGN_MUL = store_thm("RAT_SGN_MUL[simp]",
  ``!r1 r2. rat_sgn (rat_mul r1 r2) = rat_sgn r1 * rat_sgn r2``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_sgn_def, rat_mul_def] THEN
  REWRITE_TAC[RAT_SGN_CONG] THEN PROVE_TAC[FRAC_SGN_MUL2] );

(*--------------------------------------------------------------------------
   RAT_SGN_MINV: thm
   |- !r1. ~(r1 = 0q) ==> (rat_sgn (rat_minv r1) = rat_sgn r1)
 *--------------------------------------------------------------------------*)

val RAT_SGN_MINV = store_thm("RAT_SGN_MINV[simp]",
  ``!r1. ~(r1 = 0q) ==> (rat_sgn (rat_minv r1) = rat_sgn r1)``,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[rat_sgn_def, rat_minv_def] THEN
  MATCH_MP_TAC (SPEC ``rep_rat r1`` FRAC_SGN_CASES) THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_ALL_TAC THEN REWRITE_TAC[RAT_EQ0_NMR, rat_nmr_def] THEN STRIP_TAC THEN
  REWRITE_TAC[frac_sgn_def, frac_minv_def, INT_SGN_CLAUSES] THEN
  STRIP_TAC THEN
  REWRITE_TAC[RAT_NMREQ0_CONG, RAT_NMRGT0_CONG, RAT_NMRLT0_CONG] THEN
  FRAC_NMRDNM_TAC THEN
  RW_TAC int_ss
    [INT_MUL_SIGN_CASES, SGN_def, FRAC_DNMPOS, INT_MUL_LID, int_gt] THEN
  PROVE_TAC[INT_LT_ANTISYM, int_gt] );

(*--------------------------------------------------------------------------
   RAT_SGN_TOTAL
   |- !r1. (rat_sgn r1 = ~1) \/ (rat_sgn r1 = 0) \/ (rat_sgn r1 = 1i)
 *--------------------------------------------------------------------------*)

val RAT_SGN_TOTAL = store_thm("RAT_SGN_TOTAL",
  ``!r1. (rat_sgn r1 = ~1) \/ (rat_sgn r1 = 0) \/ (rat_sgn r1 = 1i)``,
  REWRITE_TAC[rat_sgn_def] THEN
  REWRITE_TAC[frac_sgn_def, SGN_def] THEN
  PROVE_TAC[] );

(*--------------------------------------------------------------------------
   RAT_SGN_COMPLEMENT
   |- !r1.
        (~(rat_sgn r1 = ~1) = ((rat_sgn r1 = 0) \/ (rat_sgn r1 = 1i))) /\
        (~(rat_sgn r1 = 0) = ((rat_sgn r1 = ~1) \/ (rat_sgn r1 = 1i))) /\
        (~(rat_sgn r1 = 1) = ((rat_sgn r1 = ~1) \/ (rat_sgn r1 = 0)))
 *--------------------------------------------------------------------------*)

val RAT_SGN_COMPLEMENT = store_thm("RAT_SGN_COMPLEMENT",
  ``!r1. (~(rat_sgn r1 = ~1) = ((rat_sgn r1 = 0) \/ (rat_sgn r1 = 1i))) /\
         (~(rat_sgn r1 = 0) = ((rat_sgn r1 = ~1) \/ (rat_sgn r1 = 1i))) /\
         (~(rat_sgn r1 = 1) = ((rat_sgn r1 = ~1) \/ (rat_sgn r1 = 0)))``,
  GEN_TAC THEN REPEAT CONJ_TAC THEN
  ASSUME_TAC (SPEC ``r1:rat`` RAT_SGN_TOTAL) THEN
  UNDISCH_ALL_TAC THEN STRIP_TAC THEN
  RW_TAC int_ss [RAT_1_NOT_0] );

(*==========================================================================
 *  order of the rational numbers (less, greater, ...)
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_LES_REF, RAT_LES_ANTISYM, RAT_LES_TRANS, RAT_LES_TOTAL

   |- !r1. ~(r1 < r1)
   |- ! r1 r2. r1 < r2 ==> ~(r2 < r1)
   |- !r1 r2 r3. r1 < r2 /\ r2 < r3 ==> r1 < r3
   |- !r1 r2. r1 < r2 \/ (r1 = r2) \/ r2 < r1
 *--------------------------------------------------------------------------*)

val RAT_LES_REF = store_thm("RAT_LES_REF", ``!r1. ~(rat_les r1 r1)``,
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_ID] THEN
        RW_TAC int_ss[RAT_SGN_0] );

val RAT_LES_ANTISYM =
let
  val lemmaX = prove(``!f. frac_sgn (frac_ainv f) = ~frac_sgn f``,
                     REWRITE_TAC[GSYM INT_NEG_EQ] THEN
                     RW_TAC int_ss[FRAC_SGN_NEG] );
in
  store_thm(
    "RAT_LES_ANTISYM",
    ``!r1 r2. rat_les r1 r2 ==> ~(rat_les r2 r1)``,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[rat_les_def, rat_sgn_def, rat_sub_def] THEN
    REWRITE_TAC[RAT_SGN_CONG] THEN
    SUBST_TAC[SPECL [``rep_rat r1``, ``rep_rat r2``] (GSYM FRAC_AINV_SUB)] THEN
    REWRITE_TAC[lemmaX] THEN REWRITE_TAC[INT_NEG_EQ] THEN RW_TAC int_ss[] )
end;

val RAT_LES_TRANS = store_thm("RAT_LES_TRANS",
  ``!r1 r2 r3. rat_les r1 r2 /\ rat_les r2 r3 ==> rat_les r1 r3``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_les_def] THEN
  SUBGOAL_THEN
    ``rat_sub r3 r1 = rat_add (rat_sub r3 r2) (rat_sub r2 r1)``
    SUBST1_TAC THEN1
  RAT_CALCEQ_TAC THEN REWRITE_TAC[rat_sgn_def, rat_sub_def, rat_add_def] THEN
  REWRITE_TAC[RAT_ADD_CONG, RAT_SUB_CONG] THEN
  REWRITE_TAC[RAT_SGN_CONG] THEN REWRITE_TAC[frac_sgn_def] THEN
  FRAC_CALC_TAC THEN FRAC_NMRDNM_TAC THEN
  REWRITE_TAC[INT_SGN_CLAUSES] THEN REWRITE_TAC[int_gt] THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r2) * frac_dnm (rep_rat r1)`` THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r3) * frac_dnm (rep_rat r2)`` THEN
  REPEAT STRIP_TAC THEN
  PROVE_TAC[INT_LT_ADD,INT_MUL_POS_SIGN] );

val RAT_LES_TOTAL = store_thm("RAT_LES_TOTAL",
  ``!r1 r2. rat_les r1 r2 \/ (r1 = r2) \/ rat_les r2 r1``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_les_def] THEN
  SUBST_TAC[SPECL[``r1:rat``,``r2:rat``] (GSYM RAT_AINV_SUB)] THEN
  SUBST_TAC[
    SPECL[``rat_sgn (rat_ainv (rat_sub r1 r2))``,``1i``] (GSYM INT_EQ_NEG)] THEN
  REWRITE_TAC[RAT_SGN_AINV] THEN
  ONCE_REWRITE_TAC[GSYM RAT_EQ_SUB0] THEN
  SUBST_TAC[
    CONJUNCT1 (CONJUNCT2 (SPEC ``rat_sub r1 r2`` (GSYM RAT_SGN_CLAUSES)))] THEN
  PROVE_TAC[RAT_SGN_TOTAL] );


(*--------------------------------------------------------------------------
   RAT_LEQ_REF, RAT_LEQ_ANTISYM, RAT_LEQ_TRANS
   |- !r1. r1 <= r1
   |- !r1 r2. r1 <= r2 = r2 >= r1
   |- !r1 r2 r3. r1 <= r2 /\ r2 <= r3 ==> r1 <= r3
 *--------------------------------------------------------------------------*)

val RAT_LEQ_REF = store_thm("RAT_LEQ_REF", ``!r1. rat_leq r1 r1``,
        GEN_TAC THEN
        REWRITE_TAC[rat_leq_def] THEN
        REWRITE_TAC[RAT_SUB_ID] THEN
        REWRITE_TAC[rat_sgn_def,rat_0] THEN
        REWRITE_TAC[frac_sgn_def,SGN_def, frac_0_def] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG,RAT_NMRLT0_CONG] THEN
        RW_TAC int_ss[NMR,DNM] );

val RAT_LEQ_ANTISYM = store_thm("RAT_LEQ_ANTISYM",
  ``!r1 r2. rat_leq r1 r2 /\ rat_leq r2 r1 ==> (r1=r2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rat_leq_def] THEN
  RW_TAC bool_ss [] THEN
  PROVE_TAC[RAT_LES_ANTISYM]);

val RAT_LEQ_TRANS = store_thm("RAT_LEQ_TRANS",
  ``!r1 r2 r3. rat_leq r1 r2 /\ rat_leq r2 r3 ==> rat_leq r1 r3``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN
  RW_TAC bool_ss [] THEN PROVE_TAC[RAT_LES_TRANS]);


(*--------------------------------------------------------------------------
   RAT_LES_01
   |- 0q < 1q
 *--------------------------------------------------------------------------*)

val RAT_LES_01 = store_thm("RAT_LES_01", ``rat_les 0q 1q``,
        REWRITE_TAC[rat_les_def] THEN
        RAT_CALC_TAC THEN
        FRAC_CALC_TAC THEN
        REWRITE_TAC[rat_sgn_def, frac_sgn_def, SGN_def] THEN
        REWRITE_TAC[RAT_NMREQ0_CONG, RAT_NMRLT0_CONG] THEN
        FRAC_NMRDNM_TAC );

(*--------------------------------------------------------------------------
   RAT_LES_IMP_LEQ
   |- !r1 r2. r1 < r2 ==> r1 <= r2
 *--------------------------------------------------------------------------*)

val RAT_LES_IMP_LEQ = store_thm("RAT_LES_IMP_LEQ",
  ``!r1 r2. rat_les r1 r2 ==> rat_leq r1 r2``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_les_def, rat_leq_def] THEN
  RW_TAC bool_ss [] );

(*--------------------------------------------------------------------------
   RAT_LES_IMP_NEQ
   |- !r1 r2. r1 < r2 ==> ~(r1 = r2)
 *--------------------------------------------------------------------------*)

val RAT_LES_IMP_NEQ = store_thm("RAT_LES_IMP_NEQ",
  ``!r1 r2. rat_les r1 r2 ==> ~(r1 = r2)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_les_def] THEN
  SUBST_TAC[ISPECL[``r1:rat``,``r2:rat``] EQ_SYM_EQ] THEN
  ONCE_REWRITE_TAC[GSYM RAT_EQ_SUB0] THEN
  SUBST_TAC[
    CONJUNCT1 (CONJUNCT2 (SPEC ``rat_sub r2 r1`` (GSYM RAT_SGN_CLAUSES)))] THEN
  SIMP_TAC int_ss []);

(*--------------------------------------------------------------------------
   RAT_LEQ_LES (RAT_NOT_LES_LEQ)
   |- !r1 r2. ~(r2 < r1) = r1 <= r2
 *--------------------------------------------------------------------------*)

val RAT_LEQ_LES = store_thm("RAT_LEQ_LES",
  ``!r1 r2. ~(rat_les r2 r1) = rat_leq r1 r2``,
  RW_TAC bool_ss[rat_leq_def] THEN
  PROVE_TAC[RAT_LES_TOTAL, RAT_LES_ANTISYM] );

(*--------------------------------------------------------------------------
   RAT_LES_LEQ, RAT_LES_LEQ2

   |- !r1 r2. ~(rat_leq r2 r1) = r1 < r2
   |- !r1 r2. r1 < r2 = r1 <= r2 /\ ~(r2 = r1)
 *--------------------------------------------------------------------------*)

val RAT_LES_LEQ = store_thm("RAT_LES_LEQ",
  ``!r1 r2. ~(rat_leq r2 r1) = rat_les r1 r2``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN
  PROVE_TAC[RAT_LES_TOTAL, RAT_LES_IMP_NEQ, RAT_LES_ANTISYM] );

val RAT_LES_LEQ2 = store_thm("RAT_LES_LEQ2",
  ``!r1 r2. rat_les r1 r2 = rat_leq r1 r2 /\ ~(rat_leq r2 r1)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN EQ_TAC THEN
  RW_TAC bool_ss [] THEN PROVE_TAC[RAT_LES_ANTISYM, RAT_LES_IMP_NEQ] );

(*--------------------------------------------------------------------------
   RAT_LES_LEQ_TRANS, RAT_LEQ_LES_TRANS

   |- !a b c. a < b /\ b <= c ==> a < c
   |- !a b c. a <= b /\ b < c ==> a < c
 *--------------------------------------------------------------------------*)

val RAT_LES_LEQ_TRANS = store_thm("RAT_LES_LEQ_TRANS",
  ``!a b c. rat_les a b /\ rat_leq b c ==> rat_les a c``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN
  PROVE_TAC[RAT_LES_TRANS] );

val RAT_LEQ_LES_TRANS = store_thm("RAT_LEQ_LES_TRANS",
  ``!a b c. rat_leq a b /\ rat_les b c ==> rat_les a c``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN PROVE_TAC[RAT_LES_TRANS] );

(*--------------------------------------------------------------------------
   RAT_0LES_0LES_ADD, RAT_LES0_LES0_ADD

   |- !r1 r2. 0q < r1 ==> 0q < r2 ==> 0q < r1 + r2
   |- !r1 r2. r1 < 0q ==> r2 < 0q ==> r1 + r2 < 0q
 *--------------------------------------------------------------------------*)

val RAT_0LES_0LES_ADD = store_thm("RAT_0LES_0LES_ADD",
  ``!r1 r2. rat_les 0q r1 ==> rat_les 0q r2 ==> rat_les 0q (rat_add r1 r2)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[RAT_0LES_NMR] THEN
  RAT_CALC_TAC THEN FRAC_CALC_TAC THEN
  REWRITE_TAC[rat_nmr_def, RAT, FRAC, RAT_NMRGT0_CONG, (GSYM int_gt)] THEN
  FRAC_NMRDNM_TAC THEN REWRITE_TAC[int_gt] THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r2)`` THEN
  REPEAT STRIP_TAC THEN PROVE_TAC[INT_MUL_SIGN_CASES, INT_LT_ADD] );

val RAT_LES0_LES0_ADD = store_thm("RAT_LES0_LES0_ADD",
  ``!r1 r2. rat_les r1 0q ==> rat_les r2 0q  ==> rat_les (rat_add r1 r2) 0q``,
  REPEAT GEN_TAC THEN REWRITE_TAC[RAT_LES0_NMR] THEN
  RAT_CALC_TAC THEN FRAC_CALC_TAC THEN
  REWRITE_TAC[rat_nmr_def, RAT, FRAC, RAT_NMRLT0_CONG] THEN
  FRAC_NMRDNM_TAC THEN REWRITE_TAC[int_gt] THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
  FRAC_POS_TAC ``frac_dnm (rep_rat r2)`` THEN
  REPEAT STRIP_TAC THEN PROVE_TAC[INT_MUL_SIGN_CASES, INT_LT_ADD_NEG] );

(*--------------------------------------------------------------------------
   RAT_0LES_0LEQ_ADD, RAT_LES0_LEQ0_ADD

   |- !r1 r2. 0q < r1 ==> 0q <= r2 ==> 0q < r1 + r2
   |- !r1 r2. r1 < 0q ==> r2 <= 0q ==> r1 + r2 < 0q
 *--------------------------------------------------------------------------*)

val RAT_0LES_0LEQ_ADD = store_thm("RAT_0LES_0LEQ_ADD",
  ``!r1 r2. rat_les 0q r1 ==> rat_leq 0q r2 ==> rat_les 0q (rat_add r1 r2)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN RW_TAC bool_ss [] THEN
  PROVE_TAC[RAT_0LES_0LES_ADD, RAT_ADD_RID] );


val RAT_LES0_LEQ0_ADD = store_thm("RAT_LES0_LEQ0_ADD",
  ``!r1 r2. rat_les r1 0q ==> rat_leq r2 0q ==> rat_les (rat_add r1 r2) 0q``,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_leq_def] THEN RW_TAC bool_ss [] THEN
  PROVE_TAC[RAT_LES0_LES0_ADD, RAT_ADD_RID] );

(*--------------------------------------------------------------------------
   RAT_LSUB_EQ, RAT_RSUB_EQ

   |- !r1 r2 r3. (r1 - r2 = r3) = (r1 = r2 + r3)
   |- !r1 r2 r3. (r1 = r2 - r3) = (r1 + r3 = r2)
 *--------------------------------------------------------------------------*)

val RAT_LSUB_EQ = store_thm("RAT_LSUB_EQ",
  ``!r1 r2 r3. (rat_sub r1 r2 = r3) = (r1 = rat_add r2 r3)``,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC[RAT_SUB_ADDAINV] THEN ONCE_REWRITE_TAC[RAT_ADD_COMM] THENL [
    ONCE_REWRITE_TAC[GSYM RAT_ADD_ASSOC]
    ,
    ONCE_REWRITE_TAC[RAT_ADD_ASSOC]
  ] THEN
  REWRITE_TAC[RAT_ADD_LINV] THEN REWRITE_TAC[RAT_ADD_LID, RAT_ADD_RID] );

val RAT_RSUB_EQ = store_thm("RAT_RSUB_EQ",
  ``!r1 r2 r3. (r1 = rat_sub r2 r3) = (rat_add r1 r3 = r2)``,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC[RAT_SUB_ADDAINV] THEN ONCE_REWRITE_TAC[GSYM RAT_ADD_ASSOC] THEN
  REWRITE_TAC[RAT_ADD_LINV, RAT_ADD_RINV] THEN
  REWRITE_TAC[RAT_ADD_LID, RAT_ADD_RID] );

(*--------------------------------------------------------------------------
   RAT_LDIV_EQ, RAT_RDIV_EQ

   |- !r1 r2 r3. ~(r2 = 0q) ==> ((r1 / r2 = r3) = (r1 = r2 * r3))
   |- !r1 r2 r3. ~(r3 = 0q) ==> ((r1 = r2 / r3) = (r1 * r3 = r2))
 *--------------------------------------------------------------------------*)

val RAT_LDIV_EQ = store_thm("RAT_LDIV_EQ",
  ``!r1 r2 r3. ~(r2 = 0q) ==> ((rat_div r1 r2 = r3) = (r1 = rat_mul r2 r3))``,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  BasicProvers.VAR_EQ_TAC THEN
  ONCE_REWRITE_TAC [RAT_MUL_COMM] THEN
  REWRITE_TAC [RAT_DIV_MULMINV, GSYM RAT_MUL_ASSOC] THEN
  ASM_SIMP_TAC std_ss [RAT_MUL_RINV, RAT_MUL_LINV, RAT_MUL_RID, RAT_MUL_LID]) ;

val RAT_RDIV_EQ = store_thm("RAT_RDIV_EQ",
  ``!r1 r2 r3. ~(r3 = 0q) ==> ((r1 = rat_div r2 r3) = (rat_mul r1 r3 = r2))``,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC [RAT_DIV_MULMINV, GSYM RAT_MUL_ASSOC] THEN
  ASM_SIMP_TAC std_ss [RAT_MUL_RINV, RAT_MUL_LINV, RAT_MUL_RID, RAT_MUL_LID]) ;


(*==========================================================================
 *  one-to-one and onto theorems
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_AINV_ONE_ONE

   |- ONE_ONE rat_ainv
 *--------------------------------------------------------------------------*)

val RAT_AINV_ONE_ONE = store_thm("RAT_AINV_ONE_ONE", ``ONE_ONE rat_ainv``,
        REWRITE_TAC[ONE_ONE_DEF] THEN
        BETA_TAC THEN
        REWRITE_TAC[RAT_EQ_AINV] );

(*--------------------------------------------------------------------------
   RAT_ADD_ONE_ONE

   |- !r1. ONE_ONE (rat_add r1)
 *--------------------------------------------------------------------------*)

val RAT_ADD_ONE_ONE = store_thm("RAT_ADD_ONE_ONE",
  ``!r1. ONE_ONE (rat_add r1)``,
  REPEAT GEN_TAC THEN
  SIMP_TAC std_ss [ONE_ONE_DEF, GSYM RAT_LSUB_EQ] THEN
  SIMP_TAC std_ss [RAT_RSUB_EQ] THEN
  MATCH_ACCEPT_TAC RAT_ADD_COMM) ;

(*--------------------------------------------------------------------------
   RAT_MUL_ONE_ONE

   |- !r1. ~(r1=0q) = ONE_ONE (rat_mul r1)
 *--------------------------------------------------------------------------*)

val RAT_MUL_ONE_ONE = store_thm("RAT_MUL_ONE_ONE",
  ``!r1. ~(r1=0q) = ONE_ONE (rat_mul r1)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [ONE_ONE_DEF] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT DISCH_TAC
  THENL [
    ASM_SIMP_TAC std_ss [GSYM RAT_LDIV_EQ] THEN
    ASM_SIMP_TAC std_ss [RAT_RDIV_EQ] THEN
    MATCH_ACCEPT_TAC RAT_MUL_COMM,
    FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL [`1q`, `0q`]) THEN
    REV_FULL_SIMP_TAC std_ss [RAT_1_NOT_0, RAT_MUL_LZERO] ]) ;

(*==========================================================================
 *  transformation of equations
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_EQ_LADD, RAT_EQ_RADD

   |- !r1 r2 r3. (r3 + r1 = r3 + r2) = (r1=r2)
   |- !r1 r2 r3. (r1 + r3 = r2 + r3) = (r1=r2)
 *--------------------------------------------------------------------------*)

val RAT_EQ_LADD = store_thm("RAT_EQ_LADD", ``!r1 r2 r3. (rat_add r3 r1 = rat_add r3 r2) = (r1=r2)``,
        PROVE_TAC [REWRITE_RULE[ONE_ONE_THM] RAT_ADD_ONE_ONE, RAT_ADD_COMM] );

val RAT_EQ_RADD = store_thm("RAT_EQ_RADD", ``!r1 r2 r3. (rat_add r1 r3 = rat_add r2 r3) = (r1=r2)``,
        PROVE_TAC [REWRITE_RULE[ONE_ONE_THM] RAT_ADD_ONE_ONE, RAT_ADD_COMM] );

(*--------------------------------------------------------------------------
   RAT_EQ_LMUL, RAT_EQ_RMUL

   |- !r1 r2 r3. ~(r3=0q) ==> ((r3 * r1 = r3 * r2) = (r1=r2))
   |- !r1 r2 r3. ~(r3=0q) ==> ((r1 * r3 = r2 * r3) = (r1=r2))
 *--------------------------------------------------------------------------*)

val RAT_EQ_RMUL = store_thm("RAT_EQ_RMUL", ``!r1 r2 r3. ~(r3=0q) ==> ((rat_mul r1 r3 = rat_mul r2 r3) = (r1=r2))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[SPEC ``r3:rat`` RAT_MUL_ONE_ONE] THEN
        REWRITE_TAC[ONE_ONE_THM] THEN
        STRIP_TAC THEN
        ONCE_REWRITE_TAC[RAT_MUL_COMM] THEN
        PROVE_TAC[] );

val RAT_EQ_LMUL = store_thm("RAT_EQ_LMUL", ``!r1 r2 r3. ~(r3=0q) ==> ((rat_mul r3 r1 = rat_mul r3 r2) = (r1=r2))``,
        PROVE_TAC[RAT_EQ_RMUL, RAT_MUL_COMM] );

(*==========================================================================
 *  transformation of inequations
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_LES_LADD, RAT_LES_RADD, RAT_LEQ_LADD, RAT_LEQ_RADD

   |- !r1 r2 r3. (r3 + r1) < (r3 + r2) = r1 < r2
   |- !r1 r2 r3. (r1 + r3) < (r2 + r3) = r1 < r2
   |- !r1 r2 r3. (r3 + r1) <= (r3 + r2) = r1 <= r2
   |- !r1 r2 r3. (r1 + r3) <= (r2 + r3) = r1 <= r2
 *--------------------------------------------------------------------------*)

val RAT_LES_RADD = store_thm("RAT_LES_RADD", ``!r1 r2 r3. rat_les (rat_add r1 r3) (rat_add r2 r3) = rat_les r1 r2``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def, rat_sgn_def] THEN
        REWRITE_TAC[RAT_SUB_ADDAINV, RAT_AINV_ADD] THEN
        SUBST_TAC[ EQT_ELIM (AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) ``rat_add (rat_add r2 r3) (rat_add (rat_ainv r1) (rat_ainv r3)) = rat_add (rat_add r2 (rat_ainv r1)) (rat_add r3 (rat_ainv r3))``) ] THEN
        REWRITE_TAC[RAT_ADD_RINV, RAT_ADD_RID] );

val RAT_LES_LADD = store_thm("RAT_LES_LADD", ``!r1 r2 r3. rat_les (rat_add r3 r1) (rat_add r3 r2) = rat_les r1 r2``,
        PROVE_TAC[RAT_LES_RADD, RAT_ADD_COMM] );

val RAT_LEQ_RADD = store_thm("RAT_LEQ_RADD",
  ``!r1 r2 r3. rat_leq (rat_add r1 r3) (rat_add r2 r3) = rat_leq r1 r2``,
        REWRITE_TAC[rat_leq_def, RAT_LES_RADD, RAT_EQ_RADD]) ;

val RAT_LEQ_LADD = store_thm("RAT_LEQ_LADD",
  ``!r1 r2 r3. rat_leq (rat_add r3 r1) (rat_add r3 r2) = rat_leq r1 r2``,
        REWRITE_TAC[rat_leq_def, RAT_LES_LADD, RAT_EQ_LADD]) ;

val RAT_ADD_MONO = Q.store_thm ("RAT_ADD_MONO",
  `!a b c d. a <= b /\ c <= d ==> rat_add a c <= rat_add b d`,
  REPEAT STRIP_TAC THEN irule RAT_LEQ_TRANS THEN
  Q.EXISTS_TAC `b + c` THEN
  ASM_SIMP_TAC std_ss [RAT_LEQ_LADD, RAT_LEQ_RADD]) ;

(*--------------------------------------------------------------------------
   RAT_LES_AINV

   |- !r1 r2. ~r1 < ~r2 = r2 < r1
 *--------------------------------------------------------------------------*)

val RAT_LES_AINV = store_thm("RAT_LES_AINV", ``!r1 r2. rat_les (rat_ainv r1) (rat_ainv r2) = rat_les r2 r1``,
        REPEAT GEN_TAC THEN
        SUBST_TAC[ SPECL[``rat_ainv r1``,``rat_ainv r2``,``r1:rat``] (GSYM RAT_LES_RADD)] THEN
        SUBST_TAC[ SPECL[``rat_add (rat_ainv r1) r1``,``rat_add (rat_ainv r2) r1``,``r2:rat``] (GSYM RAT_LES_RADD)] THEN
        SUBST_TAC[ EQT_ELIM (AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) ``rat_add (rat_add (rat_ainv r2) r1) r2 = rat_add (rat_add (rat_ainv r2) r2) r1``) ] THEN
        REWRITE_TAC[RAT_ADD_LINV, RAT_ADD_LID] );

(*--------------------------------------------------------------------------
   RAT_LSUB_LES, RAT_RSUB_LES

   |- !r1 r2 r3. (r1 - r2) < r3 = r1 < (r2 + r3)
   |- !r1 r2 r3. r1 < (r2 - r3) = (r1 + r3) < r2
 *--------------------------------------------------------------------------*)

val RAT_LSUB_LES = store_thm("RAT_LSUB_LES", ``!r1 r2 r3. rat_les (rat_sub r1 r2) r3 = rat_les r1 (rat_add r2 r3)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_ADDAINV, RAT_AINV_ADD, RAT_AINV_AINV] THEN
        PROVE_TAC [AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) ``rat_add r3 (rat_add (rat_ainv r1)  r2) = rat_add (rat_add r2 r3) (rat_ainv r1)``] );

val RAT_RSUB_LES = store_thm("RAT_RSUB_LES", ``!r1 r2 r3. rat_les r1 (rat_sub r2 r3) = rat_les (rat_add r1 r3) r2``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_ADDAINV, RAT_AINV_ADD] THEN
        PROVE_TAC [AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) ``rat_add (rat_add r2 (rat_ainv r3)) (rat_ainv r1) = rat_add r2 (rat_add (rat_ainv r1) (rat_ainv r3))``] );

val RAT_LSUB_LEQ = store_thm("RAT_LSUB_LEQ",
  ``!r1 r2 r3. rat_leq (rat_sub r1 r2) r3 = rat_leq r1 (rat_add r2 r3)``,
        REWRITE_TAC[rat_leq_def, RAT_LSUB_LES, RAT_LSUB_EQ]) ;

val RAT_RSUB_LEQ = store_thm("RAT_RSUB_LEQ",
  ``!r1 r2 r3. rat_leq r1 (rat_sub r2 r3) = rat_leq (rat_add r1 r3) r2``,
        REWRITE_TAC[rat_leq_def, RAT_RSUB_LES, RAT_RSUB_EQ]) ;

(*--------------------------------------------------------------------------
   RAT_LES_LMUL_NEG RAT_LES_LMUL_POS RAT_LES_RMUL_POS RAT_LES_RMUL_NEG

   |- !r1 r2 r3. r3 < 0q ==> (r3 * r2 < r3 * r1) = r1 < r2)
   |- !r1 r2 r3. 0q < r3 ==> (r3 * r1 < r3 * r2) = r1 < r2)
   |- !r1 r2 r3. 0q < r3 ==> (r1 * r3 < r2 * r3) = r1 < r2)
   |- !r1 r2 r3. r3 < 0q ==> (r2 * r3 < r1 * r3) = r1 < r2)
 *--------------------------------------------------------------------------*)

val RAT_LES_RMUL_POS = store_thm("RAT_LES_RMUL_POS", ``!r1 r2 r3. rat_les 0q r3 ==> (rat_les (rat_mul r1 r3) (rat_mul r2 r3) = rat_les r1 r2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_RID] THEN
        STRIP_TAC THEN
        REWRITE_TAC[GSYM RAT_SUB_RDISTRIB] THEN
        EQ_TAC THENL
        [
                SUBGOAL_THEN ``~(r3 = 0q)`` ASSUME_TAC THENL
                [
                        SUBST_TAC[CONJUNCT1 (CONJUNCT2 (SPEC ``r3:rat`` (GSYM RAT_SGN_CLAUSES)))] THEN
                        RW_TAC int_ss[]
                ,
                        UNDISCH_TAC ``rat_sgn r3 = 1i`` THEN
                        SUBST_TAC [GSYM (UNDISCH (SPEC ``r3:rat`` RAT_SGN_MINV))] THEN
                        REPEAT DISCH_TAC THEN
                        ONCE_REWRITE_TAC[GSYM RAT_MUL_RID] THEN
                        SUBST_TAC[GSYM (UNDISCH (SPEC ``r3:rat`` RAT_MUL_RINV))] THEN
                        SUBST_TAC[EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``rat_mul (rat_sub r2 r1) (rat_mul r3 (rat_minv r3)) = rat_mul (rat_mul (rat_sub r2 r1) r3) (rat_minv r3)``)] THEN
                        PROVE_TAC[RAT_SGN_MUL, INT_MUL_LID]
                ]
        ,
                STRIP_TAC THEN
                PROVE_TAC[RAT_SGN_MUL, INT_MUL_LID]
        ] );

val RAT_LES_LMUL_POS = store_thm("RAT_LES_LMUL_POS", ``!r1 r2 r3. rat_les 0q r3 ==> (rat_les (rat_mul r3 r1) (rat_mul r3 r2) = rat_les r1 r2)``,
        PROVE_TAC[RAT_LES_RMUL_POS, RAT_MUL_COMM] );

val RAT_LES_RMUL_NEG = store_thm("RAT_LES_RMUL_NEG", ``!r1 r2 r3. rat_les r3 0q ==> (rat_les (rat_mul r2 r3) (rat_mul r1 r3) = rat_les r1 r2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_ADDAINV, RAT_ADD_LID] THEN
        SUBST_TAC[REWRITE_RULE [INT_NEG_EQ] (SPECL[``r3:rat``] (RAT_SGN_AINV))] THEN
        REWRITE_TAC[INT_NEG_EQ] THEN
        STRIP_TAC THEN
        SUBST_TAC[REWRITE_RULE [RAT_AINV_EQ] (SPECL[``r1:rat``,``r3:rat``] RAT_AINV_LMUL)] THEN
        REWRITE_TAC[GSYM RAT_AINV_ADD] THEN
        REWRITE_TAC[GSYM RAT_RDISTRIB] THEN
        SUBST_TAC[SPECL[``rat_ainv r1``,``r2:rat``] RAT_ADD_COMM] THEN
        EQ_TAC THENL
        [
                SUBGOAL_THEN ``~(r3 = 0q)`` ASSUME_TAC THENL
                [
                        SUBST_TAC[CONJUNCT1 (CONJUNCT2 (SPEC ``r3:rat`` (GSYM RAT_SGN_CLAUSES)))] THEN
                        RW_TAC int_ss[]
                ,
                        UNDISCH_TAC ``rat_sgn r3 = ~1`` THEN
                        SUBST_TAC [GSYM (UNDISCH (SPEC ``r3:rat`` RAT_SGN_MINV))] THEN
                        REPEAT DISCH_TAC THEN
                        ONCE_REWRITE_TAC[GSYM RAT_MUL_RID] THEN
                        SUBST_TAC[GSYM (UNDISCH (SPEC ``r3:rat`` RAT_MUL_RINV))] THEN
                        SUBST_TAC[EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``rat_mul (rat_add r2 (rat_ainv r1)) (rat_mul r3 (rat_minv r3)) = rat_mul (rat_mul (rat_add r2 (rat_ainv r1)) r3) (rat_minv r3)``)] THEN
                        ONCE_REWRITE_TAC[GSYM RAT_SGN_AINV] THEN
                        REWRITE_TAC[INT_NEG_EQ] THEN
                        ONCE_REWRITE_TAC[RAT_AINV_LMUL] THEN
                        RW_TAC int_ss [RAT_SGN_MUL]

                ]
        ,
                STRIP_TAC THEN
                ONCE_REWRITE_TAC[GSYM INT_EQ_NEG] THEN
                REWRITE_TAC[RAT_SGN_AINV] THEN
                RW_TAC int_ss [RAT_SGN_MUL]
        ] );

val RAT_LES_LMUL_NEG = store_thm("RAT_LES_LMUL_NEG", ``!r1 r2 r3. rat_les r3 0q ==> (rat_les (rat_mul r3 r2) (rat_mul r3 r1) = rat_les r1 r2)``,
        PROVE_TAC[RAT_LES_RMUL_NEG, RAT_MUL_COMM] );

(*--------------------------------------------------------------------------
   RAT_AINV_LES

   |- !r1 r2. ~r1 < r2 = ~r2 < r1
 *--------------------------------------------------------------------------*)

val RAT_AINV_LES = store_thm("RAT_AINV_LES", ``!r1 r2. rat_les (rat_ainv r1) r2 = rat_les (rat_ainv r2) r1``,
        REPEAT GEN_TAC THEN
        SUBST_TAC[SPECL [``r1:rat``,``~r2:rat``] (GSYM RAT_LES_AINV)] THEN
        PROVE_TAC[RAT_AINV_AINV] );

(*--------------------------------------------------------------------------
   RAT_LDIV_LES_POS, RAT_LDIV_LES_NEG, RAT_RDIV_LES_POS, RAT_RDIV_LES_NEG

   |- !r1 r2 r3. 0q < r2 ==> ((r1 / r2 < r3) = (r1 < r2 * r3))
   |- !r1 r2 r3. r2 < 0q ==> ((r1 / r2 < r3) = (r2 * r3 < r1))
   |- !r1 r2 r3. 0q < r3 ==> ((r1 < r2 / r3) = (r1 * r3 < r2))
   |- !r1 r2 r3. r3 < 0q ==> ((r1 < r2 / r3) = (r2 < r1 * r3))

   RAT_LDIV_LEQ_POS, RAT_LDIV_LEQ_NEG, RAT_RDIV_LEQ_POS, RAT_RDIV_LEQ_NEG
   for <= likewise
 *--------------------------------------------------------------------------*)

val RAT_LDIV_LES_POS = store_thm("RAT_LDIV_LES_POS", ``!r1 r2 r3. 0q < r2 ==> ((rat_div r1 r2 < r3) = (r1 < rat_mul r2 r3))``,
        REPEAT STRIP_TAC THEN
        SUBST_TAC [UNDISCH (SPECL[``rat_div r1 r2``,``r3:rat``,``r2:rat``] (GSYM RAT_LES_LMUL_POS))] THEN
        SUBGOAL_THEN ``~(r2=0q)`` ASSUME_TAC THEN1
        PROVE_TAC[RAT_LES_REF] THEN
        REWRITE_TAC [RAT_DIV_MULMINV] THEN
        SUBST_TAC [EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``r2 * (r1 * rat_minv r2) = r1 * (r2 * rat_minv r2)``)] THEN
        RW_TAC bool_ss [RAT_MUL_RINV, RAT_MUL_RID] );

val RAT_LDIV_LES_NEG = store_thm("RAT_LDIV_LES_NEG", ``!r1 r2 r3. r2 < 0q ==> ((rat_div r1 r2 < r3) = (rat_mul r2 r3 < r1))``,
        REPEAT STRIP_TAC THEN
        SUBST_TAC [UNDISCH (SPECL[``rat_div r1 r2``,``r3:rat``,``r2:rat``] (GSYM RAT_LES_RMUL_NEG))] THEN
        SUBGOAL_THEN ``~(r2=0q)`` ASSUME_TAC THEN1
        PROVE_TAC[RAT_LES_REF] THEN
        RW_TAC bool_ss [RAT_DIV_MULMINV, GSYM RAT_MUL_ASSOC, RAT_MUL_LINV, RAT_MUL_RID] THEN
        PROVE_TAC[RAT_MUL_COMM] );

val RAT_RDIV_LES_POS = store_thm("RAT_RDIV_LES_POS", ``!r1 r2 r3. 0q < r3 ==> ((r1 < rat_div r2 r3) = (rat_mul r1 r3 < r2))``,
        REPEAT STRIP_TAC THEN
        SUBST_TAC [UNDISCH (SPECL[``r1:rat``,``rat_div r2 r3``,``r3:rat``] (GSYM RAT_LES_RMUL_POS))] THEN
        SUBGOAL_THEN ``~(r3=0q)`` ASSUME_TAC THEN1
        PROVE_TAC[RAT_LES_REF] THEN
        REWRITE_TAC [RAT_DIV_MULMINV] THEN
        SUBST_TAC [EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``r2 * rat_minv r3 * r3 = r2 * (r3 * rat_minv r3)``)] THEN
        RW_TAC bool_ss [RAT_MUL_RINV, RAT_MUL_RID] );

val RAT_RDIV_LES_NEG = store_thm("RAT_RDIV_LES_NEG", ``!r1 r2 r3. r3 < 0q ==> ((r1 < rat_div r2 r3) = (r2 < rat_mul r1 r3))``,
        REPEAT STRIP_TAC THEN
        SUBST_TAC [UNDISCH (SPECL[``r1:rat``,``rat_div r2 r3``,``r3:rat``] (GSYM RAT_LES_RMUL_NEG))] THEN
        SUBGOAL_THEN ``~(r3=0q)`` ASSUME_TAC THEN1
        PROVE_TAC[RAT_LES_REF] THEN
        REWRITE_TAC [RAT_DIV_MULMINV] THEN
        SUBST_TAC [EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``r2 * rat_minv r3 * r3 = r2 * (r3 * rat_minv r3)``)] THEN
        RW_TAC bool_ss [RAT_MUL_RINV, RAT_MUL_RID] );

val RAT_LDIV_LEQ_POS = store_thm("RAT_LDIV_LEQ_POS",
  ``!r1 r2 r3. 0q < r2 ==> ((rat_div r1 r2 <= r3) = (r1 <= rat_mul r2 r3))``,
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC bool_ss [rat_leq_def, RAT_LDIV_LES_POS] THEN
        RULE_ASSUM_TAC (CONJUNCT2 o
          REWRITE_RULE [rat_leq_def, DE_MORGAN_THM] o
          REWRITE_RULE [GSYM RAT_LES_LEQ]) THEN
        ASM_SIMP_TAC bool_ss [RAT_LDIV_EQ]) ;

val RAT_LDIV_LEQ_NEG = store_thm("RAT_LDIV_LEQ_NEG",
  ``!r1 r2 r3. r2 < 0q ==> ((rat_div r1 r2 <= r3) = (rat_mul r2 r3 <= r1))``,
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC bool_ss [rat_leq_def, RAT_LDIV_LES_NEG] THEN
        RULE_ASSUM_TAC (GSYM o CONJUNCT2 o
          REWRITE_RULE [rat_leq_def, DE_MORGAN_THM] o
          REWRITE_RULE [GSYM RAT_LES_LEQ]) THEN
        CONV_TAC (RHS_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
        ASM_SIMP_TAC bool_ss [RAT_LDIV_EQ]) ;

val RAT_RDIV_LEQ_POS = store_thm("RAT_RDIV_LEQ_POS",
  ``!r1 r2 r3. 0q < r3 ==> ((r1 <= rat_div r2 r3) = (rat_mul r1 r3 <= r2))``,
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC bool_ss [rat_leq_def, RAT_RDIV_LES_POS] THEN
        RULE_ASSUM_TAC (CONJUNCT2 o
          REWRITE_RULE [rat_leq_def, DE_MORGAN_THM] o
          REWRITE_RULE [GSYM RAT_LES_LEQ]) THEN
        ASM_SIMP_TAC bool_ss [RAT_RDIV_EQ]) ;

val RAT_RDIV_LEQ_NEG = store_thm("RAT_RDIV_LEQ_NEG",
  ``!r1 r2 r3. r3 < 0q ==> ((r1 <= rat_div r2 r3) = (r2 <= rat_mul r1 r3))``,
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC bool_ss [rat_leq_def, RAT_RDIV_LES_NEG] THEN
        RULE_ASSUM_TAC (GSYM o CONJUNCT2 o
          REWRITE_RULE [rat_leq_def, DE_MORGAN_THM] o
          REWRITE_RULE [GSYM RAT_LES_LEQ]) THEN
        CONV_TAC (RHS_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
        ASM_SIMP_TAC bool_ss [RAT_RDIV_EQ]) ;

(*--------------------------------------------------------------------------
   RAT_LES_SUB0

   |- !r1 r2. (r1 - r2) < 0q = r1 < r2
 *--------------------------------------------------------------------------*)

val RAT_LES_SUB0 = store_thm("RAT_LES_SUB0", ``!r1 r2. rat_les (rat_sub r1 r2) 0q = rat_les r1 r2``,
        REPEAT GEN_TAC THEN
        SUBST_TAC[GSYM (SPECL[``rat_sub r1 r2``,``0q``,``r2:rat``] RAT_LES_RADD)] THEN
        REWRITE_TAC[RAT_SUB_ADDAINV] THEN
        SUBST_TAC[EQT_ELIM(AC_CONV(RAT_ADD_ASSOC, RAT_ADD_COMM) ``rat_add (rat_add r1 (rat_ainv r2)) r2 = rat_add r1 (rat_add (rat_ainv r2) r2)``)] THEN
        REWRITE_TAC[RAT_ADD_LID, RAT_ADD_RID, RAT_ADD_LINV] );

(*--------------------------------------------------------------------------
   RAT_LES_0SUB

   |- !r1 r2. 0q < r1 - r2 = r2 < r1
 *--------------------------------------------------------------------------*)

val RAT_LES_0SUB = store_thm("RAT_LES_0SUB", ``!r1 r2. rat_les 0q (rat_sub r1 r2) = rat_les r2 r1``,
        ONCE_REWRITE_TAC[GSYM RAT_LES_AINV] THEN
        REWRITE_TAC[RAT_AINV_SUB, RAT_AINV_0] THEN
        REWRITE_TAC[RAT_LES_SUB0] THEN
        PROVE_TAC[RAT_LES_AINV] );


(*--------------------------------------------------------------------------
   RAT_MINV_LES

   |- !r1. 0q < r1 ==>
        (rat_minv r1 < 0q = r1 < 0q) /\
        (0q < rat_minv r1 = 0q < r1)
 *--------------------------------------------------------------------------*)

val RAT_MINV_LES = store_thm("RAT_MINV_LES", ``!r1. 0q < r1 ==> (rat_minv r1 < 0q = r1 < 0q) /\ (0q < rat_minv r1 = 0q < r1)``,
        GEN_TAC THEN
        DISCH_TAC THEN
        REWRITE_TAC[rat_les_def] THEN
        REWRITE_TAC[RAT_SUB_LID, RAT_SUB_RID] THEN
        ASSUME_TAC (UNDISCH (SPECL[``0q``,``r1:rat``] (prove(``!r1 r2. rat_les r1 r2 ==> ~(r1=r2)``,
        PROVE_TAC[RAT_LES_REF])))) THEN
        UNDISCH_HD_TAC THEN
        ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
        DISCH_TAC THEN
        ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
        RW_TAC bool_ss [RAT_SGN_MINV] THEN
        ONCE_REWRITE_TAC[GSYM INT_EQ_NEG] THEN
        ONCE_REWRITE_TAC[RAT_SGN_AINV] THEN
        RW_TAC bool_ss [RAT_SGN_MINV] );


(*==========================================================================
 *  other theorems
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_MUL_SIGN_CASES

   |- !p q.
        (0q < p * q = 0q < p /\ 0q < q \/ p < 0q /\ q < 0q) /\
        (p * q < 0q = 0q < p /\ q < 0q \/ p < 0q /\ 0q < q)
 *--------------------------------------------------------------------------*)

val RAT_MUL_SIGN_CASES  = store_thm("RAT_MUL_SIGN_CASES", ``!p q. (0q < p * q = 0q < p /\ 0q < q \/ p < 0q /\ q < 0q) /\ (p * q < 0q = 0q < p /\ q < 0q \/ p < 0q /\ 0q < q)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_les_def, RAT_SUB_LID, RAT_SUB_RID] THEN
        SUBST_TAC[GSYM (SPECL[``rat_sgn ~p``,``1i``] INT_EQ_NEG), GSYM (SPECL[``rat_sgn ~q``,``1i``] INT_EQ_NEG), GSYM (SPECL[``rat_sgn ~(p*q)``,``1i``] INT_EQ_NEG)] THEN
        REWRITE_TAC[RAT_SGN_AINV,RAT_SGN_MUL] THEN
        CONJ_TAC THEN
        ASSUME_TAC (SPEC ``p:rat`` RAT_SGN_TOTAL) THEN
        ASSUME_TAC (SPEC ``q:rat`` RAT_SGN_TOTAL) THEN
        UNDISCH_ALL_TAC THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC int_ss [] );

(*--------------------------------------------------------------------------
   RAT_NO_ZERODIV
   |- !r1 r2. (r1 = 0q) \/ (r2 = 0q) = (r1 * r2 = 0q)

   RAT_NO_ZERODIV_NEG
   |- !r1 r2. ~(r1 * r2 = 0q) = ~(r1 = 0q) /\ ~(r2 = 0q)
 *--------------------------------------------------------------------------*)

val RAT_NO_ZERODIV = store_thm("RAT_NO_ZERODIV", ``!r1 r2. (r1 = 0q) \/ (r2 = 0q) = (rat_mul r1 r2 = 0q)``,
        REPEAT GEN_TAC THEN
        ASM_CASES_TAC ``r1=0q`` THEN
        ASM_CASES_TAC ``r2=0q`` THEN
        RW_TAC int_ss[RAT_MUL_LZERO, RAT_MUL_RZERO] THEN
        UNDISCH_ALL_TAC THEN
        REWRITE_TAC[RAT_EQ0_NMR, rat_nmr_def] THEN
        DISCH_TAC THEN
        DISCH_TAC THEN
        RAT_CALCTERM_TAC ``rat_mul r1 r2`` THEN
        FRAC_CALCTERM_TAC ``frac_mul (rep_rat r1) (rep_rat r2)`` THEN
        REWRITE_TAC[RAT_NMREQ0_CONG] THEN
        FRAC_NMRDNM_TAC THEN
        PROVE_TAC[INT_NO_ZERODIV] );

val RAT_NO_ZERODIV_THM = save_thm(
  "RAT_NO_ZERODIV_THM[simp]",
  ONCE_REWRITE_RULE [EQ_SYM_EQ] RAT_NO_ZERODIV);

val RAT_NO_ZERODIV_NEG = store_thm("RAT_NO_ZERODIV_NEG",``!r1 r2. ~(r1 * r2 = 0q) = ~(r1 = 0q) /\ ~(r2 = 0q)``,
        PROVE_TAC[RAT_NO_ZERODIV]);

(*--------------------------------------------------------------------------
   RAT_NO_IDDIV

   |- !r1 r2. (r1 * r2 = r2) = (r1=1q) \/ (r2=0q)
 *--------------------------------------------------------------------------*)

val RAT_NO_IDDIV = store_thm("RAT_NO_IDDIV", ``!r1 r2. (rat_mul r1 r2 = r2) = (r1=1q) \/ (r2=0q)``,
        REPEAT GEN_TAC THEN
        ASM_CASES_TAC ``r2 = 0q`` THEN
        RW_TAC bool_ss [RAT_MUL_LID, RAT_MUL_RID, RAT_MUL_LZERO, RAT_MUL_RZERO] THEN
        SUBST_TAC[GSYM (SPEC ``r2:rat`` RAT_MUL_LID)] THEN
        SUBST1_TAC (EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) ``rat_mul r1 (rat_mul 1q r2) = rat_mul (rat_mul r1 1q) r2``)) THEN
        REWRITE_TAC[RAT_MUL_RID] THEN
        SUBST_TAC [UNDISCH (SPECL[``r1:rat``,``1q``,``r2:rat``] RAT_EQ_RMUL)] THEN
        PROVE_TAC[] );

(* moving divisions out *)

val RDIV_MUL_OUT = Q.store_thm(
  "RDIV_MUL_OUT",
  ‘r1 * (r2 / r3) = (r1 * r2) / r3’,
  metis_tac[RAT_MUL_ASSOC, RAT_DIV_MULMINV]);

val LDIV_MUL_OUT = Q.store_thm(
  "LDIV_MUL_OUT",
  ‘(r1 / r2) * r3 = (r1 * r3) / r2’,
  metis_tac[RAT_MUL_ASSOC, RAT_DIV_MULMINV, RAT_MUL_COMM]);

(*--------------------------------------------------------------------------
   RAT_DENSE_THM

   |- !r1 r3. r1 < r3 ==> ?r2. r1 < r2 /\ r2 < r3
 *--------------------------------------------------------------------------*)

val RAT_DENSE_THM =
let
        val lemmaZ = prove(``! a b. 0i<b ==> ((a*b > 0i) = (a > 0i))``,
                REPEAT GEN_TAC THEN
                STRIP_TAC THEN
                EQ_TAC THEN
                SUBST_TAC[SPEC ``b:int`` (GSYM INT_MUL_LZERO)] THEN
                REWRITE_TAC[UNDISCH_ALL (SPEC ``b:int`` (SPEC ``0i`` (SPEC ``a:int`` (GSYM INT_GT_RMUL_EXP))))] THEN
                REWRITE_TAC[INT_MUL_LZERO] );
        val subst1 =
                EQT_ELIM (INT_RING_CONV ``(frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3) + frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1)) * frac_dnm (rep_rat r1) + ~frac_nmr (rep_rat r1) * (2 * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3)) = frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r1) + ~frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3) * frac_dnm (rep_rat r1)``);
        val subst2 =
                EQT_ELIM (INT_RING_CONV ``frac_nmr (rep_rat r3) * (2 * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3)) + ~(frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3) + frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1)) * frac_dnm (rep_rat r3) = frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3) + ~frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3) * frac_dnm (rep_rat r3)``);
in
        store_thm("RAT_DENSE_THM", ``!r1 r3. rat_les r1 r3 ==> ?r2. rat_les r1 r2 /\ rat_les r2 r3``,
                REPEAT GEN_TAC THEN
                STRIP_TAC THEN
                EXISTS_TAC ``abs_rat(abs_frac(rat_nmr r1 * rat_dnm r3 + rat_nmr r3 * rat_dnm r1, 2 * rat_dnm r1 * rat_dnm r3))`` THEN
                UNDISCH_TAC ``rat_les r1 r3`` THEN
                REWRITE_TAC[rat_les_def,rat_sgn_def, rat_sub_def] THEN
                REWRITE_TAC[rat_nmr_def, rat_dnm_def] THEN
                REWRITE_TAC[RAT_SUB_CONG] THEN
                REWRITE_TAC[FRAC_SGN_POS] THEN
                REWRITE_TAC[GSYM int_gt] THEN
                REWRITE_TAC[RAT_NMRGT0_CONG] THEN
                REWRITE_TAC[frac_sub_def,frac_ainv_def,frac_add_def] THEN
                FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
                FRAC_POS_TAC ``frac_dnm (rep_rat r3)`` THEN
                FRAC_POS_TAC ``frac_dnm (rep_rat r3) * frac_dnm (rep_rat r1)`` THEN
                FRAC_POS_TAC ``2 * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3)`` THEN
                FRAC_POS_TAC ``2 * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3) * frac_dnm (rep_rat r1)`` THEN
                FRAC_POS_TAC ``frac_dnm (rep_rat r3) * (2 * frac_dnm (rep_rat r1) * frac_dnm (rep_rat r3))`` THEN
                RW_TAC int_ss[NMR,DNM] THENL
                [
                        SUBST_TAC[subst1] THEN
                        REWRITE_TAC[GSYM INT_RDISTRIB] THEN
                        REWRITE_TAC[UNDISCH_ALL (SPEC ``frac_dnm (rep_rat r1)`` (SPEC ``(frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1) + ~frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3))`` lemmaZ))] THEN
                        PROVE_TAC[]
                ,
                        SUBST_TAC[subst2] THEN
                        REWRITE_TAC[GSYM INT_RDISTRIB] THEN
                        REWRITE_TAC[UNDISCH_ALL (SPEC ``frac_dnm (rep_rat r3)`` (SPEC ``(frac_nmr (rep_rat r3) * frac_dnm (rep_rat r1) + ~frac_nmr (rep_rat r1) * frac_dnm (rep_rat r3))`` lemmaZ))] THEN
                        PROVE_TAC[]
                ] )
end;


(*==========================================================================
 * calculation via frac_save terms
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_SAVE: thm
   |- !r1. ?a1 b1. r1 = abs_rat(frac_save a1 b1)
 *--------------------------------------------------------------------------*)

val RAT_SAVE = store_thm("RAT_SAVE", ``!r1. ?a1 b1. r1 = abs_rat(frac_save a1 b1)``,
        REPEAT GEN_TAC THEN
        SUBST_TAC[GSYM (SPEC ``r1:rat`` RAT)] THEN
        SUBST_TAC[GSYM (SPEC ``rep_rat r1`` FRAC)] THEN
        EXISTS_TAC ``rat_nmr r1`` THEN
        EXISTS_TAC ``Num (rat_dnm r1 -1i)`` THEN
        REWRITE_TAC[frac_save_def, rat_nmr_def, rat_dnm_def, RAT_ABS_EQUIV, rat_equiv_def] THEN
        FRAC_POS_TAC ``frac_dnm (rep_rat r1)`` THEN
        ASSUME_TAC (ARITH_PROVE ``0 < & (Num (frac_dnm (rep_rat r1) - 1i)) + 1i``) THEN
        FRAC_NMRDNM_TAC THEN
        `0 <= frac_dnm (rep_rat r1) - 1i` by ARITH_TAC THEN
        `& (Num (frac_dnm (rep_rat r1) - 1i)) = frac_dnm (rep_rat r1) - 1i` by PROVE_TAC[INT_OF_NUM] THEN
        ARITH_TAC );

(*--------------------------------------------------------------------------
   RAT_SAVE_MINV: thm
   |- !a1 b1. ~(abs_rat (frac_save a1 b1) = 0q) ==>
        (rat_minv (abs_rat (frac_save a1 b1)) =
         abs_rat( frac_save (SGN a1 * (& b1 + 1)) (Num (ABS a1 - 1))) )
 *--------------------------------------------------------------------------*)

val RAT_SAVE_MINV = store_thm("RAT_SAVE_MINV", ``!a1 b1. ~(abs_rat (frac_save a1 b1) = 0q) ==> (rat_minv (abs_rat (frac_save a1 b1)) = abs_rat( frac_save (SGN a1 * (& b1 + 1i)) (Num (ABS a1 - 1i))) )``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[RAT_EQ0_NMR, rat_nmr_def, RAT_NMREQ0_CONG] THEN
        STRIP_TAC THEN
        `~(0i = frac_nmr (frac_save a1 b1))` by PROVE_TAC[] THEN
        REWRITE_TAC[UNDISCH (SPEC ``frac_save a1 b1`` RAT_MINV_CALCULATE)] THEN
        `~(a1 = 0i)` by PROVE_TAC[FRAC_NMR_SAVE] THEN
        RW_TAC int_ss [FRAC_MINV_SAVE] );

(*--------------------------------------------------------------------------
   RAT_SAVE_TO_CONS: thm
   |- !a1 b1. abs_rat (frac_save a1 b1) = rat_cons a1 (& b1 + 1)
 *--------------------------------------------------------------------------*)

val RAT_SAVE_TO_CONS = store_thm("RAT_SAVE_TO_CONS", ``!a1 b1. abs_rat (frac_save a1 b1) = rat_cons a1 (& b1 + 1)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC[rat_cons_def, frac_save_def, RAT_ABS_EQUIV, rat_equiv_def] THEN
        ASSUME_TAC (ARITH_PROVE ``0i < & b1 + 1i``) THEN
        ASSUME_TAC (ARITH_PROVE ``~(& b1 + 1i < 0i)``) THEN
        ASM_REWRITE_TAC[INT_ABS] THEN
        FRAC_NMRDNM_TAC THEN
        RW_TAC int_ss [SGN_def] );

(*==========================================================================
 * calculation of numeral forms
 *==========================================================================*)

(*--------------------------------------------------------------------------
   RAT_OF_NUM: thm
   |- !n. (0 = rat_0) /\ (!n. & (SUC n) = &n + rat_1)
 *--------------------------------------------------------------------------*)

val RAT_OF_NUM = store_thm("RAT_OF_NUM", ``!n. (0 = rat_0) /\ (!n. & (SUC n) = &n + rat_1)``,
        REWRITE_TAC[rat_of_num_def] THEN
        Induct_on `n` THEN
        REWRITE_TAC[RAT_ADD_LID, rat_of_num_def] );

(*--------------------------------------------------------------------------
   RAT_SAVE: thm
   |- !n. &n = abs_rat(frac_save (&n) 0)
 *--------------------------------------------------------------------------*)

val RAT_SAVE_NUM = store_thm("RAT_SAVE_NUM", ``!n. &n = abs_rat(frac_save (&n) 0)``,
        Induct_on `n` THEN
        RW_TAC int_ss [frac_save_def, RAT_OF_NUM] THEN1
        PROVE_TAC[rat_0_def, frac_0_def] THEN
        RAT_CALC_TAC THEN
        FRAC_CALC_TAC THEN
        REWRITE_TAC[RAT_EQ] THEN
        FRAC_NMRDNM_TAC THEN
        ARITH_TAC );

(*--------------------------------------------------------------------------
   RAT_CONS_TO_NUM: thm
   |- !n. (&n // 1 = &n) /\ ((~&n) // 1 = ~&n)
 *--------------------------------------------------------------------------*)

val RAT_CONS_TO_NUM = store_thm("RAT_CONS_TO_NUM", ``!n. (&n // 1 = &n) /\ ((~&n) // 1 = ~&n)``,
        Induct_on `n` THEN1
        RW_TAC int_ss [rat_cons_def, RAT_AINV_0, rat_0, frac_0_def] THEN
        APPLY_ASM_TAC 0 (ONCE_REWRITE_TAC[EQ_SYM_EQ]) THEN
        ASM_REWRITE_TAC[rat_cons_def, RAT_OF_NUM, RAT_AINV_ADD] THEN
        RAT_CALC_TAC THEN
        `0 < ABS 1` by ARITH_TAC THEN
        FRAC_CALC_TAC THEN
        REWRITE_TAC[RAT_EQ] THEN
        FRAC_NMRDNM_TAC THEN
        RW_TAC int_ss [SGN_def] THEN
        ARITH_TAC );

(*--------------------------------------------------------------------------
   RAT_0: thm
   |- rat_0 = 0

   RAT_1: thm
   |- rat_1 = 1
 *--------------------------------------------------------------------------*)

val RAT_0 = store_thm("RAT_0", ``rat_0 = 0q``,
        REWRITE_TAC[rat_of_num_def] );

val RAT_1 = store_thm("RAT_1", ``rat_1 = 1q``,
        `1 = SUC 0` by ARITH_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[rat_of_num_def, RAT_ADD_LID] );

val RAT_OF_NUM_LEQ_0 = prove(``!n. 0 <= &n``,
        Induct_on `n` THEN1
        PROVE_TAC[RAT_LEQ_REF] THEN
        REWRITE_TAC[RAT_OF_NUM] THEN
        ASSUME_TAC RAT_LES_01 THEN
        ASSUME_TAC (SPECL [``1:rat``, ``&n:rat``] RAT_0LES_0LEQ_ADD) THEN
        REWRITE_TAC[RAT_1, RAT_0] THEN
        REWRITE_TAC[rat_leq_def] THEN
        PROVE_TAC[RAT_ADD_COMM] );

(*--------------------------------------------------------------------------
 *  RAT_MINV_1: thm
 *  |- rat_minv 1 = 1
 *--------------------------------------------------------------------------*)

val RAT_MINV_1 = Q.store_thm ("RAT_MINV_1[simp]", `rat_minv 1 = 1`,
  REWRITE_TAC [SYM RAT_1, rat_1_def] THEN
  SIMP_TAC intLib.int_ss [RAT_MINV_CALCULATE, NMR, frac_1_def,
    REWRITE_RULE [frac_1_def] FRAC_MINV_1]) ;

val RAT_DIV_1 = Q.store_thm(
  "RAT_DIV_1[simp]",
  ‘r / 1q = r’,
  simp[RAT_DIV_MULMINV]);

val RAT_DIV_NEG1 = Q.store_thm(
  "RAT_DIV_NEG1[simp]",
  ‘r / -1q = -r’,
  simp[RAT_DIV_MULMINV, GSYM RAT_AINV_MINV, RAT_1_NOT_0, GSYM RAT_AINV_RMUL]);

val RAT_DIV_INV = Q.store_thm(
  "RAT_DIV_INV[simp]",
  ‘r <> 0 ==> (r / r = 1)’,
  simp[RAT_DIV_MULMINV, RAT_MUL_RINV]);

val RAT_MINV_MUL = Q.store_thm(
  "RAT_MINV_MUL",
  ‘a <> 0 /\ b <> 0 ==> (rat_minv (a * b) = rat_minv a * rat_minv b)’,
  strip_tac >>
  qspecl_then [‘rat_minv (a * b)’, ‘rat_minv a * rat_minv b’, ‘a’] mp_tac
              RAT_EQ_LMUL >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
  simp[RAT_MUL_ASSOC, RAT_MUL_RINV] >>
  qspecl_then [‘a * rat_minv (a * b)’, ‘rat_minv b’, ‘b’] mp_tac
              RAT_EQ_LMUL >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
  simp[RAT_MUL_RINV, RAT_MUL_ASSOC] >>
  ‘b * a * rat_minv (a * b) = a * b * rat_minv (a * b)’
    by simp[AC RAT_MUL_ASSOC RAT_MUL_COMM] >>
  pop_assum SUBST_ALL_TAC >>
  ‘a * b <> 0’ by simp[RAT_NO_ZERODIV_NEG] >>
  simp[RAT_MUL_RINV]);

val RAT_DIVDIV_MUL = Q.store_thm(
  "RAT_DIVDIV_MUL",
  ‘b <> 0 /\ d <> 0 ==> ((a / b) * (c / d) = (a * c) / (b * d))’,
  simp[RAT_DIV_MULMINV, RAT_MINV_MUL, AC RAT_MUL_COMM RAT_MUL_ASSOC])

val RAT_DIVDIV_ADD = Q.store_thm(
  "RAT_DIVDIV_ADD",
  ‘y <> 0 /\ b <> 0 ==> (x / y + a / b = (x * b + a * y) / (y * b))’,
  strip_tac >> qmatch_abbrev_tac ‘LHS = RHS’ >>
  ‘LHS = LHS * (y/y) * (b/b)’ by simp[] >>
  pop_assum SUBST1_TAC >> simp_tac bool_ss [Abbr`LHS`, RAT_RDISTRIB] >>
  ‘x / y * (y / y) = x / y’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘x / y * (b / b) = (x * b) / (y * b)’ by simp[RAT_DIVDIV_MUL] >>
  pop_assum SUBST1_TAC >> ‘b / b = 1’ by simp[] >>
  asm_simp_tac bool_ss [RAT_MUL_RID] >> simp[RAT_DIVDIV_MUL] >>
  simp[Abbr`RHS`, RAT_RDISTRIB, RAT_DIV_MULMINV, AC RAT_MUL_ASSOC RAT_MUL_COMM])

val RAT_DIV_AINV = Q.store_thm(
  "RAT_DIV_AINV",
  ‘-(x/y) = (-x)/y’,
  simp[RAT_DIV_MULMINV, RAT_AINV_LMUL]);

val RAT_MINV_EQ_0 = Q.store_thm(
  "RAT_MINV_EQ_0[simp]",
  ‘r <> 0 ==> rat_minv r <> 0’,
  strip_tac >> disch_then (mp_tac o Q.AP_TERM ‘$* r’) >>
  simp[RAT_MUL_RINV, RAT_1_NOT_0]);

val RAT_DIV_MINV = Q.store_thm(
  "RAT_DIV_MINV",
  ‘x <> 0 /\ y <> 0 ==> (rat_minv (x/y) = y / x)’,
  strip_tac >>
  ‘x / y <> 0’ by simp[RAT_DIV_MULMINV, RAT_NO_ZERODIV_NEG] >>
  qspecl_then [‘rat_minv (x / y)’, ‘y / x’, ‘x / y’] mp_tac
              RAT_EQ_LMUL >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
  simp[RAT_MUL_RINV, RAT_DIVDIV_MUL] >>
  simp[RAT_MUL_COMM, RAT_NO_ZERODIV_NEG]);

val RAT_DIV_EQ0 = Q.store_thm(
  "RAT_DIV_EQ0[simp]",
  ‘d <> 0 ==> ((n / d = 0) <=> (n = 0)) /\ ((0 = n / d) <=> (n = 0))’,
  strip_tac >> simp[RAT_DIV_MULMINV, GSYM RAT_NO_ZERODIV, RAT_MINV_EQ_0]);

(*--------------------------------------------------------------------------
   RAT_ADD_NUM: thm

   |- !n m. ( &n +  &m = &(n+m))
   |- !n m. (~&n + &m = if n<=m then &(m-n) else ~&(n-m))
   |- !n m.  &n + ~&m = if m<=n then &(n-m) else ~&(m-n)
   |- !n m. ~&n + ~&m = ~&(n+m)
 *--------------------------------------------------------------------------*)

val RAT_ADD_NUM1 = prove(``!n m. ( &n +  &m = &(n+m))``,
        Induct_on `m` THEN
        Induct_on `n` THEN
        RW_TAC int_ss [RAT_ADD_LID, RAT_ADD_RID] THEN
        LEFT_NO_FORALL_TAC 1 ``SUC (SUC n)`` THEN
        UNDISCH_HD_TAC THEN
        REWRITE_TAC[RAT_OF_NUM] THEN
        `SUC (SUC n) + m = SUC m + SUC n` by ARITH_TAC THEN
        PROVE_TAC[RAT_ADD_ASSOC, RAT_ADD_COMM] );

val RAT_ADD_NUM2 = prove(``!n m. (~&n + &m = if n<=m then &(m-n) else ~&(n-m))``,
        Induct_on `n` THEN
        Induct_on `m` THEN
        SIMP_TAC int_ss [RAT_AINV_0, RAT_ADD_LID, RAT_ADD_RID] THEN
        LEFT_NO_FORALL_TAC 1 ``m:num`` THEN
        APPLY_ASM_TAC 0 (ONCE_REWRITE_TAC[EQ_SYM_EQ]) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[RAT_OF_NUM] THEN
        REWRITE_TAC[RAT_AINV_ADD] THEN
        SUBST1_TAC (EQT_ELIM (AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) ``~& n + ~rat_1 + (& m + rat_1) = ~& n + & m + (rat_1 + ~rat_1)``)) THEN
        REWRITE_TAC[RAT_ADD_RINV, RAT_ADD_RID] );

val RAT_ADD_NUM3 = prove(``!n m.  &n + ~&m = if m<=n then &(n-m) else ~&(m-n)``,
        PROVE_TAC[RAT_ADD_NUM2, RAT_ADD_COMM] );

val RAT_ADD_NUM4 = prove(``!n m. ~&n + ~&m = ~&(n+m)``,
        PROVE_TAC[RAT_ADD_NUM1, RAT_EQ_AINV, RAT_AINV_ADD] );

val RAT_ADD_NUM_CALCULATE = save_thm("RAT_ADD_NUM_CALCULATE", LIST_CONJ[RAT_ADD_NUM1, RAT_ADD_NUM2, RAT_ADD_NUM3, RAT_ADD_NUM4] );

(*--------------------------------------------------------------------------
   RAT_ADD_MUL: thm

   |- !n m. &n *  &m =  &(n*m)
   |- !n m. ~&n *  &m = ~&(n*m)
   |- !n m.  &n * ~&m = ~&(n*m)
   |- !n m. ~&n * ~&m =  &(n*m)
 *--------------------------------------------------------------------------*)

val RAT_MUL_NUM1 = prove(``!n m. &n *  &m =  &(n*m)``,
        Induct_on `m` THEN
        Induct_on `n` THEN
        RW_TAC int_ss [RAT_MUL_LZERO, RAT_MUL_RZERO] THEN
        `!x. SUC x = x + 1` by ARITH_TAC THEN
        `(n+1) * (m+1) = n * m + n + m + 1:num` by ARITH_TAC THEN
        ASM_REWRITE_TAC[GSYM RAT_ADD_NUM1, RAT_LDISTRIB, RAT_RDISTRIB, RAT_ADD_ASSOC, RAT_MUL_ASSOC, RAT_MUL_LID, RAT_MUL_RID, MULT_CLAUSES] THEN
        METIS_TAC[RAT_ADD_ASSOC, RAT_ADD_COMM, MULT_COMM] );

val RAT_MUL_NUM2 = prove(``!n m. ~&n *  &m = ~&(n*m)``,
        PROVE_TAC[GSYM RAT_AINV_LMUL, RAT_EQ_AINV, RAT_MUL_NUM1] );

val RAT_MUL_NUM3 = prove(``!n m.  &n * ~&m = ~&(n*m)``,
        PROVE_TAC[GSYM RAT_AINV_RMUL, RAT_EQ_AINV, RAT_MUL_NUM1] );

val RAT_MUL_NUM4 = prove(``!n m. ~&n * ~&m =  &(n*m)``,
        PROVE_TAC[GSYM RAT_AINV_RMUL, GSYM RAT_AINV_LMUL, RAT_AINV_AINV, RAT_MUL_NUM1] );

val RAT_MUL_NUM_CALCULATE = save_thm("RAT_MUL_NUM_CALCULATE", LIST_CONJ[RAT_MUL_NUM1, RAT_MUL_NUM2, RAT_MUL_NUM3, RAT_MUL_NUM4] );

(*--------------------------------------------------------------------------
   RAT_EQ_NUM: thm

   |- !n m. ( &n =  &m) = (n=m)
   |- !n m. ( &n = ~&m) = (n=0) /\ (m=0)
   |- !n m. (~&n =  &m) = (n=0) /\ (m=0)
   |- !n m. (~&n = ~&m) = (n=m)
 *--------------------------------------------------------------------------*)

val RAT_EQ_NUM1 = prove(``!n m. ( &n =  &m) = (n=m)``,
        Induct_on `n` THEN
        Induct_on `m` THEN
        RW_TAC arith_ss [RAT_OF_NUM] THENL
        [
                MATCH_MP_TAC (prove(``!r1 r2. (r1 < r2) ==> ~(r1 = r2)``, PROVE_TAC[RAT_LES_ANTISYM])) THEN
                ASSUME_TAC (ONCE_REWRITE_RULE[RAT_ADD_COMM, GSYM RAT_0] (SPECL[``rat_1``,``&m:rat``] RAT_0LES_0LEQ_ADD)) THEN
                ASSUME_TAC (SPEC ``m:num`` RAT_OF_NUM_LEQ_0) THEN
                PROVE_TAC[RAT_LES_01, RAT_1, RAT_0]
        ,
                ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
                MATCH_MP_TAC (prove(``!r1 r2. (r1 < r2) ==> ~(r1 = r2)``, PROVE_TAC[RAT_LES_ANTISYM])) THEN
                ASSUME_TAC (ONCE_REWRITE_RULE[RAT_ADD_COMM, GSYM RAT_0] (SPECL[``rat_1``,``&n:rat``] RAT_0LES_0LEQ_ADD)) THEN
                ASSUME_TAC (SPEC ``n:num`` RAT_OF_NUM_LEQ_0) THEN
                PROVE_TAC[RAT_LES_01, RAT_1, RAT_0]
        ,
                LEFT_NO_FORALL_TAC 1 ``m:num`` THEN
                REWRITE_TAC[RAT_EQ_RADD] THEN
                PROVE_TAC[]
        ] );

val RAT_EQ_NUM2 = prove(``!n m. ( &n = ~&m) = (n=0) /\ (m=0)``,
        Induct_on `n` THEN
        Induct_on `m` THEN
        RW_TAC arith_ss [RAT_OF_NUM] THENL
        [
                PROVE_TAC[RAT_AINV_0, RAT_0]
        ,
                ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
                MATCH_MP_TAC (prove(``!r1 r2. (r1 < r2) ==> ~(r1 = r2)``, PROVE_TAC[RAT_LES_ANTISYM])) THEN
                REWRITE_TAC[RAT_0] THEN
                ONCE_REWRITE_TAC[GSYM RAT_AINV_0] THEN
                REWRITE_TAC[RAT_LES_AINV] THEN
                ASSUME_TAC (ONCE_REWRITE_RULE[RAT_ADD_COMM, GSYM RAT_0] (SPECL[``rat_1``,``&m:rat``] RAT_0LES_0LEQ_ADD)) THEN
                ASSUME_TAC (SPEC ``m:num`` RAT_OF_NUM_LEQ_0) THEN
                PROVE_TAC[RAT_LES_01, RAT_1, RAT_0]
        ,
                ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
                MATCH_MP_TAC (prove(``!r1 r2. (r1 < r2) ==> ~(r1 = r2)``, PROVE_TAC[RAT_LES_ANTISYM])) THEN
                REWRITE_TAC[RAT_0] THEN
                REWRITE_TAC[RAT_AINV_0] THEN
                ASSUME_TAC (ONCE_REWRITE_RULE[RAT_ADD_COMM, GSYM RAT_0] (SPECL[``rat_1``,``&n:rat``] RAT_0LES_0LEQ_ADD)) THEN
                ASSUME_TAC (SPEC ``n:num`` RAT_OF_NUM_LEQ_0) THEN
                PROVE_TAC[RAT_LES_01, RAT_1, RAT_0]
        ,
                REWRITE_TAC[GSYM RAT_RSUB_EQ] THEN
                REWRITE_TAC[RAT_SUB_ADDAINV, GSYM RAT_AINV_ADD] THEN
                LEFT_NO_FORALL_TAC 1 ``SUC (SUC m):num`` THEN
                UNDISCH_HD_TAC THEN
                SIMP_TAC arith_ss [RAT_OF_NUM]
        ] );

val RAT_EQ_NUM3 = prove(``!n m. (~&n =  &m) = (n=0)/\(m=0)``,
        PROVE_TAC[RAT_EQ_AINV, RAT_EQ_NUM2] );

val RAT_EQ_NUM4 = prove(``!n m. (~&n = ~&m) = (n=m)``,
        PROVE_TAC[RAT_AINV_EQ, RAT_EQ_NUM1] );

val RAT_EQ_NUM_CALCULATE = save_thm("RAT_EQ_NUM_CALCULATE[simp]",
  LIST_CONJ [RAT_EQ_NUM1, RAT_EQ_NUM2, RAT_EQ_NUM3, RAT_EQ_NUM4] );

(* ----------------------------------------------------------------------
    RAT_LT_NUM
   ---------------------------------------------------------------------- *)

val RAT_LT_NUM1 = RAT_OF_NUM_LES

val RAT_LT_NUM2 = Q.prove(
  ‘-&m < &n <=> 0 < m \/ 0 < n’,
  eq_tac >- (spose_not_then strip_assume_tac >> fs[]) >>
  strip_tac
  >- (irule RAT_LES_LEQ_TRANS >> qexists_tac `0` >> simp[] >>
      simp[Once RAT_AINV_LES]) >>
  irule RAT_LEQ_LES_TRANS >> qexists_tac `0` >> simp[] >>
  simp[rat_leq_def] >>
  simp[Once RAT_AINV_LES]);

val RAT_LT_NUM3 = Q.prove(
  ‘&m < -&n <=> F’,
  simp[] >> strip_tac >>
  ‘-&n <= 0’ by simp[rat_leq_def, Once RAT_AINV_LES] >>
  ‘&m < 0’ by metis_tac[RAT_LES_LEQ_TRANS] >> fs[])

val RAT_LT_NUM4 = Q.prove(
  ‘-&m < -&n <=> n < m’,
  simp[RAT_LES_AINV]);

val RAT_LT_NUM_CALCULATE = save_thm(
  "RAT_LT_NUM_CALCULATE[simp]",
  LIST_CONJ [RAT_LT_NUM1, RAT_LT_NUM2, RAT_LT_NUM3, RAT_LT_NUM4]);

(* ----------------------------------------------------------------------
    RAT_LE_NUM
   ---------------------------------------------------------------------- *)

val RAT_LE_NUM2 = Q.prove(
  ‘-&m <= &n <=> T’,
  simp[rat_leq_def]);

val RAT_LE_NUM3 = Q.prove(
  ‘&m <= -&n <=> (m = 0) /\ (n = 0)’,
  simp[rat_leq_def]);

val RAT_LE_NUM4 = Q.prove(
  ‘-&m <= -&n <=> n <= m’,
  simp[rat_leq_def]);

val RAT_LE_NUM_CALCULATE = save_thm(
  "RAT_LE_NUM_CALCULATE[simp]",
  LIST_CONJ [RAT_OF_NUM_LEQ, RAT_LE_NUM2, RAT_LE_NUM3, RAT_LE_NUM4]);

(* ----------------------------------------------------------------------
    rat_of_int
   ---------------------------------------------------------------------- *)

val rat_of_int_def = Define ‘
  rat_of_int i : rat = if i < 0 then - (& (Num (-i))) else &(Num i)
’;

val rat_of_int_11 = Q.store_thm(
  "rat_of_int_11[simp]",
  ‘(rat_of_int i1 = rat_of_int i2) <=> (i1 = i2)’,
  simp[EQ_IMP_THM] >> simp[rat_of_int_def] >> Cases_on ‘i1 < 0’ >>
  Cases_on ‘i2 < 0’ >> simp[]
  >- (‘0 <= -i1 /\ 0 <= -i2’ by simp[] >>
      rpt (pop_assum
             (mp_tac o CONV_RULE (REWR_CONV (GSYM integerTheory.INT_OF_NUM))))>>
      ntac 2 strip_tac >> disch_then (mp_tac o AP_TERM ``$& : num -> int``) >>
      ntac 2 (pop_assum SUBST1_TAC) >> simp[integerTheory.INT_EQ_CALCULATE])
  >- (rename [‘a < 0’, ‘~(b < 0)’] >>
      ‘0 <= -a /\ 0 <= b’ by (simp[] >> fs[integerTheory.INT_NOT_LT]) >>
      rpt (pop_assum
             (mp_tac o CONV_RULE (REWR_CONV (GSYM integerTheory.INT_OF_NUM))))>>
      ntac 2 strip_tac >>
      disch_then (CONJUNCTS_THEN (mp_tac o AP_TERM ``$& : num -> int``)) >>
      ntac 2 (pop_assum SUBST1_TAC) >> simp[integerTheory.INT_EQ_CALCULATE])
  >- (rename [‘a < 0’, ‘~(b < 0)’] >>
      ‘0 <= -a /\ 0 <= b’ by (simp[] >> fs[integerTheory.INT_NOT_LT]) >>
      rpt (pop_assum
             (mp_tac o CONV_RULE (REWR_CONV (GSYM integerTheory.INT_OF_NUM))))>>
      ntac 2 strip_tac >>
      disch_then (CONJUNCTS_THEN (mp_tac o AP_TERM ``$& : num -> int``)) >>
      ntac 2 (pop_assum SUBST1_TAC) >> simp[integerTheory.INT_EQ_CALCULATE])
  >- (‘0 <= i1 /\ 0 <= i2’ by fs[integerTheory.INT_NOT_LT] >>
      rpt (pop_assum
             (mp_tac o CONV_RULE (REWR_CONV (GSYM integerTheory.INT_OF_NUM))))>>
      ntac 2 strip_tac >> disch_then (mp_tac o AP_TERM ``$& : num -> int``) >>
      ntac 2 (pop_assum SUBST1_TAC) >> simp[integerTheory.INT_EQ_CALCULATE]));

val rat_of_int_of_num = Q.store_thm(
  "rat_of_int_of_num[simp]",
  ‘rat_of_int (&x) = &x’,
  simp[rat_of_int_def]);

val elim1 = intLib.ARITH_PROVE ``y <= x /\ x <= y ==> (x = y:int)``
val elim2 = intLib.ARITH_PROVE ``x:int < y /\ y < x ==> F``
fun elim_tac k =
    REPEAT_GTCL
      (fn ttcl => fn th =>
          first_assum (mp_then.mp_then (mp_then.Pos hd) ttcl th))
      (k o assert (not o is_imp o #2 o strip_forall o concl))

val num_rwt = integerTheory.INT_OF_NUM |> SPEC_ALL |> EQ_IMP_RULE |> #2

val rat_of_int_MUL = Q.store_thm(
  "rat_of_int_MUL",
  ‘rat_of_int x * rat_of_int y = rat_of_int (x * y)’,
  simp[rat_of_int_def, integerTheory.INT_MUL_SIGN_CASES] >> rw[] >>
  fs[integerTheory.INT_NOT_LT, RAT_MUL_NUM_CALCULATE, RAT_EQ_NUM_CALCULATE] >>
  TRY (elim_tac assume_tac elim1 ORELSE elim_tac assume_tac elim2) >> rw[] >>
  asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
    [GSYM integerTheory.INT_INJ, GSYM integerRingTheory.int_calculate,
     num_rwt, integerTheory.INT_LE_MUL, integerTheory.INT_LE_LT,
     integerTheory.INT_MUL_SIGN_CASES, integerTheory.INT_NEG_GT0]);

val rat_of_int_ADD = Q.store_thm(
  "rat_of_int_ADD",
  ‘rat_of_int x + rat_of_int y = rat_of_int (x + y)’,
  simp[rat_of_int_def] >> rw[]
  >- (simp[GSYM RAT_AINV_ADD, RAT_ADD_NUM_CALCULATE] >>
      asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
       [GSYM integerTheory.INT_INJ, GSYM integerRingTheory.int_calculate,
        num_rwt, integerTheory.INT_LE_MUL, integerTheory.INT_LE_LT,
        integerTheory.INT_MUL_SIGN_CASES, integerTheory.INT_NEG_GT0])
  >- (full_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [])
  >- (simp[RAT_ADD_NUM_CALCULATE] >> rw[] >>
      TRY (rename [‘Num (-a) <= Num b’] >>
           pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
           asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt]) >>
      rename [‘Num (-a) - Num b’] >>
      ‘Num b <= Num (-a)’
         by asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
            [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_LE] >>
       asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
            [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_SUB])
  >- (simp[RAT_ADD_NUM_CALCULATE] >> rw[]
      >- (rename [‘Num (-a) <= Num b’] >>
          pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
          asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt] >>
          `Num (-a) <= Num b`
             by asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
                    [num_rwt, GSYM integerTheory.INT_INJ,
                     GSYM integerTheory.INT_LE] >>
         asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
             [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_SUB])
      >- (pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
          asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt]))
  >- (simp[RAT_ADD_NUM_CALCULATE] >> rw[] >>
      TRY (rename [‘Num (-a) <= Num b’] >>
           pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
           asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt]) >>
      rename [‘Num (-a) - Num b’] >>
      ‘Num b <= Num (-a)’
         by asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
            [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_LE] >>
       asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
            [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_SUB])
  >- (simp[RAT_ADD_NUM_CALCULATE] >> rw[]
      >- (rename [‘Num (-a) <= Num b’] >>
          pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
          asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt] >>
          `Num (-a) <= Num b`
             by asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
                    [num_rwt, GSYM integerTheory.INT_INJ,
                     GSYM integerTheory.INT_LE] >>
         asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
             [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_SUB])
      >- (pop_assum (mp_tac o REWRITE_RULE [GSYM integerTheory.INT_LE]) >>
          asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [num_rwt]))
  >- (full_simp_tac (bool_ss ++ intLib.INT_ARITH_ss) [])
  >- (simp[RAT_ADD_NUM_CALCULATE] >>
      asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
         [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_ADD]))

val rat_of_int_LE = Q.store_thm(
  "rat_of_int_LE[simp]",
  ‘rat_of_int i <= rat_of_int j <=> i <= j’,
  simp[rat_of_int_def] >> rw[] >>
  asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
    [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_LE])

val rat_of_int_LT = Q.store_thm(
  "rat_of_int_LT[simp]",
  ‘rat_of_int i < rat_of_int j <=> i < j’,
  simp[rat_of_int_def] >> rw[] >>
  asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
    [num_rwt, GSYM integerTheory.INT_INJ, GSYM integerTheory.INT_LT]);

val rat_of_int_ainv = Q.store_thm(
  "rat_of_int_ainv",
  ‘rat_of_int (-i) = -(rat_of_int i)’,
  simp[rat_of_int_def] >> rw[] >>
  TRY (elim_tac mp_tac elim2 >> simp[]) >>
  asm_simp_tac (bool_ss ++ intLib.INT_ARITH_ss)
    [num_rwt, GSYM integerTheory.INT_INJ])

val RAT_OF_INT_CALCULATE = Q.store_thm(
  "RAT_OF_INT_CALCULATE",
  ‘!i. rat_of_int i = abs_rat (abs_frac (i, 1))’,
  gen_tac >> Cases_on ‘i’ >> simp[rat_of_int_def]
  >- simp[RAT_OF_NUM_CALCULATE]
  >- (simp[GSYM fracTheory.FRAC_AINV_CALCULATE, GSYM RAT_AINV_CALCULATE] >>
      simp[RAT_OF_NUM_CALCULATE])
  >- simp[RAT_OF_NUM_CALCULATE]);

(* ----------------------------------------------------------------------
    RATN and RATD, which take rational numbers and return unique
    numerator and denominator values. Numerator is integer with smallest
    possible absolute value; denominator is a natural number.  If
    numerator is zero, denominator is always one.
   ---------------------------------------------------------------------- *)

val frac_exists = Q.prove(
  ‘!r. ?n:int d:num. 0 < d /\ (&d * r = rat_of_int n)’,
  gen_tac >>
  qabbrev_tac ‘f = rep_rat r’ >>
  ‘r = abs_rat f’ by metis_tac[rat_type_thm] >>
  ‘?n0 d0. rep_frac f = (n0,d0)’ by (Cases_on ‘rep_frac f’ >> simp[]) >>
  map_every qexists_tac [‘n0’, ‘Num d0’] >>
  ‘rep_frac (abs_frac (rep_frac f)) = rep_frac f’
    by simp [fracTheory.frac_tybij] >>
  pop_assum mp_tac >> simp[GSYM (CONJUNCT2 fracTheory.frac_tybij)] >>
  strip_tac >> Cases_on ‘d0’ >> fs[] >>
  rename [‘rep_frac f = (n,&d)’] >>
  simp[RAT_OF_NUM_CALCULATE, RAT_OF_INT_CALCULATE, RAT_MUL_CALCULATE] >>
  ‘f = abs_frac (n,&d)’ by metis_tac[fracTheory.frac_tybij] >>
  simp[fracTheory.FRAC_MULT_CALCULATE, RAT_ABS_EQUIV] >>
  simp[RAT_EQUIV_ALT] >>
  map_every qexists_tac [‘1’, ‘&d’] >>
  simp[fracTheory.FRAC_MULT_CALCULATE, integerTheory.INT_MUL_COMM]);

val numdenom_exists = Q.prove(
  ‘!r:rat.
     ?n:int d:num.
       (r = rat_of_int n / &d) /\ 0 < d /\ ((n = 0) ==> (d = 1)) /\
       !n' d'. (r = rat_of_int n' / &d') /\ 0 < d' ==> ABS n <= ABS n'’,
  gen_tac >>
  qabbrev_tac `reps = { (a,b) | (&b * r = rat_of_int a) /\ 0 < b }` >>
  `WF (measure (Num o ABS o (FST : int # num -> int)))` by simp[] >>
  full_simp_tac bool_ss [relationTheory.WF_DEF] >>
  ‘?e. reps e’
    by (simp[Abbr‘reps’, pairTheory.EXISTS_PROD] >> metis_tac[frac_exists]) >>
  fs[PULL_EXISTS] >>
  Cases_on ‘r = 0’
  >- (map_every qexists_tac [‘0’, ‘1’] >> simp[] >> gen_tac >> Cases_on ‘n'’ >>
      simp[integerTheory.INT_ABS_NUM, integerTheory.INT_ABS_NEG]) >>
  res_tac >>
  ‘?mn md. min = (mn,md)’ by (Cases_on ‘min’ >> simp[]) >> rw[] >>
  map_every qexists_tac [‘mn’, ‘md’] >> fs[Abbr‘reps’] >> pairarg_tac >>
  fs[pairTheory.FORALL_PROD] >> rpt var_eq_tac >>
  qpat_x_assum ‘(_,_) = _’ kall_tac >> rpt conj_tac
  >- (rename [‘&d * r = rat_of_int n’] >> first_x_assum (SUBST1_TAC o SYM) >>
      simp[RAT_DIV_MULMINV] >>
      ‘&d:rat <> 0’ by simp[] >>
      metis_tac[RAT_MUL_ASSOC, RAT_MUL_COMM, RAT_MUL_RINV, RAT_MUL_LID])
  >- (rename [‘(_ = 0) ==> (_ = 1)’] >> strip_tac >> fs[])
  >- (rpt strip_tac >>
      rename [‘&d * r = rat_of_int n’, ‘r = rat_of_int nn / &dd’] >>
      spose_not_then (assume_tac o REWRITE_RULE[integerTheory.INT_NOT_LE]) >>
      first_x_assum (qspecl_then [‘nn’, ‘dd’] mp_tac) >> simp[] >>
      reverse conj_tac
      >- (‘&dd <> 0’ by simp[] >> simp[RAT_DIV_MULMINV] >>
          metis_tac[RAT_MUL_ASSOC, RAT_MUL_COMM, RAT_MUL_RINV, RAT_MUL_LID]) >>
      simp[NUM_LT]))

val RATND_THM = new_specification("RATND_THM", ["RATN", "RATD"],
  CONV_RULE (SKOLEM_CONV THENC BINDER_CONV SKOLEM_CONV) numdenom_exists)

val RATD_NZERO = save_thm(
  "RATD_NZERO[simp]",
  let val th = List.nth(RATND_THM |> SPEC_ALL |> CONJUNCTS, 1)
  in
    CONJ th (CONV_RULE (REWR_CONV (GSYM NOT_ZERO_LT_ZERO)) th)
  end);

val RATN_LEAST = save_thm(
  "RATN_LEAST",
  List.nth(RATND_THM |> SPEC_ALL |> CONJUNCTS, 3))

val RATN_RATD_EQ_THM = save_thm(
  "RATN_RATD_EQ_THM",
  RATND_THM |> SPEC_ALL |> CONJUNCTS |> hd);

val RATN_RATD_MULT = save_thm(
  "RATN_RATD_MULT",
  RATN_RATD_EQ_THM |> Q.AP_TERM ‘\x. x * &RATD r’ |> BETA_RULE
                   |> SIMP_RULE (srw_ss()) [RAT_DIV_MULMINV, GSYM RAT_MUL_ASSOC,
                                            RAT_MUL_LINV]);

val RATND_RAT_OF_NUM = Q.store_thm(
  "RATND_RAT_OF_NUM[simp]",
  ‘(RATN (&n) = &n) /\ (RATD (&n) = 1)’,
  mp_tac (Q.INST [`r` |-> `&n`] RATN_RATD_MULT) >> strip_tac >>
  ‘&n:rat = rat_of_int (&n) / 1’ by simp[] >>
  ‘ABS (RATN (&n)) <= ABS (&n)’ by metis_tac[RATN_LEAST, DECIDE ``0n < 1``] >>
  full_simp_tac bool_ss [integerTheory.INT_ABS_NUM, GSYM rat_of_int_of_num,
                         rat_of_int_MUL, rat_of_int_11,
                         integerTheory.INT_MUL] >>
  fs[] >>
  ‘?rn. RATN (&n) = &rn’ by (Cases_on ‘RATN (&n)’ >> fs[]) >>
  fs[integerTheory.INT_ABS_NUM] >>
  conj_asm1_tac
  >- (‘n <= rn’ suffices_by simp[] >>
      Cases_on ‘RATD(&n)’ >> fs[MULT_CLAUSES]) >> rpt var_eq_tac >>
  ‘(RATD(&n) = 1) \/ (n = 0)’ by metis_tac[MULT_RIGHT_1,EQ_MULT_LCANCEL] >>
  metis_tac[RATND_THM]);

val RATN_EQ0 = Q.store_thm(
  "RATN_EQ0[simp]",
  ‘((RATN r = 0) <=> (r = 0)) /\ ((0 = RATN r) <=> (r = 0))’,
  reverse conj_asm1_tac >- metis_tac[] >>
  simp[EQ_IMP_THM] >> strip_tac >>
  mp_tac RATN_RATD_MULT >> simp[]);

val RATN_SIGN = Q.store_thm(
  "RATN_SIGN[simp]",
  ‘(0 < RATN x <=> 0 < x) /\ (0 <= RATN x <=> 0 <= x) /\ (RATN x < 0 <=> x < 0) /\
   (RATN x <= 0 <=> x <= 0)’,
  reverse conj_asm1_tac
  >- (simp[integerTheory.INT_LE_LT, rat_leq_def, EQ_SYM_EQ] >>
      conj_tac >> ONCE_REWRITE_TAC [DECIDE ``(p:bool = q) = (~p = ~q)``] >>
      ASM_REWRITE_TAC [integerTheory.INT_NOT_LT, integerTheory.INT_LE_LT, RAT_LEQ_LES,
                       rat_leq_def, DE_MORGAN_THM] >> simp[] >> metis_tac[]) >>
  eq_tac >> strip_tac >> mp_tac (Q.INST [`r` |-> `x`] RATN_RATD_MULT)
  >- (‘0 < rat_of_int (RATN x)’
        by asm_simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_LT] >>
      strip_tac >>
      ‘0 < x * &RATD x’ by metis_tac[] >>
      pop_assum mp_tac >> simp[RAT_MUL_SIGN_CASES]) >>
  ‘0 < x * &RATD x’ by simp[RAT_MUL_SIGN_CASES] >> strip_tac >>
  ‘0 < rat_of_int (RATN x)’ by metis_tac[] >>
  full_simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_LT]);

val RATN_MUL_LEAST =
    SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ ARITH_ss) [RAT_RDIV_EQ] RATN_LEAST;

val RAT_AINV_SGN = Q.store_thm(
  "RAT_AINV_SGN[simp]",
  ‘(0 < -r <=> r < 0) /\ (-r < 0 <=> 0 < r)’,
  metis_tac[RAT_LES_AINV, RAT_AINV_0]);

val RATN_NEG = Q.store_thm(
  "RATN_NEG[simp]",
  ‘RATN (-r) = -RATN r’,
  assume_tac RATN_RATD_MULT >> assume_tac (Q.INST [`r` |-> `-r`] RATN_RATD_MULT) >>
  first_assum (mp_tac o Q.AP_TERM `rat_ainv`) >>
  REWRITE_TAC[RAT_AINV_LMUL] >> simp[] >> strip_tac >>
  ‘ABS (RATN r) <= ABS (-RATN (-r))’
    by (irule RATN_MUL_LEAST >> qexists_tac ‘&RATD (-r)’ >> simp[rat_of_int_ainv]) >>
  fs[] >>
  last_assum (mp_tac o Q.AP_TERM `rat_ainv`) >>
  REWRITE_TAC[RAT_AINV_LMUL] >> simp[] >> strip_tac >>
  ‘ABS (RATN (-r)) <= ABS (-RATN (r))’
    by (irule RATN_MUL_LEAST >> qexists_tac ‘&RATD r’ >> simp[rat_of_int_ainv]) >>
  fs[] >>
  ‘ABS (RATN (-r)) = ABS (RATN r)’ by metis_tac[INT_LE_ANTISYM] >>
  fs[INT_ABS_EQ_ABS] >> fs[] >>
  ‘r * &RATD r = -r * &RATD (-r)’ by simp[] >> pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  qspecl_then [‘0’, ‘r’] strip_assume_tac RAT_LES_TOTAL
  >- (‘0 < r * &RATD r’ by simp[RAT_MUL_SIGN_CASES] >>
      ‘~(0 < -r * &RATD (-r))’
        by (simp[RAT_MUL_SIGN_CASES] >> metis_tac[RAT_LES_REF, RAT_LES_TRANS]) >>
      metis_tac[])
  >- simp[]
  >- (‘r * &RATD r < 0’ by simp[RAT_MUL_SIGN_CASES] >>
      ‘~(-r * &RATD(-r) < 0)’
         by (simp[RAT_MUL_SIGN_CASES] >> metis_tac[RAT_LES_REF, RAT_LES_TRANS]) >>
      metis_tac[]));

val RATD_NEG = Q.store_thm(
  "RATD_NEG[simp]",
  ‘RATD (-r) = RATD r’,
  Cases_on ‘r = 0’ >> fs[] >>
  assume_tac RATN_RATD_MULT >> assume_tac (Q.INST [`r` |-> `-r`] RATN_RATD_MULT) >> fs[] >>
  pop_assum (mp_tac o Q.AP_TERM ‘rat_ainv’) >> REWRITE_TAC [RAT_AINV_LMUL] >>
  simp[rat_of_int_ainv] >> metis_tac[RAT_EQ_LMUL, RAT_EQ_NUM_CALCULATE]);

val RATN_RATD_RAT_OF_INT = Q.store_thm(
  "RATN_RATD_RAT_OF_INT[simp]",
  ‘(RATN (rat_of_int i) = i) /\ (RATD (rat_of_int i) = 1)’,
  Cases_on ‘i’ >> simp[rat_of_int_ainv]);

val RATN_DIV_RATD = Q.store_thm(
  "RATN_DIV_RATD[simp]",
  ‘rat_of_int (RATN r) / &RATD r = r’,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >> simp[RAT_RDIV_EQ, RATN_RATD_MULT]);

val RAT_AINV_EQ_NUM = Q.store_thm(
  "RAT_AINV_EQ_NUM[simp]",
  ‘(rat_ainv x = rat_of_num n) <=> (x = rat_of_int (-&n))’,
  simp[EQ_IMP_THM, rat_of_int_ainv] >> disch_then (SUBST1_TAC o SYM) >> simp[]);

(* ----------------------------------------------------------------------
    more theorems about RAT_SGN : rat -> int  (-1,0,1)
   ---------------------------------------------------------------------- *)

val _ = temp_overload_on ("RAT_SGN", ``rat_sgn``)
val RAT_SGN_NUM_COND = Q.store_thm(
  "RAT_SGN_NUM_COND",
  ‘rat_sgn (&n) = if n = 0 then 0 else 1’,
  rw[] >> `0 < n` by simp[] >>
  `0 < &n` by simp[] >>
  pop_assum (mp_tac o REWRITE_RULE [rat_les_def]) >> simp[]);

val RAT_SGN_AINV_RWT = Q.store_thm(
  "RAT_SGN_AINV_RWT[simp]",
  ‘rat_sgn (-r) = -rat_sgn r’,
  simp[SimpLHS, Once (GSYM RAT_SGN_AINV)]);

val RAT_SGN_ALT = Q.store_thm("RAT_SGN_ALT",
  ‘rat_sgn r = SGN (RATN r)’,
  assume_tac RATN_RATD_EQ_THM >>
  map_every qabbrev_tac [`n = RATN r`, `nr = rat_of_int n`, `d = &(RATD r)`] >>
  `d <> 0` by simp[Abbr`d`] >>
  simp[RAT_DIV_MULMINV, RAT_SGN_MUL, RAT_SGN_MINV] >>
  `d > 0` by simp[Abbr`d`, rat_gre_def] >>
  `rat_sgn d = 1` by metis_tac[RAT_SGN_CLAUSES] >> simp[] >>
  simp[Abbr`nr`, rat_of_int_def, SGN_def] >> Cases_on `n = 0` >> simp[] >>
  rw[] >> rw[RAT_SGN_NUM_COND] >>
  Cases_on `n` >> fs[]);

val RAT_SGN_NUM_BITs = Q.store_thm(
  "RAT_SGN_NUM_BITs[simp]",
  ‘(rat_sgn (&(NUMERAL (BIT1 n))) = 1) /\ (rat_sgn (&(NUMERAL (BIT2 n))) = 1)’,
  REWRITE_TAC[arithmeticTheory.BIT1, arithmeticTheory.BIT2,
              arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO] >>
  simp[RAT_SGN_NUM_COND]);

val RAT_SGN_EQ0 = Q.store_thm(
  "RAT_SGN_EQ0[simp]",
  ‘((rat_sgn r = 0) <=> (r = 0)) /\ ((0 = rat_sgn r) <=> (r = 0))’,
  metis_tac[RAT_SGN_CLAUSES]);

val RAT_SGN_POS = Q.store_thm(
  "RAT_SGN_POS[simp]",
  ‘(rat_sgn r = 1) <=> 0 < r’,
  rw[RAT_SGN_CLAUSES, rat_gre_def]);

val RAT_SGN_NEG = Q.store_thm(
  "RAT_SGN_NEG[simp]",
  ‘(rat_sgn r = -1) <=> r < 0’,
  rw[RAT_SGN_CLAUSES]);

val RAT_SGN_DIV = Q.store_thm(
  "RAT_SGN_DIV[simp]",
  ‘d <> 0 ==> (rat_sgn (n/d) = rat_sgn n * rat_sgn d)’,
  simp[RAT_SGN_MINV, RAT_DIV_MULMINV]);

val RAT_MINV_RATND = Q.store_thm(
  "RAT_MINV_RATND",
  ‘r <> 0 ==>
    (rat_minv r =
       (rat_of_int (rat_sgn r) * &RATD r) / rat_of_int (ABS (RATN r)))’,
  assume_tac (SYM RATN_DIV_RATD) >>
  map_every qabbrev_tac [‘n = RATN r’, ‘d = RATD r’] >>
  first_x_assum SUBST1_TAC >> ‘0 < d’ by simp[Abbr‘d’] >> simp[RAT_DIV_EQ0] >>
  simp[RAT_SGN_NUM_COND] >> Cases_on ‘n’ >>
  simp[RAT_DIV_MINV, rat_of_int_ainv, RAT_SGN_NUM_COND] >>
  simp[RAT_DIV_MULMINV, GSYM RAT_AINV_MINV, GSYM RAT_AINV_LMUL,
       GSYM RAT_AINV_RMUL]);

(* ----------------------------------------------------------------------
    rational min and max
   ---------------------------------------------------------------------- *)

val rat_min_def = Define‘rat_min (r1:rat) r2 = if r1 < r2 then r1 else r2’;
val rat_max_def = Define‘rat_max (r1:rat) r2 = if r1 > r2 then r1 else r2’;

(*==========================================================================
 * end of theory
 *==========================================================================*)

val _ = export_theory();
