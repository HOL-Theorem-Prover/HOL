open Term Type Thm Theory Tactic Tactical Drule Rewrite boolSyntax;
open Lib bossLib Conv Parse translateLib intLib
open sexpTheory translateTheory integerTheory 
open boolTheory defaxiomsTheory extendTranslateTheory;
open hol_defaxioms_proofsTheory;

val _ = new_theory "extend_correct";

val CHOOSEP_TAC = 
    translateLib.CHOOSEP_TAC
    [INT_OF_SEXP_TO_INT,NAT_OF_SEXP_TO_NAT];


local
fun place_tac tm (a,g) = 
let val term = Parse.parse_in_context (g::a) tm
    val vars = set_diff (free_varsl (g::a)) (free_vars term)
in  
    (Cases_on tm THEN
    MAP_EVERY SPEC_TAC (Lib.zip vars vars)) (a,g)
end;
in
fun ZP_INDUCT_TAC tm =
    REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    place_tac tm THEN
    FULL_SIMP_TAC int_ss [zp_def,ite_def,TRUTH_REWRITES,GSYM int_def] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [GSYM INT_THMS,not_def,TRUTH_REWRITES] THEN
    FULL_SIMP_TAC int_ss [int_ge,INT_NOT_LE,INTEGERP_INT] THEN
    MAP_EVERY IMP_RES_TAC [INT_LT_IMP_LE,int_nat_lem] THEN
    TRY (POP_ASSUM SUBST_ALL_TAC THEN Induct_on `a'`)
end;

(*****************************************************************************)
(* defaxioms rewrites                                                        *)
(*****************************************************************************)

val axiom_rewrites = ref [];

fun make_goal_term thm1 thm2 = 
      mk_eq(fst (strip_comb (lhs (concl (SPEC_ALL thm1)))),
            fst (strip_comb (lhs (concl (SPEC_ALL thm2)))));

fun start_proof thm1 thm2 = 
    REWRITE_TAC (FUN_EQ_THM::thm1::thm2::(!axiom_rewrites));

fun prove_axiom name thm1 thm2 tac =
let val r = store_thm(name,make_goal_term thm1 thm2,
    	  start_proof thm1 thm2 THEN tac)
     val r = TRUTH
in  (axiom_rewrites := r::(!axiom_rewrites) ; r)
end;

fun store_axm (name,term,tac) = 
let val thm = store_thm(name,term,tac)
    val rthm = CONV_RULE (REPEATC polytypicLib.UNFUN_EQ_CONV) (GEN_ALL thm)
in  (axiom_rewrites := rthm :: (!axiom_rewrites) ; thm)
end;

fun axiom_proofs () = LIST_CONJ (!axiom_rewrites);


(*****************************************************************************)
(* Simple, non-recursive, axioms                                             *)
(*****************************************************************************)

val equal_axm =
    prove_axiom "equal_axm" 
    		defaxiomsTheory.common_lisp_equal_def equal_def
		ALL_TAC;

val fix_axm = 
    prove_axiom "fix_axm" defaxiomsTheory.fix_def fix_def ALL_TAC;

val zip_axm = 
    prove_axiom "zip_axm" defaxiomsTheory.zip_def zip_def ALL_TAC;

val not_axm = 
    prove_axiom "not_axm" defaxiomsTheory.not_def not_def ALL_TAC;

val nfix_axm = 
    prove_axiom "nfix_axm" defaxiomsTheory.nfix_def nfix_def
    		(REWRITE_TAC [andl_def,nat_def,int_def]);

val ifix_axm = 
    prove_axiom "ifix_axm" defaxiomsTheory.ifix_def ifix_def
    		(REWRITE_TAC [andl_def,nat_def,int_def]);

val atom_axm = 
    prove_axiom "atom_axm" defaxiomsTheory.atom_def atom_def ALL_TAC;

val endp_axm = 
    prove_axiom "endp_axm" defaxiomsTheory.endp_def endp_def ALL_TAC;

val zp_axm = 
    prove_axiom "zp_axm" defaxiomsTheory.zp_def zp_def ALL_TAC;

(*****************************************************************************)
(* Exponentation:                                                            *)
(*****************************************************************************)

val expt_correct = store_axm("expt_correct",
    make_goal_term defaxiomsTheory.expt_def acl2_expt_def,
    REWRITE_TAC [FUN_EQ_THM] THEN
    MAP_EVERY Q.X_GEN_TAC [`j`,`i`] THEN
    CONV_TAC SYM_CONV THEN
    Cases_on `|= integerp i` THENL [
        CHOOSEP_TAC,
        ONCE_REWRITE_TAC [acl2_expt_def,defaxiomsTheory.expt_def] THEN
        ASM_REWRITE_TAC [zip_def,defaxiomsTheory.zip_def,ite_def,
        TRUTH_REWRITES,int_def]] THEN
    completeInduct_on `Num (ABS i')` THEN
    ONCE_REWRITE_TAC [acl2_expt_def,defaxiomsTheory.expt_def] THEN
    REWRITE_TAC [GSYM int_def,GSYM INT_THMS,zip_def,ite_def,TRUTH_REWRITES,
    		INTEGERP_INT,axiom_proofs()] THEN
    RW_TAC std_ss [int_sub] THEN REPEAT AP_TERM_TAC THEN
    FIX_CI_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EQUAL_EXISTS_TAC THEN
    REWRITE_TAC [INTEGERP_INT,GSYM integerTheory.INT_LT,NUM_OF_ABS] THEN
    ARITH_TAC);

(*****************************************************************************)
(* Division: nonnegative-integer-quotient, floor, truncate, rem, mod         *)
(*****************************************************************************)

val nniq_correct = store_axm("nniq_correct",
    make_goal_term defaxiomsTheory.nonnegative_integer_quotient_def 
    		   acl2_nniq_def,
    REWRITE_TAC [FUN_EQ_THM] THEN
    MAP_EVERY Q.X_GEN_TAC [`a`,`b`] THEN
    Cases_on `(|= integerp a) /\ (|= integerp b)` THENL [
        CHOOSEP_TAC,
	ONCE_REWRITE_TAC [acl2_nniq_def,
    	     defaxiomsTheory.nonnegative_integer_quotient_def] THEN
        FULL_SIMP_TAC int_ss [] THEN
    	RW_TAC int_ss [axiom_proofs(),ite_def,TRUTH_REWRITES,GSYM int_def,
	       	       ifix_def,GSYM INT_THMS,nfix_def,andl_def,
		       not_def,equal_def,nat_def] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss [] THEN 
    	FULL_SIMP_TAC int_ss [] THEN
    	CHOOSEP_TAC THEN 
    	FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES,INT_CONG] THEN
    	CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN ARITH_TAC] THEN
    FULL_SIMP_TAC int_ss [] THEN
    CHOOSEP_TAC THEN
    completeInduct_on `Num (ABS a')` THEN
    ONCE_REWRITE_TAC [acl2_nniq_def,
    	     defaxiomsTheory.nonnegative_integer_quotient_def] THEN
    RW_TAC int_ss [INTEGERP_INT,ite_def,TRUTH_REWRITES,nfix_def,andl_def,
    	   GSYM INT_THMS,GSYM int_def,axiom_proofs(),equal_def] THEN
    REPEAT AP_TERM_TAC THEN
    FULL_SIMP_TAC int_ss [nat_def,GSYM INT_THMS,not_def,TRUTH_REWRITES,
    		  ite_def,ifix_def,INTEGERP_INT] THEN
    FIX_CI_TAC THEN 
    FIRST_ASSUM MATCH_MP_TAC THEN
    EQUAL_EXISTS_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC std_ss [GSYM integerTheory.INT_LT,NUM_OF_ABS,INT_CONG,
    	   	  INTEGERP_INT] THEN
    ARITH_TAC);

val floor_correct = store_axm("floor_correct",
    make_goal_term defaxiomsTheory.floor_def acl2_floor_def,
    REWRITE_TAC [FUN_EQ_THM,defaxiomsTheory.floor_def,
    		acl2_floor_def,axiom_proofs(),GSYM int_def] THEN
    RW_TAC (int_ss ++ boolSimps.LET_ss) [INT_THMS]);

val truncate_correct = store_axm("truncate_correct",
    make_goal_term defaxiomsTheory.truncate_def acl2_truncate_def,
    REWRITE_TAC [FUN_EQ_THM,defaxiomsTheory.truncate_def,acl2_truncate_def,
    		axiom_proofs(),GSYM int_def] THEN 
    RW_TAC (int_ss ++ boolSimps.LET_ss) [INT_THMS]);

val mod_correct = 
    prove_axiom "mod_correct" defaxiomsTheory.mod_def acl2_mod_def ALL_TAC;

val rem_correct = 
    prove_axiom "rem_correct" defaxiomsTheory.rem_def acl2_rem_def ALL_TAC;

(*****************************************************************************)
(* Integer theorems: odd, even, max, min, ash...                             *)
(*****************************************************************************)

val zerop_axm = 
    prove_axiom "zerop_axm" defaxiomsTheory.zerop_def acl2_zerop_def 
    (REWRITE_TAC [defaxiomsTheory.eql_def,equal_def,int_def]);

val minusp_axm = 
    prove_axiom "minusp_axm" defaxiomsTheory.minusp_def acl2_minusp_def
    (REWRITE_TAC [int_def]);

val signnum_correct = 
    prove_axiom "signnum_correct" defaxiomsTheory.signum_def acl2_signum_def
    (REWRITE_TAC [int_def,acl2_zerop_def,acl2_minusp_def]);

val evenp_axm = 
    prove_axiom "evenp_axm" defaxiomsTheory.evenp_def acl2_evenp_def
    (REWRITE_TAC [int_def]);

val oddp_axm = 
    prove_axiom "oddp_axm" defaxiomsTheory.oddp_def acl2_oddp_def
    ALL_TAC;

val ash_axm = 
    prove_axiom "ash_axm" defaxiomsTheory.ash_def acl2_ash_def
    (REWRITE_TAC [int_def]);

val max_axm = 
    prove_axiom "max_axm" defaxiomsTheory.max_def acl2_max_def ALL_TAC;

val min_axm = 
    prove_axiom "min_axm" defaxiomsTheory.min_def acl2_min_def ALL_TAC;

val abs_axm = 
    prove_axiom "abs_axm" defaxiomsTheory.abs_def acl2_abs_def
    (REWRITE_TAC [acl2_minusp_def]);

(*****************************************************************************)
(* List theorems: append, revappend, reverse, nthcdr, first_nac,             *)
(*                butlast, nth                                               *)
(*****************************************************************************)

val APPEND_NIL_LEMMA = store_thm("APPEND_NIL_LEMMA",
    ``!x. binary_append nil x = x``,
    Cases THEN ONCE_REWRITE_TAC [defaxiomsTheory.binary_append_def] THEN 
    RW_TAC int_ss [ite_def,endp_def,atom_def,axiom_proofs(),TRUTH_REWRITES,
    	   not_def]);

val append_correct = store_axm("append_correct",
    make_goal_term defaxiomsTheory.binary_append_def acl2_append_def,
    REWRITE_TAC [FUN_EQ_THM] THEN 
    completeInduct_on `sexp_size x + sexp_size x'` THEN
    ONCE_REWRITE_TAC [acl2_append_def,defaxiomsTheory.binary_append_def] THEN
    Cases THEN 
    RW_TAC int_ss [endp_def,consp_def,axiom_proofs(),atom_def,car_def,cdr_def,
    	   TRUTH_REWRITES,ite_def,APPEND_NIL_LEMMA,CAR_NIL,CDR_NIL,not_def] THEN
    FIX_CI_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN 
    EQUAL_EXISTS_TAC THEN RW_TAC int_ss [sexp_size_def]);

val REVAPPEND_NIL_LEMMA = store_thm("REVAPPEND_NIL_LEMMA",
    ``!x. revappend nil x = x``,
    Cases THEN ONCE_REWRITE_TAC [defaxiomsTheory.revappend_def] THEN 
    RW_TAC int_ss [ite_def,endp_def,atom_def,axiom_proofs(),TRUTH_REWRITES,
    	   not_def]);

val revappend_correct = store_axm("revappend_correct",
    make_goal_term defaxiomsTheory.revappend_def acl2_revappend_def,
    REWRITE_TAC [FUN_EQ_THM] THEN 
    Induct THEN
    ONCE_REWRITE_TAC [acl2_revappend_def,defaxiomsTheory.revappend_def] THEN
    RW_TAC int_ss [endp_def,consp_def,axiom_proofs(),atom_def,car_def,cdr_def,
    	   TRUTH_REWRITES,ite_def,REVAPPEND_NIL_LEMMA,
	   CAR_NIL,CDR_NIL,not_def]);

val reverse_axm = 
    prove_axiom "reverse_axm" defaxiomsTheory.reverse_def acl2_reverse_def
    ALL_TAC;


val first_nac_correct = store_axm("first_nac_correct",
    make_goal_term defaxiomsTheory.first_n_ac_def acl2_firstnac_def,
    REWRITE_TAC [FUN_EQ_THM] THEN
    completeInduct_on `sexp_to_nat x` THEN
    ONCE_REWRITE_TAC [defaxiomsTheory.first_n_ac_def,acl2_firstnac_def] THEN
    RW_TAC int_ss [zp_def,axiom_proofs(),ite_def,
    	   TRUTH_REWRITES,GSYM int_def,nat_def,not_def] THEN
    RW_TAC int_ss [] THEN
    CHOOSEP_TAC THEN FULL_SIMP_TAC int_ss [GSYM INT_THMS,TRUTH_REWRITES] THEN
    FIX_CI_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN EQUAL_EXISTS_TAC THEN
    `?i. (x''' = &i) /\ 0 < i` by 
    	 METIS_TAC [INT_OF_NUM,int_gt,integerTheory.INT_LT,INT_LT_IMP_LE] THEN
    RW_TAC int_ss [INT_ADD_COMM,GSYM int_sub,INT_SUB,GSYM nat_def,
    	   SEXP_TO_NAT_OF_NAT]);

val take_axm = 
    prove_axiom "take_axm" defaxiomsTheory.take_def acl2_take_def ALL_TAC;


val nth_cdr_correct = store_axm("nth_cdr_correct",
    make_goal_term defaxiomsTheory.nthcdr_def acl2_nthcdr_def,
    ZP_INDUCT_TAC `|= zp x` THEN
    ONCE_REWRITE_TAC [acl2_nthcdr_def,defaxiomsTheory.nthcdr_def] THEN
    RW_TAC int_ss [zp_def,ite_def,TRUTH_REWRITES,nat_def,
    	   axiom_proofs(),GSYM int_def,INTEGERP_INT,GSYM INT_THMS,not_def]);

val len_axm = store_axm("len_axm",
    make_goal_term defaxiomsTheory.len_def len_def,
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    ONCE_REWRITE_TAC [len_def,defaxiomsTheory.len_def] THEN
    RW_TAC int_ss [consp_def,car_def,cdr_def,ite_def,TRUTH_REWRITES,
    	   nat_def,GSYM int_def]);


val butlast_correct = store_axm("butlast_correct",
    make_goal_term defaxiomsTheory.butlast_def acl2_butlast_def,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [FUN_EQ_THM,acl2_butlast_def,
    	   defaxiomsTheory.butlast_def,axiom_proofs(),
   	   acl2_take_def,ite_def,not_def,TRUTH_REWRITES] THEN
    PROVE_TAC []);

val nth_correct = store_axm("nth_correct",
    make_goal_term defaxiomsTheory.nth_def acl2_nth_def,
    ZP_INDUCT_TAC `|= zp x` THEN 
    ONCE_REWRITE_TAC [defaxiomsTheory.nth_def,acl2_nth_def] THEN 
    RW_TAC int_ss [axiom_proofs(),endp_def,atom_def,consp_def,ite_def,
    	   not_def,TRUTH_REWRITES,GSYM int_def,zp_def,GSYM INT_THMS,
	   INTEGERP_INT,INT_ADD_CALCULATE,nat_def] THEN1
        (CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN ARITH_TAC) THEN
    Cases_on `a' = 0` THEN
    RW_TAC int_ss [] THEN 
    ONCE_REWRITE_TAC [defaxiomsTheory.nth_def,acl2_nth_def] THEN 
    RW_TAC int_ss [zp_def,endp_def,atom_def,axiom_proofs(),ite_def,
    	   TRUTH_REWRITES,GSYM int_def,GSYM INT_THMS,not_def]);

val _ = export_theory();
