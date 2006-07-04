(*****************************************************************************)
(* File: translateScript.sml                                                 *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Provides theories and definitions for conversion between s-expressions    *)
(* and native HOL                                                            *)
(*****************************************************************************)

(* A brief changelog *)

(* 17/05 	- Added LISTP_CONS function              *)
(* 04/07        - switched to hol_defaxiomsTheory (MJCG) *)

(*****************************************************************************)
(* Load base theories                                                        *)
(*****************************************************************************)

(*
val _ = loadPath := "../ml" :: !loadPath;     (* add acl2/ml to load path    *)
val _ = app                                   (* load infrastructure         *)
 load 
 ["sexp",
  "sexpTheory",
  "hol_defaxiomsTheory",
  "intLib","listLib"];
*)

open sexp sexpTheory;                         (* open in current session     *)
open arithmeticTheory fracTheory ratTheory integerTheory intLib 
     complex_rationalTheory intExtensionTheory
     hol_defaxiomsTheory listTheory;

(*****************************************************************************)
(* Start new theory "translate"                                              *)
(*****************************************************************************)
val _ = new_theory "translate";

(*****************************************************************************)
(* Extra ACL2 definitions required for natural number encoding               *)
(*****************************************************************************)

val natp_def = Define `natp a = (ite (integerp a) (ite (less (nat 0) a) t (ite (equal (nat 0) a) t nil)) nil)`;

val nfix_def = Define `nfix a = ite (natp a) a (nat 0)`;

val ifix_def = Define `ifix a = ite (integerp a) a (int 0)`;

(*****************************************************************************)
(* Extra encoding functions:                                                 *)
(*****************************************************************************)

val rat_def = Define `rat a = num (com a rat_0)`;

val bool_def = Define `(bool T = t) /\ (bool F = nil)`;

(*****************************************************************************)
(* Decoding functions:                                                       *)
(*                                                                           *)
(* Inverse to ``num : complex_rational -> sexp``                             *)
(* Inverse to ``int : int -> sexp``                                          *)
(* Inverse to ``nat : num -> sexp``                                          *)
(* Inverse to ``rat : rat -> sexp``                                          *)
(* Inverse to ``bool : bool -> sexp``                                        *)
(*****************************************************************************)

val sexp_to_com_def = 
 Define 
  `(sexp_to_com (num a) = a) /\ (sexp_to_com _ = com_0)`;

val sexp_to_int_def = 
 Define 
  `(sexp_to_int (num (com a b)) = if (integerp (num (com a b)) = t) then (rat_nmr a) / (rat_dnm a) else 0) /\ (sexp_to_int _ = 0)`;

val sexp_to_nat_def = 
 Define 
  `sexp_to_nat a = if (natp a = t) then Num (sexp_to_int a) else 0`;

val sexp_to_rat_def = 
 Define 
  `(sexp_to_rat (num (com a b)) = if (rationalp (num (com a b)) = t) then a else 0) /\ (sexp_to_rat _ = 0)`;

val sexp_to_bool_def = Define `sexp_to_bool x = (x = t)`;

(*****************************************************************************)
(* Encoding and decoding pairs                                               *)
(*                                                                           *)
(* if f : 'a -> sexp, g : 'b -> sexp then pair f g : 'a # 'b -> sexp         *)
(* if f': sexp -> 'a, g': sexp -> 'b then pair f' g' : sexp -> 'a # 'b       *)
(*                                                                           *)
(* Eg: 	pair nat int (1,2) = cons (nat 1) (int 2)                            *)
(*****************************************************************************)

val pair_def = Define `pair f g p = cons (f (FST p)) (g (SND p))`;

val sexp_to_pair_def = Define `sexp_to_pair f' g' (cons a b) = (f' a,g' b)`;

(*****************************************************************************)
(* Encoding and decoding lists                                               *)
(*                                                                           *)
(* if f : 'a -> sexp then list f : 'a list -> sexp                           *)
(* if f': sexp -> 'a then sexp_to_list f' : sexp -> 'a list                  *)
(*                                                                           *)
(* Eg: 	list nat [1;2;3] = cons (nat 1) (cons (nat 2) (cons (nat 3) nil))    *)
(*****************************************************************************)

val list_def = Define `(list f (x::xs) = cons (f x) (list f xs)) /\ (list f [] = nil)`;

val sexp_to_list_def = Define `(sexp_to_list f (cons x xs) = (f x)::(sexp_to_list f xs)) /\ (sexp_to_list f _ = [])`;



(*****************************************************************************)
(* RAT_CONG_TAC:                                                             *)
(*                                                                           *)
(* Abbreviates as x = rep_rat (abs_rat (abs_frac (a,b))) and adds the        *)
(* rational equivalence:                                                     *)
(*    |- frac_nmr x * frac_dnm (abs_frac (a,b)) =                            *)
(*	        frac_nmr (abs_frac (a,b)) * frac_dnm x                       *)
(*                                                                           *)
(*****************************************************************************)

val RAT_CONG_TAC = 
	REPEAT (POP_ASSUM MP_TAC) THEN
	REPEAT (Q.PAT_ABBREV_TAC `x = rep_rat (abs_rat (abs_frac (a''''',b''''')))`) THEN
	REPEAT (DISCH_TAC) THEN
	EVERY_ASSUM (fn th => (ASSUME_TAC o REWRITE_RULE [RAT] o MATCH_MP (prove(``(a = b) ==> (abs_rat a = abs_rat b)``,RW_TAC std_ss []))) 
		(REWRITE_RULE [markerTheory.Abbrev_def] th) handle e => ALL_TAC) THEN
	RULE_ASSUM_TAC (REWRITE_RULE [RAT_EQ]);

(*****************************************************************************)
(* IS_INT_EXISTS :                                                           *)
(*                                                                           *)
(* |- !a b.                                                                  *)
(*      IS_INT (com a b) = (b = rat_0) /\ ?c. a = abs_rat (abs_frac (c,1))   *)
(*****************************************************************************)

val int_pos = prove(``0 < a ==> 0 < Num a``,METIS_TAC [INT_OF_NUM,INT_LT,INT_LT_IMP_LE]);

val int_mod_eq_thm = prove(``0 < b ==> ((Num (ABS a) MOD Num b = 0) = (a % b = 0))``,
	ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
	RW_TAC std_ss [GSYM INT_MOD,int_pos,DECIDE ``0 < a ==> ~(a = 0n)``,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE,INT_ABS_POS] THEN
	RW_TAC int_ss [INT_ABS,INT_MOD_EQ0,INT_LT_IMP_NE] THEN
	EQ_TAC THEN STRIP_TAC THEN
	Q.EXISTS_TAC `~k` THEN
	intLib.ARITH_TAC);

val QUOTIENT_def = fst (snd (hd (DB.find("QUOTIENT_def"))));


val  IS_INT_select = prove(``!a b. IS_INT (com a b) ==> (b = rat_0) /\ ?c. a = abs_rat (abs_frac(c,1))``,
	RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_MOD_EQ0,INT_LT_IMP_NE] THEN
	Q.EXISTS_TAC `rat_nmr a / rat_dnm a` THEN
	SUBGOAL_THEN ``?a'. a  = abs_rat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
		(Q.EXISTS_TAC `rep_rat a` THEN METIS_TAC [QUOTIENT_def,ratTheory.rat_def]) THEN
	RW_TAC int_ss [rat_nmr_def,rat_dnm_def,RAT_EQ,DNM,NMR,INT_LT_01,INT_DIV_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE] THEN
	SUBGOAL_THEN ``?c d. (a' = abs_frac (c,d)) /\ 0 < d`` STRIP_ASSUME_TAC THEN1
		(Q.EXISTS_TAC `frac_nmr a'` THEN Q.EXISTS_TAC `frac_dnm a'` THEN REWRITE_TAC [FRAC,FRAC_DNMPOS]) THEN
	RW_TAC std_ss [NMR,DNM] THEN
	RAT_CONG_TAC THEN
	PAT_ASSUM ``0i < d`` (fn th => (RULE_ASSUM_TAC (SIMP_RULE std_ss [th,NMR,DNM]))) THEN
	PAT_ASSUM ``frac_nmr a = b * c:int`` SUBST_ALL_TAC THEN
	`k * frac_dnm x * d = (k * d) * frac_dnm x` by (CONV_TAC (AC_CONV (INT_MUL_ASSOC,INT_MUL_COMM))) THEN
	METIS_TAC [INT_EQ_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE]);

val IS_INT_eq = prove(``!a. IS_INT (com (abs_rat (abs_frac(a,1))) rat_0)``,
	RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_LT_IMP_NE] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_MOD_COMMON_FACTOR,INT_LT_IMP_NE,FRAC_DNMPOS]);

val IS_INT_EXISTS = store_thm("IS_INT_EXISTS",``!a b. IS_INT (com a b) = (b = rat_0) /\ ?c. a = abs_rat (abs_frac(c,1))``,
	METIS_TAC [IS_INT_select,IS_INT_eq]);

(*****************************************************************************)
(* Make sure all 'p' functions operate on t instead of nil                   *)
(*****************************************************************************)

val NIL_REWRITES = LIST_CONJ 
	(map (fn x => 	prove(x,TRY (Cases_on `a`) THEN TRY (Cases_on `b`) THEN 
				REPEAT (RW_TAC std_ss [bool_def,nil_def,t_def,integerp_def,natp_def,ite_def,less_def,equal_def,consp_def,
								rationalp_def,acl2_numberp_def] THEN
					TRY (Cases_on `c`) THEN TRY (Cases_on `c'`)))) [
	``~(nil = t)``,``(((if a then t else nil) = t) = a) /\ (((if a then t else nil) = nil) = ~a)``,
	``(integerp a = nil) = ~(integerp a = t)``,``(natp a = nil) = ~(natp a = t)``,
	``(acl2_numberp a = nil) = ~(acl2_numberp a = t)``,``(rationalp a = nil) = ~(rationalp a = t)``,	
	``((bool a = nil) = ~a) /\ ((bool a = t) = a)``,
	``((consp a = nil) = ~(consp a = t))``,
	``(consp nil = nil)``,``ite nil a b = b``,``ite t a b = a``,``(less a b = nil) = ~(less a b = t)``]);

(*****************************************************************************)
(* Judgement theorems                                                        *)
(*****************************************************************************)

val BOOLEANP_BOOL = store_thm("BOOLEANP_BOOL",``!a. booleanp (bool a) = t``,
	REWRITE_TAC [booleanp_def] THEN GEN_TAC THEN Cases_on `a` THEN RW_TAC std_ss [equal_def,ite_def,bool_def]);

val INTEGERP_INT = store_thm("INTEGERP_INT",``!a. integerp (int a) = t``,
	RW_TAC std_ss [integerp_def,int_def,cpx_def,IS_INT_EXISTS,NIL_REWRITES,sexpTheory.rat_def,rat_0_def,frac_0_def] THEN
	Q.EXISTS_TAC `a` THEN REFL_TAC);

val NATP_NAT = store_thm("NATP_NAT",``!a. natp (nat a) = t``,
	RW_TAC std_ss [natp_def,nat_def,INTEGERP_INT,ite_def,NIL_REWRITES] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN
	RW_TAC int_ss [ite_def,less_def,equal_def,NIL_REWRITES,int_def,cpx_def,sexpTheory.rat_def,RAT_LES_CALCULATE,RAT_EQ,NMR,DNM]);

val RATIONALP_RAT = store_thm("RATIONALP_RAT",``!a. rationalp (rat a) = t``,RW_TAC std_ss [rationalp_def,rat_def]);

val ACL2_NUMBERP_NUM = store_thm("ACL2_NUMBERP_NUM",``!a. acl2_numberp (num a) = t``,RW_TAC std_ss [acl2_numberp_def]);
	
val CONSP_PAIR = store_thm("CONSP_PAIR",``!x f g. consp (pair f g x) = t``,RW_TAC std_ss [consp_def,pair_def]);

(*****************************************************************************)
(* Encode then decode proofs                                                 *)
(*****************************************************************************)


val SEXP_TO_INT_OF_INT = store_thm("SEXP_TO_INT_OF_INT",``!a. sexp_to_int (int a) = a``,
	GEN_TAC THEN ASSUME_TAC (SPEC_ALL INTEGERP_INT) THEN
	FULL_SIMP_TAC std_ss [sexp_to_int_def,int_def,cpx_def,sexpTheory.rat_def,rat_nmr_def,rat_dnm_def] THEN
	Q.ABBREV_TAC `x = rep_rat (abs_rat (abs_frac (a , 1)))` THEN
	`abs_rat x = abs_rat (abs_frac (a , 1))` by (Q.UNABBREV_TAC `x` THEN REWRITE_TAC [RAT]) THEN
	RULE_ASSUM_TAC (REWRITE_RULE [RAT_EQ]) THEN
	FULL_SIMP_TAC std_ss [NMR,DNM,INT_LT_01,INT_MUL_RID,INT_MUL_LZERO] THEN
	RW_TAC int_ss [FRAC_DNMPOS,INT_LT_IMP_NE,INT_DIV_RMUL]);

val SEXP_TO_NAT_OF_NAT = store_thm("SEXP_TO_NAT_OF_NAT",``!a. sexp_to_nat (nat a) = a``,RW_TAC std_ss [NATP_NAT,sexp_to_nat_def,nat_def,SEXP_TO_INT_OF_INT,NUM_OF_INT]);

val SEXP_TO_RAT_OF_RAT = store_thm("SEXP_TO_RAT_OF_RAT",``!a. sexp_to_rat (rat a) = a``,
	GEN_TAC THEN ASSUME_TAC (SPEC_ALL RATIONALP_RAT) THEN
	FULL_SIMP_TAC std_ss [sexp_to_rat_def,rat_def]);

val SEXP_TO_COM_OF_COM = store_thm("SEXP_TO_COM_OF_COM",``!a. sexp_to_com (num a) = a``,RW_TAC std_ss [sexp_to_com_def]);

val SEXP_TO_PAIR_OF_PAIR = store_thm("SEXP_TO_PAIR_OF_PAIR",``(!a. (f' (f a) = a)) /\ (!b. (g' (g b) = b)) ==> !p. (sexp_to_pair f' g' (pair f g p) = p)``,
	RW_TAC std_ss [pair_def,sexp_to_pair_def]);

val SEXP_TO_LIST_OF_LIST = store_thm("SEXP_TO_LIST_OF_LIST",``(!p. (f' (f p) = p)) ==> !l. (sexp_to_list f' (list f l) = l)``,
	DISCH_TAC THEN Induct THEN RW_TAC std_ss [list_def,sexp_to_list_def,nil_def]);

val SEXP_TO_BOOL_OF_BOOL = store_thm("SEXP_TO_BOOL_OF_BOOL",``!a. sexp_to_bool (bool a) = a``,Cases_on `a` THEN RW_TAC std_ss [bool_def,sexp_to_bool_def,nil_def,t_def]);


(*****************************************************************************)
(* Boolean theorems and definitions                                          *)
(*****************************************************************************)

val BOOL_OF_SEXP_TO_BOOL = store_thm("BOOL_OF_SEXP_TO_BOOL",``!a. (booleanp a = t) ==> (bool (sexp_to_bool a) = a)``,
	RW_TAC std_ss [sexp_to_bool_def,bool_def,booleanp_def,ite_def,equal_def,NIL_REWRITES]);

val BOOLEANP_EQUAL = prove(``!a b. (booleanp (equal a b) = t)``,RW_TAC std_ss [equal_def,booleanp_def,ite_def,NIL_REWRITES]);

val BOOLEANP_LESS = prove(``!a b. (booleanp (less a b) = t)``,
	RW_TAC std_ss [less_def,booleanp_def,ite_def,NIL_REWRITES,equal_def] THEN
	Cases_on `a` THEN Cases_on `b` THEN FULL_SIMP_TAC std_ss [] THEN TRY (Cases_on `c`) THEN TRY (Cases_on `c'`) THEN 
	FULL_SIMP_TAC std_ss [less_def,NIL_REWRITES] THEN METIS_TAC []);

val BOOLEANP_NOT = prove(``!a. (booleanp (not a) = t)``,
	RW_TAC std_ss [booleanp_def,not_def,ite_def,nil_def,t_def,equal_def] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss []);

val BOOLEANP_IF = prove(``!a b. (booleanp a = t) /\ (booleanp b = t) ==> (booleanp (ite p a b) = t)``,
	RW_TAC std_ss [booleanp_def,not_def,ite_def,nil_def,t_def,equal_def] THEN
	REPEAT (REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss []));


val BOOLEANP_CONSP = prove(``booleanp (consp a) = t``,Cases_on `a` THEN RW_TAC std_ss [booleanp_def,consp_def,ite_def,NIL_REWRITES,equal_def]);

val BOOLEANP_ZP = prove(``booleanp (zp a) = t``,
	RW_TAC std_ss [booleanp_def,ite_def,equal_def,zp_def,NIL_REWRITES,GSYM (SPEC ``0i`` int_def)] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [NIL_REWRITES,not_def,ite_def]);

val BOOLEANP_NATP = prove(``booleanp (natp a) = t``,
	Cases_on `a` THEN RW_TAC std_ss [booleanp_def,natp_def,ite_def,NIL_REWRITES,integerp_def,equal_def]);

val BOOL_AND = prove(``bool (a /\ b) = ite (bool a) (bool b) nil``,REPEAT (RW_TAC std_ss [bool_def,ite_def,NIL_REWRITES]));

val BOOL_OR = prove(``bool (a \/ b) = ite (bool a) t (bool b)``,REPEAT (RW_TAC std_ss [bool_def,ite_def,NIL_REWRITES]));
	
val BOOL_IMPLIES = prove(``bool (a ==> b) = ite (bool a) (bool b) t``,REPEAT (RW_TAC std_ss [bool_def,ite_def,NIL_REWRITES]));

val BOOL_NOT = prove(``bool (~a) = not (bool a)``,REPEAT (RW_TAC std_ss [bool_def,ite_def,NIL_REWRITES,not_def]));

val BOOL_EQ = prove(``bool (a = b) = equal (bool a) (bool b)``,Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,equal_def]);

val BOOL_T = CONJUNCT1 bool_def;

val BOOL_F = CONJUNCT2 bool_def;

val BOOL_SEXP_T = prove(``(booleanp x = t) ==> (bool (x = t) = x)``,
	RW_TAC std_ss [bool_def,booleanp_def,ite_def,equal_def,NIL_REWRITES]);

val BOOL_SEXP_F = prove(``(booleanp x = t) ==> (bool (x = nil) = not x)``,
	RW_TAC std_ss [bool_def,booleanp_def,ite_def,equal_def,NIL_REWRITES,not_def]);

(*****************************************************************************)
(* Integer theorems:                                                         *)
(*****************************************************************************)

val INTEGERP_INT = store_thm("INTEGERP_INT",``!a. integerp (int a) =  t``,
	RW_TAC std_ss [integerp_def,int_def,sexpTheory.rat_def,cpx_def,rat_0_def,frac_0_def,NIL_REWRITES,IS_INT_EXISTS] THEN
	Q.EXISTS_TAC `a` THEN REFL_TAC);

val INTEGERP_ADD = store_thm("INTEGERP_ADD",``!a b. (integerp a = t) /\ (integerp b = t) ==> (integerp (add a b) = t)``,
	Cases_on `a` THEN Cases_on `b` THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,add_def,NIL_REWRITES] THEN
	Cases_on `c` THEN Cases_on `c'` THEN
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_ADD_def,RAT_ADD_RID,rat_0_def,GSYM rat_0] THEN
	Q.EXISTS_TAC `c + c'` THEN
	RW_TAC std_ss [rat_add_def,frac_add_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
	RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
	ARITH_TAC);

val INTEGERP_MULT = store_thm("INTEGERP_MULT",``!a b. (integerp a = t) /\ (integerp b = t) ==> (integerp (mult a b) = t)``,
	Cases_on `a` THEN Cases_on `b` THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,mult_def,NIL_REWRITES] THEN
	Cases_on `c` THEN Cases_on `c'` THEN
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_MULT_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,RAT_MUL_LZERO,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID] THEN
	Q.EXISTS_TAC `c * c'` THEN
	RW_TAC std_ss [rat_mul_def,frac_mul_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
	RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
	ARITH_TAC);

val INTEGERP_UNARY_MINUS = store_thm("INTEGERP_UNARY_MINUS",``!a. (integerp a = t) ==> (integerp (unary_minus a) = t)``,
	Cases_on `a` THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,unary_minus_def,NIL_REWRITES] THEN
	Cases_on `c` THEN 
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_SUB_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,com_0_def] THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [RAT_SUB_RID,RAT_SUB_LID,RAT_AINV_0] THEN
	Q.EXISTS_TAC `~c` THEN
	RW_TAC std_ss [RAT_AINV_CALCULATE,frac_ainv_def,NMR,INT_LT_01,DNM]);

val INT_OF_SEXP_TO_INT = store_thm("INT_OF_SEXP_TO_INT",``!a. (integerp a = t) ==> (int (sexp_to_int a) = a)``,
	Cases_on `a` THEN RW_TAC std_ss [integerp_def,NIL_REWRITES] THEN
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [IS_INT_EXISTS,int_def,sexp_to_int_def,cpx_def] THEN
	RW_TAC std_ss [integerp_def,IS_INT_EXISTS,sexpTheory.rat_def,NIL_REWRITES,rat_0_def,frac_0_def] THEN
	RW_TAC std_ss [complex_rational_11,rat_0_def,sexpTheory.rat_def,frac_0_def,rat_nmr_def,rat_dnm_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_DIV_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE]);

val INT_ADD = prove(``!a b. int (a + b) = add (int a) (int b)``,
	RW_TAC int_ss [add_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_ADD_def,rat_add_def,frac_add_def,RAT_EQ,NMR,DNM,INT_LT_01] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,GSYM INT_ADD] THEN ARITH_TAC);

val INT_MULT = prove(``!a b. int (a * b) = mult (int a) (int b)``,
	RW_TAC std_ss [mult_def,int_def,cpx_def,sexpTheory.rat_def,GSYM rat_0,GSYM frac_0_def,COMPLEX_MULT_def,
		RAT_MUL_RZERO,RAT_SUB_RID,RAT_MUL_LZERO,RAT_ADD_RID] THEN
	RW_TAC int_ss [RAT_EQ,rat_mul_def,frac_mul_def,DNM,NMR,INT_LT_01] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [DNM,NMR,INT_LT_01,FRAC_DNMPOS,INT_MUL_POS_SIGN] THEN ARITH_TAC);

val INT_UNARY_MINUS = prove(``!a. int (~a) = unary_minus (int a)``,
	RW_TAC int_ss [unary_minus_def,int_def,cpx_def,sexpTheory.rat_def,GSYM rat_0,GSYM frac_0_def,COMPLEX_SUB_def,com_0_def,
		rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_AINV_CALCULATE,RAT_AINV_0,FRAC_AINV_CALCULATE]);

val INT_EQUAL = prove(``!a b. bool (a = b) = equal (int a) (int b)``,
	RW_TAC int_ss [int_def,cpx_def,sexpTheory.rat_def,RAT_EQ,NIL_REWRITES,NMR,DNM,INT_LT_01,equal_def]);

val INT_LT = prove(``!a b. bool (a < b) = less (int a) (int b)``,
	RW_TAC int_ss [less_def,int_def,cpx_def,sexpTheory.rat_def,RAT_LES_CALCULATE,NIL_REWRITES,RAT_EQ,NMR,DNM,INT_LT_01]);

(*****************************************************************************)
(* Nat theorems:                                                             *)
(*****************************************************************************)

val integerp_natp = prove(``(natp a = t) ==> (integerp a = t)``,
	RW_TAC std_ss [natp_def,NIL_REWRITES,ite_def]);

val natp_int_pos = prove(``(natp a = t) ==> 0 <= sexp_to_int a``,
	Cases_on `a` THEN RW_TAC std_ss [natp_def,nat_def,ite_def,NIL_REWRITES,GSYM INT_LT,GSYM INT_EQUAL] THEN
		TRY (FULL_SIMP_TAC std_ss [less_def,integerp_def,equal_def,NIL_REWRITES] THEN NO_TAC) THEN
	(SUBGOAL_THEN ``?a. num c = int a`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int (num c)` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT])) THEN
	FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM INT_EQUAL,NIL_REWRITES,SEXP_TO_INT_OF_INT]);


val NATP_NAT = store_thm("NATP_NAT",``!a. (natp (nat a) = t)``,
	RW_TAC std_ss [natp_def,nat_def,INTEGERP_INT,ite_def,equal_def,NIL_REWRITES] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss [less_def,int_def,cpx_def,sexpTheory.rat_def,RAT_EQ,RAT_LES_CALCULATE,NMR,DNM,INT_LT_01,NIL_REWRITES]);

val NAT_EQUAL = prove(``!a b. bool (a = b) = equal (nat a) (nat b)``,
	RW_TAC int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,RAT_EQ,NIL_REWRITES,NMR,DNM,INT_LT_01,equal_def]);

(* Special cases... *)

val NAT_EQUAL_0 = prove(``!a. bool (a = 0n) = zp (nat a)``,
	RW_TAC std_ss [bool_def,zp_def,nat_def,INTEGERP_INT,ite_def,not_def,GSYM int_def,GSYM INT_LT,NIL_REWRITES,INT_NOT_LT] THEN
	ARITH_TAC);

val NAT_0_LT = prove(``!a. bool (0n < a) = not (zp (nat a))``,
	RW_TAC std_ss [bool_def,zp_def,nat_def,INTEGERP_INT,ite_def,not_def,GSYM int_def,GSYM INT_LT,NIL_REWRITES,INT_NOT_LT] THEN
	ARITH_TAC);



val NAT_OF_SEXP_TO_NAT = store_thm("NAT_OF_SEXP_TO_NAT",``!a. (natp a = t) ==> (nat (sexp_to_nat a) = a)``,
	RW_TAC std_ss [sexp_to_nat_def,nat_def,INT_OF_SEXP_TO_INT,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),natp_int_pos,integerp_natp]);

val NAT_ADD = prove(``!a b. nat (a + b) = add (nat a) (nat b)``,
	RW_TAC std_ss [nat_def,add_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_ADD_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,RAT_ADD_RID,rat_add_def,frac_add_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_LT_IMP_NE] THEN ARITH_TAC);

val NAT_SUC = prove(``!a. nat (SUC a) = add (nat a) (nat 1)``,
	RW_TAC std_ss [NAT_ADD,ADD1]);

val NAT_MULT = prove(``!a b. nat (a * b) = mult (nat a) (nat b)``,
	RW_TAC std_ss [nat_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_MULT_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,
		RAT_MUL_RZERO,RAT_SUB_RID,rat_mul_def,frac_mul_def,RAT_ADD_RID] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_LT_IMP_NE,rat_0,frac_0_def,RAT_NMREQ0_CONG] THEN
	ARITH_TAC);

val NATP_ADD = prove(``!a b. (natp a = t) /\ (natp b = t) ==> (natp (add a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?c. a = nat c`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?c. b = nat c`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [GSYM NAT_ADD,NATP_NAT]);

val NATP_MULT = prove(``!a b. (natp a = t) /\ (natp b = t) ==> (natp (mult a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?c. a = nat c`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?c. b = nat c`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [GSYM NAT_MULT,NATP_NAT]);

val NATP_NFIX = prove(``!a. natp (nfix a) = t``,RW_TAC std_ss [nfix_def,NATP_NAT,ite_def,NIL_REWRITES]);

	
val NZP_NATP = prove(``~(zp x = t) ==> (natp x = t)``,
	RW_TAC std_ss [zp_def,natp_def,ite_def,NIL_REWRITES,GSYM int_def,GSYM (REWRITE_CONV [nat_def] ``nat 0``),not_def]);

val NATP_SUB1 = prove(``!a. ~(zp a = t) ==> (natp (add a (unary_minus (nat 1))) = t)``,
	REPEAT STRIP_TAC THEN 
	`natp a = t` by METIS_TAC [NZP_NATP] THEN
	SUBGOAL_THEN ``?a'. a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
		(Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN 
	RW_TAC std_ss [nat_def,not_def,zp_def,natp_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,GSYM INT_LT,GSYM INT_EQUAL,ite_def,NIL_REWRITES,INTEGERP_INT,
		NIL_REWRITES,GSYM (SPEC ``(& 0n) :int`` int_def)] THEN
	ARITH_TAC);

val NATP_SUC_SUB1 = prove(``!a. ~(zp a = t) ==> (SUC (sexp_to_nat (add a (unary_minus (nat 1)))) = sexp_to_nat a)``,
	REPEAT STRIP_TAC THEN `natp a = t` by METIS_TAC [NZP_NATP] THEN
	SUBGOAL_THEN ``?a'. a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN
	RW_TAC std_ss [natp_def,nat_def,sexp_to_nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,GSYM INT_EQUAL,
		GSYM INT_LT,ite_def,NIL_REWRITES,INTEGERP_INT,SEXP_TO_INT_OF_INT,ADD1,GSYM int_sub,integerTheory.INT_SUB,
		ARITH_PROVE ``0i < & a ==> 1n <= a``,NUM_OF_INT,not_def,zp_def,GSYM (SPEC ``(& 0n):int`` int_def)] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss []);

val NATP_ZERO = prove(``!a. (zp a = t) ==> (sexp_to_nat a = 0)``,
	RW_TAC std_ss [zp_def,equal_def,ite_def,NIL_REWRITES,GSYM (SPEC ``(& 0n):int`` int_def),not_def,natp_def] THEN
	FULL_SIMP_TAC std_ss [SEXP_TO_NAT_OF_NAT,nat_def,NIL_REWRITES] THENL [
		Cases_on `a` THEN RW_TAC std_ss [integerp_def,sexp_to_nat_def,natp_def,ite_def,NIL_REWRITES],
		SUBGOAL_THEN ``?a'. a = int a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int a` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT])] THEN
	FULL_SIMP_TAC int_ss [GSYM INT_LT,INTEGERP_INT,NIL_REWRITES,sexp_to_nat_def,natp_def,ite_def,NIL_REWRITES,nat_def,GSYM INT_EQUAL,SEXP_TO_INT_OF_INT] THEN
	Cases_on `a' = 0` THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss [NIL_REWRITES]);

val NATP_UMINUS_ADD = prove(``(natp a = t) ==> (add (add a (unary_minus (nat b))) (unary_minus (nat c)) = add a (unary_minus (nat (b + c))))``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'. a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN
	RW_TAC std_ss [natp_def,nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,ite_def,NIL_REWRITES,GSYM INT_LT,GSYM INT_EQUAL,GSYM int_sub,integerTheory.INT_SUB,
		ARITH_PROVE ``~(& a = 0i) ==> 1n <= a``,NUM_OF_INT] THEN
	MATCH_MP_TAC (prove(``(a = b) ==> (int a = int b)``,RW_TAC std_ss [])) THEN ARITH_TAC);

(* Probably not required anymore...

val NATP_COMPLETE_INDUCT = prove(``(!n. (natp n = t) ==> (!m. (natp m = t) /\ (less m n = t) ==> P m) ==> P n) ==> !n. (natp n = t) ==> P n``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a. n = nat a`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat n` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [NATP_NAT] THEN
	completeInduct_on `a` THEN
	RW_TAC std_ss [] THEN
	PAT_ASSUM ``!n. (natp n = t) ==> B`` (ASSUME_TAC o SPEC ``nat a``) THEN
	FULL_SIMP_TAC std_ss [NATP_NAT] THEN
	POP_ASSUM MATCH_MP_TAC THEN
	RW_TAC std_ss [] THEN
	PAT_ASSUM ``!m. P`` (ASSUME_TAC o SPEC ``sexp_to_nat m``) THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [] THEN
	SUBGOAL_THEN ``?b. m = nat b`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat m` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [] THEN
	FULL_SIMP_TAC std_ss [GSYM NAT_LT,NIL_REWRITES,NATP_NAT,SEXP_TO_NAT_OF_NAT]);
*)




(*****************************************************************************)
(* Rational theorems:                                                        *)
(*****************************************************************************)

val RATIONALP_ADD = store_thm("RATIONALP_ADD",``(rationalp a = t) /\ (rationalp b = t) ==> (rationalp (add a b) = t)``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [rationalp_def,add_def,NIL_REWRITES] THEN 
	Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_ADD_def,NIL_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID]);

val RATIONALP_MULT = store_thm("RATIONALP_MULT",``(rationalp a = t) /\ (rationalp b = t) ==> (rationalp (mult a b) = t)``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [rationalp_def,mult_def,NIL_REWRITES] THEN 
	Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_MULT_def,NIL_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID,RAT_MUL_RZERO,RAT_MUL_LZERO]);

val RATIONALP_UNARY_MINUS = store_thm("RATIONALP_UNARY_MINUS",``(rationalp a = t) ==> (rationalp (unary_minus a) = t)``,
	Cases_on `a` THEN RW_TAC std_ss [rationalp_def,unary_minus_def,NIL_REWRITES] THEN 
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [rationalp_def,NIL_REWRITES,rat_0_def,GSYM rat_0,com_0_def,COMPLEX_SUB_def,RAT_SUB_RID]);

val RATIONALP_RECIPROCAL = store_thm("RATIONALP_RECIPROCAL",``(rationalp a = t) ==> (rationalp (reciprocal a) = t)``,
	Cases_on `a` THEN RW_TAC std_ss [rationalp_def,reciprocal_def,NIL_REWRITES,int_def,com_0_def,cpx_def,sexpTheory.rat_def,rat_0_def, GSYM rat_0,GSYM frac_0_def] THEN
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [COMPLEX_RECIPROCAL_def,complex_rational_11,rationalp_def,NIL_REWRITES,rat_0_def,
		GSYM rat_0,RAT_MUL_RZERO,RAT_ADD_RID,RAT_AINV_0,RAT_LDIV_EQ,RAT_NO_ZERODIV_NEG]);


val RAT_OF_SEXP_TO_RAT = store_thm("RAT_OF_SEXP_TO_RAT",``!a. (rationalp a = t) ==> (rat (sexp_to_rat a) = a)``,
	Cases_on `a` THEN RW_TAC std_ss [rationalp_def,NIL_REWRITES,rat_def] THEN Cases_on `c` THEN FULL_SIMP_TAC std_ss [rationalp_def,sexp_to_rat_def,NIL_REWRITES]);

val RAT_ADD = prove(``!a b. rat (a + b) = add (rat a) (rat b)``,
	RW_TAC std_ss [add_def,COMPLEX_ADD_def,rat_0_def,GSYM rat_0,RAT_ADD_RID,rat_def]);

val RAT_MULT = prove(``!a b. rat (a * b) = mult (rat a) (rat b)``,
	RW_TAC std_ss [mult_def,COMPLEX_MULT_def,rat_0_def,GSYM rat_0,rat_def,RAT_SUB_RID,RAT_MUL_LZERO,RAT_MUL_RZERO,RAT_ADD_RID]);

val RAT_UNARY_MINUS = prove(``!a. rat (~a) = unary_minus (rat a)``,
	RW_TAC std_ss [rat_def,unary_minus_def,com_0_def,COMPLEX_SUB_def,rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_AINV_0]);

val rat_divshiftthm = prove(``a * (b / c) = a * b / c:rat``,RW_TAC std_ss [RAT_DIV_MULMINV,RAT_MUL_ASSOC]);

val RAT_DIV = prove(``!a b. ~(b = 0) ==> (rat (a / b) = mult (rat a) (reciprocal (rat b)))``,
	RW_TAC std_ss [rat_def,mult_def,reciprocal_def,COMPLEX_RECIPROCAL_def,rat_0_def,GSYM rat_0,COMPLEX_MULT_def,RAT_MUL_RZERO,
		RAT_ADD_RID,RAT_MUL_LZERO,RAT_ADD_LID,RAT_AINV_0,int_def,RAT_SUB_RID,com_0_def,complex_rational_11,cpx_def,sexpTheory.rat_def,
		GSYM frac_0_def,RAT_LDIV_EQ,rat_divshiftthm,RAT_NO_ZERODIV_NEG,RAT_RDIV_EQ,RAT_MUL_ASSOC] THEN
	CONV_TAC (AC_CONV (RAT_MUL_ASSOC,RAT_MUL_COMM)));

val RAT_SUB = prove(``!a b. rat (a - b) = add (rat a) (unary_minus (rat b))``,
	RW_TAC std_ss [rat_def,add_def,unary_minus_def,com_0_def,rat_0_def,GSYM rat_0,COMPLEX_SUB_def,COMPLEX_ADD_def,RAT_SUB_LID,RAT_ADD_RID,RAT_AINV_0,RAT_SUB_ADDAINV]);

val RAT_EQUAL = prove(``!a b. bool (a = b) = equal (rat a) (rat b)``,RW_TAC std_ss [bool_def,equal_def,rat_def,RAT_LES_REF]);

(*****************************************************************************)
(* Complex (general number) theorems:                                        *)
(*****************************************************************************)

val ACL2_NUMBERP_COM = store_thm("ACL2_NUMBERP_COM",``acl2_numberp (num a) = t``,RW_TAC std_ss [acl2_numberp_def]);

val ACL2_NUMBERP_ADD = store_thm("ACL2_NUMBERP_ADD",``acl2_numberp (add a b) = t``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [acl2_numberp_def,add_def,NIL_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_MULT = store_thm("ACL2_NUMBERP_MULT",``acl2_numberp (mult a b) = t``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [acl2_numberp_def,mult_def,NIL_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_UNARY_MINUS = store_thm("ACL2_NUMBERP_UNARY_MINUS",``acl2_numberp (unary_minus a) = t``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,unary_minus_def,NIL_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_RECIPROCAL = store_thm("ACL2_NUMBERP_RECIPROCAL",``acl2_numberp (reciprocal a) = t``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,reciprocal_def,NIL_REWRITES,int_def,cpx_def]);

val NUM_OF_SEXP_TO_COM = store_thm("NUM_OF_SEXP_TO_COM",``!a. (acl2_numberp a = t) ==> (num (sexp_to_com a) = a)``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,NIL_REWRITES,sexp_to_com_def]);

val COM_ADD = prove(``!a b. num (a + b) = add (num a) (num b)``,RW_TAC std_ss [add_def]);

val COM_MULT = prove(``!a b. num (a * b) = mult (num a) (num b)``,RW_TAC std_ss [mult_def]);

val COM_UNARY_MINUS = prove(``!a. num (~a) = unary_minus (num a)``,RW_TAC std_ss [unary_minus_def,COMPLEX_NEG_def]);

val COM_SUB = prove(``num (a - b) = add (num a) (unary_minus (num b))``,
	RW_TAC std_ss [unary_minus_def,add_def,com_0_def] THEN
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_ADD_def,COMPLEX_SUB_def,rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_LSUB_EQ] THEN
	METIS_TAC [RAT_ADD_COMM,RAT_ADD_ASSOC,RAT_ADD_RINV,RAT_ADD_RID]);

val COM_DIV = prove(``!a b. ~(b = com_0) ==> (num (a / b) = mult (num a) (reciprocal (num b)))``,
	RW_TAC std_ss [mult_def,reciprocal_def,COMPLEX_DIV_def]);

val COM_EQUAL = prove(``bool (a = b) = equal (num a) (num b)``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,equal_def,NIL_REWRITES,complex_rational_11]);

val FIX_NUM = prove(``(!a. fix (num a) = num a) /\ (!a. fix (rat a) = rat a) /\ (!a. fix (int a) = int a) /\ (!a. fix (nat a) = nat a)``,
	RW_TAC std_ss [fix_def,ACL2_NUMBERP_NUM,ite_def,NIL_REWRITES,rat_def,int_def,nat_def,cpx_def]);

val NAT_NFIX = prove(``nfix (nat a) = nat a``,RW_TAC std_ss [nfix_def,ite_def,NIL_REWRITES,NATP_NAT]);

val INT_IFIX = prove(``ifix (int a) = int a``,RW_TAC std_ss [ifix_def,ite_def,NIL_REWRITES,INTEGERP_INT]);

(*****************************************************************************)
(* Pair theorems:                                                            *)
(*****************************************************************************)

val CONSP_MK_PAIR = prove(``(consp a = t) ==> ((f (car a),g (cdr a)) = sexp_to_pair f g a)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?x y. a = cons x y`` (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN1
		(Q.EXISTS_TAC `car a` THEN Q.EXISTS_TAC `cdr a` THEN Cases_on `a` THEN FULL_SIMP_TAC std_ss [car_def,cdr_def,consp_def,sexp_distinct,NIL_REWRITES]) THEN
	RW_TAC std_ss [sexp_to_pair_def,car_def,cdr_def]);

val CONSP_PAIR = prove(``consp (pair f g x) = t``,RW_TAC std_ss [consp_def,pair_def]);
	
val PAIR_OF_SEXP_TO_PAIR = store_thm("PAIR_OF_SEXP_TO_PAIR",``(consp a = t) ==> (pair f g (sexp_to_pair f' g' a) = (cons (f (f' (car a))) (g (g' (cdr a)))))``,
	Cases_on `a` THEN RW_TAC std_ss [pair_def,sexp_to_pair_def,consp_def,NIL_REWRITES,car_def,cdr_def]);
	
val PAIR_OF_SEXP_TO_PAIR_CONS = prove(``(pair f g (sexp_to_pair f' g' (cons a b)) = (cons (f (f' a)) (g (g' b))))``,
	Cases_on `a` THEN RW_TAC std_ss [pair_def,sexp_to_pair_def,consp_def,NIL_REWRITES,car_def,cdr_def]);

val PAIR_COMMA = prove(``pair f g (a,b) = cons (f a) (g b)``,RW_TAC std_ss [pair_def]);

val PAIR_FST = prove(``f (FST x) = car (pair f g x)``,RW_TAC std_ss [pairTheory.FST,pair_def,car_def]);

val PAIR_SND = prove(``g (SND x) = cdr (pair f g x)``,RW_TAC std_ss [pairTheory.SND,pair_def,cdr_def]);


val PAIR_IDENTITY = prove(``(consp x = t) /\ (f (f' (car x)) = car x) /\ (g (g' (cdr x)) = cdr x) ==> (pair f g (f' (car x),g' (cdr x)) = x)``,
	Cases_on `x` THEN RW_TAC std_ss [pair_def,cdr_def,car_def,consp_def,NIL_REWRITES]);


(*****************************************************************************)
(* List theorems:                                                            *)
(*****************************************************************************)

val sexp_EVERY_def = Define `(sexp_EVERY P (cons a b) = P a /\ sexp_EVERY P b) /\ (sexp_EVERY P x = (x = nil))`;

val SEXP_TO_LIST_CONSP = prove(``!a f. (consp a = t) ==> ((f (car a) = head) /\ (sexp_to_list f (cdr a) = tail) ==> (sexp_to_list f a = head::tail))``,
	REPEAT STRIP_TAC THEN
	POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
	Induct_on `a` THEN
	RW_TAC std_ss [atom_def,consp_def,ite_def,NIL_REWRITES,not_def,eq_def,equal_def,sexp_to_list_def,car_def,cdr_def]);

val SEXP_TO_LIST_NULL = prove(``!a f. ~(consp a = t) ==> (sexp_to_list f a = [])``,Cases_on `a` THEN RW_TAC std_ss [consp_def,sexp_to_list_def]);


val LIST_CONS = prove(``list encode (a::b) = cons (encode a) (list encode b)``,RW_TAC std_ss [list_def]);

val LIST_NIL = prove(``list encode [] = nil``,RW_TAC std_ss [list_def]);

val LIST_OF_SEXP_TO_LIST = store_thm("LIST_OF_SEXP_TO_LIST",``!l. (sexp_EVERY P l) /\ (!a. P a ==> (encode (decode a) = a)) ==> (list encode (sexp_to_list decode l) = l)``,
	Induct THEN RW_TAC std_ss [sexp_EVERY_def,list_def,sexp_to_list_def,NIL_REWRITES,ite_def,equal_def] THEN
	METIS_TAC []);

val LISTP_LIST = store_thm ("LISTP_LIST",``(!a. P (f a)) ==> (sexp_EVERY P (list f a))``,Induct_on `a` THEN RW_TAC std_ss [sexp_EVERY_def,list_def,nil_def]);

val LISTP_TAIL = prove(``(sexp_EVERY P a) ==> (sexp_EVERY P (cdr a))``,
	Induct_on `a` THEN RW_TAC std_ss [sexp_EVERY_def,nil_def,cdr_def]);

val LISTP_HEAD = prove(``~(sexp_to_list f a = []) /\ (sexp_EVERY P a) ==> P (car a)``,
	Induct_on `a` THEN RW_TAC std_ss [sexp_EVERY_def,nil_def,cdr_def,consp_def,t_def,car_def,sexp_to_list_def]);

val LISTP_CONS_HT = prove(``~(sexp_to_list f a = []) /\ sexp_EVERY P a ==> sexp_EVERY P (cons (car a) (cdr a))``,
	Induct_on `a` THEN RW_TAC std_ss [sexp_EVERY_def,nil_def,cdr_def,consp_def,t_def,car_def,sexp_to_list_def]);

val LISTP_CONS = prove(``P a /\ sexp_EVERY P b ==> sexp_EVERY P (cons a b)``,
	Induct_on `b` THEN RW_TAC std_ss [sexp_EVERY_def,nil_def,cdr_def,consp_def,t_def,car_def]);

val LIST_HD = prove(``~(l = []) ==> (encode (HD l) = car (list encode l))``,
	Induct_on `l` THEN RW_TAC std_ss [list_def,HD,car_def]);

val LIST_TL = prove(``~(l = []) ==> (list encode (TL l) = cdr (list encode l))``,
	Induct_on `l` THEN RW_TAC std_ss [list_def,TL,cdr_def]);

(* true_listp theorems, now depreciated for acl2_EVERY, but staying here, just in case *)

(*

val LISTP_LIST = store_thm("LISTP_LIST",``!f l. true_listp (list f l) = t``,
	Induct_on `l` THEN ONCE_REWRITE_TAC [true_listp_def] THEN RW_TAC std_ss [list_def,ite_def,consp_def,nil_def,eq_def,equal_def,cdr_def]);

val LISTP_CDR = prove(``!a. (true_listp a = t) ==> (true_listp (cdr a) = t)``,
	Induct_on `a` THEN 
	REPEAT (ONCE_REWRITE_TAC [true_listp_def] THEN 
		RW_TAC std_ss [cdr_def,ite_def,NIL_REWRITES,consp_def,atom_def,not_def,eq_def,equal_def,car_def] THEN
		FULL_SIMP_TAC std_ss [(REWRITE_CONV [nil_def] THENC REWRITE_CONV [consp_def]) ``consp nil``,NIL_REWRITES]));

val LISTP_NIL = prove(``true_listp nil = t``,
	ONCE_REWRITE_TAC [true_listp_def] THEN RW_TAC std_ss [ite_def,NIL_REWRITES,consp_def,REWRITE_CONV [nil_def] ``consp nil``,eq_def,equal_def]);

val LISTP_CONS = prove(``(true_listp tl = t) = (true_listp (cons v tl) = t)``,
	EQ_TAC THEN REPEAT STRIP_TAC THENL [
		ALL_TAC,CCONTR_TAC THEN PAT_ASSUM ``a = t`` MP_TAC] THEN
	PURE_ONCE_REWRITE_TAC [true_listp_def] THEN 
	RW_TAC std_ss [ite_def,NIL_REWRITES,consp_def,REWRITE_CONV [nil_def] ``consp nil``,eq_def,equal_def,cdr_def]);

val LISTP_REWRITE = prove(``(true_listp h = t) = (h = nil) \/ ?v tl. (h = cons v tl) /\ (true_listp tl = t)``,
	Cases_on `h = nil` THEN RW_TAC std_ss [LISTP_NIL] THEN
	Induct_on `h` THEN ONCE_REWRITE_TAC [true_listp_def] THEN 
	RW_TAC std_ss [ite_def,consp_def,car_def,cdr_def,NIL_REWRITES,eq_def,equal_def,LISTP_NIL] THENL [
		Cases_on `h' = cons v tl` THEN FULL_SIMP_TAC std_ss [consp_def],
		EQ_TAC THEN RW_TAC std_ss [LISTP_CDR]] THEN
	Cases_on `h' = nil` THEN RW_TAC std_ss [LISTP_NIL] THEN
	Q.EXISTS_TAC `car h'` THEN Q.EXISTS_TAC `cdr h'` THEN
	Cases_on `h'` THEN FULL_SIMP_TAC std_ss [car_def,cdr_def,consp_def,sexp_distinct,NIL_REWRITES]);

val LISTP_INDUCT = prove(``!P. P nil /\ (!l. (true_listp l = t) ==> P (cdr l) ==> P l) ==> !l. (true_listp l = t) ==> P l``,
	REPEAT STRIP_TAC THEN Induct_on `l` THEN REPEAT STRIP_TAC THEN
	POP_ASSUM (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [LISTP_REWRITE] th)) THEN
	RW_TAC std_ss [] THEN
	TRY (POP_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
	METIS_TAC [LISTP_CONS,cdr_def]);

*)

(*****************************************************************************)
(* Comparison theorems:                                                      *)
(*****************************************************************************)

(* LT, LE, GT, GE *)

val NAT_LT = prove(``!a b. bool (a < b) = less (nat a) (nat b)``,
	RW_TAC int_ss [less_def,nat_def,int_def,cpx_def,sexpTheory.rat_def,RAT_LES_CALCULATE,NIL_REWRITES,RAT_EQ,NMR,DNM,INT_LT_01]);

val RAT_LT = prove(``!a b. bool (a < b) = less (rat a) (rat b)``,RW_TAC std_ss [bool_def,less_def,rat_def,RAT_LES_REF]);

val COM_LT = prove(``bool (a < b) = less (num a) (num b)``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,less_def,NIL_REWRITES,COMPLEX_LT_def]);


val COM_NOT_LT = prove(``!a b. ~(a < b) = b <= a:complex_rational``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_LT_def,COMPLEX_LE_def,RAT_LEQ_LES,rat_leq_def] THEN METIS_TAC [RAT_LES_IMP_NEQ]);

val NAT_LE = prove(``bool (a <= b) = not (less (nat b) (nat a))``,RW_TAC std_ss [bool_def,NIL_REWRITES,not_def,ite_def,GSYM NAT_LT,NOT_LESS]);

val INT_LE = prove(``bool (a <= b) = not (less (int b) (int a))``,RW_TAC int_ss [bool_def,NIL_REWRITES,not_def,ite_def,GSYM INT_LT,INT_NOT_LT]);

val RAT_LE = prove(``bool (a <= b) = not (less (rat b) (rat a))``,RW_TAC std_ss [bool_def,NIL_REWRITES,not_def,ite_def,GSYM RAT_LT,RAT_LEQ_LES]);

val COM_LE = prove(``bool (a <= b) = not (less (num b) (num a))``,RW_TAC std_ss [bool_def,NIL_REWRITES,not_def,ite_def,GSYM COM_LT,COM_NOT_LT]);


val NAT_GE = prove(``bool (a >= b) = bool (b <= a:num)``,AP_TERM_TAC THEN DECIDE_TAC);
val INT_GE = prove(``bool (a >= b) = bool (b <= a:int)``,AP_TERM_TAC THEN ARITH_TAC);
val RAT_GE = prove(``bool (a >= b) = bool (b <= a:rat)``,REWRITE_TAC [rat_geq_def]);
val COM_GE = prove(``bool (a >= b) = bool (b <= a:complex_rational)``,
	Cases_on `a` THEN Cases_on `b` THEN REWRITE_TAC [COMPLEX_LE_def,COMPLEX_GE_def,rat_geq_def,rat_gre_def] THEN AP_TERM_TAC THEN PROVE_TAC []);


val NAT_GT = prove(``bool (a > b) = bool (b < a:num)``,AP_TERM_TAC THEN DECIDE_TAC);
val INT_GT = prove(``bool (a > b) = bool (b < a:int)``,AP_TERM_TAC THEN ARITH_TAC);
val RAT_GT = prove(``bool (a > b) = bool (b < a:rat)``,REWRITE_TAC [rat_gre_def]);
val COM_GT = prove(``bool (a > b) = bool (b < a:complex_rational)``,
	Cases_on `a` THEN Cases_on `b` THEN REWRITE_TAC [COMPLEX_LT_def,COMPLEX_GT_def,rat_geq_def,rat_gre_def] THEN AP_TERM_TAC THEN PROVE_TAC []);



val INT_CONG = prove(``(int a = int b) = (a = b)``,EQ_TAC THEN RW_TAC int_ss [int_def,cpx_def,sexpTheory.rat_def,ratTheory.RAT_EQ,NMR,DNM]);


(*****************************************************************************)
(* Subtraction theorems:                                                     *)
(*****************************************************************************)

val INT_SUB = prove(``int (a - b) = add (int a) (unary_minus (int b))``,RW_TAC int_ss [GSYM INT_ADD,GSYM INT_UNARY_MINUS,int_sub]);
val NAT_SUB = prove(``nat (a - b) = nfix (add (nat a) (unary_minus (nat b)))``,
	RW_TAC int_ss [GSYM INT_ADD,GSYM INT_UNARY_MINUS,nat_def,nfix_def,natp_def,INTEGERP_INT,GSYM int_sub,
		GSYM INT_LT,GSYM INT_EQUAL,NIL_REWRITES,ite_def] THEN
	POP_ASSUM MP_TAC THEN RW_TAC int_ss [NIL_REWRITES,INT_NOT_LT,INT_CONG,integerTheory.INT_SUB,INT_LE_SUB_RADD,INT_EQ_SUB_LADD] THEN
	RW_TAC int_ss [INT_NOT_LE,INT_LT_IMP_LE,GSYM integerTheory.INT_SUB]);
val RAT_SUB = prove(``rat (a - b) = add (rat a) (unary_minus (rat b))``,
	RW_TAC std_ss [rat_sub_def,frac_sub_def,GSYM RAT_ADD,GSYM RAT_UNARY_MINUS,rat_ainv_def,rat_add_def,frac_ainv_def,RAT_ADD_CONG]);
val COM_SUB = prove(``num (a - b) = add (num a) (unary_minus (num b))``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_SUB_def,GSYM COM_UNARY_MINUS,GSYM COM_ADD,
		COMPLEX_NEG_def,COMPLEX_ADD_def,com_0_def,RAT_SUB_LID,rat_0_def,GSYM rat_0,RAT_SUB_ADDAINV]);

val NAT_SUB_COND = prove(``!a b. b <= a ==> (nat (a - b) = add (nat a) (unary_minus (nat b)))``,
	RW_TAC std_ss [NAT_SUB,nfix_def,ite_def,NIL_REWRITES] THEN
	CCONTR_TAC THEN PAT_ASSUM ``~(a = t)`` MP_TAC THEN 
	RW_TAC int_ss [natp_def,nat_def,ite_def,NIL_REWRITES,GSYM INT_LT,GSYM INT_SUB,INTEGERP_INT,GSYM INT_EQUAL] THEN
	ARITH_TAC);

(*****************************************************************************)
(* Exponentiation theorems:                                                  *)
(*****************************************************************************)

val (expt_def,expt_ind) = Defn.tprove(Hol_defn "expt" `expt r i =
	if i = 0 then com_1 else
		if r = com_0 then com_0 else 
			if (0 < i) then	(r * (expt r (i - 1i))) else ((com_1 / r) * (expt r (i + 1)))`,
	WF_REL_TAC `measure (\a. Num (ABS (SND a)))` THEN ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
	RW_TAC std_ss [INT_ABS] THEN 
	FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN ARITH_TAC);

val (acl2_expt_def,acl2_expt_ind) = (REWRITE_RULE [GSYM ite_def] ## I) (Defn.tprove(Hol_defn "acl2_expt" `acl2_expt r i = 
		if zip i = nil then 
	        	(ite (equal (fix r) (num (com_0))) (num (com_0))
                        	 (if less (int 0) i = nil then (mult (reciprocal r) (acl2_expt r (add i (int 1)))) else (mult r (acl2_expt r (add i (unary_minus (int 1)))))))
		else num (com_1)`,
	WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (SND a))))` THEN
	RW_TAC std_ss [] THEN (
		Cases_on `integerp i = t` THENL [
			SUBGOAL_THEN ``?i'. i = int i'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int i` THEN RW_TAC int_ss [INT_OF_SEXP_TO_INT]) THEN
			FULL_SIMP_TAC int_ss [zip_def,INTEGERP_INT,GSYM INT_SUB,GSYM INT_LT,GSYM int_def,common_lisp_equal_def,
				GSYM INT_EQUAL,NIL_REWRITES,SEXP_TO_INT_OF_INT,INT_IFIX,GSYM INT_ADD] THEN
			ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
			RW_TAC std_ss [INT_ABS] THEN 
			FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
			ARITH_TAC,
			FULL_SIMP_TAC int_ss [zip_def,ite_def,equal_def,NIL_REWRITES]])));

val acl2_expt_num = prove(``acl2_numberp (acl2_expt r i) = t``,
	ONCE_REWRITE_TAC [acl2_expt_def] THEN RW_TAC std_ss [ite_def,NIL_REWRITES,ACL2_NUMBERP_MULT,ACL2_NUMBERP_NUM]);

val acl2_expt_correct = prove(``expt r i = sexp_to_com (acl2_expt (num r) (int i))``,
	completeInduct_on `Num (ABS i)` THEN
	RW_TAC std_ss [] THEN
	ONCE_REWRITE_TAC [expt_def,acl2_expt_def] THEN
	RW_TAC int_ss [zip_def,common_lisp_equal_def,GSYM int_def,INTEGERP_INT,FIX_NUM,
			GSYM INT_EQUAL,INT_IFIX,GSYM INT_ADD,GSYM INT_SUB,ite_def,NIL_REWRITES,SEXP_TO_COM_OF_COM,GSYM INT_LT,GSYM COM_EQUAL] THENL [
		PAT_ASSUM ``!a.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (i - 1))``) THEN
		SUBGOAL_THEN ``Num (ABS (i - 1)) < Num (ABS i)`` (fn th => FULL_SIMP_TAC std_ss [th]),
		PAT_ASSUM ``!a.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (i + 1))``) THEN
		SUBGOAL_THEN ``Num (ABS (i + 1)) < Num (ABS i)`` (fn th => FULL_SIMP_TAC std_ss [th])] THEN
	TRY (	ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
		RW_TAC std_ss [INT_ABS] THEN 
		FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
		ARITH_TAC) THENL [
		SUBGOAL_THEN ``?x. acl2_expt (num r) (int (i - 1)) = num x`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
			(Q.EXISTS_TAC `sexp_to_com (acl2_expt (num r) (int (i - 1)))` THEN RW_TAC std_ss [acl2_expt_num,NUM_OF_SEXP_TO_COM]),
		SUBGOAL_THEN ``?x. acl2_expt (num r) (int (i + 1)) = num x`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
			(Q.EXISTS_TAC `sexp_to_com (acl2_expt (num r) (int (i + 1)))` THEN RW_TAC std_ss [acl2_expt_num,NUM_OF_SEXP_TO_COM])] THEN
	ONCE_REWRITE_TAC [prove(``mult a b = mult b a``,Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [mult_def] THEN METIS_TAC [COMPLEX_MULT_COMM])] THEN
	RW_TAC std_ss [GSYM COM_MULT,SEXP_TO_COM_OF_COM,GSYM COM_DIV,COMPLEX_DIV_def] THEN
	METIS_TAC [COMPLEX_MULT_RID,COMPLEX_MULT_COMM,COMPLEX_MULT_ASSOC]);



val ACL2_NUMBERP_INT = prove(``!a. acl2_numberp (int a) = t``,RW_TAC std_ss [acl2_numberp_def,int_def,cpx_def]);

val TO_INT_ZERO = prove(``(nat 0 = int 0) /\ (num com_0 = int 0)``,RW_TAC arith_ss [com_0_def,nat_def,int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def]);

val TO_INT_ONE = prove(``(nat 1 = int 1) /\ (num com_1 = int 1)``,
	RW_TAC arith_ss [com_1_def,nat_def,int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,rat_1_def,frac_1_def]);

val INT_EXP = prove(``int (a ** b) = acl2_expt (int a) (nat b)``,
	Induct_on `b` THEN ONCE_REWRITE_TAC [acl2_expt_def] THEN
	RW_TAC int_ss [nat_def,INTEGERP_INT,ACL2_NUMBERP_INT,equal_def,zip_def,common_lisp_equal_def,GSYM int_def,NIL_REWRITES,int_exp,
		TO_INT_ZERO,TO_INT_ONE,INT_CONG,FIX_NUM] THEN
	RW_TAC int_ss [GSYM INT_LT,GSYM INT_UNARY_MINUS,GSYM INT_ADD,GSYM INT_MULT,BOOL_T,ite_def,GSYM INT_MULT,
		NIL_REWRITES,GSYM int_sub,ARITH_PROVE ``& (SUC a) - 1i = & a``] THEN
	ASSUM_LIST (fn list => REWRITE_TAC (map GSYM (nat_def::list))) THEN
	RW_TAC int_ss [GSYM INT_MULT]);

val NAT_EXP = prove(``nat (a ** b) = acl2_expt (nat a) (nat b)``,RW_TAC int_ss [nat_def,REWRITE_RULE [nat_def] (GSYM INT_EXP)]);

val NATP_EXP = prove(``(natp a = t) /\ (natp b = t) ==> (natp (acl2_expt a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?b'.b = nat b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [GSYM NAT_EXP,NATP_NAT]);

val INTEGERP_EXP = prove(``(integerp a = t) /\ (natp b = t) ==> (integerp (acl2_expt a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = int a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int a` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]) THEN
	SUBGOAL_THEN ``?b'.b = nat b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	RW_TAC std_ss [GSYM INT_EXP,INTEGERP_INT]);


(* DIV *)
	

val (nniq_def,nniq_induction) = Defn.tprove(Defn.Hol_defn "nniq" `nniq a b = (if b <= 0i then 0i else (if a < b then 0 else 1 + nniq (a - b) b))`,
	WF_REL_TAC `measure (\a.Num (FST a))` THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN `0 <= a /\ 0 <= a - b` by ARITH_TAC THEN 
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN ARITH_TAC);

val (acl2_nniq_def,acl2_nniq_ind) = (REWRITE_RULE [GSYM ite_def] ## I) (Defn.tprove(Defn.Hol_defn "acl2_nniq" 
	`acl2_nniq i j = 
		if (equal (nfix j) (int 0)) = nil then (
			if less (ifix i) j = nil then (add (int 1) (acl2_nniq (add i (unary_minus j)) j)) else (int 0)) 
		else (int 0)`,
	WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (FST a))))` THEN
	RW_TAC std_ss [] THEN
	Cases_on `integerp i = t` THENL [
		SUBGOAL_THEN ``?i'.i = int i'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int i` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]),
		FULL_SIMP_TAC std_ss [ifix_def,ite_def,NIL_REWRITES]] THEN
	(Cases_on `natp j = t` THENL [
		SUBGOAL_THEN ``?j'. j = nat j'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat j` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]),
		FULL_SIMP_TAC std_ss [nfix_def,ite_def,NIL_REWRITES]]) THEN
	FULL_SIMP_TAC std_ss [NAT_NFIX,INT_IFIX] THEN
	FULL_SIMP_TAC std_ss [nat_def,GSYM INT_EQUAL,GSYM INT_LT,GSYM INT_SUB,NIL_REWRITES,SEXP_TO_INT_OF_INT] THEN
	TRY (ARITH_TAC) THEN
	ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
		RW_TAC std_ss [INT_ABS] THEN 
		FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
		ARITH_TAC));

val acl2_nniq_int = prove(``integerp (acl2_nniq i j) = t``,
	completeInduct_on `Num (ABS (sexp_to_int i))` THEN
	ONCE_REWRITE_TAC [acl2_nniq_def] THEN RW_TAC std_ss [ite_def,NIL_REWRITES,INTEGERP_INT] THEN
	Cases_on `integerp i = t` THENL [
		SUBGOAL_THEN ``?i'.i = int i'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int i` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]),
		FULL_SIMP_TAC std_ss [ifix_def,ite_def,NIL_REWRITES]] THEN
	(Cases_on `natp j = t` THENL [
		SUBGOAL_THEN ``?j'. j = nat j'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat j` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]),
		FULL_SIMP_TAC std_ss [nfix_def,ite_def,NIL_REWRITES]]) THEN
	FULL_SIMP_TAC std_ss [NAT_NFIX,INT_IFIX] THEN
	FULL_SIMP_TAC std_ss [nat_def,GSYM INT_EQUAL,GSYM INT_LT,GSYM INT_SUB,NIL_REWRITES,SEXP_TO_INT_OF_INT] THENL [
		PAT_ASSUM ``!b.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (i' - & j'))``) THEN
		SUBGOAL_THEN ``Num (ABS (i' - & j')) < Num (ABS i')`` (fn th => FULL_SIMP_TAC std_ss [th]) THEN1
			(ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
			RW_TAC std_ss [INT_ABS] THEN 
			FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
			ARITH_TAC) THEN
		METIS_TAC [SEXP_TO_INT_OF_INT,INTEGERP_ADD,INTEGERP_INT],
		PROVE_TAC [ARITH_PROVE ``~(~(& a = 0i) /\ ~(0i < & a))``]]);


val acl2_nniq_correct = prove(``nniq a b = sexp_to_int (acl2_nniq (int a) (int b))``,
	completeInduct_on `Num (ABS a)` THEN
	ONCE_REWRITE_TAC [nniq_def,acl2_nniq_def] THEN
	RW_TAC std_ss [ite_def,NIL_REWRITES,INT_IFIX,SEXP_TO_INT_OF_INT,GSYM INT_LT] THENL [
		Cases_on `natp (int b) = t` THEN FULL_SIMP_TAC std_ss [nfix_def,ite_def,NIL_REWRITES,natp_def,INTEGERP_INT,nat_def,GSYM INT_LT,GSYM INT_EQUAL],
		PAT_ASSUM ``!b.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (a - b))``) THEN
		SUBGOAL_THEN ``Num (ABS (a - b)) < Num (ABS a)`` (fn th => FULL_SIMP_TAC std_ss [th,GSYM INT_SUB]) THEN1
			(ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
			RW_TAC std_ss [INT_ABS] THEN 
			FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
			ARITH_TAC) THEN
		SUBGOAL_THEN ``?x. acl2_nniq (int (a - b)) (int b) = int x`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
			(Q.EXISTS_TAC `sexp_to_int (acl2_nniq (int (a - b)) (int b))` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT,acl2_nniq_int]) THEN
		RW_TAC std_ss [GSYM INT_ADD,SEXP_TO_INT_OF_INT],
		POP_ASSUM MP_TAC THEN RW_TAC int_ss [nfix_def,ite_def,NIL_REWRITES,GSYM INT_EQUAL,nat_def,natp_def,INTEGERP_INT,GSYM INT_LT]] THEN
	METIS_TAC [NIL_REWRITES,ARITH_PROVE ``~(~(b <= 0) /\ ~(0i < b)) /\ a <= a:int``,ARITH_PROVE ``~(b <= 0 /\ 0i < b)``]);


val acl2_nniq_rewrite = prove(``acl2_nniq (int a) (int b) = int (nniq a b)``,RW_TAC std_ss [acl2_nniq_correct,INT_OF_SEXP_TO_INT,acl2_nniq_int]);

val nniq_correct = prove(``0 <= a /\ 0 <= b /\ ~(b = 0) ==> (a / b = nniq a b)``,
	REPEAT STRIP_TAC THEN 
	Q.SUBGOAL_THEN `?a':num. (a:int = & a')` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `Num a` THEN METIS_TAC [INT_OF_NUM]) THEN
	Q.SUBGOAL_THEN `?b':num. (b:int = & b')` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `Num b` THEN METIS_TAC [INT_OF_NUM]) THEN
	completeInduct_on `a'` THEN ONCE_REWRITE_TAC [nniq_def] THEN RW_TAC int_ss [LESS_DIV_EQ_ZERO] THEN
	FULL_SIMP_TAC int_ss [NOT_LESS,integerTheory.INT_SUB] THEN
	PAT_ASSUM ``!a.P`` (MP_TAC o SPEC ``a' - b':num``) THEN
	RW_TAC int_ss [] THEN POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
	SUBGOAL_THEN ``0 < a' DIV b'`` ASSUME_TAC THEN 
	RW_TAC int_ss [integerTheory.INT_ADD,X_LT_DIV,SIMP_RULE arith_ss [GSYM NOT_LESS] (INST [``q:num`` |-> ``1n``] DIV_SUB)]);

val acl2_floor_def = Define `acl2_floor a b = 
	let q = mult a (reciprocal b) in
	let n = numerator q in
	let d = denominator q in
		ite (equal d (int 1)) n
			(ite (less n (int 0)) 
				(add (unary_minus (acl2_nniq (unary_minus n) d)) (unary_minus (int 1)))
				(acl2_nniq n d))`;

val rat_of_int_def = Define `rat_of_int x = if 0 <= x then & (Num (ABS x)) else rat_ainv (& (Num (ABS x)))`;

val sexp_int_rat = prove(``int a = rat (rat_of_int a)``,
	RW_TAC int_ss [int_def,rat_def,rat_of_int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,RAT_OF_NUM_CALCULATE,
		RAT_AINV_CALCULATE,FRAC_AINV_CALCULATE,ratTheory.RAT_EQ,NMR,DNM,INT_ABS_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN
	ARITH_TAC);

val rat_of_int_nz = prove(``~(b = 0) ==> ~(rat_of_int b = 0)``,
	RW_TAC int_ss [rat_of_int_def,INT_ABS_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),ratTheory.RAT_EQ,
		RAT_OF_NUM_CALCULATE,NMR,DNM,RAT_AINV_CALCULATE,FRAC_AINV_CALCULATE] THEN
	ARITH_TAC);

val nmr_dnm_rewrite = prove(``(numerator (rat a) = int (reduced_nmr a)) /\ (denominator (rat a) = int (reduced_dnm a))``,
	RW_TAC std_ss [numerator_def,denominator_def,rat_def]);


val num_nz = prove(``0 < a ==> ~(Num a = 0)``,
	ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN 
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE] THEN ARITH_TAC);
	
val gcd_less_eq = prove(``!a b. 0 < b ==> (gcd a b <= b)``,
	completeInduct_on `a` THEN ONCE_REWRITE_TAC [gcdTheory.GCD_EFFICIENTLY] THEN RW_TAC arith_ss [] THEN
	Cases_on `a <= b` THEN FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL] THENL [
		PAT_ASSUM ``!a.P`` (MP_TAC o SPEC ``b MOD a``) THEN RW_TAC arith_ss [DIVISION,DECIDE ``~(a = 0n) ==> 0 < a``] THEN
		POP_ASSUM (MP_TAC o SPEC ``a:num``) THEN RW_TAC arith_ss [],
		ONCE_REWRITE_TAC [gcdTheory.GCD_EFFICIENTLY] THEN
		RW_TAC arith_ss [] THEN
		`a MOD b < a` by (MATCH_MP_TAC LESS_TRANS THEN Q.EXISTS_TAC `b` THEN RW_TAC arith_ss [DIVISION]) THEN
		PAT_ASSUM ``!a.P`` (MP_TAC o SPEC ``a MOD b``) THEN RW_TAC arith_ss []]);

val reduced_dnm_pos = prove(``0 < reduced_dnm x``,
	FULL_SIMP_TAC int_ss [reduced_dnm_def] THEN 
	SUBGOAL_THEN ``rep_frac (rep_rat x) = (frac_nmr (rep_rat x),frac_dnm (rep_rat x))`` SUBST_ALL_TAC THEN1 
		RW_TAC std_ss [frac_nmr_def,frac_dnm_def] THEN FULL_SIMP_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] THEN
	RW_TAC int_ss [FRAC_DNMPOS,INT_ABS_CALCULATE_POS,num_nz,gcdTheory.GCD_EQ_0,int_div] THEN
	FULL_SIMP_TAC arith_ss [num_nz,gcdTheory.GCD_EQ_0,DECIDE ``~(0 < a) = (a = 0n)``,FRAC_DNMPOS,X_LT_DIV,gcd_less_eq,DECIDE ``~(a = 0n) ==> 0 < a``]);

val rat_of_int_div_pos1 = prove(``0 < b /\ 0 <= a ==> (rat_of_int a / rat_of_int b = abs_rat (abs_frac (a,b)))``,
	RW_TAC int_ss [rat_ainv_def,frac_ainv_def,rat_div_def,rat_of_int_def,frac_div_def,frac_mul_def,frac_minv_def,RAT_OF_NUM_CALCULATE,ratTheory.RAT_EQ,DNM,NMR] THEN
	RAT_CONG_TAC THEN
	`!a. 0 < ABS (& (Num (ABS b)) * frac_dnm a)` by 
		RW_TAC int_ss [FRAC_DNMPOS,INT_ABS_CALCULATE_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE,INT_MUL_POS_SIGN] THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_MUL_POS_SIGN,frac_sgn_def] THEN
	RW_TAC std_ss [FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM] THEN
	RW_TAC int_ss [INT_ABS,SGN_def,FRAC_DNMPOS,INT_LT_IMP_NE,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN 
	TRY (PAT_ASSUM ``!a.P`` (K ARITH_TAC)) THEN
	METIS_TAC [num_nz]);

val rat_of_int_neg = prove(``rat_of_int ~x = ~rat_of_int x``,
	RW_TAC std_ss [rat_of_int_def] THEN TRY (`x = 0` by ARITH_TAC) THEN RW_TAC int_ss [RAT_AINV_0,RAT_AINV_AINV,INT_ABS_NEG]);

val rat_of_int_div_pos = prove(``0 < b ==> (rat_of_int a / rat_of_int b = abs_rat (abs_frac (a,b)))``,
	Cases_on `0 <= a` THEN RW_TAC std_ss [rat_of_int_div_pos1] THEN
	`?c. (a = ~c) /\ 0 <= c` by (Q.EXISTS_TAC `~a` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
	RW_TAC int_ss [rat_of_int_neg,GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV,RAT_DIV_MULMINV,GSYM RAT_AINV_LMUL] THEN
	RW_TAC int_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos1]);

val rat_of_int_div_neg = prove(``b < 0 ==> (rat_of_int a / rat_of_int b = abs_rat (abs_frac (~a,~b)))``,
	DISCH_TAC THEN
	`?c. (b = ~c) /\ 0 < c` by (Q.EXISTS_TAC `~b` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
	RW_TAC int_ss [rat_of_int_neg,RAT_DIV_MULMINV,GSYM RAT_AINV_RMUL,GSYM RAT_AINV_MINV,rat_of_int_nz,INT_LT_IMP_NE,
		GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV] THEN
	RW_TAC std_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos]);

open dividesTheory gcdTheory;

val coprime_equal = prove(``(gcd a d = 1) /\ (gcd b c = 1) /\ (a * b = c * d) ==> (a = c) /\ (b = d)``,
	REPEAT STRIP_TAC THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (prove(``(a * b = c) ==> divides a c /\ divides b c``,METIS_TAC [divides_def,MULT_COMM]))) THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (prove(``(a * b = c) ==> divides a c /\ divides b c``,METIS_TAC [divides_def,MULT_COMM])) o GSYM) THEN
	METIS_TAC [L_EUCLIDES,GCD_SYM,MULT_COMM,DIVIDES_ANTISYM]);


val num_abs_nz = prove(``0 < b \/ ~(b = 0) ==> ~(Num (ABS b) = 0)``,
	DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_ABS_POS] THEN
	ARITH_TAC);

val r1 = prove(``a < 0 ==> (a = ~& (Num ~a))``,METIS_TAC [INT_NEG_GT0,INT_OF_NUM,INT_LT_IMP_LE,INT_NEG_EQ]);
val r2 = prove(``0 < a ==> (a = & (Num a))``,METIS_TAC [INT_NEG_GT0,INT_OF_NUM,INT_LT_IMP_LE]);

val FACTOR_GCD2 = prove(``!n m. ~(n = 0) /\ ~(m = 0) ==> ?p q. (n = p * gcd n m) /\ (m = q * gcd n m) /\ (gcd p q = 1) /\ ~(gcd n m = 0)``,
	RW_TAC std_ss [FACTOR_OUT_GCD,GCD_EQ_0]);


fun find_gcd term = 
	if can (match_term ``gcd a b``) term then [term] else
	(op@ o (find_gcd ## find_gcd)) (dest_comb term) handle _ => [];

fun GCD_FACTOR_GOAL (assums,goal) =
let	val match =  PART_MATCH (fst o dest_eq o dest_neg o last o strip_conj o snd o dest_exists o snd o dest_exists o snd o dest_imp) FACTOR_GCD2 in
(MAP_EVERY (fn x => (STRIP_ASSUME_TAC (SIMP_RULE std_ss (map ASSUME assums) (match x)))) (mk_set (find_gcd goal))) (assums,goal)
end;




val reduce_thm = prove(``0 < b /\ 0 < y /\ ((0 < a /\ 0 < x) \/ (x < 0 /\ a < 0)) /\ (x * b = a * y) ==> 
				(x / & (gcd (Num (ABS x)) (Num (ABS y))) = a / & (gcd (Num (ABS a)) (Num (ABS b)))) /\
				(y / & (gcd (Num (ABS x)) (Num (ABS y))) = b / & (gcd (Num (ABS a)) (Num (ABS b))))``,
	REPEAT STRIP_TAC THEN
	FULL_SIMP_TAC int_ss [num_abs_nz,GCD_EQ_0,INT_DIV_0] THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	FULL_SIMP_TAC std_ss [INT_NEG_LT0,GSYM INT_NEG_GT0,INT_LT_CALCULATE,GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,
		DECIDE ``0 < a = ~(a = 0n)``,INT_ABS_NEG,NUM_OF_INT,INT_ABS_NUM,INT_NEG_MUL2,INT_MUL,INT_EQ_CALCULATE] THEN
	GCD_FACTOR_GOAL THEN
	ASSUM_LIST (fn list => GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o DEPTH_CONV) (bool_rewrites) list) THEN
	RW_TAC std_ss [INT_DIV_RMUL,GSYM INT_MUL,INT_NEG_LMUL,INT_EQ_CALCULATE,ARITH_PROVE ``~(a = 0) ==> ~(& a = 0i)``] THEN
	PAT_ASSUM ``a * b = c * d:num`` MP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
	ONCE_REWRITE_TAC [prove(``(a * b * (c * d) = e * d * (g * b)) = (b * (d * (a * c)) = b * (d * (e * g:num)))``,
		HO_MATCH_MP_TAC (PROVE [] ``(a = c) /\ (b = d) ==> (f a b = f c d)``) THEN CONJ_TAC THEN CONV_TAC (AC_CONV (MULT_ASSOC,MULT_COMM)))] THEN
	RW_TAC std_ss [EQ_MULT_LCANCEL] THEN
	METIS_TAC [coprime_equal,GCD_SYM]);


val neg_reduce_rat = prove(``b < 0 ==> (reduce (rep_frac (rep_rat (rat_of_int a / rat_of_int b))) = reduce (~a,~b))``,
	RW_TAC int_ss [rat_of_int_div_neg,rat_of_int_div_pos] THEN
	RAT_CONG_TAC THEN
	POP_ASSUM MP_TAC THEN RW_TAC int_ss [NMR,DNM,snd(EQ_IMP_RULE(SPEC_ALL INT_NEG_GT0))] THEN
	(SUBGOAL_THEN ``rep_frac x = (frac_nmr x,frac_dnm x)`` SUBST_ALL_TAC THEN1 RW_TAC std_ss [frac_nmr_def,frac_dnm_def]) THEN
	RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] THEN
	`(0 < frac_nmr x /\ a < 0) \/ (frac_nmr x < 0 /\ 0 < a) \/ ((frac_nmr x = 0) /\ (a = 0))` by (
		`frac_nmr x < 0 \/ (frac_nmr x = 0) \/ 0 < frac_nmr x` by ARITH_TAC THEN `a < 0 \/ (a = 0) \/ 0 < a` by ARITH_TAC THEN 
		FULL_SIMP_TAC int_ss [INT_NEG_0,FRAC_DNMPOS,INT_LT_IMP_NE] THEN METIS_TAC [INT_MUL_SIGN_CASES,INT_NEG_GT0,FRAC_DNMPOS,INT_LT_TRANS,INT_LT_IMP_NE]) THEN
	RW_TAC int_ss [INT_DIV_0,num_abs_nz,INT_NEG_GT0,GCD_0L,GCD_0R,FRAC_DNMPOS] THEN
	FIRST [	MATCH_MP_TAC (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL (SPEC_ALL reduce_thm)))),
		MATCH_MP_TAC (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL (SPEC_ALL reduce_thm)))),ALL_TAC] THEN
	RW_TAC int_ss [FRAC_DNMPOS,INT_NEG_GT0,INT_ABS_CALCULATE_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE,INT_LT_IMP_NE,INT_DIV_ID]);

val pos_reduce_rat = prove(``0 < b ==> (reduce (rep_frac (rep_rat (rat_of_int a / rat_of_int b))) = reduce (a,b))``,
	RW_TAC int_ss [rat_of_int_div_neg,rat_of_int_div_pos] THEN
	RAT_CONG_TAC THEN
	POP_ASSUM MP_TAC THEN RW_TAC int_ss [NMR,DNM,snd(EQ_IMP_RULE(SPEC_ALL INT_NEG_GT0))] THEN
	(SUBGOAL_THEN ``rep_frac x = (frac_nmr x,frac_dnm x)`` SUBST_ALL_TAC THEN1 RW_TAC std_ss [frac_nmr_def,frac_dnm_def]) THEN
	RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] THEN
	`(0 < frac_nmr x /\ 0 < a) \/ (frac_nmr x < 0 /\ a < 0) \/ ((frac_nmr x = 0) /\ (a = 0))` by (
		`frac_nmr x < 0 \/ (frac_nmr x = 0) \/ 0 < frac_nmr x` by ARITH_TAC THEN `a < 0 \/ (a = 0) \/ 0 < a` by ARITH_TAC THEN 
		FULL_SIMP_TAC int_ss [INT_NEG_0,FRAC_DNMPOS,INT_LT_IMP_NE] THEN METIS_TAC [INT_MUL_SIGN_CASES,INT_NEG_GT0,FRAC_DNMPOS,INT_LT_TRANS,INT_LT_IMP_NE]) THEN
	RW_TAC int_ss [INT_DIV_0,num_abs_nz,INT_NEG_GT0,GCD_0L,GCD_0R,FRAC_DNMPOS] THEN
	FIRST [	MATCH_MP_TAC (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL (SPEC_ALL reduce_thm)))),
		MATCH_MP_TAC (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL (SPEC_ALL reduce_thm)))),ALL_TAC] THEN
	RW_TAC int_ss [FRAC_DNMPOS,INT_NEG_GT0,INT_ABS_CALCULATE_POS,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE,INT_LT_IMP_NE,INT_DIV_ID]);


val mod_common = prove(``0 < b /\ 0 < c ==> ((a MOD b = 0) = ((a * c) MOD (b * c) = 0))``,
	REPEAT STRIP_TAC THEN EQ_TAC THEN
	RW_TAC arith_ss [CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) (GSYM MOD_COMMON_FACTOR)]);

val int_div_common = prove(``~(b = 0) /\ ~(c = 0i) ==> (a * & b / (c * & b) = a / c)``,
	REPEAT STRIP_TAC THEN `(a < 0 \/ (a = 0) \/ 0 < a) /\ (c < 0 \/ 0 < c)` by ARITH_TAC THEN 
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	FULL_SIMP_TAC std_ss [INT_NEG_LT0,GSYM INT_NEG_GT0,INT_LT_CALCULATE,GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,
		DECIDE ``0 < a = ~(a = 0n)``,INT_ABS_NEG,NUM_OF_INT,INT_ABS_NUM,INT_NEG_MUL2,INT_MUL,INT_EQ_CALCULATE,INT_DIV_NEG,INT_NEGNEG,INT_DIV,ZERO_DIV] THEN
	RW_TAC int_ss [int_div] THEN
	FULL_SIMP_TAC arith_ss [ZERO_DIV,DECIDE ``~(0 < a) = (a = 0n)``,GSYM (CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) DIV_DIV_DIV_MULT),MULT_DIV] THEN
	METIS_TAC [mod_common,DECIDE ``0 < a = ~(a = 0n)``]);

val mod_zero_mult = prove(``0 < b ==> ((a MOD b = 0) = (b = 1) \/ (?c. a = b * c))``,
	REPEAT STRIP_TAC THEN EQ_TAC THENL [
		Cases_on `b = 1n` THEN RW_TAC arith_ss [] THEN
		ASSUM_LIST (fn list => SUBST_ALL_TAC (SIMP_RULE arith_ss list (DISCH_ALL (CONJUNCT1 (SPEC ``a:num`` (UNDISCH (SPEC ``b:num`` DIVISION))))))),
		ALL_TAC] THEN
	METIS_TAC [MOD_1,MOD_EQ_0,MULT_COMM]);

val gcd_mod = prove(``~(p = q) /\ 1 < q /\ ~(p = 0) /\ ~(q = 0) /\ (gcd p q = 1) ==> ~(p MOD q = 0)``,
	RW_TAC arith_ss [mod_zero_mult] THEN
	CCONTR_TAC THEN FULL_SIMP_TAC arith_ss [] THEN POP_ASSUM SUBST_ALL_TAC THEN
	RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ONCE_REWRITE_RULE [GCD_SYM] GCD_EFFICIENTLY]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC arith_ss [ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0,GCD_0R]);


val INT_DIV = prove(``~(b = 0i) ==> (int (a / b) = acl2_floor (int a) (int b))``,
	RW_TAC (std_ss ++ boolSimps.LET_ss) [acl2_floor_def,ite_def,NIL_REWRITES] THEN
	FULL_SIMP_TAC std_ss [sexp_int_rat,rat_of_int_nz,nmr_dnm_rewrite,GSYM RAT_DIV] THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [sexp_int_rat,rat_of_int_nz,nmr_dnm_rewrite,GSYM RAT_DIV] THEN
	FULL_SIMP_TAC std_ss [GSYM sexp_int_rat,acl2_nniq_rewrite,GSYM INT_UNARY_MINUS,GSYM INT_ADD,GSYM INT_EQUAL,GSYM INT_LT,NIL_REWRITES,INT_NOT_LT] THEN
	FULL_SIMP_TAC int_ss [INT_NOT_LE] THEN RW_TAC int_ss [GSYM nniq_correct,reduced_dnm_pos,ARITH_PROVE ``0 < a ==> 0 <= a /\ ~(a = 0i)``,
		REWRITE_RULE [INT_NEG_GE0] (GSYM (INST [``a:int`` |-> ``~a:int``] nniq_correct)),INT_LT_IMP_LE] THEN
	FULL_SIMP_TAC std_ss [reduced_nmr_def,reduced_dnm_def] THEN
	`0 < b \/ b < 0` by ARITH_TAC THEN
	FULL_SIMP_TAC std_ss [pos_reduce_rat,neg_reduce_rat] THEN AP_TERM_TAC THEN 
	FULL_SIMP_TAC (std_ss ++ boolSimps.LET_ss) [reduce_def,INT_ABS_NEG] THEN
	`0 < a \/ (a = 0) \/ a < 0` by ARITH_TAC THEN
	FULL_SIMP_TAC int_ss [num_abs_nz,GCD_EQ_0,INT_DIV_0,ARITH_PROVE ``(0 < a ==> (ABS a = a)) /\ (a < 0 ==> (ABS a = ~a))``] THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	FULL_SIMP_TAC int_ss [DECIDE ``0 < a = ~(a = 0n)``,GCD_0L,GCD_0R,ZERO_DIV] THEN 
	GCD_FACTOR_GOAL THEN
	ASSUM_LIST (fn list => REWRITE_TAC (map (AP_TERM ``int_of_num``) (filter (can (AP_TERM ``int_of_num``)) list))) THEN
	Cases_on `q = 0` THEN FULL_SIMP_TAC int_ss [GCD_0L,GCD_0R] THEN
	RW_TAC int_ss [MULT_DIV,int_div,GCD_EQ_0,ZERO_DIV,MOD_EQ_0,GSYM (ONCE_REWRITE_RULE [MULT_COMM] DIV_DIV_DIV_MULT)] THEN
	FULL_SIMP_TAC int_ss [] THEN
	FIRST [
		Cases_on `q = 1` THEN1 METIS_TAC [DIVMOD_ID,GCD_EQ_0,DECIDE ``0 < a = ~(a = 0n)``,MULT_LEFT_1] THEN
		Cases_on `p = q` THEN1 METIS_TAC [GCD_REF],
		`q = 1` by METIS_TAC [MULT_DIV,DECIDE ``0 < a = ~(a = 0n)``] THEN
		METIS_TAC [MULT_DIV,MULT_LEFT_1,DECIDE ``0 < a = ~(a = 0n)``,DIV_1,MOD_EQ_0]] THEN
	METIS_TAC [DIV_DIV_DIV_MULT,MULT_COMM,MULT_DIV,DECIDE ``~(a = 0n) = 0 < a``,mod_common,GCD_EQ_0,gcd_mod,DECIDE ``1 < a = ~(a = 0n) /\ ~(a = 1n)``]);

val NAT_DIV = prove(``~(b = 0n) ==> (nat (a DIV b) = acl2_floor (nat a) (nat b))``,RW_TAC int_ss [nat_def,GSYM INT_DIV]);

val MULT_ZERO = prove(``mult a (num com_0) = int 0``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_floor_def,int_def,cpx_def,sexpTheory.rat_def,mult_def,GSYM com_0_def,GSYM rat_0_def,GSYM frac_0_def] THEN
	Cases_on `c` THEN RW_TAC std_ss [COMPLEX_MULT_def,com_0_def,rat_0_def,GSYM rat_0,RAT_MUL_RZERO,RAT_SUB_RID,RAT_ADD_RID]);

val FLOOR_ZERO = prove(``acl2_floor a (int 0) = int 0``,
	RW_TAC (std_ss ++ boolSimps.LET_ss) [acl2_floor_def,
		prove(``int 0 = num com_0``,RW_TAC std_ss [cpx_def,int_def,sexpTheory.rat_def,com_0_def,GSYM rat_0_def,GSYM frac_0_def]),reciprocal_def,MULT_ZERO] THEN
	RW_TAC (std_ss ++ boolSimps.LET_ss) [com_0_def,denominator_def,numerator_def,reduced_dnm_def,reduced_nmr_def,reduce_def,rat_0_def,frac_0_def] THEN
	RAT_CONG_TAC THEN FULL_SIMP_TAC int_ss [DNM,NMR] THEN
	SUBGOAL_THEN ``rep_frac x = (0,frac_dnm x)`` SUBST_ALL_TAC THEN1 (METIS_TAC [frac_dnm_def,frac_nmr_def,pairTheory.PAIR]) THEN
	RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def,FRAC_DNMPOS,gcdTheory.GCD_0L,gcdTheory.GCD_0R,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),
		INT_LT_IMP_LE,INT_ABS_CALCULATE_POS,INT_DIV_0,INT_LT_IMP_NE,equal_def,ite_def,NIL_REWRITES] THEN
	RW_TAC std_ss [int_def,cpx_def,sexpTheory.rat_def]);

val INTEGERP_DIV = prove(``(integerp a = t) /\ (integerp b = t) ==> (integerp (acl2_floor a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = int a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int a` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]) THEN
	SUBGOAL_THEN ``?b'.b = int b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int b` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]) THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_DIV,INTEGERP_INT,FLOOR_ZERO]);

val NATP_DIV = prove(``(natp a = t) /\ (natp b = t) ==> (natp (acl2_floor a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?b'.b = nat b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	Cases_on `b' = 0` THENL [
		RW_TAC std_ss [nat_def,FLOOR_ZERO],
		RW_TAC std_ss [GSYM NAT_DIV,NATP_NAT]] THEN
	RW_TAC std_ss [GSYM nat_def,NATP_NAT]);
		




(* MOD *)

val acl2_mod_def = Define `acl2_mod x y = add x (unary_minus (mult (acl2_floor x y) y))`;

val INT_MOD = prove(``~(b = 0i) ==> (int (a % b) = acl2_mod (int a) (int b))``,
	RW_TAC int_ss [acl2_mod_def,GSYM INT_DIV,GSYM INT_MULT,GSYM INT_UNARY_MINUS,GSYM INT_ADD,int_mod,int_sub]);

val INTEGERP_MOD = prove(``(integerp a = t) /\ (integerp b = t) ==> (integerp (acl2_mod a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = int a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int a` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]) THEN
	SUBGOAL_THEN ``?b'.b = int b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_int b` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT]) THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_MOD,INTEGERP_INT] THEN
	RW_TAC std_ss [FLOOR_ZERO,acl2_mod_def] THEN
	FULL_SIMP_TAC std_ss [unary_minus_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,com_0_def,GSYM frac_0_def,GSYM rat_0,rat_0_def,
		COMPLEX_MULT_def,COMPLEX_SUB_def,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID,add_def,COMPLEX_ADD_def,nat_def]);

val NAT_MOD = prove(``~(b = 0n) ==> (nat (a MOD b) = acl2_mod (nat a) (nat b))``,RW_TAC int_ss [nat_def,GSYM INT_MOD]);

val NATP_MOD = prove(``(natp a = t) /\ (natp b = t) ==> (natp (acl2_mod a b) = t)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?b'.b = nat b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	Cases_on `b' = 0` THENL [
		RW_TAC std_ss [nat_def,FLOOR_ZERO,acl2_mod_def],
		RW_TAC std_ss [GSYM NAT_MOD,NATP_NAT]] THEN
	FULL_SIMP_TAC std_ss [unary_minus_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,com_0_def,GSYM frac_0_def,GSYM rat_0,rat_0_def,
		COMPLEX_MULT_def,COMPLEX_SUB_def,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID,add_def,COMPLEX_ADD_def,nat_def]);

(* EVEN and ODD *)

val NAT_EVEN = prove(``bool (EVEN a) = equal (acl2_mod (nat a) (nat 2)) (nat 0)``,
	RW_TAC std_ss [GSYM NAT_MOD,GSYM NAT_EQUAL,NIL_REWRITES,mod_zero_mult] THEN AP_TERM_TAC THEN
	METIS_TAC [EVEN_EXISTS,EVEN_DOUBLE]);

val NAT_ODD = prove(``bool (ODD a) = equal (acl2_mod (nat a) (nat 2)) (nat 1)``,
	RW_TAC std_ss [GSYM NAT_MOD,GSYM NAT_EQUAL,NIL_REWRITES,not_def,ite_def] THEN AP_TERM_TAC THEN
	`?n. (a = n * 2) \/ (a = SUC (n * 2))` by (Q.EXISTS_TAC `a DIV 2` THEN RW_TAC arith_ss [] THEN
		DISJ_CASES_TAC (SPEC ``a:num`` EVEN_OR_ODD) THEN IMP_RES_TAC EVEN_ODD_EXISTS THEN
		RW_TAC arith_ss [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,ADD1,ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]) THEN
	RW_TAC arith_ss [MOD_EQ_0,GSYM EVEN_ODD,ONCE_REWRITE_RULE [MULT_COMM] EVEN_DOUBLE,ONCE_REWRITE_RULE [MULT_COMM] ODD_DOUBLE] THEN
	RW_TAC arith_ss [MOD_TIMES,ADD1]);

(* EXP 2 *)

val acl2_ash_def = Define `acl2_ash i c = acl2_floor (mult (ifix i) (acl2_expt (int 2) c)) (int 1)`;

val NAT_ASL = prove(``nat (i * 2 ** c) = acl2_ash (nat i) (nat c)``,
	RW_TAC int_ss [acl2_ash_def,nat_def,GSYM INT_EXP,GSYM INT_MULT,ifix_def,ite_def,NIL_REWRITES,INTEGERP_INT,GSYM INT_DIV]);

val INT_ASL = prove(``int (i * 2 ** c) = acl2_ash (int i) (nat c)``,
	RW_TAC int_ss [acl2_ash_def,nat_def,GSYM INT_EXP,GSYM INT_MULT,ifix_def,ite_def,NIL_REWRITES,INTEGERP_INT,GSYM INT_DIV]);


(* Export necessary theorems *)

val MK_THMS = LIST_CONJ o (map GEN_ALL);


val NAT_THMS = save_thm("NAT_THMS",
	MK_THMS [	NAT_OF_SEXP_TO_NAT,NAT_EQUAL_0,NAT_EQUAL,NAT_0_LT,NAT_LT,NAT_LE,NAT_GE,NAT_GT,
			NAT_ADD,NAT_SUC,NAT_MULT,NAT_SUB,NAT_EXP,NAT_DIV,NAT_MOD,NAT_EVEN,NAT_ODD]);

val INT_THMS = save_thm("INT_THMS",
	MK_THMS [	INT_OF_SEXP_TO_INT,INT_EQUAL,INT_LT,INT_LE,INT_GE,INT_GT,
			INT_ADD,INT_MULT,INT_UNARY_MINUS,INT_SUB,INT_EXP,INT_DIV,INT_MOD]);

val RAT_THMS = save_thm("RAT_THMS",
	MK_THMS [	RAT_OF_SEXP_TO_RAT,RAT_EQUAL,RAT_LT,RAT_LE,RAT_GE,RAT_GT,
			RAT_ADD,RAT_MULT,RAT_UNARY_MINUS,RAT_DIV,RAT_SUB]);

val COM_THMS = save_thm("COM_THMS",
	MK_THMS [	NUM_OF_SEXP_TO_COM,COM_EQUAL,COM_LT,COM_LE,COM_GE,COM_GT,
			COM_ADD,COM_MULT,COM_UNARY_MINUS,COM_DIV,COM_SUB]);

val BOOL_THMS = save_thm("BOOL_THMS",
	MK_THMS [	BOOL_OF_SEXP_TO_BOOL,BOOL_AND,BOOL_OR,BOOL_IMPLIES,BOOL_NOT,BOOL_EQ,BOOL_T,BOOL_F]);

val LIST_THMS = save_thm("LIST_THMS",
	MK_THMS [	LIST_OF_SEXP_TO_LIST,LIST_CONS,LIST_NIL,LIST_HD,LIST_TL]);

val PAIR_THMS = save_thm("PAIR_THMS",
	MK_THMS [	PAIR_OF_SEXP_TO_PAIR,PAIR_COMMA,PAIR_FST,PAIR_SND]);


val JUDGEMENT_THMS = save_thm("JUDGEMENT_THMS",
	MK_THMS [	NATP_NAT,INTEGERP_INT,RATIONALP_RAT,ACL2_NUMBERP_NUM,BOOLEANP_BOOL,CONSP_PAIR,
			NATP_ADD,NATP_NFIX,NATP_MULT,NATP_DIV,NATP_EXP,NATP_MOD,
			BOOLEANP_EQUAL,BOOLEANP_LESS,BOOLEANP_NOT,BOOLEANP_CONSP,BOOLEANP_IF,
			INTEGERP_ADD,INTEGERP_MULT,INTEGERP_DIV,INTEGERP_UNARY_MINUS,INTEGERP_MOD,
			RATIONALP_ADD,RATIONALP_MULT,RATIONALP_RECIPROCAL,RATIONALP_UNARY_MINUS,
			ACL2_NUMBERP_ADD,ACL2_NUMBERP_MULT,ACL2_NUMBERP_RECIPROCAL,ACL2_NUMBERP_UNARY_MINUS,
			LISTP_TAIL,LISTP_HEAD,LISTP_CONS_HT,LISTP_CONS]);


(* One to one theorems *)

val NAT_11 = store_thm("NAT_11",
	``(nat a = nat b) ==> (a = b)``,
	RW_TAC std_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def] THEN RAT_CONG_TAC THEN FULL_SIMP_TAC int_ss [NMR,DNM]);

val LIST_11 = prove(``(ONE_ONE f ==> ONE_ONE (list f))``,
	RW_TAC std_ss [ONE_ONE_THM] THEN
	measureInduct_on `LENGTH (x1 ++ x2)` THEN
	Cases_on `x1` THEN Cases_on `x2` THEN
	RW_TAC std_ss [list_def,nil_def] THEN
	METIS_TAC [listTheory.LENGTH_APPEND,listTheory.LENGTH,DECIDE ``a + b < SUC a + SUC b``]);

val ENCODE_ONE_ONE = store_thm("ENCODE_ONE_ONE",
	``	ONE_ONE nat /\ ONE_ONE int /\ ONE_ONE rat /\ ONE_ONE num /\ ONE_ONE bool /\
		(ONE_ONE f /\ ONE_ONE g ==> ONE_ONE (pair f g)) /\ (ONE_ONE f ==> ONE_ONE (list f))``,
	RW_TAC std_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,rat_def,ONE_ONE_THM,pair_def,LIST_11,bool_def] THEN RAT_CONG_TAC THEN FULL_SIMP_TAC int_ss [NMR,DNM] THEN
	Cases_on `x1` THEN Cases_on `x2` THEN FULL_SIMP_TAC std_ss [pairTheory.FST,pairTheory.SND,bool_def,nil_def,t_def] THEN 
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss []);

(* bool theorems for judgement rewrites *)

val boolp_eq = prove(``!x. (booleanp x = t) ==> (bool (x = t) = x)``,RW_TAC std_ss [booleanp_def,bool_def,ite_def,NIL_REWRITES,equal_def]);

val BOOLP_THMS = store_thm("BOOLP_THMS",``
	(!n. bool (natp n = t) = natp n) /\ (!n. bool (integerp n = t) = integerp n) /\ (!n. bool (rationalp n = t) = rationalp n) /\
	(!n. bool (acl2_numberp n = t) = acl2_numberp n) /\ (!n. bool (consp n = t) = consp n) /\ (!n. bool (booleanp n = t) = booleanp n)``,
	REPEAT STRIP_TAC THEN MATCH_MP_TAC boolp_eq THEN	
	Cases_on `n` THEN REPEAT (
		RW_TAC std_ss [booleanp_def,natp_def,integerp_def,rationalp_def,acl2_numberp_def,consp_def,NIL_REWRITES,ite_def,equal_def] THEN 
		REPEAT (POP_ASSUM MP_TAC)));

val _ = export_theory();






