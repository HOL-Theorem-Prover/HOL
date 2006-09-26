(*****************************************************************************)
(* File: translateScript.sml                                                 *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Provides theories and definitions for conversion between s-expressions    *)
(* and native HOL                                                            *)
(*****************************************************************************)

(* A brief changelog *)

(* 	17/05/2006:	Added LISTP_CONS function              *)
(* 	04/07/2006:	Switched to hol_defaxiomsTheory (MJCG) *)
(* 	03/08/2006:	Various improvements:                  
		        switched to |= instead of =t/nil
			added case & 'flat' theorems
			created translateLib for CHOOSEP *)
(* 	14/08/2006:	Changed NAT_CASE to use PRE (which uses ~(n = 0)) *) 
(*	15/08/2006:	Added NAT_SUC_PRE because (SUC (PRE a)) is a common, resolvable, 
			term in many function definitions *)
(* 	28/08/2006:	Exported some additional theorems (MJCG) *)
(*	17/09/2006:	Definitions renamed to match ACL2 and are now checked on compile *)
(*	19/09/2006:	Many new list definitions added, plus max/min and odd/even *)
(*	21/09/2006:	Added quot/rem/sgn from integer using TRUNCATE and REM
			Added typing judgements for the new acl2 functions *)
(*	22/09/2006:	Definitions now checked one by one to avoid 'couldn't protect' error
			String and character conversions implemented *)

(*****************************************************************************)
(* Load files for interactive sessions                                       *)
(*****************************************************************************)

(*
val _ = app                                   (* load infrastructure         *)
 load 
 ["sexp",
  "sexpTheory",
  "hol_defaxiomsTheory",
  "intLib","listLib","translateLib"];
*)

(*****************************************************************************)
(* Locations of ACL2 executable and output .lisp script                      *)
(*****************************************************************************)

val acl2_test_file = (FileSys.fullPath "../lisp") ^ "/native";
val acl2_executable = "acl2";

(*****************************************************************************)
(* Load base theories                                                        *)
(*****************************************************************************)

open sexp sexpTheory arithmeticTheory fracTheory ratTheory integerTheory intLib 
     complex_rationalTheory intExtensionTheory
     hol_defaxiomsTheory rich_listTheory listTheory translateLib;

(*****************************************************************************)
(* Start new theory "translate"                                              *)
(*****************************************************************************)
val _ = new_theory "translate";

(*****************************************************************************)
(* Extra ACL2 definitions required for natural number encoding               *)
(*****************************************************************************)

val natp_def = acl2Define "ACL2::NATP" 
			`natp a = (ite (integerp a) (ite (less (nat 0) a) t (ite (equal (nat 0) a) t nil)) nil)`;

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
(* Inverse to ``chr : char -> sexp``                                         *)
(* Inverse to ``str : string -> sexp``                                       *)
(*****************************************************************************)

val sexp_to_com_def = 
 Define 
  `(sexp_to_com (num a) = a) /\ (sexp_to_com _ = com_0)`;

val sexp_to_int_def = 
 Define 
  `(sexp_to_int (num (com a b)) = if |= integerp (num (com a b)) then (rat_nmr a) / (rat_dnm a) else 0) /\ (sexp_to_int _ = 0)`;

val sexp_to_nat_def = 
 Define 
  `sexp_to_nat a = if |= natp a then Num (sexp_to_int a) else 0`;

val sexp_to_rat_def = 
 Define 
  `(sexp_to_rat (num (com a b)) = if |= rationalp (num (com a b)) then a else 0) /\ (sexp_to_rat _ = 0)`;

val sexp_to_bool_def = Define `sexp_to_bool x = |= x`;

val sexp_to_char_def = Define `(sexp_to_char (chr x) = x) /\ (sexp_to_char _ = #"a")`;

val sexp_to_string_def = Define `(sexp_to_string (str x) = x) /\ (sexp_to_string _ = "a")`;

(*****************************************************************************)
(* Encoding and decoding pairs                                               *)
(*                                                                           *)
(* pair         : ('a -> sexp) -> ('b -> sexp) -> ('a # 'b) -> sexp          *)
(* sexp_to_pair : (sexp -> 'a) -> (sexp -> 'a) -> sexp -> ('a # 'b)          *)
(* pairp        : (sexp -> [t/nil]) -> (sexp -> [t/nil]) -> sexp -> [t/nil]  *)
(*                                                                           *)
(* Eg: 	    pair nat int (1,2) = cons (nat 1) (int 2)                        *)
(*      and pairp natp integerp (cons (nat 1) (int 2) = t                    *)
(*****************************************************************************)

val pair_def = Define `pair f g p = cons (f (FST p)) (g (SND p))`;

val pairp_def = Define `(pairp l r (cons a b) = ite (l a) (r b) nil) /\ (pairp l r x = nil)`;

val sexp_to_pair_def = Define `(sexp_to_pair f g (cons a b) = (f a,g b)) /\ (sexp_to_pair f g _ = ARB)`;

(*****************************************************************************)
(* Encoding and decoding lists                                               *)
(*                                                                           *)
(* list         : ('a -> sexp) -> 'a list -> sexp                            *)
(* sexp_to_list : (sexp -> 'a) -> sexp -> 'a list                            *)
(* listp        : (sexp -> [t/nil]) -> sexp -> [t/nil]                       *)
(*                                                                           *)
(* Eg: 	   list nat [1;2;3] = cons (nat 1) (cons (nat 2) (cons (nat 3) nil)) *)
(*     and listp natp (cons (nat 1) (cons (nat 2) (cons (nat 3) nil))) = t   *)
(*****************************************************************************)

val list_def = Define `(list f (x::xs) = cons (f x) (list f xs)) /\ (list f [] = nil)`;

val listp_def = Define `(listp l (cons a b) = ite (l a) (listp l b) nil) /\ (listp l x = equal x nil)`;

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
	EVERY_ASSUM (fn th => (ASSUME_TAC o REWRITE_RULE [RAT] o AP_TERM ``abs_rat``)
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

val IS_INT_select = prove(``!a b. IS_INT (com a b) ==> (b = rat_0) /\ ?c. a = abs_rat (abs_frac(c,1))``,
	RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,
		INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_MOD_EQ0,INT_LT_IMP_NE] THEN
	Q.EXISTS_TAC `rat_nmr a / rat_dnm a` THEN
	SUBGOAL_THEN ``?a'. a  = abs_rat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
		(Q.EXISTS_TAC `rep_rat a` THEN MATCH_ACCEPT_TAC (GSYM ratTheory.RAT)) THEN
	RW_TAC int_ss [rat_nmr_def,rat_dnm_def,RAT_EQ,DNM,NMR,INT_LT_01,INT_DIV_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE] THEN
	SUBGOAL_THEN ``?c d. (a' = abs_frac (c,d)) /\ 0 < d`` STRIP_ASSUME_TAC THEN1
		(Q.EXISTS_TAC `frac_nmr a'` THEN Q.EXISTS_TAC `frac_dnm a'` THEN REWRITE_TAC [FRAC,FRAC_DNMPOS]) THEN
	RW_TAC std_ss [NMR,DNM] THEN
	RAT_CONG_TAC THEN
	PAT_ASSUM ``0i < d`` (fn th => (RULE_ASSUM_TAC (SIMP_RULE std_ss [th,NMR,DNM]))) THEN
	PAT_ASSUM ``frac_nmr a = b * c:int`` SUBST_ALL_TAC THEN
	RULE_ASSUM_TAC (ONCE_REWRITE_RULE [
		CONV_RULE bool_EQ_CONV (AC_CONV(INT_MUL_ASSOC,INT_MUL_COMM) ``a * b * c = (a * c) * b:int``)]) THEN
	IMP_RES_TAC (fst (EQ_IMP_RULE (SPEC_ALL INT_EQ_RMUL))) THEN
	MP_TAC (SPEC ``x:frac`` FRAC_DNMPOS) THEN ASM_REWRITE_TAC [INT_LT_REFL]);

val IS_INT_eq = prove(``!a. IS_INT (com (abs_rat (abs_frac(a,1))) rat_0)``,
	RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_LT_IMP_NE] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_MOD_COMMON_FACTOR,INT_LT_IMP_NE,FRAC_DNMPOS]);

val IS_INT_EXISTS = store_thm("IS_INT_EXISTS",``!a b. IS_INT (com a b) = (b = rat_0) /\ ?c. a = abs_rat (abs_frac(c,1))``,
	METIS_TAC [IS_INT_select,IS_INT_eq]);

(*****************************************************************************)
(* Congruence theorems to make proofs easier...                              *)
(*****************************************************************************)

val NAT_CONG = prove(``!a b. (nat a = nat b) = (a = b)``,
	RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM]);

val INT_CONG = prove(``!a b. (int a = int b) = (a = b)``,
	RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM]);

val BOOL_CONG = prove(``!a b. (bool a = bool b) = (a = b)``,
	REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN TRY AP_TERM_TAC THEN 
	Cases_on `a` THEN Cases_on `b` THEN POP_ASSUM MP_TAC THEN RW_TAC std_ss [bool_def,nil_def,t_def]);

(*****************************************************************************)
(* Make sure all 'p' functions operate on |= instead of nil or t             *)
(*****************************************************************************)

val nil_t = CONV_RULE bool_EQ_CONV (EVAL ``~(nil = t)``);
val true_t = CONV_RULE bool_EQ_CONV (EVAL ``|= t``);
val false_f = CONV_RULE bool_EQ_CONV (EVAL ``~(|= nil)``);
val nil_nil = prove(``(x = nil) = ~|= x``,EQ_TAC THEN RW_TAC std_ss [false_f] THEN 
			REPEAT (POP_ASSUM MP_TAC THEN RW_TAC std_ss [ACL2_TRUE_def,ite_def,equal_def,nil_t]));

val TRUTH_REWRITES = save_thm("TRUTH_REWRITES",LIST_CONJ 
	(map (fn x => prove(x,	TRY (Cases_on `a`) THEN 
				RW_TAC std_ss [ite_def,nil_t,true_t,false_f,bool_def,consp_def,
					AP_TERM ``consp`` nil_def,nil_nil]))
		[``~(nil = t)``,``(|= (if a then b else c)) = a /\ (|= b) \/ ~a /\ |= c``,
		``(consp nil = nil)``,``ite nil a b = b``,``ite t a b = a``,
		``(x = nil) = ~(|= x)``,``~(x = nil) = (|= x)``,``|= t``,``~(|= nil)``,``(|= bool a) = a``]));

val ANDL_JUDGEMENT = prove(``(|= andl []) /\ !a b. (|= a) /\ (|= andl b) ==> (|= andl (a::b))``,
	STRIP_TAC THENL [ALL_TAC,GEN_TAC THEN Induct] THEN RW_TAC std_ss [andl_def,TRUTH_REWRITES,ite_def]);

val ANDL_REWRITE = prove(``!a b. (|= andl []) /\ ((|= andl (a::b)) = (|= a) /\ (|= andl b))``,
	GEN_TAC THEN Cases THEN RW_TAC std_ss [andl_def,TRUTH_REWRITES,ite_def]);

(*****************************************************************************)
(* Judgement theorems                                                        *)
(*****************************************************************************)

val BOOLEANP_BOOL = store_thm("BOOLEANP_BOOL",``!a. |= booleanp (bool a)``,
	Cases THEN RW_TAC std_ss [ite_def,bool_def,booleanp_def,TRUTH_REWRITES,equal_def]);

val INTEGERP_INT = store_thm("INTEGERP_INT",``!a. |= integerp (int a)``,
	RW_TAC std_ss [integerp_def,int_def,cpx_def,IS_INT_EXISTS,TRUTH_REWRITES,sexpTheory.rat_def,rat_0_def,frac_0_def] THEN Q.EXISTS_TAC `a` THEN REFL_TAC);

val NATP_NAT = store_thm("NATP_NAT",``!a. |= natp (nat a)``,
	RW_TAC int_ss [natp_def,nat_def,INTEGERP_INT,ite_def,TRUTH_REWRITES] THEN
	FULL_SIMP_TAC int_ss [less_def,equal_def,int_def,cpx_def,sexpTheory.rat_def,RAT_EQ,TRUTH_REWRITES,sexp_11,complex_rational_11,RAT_LES_CALCULATE,NMR,DNM]);

val RATIONALP_RAT = store_thm("RATIONALP_RAT",``!a. |= rationalp (rat a)``,RW_TAC std_ss [rationalp_def,rat_def,TRUTH_REWRITES]);

val ACL2_NUMBERP_NUM = store_thm("ACL2_NUMBERP_NUM",``!a. |= acl2_numberp (num a)``,RW_TAC std_ss [acl2_numberp_def,TRUTH_REWRITES]);
	
val PAIRP_PAIR = store_thm("PAIRP_PAIR",``(!a. |= p1 (f1 a)) /\ (!a.|= p2 (f2 a)) ==> !a. |= pairp p1 p2 (pair f1 f2 a)``,
	STRIP_TAC THEN Cases THEN RW_TAC std_ss [pair_def,pairp_def,TRUTH_REWRITES,ite_def]);

val LISTP_LIST = store_thm("LISTP_LIST",``(!a. |= p (f a)) ==> !a. |= listp p (list f a)``,
	STRIP_TAC THEN Induct THEN FULL_SIMP_TAC std_ss [listp_def,list_def,TRUTH_REWRITES,nil_def,equal_def,ite_def] THEN
	RW_TAC std_ss [ACL2_TRUE_def,t_def,equal_def,ite_def,nil_def]);

val CHARACTERP_CHAR = store_thm("CHARACTERP_CHAR",``!a. |= characterp (chr a)``,RW_TAC std_ss [characterp_def,TRUTH_REWRITES]);

val STRINGP_STRING = store_thm("STRINGP_STRING",``!a. |= stringp (str a)``,RW_TAC std_ss [stringp_def,TRUTH_REWRITES]);

val TYPE_ITE = store_thm("TYPE_ITE",``((|= P) ==> (|= p a)) /\ (~(|= P) ==> (|= p b)) ==> |= p (ite P a b)``,
 	Cases_on `|= P` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES]);
 
val TYPE_IMP = store_thm("TYPE_IMP",``((|= A) ==> (|= booleanp B)) ==> |= booleanp (implies A B)``,
	Cases_on `|= A` THEN RW_TAC std_ss [implies_def,ite_def,andl_def,TRUTH_REWRITES,booleanp_def,equal_def]);

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

val SEXP_TO_BOOL_OF_BOOL = store_thm("SEXP_TO_BOOL_OF_BOOL",``!a. sexp_to_bool (bool a) = a``,Cases THEN RW_TAC std_ss [bool_def,sexp_to_bool_def,TRUTH_REWRITES]);

val SEXP_TO_CHAR_OF_CHAR = store_thm("SEXP_TO_CHAR_OF_CHAR",``!a. sexp_to_char (chr a) = a``,RW_TAC std_ss [sexp_to_char_def]);

val SEXP_TO_STRING_OF_STRING = store_thm("SEXP_TO_STRING_OF_STRING",``!a. sexp_to_string (str a) = a``,RW_TAC std_ss [sexp_to_string_def]);

(*****************************************************************************)
(* Decode then encode proofs                                                 *)
(*****************************************************************************)

val BOOL_OF_SEXP_TO_BOOL = store_thm("BOOL_OF_SEXP_TO_BOOL",``!a. (|= booleanp a) ==> (bool (sexp_to_bool a) = a)``,
	GEN_TAC THEN Cases_on `a = t` THEN RW_TAC std_ss [sexp_to_bool_def,bool_def,booleanp_def,ite_def,equal_def,TRUTH_REWRITES]);

val INT_OF_SEXP_TO_INT = store_thm("INT_OF_SEXP_TO_INT",``!a. (|= integerp a) ==> (int (sexp_to_int a) = a)``,
	Cases THEN RW_TAC std_ss [integerp_def,TRUTH_REWRITES] THEN
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [IS_INT_EXISTS,int_def,sexp_to_int_def,cpx_def] THEN
	RW_TAC std_ss [integerp_def,IS_INT_EXISTS,sexpTheory.rat_def,TRUTH_REWRITES,rat_0_def,frac_0_def] THEN
	RW_TAC std_ss [complex_rational_11,rat_0_def,sexpTheory.rat_def,frac_0_def,rat_nmr_def,rat_dnm_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_DIV_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE]);

val NAT_OF_SEXP_TO_NAT = store_thm("NAT_OF_SEXP_TO_NAT",``!a. (|= natp a) ==> (nat (sexp_to_nat a) = a)``,
	RW_TAC std_ss [sexp_to_nat_def,nat_def,INT_OF_SEXP_TO_INT,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),natp_def,TRUTH_REWRITES,ite_def] THEN
	(SUBGOAL_THEN ``?a'. a = int a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (EXISTS_TAC ``sexp_to_int a`` THEN RW_TAC std_ss [INT_OF_SEXP_TO_INT])) THEN
	RW_TAC std_ss [SEXP_TO_INT_OF_INT,INT_CONG,INT_OF_NUM] THEN
	FULL_SIMP_TAC int_ss [less_def,int_def,cpx_def,sexpTheory.rat_def,equal_def,TRUTH_REWRITES,sexp_11,complex_rational_11,RAT_EQ,RAT_LES_CALCULATE,NMR,DNM]);

val RAT_OF_SEXP_TO_RAT = store_thm("RAT_OF_SEXP_TO_RAT",``!a. (|= rationalp a) ==> (rat (sexp_to_rat a) = a)``,
	Cases_on `a` THEN RW_TAC std_ss [rationalp_def,TRUTH_REWRITES,rat_def] THEN Cases_on `c` THEN FULL_SIMP_TAC std_ss [rationalp_def,sexp_to_rat_def,TRUTH_REWRITES]);

val NUM_OF_SEXP_TO_COM = store_thm("NUM_OF_SEXP_TO_COM",``!a. (|= acl2_numberp a) ==> (num (sexp_to_com a) = a)``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,TRUTH_REWRITES,sexp_to_com_def]);

val CHAR_OF_SEXP_TO_CHAR = store_thm("CHAR_OF_SEXP_TO_CHAR",``!a. (|= characterp a) ==> (chr (sexp_to_char a) = a)``,
	Cases THEN RW_TAC std_ss [characterp_def,TRUTH_REWRITES,sexp_to_char_def]);

val STRING_OF_SEXP_TO_STRING = store_thm("STRING_OF_SEXP_TO_STRING",``!a. (|= stringp a) ==> (str (sexp_to_string a) = a)``,
	Cases THEN RW_TAC std_ss [stringp_def,TRUTH_REWRITES,sexp_to_string_def]);

val CHOOSEP_TAC = translateLib.CHOOSEP_TAC [BOOL_OF_SEXP_TO_BOOL,INT_OF_SEXP_TO_INT,NAT_OF_SEXP_TO_NAT,RAT_OF_SEXP_TO_RAT,NUM_OF_SEXP_TO_COM];

(*****************************************************************************)
(* Label theorems, required only for encoding                                *)
(*****************************************************************************)

val LABEL_CONS = store_thm("LABEL_CONS",``!x n p. (|= pairp (equal (nat n)) p x) ==> (?b. x = cons (nat n) b)``,
		Cases THEN RW_TAC std_ss [TRUTH_REWRITES,pairp_def,ite_def,equal_def]);

val LABEL = store_thm("LABEL",``!x y. (|= equal (nat n) x) ==> (x = nat n)``,RW_TAC std_ss [equal_def,ite_def,TRUTH_REWRITES]);

val LABEL_CONG = store_thm("LABEL_CONG",``(nat a = nat b) = (a = b)``,EQ_TAC THEN RW_TAC std_ss [NAT_CONG]);

val LABEL_EQ = store_thm("LABEL_EQ",``pairp (equal (nat x)) Y (cons (nat y) Z) = if x = y then Y Z else nil``,
	RW_TAC std_ss [pairp_def,ite_def,equal_def,TRUTH_REWRITES,LABEL_CONG] THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [TRUTH_REWRITES]);

(*****************************************************************************)
(* Boolean theorems and definitions                                          *)
(*****************************************************************************)

val BOOLEANP_EQUAL = prove(``!a b. |= booleanp (equal a b)``,RW_TAC std_ss [equal_def,booleanp_def,ite_def,TRUTH_REWRITES]);

val BOOLEANP_LESS = prove(``!a b. |= booleanp (less a b)``,
	REWRITE_TAC [booleanp_def,ite_def,equal_def,TRUTH_REWRITES] THEN
	Cases THEN Cases THEN TRY (Cases_on `c`) THEN TRY (Cases_on `c'`) THEN RW_TAC std_ss [less_def,TRUTH_REWRITES]);


val BOOLEANP_NOT = prove(``!a. |= booleanp (not a)``,
	RW_TAC std_ss [booleanp_def,equal_def,ite_def,TRUTH_REWRITES,not_def]);

val BOOLEANP_IF = prove(``!a b. (|= booleanp a) /\ (|= booleanp b) ==> |= booleanp (ite p a b)``,
	REPEAT GEN_TAC THEN Cases_on `a = nil` THEN Cases_on `b = nil` THEN RW_TAC std_ss [booleanp_def,equal_def,ite_def,TRUTH_REWRITES]);

val BOOLEANP_CONSP = prove(``!a. |= booleanp (consp a)``,Cases THEN RW_TAC std_ss [booleanp_def,consp_def,ite_def,TRUTH_REWRITES,equal_def]);

val BOOLEANP_ZP = prove(``!a. |= booleanp (zp a)``,
	RW_TAC std_ss [booleanp_def,ite_def,equal_def,zp_def,TRUTH_REWRITES,GSYM (SPEC ``0i`` int_def)] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [TRUTH_REWRITES,not_def,ite_def]);

val BOOLEANP_NATP = prove(``!a. |= booleanp (natp a)``,
	Cases_on `a` THEN RW_TAC std_ss [booleanp_def,natp_def,ite_def,TRUTH_REWRITES,integerp_def,equal_def]);

val BOOLEANP_IMPLIES = prove(``!a b. (|= booleanp a) /\ (|= booleanp b) ==> (|= booleanp (implies a b))``,
	RW_TAC std_ss [implies_def,booleanp_def,andl_def,ite_def,equal_def,TRUTH_REWRITES]);

val BOOLEANP_ANDL = prove(``!a b. (|= booleanp a) /\ (|= booleanp (andl b)) ==> (|= booleanp (andl (a::b)))``,
	GEN_TAC THEN Induct THEN RW_TAC std_ss [implies_def,booleanp_def,andl_def,ite_def,equal_def,TRUTH_REWRITES]);

val BOOLEANP_ANDL_NULL = prove(``|= booleanp (andl [])``,
	RW_TAC std_ss [andl_def,booleanp_def,ite_def,equal_def,TRUTH_REWRITES]);

val BOOL_AND = prove(``!a b. bool (a /\ b) = andl [bool a; bool b]``,Cases THEN Cases THEN RW_TAC std_ss [bool_def,andl_def,TRUTH_REWRITES]);

val BOOL_OR = prove(``!a b. bool (a \/ b) = not (andl [bool ~a ; bool ~b])``,Cases THEN Cases THEN RW_TAC std_ss [bool_def,andl_def,TRUTH_REWRITES,not_def]);
	
val BOOL_IMPLIES = prove(``!a b. bool (a ==> b) = implies (bool a) (bool b)``,Cases THEN Cases THEN RW_TAC std_ss [implies_def,bool_def,TRUTH_REWRITES,andl_def]);

val BOOL_NOT = prove(``!a. bool (~a) = not (bool a)``,Cases THEN RW_TAC std_ss [not_def,TRUTH_REWRITES,bool_def]);

val BOOL_EQ = prove(``!a b. bool (a = b) = equal (bool a) (bool b)``,Cases THEN Cases THEN RW_TAC std_ss [bool_def,equal_def]);

val BOOL_T = CONJUNCT1 bool_def;

val BOOL_F = CONJUNCT2 bool_def;

val BOOL_SEXP_T = prove(``!x. (|= booleanp x) ==> (bool (x = t) = x)``,
	GEN_TAC THEN Cases_on `x = t` THEN RW_TAC std_ss [bool_def,booleanp_def,ite_def,equal_def,TRUTH_REWRITES]);

val BOOL_SEXP_F = prove(``!x. (|= booleanp x) ==> (bool (x = nil) = not x)``,
	RW_TAC std_ss [bool_def,booleanp_def,ite_def,equal_def,TRUTH_REWRITES,not_def]);

(*****************************************************************************)
(* Integer theorems:                                                         *)
(*****************************************************************************)

val INTEGERP_ADD = store_thm("INTEGERP_ADD",``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (add a b)``,
	Cases THEN Cases THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,add_def,TRUTH_REWRITES] THEN
	Cases_on `c` THEN Cases_on `c'` THEN
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_ADD_def,RAT_ADD_RID,rat_0_def,GSYM rat_0] THEN
	Q.EXISTS_TAC `c + c'` THEN
	RW_TAC std_ss [rat_add_def,frac_add_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
	RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
	ARITH_TAC);

val INTEGERP_MULT = store_thm("INTEGERP_MULT",``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (mult a b)``,
	Cases THEN Cases THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,mult_def,TRUTH_REWRITES] THEN
	Cases_on `c` THEN Cases_on `c'` THEN
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_MULT_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,RAT_MUL_LZERO,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID] THEN
	Q.EXISTS_TAC `c * c'` THEN
	RW_TAC std_ss [rat_mul_def,frac_mul_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
	RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
	ARITH_TAC);

val INTEGERP_UNARY_MINUS = store_thm("INTEGERP_UNARY_MINUS",``!a. (|= integerp a) ==> |= integerp (unary_minus a)``,
	Cases THEN 
	RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,unary_minus_def,TRUTH_REWRITES] THEN
	Cases_on `c` THEN 
	FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_SUB_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,com_0_def] THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [RAT_SUB_RID,RAT_SUB_LID,RAT_AINV_0] THEN
	Q.EXISTS_TAC `~c` THEN
	RW_TAC std_ss [RAT_AINV_CALCULATE,frac_ainv_def,NMR,INT_LT_01,DNM]);

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
	RW_TAC std_ss [INT_CONG,equal_def,bool_def,TRUTH_REWRITES]);

val INT_LT = prove(``!a b. bool (a < b) = less (int a) (int b)``,
	RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM,less_def,RAT_LES_CALCULATE,bool_def]);

(*****************************************************************************)
(* Nat theorems:                                                             *)
(*****************************************************************************)

val NAT_EQUAL = prove(``!a b. bool (a = b) = equal (nat a) (nat b)``,
	RW_TAC int_ss [NAT_CONG,equal_def,bool_def]);

val NAT_EQUAL_0 = prove(``!a. bool (a = 0n) = zp (nat a)``,
	Cases THEN RW_TAC int_ss [bool_def,zp_def,nat_def,INTEGERP_INT,TRUTH_REWRITES,ite_def,GSYM int_def,GSYM INT_LT,not_def]);

val NAT_0_LT = prove(``!a. bool (0n < a) = not (zp (nat a))``,
	Cases THEN RW_TAC int_ss [bool_def,zp_def,nat_def,INTEGERP_INT,TRUTH_REWRITES,ite_def,GSYM int_def,GSYM INT_LT,not_def]);
	

val NAT_ADD = prove(``!a b. nat (a + b) = add (nat a) (nat b)``,
	RW_TAC std_ss [nat_def,add_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_ADD_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,RAT_ADD_RID,rat_add_def,frac_add_def] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_LT_IMP_NE] THEN ARITH_TAC);

val NAT_SUC = prove(``!a. nat (SUC a) = add (nat a) (nat 1)``,
	RW_TAC std_ss [NAT_ADD,ADD1]);

val NAT_PRE = prove(``!a. ~(a = 0n) ==> (nat (PRE a) = add (nat a) (unary_minus (nat 1)))``,
	Cases THEN RW_TAC arith_ss [nat_def,GSYM INT_UNARY_MINUS,GSYM INT_ADD] THEN AP_TERM_TAC THEN RW_TAC int_ss [ADD1,GSYM integerTheory.INT_ADD] THEN ARITH_TAC);

val NAT_SUC_PRE = prove(``!a. ~(a = 0n) ==> (nat (SUC (PRE a)) = nat a)``,
	REPEAT STRIP_TAC THEN AP_TERM_TAC THEN RW_TAC arith_ss [ADD1]);

val NAT_MULT = prove(``!a b. nat (a * b) = mult (nat a) (nat b)``,
	RW_TAC std_ss [nat_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_MULT_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,
		RAT_MUL_RZERO,RAT_SUB_RID,rat_mul_def,frac_mul_def,RAT_ADD_RID] THEN
	RAT_CONG_TAC THEN
	FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_LT_IMP_NE,rat_0,frac_0_def,RAT_NMREQ0_CONG] THEN
	ARITH_TAC);


val NATP_ADD = prove(``!a b. (|= natp a) /\ (|= natp b) ==> |= natp (add a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM NAT_ADD,NATP_NAT]);

val NATP_MULT = prove(``!a b. (|= natp a) /\ (|= natp b) ==> |= natp (mult a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM NAT_MULT,NATP_NAT]);

val NATP_PRE = prove(``!a. (|= natp a) /\ ~(a = nat 0) ==> |= natp (add a (unary_minus (nat 1)))``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN FULL_SIMP_TAC std_ss [GSYM NAT_PRE,NAT_CONG,NATP_NAT]);

val NATP_NFIX = prove(``!a. |= natp (nfix a)``,
	RW_TAC std_ss [natp_def,nfix_def,ite_def,TRUTH_REWRITES,ANDL_REWRITE,nat_def] THEN
	FULL_SIMP_TAC std_ss [INTEGERP_INT,GSYM INT_LT,GSYM INT_EQUAL,TRUTH_REWRITES] THEN
	CHOOSEP_TAC THEN
	FULL_SIMP_TAC std_ss [GSYM BOOL_NOT,INTEGERP_INT,GSYM INT_LT,GSYM INT_EQUAL,TRUTH_REWRITES] THEN
	ARITH_TAC);



val NZP_NATP = prove(``~(zp x = t) ==> |= natp x``,
	RW_TAC std_ss [zp_def,natp_def,ite_def,TRUTH_REWRITES,GSYM int_def,GSYM (REWRITE_CONV [nat_def] ``nat 0``),not_def]);

val NATP_ZERO = prove(``!a. (zp a = t) ==> (sexp_to_nat a = 0)``,
	RW_TAC std_ss [zp_def,equal_def,ite_def,TRUTH_REWRITES,GSYM (SPEC ``(& 0n):int`` int_def),not_def,natp_def] THEN
	FULL_SIMP_TAC std_ss [SEXP_TO_NAT_OF_NAT,nat_def,TRUTH_REWRITES] THENL [
		Cases_on `a` THEN RW_TAC std_ss [integerp_def,sexp_to_nat_def,natp_def,ite_def,TRUTH_REWRITES],
		CHOOSEP_TAC] THEN
	FULL_SIMP_TAC int_ss [GSYM INT_LT,INTEGERP_INT,TRUTH_REWRITES,sexp_to_nat_def,natp_def,ite_def,TRUTH_REWRITES,nat_def,GSYM INT_EQUAL,SEXP_TO_INT_OF_INT] THEN
	Cases_on `a' = 0` THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss [TRUTH_REWRITES]);

val NATP_UMINUS_ADD = prove(``!a. (|= natp a) ==> (add (add a (unary_minus (nat b))) (unary_minus (nat c)) = add a (unary_minus (nat (b + c))))``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'. a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN
	RW_TAC std_ss [natp_def,nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,ite_def,TRUTH_REWRITES,GSYM INT_LT,GSYM INT_EQUAL,GSYM int_sub,integerTheory.INT_SUB,
		ARITH_PROVE ``~(& a = 0i) ==> 1n <= a``,NUM_OF_INT] THEN
	AP_TERM_TAC THEN ARITH_TAC);

(*****************************************************************************)
(* Rational theorems:                                                        *)
(*****************************************************************************)

val RATIONALP_ADD = store_thm("RATIONALP_ADD",``!a b. (|= rationalp a) /\ (|= rationalp b) ==> |= rationalp (add a b)``,
	Cases THEN Cases THEN RW_TAC std_ss [rationalp_def,add_def,TRUTH_REWRITES] THEN 
	Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_ADD_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID]);

val RATIONALP_MULT = store_thm("RATIONALP_MULT",``!a b. (|= rationalp a) /\ (|= rationalp b) ==> |= rationalp (mult a b)``,
	Cases THEN Cases THEN RW_TAC std_ss [rationalp_def,mult_def,TRUTH_REWRITES] THEN 
	Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_MULT_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID,RAT_MUL_RZERO,RAT_MUL_LZERO]);

val RATIONALP_UNARY_MINUS = store_thm("RATIONALP_UNARY_MINUS",``!a. (|= rationalp a) ==> |= rationalp (unary_minus a)``,
	Cases THEN RW_TAC std_ss [rationalp_def,unary_minus_def,TRUTH_REWRITES] THEN 
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [rationalp_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,com_0_def,COMPLEX_SUB_def,RAT_SUB_RID]);

val RATIONALP_RECIPROCAL = store_thm("RATIONALP_RECIPROCAL",``!a. (|= rationalp a) ==> |= rationalp (reciprocal a)``,
	Cases THEN RW_TAC std_ss [rationalp_def,reciprocal_def,TRUTH_REWRITES,int_def,com_0_def,cpx_def,sexpTheory.rat_def,rat_0_def, GSYM rat_0,GSYM frac_0_def] THEN
	Cases_on `c` THEN FULL_SIMP_TAC std_ss [COMPLEX_RECIPROCAL_def,complex_rational_11,rationalp_def,TRUTH_REWRITES,rat_0_def,
		GSYM rat_0,RAT_MUL_RZERO,RAT_ADD_RID,RAT_AINV_0,RAT_LDIV_EQ,RAT_NO_ZERODIV_NEG]);


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

val ACL2_NUMBERP_COM = store_thm("ACL2_NUMBERP_COM",``!a. |= acl2_numberp (num a)``,RW_TAC std_ss [acl2_numberp_def,TRUTH_REWRITES]);

val ACL2_NUMBERP_ADD = store_thm("ACL2_NUMBERP_ADD",``!a b. |= acl2_numberp (add a b)``,
	Cases THEN Cases THEN RW_TAC std_ss [acl2_numberp_def,add_def,TRUTH_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_MULT = store_thm("ACL2_NUMBERP_MULT",``!a b. |= acl2_numberp (mult a b)``,
	Cases THEN Cases THEN RW_TAC std_ss [acl2_numberp_def,mult_def,TRUTH_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_UNARY_MINUS = store_thm("ACL2_NUMBERP_UNARY_MINUS",``!a. |= acl2_numberp (unary_minus a)``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,unary_minus_def,TRUTH_REWRITES,int_def,cpx_def]);

val ACL2_NUMBERP_RECIPROCAL = store_thm("ACL2_NUMBERP_RECIPROCAL",``!a. |= acl2_numberp (reciprocal a)``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,reciprocal_def,TRUTH_REWRITES,int_def,cpx_def]);

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
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,equal_def,TRUTH_REWRITES,complex_rational_11]);

val FIX_NUM = prove(``(!a. fix (num a) = num a) /\ (!a. fix (rat a) = rat a) /\ (!a. fix (int a) = int a) /\ (!a. fix (nat a) = nat a)``,
	RW_TAC std_ss [fix_def,ACL2_NUMBERP_NUM,ite_def,TRUTH_REWRITES,rat_def,int_def,nat_def,cpx_def]);

val NAT_NFIX = prove(``nfix (nat a) = nat a``,
	RW_TAC std_ss [nfix_def,ite_def,TRUTH_REWRITES,nat_def,ANDL_REWRITE,INTEGERP_INT,GSYM INT_LT,GSYM BOOL_NOT] THEN
	METIS_TAC [INT_POS,INT_NOT_LT]);

val INT_IFIX = prove(``ifix (int a) = int a``,RW_TAC std_ss [ifix_def,ite_def,TRUTH_REWRITES,INTEGERP_INT]);

(*****************************************************************************)
(* Pair theorems:                                                            *)
(*****************************************************************************)

val PAIR_JUDGEMENT = store_thm("PAIR_JUDGEMENT",``!x p1 p2. (|= pairp p1 p2 x) ==> (|= p1 (car x)) /\ (|= p2 (cdr x))``,
				Cases THEN RW_TAC std_ss [pairp_def,ite_def,car_def,cdr_def,TRUTH_REWRITES]);

val PAIR_NCHOTOMY = store_thm("PAIR_NCHOTOMY",``!x p1 p2. (|= pairp p1 p2 x) ==> ?a b. x = cons a b``,
		Cases THEN RW_TAC std_ss [pairp_def,ite_def,TRUTH_REWRITES]);

val PAIR_OF_SEXP_TO_PAIR = store_thm("PAIR_OF_SEXP_TO_PAIR",``(!x. (|= p1 x) ==> (f1 (g1 x) = x)) /\ (!x. (|= p2 x) ==> (f2 (g2 x) = x)) ==> 
				!p. (|= pairp p1 p2 p) ==> (pair f1 f2 (sexp_to_pair g1 g2 p) = p)``,
		DISCH_TAC THEN Cases THEN RW_TAC std_ss [pairp_def,sexp_to_pair_def,pair_def,ite_def,TRUTH_REWRITES]);

val PAIR_COMMA = prove(``pair f g (a,b) = cons (f a) (g b)``,RW_TAC std_ss [pair_def]);

val PAIR_FST = prove(``f (FST x) = car (pair f g x)``,RW_TAC std_ss [pairTheory.FST,pair_def,car_def]);

val PAIR_SND = prove(``g (SND x) = cdr (pair f g x)``,RW_TAC std_ss [pairTheory.SND,pair_def,cdr_def]);

val PAIR_OF_SEXP_TO_PAIR2 = prove(``	(!x. (|= p1 x) ==> (f1 (g1 x) = x)) /\
					(!x. (|= p2 x) ==> (f2 (g2 x) = x)) ==> !x. (|= pairp p1 p2 x) ==> (cons (f1 (g1 (car x))) (f2 (g2 (cdr x))) = x)``,
		DISCH_TAC THEN Cases THEN RW_TAC std_ss [pairp_def,car_def,cdr_def,ite_def,TRUTH_REWRITES]);

val PAIRP_CONS = store_thm("PAIRP_CONS",``!a b. (|= p1 a) /\ (|= p2 b) ==> |= pairp p1 p2 (cons a b)``,RW_TAC std_ss [pairp_def,ite_def,TRUTH_REWRITES]);

(*****************************************************************************)
(* List theorems:                                                            *)
(*****************************************************************************)

val LIST_OF_SEXP_TO_LIST = 
		store_thm("LIST_OF_SEXP_TO_LIST",``(!x. (|= p x) ==> (f (g x) = x)) ==> !l. (|= listp p l) ==> (list f (sexp_to_list g l) = l)``,
		DISCH_TAC THEN Induct THEN RW_TAC std_ss [listp_def,list_def,sexp_to_list_def,ite_def,equal_def,TRUTH_REWRITES]);

val LIST_JUDGEMENT = store_thm("LIST_JUDGEMENT",``
			(!x l. (|= listp l x) ==> (?a b. x = cons a b) ==> (|= listp l (cdr x)) /\ (|= l (car x))) /\
			(!x l. (|= listp l x) ==> ((x = nil) ==> (|= equal x nil)) /\ ((?a b. x = cons a b) ==> (|= pairp l (listp l) x)))``,
		REPEAT CONJ_TAC THEN Induct THEN GEN_TAC THEN RULE_ASSUM_TAC SPEC_ALL THEN
		RW_TAC std_ss [listp_def,car_def,cdr_def,REWRITE_CONV [nil_def] ``listp l nil``,equal_def,TRUTH_REWRITES,ite_def,pairp_def]);

val LIST_NCHOTOMY = store_thm("LIST_NCHOTOMY",``(!x l. (|= listp l x) ==> (x = nil) \/ (?a b. x = cons a b))``,
		REPEAT CONJ_TAC THEN Induct THEN GEN_TAC THEN RULE_ASSUM_TAC SPEC_ALL THEN
		RW_TAC std_ss [listp_def,car_def,cdr_def,REWRITE_CONV [nil_def] ``listp l nil``,equal_def,TRUTH_REWRITES,ite_def,pairp_def]);

val LIST_CONS = CONJUNCT1 list_def;

val LIST_NIL = CONJUNCT2 list_def;

val LISTP_TAIL = prove(``!a. (|= listp p a) ==> |= listp p (cdr a)``,
	Induct THEN RW_TAC std_ss [listp_def,cdr_def,equal_def,ite_def,TRUTH_REWRITES,(REWRITE_CONV [listp_def,nil_def] THENC REWRITE_CONV [GSYM nil_def]) ``listp l nil``]);

val LISTP_CONS_HT = prove(``!x. (|= listp l x) ==> (?a b. x = cons a b) ==> |= listp l (cons (car x) (cdr x))``,
	Induct THEN RW_TAC std_ss [listp_def,cdr_def,equal_def,ite_def,nil_def,car_def,TRUTH_REWRITES]);

val LISTP_CONS = prove(``!a b. (|= l a) /\ (|= listp l b) ==> (|= listp l (cons a b))``,
	RW_TAC std_ss [listp_def,ite_def,TRUTH_REWRITES]);

val LISTP_NIL = prove(``|= listp f nil``,RW_TAC std_ss [listp_def,TRUTH_REWRITES,equal_def,ite_def,nil_def]);

val LIST_HD = prove(``~(l = []) ==> (encode (HD l) = car (list encode l))``,
	Induct_on `l` THEN RW_TAC std_ss [list_def,HD,car_def]);

val LIST_TL = prove(``~(l = []) ==> (list encode (TL l) = cdr (list encode l))``,
	Induct_on `l` THEN RW_TAC std_ss [list_def,TL,cdr_def]);

val LIST_LENGTH = prove(``nat (LENGTH l) = len (list f l)``,
	Induct_on `l` THEN ONCE_REWRITE_TAC [len_def] THEN 
	RW_TAC std_ss [LENGTH,list_def,consp_def,ite_def,TRUTH_REWRITES,NAT_SUC,cdr_def] THEN
	POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
	RW_TAC arith_ss [GSYM NAT_ADD]);

(*****************************************************************************)
(* String theorems:                                                          *)
(*****************************************************************************)

val list_rewrite = prove(``list_to_sexp = list``,REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN Induct THEN METIS_TAC [list_def,list_to_sexp_def]);

val STRING_JUDGEMENT = store_thm("STRING_JUDGEMENT",``!a. (|= stringp a) ==> (|= listp characterp (coerce a (sym "COMMON-LISP" "LIST")))``,
	Cases THEN RW_TAC std_ss [stringp_def,coerce_def,LISTP_NIL,TRUTH_REWRITES,coerce_string_to_list_def,list_rewrite,LISTP_LIST,CHARACTERP_CHAR]);

val STRING_EXPLODE = prove(``list chr (EXPLODE s) = coerce (str s) (sym "COMMON-LISP" "LIST")``,
	RW_TAC std_ss [coerce_def,coerce_string_to_list_def,list_rewrite]);

val STRING_IMPLODE = prove(``str (IMPLODE l) = coerce (list chr l) (sym "COMMON-LISP" "STRING")``,
	Induct_on `l` THEN RW_TAC std_ss [coerce_def,coerce_list_to_string_def,list_rewrite,list_def,nil_def,stringTheory.IMPLODE_EQNS,make_character_list_def] THEN
	Cases_on `list chr l` THEN REPEAT (POP_ASSUM MP_TAC) THEN Cases_on `l` THEN RW_TAC std_ss [coerce_def,list_def,nil_def,stringTheory.IMPLODE_EQNS,make_character_list_def,coerce_list_to_string_def]);

val coerce_rewrite = CONJ (GSYM STRING_EXPLODE) (GSYM STRING_IMPLODE);

val STRING_LENGTH = prove(``nat (STRLEN s) = length (str s)``,
	RW_TAC std_ss [stringp_def,ite_def,TRUTH_REWRITES,length_def,coerce_def,coerce_string_to_list_def,
			stringTheory.STRLEN_THM,LIST_LENGTH,list_rewrite,csym_def,COMMON_LISP_def]);

(*****************************************************************************)
(* Case theorems                                                             *)
(*****************************************************************************)

val NAT_CASE = store_thm("NAT_CASE",``!a. encode (case a of 0 -> A || (SUC n) -> B n) = ite (equal (nat a) (nat 0)) (encode A) (encode (B (PRE a)))``,
		Cases THEN RW_TAC int_ss [equal_def,ite_def,TRUTH_REWRITES,NAT_CONG]);

val PAIR_CASE = store_thm("PAIR_CASE",``
		(!x. decode_'a (encode_'a x) = x) /\ (!x. decode_'b (encode_'b x) = x) ==> 
		!p. (encode:'c -> sexp) (case p of (a,b) -> A a b) = 
			encode (A (decode_'a (car (pair encode_'a encode_'b p))) (decode_'b (cdr (pair encode_'a encode_'b p))))``,
		STRIP_TAC THEN Cases THEN RW_TAC std_ss [TypeBase.case_def_of ``:'a # 'b``,car_def,cdr_def,pair_def]);

val LIST_CASE = store_thm("LIST_CASE",``(!x. decode_'a (encode_'a x) = x) ==>
			!l. (encode:'b -> sexp) (case l of [] -> A || hd::tl -> B hd tl) = 
				ite (consp (list encode_'a l)) 	(encode (B (decode_'a (car (list encode_'a l))) (sexp_to_list decode_'a (cdr (list encode_'a l)))))
								(encode A)``,
		STRIP_TAC THEN Cases THEN RW_TAC std_ss [eq_def,list_def,equal_def,ite_def,car_def,cdr_def,SEXP_TO_LIST_OF_LIST,nil_def,t_def,consp_def]);

val BOOL_CASE = store_thm("BOOL_CASE",``!a. encode (case a of T -> A || F -> B) = ite (bool a) (encode A) (encode B)``,
		Cases THEN RW_TAC std_ss [bool_def,TRUTH_REWRITES]);

val uncoerce = prove(``sexp_to_string (coerce (list chr (EXPLODE s)) (sym "COMMON-LISTP" "STRING")) = s``,
	Induct_on `s` THEN RW_TAC std_ss [coerce_def,list_def,stringTheory.EXPLODE_EQNS,nil_def,SEXP_TO_STRING_OF_STRING,make_character_list_def,coerce_list_to_string_def] THEN
	Cases_on `(list chr (EXPLODE s))` THEN REPEAT (POP_ASSUM MP_TAC) THEN 
	RW_TAC std_ss [coerce_def,SEXP_TO_STRING_OF_STRING] THEN FULL_SIMP_TAC std_ss [stringTheory.EXPLODE_EQNS,list_def,nil_def,sexp_11,sexp_distinct,make_character_list_def,coerce_list_to_string_def]);

val STRING_CASE = store_thm("STRING_CASE",``encode (case s of "" -> X || STRING c s -> Y c s) = 
			ite (equal (str s) (str "")) (encode X) 
				(encode (Y (sexp_to_char (car (coerce (str s) (sym "COMMON-LISP" "LIST")))) 
					(sexp_to_string (coerce (cdr (coerce (str s) (sym "COMMON-LISP" "LIST"))) (sym "COMMON-LISTP" "STRING")))))``,
	Cases_on `s` THEN RW_TAC std_ss [equal_def,ite_def,coerce_def,coerce_string_to_list_def,list_rewrite,stringTheory.EXPLODE_EQNS,list_def,car_def,cdr_def,TRUTH_REWRITES,SEXP_TO_CHAR_OF_CHAR,uncoerce]);

(*****************************************************************************)
(* Flat theorems                                                             *)
(*****************************************************************************)

val LISTP_FLAT = store_thm("LISTP_FLAT",``listp p x = ite (equal x nil) t (andl [consp x; p (car x); listp p (cdr x)])``,
	`!a b. |= cons a b` by RW_TAC std_ss [ACL2_TRUE_def,equal_def,ite_def,nil_def] THEN
	Cases_on `x` THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites [listp_def] THEN
	RW_TAC std_ss [equal_def,ite_def,TRUTH_REWRITES,car_def,consp_def,cdr_def,andl_def] THEN
	FULL_SIMP_TAC std_ss []);

val PAIRP_FLAT = store_thm("PAIRP_FLAT",``!x. pairp f g x = andl [consp x; f (car x); g (cdr x)]``,
	Cases THEN RW_TAC std_ss [pairp_def,andl_def,consp_def,car_def,cdr_def,ite_def,TRUTH_REWRITES]);


(*****************************************************************************)
(* Constructor typing                                                        *)
(*****************************************************************************)

val PAIRP_CONS = store_thm("PAIRP_CONS",``(|= p1 a) /\ (|= p2 b) ==> |= pairp p1 p2 (cons a b)``,
		RW_TAC std_ss [pairp_def,ite_def,TRUTH_REWRITES]);

val LISTP_CONS = store_thm("LISTP_CONS",``(|= p a) /\ (|= listp p b) ==> |= listp p (cons a b)``,
		RW_TAC std_ss [listp_def,ite_def,TRUTH_REWRITES]);

(*****************************************************************************)
(* Comparison theorems:                                                      *)
(*****************************************************************************)

(* LT, LE, GT, GE *)

val NAT_LT = prove(``!a b. bool (a < b) = less (nat a) (nat b)``,
	RW_TAC int_ss [nat_def,GSYM INT_LT,bool_def]);

val RAT_LT = prove(``!a b. bool (a < b) = less (rat a) (rat b)``,RW_TAC std_ss [bool_def,less_def,rat_def,RAT_LES_REF]);

val COM_LT = prove(``bool (a < b) = less (num a) (num b)``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,less_def,TRUTH_REWRITES,COMPLEX_LT_def]);


val COM_NOT_LT = prove(``!a b. ~(a < b) = b <= a:complex_rational``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_LT_def,COMPLEX_LE_def,RAT_LEQ_LES,rat_leq_def] THEN METIS_TAC [RAT_LES_IMP_NEQ]);

val NAT_LE = prove(``bool (a <= b) = not (less (nat b) (nat a))``,RW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM NAT_LT,NOT_LESS]);

val INT_LE = prove(``bool (a <= b) = not (less (int b) (int a))``,RW_TAC int_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM INT_LT,INT_NOT_LT]);

val RAT_LE = prove(``bool (a <= b) = not (less (rat b) (rat a))``,RW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM RAT_LT,RAT_LEQ_LES]);

val COM_LE = prove(``bool (a <= b) = not (less (num b) (num a))``,RW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM COM_LT,COM_NOT_LT]);


val NAT_GE = prove(``bool (a >= b) = bool (b <= a:num)``,AP_TERM_TAC THEN DECIDE_TAC);
val INT_GE = prove(``bool (a >= b) = bool (b <= a:int)``,AP_TERM_TAC THEN ARITH_TAC);
val RAT_GE = prove(``bool (a >= b) = bool (b <= a:rat)``,REWRITE_TAC [rat_geq_def]);
val COM_GE = prove(``bool (a >= b) = bool (b <= a:complex_rational)``,
	AP_TERM_TAC THEN Cases_on `a` THEN Cases_on `b` THEN 
	REWRITE_TAC [COMPLEX_LE_def,COMPLEX_GE_def,rat_gre_def,rat_geq_def] THEN 
	EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val NAT_GT = prove(``bool (a > b) = bool (b < a:num)``,AP_TERM_TAC THEN DECIDE_TAC);
val INT_GT = prove(``bool (a > b) = bool (b < a:int)``,AP_TERM_TAC THEN ARITH_TAC);
val RAT_GT = prove(``bool (a > b) = bool (b < a:rat)``,REWRITE_TAC [rat_gre_def]);
val COM_GT = prove(``bool (a > b) = bool (b < a:complex_rational)``,
	AP_TERM_TAC THEN Cases_on `a` THEN Cases_on `b` THEN 
	REWRITE_TAC [COMPLEX_LT_def,COMPLEX_GT_def,rat_gre_def,rat_geq_def] THEN 
	EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

(*****************************************************************************)
(* Subtraction theorems:                                                     *)
(*****************************************************************************)

val INT_SUB = prove(``!a b. int (a - b) = add (int a) (unary_minus (int b))``,
	RW_TAC int_ss [GSYM INT_ADD,GSYM INT_UNARY_MINUS,int_sub]);

val NAT_SUB = prove(``!a b. nat (a - b) = nfix (add (nat a) (unary_minus (nat b)))``,
	RW_TAC int_ss [nat_def,GSYM INT_SUB,nfix_def,ite_def,TRUTH_REWRITES,natp_def,INTEGERP_INT,GSYM INT_EQUAL,
		GSYM INT_LT,INT_CONG,GSYM BOOL_NOT,ANDL_REWRITE] THEN
	FULL_SIMP_TAC int_ss [INT_NOT_LT,INT_LE_SUB_RADD,INT_LT_SUB_LADD,integerTheory.INT_SUB,
		INT_LE_SUB_LADD,INT_LT_SUB_RADD] );

val NATP_SUB = prove(``!a b. (|= natp a) /\ (|= natp b) /\ (|= not (less a b)) ==> |= natp (add a (unary_minus b))``,
	REPEAT STRIP_TAC THEN
	CHOOSEP_TAC THEN
	FULL_SIMP_TAC arith_ss [nat_def,GSYM INT_ADD,GSYM BOOL_NOT,GSYM INT_UNARY_MINUS,GSYM NAT_LT,TRUTH_REWRITES,integerTheory.INT_ADD_CALCULATE] THEN
	RW_TAC arith_ss [GSYM nat_def,NATP_NAT]);

val RAT_SUB = prove(``rat (a - b) = add (rat a) (unary_minus (rat b))``,
	RW_TAC std_ss [rat_sub_def,frac_sub_def,GSYM RAT_ADD,GSYM RAT_UNARY_MINUS,rat_ainv_def,rat_add_def,frac_ainv_def,RAT_ADD_CONG]);
val COM_SUB = prove(``num (a - b) = add (num a) (unary_minus (num b))``,
	Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_SUB_def,GSYM COM_UNARY_MINUS,GSYM COM_ADD,
		COMPLEX_NEG_def,COMPLEX_ADD_def,com_0_def,RAT_SUB_LID,rat_0_def,GSYM rat_0,RAT_SUB_ADDAINV]);

val NAT_SUB_COND = prove(``!a b. b <= a ==> (nat (a - b) = add (nat a) (unary_minus (nat b)))``,
	RW_TAC int_ss [nat_def,GSYM INT_SUB,nfix_def,ite_def,TRUTH_REWRITES,natp_def,INTEGERP_INT,GSYM INT_EQUAL,GSYM INT_LT,INT_CONG] THEN
	FULL_SIMP_TAC int_ss [INT_NOT_LT,INT_LE_SUB_RADD,INT_LT_SUB_LADD,integerTheory.INT_SUB] THEN FULL_SIMP_TAC int_ss [INT_EQ_SUB_LADD]);


(*****************************************************************************)
(* Exponentiation for int and num using acl2 function EXPT                   *)
(*****************************************************************************)

val (expt_def,expt_ind) = 
	Defn.tprove (Hol_defn "expt" 
	`expt r i =
	if i = 0 then com_1 else
		if r = com_0 then com_0 else 
			if (0 < i) then	(r * (expt r (i - 1i))) else ((com_1 / r) * (expt r (i + 1)))`,
	WF_REL_TAC `measure (\a. Num (ABS (SND a)))` THEN ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
	RW_TAC std_ss [INT_ABS] THEN 
	FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),
		INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN ARITH_TAC);

val (acl2_expt_def,acl2_expt_ind) = (REWRITE_RULE [GSYM ite_def] ## I) 
	(acl2_defn "ACL2::EXPT" 
		(`acl2_expt r i = 
		if zip i = nil then 
	        	(ite (equal (fix r) (int 0)) (int 0)
                        	 (if less (int 0) i = nil then (mult (reciprocal r) (acl2_expt r (add i (int 1)))) 
						else (mult r (acl2_expt r (add i (unary_minus (int 1)))))))
		else int 1`,
	WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (SND a))))` THEN
	RW_TAC std_ss [] THEN
	FULL_SIMP_TAC std_ss [zip_def,TRUTH_REWRITES,ite_def,GSYM int_def] THEN
	CHOOSEP_TAC THEN
	FULL_SIMP_TAC std_ss [GSYM INT_SUB,GSYM INT_ADD,GSYM INT_LT,GSYM INT_EQUAL,TRUTH_REWRITES,INTEGERP_INT,SEXP_TO_INT_OF_INT] THEN
	ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN RW_TAC std_ss [INT_ABS] THEN 
	FULL_SIMP_TAC std_ss [INT_NOT_LT,snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),ARITH_PROVE ``a < 0 ==> 0i <= ~a``] THEN TRY ARITH_TAC));

val ACL2_NUMBERP_INT = prove(``!a. |= acl2_numberp (int a)``,RW_TAC std_ss [acl2_numberp_def,int_def,cpx_def,TRUTH_REWRITES]);

val TO_INT_ZERO = prove(``(nat 0 = int 0) /\ (num com_0 = int 0)``,RW_TAC arith_ss [com_0_def,nat_def,int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def]);

val TO_INT_ONE = prove(``(nat 1 = int 1) /\ (num com_1 = int 1)``,
	RW_TAC arith_ss [com_1_def,nat_def,int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,rat_1_def,frac_1_def]);

val SEXP_TO_COM_INT = prove(``(sexp_to_com (int 1) = com_1) /\ (sexp_to_com (int 0) = com_0)``,
	RW_TAC std_ss [CONJUNCT2 (GSYM TO_INT_ZERO),CONJUNCT2 (GSYM TO_INT_ONE),SEXP_TO_COM_OF_COM]);


val acl2_expt_num = prove(``|= acl2_numberp (acl2_expt r i)``,
	ONCE_REWRITE_TAC [acl2_expt_def] THEN 
	RW_TAC std_ss [ite_def,TRUTH_REWRITES,ACL2_NUMBERP_MULT,ACL2_NUMBERP_NUM,ACL2_NUMBERP_INT]);

val acl2_expt_correct = prove(``expt r i = sexp_to_com (acl2_expt (num r) (int i))``,
	completeInduct_on `Num (ABS i)` THEN
	RW_TAC std_ss [] THEN
	ONCE_REWRITE_TAC [expt_def,acl2_expt_def] THEN
	RW_TAC int_ss [zip_def,common_lisp_equal_def,GSYM int_def,INTEGERP_INT,FIX_NUM,
			GSYM INT_EQUAL,INT_IFIX,GSYM INT_ADD,GSYM INT_SUB,ite_def,TRUTH_REWRITES,
			SEXP_TO_COM_OF_COM,GSYM INT_LT,GSYM COM_EQUAL,
			CONJUNCT2 (GSYM TO_INT_ZERO),CONJUNCT2 (GSYM TO_INT_ZERO)] THEN
	FULL_SIMP_TAC int_ss [nat_def,TRUTH_REWRITES,equal_def,TO_INT_ZERO,SEXP_TO_COM_INT,INT_CONG] THENL [
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



val INT_EXP = prove(``int (a ** b) = acl2_expt (int a) (nat b)``,
	Induct_on `b` THEN ONCE_REWRITE_TAC [acl2_expt_def] THEN
	RW_TAC int_ss [nat_def,INTEGERP_INT,ACL2_NUMBERP_INT,equal_def,zip_def,common_lisp_equal_def,GSYM int_def,TRUTH_REWRITES,int_exp,
		TO_INT_ZERO,TO_INT_ONE,INT_CONG,FIX_NUM] THEN
	RW_TAC int_ss [GSYM INT_LT,GSYM INT_UNARY_MINUS,GSYM INT_ADD,GSYM INT_MULT,BOOL_T,ite_def,GSYM INT_MULT,
		TRUTH_REWRITES,GSYM int_sub,ARITH_PROVE ``& (SUC a) - 1i = & a``] THEN
	ASSUM_LIST (fn list => REWRITE_TAC (map GSYM (nat_def::list))) THEN
	FULL_SIMP_TAC int_ss [GSYM INT_MULT,INTEGERP_INT]); 

val NAT_EXP = prove(``nat (a ** b) = acl2_expt (nat a) (nat b)``,RW_TAC int_ss [nat_def,REWRITE_RULE [nat_def] (GSYM INT_EXP)]);

val NATP_EXP = prove(``!a b. (|= natp a) /\ (|= natp b) ==> |= natp (acl2_expt a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM NAT_EXP,NATP_NAT]);

val INTEGERP_EXP = prove(``!a b. (|= integerp a) /\ (|= natp b) ==> |= integerp (acl2_expt a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM INT_EXP,INTEGERP_INT]);


(*****************************************************************************)
(* Integer and natural number division and remainder:                        *)
(*                                                                           *)
(* DIV : num -> num -> num, $/ : int -> int -> int   use FLOOR               *)
(* MOD : num -> num -> num, $% : int -> int -> int   use MOD                 *)
(*                        quot : int -> int -> int  uses TRUNCATE            *)
(*                         rem : int -> int -> int  uses REM                 *)
(*                                                                           *)
(*****************************************************************************)

val (nniq_def,nniq_induction) = 
	Defn.tprove(Defn.Hol_defn "nniq" `nniq a b = (if b <= 0i then 0i else (if a < b then 0 else 1 + nniq (a - b) b))`,
	WF_REL_TAC `measure (\a.Num (FST a))` THEN REPEAT STRIP_TAC THEN 
	ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN `0 <= a /\ 0 <= a - b` by ARITH_TAC THEN 
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM))] THEN ARITH_TAC);

val (acl2_nniq_def,acl2_nniq_ind) = (REWRITE_RULE [GSYM ite_def] ## I) 
	(acl2_defn "ACL2::NONNEGATIVE-INTEGER-QUOTIENT" 
	(`acl2_nniq i j = 
		if (equal (nfix j) (int 0)) = nil then (
			if less (ifix i) j = nil then (add (int 1) (acl2_nniq (add i (unary_minus j)) j)) else (int 0)) 
		else (int 0)`,
	WF_REL_TAC `measure (\a. Num (ABS (sexp_to_int (FST a))))` THEN
	RW_TAC std_ss [] THEN
	FULL_SIMP_TAC std_ss [nfix_def,ANDL_REWRITE,ifix_def,TRUTH_REWRITES,ite_def,nat_def,
		TO_INT_ZERO,GSYM BOOL_NOT] THEN
	Cases_on `|= natp j` THEN Cases_on `|= integerp i` THEN
	FULL_SIMP_TAC std_ss [natp_def,ANDL_REWRITE,TRUTH_REWRITES,ite_def] THEN 
	TRY (Cases_on `|= integerp j` THEN FULL_SIMP_TAC std_ss []) THEN
	CHOOSEP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN 
	RW_TAC int_ss [GSYM INT_EQUAL,TRUTH_REWRITES,INTEGERP_INT,NATP_NAT,nat_def,GSYM BOOL_NOT,
		GSYM INT_LT,GSYM INT_SUB,SEXP_TO_INT_OF_INT,INT_NOT_LT] THEN
	ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN RW_TAC std_ss [INT_ABS] THEN 
	FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,
		INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
	ARITH_TAC));


val acl2_nniq_int = prove(``!i j. |= integerp (acl2_nniq i j)``,
	REPEAT GEN_TAC THEN completeInduct_on `Num (ABS (sexp_to_int i))` THEN
	ONCE_REWRITE_TAC [acl2_nniq_def] THEN 
	RW_TAC std_ss [ite_def,TRUTH_REWRITES,INTEGERP_INT,ifix_def,nfix_def,nat_def,ANDL_REWRITE] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [TRUTH_REWRITES,GSYM INT_EQUAL,GSYM INT_LT,GSYM BOOL_NOT] THEN 
	FULL_SIMP_TAC std_ss [] THEN CHOOSEP_TAC THEN 
	FULL_SIMP_TAC int_ss [NATP_NAT,INTEGERP_INT,SEXP_TO_INT_OF_INT,TRUTH_REWRITES,nat_def,
		GSYM INT_EQUAL,GSYM INT_LT,GSYM INT_SUB,GSYM BOOL_NOT] THEN
	MATCH_MP_TAC INTEGERP_ADD THEN PAT_ASSUM ``!m.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (i' - j'))``) THEN
	(SUBGOAL_THEN ``Num (ABS (i' - j')) < Num (ABS i')`` (fn th => FULL_SIMP_TAC std_ss [th]) THEN1
		(ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
		RW_TAC std_ss [INT_ABS] THEN 
		FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,
			INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
		ARITH_TAC)) THEN
	FULL_SIMP_TAC int_ss [INTEGERP_INT,INT_NOT_LT] THEN
	METIS_TAC [INT_LE_ANTISYM,SEXP_TO_INT_OF_INT,INTEGERP_ADD,INTEGERP_INT]);

val acl2_nniq_add = prove(``!i j. sexp_to_int (add (int a) (acl2_nniq i j)) = a + sexp_to_int (acl2_nniq i j)``,
	REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL acl2_nniq_int) THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM INT_ADD,SEXP_TO_INT_OF_INT]);

val acl2_nniq_correct = prove(``nniq a b = sexp_to_int (acl2_nniq (int a) (int b))``,
	completeInduct_on `Num (ABS a)` THEN
	ONCE_REWRITE_TAC [nniq_def,acl2_nniq_def] THEN
	RW_TAC int_ss [ite_def,TRUTH_REWRITES,INT_IFIX,SEXP_TO_INT_OF_INT,GSYM INT_LT,nat_def,
		natp_def,nfix_def,INT_NOT_LT,INT_NOT_LE,ANDL_REWRITE,INTEGERP_INT,GSYM BOOL_NOT,equal_def] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC int_ss [TRUTH_REWRITES,equal_def,INT_CONG,GSYM INT_SUB,GSYM INT_ADD,INTEGERP_INT,acl2_nniq_add] THEN
	FULL_SIMP_TAC std_ss [INT_NOT_LT,INT_NOT_LE] THEN 
	TRY (CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN PAT_ASSUM ``!b:num.P`` (K ARITH_TAC)) THEN
	PAT_ASSUM ``!b:num.P`` (STRIP_ASSUME_TAC o SPEC ``Num (ABS (a - b))``) THEN
	SUBGOAL_THEN ``Num (ABS (a - b)) < Num (ABS a)`` (fn th => FULL_SIMP_TAC std_ss [th,GSYM INT_SUB]) THEN1
		(ONCE_REWRITE_TAC [GSYM INT_LT_CALCULATE] THEN
		RW_TAC std_ss [INT_ABS] THEN 
		FULL_SIMP_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_NOT_LT,GSYM INT_NEG_GT0,INT_LT_IMP_LE,INT_LT_NEG,GSYM INT_NEG_GE0,INT_NEGNEG] THEN 
		ARITH_TAC));

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

val acl2_floor_def = acl2Define "ACL2::FLOOR" `acl2_floor a b = 
	let q = mult a (reciprocal b) in
	let n = numerator q in
	let d = denominator q in
		ite (equal d (int 1)) n
			(ite (less n (int 0)) 
				(add (unary_minus (acl2_nniq (unary_minus n) d)) (unary_minus (int 1)))
				(acl2_nniq n d))`;

val truncate_def = acl2Define "ACL2::TRUNCATE" `truncate a b = 
	let q = mult a (reciprocal b) in
	let n = numerator q in
	let d = denominator q in
		ite (equal d (int 1)) n
			(ite (less n (int 0)) 
				(unary_minus (acl2_nniq (unary_minus n) d))
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
	REPEAT STRIP_TAC THEN
	`~(& (Num (ABS b)) = 0i)` by 
		(RW_TAC int_ss [INT_ABS] THEN FIRST [ARITH_TAC,METIS_TAC [INT_OF_NUM,INT_LT_IMP_LE,INT_LT_IMP_NE]]) THEN
	`~(frac_nmr (abs_frac (& (Num (ABS b)),1)) = 0)` by RW_TAC int_ss [NMR] THEN
	RW_TAC int_ss [rat_of_int_def,RAT_DIV_CALCULATE,RAT_EQ_CALCULATE,RAT_OF_NUM_CALCULATE,
		FRAC_DIV_CALCULATE,NMR,DNM,SGN_def] THEN
	`(& (Num (ABS a)) = a) /\ (& (Num (ABS b)) = b)` by 
		(RW_TAC int_ss [INT_OF_NUM,INT_LT_IMP_LE,INT_ABS] THEN ARITH_TAC) THEN
	ASM_REWRITE_TAC [] THEN RW_TAC int_ss [NMR,DNM,INT_ABS] THEN ARITH_TAC);

val rat_of_int_neg = 
 store_thm
  ("rat_of_int_neg",
   ``rat_of_int ~x = ~rat_of_int x``,
	RW_TAC std_ss [rat_of_int_def] THEN TRY (`x = 0` by ARITH_TAC) THEN RW_TAC int_ss [RAT_AINV_0,RAT_AINV_AINV,INT_ABS_NEG]);

val rat_of_int_div_pos = 
 store_thm
  ("rat_of_int_div_pos",
   ``0 < b ==> (rat_of_int a / rat_of_int b = abs_rat (abs_frac (a,b)))``,
	Cases_on `0 <= a` THEN RW_TAC std_ss [rat_of_int_div_pos1] THEN
	`?c. (a = ~c) /\ 0 <= c` by (Q.EXISTS_TAC `~a` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
	RW_TAC int_ss [rat_of_int_neg,GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV,RAT_DIV_MULMINV,GSYM RAT_AINV_LMUL] THEN
	RW_TAC int_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos1]);

val rat_of_int_div_neg = 
 store_thm
  ("rat_of_int_div_neg",
   ``b < 0 ==> (rat_of_int a / rat_of_int b = abs_rat (abs_frac (~a,~b)))``,
	DISCH_TAC THEN
	`?c. (b = ~c) /\ 0 < c` by (Q.EXISTS_TAC `~b` THEN RW_TAC int_ss [] THEN ARITH_TAC) THEN
	RW_TAC int_ss [rat_of_int_neg,RAT_DIV_MULMINV,GSYM RAT_AINV_RMUL,GSYM RAT_AINV_MINV,rat_of_int_nz,INT_LT_IMP_NE,
		GSYM FRAC_AINV_CALCULATE,GSYM RAT_AINV_CALCULATE,RAT_EQ_AINV] THEN
	RW_TAC std_ss [GSYM RAT_DIV_MULMINV,rat_of_int_div_pos]);

open dividesTheory gcdTheory;

val both_divides = prove(``(a * b = c) ==> divides a c /\ divides b c``,METIS_TAC [divides_def,MULT_COMM]);

val coprime_equal = prove(``(gcd a d = 1) /\ (gcd b c = 1) /\ (a * b = c * d) ==> (a = c) /\ (b = d)``,
	DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP both_divides) THEN
	FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP both_divides o GSYM) THEN
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
let	val match =  PART_MATCH (fst o dest_eq o dest_neg o last o strip_conj o snd o strip_exists o snd o dest_imp o snd o strip_forall) FACTOR_GCD2 in
(MAP_EVERY (fn x => (STRIP_ASSUME_TAC (SIMP_RULE std_ss (map ASSUME assums) (match x)))) (mk_set (find_gcd goal))) (assums,goal)
end;




val reduce_thm = 
 store_thm
   ("reduce_thm",
    ``0 < b /\ 0 < y /\ ((0 < a /\ 0 < x) \/ (x < 0 /\ a < 0)) /\ (x * b = a * y) ==> 
       (x / & (gcd (Num (ABS x)) (Num (ABS y))) = a / & (gcd (Num (ABS a)) (Num (ABS b)))) 
       /\
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


val neg_reduce_rat = 
 store_thm
  ("neg_reduce_rat",
   ``b < 0 ==> (reduce (rep_frac (rep_rat (rat_of_int a / rat_of_int b))) = reduce (~a,~b))``,
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

val pos_reduce_rat = 
 store_thm
  ("pos_reduce_rat",
   ``0 < b ==> (reduce (rep_frac (rep_rat (rat_of_int a / rat_of_int b))) = reduce (a,b))``,
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


val mod_common = 
 store_thm
  ("mod_common",
   ``0 < b /\ 0 < c ==> ((a MOD b = 0) = ((a * c) MOD (b * c) = 0))``,
	REPEAT STRIP_TAC THEN EQ_TAC THEN
	RW_TAC arith_ss [CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) (GSYM MOD_COMMON_FACTOR)]);

val int_div_common = 
 store_thm
  ("int_div_common",
   ``~(b = 0) /\ ~(c = 0i) ==> (a * & b / (c * & b) = a / c)``,
	REPEAT STRIP_TAC THEN `(a < 0 \/ (a = 0) \/ 0 < a) /\ (c < 0 \/ 0 < c)` by ARITH_TAC THEN 
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	FULL_SIMP_TAC std_ss [INT_NEG_LT0,GSYM INT_NEG_GT0,INT_LT_CALCULATE,GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,
		DECIDE ``0 < a = ~(a = 0n)``,INT_ABS_NEG,NUM_OF_INT,INT_ABS_NUM,INT_NEG_MUL2,INT_MUL,INT_EQ_CALCULATE,INT_DIV_NEG,INT_NEGNEG,INT_DIV,ZERO_DIV] THEN
	RW_TAC int_ss [int_div] THEN
	FULL_SIMP_TAC arith_ss [GSYM DIV_DIV_DIV_MULT,DECIDE ``~(0 < a) = (a = 0n)``,ZERO_DIV,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] THEN
	METIS_TAC [ONCE_REWRITE_RULE [MULT_COMM] mod_common,DECIDE ``0 < a = ~(a = 0n)``]);


val mod_zero_mult = 
 store_thm
  ("mod_zero_mult",
   ``0 < b ==> ((a MOD b = 0) = (b = 1) \/ (?c. a = b * c))``,
	REPEAT STRIP_TAC THEN EQ_TAC THENL [
		Cases_on `b = 1n` THEN RW_TAC arith_ss [] THEN
		ASSUM_LIST (fn list => SUBST_ALL_TAC (SIMP_RULE arith_ss list (DISCH_ALL (CONJUNCT1 (SPEC ``a:num`` (UNDISCH (SPEC ``b:num`` DIVISION))))))),
		ALL_TAC] THEN
	METIS_TAC [MOD_1,MOD_EQ_0,MULT_COMM]);

val gcd_mod = 
 store_thm
  ("gcd_mod",
   ``~(p = q) /\ 1 < q /\ ~(p = 0) /\ ~(q = 0) /\ (gcd p q = 1) ==> ~(p MOD q = 0)``,
	RW_TAC arith_ss [mod_zero_mult] THEN
	CCONTR_TAC THEN FULL_SIMP_TAC arith_ss [] THEN POP_ASSUM SUBST_ALL_TAC THEN
	RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ONCE_REWRITE_RULE [GCD_SYM] GCD_EFFICIENTLY]) THEN
	REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC arith_ss [MOD_EQ_0,GCD_0R]);


local
val match_div1 = prove(``~(q = 0) /\ ~(b = 0) ==> (p * b DIV (q * b) = p DIV q)``,
		METIS_TAC [DECIDE ``0 < a = ~(a = 0n)``,GSYM DIV_DIV_DIV_MULT,MULT_DIV,MULT_COMM]);
val match_div2 = prove(``
		(a = p * c) /\ (b = q * c) /\ ~(p * c = 0) /\ ~(q * c = 0) /\ ~(q = 0n) /\ 
		~(c = 0n) /\ ((q * c) DIV c = 1) ==> 
			((p * c) DIV (q * c) = p)``,
	REPEAT STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN 
	RW_TAC arith_ss [MULT_DIV,CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) MULT_DIV,
		DECIDE ``~(a = 0n) = 0n < a``]);
val match_div3 = prove(``~(c = 0n) /\ ~(p = 0n) ==> ~(0i <= ~&(p * c) / &c)``,
	RW_TAC int_ss [int_div,INT_NOT_LE,ARITH_PROVE ``~a + ~1 < 0 = 0i <= a``] THEN
	METIS_TAC [MULT_DIV,DECIDE ``0 < a = ~(a = 0n)``,MULT_COMM]);
val match_div4 = prove(``~(q * c DIV c = 1) /\ (gcd p q = 1) /\ ~(p = 0) /\ ~(q = 0) /\ ~(c = 0n) ==> 
			~((p * c) MOD (q * c) = 0)``,
	REPEAT STRIP_TAC THEN
	Cases_on `q = 1` THENL [
		FULL_SIMP_TAC arith_ss [DIVMOD_ID,DECIDE ``~(a = 0n) = 0 < a``],
		METIS_TAC [mod_common,gcd_mod,DECIDE ``~(a = 0n) = 0 < a``,GCD_REF,
			DECIDE ``~(a = 0n) /\ ~(a = 1n) = 1n < a``]]);
val match_div5 = prove(``(q * c DIV c = 1) /\ ~(q = 0) /\ ~(c = 0) ==> ((p * c) MOD (q * c) = 0)``,
	RW_TAC std_ss [GSYM mod_common,DECIDE ``~(c = 0n) = 0 < c``] THEN
	FULL_SIMP_TAC arith_ss [MULT_DIV]);
in
val div_tactic = 
	RW_TAC (std_ss ++ boolSimps.LET_ss) [acl2_floor_def,truncate_def,ite_def,TRUTH_REWRITES] THEN
	FULL_SIMP_TAC std_ss [sexp_int_rat,rat_of_int_nz,nmr_dnm_rewrite,GSYM RAT_DIV] THEN
	POP_ASSUM MP_TAC THEN RW_TAC std_ss [sexp_int_rat,rat_of_int_nz,nmr_dnm_rewrite,GSYM RAT_DIV] THEN
	FULL_SIMP_TAC std_ss [GSYM sexp_int_rat,acl2_nniq_rewrite,GSYM INT_UNARY_MINUS,GSYM INT_ADD,
		GSYM INT_EQUAL,GSYM INT_LT,TRUTH_REWRITES,INT_NOT_LT] THEN
	FULL_SIMP_TAC int_ss [INT_NOT_LE] THEN RW_TAC int_ss [GSYM nniq_correct,reduced_dnm_pos,
		ARITH_PROVE ``0 < a ==> 0 <= a /\ ~(a = 0i)``,
		REWRITE_RULE [INT_NEG_GE0] (GSYM (INST [``a:int`` |-> ``~a:int``] nniq_correct)),INT_LT_IMP_LE] THEN
	FULL_SIMP_TAC std_ss [reduced_nmr_def,reduced_dnm_def] THEN
	`0 < b \/ b < 0` by ARITH_TAC THEN
	FULL_SIMP_TAC std_ss [pos_reduce_rat,neg_reduce_rat] THEN AP_TERM_TAC THEN 
	FULL_SIMP_TAC (std_ss ++ boolSimps.LET_ss) [reduce_def,INT_ABS_NEG] THEN
	`0 < a \/ (a = 0) \/ a < 0` by ARITH_TAC THEN
	FULL_SIMP_TAC int_ss [num_abs_nz,GCD_EQ_0,INT_DIV_0,
		ARITH_PROVE ``(0 < a ==> (ABS a = a)) /\ (a < 0 ==> (ABS a = ~a))``] THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r1) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	EVERY_ASSUM (fn th => (SUBST_ALL_TAC o MATCH_MP r2) th THEN ASSUME_TAC th handle _ => ALL_TAC) THEN
	FULL_SIMP_TAC int_ss [DECIDE ``0 < a = ~(a = 0n)``,GCD_0L,GCD_0R,ZERO_DIV] THEN 
	GCD_FACTOR_GOAL THEN
	ASSUM_LIST (fn list => REWRITE_TAC (map (AP_TERM ``int_of_num``) 
		(filter (can (AP_TERM ``int_of_num``)) list))) THEN
	Cases_on `q = 0` THEN FULL_SIMP_TAC int_ss [GCD_0L,GCD_0R] THEN
	RW_TAC int_ss [MULT_DIV,int_div,int_quot,GCD_EQ_0,ZERO_DIV,MOD_EQ_0,
		GSYM (ONCE_REWRITE_RULE [MULT_COMM] DIV_DIV_DIV_MULT)] THEN
	FULL_SIMP_TAC int_ss [] THEN
	METIS_TAC [match_div1,match_div2,match_div3,match_div4,match_div5]
end;

val INT_DIV = prove(``~(b = 0i) ==> (int (a / b) = acl2_floor (int a) (int b))``,div_tactic);

val INT_QUOT = prove(``~(b = 0i) ==> (int (a quot b) = truncate (int a) (int b))``,div_tactic);
	
val NAT_DIV = prove(``~(b = 0n) ==> (nat (a DIV b) = acl2_floor (nat a) (nat b))``,RW_TAC int_ss [nat_def,GSYM INT_DIV]);

val MULT_ZERO = prove(``mult a (num com_0) = int 0``,
	Cases_on `a` THEN RW_TAC std_ss [acl2_floor_def,int_def,cpx_def,sexpTheory.rat_def,mult_def,GSYM com_0_def,GSYM rat_0_def,GSYM frac_0_def] THEN
	Cases_on `c` THEN RW_TAC std_ss [COMPLEX_MULT_def,com_0_def,rat_0_def,GSYM rat_0,RAT_MUL_RZERO,RAT_SUB_RID,RAT_ADD_RID]);

val FLOOR_ZERO = prove(``(acl2_floor a (int 0) = int 0) /\ (truncate a (int 0) = int 0)``,
	RW_TAC (std_ss ++ boolSimps.LET_ss) [acl2_floor_def,truncate_def,
		prove(``int 0 = num com_0``,RW_TAC std_ss [cpx_def,int_def,sexpTheory.rat_def,com_0_def,
		GSYM rat_0_def,GSYM frac_0_def]),reciprocal_def,MULT_ZERO] THEN
	RW_TAC (std_ss ++ boolSimps.LET_ss) [com_0_def,denominator_def,numerator_def,reduced_dnm_def,
		reduced_nmr_def,reduce_def,rat_0_def,frac_0_def] THEN
	RAT_CONG_TAC THEN FULL_SIMP_TAC int_ss [DNM,NMR] THEN
	(SUBGOAL_THEN ``rep_frac x = (0,frac_dnm x)`` SUBST_ALL_TAC THEN1 
		(METIS_TAC [frac_dnm_def,frac_nmr_def,pairTheory.PAIR])) THEN
	RW_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def,FRAC_DNMPOS,gcdTheory.GCD_0L,gcdTheory.GCD_0R,
		snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),
		INT_LT_IMP_LE,INT_ABS_CALCULATE_POS,INT_DIV_0,INT_LT_IMP_NE,equal_def,ite_def,TRUTH_REWRITES] THEN
	RW_TAC std_ss [int_def,cpx_def,sexpTheory.rat_def]);

val INTEGERP_DIV = prove(``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (acl2_floor a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_DIV,INTEGERP_INT,FLOOR_ZERO]);

val INTEGERP_QUOT = prove(``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (truncate a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_QUOT,INTEGERP_INT,FLOOR_ZERO]);

val NATP_DIV = prove(``!a b. (|= natp a) /\ (|= natp b) ==> |= natp (acl2_floor a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	Cases_on `b' = 0` THENL [
		RW_TAC std_ss [nat_def,FLOOR_ZERO],
		RW_TAC std_ss [GSYM NAT_DIV,NATP_NAT]] THEN
	RW_TAC std_ss [GSYM nat_def,NATP_NAT]);

val acl2_mod_def = acl2Define "ACL2::MOD" `acl2_mod x y = add x (unary_minus (mult (acl2_floor x y) y))`;

val acl2_rem_def = acl2Define "ACL2::REM" `acl2_rem x y = add x (unary_minus (mult (truncate x y) y))`;

val INT_MOD = prove(``~(b = 0i) ==> (int (a % b) = acl2_mod (int a) (int b))``,
	RW_TAC int_ss [acl2_mod_def,GSYM INT_DIV,GSYM INT_MULT,GSYM INT_UNARY_MINUS,GSYM INT_ADD,int_mod,int_sub]);

val INT_REM = prove(``~(b = 0i) ==> (int (a rem b) = acl2_rem (int a) (int b))``,
	RW_TAC int_ss [acl2_rem_def,GSYM INT_QUOT,GSYM INT_MULT,GSYM INT_UNARY_MINUS,GSYM INT_ADD,int_rem,int_sub]);

val INTEGERP_MOD = prove(``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (acl2_mod a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_MOD,INTEGERP_INT] THEN
	RW_TAC std_ss [FLOOR_ZERO,acl2_mod_def] THEN
	FULL_SIMP_TAC std_ss [GSYM INT_MULT,GSYM INT_SUB,INTEGERP_INT]);

val INTEGERP_REM = prove(``!a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (acl2_rem a b)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	Cases_on `b' = 0` THEN RW_TAC std_ss [GSYM INT_REM,INTEGERP_INT] THEN
	RW_TAC std_ss [FLOOR_ZERO,acl2_rem_def] THEN
	FULL_SIMP_TAC std_ss [GSYM INT_MULT,GSYM INT_SUB,INTEGERP_INT]);

val NAT_MOD = prove(``~(b = 0n) ==> (nat (a MOD b) = acl2_mod (nat a) (nat b))``,RW_TAC int_ss [nat_def,GSYM INT_MOD]);

val NATP_MOD = prove(``!a b. (|= natp a) /\ (|= natp b) ==> |= natp (acl2_mod a b)``,
	REPEAT STRIP_TAC THEN
	SUBGOAL_THEN ``?a'.a = nat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat a` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	SUBGOAL_THEN ``?b'.b = nat b'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1 (Q.EXISTS_TAC `sexp_to_nat b` THEN RW_TAC std_ss [NAT_OF_SEXP_TO_NAT]) THEN
	Cases_on `b' = 0` THENL [
		RW_TAC std_ss [nat_def,FLOOR_ZERO,acl2_mod_def],
		RW_TAC std_ss [GSYM NAT_MOD,NATP_NAT]] THEN
	FULL_SIMP_TAC std_ss [unary_minus_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,com_0_def,GSYM frac_0_def,GSYM rat_0,rat_0_def,
		COMPLEX_MULT_def,COMPLEX_SUB_def,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID,add_def,COMPLEX_ADD_def,nat_def]);

(****************************************************************************)
(* SGN : int -> int using acl2 function SIGNUM                              *)
(****************************************************************************)

val signum_def = acl2Define "ACL2::SIGNUM" 
	`signum x = ite (equal x (int 0)) (int 0) (ite (less x (int 0)) (int ~1) (int 1))`;

val INT_SGN = prove(``int (SGN x) = signum (int x)``,
	RW_TAC int_ss [ite_def,GSYM INT_EQUAL,GSYM INT_LT,SGN_def,signum_def,TRUTH_REWRITES,bool_def]);

val INTEGERP_SGN = prove(``!x. (|= integerp x) ==> |= integerp (signum x)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM INT_SGN,INTEGERP_INT]);

(*****************************************************************************)
(* even and odd for natural numbers using acl2 functions evenp and oddp      *)
(*****************************************************************************)

val evenp_def = acl2Define "ACL2::EVENP" `evenp x = integerp (mult x (reciprocal (int 2)))`;

val oddp_def = acl2Define "ACL2::ODDP" `oddp x = not (evenp x)`;

val nat_rat = prove(``!a. nat a = rat (& a)``,
	RW_TAC std_ss [nat_def,int_def,rat_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,rat_0,RAT_OF_NUM_CALCULATE]);

val int_rat_n = prove(``!a. int (& a) = rat (& a)``,
	RW_TAC std_ss [nat_def,int_def,rat_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,rat_0,RAT_OF_NUM_CALCULATE]);

val rat_2_nz = prove(``~(0 = 2:rat)``,RW_TAC int_ss [RAT_EQ_CALCULATE,RAT_OF_NUM_CALCULATE,NMR,DNM]);

val NAT_EVEN = prove(``bool (EVEN a) = evenp (nat a)``,
	Cases_on `EVEN a` THEN
	RW_TAC std_ss [bool_def,evenp_def,TRUTH_REWRITES,integerp_def,nat_rat,GSYM RAT_DIV,int_rat_n,rat_2_nz] THEN
	RULE_ASSUM_TAC (REWRITE_RULE [GSYM ODD_EVEN]) THEN
	IMP_RES_TAC EVEN_EXISTS THEN IMP_RES_TAC ODD_EXISTS THEN
	RW_TAC std_ss [rat_def,integerp_def,TRUTH_REWRITES,IS_INT_EXISTS,rat_2_nz,RAT_LDIV_EQ,GSYM RAT_MUL_NUM_CALCULATE, GSYM RAT_ADD_NUM_CALCULATE,ADD1,RAT_EQ_LMUL] THENL [
		METIS_TAC [RAT_OF_NUM_CALCULATE],
		RW_TAC int_ss [RAT_EQ_CALCULATE,RAT_OF_NUM_CALCULATE,RAT_ADD_CALCULATE,RAT_MUL_CALCULATE,frac_mul_def,frac_add_def,NMR,DNM]] THEN
	ARITH_TAC);

val NAT_ODD = prove(``bool (ODD a) = oddp (nat a)``,RW_TAC std_ss [oddp_def,GSYM NAT_EVEN,bool_def,TRUTH_REWRITES,not_def,ite_def,EVEN_ODD]);
	

val BOOLEANP_EVEN = prove(``!x. |= booleanp (evenp x)``,
	GEN_TAC THEN Cases_on `mult x (reciprocal (int 2))` THEN 
	RW_TAC std_ss [evenp_def,integerp_def,ite_def,TRUTH_REWRITES,booleanp_def,equal_def]);

val BOOLEANP_ODD = prove(``!x. |= booleanp (oddp x)``,
	RW_TAC std_ss [oddp_def,BOOLEANP_EVEN,BOOLEANP_NOT]);



(*****************************************************************************)
(* Arithmetic shift left for int and num using acl2 function ASH             *)
(*****************************************************************************) 

val acl2_ash_def = acl2Define "ACL2::ASH" `acl2_ash i c = acl2_floor (mult (ifix i) (acl2_expt (int 2) c)) (int 1)`;

val NAT_ASL = prove(``nat (i * 2 ** c) = acl2_ash (nat i) (nat c)``,
	RW_TAC int_ss [acl2_ash_def,nat_def,GSYM INT_EXP,GSYM INT_MULT,ifix_def,ite_def,
		TRUTH_REWRITES,INTEGERP_INT,GSYM INT_DIV]);

val INT_ASL = prove(``int (i * 2 ** c) = acl2_ash (int i) (nat c)``,
	RW_TAC int_ss [acl2_ash_def,nat_def,GSYM INT_EXP,GSYM INT_MULT,ifix_def,ite_def,
		TRUTH_REWRITES,INTEGERP_INT,GSYM INT_DIV]);

val NATP_ASH = prove(``(|= natp i) /\ (|= natp c) ==> |= natp (acl2_ash i c)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM NAT_ASL,NATP_NAT]);

val INTEGERP_ASH = prove(``(|= natp c) ==> |= integerp (acl2_ash i c)``,
	Cases_on `|= integerp i` THEN
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
	RW_TAC std_ss [GSYM INT_ASL,INTEGERP_INT] THEN
	FULL_SIMP_TAC std_ss [acl2_ash_def,ifix_def,ite_def,TRUTH_REWRITES] THEN
	METIS_TAC [INTEGERP_DIV,INTEGERP_EXP,INTEGERP_MULT,nat_def,INTEGERP_INT]);

(*****************************************************************************)
(* Maximum and minimum theories for int and num,                             *)
(* using acl2 functions max and min                                          *)
(*****************************************************************************)

val acl2_max_def = acl2Define "ACL2::MAX" `acl2_max x y = ite (less y x) x y`;
val acl2_min_def = acl2Define "ACL2::MIN" `acl2_min x y = ite (less x y) x y`;

val NAT_MAX = prove(``nat (MAX x y) = acl2_max (nat x) (nat y)``,
	RW_TAC arith_ss [acl2_max_def,MAX_DEF,GSYM NAT_LT,ite_def,TRUTH_REWRITES] THEN AP_TERM_TAC THEN DECIDE_TAC);

val NAT_MIN = prove(``nat (MIN x y) = acl2_min (nat x) (nat y)``,
	RW_TAC arith_ss [acl2_min_def,MIN_DEF,GSYM NAT_LT,ite_def,TRUTH_REWRITES] THEN AP_TERM_TAC THEN DECIDE_TAC);

val INT_MAX = prove(``int (int_max x y) = acl2_max (int x) (int y)``,
	RW_TAC int_ss [acl2_max_def,INT_MAX,GSYM INT_LT,ite_def,TRUTH_REWRITES] THEN AP_TERM_TAC THEN ARITH_TAC);

val INT_MIN = prove(``int (int_min x y) = acl2_min (int x) (int y)``,
	RW_TAC int_ss [acl2_min_def,INT_MIN,GSYM INT_LT,ite_def,TRUTH_REWRITES] THEN AP_TERM_TAC THEN ARITH_TAC);


val NATP_MAX = prove(``!x y. (|= natp x) /\ (|= natp y) ==> |= natp (acl2_max x y)``,
	RW_TAC std_ss [acl2_max_def,ite_def,TRUTH_REWRITES]);

val NATP_MIN = prove(``!x y. (|= natp x) /\ (|= natp y) ==> |= natp (acl2_min x y)``,
	RW_TAC std_ss [acl2_min_def,ite_def,TRUTH_REWRITES]);

val INTEGERP_MAX = prove(``!x y. (|= integerp x) /\ (|= integerp y) ==> |= integerp (acl2_max x y)``,
	RW_TAC std_ss [acl2_max_def,ite_def,TRUTH_REWRITES]);

val INTEGERP_MIN = prove(``!x y. (|= integerp x) /\ (|= integerp y) ==> |= integerp (acl2_min x y)``,
	RW_TAC std_ss [acl2_min_def,ite_def,TRUTH_REWRITES]);

(*****************************************************************************)
(* ABS:int -> int, using acl2 function ABS                                   *)
(*****************************************************************************)

val acl2_abs_def = acl2Define "ACL2::ABS" `acl2_abs x = ite (less x (int 0)) (unary_minus x) x`;

val INT_ABS = prove(``int (ABS x) = acl2_abs (int x)``,
	RW_TAC int_ss [INT_ABS,acl2_abs_def,GSYM INT_UNARY_MINUS,GSYM INT_LT,ite_def,TRUTH_REWRITES]);

val INTEGERP_ABS = prove(``!x. (|= integerp x) ==> |= integerp (acl2_abs x)``,
	REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN RW_TAC std_ss [GSYM INT_ABS,INTEGERP_INT]);

(*****************************************************************************)
(* List theorems:                                                            *)
(*                                                                           *)
(* acl2 functions: binary-append, revappend, reverse, take, nthcdr, butlast, *)
(*                 nth, last, strip_cars, strip_cdrs, pairlis$               *)
(*                                                                           *)
(*****************************************************************************)

val zp_less = prove(``!n. (zp n = nil) ==> (sexp_to_nat (add n (unary_minus (nat 1))) < sexp_to_nat n)``,
	GEN_TAC THEN Cases_on `|= natp n` THENL [
			CHOOSEP_TAC THEN 
			RW_TAC std_ss [TRUTH_REWRITES,GSYM NAT_EQUAL_0] THEN
			RW_TAC int_ss [GSYM INT_ADD,GSYM INT_UNARY_MINUS,nat_def,sexp_to_nat_def,SEXP_TO_INT_OF_INT,
					GSYM int_sub,integerTheory.INT_SUB],
			Cases_on `n` THEN
			TRY (Cases_on `c`) THEN 
			RW_TAC std_ss [zp_def,ite_def,integerp_def,TRUTH_REWRITES,IS_INT_EXISTS,GSYM int_def] THEN 
			FULL_SIMP_TAC int_ss [RAT_EQ_CALCULATE,NMR,DNM,GSYM sexpTheory.rat_def,
				GSYM cpx_def,GSYM int_def,rat_0_def,frac_0_def,GSYM INT_LT,not_def,ite_def,
				TRUTH_REWRITES,natp_def,INTEGERP_INT,nat_def]]);

val zp_comm = prove(``add (unary_minus (nat 1)) n = add n (unary_minus (nat 1))``,
	Cases_on `n` THEN TRY (Cases_on `c`) THEN 
	RW_TAC std_ss [nat_def,GSYM INT_UNARY_MINUS] THEN 
	RW_TAC std_ss [int_def,cpx_def,sexpTheory.rat_def,add_def,COMPLEX_ADD_def,RAT_ADD_COMM]);

val (acl2_append_def,acl2_append_ind) = 
	acl2_defn "ACL2::BINARY-APPEND" 
		(`acl2_append x y = ite (consp x) (cons (car x) (acl2_append (cdr x) y)) y`,
		WF_REL_TAC `measure (sexp_size o FST)` THEN
		Cases THEN RW_TAC arith_ss [cdr_def,nil_def,consp_def,sexp_size_def]);

val LIST_APPEND = prove(``list f (x ++ y) = acl2_append (list f x) (list f y)``,
	Induct_on `x` THEN ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [APPEND,list_def,consp_def,ite_def,TRUTH_REWRITES,car_def,cdr_def]);

val LISTP_APPEND = prove(``!x y. (|= listp f x) /\ (|= listp f y) ==> |= listp f (acl2_append x y)``,
	Induct_on `x` THEN ONCE_REWRITE_TAC [acl2_append_def] THEN 
	RW_TAC std_ss [consp_def,ite_def,TRUTH_REWRITES,car_def,cdr_def,listp_def]);

val NATP_LEN = prove(``!x. |= natp (len x)``,
	Induct THEN ONCE_REWRITE_TAC [len_def] THEN RW_TAC std_ss [ite_def,consp_def,NATP_NAT,car_def,cdr_def,NATP_ADD]);

val (acl2_revappend_def,acl2_revappend_ind) = 
	(PURE_REWRITE_RULE [GSYM ite_def] ## I)
	(acl2_defn "ACL2::REVAPPEND" 
		(`acl2_revappend x y = if (consp x = nil) then y else acl2_revappend (cdr x) (cons (car x) y)`,
		WF_REL_TAC `measure (sexp_size o FST)` THEN 
		Cases THEN RW_TAC arith_ss [cdr_def,nil_def,consp_def,sexp_size_def]));

val consp_revappend1 = prove(``!a b c. |= consp (acl2_revappend (cons a b) c)``,
	Induct_on `b` THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN 
	RW_TAC std_ss [consp_def,TRUTH_REWRITES,ite_def,car_def,cdr_def] THEN 
	ONCE_REWRITE_TAC [acl2_revappend_def] THEN RW_TAC std_ss [consp_def,TRUTH_REWRITES,ite_def,car_def,cdr_def]);

val cons_append = prove(``!a b c. cons a (acl2_append b c) = acl2_append (cons a b) c``,
	Induct_on `b` THEN ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [car_def,cdr_def,consp_def,ite_def,TRUTH_REWRITES] THEN
	TRY (ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [car_def,cdr_def,consp_def,ite_def,TRUTH_REWRITES] THEN NO_TAC));

val nil_append = prove(``!a. acl2_append nil a = a``,ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [ite_def,consp_def,TRUTH_REWRITES,AP_TERM ``consp`` nil_def]);

val consp_append = prove(``!a b. (|= consp (acl2_append a b)) = (|= consp a) \/ |= consp b``,
	ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [consp_def,ite_def,TRUTH_REWRITES] THEN PROVE_TAC []);

val nconsp_append = prove(``!a b. (~|= consp a) ==> (acl2_append a b = b)``,ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES]);

val append_assoc = prove(``!a b c. acl2_append a (acl2_append b c) = acl2_append (acl2_append a b) c``,
	Induct_on `a` THEN ONCE_REWRITE_TAC [acl2_append_def] THEN RW_TAC std_ss [consp_def,ite_def,TRUTH_REWRITES,consp_append,nconsp_append,car_def,cdr_def] THEN
	RW_TAC std_ss [cons_append,prove(``!a. (|= consp a) ==> (cons (car a) (cdr a) = a)``,Cases THEN RW_TAC std_ss [car_def,cdr_def,consp_def,TRUTH_REWRITES])] THENL [
		ONCE_REWRITE_TAC [acl2_append_def],
		GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV) bool_rewrites [acl2_append_def]] THEN
	RW_TAC std_ss [consp_def,ite_def,TRUTH_REWRITES,car_def,cdr_def]);

val acl2_reverse_def = 
	acl2Define "ACL2::REVERSE" 
		`acl2_reverse x = 
			ite (stringp x) 
				(coerce (acl2_revappend 
					(coerce x (sym "COMMON-LISP" "LIST")) nil) (sym "COMMON-LISP" "STRING"))
				(acl2_revappend x nil)`;

	
val revappend_append = prove(``!x y. acl2_revappend (list f x) y = acl2_append (acl2_reverse (list f x)) y``,
	Induct_on `x` THEN 
	REWRITE_TAC [acl2_reverse_def] THEN 
	ONCE_REWRITE_TAC [acl2_revappend_def,acl2_append_def] THEN 
	RW_TAC std_ss [list_def,ite_def,TRUTH_REWRITES,consp_def,AP_TERM ``consp`` nil_def,stringp_def,AP_TERM ``stringp`` nil_def,car_def,cdr_def,consp_revappend1] THENL [
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [acl2_revappend_def]) THEN FULL_SIMP_TAC std_ss [consp_def,AP_TERM ``consp`` nil_def,TRUTH_REWRITES],
		ONCE_REWRITE_TAC [acl2_revappend_def] THEN RW_TAC std_ss [ite_def,consp_def,TRUTH_REWRITES,cdr_def,car_def,cons_append] THEN
		SUBGOAL_THEN ``|= consp (acl2_append (acl2_reverse (list f x)) (cons (f h) nil))`` 
			(fn th => ASM_REWRITE_TAC [GSYM append_assoc,MATCH_MP (prove(``!a. (|= consp a) ==> (cons (car a) (cdr a) = a)``,Cases THEN RW_TAC std_ss [car_def,cdr_def,consp_def,TRUTH_REWRITES])) th]) THEN1
			(RW_TAC std_ss [consp_append,consp_def,TRUTH_REWRITES])] THEN
	RW_TAC std_ss [GSYM cons_append,nil_append]);


val LIST_REVERSE = prove(``list f (REVERSE l) = acl2_reverse (list f l)``,
	Induct_on `l` THEN 
	RW_TAC std_ss [acl2_reverse_def,stringp_def,list_def,REVERSE_DEF,ite_def,TRUTH_REWRITES] THEN 
	ONCE_REWRITE_TAC [acl2_revappend_def] THEN 
	RW_TAC std_ss [cdr_def,car_def,ite_def,TRUTH_REWRITES,stringp_def,
		AP_TERM ``stringp`` nil_def,consp_def,LIST_APPEND,list_def,revappend_append]);

val LISTP_REVAPPEND = prove(``!x y. (|= listp f x) /\ (|= listp f y) ==> |= listp f (acl2_revappend x y)``,
	Induct THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN 
	RW_TAC std_ss [listp_def,car_def,consp_def,ite_def,TRUTH_REWRITES,cdr_def]);

val equal_nil_eq = prove(``(|= equal x nil) = (x = nil)``,
	Cases_on `x` THEN RW_TAC std_ss [equal_def,ACL2_TRUE_def,nil_def,t_def,ite_def] THEN
	REPEAT (POP_ASSUM MP_TAC THEN RW_TAC std_ss [DE_MORGAN_THM]));

val LISTP_REVERSE = prove(``!l. (|= listp f l) ==> (|= listp f (acl2_reverse l))``,
	Induct THEN RW_TAC std_ss [acl2_reverse_def,LISTP_REVAPPEND,ite_def,TRUTH_REWRITES,stringp_def,listp_def] THEN
	FULL_SIMP_TAC std_ss [equal_nil_eq,LISTP_NIL,LISTP_REVAPPEND] THEN
	FULL_SIMP_TAC std_ss [nil_def,sexp_distinct] THEN
	METIS_TAC [LISTP_CONS,LISTP_REVAPPEND,nil_def,LISTP_NIL]);

val (firstnac_def,firstnac_ind) = 
	acl2_defn "ACL2::FIRST-N-AC" 
		(`firstnac i l ac = 
			ite (zp i) 
				(acl2_reverse ac) 
				(firstnac (add (unary_minus (nat 1)) i) (cdr l) (cons (car l) ac))`,
		WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
		METIS_TAC [zp_less,zp_comm]);

val acl2_take_def = acl2Define "ACL2::TAKE" `acl2_take n l = firstnac n l nil`;


val reverse_nil = prove(``acl2_reverse nil = nil``,
	REWRITE_TAC [acl2_reverse_def] THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN 
	RW_TAC std_ss [ite_def,stringp_def,TRUTH_REWRITES,AP_TERM ``stringp`` nil_def]);

val stringp_revappend1 = prove(``!a b. (~|= stringp a) ==> ~|= stringp (acl2_revappend b a)``,
	Induct_on `b` THEN ONCE_REWRITE_TAC [acl2_revappend_def] THEN 
	RW_TAC std_ss [car_def,cdr_def,consp_def,TRUTH_REWRITES,ite_def,stringp_def]);

val stringp_revappend = prove(``!a b. ~|= stringp (acl2_revappend b (cons a nil))``,
	REPEAT GEN_TAC THEN MATCH_MP_TAC stringp_revappend1 THEN 
	RW_TAC std_ss [stringp_def,TRUTH_REWRITES]);

val sym_nil = prove(``~(|= sym s s0) = (sym s s0 = nil)``,
	RW_TAC std_ss [ite_def,equal_def,ACL2_TRUE_def,nil_def,t_def] THEN REPEAT (POP_ASSUM MP_TAC) THEN 
	RW_TAC std_ss [] THEN METIS_TAC []);


val firstnac_lemma = prove(``!n l a b. n <= LENGTH l ==> (cons (f a) (firstnac (nat n) (list f l) (list f b)) = 
		firstnac (nat n) (list f l) (acl2_reverse (cons (f a) (acl2_reverse (list f b)))))``,
	Induct_on `l` THEN ONCE_REWRITE_TAC [firstnac_def] THEN 
	RW_TAC std_ss [LENGTH,list_def,car_def,cdr_def,AP_TERM ``car`` nil_def,AP_TERM ``cdr`` nil_def,
			TRUTH_REWRITES,GSYM NAT_EQUAL_0,ite_def] THEN
	FULL_SIMP_TAC int_ss [GSYM list_def,GSYM LIST_REVERSE,REVERSE_REVERSE,
				GSYM INT_ADD,GSYM INT_UNARY_MINUS,nat_def,
				GSYM (CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV INT_ADD_COMM)) int_sub),
				integerTheory.INT_SUB,DECIDE ``~(n = 0n) ==> 1 <= n``] THEN
	SUBGOAL_THEN ``h::REVERSE (a::REVERSE b) = REVERSE (a::REVERSE (h::b))`` SUBST_ALL_TAC THEN1
		RW_TAC std_ss [REVERSE_DEF,APPEND,REVERSE_REVERSE,APPEND_ASSOC] THEN
	REFL_TAC);

val reversed_nil = prove(``acl2_reverse (cons (f h) (acl2_reverse nil)) = cons (f h) nil``,
	REWRITE_TAC [prove(``nil = list f []``,RW_TAC std_ss [list_def])] THEN
	RW_TAC std_ss [GSYM LIST_REVERSE,GSYM list_def,REVERSE_DEF,APPEND]);

val LIST_FIRSTN = prove(``!n l. (n <= LENGTH l) ==> (list f (FIRSTN n l) = acl2_take (nat n) (list f l))``,
	Induct_on `l` THEN REWRITE_TAC [acl2_take_def] THEN ONCE_REWRITE_TAC [firstnac_def] THEN 
	RW_TAC std_ss [ite_def,list_def,FIRSTN,LENGTH,GSYM NAT_EQUAL_0,TRUTH_REWRITES,reverse_nil] THEN
	RW_TAC std_ss [list_def,FIRSTN,TRUTH_REWRITES] THEN
	Cases_on `n` THEN 
	FULL_SIMP_TAC int_ss [FIRSTN,list_def,nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,
			GSYM (CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV INT_ADD_COMM)) int_sub),integerTheory.INT_SUB,
			ADD1,car_def,cdr_def,acl2_take_def] THEN
	RW_TAC std_ss [REWRITE_RULE [list_def] (SPECL [``n:num``,``l:'a list``,``a:'a``,``[]:'a list``] firstnac_lemma),
			GSYM nat_def,reversed_nil]);

val pre_sym = prove(``~(a = 0) ==> (add (unary_minus (nat 1)) (nat a) = nat (PRE a))``,
	Cases_on `a` THEN RW_TAC int_ss [nat_def,GSYM INT_UNARY_MINUS,GSYM INT_ADD,ADD1] THEN
	AP_TERM_TAC THEN ARITH_TAC);

val len_rewrite = GSYM (SIMP_RULE std_ss [NAT_OF_SEXP_TO_NAT,SEXP_TO_NAT_OF_NAT,NATP_LEN] 
			(AP_TERM ``sexp_to_nat`` (SPECL [``a:num``,``sexp_to_nat (len l)``] NAT_ADD)));
val listp_firstnac = 
	prove(``!x l ac. x <= sexp_to_nat (len l) /\ (|= listp f l) /\ (|= listp f ac) ==> 
			(|= listp f (firstnac (nat x) l ac))``,
	Induct THEN ONCE_REWRITE_TAC [firstnac_def] THEN 
	RW_TAC std_ss [ite_def,GSYM NAT_EQUAL_0,pre_sym,car_def,cdr_def,TRUTH_REWRITES,LISTP_REVERSE] THEN
	Cases_on `l` THEN PAT_ASSUM ``a <= b:num`` MP_TAC THEN 
	ONCE_REWRITE_TAC [len_def] THEN 
	RW_TAC std_ss [ite_def,TRUTH_REWRITES,consp_def,SEXP_TO_NAT_OF_NAT] THEN 
	FULL_SIMP_TAC arith_ss [listp_def,car_def,cdr_def,ite_def,TRUTH_REWRITES,len_rewrite,ADD1]);

val LISTP_TAKE = prove(``!x l. (|= not (less (len l) x)) /\ (|= listp f l) /\ (|= natp x) ==> 
					|= listp f (acl2_take x l)``,
	REPEAT STRIP_TAC THEN
	CHOOSEP_TAC THEN
	RW_TAC std_ss [] THEN
	FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [NAT_OF_SEXP_TO_NAT,NATP_LEN] 
				(SPEC ``sexp_to_nat (len l)`` (GEN_ALL (GSYM NAT_LE))),
		GSYM NAT_LT,acl2_take_def,TRUTH_REWRITES,listp_firstnac,LISTP_NIL]);

val (nthcdr_def,nthcdr_ind) =
	acl2_defn "ACL2::NTHCDR" 
		(`nthcdr n l = ite (zp n) l (nthcdr (add n (unary_minus (nat 1))) (cdr l))`,
		WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
		METIS_TAC [zp_less,zp_comm]);

val LIST_BUTFIRSTN = prove(``!n l. n <= LENGTH l ==> (list f (BUTFIRSTN n l) = nthcdr (nat n) (list f l))``,
	Induct_on `l` THEN Cases_on `n` THEN 
	ONCE_REWRITE_TAC [nthcdr_def] THEN 
	RW_TAC arith_ss [BUTFIRSTN,list_def,LENGTH,TRUTH_REWRITES,GSYM NAT_EQUAL_0,ite_def,GSYM NAT_PRE,cdr_def]);

val LISTP_NTHCDR = prove(``!n l. (|= listp f l) ==> |= listp f (nthcdr n l)``,
	GEN_TAC THEN Cases_on `|= natp n` THENL [
		CHOOSEP_TAC THEN Induct_on `n'` THEN ONCE_REWRITE_TAC [nthcdr_def] THEN
		RW_TAC std_ss [ite_def,GSYM NAT_PRE,zp_def,GSYM int_def,GSYM nat_def,
			GSYM NAT_LT,GSYM BOOL_NOT,TRUTH_REWRITES,
			prove(``|= integerp (nat a)``,RW_TAC std_ss [nat_def,INTEGERP_INT])] THEN
		METIS_TAC [NATP_NAT,LISTP_TAIL],
		Cases_on `|= zp n` THENL [
			ONCE_REWRITE_TAC [nthcdr_def] THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES],
			CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC)]] THEN 
	RW_TAC std_ss [natp_def,zp_def,ite_def,TRUTH_REWRITES,GSYM int_def] THEN RW_TAC std_ss [] THEN
	Cases_on `|= integerp n` THEN RW_TAC std_ss [] THEN CHOOSEP_TAC THEN 
	FULL_SIMP_TAC std_ss [GSYM INT_LT,GSYM BOOL_NOT,TRUTH_REWRITES,GSYM INT_EQUAL,nat_def]);

val acl2_butlast_def = 
	acl2Define "ACL2::BUTLAST" 
		`acl2_butlast l n = 
			let lng = len l in 
			ite (less n lng) (acl2_take (add lng (unary_minus n)) l) nil`;
		
val LIST_BUTLASTN = prove(``!n l. n <= LENGTH l ==> (list f (BUTLASTN n l) = acl2_butlast (list f l) (nat n))``,
	RW_TAC (int_ss ++ boolSimps.LET_ss) [BUTLASTN_FIRSTN,acl2_butlast_def,nat_def,GSYM INT_SUB,
		GSYM LIST_LENGTH,ite_def,GSYM INT_LT,TRUTH_REWRITES,NOT_LESS] THENL [
			SUBGOAL_THEN ``LENGTH l - n = 0`` SUBST_ALL_TAC THEN1 DECIDE_TAC THEN
			RW_TAC int_ss [FIRSTN,list_def,TRUTH_REWRITES],
			RW_TAC int_ss [integerTheory.INT_SUB,GSYM nat_def,LIST_FIRSTN]]);

val LISTP_BUTLAST = prove(``!x l. (|= listp f l) /\ (|= natp x) ==> 
					|= listp f (acl2_butlast l x)``,
	REPEAT STRIP_TAC THEN
	RW_TAC (std_ss ++ boolSimps.LET_ss) [acl2_butlast_def,ite_def,TRUTH_REWRITES,LISTP_NIL] THEN 
	MATCH_MP_TAC LISTP_TAKE THEN
	ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN
	CHOOSEP_TAC THEN
	FULL_SIMP_TAC int_ss [nat_def,GSYM INT_LT,GSYM INT_SUB,natp_def,ite_def,TRUTH_REWRITES,
		INTEGERP_INT,GSYM INT_EQUAL,GSYM BOOL_NOT] THEN
	ARITH_TAC);
	
val LIST_LASTN = prove(``!n l. n <= LENGTH l ==> (list f (LASTN n l) = nthcdr (nat (LENGTH l - n)) (list f l))``,
	RW_TAC arith_ss [LASTN_BUTFIRSTN,GSYM LIST_BUTFIRSTN]);

val (nth_def,nth_ind) = 
	acl2_defn "ACL2::NTH" 
		(`nth n l = ite (consp l) (ite (zp n) (car l) (nth (add (unary_minus (nat 1)) n) (cdr l))) nil`,
		WF_REL_TAC `measure (sexp_to_nat o FST)` THEN
		METIS_TAC [zp_less,zp_comm]);

val LIST_EL = prove(``!n l. n < LENGTH l ==> (encode (EL n l) = nth (nat n) (list encode l))``,
	Induct_on `n` THEN Cases_on `l` THEN ONCE_REWRITE_TAC [nth_def] THEN 
	FULL_SIMP_TAC arith_ss [EL,HD,TL,car_def,cdr_def,list_def,LENGTH,ite_def,TRUTH_REWRITES,
		GSYM NAT_EQUAL_0,consp_def,zp_comm,GSYM NAT_PRE]);

val LISTP_NTH = prove(``!n l. (|= less n (len l)) /\ (|= natp n) /\ (|= listp f l) ==> (|= f (nth n l))``,
	Induct_on `l` THEN RW_TAC std_ss [listp_def,equal_nil_eq] THEN CHOOSEP_TAC THEN
	TRY (	RULE_ASSUM_TAC (ONCE_REWRITE_RULE [len_def]) THEN 
		FULL_SIMP_TAC arith_ss [ite_def,nil_def,consp_def,GSYM NAT_LT] THEN
		FULL_SIMP_TAC std_ss [TRUTH_REWRITES] THEN NO_TAC) THEN
	ONCE_REWRITE_TAC [nth_def] THEN 
	FULL_SIMP_TAC std_ss [ONCE_REWRITE_CONV [len_def] ``len (cons a b)``,GSYM NAT_LT,NATP_NAT,ite_def,
		TRUTH_REWRITES,consp_def,cdr_def] THEN
	REPEAT (POP_ASSUM MP_TAC) THEN STRIP_ASSUME_TAC (SPEC ``l':sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN
	RW_TAC std_ss [nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,GSYM INT_LT,zp_def,ite_def,
		TRUTH_REWRITES,GSYM int_def,GSYM BOOL_NOT,car_def] THEN
	FIRST_ASSUM MATCH_MP_TAC THEN
	RW_TAC int_ss [GSYM INT_LT,TRUTH_REWRITES,natp_def,INTEGERP_INT,ite_def,nat_def,GSYM INT_EQUAL] THEN
	ARITH_TAC);

val acl2_subseq_def = acl2Define "ACL2::SUBSEQ-LIST" 
	`acl2_subseq lst start end = acl2_take (nfix (add end (unary_minus start))) (nthcdr start lst)`;

val LIST_SEG = prove(``n + s <= LENGTH l ==> (list f (SEG n s l) = acl2_subseq (list f l) (nat s) (nat (n + s)))``,
	RW_TAC arith_ss [SEG_FIRSTN_BUTFISTN,acl2_subseq_def,LIST_BUTFIRSTN,LENGTH_BUTFIRSTN,LIST_FIRSTN] THEN
	RW_TAC int_ss [GSYM NAT_SUB]);

val len_cons = prove(``len (cons a b) = add (int 1) (len b)``,
	RW_TAC std_ss [ONCE_REWRITE_CONV [len_def] ``len (cons a b)``,ite_def,TRUTH_REWRITES,consp_def,cdr_def,nat_def]);

val zp_rewrite = prove(``(|= zp (nat n)) = (n = 0)``,
	RW_TAC int_ss [zp_def,integerp_def,GSYM int_def,nat_def,GSYM INT_LT,GSYM BOOL_NOT,ite_def,
		TRUTH_REWRITES,INTEGERP_INT]);

val len_nth = 
	prove(``!n l. (|= not (less (len l) (nat n))) ==> (len (nthcdr (nat n) l) = add (len l) (unary_minus (nat n)))``,
	Induct_on `l` THEN REPEAT STRIP_TAC THEN
	TRY (ONCE_REWRITE_TAC [len_def] THEN ONCE_REWRITE_TAC [nthcdr_def] THEN 
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [len_def]) THEN 
		FULL_SIMP_TAC arith_ss [ite_def,TRUTH_REWRITES,consp_def,GSYM NAT_LT,GSYM BOOL_NOT,cdr_def] THEN
		SUBGOAL_THEN ``n = 0n`` SUBST_ALL_TAC THEN1 DECIDE_TAC THEN 
		RW_TAC int_ss [nat_def,GSYM INT_SUB,zp_def,GSYM int_def,INTEGERP_INT,GSYM INT_LT,ite_def,
			TRUTH_REWRITES,GSYM BOOL_NOT,consp_def] THEN NO_TAC) THEN
	ONCE_REWRITE_TAC [nthcdr_def] THEN FULL_SIMP_TAC std_ss [len_cons,ite_def,TRUTH_REWRITES,zp_rewrite,cdr_def] THEN
	RW_TAC int_ss [nat_def,GSYM INT_ADD,len_cons,GSYM INT_UNARY_MINUS] THEN
	ASSUME_TAC (SPEC ``l':sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN 
	FULL_SIMP_TAC int_ss [GSYM INT_ADD,nat_def,GSYM INT_LT,GSYM BOOL_NOT,TRUTH_REWRITES,
		integerTheory.INT_SUB,GSYM int_sub] THEN
	`~(x < n - 1)` by ARITH_TAC THEN RES_TAC THEN
	POP_ASSUM SUBST_ALL_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM INT_SUB] THEN AP_TERM_TAC THEN
	Cases_on `n` THEN FULL_SIMP_TAC int_ss [ADD1] THEN ARITH_TAC);


val subseq_lem1 = 
	prove(``a <= b /\ (|= not (less (len l) (nat b))) ==> |= not (less (len (nthcdr (nat a) l)) (nat (b - a)))``,
		REPEAT STRIP_TAC THEN
		`|= not (less (len l) (nat a))` by 
			(ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN 
			FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM BOOL_NOT,nat_def,TRUTH_REWRITES]) THEN
		RW_TAC arith_ss [len_nth] THEN
		ASSUME_TAC (SPEC ``l:sexp`` NATP_LEN) THEN CHOOSEP_TAC THEN 
		FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM BOOL_NOT,nat_def,TRUTH_REWRITES,GSYM INT_SUB,NOT_LESS,
			integerTheory.INT_SUB]);

val nthcdr_nil = prove(``nthcdr n nil = nil``,
	Cases_on `|= natp n` THENL [
		CHOOSEP_TAC THEN FULL_SIMP_TAC std_ss [NATP_NAT] THEN Induct_on `n'`,
		ALL_TAC] THEN
	ONCE_REWRITE_TAC [nthcdr_def] THEN 
	RW_TAC int_ss [ite_def,zp_rewrite,TRUTH_REWRITES,nat_def,GSYM INT_SUB,ADD1,integerTheory.INT_SUB,
		cdr_def,AP_TERM ``cdr`` nil_def] THEN
	FULL_SIMP_TAC std_ss [TRUTH_REWRITES,nat_def,natp_def,zp_def,ite_def,GSYM int_def] THEN
	Cases_on `|= integerp n` THEN TRY CHOOSEP_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM INT_LT,GSYM INT_EQUAL,TRUTH_REWRITES,GSYM BOOL_NOT]);



val subseq_lem2 = prove(``!l s. ~(|= not (less (len l) (nat s))) ==> (len (nthcdr (nat s) l) = nat 0)``,
	Induct_on `l` THEN REPEAT STRIP_TAC THEN
	TRY (ONCE_REWRITE_TAC [len_def] THEN ONCE_REWRITE_TAC [nthcdr_def] THEN 
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [len_def]) THEN 
		FULL_SIMP_TAC arith_ss [ite_def,TRUTH_REWRITES,consp_def,GSYM NAT_LT,GSYM BOOL_NOT,cdr_def,
			zp_rewrite,nthcdr_nil] THEN NO_TAC) THEN
	ONCE_REWRITE_TAC [nthcdr_def] THEN 
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

(*****************************************************************************)
(* Check to ensure our definitions are the same as ACL2s:                    *)
(*                                                                           *)
(* 1) Save definitions in an ACL2 book as 'HOL_FLOOR' etc ...                *)
(* 2) Add defthms for 'equal (HOL_FLOOR i j) (FLOOR i j)'                    *)
(* 3) Certify the book                                                       *)
(*                                                                           *)
(* If any steps fail then this file won't compile                            *)
(*                                                                           *)
(*****************************************************************************)

val native_definitions = 
	[natp_def,acl2_nniq_def,acl2_floor_def,acl2_mod_def,truncate_def,acl2_rem_def,
	acl2_expt_def,acl2_ash_def,evenp_def,oddp_def,
	acl2_append_def,acl2_revappend_def,acl2_reverse_def,firstnac_def,acl2_take_def,
	nthcdr_def,acl2_butlast_def,nth_def,acl2_subseq_def,acl2_last_def,strip_cars_def,
	strip_cdrs_def,pairlist_def,acl2_max_def,acl2_min_def,acl2_abs_def,signum_def,
	acl2_strcat_def];



val comment  = "; This book is automatically generated by translateTheory\n" ^
               "; and contains a HOL version of a native ACL2 function which must\n" ^ 
               "; be proven equivalent before use.";

val preamble = "(in-package \"ACL2\")\n";

val def_comment = "; Definition from 'translateTheory'\n";
val thm_comment = "; Theorem proving equivalence\n";

(* Output the definition, but rename it to HOL-function *)
fun make_test_defun tm = 
let	val (function,terms) = (strip_comb o lhs) tm
in
	case (string_to_mlsym (fst (dest_const function)))
	of mlsym(pkg,fname) => 
		mk_mldefun(
			mksym pkg ("HOL-" ^ fname),
			map term_to_mlsexp terms,
			term_to_mlsexp (rhs tm))
	|  _ => raise (mk_HOL_ERR "translateTheory" "make_test_defun" "string_to_mlsym didn't return an mlsym!\n")
end;

(* Create theorems of the form: (defthm (equal (HOL-f ...) (f ...))) *)
fun make_test_defthm tm = 
let	val (function,terms) = (strip_comb o lhs) tm
in
	case (string_to_mlsym (fst (dest_const function)))
	of mlsym(pkg,fname) => 
		mk_mldefthm(
			mksym "ACL2" ("eq_"^fname),
			mk_mlsexp_list [
				term_to_mlsexp ``equal``,
				mk_mlsexp_list (mksym "ACL2" ("HOL-" ^ fname):: 
						((map term_to_mlsexp o snd o strip_comb o lhs) tm)),
				term_to_mlsexp (lhs tm)])
	|  _ => raise (mk_HOL_ERR "translateTheory" "make_equal_thm" "string_to_mlsym didn't return an mlsym!\n")
end;

val thms = map (concl o SPEC_ALL) native_definitions			

fun write_native_definition tm =
let	val outs = TextIO.openOut (acl2_test_file ^ ".lisp")
	fun pprint s = TextIO.output(outs,s);
in
	(
	TextIO.output(outs,comment)               ; TextIO.output(outs,"\n\n")            ; 
	TextIO.output(outs,preamble)              ; TextIO.output(outs,"\n\n")            ; 
	TextIO.output(outs,def_comment)           ; TextIO.output(outs,"\n")              ; 
	print_mlsexp pprint (make_test_defun tm)  ; TextIO.output(outs,"\n\n")            ;
	TextIO.output(outs,thm_comment)           ; TextIO.output(outs,"\n")              ;
	print_mlsexp pprint (make_test_defthm tm) ; TextIO.closeOut outs)
end;

fun check_substring (s1:char list) s2 = 
let	val occs = Array.tabulate (Char.maxOrd,fn x => (length s1));
	val _ = Array.modifyi (fn (a,n) => n - (length s1)) (occs,0,NONE);
	val s1' = rev s1
	fun match [] _ = NONE
          | match ((c1,c2)::cs) npos = 
		if (c1 = c2) 	then match cs (npos - 1)
				else SOME (npos,c2)
	fun check s3 = 
		case (match (combine(s1',(rev (List.take(s3,length s1))))) (length s1 - 1))
		of NONE => true
		|  SOME (npos,npos_char) => check (List.drop(s3,Int.max (length s1 - npos,Array.sub(occs,ord npos_char))))
				handle e => false
in
	check s2
end;
	
(* Runs the theorem test *)
fun check_theorem thm =
let	val _ = print "..."
	val _ = print_term ((repeat rator o lhs o concl o SPEC_ALL) thm)
	val _ = print "."
	val _ = (write_native_definition o concl o SPEC_ALL) thm
	val _ = print "."
	fun check_file s = check_substring (explode ("Finished compiling " ^ acl2_test_file)) (explode s)
	fun output s = 
	let 	val outs = TextIO.openOut (acl2_test_file ^ ".log") 
	in	(TextIO.output(outs,s) ; TextIO.closeOut outs)
	end;
in
	case (Mosml.run acl2_executable []
			("(certify-book \"" ^ acl2_test_file ^ "\")\n" ^ 
			"(good-bye)\n:q\n(good-bye)\n"))
	of (Mosml.Success s) => (output s ; if check_file s then (print ".passed!\n") else 
				Raise (mk_HOL_ERR "translateTheory" "run_theorem_test" (".Failed: \n\n" ^ s)))
        |  (Mosml.Failure s) => Raise (mk_HOL_ERR "translateTheory" "run_theorem_test" (".Failed: \n\n" ^ s))
end;

val _ = (print "Checking definitions:\n" ; app check_theorem native_definitions);

(* Export necessary theorems *)

val MK_THMS = LIST_CONJ o (map GEN_ALL);


val NAT_THMS = save_thm("NAT_THMS",
	MK_THMS [	NAT_OF_SEXP_TO_NAT,NAT_EQUAL_0,NAT_EQUAL,NAT_0_LT,NAT_LT,NAT_LE,NAT_GE,NAT_GT,NAT_ASL,
			NAT_ADD,NAT_SUC_PRE,NAT_PRE,NAT_SUC,NAT_MULT,NAT_SUB,NAT_EXP,NAT_DIV,NAT_MOD,
			NAT_EVEN,NAT_ODD,NAT_MAX,NAT_MIN]);

val INT_THMS = save_thm("INT_THMS",
	MK_THMS [	INT_OF_SEXP_TO_INT,INT_EQUAL,INT_LT,INT_LE,INT_GE,INT_GT,INT_ASL,
			INT_ADD,INT_MULT,INT_UNARY_MINUS,INT_SUB,INT_EXP,INT_DIV,INT_MOD,INT_MAX,INT_MIN,
			INT_ABS,INT_REM,INT_QUOT,INT_SGN]);

val RAT_THMS = save_thm("RAT_THMS",
	MK_THMS [	RAT_OF_SEXP_TO_RAT,RAT_EQUAL,RAT_LT,RAT_LE,RAT_GE,RAT_GT,
			RAT_ADD,RAT_MULT,RAT_UNARY_MINUS,RAT_DIV,RAT_SUB]);

val COM_THMS = save_thm("COM_THMS",
	MK_THMS [	NUM_OF_SEXP_TO_COM,COM_EQUAL,COM_LT,COM_LE,COM_GE,COM_GT,
			COM_ADD,COM_MULT,COM_UNARY_MINUS,COM_DIV,COM_SUB]);

val BOOL_THMS = save_thm("BOOL_THMS",
	MK_THMS [	BOOL_OF_SEXP_TO_BOOL,BOOL_AND,BOOL_OR,BOOL_IMPLIES,BOOL_NOT,BOOL_EQ,BOOL_T,BOOL_F]);

val LIST_THMS = save_thm("LIST_THMS",
	MK_THMS [	LIST_OF_SEXP_TO_LIST,LIST_CONS,LIST_NIL,LIST_HD,LIST_TL,LIST_APPEND,
			LIST_LENGTH,LIST_REVERSE,LIST_FIRSTN,LIST_BUTFIRSTN,LIST_LASTN,LIST_BUTLASTN,
			LIST_EL,LIST_SEG,LIST_LAST,LIST_UNZIP,LIST_ZIP,LIST_REV,LIST_LEN,LIST_FRONT]);

val PAIR_THMS = save_thm("PAIR_THMS",
	MK_THMS [	PAIR_OF_SEXP_TO_PAIR,PAIR_COMMA,PAIR_FST,PAIR_SND]);

val STRING_THMS = save_thm("STRING_THMS",
	MK_THMS [	STRING_EXPLODE,STRING_IMPLODE,STRING_LENGTH,STRING_STRCAT,STRING_PREFIX]);


val JUDGEMENT_THMS = save_thm("JUDGEMENT_THMS",
	MK_THMS [	CONJUNCT1 ANDL_JUDGEMENT,CONJUNCT2 ANDL_JUDGEMENT,
			NATP_NAT,INTEGERP_INT,RATIONALP_RAT,ACL2_NUMBERP_NUM,BOOLEANP_BOOL,PAIRP_PAIR,
			NATP_ADD,NATP_PRE,NATP_SUB,NATP_NFIX,NATP_MULT,NATP_DIV,NATP_EXP,NATP_MOD,
			BOOLEANP_IMPLIES,BOOLEANP_ANDL,BOOLEANP_ANDL_NULL,
			BOOLEANP_EQUAL,BOOLEANP_LESS,BOOLEANP_NOT,BOOLEANP_CONSP,BOOLEANP_IF,
			INTEGERP_ADD,INTEGERP_MULT,INTEGERP_DIV,INTEGERP_UNARY_MINUS,INTEGERP_MOD,
			RATIONALP_ADD,RATIONALP_MULT,RATIONALP_RECIPROCAL,RATIONALP_UNARY_MINUS,
			ACL2_NUMBERP_ADD,ACL2_NUMBERP_MULT,ACL2_NUMBERP_RECIPROCAL,ACL2_NUMBERP_UNARY_MINUS,
			PAIR_JUDGEMENT,CONJUNCT1 LIST_JUDGEMENT,LISTP_TAIL,LISTP_CONS_HT,LISTP_CONS,
			INTEGERP_QUOT,INTEGERP_REM,INTEGERP_ABS,INTEGERP_SGN,INTEGERP_MAX,INTEGERP_MIN,
			BOOLEANP_EVEN,BOOLEANP_ODD,
			NATP_MAX,NATP_MIN,NATP_LEN,NATP_ASH,INTEGERP_ASH,
			LISTP_APPEND,LISTP_REVAPPEND,LISTP_REVERSE,LISTP_TAKE,LISTP_NTH,LISTP_NTHCDR,
			LISTP_BUTLAST,LISTP_LAST,LISTP_SUBSEQ,LISTP_STRIP_CARS,LISTP_STRIP_CDRS,LISTP_PAIRLIST,
			LISTP_EXPLODE,STRINGP_IMPLODE,NATP_LENGTH,STRINGP_STRCAT]);

val _ = export_theory();
