(* FILE		: tempabs.ml						*)
(* DESCRIPTION  : Theory of temporal abstraction for signals.		*)
(*									*)
(* READS FILES	: wop.th, next.th, stable.th				*)
(* WRITES FILES : tempabs.th						*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 85.04.17						*)
(*                                                                      *)
(* PORTED HOL98  : M. Gordon                                            *)
(* DATE		 : 00.10.03						*)
(* MODIFIED      : M. Gordon                                            *)
(* DATE		 : 02.01.08						*)


(*
load "hol88Lib";
load "nextTheory";
load "stableTheory";
*)

open Globals HolKernel Parse boolLib proofManagerLib;
open Psyntax;
open bossLib;
open arithmeticTheory;
open prim_recTheory;
open combinTheory;
open hol88Lib;
open pairTheory;
open numLib;
open numTheory;
open nextTheory;
open stableTheory;

(* Create the new theory, "tempabs.th". *)
val _ = new_theory "tempabs";

val SUB_MONO_EQ =
    store_thm
    ("SUB_MONO_EQ",
     ``!n m. (SUC n) - (SUC m) = (n - m)``,
     DECIDE_TAC);

val SUB_PLUS =
   store_thm
   ("SUB_PLUS",
    ``!a b c. a - (b + c) = (a - b) - c``,
    DECIDE_TAC);

val INV_PRE_LESS =
   store_thm
   ("INV_PRE_LESS",
    ``!m n. 0 < m /\ 0 < n ==> ((PRE m < PRE n) = (m < n))``,
    DECIDE_TAC);

val INV_PRE_LESS_EQ =
   store_thm
   ("INV_PRE_LESS_EQ",
    ``!m n. 0 < m /\ 0 < n ==> ((PRE m <= PRE n) = (m <= n))``,
    DECIDE_TAC);

val SUB_LESS_EQ =
    store_thm
    ("SUB_LESS_EQ",
     ``!n m. (n - m) <= n``,
     DECIDE_TAC);

val SUB_EQ_EQ_0 =
    store_thm
    ("SUB_EQ_EQ_0",
     ``!m n. (m - n = m) = ((m = 0) \/ (n = 0))``,
     DECIDE_TAC);


(* --------------------------------------------------------------------- *)
(* Preliminary lemmas, etc.						*)
(* --------------------------------------------------------------------- *)

(* Define a little rule for deriving consequences from WOP.		*)
fun MATCH_WOP_MP th =
    let val (e,lam)  = dest_comb (concl th)
        val wop_spec = SPEC lam WOP
    in
     MP (REWRITE_RULE [BETA_CONV ``^lam ^(fst(dest_abs lam))``] wop_spec) th
    end;

(* Prove that a non-empty bounded subset of P has a greatest element.	*)
val Bounded =
    TAC_PROOF(([],``!n. (?m. P(m) /\ m < n) ==>
		       (?m. P(m) /\ m < n /\ !i. m<i /\ i<n ==> ~P(i))``),
	      REPEAT STRIP_TAC THEN
	      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
	      REWRITE_TAC [ADD_CLAUSES,num_CONV ``1``] THEN
	      SPEC_TAC (``p:num``,``p:num``) THEN
	      INDUCT_TAC THENL
	      [EXISTS_TAC ``m:num`` THEN
	       ASM_REWRITE_TAC [ADD_CLAUSES,LESS_SUC_REFL,LESS_LESS_SUC],
	       POP_ASSUM STRIP_ASSUME_TAC THEN
	       ASM_CASES_TAC ``P(SUC(m+p)):bool`` THENL
	       [EXISTS_TAC ``SUC(m+p)`` THEN
	        ASM_REWRITE_TAC[LESS_SUC_REFL,LESS_LESS_SUC,ADD_CLAUSES],
		EXISTS_TAC ``m':num`` THEN
		IMP_RES_TAC LESS_SUC THEN
		ASM_REWRITE_TAC[ADD_CLAUSES] THEN
	        CONV_TAC (DEPTH_CONV ANTE_CONJ_CONV) THEN
	        GEN_TAC THEN DISCH_TAC THEN
	        DISCH_THEN
		(STRIP_ASSUME_TAC o
		 MATCH_MP (fst(EQ_IMP_RULE (SPEC_ALL LESS_THM)))) THENL
	        [ASM_REWRITE_TAC[],RES_TAC]]]);

(* less_lemma = |- m < (SUC n) = m <= n					*)
val less_lemma =
    REWRITE_RULE [SYM(SPEC_ALL ADD1)]
    (REWRITE_RULE [ADD1,LESS_EQ_MONO_ADD_EQ]
	          (SPECL [``m:num``,``SUC n``] LESS_EQ));

(* --------------------------------------------------------------------- *)
(* DEFINITIONS								*)
(* --------------------------------------------------------------------- *)

(* Define the relation Istimeof.						*)
(* Istimeof n sig t <==> "t" is the time of the "n"th high value of "sig"*)
(*			i.e. sig is high for the nth time at time t.	*)
val Istimeof = new_recursive_definition
  {name = "Istimeof",
   def = ``(Istimeof 0 sig t = (sig t /\ !t'. t'<t ==> ~sig t')) /\
             (Istimeof (SUC n) sig t =
               ?t'.(Istimeof n sig t') /\ Next t' t sig)``,
   rec_axiom = num_Axiom}

(* Timeof n sig = the time of the nth occurence of a high value on sig.	*)
val Timeof =
    new_definition
        ("Timeof", ``!n sig. Timeof sig n = @t. Istimeof n sig t``);

(* Inf(sig) = the signal, "sig", is high infinitely often. 		*)
val Inf = new_definition("Inf", ``!sig. Inf sig = !t. ?t'. t<t' /\ sig(t')``);

(* Incr(f) = the function, ``f``, is increasing.		 	*)
val Incr = new_definition("Incr", ``!f. Incr f = !n m. n<m ==> f(n) < f(m)``);

(* Define the abstraction function, ``when``.				*)
val when =
    new_definition
    ("when",``!cntl sig. $when sig cntl= sig o (Timeof cntl)``);

val _ = set_fixity "when"  (Infixl 350);

(* --------------------------------------------------------------------- *)
(* Theorems about Inf.							*)
(* --------------------------------------------------------------------- *)

(* Prove that Inf could be alternatively defined as follows:		*)
val Inf_thm1 =
    store_thm("Inf_thm1",
	      ``!sig. Inf(sig) =
		     (?t.sig(t)) /\ (!t. sig t ==> ?t'. t < t' /\ sig t')``,
	      REWRITE_TAC [Inf] THEN GEN_TAC THEN EQ_TAC THENL
	      [REPEAT STRIP_TAC THENL
	       [POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
		EXISTS_TAC ``t':num`` THEN FIRST_ASSUM ACCEPT_TAC,
		FIRST_ASSUM MATCH_ACCEPT_TAC],
	       STRIP_TAC THEN
	       INDUCT_TAC THENL
	       [REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
		           (SPEC ``t:num`` num_CASES) THENL
	        [RES_TAC,
		 EXISTS_TAC ``SUC n`` THEN ASM_REWRITE_TAC [LESS_0]]
                 THEN PROVE_TAC[],
	        POP_ASSUM STRIP_ASSUME_TAC
                 THEN RES_TAC
                 THEN IMP_RES_TAC(DECIDE``t' < t'' ==> t'' < t''' ==> SUC t' < t'''``)
                 THEN PROVE_TAC[]]]);

(* Prove that Inf could be alternatively defined as follows:		*)
val Inf_thm2 =
    store_thm("Inf_thm2",
	      ``!sig. Inf sig = !t. ?t'. t<=t' /\ sig(t')``,
	      REWRITE_TAC [Inf,LESS_OR_EQ] THEN
	      REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
	      [POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``t:num``) THEN
	       EXISTS_TAC ``t':num`` THEN
	       ASM_REWRITE_TAC[],
	       POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``SUC t``) THENL
	       [IMP_RES_TAC SUC_LESS THEN
	        EXISTS_TAC ``t':num`` THEN ASM_REWRITE_TAC[],
	        EXISTS_TAC ``t':num`` THEN
	        ASM_REWRITE_TAC [LESS_EQ,LESS_EQ_REFL]]]);

(* Conditions for ~Inf(sig)						*)
val Not_Inf =
    store_thm("Not_Inf",
	      ``!sig. (~Inf(sig)) =
		      (!t.~sig(t)) \/ (?t. sig t /\ !t'. t < t' ==> ~sig t')``,
	      REWRITE_TAC [Inf_thm1,IMP_DISJ_THM,DE_MORGAN_THM] THEN
	      CONV_TAC
	       (REDEPTH_CONV (NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV)) THEN
	      REWRITE_TAC [DE_MORGAN_THM] THEN
	      CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
	      REWRITE_TAC [DE_MORGAN_THM]);

(* --------------------------------------------------------------------- *)
(* THEOREMS about Istimeof						*)
(* --------------------------------------------------------------------- *)

(* Proof that |- sig (t) = ?n. Istimeof n sig t.  We first prove the 	*)
(* following lemma:							*)
val n_exists_lemma =
    TAC_PROOF(([], ``!sig t t'. sig(t') /\ t'<=t ==> ?n. Istimeof n sig t'``),
	      GEN_TAC THEN
	      INDUCT_TAC THENL
	      [REWRITE_TAC [NOT_LESS_0,LESS_OR_EQ] THEN
 	       REPEAT STRIP_TAC THEN EXISTS_TAC ``0`` THEN
	       ASM_REWRITE_TAC [Istimeof,NOT_LESS_0],
	       REWRITE_TAC [LESS_THM,LESS_OR_EQ] THEN
	       REWRITE_TAC [SYM(SPEC_ALL(CONV_RULE(ONCE_DEPTH_CONV
			       (REWR_CONV DISJ_SYM)) LESS_OR_EQ))] THEN
	       REPEAT STRIP_TAC THENL
	       [RES_TAC,
	        POP_ASSUM SUBST_ALL_TAC THEN
	        ASM_CASES_TAC ``?t'.sig(t') /\ t'<(SUC t)`` THENL
	        [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [less_lemma] o
		            MATCH_MP Bounded) THEN
	         RES_TAC THEN
	         POP_ASSUM STRIP_ASSUME_TAC THEN
                 EXISTS_TAC ``SUC n'`` THEN
	         ASM_REWRITE_TAC [Istimeof,Next] THEN
	         EXISTS_TAC ``m:num`` THEN
	         ASM_REWRITE_TAC[less_lemma],
	         POP_ASSUM (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
	         EXISTS_TAC ``0`` THEN
	         ASM_REWRITE_TAC [Istimeof] THEN
	         REPEAT STRIP_TAC THEN
	         RES_TAC]]] THEN PROVE_TAC[]);

(* We now show that |- !sig t. sig t ==> (?n. Istimeof n sig t). 	*)
(* I.e., whenever sig is true at some time t, there exists an n such 	*)
(* that n is the nth time sig is true.					*)
val Istimeof_thm1 =
    save_thm("Istimeof_thm1",
	     GEN_ALL(REWRITE_RULE [LESS_EQ_REFL]
		  (SPECL [``sig:num->bool``,``t:num``,``t:num``] n_exists_lemma)));

(* We now show that if (Istimeof n sig t) holds then sig(t).		*)
val Istimeof_thm2 =
    store_thm
     ("Istimeof_thm2",
      ``!sig t. (?n. Istimeof n sig t) ==> sig t``,
      REPEAT STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      (REPEAT_TCL STRIP_THM_THEN) SUBST1_TAC (SPEC ``n:num`` num_CASES) THEN
      REWRITE_TAC [Istimeof,Next] THEN
      STRIP_TAC);

(* There is an n such that Istimeof n sig t only if sig(t).		*)
val Istimeof_thm3 =
    store_thm("Istimeof_thm3",
	      ``!sig t. sig t = ?n. Istimeof n sig t``,
              PROVE_TAC[Istimeof_thm1,Istimeof_thm2]);

(* If sig is true infinitely often, then, for any n, there always exists *)
(* a time t such that sig is true for the nth time at time t.		*)
(*									*)
(* I.e. Inf(sig) ==> !n.?t.Istimeof n sig t				*)
(* 									*)
(* This will be proven by induction on n.				*)
val Istimeof_thm4 =
    store_thm("Istimeof_thm4",
	      ``!sig. Inf(sig) ==> !n.?t.Istimeof n sig t``,
	      PURE_REWRITE_TAC [Inf] THEN
	      REPEAT (FILTER_STRIP_TAC ``n:num``) THEN
	      INDUCT_TAC THEN
	      REWRITE_TAC [Istimeof] THENL
	      [MATCH_MP_TAC WOP THEN
	       POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
	       EXISTS_TAC ``t':num`` THEN FIRST_ASSUM ACCEPT_TAC,
	       POP_ASSUM STRIP_ASSUME_TAC THEN
	       CONV_TAC SWAP_EXISTS_CONV THEN
	       EXISTS_TAC ``t:num`` THEN
	       POP_ASSUM (fn th => REWRITE_TAC [th,Next]) THEN
	       POP_ASSUM (STRIP_ASSUME_TAC o MATCH_WOP_MP o SPEC_ALL) THEN
	       EXISTS_TAC ``n:num`` THEN
	       ASM_REWRITE_TAC[] THEN
	       REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC]);

(* Istimeof defines a Unique time:					*)
(* Istimeof n sig t /\ Istimeof n sig t' ==> (t=t')			*)
val Istimeof_thm5 =
    store_thm("Istimeof_thm5",
	      ``!n sig t t'.Istimeof n sig t /\ Istimeof n sig t' ==> (t=t')``,
	      INDUCT_TAC THEN
	      REWRITE_TAC [Istimeof] THENL
	      [CONV_TAC (ONCE_DEPTH_CONV (CONTRAPOS_CONV)) THEN
	       REPEAT STRIP_TAC THEN
	       ASM_CASES_TAC ``t < t'`` THENL
	       [RES_TAC,IMP_RES_TAC LESS_CASES_IMP THEN RES_TAC],
	       REPEAT STRIP_TAC THEN
	       RES_TAC THEN REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
	       IMP_RES_TAC Next_Unique]);

(* If there is always a time when sig is true for the nth time, then sig	*)
(* is true infinitely often.						*)
val Istimeof_thm6 =
    store_thm
     ("Istimeof_thm6",
      ``!sig. (!n.?t.Istimeof n sig t) ==> Inf sig``,
      CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
      CONV_TAC (REDEPTH_CONV (NOT_FORALL_CONV ORELSEC NOT_EXISTS_CONV)) THEN
      REWRITE_TAC [Not_Inf] THEN
      REPEAT STRIP_TAC THENL
      [EXISTS_TAC ``0`` THEN ASM_REWRITE_TAC [Istimeof],
       IMP_RES_THEN STRIP_ASSUME_TAC Istimeof_thm1 THEN
       EXISTS_TAC ``SUC n`` THEN REWRITE_TAC [Istimeof,Next] THEN
       CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
       REWRITE_TAC [DE_MORGAN_THM,SYM(SPEC_ALL IMP_DISJ_THM)] THEN
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC Istimeof_thm5 THEN
       REPEAT (POP_ASSUM SUBST_ALL_TAC) THEN
       RES_TAC]);

(* Inf sig iff there is always an nth time sig is true.			*)
val Istimeof_thm7 =
    store_thm("Istimeof_thm7",
	      ``!sig. Inf(sig) = !n. ?t. Istimeof n sig t``,
	      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
	      [IMP_RES_TAC Istimeof_thm4, IMP_RES_TAC Istimeof_thm6]);

(* --------------------------------------------------------------------- *)
(* THEOREMS about Timeof							*)
(* --------------------------------------------------------------------- *)

(* We prove the theorem relating Timeof and Next:			*)
(* ``!sig. Inf(sig) ==> !n. Next (Timeof n sig) (Timeof (n+1) sig) sig``	*)
val Timeof_thm1 =
    store_thm
    ("Timeof_thm1",
     ``!sig. Inf(sig) ==> !n. Next (Timeof sig n) (Timeof sig (SUC n)) sig``,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [Timeof,Istimeof] THEN
     IMP_RES_THEN
       (ASSUME_TAC o SELECT_RULE o (SPEC ``SUC n``)) Istimeof_thm4 THEN
     POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[Istimeof]) THEN
     FIRST_ASSUM
      (fn th => ASSUME_TAC
      (EXISTS (``?t'.Istimeof n sig t'``,``t':num``) th) ORELSE NO_TAC) THEN
     POP_ASSUM (ASSUME_TAC o SELECT_RULE) THEN
     POP_ASSUM
        (ASSUME_TAC o GEN_ALL o (MATCH_MP (hd(RES_CANON Istimeof_thm5)))) THEN
     RES_THEN SUBST1_TAC THEN
     FIRST_ASSUM ACCEPT_TAC);

val Timeof_thm2 =
    store_thm
    ("Timeof_thm2",
     ``!sig. Inf(sig) ==> !n. (Timeof sig n) < (Timeof sig (SUC n))``,
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN MP_TAC Timeof_thm1 THEN
     REWRITE_TAC [Next] THEN
     DISCH_THEN (STRIP_ASSUME_TAC o SPEC ``n:num``) THEN
     FIRST_ASSUM ACCEPT_TAC);

val Timeof_thm3 =
    store_thm
    ("Timeof_thm3",
     ``!sig. Inf(sig) ==>
      !n t. ((Timeof sig n) < t /\ t < (Timeof sig (SUC n))) ==> ~sig t``,
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN MP_TAC Timeof_thm1 THEN
     REWRITE_TAC [Next] THEN
     DISCH_THEN (STRIP_ASSUME_TAC o SPEC ``n:num``) THEN
     RES_TAC);

(* Also prove that:  Inf(sig) ==> sig(Timeof n sig)			*)
val Timeof_thm4 =
    store_thm
    ("Timeof_thm4",
     ``!sig. Inf(sig) ==> !n. sig(Timeof sig n)``,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [Timeof] THEN
     IMP_RES_THEN (MP_TAC o SELECT_RULE o SPEC_ALL) Istimeof_thm4 THEN
     STRIP_ASSUME_TAC (SPEC ``n:num`` num_CASES) THEN
     ASM_REWRITE_TAC [Istimeof,Next] THEN
     REPEAT STRIP_TAC);

val Timeof_thm5 =
    store_thm
      ("Timeof_thm5",
       ``!sig t. sig(t) ==> ?n. t = Timeof sig n``,
       REPEAT STRIP_TAC THEN
       IMP_RES_THEN STRIP_ASSUME_TAC Istimeof_thm1 THEN
       EXISTS_TAC ``n:num`` THEN
       ASSUME_TAC (SELECT_RULE (EXISTS (``?t.Istimeof n sig t``,``t:num``)
				       (ASSUME ``Istimeof n sig t``))) THEN
       REWRITE_TAC [Timeof] THEN
       IMP_RES_TAC Istimeof_thm5);


val Timeof_thm6 =
    store_thm
      ("Timeof_thm6",
       ``!sig. Inf sig ==> !t. 0 < (Timeof sig (SUC t) - Timeof sig t)``,
       REPEAT STRIP_TAC THEN
       IMP_RES_THEN
	(STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1 o SPEC ``t:num``)
	Timeof_thm2 THEN
       REWRITE_TAC [ADD_ASSOC,num_CONV ``1``,ADD_CLAUSES,SUB] THEN
       REWRITE_TAC [REWRITE_RULE[SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD] THEN
       REWRITE_TAC [LESS_0]);

val Timeof_thm7 =
    store_thm
    ("Timeof_thm7",
     ``!c. Inf c ==> !t. (Timeof c (SUC t) - 1) < Timeof c (SUC t)``,
     REPEAT STRIP_TAC THEN
     STRIP_ASSUME_TAC (SPECL [``Timeof c (SUC t)``,``1``] SUB_LESS_EQ) THEN
     POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LESS_OR_EQ]) THEN
     POP_ASSUM
	 (ASSUME_TAC o REWRITE_RULE [SUB_EQ_EQ_0,num_CONV ``1``,NOT_SUC]) THEN
     IMP_RES_THEN (MP_TAC o SPEC ``t:num``) Timeof_thm2 THEN
     ASM_REWRITE_TAC [NOT_LESS_0]);


(* --------------------------------------------------------------------- *)
(* THEOREMS about Incr							*)
(* --------------------------------------------------------------------- *)

(* A little lemma about Incr.						*)
val Incr_lemma1 =
    TAC_PROOF(([], ``!f. Incr(f) ==> !n. n <= f(n)``),
	      PURE_REWRITE_TAC [Incr] THEN
	      GEN_TAC THEN
	      CONV_TAC CONTRAPOS_CONV THEN
	      DISCH_THEN (ASSUME_TAC o (CONV_RULE NOT_FORALL_CONV)) THEN
	      POP_ASSUM
	       (STRIP_ASSUME_TAC o
	        REWRITE_RULE [SYM(SPEC_ALL NOT_LESS)] o MATCH_WOP_MP) THEN
	      STRIP_TAC THEN RES_TAC);

(* Another lemma about Incr.						*)
val Incr_lemma2 =
    TAC_PROOF(([], ``!f. Incr(f) ==> !n. n < f(SUC n)``),
	      REPEAT STRIP_TAC THEN
	      IMP_RES_TAC Incr_lemma1 THEN
 	      POP_ASSUM (STRIP_ASSUME_TAC o
			 REWRITE_RULE [LESS_OR_EQ] o SPEC ``SUC n``) THENL
	      [ASSUME_TAC (SPEC ``n:num`` LESS_SUC_REFL) THEN
	       IMP_RES_TAC LESS_TRANS,
	       POP_ASSUM (SUBST1_TAC o SYM) THEN
	       MATCH_ACCEPT_TAC LESS_SUC_REFL]);

(* A lemma relating Incr and Inf.					*)
val Incr_lemma3 =
    TAC_PROOF(([], ``!f. Incr(f) ==> Inf(\n.?m. n = f m)``),
	      PURE_REWRITE_TAC [Inf] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT STRIP_TAC THEN
      IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC ``t:num``) Incr_lemma2 THEN
	      EXISTS_TAC ``f (SUC t):num`` THEN
	      ASM_REWRITE_TAC [] THEN
	      EXISTS_TAC ``SUC t`` THEN REFL_TAC);;

val LESS_SUC_EQ = DECIDE ``m < n ==> SUC m < n \/ (SUC m = n)``;

(* A lemma concerning Incr and Istimeof.					*)
val Istimeof_lemma =
    TAC_PROOF(([], ``Incr(f) ==> !n. Istimeof n (\n.?m. n = f m) (f n)``),
	      REWRITE_TAC [Incr] THEN
	      DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [Istimeof] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THENL
	      [CONJ_TAC THENL
	       [EXISTS_TAC ``0`` THEN REFL_TAC,
	        REPEAT STRIP_TAC THEN
	        POP_ASSUM SUBST_ALL_TAC THEN
	        STRIP_ASSUME_TAC (SPEC ``m:num`` LESS_0_CASES) THENL
	        [POP_ASSUM (SUBST_ALL_TAC o SYM) THEN IMP_RES_TAC LESS_REFL,
	         RES_TAC THEN IMP_RES_TAC LESS_ANTISYM]],
               EXISTS_TAC ``(f:num->num) n`` THEN
	       ASM_REWRITE_TAC[Next] THEN
	       CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	       REPEAT STRIP_TAC THENL
	       [ANTE_RES_THEN ACCEPT_TAC (SPEC ``n:num`` LESS_SUC_REFL),
	        EXISTS_TAC ``SUC n`` THEN REFL_TAC,
	        POP_ASSUM SUBST_ALL_TAC THEN
	        STRIP_ASSUME_TAC
	          (SPEC_ALL (REWRITE_RULE [LESS_OR_EQ] LESS_CASES)) THENL
	        [RES_TAC THEN IMP_RES_TAC LESS_ANTISYM,
	         POP_ASSUM (STRIP_ASSUME_TAC o
	            (MATCH_MP (REWRITE_RULE [LESS_OR_EQ] LESS_SUC_EQ))) THENL
	         [RES_TAC THEN IMP_RES_TAC LESS_ANTISYM,
	          POP_ASSUM SUBST_ALL_TAC THEN IMP_RES_TAC LESS_REFL],
	         POP_ASSUM SUBST_ALL_TAC THEN IMP_RES_TAC LESS_REFL]]]);

(* ---------------------------------------------------------------------	*)
(* A theorem relating Incr, Inf and Timeof.				*)
(* ---------------------------------------------------------------------	*)

val Incr_Inf_thm =
    store_thm("Incr_Inf_thm",
	      ``!f.Incr f = ?g. Inf(g) /\ (f = Timeof g)``,
	      REPEAT (FIRST [STRIP_TAC, EQ_TAC]) THENL
	      [EXISTS_TAC ``\n:num.?m:num. n = f m`` THEN
	       CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
	       IMP_RES_TAC Incr_lemma3 THEN
	       ASM_REWRITE_TAC[Timeof] THEN
	       GEN_TAC THEN
	       IMP_RES_THEN
	         (ASSUME_TAC o SELECT_RULE o SPEC ``n:num``) Istimeof_thm4 THEN
	       IMP_RES_THEN
	         (ASSUME_TAC o SPEC ``n:num``) Istimeof_lemma THEN
	       IMP_RES_TAC Istimeof_thm5,
	       POP_ASSUM SUBST1_TAC THEN
	       PURE_REWRITE_TAC [Incr] THEN
	       REPEAT GEN_TAC THEN
	       DISCH_THEN
	         (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
	       PURE_REWRITE_TAC [num_CONV ``1``,ADD_CLAUSES] THEN
	       SPEC_TAC (``p:num``,``p:num``) THEN
	       INDUCT_TAC THENL
	       [REWRITE_TAC [ADD_CLAUSES] THEN
	        IMP_RES_THEN
	          (STRIP_ASSUME_TAC o SPEC ``n:num`` o REWRITE_RULE [Next])
	          Timeof_thm1,
	        REWRITE_TAC [ADD_CLAUSES] THEN
	        POP_ASSUM (MATCH_MP_TAC o
	                   MATCH_MP (CONV_RULE ANTE_CONJ_CONV
				               (SPEC_ALL LESS_TRANS))) THEN
	        IMP_RES_THEN
	          (STRIP_ASSUME_TAC o
		    SPEC ``SUC(n+p)`` o REWRITE_RULE [Next]) Timeof_thm1]]);

(* --------------------------------------------------------------------- *)
(* Theorems about when.							*)
(* --------------------------------------------------------------------- *)

val when_thm1 =
    store_thm
     ("when_thm1",
      ``!f g c. (((\t.(f t,g t))when c)t) = (((f when c) t),((g when c) t))``,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [when,o_THM] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN REFL_TAC);

val when_thm2 =
    store_thm
     ("when_thm2",
      ``!c. Inf(c) ==> !t. (c when c) t``,
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC Timeof_thm4 THEN
      ASM_REWRITE_TAC [when,o_THM]);

(* --------------------------------------------------------------------- *)
(* Iteration theorems.							 *)
(* --------------------------------------------------------------------- *)

val Funpow_DEF = new_recursive_definition
  {name = "Funpow_DEF",
   def = ``(Funpow 0 f = I) /\ (Funpow (SUC n) f = (f o (Funpow n f)))``,
   rec_axiom = num_Axiom}

val Funpow1 =
    store_thm("Funpow1",
     	     ``!f. (Funpow 0 f x = x) /\
      	          (!n. Funpow (SUC n) f x = f((Funpow n f)x))``,
	     REWRITE_TAC [Funpow_DEF,I_THM,o_THM]);

val Dev =
    new_definition
    ("Dev",
     ``Dev f g (c,a,b,s) =
       !t:num. s(t+1) = if c t then f (a t) (b t) (s t) else g (a t) (s t)``);

val tempabs =
    store_thm
   ("tempabs",
    ``!a b s c f g.
     Dev f g (c,a,b,s) ==>
     (!t. Stable (Timeof c t) (Timeof c (t+1)) a) ==>
     Inf(c) ==>
     !n t.((Timeof c n < t) /\ (t <= Timeof c (n+1))) ==>
           (s t =
	    Funpow (t - ((Timeof c n)+1)) (g ((a when c) n))
	           (f((a when c) n) ((b when c) n) ((s when c) n)))``,
    PURE_ONCE_REWRITE_TAC [Dev] THEN
    CONV_TAC (DEPTH_CONV num_CONV) THEN
    REWRITE_TAC [ADD_CLAUSES,when,o_THM,Stable] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN GEN_TAC THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [NOT_LESS_0],
     REWRITE_TAC [LESS_THM] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_THEN (ASSUME_TAC o SPEC ``n:num``) Timeof_thm4 THEN
      EVERY_ASSUM (fn th => SUBST1_TAC(SYM th) handle _ => ALL_TAC) THEN
      ASM_REWRITE_TAC [SUB,LESS_SUC_REFL,Funpow1,I_THM],
      IMP_RES_THEN (ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ)
                       OR_LESS THEN
      IMP_RES_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [Next] o SPEC ``n:num``)
	               Timeof_thm1 THEN
      IMP_RES_TAC OR_LESS THEN
      RES_TAC THEN
      IMP_RES_TAC LESS_LESS_SUC THEN
      POP_ASSUM (ASSUME_TAC o NOT_INTRO) THEN
      ASM_REWRITE_TAC[SUB,Funpow1,o_THM] THEN
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [NOT_LESS])) THEN
      POP_ASSUM (ASSUME_TAC o (MATCH_MP OR_LESS)) THEN
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
      RES_TAC THEN ASM_REWRITE_TAC[]]]);

val tempabs' =
    store_thm
   ("tempabs'",
    ``!a b s c f g.
     Dev f g (c,a,b,s) ==>
     (!t. Stable (Timeof c t) (Timeof c (t+1)) a) ==>
     Inf(c) ==>
     !n.(s when c) (n+1) =
	    Funpow ((Timeof c (n+1)) - ((Timeof c n)+1)) (g ((a when c) n))
	           (f((a when c) n) ((b when c) n) ((s when c) n))``,
    REPEAT (DISCH_TAC ORELSE GEN_TAC) THEN
    REWRITE_TAC [when,o_THM] THEN
    MATCH_MP_TAC (REWRITE_RULE [when,o_THM]
			       (UNDISCH_ALL (SPEC_ALL tempabs))) THEN
    IMP_RES_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [Next] o SPEC ``n:num``)
	               Timeof_thm1 THEN
    ASM_REWRITE_TAC [LESS_OR_EQ,num_CONV ``1``,ADD_CLAUSES]);


val _ = export_theory();
