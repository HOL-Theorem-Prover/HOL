
(* FILE		: next.ml						*)
(* DESCRIPTION   : Creates the theory "next" containing the definition 	*)
(*		  of the predicate, Next, and associated theorems. 	*)
(*									*)
(* READS FILES	: <none>						*)
(* WRITES FILES	: next.th						*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 84.12.05						*)
(* REVISED	: 86.05.11						*)
(*                                                                      *)
(* PORTED HOL98  : M. Gordon                                            *)
(* DATE		: 00.10.03						*)

(*
load "bossLib";
*)

open Globals HolKernel Parse boolLib proofManagerLib;
infixr 3 -->;
infix 8 by;
infix &&;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;


open bossLib;
open arithmeticTheory;
open prim_recTheory;
open hol88Lib;


(* Create the new theory "next.th"					*)
val _ = new_theory "next";;

(* Definition of Next.  Time t2 is the first (i.e. next) time after t1  *)
(* when the signal sig is true.						*)
val Next =
    new_definition
    ("Next",
     ``!sig t1 t2.
      Next t1 t2 sig = (t1<t2)/\(sig t2)/\(!t. (t1<t)/\(t<t2) ==> ~sig t)``);

(* The following lemma will be needed in the proofs below:		*)
val cases = DECIDE ``!m n. m < n ==> (SUC m) < n \/ (SUC m = n)``;


(* Theorem for Increasing the size of the interval covered by the 	*)
(* predicate Next.							*)
val Next_Increase =
    store_thm
     ("Next_Increase",
      ``!sig t1 t2. ~sig(SUC(t1)) /\ Next (SUC t1) t2 sig ==> Next t1 t2 sig``,
      PURE_REWRITE_TAC [Next] THEN
      REPEAT (FILTER_STRIP_TAC ``t:num``) THENL
      [IMP_RES_TAC SUC_LESS,
       FIRST_ASSUM ACCEPT_TAC,
       CONV_TAC (DEPTH_CONV ANTE_CONJ_CONV) THEN
       GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP cases) THENL
       [RES_TAC, POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]]);

(* Lemma for decreasing the size of the interval covered by Next.	*)
val Next_Decrease =
    store_thm
     ("Next_Decrease",
      ``!sig t1 t2. Next t1 t2 sig /\ ~sig(SUC t1) ==> Next (SUC t1) t2 sig``,
      PURE_REWRITE_TAC [Next] THEN
      REPEAT STRIP_TAC THENL
      [IMP_RES_THEN
        (DISJ_CASES_THEN2 ACCEPT_TAC
		(MP_TAC o (AP_TERM ``sig:num->bool``))) cases THEN
       ASM_REWRITE_TAC[],
       FIRST_ASSUM ACCEPT_TAC,
       IMP_RES_TAC SUC_LESS THEN RES_TAC]);

(* Uniqueness lemma for Next.						*)
val Next_Unique =
    store_thm
     ("Next_Unique",
      ``!sig t t1 t2. Next t t1 sig /\ Next t t2 sig ==> (t1 = t2)``,
      PURE_REWRITE_TAC [Next] THEN
      CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC ``t1 < t2`` THENL
      [RES_TAC, IMP_RES_TAC LESS_CASES_IMP THEN RES_TAC]);

(* Close the theory ``next.th``.					*)
val _ = export_theory();
