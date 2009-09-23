(* FILE		: stable.ml						*)
(* DESCRIPTION   : Creates the theory "stable" containing the definition*)
(*		  of the predicate, Stable, and associated theorems. 	*)
(*									*)
(* READS FILES	: <none>						*)
(* WRITES FILES	: stable.th						*)
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
open pairTheory;

(* Create the new theory "stable.th"					*)
val _ = new_theory "stable";;

(* Definition of Stable: a predicate for signals that are stable in an 	*)
(* interval.								*)
val Stable =
    new_definition
        ("Stable",
	 ``!sig t1 t2. Stable t1 t2 sig =
	    !t. ((t1 <= t) /\ (t < t2)) ==> (sig(t) = sig(t1))``);;

val Stable_pair =
    store_thm
    ("Stable_pair",
     ``!f t1 t2.
        Stable t1 t2 (\t. f t, g t) = ((Stable t1 t2 f) /\ Stable t1 t2 g)``,
     REWRITE_TAC [Stable] THEN
     REPEAT STRIP_TAC THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [PAIR_EQ] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THEN
     RES_TAC);;

val _ = export_theory();;
