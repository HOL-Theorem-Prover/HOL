
(* FILE		: dff.ml						*)
(* DESCRIPTION   : Proof that a unit delay is implemented by a simple 	*)
(*		  model of the D-type.  Temporal abstraction.		*)
(*		 							*)
(* READS FILES	: tempabs.th						*)
(* WRITES FILES  : dff.th						*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 87.04.16						*)
(*                                                                      *)
(* PORTED HOL98  : M. Gordon                                            *)
(* DATE		: 00.10.03						*)


(*
load "bossLib";
load "hol88Lib";
load "nextTheory";
load "stableTheory";
load "tempabsTheory";
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
open tempabsTheory;


(* Open the new theory.							*)
val _ = new_theory "dff";

(* Rise s t : signal s rises ``at`` time t.				*)
val Rise =
    new_definition
     ("Rise", ``!s t.Rise s t = ~s(t) /\ s(t+1)``);

(* D-TYPE flip flop - rising-edge triggered - SIMPLE MODEL.		*)
val Dtype =
    new_definition
        ("Dtype",
         ``!ck d q.
	   Dtype(ck,d,q) = !t. q(t+1) = if Rise ck t then d(t) else q(t)``);

(* Unit delay								*)
val Del =
    new_definition
        ("Del", ``!inp out. Del(inp,out) = (!t. out(t+1) = (inp t))``);

(* Proof that there is no simple SINGLE abstraction from                *)
(* a Boolean Dtype to Del.	                                        *)
val no_simple_abs =
    prove_thm("no_simple_abs",
              ``~?p. Inf(p) /\
		    !ck (d:num->bool) q. Dtype(ck,d,q) ==> Del(d when p, q when p)``,
	      CONV_TAC NOT_EXISTS_CONV THEN
	      REWRITE_TAC [DE_MORGAN_THM,SYM(SPEC_ALL IMP_DISJ_THM),Inf] THEN
	      CONV_TAC (REDEPTH_CONV NOT_FORALL_CONV) THEN
	      REPEAT STRIP_TAC THEN
	      REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM,Dtype,Del,Rise] THEN
	      MAP_EVERY EXISTS_TAC [``\t:num.F``, ``\t:num.T``, ``\t:num.F``] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REWRITE_TAC[when,o_THM]);

val Funpow_I =
 prove_thm
  ("Funpow_I",
   ``Funpow n I x = x``,
   Induct_on `n`
    THEN RW_TAC arith_ss [Funpow_DEF,I_THM,o_THM]);

(* Put tempabs' in the correct form for application to D-type		*)
(* NOTE: Need to automate this... and the tactic below.			*)

val tempabs =
 let val spec = Q.ISPECL [`\t:num.T`,
                          `d:num->'a`,
                          `q:num->'a`,
                          `Rise ck`,
                          `(K K):bool->'a->'a->'a`, (* \(x:bool) (y:'a) (z:'a). y *)
                          `(K I):bool->'a->'a` (* \(x:bool) (y:'a). y *)] tempabs'
     val simp1 = REWRITE_RULE [K_THM,ASSUME ``Inf(Rise ck)``,Stable] spec
     val simp2 = REWRITE_RULE [Funpow_I,I_THM] simp1
     val simp3 = REWRITE_RULE [Dev,K_THM,GSYM Dtype,I_THM] simp2
 in
    DISCH_ALL simp3
 end;

(* Correctness of Dtype w.r.t. the temporal abstraction Del.		*)
val Dtype_correct =
    prove_thm("Dtype_correct"     ,
	      ``!ck.Inf(Rise ck) ==>
                   !d q. Dtype(ck,d,q) ==>
		         Del(d when (Rise ck), q when (Rise ck))``,
              PROVE_TAC[Del,tempabs]);

val _ = export_theory();
