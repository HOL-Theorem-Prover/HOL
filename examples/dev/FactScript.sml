
(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial            *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
map load  ["compile"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory
     composeTheory compileTheory compile;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory compile;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "Fact"                                                   *)
(*****************************************************************************)
val _ = new_theory "Fact";

(*****************************************************************************)
(* First build a naive iterative multiplier function (repeated addition)     *)
(*****************************************************************************)
val (MultIter,MultIter_ind,MultIter_dev) =
 xRecDev_defn
  []
  "MultIter"
  `MultIter (m,n,acc) =
    if m = 0 then (0,n,acc) else MultIter(m-1,n,n + acc)`
  `\(m:num,n:num,acc:num). m`;

(*****************************************************************************)
(* Verify that MultIter does compute multiplication                          *)
(*****************************************************************************)
val MultIterRecThm =  (* proof adapted from similar one from KXS *)
 save_thm
  ("MultIterRecThm",
   Q.prove
    (`!m n acc. SND(SND(MultIter (m,n,acc))) = (m * n) + acc`,
     recInduct MultIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once MultIter,MULT,RIGHT_SUB_DISTRIB]
      THEN Cases_on `m` THEN FULL_SIMP_TAC arith_ss [MULT]));

(*****************************************************************************)
(* Create an implementation of a multiplier from MultIter                    *)
(*****************************************************************************)
val (Mult,Mult_dev) =
 xDev_defn
  [MultIter_dev]
  "Mult"
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)
val MultThm =
 store_thm
  ("MultThm",
   ``Mult = UNCURRY $*``,
   CONV_TAC FUN_EQ_CONV
    THEN Cases_on `p`
    THEN RW_TAC arith_ss [UNCURRY,Mult,MultIterRecThm]);

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(* (use Mult to implement multiplication)                                    *)
(*****************************************************************************)
val (FactIter,FactIter_ind,FactIter_dev) =
 xRecDev_defn
  [SUBS [MultThm] Mult_dev]
  "FactIter"
  `FactIter (n,acc) =
     (if n = 0 then (n,acc) else FactIter (n - 1,n * acc))`
  `\(n:num,acc:num). n`;

(*****************************************************************************)
(* Alternative implementation with multiplication as atomic                  *)
(*****************************************************************************)
val (AltFactIter,AltFactIter_ind,AltFactIter_dev) =
 xRecDev_defn
  []
  "AltFactIter"
  `AltFactIter (n,acc) =
     (if n = 0 then (n,acc) else AltFactIter (n - 1,n * acc))`
  `\(n:num,acc:num). n`;

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)
val FactIterRecThm =  (* proof from KXS *)
 save_thm
  ("FactIterRecThm",
   Q.prove
    (`!n acc. SND(FactIter (n,acc)) = acc * FACT n`,
     recInduct FactIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once FactIter,FACT]
      THEN Cases_on `n` THEN FULL_SIMP_TAC arith_ss [FACT]
      THEN PROVE_TAC [MULT_ASSOC,MULT_SYM]));

(*****************************************************************************)
(* Implement a function Fact to compute SND(FactIter (n,1))                  *)
(*****************************************************************************)
val (Fact,Fact_dev) =
 xDev_defn
  [FactIter_dev]
  "Fact"
  `Fact n = SND(FactIter (n,1))`;

(*****************************************************************************)
(* Verify Fact is indeed the factorial function                              *)
(*****************************************************************************)
val FactThm =
 store_thm
  ("FactThm",
   ``Fact = FACT``,
   CONV_TAC FUN_EQ_CONV
    THEN RW_TAC arith_ss [Fact,FactIterRecThm]);

(*****************************************************************************)
(* Create implementation of factorial (HOL's built-in FACT)                  *)
(*****************************************************************************)
val FACT_def =
 save_thm
  ("FACT_dev",
   REWRITE_RULE [FactThm] Fact_dev);

(*****************************************************************************)
(* Temporary hack to work around a system prettyprinter bug                  *)
(*****************************************************************************)
val _ = overload_on(" * ", numSyntax.mult_tm);

val _ = export_theory();
