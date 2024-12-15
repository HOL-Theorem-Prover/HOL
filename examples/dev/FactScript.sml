(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial            *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
 * Boilerplate needed for compilation. Batch mode.
 ******************************************************************************)

open HolKernel Parse boolLib bossLib;

(******************************************************************************
 * Open theories. Batch mode.
 ******************************************************************************)
open arithmeticTheory pairLib pairTheory PairRules combinTheory
     composeTheory compile vsynth;
infixr 3 THENR;
infixr 3 ORELSER;

(******************************************************************************
 * Set default parsing to natural numbers rather than integers
 ******************************************************************************)

val _ = numLib.temp_prefer_num();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "Fact"                                                   *)
(*****************************************************************************)

val _ = new_theory "Fact";

(*****************************************************************************)
(* Define arithmetic operators used and associate them with their Verilog    *)
(* implementations.                                                          *)
(*****************************************************************************)

val _ = AddBinop ("ADD",  (``UNCURRY $+ : num#num->num``,  "+"));
val _ = AddBinop ("SUB",  (``UNCURRY $- : num#num->num``,  "-"));
val _ = AddBinop ("LESS", (``UNCURRY $< : num#num->bool``, "<"));
val _ = AddBinop ("EQ",   (``UNCURRY $= : num#num->bool``, "=="));

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)

val (FactIter,FactIter_ind,FactIter_dev) =
 hwDefine
  `FactIter (n,acc:num) =
      if n = 0 then (n,acc) else FactIter (n - 1, n * acc)`;

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)

val FactIterRecThm =  (* proof from KXS *)
 Q.store_thm
  ("FactIterRecThm",
   `!n acc. SND(FactIter (n,acc)) = acc * FACT n`,
    recInduct FactIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once FactIter,FACT]
      THEN Cases_on `n`
      THEN RW_TAC std_ss [FACT, AC MULT_ASSOC MULT_SYM]);

(*****************************************************************************)
(* Implement a function Fact to compute SND(FactIter (n,1))                  *)
(*****************************************************************************)

val (Fact,_,Fact_dev) = hwDefine `Fact n = SND(FactIter (n,1))`;

(*****************************************************************************)
(* Verify Fact is indeed the factorial function                              *)
(*****************************************************************************)

val FactThm =
 Q.store_thm
  ("FactThm",
   `Fact = FACT`,
   RW_TAC arith_ss [FUN_EQ_THM,Fact,FactIterRecThm]);

(*****************************************************************************)
(* To implement ``$*`` we build a naive iterative multiplier function        *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)

val (MultIter,MultIter_ind,MultIter_dev) =
 hwDefine
  `MultIter (m,n:num,acc:num) =
      if m = 0n then (0,n,acc) else MultIter(m-1,n,n + acc)`;


(*****************************************************************************)
(* Two argument multiplication, defined in terms of MultIter                 *)
(*****************************************************************************)

val (Mult,_,Mult_dev) =
 hwDefine
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Verify that MultIter does compute accumulator-style multiplication        *)
(*****************************************************************************)

val MultIterRecThm =  (* proof adapted from similar one from KXS *)
 Q.store_thm
  ("MultIterRecThm",
   `!m n acc. SND(SND(MultIter (m,n,acc))) = (m * n) + acc`,
    recInduct MultIter_ind THEN RW_TAC std_ss []
      THEN RW_TAC arith_ss [Once MultIter]
      THEN Cases_on `m`
      THEN FULL_SIMP_TAC arith_ss [MULT]);

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)

val MultThm =
 Q.store_thm
  ("MultThm",
   `Mult = UNCURRY $*`,
   RW_TAC arith_ss [FUN_EQ_THM,FORALL_PROD,Mult,MultIterRecThm]);

(*****************************************************************************)
(* Theorem used in an example in the README file                             *)
(*****************************************************************************)

val FactIter_TOTAL =
 store_thm
  ("FactIter_TOTAL",
   ``TOTAL((\(n:num,acc:num). n = 0),
           (\(n:num,acc:num). (n,acc)),
           (\(n:num,acc:num). (n - 1,n * acc)))``,
   RW_TAC list_ss [TOTAL_def]
    THEN Q.EXISTS_TAC `\(x,y).x`
    THEN GEN_BETA_TAC
    THEN DECIDE_TAC);

(*****************************************************************************)
(* Use Mult_dev to refine ``DEV (UNCURRY $* )`` in FactIter_dev              *)
(*****************************************************************************)

val FactIter1_dev =
 REFINE (DEPTHR(LIB_REFINE[SUBS [MultThm] Mult_dev])) FactIter_dev;

(*****************************************************************************)
(* Use MultIter_dev to refine ``DEV MultIter`` in FactIter1_dev              *)
(*****************************************************************************)

val FactIter2_dev =
 REFINE (DEPTHR(LIB_REFINE[MultIter_dev])) FactIter1_dev;

(*****************************************************************************)
(* Use FactIter2_dev to refine ``DEV FactIter`` in Fact_dev                  *)
(*****************************************************************************)

val Fact1_dev =
  REFINE (DEPTHR(LIB_REFINE[FactIter2_dev])) Fact_dev;

(*****************************************************************************)
(* REFINE all remaining DEVs to ATM                                          *)
(*****************************************************************************)

val Fact2_dev = REFINE (DEPTHR ATM_REFINE) Fact1_dev;

(*****************************************************************************)
(* Alternative derivation using refinement combining combinators             *)
(*****************************************************************************)

val Fact3_dev =
 REFINE
  (DEPTHR(LIB_REFINE[FactIter_dev])
    THENR DEPTHR(LIB_REFINE[SUBS [MultThm] Mult_dev])
    THENR DEPTHR(LIB_REFINE[MultIter_dev])
    THENR DEPTHR ATM_REFINE)
  Fact_dev;

(*****************************************************************************)
(* Finally, create implementation of FACT (HOL's native factorial function)  *)
(*****************************************************************************)

val FACT_dev =
 save_thm
  ("FACT_dev",
   REWRITE_RULE [FactThm] Fact3_dev);

val FACT_net =
 save_thm
  ("Fact_net",
   Count.apply MAKE_NETLIST FACT_dev);

val FACT_cir =
 save_thm
  ("Fact_cir",
   time MAKE_CIRCUIT FACT_dev);

(*****************************************************************************)
(* Print Verilog to file FACT.vl                                             *)
(*****************************************************************************)

val _ = PRINT_VERILOG FACT_cir;  (* N.B. FACT.vl overwritten by stuff below! *)

(*****************************************************************************)
(* Print Verilog + a simulation environment to FACT.vl                       *)
(* Run using: iverilog -o FACT.vvp FACT.vl; vvp FACT.vvp                     *)
(*****************************************************************************)

(*
 iverilog -o FACT.vvp FACT.vl;
 vvp FACT.vvp;
 gtkwave FACT.vcd
*)

(*****************************************************************************)
(* Temporary hack to work around a system prettyprinter bug                  *)
(*****************************************************************************)

val _ = temp_overload_on(" * ", numSyntax.mult_tm);

val _ = export_theory();
