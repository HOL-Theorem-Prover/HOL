(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial.           *)
(* Version for interactive use -- runs simulator and then waveform viewer.   *)
(*****************************************************************************)

quietdec := true;
val _ = set_trace "show_alias_printing_choices" 0;
loadPath := "dff" :: !loadPath;
app load  ["compile","vsynth","dffTheory"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory;
infixr 3 THENR;
infixr 3 ORELSER;
quietdec := false;


(*****************************************************************************)
(* Start new theory "Fact"                                                   *)
(*****************************************************************************)

val _ = new_theory "Fact";

(*****************************************************************************)
(* Define arithmetic operators used and their Verilog implementations.       *)
(*****************************************************************************)

val _ = AddBinop ("ADD",  (``UNCURRY $+ : num#num->num``,  "+"));
val _ = AddBinop ("SUB",  (``UNCURRY $- : num#num->num``,  "-"));
val _ = AddBinop ("LESS", (``UNCURRY $< : num#num->bool``, "<"));
val _ = AddBinop ("EQ",   (``UNCURRY $= : num#num->bool``, "=="));

(*****************************************************************************)
(* To implement multiplication we use a naive iterative multiplier function  *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)

val (MultIter,MultIter_ind,MultIter_dev) =
 hwDefine
  `(MultIter (m:num,n:num,acc:num) =
     if m = 0 then (0,n,acc) else MultIter(m-1,n,n + acc))
   measuring FST`;

(*****************************************************************************)
(* Create an implementation of a multiplier from MultIter                    *)
(*****************************************************************************)

val (Mult,_,Mult_dev) =
 hwDefine
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)

val (FactIter_def,FactIter_ind,FactIter_dev) =
 hwDefine
  `(FactIter (n,acc) =
      if n = 0 then (n,acc) else FactIter(n - 1, Mult(n,acc)))
   measuring FST`;

(*****************************************************************************)
(* Implement a function Fact to compute SND(FactIter (n,1))                  *)
(*****************************************************************************)

val (Fact,_,Fact_dev) =
 hwDefine
  `Fact n = SND(FactIter (n,1))`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)

val FactImp_dev = REFINE_ALL Fact_dev;

val Fact_cir =
 save_thm
  ("Fact_cir",
   time MAKE_CIRCUIT FactImp_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module FACT.                                                   *)
(*****************************************************************************)

dump_all_flag := false; 

(*****************************************************************************)
(* Change these variables to select simulator and viewer. Commenting out the *)
(* three assignments below will revert to the defaults: cver/dinotrace.      *)
(*****************************************************************************)
(*
iverilog_path      := "/usr/bin/iverilog";
verilog_simulator  := iverilog;
waveform_viewer    := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)

numWarning := false;

SIMULATE Fact_cir [("inp","4")];
*)
(*****************************************************************************)
(* Verify that MultIter does compute multiplication                          *)
(*****************************************************************************)

val MultIterThm =                 (* proof adapted from similar one from KXS *)
 save_thm
  ("MultIterThm",
   prove
    (``!m n acc. MultIter (m,n,acc) = (0, n, (m * n) + acc)``,
     recInduct MultIter_ind THEN RW_TAC std_ss []
      THEN RW_TAC arith_ss [Once MultIter]
      THEN Cases_on `m` 
      THEN FULL_SIMP_TAC arith_ss [MULT]));

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)

val MultThm =
 store_thm
  ("MultThm",
   ``Mult = UNCURRY $*``,
   RW_TAC arith_ss [FUN_EQ_THM,FORALL_PROD,Mult,MultIterThm]);

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)

val FactIterThm =                                       (* proof from KXS *)
 save_thm
  ("FactIterThm",
   prove
    (``!n acc. FactIter (n,acc) = (0, acc * FACT n)``,
     recInduct FactIter_ind THEN REPEAT STRIP_TAC
      THEN RW_TAC arith_ss [Once FactIter_def] THENL 
      [RW_TAC arith_ss [FACT],
       Cases_on `n` THENL
       [FULL_SIMP_TAC arith_ss [FACT],
        FULL_SIMP_TAC arith_ss [FACT,MultThm]]]));


(*****************************************************************************)
(* Verify Fact is indeed the factorial function                              *)
(*****************************************************************************)

val FactThm =
 store_thm
  ("FactThm",
   ``Fact = FACT``,
   RW_TAC arith_ss [FUN_EQ_THM,Fact,FactIterThm]);

val _ = export_theory();
