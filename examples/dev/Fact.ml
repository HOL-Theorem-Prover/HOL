
(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial.           *)
(* Version for interactive use -- runs simulator and then waveform viewer.   *)
(*****************************************************************************)

quietdec := true;
val _ = set_trace "show_alias_printing_choices" 0;
loadPath :="dff" :: !loadPath;
map load  ["compile","intLib","vsynth","dffTheory"];
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory;
infixr 3 THENR;
infixr 3 ORELSER;
val _ = intLib.deprecate_int();
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
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)
val (FactIter,FactIter_ind,FactIter_dev) =
 hwDefine
  `(FactIter (n,acc) =
      if n = 0 then (n,acc) else FactIter (n - 1,n * acc))
   measuring FST`;

(*****************************************************************************)
(* To implement `$*`` we build a naive iterative multiplier function         *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)
val (MultIter,MultIter_ind,MultIter_dev) =
 hwDefine
  `(MultIter (m,n,acc) =
      if m = 0 then (0,n,acc) else MultIter(m-1,n,n + acc))
   measuring FST`;

(*****************************************************************************)
(* Verify that MultIter does compute multiplication                          *)
(*****************************************************************************)
val MultIterRecThm =              (* proof adapted from similar one from KXS *)
 save_thm
  ("MultIterRecThm",
   prove
    (``!m n acc. SND(SND(MultIter (m,n,acc))) = (m * n) + acc``,
     recInduct MultIter_ind THEN RW_TAC std_ss []
      THEN RW_TAC arith_ss [Once MultIter]
      THEN Cases_on `m` 
      THEN FULL_SIMP_TAC arith_ss [MULT]));

(*****************************************************************************)
(* Create an implementation of a multiplier from MultIter                    *)
(*****************************************************************************)
val (Mult,_,Mult_dev) =
 hwDefine
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)
val MultThm =
 store_thm
  ("MultThm",
   ``Mult = UNCURRY $*``,
   RW_TAC arith_ss [FUN_EQ_THM,FORALL_PROD,Mult,MultIterRecThm]);

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)
val FactIterRecThm =                                       (* proof from KXS *)
 save_thm
  ("FactIterRecThm",
   prove
    (``!n acc. SND(FactIter (n,acc)) = acc * FACT n``,
     recInduct FactIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once FactIter,FACT]
      THEN Cases_on `n` 
      THEN FULL_SIMP_TAC arith_ss [FACT, AC MULT_ASSOC MULT_SYM]));

(*****************************************************************************)
(* Implement a function Fact to compute SND(FactIter (n,1))                  *)
(*****************************************************************************)
val (Fact,_,Fact_dev) =
 hwDefine
  `Fact n = SND(FactIter (n,1))`;

(*****************************************************************************)
(* Verify Fact is indeed the factorial function                              *)
(*****************************************************************************)
val FactThm =
 store_thm
  ("FactThm",
   ``Fact = FACT``,
   RW_TAC arith_ss [FUN_EQ_THM,Fact,FactIterRecThm]);

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val Fact_dev =
 REFINE
  (DEPTHR(LIB_REFINE[FactIter_dev])
    THENR DEPTHR(LIB_REFINE[SUBS [MultThm] Mult_dev])
    THENR DEPTHR(LIB_REFINE[MultIter_dev])
    THENR DEPTHR ATM_REFINE)
  Fact_dev;

(*****************************************************************************)
(* Create implementation of FACT (HOL's native factorial function)           *)
(*****************************************************************************)
val FACT_dev =
 save_thm
  ("FACT_dev",
   REWRITE_RULE [FactThm] Fact_dev);

val FACT_net =
 save_thm
  ("Fact_net",
   time MAKE_NETLIST FACT_dev);

val FACT_cir =
 save_thm
  ("Fact_cir",
   time MAKE_CIRCUIT FACT_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module FACT.                                                   *)
(*****************************************************************************)
dump_all_flag := true; 

(*****************************************************************************)
(* Change these variables to select simulator and viewer. Commenting out the *)
(* three assignments below will revert to the defaults: cver/dinotrace.      *)
(*****************************************************************************)
vlogger_path      := "/homes/mjcg/bin/verilog/vlogger/vlogcmd";
verilog_simulator := vlogger;

(******************************************************************************
(*****************************************************************************)
(* Alternative: could replace "/homes/mjcg/bin/verilog/vlogger/vlogcmd" by   *)
(* another verilog simulator.                                                *)
(*****************************************************************************)
verilog_simulator :=
 let fun verilog name =
      let val vlog_command = ("/homes/mjcg/bin/verilog/vlogger/vlogcmd"
                              ^ " " ^ name ^ ".vl")
          val code = Process.system vlog_command
          val _ = if isSuccess code
                   then print(vlog_command ^ "\n")
                   else print("Warning:\n failure signal returned by\n "
                              ^ vlog_command ^ "\n")
      in
       ()
      end
 in
  verilog
 end;
******************************************************************************)

waveform_viewer   := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)
numWarning := true;

SIMULATE FACT_cir [("inp","4")];

val _ = export_theory();
