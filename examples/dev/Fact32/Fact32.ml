(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial            *)
(* using ``:word32`` instead of ``:num``                                     *)
(*****************************************************************************)

quietdec := true;
loadPath := "../" :: "word32" :: "../dff/" :: !loadPath;
map load
 ["compileTheory","compile","metisLib","intLib","word32Theory", "word32Lib",
  "dffTheory","vsynth" (* ,"compile32Theory"*)];
open compile metisLib word32Theory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory
  (* compile32Theory *) ;
quietdec := false;

infixr 3 THENR;
infixr 3 ORELSER;
intLib.deprecate_int();

(*---------------------------------------------------------------------------*)
(* Tell hwDefine about how to deal with "predecessor-based" recursions on    *)
(* words. Allows factorial and other iterations to be dealt with.            *)
(*---------------------------------------------------------------------------*)

val _ = 
  compile.termination_simps := (word32Theory.WORD_PRED_THM :: 
                                !compile.termination_simps);

add_combinational ["MOD","WL","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","HB","w2n","n2w"];

add_combinational_components
 [COMB_ADD, 
  COMB_SUB, 
  COMB_LESS, 
  COMB_EQ];

add_temporal_abstractions
 [EQ_at, 
  ADD_at, 
  SUB_at, 
  LESS_at];


(*****************************************************************************)
(* Start new theory "Fact32"                                                 *)
(*****************************************************************************)
val _ = new_theory "Fact32";

(*****************************************************************************)
(* We implement multiplication with a naive iterative multiplier function    *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)
val (Mult32Iter,Mult32Iter_ind,Mult32Iter_dev) =
 hwDefine
  `(Mult32Iter (m,n,acc) =
     if m = 0w then (0w,n,acc) else Mult32Iter(m-1w,n,n + acc))
   measuring (w2n o FST)`;

(*****************************************************************************)
(* Create an implementation of a multiplier from Mult32Iter                  *)
(*****************************************************************************)
val (Mult32,_,Mult32_dev) =
 hwDefine
  `Mult32(m,n) = SND(SND(Mult32Iter(m,n,0w)))`;

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)
val (Fact32Iter,Fact32Iter_ind,Fact32Iter_dev) =
 hwDefine
  `(Fact32Iter (n,acc) =
     if n = 0w then (n,acc) else Fact32Iter(n-1w, Mult32(n,acc)))
   measuring (w2n o FST)`;

(*****************************************************************************)
(* Implement a function Fact32 to compute SND(Fact32Iter (n,1))              *)
(*****************************************************************************)
val (Fact32,_,Fact32_dev) =
 hwDefine
  `Fact32 n = SND(Fact32Iter (n,1w))`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val Fact32Imp_dev =
 REFINE
  (DEPTHR(LIB_REFINE[Fact32Iter_dev])
    THENR DEPTHR(LIB_REFINE[Mult32_dev])
    THENR DEPTHR(LIB_REFINE[Mult32Iter_dev])
    THENR DEPTHR ATM_REFINE)
  Fact32_dev;

val Fact32_net =
 save_thm
  ("Fact32_net",
   time MAKE_NETLIST Fact32Imp_dev);

val Fact32_cir =
 save_thm
  ("Fact32_cir",
   time MAKE_CIRCUIT Fact32Imp_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module Fact32.                                                 *)
(*****************************************************************************)
dump_all_flag := true; 

(*****************************************************************************)
(* Change these variables to select simulator and viewer. Commenting out the *)
(* three assignments below will revert to the defaults: cver/dinotrace.      *)
(*****************************************************************************)
vlogger_path      := "/homes/mjcg/bin/verilog/vlogger/vlogcmd";
verilog_simulator := vlogger;
waveform_viewer   := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)
numWarning := true;

SIMULATE Fact32_cir [("inp","4")];

val _ = export_theory();
