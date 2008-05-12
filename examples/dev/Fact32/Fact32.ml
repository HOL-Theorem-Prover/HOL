(*****************************************************************************)
(* High level (TFL) specification and implementation of factorial            *)
(* using ``:word32`` instead of ``:num``                                     *)
(*****************************************************************************)

quietdec := true;
loadPath := "../" :: "../dff/" :: !loadPath;
app load
 ["compileTheory","compile","metisLib", "wordsLib", "dffTheory","vsynth"];
open compile metisLib wordsTheory wordsLib;
open arithmeticTheory pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory;
quietdec := false;

infixr 3 THENR;
infixr 3 ORELSER;
numLib.prefer_num();

(*---------------------------------------------------------------------------*)
(* Tell hwDefine about how to deal with "predecessor-based" recursions on    *)
(* words. Allows factorial and other iterations to be dealt with.            *)
(*---------------------------------------------------------------------------*)

add_combinational ["MOD","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","w2n","n2w"];

(*****************************************************************************)
(* Start new theory "Fact32"                                                 *)
(*****************************************************************************)

val _ = new_theory "Fact32";

AddBinop ("ADD32",   (``UNCURRY $+ : word32#word32->word32``,  "+"));
AddBinop ("SUB32",   (``UNCURRY $- : word32#word32->word32``,  "-"));
AddBinop ("LESS32",  (``UNCURRY $< : word32#word32->bool``,    "<"));
AddBinop ("EQ32",    (``UNCURRY $= : word32#word32->bool``,    "=="));

(*****************************************************************************)
(* 32-bit MUX                                                                *)
(*****************************************************************************)
add_vsynth
 [(``\(sel:bool,in1:word32,in2:word32). if sel then in1 else in2``,
   fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))
 ];

(*****************************************************************************)
(* We implement multiplication with a naive iterative multiplier function    *)
(* (works by repeated addition)                                              *)
(*****************************************************************************)

val (Mult32Iter,Mult32Iter_ind,Mult32Iter_cir) =
 compile.cirDefine
  `(Mult32Iter (m,n,acc) =
     if m = 0w then (0w,n,acc) else Mult32Iter(m-1w,n,n + acc))
   measuring (w2n o FST)`;

(*****************************************************************************)
(* Create an implementation of a multiplier from Mult32Iter                  *)
(*****************************************************************************)

val (Mult32,_,Mult32_cir) =
 compile.cirDefine
  `Mult32(m,n) = SND(SND(Mult32Iter(m:word32,n,0):word32 # num # num))`;

(*****************************************************************************)
(* Implement iterative function as a step to implementing factorial          *)
(*****************************************************************************)

val (Fact32Iter,Fact32Iter_ind,Fact32Iter_cir) =
 compile.cirDefine
  `(Fact32Iter (n,acc) =
     if n = 0w then (n,acc) else Fact32Iter(n-1w, Mult32(n,acc)))
   measuring (w2n o FST)`;

(*****************************************************************************)
(* Implement a function Fact32 to compute SND(Fact32Iter (n,1))              *)
(*****************************************************************************)

val (Fact32,_,Fact32_cir) =
 compile.cirDefine
  `Fact32 n = SND(Fact32Iter (n,1w))`;

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module Fact32.                                                 *)
(*****************************************************************************)

dump_all_flag := true; 

(*****************************************************************************)
(* Change these variables to select simulator and viewer. Commenting out the *)
(* three assignments below will revert to the defaults: cver/dinotrace.      *)
(*****************************************************************************)

iverilog_path      := "/usr/bin/iverilog";
verilog_simulator  := iverilog;
waveform_viewer    := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)

numWarning := true;

SIMULATE Fact32_cir [("inp","4")];

val _ = export_theory();
