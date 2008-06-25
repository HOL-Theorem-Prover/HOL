(*****************************************************************************)
(* Example to illiustrate adding a component: XOR32 (see ../README).         *)
(*****************************************************************************)

quietdec := true;
loadPath := "../" :: "../dff/" :: !loadPath;
map load
 ["compileTheory","compile","metisLib","intLib","wordsLib",
  "dffTheory","vsynth"];
open compile metisLib wordsTheory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory;
quietdec := false;

infixr 3 THENR;
infixr 3 ORELSER;
intLib.deprecate_int();

(*****************************************************************************)
(* Boilerplate. Probably more than is needed.                                *)
(*****************************************************************************)
add_combinational ["MOD","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","w2n","n2w"];

(*****************************************************************************)
(* Start new theory "Xor32"                                                  *)
(*****************************************************************************)
val _ = new_theory "Xor32";

(*****************************************************************************)
(* Add definition of XOR32                                                   *)
(*****************************************************************************)
AddBinop ("XOR32", (``UNCURRY $?? : word32#word32->word32``, "^"));

(*****************************************************************************)
(* Implement an atomic device computing XOR                                  *)
(*****************************************************************************)
val (Xor32,_,Xor32_dev) =
 hwDefine
  `Xor32(in1:word32,in2) = in1 ?? in2`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val Xor32Imp_dev =
 REFINE
  (DEPTHR ATM_REFINE)
  Xor32_dev;

val Xor32_cir =
 save_thm
  ("Xor32_cir",
   time MAKE_CIRCUIT Xor32Imp_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module Xor32.                                                  *)
(*****************************************************************************)
dump_all_flag := true; 

verilog_simulator := iverilog;
waveform_viewer   := gtkwave;

(*****************************************************************************)
(* Stop zillions of warning messages that HOL variables of type ``:num``     *)
(* are being converted to Verilog wires or registers of type [31:0].         *)
(*****************************************************************************)
numWarning := false;

SIMULATE Xor32_cir [("inp1","537"),("inp2","917")];

val _ = export_theory();
