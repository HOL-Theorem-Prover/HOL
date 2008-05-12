(*****************************************************************************)
(* Another example to illiustrate adding a component (see ../README).        *)
(*****************************************************************************)

(*****************************************************************************)
(* Boilerplate theory loading stuff                                          *)
(*****************************************************************************)
quietdec := true;
loadPath := "../" :: "../dff/" :: !loadPath;
app load
 ["compileTheory","compile","metisLib","intLib", "wordsLib",
  "dffTheory","vsynth"];
open compile metisLib wordsTheory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory;
quietdec := false;

infixr 3 THENR;
infixr 3 ORELSER;
intLib.deprecate_int();

(*****************************************************************************)
(* More boilerplate. Declaring combinational logic functions.                *)
(* Probably more than is needed.                                             *)
(*****************************************************************************)
add_combinational ["MOD","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","w2n","n2w"];

(*****************************************************************************)
(* Start new theory "NotXor32"                                               *)
(*****************************************************************************)
val _ = new_theory "NotXor32";

(*****************************************************************************)
(* Add definitions of XOR32 and NOT32                                        *)
(*****************************************************************************)
AddBinop ("XOR32", (``UNCURRY $?? : word32#word32->word32``, "^"));
add_vsynth [(``word_1comp:word32->word32``, fn l => ("~ " ^ hd l))];
add_vsynth [(``\(sel:bool,in1:word32,in2:word32). if sel then in1 else in2``,
   fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))];

(*****************************************************************************)
(* Implement an atomic device computing XOR                                  *)
(*****************************************************************************)
val (NotXor32,_,NotXor32_dev) =
 hwDefine
  `NotXor32(in1:word32,in2) = ((in1 ?? in2), ~(in1 ?? in2))`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val NotXor32Imp_dev =
 REFINE
  (DEPTHR ATM_REFINE)
  NotXor32_dev;

val NotXor32_cir =
 save_thm
  ("NotXor32_cir",
   time MAKE_CIRCUIT NotXor32Imp_dev);

(*****************************************************************************)
(* This dumps changes to all variables. Set to false to dump just the        *)
(* changes to module NotXor32.                                               *)
(*****************************************************************************)
dump_all_flag := true; 

verilog_simulator := iverilog;
waveform_viewer   := gtkwave;

SIMULATE NotXor32_cir [("inp1","537"),("inp2","917")];

val _ = export_theory();
