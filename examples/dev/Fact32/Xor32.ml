(*****************************************************************************)
(* Example to illiustrate adding a component (see ../README).                *)
(*****************************************************************************)

quietdec := true;
loadPath := "../" :: "word32" :: "../dff/" :: !loadPath;
map load
 ["compileTheory","compile","metisLib","intLib","word32Theory", "word32Lib",
  "dffTheory","vsynth" ,"compile32Theory"];
open compile metisLib word32Theory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth dffTheory
     compile32Theory;
quietdec := false;

infixr 3 THENR;
infixr 3 ORELSER;
intLib.deprecate_int();

(*****************************************************************************)
(* Boilerplate. Probably more than is needed.                                *)
(*****************************************************************************)
add_combinational ["MOD","WL","DIV"];
add_combinational ["word_add","word_sub"];
add_combinational ["BITS","HB","w2n","n2w"];

(*****************************************************************************)
(* Start new theory "Xor32"                                                  *)
(*****************************************************************************)
val _ = new_theory "Xor32";

(*****************************************************************************)
(* The sources have lots of cut-and-paste-and-tweak style repetition for the *)
(* various combinational components (NOT, AND, OR, MUX, ADD, SUB, LESS, EQ). *)
(* I may eventually implement some generic tools to make adding new          *)
(* combinational components a one-liner. However, this will be a tricky      *)
(* and possibly -- at least for now -- not worth the effort, since adding    *)
(* new components is likely to be relatively rare.                           *)
(*                                                                           *)
(* Here are the steps currently needed to add a new component,               *)
(* illustrated with the addition of exclusive-or (XOR).                      *)
(*****************************************************************************)

(*****************************************************************************)
(* Step 1                                                                    *)
(* ------                                                                    *)
(* Define the component in HOL                                               *)
(* (assumes word32Theory loaded and open)                                    *)
(*****************************************************************************)
val XOR_def =
 Define 
  `XOR(in1,in2,out) = !t. out t = (in1 t) # (in2 t)`;

(*****************************************************************************)
(* Step 2                                                                    *)
(* ------                                                                    *)
(* Prove some boilerplate theorems and add to global lists:                  *)
(*****************************************************************************)
val COMB_XOR =
 store_thm
  ("COMB_XOR",
   ``COMB (UNCURRY $#) (in1 <> in2, out) = XOR(in1,in2,out)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,XOR_def]);

add_combinational_components[COMB_XOR];

val XOR_at =
 store_thm
  ("XOR_at",
   ``XOR(in1,in2,out)
     ==>
     XOR(in1 at clk,in2 at clk,out at clk)``,
   RW_TAC std_ss [XOR_def,at_def,tempabsTheory.when]);

add_temporal_abstractions[XOR_at];

(*****************************************************************************)
(* Step 3                                                                    *)
(* ------                                                                    *)
(* Define a Verilog module as an ML string (XORvDef), a function to          *)
(* create an instance with a given size as a string (XORvInst), an           *)
(* instance counter (XORvInst_count -- used to create unique names for       *)
(* instances) and a function to print a HOL term ``XOR(in1,in2,out)`` as     *)
(* an instance, using the the type of ``out`` to compute the word width      *)
(* needed for setting of parameter "size" in XORvDef (termToVerilog_XOR).    *)
(* These functions are added to a couple of global lists.                    *)
(*****************************************************************************)
val XORvDef =
"// Combinational bitwise XOR\n\
\module XOR (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = in1 ^ in2;\n\
\\n\
\endmodule\n\
\\n";

val XORvInst_count = ref 0;
fun XORvInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !XORvInst_count
     val _ = (XORvInst_count := count+1);
     val inst_name = "XOR" ^ "_" ^ Int.toString count
 in
 (out " XOR        "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size;
  out ";\n\n")
 end;

add_module ("XOR", (XORvDef, XORvInst));

fun termToVerilog_XOR (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "XOR")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then XORvInst
        out
        [("size", var2size(last(strip_pair(rand tm))))]
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_XOR" "bad component term";

termToVerilogLib := (!termToVerilogLib) @ [termToVerilog_XOR];

(*****************************************************************************)
(* Implement an atomic device computing XOR                                  *)
(*****************************************************************************)
val (Xor32,_,Xor32_dev) =
 hwDefine
  `Xor32(in1,in2) = in1 # in2`;

(*****************************************************************************)
(* Derivation using refinement combining combinators                         *)
(*****************************************************************************)
val Xor32Imp_dev =
 REFINE
  (DEPTHR ATM_REFINE)
  Xor32_dev;

val Xor32_net =
 save_thm
  ("Xor32_net",
   time MAKE_NETLIST Xor32Imp_dev);

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
numWarning := true;

SIMULATE Xor32_cir [("inp1","537"),("inp2","917")];

val _ = export_theory();
