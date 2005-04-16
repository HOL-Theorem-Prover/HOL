(*****************************************************************************)
(* The sources have lots of cut-and-paste-and-tweak style repetition for the *)
(* various combinational components (NOT, AND, OR, MUX, ADD, SUB, LESS, EQ). *)
(* I may eventually implement some generic tools to make adding new          *)
(* combinational components a one-liner. However, this will be a tricky      *)
(* and possibly -- at least for now -- not worth the effort, since adding    *)
(* new components is likely to be relatively rare.                           *)
(*                                                                           *)
(* Here are the steps currently needed to add a new component,               *)
(* illustrated with the addition of 32-bit bitwise exclusive-or (XOR32).     *)
(*****************************************************************************)

(*****************************************************************************)
(* Step 1                                                                    *)
(* ------                                                                    *)
(* Define the component in HOL                                               *)
(* (assumes word32Theory loaded and open)                                    *)
(*****************************************************************************)
val XOR32_def =
 Define 
  `XOR32(in1,in2,out) = !t. out t = (in1 t) # (in2 t)`;

(*****************************************************************************)
(* Step 2                                                                    *)
(* ------                                                                    *)
(* Prove some boilerplate theorems and add to global lists:                  *)
(*****************************************************************************)
val COMB_XOR32 =
 store_thm
  ("COMB_XOR32",
   ``COMB (UNCURRY $#) (in1 <> in2, out) = XOR32(in1,in2,out)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,XOR32_def]);

add_combinational_components[COMB_XOR32];

val XOR32_at =
 store_thm
  ("XOR32_at",
   ``XOR32(in1,in2,out)
     ==>
     XOR32(in1 at clk,in2 at clk,out at clk)``,
   RW_TAC std_ss [XOR32_def,at_def,tempabsTheory.when]);

add_temporal_abstractions[XOR32_at];

(*****************************************************************************)
(* Step 3                                                                    *)
(* ------                                                                    *)
(* Define a Verilog module as an ML string (XOR32vDef), a function to        *)
(* create an instance with a given size as a string (XOR32vInst), an         *)
(* instance counter (XOR32vInst_count -- used to create unique names for     *)
(* instances) and a function to print a HOL term ``XOR32(in1,in2,out)`` as   *)
(* an instance, using the the type of ``out`` to compute the word width      *)
(* needed to set parameter "size" in XOR32vDef (termToVerilog_XOR32).        *)
(* These functions are added to a couple of global lists.                    *)
(*****************************************************************************)
val XOR32vDef =
"// Combinational bitwise XOR32\n\
\module XOR32 (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = in1 ^ in2;\n\
\\n\
\endmodule\n\
\\n";

val XOR32vInst_count = ref 0;
fun XOR32vInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !XOR32vInst_count
     val _ = (XOR32vInst_count := count+1);
     val inst_name = "XOR32" ^ "_" ^ Int.toString count
 in
 (out " XOR32        "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size;
  out ";\n\n")
 end;

add_module ("XOR32", (XOR32vDef, XOR32vInst));

fun termToVerilog_XOR32 (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "XOR32")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then XOR32vInst
        out
        [("size", var2size(last(strip_pair(rand tm))))]
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_XOR32" "bad component term";

termToVerilogLib := (!termToVerilogLib) @ [termToVerilog_XOR32];




