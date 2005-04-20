 
val NOT32_def =
 Define 
  `NOT32(inp,out) = !t. out t = ~(inp t : word32)`;

val COMB_NOT32 =
 store_thm
  ("COMB_NOT32",
   ``COMB ($~:word32->word32) (inp, out) = NOT32(inp,out)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,NOT32_def]);

add_combinational_components[COMB_NOT32];

val NOT32_at =
 store_thm
  ("NOT32_at",
   ``NOT32(inp,out)
     ==>
     NOT32(inp at clk,out at clk)``,
   RW_TAC std_ss [NOT32_def,at_def,tempabsTheory.when]);

add_temporal_abstractions[NOT32_at];

val NOT32vDef =
"// Combinational 32-bit inverter\n\
\module NOT32 (inp,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] inp;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = ~inp;\n\
\\n\
\endmodule\n\
\\n";

val NOT32vInst_count = ref 0;
fun NOT32vInst (out:string->unit) [("size",size)] [inp_name,out_name] =
 let val count = !NOT32vInst_count
     val _ = (NOT32vInst_count := count+1);
     val inst_name = "NOT32" ^ "_" ^ Int.toString count
 in
 (out " NOT32        "; out inst_name;
  out " (";out inp_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size;
  out ";\n\n")
 end;

add_module ("NOT32", NOT32vDef);

fun termToVerilog_NOT32 (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "NOT32")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 2)
     andalso all is_var (strip_pair(rand tm))
  then NOT32vInst
        out
        [("size", var2size(last(strip_pair(rand tm))))]
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_NOT32" "bad component term";

termToVerilogLib := (!termToVerilogLib) @ [termToVerilog_NOT32];




