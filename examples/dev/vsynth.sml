
(*****************************************************************************)
(* Coversion of output of compiler to Verilog                                *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
loadPath :="dff" :: !loadPath;
map load  
 ["composeTheory","compileTheory", "hol88Lib" (*for subst*),"compile",
  "Date","FileSys","TextIO","Process","Char","String"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory listTheory
     composeTheory compileTheory compile;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib compileTheory;

(******************************************************************************
* Open theories
******************************************************************************)
open arithmeticTheory pairLib pairTheory PairRules combinTheory listTheory
     unwindLib composeTheory compileTheory compile;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)
val ERR = mk_HOL_ERR "compile";

(*****************************************************************************)
(* Date and time                                                             *)
(*****************************************************************************)
fun date() = Date.fmt "%c" (Date.fromTimeLocal (Time.now ()));

(*****************************************************************************)
(* Boilerplate definitions of primitive components                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Clock. Default has 10 units of simulation time between edges              *)
(*****************************************************************************)
val ClockvDef =
"// Clock\n\
\module Clock (clk);\n\
\ parameter period = 10; // time between clock edges\n\
\ output clk;\n\
\ reg clk;\n\
\\n\
\ initial begin clk = 0; forever #period clk <= !clk; end\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational boolean inverter                                            *)
(*****************************************************************************)
val NOTvDef =
"// Combinational inverter\n\
\module NOT (inp,out);\n\
\ input inp;\n\
\ output out;\n\
\\n\
\ assign out = !inp;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Constant output of T (1)                                                  *)
(*****************************************************************************)
val TRUEvDef =
"// Constant T (1)\n\
\module TRUE (out);\n\
\ output out;\n\
\\n\
\ assign out = 1;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational multiplexer. Default has 32-bits inputs and output          *)
(*****************************************************************************)
val MUXvDef =
"// Combinational multiplexer\n\
\module MUX (sw,in1,in2,out);\n\
\ parameter size = 31;\n\
\ input sw;\n\
\ input  [size:0] in1,in2;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = sw?in1:in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational boolean and-gate                                            *)
(*****************************************************************************)
val ANDvDef =
"// Combinational and-gate\n\
\module AND (in1,in2,out);\n\
\ input in1,in2;\n\
\ output out;\n\
\\n\
\ assign out = in1 && in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational boolean or-gate                                             *)
(*****************************************************************************)
val ORvDef =
"// Combinational or-gate\n\
\module OR (in1,in2,out);\n\
\ input in1,in2;\n\
\ output out;\n\
\\n\
\ assign out = in1 || in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Positive edge triggered Dtype register. Default is 32-bits wide.          *)
(*****************************************************************************)
val DtypevDef =
"// Positive edge triggered Dtype register\n\
\module Dtype (clk,d,q);\n\
\ parameter size = 31;\n\
\ input clk;\n\
\ input  [size:0] d;\n\
\ output [size:0] q;\n\
\ reg    [size:0] q;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Boolean positive edge triggered flip-flop starting in state 0             *)
(*****************************************************************************)
val DffvDef =
"// Boolean positive edge triggered flip-flop starting in state 0\n\
\module Dff (clk,d,q);\n\
\ input clk,d;\n\
\ output q;\n\
\ reg q;\n\
\\n\
\ initial q = 0;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Non-primitive components                                                  *)
(*****************************************************************************)

(*****************************************************************************)
(* Combinational adder. Default has 32-bit inputs and output                 *)
(*****************************************************************************)
val ADDvDef =
"// Combinational adder\n\
\module ADD (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = in1 + in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Read only register holding a number (default value 0)                     *)
(*****************************************************************************)
val CONSTANTvDef =
"// Read only register\n\
\module CONSTANT (out);\n\
\ parameter size  = 31;\n\
\ parameter value = 0;\n\

\ output [size:0] out;\n\
\\n\
\ assign out = value;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational subtractor. Default has 32-bit inputs and output            *)
(*****************************************************************************)
val SUBvDef =
"// Combinational subtractor\n\
\module SUB (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output [size:0] out;\n\
\\n\
\ assign out = in1 - in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational less-than test. Default has 32-bit inputs                   *)
(*****************************************************************************)
val LESSvDef =
"//Combinational less-than test\n\
\module LESS (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output out;\n\
\\n\
\ assign out = in1 < in2;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Combinational equality test. Default has 32-bit inputs and output         *)
(*****************************************************************************)
val EQvDef =
"// Combinational equality test\n\
\module EQ (in1,in2,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] in1,in2;\n\
\ output out;\n\
\\n\
\ assign out = in1 == in2;\n\
\\n\
\endmodule\n\
\\n";

fun string2int s =
 let val (SOME n) = Int.fromString s in n end;

(*****************************************************************************)
(* ``v : num -> wordn`` --> "n-1" (e.g. v:word32`` --> "31")                 *)
(* ``v : num -> num``   --> 31                                               *)
(* ``v : num -> bool``  --> "0"                                              *)
(*****************************************************************************)
fun var2size tm =
 let val ("fun", [_,ty]) = dest_type(type_of tm)
     val n = if (ty = ``:bool``)
              then 1
              else if (ty = ``:num``)
              then 32
              else
               let val chars = explode(fst(dest_type ty))
                   val num = tl(tl(tl(tl chars)))
               in
                string2int(implode num)
               end
    
 in
  Int.toString(n-1)
 end;

(*****************************************************************************)
(* Make instances of modules. Each kind of module M generates an instance    *)
(* M_n, where n starts at 0 and is increased each time a new instance is     *)
(* created. A reference variable MvInst_count holds the current value of n.  *)
(*****************************************************************************)

(*****************************************************************************)
(* ClockvInst out n "clk" prints, using function out, an instance of Clock   *)
(* driving a line named "clk" and with n units of time between edges.        *)
(*****************************************************************************)
val ClockvInst_count = ref 0;
fun ClockvInst (out:string->unit) [("period",period)] [clk_name] =
 let val count = !ClockvInst_count
     val _ = (ClockvInst_count := count+1);
     val inst_name = "Clock" ^ "_" ^ Int.toString count
 in
 (out " Clock      "; out inst_name;
  out " (";out clk_name; out ");\n";
  out "   defparam ";out inst_name; out ".period = "; out period; 
  out ";\n\n")
 end;

(*****************************************************************************)
(* TRUEvInst out "output" prints, using out, and instance of TRUE driving    *)
(* a line named "output"                                                     *)
(*****************************************************************************)
val TRUEvInst_count = ref 0;
fun TRUEvInst (out:string->unit) [] [out_name] =
 let val count = !TRUEvInst_count
     val _ = (TRUEvInst_count := count+1);
     val inst_name = "TRUE" ^ "_" ^ Int.toString count
 in
 (out " TRUE       "; out inst_name;
  out " (";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_TRUE (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "TRUE")
     andalso is_var(rand tm)
  then TRUEvInst out [] [fst(dest_var(rand tm))]
  else raise ERR "termToVerilog_TRUE" "bad component term";


(*****************************************************************************)
(* Print an instance of a NOT                                                *)
(*****************************************************************************)
val NOTvInst_count = ref 0;
fun NOTvInst (out:string->unit) [] [in_name,out_name] =
 let val count = !NOTvInst_count
     val _ = (NOTvInst_count := count+1);
     val inst_name = "NOT" ^ "_" ^ Int.toString count
 in
 (out " NOT        "; out inst_name;
  out " (";out in_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_NOT (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "NOT")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 2)
     andalso all is_var (strip_pair(rand tm))
  then NOTvInst out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_NOT" "bad component term";

(*****************************************************************************)
(* Print an instance of an AND                                                *)
(*****************************************************************************)
val ANDvInst_count = ref 0;
fun ANDvInst (out:string->unit) [] [in1_name,in2_name,out_name] =
 let val count = !ANDvInst_count
     val _ = (ANDvInst_count := count+1);
     val inst_name = "AND" ^ "_" ^ Int.toString count
 in
 (out " AND        "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_AND (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "AND")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then ANDvInst out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_AND" "bad component term";

(*****************************************************************************)
(* Print an instance of an OR                                                *)
(*****************************************************************************)
val ORvInst_count = ref 0;
fun ORvInst (out:string->unit) [] [in1_name,in2_name,out_name] =
 let val count = !ORvInst_count
     val _ = (ORvInst_count := count+1);
     val inst_name = "OR" ^ "_" ^ Int.toString count
 in
 (out " OR         "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_OR (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "OR")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then ORvInst out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_OR" "bad component term";

(*****************************************************************************)
(* Print and instance of a MUX with a given size                             *)
(*****************************************************************************)
val MUXvInst_count = ref 0;
fun MUXvInst (out:string->unit) [("size",size)] [sw_name,in1_name,in2_name,out_name] =
 let val count = !MUXvInst_count
     val _ = (MUXvInst_count := count+1);
     val inst_name = "MUX" ^ "_" ^ Int.toString count
 in
 (out " MUX        "; out inst_name;
  out " (";out sw_name;out",";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_MUX (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "MUX")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 4)
     andalso all is_var (strip_pair(rand tm))
  then MUXvInst 
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_MUX" "bad component term";

(*****************************************************************************)
(* Print an instance of a Dtype with a given size                            *)
(*****************************************************************************)
val DtypevInst_count = ref 0;
fun DtypevInst (out:string->unit) [("size",size)] [clk_name,in_name,out_name] =
 let val count = !DtypevInst_count
     val _ = (DtypevInst_count := count+1);
     val inst_name = "Dtype" ^ "_" ^ Int.toString count
 in
 (out " Dtype      "; out inst_name;
  out " (";out clk_name;out",";out in_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_Dtype (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "Dtype")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then DtypevInst 
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_Dtype" "bad component term";

(*****************************************************************************)
(* Print an instance of a Dff                                                *)
(*****************************************************************************)
val DffvInst_count = ref 0;
fun DffvInst (out:string->unit) [] [clk_name,in_name,out_name] =
 let val count = !DffvInst_count
     val _ = (DffvInst_count := count+1);
     val inst_name = "Dff" ^ "_" ^ Int.toString count
 in
 (out " Dff        "; out inst_name;
  out " (";out clk_name;out",";out in_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_Dff (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "Dff")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then DffvInst out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_Dff" "bad component term";


(*****************************************************************************)
(* Print an instance of an CONSTANT with a given size and value              *)
(*****************************************************************************)
val CONSTANTvInst_count = ref 0;
fun CONSTANTvInst 
 (out:string->unit) [("size",size),("value",value)] [out_name] =
 let val count = !CONSTANTvInst_count
     val _ = (CONSTANTvInst_count := count+1);
     val inst_name = "CONSTANT" ^ "_" ^ Int.toString count
 in
 (out " CONSTANT   "; out inst_name;
  out " (";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size  = "; out size; 
  out "\n";
  out "   defparam ";out inst_name; out ".value = "; out value; 
  out ";\n\n")
 end;

fun termToVerilog_CONSTANT (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "CONSTANT")
     andalso numSyntax.is_numeral(rand(rator tm))
     andalso is_var (rand tm)
  then CONSTANTvInst 
        out 
        [("size", var2size(last(strip_pair(rand tm)))),
         ("value",Arbnum.toString(numSyntax.dest_numeral(rand(rator tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_CONSTANT" "bad component term";

(*****************************************************************************)
(* Print an instance of an ADD with a given size                             *)
(*****************************************************************************)
val ADDvInst_count = ref 0;
fun ADDvInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !ADDvInst_count
     val _ = (ADDvInst_count := count+1);
     val inst_name = "ADD" ^ "_" ^ Int.toString count
 in
 (out " ADD        "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_ADD (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "ADD")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then ADDvInst 
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_ADD" "bad component term";

(*****************************************************************************)
(* Print an instance of a SUB with a given size                              *)
(*****************************************************************************)
val SUBvInst_count = ref 0;
fun SUBvInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !SUBvInst_count
     val _ = (SUBvInst_count := count+1);
     val inst_name = "SUB" ^ "_" ^ Int.toString count
 in
 (out " SUB        "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_SUB (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "SUB")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then SUBvInst 
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_SUB" "bad component term";

(*****************************************************************************)
(* Print an instance of a LESS with a given size                             *)
(*****************************************************************************)
val LESSvInst_count = ref 0;
fun LESSvInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !LESSvInst_count
     val _ = (LESSvInst_count := count+1);
     val inst_name = "LESS" ^ "_" ^ Int.toString count
 in
 (out " LESS       "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_LESS (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "LESS")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then LESSvInst 
        out 
        [("size", var2size(hd(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_LESS" "bad component term";

(*****************************************************************************)
(* Print an instance of an EQ with a given size                              *)
(*****************************************************************************)
val EQvInst_count = ref 0;
fun EQvInst (out:string->unit) [("size",size)] [in1_name,in2_name,out_name] =
 let val count = !EQvInst_count
     val _ = (EQvInst_count := count+1);
     val inst_name = "EQ" ^ "_" ^ Int.toString count
 in
 (out " EQ         "; out inst_name;
  out " (";out in1_name;out",";out in2_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_EQ (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "EQ")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then EQvInst 
        out 
        [("size", var2size(hd(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_EQ" "bad component term";

fun termToVerilog out tm =
 termToVerilog_TRUE out tm       handle _ =>
 termToVerilog_NOT out tm        handle _ =>
 termToVerilog_AND out tm        handle _ =>
 termToVerilog_OR out tm         handle _ =>
 termToVerilog_MUX out tm        handle _ =>
 termToVerilog_Dtype out tm      handle _ =>
 termToVerilog_Dff out tm        handle _ =>
 termToVerilog_CONSTANT out tm   handle _ =>
 termToVerilog_ADD out tm        handle _ =>
 termToVerilog_SUB out tm        handle _ =>
 termToVerilog_LESS out tm       handle _ =>
 termToVerilog_EQ out tm         handle _ =>
 (if_print "termToVerilog failed on:\n";
  if_print_term tm;
  raise ERR "termToVerilog" "can't handle this case");

(* Testing stuff
val file_name = "foo";
val outstr       = TextIO.openOut(file_name^".vl")
fun out s        = TextIO.output(outstr,s);

ClockvInst out [("period","10")] ["clk1"];
ClockvInst out [("period","20")] ["clk2"];

TRUEvInst out  [] ["out1"];
TRUEvInst out  [] ["out2"];

ANDvInst out [] ["inA1","inA2","outA"];
ANDvInst out [] ["inB1","inB2","outB"];

ORvInst out  [] ["inA1","inA2","outA"];
ORvInst out  [] ["inB1","inB2","outB"];

MUXvInst out [("size","31")] ["sw","inA1","inA2","outA"];
MUXvInst out [("size","15")] ["sw","inB1","inB2","outB"];

DtypevInst out [("size","31")] ["clk1","in1","out1"];
DtypevInst out [("size","15")] ["clk2","in2","out2"];

DffvInst out [] ["clk1","in1","out1"];
DffvInst out [] ["clk2","in2","out2"];

ADDvInst out [("size","31")] ["inA1","inA2","outA"];
ADDvInst out [("size","15")] ["inB1","inB2","outB"];

SUBvInst out [("size","31")] ["inA1","inA2","outA"];
SUBvInst out [("size","15")] ["inB1","inB2","outB"];

LESSvInst out [("size","31")] ["inA1","inA2","outA"];
LESSvInst out [("size","15")] ["inB1","inB2","outB"];

TextIO.flushOut outstr;
TextIO.closeOut outstr;

*)

(*****************************************************************************)
(* Library of modules with Verilog models                                    *)
(*****************************************************************************)
val module_lib = 
 ref
  ([]:(string * 
       (string *
        ((string->unit)->(string*string)list->string list->unit)))list);

fun add_module (name,(vdef,vinst)) = 
 (module_lib := (!module_lib) @ [(name,(vdef,vinst))]);

val _ = 
 map
  add_module
  [("Dtype",    (DtypevDef,      DtypevInst)),
   ("Dff",      (DffvDef,        DffvInst)),
   ("TRUE",     (TRUEvDef,       TRUEvInst)),
   ("NOT",      (NOTvDef,        NOTvInst)),
   ("AND",      (ANDvDef,        ANDvInst)),
   ("OR",       (ORvDef,         ORvInst)),
   ("MUX",      (MUXvDef,        MUXvInst)),
   ("CONSTANT", (CONSTANTvDef,   CONSTANTvInst)),
   ("ADD",      (ADDvDef,        ADDvInst)),
   ("SUB",      (SUBvDef,        SUBvInst)),
   ("LESS",     (LESSvDef,       LESSvInst)),
   ("EQ",       (EQvDef,         EQvInst))];

(*****************************************************************************)
(* ``v0 <> ... <> vn`` --> [``v0``, ... ,``vn``]                             *)
(*****************************************************************************)
fun strip_BUS_CONCAT tm =
 if is_BUS_CONCAT tm
  then let val (tm1,tm2) = dest_BUS_CONCAT tm
       in
        strip_BUS_CONCAT tm1 @ strip_BUS_CONCAT tm2
       end
  else [tm];

(*
** (|- InRise clk 
**     ==>
**     (?v0 .... vn. M1(...) /\ ... /\ Mp(...))
**     ==>
**     DEV Spec (load at clk,
**               (inp1 <> ... <> inpu) at clk,
**               done at clk,
**               (out1 <> ... <> outv) at clk))
**
** -->
**
** (Spec,
**  (``clk``,``load``,[``inp1``,...,``inpu``],``done``,[``out1``,...,``outv``]),
**  [``v0``, ... ,``vn``],
**  [``M1(...)``, ... ,``Mp(...)``])
*)

fun dest_cir thm =
 let val tm = concl(SPEC_ALL thm)
     val (tm1,tm2) = dest_imp tm
     val (tm3,tm4) = dest_imp tm2
     val spec_tm = rand(rator tm4)
     val clk_tm = rand tm1
     val [load_tm,inp_tm,done_tm,out_tm] =
         map (rand o rator) (strip_pair(rand tm4))
     val (vars,bdy) = strip_exists tm3
     val tml = strip_conj bdy
     val inpl = strip_BUS_CONCAT inp_tm
     val outl = strip_BUS_CONCAT out_tm
 in
  (spec_tm,(clk_tm,load_tm,inpl,done_tm,outl), vars, tml)
 end;

(*****************************************************************************)
(* Name of a variable                                                        *)
(*****************************************************************************)
fun var_name v = fst(dest_var v);

(*****************************************************************************)
(* Create a output stream to a file called file_name, apply a printer to     *)
(* it and then flush and close the stream.                                   *)
(*****************************************************************************)
fun printToFile file_name printer =
 let val outstr = TextIO.openOut file_name
     fun out s = TextIO.output(outstr,s)
 in
 (printer out;
  TextIO.flushOut outstr;
  TextIO.closeOut outstr)
 end;

(*****************************************************************************)
(* []              --> []                                                    *)
(* ["s"]           --> ["s"]                                                 *)
(* ["s1",...,"sn"] --> ["s1", "," , ... , ",", "sn"]                         *)
(*****************************************************************************)
fun add_commas [] = []
 |  add_commas [s] = [s]
 |  add_commas (s::sl) = s :: "," :: add_commas sl;

(*
** MAKE_VERILOG
**  name 
**  (|- InRise clk 
**      ==>
**      (?v0 .... vn. <circuit>)
**      ==>
**      DEV Spec (load at clk,
**                (inp1 <> ... <> inpu) at clk,
**                done at clk,
**                (out1 <> ... <> outv) at clk))
**  output_stream
** 
** creates a module called name that has
** the definitions of the modules used in <circuit>,
** and prints it and the definitions it needs to output_stream.
**
** The header is:
**
**  module name (clk,load,inp1,...,inpu,done,out1,...,outv);
**   input  clk,load;
**   input  [<size>:0] inp1,inp2;
**   output done;
**   output [<size>:0] out;
**   wire   clk,done;
**
** where <size> is the appropriate width computed from the types.
*)

(*
printToFile "Foo.vl" (MAKE_VERILOG "Foo" thm);
*)

fun MAKE_VERILOG name thm out =
 let val (spec_tm,
          (clk, load_tm,inpl,done_tm,outl), 
          vars, 
          modules) = dest_cir thm
     val clk_name = var_name clk
     val load_name = var_name load_tm
     val inp_names = map var_name inpl
     val done_name = var_name done_tm
     val out_names = map var_name outl
     val module_args = 
          [clk_name,load_name] @ inp_names @ [done_name] @ out_names;
     val module_names  = map (fst o dest_const o fst o strip_comb) modules
     val _ = if not(null(subtract module_names (map fst (!module_lib))))
              then (print "unknown module in circuit: ";
                    print(hd(subtract module_names (map fst (!module_lib))));
                    print "\n";
                    raise ERR "MAKE_VERILOG" "unknown modules in circuit")
              else ()
 in
 (out("// Definition of module " ^ name ^ " [Created: " ^ date() ^ "]\n\n// Definitions of components\n\n");
  
  map            (* Print definition of components *)
   (fn(_,(def,_)) => out def)
   (filter
     (fn(name,_) => mem name module_names)
     (!module_lib));
  out("\n// Definition of module " ^ name ^ "\n");
  out "module ";
  out name; 
  out " (";
  map out (add_commas module_args);
  out ");\n";
  out(" input " ^ clk_name ^ "," ^ load_name ^ ";\n");
  map 
   (fn v => out(" input [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n")) 
   inpl;
  out(" output " ^ done_name ^ ";\n");
  map 
   (fn v => out(" output [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n")) 
   outl;
  out(" wire " ^ clk_name ^ "," ^ done_name ^ ";\n");
  out "\n";
  map 
   (fn v => out(" wire [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n")) 
   vars;
  out "\n";
  map
   (termToVerilog out)
   modules;
  out"endmodule\n")
 end;


(* Example for testing
val stimulus =
 [(10, 12, [("inp1", "5"),("inp2","7")], 15),
  (10, 12, [("inp1", "0"),("inp2","5")], 15),
  (10, 12, [("inp1", "3"),("inp2","3")], 15)];
*)

(*****************************************************************************)
(* Print in Verilog one line of a stimulus specification                     *)
(*****************************************************************************)
fun printStimulusLine 
 (out:string->unit) load_name (start_delay, load_delay, in_stim, end_delay) =
 (out("   " ^ "#" ^ Int.toString start_delay ^ "\n");
  out("   " ^ load_name ^ " = 0;\n");
  out("   " ^ "#" ^ Int.toString load_delay ^ "\n");
  map 
   (fn (inname,inval) => out("   " ^ inname ^ " = " ^ inval ^ ";\n"))
   in_stim;
  out("   " ^ "#" ^ Int.toString end_delay ^ "\n");
  out("   " ^ load_name ^ " = 1;\n"));

(* Example for testing
val maxtime = 1000
and period  = 5
and file_name = "foo"
and thm = Adder_cir
and stimulus =
 [(10, 12, [("inp1", "5"),("inp2","7")], 15),
  (10, 12, [("inp1", "5"),("inp2","0")], 15),
  (10, 12, [("inp1", "3"),("inp2","3")], 15)]
and name = "Adder";

printToFile "Foo.vl" (MAKE_SIMULATION maxtime period thm stimulus name);
*)


fun MAKE_SIMULATION name thm maxtime period stimulus out =
 let val (spec_tm,
          (clk, load_tm,inpl,done_tm,outl), 
          vars, 
          modules) = dest_cir thm
     val clk_name = var_name clk
     val load_name = var_name load_tm
     val inp_names = map var_name inpl
     val done_name = var_name done_tm
     val out_names = map var_name outl
     val module_args = 
          [clk_name,load_name] @ inp_names @ [done_name] @ out_names;

 in
 (MAKE_VERILOG name thm out;
  out "\n";
  out ClockvDef; (* Print definition of Clock *)
  out "module Main ();\n";
  out(" parameter maxtime = " ^ Int.toString maxtime ^ ";\n");
  out(" wire " ^ clk_name ^ ";\n");
  out(" reg " ^ load_name ^ ";\n");
  map 
   (fn v => out(" reg [0:" ^ var2size v ^ "] " ^ var_name v ^ ";\n")) 
   inpl;
  out(" wire " ^ done_name ^ ";\n");
  map 
   (fn v => out(" wire [0:" ^ var2size v ^ "] " ^ var_name v ^ ";\n")) 
   outl;
  out "\n";
  out(" initial #maxtime $finish;\n\n");
  out " initial\n  begin\n";
  map (printStimulusLine out load_name) stimulus;
  out " end\n";
  out "\n";
  out(" initial\n  begin\n   $dumpfile(\"" ^name ^ ".vcd\");\n   $dumpvars(1,");
  map out (add_commas module_args);
  out(");\n  end\n");
  out "\n";
  ClockvInst out [("period", Int.toString period)] [clk_name]; (* Create a clock *)
  out(" " ^ name ^ "    " ^ name ^ " (");
  map out (add_commas module_args);
  out ");\n\n";
  out"endmodule\n")
 end;

(*
** PRINT_VERILOG
**  (|- InRise clk 
**      ==>
**      (?v0 .... vn. <circuit>)
**      ==>
**      DEV Spec (load at clk,
**                (inp1 <> ... <> inpu) at clk,
**                done at clk,
**                (out1 <> ... <> outv) at clk))
** 
** Prints translation to Verilog to a file Spec.vl and creates a module Spec
* (fails if Spec isn't a constant)
*)

fun PRINT_VERILOG thm =
 let val name = fst(dest_const(#1(dest_cir thm)))
 in
  printToFile (name ^ ".vl") (MAKE_VERILOG name thm)
 end;

(*
** PRINT_SIMULATION
**  (|- InRise clk 
**      ==>
**      (?v0 .... vn. <circuit>)
**      ==>
**      DEV Spec (load at clk,
**                (inp1 <> ... <> inpu) at clk,
**                done at clk,
**                (out1 <> ... <> outv) at clk))
**  maxtime period stimulus
** 
** Prints translation to Verilog and a stimulus to a file Spec.vl and creates 
** a module Main that invokes module Spec connected to a simulation environment
** described by stimulus. 
** (fails if Spec isn't a constant)
*)

fun PRINT_SIMULATON thm maxtime period stimulus =
 let val name = fst(dest_const(#1(dest_cir thm)))
 in
  printToFile (name ^ ".vl") (MAKE_SIMULATION name thm maxtime period stimulus)
 end;

