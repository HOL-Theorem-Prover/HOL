structure vsynth =
struct

(*****************************************************************************)
(* Conversion ("pretty printing") of output of compiler to Verilog           *)
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
app load ["compile","wordsLib",
          "FileSys","TextIO","Process","Char","String"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory listTheory
     composeTheory compileTheory compile;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)

local
open HolKernel Parse boolLib bossLib compileTheory;

(******************************************************************************
* Open theories
******************************************************************************)

open arithmeticTheory pairLib pairTheory PairRules combinTheory listTheory
     unwindLib composeTheory compileTheory compile;

in

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)

val ERR = mk_HOL_ERR "vsynth";

(*****************************************************************************)
(* Date and time                                                             *)
(*****************************************************************************)

fun date() = "<UNSPECIFIED DATE>"
(* used to be: Date.fmt "%c" (Date.fromTimeLocal (Time.now ()));
   but this leads to occasional segfaults in some glibc environments under
   Poly/ML.
*)

(*****************************************************************************)
(* Convert a term to a string showing types of variables                     *)
(* by setting show_types to true during printing                             *)
(*****************************************************************************)

fun term2string tm =
 let val saved_val = !show_types
     val _ = (show_types := true)
     val s = Parse.term_to_string tm
     val _ = (show_types := saved_val)
 in
  s
 end;

(*****************************************************************************)
(* Test if a string is a constant                                            *)
(*****************************************************************************)

fun is_constant s = mem s (known_constants());

(*****************************************************************************)
(* Boilerplate definitions of primitive components                           *)
(*****************************************************************************)

fun string2int s =
 let val (SOME n) = Int.fromString s in n end;

(*****************************************************************************)
(* Test if a ty is ``:word<n>`` for some n                                   *)
(*****************************************************************************)

val is_word_type = wordsSyntax.is_word_type;

(*****************************************************************************)
(* Extraxt <n> from ``:word<n>``                                             *)
(*****************************************************************************)

val dest_word_type =
  Arbnum.toInt o fcpLib.index_to_num o wordsSyntax.dest_word_type;

(*****************************************************************************)
(* Test if a type can be represented in Verilog.                             *)
(* Currently this means the type is ``:word<n>``, ``:num`` or ``:bool``      *)
(*****************************************************************************)

fun is_supported_type ty =
 is_word_type ty orelse (ty = ``:num``) orelse (ty = ``:bool``);

(*****************************************************************************)
(* ``:wordn`` --> "n-1" (e.g. ``:word32`` --> "31")                          *)
(* ``:num``   --> 31                                                         *)
(* ``:bool``  --> "0"                                                        *)
(*****************************************************************************)

fun ty2size ty =
 let val n =
      if (ty = ``:bool``) then 1
      else if (ty = ``:num``) then
        32
      else if is_word_type ty then
        dest_word_type ty handle _ => 32
      else raise ERR "ty2size" "unsupported type"
 in
  Int.toString(n-1)
 end;

(*****************************************************************************)
(* ``v : num -> wordn`` --> "n-1" (e.g. ``v:word32`` --> "31")               *)
(* ``v : num -> num``   --> 31    (warning issued if !numWarning is true)    *)
(* ``v : num -> bool``  --> "0"                                              *)
(*****************************************************************************)

val numWarning = ref true;
fun var2size tm =
 let val (str, [_,ty]) = dest_type(type_of tm)
     val _ = if ((ty = ``:num``) orelse
                 (is_word_type ty andalso not (null (type_vars_in_term tm))))
                andalso (!numWarning)
              then
               (print "Warning: type of ";
                print_term tm ;
                print " is ``";
                print_type ty;
                print "``, but is compiled to [31:0].\n")
              else ()
 in
  ty2size ty
 end;


(*****************************************************************************)
(* ``:ty1 --> ty2`` --> (``:ty1``,``:ty2``)                                  *)
(*****************************************************************************)

fun dest_unop_type uty =
 let val (opr, utyl) = dest_type uty
     val _ = if opr = "fun"
              then ()
              else(print_type uty;
                   print "\nis not a function type\n";
                   raise ERR "dest_unop_type" "not a function type")
     val [argty,resty] = utyl
 in
  (argty,resty)
 end

(*****************************************************************************)
(* ``:ty1 # ty2 --> ty3`` --> (``:ty1``,``:ty2``,``:ty3``)                   *)
(*****************************************************************************)

fun dest_binop_type bty =
 let val (opr, btyl) = dest_type bty
     val _ = if opr = "fun"
              then ()
              else(print_type bty;
                   print "\nis not a function type\n";
                   raise ERR "dest_binop_type" "not a function type")
     val [argsty,resty] = btyl
     val (opr, argstyl) = dest_type argsty
     val _ = if opr = "prod"
              then ()
              else(print_type argsty;
                   print "\nis not a product type\n";
                   raise ERR "dest_binop_type" "not a product type")
     val [argty1,argty2] = argstyl
 in
  (argty1,argty2,resty)
 end

(*****************************************************************************)
(* Non-primitive components                                                  *)
(*****************************************************************************)

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
  (spec_tm, (clk_tm,load_tm,inpl,done_tm,outl), vars, tml)
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


(*****************************************************************************)
(*  ``DTYPE c (clk,inp,out)``     --> ``DTYPE c (clk,inp,out)``              *)
(*  ``?v. DTYPE v (clk,inp,out)`` --> ``DTYPE c (clk,inp,out)``              *)
(*****************************************************************************)
fun dest_DTYPE tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "DTYPE")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then tm else
 if is_exists tm
  then dest_DTYPE(snd(strip_exists tm))
  else raise ERR "dest_DTYPE" "bad arg"

val is_DTYPE = can dest_DTYPE;


(*****************************************************************************)
(* Test a term has the form ``CONSTANT c out``,                              *)
(* where c is 0 or T, F or NUMERAL n or n2w n                                *)
(*****************************************************************************)
fun is_CONSTANT tm =
 is_comb tm
  andalso is_const(fst(strip_comb tm))
  andalso (fst(dest_const(fst(strip_comb tm))) = "CONSTANT")
  andalso ((rand(rator tm) ~~ ``0``)
           orelse Feq (rand(rator tm))
           orelse Teq (rand(rator tm))
           orelse is_comb(rand(rator tm))
                  andalso is_const(rator(rand(rator tm)))
                  andalso mem
                           (fst(dest_const(rator(rand(rator tm)))))
                           ["NUMERAL","n2w"])
  andalso is_var (rand tm);

(*****************************************************************************)
(* ``CONSTANT c out`` --> ("c", ``out``) where c is Verilog form of c        *)
(*****************************************************************************)
fun dest_CONSTANT tm =
 let val num = rand(rator tm)
     val n = if Feq num then ``0``
             else if Teq num then ``1``
             else if num ~~ ``0`` orelse (fst(dest_const(rator num)) = "NUMERAL")
             then num
             else rand num
  in
   (Arbnum.toString(numSyntax.dest_numeral n), rand tm)
  end;


(*****************************************************************************)
(* ``COMB f (i1<>...<>im,out1<>...<>outn)``                                  *)
(* -->                                                                       *)
(* (f, ["i1",...,"im"], ["out1",...,"outn"])                                 *)
(*****************************************************************************)
fun dest_COMB tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "COMB")
     andalso (length(strip_prod(hd(fst(strip_fun(type_of(rand(rator tm)))))))
              = length(strip_BUS_CONCAT(fst(dest_pair(rand tm)))))
 then (rand(rator tm),
       map var_name (strip_BUS_CONCAT(fst(dest_pair(rand tm)))),
       map var_name (strip_BUS_CONCAT(snd(dest_pair(rand tm)))))
 else (print "dest_COMB fails on: \n";
       print_term tm; print "\n";
       raise ERR "dest_COMB" "bad argument");

val is_COMB = can dest_COMB;

(*****************************************************************************)
(* Library associating HOL terms with ML functions for generating            *)
(* combinational Verilog. Typical example:                                   *)
(*                                                                           *)
(*  add_vsynth                                                               *)
(*   [(``\(in1,in2). in1 >> in2``,                                           *)
(*     (fn[i1,i2] => ("{{31{" ^ i1 ^ "[31]}}," ^ i1 ^ "} >> " ^i2))),        *)
(*    (``UNCURRY $>>``,                                                      *)
(*     (fn[i1,i2] => ("{{31{" ^ i1 ^ "[31]}}," ^ i1 ^ "} >> " ^i2)))]        *)
(*                                                                           *)
(* which will cause both                                                     *)
(*                                                                           *)
(*  ``COMB (\(in1,in2). in1 >> in2) (x<>y, z)``                              *)
(*                                                                           *)
(* and                                                                       *)
(*                                                                           *)
(*  ``COMB (UNCURRY $>>) (x<>y, z)``                                         *)
(*                                                                           *)
(* to generate the Verilog statement                                         *)
(*                                                                           *)
(*  assign z = {{31{x[31]}},x} >> y;                                         *)
(*****************************************************************************)
val vsynth_lib = ref([] : (term * (string list -> string)) list);

(*****************************************************************************)
(* Add a list of entries to front of vsynth_lib                              *)
(*****************************************************************************)
fun add_vsynth pl = (vsynth_lib := pl @ (!vsynth_lib));

(*****************************************************************************)
(* Lookup in vsynth_lib                                                      *)
(*****************************************************************************)
fun lookup_vsynth_lib [] tm =
     raise ERR "lookup_vsynth" "not in vsynth_lib"
 |  lookup_vsynth_lib ((t, f : string list -> string)::vl) tm =
     if aconv t tm then f else lookup_vsynth_lib vl tm;

fun lookup_vsynth tm = lookup_vsynth_lib (!vsynth_lib) tm;


(*****************************************************************************)
(* Useful initial vsynth_lib                                                 *)
(*****************************************************************************)
val _ =
 add_vsynth
  [(``$~``,
    fn[i] => ("~ " ^ i)),
   (``UNCURRY $/\``,
    fn[i1,i2] => (i1 ^ " && " ^ i2)),
   (``UNCURRY $\/``,
    fn[i1,i2] => (i1 ^ " || " ^ i2)),
   (``\(sel:bool,in1:bool,in2:bool). if sel then in1 else in2``,
    fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3)),
   (``\(sel:bool,in1:num,in2:num). if sel then in1 else in2``,
    fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))
  ];


(******************************************************************************
Needed for crypto examples
add_vsynth
   [(``\(in1,in2). in1 >> in2``,
     (fn[i1,i2] => ("{{31{" ^ i1 ^ "[31]}}," ^ i1 ^ "} >> " ^i2))),
    (``UNCURRY $>>``,
     (fn[i1,i2] => ("{{31{" ^ i1 ^ "[31]}}," ^ i1 ^ "} >> " ^i2)))];
******************************************************************************)

(*****************************************************************************)
(* Positive edge triggered Dtype register.                                   *)
(* Default: 32-bits wide, initial value = 1.                                 *)
(*****************************************************************************)
val DTYPEvDef =
"// Variable width edge triggered Dtype register (default initial value 1)\n\
\// DTYPE v (clk,d,q) = (q 0 = v) /\\\
\ !t. q(t+1) = if Rise clk t then d t else q t\n\n\
\module dtype (clk,d,q);\n\
\ parameter size = 31;\n\
\ parameter value = 1;\n\
\ input clk;\n\
\ input  [size:0] d;\n\
\ output [size:0] q;\n\
\ reg    [size:0] q = value;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Print an instance of a Dtype with a given size and default initial value  *)
(*****************************************************************************)
val DTYPEvInst_count = ref 0;
fun DTYPEvInst tm (out:string->unit) [("size",size)] [clk_name,in_name,out_name] =
 let val count = !DTYPEvInst_count
     val _ = (DTYPEvInst_count := count+1);
     val inst_name = "dtype" ^ "_" ^ Int.toString count
 in
 (out "/*\n";
  out(term2string tm); out "\n*/\n";
  out "dtype   "; out inst_name;
  out " (";out clk_name;out",";out in_name;out",";out out_name; out ");";
  out "   defparam ";out inst_name; out ".size = "; out size;
  out ";\n\n")
 end;

fun termToVerilog_DTYPE (out:string->unit) tm =
 let val dest_tm = dest_DTYPE tm
 in
  DTYPEvInst
   tm
   out
   [("size", var2size(last(strip_pair(rand dest_tm))))]
   (map (fst o dest_var) (strip_pair(rand dest_tm)))
  end;


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
  out " (";out clk_name; out ");";
  out "   defparam ";out inst_name; out ".period = "; out period;
  out ";\n\n")
 end;

(*****************************************************************************)
(* Add a binary operator (gives compatibility with old code)                 *)
(*****************************************************************************)
fun AddBinop (_:string, (hbinop,vbinop)) =
 add_vsynth[(hbinop, fn[i1,i2] => (i1 ^ " " ^ vbinop ^ " " ^ i2))];


(*****************************************************************************)
(* Generate Verilog statement to implement a component                       *)
(*                                                                           *)
(*  ``DTYPE T (clk,inp,out)``     --> dtype dtype_<n> (clk,inp,out)          *)
(*  ``?v. DTYPE v (clk,inp,out)`` --> dtype dtype_<n> (clk,inp,out)          *)
(*  ``CONSTANT v out``            --> assign out = v;                        *)
(*  ``COMB f (i1<>...<>in,out)``  --> call generate_verilog ``f``            *)
(*****************************************************************************)
fun MAKE_COMPONENT_VERILOG (out:string->unit) tm =
 if is_DTYPE tm
  then termToVerilog_DTYPE (out:string->unit) tm else
 if is_CONSTANT tm
  then
   let val (c, out_var) = dest_CONSTANT tm
       val out_name = var_name out_var
   in
    (out "/*\n"; out(term2string tm); out "\n*/\n";
     out "assign "; out out_name; out " = "; out c; out ";\n\n")
   end else
 if is_COMB tm
  then
   let val (f, in_names, out_names) = dest_COMB tm
       val ml_fun = (lookup_vsynth f
                      handle e => (print_term f;
                                   print "\n"; print "not in vsynth_lib\n";
                                   raise e))
       val vstring = (ml_fun in_names
                      handle e => (print "ML function associated in vsynth_lib with:\n";
                                   print_term f; print "\nfails on\n";
                                   print_term(fst(dest_pair(rand tm))); print "\n";
                                   raise e))
   in
    (out "/*\n"; out(term2string tm); out "\n*/\n";
     out "assign ";
     if null(tl out_names)
      then out(hd out_names)
      else (out "{";
            out(hd out_names);
            map (fn s => (out ","; out s)) (tl out_names);
            out "}");
     out " = "; out vstring; out ";\n\n")
   end
   else (print "Can't generate Verilog for:\n";
         print_term tm; print "\n";
         raise ERR "MAKE_COMPONENT_VERILOG" "bad component term");


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
** creates a module called name with header:
**
**  module name (clk,load,inp1,...,inpu,done,out1,...,outv);
**   input  clk,load;
**   input  [<size>:0] inp1,inp2;
**   output done;
**   output [<size>:0] out;
**   wire   clk,done;
**
** where <size> is the appropriate width computed from the types.
** Body generated using MAKE_COMPONENT_VERILOG.
*)


(* New version that generates behavioral Verilog for combinational logic *)
fun MAKE_VERILOG name thm out =
 let val (spec_tm,
          (clk, load_tm,inpl,done_tm,outl),
          wire_vars,
          modules) = dest_cir thm
     val clk_name = var_name clk
     val load_name = var_name load_tm
     val inp_names = map var_name inpl
     val done_name = var_name done_tm
     val out_names = map var_name outl
     val module_args =
          [clk_name,load_name] @ inp_names @ [done_name] @ out_names
 in
 (out("// This file defines module " ^ name ^ " [Created: " ^ date() ^ "]\n\n");
  out("// Definition of Dtype register component\n\n");
  out DTYPEvDef;
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
   wire_vars;
  out "\n";
  map (MAKE_COMPONENT_VERILOG out) modules;
  out"endmodule\n\n")
 end;


(* Example for testing
val out      = print
and clk_name = "clk"
and load_name = "load"
and done_name = "done"
and stimulus  = [("inp1", "5"),("inp2","7")];
*)

(*****************************************************************************)
(* Print test bench stimulus in Verilog                                      *)
(*****************************************************************************)
fun printStimulus (out:string->unit) clk_name load_name done_name stimulus =
 (out(" always @(posedge " ^ clk_name ^") if (" ^ done_name ^ ")\n");
  out("                        begin\n");
  out("                         #1 " ^ load_name ^ " = 1;\n");
  out("                         #1 ");
  map
   (fn (inname,inval) => out(inname ^ " = " ^ inval ^ "; "))
   stimulus;
  out("\n");
  out("                         forever @(posedge " ^ clk_name ^ ") if (" ^ done_name ^ ") $finish;\n");
  out("                        end\n"));


(* Example for testing
val period  = 5
and file_name = "foo"
and thm = Adder_cir
and stimulus =[("inp1", "5"),("inp2","7")]
and name = "Adder"
and dump_all = true;

printToFile "Foo.vl" (MAKE_SIMULATION period thm stimulus name);
*)


fun MAKE_SIMULATION name thm period stimulus dump_all out =
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
  out(" wire " ^ clk_name ^ ";\n");
  out(" reg  " ^ load_name ^ ";\n");
  map
   (fn v => out(" reg  [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n"))
   inpl;
  out(" wire " ^ done_name ^ ";\n");
  map
   (fn v => out(" wire [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n"))
   outl;
  out "\n";
  out(" initial\n  begin\n   $dumpfile(\"" ^name ^ ".vcd\");\n");
  (if dump_all
    then out("   $dumpvars(1, " ^ name ^ ");\n")
    else
     (out("   $dumpvars(1,");
      map out (add_commas module_args);
      out ");\n"));
  out"  end\n\n";
  out(" initial " ^ load_name ^ " = 0;\n\n");
  printStimulus out clk_name load_name done_name stimulus;
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

(*****************************************************************************)
(* Flag (default false) to determine if all variables are dumped,            *)
(* or just the top level ones.                                               *)
(*****************************************************************************)
val dump_all_flag = ref false;

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
**  period stimulus (!dump_all_flag)
**
** Prints translation to Verilog and a stimulus to a file Spec.vl and creates
** a module Main that invokes module Spec connected to a simulation environment
** described by stimulus. If
** (fails if Spec isn't a constant)
*)

fun PRINT_SIMULATION thm period stimulus =
 let val name = fst(dest_const(#1(dest_cir thm)))
 in
  printToFile
   (name ^ ".vl")
   (MAKE_SIMULATION name thm period stimulus (!dump_all_flag))
 end;

(*****************************************************************************)
(* User resettable paths of Verilog simulator and waveform viewer            *)
(*****************************************************************************)

val iverilog_path   = ref "/usr/bin/iverilog";
val vvp_path        = ref "/usr/bin/vvp";
val gtkwave_path    = ref "/usr/bin/gtkwave -a";

(*
val cver_path       = ref "./gplcver-2.10c.linux.bin/bin/cver";
val dinotrace_path  = ref "./gplcver-2.10c.linux.bin/bin/dinotrace";
*)
val cver_path       = ref "/Users/konradslind/Desktop/gplcver-2.10c.osx.bin/bin/cver";
val dinotrace_path  = ref "/Users/konradslind/Desktop/gplcver-2.10c.osx.bin/bin/dinotrace";

val vlogger_path    = ref "/usr/bin/vlogcmd";

(*
** Test for success of the result of Process.system
** N.B. isSuccess was expected to primitive in next release of
** Moscow ML, and Process.status will then lose eqtype status
** (not happened yet apparently)
*)

val isSuccess = Process.isSuccess;

(*****************************************************************************)
(* Run iverilog on name.vl                                                   *)
(*****************************************************************************)
fun iverilog name =
 let val vvp_file = (name ^ ".vvp")
     val iverilog_command = ((!iverilog_path) ^ " -o " ^ vvp_file
                             ^ " " ^ name ^ ".vl")
     val code1 = Process.system iverilog_command
     val _ = if isSuccess code1
              then print(iverilog_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ iverilog_command ^ "\n")
     val vvp_command = ((!vvp_path) ^ " " ^ vvp_file)
     val code2 = Process.system vvp_command
     val _ = if isSuccess code2
              then print(vvp_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ vvp_command ^ "\n")
 in
  ()
 end;

(*****************************************************************************)
(* Run cver on name.vl                                                       *)
(*****************************************************************************)
fun cver name =
 let val cver_command = ((!cver_path) ^ " " ^ name ^ ".vl")
     val code = Process.system cver_command
     val _ = if isSuccess code
              then print(cver_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ cver_command ^ "\n")
 in
  ()
 end;

(*****************************************************************************)
(* Run gtkwave on name.vcd                                                   *)
(*****************************************************************************)
fun gtkwave name =
 let val vcd_file = (name ^ ".vcd")
     val gtkwave_command = ((!gtkwave_path) ^ " " ^ vcd_file ^ "&")
     val code = Process.system gtkwave_command
     val _ = if isSuccess code
              then print(gtkwave_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ gtkwave_command ^ "\n")
 in
  ()
 end;

(*****************************************************************************)
(* Run vlogger on name.vl                                                    *)
(*****************************************************************************)
fun vlogger name =
 let val vlogger_command = ((!vlogger_path) ^ " " ^ name ^ ".vl")
     val code = Process.system vlogger_command
     val _ = if isSuccess code
              then print(vlogger_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ vlogger_command ^ "\n")
 in
  ()
 end;

(*****************************************************************************)
(* Run dinotrace on name.vcd                                                 *)
(*****************************************************************************)
fun dinotrace name =
 let val vcd_file = (name ^ ".vcd")
     val dinotrace_command = ((!dinotrace_path) ^ " " ^ vcd_file ^ "&")
     val code = Process.system dinotrace_command
     val _ = if isSuccess code
              then print(dinotrace_command ^ "\n")
              else print
                    ("Warning:\n Process.system reports failure signal returned by\n "
                     ^ dinotrace_command ^ "\n")
 in
  ()
 end;

(*
val verilog_simulator = ref iverilog;
val waveform_viewer   = ref gtkwave;
*)

val verilog_simulator = ref cver;
val waveform_viewer   = ref dinotrace;

(* Example for testing
use "Ex3.ml";

val thm    = DoubleDouble_cir
and inputs = [("inp", "5")];
*)

(*****************************************************************************)
(* Default values for simulation                                             *)
(*****************************************************************************)

val period_default   = ref 5;

fun SIMULATE thm stimulus =
 let val _ = PRINT_SIMULATION thm (!period_default) stimulus
     val name = fst(dest_const(#1(dest_cir thm)))
     val _ = (!verilog_simulator) name
     val _ = (!waveform_viewer) name
 in
  ()
 end;

end (* local open *)

end (* vsynth *)
