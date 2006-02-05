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
val ERR = mk_HOL_ERR "vsynth";

(*****************************************************************************)
(* Date and time                                                             *)
(*****************************************************************************)
fun date() = Date.fmt "%c" (Date.fromTimeLocal (Time.now ()));

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
fun is_word_type wty =
 let val (opr, tyargs) = dest_type wty
     val oprl = explode opr
 in
  (tyargs = []      andalso
   length oprl > 4  andalso
   el 1 oprl = #"w" andalso
   el 2 oprl = #"o" andalso
   el 3 oprl = #"r" andalso
   el 4 oprl = #"d" andalso
   (case Int.fromString(implode(tl(tl(tl(tl oprl))))) of
       SOME _ => true
     | NONE   => false))
 end;

(*****************************************************************************)
(* Extraxt <n> from ``:word<n>``                                             *)
(*****************************************************************************)
fun dest_word_type wty =
 let val (opr, tyargs) = dest_type wty
     val oprl = explode opr
 in
  string2int(implode(tl(tl(tl(tl oprl)))))
 end;

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
       else if (ty = ``:num``)
       then 32
       else if  is_word_type ty
       then dest_word_type ty
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
 let val ("fun", [_,ty]) = dest_type(type_of tm)
     val _ = if (ty = ``:num``) andalso (!numWarning)
              then 
               (print "Warning: type of ";
                print_term tm ;
                print " is ``:num``, but is compiled to [31:0].\n")
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
(* Library of modules with Verilog models                                    *)
(*****************************************************************************)
val module_lib = ref ([]:(string * string) list);

fun add_modules name_vdef_list = 
 module_lib := (!module_lib) @ name_vdef_list;

(*****************************************************************************)
(* Library of functions for printing terms to Verilog.                       *)
(* For debugging, each function is paired with a string descriptor           *)
(*****************************************************************************)
val termToVerilog_lib = 
 ref([]:(string * ((string -> unit) -> term -> unit)) list);

fun add_termToVerilog fl =
 (termToVerilog_lib := (!termToVerilog_lib) @ fl);

(*****************************************************************************)
(* Function for generating Verilog module definitions,                       *)
(* e.g. UnopVlogDef "NOT32" (``$~``, "~") generates                          *)
(*                                                                           *)
(* // Verilog module implementing HOL unary operator                         *)
(* // $~ :bool -> bool                                                       *)
(* //                                                                        *)
(* // Automatically generated definition of NOT32                            *)
(* module NOT32 (inp,out);                                                   *)
(*  parameter inpsize = 31;                                                  *)
(*  parameter outsize = 31;                                                  *)
(*  input   [inpsize:0] inp;                                                 *)
(*  output  [outsize:0] out;                                                 *)
(*                                                                           *)
(*  assign out = ~ inp;                                                      *)
(*                                                                           *)
(* endmodule                                                                 *)
(*****************************************************************************)
fun UnopVlogDef name (hunop,vunop) =
 let val (argty,resty) = dest_unop_type(type_of hunop)
     val argsize = ty2size argty
     val ressize = ty2size resty
 in
 ("// Verilog module implementing HOL unary operator\n// " ^
  term2string hunop ^ " " ^
  Parse.type_to_string(type_of hunop) ^ "\n//\n" ^ 
  "// Automatically generated definition of " ^ name ^ "\n\
   \module " ^ name ^ " (inp,out);\n\
   \ parameter inpsize = " ^ argsize ^ ";\n\
   \ parameter outsize = " ^ ressize ^ ";\n\
   \ input   [inpsize:0] inp;\n\
   \ output  [outsize:0] out;\n\
   \\n\
   \ assign out = " ^ vunop ^ " inp;\n\
   \\n\
   \endmodule\n\
   \\n")
 end;

(*****************************************************************************)
(* Function for generating instances. The first evaluation of:               *)
(*                                                                           *)
(*  UnopVlogInstFun "NOT32"                                                  *)
(*   ``NOT32(inp,out)`` print [("inp","32"),("out","32")]                    *)
(*                                                                           *)
(* generates                                                                 *)
(*                                                                           *)
(*  /* NOT32 (inp,out) */                                                    *)
(*  NOT32        NOT32_0 (inp,out);                                          *)
(*    defparam NOT32_0.inpsize = 32;                                         *)
(*    defparam NOT32_0.outsize = 32;                                         *)
(*                                                                           *)
(* Subsequent evaluations inc the instance counter (NOT32_1, NOT32_2 etc)    *)
(*                                                                           *)
(*****************************************************************************)
fun UnopVlogInstFun name =
 let val instcount = ref 0
     fun InstFn 
          tm
          (out:string->unit)
          [(argname,argsize),(outname,outsize)] =
      let val count = !instcount
          val _ = (instcount := count+1)
          val inst_name = name ^ "_" ^ Int.toString count
      in
        (out " /* ";
         out(term2string tm); out " */\n";
         out(" " ^ name ^ "        "); out inst_name;
         out " (";out argname;out",";out outname; out ");\n";
         out "   defparam ";out inst_name; out ".inpsize = "; out argsize; out ";\n";
         out "   defparam ";out inst_name; out ".outsize = "; out outsize; out ";\n";
         out "\n")
      end
 in     
  InstFn
 end;

(*****************************************************************************)
(* Test if a term has the form ``name(v1,v2)`` where name is a constant      *)
(* and v1, v2 are variables.                                                 *)
(*****************************************************************************)
fun is_unop name tm =
 is_comb tm
  andalso is_const(fst(strip_comb tm))
  andalso (fst(dest_const(fst(strip_comb tm))) = name)
  andalso is_pair(rand tm)
  andalso (length(strip_pair(rand tm)) = 2)
  andalso all is_var (strip_pair(rand tm));

(*****************************************************************************)
(* Invoke an instance of BinopVlogInstFun on a unop term                     *)
(*****************************************************************************)
fun UnopTermToVerilog nameVlogInstFun name (out:string->unit) tm =
 if is_unop name tm
  then nameVlogInstFun
        tm
        out
        (map (fn v => (fst(dest_var v), var2size v)) (strip_pair(rand tm)))
  else raise ERR "UnopTermToVerilog" "bad component term";

(*****************************************************************************)
(* Evaluating                                                                *)
(*                                                                           *)
(*  AddUnop                                                                  *)
(*   ("component name", (``function``, "corresponding Verilog operator"))    *)
(*                                                                           *)
(* defines a HOL component and a corresponding Verilog module and            *)
(* adds these to the synthesis engine.                                       *)
(*****************************************************************************)
fun AddUnop(name, (hunop,vunop)) =
 let val _ = if is_constant name
               then (print "Warning: "; print name;
                     print " is the name of an existing constant\n")
               else ()
     val uty = type_of hunop
     val (argty,resty) = dest_unop_type uty
     val _ = if not(is_supported_type argty)
              then (print "type of argument: ";print_type argty; 
                    print " doesn't correspond to a Verilog type\n";
                    raise ERR "AddUnop" "arg1 not a Verilog type")
              else ()
     val _ = if not(is_supported_type resty)
              then (print "type of result: ";print_type resty; 
                    print " doesn't correspond to a Verilog type\n";
                    raise ERR "AddUnop" "result not a Verilog type")
              else ()
     val namevar = mk_var(name,``:(num->^argty)#(num->^resty)->bool``)
     val deftm = ``^namevar(inp,out) = !t:num. out t = ^hunop(inp t)``
     val defth = Define `^deftm`
     val deflhs = lhs(concl(SPEC_ALL defth))
     val combtm = ``COMB ^hunop (inp, out) = ^deflhs``
     val combth = prove
                   (combtm,
                    RW_TAC bool_ss [COMB_def,BUS_CONCAT_def,defth])
     val namecon  = fst(strip_comb deflhs)
     val attm = ``^deflhs ==> ^namecon(inp at clk, out at clk)``
     val atth = prove
                 (attm,
                  RW_TAC bool_ss [defth,at_def,tempabsTheory.when,o_THM])
     val argsize = ty2size argty
     val ressize = ty2size resty
     val nameVlogDef = UnopVlogDef name (hunop,vunop)
     val nameVlogInstFun = UnopVlogInstFun name
     val nameTermToVerilog = UnopTermToVerilog nameVlogInstFun name
 in
  (add_combinational_components[combth];
   add_temporal_abstractions[atth];
   add_modules[(name, nameVlogDef)];
   add_termToVerilog[("Unop",nameTermToVerilog)])
 end;

(*****************************************************************************)
(* Function for generating Verilog module definitions,                       *)
(* e.g. BinopVlogDef "XOR32" (``UNCURRY $#``, "^") generates                 *)
(*                                                                           *)
(* // Verilog module implementing HOL binary operator                        *)
(* // UNCURRY $# :word32 # word32 -> word32                                  *)
(* //                                                                        *)
(* // Automatically generated definition of XOR32                            *)
(* module XOR32 (in1,in2,out);                                               *)
(*  parameter in1size = 31;                                                  *)
(*  parameter in2size = 31;                                                  *)
(*  parameter outsize = 31;                                                  *)
(*  input   [in1size:0] in1;                                                 *)
(*  input   [in2size:0] in2;                                                 *)
(*  output  [outsize:0] out;                                                 *)
(*                                                                           *)
(*  assign out = in1 ^ in2;                                                  *)
(*                                                                           *)
(* endmodule                                                                 *)
(*                                                                           *)
(*****************************************************************************)
fun BinopVlogDef name (hbinop,vbinop) =
 let val (arg1ty,arg2ty,resty) = dest_binop_type(type_of hbinop)
     val arg1size = ty2size arg1ty
     val arg2size = ty2size arg2ty
     val ressize = ty2size resty
 in
 ("// Verilog module implementing HOL binary operator\n// " ^
  term2string hbinop ^ " " ^
  Parse.type_to_string(type_of hbinop) ^ "\n//\n" ^ 
  "// Automatically generated definition of " ^ name ^ "\n\
   \module " ^ name ^ " (in1,in2,out);\n\
   \ parameter in1size = " ^ arg1size ^ ";\n\
   \ parameter in2size = " ^ arg2size ^ ";\n\
   \ parameter outsize = " ^ ressize ^ ";\n\
   \ input   [in1size:0] in1;\n\
   \ input   [in2size:0] in2;\n\
   \ output  [outsize:0] out;\n\
   \\n\
   \ assign out = in1 " ^ vbinop ^ " in2;\n\
   \\n\
   \endmodule\n\
   \\n")
 end;

(*****************************************************************************)
(* Function for generating instances. The first evaluation of:               *)
(*                                                                           *)
(*   BinopVlogInstFun "XOR32"                                                *)
(*    ``XOR32 (in1,in2,out)`` print [("in1","32"),("in2","32"),("out","32")] *)
(*                                                                           *)
(* generates                                                                 *)
(*                                                                           *)
(*  /* XOR32 (in1,in2,out) */                                                *)
(*  XOR32        XOR32_0 (in1,in2,out);                                      *)
(*    defparam XOR32_0.in1size = 32;                                         *)
(*    defparam XOR32_0.in2size = 32;                                         *)
(*    defparam XOR32_0.outsize = 32;                                         *)
(*                                                                           *)
(* Subsequent evaluations inc the instance counter (XOR32_1, XOR32_2 etc)    *)
(*                                                                           *)
(*****************************************************************************)
fun BinopVlogInstFun name =
 let val instcount = ref 0
     fun InstFn 
          tm
          (out:string->unit)
          [(arg1name,arg1size),(arg2name,arg2size),(outname,outsize)] =
      let val count = !instcount
          val _ = (instcount := count+1)
          val inst_name = name ^ "_" ^ Int.toString count
      in
        (out " /* ";
         out(term2string tm); out " */\n";
         out(" " ^ name ^ "        "); out inst_name;
         out " (";out arg1name;out",";out arg2name;out",";out outname; out ");\n";
         out "   defparam ";out inst_name; out ".in1size = "; out arg1size; out ";\n";
         out "   defparam ";out inst_name; out ".in2size = "; out arg2size; out ";\n";
         out "   defparam ";out inst_name; out ".outsize = "; out outsize; out ";\n";
         out "\n")
      end
 in     
  InstFn
 end;

(*****************************************************************************)
(* Test if a term has the form ``name(v1,v2,v3)`` where name is a constant   *)
(* and v1, v2  and v3are variables.                                          *)
(*****************************************************************************)
fun is_binop name tm =
 is_comb tm
  andalso is_const(fst(strip_comb tm))
  andalso (fst(dest_const(fst(strip_comb tm))) = name)
  andalso is_pair(rand tm)
  andalso (length(strip_pair(rand tm)) = 3)
  andalso all is_var (strip_pair(rand tm));

(*****************************************************************************)
(* Invoke an instance of BinopVlogInstFun on a binop term                    *)
(*****************************************************************************)
fun BinopTermToVerilog nameVlogInstFun name (out:string->unit) tm =
 if is_binop name tm
  then nameVlogInstFun
        tm
        out
        (map (fn v => (fst(dest_var v), var2size v)) (strip_pair(rand tm)))
  else raise ERR "BinopTermToVerilog" "bad component term";

(*****************************************************************************)
(* Evaluating                                                                *)
(*                                                                           *)
(*  AddBinop                                                                 *)
(*   ("component name",                                                      *)
(*    (``uncurried binary function``, "corresponding Verilog operator"))     *)
(*                                                                           *)
(* defines a HOL component and a corresponding Verilog module and            *)
(* adds these to the synthesis engine.                                       *)
(*****************************************************************************)
fun AddBinop(name, (hbinop,vbinop)) =
 let val _ = if is_constant name
               then (print "Warning: "; print name;
                     print " is the name of an existing constant\n")
               else ()
     val bty = type_of hbinop
     val (arg1ty,arg2ty,resty) = dest_binop_type bty
     val _ = if not(is_supported_type arg1ty)
              then (print "type of first argument: ";print_type arg1ty; 
                    print " doesn't correspond to a Verilog type\n";
                    raise ERR "AddBinop" "arg1 not a Verilog type")
              else ()
     val _ = if not(is_supported_type arg2ty)
              then (print "type of second argument: ";print_type arg2ty; 
                    print " doesn't correspond to a Verilog type\n";
                    raise ERR "AddBinop" "arg2 not a Verilog type")
              else ()
     val _ = if not(is_supported_type resty)
              then (print "type of result: ";print_type resty; 
                    print " doesn't correspond to a Verilog type\n";
                    raise ERR "AddBinop" "result not a Verilog type")
              else ()
     val namevar = mk_var
                    (name,
                     ``:(num->^arg1ty)#(num->^arg2ty)#(num->^resty)->bool``)
     val deftm = ``^namevar(in1,in2,out) = 
                   !t:num. out t = ^hbinop((in1 t), (in2 t))``
     val defth = Define `^deftm`
     val deflhs = lhs(concl(SPEC_ALL defth))
     val combtm = ``COMB ^hbinop (in1 <> in2, out) = ^deflhs``
     val combth = prove
                   (combtm,
                    RW_TAC bool_ss [COMB_def,BUS_CONCAT_def,defth])
     val namecon  = fst(strip_comb deflhs)
     val attm = ``^deflhs ==> ^namecon(in1 at clk, in2 at clk, out at clk)``
     val atth = prove
                 (attm,
                  RW_TAC bool_ss [defth,at_def,tempabsTheory.when,o_THM])
     val arg1size = ty2size arg1ty
     val arg2size = ty2size arg1ty
     val ressize  = ty2size resty
     val nameVlogDef = BinopVlogDef name (hbinop,vbinop)
     val nameVlogInstFun = BinopVlogInstFun name
     val nameTermToVerilog = BinopTermToVerilog nameVlogInstFun name
 in
  (add_combinational_components[combth];
   add_temporal_abstractions[atth];
   add_modules[(name, nameVlogDef)];
   add_termToVerilog[("Binop",nameTermToVerilog)])
 end;


(*****************************************************************************)
(* Each kind of module M generates an instance M_n, where n starts at 0 and  *)
(* is increased each time a new instance is created.                         *)
(* A reference variable MvInst_count holds the current value of n.           *)
(*****************************************************************************)

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
(* Print an instance of an CONSTANT with a given size and value              *)
(*****************************************************************************)
val CONSTANTvInst_count = ref 0;
fun CONSTANTvInst 
 tm
 (out:string->unit) [("size",size),("value",value)] [out_name] =
 let val count = !CONSTANTvInst_count
     val _ = (CONSTANTvInst_count := count+1);
     val inst_name = "CONSTANT" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " CONSTANT   "; out inst_name;
  out " (";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size  = "; out size; out ";";
  out "\n";
  out "   defparam ";out inst_name; out ".value = "; out value; 
  out ";\n\n")
 end;

(*****************************************************************************)
(* Code below is fairly gross because it needs to deal with numerals         *)
(* of type `:num`` and of type ``:word<n>``.                                 *)
(*****************************************************************************)
fun termToVerilog_CONSTANT (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "CONSTANT")
     andalso ((rand(rator tm) = ``0``)
              orelse is_comb(rand(rator tm))
                     andalso is_const(rator(rand(rator tm)))
                     andalso mem 
                              (fst(dest_const(rator(rand(rator tm))))) 
                              ["NUMERAL","n2w"])
     andalso is_var (rand tm)
  then CONSTANTvInst 
        tm
        out 
        [("size", var2size(last(strip_pair(rand tm)))),
         ("value",
          let val num = rand(rator tm)
              val n = 
               if (num = ``0``) orelse (fst(dest_const(rator num)) = "NUMERAL")
                then num
                else rand num
          in
           Arbnum.toString(numSyntax.dest_numeral n)
          end)]
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_CONSTANT" "bad component term";

val _ = add_termToVerilog[("CONSTANT",termToVerilog_CONSTANT)];
val _ = add_modules[("CONSTANT",CONSTANTvDef)];

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
  out " (";out clk_name; out ");\n";
  out "   defparam ";out inst_name; out ".period = "; out period; 
  out ";\n\n")
 end;

(*****************************************************************************)
(* Combinational boolean inverter                                            *)
(*****************************************************************************)
val NOTvDef= UnopVlogDef "devNOT" (``$~:bool->bool``,"!");
val _ = add_termToVerilog
         [("NOT",UnopTermToVerilog (UnopVlogInstFun "devNOT") "NOT")];
val _ = add_modules[("devNOT",NOTvDef)];

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
(* TRUEvInst out "output" prints, using out, and instance of TRUE driving    *)
(* a line named "output"                                                     *)
(*****************************************************************************)
val TRUEvInst_count = ref 0;
fun TRUEvInst tm (out:string->unit) [] [out_name] =
 let val count = !TRUEvInst_count
     val _ = (TRUEvInst_count := count+1);
     val inst_name = "TRUE" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " TRUE       "; out inst_name;
  out " (";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_TRUE (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "TRUE")
     andalso is_var(rand tm)
  then TRUEvInst tm out [] [fst(dest_var(rand tm))]
  else raise ERR "termToVerilog_TRUE" "bad component term";

val _ = add_termToVerilog[("TRUE",termToVerilog_TRUE)];
val _ = add_modules[("TRUE",TRUEvDef)];

(*****************************************************************************)
(* Combinational multiplexer. Default has 32-bits inputs and output          *)
(*****************************************************************************)
val MUXvDef =
"// Combinational multiplexer\n\
\module devMUX (sw,in1,in2,out);\n\
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
(* Print and instance of a MUX with a given size                             *)
(*****************************************************************************)
val MUXvInst_count = ref 0;
fun MUXvInst tm (out:string->unit) [("size",size)] 
     [sw_name,in1_name,in2_name,out_name] =
 let val count = !MUXvInst_count
     val _ = (MUXvInst_count := count+1);
     val inst_name = "devMUX" ^ "_" ^ Int.toString count
 in
 (out " /*\n ";
  out(term2string tm); out "\n */\n";
  out " devMUX        "; out inst_name;
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
        tm
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_MUX" "bad component term";

val _ = add_termToVerilog[("MUX",termToVerilog_MUX)];
val _ = add_modules[("devMUX",MUXvDef)];

(*****************************************************************************)
(* Combinational Boolean and-gate                                            *)
(*****************************************************************************)
val ANDvDef = BinopVlogDef "devAND" (``UNCURRY $/\ :bool#bool->bool``,"&&");
val _ = add_termToVerilog
         [("AND",BinopTermToVerilog (BinopVlogInstFun "devAND") "AND")];
val _ = add_modules[("devAND",ANDvDef)];

(*****************************************************************************)
(* Combinational Boolean or-gate                                             *)
(*****************************************************************************)
val ORvDef = BinopVlogDef "devOR" (``UNCURRY $\/ :bool#bool->bool``,"||");
val _ = add_termToVerilog
         [("OR",BinopTermToVerilog (BinopVlogInstFun "devOR") "OR")];
val _ = add_modules[("devOR",ORvDef)];

(*****************************************************************************)
(* Abstract delay element                                                    *)
(*****************************************************************************)
val DELvDef =
"// Abstract delay\n\
\module DEL (inp,out);\n\
\ parameter size = 31;\n\
\ input  [size:0] inp;\n\
\ output [size:0] out;\n\
\ reg    [size:0] out;\n\
\\n\
\ always  out = #1 inp;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Print an instance of an DEL with a given size                             *)
(*****************************************************************************)
val DELvInst_count = ref 0;
fun DELvInst tm (out:string->unit) [("size",size)] [inp_name,out_name] =
 let val count = !DELvInst_count
     val _ = (DELvInst_count := count+1);
     val inst_name = "DEL" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " DEL        "; out inst_name;
  out " (";out inp_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_DEL (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "DEL")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 2)
     andalso all is_var (strip_pair(rand tm))
  then DELvInst 
        tm
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_DEL" "bad component term";

val _ = add_termToVerilog[("DEL",termToVerilog_DEL)];
val _ = add_modules[("DEL",DELvDef)];

(*****************************************************************************)
(* Abstract edge-triggered clocked flipflop                                  *)
(*****************************************************************************)
val DFFvDef =
"// Abstract edge triggered flipflop\n\
\module DFF (d,clk,q);\n\
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
(* Print an instance of a DFF with a given size                              *)
(*****************************************************************************)
val DFFvInst_count = ref 0;
fun DFFvInst tm (out:string->unit) [("size",size)] [in_name,clk_name,out_name] =
 let val count = !DFFvInst_count
     val _ = (DFFvInst_count := count+1);
     val inst_name = "DFF" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " DFF      "; out inst_name;
  out " (";out in_name;out",";out clk_name;out",";out out_name; out ");\n";
  out "   defparam ";out inst_name; out ".size = "; out size; 
  out ";\n\n")
 end;

fun termToVerilog_DFF (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "DFF")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then DFFvInst 
        tm
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_DFF" "bad component term";

val _ = add_termToVerilog[("DFF",termToVerilog_DFF)];
val _ = add_modules[("DFF",DFFvDef)];

(*****************************************************************************)
(* Positive edge triggered Dtype register. Default is 32-bits wide.          *)
(*****************************************************************************)
val DtypevDef =
"// Positive edge triggered Dtype register\n\
\// Dtype(clk,d,q) = !t. q(t+1) = if Rise clk t then d t else q t\n\
\module Dtype (clk,d,q);\n\
\ parameter size = 31;\n\
\ input clk;\n\
\ input  [size:0] d;\n\
\ output [size:0] q;\n\
\ reg    [size:0] q = 0;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Print an instance of a Dtype with a given size                            *)
(*****************************************************************************)
val DtypevInst_count = ref 0;
fun DtypevInst tm (out:string->unit) [("size",size)] [clk_name,in_name,out_name] =
 let val count = !DtypevInst_count
     val _ = (DtypevInst_count := count+1);
     val inst_name = "Dtype" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " Dtype      "; out inst_name;
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
        tm
        out 
        [("size", var2size(last(strip_pair(rand tm))))] 
        (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_Dtype" "bad component term";

val _ = add_termToVerilog[("Dtype",termToVerilog_Dtype)];
val _ = add_modules[("Dtype",DtypevDef)];

(*****************************************************************************)
(* Boolean positive edge triggered flip-flop starting in state 1             *)
(*****************************************************************************)
val DtypeTvDef =
"// Boolean positive edge triggered flip-flop starting in state 1\n\
\// DtypeT(clk,d,q) = (q 0 = T) /\\ Dtype(clk,d,q)\n\
\module DtypeT (clk,d,q);\n\
\ input clk,d;\n\
\ output q;\n\
\ reg q = 1;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Print an instance of a DtypeT                                             *)
(*****************************************************************************)
val DtypeTvInst_count = ref 0;
fun DtypeTvInst tm (out:string->unit) [] [clk_name,in_name,out_name] =
 let val count = !DtypeTvInst_count
     val _ = (DtypeTvInst_count := count+1);
     val inst_name = "DtypeT" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " DtypeT        "; out inst_name;
  out " (";out clk_name;out",";out in_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_DtypeT (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "DtypeT")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then DtypeTvInst tm out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_DtypeT" "bad component term";

val _ = add_termToVerilog[("DtypeT",termToVerilog_DtypeT)];
val _ = add_modules[("DtypeT",DtypeTvDef)];

(*****************************************************************************)
(* Boolean positive edge triggered flip-flop starting in state 0             *)
(*****************************************************************************)
val DtypeFvDef =
"// Boolean positive edge triggered flip-flop starting in state 0\n\
\module DtypeF (clk,d,q);\n\
\ input clk,d;\n\
\ output q;\n\
\ reg q = 0;\n\
\\n\
\ always @(posedge clk) q <= d;\n\
\\n\
\endmodule\n\
\\n";

(*****************************************************************************)
(* Print an instance of a DtypeF                                             *)
(*****************************************************************************)
val DtypeFvInst_count = ref 0;
fun DtypeFvInst tm (out:string->unit) [] [clk_name,in_name,out_name] =
 let val count = !DtypeFvInst_count
     val _ = (DtypeFvInst_count := count+1);
     val inst_name = "DtypeF" ^ "_" ^ Int.toString count
 in
 (out " /* ";
  out(term2string tm); out " */\n";
  out " DtypeF        "; out inst_name;
  out " (";out clk_name;out",";out in_name;out",";out out_name; out ");";
  out "\n\n")
 end;

fun termToVerilog_DtypeF (out:string->unit) tm =
 if is_comb tm
     andalso is_const(fst(strip_comb tm))
     andalso (fst(dest_const(fst(strip_comb tm))) = "DtypeF")
     andalso is_pair(rand tm)
     andalso (length(strip_pair(rand tm)) = 3)
     andalso all is_var (strip_pair(rand tm))
  then DtypeFvInst tm out [] (map (fst o dest_var) (strip_pair(rand tm)))
  else raise ERR "termToVerilog_DtypeF" "bad component term";

val _ = add_termToVerilog[("DtypeF",termToVerilog_DtypeF)];
val _ = add_modules[("DtypeF",DtypeFvDef)];

(*****************************************************************************)
(* Non-primitive components                                                  *)
(*****************************************************************************)

(*****************************************************************************)
(* Lookup a term printer in termToVerilog_lib and apply it                   *)
(*****************************************************************************)
fun termToVerilog out tm =
 let val results =
          mapfilter (fn (_,f) => f out tm) (!termToVerilog_lib);
 in
  if (length results = 0)
   then (if_print "termToVerilog failed on:\n";
         if_print_term tm;
         raise ERR "termToVerilog" "can't handle this case") else
  if (length results > 1)
   then (if_print "Warning: termToVerilog found more than one module for\n";
         if_print_term tm; if_print "\n\n";
         ()) 
   else ()
 end;
 
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
          [clk_name,load_name] @ inp_names @ [done_name] @ out_names
     val module_names  = map (fst o dest_const o fst o strip_comb) modules
     fun removeTag tag s = let val l = explode s
                       in if (size s > size tag) andalso 
                             (implode (List.take(l,size tag)) = tag) then
                             implode (List.drop(l,size tag))
                          else s
                       end
     val _ = if not(null(subtract module_names 
                        (map ((removeTag "dev") o fst) (!module_lib))))
              then (print "unknown module in circuit: ";
                    print(hd(subtract module_names (map ((removeTag "dev") o fst)
                                                              (!module_lib))));
                    print "\n";
                    raise ERR "MAKE_VERILOG" "unknown modules in circuit")
              else ()
 in
 (out("// Definition of module " ^ name ^ " [Created: " ^ date() ^ "]\n\n");
  out("// Definitions of components used in " ^ name ^ "\n\n");
  map            (* Print definition of components *)
   (out o snd)
   (filter
     (fn(name,_) => mem (removeTag "dev" name) module_names)
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
(* Stuff to genenerate Verilog from unclocked netlists                       *)
(*****************************************************************************)

(*
**     (?v0 .... vn. M1(...) /\ ... /\ Mp(...))
**     ==>
**     DEV Spec (load, inp1 <> ... <> inpu, done, out1 <> ... <> outv)
**
** -->
**
** (Spec,
**  (``load``,[``inp1``,...,``inpu``],``done``,[``out1``,...,``outv``]),
**  [``v0``, ... ,``vn``],
**  [``M1(...)``, ... ,``Mp(...)``])
*)

fun dest_net thm =
 let val tm = concl(SPEC_ALL thm)
     val (tm3,tm4) = dest_imp tm
     val spec_tm = rand(rator tm4)
     val [load_tm,inp_tm,done_tm,out_tm] = strip_pair(rand tm4)
     val (vars,bdy) = strip_exists tm3
     val tml = strip_conj bdy
     val inpl = strip_BUS_CONCAT inp_tm
     val outl = strip_BUS_CONCAT out_tm
 in
  (spec_tm, (load_tm,inpl,done_tm,outl), vars, tml)
 end;

fun MAKE_NET_VERILOG name thm out =
 let val (spec_tm,
          (load_tm,inpl,done_tm,outl), 
          vars, 
          modules) = dest_net thm
     val load_name = var_name load_tm
     val inp_names = map var_name inpl
     val done_name = var_name done_tm
     val out_names = map var_name outl
     val module_args = 
          [load_name] @ inp_names @ [done_name] @ out_names;
     val module_names  = map (fst o dest_const o fst o strip_comb) modules
     val _ = if not(null(subtract module_names (map fst (!module_lib))))
              then (print "unknown module in circuit: ";
                    print(hd(subtract module_names (map fst (!module_lib))));
                    print "\n";
                    raise ERR "MAKE_NET_VERILOG" "unknown modules in circuit")
              else ()
 in
 (out("// Definition of module " ^ name ^ " [Created: " ^ date() ^ "]\n\n");
  out("// Definitions of components used in " ^ name ^ "\n\n");
  map            (* Print definition of components *)
   (out o snd)
   (filter
     (fn(name,_) => mem name module_names)
     (!module_lib));
  out("\n// Definition of module " ^ name ^ "\n");
  out "module ";
  out name; 
  out " (";
  map out (add_commas module_args);
  out ");\n";
  out(" input " ^ load_name ^ ";\n");
  map 
   (fn v => out(" input [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n")) 
   inpl;
  out(" output " ^ done_name ^ ";\n");
  map 
   (fn v => out(" output [" ^ var2size v ^ ":0] " ^ var_name v ^ ";\n")) 
   outl;
  out(" wire " ^ done_name ^ ";\n");
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

fun isSuccess s = (s = Process.success);

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
