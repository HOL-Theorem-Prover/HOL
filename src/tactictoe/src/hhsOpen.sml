(* =========================================================================  *)
(* FILE          : hhsOpen.sml                                                *)
(* DESCRIPTION   : Find string representation of SML values and structures in *)
(* a signature.                                                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsOpen :> hhsOpen =
struct

open HolKernel boolLib hhsRedirect hhsTools

val ERR = mk_HOL_ERR "hhsOpen"

(* Maybe all exceptions are constructors *)
fun gencode_values s =
  let
    val dir = hhs_open_dir ^ "/" ^ s
    val file1 = dir ^ "/code_values.sml"
    val file2 = dir ^ "/values"
    val file3 = dir ^ "/constructors"
    val file4 = dir ^ "/exceptions"
    val structl = rev (String.tokens (fn x => x = #".") s)
    val code_values =
    [
    "load " ^ (mlquote "lprefix_lubTheory") ^ ";",
    "load " ^ mlquote (last structl) ^ ";",
    "val tactictoe_it = List.map #1 (#allVal (PolyML.globalNameSpace) ());",
    "val _  = app PolyML.Compiler.forgetValue tactictoe_it;",
    "open " ^ s ^ ";",
    "val tactictoe_it = #allVal (PolyML.globalNameSpace) ();",
    "fun tactictoe_writel file sl =",
    "  let val oc = TextIO.openOut file in",
    "    List.app (fn s => TextIO.output (oc, String.concat [s,\"\\n\"])) sl;",
    "    TextIO.closeOut oc",
    "  end;",
    "val values = ",
    "  List.filter",
    "    (fn x => Bool.not (Lib.mem (#1 x) [\"it\",\"tactictoe_it\"]))", 
    "    tactictoe_it;",
    "val (constructors,l1) =",
    "  List.partition",
    "  (fn x => PolyML.NameSpace.Values.isConstructor (#2 x)) values;",
    "val (exceptions,l2) =",
    "  List.partition",
    "  (fn x => PolyML.NameSpace.Values.isException (#2 x)) l1;",
    "val _ = tactictoe_writel " ^ mlquote file2 ^ " (List.map #1 l2);",
    "val _ = tactictoe_writel " ^ mlquote file3 ^ " (List.map #1 constructors);",
    "val _ = tactictoe_writel " ^ mlquote file4 ^ " (List.map #1 exceptions);"
    ]
  in
    OS.FileSys.mkDir dir handle _ => ();
    writel file1 code_values
  end

fun all_values s = 
  let 
    val dir = hhs_open_dir ^ "/" ^ s
    val hide_file = dir ^ "/hide_values"
    val file = dir ^ "/code_values.sml"
    val cmd1 = "cd /home/tgauthier/cakeml"
    val cmd2 = (HOLDIR ^ "/bin/hol") ^ " < " ^ file
    val cmd = cmd1 ^ "; " ^ cmd2
  in
    gencode_values s;
    ignore (hide hide_file OS.Process.system cmd);
    (
    readl (dir ^ "/values"), 
    readl (dir ^ "/constructors"), 
    readl (dir ^ "/exceptions")
    )
  end

fun gencode_structures s =
  let
    val dir = hhs_open_dir ^ "/" ^ s
    val file1 = dir ^ "/code_structures.sml"
    val file2 = dir ^ "/structures"
    val structl = rev (String.tokens (fn x => x = #".") s)
    val loads = mlquote (last structl)
    val code_structures =
    [
    "load " ^ (mlquote "lprefix_lubTheory") ^ ";",
    "load " ^ loads ^ ";",
    "fun tactictoe_writel file sl =",
    "  let val oc = TextIO.openOut file in",
    "    List.app (fn s => TextIO.output (oc, s ^ \"\\n\")) sl;",
    "    TextIO.closeOut oc",
    "  end;",
    "val l1 = List.map #1 (#allStruct (PolyML.globalNameSpace) ());",
    "val l2 = List.filter (fn x => Bool.not (Lib.mem x [" ^ loads ^ ",\"PolyML\"])) l1;",
    "val tactictoe_map = List.map;",
    "val tactictoe_filter = List.filter;",
    "val tactictoe_not = Bool.not;",
    "val tactictoe_mem = Lib.mem;",
    "val _  = List.app PolyML.Compiler.forgetStructure l2;",
    "val l3 = tactictoe_map #1 (#allStruct (PolyML.globalNameSpace) ());",
    "open " ^ s ^ ";",
    "val l4 = tactictoe_map #1 (#allStruct (PolyML.globalNameSpace) ());",
    "val l5 = tactictoe_filter",
    "  (fn x => tactictoe_not (tactictoe_mem x l3)) l4;",
    "val _ = tactictoe_writel " ^ mlquote file2 ^ " l5;"
    ]
  in
    OS.FileSys.mkDir dir handle _ => ();
    writel file1 code_structures
  end

fun all_structures s = 
  let 
    val dir = hhs_open_dir ^ "/" ^ s
    val hide_file = dir ^ "/hide_structures"
    val file = dir ^ "/code_structures.sml"
    val cmd1 = "cd /home/tgauthier/cakeml"
    val cmd2 = (HOLDIR ^ "/bin/hol") ^ " < " ^ file
    val cmd = cmd1 ^ "; " ^ cmd2
  in
    gencode_structures s;
    ignore (hide hide_file OS.Process.system cmd);
    readl (dir ^ "/structures")
  end


end (* struct *)
