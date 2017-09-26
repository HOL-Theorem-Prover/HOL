(* =========================================================================  *)
(* FILE          : hhsOpen.sml                                                *)
(* DESCRIPTION   : Find string representation of SML values and structures in *)
(* a signature.                                                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsOpen :> hhsOpen =
struct

open HolKernel boolLib hhsTools

val ERR = mk_HOL_ERR "hhsOpen"

(* ---------------------------------------------------------------------------
   Needed for cakeml at the beginning of code_val
   "load " ^ (mlquote "lprefix_lubTheory") ^ ";",
   "load " ^ (mlquote "reg_allocTheory") ^ ";",
   -------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val cthy_unfold_glob = ref "scratch"

val hhs_unfold_dir = tactictoe_dir ^ "/unfold_log"
val hhs_scripts_dir = tactictoe_dir ^ "/scripts"
fun debug_unfold s = 
  append_endline (hhs_unfold_dir ^ "/" ^ !cthy_unfold_glob) s

(* ---------------------------------------------------------------------------
   Computation of dependencies (not used)
   -------------------------------------------------------------------------- *)

fun write_dep file cthy =
  let 
    val file_out = hhs_open_dir ^ "/tactictoe_" ^ cthy ^ "_holdep"
    val cmd = HOLDIR ^ "/bin/holdeptool.exe " ^ file ^ " > " ^ file_out
  in
    ignore (OS.Process.system cmd)
  end

fun read_dep cthy = 
  readl (hhs_open_dir ^ "/tactictoe_" ^ cthy ^ "_holdep")
  handle _ => raise ERR "read_dep" ""
  
fun tactictoe_load s = 
  load s handle _ => print_endline ("could not load " ^ s)

fun read_load cthy =
  "val _ = List.app hhsOpen.tactictoe_load [" ^ String.concatWith ", " 
  (map mlquote (read_dep cthy)) ^ "];"

(* ---------------------------------------------------------------------------
   Exporting elements of a structure (values + substructures)
   -------------------------------------------------------------------------- *)

fun top_struct s = hd (String.tokens (fn x => x = #".") s)
  
fun part_val l =
  let
    open PolyML.NameSpace.Values
    val (constructors,l0) = partition (fn x => isConstructor (snd x)) l
    val (exceptions,l1) = partition (fn x => isException (snd x)) l0 
  in
    (l1,constructors,exceptions)
  end

fun test_struct s x = fst x <> top_struct s

fun tactictoe_cleanstruct s = 
  let val l = filter (test_struct s) (#allStruct PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetStructure (map fst l)
  end

fun test_val x = 
  not (String.isPrefix "tactictoe" (fst x) orelse fst x = "it")

fun tactictoe_cleanval () = 
  let val l = filter test_val (#allVal PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetValue (map fst l)
  end

fun tactictoe_export s =
  let
    val dir = hhs_open_dir ^ "/" ^ s
    val l = filter test_val (#allVal PolyML.globalNameSpace ())
    val structures = 
      filter (test_struct s) (#allStruct PolyML.globalNameSpace ())
    val (values,constructors,exceptions) = part_val l
  in
    writel (dir ^ "/structures")   (map fst structures);
    writel (dir ^ "/values")       (map fst values);
    writel (dir ^ "/constructors") (map fst constructors);
    writel (dir ^ "/exceptions")   (map fst exceptions)
  end

(* ---------------------------------------------------------------------------
   Generating code
   -------------------------------------------------------------------------- *)

fun run_hol file =
  let
    val dir = #dir (OS.Path.splitDirFile file)
    val basename = #file (OS.Path.splitDirFile file)
    val hol_ni = HOLDIR ^ "/bin/buildheap " ^ "--gcthreads=1 " ^ "--poly"
    val cmd = 
      if dir = ""
      then hol_ni ^ " " ^ basename
      else "cd " ^ dir ^ ";" ^ hol_ni ^ " " ^ basename
  in
    ignore (OS.Process.system cmd)
  end

fun code_of s =
  ["load \"hhsOpen\";",
   "open hhsOpen;",
   "load " ^ mlquote (top_struct s) ^ ";",
   "tactictoe_cleanval ();", 
   "tactictoe_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "tactictoe_export " ^ mlquote s ^ ";"]

(* ---------------------------------------------------------------------------
   Executing and reading the result
   -------------------------------------------------------------------------- *)

fun read_open s = 
  let val dir = hhs_open_dir ^ "/" ^ s in
    (readl (dir ^ "/values"), readl (dir ^ "/constructors"),
     readl (dir ^ "/exceptions"), readl (dir ^ "/structures"))
  end

fun export_struct s = 
  let 
    val dir = hhs_open_dir ^ "/" ^ s
    val file = dir ^ "/code.sml"
  in
    mkDir_err hhs_open_dir;
    mkDir_err dir;
    writel file (code_of s);
    run_hol file;
    read_open s handle _ => 
    (debug_unfold ("warning: structure " ^ s ^ " not found"); ([],[],[],[]))
  end


end (* struct *)
