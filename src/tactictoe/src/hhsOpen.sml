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
   Deprecated cakeml hack:
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
   Running a command on a file in a directory
   -------------------------------------------------------------------------- *)

fun run_cmd cmd file =
  let 
    val dir = #dir (OS.Path.splitDirFile file)
    val basename = #file (OS.Path.splitDirFile file)
    val new_cmd =
      if dir = ""
      then cmd ^ " " ^ basename
      else "cd " ^ dir ^ ";" ^ cmd ^ " " ^ basename
  in
    ignore (OS.Process.system new_cmd)
  end

(* ---------------------------------------------------------------------------
   Running holmake on a file
   -------------------------------------------------------------------------- *)

fun run_holmake file = run_cmd (HOLDIR ^ "/bin/Holmake") file

(* ---------------------------------------------------------------------------
   Running buildheap on a file
   -------------------------------------------------------------------------- *)

fun run_hol0 file =
  let
    val buildheap = HOLDIR ^ "/bin/buildheap"
    val state0 = "-b " ^ HOLDIR ^ "/bin/hol.state0"
    val gc = "--gcthreads=1"
    val hol0 = String.concatWith " " [buildheap,gc,state0]
  in
    run_cmd hol0 file
  end

fun run_hol file =
  let
    val buildheap = HOLDIR ^ "/bin/buildheap"
    val gc = "--gcthreads=1"
    val hol = String.concatWith " " [buildheap,gc]
  in
    run_cmd hol file
  end

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

fun load_err s = load s handle _ => () 

fun code_of s =
  [
   "open hhsOpen;",
   "tactictoe_cleanval ();", 
   "tactictoe_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "tactictoe_export " ^ mlquote s ^ ";"]

(* ---------------------------------------------------------------------------
   Export
   -------------------------------------------------------------------------- *)

fun export_struct dir s = 
  let 
    val diro = hhs_open_dir ^ "/" ^ s
    val diri = dir ^ "/" ^ s
    val file = diri ^ "/code.sml"
    val fileuo = diri ^ "/code.uo"
  in
    mkDir_err hhs_open_dir; mkDir_err diro;
    mkDir_err dir; mkDir_err diri; 
    writel file (code_of s);
    run_holmake fileuo;
    run_hol fileuo
  end

(* ---------------------------------------------------------------------------
   Import
   -------------------------------------------------------------------------- *)

fun import_struct s = 
  let val dir = hhs_open_dir ^ "/" ^ s in
    (readl (dir ^ "/values"), readl (dir ^ "/constructors"),
     readl (dir ^ "/exceptions"), readl (dir ^ "/structures"))
  end

(* ---------------------------------------------------------------------------
   Export and import
   -------------------------------------------------------------------------- *)

fun export_import_struct dir s =
  (
  export_struct dir s;
  import_struct s handle _ => 
    (debug_unfold ("warning: structure " ^ s ^ " not found"); ([],[],[],[]))
  )



end (* struct *)
