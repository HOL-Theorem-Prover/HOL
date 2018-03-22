(* =========================================================================  *)
(* FILE          : tttOpen.sml                                                *)
(* DESCRIPTION   : Find string representation of SML values and structures in *)
(* a signature.                                                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttOpen :> tttOpen =
struct

open HolKernel boolLib tttTools

val ERR = mk_HOL_ERR "tttOpen"

(* ---------------------------------------------------------------------------
   Holmake
   -------------------------------------------------------------------------- *)

val core_theories =
  ["ConseqConv", "quantHeuristics", "patternMatches", "ind_type", "while",
   "one", "sum", "option", "pair", "combin", "sat", "normalForms",
   "relation", "min", "bool", "marker", "num", "prim_rec", "arithmetic",
   "numeral", "basicSize", "numpair", "pred_set", "list", "rich_list",
   "indexedLists"];

fun all_files file =
  let
    val base   = OS.Path.base file
    val fileuo = base ^ ".uo"
    val fileui = base ^ ".ui"
  in
    [file,fileuo,fileui]
  end

fun theory_files script =
  let
    val base      = fst (split_string "Script." script)
    val theory    = base ^ "Theory"
    val theoryuo  = theory ^ ".uo"
    val theoryui  = theory ^ ".ui"
    val theorydat = theory ^ ".dat"
    val theorysml = theory ^ ".sml"
  in
    [theorysml,theorydat,theoryuo,theoryui]
  end

fun run_holmake fileuo =
  let
    val dir = OS.Path.dir fileuo
    val holmake = HOLDIR ^ "/bin/Holmake"
    val cmd = String.concatWith " " [holmake, "-j1", fileuo]
  in
    print_endline ("TacticToe: running Holmake on " ^ fileuo);
    cmd_in_dir dir cmd
  end

fun find_heapname dir =
  let 
    val heapname_string = HOLDIR ^ "/bin/heapname"
    val _ = mkDir_err ttt_code_dir
    val fileout = ttt_code_dir ^ "/ttt_heapname" 
    val cmd = String.concatWith " " [heapname_string,">",fileout]
  in
    cmd_in_dir dir cmd;
    hd (readl fileout)
  end
  handle _ => raise ERR "heapname" ""

fun run_buildheap core_flag file =
  let 
    val dir = OS.Path.dir file
    val buildheap = HOLDIR ^ "/bin/buildheap"
    val state = 
      if core_flag then HOLDIR ^ "/bin/hol.state0" else find_heapname dir
    val cmd = 
      String.concatWith " " [buildheap,"--holstate=" ^ state,"-j1",file]
  in
    cmd_in_dir dir cmd
  end

fun remove_err s = FileSys.remove s handle SysErr _ => ()

fun run_rm_script core_flag file =
  (
  run_holmake (OS.Path.base file ^ ".uo");
  run_buildheap core_flag file;
  app remove_err (all_files file)
  )
  handle Interrupt => (app remove_err (all_files file); raise Interrupt)

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
    val dir = ttt_open_dir ^ "/" ^ s
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

fun code_of s =
  [
   "open tttOpen;",
   "tactictoe_cleanval ();",
   "tactictoe_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "tactictoe_export " ^ mlquote s ^ ";"
  ]

(* ---------------------------------------------------------------------------
   Export
   -------------------------------------------------------------------------- *)

fun export_struct dir s =
  let val script = dir ^ "/" ^ s ^ "__open__ttt.sml" in
    mkDir_err ttt_open_dir;
    mkDir_err (ttt_open_dir ^ "/" ^ s);
    writel script (code_of s);
    run_rm_script false script
  end

(* ---------------------------------------------------------------------------
   Import
   -------------------------------------------------------------------------- *)

fun import_struct s =
  let val dir = ttt_open_dir ^ "/" ^ s in
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
