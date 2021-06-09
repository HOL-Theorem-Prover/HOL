(* ========================================================================  *)
(* FILE          : smlOpen.sml                                               *)
(* DESCRIPTION   : Find string representation of SML values and structures   *)
(* in a signature.                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlOpen :> smlOpen =
struct

open HolKernel boolLib aiLib

val ERR = mk_HOL_ERR "smlOpen"

val sml_dir = HOLDIR ^ "/src/AI/sml_inspection"
val sml_code_dir = sml_dir ^ "/code"
val sml_open_dir = sml_dir ^ "/open"
val sml_buildheap_dir = sml_dir ^ "/buildheap"
fun bare file = OS.Path.base (OS.Path.file file)

(* -------------------------------------------------------------------------
   Running buildheap
   ------------------------------------------------------------------------- *)

(* ancestry "scratch"; *)
val core_theories =
  ["ConseqConv", "quantHeuristics", "patternMatches", "ind_type", "while",
   "one", "sum", "option", "pair", "combin", "sat", "normalForms",
   "relation", "min", "bool", "marker", "num", "prim_rec", "arithmetic",
   "numeral", "basicSize", "numpair", "pred_set", "list", "rich_list",
   "indexedLists"];

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

fun find_heapname dir file =
  let
    val _ = mkDir_err dir
    val heapname_bin = HOLDIR ^ "/bin/heapname"
    val fileout = dir ^ "/heapname_" ^ bare file
    val cmd = String.concatWith " " [heapname_bin,">",fileout]
  in
    cmd_in_dir (OS.Path.dir file) cmd;
    hd (readl fileout)
  end
  handle Interrupt => raise Interrupt
    | _ => raise ERR "find_heapname" file

fun find_genscriptdep dir file =
  let
    val _ = mkDir_err dir
    val genscriptdep_bin = HOLDIR ^ "/bin/genscriptdep"
    val fileout = dir ^ "/genscriptdep_" ^ bare file
    val cmd = String.concatWith " "
      [genscriptdep_bin, OS.Path.file file, ">", fileout]
  in
    cmd_in_dir (OS.Path.dir file) cmd;
    map holpathdb.subst_pathvars (readl fileout)
  end
  handle Interrupt => raise Interrupt
    | _ => raise ERR "find_genscriptdep" file

val buildheap_options = ref ""

fun run_buildheap dir core_flag file =
  let
    val _ = mkDir_err dir
    val buildheap_bin = HOLDIR ^ "/bin/buildheap"
    val filel = find_genscriptdep dir file
    val fileout = dir ^ "/buildheap_" ^ bare file
    val state =
      if core_flag
      then HOLDIR ^ "/bin/hol.state0"
      else find_heapname dir file
    val cmd =
      String.concatWith " "
        ([buildheap_bin,"--holstate=" ^ state,"--gcthreads=1"] @
         [!buildheap_options] @
         filel @
         [OS.Path.file file]  @
         [">",fileout])
  in
    cmd_in_dir (OS.Path.dir file) cmd
  end
  handle Interrupt => raise Interrupt
    | _ => raise ERR "run_buildheap" file

fun run_buildheap_nodep dir file =
  let
    val _ = mkDir_err dir
    val buildheap_bin = HOLDIR ^ "/bin/buildheap"
    val fileout = dir ^ "/buildheap_" ^ bare file
    val state = HOLDIR ^ "/bin/hol.state0"
    val cmd = String.concatWith " "
      ([buildheap_bin,"--holstate=" ^ state,"--gcthreads=1"] @
       [!buildheap_options] @
       [OS.Path.file file] @
       [">",fileout])
  in
    cmd_in_dir (OS.Path.dir file) cmd
  end
  (* handle Interrupt => raise Interrupt
    | _ => raise ERR "run_buildheap_nodep" file *)

fun remove_err s = FileSys.remove s handle SysErr _ => ()

fun run_rm_script core_flag file =
  (run_buildheap sml_buildheap_dir core_flag file; remove_err file)
  handle Interrupt => (remove_err file; raise Interrupt)

(* -------------------------------------------------------------------------
   Code for exporting values of a structure
   ------------------------------------------------------------------------- *)

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

fun sml_cleanstruct s =
  let val l = filter (test_struct s) (#allStruct PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetStructure (map fst l)
  end

fun test_val x =
  not (String.isPrefix "sml" (fst x) orelse fst x = "it")

fun sml_cleanval () =
  let val l = filter test_val (#allVal PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetValue (map fst l)
  end

fun sml_export s =
  let
    val dir = sml_open_dir ^ "/" ^ s
    val _ = mkDir_err sml_open_dir
    val _ = mkDir_err (sml_open_dir ^ "/" ^ s)
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

fun export_struct_code s =
  [
   "open smlOpen;",
   "sml_cleanval ();",
   "sml_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "sml_export " ^ mlquote s ^ ";"
  ]

(* -------------------------------------------------------------------------
   Running previous code.
   ------------------------------------------------------------------------- *)

fun export_struct s =
  let
    val _ = mkDir_err sml_code_dir
    val tempfile = sml_code_dir ^ "/" ^ s ^ "__open__sml.sml"
  in
    writel tempfile (export_struct_code s);
    run_rm_script false tempfile
  end

fun import_struct s =
  let val dir = sml_open_dir ^ "/" ^ s in
    (readl (dir ^ "/values"), readl (dir ^ "/constructors"),
     readl (dir ^ "/exceptions"), readl (dir ^ "/structures"))
  end

fun export_import_struct s =
  (
  export_struct s;
  import_struct s handle Interrupt => raise Interrupt | _ => ([],[],[],[])
  )

end (* struct *)
