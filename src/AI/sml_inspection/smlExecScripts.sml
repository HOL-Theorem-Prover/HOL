(* ========================================================================  *)
(* FILE          : smlExecScripts.sml                                        *)
(* DESCRIPTION   : Execute a script from a given file                        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlExecScripts :> smlExecScripts =
struct

open HolKernel boolLib aiLib

val ERR = mk_HOL_ERR "smlExecScripts"

(* -------------------------------------------------------------------------
   Helper functions
   ------------------------------------------------------------------------- *)

fun bare file = OS.Path.base (OS.Path.file file)
fun remove_err s = FileSys.remove s handle SysErr _ => ()

(* -------------------------------------------------------------------------
   Find the right heap for running a script
   ------------------------------------------------------------------------- *)

val heapname_dir = HOLDIR ^ "/src/AI/sml_inspection/heapname"
val use_state0 = ref false

fun find_heapname file =
  if !use_state0 then HOLDIR ^ "/bin/hol.state0" else
  let
    val _ = mkDir_err heapname_dir
    val heapname_bin = HOLDIR ^ "/bin/heapname"
    val fileout = heapname_dir ^ "/heapname_" ^ bare file
    val cmd = String.concatWith " " [heapname_bin,">",fileout]
  in
    cmd_in_dir (OS.Path.dir file) cmd;
    hd (readl fileout)
  end
  handle Interrupt => raise Interrupt | _ => raise ERR "find_heapname" file


val core_scripts = map (fn x => x ^ "Script_ttt")
  ["ConseqConv", "quantHeuristics", "patternMatches", "ind_type", "while",
   "one", "sum", "option", "pair", "combin", "sat", "normalForms",
   "relation", "min", "bool", "marker", "num", "prim_rec", "arithmetic",
   "numeral", "basicSize", "numpair", "pred_set", "list", "rich_list",
   "indexedLists"];

fun find_tttheapname file =
  if mem (bare file) core_scripts
  then HOLDIR ^ "/bin/hol.state0"
  else find_heapname file

(* -------------------------------------------------------------------------
   Find script dependencies
   ------------------------------------------------------------------------- *)

val genscriptdep_dir = HOLDIR ^ "/src/AI/sml_inspection/genscriptdep"

fun find_genscriptdep file =
  let
    val _ = mkDir_err genscriptdep_dir
    val genscriptdep_bin = HOLDIR ^ "/bin/genscriptdep"
    val fileout = genscriptdep_dir ^ "/genscriptdep_" ^ bare file
    val cmd = String.concatWith " "
      [genscriptdep_bin, OS.Path.file file, ">", fileout]
  in
    cmd_in_dir (OS.Path.dir file) cmd;
    map holpathdb.subst_pathvars (readl fileout)
  end
  handle Interrupt => raise Interrupt
    | _ => raise ERR "find_genscriptdep" file

(* -------------------------------------------------------------------------
   Execute the script (for its side effects)
   ------------------------------------------------------------------------- *)

val buildheap_options = ref ""
val buildheap_dir = ref (HOLDIR ^ "/src/AI/sml_inspection/buildheap")
val buildheap_bin = HOLDIR ^ "/bin/buildheap"

fun exec_scriptb b script =
  let
    val _ = mkDir_err (!buildheap_dir)
    val fileout = !buildheap_dir ^ "/buildheap_" ^ bare script
    val depl = find_genscriptdep script
    val heap = if b then find_tttheapname script else find_heapname script
    val cmd = String.concatWith " "
      ([buildheap_bin,"--holstate=" ^ heap,"--gcthreads=1"] @
       [!buildheap_options] @
       depl @ [OS.Path.file script,">",fileout])
  in
    cmd_in_dir (OS.Path.dir script) cmd
  end

val exec_script = exec_scriptb false

(* -------------------------------------------------------------------------
   Restore theory files in case they were modified  during
   the execution of a tactictoe script (unlikely as
   export_theory is edited out from the modified script)
   ------------------------------------------------------------------------- *)

fun theory_files script =
  let
    val base      = fst (split_string "Script_ttt." script)
    val theory    = base ^ "Theory"
    val theoryuo  = theory ^ ".uo"
    val theoryui  = theory ^ ".ui"
    val theorydat = theory ^ ".dat"
    val theorysml = theory ^ ".sml"
  in
    [theorysml,theorydat,theoryuo,theoryui]
  end

fun save_file file =
  let
    val dir = #dir (OS.Path.splitDirFile file)
    val cmd = "cp -p " ^ file ^ " " ^ (file ^ ".tttsave")
  in
    cmd_in_dir dir cmd
  end

fun restore_file file =
  let
   val dir = #dir (OS.Path.splitDirFile file)
    val cmd1 = "cp -p " ^ (file ^ ".tttsave") ^ " " ^ file
    val cmd2 = "rm " ^ (file ^ ".tttsave")
  in
    cmd_in_dir dir (cmd1 ^ "; " ^ cmd2)
  end

fun save_thyfiles script = app save_file (theory_files script)
fun restore_thyfiles script = app restore_file (theory_files script)

(* -------------------------------------------------------------------------
   Execute tactictoe scripts.
   The recording script is erased at the end of the execution.
   ------------------------------------------------------------------------- *)

fun exec_tttrecord script =
  let fun cleanup () = (restore_thyfiles script; remove_err script) in
    ((save_thyfiles script; exec_scriptb true script; cleanup ())
    handle Interrupt => (cleanup (); raise Interrupt) | e => raise e)
  end

fun exec_ttteval dirout script =
  let
    val fileout = dirout ^ "/buildheap_" ^ bare script
    val heap = HOLDIR ^ "/bin/hol.state0"
    val cmd = String.concatWith " "
      ([buildheap_bin,"--holstate=" ^ heap,"--gcthreads=1"] @
       [!buildheap_options,OS.Path.file script,">",fileout])
  in
    cmd_in_dir (OS.Path.dir script) cmd
  end


end (* struct *)
