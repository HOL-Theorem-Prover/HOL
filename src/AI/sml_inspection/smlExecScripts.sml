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

fun heapname_dir () = scratch_dir_of () ^ "/sml_inspection/heapname"
val use_state0 = ref false
val hol_bin = HOLDIR ^ "/bin/hol"

fun script_arg file = if OS.Path.isAbsolute file then file else OS.Path.file file

fun find_heapname_in_dir dir file =
  if !use_state0 then HOLDIR ^ "/bin/hol.state0" else
  let
    val _ = mkDir_err (heapname_dir ())
    val fileout = heapname_dir () ^ "/heapname_" ^ bare file
    val cmd = String.concatWith " "
      [shell_quote hol_bin, "heapname", ">", shell_quote fileout]
  in
    cmd_in_dir dir cmd;
    hd (readl fileout)
  end
  handle Interrupt => raise Interrupt | _ => raise ERR "find_heapname" file

fun find_heapname file = find_heapname_in_dir (OS.Path.dir file) file

val core_scripts = map (fn x => x ^ "Script_ttt")
  ["ConseqConv", "quantHeuristics", "patternMatches", "ind_type", "while",
   "one", "sum", "option", "pair", "combin", "sat", "normalForms",
   "relation", "min", "bool", "marker", "num", "prim_rec", "arithmetic",
   "numeral", "basicSize", "numpair", "pred_set", "list", "rich_list",
   "indexedLists"];

fun find_tttheapname_in_dir dir file =
  if mem (bare file) core_scripts
  then HOLDIR ^ "/bin/hol.state0"
  else find_heapname_in_dir dir file

(* -------------------------------------------------------------------------
   Find script dependencies
   ------------------------------------------------------------------------- *)

fun genscriptdep_dir () = scratch_dir_of () ^ "/sml_inspection/genscriptdep"
val script_includes = ref ([] : string list)

fun genscriptdep_env_prefix () =
  case !script_includes of
    [] => ""
  | l => "HOL_GENSCRIPTDEP_INCLUDES=" ^
         shell_quote (String.concatWith ":" l) ^ " "

fun find_genscriptdep_in_dir dir file =
  let
    val _ = mkDir_err (genscriptdep_dir ())
    val genscriptdep_bin = HOLDIR ^ "/bin/genscriptdep"
    val fileout = genscriptdep_dir () ^ "/genscriptdep_" ^ bare file
    val cmd = String.concatWith " "
      [genscriptdep_env_prefix () ^ shell_quote genscriptdep_bin,
       shell_quote (script_arg file), ">",
       shell_quote fileout]
  in
    cmd_in_dir dir cmd;
    map holpathdb.subst_pathvars (readl fileout)
  end
  handle Interrupt => raise Interrupt
    | _ => raise ERR "find_genscriptdep" file

fun find_genscriptdep file = find_genscriptdep_in_dir (OS.Path.dir file) file

(* -------------------------------------------------------------------------
   Execute the script (for its side effects)
   ------------------------------------------------------------------------- *)

val buildheap_options = ref ""
fun buildheap_dir () = scratch_dir_of () ^ "/sml_inspection/buildheap"

fun with_deferred_interrupts f =
  let
    val attributes = Thread.getAttributes ()
    val _ = Thread.setAttributes
      [Thread.InterruptState Thread.InterruptDefer]
    fun restore () = Thread.setAttributes attributes
  in
    (let val result = f () in restore (); result end
     handle e => (restore (); raise e))
  end

(* Fork the command ourselves rather than using OS.Process.system so callers
   can terminate a long-running HOL child.  A private process group includes
   any commands the child starts while running the script; the shell then
   immediately execs HOL. *)
fun run_with_pid private_group started finished dir cmd =
  case Posix.Process.fork () of
    NONE =>
      ((if private_group
        then ((ignore (Posix.ProcEnv.setsid ())) handle _ => ())
        else ());
       (OS.FileSys.chDir dir;
        Posix.Process.exec ("/bin/sh", ["sh", "-c", "exec " ^ cmd]))
       handle _ => Posix.Process.exit 0w127)
  | SOME pid =>
      let
        fun signal sigv =
          ((if private_group
            then Posix.Process.kill (Posix.Process.K_GROUP pid,sigv)
                   handle _ => ()
            else ());
           Posix.Process.kill (Posix.Process.K_PROC pid,sigv) handle _ => ())
        fun reap () = #2 (Posix.Process.waitpid
          (Posix.Process.W_CHILD pid,[]))
        fun finish () = finished pid handle _ => ()
        fun abort e = with_deferred_interrupts (fn () =>
          (signal Posix.Signal.kill;
           (reap () handle _ => Posix.Process.W_SIGNALED Posix.Signal.kill);
           finish ();
           raise e))
        val _ =
          (with_deferred_interrupts (fn () =>
             ((if private_group
               then Posix.ProcEnv.setpgid {pid = SOME pid, pgid = SOME pid}
                      handle _ => ()
               else ());
              started pid))
           handle e => abort e)
        val status = reap ()
          handle e => abort e
        val _ = finish ()
      in
        case status of
          Posix.Process.W_EXITED => ()
        | _ => raise ERR "run_with_pid" "external command failed"
      end

fun exec_scriptb_in_dir_with_pid private_group started finished b dir script =
  let
    val _ = mkDir_err (buildheap_dir ())
    val fileout = buildheap_dir () ^ "/buildheap_" ^ bare script
    val depl = find_genscriptdep_in_dir dir script
    val heap = if b then find_tttheapname_in_dir dir script
               else find_heapname_in_dir dir script
    (* Poly/ML runtime options must come before subcommand *)
    val cmd = String.concatWith " "
      ([shell_quote hol_bin,"--gcthreads=1"] @ [!buildheap_options] @
       ["run","--holstate=" ^ shell_quote heap] @
       map shell_quote depl @
       [shell_quote (script_arg script), ">", shell_quote fileout])
    val _ = run_with_pid private_group started finished dir cmd
  in
    ()
  end
  handle Interrupt => raise Interrupt
       | e => raise ERR "exec_scriptb_in_dir"
           ("HOL child failed while running " ^ script ^ ": " ^
            exnMessage e)

fun exec_script_with_pid started finished script =
  exec_scriptb_in_dir_with_pid true started finished false
    (OS.Path.dir script) script

fun exec_scriptb_in_dir b dir script =
  exec_scriptb_in_dir_with_pid false (fn _ => ()) (fn _ => ()) b dir script

fun exec_script_in_dir dir script = exec_scriptb_in_dir false dir script

fun exec_script script = exec_script_in_dir (OS.Path.dir script) script

(* -------------------------------------------------------------------------
   Execute tactictoe scripts.
   The recording script is erased at the end of the execution.
   ------------------------------------------------------------------------- *)

fun exec_tttrecord_in_dir dir script =
  let fun cleanup () = remove_err script in
    ((exec_scriptb_in_dir true dir script; cleanup ())
    handle Interrupt => (cleanup (); raise Interrupt)
         | e => (cleanup (); raise e))
  end

fun exec_tttrecord script = exec_tttrecord_in_dir (OS.Path.dir script) script

fun exec_ttteval dirout script =
  let
    val _ = mkDir_err dirout
    val fileout = dirout ^ "/buildheap_" ^ bare script
    val heap = HOLDIR ^ "/bin/hol.state0"
    (* Poly/ML runtime options must come before subcommand *)
    val cmd = String.concatWith " "
      ([shell_quote hol_bin,"--gcthreads=1"] @ [!buildheap_options] @
       ["run","--holstate=" ^ shell_quote heap,
        shell_quote (script_arg script),">",shell_quote fileout])
  in
    cmd_in_dir (OS.Path.dir script) cmd
  end


end (* struct *)
