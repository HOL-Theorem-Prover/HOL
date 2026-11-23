(* ========================================================================= *)
(* FILE          : smoke.sml                                                 *)
(* DESCRIPTION   : End-to-end smoke driver for HolyHammer                    *)
(* ========================================================================= *)

fun fresh_output () =
  let
    val path = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove path handle OS.SysErr _ => ()
  in
    path
  end

(* Runs every installed prover once, through its own command line, on a
   one-step problem; an absent prover is reported and skipped. *)
fun runner_smoke problem prover =
  let
    val name = hhConfig.prover_name prover
    val config = hhProver.config_of prover
  in
    case hhProver.probe config of
        NONE => print ("runner " ^ name ^ ": skipped (absent)\n")
      | SOME _ =>
          let
            val result = hhProver.run config
              {timeout = 5, problem = problem, extra = [], debug_dir = NONE}
          in
            if #szs result = hhProver.SzsTheorem then
              print ("runner " ^ name ^ ": Theorem\n")
            else raise Fail ("runner smoke failed for " ^ name ^
              ": status=" ^ hhProver.szs_name (#szs result))
          end
  end

fun runner_smokes () =
  let
    val problem = OS.FileSys.tmpName ()
    val stream = TextIO.openOut problem
    val _ = TextIO.output (stream,
      "fof(thm_2Ekeep__name, axiom, p).\nfof(conjecture, conjecture, p).\n")
    val _ = TextIO.closeOut stream
    fun remove () = OS.FileSys.remove problem handle OS.SysErr _ => ()
  in
    (app (runner_smoke problem) hhConfig.all_provers; remove ())
    handle error => (remove (); raise error)
  end

fun status_name (hhEval.Szs szs) = hhProver.szs_name szs
  | status_name hhEval.EvalError = "Error"
  | status_name hhEval.BrokenDeps = "BrokenDeps"
  | status_name hhEval.LoadFailure = "LoadFailure"

fun prover_text NONE = "no prover"
  | prover_text (SOME prover) = hhConfig.prover_name prover

fun show_result (entry : hhEval.journal_entry) =
  print (#goal_id entry ^ " [" ^ prover_text (#prover entry) ^ "]: " ^
    status_name (#szs entry) ^
    (case #recon_ok entry of
         SOME true => ", reconstructed\n"
       | SOME false => ", reconstruction failed\n"
       | NONE => ", not reconstructed\n"))

fun main () =
  let
    (* The standalone executable has no script-owned theory by default.
       Reconstruction evaluates a tactic and therefore needs initialized
       kernel theory state, just as an interactive HOL session has. *)
    val _ =
      (ignore (Theory.current_theory ()); ())
      handle Feedback.HOL_ERR _ =>
        Feedback.quiet_messages Theory.new_theory "hhSmoke"
    val _ = runner_smokes ()
    val expdir = fresh_output ()
    val entries = hhEval.run_smoke {expdir = expdir, timeout = 30}
      handle error =>
        (print ("HolyHammer smoke output kept in " ^ expdir ^ "\n");
         raise error)
    val _ = app show_result entries
    val _ = print ("HolyHammer smoke passed " ^
      Int.toString (length entries) ^ "/" ^
      Int.toString (length hhEval.smoke_goals) ^ " goals\n")
    val _ = hhConfig.remove_tree expdir
  in
    OS.Process.success
  end

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "HolyHammer smoke failed: " ^ General.exnMessage error ^ "\n");
            OS.Process.failure)

val _ = OS.Process.exit status
