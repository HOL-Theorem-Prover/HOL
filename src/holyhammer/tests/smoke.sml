(* ========================================================================= *)
(* FILE          : smoke.sml                                                 *)
(* DESCRIPTION   : End-to-end smoke driver for HolyHammer                    *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

val join = hhTestLib.join
val with_fresh_dir = hhTestLib.with_fresh_dir

fun installed prover = isSome (hhProver.probe (hhProver.config_of prover))

(* Each check prints one line and is counted; one that fails or raises
   makes the smoke fail. *)
val checks = ref 0
val failures = ref 0

fun check name run =
  let
    val (ok, detail) =
      run () handle Interrupt => raise Interrupt
                  | error => (false, "error: " ^ General.exnMessage error)
  in
    checks := !checks + 1;
    if ok then () else failures := !failures + 1;
    print (name ^ ": " ^ detail ^ "\n")
  end

(* Runs every installed prover once, through its own command line, on a
   one-step problem.  Z3, which no other check uses, may be absent. *)
fun runner_smoke problem prover =
  let val name = "runner " ^ hhConfig.prover_name prover in
    if installed prover then
      check name (fn () =>
        let
          val result = hhProver.run (hhProver.config_of prover)
            {timeout = 5, problem = problem, extra = [], debug_dir = NONE}
        in
          (#szs result = hhProver.SzsTheorem,
           hhProver.szs_name (#szs result))
        end)
    else print (name ^ ": skipped (absent)\n")
  end

fun runner_smokes () =
  with_fresh_dir (fn dir =>
    let
      val problem = join dir "problem.p"
      val _ = aiLib.write_file problem
        "fof(thm_2Ekeep__name, axiom, p).\nfof(conjecture, conjecture, p).\n"
    in
      app (runner_smoke problem) hhConfig.all_provers
    end)

(* Runs the user-facing hh_pb with E on arithmeticTheory.ADD1, and checks
   that the tactic to use is the last thing printed, after every slice has
   reported. *)
fun hh_pb_smoke () =
  check "hh_pb e" (fn () => with_fresh_dir (fn root =>
    let
      val output = join root "stdout"
      val add1 = DB.fetch "arithmetic" "ADD1"
      fun call () =
        (ignore (holyHammer.hh_pb root [hhConfig.Eprover]
           ["arithmeticTheory.ADD1"] (Thm.dest_thm add1));
         TextIO.flushOut TextIO.stdOut)
      val printed =
        (holyHammer.set_timeout 10;
         TextIO.flushOut TextIO.stdOut;
         smlRedirect.hide_in_file output call ();
         hhConfig.hh_unset "timeout";
         aiLib.readl output)
        handle error => (hhConfig.hh_unset "timeout"; raise error)
    in
      case List.rev printed of
          tactic :: "Replace `hh_pb` with:" :: _ =>
            if String.isPrefix "  " tactic andalso
               String.isSubstring "ADD1" tactic
            then (true, String.extract (tactic, 2, NONE))
            else (false, "unexpected tactic " ^ tactic)
        | _ => (false, "no tactic printed last")
    end))

(* The checks below run the tested provers on their default slice tables,
   each search for at most timeout seconds, on the premises given (filter
   none), without the cache and without fact or monomorphisation caps. *)
val timeout = 30
val tested_provers =
  [hhConfig.Eprover, hhConfig.Vampire, hhConfig.Zipperposition]
val settings =
  [("timeout", Int.toString timeout),
   ("provers",
    String.concatWith " " (map hhConfig.prover_name tested_provers)),
   ("slices", "16"), ("cores", "16"), ("filter", "none"),
   ("cache", "false"), ("format", ""), ("type_enc", ""), ("lam_trans", ""),
   ("max_facts", ""), ("mono_instances", "")]

(* NONE when Metis replays the proof from axioms, else why it did not. *)
fun reconstruction_error axioms goal =
  let val options = hhConfig.snapshot () in
    (ignore (hhReconstruct.hh_reconstruct_with
       {minimize = true, preplay_timeout = #preplay_timeout options,
        minimize_timeout = #minimize_timeout options,
        minimize_deadline = NONE} axioms goal (Context.snapshot ()));
     NONE)
    handle Interrupt => raise Interrupt
         | error => SOME (General.exnMessage error)
  end

(* A prover run passes with a theorem whose parsed axioms Metis replays. *)
fun verdict goal (result : hhProver.run_result) =
  case (#szs result, #used_axioms result) of
      (hhProver.SzsTheorem, SOME axioms) =>
        (case reconstruction_error axioms goal of
             NONE => (true, "Theorem, reconstructed")
           | SOME message =>
               (false, "Theorem, reconstruction failed: " ^ message))
    | (hhProver.SzsTheorem, NONE) => (false, "Theorem, no axioms parsed")
    | (szs, _) => (false, hhProver.szs_name szs)

(* One prover alone on the legacy FOF problem of goal and premises. *)
fun run_alone prover goal premises =
  with_fresh_dir (fn dir =>
    (hhExportFof.fof_export_pb dir
       (boolSyntax.list_mk_imp goal, mlThmData.thml_of_namel premises);
     hhProver.run (hhProver.config_of prover)
       {timeout = timeout, problem = join dir "atp_in", extra = [],
        debug_dir = NONE}))

fun run_schedule options max_proofs goal premises =
  hhSchedule.run
    {options = options, max_proofs = max_proofs, goal = goal,
     context = Context.snapshot (), rankings = [("none", premises)],
     progress = NONE}

(* The schedule of the schedule goal: three slices on three cores. *)
fun schedule_options () =
  hhConfig.snapshot_with [("slices", "3"), ("cores", "3"), ("cache", "true")]

fun schedule_verdict (result : hhSchedule.result) =
  case #suggestions result of
      suggestion :: _ =>
        if #stopped result = hhSchedule.MaxProofs then
          (true, "Theorem, reconstructed [" ^
             hhConfig.prover_name (#prover suggestion) ^ "]")
        else (false, "a proof, but the run did not stop at it")
    | [] => (false, "no proof")

(* Each goal is proved from its recorded dependencies: by one prover on
   all of them, by one prover on their MePo, MaSh or MeSh ranking, or by
   the schedule. *)
datatype kind =
    Alone of hhConfig.prover
  | Ranked of hhConfig.prover * string * int
  | Schedule

val goals =
  let open hhConfig in
    [("pair", "FST_SWAP", Alone Eprover),
     ("pair", "SND_SWAP", Alone Vampire),
     ("pair", "PAIR_FST_SND_EQ", Alone Zipperposition),
     ("option", "NOT_SOME_NONE", Alone Eprover),
     ("option", "OPTION_MAP_id", Alone Vampire),
     ("option", "OPTION_MAP_EQ_NONE_both_ways", Alone Zipperposition),
     ("arithmetic", "ADD_COMM", Alone Eprover),
     ("arithmetic", "SUC_ONE_ADD", Alone Vampire),
     ("arithmetic", "MULT_COMM", Alone Zipperposition),
     ("pair", "CLOSED_PAIR_EQ", Alone Eprover),
     ("arithmetic", "SUC_NOT_ZERO", Alone Vampire),
     ("arithmetic", "SUC_ADD_SYM", Alone Zipperposition),
     ("arithmetic", "ADD1", Schedule),
     ("bool", "TRUTH", Ranked (Eprover, "mepo", 96)),
     ("bool", "EQ_REFL", Ranked (Vampire, "mash", 96)),
     ("bool", "IMP_CLAUSES", Ranked (Zipperposition, "mesh", 128))]
  end

fun ranked thy filter count goal dependencies =
  hhLearn.rank
    (hhLearn.create_deferred_context_for thy (hhLearn.create_thmdata_for thy))
    {filter = filter, pool = SOME dependencies, goal = goal, n = count}

fun goal_smoke (thy, name, kind) =
  let
    val thm = DB.fetch thy name
    val goal = Thm.dest_thm thm
    val label =
      case kind of
          Alone prover => hhConfig.prover_name prover
        | Ranked (prover, filter, _) =>
            hhConfig.prover_name prover ^ ", " ^ filter
        | Schedule => "schedule"
    fun proof dependencies =
      case kind of
          Alone prover => verdict goal (run_alone prover goal dependencies)
        | Ranked (prover, filter, count) =>
            verdict goal (run_alone prover goal
              (ranked thy filter count goal dependencies))
        | Schedule =>
            schedule_verdict
              (run_schedule (schedule_options ()) 1 goal dependencies)
    fun run () =
      case mlThmData.intactdep_of_thm thm of
          (true, dependencies) => proof dependencies
        | (false, _) => (false, "broken dependencies")
  in
    check (thy ^ "." ^ name ^ " [" ^ label ^ "]") run
  end

(* The first proof of a schedule cancels its remaining slices, whose
   results do not enter the cache.  An unreachable proof limit runs the
   whole schedule; a repeat must then be answered from the cache alone. *)
fun cache_smoke () =
  let
    val options = schedule_options ()
    val thm = DB.fetch "arithmetic" "ADD1"
    val goal = Thm.dest_thm thm
    val dependencies = #2 (mlThmData.intactdep_of_thm thm)
    val primed = run_schedule options (#slices options + 1) goal dependencies
  in
    if #stopped primed <> hhSchedule.Exhausted orelse
       length (#slices_run primed) <> #slices options
    then (false, "priming did not run the whole schedule")
    else
      let
        val _ = hhProver.reset_spawn_count ()
        val repeated = run_schedule options 1 goal dependencies
        val spawned = hhProver.spawn_count ()
        val uncached =
          List.filter (fn (_, _, _, cached) => not cached)
            (#slices_run repeated)
      in
        if spawned = 0 andalso null uncached andalso
           not (null (#slices_run repeated)) andalso
           #1 (schedule_verdict repeated)
        then (true, "repeat answered from the cache")
        else (false, Int.toString spawned ^ " spawned processes and " ^
          Int.toString (length uncached) ^ " uncached slices")
      end
  end

fun run_slice options timeout goal premises (slice : hhProver.slice) =
  let val config = hhProver.config_of (#prover slice) in
    hhSchedule.with_problem_dir (join (hhConfig.state_dir ()) "problems")
      options (fn root =>
        (hhSchedule.export_problems root options goal
           [(#filter slice, premises)] [(config, slice)];
         hhProver.run config
           {timeout = timeout, problem = hhSchedule.problem_path root slice,
            extra = #extra_opts slice, debug_dir = NONE}))
  end

(* Every typed slice of the default schedule, of which there must be
   some, proves ADD1 from ADD1 itself, and its proof, which must use that
   premise, is parsed back and replayed. *)
fun format_smoke () =
  let
    val options = hhConfig.snapshot ()
    val goal = Thm.dest_thm (DB.fetch "arithmetic" "ADD1")
    fun format_verdict (result : hhProver.run_result) =
      if #used_axioms result = SOME [] then
        (false, hhProver.szs_name (#szs result) ^ ", no axioms parsed")
      else verdict goal result
    fun one (_, slice : hhProver.slice) =
      check ("format " ^ hhConfig.prover_name (#prover slice) ^ "/" ^
             #format slice ^ "/" ^ #type_enc slice ^ "/" ^ #lam_trans slice)
        (fn () => format_verdict
          (run_slice options timeout goal ["arithmeticTheory.ADD1"] slice))
    val typed = List.filter (fn (_, slice) => #type_enc slice <> "")
      (hhSlice.mk_schedule options)
  in
    if null typed then
      check "format" (fn () => (false, "no typed slice in the schedule"))
    else app one typed
  end

fun pigeonhole count =
  let
    val variables = List.tabulate (count, fn n =>
      Term.mk_var ("pigeonhole_" ^ Int.toString n, Type.bool))
    fun unequal left right =
      boolSyntax.mk_neg (boolSyntax.mk_eq (left, right))
    fun pairs [] = []
      | pairs (item :: rest) = map (unequal item) rest @ pairs rest
  in
    boolSyntax.list_mk_exists
      (variables, boolSyntax.list_mk_conj (pairs variables))
  end

fun matrix_slice prover format type_enc lam_trans nfacts =
  hhProver.mk_slice prover (format, type_enc, lam_trans) "none" nfacts

(* The complete typed-slice encoding matrix.  The final three rows are the
   table triples that the portfolio's substitutions replaced (see
   hhProver.portfolio): a substitution removes a slice from the schedule,
   but must not remove its encoding from the soundness checks. *)
val matrix =
  let open hhConfig in
    [matrix_slice Vampire "tx0" "mono_native_fool" "lifting" 96,
     matrix_slice Zipperposition "th1" "mono_native_higher_fool"
       "keep_lams" 128,
     matrix_slice Eprover "th0" "mono_native_higher" "keep_lams" 512,
     matrix_slice Eprover "tx0-" "mono_native_fool" "combs_and_lifting"
       1024,
     matrix_slice Vampire "tx0" "mono_native_fool" "combs" 512,
     matrix_slice Vampire "tf1" "poly_native" "lifting" 512,
     matrix_slice Eprover "tf0" "mono_native" "combs_and_lifting" 1024,
     matrix_slice Zipperposition "fof" "mono_guards??" "lifting" 32]
  end

(* On an unprovable pigeonhole goal, no slice of the default schedule, no
   encoding of the matrix (each queried briefly: enough to catch an
   unsound immediate theorem) and no user-facing call may claim a
   theorem. *)
fun soundness_smoke (name, count) =
  check ("soundness " ^ name) (fn () =>
    let
      val options = hhConfig.snapshot ()
      val goal = ([], pigeonhole count)
      val result = run_schedule options 1 goal []
      fun no_theorem szs = szs <> hhProver.SzsTheorem
      val schedule_ok =
        length (#slices_run result) =
          length (hhSlice.mk_schedule options) andalso
        List.all (fn (_, szs, _, _) => no_theorem szs)
          (#slices_run result) andalso
        null (#suggestions result)
      val matrix_ok =
        List.all (no_theorem o #szs o run_slice options 3 goal []) matrix
      val public_ok =
        with_fresh_dir (fn dir =>
          holyHammer.main_hh_lemmas dir mlThmData.empty_thmdata goal) = NONE
    in
      if schedule_ok andalso matrix_ok andalso public_ok then
        (true, "no theorem claimed")
      else (false, "a theorem was claimed")
    end)

fun main () =
  case List.filter (not o installed) tested_provers of
      absent as _ :: _ =>
        (print ("HolyHammer smoke: absent provers: " ^
           String.concatWith " " (map hhConfig.prover_name absent) ^ "\n");
         OS.Process.failure)
    | [] =>
      let
        (* The standalone executable has no script-owned theory by
           default.  Reconstruction evaluates a tactic and therefore needs
           initialized kernel theory state, just as an interactive HOL
           session has. *)
        val _ =
          (ignore (Theory.current_theory ()); ())
          handle Feedback.HOL_ERR _ =>
            Feedback.quiet_messages Theory.new_theory "hhSmoke"
        val _ = runner_smokes ()
        val _ = hh_pb_smoke ()
        val _ = List.app hhConfig.hh_set settings
        val _ = List.app goal_smoke goals
        val _ = check "arithmetic.ADD1 [schedule cache]" cache_smoke
        val _ = format_smoke ()
        val _ = List.app soundness_smoke
          [("bool-three-pigeonhole", 3), ("bool-four-pigeonhole", 4)]
      in
        print ("HolyHammer smoke passed " ^
          Int.toString (!checks - !failures) ^ "/" ^
          Int.toString (!checks) ^ " checks\n");
        if !failures = 0 then OS.Process.success else OS.Process.failure
      end

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "HolyHammer smoke failed: " ^ General.exnMessage error ^ "\n");
            OS.Process.failure)

val _ = OS.Process.exit status
