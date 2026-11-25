(* ========================================================================= *)
(* FILE          : smoke.sml                                                 *)
(* DESCRIPTION   : End-to-end smoke driver for HolyHammer                    *)
(* AUTHOR        : Lukasz Czajka                                             *)
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

(* Runs the user-facing hh_pb with E on arithmeticTheory.ADD1, and checks
   that the tactic to use is the last thing printed, after every slice has
   reported. *)
fun hh_pb_smoke () =
  case hhProver.probe (hhProver.config_of hhConfig.Eprover) of
      NONE => print "hh_pb e: skipped (absent)\n"
    | SOME _ =>
        let
          val root = fresh_output ()
          val _ = OS.FileSys.mkDir root
          val output = OS.Path.concat (root, "stdout")
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
            handle error =>
              (hhConfig.hh_unset "timeout"; hhConfig.remove_tree root;
               raise error)
          val _ = hhConfig.remove_tree root
        in
          case List.rev printed of
              tactic :: "Replace `hh_pb` with:" :: _ =>
                if String.isPrefix "  " tactic andalso
                   String.isSubstring "ADD1" tactic
                then print ("hh_pb e:" ^ tactic ^ "\n")
                else raise Fail ("hh_pb smoke: unexpected tactic " ^ tactic)
            | _ => raise Fail "hh_pb smoke: no tactic printed last"
        end


fun join a b = OS.Path.concat (a, b)

(* Applies f to a fresh directory, which is removed afterwards. *)
fun with_fresh_dir f =
  let
    val dir = fresh_output ()
    val _ = OS.FileSys.mkDir dir
  in
    (f dir before hhConfig.remove_tree dir)
    handle error => (hhConfig.remove_tree dir; raise error)
  end

fun installed prover = isSome (hhProver.probe (hhProver.config_of prover))

(* The checks below run the installed tested provers on their default
   slice tables, each search for at most timeout seconds, on the premises
   given (filter none) and without the cache. *)
val timeout = 30
val tested_provers =
  List.filter installed
    [hhConfig.Eprover, hhConfig.Vampire, hhConfig.Zipperposition]
val settings =
  [("timeout", Int.toString timeout),
   ("provers",
    String.concatWith " " (map hhConfig.prover_name tested_provers)),
   ("slices", "16"), ("cores", "16"), ("filter", "none"),
   ("cache", "false"), ("format", ""), ("type_enc", ""), ("lam_trans", "")]

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

fun reconstructs axioms goal =
  let val options = hhConfig.snapshot () in
    (ignore (hhReconstruct.hh_reconstruct_with
       {minimize = true, preplay_timeout = #preplay_timeout options,
        minimize_timeout = #minimize_timeout options,
        minimize_deadline = NONE} axioms goal);
     true)
    handle Interrupt => raise Interrupt | _ => false
  end

(* A prover run passes with a theorem whose parsed axioms Metis replays. *)
fun verdict goal (result : hhProver.run_result) =
  case (#szs result, #used_axioms result) of
      (hhProver.SzsTheorem, SOME axioms) =>
        if reconstructs axioms goal then (true, "Theorem, reconstructed")
        else (false, "Theorem, reconstruction failed")
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
     rankings = [("none", premises)], progress = NONE}

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
    val (prover, label) =
      case kind of
          Alone prover => (SOME prover, hhConfig.prover_name prover)
        | Ranked (prover, filter, _) =>
            (SOME prover, hhConfig.prover_name prover ^ ", " ^ filter)
        | Schedule => (NONE, "schedule")
    val label = thy ^ "." ^ name ^ " [" ^ label ^ "]"
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
    if Option.getOpt (Option.map installed prover, true) then
      check label run
    else print (label ^ ": skipped (absent)\n")
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

(* Every typed slice of the default schedule proves ADD1 from ADD1 itself,
   and its proof, which must name ADD1, is parsed back and replayed. *)
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
  in
    app one (List.filter (fn (_, slice) => #type_enc slice <> "")
      (hhSlice.mk_schedule options))
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

fun matrix_slice prover format type_enc lam_trans nfacts : hhProver.slice =
  {prover = prover, format = format, type_enc = type_enc,
   lam_trans = lam_trans, nfacts = nfacts, filter = "none", extra_opts = [],
   slice_size = 1}

(* The complete typed-slice encoding matrix.  The final three rows
   deliberately retain the parser-rejected table triples: a substitution
   removes a slice from the schedule, but must not remove its encoding from
   the soundness checks. *)
val matrix =
  let open hhConfig in
    [matrix_slice Vampire "tx0" "mono_native_fool" "lifting" 96,
     matrix_slice Zipperposition "th1" "mono_native_higher_fool"
       "keep_lams" 128,
     matrix_slice Eprover "th0" "mono_native_higher" "keep_lams" 512,
     matrix_slice Eprover "tx0-" "mono_native_fool" "combs_and_lifting"
       1024,
     matrix_slice Vampire "tf1" "poly_native" "lifting" 512,
     matrix_slice Eprover "tf0" "mono_native" "combs_and_lifting" 1024,
     matrix_slice Vampire "tx0" "mono_native_fool" "combs" 512,
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
        List.all (no_theorem o #szs o run_slice options 3 goal [])
          (List.filter (installed o #prover) matrix)
      val public_ok =
        with_fresh_dir (fn dir =>
          holyHammer.main_hh_lemmas dir mlThmData.empty_thmdata goal) = NONE
    in
      if schedule_ok andalso matrix_ok andalso public_ok then
        (true, "no theorem claimed")
      else (false, "a theorem was claimed")
    end)

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
    val _ = hh_pb_smoke ()
  in
    if null tested_provers then
      (print "HolyHammer smoke: no tested prover is installed\n";
       OS.Process.failure)
    else
      let
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
  end

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "HolyHammer smoke failed: " ^ General.exnMessage error ^ "\n");
            OS.Process.failure)

val _ = OS.Process.exit status
