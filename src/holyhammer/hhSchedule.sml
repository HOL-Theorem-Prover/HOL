(* ========================================================================= *)
(* FILE          : hhSchedule.sml                                            *)
(* DESCRIPTION   : HolyHammer parallel slice scheduler                       *)
(* ========================================================================= *)

structure hhSchedule :> hhSchedule =
struct

open HolKernel boolLib aiLib

datatype event =
    SliceStarted of hhProver.slice
  | SliceDone of hhProver.slice * hhProver.szs * real
  | ProofFound of hhProver.slice * string list
  | Verified of suggestion
  | ScheduleDone of stop_reason
and stop_reason = MaxProofs | Timeout | Exhausted | Interrupted
withtype suggestion =
  {stac : string, tac : tactic, lemmas : string list,
   prover : hhProver.prover, slice : hhProver.slice,
   t_prover : real, t_recon : real, t_replay : real}

type result =
  {suggestions : suggestion list,
   slices_run : (hhProver.slice * hhProver.szs * real * bool) list,
   stopped : stop_reason, t_total : real}

type success = hhProver.slice * string list * real

(* A lemma list waiting for reconstruction.  A Retry is a list that Metis
   could not replay, less one of its lemmas; origin is the key of that
   list. *)
datatype recon_item =
    Fresh of success
  | Retry of {origin : string, success : success}

(* The lists left by dropping each lemma in turn. *)
fun drop_one_variants lemmas =
  List.tabulate (length lemmas, fn index =>
    List.take (lemmas, index) @ List.drop (lemmas, index + 1))

fun join left right = OS.Path.concat (left, right)

val with_mutex = hhProver.with_mutex
val elapsed = hhProver.elapsed

fun time_before left right = Time.compare (left, right) = LESS

fun time_min left right = if time_before left right then left else right

val szs_name = hhProver.szs_name

fun prover_of (slice : hhProver.slice) =
  hhConfig.prover_name (#prover slice)

fun default_progress (SliceStarted slice) =
      print_endline
        ("  starting " ^ prover_of slice ^ " slice (" ^
         Int.toString (#nfacts slice) ^ " facts)")
  | default_progress (SliceDone (slice, szs, time)) =
      print_endline
        ("  " ^ prover_of slice ^ " slice: " ^ szs_name szs ^ " (" ^
         Real.toString time ^ " s)")
  | default_progress (ProofFound (slice, lemmas)) =
      (print_endline ("  proof found by " ^ prover_of slice ^ ":");
       print_endline
         ("    metis_tac [" ^
          String.concatWith ", " (map mlThmData.dbfetch_of_thmid lemmas) ^
          "]"))
  | default_progress (Verified suggestion) =
      print_endline
        ("  verified proof (replays in " ^
         Real.fmt (StringCvt.FIX (SOME 2)) (#t_replay suggestion) ^
         " s):\n    " ^ #stac suggestion)
  | default_progress (ScheduleDone _) = ()

fun problem_key (slice : hhProver.slice) =
  String.concatWith "."
    (map aiLib.escape [prover_of slice, #filter slice, #format slice,
                       #type_enc slice, #lam_trans slice,
                       Int.toString (#nfacts slice)])

(* mkdir reserves each invocation even across processes and saved heaps. *)
val next_directory_serial = Portable.make_counter {init = 1, inc = 1}

fun new_problem_dir parent =
  let
    val _ = hhConfig.ensure_dir parent
    fun reserve () =
      let
        val serial = next_directory_serial ()
        val directory = join parent
          (Portable.unique_tmp_suffix () ^ "." ^ Int.toString serial)
      in
        (OS.FileSys.mkDir directory; directory)
        handle error as OS.SysErr _ =>
          if (OS.FileSys.isDir directory handle OS.SysErr _ => false) then
            reserve ()
          else raise error
      end
  in
    reserve ()
  end

(* Each call removes only the root it reserved, never parent, so parallel
   calls in this or other processes do not interfere.  With debug_dir set,
   the problems are kept there instead, next to the prover output. *)
fun with_problem_dir parent (options : hhConfig.hh_options) f =
  case #debug_dir options of
      SOME directory => f (new_problem_dir (join directory "problems"))
    | NONE =>
        let
          val root = new_problem_dir parent
          fun cleanup () = hhConfig.remove_tree root
          val result = f root handle error => (cleanup (); raise error)
        in
          cleanup (); result
        end

fun problem_dir root (slice : hhProver.slice) =
  join root (problem_key slice)

fun problem_path root slice = join (problem_dir root slice) "atp_in"

fun same_problem_key (left : hhProver.slice) (right : hhProver.slice) =
  #prover left = #prover right andalso #filter left = #filter right andalso
  #format left = #format right andalso
  #type_enc left = #type_enc right andalso
  #lam_trans left = #lam_trans right andalso #nfacts left = #nfacts right

fun distinct_problem_slices slices =
  let
    fun collect _ [] = []
      | collect seen (slice :: rest) =
          if List.exists (same_problem_key slice) seen then collect seen rest
          else slice :: collect (slice :: seen) rest
  in
    collect [] slices
  end

(* The cap on new monomorphic instances.  The monomorphiser instantiates
   the facts in rank order and drops a polymorphic fact that gets no
   instance, and it makes about one instance per fact, so a cap below the
   slice's fact count silently cuts its lowest-ranked polymorphic facts:
   at the prover's own 256, a 512-fact slice for SORTED $<= l ==>
   isort l = l lost SORTED_PERM_EQ (ranked 158).  The prover's cap is
   therefore only a floor.  An explicit mono_instances is used as is. *)
fun mono_instances options config (slice : hhProver.slice) =
  case #mono_instances options of
      SOME cap => cap
    | NONE => Int.max (#mono_instances config, #nfacts slice)

(* This function is called before any scheduler thread is created.  Both
   thml_of_namel and the exporters touch HOL process-global state. *)
fun export_problems root options goal rankings schedule =
  let
    val slices = distinct_problem_slices (map #2 schedule)
    val conjecture = list_mk_imp goal
    val memo = hhProblemGen.new_export_memo ()
    val named_memo = ref []
    fun ranking_for filter =
      case List.find (fn (name, _) => name = filter) rankings of
          SOME (_, ranking) => ranking
        | NONE => raise Fail
            ("HolyHammer: missing premise ranking for filter '" ^
             filter ^ "'")
    (* Check every ranking before creating a directory or problem file. *)
    val _ = List.app (ignore o ranking_for o #filter) slices
    fun named_for filter nfacts =
      let
        val premises = ranking_for filter
        val count =
          if filter = "none" then
            (case #max_facts options of
                 NONE => length premises
               | SOME maximum => Int.min (maximum, length premises))
          else nfacts
      in
      case List.find (fn ((old_filter, old_nfacts), _) =>
          old_filter = filter andalso old_nfacts = nfacts)
          (!named_memo) of
          SOME (_, named) => named
        | NONE =>
            let
              val selected = first_n count premises
              (* Theorems with hypotheses are no premises (see hhLearn);
                 explicit hh_pb lists bypass premise selection. *)
              val named = List.filter (null o hyp o #2)
                (smlRedirect.hidef mlThmData.thml_of_namel selected)
            in
              named_memo := ((filter, nfacts), named) :: !named_memo;
              named
            end
      end
    fun config_for slice =
      case List.find
          (fn (config, other) => same_problem_key slice other) schedule of
          SOME (config, _) => config
        | NONE => raise Fail "HolyHammer: missing config for problem slice"
    fun export slice =
      let
        val config = config_for slice
        val directory = problem_dir root slice
        val named = named_for (#filter slice) (#nfacts slice)
        val _ = hhConfig.ensure_dir directory
      in
        case hhSlice.encoding_of slice of
            hhSlice.Legacy =>
              hhExportFof.fof_export_pb directory (conjecture, named)
          | hhSlice.Generated {format, type_enc, lam_trans} =>
              hhProblemGen.export_pb_in memo
                {format = format, type_enc = type_enc, lam_trans = lam_trans,
                 mono_iters = #mono_iters options,
                 mono_instances = mono_instances options config slice}
                (problem_path root slice) (conjecture, named)
      end
  in
    List.app export slices
  end

fun sorted_lemmas lemmas =
  Portable.sort
    (fn left => fn right => String.compare (left, right) <> GREATER) lemmas

fun lemma_key lemmas =
  String.concat
    (map (fn lemma => Int.toString (String.size lemma) ^ ":" ^ lemma)
      (sorted_lemmas lemmas))

fun distinct_configs schedule =
  let
    fun collect _ [] = []
      | collect seen ((config, _) :: rest) =
          if List.exists (fn name => #name config = name) seen then
            collect seen rest
          else config :: collect (#name config :: seen) rest
  in
    collect [] schedule
  end

fun run_in root {options, goal, rankings, progress} =
  let
    val started = Time.now ()
    val schedule = hhSlice.mk_schedule options
    val schedule_length = length schedule
    val report = case progress of NONE => default_progress | SOME f => f
    val report_mutex = Mutex.mutex ()
    fun emit event =
      (with_mutex report_mutex (fn () => report event)
       handle Interrupt => () | error =>
         TextIO.output (TextIO.stdErr,
           "HolyHammer progress callback failed: " ^
           General.exnMessage error ^ "\n"))
    val _ = export_problems root options goal rankings schedule
    val _ = hhCache.prune options
    (* Probe once on the calling thread.  Besides keeping version probes out
       of the worker pool, this avoids concurrent access to hhProver's probe
       memo table and makes cache hits process-free after the first run. *)
    val _ = List.app (ignore o hhProver.probe) (distinct_configs schedule)
    val execution_started = Time.now ()
    val deadline = Time.+
      (execution_started, Time.fromReal (Real.fromInt (#timeout options)))
    val hard_deadline = Time.+
      (deadline, Time.fromSeconds (Int.toLarge hhProver.grace_seconds))
    val state_mutex = Mutex.mutex ()
    val state_changed = ConditionVar.conditionVar ()
    val work = ref schedule
    val recon = ref ([] : success list)
    val slices_run = ref
      ([] : (hhProver.slice * hhProver.szs * real * bool) list)
    val suggestions = ref ([] : suggestion list)
    (* Lemma lists already reconstructed, successfully or not.  Metis
       does the same on the same list, so a list found again by another
       slice is not replayed again. *)
    val tried_keys = ref ([] : string list)
    (* With preplay_drop_one, a list Metis cannot replay queues its
       drop-one variants here.  They are tried only while no new list
       waits, and no longer once one variant of the same list verifies. *)
    val retries = ref ([] : {origin : string, success : success} list)
    val recovered = ref ([] : string list)
    val stopping = ref false
    val reason = ref (NONE : stop_reason option)
    val running = ref ([] : (int * bool ref * (unit -> unit)) list)
    val next_running = ref 0
    val worker_count = Int.min (#cores options, schedule_length)
    val workers_left = ref 0
    val launch_done = ref false
    val recon_done = ref false
    val recon_thread = ref (NONE : Thread.thread option)

    fun signal () = ConditionVar.broadcast state_changed

    fun get_work () =
      with_mutex state_mutex (fn () =>
        if !stopping orelse not (time_before (Time.now ()) deadline) then
          NONE
        else
          case !work of
              [] => NONE
            | item :: rest => (work := rest; SOME item))

    fun worker_finished () =
      with_mutex state_mutex (fn () =>
        (workers_left := !workers_left - 1; signal ()))

    fun launching_worker () =
      with_mutex state_mutex (fn () => workers_left := !workers_left + 1)

    fun finished_launching () =
      with_mutex state_mutex (fn () => (launch_done := true; signal ()))

    fun register_running kill =
      with_mutex state_mutex (fn () =>
        if !stopping then NONE
        else
          let val id = !next_running in
            next_running := id + 1;
            running := (id, ref false, kill) :: !running;
            SOME id
          end)

    (* Removal and cancellation marking share the mutex, so a completed
       slice cannot race a stop into caching a prematurely killed result. *)
    fun unregister_running id =
      with_mutex state_mutex (fn () =>
        let
          val cancelled =
            case List.find (fn (other, _, _) => id = other) (!running) of
                SOME (_, flag, _) => !flag
              | NONE => true
          val _ = running :=
            List.filter (fn (other, _, _) => id <> other) (!running)
        in
          cancelled
        end)

    fun kill_all stop_reason =
      let
        val kills = with_mutex state_mutex (fn () =>
          let
            val _ =
              case !reason of
                  NONE => reason := SOME stop_reason
                | SOME _ => ()
            val _ = stopping := true
            val _ = work := []
            val _ = recon := []
            val kills = map (fn (_, cancelled, kill) =>
              (cancelled := true; kill)) (!running)
            val _ = signal ()
          in
            kills
          end)
      in
        List.app (fn kill => kill () handle _ => ()) kills
      end

    fun cache_parts config request =
      case hhProver.probe config of
          NONE => NONE
        | SOME {path, version, ...} =>
            let
              val (_, argv) = #mk_command config path request
            in
              SOME
                ({prover = #name config, version = version, argv = argv,
                  problem = #problem request} : hhCache.key_parts)
            end

    fun note_result slice cached result =
      let
        val axioms =
          case (#szs result, #used_axioms result) of
              (hhProver.SzsTheorem, SOME values) => SOME values
            | _ => NONE
        val _ = with_mutex state_mutex (fn () =>
          slices_run :=
            (slice, #szs result, #time result, cached) :: !slices_run)
        val _ = emit (SliceDone (slice, #szs result, #time result))
      in
        case axioms of
            NONE => ()
          | SOME values =>
              (emit (ProofFound (slice, values));
               with_mutex state_mutex (fn () =>
                 (recon := !recon @ [(slice, values, #time result)];
                  signal ())))
      end

    fun run_slice (config, slice) =
      let
        val now = Time.now ()
        val remaining = Time.toReal (Time.- (hard_deadline, now))
        val wanted = hhSlice.slice_budget schedule_length options slice
        val budget = Real.max (0.001, Real.min (wanted, remaining))
        val request : hhProver.run_request =
          {timeout = Real.ceil budget, format = #format slice,
           problem = problem_path root slice, extra = #extra_opts slice,
           debug_dir = #debug_dir options}
        val _ = emit (SliceStarted slice)
        val parts = if #cache options then cache_parts config request else NONE
        val cached =
          case parts of NONE => NONE | SOME key => hhCache.lookup options key
        val result =
          case cached of
              SOME value => value
            | NONE =>
                let
                  val process = hhProver.run_async config request
                in
                  case register_running (#kill process) of
                      NONE =>
                        (#kill process (); #wait process ())
                    | SOME id =>
                        let
                          val result =
                            (#wait process ()
                             handle error =>
                               (ignore (unregister_running id); raise error))
                          val cancelled = unregister_running id
                          val _ = if cancelled then () else
                            case parts of
                                NONE => ()
                              | SOME key => hhCache.store options key result
                        in
                          result
                        end
                end
      in
        note_result slice (Option.isSome cached) result
      end

    fun worker_loop () =
      case get_work () of
          NONE => ()
        | SOME item =>
            ((run_slice item
              handle Interrupt => ()
                   | error =>
                     TextIO.output (TextIO.stdErr,
                       "HolyHammer slice failed: " ^
                       General.exnMessage error ^ "\n"));
             worker_loop ())

    fun worker () =
      ((worker_loop () handle _ => ()); worker_finished ())

    fun take_success () =
      let
        fun wait () =
          if !stopping then NONE
          else
            case (!recon, !retries) of
                (item :: rest, _) => (recon := rest; SOME (Fresh item))
              | ([], retry :: rest) =>
                  if time_before (Time.now ()) deadline then
                    (retries := rest; SOME (Retry retry))
                  else (retries := []; wait ())
              | ([], []) =>
                  if !launch_done andalso !workers_left = 0 then NONE
                  else
                    (ConditionVar.wait (state_changed, state_mutex); wait ())
        val _ = Mutex.lock state_mutex
        val result = wait ()
        val _ = Mutex.unlock state_mutex
      in
        result
      end
      handle exn => (Mutex.unlock state_mutex handle _ => (); raise exn)

    fun reconstruct item =
      let
        val (origin, (slice, lemmas, t_prover)) =
          case item of
              Fresh success => (NONE, success)
            | Retry {origin, success} => (SOME origin, success)
        val key = lemma_key lemmas
        fun member list value = List.exists (fn other => value = other) list
        val skip = with_mutex state_mutex (fn () =>
          (case origin of
               SOME parent => member (!recovered) parent
             | NONE => false) orelse
          member (!tried_keys) key orelse
          (tried_keys := key :: !tried_keys; false))
        fun queue_variants () =
          if #preplay_drop_one options andalso length lemmas > 1 then
            with_mutex state_mutex (fn () =>
              retries := !retries @
                map (fn variant =>
                       {origin = key, success = (slice, variant, t_prover)})
                  (drop_one_variants lemmas))
          else ()
      in
        if skip then ()
        else
          ((let
              (* Minimisation stops at the deadline, so that a verified
                 proof found late is still returned before the hard
                 deadline interrupts this thread. *)
              val ({stac, tac, t_replay}, t_recon) =
                add_time
                  (smlRedirect.hidef
                    (hhReconstruct.hh_reconstruct_with
                      {minimize = #minimize options,
                       preplay_timeout = #preplay_timeout options,
                       minimize_timeout = #minimize_timeout options,
                       minimize_deadline = SOME deadline}
                      lemmas))
                  goal
              val suggestion : suggestion =
                {stac = stac, tac = tac, lemmas = lemmas,
                 prover = #prover slice, slice = slice,
                 t_prover = t_prover, t_recon = t_recon,
                 t_replay = t_replay}
              val reached = with_mutex state_mutex (fn () =>
                (suggestions := suggestion :: !suggestions;
                 Option.app (fn parent => recovered := parent :: !recovered)
                   origin;
                 length (!suggestions) >= #max_proofs options))
              val _ = emit (Verified suggestion)
            in
              if reached then kill_all MaxProofs else ()
            end)
           handle Interrupt => raise Interrupt
                | error =>
                    (* A variant that fails is expected and not reported. *)
                    if Option.isSome origin then ()
                    else
                      (TextIO.output (TextIO.stdErr,
                         "HolyHammer reconstruction failed: " ^
                         General.exnMessage error ^ "\n");
                       queue_variants ()))
      end

    fun recon_loop () =
      case take_success () of
          NONE => ()
        | SOME item => (reconstruct item; recon_loop ())

    fun reconstruction_worker () =
      ((recon_loop () handle _ => ());
       with_mutex state_mutex (fn () => (recon_done := true; signal ())))

    fun completed () =
      with_mutex state_mutex
        (fn () => !launch_done andalso !workers_left = 0 andalso !recon_done)

    fun await () =
      if completed () then ()
      else if not (time_before (Time.now ()) hard_deadline) then
        (kill_all Timeout;
         case !recon_thread of
             NONE => ()
           | SOME thread => Thread.interrupt thread handle Thread _ => ();
         OS.Process.sleep (Time.fromMilliseconds 10);
         await ())
      else
        let
          val wake = time_min hard_deadline
            (Time.+ (Time.now (), Time.fromMilliseconds 100))
          val _ = Mutex.lock state_mutex
          val _ =
            if !launch_done andalso !workers_left = 0 andalso !recon_done
            then ()
            else ignore (ConditionVar.waitUntil (state_changed, state_mutex,
                                                  wake))
          val _ = Mutex.unlock state_mutex
        in
          await ()
        end
        handle exn => (Mutex.unlock state_mutex handle _ => (); raise exn)

    fun finish stopped =
      let
        val result : result =
          {suggestions = List.rev (!suggestions),
           slices_run = List.rev (!slices_run), stopped = stopped,
           t_total = elapsed started}
        val _ = emit (ScheduleDone stopped)
      in
        result
      end
  in
    if schedule_length = 0 then finish Exhausted
    else
      let
        fun launch () =
          let
            val consumer = Thread.fork (reconstruction_worker, [])
            val _ = recon_thread := SOME consumer
            fun start_worker _ =
              let
                val _ = launching_worker ()
              in
                Thread.fork (worker, [])
                handle error => (worker_finished (); raise error)
              end
            val _ = List.tabulate (worker_count, start_worker)
            val _ = finished_launching ()
          in
            await ()
          end
        fun interrupt () =
          (finished_launching ();
           kill_all Interrupted;
           case !recon_thread of
               NONE => ()
             | SOME thread =>
                 Thread.interrupt thread handle Thread _ => ();
           await ())
        val interrupted =
          ((launch (); false)
           handle Interrupt =>
             (interrupt (); true)
                | error => (interrupt (); raise error))
        val stopped =
          if interrupted then Interrupted
          else
            case !reason of
                SOME value => value
              | NONE =>
                  if time_before (Time.now ()) deadline then Exhausted
                  else Timeout
      in
        finish stopped
      end
  end

fun run request =
  with_problem_dir (join (hhConfig.state_dir ()) "problems")
    (#options request) (fn root => run_in root request)

end
