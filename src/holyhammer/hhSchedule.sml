(* ========================================================================= *)
(* FILE          : hhSchedule.sml                                            *)
(* DESCRIPTION   : HolyHammer parallel slice scheduler                       *)
(* ========================================================================= *)

(* Kept outside the public [hhSchedule] signature so [selftest.sml] can start
   the workers of the export pool its own way ([fork]), act on a worker
   before it finishes an item ([before_finish], applied to the item's
   index), act where an item is handed to the pool ([after_submit]) or
   before it is prepared ([before_prepare]), act at the launch points of
   run_in ([launch_point]) and before a slice worker claims work
   ([before_claim]), set the gap between prover launches ([launch_gap]),
   select the export of run_in ([export_choice]) and read
   the export state of the problems of the last pipelined run
   ([export_states]).  Production leaves the hooks at their defaults. *)
structure hhSchedule_Test =
struct
  (* The export of one problem file in a pipelined run: Pending until its
     file is published (Ready), or until the export stops for good before
     reaching it (Cancelled: the run is stopping or past its soft deadline,
     or the export was interrupted) or fails (Failed). *)
  datatype export_state = Pending | Ready | Failed | Cancelled
  (* The state of every distinct problem path of the last pipelined run,
     as it was when the run ended. *)
  val export_states = ref ([] : (string * export_state) list)
  val fork = ref hhPool.default_fork
  (* Called on the worker with the item's index, after the temporary is
     opened and just before the tail runs, so that an exception raised
     here is a tail failure. *)
  val before_finish = ref (fn (_ : int) => ())
  (* Called on the caller with the item's index once a pooled item has
     been handed to the pool. *)
  val after_submit = ref (fn (_ : int) => ())
  (* Called with the item's index on the thread that prepares, before the
     item is prepared (after the producer's own check for a stop). *)
  val before_prepare = ref (fn (_ : int) => ())
  (* Which export run_in takes where hhSchedule.export_mode allows a
     choice: the measured policy (see export_mode), or either export
     whatever the policy says. *)
  datatype export_choice = Policy | ForceBlocking | ForcePipelined
  val export_choice = ref Policy
  (* Whether the pipelined run_in bounds the slices running at once while
     the export is unfinished (see run_in).  On by default; the knob lets a
     measurement compare the bounded and the unbounded run. *)
  val bound_slices = ref true
  (* Called at the launch points of a run_in: with "<thread>-registered"
     after the bookkeeping of a thread to launch (before it is forked) and
     with "<thread>-forked" right after it, for the threads "recon",
     "producer" and "worker".  An exception raised here stands for an
     asynchronous interrupt of the caller at that point. *)
  val launch_point = ref (fn (_ : string) => ())
  (* Called on a slice worker before each claim of work, with a test of
     whether the run is stopping. *)
  val before_claim = ref (fn (_ : unit -> bool) => ())
  (* The gap between two prover launches of a run_in, where not NONE (see
     launch_gap in hhSchedule.sml). *)
  val launch_gap = ref (NONE : Time.time option)
end

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

(* The least time between two prover launches of one run_in.  hhProver
   starts a prover with posix_spawn, which takes about a millisecond, so
   without a gap all the provers of a run start at once.  Many wall-clock
   timed prover strategies then miss their slices when the host is loaded.
   The fork it replaced took about 45 ms of the HOL heap and so spaced the
   launches that much, which measured better: the earlier slices of the
   schedule get the start-up CPU first.  A cache hit launches nothing and
   is never delayed. *)
val launch_gap = Time.fromMilliseconds 45

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
        let val root = new_problem_dir parent in
          Portable.finally (fn () => hhConfig.remove_tree root) f root
        end

fun problem_dir root (slice : hhProver.slice) =
  join root (problem_key slice)

fun problem_path root slice = join (problem_dir root slice) "atp_in"

(* The schedule's entries with distinct problems, each with its config.
   Slices with the same problem key share one problem file. *)
fun distinct_problems schedule =
  let
    fun collect _ [] = []
      | collect seen ((entry as (_, slice)) :: rest) =
          let val key = problem_key slice in
            if List.exists (fn other => other = key) seen
            then collect seen rest
            else entry :: collect (key :: seen) rest
          end
  in
    collect [] schedule
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

(* Copy source to destination through a fresh sibling temporary renamed
   on success, so that an existing destination is replaced whole and no
   temporary survives an error or an interrupt.  Returns the byte count.
   Hard links are not an option: opening an old path for writing would
   truncate every other path linked to it. *)
fun copy_file source destination =
  let
    val input = BinIO.openIn source
    val bytes = BinIO.inputAll input
      handle error => (BinIO.closeIn input; raise error)
    val _ = BinIO.closeIn input
  in
    hhConfig.write_atomically
      {open_out = BinIO.openOut, close_out = BinIO.closeOut} destination
      (fn output => BinIO.output (output, bytes));
    Word8Vector.length bytes
  end

type export_observer =
  {generated : hhProver.slice -> unit,
   copied : hhProver.slice * int -> unit}

val silent_observer : export_observer =
  {generated = fn _ => (), copied = fn _ => ()}

fun ranking_for rankings filter =
  case List.find (fn (name, _) => name = filter) rankings of
      SOME (_, ranking) => ranking
    | NONE => raise Fail
        ("HolyHammer: missing premise ranking for filter '" ^
         filter ^ "'")

(* The named selection of a slice (filter and actual prefix length): the
   conjecture and the legacy printer are fixed, so slices with the same
   selection share one legacy problem. *)
fun selection options rankings filter nfacts =
  let
    val premises = ranking_for rankings filter
    val wanted =
      if filter = "none" then
        (case #max_facts options of
             NONE => length premises
           | SOME maximum => maximum)
      else nfacts
  in
    (filter, Int.max (0, Int.min (wanted, length premises)))
  end

datatype kind =
    ExportLegacy
  | CopyLegacy of string
  | ExportGenerated of hhProblemGen.problem_options

type work =
  {index : int, config : hhProver.prover_config, slice : hhProver.slice,
   path : string, key : string * int, kind : kind}

(* The ordered work of one export: one item per distinct problem, in
   distinct_problems order.  The first legacy item of a selection is
   exported, the later ones copy its published file.  Every ranking is
   checked before the caller creates a directory or problem file. *)
fun ordered_work root options rankings schedule =
  let
    val problems = distinct_problems schedule
    val _ = List.app (ignore o ranking_for rankings o #filter o #2) problems
    fun item index (config, slice) firsts =
      let
        val path = problem_path root slice
        val key = selection options rankings (#filter slice) (#nfacts slice)
        fun work kind =
          {index = index, config = config, slice = slice, path = path,
           key = key, kind = kind}
      in
        case hhSlice.encoding_of slice of
            hhSlice.Legacy =>
              (case List.find (fn (old, _) => old = key) firsts of
                   SOME (_, first) => (work (CopyLegacy first), firsts)
                 | NONE => (work ExportLegacy, (key, path) :: firsts))
          | hhSlice.Generated {format, type_enc, lam_trans} =>
              (work (ExportGenerated
                 {format = format, type_enc = type_enc,
                  lam_trans = lam_trans, mono_iters = #mono_iters options,
                  mono_instances = mono_instances options config slice}),
               firsts)
      end
    fun build _ _ [] = []
      | build index firsts (entry :: rest) =
          let val (w, firsts') = item index entry firsts in
            w :: build (index + 1) firsts' rest
          end
  in
    build 0 [] problems
  end

(* The staged pipeline over ordered work.  Per item:
     prepare w         on the caller, in order; may touch HOL state and draw
                       fresh names;
     submit (w, p)     at admission: start the item's finishing work and
                       return it as a pending item;
     await q           at resolution, in order: wait for the pending item
                       and return what it staged;
     publish (w, f)    in order, on the caller.  An implementation may
                       commit an item earlier (at submit, or on a worker):
                       publish then only reports it, as the pipelined
                       export does by telling readiness again.
   Finishing work draws no fresh names and uses neither the memo nor
   the caches; it may read the live signature (see hhSchedule.sig).
   submit and await must be interchangeable in timing: an implementation
   may run the finishing work inside await (deferred, window 0) or on a
   worker started by submit.
   submit cleans up what it was given when it fails, await what it staged
   when it fails and publish what it was given when it fails.  abandon q
   cancels a pending item (waiting for its work to stop) and removes
   whatever it staged, release f removes whatever a finished item staged;
   both are idempotent and are applied to every item that is dropped.

   A failed stage stops admission, the work admitted before the failing
   index is resolved, the successful prefix is published and the exception
   of the earliest failing index is raised.  An interrupt drops all waiting
   work and propagates.

   Up to window admitted items wait while later ones are prepared.  With
   window 0 each item is prepared, awaited and published before the next is
   prepared; with window > 0 the finishing work of up to window items (on
   the workers of a pool) overlaps later prepares.  An
   observer sees the effects in stage order: a generated event fires in
   prepare and a copied event in publish, so with a window the copies are
   reported after later generated events. *)
fun run_staged {window}
    {prepare, submit, await, publish, abandon, release} works =
  let
    val queue = ref []
    val failure = ref NONE
    val stopped = ref NONE
    (* Newest first: an abandoned running item frees its worker slot, which
       the pool would hand to a waiting item, so the waiting (later) items
       are cancelled before the running (earlier) ones are interrupted. *)
    fun forget () =
      (List.app (fn (_, q) => (abandon q handle _ => ()))
         (List.rev (!queue));
       queue := [])
    (* The head stays queued until it is published, so that forget covers
       it whenever an exception leaves resolve. *)
    fun resolve () =
      case !queue of
          [] => ()
        | (w, q) :: rest =>
            let val finished = ref NONE in
              (finished := SOME (await q);
               publish (w, valOf (!finished));
               queue := rest)
              handle exn =>
                ((case !finished of
                      SOME f => (release f handle _ => ())
                    | NONE => ());
                 raise exn)
            end
            handle Interrupt => (forget (); raise Interrupt)
                 | exn => (failure := SOME exn; forget ())
    fun settle limit =
      while List.length (!queue) > limit andalso not (isSome (!failure)) do
        resolve ()
    fun admit [] = ()
      | admit (w :: rest) =
          case (SOME (submit (w, prepare w))
                handle Interrupt => (forget (); raise Interrupt)
                     | exn => (stopped := SOME exn; NONE)) of
              NONE => ()
            | SOME q =>
                (queue := !queue @ [(w, q)];
                 settle window;
                 if isSome (!failure) then () else admit rest)
    val _ = admit works
    val _ = settle 0
  in
    case (!failure, !stopped) of
        (SOME exn, _) => raise exn
      | (NONE, SOME exn) => raise exn
      | (NONE, NONE) => ()
  end

datatype prepared =
    Problem of hhProblemGen.problem_options * hhProblemGen.tail
  | Written of string
  | Copy of string

datatype finished = Temp of string | Copying of string | Published

(* A pending item: the finishing work of one item, awaited at resolution
   or cancelled when the item is dropped. *)
type pending = {await : unit -> finished, cancel : unit -> unit}

(* Prepare runs on the caller and the legacy exporter stages its file
   here too: it opens its output before collecting arities, and it closes
   the stream on every exception, so a failure leaves nothing behind. *)
fun prepare_work (observer : export_observer) conjecture memo named_for
    ({path, key, kind, slice, ...} : work) =
  let val _ = hhConfig.ensure_dir (OS.Path.dir path) in
    case kind of
        CopyLegacy first => Copy first
      | ExportLegacy =>
          (#generated observer slice;
           Written (#1 (hhConfig.stage_write
             {open_out = fn temporary => temporary, close_out = ignore} path
             (fn temporary => hhExportFof.fof_export_pbfile temporary
                (conjecture, named_for key)))))
      | ExportGenerated options =>
          (#generated observer slice;
           Problem (options,
             hhProblemGen.prepare_pb memo options
               (conjecture, named_for key)))
  end

(* The finishing work of a generated problem runs the tail of its
   preparation (the final first-orderization and the build of the AST),
   formats the AST and writes it to a temporary whose name was chosen
   beforehand, so that whoever drops the item can remove it whatever the
   writer did.  It draws no fresh names and uses no memo or cache, but the
   tail reads the live signature and type database, so it runs on a worker
   only when no context is pinned (see pool_size).  A failure of the tail
   is raw (hhProblemGen.Lambda_survived) and becomes its text where the
   caller awaits the item. *)
fun finish_problem started options tail temporary =
  (hhConfig.stage_to
     {open_out = TextIO.openOut, close_out = TextIO.closeOut} temporary
     (fn output =>
        (started ();
         TextIO.output (output, hhProblemGen.format_pb options (tail ()))));
   Temp temporary)

(* The inline implementation: the finishing work is deferred and runs on
   the caller when await forces it.  A staged legacy file or a copy needs
   no work. *)
fun submit_inline ({path, ...} : work, prepared) : pending =
  case prepared of
      Problem (options, tail) =>
        let val temporary = hhConfig.temp_path path in
          {await = fn () => finish_problem ignore options tail temporary,
           cancel = fn () => hhConfig.remove_quietly temporary}
        end
    | Written temporary =>
        {await = fn () => Temp temporary,
         cancel = fn () => hhConfig.remove_quietly temporary}
    | Copy first => {await = fn () => Copying first, cancel = fn () => ()}

fun release_finished (Temp temporary) = hhConfig.remove_quietly temporary
  | release_finished (Copying _) = ()
  | release_finished Published = ()

(* The pool-backed implementation: a generated problem is finished on a
   worker, everything else (a staged legacy file, a copy) is cheap and
   stays inline.  With early set, an item is published by the thread that
   finishes it (the worker, or the submitting thread for the cheap items)
   as soon as it is finished and awaiting it returns Published, so that a
   file does not wait for earlier items. *)
fun submit_pooled pool early before_finish after_submit
    (work as {path, index, ...} : work, prepared) : pending =
  case (prepared, early) of
      (Problem (options, tail), _) =>
        let
          val temporary = hhConfig.temp_path path
          fun run () =
            let
              val finished = finish_problem
                (fn () => before_finish index) options tail temporary
            in
              case early of
                  NONE => finished
                | SOME publish => (publish (work, finished); Published)
            end
          val job = hhPool.submit pool
            {run = run,
             discard = fn () => hhConfig.remove_quietly temporary}
          val _ = after_submit index
        in
          {await = fn () => hhPool.await job,
           cancel = fn () => hhPool.abandon job}
        end
    | (_, NONE) => submit_inline (work, prepared)
    | (_, SOME publish) =>
        let val {await, cancel} = submit_inline (work, prepared) in
          (publish (work, await ())
           handle exn => (cancel (); raise exn);
           {await = fn () => Published, cancel = fn () => ()})
        end

(* The caller-side conversion of a tail's failure to its text: the
   grammar is not read on a worker. *)
fun await_pending ({await, ...} : pending) =
  await () handle exn => raise hhProblemGen.describe_failure exn

fun abandon_pending ({cancel, ...} : pending) = cancel ()

fun publish_work (observer : export_observer)
    ({path, slice, ...} : work, finished) =
  case finished of
      Temp temporary =>
        (hhConfig.commit {temporary = temporary, final = path}
         handle exn => (hhConfig.remove_quietly temporary; raise exn))
    | Copying first => #copied observer (slice, copy_file first path)
    | Published => ()

(* The number of threads that finish generated problems: the configured
   export_workers, at most the cores and the number of generated problems;
   one means inline.  A caller with a pinned context (Context.is_pinned,
   in practice only the proof replay of the language server) gets one:
   the tail reads the ambient signature, which a fresh thread would see
   unpinned.  pinned is the caller's answer, asked once where the export
   starts: a forked producer is never pinned.  The producer does install a
   pin itself (hhNames.scoped, a snapshot of the context taken at its
   start, with writes discarded), but only for its own thread; its pool
   workers are unpinned and read the live context, which agrees with the
   snapshot because nothing writes the context during an export.  The
   items admitted and waiting for resolution are bounded by the workers
   (the queue briefly holds one more at admission), so the prepared tails
   (retained HOL terms) and the finished files held at any time are
   bounded as well. *)
fun pool_size pinned (options : hhConfig.hh_options) works =
  let
    val generated = length (List.filter
      (fn {kind = ExportGenerated _, ...} => true | _ => false) works)
  in
    if pinned then 1
    else Int.min (Int.min (#export_workers options, #cores options),
                  generated)
  end

(* The threads of the pool: a pool of at most one worker is the inline
   export, which has none. *)
fun pool_threads pinned options works =
  let val workers = pool_size pinned options works in
    if workers <= 1 then 0 else workers
  end

(* Which export a run_in uses.  The structural reasons come first: an empty
   schedule has nothing to export, a pinned caller would see a producer
   thread that is not pinned, and debug_dir keeps the whole problem set.
   Then hhSchedule_Test.export_choice, if it forces one.  Otherwise the
   policy decides.  The policy is what paired measurements of both exports
   with real provers support, nothing more: a measured cell either passed
   met the pre-registered criteria and is pipelined, or it failed or was
   not measured and keeps the blocking export.  The pipelined
   export is chosen only with max_proofs 1 and a (cores, timeout) pair of
   pipelined_region, the passing cells.  The pipelined run charges the
   export to the timeout and the export competes with the search for the
   CPU, which showed at more than one proof (later proofs lost, goals
   slower), at 1 core with a 60 s budget (a proof lost at the budget edge)
   and with 16 cores (more CPU, goals slower).  The measurements are kept
   outside the repository.  This is the one place that states the
   region. *)
datatype blocking_reason =
    EmptySchedule | PinnedCaller | Debugging | UnmeasuredCores
  | UnmeasuredTimeout | MoreProofs | Forced
datatype export_mode = Blocking of blocking_reason | Pipelined

(* The timeouts measured to pass: exactly one value, or that value and any
   longer one (the longer budget measured at 4 cores passed as well). *)
datatype budget = Exactly of int | AtLeast of int

val pipelined_region =
  [(1, Exactly 30), (2, Exactly 30), (3, Exactly 30), (4, AtLeast 30)]
val pipelined_max_proofs = 1

fun in_budget (Exactly t) timeout = timeout = t
  | in_budget (AtLeast t) timeout = timeout >= t

fun export_mode {pinned, options : hhConfig.hh_options, schedule_length} =
  if schedule_length = 0 then Blocking EmptySchedule
  else if pinned then Blocking PinnedCaller
  else if Option.isSome (#debug_dir options) then Blocking Debugging
  else
    case !hhSchedule_Test.export_choice of
        hhSchedule_Test.ForceBlocking => Blocking Forced
      | hhSchedule_Test.ForcePipelined => Pipelined
      | hhSchedule_Test.Policy =>
          (case List.find (fn (c, _) => c = #cores options)
                  pipelined_region of
               NONE => Blocking UnmeasuredCores
             | SOME (_, budget) =>
                 if not (in_budget budget (#timeout options)) then
                   Blocking UnmeasuredTimeout
                 else if #max_proofs options <> pipelined_max_proofs then
                   Blocking MoreProofs
                 else Pipelined)

(* Theorems with hypotheses are no premises (see hhLearn); explicit hh_pb
   lists bypass premise selection. *)
fun premises_of named = List.filter (null o hyp o #2) named

(* The theorems of a selection, fetched lazily the first time a key is
   used. *)
fun lazy_named rankings =
  let
    val named_memo = ref []
    fun named_for (key as (filter, count)) =
      case List.find (fn (old, _) => old = key) (!named_memo) of
          SOME (_, named) => named
        | NONE =>
            let
              val selected = first_n count (ranking_for rankings filter)
              val named = premises_of
                (smlRedirect.hidef mlThmData.thml_of_namel selected)
            in
              named_memo := (key, named) :: !named_memo;
              named
            end
  in
    named_for
  end

(* The same theorems, fetched at once before anything is exported: one
   fetch per filter, at the largest count any exported item of the filter
   uses, and the smaller counts take their prefix by name (the fetch is
   element-wise, so it adds no work to the lazy one).  A theorem that
   cannot be fetched raises here, before any file is written, where the
   lazy fetch raises at the key's first use.  The theorems are read on the
   calling thread, which is the only one that may run them (the fetch uses
   process-global state that the reconstruction thread uses as well). *)
fun hoisted_named rankings (works : work list) =
  let
    val keys = List.mapPartial
      (fn {kind = CopyLegacy _, ...} => NONE | {key, ...} => SOME key) works
    fun largest filter =
      List.foldl (fn ((other, count), best) =>
                    if other = filter then Int.max (best, count) else best)
        0 keys
    fun distinct [] = []
      | distinct ((filter, _) :: rest) =
          filter :: distinct (List.filter (fn (other, _) => other <> filter)
                               rest)
    fun fetch filter =
      let
        val names = first_n (largest filter) (ranking_for rankings filter)
        val fetched = smlRedirect.hidef (fn () =>
          map (fn name => mlThmData.thml_of_namel [name]) names) ()
      in
        (filter, fetched)
      end
    val fetched = map fetch (distinct keys)
    fun named_for (filter, count) =
      premises_of
        (List.concat (first_n count (valOf
           (Option.map #2 (List.find (fn (old, _) => old = filter) fetched)))))
  in
    named_for
  end

(* How the staged export publishes.  Ordered: items are published in
   schedule order as they resolve.  Early: an item is published as soon
   as it is finished, and ready is told of each published item; before and
   after bracket the preparation of each item (before may raise to stop
   the export).  Hence the pool-backed commit happens at submit (staged
   legacy files and copies) or on the pool worker (generated problems),
   and the in-order publish of run_staged then only tells ready again; an
   export without a pool (one worker) commits at that in-order publish. *)
datatype publication =
    Ordered
  | Early of {ready : work -> unit, before_prepare : work -> unit}

(* prepare (and everything that draws fresh names or touches HOL state
   other than reading the signature) runs on the thread that calls this
   function, before any pool worker exists.  Both thml_of_namel and the
   exporters touch HOL process-global state.  Only the finishing work of
   generated problems (the tail of the preparation, then format and write)
   moves to the workers of a pool, which is closed (its workers stopped and
   their files removed) before this returns or raises.  Every fresh name
   prepare draws comes from names (see hhNames). *)
fun export_works publication names pinned (observer : export_observer)
    options goal named_for works =
  let
    val fork = !hhSchedule_Test.fork
    val before_finish = !hhSchedule_Test.before_finish
    val after_submit = !hhSchedule_Test.after_submit
    val before_prepare = !hhSchedule_Test.before_prepare
    val conjecture = list_mk_imp goal
    val memo = hhProblemGen.new_export_memo_with names
    val (prior, early, publish) =
      case publication of
          Ordered => (ignore, NONE, publish_work observer)
        | Early {ready, before_prepare = pre} =>
            let fun now (w, f) = (publish_work observer (w, f); ready w) in
              (pre, SOME now, now)
            end
    fun prepare w =
      let
        val _ = prior w
        val _ = before_prepare (#index w)
      in
        prepare_work observer conjecture memo named_for w
      end
    fun run window submit =
      run_staged {window = window}
        {prepare = prepare, submit = submit, await = await_pending,
         publish = publish, abandon = abandon_pending,
         release = release_finished} works
    val workers = pool_threads pinned options works
  in
    if workers = 0 then run 0 submit_inline
    else
      hhPool.with_pool {workers = workers, fork = fork}
        (fn pool =>
         run workers
           (submit_pooled pool early before_finish after_submit))
  end

fun export_problems_observed
    (observer : export_observer) root options goal rankings schedule =
  let val works = ordered_work root options rankings schedule in
    export_works Ordered hhNames.global (Context.is_pinned ()) observer
      options goal (lazy_named rankings) works
  end

val export_problems = export_problems_observed silent_observer

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

(* A failure that is reported and does not end the run, on stderr. *)
fun warn what error =
  TextIO.output (TextIO.stdErr,
    "HolyHammer " ^ what ^ " failed: " ^ General.exnMessage error ^ "\n")

fun run_in root {options, goal, rankings, progress} =
  let
    val started = Time.now ()
    val schedule = hhSlice.mk_schedule options
    val schedule_length = length schedule
    val report = case progress of NONE => default_progress | SOME f => f
    val report_mutex = Mutex.mutex ()
    fun emit event =
      (with_mutex report_mutex (fn () => report event)
       handle Interrupt => () | error => warn "progress callback" error)
    (* Decided once, on the calling thread (a forked producer is never
       pinned, so the answer about the caller is asked here). *)
    val pipelined = export_mode
      {pinned = Context.is_pinned (), options = options,
       schedule_length = schedule_length} = Pipelined
    (* Everything that must stay on the calling thread comes first: the
       validation of the rankings and, when pipelined, the named fetches
       (they use process-global state that the reconstruction thread uses
       as well).  The blocking export runs entirely before the search. *)
    val plan =
      if pipelined then
        let val works = ordered_work root options rankings schedule in
          SOME (works, hoisted_named rankings works)
        end
      else (export_problems root options goal rankings schedule; NONE)
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
    (* The slices claimed and not yet finished, and how many may be while
       the export is unfinished: the producer needs a core of its own and
       the pool workers one each, so that provers do not starve them (see
       claim).  Without the pipelined export, or once the producer is
       terminal, only the number of workers bounds the slices. *)
    val active = ref 0
    val export_cap =
      case plan of
          SOME (works, _) =>
            if !hhSchedule_Test.bound_slices then
              Int.max (1, #cores options - 1
                          - pool_threads false options works)
            else schedule_length
        | NONE => schedule_length
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
    (* The pipelined export.  Every problem path has an export state
       (Pending until its file is published, then Ready; Cancelled or
       Failed when the producer ends without it); a slice is claimed only
       when its problem is Ready.  Without the pipelined export every
       problem is Ready from the start.  The producer is active from its
       launch until it is terminal (it finished, failed, was cancelled or
       interrupted).  The producer draws its fresh names from a supply of
       its own (see producer), so a replay, which draws from the global
       counter, starts as soon as a proof is found. *)
    datatype export_state = datatype hhSchedule_Test.export_state
    val exports =
      let
        val initial = if pipelined then Pending else Ready
        fun add (slice, seen) =
          let val path = problem_path root slice in
            if List.exists (fn (other, _) => other = path) seen then seen
            else (path, initial) :: seen
          end
      in
        ref (List.rev (List.foldl (fn ((_, slice), seen) => add (slice, seen))
                         [] schedule))
      end
    val producer_active = ref false
    (* The first fatal export error.  It and reason are the two outcomes of
       a stop that win by being first: once one is set (or the soft
       deadline has passed, or the producer was cancelled for it), a
       later error of the export is a late error of a cancelled job and is
       dropped. *)
    val producer_error = ref (NONE : exn option)
    val producer_thread = ref (NONE : Thread.thread option)
    val producer_cancelled = ref false
    (* Every thread forked by the caller, to be joined before it returns. *)
    val threads = ref ([] : Thread.thread list)
    val launch_point = !hhSchedule_Test.launch_point
    val before_claim = !hhSchedule_Test.before_claim
    val gap = getOpt (!hhSchedule_Test.launch_gap, launch_gap)
    (* The earliest time the next prover launch may take (see
       await_launch_slot). *)
    val next_launch = ref Time.zeroTime

    fun signal () = ConditionVar.broadcast state_changed

    (* The export state of a problem path (the mutex is held). *)
    fun export_state path =
      case List.find (fn (other, _) => other = path) (!exports) of
          SOME (_, state) => state
        | NONE => Failed

    (* The Pending problems end in the given state when the producer is
       terminal (the mutex is held). *)
    fun end_exports state =
      exports := map (fn (path, Pending) => (path, state) | other => other)
                     (!exports)

    fun entry_state (_, slice) = export_state (problem_path root slice)

    fun is_ready entry = entry_state entry = Ready

    (* A Pending entry may still become ready; an entry whose problem
       failed or was cancelled never will. *)
    fun may_become_ready entry = entry_state entry = Pending

    (* The earliest entry whose problem is ready, with the entries left. *)
    fun take_ready [] = NONE
      | take_ready (item :: rest) =
          if is_ready item then SOME (item, rest)
          else
            Option.map (fn (found, others) => (found, item :: others))
              (take_ready rest)

    (* Whether another slice may start (the mutex is held). *)
    fun has_room () = not (!producer_active) orelse !active < export_cap

    (* Waits (until the soft deadline) for a ready entry and for room.  The
       mutex is held on entry and on exit of the wait. *)
    fun claim () =
      if !stopping orelse not (time_before (Time.now ()) deadline) then NONE
      else
        case if has_room () then take_ready (!work) else NONE of
            SOME (item, rest) => (work := rest; active := !active + 1;
                                  SOME item)
          | NONE =>
              if null (!work) orelse
                 (has_room () andalso
                  not (List.exists may_become_ready (!work))) then NONE
              else
                (ignore (ConditionVar.waitUntil
                           (state_changed, state_mutex, deadline));
                 claim ())

    (* Runs f with the mutex held.  Unlike with_mutex, f's waits stay
       interruptible: an exception, an interrupt included, releases the
       mutex and propagates. *)
    fun with_locked f =
      let
        val _ = Mutex.lock state_mutex
        val result = f ()
        val _ = Mutex.unlock state_mutex
      in
        result
      end
      handle exn => (Mutex.unlock state_mutex handle _ => (); raise exn)

    fun get_work () = with_locked claim

    (* Reserves the next launch slot (never earlier than gap after the
       previous one, in the order of the reservations) and waits for it,
       with the mutex released while waiting and not held by the launch
       that follows.  False, with the slice not to be launched, when the
       run is stopping or past its soft deadline by then, like a claim
       (kill_all and the deadline checks signal state_changed); an
       interrupt of the wait propagates. *)
    fun await_launch_slot () =
      with_locked (fn () =>
        let
          val now = Time.now ()
          val slot = if time_before now (!next_launch) then !next_launch
                     else now
          val _ = next_launch := Time.+ (slot, gap)
          fun wait () =
            if !stopping orelse not (time_before (Time.now ()) deadline)
            then false
            else if not (time_before (Time.now ()) slot) then true
            else (ignore (ConditionVar.waitUntil
                            (state_changed, state_mutex,
                             time_min slot deadline));
                  wait ())
        in
          wait ()
        end)

    fun worker_finished () =
      with_mutex state_mutex (fn () =>
        (workers_left := !workers_left - 1; signal ()))

    fun launching_worker () =
      with_mutex state_mutex (fn () => workers_left := !workers_left + 1)

    fun finished_launching () =
      with_mutex state_mutex (fn () => (launch_done := true; signal ()))

    fun launching_producer () =
      with_mutex state_mutex (fn () => producer_active := true)

    fun mark_ready (work : work) =
      with_mutex state_mutex (fn () =>
        (exports := map (fn (path, Pending) =>
                              (path, if path = #path work then Ready
                                     else Pending)
                          | other => other) (!exports);
         signal ()))

    (* The one terminal step of the producer, whatever ended it: failed
       says that its unfinished problems ended in an error of the run
       (Failed) and not in a stop or a late error (Cancelled). *)
    fun producer_finished failed =
      with_mutex state_mutex (fn () =>
        (end_exports (if failed then Failed else Cancelled);
         producer_active := false; signal ()))

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

    (* A directed interrupt of a thread of the run, never of the running
       one (it would be taken at its next wait). *)
    fun interrupt_thread thread =
      if Thread.equal (thread, Thread.self ()) then ()
      else Thread.interrupt thread handle Thread _ => ()

    fun interrupt_recon () = Option.app interrupt_thread (!recon_thread)

    fun kill_all stop_reason =
      let
        val (kills, producer) = with_mutex state_mutex (fn () =>
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
            (kills, if !producer_active then !producer_thread else NONE)
          end)
      in
        List.app (fn kill => kill () handle _ => ()) kills;
        Option.app interrupt_thread producer
      end

    (* The soft deadline (or any later stop) cancels the export: nothing
       claims a problem past it, so its remaining problems have no
       consumer.  The producer is interrupted, once, wherever it waits;
       one that computes a prepare ends at the end of that prepare. *)
    fun cancel_exports () =
      let
        val producer = with_mutex state_mutex (fn () =>
          if !producer_active andalso not (!producer_cancelled) then
            (producer_cancelled := true; !producer_thread)
          else NONE)
      in
        Option.app interrupt_thread producer
      end

    (* A stop that also cancels the replays. *)
    fun stop_hard stop_reason =
      (kill_all stop_reason; interrupt_recon ())

    (* The export failed with exn.  If that is the first outcome of the run
       it is the run's error: the run stops, replays included, and the
       caller re-raises it.  Otherwise it is the late error of a cancelled
       export: it is reported on stderr, as the failure of a slice is, and
       dropped.  True when the error is the run's.  "First" is the order
       in which the errors are reported here (run_staged raises an error
       after the items admitted before it have settled), not the order in
       which the prepares failed. *)
    fun fail_export exn =
      let
        val first = with_mutex state_mutex (fn () =>
          if Option.isSome (!reason) orelse Option.isSome (!producer_error)
             orelse !producer_cancelled
             orelse not (time_before (Time.now ()) deadline) then false
          else (producer_error := SOME exn; true))
      in
        if first then stop_hard Exhausted else warn "late export" exn;
        first
      end

    exception Export_cancelled

    (* The export of the pipelined path, run on its own thread: the
       producer.  It stops between two prepares when the run is stopping
       or the soft deadline has passed (nothing is claimed after it), and
       a stop interrupts it where it waits (for a pooled tail).  The
       interrupts are taken only at waits and at the check between the
       prepares: a prepare is never cut, so its partial state cannot
       be left behind and the response to a stop is bounded by one
       prepare.  An interrupt that is neither a stop nor a cancellation is
       a stop of the run (Interrupted); an export failure is the run's
       error or a late error (see fail_export).

       Fresh names.  The producer draws every fresh name of its prepares
       from a supply of its own, seeded by one draw from the global
       counter when it starts (so its first name is the one the blocking
       export would draw and the sequence goes on from there, whatever the
       other threads draw meanwhile), and advances the global counter past
       its last name when it ends, however it ends.  Hence the files equal
       the blocking export's for the same start of the counter, and a
       replay, which draws from the global counter, needs no wait.  That
       the two sets of names may coincide while the producer runs is
       harmless: the names live in terms of the export (its memo, the
       translation caches, the monomorphization pools), which no replay
       sees, and the replay's names live in terms of Metis, which the
       export never sees; the goal and the theorems are shared but hold no
       generated name, as an export never changes them.  After the end of
       the producer a name drawn globally is past everything the memo
       holds, and any generated name that the producer holds from before
       its seed was drawn globally, below every private number.  The
       producer runs in hhNames.scoped, which pins its thread for the
       private format of the names (see hhNames). *)
    fun producer (works : work list, named_for) () =
      let
        fun cancelled () = with_mutex state_mutex (fn () =>
          !stopping orelse !producer_cancelled
          orelse not (time_before (Time.now ()) deadline))
        val publication = Early
          {ready = mark_ready,
           before_prepare = fn _ =>
             (Thread.testInterrupt ();
              if cancelled () then raise Export_cancelled else ())}
        datatype outcome = Quiet | Cut | Broke of exn
        (* The supply is created inside the handled region, so that a
           failure of its creation still ends in producer_finished.  The
           release is then only known once it exists. *)
        val released = ref (fn () => ())
        val outcome =
          (let
             val {supply, release, scoped} = hhNames.private_supply ()
           in
             released := release;
             scoped (fn () =>
               export_works publication supply false silent_observer options
                 goal named_for works);
             Quiet
           end)
          handle Export_cancelled => Quiet
               | Interrupt => Cut
               | exn => Broke exn
        (* No interrupt cuts the conclusion short.  A failure of release
           is an export failure unless the export has ended otherwise. *)
        val failed = Thread_Attributes.uninterruptible_defer
          (fn _ => fn () =>
            let
              val outcome =
                (!released (); outcome) handle exn =>
                  (case outcome of Broke _ => outcome | _ => Broke exn)
            in
              (case outcome of
                   Quiet => false
                 | Cut =>
                     (if with_mutex state_mutex (fn () =>
                           !stopping orelse !producer_cancelled) then ()
                      else stop_hard Interrupted;
                      false)
                 | Broke exn => fail_export exn)
              handle _ => false
            end) ()
      in
        Thread_Attributes.uninterruptible_defer
          (fn _ => fn () => producer_finished failed) ()
      end

    fun cache_key config request =
      case hhProver.probe config of
          NONE => NONE
        | SOME {path, version, ...} =>
            let
              val (_, argv) = #mk_command config path request
            in
              SOME (hhCache.key_of
                {prover = #name config, version = version, argv = argv,
                 problem = #problem request})
              handle Interrupt => raise Interrupt | _ => NONE
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
          {timeout = Real.ceil budget,
           problem = problem_path root slice, extra = #extra_opts slice,
           debug_dir = #debug_dir options}
        val key = if #cache options then cache_key config request else NONE
        val cached = Option.mapPartial (hhCache.lookup options) key
        fun launch () =
          let
            val _ = emit (SliceStarted slice)
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
                      Option.app
                        (fn key => hhCache.store options key result) key
                  in
                    result
                  end
          end
      in
        case cached of
            SOME value =>
              (emit (SliceStarted slice); note_result slice true value)
          | NONE =>
              if await_launch_slot () then note_result slice false (launch ())
              else ()
      end

    fun worker_loop () =
      (before_claim (fn () => with_mutex state_mutex (fn () => !stopping));
       case get_work () of
           NONE => ()
         | SOME item =>
             ((run_slice item
               handle Interrupt => ()
                    | error => warn "slice" error);
              (* only the cap, which only the pipelined export has, waits
                 on the count *)
              if Option.isSome plan then
                with_mutex state_mutex (fn () =>
                  (active := !active - 1; signal ()))
              else ();
              worker_loop ()))

    fun worker () =
      ((worker_loop () handle _ => ()); worker_finished ())

    (* The search is over: every worker is finished and the producer is
       terminal (the mutex is held). *)
    fun search_finished_locked () =
      !launch_done andalso !workers_left = 0 andalso not (!producer_active)

    (* Everything has stopped, reconstruction included (the mutex is
       held). *)
    fun finished_locked () = search_finished_locked () andalso !recon_done

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
                  if search_finished_locked () then NONE
                  else
                    (ConditionVar.wait (state_changed, state_mutex); wait ())
      in
        with_locked wait
      end

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
                      (warn "reconstruction" error;
                       queue_variants ()))
      end

    fun recon_loop () =
      case take_success () of
          NONE => ()
        | SOME item => (reconstruct item; recon_loop ())

    fun reconstruction_worker () =
      ((recon_loop () handle _ => ());
       with_mutex state_mutex (fn () => (recon_done := true; signal ())))

    fun completed () = with_mutex state_mutex finished_locked

    (* Waits for the run to finish.  The soft deadline cancels the export,
       the hard deadline stops everything that is left: the provers are
       killed and the replay and the producer interrupted. *)
    fun await () =
      if completed () then ()
      else if not (time_before (Time.now ()) hard_deadline) then
        (stop_hard Timeout;
         OS.Process.sleep (Time.fromMilliseconds 10);
         await ())
      else
        let
          val now = Time.now ()
          val soft = time_before now deadline
          val _ = if soft then () else cancel_exports ()
          val wake = time_min hard_deadline
            (time_min (if soft then deadline else hard_deadline)
               (Time.+ (now, Time.fromMilliseconds 100)))
          val _ = with_locked (fn () =>
            if finished_locked () then ()
            else ignore (ConditionVar.waitUntil (state_changed, state_mutex,
                                                  wake)))
        in
          await ()
        end

    (* Waits, masked, until every thread forked by the caller has exited;
       an interrupt that arrives meanwhile is raised afterwards. *)
    fun join_all () =
      Thread_Attributes.uninterruptible_wait (fn observe => fn () =>
        Multithreading.join_threads observe (fn () => ()) (!threads)) ()

    (* Everything has exited: the problems whose export never started or
       was left unfinished are Cancelled. *)
    fun close_exports () =
      with_mutex state_mutex (fn () => end_exports Cancelled)

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
        (* Forks a thread of the run.  The bookkeeping before the fork
           (started) and after it (forked, which records the thread) must
           not be cut apart by an interrupt of the caller: they run with
           interrupts deferred, and a failure to fork undoes started
           (failed).  An exception from a launch point before the fork
           takes the same way; one after it leaves the thread running and
           recorded, so that the cleanup stops and joins it. *)
        fun spawn name {started, failed, forked} body =
          Thread_Attributes.uninterruptible_defer (fn _ => fn () =>
            let
              val _ = started ()
              val thread =
                (launch_point (name ^ "-registered");
                 Thread.fork (body, []))
                handle error => (failed (); raise error)
              val _ = threads := thread :: !threads
              val _ = forked thread
              val _ = launch_point (name ^ "-forked")
            in
              ()
            end) ()
        fun launch () =
          let
            val _ = spawn "recon"
              {started = ignore,
               forked = fn thread => recon_thread := SOME thread,
               failed = fn () => with_mutex state_mutex (fn () =>
                 (recon_done := true; signal ()))}
              reconstruction_worker
            val _ =
              case plan of
                  NONE => ()
                | SOME (works, named_for) =>
                    spawn "producer"
                      {started = launching_producer,
                       forked = fn thread =>
                         if with_mutex state_mutex (fn () =>
                              (producer_thread := SOME thread; !stopping))
                         then interrupt_thread thread else (),
                       failed = fn () => producer_finished false}
                      (producer (works, named_for))
            fun start_worker _ =
              spawn "worker"
                {started = launching_worker, forked = ignore,
                 failed = worker_finished} worker
            val _ = List.tabulate (worker_count, start_worker)
            val _ = finished_launching ()
          in
            await ()
          end
        (* Everything that follows an interrupt or a failure of the caller
           is masked: a second interrupt is raised after the cleanup, which
           leaves no thread or process behind. *)
        fun interrupt () =
          Thread_Attributes.uninterruptible_defer (fn _ => fn () =>
            (finished_launching ();
             stop_hard Interrupted;
             await ();
             join_all ();
             close_exports ())) ()
        val interrupted =
          ((launch (); false)
           handle Interrupt =>
             (interrupt (); true)
                | error => (interrupt (); raise error))
        val _ = join_all ()
        val _ = close_exports ()
        val _ = if pipelined then hhSchedule_Test.export_states :=
                  with_mutex state_mutex (fn () => !exports)
                else ()
        val _ = case with_mutex state_mutex (fn () => !producer_error) of
                    SOME error => raise error
                  | NONE => ()
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
