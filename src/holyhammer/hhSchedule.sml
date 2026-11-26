(* ========================================================================= *)
(* FILE          : hhSchedule.sml                                            *)
(* DESCRIPTION   : HolyHammer parallel slice scheduler                       *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

(* Kept outside the public [hhSchedule] signature so [selftest.sml] can start
   the workers of the export pool its own way ([fork]), act on a worker
   before it finishes an item ([before_finish], applied to the item's
   index), act where an item is handed to the pool ([after_submit]), act
   at the launch points of run_in ([launch_point]) and before a slice
   worker claims work ([before_claim]), and replace the reconstruction of
   a proof ([reconstruct]).  Production leaves the hooks at their
   defaults. *)
structure hhSchedule_Test =
struct
  val fork = ref hhPool.default_fork
  (* Called on the worker with the item's index, after the temporary is
     opened and just before the tail runs, so that an exception raised
     here is a tail failure. *)
  val before_finish = ref (fn (_ : int) => ())
  (* Called on the caller with the item's index once a pooled item has
     been handed to the pool. *)
  val after_submit = ref (fn (_ : int) => ())
  (* Called at the launch points of a run_in: with "<thread>-registered"
     after the bookkeeping of a thread to launch (before it is forked) and
     with "<thread>-forked" right after it, for the threads "recon" and
     "worker".  An exception raised here stands for an asynchronous
     interrupt of the caller at that point. *)
  val launch_point = ref (fn (_ : string) => ())
  (* Called on a slice worker before each claim of work, with a test of
     whether the run is stopping. *)
  val before_claim = ref (fn (_ : unit -> bool) => ())
  (* The reconstruction of a lemma list on the reconstruction thread. *)
  val reconstruct = ref hhReconstruct.hh_reconstruct_with
end

structure hhSchedule :> hhSchedule =
struct

open HolKernel boolLib aiLib

datatype event =
    SliceStarted of hhProver.slice
  | SliceDone of hhProver.slice * hhProver.szs * real
  | ProofFound of hhProver.slice * string list
  | ReplayFailed of hhProver.slice * string list
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

(* A retry drops one lemma from a failed reconstruction. The origin key
   identifies the full list. *)
type retry =
  {origin : string, success : hhProver.slice * (unit -> string list) * real}

datatype recon_item = Fresh of success | Retry of retry

(* Share prefixes and suffixes until a variant is taken for replay. *)
fun drop_one_variants lemmas =
  let
    fun loop _ [] variants = List.rev variants
      | loop prefix (lemma :: rest) variants =
          loop (lemma :: prefix) rest
            ((fn () => List.revAppend (prefix, rest)) :: variants)
  in
    loop [] lemmas []
  end

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
  | default_progress (ReplayFailed (slice, _)) =
      print_endline ("  proof by " ^ prover_of slice ^ " not replayed")
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

fun schedule_paths root schedule =
  map (fn entry as (_, slice) => (entry, problem_path root slice)) schedule

(* The schedule's entries with distinct problems, each with its config.
   Slices with the same problem key share one problem file. *)
fun distinct_problems schedule =
  let
    fun collect _ entries [] = List.rev entries
      | collect seen entries ((entry as (_, path)) :: rest) =
          if Redblackset.member (seen, path) then collect seen entries rest
          else collect (Redblackset.add (seen, path)) (entry :: entries) rest
  in
    collect (Redblackset.empty String.compare) [] schedule
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
  hhConfig.write_atomically
    {open_out = BinIO.openOut, close_out = BinIO.closeOut} destination
    (fn output =>
      Portable.bracket (fn () => BinIO.openIn source) BinIO.closeIn
        (fn input =>
          let
            fun copy total =
              let
                val bytes = BinIO.inputN (input, 65536)
                val size = Word8Vector.length bytes
              in
                if size = 0 then total
                else (BinIO.output (output, bytes); copy (total + size))
              end
          in
            copy 0
          end))

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

(* Count each used ranking once, stopping at its largest requested prefix. *)
fun selection_sizes (options : hhConfig.hh_options) rankings problems =
  let
    fun prefix_size 0 _ count = count
      | prefix_size _ [] count = count
      | prefix_size remaining (_ :: rest) count =
          prefix_size (remaining - 1) rest (count + 1)
    fun size (filter, maximum) =
      let
        val premises = ranking_for rankings filter
        val bound = if filter = "none" then #max_facts options
                    else SOME maximum
      in
        (filter, case bound of
                     NONE => length premises
                   | SOME n => prefix_size (Int.max (0, n)) premises 0)
      end
  in
    map size (hhSlice.filter_maxima problems)
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
fun ordered_work_for options rankings scheduled_paths =
  let
    val problems = distinct_problems scheduled_paths
    val sizes = selection_sizes options rankings (map #1 problems)
    fun item index ((config, slice), path) firsts =
      let
        val filter = #filter slice
        val size = ranking_for sizes filter
        (* The conjecture and the legacy printer are fixed, so slices
           with the same selection share one legacy problem. *)
        val count = if filter = "none" then size
                    else Int.max (0, Int.min (#nfacts slice, size))
        val key = (filter, count)
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

fun ordered_work root options rankings schedule =
  ordered_work_for options rankings (schedule_paths root schedule)

(* The staged pipeline over ordered work.  Per item:
     prepare w         on the caller, in order; may touch HOL state and draw
                       fresh names;
     submit (w, p)     at admission: start the item's finishing work and
                       return it as a pending item;
     await q           at resolution, in order: wait for the pending item
                       and return what it staged;
     publish (w, f)    in order, on the caller.
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

datatype finished = Temp of string | Copying of string

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

(* The pool-backed implementation: a generated problem is finished on a
   worker, everything else (a staged legacy file, a copy) is cheap and
   stays inline. *)
fun submit_pooled pool before_finish after_submit
    (work as {path, index, ...} : work, prepared) : pending =
  case prepared of
      Problem (options, tail) =>
        let
          val temporary = hhConfig.temp_path path
          fun run () = finish_problem
            (fn () => before_finish index) options tail temporary
          val job = hhPool.submit pool
            {run = run,
             discard = fn () => hhConfig.remove_quietly temporary}
          val _ = after_submit index
        in
          {await = fn () => hhPool.await job,
           cancel = fn () => hhPool.abandon job}
        end
    | _ => submit_inline (work, prepared)

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

(* The number of threads that finish generated problems: the configured
   export_workers, at most the cores and the number of generated problems;
   one means inline.  A caller with a pinned context (Context.is_pinned,
   in practice only the proof replay of the language server) gets one:
   the tail reads the ambient signature, which a fresh thread would see
   unpinned.  The items admitted and waiting for resolution are bounded by
   the workers (the queue briefly holds one more at admission), so the
   prepared tails (retained HOL terms) and the finished files held at any
   time are bounded as well. *)
fun pool_size (options : hhConfig.hh_options) works =
  let
    val generated = length (List.filter
      (fn {kind = ExportGenerated _, ...} => true | _ => false) works)
  in
    if Context.is_pinned () then 1
    else Int.min (Int.min (#export_workers options, #cores options),
                  generated)
  end

(* Theorems with hypotheses are no premises (see hhLearn); explicit hh_pb
   lists bypass premise selection. *)
fun premises_of named = List.filter (null o hyp o #2) named

(* The theorems of a selection (filter, count), fetched the first time
   the key is used. *)
fun lazy_named rankings =
  let
    val named_memo = ref []
    fun named_for (key as (filter, count)) =
      case List.find (fn (old, _) => old = key) (!named_memo) of
          SOME (_, named) => named
        | NONE =>
            let
              val selected = first_n count (ranking_for rankings filter)
              val named = premises_of (mlThmData.thml_of_namel selected)
            in
              named_memo := (key, named) :: !named_memo;
              named
            end
  in
    named_for
  end

(* prepare (and everything that draws fresh names or touches HOL state
   other than reading the signature) runs on the thread that calls this
   function, before any pool worker exists.  Both thml_of_namel and the
   exporters touch HOL process-global state.  Only the finishing work of
   generated problems (the tail of the preparation, then format and write)
   moves to the workers of a pool, which is closed (its workers stopped and
   their files removed) before this returns or raises. *)
fun export_works (observer : export_observer) options goal rankings works =
  let
    val fork = !hhSchedule_Test.fork
    val before_finish = !hhSchedule_Test.before_finish
    val after_submit = !hhSchedule_Test.after_submit
    val conjecture = list_mk_imp goal
    val memo = hhProblemGen.new_export_memo ()
    val named_for = lazy_named rankings
    fun run window submit =
      run_staged {window = window}
        {prepare = prepare_work observer conjecture memo named_for,
         submit = submit, await = await_pending,
         publish = publish_work observer, abandon = abandon_pending,
         release = release_finished} works
    val workers = pool_size options works
  in
    if workers <= 1 then run 0 submit_inline
    else
      hhPool.with_pool {workers = workers, fork = fork}
        (fn pool =>
         run workers (submit_pooled pool before_finish after_submit))
  end

fun export_problems_observed observer root options goal rankings schedule =
  export_works observer options goal rankings
    (ordered_work root options rankings schedule)

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
    "HolyHammer " ^ what ^ " failed: " ^ Feedback.exn_to_string error ^
    "\n")

fun run_with_root share_digests root
    {options, max_proofs, goal, context, rankings, progress} =
  let
    val started = Time.now ()
    val schedule = hhSlice.mk_schedule options
    val schedule_length = length schedule
    val report = case progress of NONE => default_progress | SOME f => f
    val report_mutex = Mutex.mutex ()
    fun emit event =
      (with_mutex report_mutex (fn () => report event)
       handle Interrupt => () | error => warn "progress callback" error)
    (* The export runs on the calling thread before the search (it uses
       process-global state that the reconstruction thread uses as well);
       an error or an interrupt of it propagates before any event. *)
    val scheduled_paths = schedule_paths root schedule
    val works = ordered_work_for options rankings scheduled_paths
    val _ = export_works silent_observer options goal rankings works
    val _ = hhCache.prune options
    (* In a private root, a byte copy and its source share a digest.
       Each group has its own lock so unrelated hashes can overlap. *)
    val problem_digests =
      let
        val empty = Redblackmap.mkDict String.compare
        fun add ({path, kind, ...} : work, digests) =
          let
            val cell =
              case kind of
                  CopyLegacy source => Redblackmap.find (digests, source)
                | _ => (Mutex.mutex (), ref NONE)
          in
            Redblackmap.insert (digests, path, cell)
          end
      in
        if #cache options andalso share_digests then
          List.foldl add empty works
        else empty
      end
    fun problem_digest path =
      case Redblackmap.peek (problem_digests, path) of
          NONE => SHA1.sha1_file {filename = path}
        | SOME (mutex, saved) =>
            with_mutex mutex (fn () =>
              case !saved of
                  SOME digest => digest
                | NONE =>
                    let val digest = SHA1.sha1_file {filename = path} in
                      saved := SOME digest;
                      digest
                    end)
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
    val recon = ref ([] : success list)
    val reconstruct_with = !hhSchedule_Test.reconstruct
    val slices_run = ref
      ([] : (hhProver.slice * hhProver.szs * real * bool) list)
    val suggestions = ref ([] : suggestion list)
    (* Lemma lists already reconstructed, successfully or not.  Metis
       does the same on the same list, so a list found again by another
       slice is not replayed again. *)
    val tried_keys = ref ([] : string list)
    (* With preplay_drop_one, a list Metis cannot replay queues its
       drop-one variants here.  They are tried only while no new list
       waits, no longer once one variant of the same list verifies, and
       not past the soft deadline: a variant is not a proof a prover
       found, and each can cost two preplay timeouts, so the variants of
       a list would keep the call going for as long as there are lemmas. *)
    val retries = ref ([] : retry list)
    val recovered = ref ([] : string list)
    (* stopping: the run ends and reconstruction with it (MaxProofs, the
       caller's interrupt, end_run).  halted: the provers are killed and no
       prover starts (the same stops, and the hard deadline, which does not
       end the reconstruction of the proofs found). *)
    val stopping = ref false
    val halted = ref false
    (* When every worker had finished (see signal). *)
    val search_ended = ref (NONE : Time.time option)
    val reason = ref (NONE : stop_reason option)
    val running = ref ([] : (int * bool ref * (unit -> unit)) list)
    val next_running = ref 0
    val worker_count = Int.min (#cores options, schedule_length)
    val workers_left = ref 0
    val launch_done = ref false
    val recon_done = ref false
    val recon_thread = ref (NONE : Thread.thread option)
    (* The slices not yet claimed, in schedule order. *)
    val work = ref scheduled_paths
    (* Every thread forked by the caller, to be joined before it returns. *)
    val threads = ref ([] : Thread.thread list)
    val launch_point = !hhSchedule_Test.launch_point
    val before_claim = !hhSchedule_Test.before_claim

    fun signal () =
      ((if Option.isSome (!search_ended) orelse not (!launch_done)
           orelse !workers_left > 0 then ()
        else search_ended := SOME (Time.now ()));
       ConditionVar.broadcast state_changed)

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

    (* The next slice, until the soft deadline. *)
    fun get_work () =
      with_mutex state_mutex (fn () =>
        if !stopping orelse not (time_before (Time.now ()) deadline) then NONE
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
        if !stopping orelse !halted then NONE
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

    fun interrupt_recon () =
      Option.app (fn t => Thread.interrupt t handle Thread _ => ())
        (!recon_thread)

    (* Kills the provers.  A final stop (SOME reason) also ends the run and
       drops the queued proofs; the halt of the hard deadline (NONE) leaves
       reconstruction to finish them, and is done once. *)
    fun stop_search final =
      let
        val kills = with_mutex state_mutex (fn () =>
          if !halted andalso not (Option.isSome final) then []
          else
            let
              val _ =
                case final of
                    SOME stop_reason =>
                      (case !reason of
                           NONE => reason := SOME stop_reason
                         | SOME _ => ();
                       stopping := true;
                       recon := [])
                  | NONE => ()
              val kills =
                map (fn (_, cancelled, kill) =>
                  (cancelled := true; kill)) (!running)
              val _ = halted := true
              val _ = work := []
              val _ = signal ()
            in
              kills
            end)
      in
        List.app (fn kill =>
          (kill () handle Interrupt => raise Interrupt | _ => ())) kills
      end

    fun kill_all stop_reason = stop_search (SOME stop_reason)

    (* The run ends with no reason of its own (Exhausted or Timeout, by
       when the search ended): the proofs still queued are dropped and the
       provers killed.  The reconstruction that calls it is the last. *)
    fun end_run () =
      (with_mutex state_mutex (fn () =>
         (stopping := true; recon := []; signal ()));
       stop_search NONE)

    (* A stop that also cancels the replays. *)
    fun stop_hard stop_reason =
      (kill_all stop_reason; interrupt_recon ())

    fun cache_key config request =
      case hhProver.probe config of
          NONE => NONE
        | SOME {path, version, ...} =>
            let
              val (_, argv) = #mk_command config path request
            in
              SOME (hhCache.key_of_digest (problem_digest (#problem request))
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

    fun run_slice ((config, slice), path) =
      let
        val now = Time.now ()
        val remaining = Time.toReal (Time.- (hard_deadline, now))
        val wanted = hhSlice.slice_budget schedule_length options slice
        val budget = Real.max (0.001, Real.min (wanted, remaining))
        val request : hhProver.run_request =
          {timeout = Real.ceil budget,
           problem = path, extra = #extra_opts slice,
           debug_dir = #debug_dir options}
        val _ = emit (SliceStarted slice)
        val key = if #cache options then cache_key config request else NONE
        val cached = Option.mapPartial (hhCache.lookup options) key
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
                            Option.app
                              (fn key => hhCache.store options key result) key
                        in
                          result
                        end
                end
      in
        note_result slice (Option.isSome cached) result
      end

    fun worker_loop () =
      (before_claim (fn () => with_mutex state_mutex (fn () => !stopping));
       case get_work () of
           NONE => ()
         | SOME item =>
             ((run_slice item
               handle Interrupt => ()
                    | error => (warn "slice" error handle _ => ()));
              worker_loop ()))

    fun worker () =
      ((worker_loop () handle _ => ()); worker_finished ())

    (* The search is over: every worker is finished (the mutex is held). *)
    fun search_finished_locked () = !launch_done andalso !workers_left = 0

    (* Everything has stopped, reconstruction included (the mutex is
       held). *)
    fun finished_locked () = search_finished_locked () andalso !recon_done

    (* Now is past the soft deadline and a proof has verified: such a
       run is ended at the deadline (the mutex is held). *)
    fun past_soft_with_proof_locked now =
      not (null (!suggestions)) andalso not (time_before now deadline)

    fun take_success () =
      let
        (* Past the soft deadline a verified proof ends the run: nothing
           more is taken.  This covers the moment between the deadline
           and await's end_run: a reconstruction failing in that window
           would otherwise start the next queued list, costing seconds. *)
        fun wait () =
          if !stopping then NONE
          else if past_soft_with_proof_locked (Time.now ()) then NONE
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

    fun reconstruct origin (slice, lemmas, t_prover) =
      let
        val key = lemma_key lemmas
        val skip = with_mutex state_mutex (fn () =>
          Lib.mem key (!tried_keys) orelse
          (tried_keys := key :: !tried_keys; false))
        fun queue_variants () =
          if #preplay_drop_one options andalso length lemmas > 1 then
            let
              val variants = map (fn variant =>
                {origin = key, success = (slice, variant, t_prover)})
                (drop_one_variants lemmas)
            in
              with_mutex state_mutex (fn () => retries := !retries @ variants)
            end
          else ()
      in
        if skip then ()
        else
          ((let
              (* Nothing interrupts this reconstruction but the caller's
                 interrupt: a proof a prover found is
                 reconstructed until it verifies or fails, in about two
                 preplay timeouts (the list, then without its permutative
                 equations), the minimisation, which stops at the soft
                 deadline and keeps the shortest verified list, and the
                 final replay. *)
              val ({stac, tac, t_replay}, t_recon) =
                add_time
                  (reconstruct_with
                    {minimize = #minimize options,
                     preplay_timeout = #preplay_timeout options,
                     minimize_timeout = #minimize_timeout options,
                     minimize_deadline = SOME deadline}
                    lemmas goal)
                  context
              val suggestion : suggestion =
                {stac = stac, tac = tac, lemmas = lemmas,
                 prover = #prover slice, slice = slice,
                 t_prover = t_prover, t_recon = t_recon,
                 t_replay = t_replay}
              (* max_proofs proofs end the run whenever reached; past the
                 soft deadline one verified proof (this one, or an earlier
                 one) ends it. *)
              val (reached, late) = with_mutex state_mutex (fn () =>
                (suggestions := suggestion :: !suggestions;
                 Option.app (fn parent => recovered := parent :: !recovered)
                   origin;
                 (length (!suggestions) >= max_proofs,
                  past_soft_with_proof_locked (Time.now ()))))
              val _ = emit (Verified suggestion)
            in
              if reached then kill_all MaxProofs
              else if late then end_run ()
              else ()
            end)
           handle Interrupt => raise Interrupt
                | error =>
                    (* A list Metis cannot replay fails with HOL_ERR, which
                       is expected and only an event (none for a variant);
                       any other exception is a bug and is reported. *)
                    ((case error of
                          HOL_ERR _ => ()
                        | _ => warn "reconstruction" error);
                     if Option.isSome origin then ()
                     else
                       (emit (ReplayFailed (slice, lemmas));
                        queue_variants ())))
      end

    fun recon_loop () =
      case take_success () of
          NONE => ()
        | SOME (Fresh success) => (reconstruct NONE success; recon_loop ())
        | SOME (Retry {origin, success = (slice, variant, t_prover)}) =>
            (if with_mutex state_mutex
                (fn () => Lib.mem origin (!recovered)) then ()
             else reconstruct (SOME origin) (slice, variant (), t_prover);
             recon_loop ())

    fun reconstruction_worker () =
      ((recon_loop () handle _ => ());
       with_mutex state_mutex (fn () => (recon_done := true; signal ())))

    fun completed () = with_mutex state_mutex finished_locked

    (* A proof has verified, now is past the soft deadline and the run has
       not been ended. *)
    fun verified_pending_end now =
      with_mutex state_mutex (fn () =>
        not (!stopping) andalso past_soft_with_proof_locked now)

    (* Waits for the run to finish.  The hard deadline kills the provers
       that are left, and the wait goes on until the reconstruction has
       finished the proofs found: no deadline ends it.  A stop does
       (MaxProofs, the caller's interrupt), and so does a verified proof
       once the soft deadline has passed, one verified before it included:
       the run is then ended at the deadline. *)
    fun await () =
      if completed () then ()
      else
        let
          val now = Time.now ()
          val soft = time_before now deadline
          val hard = time_before now hard_deadline
          val _ = if hard then () else stop_search NONE
          val _ = if verified_pending_end now then end_run () else ()
          val wake = Time.+ (now, Time.fromMilliseconds 100)
          val wake = if soft then time_min deadline wake
                     else if hard then time_min hard_deadline wake
                     else wake
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
             join_all ())) ()
        val interrupted =
          ((launch (); false)
           handle Interrupt =>
             (interrupt (); true)
                | error => (interrupt (); raise error))
        val _ = join_all ()
        val stopped =
          if interrupted then Interrupted
          else
            case !reason of
                SOME value => value
              | NONE =>
                  (case !search_ended of
                       SOME ended =>
                         if time_before ended deadline then Exhausted
                         else Timeout
                     | NONE => Timeout)
      in
        finish stopped
      end
  end

(* A caller with access to the root can edit published problems from
   its progress callback.  Those runs hash the file for each request. *)
val run_in = run_with_root false

fun run_under parent request =
  let val options = #options request in
    with_problem_dir parent options
      (fn root =>
        (root, run_with_root (not (isSome (#debug_dir options))) root request))
  end

fun run request =
  #2 (run_under (join (hhConfig.state_dir ()) "problems") request)

end
