(* tools-poly/lsp/deferred_proofs.ML

   The LSP's prover hook and the worker pool that replays what it
   defers.

   Default behaviour is the historical one -- don't run the tactic,
   return an oracle-tagged theorem for the goal, so a compile pass costs
   elaboration only.  With `LSPExtension.deferProofs` set, the goal,
   tactic and context are additionally enqueued, so the work can be
   replayed afterwards rather than discarded.  That is Phase A of the
   replay described in
   developers/discussion/context-passing-tactics.md; an item is
   self-contained because the context is an immutable value and the
   tactic has already been elaborated.

   Loaded by tools-poly/hol.ML's LSP runtime init, at a point where the
   heap is up, so this can be ordinary type-checked SML rather than a
   string handed to the compiler. *)

structure DeferredProofs :> sig
  (* installed at load time; exposed for tests and for restoring the
     hook after something else has replaced it *)
  val install : unit -> unit

  (* Hand the queued proofs to the pool, given the byte the pass that
     produced them re-elaborated from.  Returns at once: the proofs run
     on worker threads.

     A proof already being checked is not started again.  Re-elaborating
     a declaration re-enqueues its proofs whether or not anything about
     it changed, so without this an edit anywhere above would throw away
     work in progress everywhere below.  See `itemSite`. *)
  val check : LSPExtension.check_scope -> unit
  (* Whether any proof the pool holds is still being checked.  Read
     without taking the pool's lock, which is what lets it be called
     from inside one -- `check`'s `Checking` announcement reaches the
     server hook, which asks this. *)
  val anyChecking : unit -> bool
  (* Give up on every proof whose declaration starts at or after this
     byte; proofs above it are untouched.  Called with the point a
     compile is about to resume from, since everything from there on is
     re-elaborated and enqueued again. *)
  val cancelAtOrAfter : int -> unit
  (* Give up on just this declaration's proofs.  For an edit inside a
     `Proof ... QED` body, which leaves every later declaration's
     obligation untouched. *)
  val cancelAt : int -> unit
  val cancelAll : unit -> unit
  (* How many workers the pool may use.  0 asks for one per processor,
     which Multithreading caps at 8. *)
  val setWorkerCount : int -> unit
end = struct

(* ------------------------------------------------------------------
   Phase A: the prover hook
   ------------------------------------------------------------------ *)

(* Replay must not re-enter the deferring branch.  Per-thread rather
   than a global flag: with a worker pool, one worker replaying must not
   switch deferral off for another thread that is still elaborating.
   ThreadLocal.get is NONE on a fresh thread, which reads as "not
   replaying" -- the right default for a thread that has only ever
   elaborated. *)
val replaying : bool ThreadLocal.t = ThreadLocal.new ()

fun isReplaying () =
    case ThreadLocal.get replaying of SOME b => b | NONE => false

val replayFlag = {get = isReplaying,
                  set = fn b => ThreadLocal.set (replaying, b)}
fun asReplay f = Portable.genwith_flag (replayFlag, true) f ()

(* How a proof is named, here and on the wire.  The name is the only
   identity that survives re-elaboration: an edit above a proof moves
   it, so the offset identifies nothing for longer than one pass.  A
   name can occur twice, though -- `Theorem foo' and a later
   `Theorem foo[allow_rebind]' -- so it is paired with the occurrence
   number the compile driver read off the buffer, and the first
   occurrence is left unadorned: `foo' and `foo#2'. *)
fun qualify nm ord =
    if nm = "" orelse ord <= 1 then nm else nm ^ "#" ^ Int.toString ord

fun proofName ctxt =
    qualify (boolLib.current_thm_name ctxt) (!LSPExtension.currentProofOrd)

(* Did the real proof produce the theorem elaboration stood in for?
   The placeholder was `mk_oracle_thm _ g`, whose hypotheses are exactly
   the goal's assumptions.  Anything extra means the proof suspended
   subgoals (a marker$suspendlabel hypothesis apiece), which makes the
   theorem a different value from the one every later declaration was
   elaborated against. *)
fun extraHyps (asl, _) th =
    HOLset.difference (Thm.hypset th,
                       HOLset.addList (Term.empty_tmset, asl))

(* What a proved theorem says about the placeholder elaboration stood in
   for.  A suspension is the expected reason for extra hypotheses and
   gets its own status, because it calls for a different response: the
   proof is fine and the elaboration below it is not.  Anything else is a
   bare divergence. *)
fun verdict g th =
    let val extra = HOLset.numItems (extraHyps g th) in
      if extra = 0 then LSPExtension.Proved
      else if boolLib.has_suspended_subgoals th then
        LSPExtension.Suspended
          (String.concatWith ", " (boolLib.get_suspended_names th))
      else
        LSPExtension.Diverged
          (Int.toString extra ^ " extra hypothes" ^
           (if extra = 1 then "is" else "es"))
    end

(* `Context.with_context` for the whole replay, not just
   `TAC_PROOF_in`'s parameter.  The parameter covers a tactic that uses
   the context it was handed; this covers the rest, and the rest is not
   sloppiness -- `mk_const` and `mk_type` resolve names against the live
   signature by design, so a replaying proof reads the live cell every
   time it builds a term from a name.  That cell belongs to whichever
   compile is in progress, and a pass resuming part-way down the file
   rewinds it: the worker then cannot find a constant its own file
   defines and reports a sound proof as failed, differently on each
   keystroke.  Pinned here, the rewind is invisible to it. *)
fun replay ctxt g tac =
    Context.with_context ctxt
      (fn () =>
          verdict g (asReplay (fn () =>
                                  Tactical.TAC_PROOF_in ctxt (g, tac))))
      ()
    handle e =>
           if Exn.is_interrupt e then Exn.reraise e
           else LSPExtension.Failed (Feedback.exn_to_string e)

(* The checker found this proof suspends, so elaboration cannot stand in
   `mk_oracle_thm g` for it and still be right about what the
   declarations below see: a real build stashes such a theorem rather
   than saving it.  Run it here, synchronously.  Only proofs already
   known to suspend pay this.

   It is still handed to the pool, with its verdict already decided, so
   the reported state does not vanish the moment we stop cheating it.
   `asReplay` so a nested `prove` takes the replaying branch below rather
   than coming back through here under the same name. *)
fun proveForReal ctxt site (g, tac) =
    let
      val th = asReplay (fn () => Tactical.TAC_PROOF_in ctxt (g, tac))
      val st = verdict g th
    in
      (* No longer suspends -- the user has changed the proof, so stop
         paying to run it during elaboration. *)
      (case st of
           LSPExtension.Proved => LSPExtension.dropNoCheatSite site
         | _ => ());
      LSPExtension.enqueueDeferred
        {site = site,
         offset = !LSPExtension.currentProofOffset,
         run = fn () => st};
      th
    end

(* A proof with no name is not one the user wrote.  The definition
   principle justifies itself with tactic proofs -- pattern coverage,
   automatic termination -- and those appear nowhere in the script: a
   file of 61 theorems was reporting 65 proofs, the extra four being
   obligations of four `Definition's that have no `Termination' clause
   and no proof to look at.  Naming them after their declaration only
   made them look like proofs the reader had written.

   They are also the entries the pool could never reuse across passes,
   having no name to match on (see `itemSite'), so each recompile
   dropped them and forked them again, announcing a `Cheated' at the
   offset the declaration used to start at.  A client accumulating the
   stream gained a phantom entry per anonymous proof per recompile,
   which is what made the tally climb -- 65 became 68 -- when
   whitespace was added to a tactic.

   So run them here, during elaboration, as a build would.  They are
   part of the declaration succeeding rather than proofs in their own
   right: one that fails belongs in that declaration's error, not in a
   tally of the user's proofs. *)
fun prover ctxt (g, tac) = let
  val site = proofName ctxt
in
    if isReplaying () then
      (* Reached from inside a replay: this call needs a real theorem.
         Returning an oracle here would let the outer proof succeed on a
         fabricated lemma -- the tag would make that detectable, but the
         pass/fail verdict reported for the outer proof would be wrong.
         TAC_PROOF_in is the unhooked entry, so this does not recurse. *)
      Tactical.TAC_PROOF_in ctxt (g, tac)
    else if LSPExtension.isNoCheatSite site then
      proveForReal ctxt site (g, tac)
    else if !LSPExtension.deferProofs andalso
            not (!LSPExtension.cheatSubstituted) then
      if site = "" then Tactical.TAC_PROOF_in ctxt (g, tac)
      else
        (* currentProofOffset is still ambient -- elaboration is one
           thread, and it is set immediately before the proof -- and a
           replaying worker must not consult it, which is why it is
           read now and carried in the item. *)
        (LSPExtension.enqueueDeferred
           {site = site,
            offset = !LSPExtension.currentProofOffset,
            run = fn () => replay ctxt g tac};
         Thm.mk_oracle_thm "lsp_deferred" g)
    else
      Thm.mk_oracle_thm "lsp_compile_skip" g
end

fun install () = Tactical.set_prover prover

(* ------------------------------------------------------------------
   Phase B: the worker pool

   Future is Isabelle's task framework: a pool bounded by
   Multithreading.max_threads, with per-group cancellation that
   interrupts a running thread rather than only dropping a queued task.
   That is what makes a proof cancellable mid-tactic, which matters
   because a proof can run far longer than the edit that invalidated it.

   One group per proof, so each can be cancelled on its own.  The group
   need not be kept: `Future.cancel` recovers it from the future, which
   `forks` enqueued under it.  We keep the future to read its outcome
   and the offset to decide whether an edit reaches it.
   ------------------------------------------------------------------ *)

(* `site` and `offset` live here rather than being read back out of the
   item, because the item does not outlive the proof: its closure pins a
   Context snapshot, and an entry that held one would keep that snapshot
   for as long as the file stays open.  Nothing re-forks a taken-off
   proof -- the next pass re-elaborates and re-enqueues it -- so the
   entry keeps only what reporting needs.

   `result` is what the replay decided, recorded by the worker itself.
   Future.peek is not enough: the announcement has to happen from inside
   the task, and at that point the future is not yet fulfilled, so peek
   still says NONE and every report would read `Checking`.

   Both refs are written by the one worker and read by whoever is
   reporting, and each holds an immutable value, so the worst a racing
   reader sees is the previous one -- and another announcement follows. *)
type entry = {site : string,
              offset : int,
              result : LSPExtension.proof_status option ref,
              future : LSPExtension.proof_status Future.future}

fun offsetOf ({offset, ...} : entry) = offset

val entries : entry list Sref.t = Sref.new []

fun setWorkerCount n = Multithreading.max_threads_update n

(* Every change to what the pool is doing is announced by the thread that
   causes it, and nothing samples the whole set.  Sampling cannot be made
   correct: the set is read, and only then sent, so a worker that
   settles in between has its newer verdict overwritten by the older
   sample.  Announcing transitions has no such window, and per proof the
   order is guaranteed -- `Checking` is sent before the task is forked,
   and a verdict only after it runs.

   Dropping an entry is announced as `Cheated`, which is what absence
   from the pool means: the proof is taken on trust again.  A worker
   interrupted by the cancellation stays silent, so it cannot contradict
   this afterwards. *)
fun announce st = !LSPExtension.proofStateChanged st

fun announceEntry status (e : entry) =
    announce {site = #site e, offset = #offset e, status = status}

fun dropped e = announceEntry LSPExtension.Cheated e

(* Cancel after removing from `entries`: an interrupted worker needs its
   group cancelled whether or not we still track it, and a caller that
   cancelled first would leave a window in which the entry is live but
   its future is already dead. *)
fun discard (doomed : entry list) =
    (List.app (Future.cancel o #future) doomed;
     List.app dropped doomed)

fun forkAt ({site, offset, run} : LSPExtension.deferred) =
    let
      val group = Future.new_group NONE
      val params = {name = "lsp_proof:" ^ site, group = SOME group,
                    deps = [], pri = 0, interrupts = true}
      val result = ref NONE
      (* Announce the new state on the worker that settled it, so the
         caller need not poll, recording it first for the reasons given
         at `entry`.  An interrupt is not announced: whoever cancelled
         already knows, and the entry is gone. *)
      fun announcing () =
          let
            val r = run ()
          in
            result := SOME r;
            announce {site = site, offset = offset, status = r};
            r
          end
    in
      {site = site, offset = offset, result = result,
       future = Portable.singleton (Future.forks params) announcing}
    end

fun siteOf ({site, ...} : entry) = site
fun itemSite ({site, ...} : LSPExtension.deferred) = site

(* Is a newly enqueued proof the one a live entry is already checking?

   Reuse needs an identity that survives re-elaboration, and the offset
   is not one: an insertion moves every declaration below it.  The name
   is, now that `prove_named' gives one to every route into the prover
   that has one to give -- paired with the occurrence number, so a
   rebound name still names one proof each.

   The occurrence number is counted from the start of the file, which a
   resumed pass can do without re-reading what it skipped: the entries
   above its resume point survive the pass untouched, so their numbers
   are already assigned and this pass's items carry on from there. *)
fun statusOf ({future, result, ...} : entry) =
    case !result of
        SOME st => st
      | NONE =>
    case Future.peek future of
        NONE => LSPExtension.Checking
      (* the replay reports its own status *)
      | SOME (Exn.Res st) => st
      | SOME (Exn.Exn e) =>
        (* A cancelled proof is back to being taken on trust, which is
           what the user saw before we started checking it.  Anything
           else that escaped is a failure. *)
        if Exn.is_interrupt e then LSPExtension.Cheated
        else LSPExtension.Failed (Feedback.exn_to_string e)

fun check {resumeFrom, keptFrom, bytes} =
    let
      (* takeDeferred empties the queue in one step, so a second call
         cannot fork the same proof twice.  A worker never adds to it --
         it takes `prover`'s replaying branch -- but the server's
         goal-state and walk threads run tactics too, and they are not
         replaying, so the queue is synchronised rather than relying on
         a single writer. *)
      val items = LSPExtension.takeDeferred ()
      (* Built before the lock is taken, since it touches nothing
         shared: an item and an entry match on site and nothing else, so a
         dictionary answers in one lookup what a scan of every item, per
         entry, used to answer.  On a 61-theorem script that was some
         7,400 string comparisons inside the critical section. *)
      val itemOffset =
          List.foldl (fn (it, m) => Binarymap.insert (m, itemSite it,
                                                      #offset it))
                     (Binarymap.mkDict String.compare) items
      (* Read without the lock: `entries` only grows by this function,
         which runs on one compile thread at a time, and a canceller
         removing an entry meanwhile can only make us announce a
         `Checking` that is then immediately dropped as `Cheated`. *)
      val liveNow =
          List.foldl (fn (e, st) => Binaryset.add (st, siteOf e))
                     (Binaryset.empty String.compare) (Sref.value entries)
      fun isLive it = Binaryset.member (liveNow, itemSite it)
      (* Announced before the lock, deliberately.  An announcement goes
         down a one-slot channel and blocks until the writer thread has
         written the previous one to stdout, so doing this per proof
         inside the critical section would hold the pool's lock for as
         long as the *client* takes to read -- and the thread that wants
         it next is the one reading LSP input, which is how a slow
         editor turns into a server that has stopped listening.

         Announcing early is sound: a cancellation arriving in the gap
         announces `Cheated` after this `Checking`, which is the order
         the drop path produces anyway. *)
      val () = List.app (fn it => announce {site = itemSite it,
                                            offset = #offset it,
                                            status = LSPExtension.Checking})
                        (List.filter (fn it => not (isLive it)) items)
      (* One critical section, covering the forking too.  Publishing the
         new entries in a second one left them invisible to a canceller
         for as long as forking took: an edit arriving in that window
         could not stop the proofs of the text it had just replaced, so
         they ran on, filled the pool, and announced verdicts against a
         buffer the user had already changed.  Forking here is only an
         enqueue -- `Future.forks` does not run the proof, and takes no
         lock of ours. *)
      val (doomed, moved) =
          Sref.gen_update entries
            (fn live =>
                let
                  val liveSites =
                      List.foldl (fn (e, st) => Binaryset.add (st, siteOf e))
                                 (Binaryset.empty String.compare) live
                  val fresh =
                      List.filter
                        (fn it => not (Binaryset.member (liveSites,
                                                         itemSite it)))
                        items

                  (* An entry survives if this pass re-enqueued its proof
                     -- with its offset refreshed, since the edit may
                     have moved the declaration -- or if it sits above
                     what was re-elaborated and so was never in
                     question.  Anything else the pass has orphaned. *)
                  fun moveTo off (e : entry) =
                      {site = #site e, offset = off,
                       result = #result e, future = #future e}
                  (* A pass that stopped early did not re-enqueue what
                     it never reached, but those are still the right
                     proofs: keep them, moved to where the edit has put
                     them.  Orphaning them instead dropped every proof
                     below an edited tactic. *)
                  fun keptBelow (e : entry) =
                      case keptFrom of
                          SOME b => if offsetOf e >= b
                                    then SOME (moveTo (offsetOf e + bytes) e)
                                    else NONE
                        | NONE => NONE
                  fun classify (e : entry) =
                      case Binarymap.peek (itemOffset, siteOf e) of
                          SOME off => SOME (moveTo off e)
                        | NONE =>
                          if offsetOf e < resumeFrom then SOME e
                          else keptBelow e
                  (* One pass, three answers.  `moved` is a reused entry
                     whose declaration the edit shifted: its offset is
                     how a client finds the proof, and nothing else will
                     say it has shifted, a reused entry being neither
                     dropped nor forked. *)
                  fun step (e, (keep, doomed, moved)) =
                      case classify e of
                          NONE => (keep, e :: doomed, moved)
                        | SOME e' =>
                          (e' :: keep, doomed,
                           if offsetOf e' = offsetOf e then moved
                           else e' :: moved)
                  val (keep, doomed, moved) =
                      List.foldr step ([], [], []) live
                in
                  (keep @ List.map forkAt fresh, (doomed, moved))
                end)
      val () = discard doomed
      val () = List.app (fn e => announceEntry (statusOf e) e) moved
    in () end

(* Short-circuits on the first unsettled proof: this is asked once per
   verdict, so a file's worth of failures used to pay a traversal -- and
   a record per entry -- apiece.  `Sref.value` takes no lock, and that
   is load-bearing rather than incidental: this is reachable from inside
   the `entries` critical section, and a locking read would deadlock on
   a non-reentrant mutex. *)
fun anyChecking () =
    List.exists (fn e => statusOf e = LSPExtension.Checking)
                (Sref.value entries)

(* One shape for both entry points: take the doomed entries out under the
   lock and cancel them.  `gen_update` rather than a read followed by a
   blind write, so a worker announcing an outcome concurrently cannot
   have its change discarded. *)
fun cancelIf doomed_at =
    let
      val doomed =
          Sref.gen_update entries
            (fn es => let val (d, k) = List.partition (doomed_at o offsetOf) es
                      in (k, d) end)
    in discard doomed end

fun cancelAtOrAfter off = cancelIf (fn off' => off' >= off)
fun cancelAt off = cancelIf (fn off' => off' = off)
fun cancelAll () = cancelIf (fn _ => true)

end;

val () = DeferredProofs.install ();
val () = LSPExtension.checkDeferred := DeferredProofs.check;
val () = LSPExtension.poolBusy := DeferredProofs.anyChecking;
val () = LSPExtension.cancelProofsAtOrAfter := DeferredProofs.cancelAtOrAfter;
val () = LSPExtension.cancelProofAt := DeferredProofs.cancelAt;
val () = LSPExtension.cancelAllProofs := DeferredProofs.cancelAll;
