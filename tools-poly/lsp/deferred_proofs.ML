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
  (* true while this thread is replaying a deferred proof *)
  val isReplaying : unit -> bool

  (* Hand the queued proofs to the pool.  Returns at once: the proofs
     run on worker threads. *)
  val check : unit -> unit
  (* Only ever reports Checking, Proved or Failed.  A proof the pool is
     not working on is absent, which the caller renders as Cheated. *)
  val statuses : unit -> LSPExtension.proof_state list
  (* The declaration the user is working on, by byte offset, or NONE.
     Its proof is held back rather than checked -- the goal-state walker
     is already replaying that tactic on every keystroke, so a worker
     doing it too is duplicated effort -- and is checked, at raised
     priority, once the user moves on. *)
  val setFocus : int option -> unit
  (* Give up on every proof whose declaration starts at or after this
     byte; proofs above it are untouched.  Called with the point a
     compile is about to resume from, since everything from there on is
     re-elaborated and enqueued again. *)
  val cancelAtOrAfter : int -> unit
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

(* Did the real proof produce the theorem elaboration stood in for?
   The placeholder was `mk_oracle_thm _ g`, whose hypotheses are exactly
   the goal's assumptions.  Anything extra means the proof suspended
   subgoals (a marker$suspendlabel hypothesis apiece), which makes the
   theorem a different value from the one every later declaration was
   elaborated against. *)
fun extraHyps (asl, _) th =
    let
      val goalAsms = HOLset.addList (Term.empty_tmset, asl)
    in
      List.filter (fn h => not (HOLset.member (goalAsms, h))) (Thm.hyp th)
    end

(* What a proved theorem says about the placeholder elaboration stood in
   for.  A suspension is the expected reason for extra hypotheses and
   gets its own status, because it calls for a different response: the
   proof is fine and the elaboration below it is not.  Anything else is a
   bare divergence. *)
fun verdict g th =
    case extraHyps g th of
        [] => LSPExtension.Proved
      | extra =>
        if boolLib.has_suspended_subgoals th then
          LSPExtension.Suspended
            (String.concatWith ", " (boolLib.get_suspended_names th))
        else
          LSPExtension.Diverged
            (Int.toString (length extra) ^ " extra hypothes" ^
             (if length extra = 1 then "is" else "es"))

fun replay ctxt g tac =
    verdict g (asReplay (fn () => Tactical.TAC_PROOF_in ctxt (g, tac)))
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
fun proveForReal ctxt (g, tac) =
    let
      val th = asReplay (fn () => Tactical.TAC_PROOF_in ctxt (g, tac))
      val st = verdict g th
      val site = boolLib.current_thm_name ()
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

fun prover ctxt (g, tac) =
    if isReplaying () then
      (* Reached from inside a replay: this call needs a real theorem.
         Returning an oracle here would let the outer proof succeed on a
         fabricated lemma -- the tag would make that detectable, but the
         pass/fail verdict reported for the outer proof would be wrong.
         TAC_PROOF_in is the unhooked entry, so this does not recurse. *)
      Tactical.TAC_PROOF_in ctxt (g, tac)
    else if LSPExtension.isNoCheatSite (boolLib.current_thm_name ()) then
      proveForReal ctxt (g, tac)
    else if !LSPExtension.deferProofs andalso
            not (!LSPExtension.cheatSubstituted) then
      (* current_thm_name and currentProofOffset are meaningful here --
         elaboration, one thread, both set immediately before the proof.
         A replaying worker must not consult either, which is why they
         are read now and carried in the item. *)
      (LSPExtension.enqueueDeferred
         {site = boolLib.current_thm_name (),
          offset = !LSPExtension.currentProofOffset,
          run = fn () => replay ctxt g tac};
       Thm.mk_oracle_thm "lsp_deferred" g)
    else
      Thm.mk_oracle_thm "lsp_compile_skip" g

fun install () = Tactical.set_prover prover

(* ------------------------------------------------------------------
   Phase B: the worker pool

   Future is Isabelle's task framework: a pool bounded by
   Multithreading.max_threads, with per-group cancellation that
   interrupts a running thread rather than only dropping a queued task.
   That is what makes a proof cancellable mid-tactic, which matters
   because a proof can run far longer than the edit that invalidated it.

   One group per proof, so each can be cancelled on its own.  We keep
   the future to read its outcome and the offset to decide whether an
   edit reaches it.
   ------------------------------------------------------------------ *)

(* `site` and `offset` live here rather than being read back out of the
   item, because the item does not outlive the proof.  Its closure pins a
   Context snapshot, and a settled proof is never forked again, so the
   worker clears `item` on the way out and only the reporting fields
   remain.  While a proof is unsettled the item is kept, so a proof taken
   off a worker -- because the user has started editing it -- can be
   forked again without re-elaborating it.

   `result` is what the replay decided, recorded by the worker itself.
   Future.peek is not enough: the announcement has to happen from inside
   the task, and at that point the future is not yet fulfilled, so peek
   still says NONE and every report would read `Checking`.

   Both refs are written by the one worker and read by whoever is
   reporting, and each holds an immutable value, so the worst a racing
   reader sees is the previous one -- and another announcement follows. *)
type entry = {site : string,
              offset : int,
              item : LSPExtension.deferred option ref,
              group : Future.group,
              result : LSPExtension.proof_status option ref,
              future : LSPExtension.proof_status Future.future}

fun offsetOf ({offset, ...} : entry) = offset
fun isSettled ({result, ...} : entry) = isSome (!result)

val entries : entry list Sref.t = Sref.new []
(* Elaborated and queued, but deliberately not being checked: the
   declaration the user is working on.  Invisible to `statuses`, so it
   reads as Cheated, which is what it is. *)
val held : LSPExtension.deferred list Sref.t = Sref.new []
val focus : int option Sref.t = Sref.new NONE

fun setWorkerCount n = Multithreading.max_threads_update n

(* Above the default of 0 so a just-abandoned proof is picked up ahead of
   the backlog, but well below Task_Queue's urgent_pri, which bypasses
   the normal ready-job path and would let a stream of these starve
   everything else. *)
val resumed_pri = 100

fun forkAt pri (item as {site, offset, run} : LSPExtension.deferred) =
    let
      val group = Future.new_group NONE
      val params = {name = "lsp_proof:" ^ site, group = SOME group,
                    deps = [], pri = pri, interrupts = true}
      val result = ref NONE
      val itemR = ref (SOME item)
      (* Announce the new state on the worker that settled it, so the
         caller need not poll.  Record it and drop the item first, for
         the reasons given at `entry`.  An interrupt is not announced:
         whoever cancelled already knows, and the entry is gone. *)
      fun announcing () =
          let
            val r = run ()
          in
            result := SOME r;
            itemR := NONE;
            !LSPExtension.proofStateChanged
              {site = site, offset = offset, status = r};
            r
          end
    in
      case Future.forks params [announcing] of
          [f] => SOME {site = site, offset = offset, item = itemR,
                       group = group, result = result, future = f}
        | _ => NONE
    end

fun isFocused off =
    case Sref.value focus of SOME f => f = off | NONE => false

fun check () =
    let
      (* takeDeferred empties the queue, so a second call cannot fork
         the same proof twice *)
      val items = LSPExtension.takeDeferred ()
      val (focused, rest) =
          List.partition (fn ({offset, ...} : LSPExtension.deferred) =>
                             isFocused offset) items
      val new = List.mapPartial (forkAt 0) rest
    in
      Sref.update held (fn hs => hs @ focused);
      Sref.update entries (fn es => es @ new)
    end

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

fun statuses () =
    List.map (fn (e as {site, offset, ...} : entry) =>
                 {site = site, offset = offset, status = statusOf e})
             (Sref.value entries)

(* One shape for both entry points: take the doomed entries out under the
   lock, cancel them, and drop the held items the same predicate
   condemns.  `gen_update` rather than a read followed by a blind write,
   so a worker announcing an outcome concurrently cannot have its change
   discarded.  One predicate, so the two lists cannot disagree about what
   an edit reached. *)
fun cancelIf doomed_at =
    let
      val doomed =
          Sref.gen_update entries
            (fn es => let val (d, k) = List.partition (doomed_at o offsetOf) es
                      in (k, d) end)
    in
      (* cancel after removing: an interrupted worker needs its group
         cancelled whether or not we still track it *)
      List.app (fn {group, ...} => Future.cancel_group group) doomed;
      (* a held proof the edit reached is stale too, and re-elaboration
         will queue it again *)
      Sref.update held
        (List.filter (fn ({offset, ...} : LSPExtension.deferred) =>
                         not (doomed_at offset)))
    end

fun cancelAtOrAfter off = cancelIf (fn off' => off' >= off)
fun cancelAll () = cancelIf (fn _ => true)

fun setFocus off =
    let
      val () = Sref.update focus (fn _ => off)
      fun nowFocusedAt off' = case off of SOME f => off' = f | NONE => false
      (* Stop checking whatever the user has just started editing: the
         walker is replaying that tactic anyway.  Keep the item so it can
         be forked again when they move on.  A proof that has already
         settled stays put: there is nothing to cancel, and its verdict
         is worth more than a re-check. *)
      val nowFocused =
          Sref.gen_update entries
            (fn es =>
                let
                  val (d, k) =
                      List.partition
                        (fn e => nowFocusedAt (offsetOf e) andalso
                                 not (isSettled e))
                        es
                in (k, d) end)
      val () = List.app (fn {group, ...} => Future.cancel_group group)
                        nowFocused
      (* Anything held that is no longer the focus can be checked, and
         should be: the user has just stopped working on it. *)
      val release =
          Sref.gen_update held
            (fn hs =>
                let
                  val hs = hs @ List.mapPartial (fn {item, ...} => !item)
                                                nowFocused
                  val (r, stay) =
                      List.partition
                        (fn ({offset, ...} : LSPExtension.deferred) =>
                            not (nowFocusedAt offset)) hs
                in (stay, r) end)
      val resumed = List.mapPartial (forkAt resumed_pri) release
    in
      Sref.update entries (fn es => es @ resumed)
    end

end;

val () = DeferredProofs.install ();
val () = LSPExtension.checkDeferred := DeferredProofs.check;
val () = LSPExtension.proofStates := DeferredProofs.statuses;
val () = LSPExtension.cancelProofsAtOrAfter := DeferredProofs.cancelAtOrAfter;
val () = LSPExtension.cancelAllProofs := DeferredProofs.cancelAll;
val () = LSPExtension.setProofFocus := DeferredProofs.setFocus;
