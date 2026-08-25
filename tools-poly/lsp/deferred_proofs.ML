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
     byte.  Proofs above the offset are untouched.  For an edit that
     elaboration will consume -- a statement, a definition -- since that
     can change any declaration below it. *)
  val cancelAtOrAfter : int -> unit
  (* Give up on just this declaration's proof.  For an edit *inside* a
     Proof...QED body: what a theorem contributes downstream is its
     statement, and the tactic is not run during the cheating pass, so
     editing the tactic leaves every later declaration untouched.  That
     is the case worth being precise about, because it is what someone
     iterating on a proof does all day. *)
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

fun asReplay f =
    let
      val saved = isReplaying ()
      val () = ThreadLocal.set (replaying, true)
      fun restore () = ThreadLocal.set (replaying, saved)
    in
      (f () before restore ()) handle e => (restore (); raise e)
    end

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

fun replay ctxt g tac =
    (case asReplay (fn () => Tactical.TAC_PROOF_in ctxt (g, tac)) of
         th =>
         case extraHyps g th of
             [] => LSPExtension.Proved
           | extra =>
             LSPExtension.Diverged
               (Int.toString (length extra) ^
                " extra hypothes" ^ (if length extra = 1 then "is" else "es") ^
                (if boolLib.has_suspended_subgoals th then
                   " (suspended subgoals: " ^
                   String.concatWith ", " (boolLib.get_suspended_names th) ^ ")"
                 else "")))
    handle e => LSPExtension.Failed (Feedback.exn_to_string e)

fun prover ctxt (g, tac) =
    if isReplaying () then
      (* Reached from inside a replay: this call needs a real theorem.
         Returning an oracle here would let the outer proof succeed on a
         fabricated lemma -- the tag would make that detectable, but the
         pass/fail verdict reported for the outer proof would be wrong.
         TAC_PROOF_in is the unhooked entry, so this does not recurse. *)
      Tactical.TAC_PROOF_in ctxt (g, tac)
    else if !LSPExtension.deferProofs then
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

(* The item is kept alongside the future so a proof taken off a worker
   -- because the user has started editing it -- can be forked again
   later without re-elaborating it. *)
type entry = {item : LSPExtension.deferred,
              group : Future.group,
              future : LSPExtension.proof_status Future.future}

fun offsetOf ({item = {offset, ...}, ...} : entry) = offset

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

fun forkAt pri (item as {site, offset = _, run} : LSPExtension.deferred) =
    let
      val group = Future.new_group NONE
      val params = {name = "lsp_proof:" ^ site, group = SOME group,
                    deps = [], pri = pri, interrupts = true}
    in
      case Future.forks params [run] of
          [f] => SOME {item = item, group = group, future = f}
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

fun statusOf ({future, ...} : entry) =
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
    List.map (fn e =>
                 let val {item = {site, offset, ...}, ...} = e
                 in {site = site, offset = offset, status = statusOf e} end)
             (Sref.value entries)

fun cancelAtOrAfter off =
    let
      val (doomed, kept) =
          List.partition (fn e => offsetOf e >= off) (Sref.value entries)
    in
      (* cancel first, then forget: an interrupted worker needs its group
         cancelled whether or not we still track it *)
      List.app (fn {group, ...} => Future.cancel_group group) doomed;
      Sref.update entries (fn _ => kept);
      (* held proofs below the edit are stale too, and re-elaboration
         will queue them again *)
      Sref.update held
        (List.filter (fn ({offset, ...} : LSPExtension.deferred) =>
                         offset < off))
    end

fun cancelAt off =
    let
      val (doomed, kept) =
          List.partition (fn e => offsetOf e = off) (Sref.value entries)
    in
      List.app (fn {group, ...} => Future.cancel_group group) doomed;
      Sref.update entries (fn _ => kept);
      Sref.update held
        (List.filter (fn ({offset, ...} : LSPExtension.deferred) =>
                         offset <> off))
    end

fun cancelAll () =
    (List.app (fn {group, ...} => Future.cancel_group group)
              (Sref.value entries);
     Sref.update entries (fn _ => []);
     Sref.update held (fn _ => []))

fun setFocus off =
    let
      val () = Sref.update focus (fn _ => off)
      (* Stop checking whatever the user has just started editing: the
         walker is replaying that tactic anyway.  Keep the item so it can
         be forked again when they move on. *)
      val (nowFocused, keep) =
          List.partition (fn e => case off of
                                      SOME f => offsetOf e = f
                                    | NONE => false)
                         (Sref.value entries)
      val () = List.app (fn {group, ...} => Future.cancel_group group)
                        nowFocused
      val () = Sref.update entries (fn _ => keep)
      val () = Sref.update held
                 (fn hs => hs @ List.map #item nowFocused)
      (* Anything held that is no longer the focus can be checked, and
         should be: the user has just stopped working on it. *)
      val (release, stayHeld) =
          List.partition (fn ({offset, ...} : LSPExtension.deferred) =>
                             not (isFocused offset))
                         (Sref.value held)
      val resumed = List.mapPartial (forkAt resumed_pri) release
    in
      Sref.update held (fn _ => stayHeld);
      Sref.update entries (fn es => es @ resumed)
    end

end;

val () = DeferredProofs.install ();
val () = LSPExtension.checkDeferred := DeferredProofs.check;
val () = LSPExtension.proofStates := DeferredProofs.statuses;
val () = LSPExtension.cancelProofsAtOrAfter := DeferredProofs.cancelAtOrAfter;
val () = LSPExtension.cancelAllProofs := DeferredProofs.cancelAll;
val () = LSPExtension.setProofFocus := DeferredProofs.setFocus;
val () = LSPExtension.cancelProofAt := DeferredProofs.cancelAt;
