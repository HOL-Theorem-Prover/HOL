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

  (* Hand the queued proofs to the pool, given the byte the pass that
     produced them re-elaborated from.  Returns at once: the proofs run
     on worker threads.

     A proof already being checked is not started again.  Re-elaborating
     a declaration re-enqueues its proofs whether or not anything about
     it changed, so without this an edit anywhere above would throw away
     work in progress everywhere below.  See `sameProof`. *)
  val check : int -> unit
  (* Only ever reports Checking, Proved or Failed.  A proof the pool is
     not working on is absent, which the caller renders as Cheated. *)
  val statuses : unit -> LSPExtension.proof_state list
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
   having no name to match on (see `sameProof'), so each recompile
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

val entries : entry list Sref.t = Sref.new []

fun setWorkerCount n = Multithreading.max_threads_update n

(* Every change to what the pool is doing is announced by the thread that
   causes it, and nothing samples the whole set.  Sampling cannot be made
   correct: `statuses ()` is read, and only then sent, so a worker that
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

fun forkAt (item as {site, offset, run} : LSPExtension.deferred) =
    let
      val group = Future.new_group NONE
      val params = {name = "lsp_proof:" ^ site, group = SOME group,
                    deps = [], pri = 0, interrupts = true}
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
      announce {site = site, offset = offset,
                status = LSPExtension.Checking};
      case Future.forks params [announcing] of
          [f] => SOME {site = site, offset = offset, item = itemR,
                       group = group, result = result, future = f}
        | _ => NONE
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
fun sameProof (it : LSPExtension.deferred) (e : entry) =
    itemSite it = siteOf e

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

fun check resumeFrom =
    let
      (* takeDeferred empties the queue, so a second call cannot fork
         the same proof twice *)
      val items = LSPExtension.takeDeferred ()
      (* Decide under the lock, so a concurrent cancellation cannot be
         lost, and fork afterwards -- forking while holding it would
         serialise the pool behind this. *)
      val (fresh, doomed, moved) =
          Sref.gen_update entries
            (fn live =>
                let
                  val (reused, fresh) =
                      List.partition
                        (fn it => List.exists (sameProof it) live) items
                  fun reusedOffset e =
                      case List.find (fn it => sameProof it e) reused of
                          SOME {offset, ...} => SOME offset
                        | NONE => NONE
                  (* An entry survives if this pass re-enqueued its proof
                     -- with its offset refreshed, since the edit may
                     have moved the declaration -- or if it sits above
                     what was re-elaborated and so was never in
                     question.  Anything else the pass has orphaned. *)
                  fun classify (e : entry) =
                      case reusedOffset e of
                          SOME off =>
                            SOME {site = #site e, offset = off,
                                  item = #item e, group = #group e,
                                  result = #result e, future = #future e}
                        | NONE =>
                          if offsetOf e < resumeFrom then SOME e else NONE
                  val classified = List.map (fn e => (e, classify e)) live
                  val keep = List.mapPartial #2 classified
                  val doomed =
                      List.mapPartial (fn (e, NONE) => SOME e | _ => NONE)
                                      classified
                  (* A reused entry whose declaration the edit moved.
                     Its offset is how a client finds the proof, and
                     nothing else will tell it the declaration is
                     somewhere else now: a reused entry is not dropped
                     and not forked, so it announces nothing of its
                     own. *)
                  val moved =
                      List.mapPartial
                        (fn (e, SOME e') =>
                            if offsetOf e' = offsetOf e then NONE
                            else SOME e'
                          | _ => NONE) classified
                in
                  (keep, (fresh, doomed, moved))
                end)
      val () = List.app (fn {group, ...} => Future.cancel_group group) doomed
      val () = List.app dropped doomed
      val () = List.app (fn e => announceEntry (statusOf e) e) moved
      val new = List.mapPartial forkAt fresh
    in
      Sref.update entries (fn es => es @ new)
    end

fun statuses () =
    List.map (fn (e as {site, offset, ...} : entry) =>
                 {site = site, offset = offset, status = statusOf e})
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
    in
      (* cancel after removing: an interrupted worker needs its group
         cancelled whether or not we still track it *)
      List.app (fn {group, ...} => Future.cancel_group group) doomed;
      List.app dropped doomed
    end

fun cancelAtOrAfter off = cancelIf (fn off' => off' >= off)
fun cancelAt off = cancelIf (fn off' => off' = off)
fun cancelAll () = cancelIf (fn _ => true)

end;

val () = DeferredProofs.install ();
val () = LSPExtension.checkDeferred := DeferredProofs.check;
val () = LSPExtension.proofStates := DeferredProofs.statuses;
val () = LSPExtension.cancelProofsAtOrAfter := DeferredProofs.cancelAtOrAfter;
val () = LSPExtension.cancelProofAt := DeferredProofs.cancelAt;
val () = LSPExtension.cancelAllProofs := DeferredProofs.cancelAll;
