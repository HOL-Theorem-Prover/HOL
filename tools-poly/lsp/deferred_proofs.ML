(* tools-poly/lsp/deferred_proofs.ML

   The LSP's prover hook: what happens when a Script.sml being
   elaborated for the LSP reaches a tactic proof.

   Default behaviour is the historical one -- don't run the tactic,
   return an oracle-tagged theorem for the goal, so a compile pass costs
   elaboration only.  With `LSPExtension.deferProofs` set, the goal,
   tactic and context are additionally enqueued as a deferred proof, so
   the work can be replayed afterwards rather than discarded.  That is
   Phase A of the replay described in
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
end = struct

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

fun prover ctxt (g, tac) =
    if isReplaying () then
      (* Reached from inside a replay: this call needs a real theorem.
         Returning an oracle here would let the outer proof succeed on a
         fabricated lemma -- the tag would make that detectable, but the
         pass/fail verdict reported for the outer proof would be wrong.
         TAC_PROOF_in is the unhooked entry, so this does not recurse. *)
      Tactical.TAC_PROOF_in ctxt (g, tac)
    else if !LSPExtension.deferProofs then
      (* current_thm_name is meaningful here -- elaboration, one thread,
         set immediately before the proof.  A replaying worker must not
         consult it, which is why it is read now and carried in the
         item. *)
      (LSPExtension.enqueueDeferred
         {site = boolLib.current_thm_name (),
          run = fn () =>
                   ((asReplay
                       (fn () => Tactical.TAC_PROOF_in ctxt (g, tac));
                     NONE)
                    handle e => SOME (Feedback.exn_to_string e))};
       Thm.mk_oracle_thm "lsp_deferred" g)
    else
      Thm.mk_oracle_thm "lsp_compile_skip" g

fun install () = Tactical.set_prover prover

end;

val () = DeferredProofs.install ();
