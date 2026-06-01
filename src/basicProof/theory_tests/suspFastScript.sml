(*  --fast compatibility test for suspend/resume (issue #1909).

    Holmake --fast replaces Tactical.prove's underlying prover with
    an oracle-producing shim.  That means Theorem...Proof...QED
    blocks that use the suspend tactical never actually run suspend,
    so the saved theorem has no suspendlabel hypotheses.  Resume
    detects this situation (fast_proof oracle tag on the parent) and
    short-circuits to an oracle-tagged placeholder so the overall
    build still succeeds.

    This script simulates --fast in-process by directly setting the
    prover to an oracle shim.  It then runs the exact reproduction
    from #1909 and asserts that the whole Theorem/Resume/Finalise
    sequence completes without error.
*)

Theory suspFast[bare]

Libs HolKernel Parse boolLib markerLib BasicProvers

(* Install the same oracle prover that fastbuild installs, so that
   this script file executes as though Holmake --fast were in effect.
   Under this prover, every call to Tactical.prove / prove_goal
   returns an oracle theorem of the stated goal without running the
   tactic, so suspend never inserts any suspendlabel hypotheses. *)
val _ =
  Tactical.set_prover
    (fn (g, _ : tactic) => Thm.mk_oracle_thm "fast_proof" g)

(* The tactic bodies below are never actually run (the oracle prover
   discards them), so they need only be syntactically valid SML. *)
Theorem lemma:
  p ∧ (p ⇒ q) ⇒ p ∧ q
Proof
  strip_tac >> conj_tac
  >- suspend "p"
  >- suspend "q"
QED

Resume lemma[p]:
  ASM_REWRITE_TAC[]
QED

Resume lemma[q]:
  RES_TAC
QED

Finalise lemma

(* Restore the default prover so that later code in this script (and
   any concurrent activity) sees normal behaviour.  Theory finalisation
   then runs under the normal prover. *)
val _ = Tactical.restore_prover ()

(* The saved lemma should be oracle-tagged fast_proof and have the
   conclusion from the Theorem statement. *)
val _ =
  let
    val th = DB.fetch "-" "lemma"
    val tags = #1 (Tag.dest_tag (Thm.tag th))
  in
    if not (Lib.mem "fast_proof" tags) then
      raise Fail "Finalised lemma lost its fast_proof oracle tag"
    else if not (aconv (concl th) “p ∧ (p ⇒ q) ⇒ p ∧ q”) then
      raise Fail ("Unexpected conclusion of finalised lemma: " ^
                  Parse.term_to_string (concl th))
    else ()
  end
