Theory suspCycle[bare]

(* Regression test for #1960: a resumption body that cites its own
   parent (e.g. `MATCH_ACCEPT_TAC (cj 1 useful)`) would otherwise
   re-introduce the parent's suspendlabel hyps at every PROVE_HYP, so
   Finalise's assembly loop diverges.  `resume` now rejects this at
   recording time; the same check also covers cross-theorem citation
   (see suspCrossThm). *)

Libs HolKernel Parse boolLib markerLib testutils

Theorem useful:
  (x ==> T) /\ (F ==> T)
Proof
  conj_tac >- suspend "x" >> suspend "F"
QED

Resume useful[x]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

val _ = shouldfail {
  testfn = (fn () =>
              resume {suspension_name = "useful", label_name = "F"}
                     (MATCH_ACCEPT_TAC (cj 1 useful))),
  printarg = (fn _ =>
              "resume useful[F] with MATCH_ACCEPT_TAC (cj 1 useful)"),
  printresult = (fn _ => "<unexpected success>"),
  checkexn =
    check_HOL_ERRexn (fn (_, fnm, msg) =>
        fnm = "resume" andalso String.isSubstring "still-suspended" msg)
} ()
