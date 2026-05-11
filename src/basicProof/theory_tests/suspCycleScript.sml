Theory suspCycle[bare]

(* Regression test for GitHub issue #1960.

   If a Resume proof depends on the parent theorem's own
   suspendlabel hypotheses (e.g. via `cj 1 useful` where `useful`
   is the still-suspended parent), the resulting resumption
   theorem re-introduces those hypotheses every time PROVE_HYP
   discharges them, so Finalise's assembly loop never converges.

   Reproduced from the issue:

     Theorem useful:
       (x ==> T) /\ (F ==> T)
     Proof
       conj_tac >- suspend "x" >> suspend "F"
     QED
     Resume useful[x]:
       strip_tac >> ACCEPT_TAC TRUTH
     QED
     Resume useful[F]:
       MATCH_ACCEPT_TAC (cj 1 useful)
     QED
     Finalise useful

   Used to spin forever inside finalise_suspended_thm; now
   `resume` rejects the cyclic proof up-front. *)

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
        fnm = "resume" andalso String.isSubstring "cycle" msg)
} ()
