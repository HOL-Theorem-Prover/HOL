Theory suspCrossThm[bare]

(* Demonstrates the cross-theorem Resume-dependency limitation
   tracked at GitHub issue #1963.

   A Resume proof for th1 is allowed to depend on another, still
   suspended theorem th2: the cycle check from #1960 is scoped
   to the current parent's slabs, so th2's slab does not match.
   Finalise th1, however, cannot resolve the foreign slab because
   find_res_for keys lookups on the current parent's name.

   This test pins down the current behaviour: Resume th1[l1]
   succeeds, Finalise th2 succeeds, and Finalise th1 then raises
   a HOL_ERR "No resumption proof found ..." rather than looping
   (the failure mode #1960 used to exhibit). *)

Libs HolKernel Parse boolLib markerLib testutils

Theorem th1:
  p ==> T
Proof
  suspend "l1"
QED

Theorem th2:
  q ==> T
Proof
  suspend "l2"
QED

(* th2 is still suspended at this point; the resume-time check
   accepts this proof because slab_th2_l2 differs from any of
   th1's slabs. *)
Resume th1[l1]:
  MATCH_ACCEPT_TAC th2
QED

Resume th2[l2]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

Finalise th2

val _ = shouldfail {
  testfn = (fn () =>
              finalise_suspended_thm (DB_dtype.mkloc(#(FILE),#(LINE),true))
                                     "th1"),
  printarg = (fn _ => "Finalise th1 (cross-theorem dependency on th2)"),
  printresult = (fn _ => "<unexpected success>"),
  checkexn =
    check_HOL_ERRexn (fn (_, fnm, msg) =>
        fnm = "Finalise" andalso String.isSubstring "No resumption" msg)
} ()
