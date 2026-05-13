Theory suspCrossThm[bare]

(* Regression test for GitHub issue #1963.

   A Resume proof for th1 is allowed to depend on another, still
   suspended theorem th2 (the per-parent cycle check from #1960
   only rejects dependencies on the current parent's own slabs).
   Each slab is owner-stamped at save_thm_attrs time, so the
   assembly loop in Finalise can route foreign-slab lookups
   through the slab's true owner.

   This test exercises that path end to end:
   - Resume th1[l1] cites th2 (still suspended).
   - Resume th2[l2] cleanly.
   - Finalise th2 first; its clean form lands in DB.
   - Finalise th1 then discharges slab_th2_l2 via the DB-fallback
     in find_res_for, reconstructing the resumption from th2's
     clean theorem. *)

Libs HolKernel Parse boolLib markerLib

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

Resume th1[l1]:
  MATCH_ACCEPT_TAC th2
QED

Resume th2[l2]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

Finalise th2

Finalise th1
