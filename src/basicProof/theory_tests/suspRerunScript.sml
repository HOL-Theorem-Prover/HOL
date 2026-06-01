(*  Rerunnable Resume test (issue #1881).

    In the pure suspend/resume design, Resume no longer mutates the
    suspended parent theorem; it just saves a fresh resumption proof.
    Running the same Resume block twice should succeed and leave the
    theory in a state where Finalise still produces the expected
    clean theorem.
*)

Theory suspRerun[bare]

Libs HolKernel Parse boolLib markerLib

Theorem rr_thm:
  p ∧ (p ⇒ q) ⇒ p ∧ q
Proof
  strip_tac >> conj_tac
  >- suspend "p"
  >- suspend "q"
QED

Resume rr_thm[p]:
  ASM_REWRITE_TAC[]
QED

(* Re-run the same Resume.  Under the pure design, this just re-saves
   the resumption proof (rebind allowed); the parent theorem remains
   the original suspended form. *)
Resume rr_thm[p]:
  ASM_REWRITE_TAC[]
QED

Resume rr_thm[q]:
  RES_TAC
QED

Resume rr_thm[q]:
  RES_TAC
QED

Finalise rr_thm

val _ =
  let val th = DB.fetch "-" "rr_thm"
      val susp_names = boolLib.get_suspended_names th
  in
    if null susp_names then ()
    else raise Fail ("Finalised theorem still has suspended hypotheses: [" ^
                     String.concatWith "," susp_names ^ "]")
  end

val _ =
  let val th = DB.fetch "-" "rr_thm"
  in
    if aconv (concl th) “p ∧ (p ⇒ q) ⇒ p ∧ q” then ()
    else raise Fail ("Unexpected conclusion of finalised rr_thm: " ^
                     Parse.term_to_string (concl th))
  end
