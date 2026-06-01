(*  Cross-file suspend/resume test, part 2 of 2.

    Resumes both suspended labels of suspCrossA$cross_thm and finalises
    the result in this downstream theory.  See issue #1883.
*)

Theory suspCrossB[bare]
Ancestors suspCrossA

Libs HolKernel Parse boolLib markerLib

Resume cross_thm[p]:
  ASM_REWRITE_TAC[]
QED

Resume cross_thm[q]:
  RES_TAC
QED

Finalise cross_thm

(* After Finalise, the suspension store entry has been removed
   (RemoveSuspended delta), so lookup_suspension returns NONE. *)
val _ =
  case lookup_suspension "cross_thm" of
      NONE => ()
    | SOME _ => raise Fail
        "cross_thm still in suspension store after Finalise"

(* In this theory the finalised, clean form should be visible. *)
val _ =
  let val th = DB.fetch "-" "cross_thm"
      val susp_names = boolLib.get_suspended_names th
  in
    if null susp_names then ()
    else raise Fail ("Finalised theorem still has suspended hypotheses: [" ^
                     String.concatWith "," susp_names ^ "]")
  end

val _ =
  let val th = DB.fetch "-" "cross_thm"
  in
    if aconv (concl th) “p ∧ (p ⇒ q) ⇒ p ∧ q” then ()
    else raise Fail ("Unexpected conclusion of finalised cross_thm: " ^
                     Parse.term_to_string (concl th))
  end
