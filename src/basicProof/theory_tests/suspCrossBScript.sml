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

(* The suspended form still lives in the ancestor theory, untouched. *)
val _ =
  let val th = DB.fetch "suspCrossA" "cross_thm"
      val susp_names = boolLib.get_suspended_names th
  in
    if length susp_names = 2 then ()
    else raise Fail ("Ancestor suspended theorem unexpectedly modified: [" ^
                     String.concatWith "," susp_names ^ "]")
  end

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
