(*  Sibling-finalise suspend/resume test, part 4 of 4.

    Inherits both sibling resumption proofs (from suspSibB and
    suspSibC) and finalises the parent theorem suspSibA$sib_thm.  The
    resumption proofs live in *ancestor* theories, so Finalise must
    look past the current theory segment.
*)

Theory suspSibD[bare]
Ancestors suspSibB suspSibC

Libs HolKernel Parse boolLib markerLib

Finalise sib_thm

(* The suspended form still lives unmodified in suspSibA. *)
val _ =
  let val th = DB.fetch "suspSibA" "sib_thm"
      val susp_names = boolLib.get_suspended_names th
  in
    if length susp_names = 2 then ()
    else raise Fail ("Ancestor suspended theorem unexpectedly modified: [" ^
                     String.concatWith "," susp_names ^ "]")
  end

val _ =
  let val th = DB.fetch "-" "sib_thm"
      val susp_names = boolLib.get_suspended_names th
  in
    if null susp_names then ()
    else raise Fail ("Finalised theorem still has suspended hypotheses: [" ^
                     String.concatWith "," susp_names ^ "]")
  end

val _ =
  let val th = DB.fetch "-" "sib_thm"
  in
    if aconv (concl th) “p ∧ (p ⇒ q) ⇒ p ∧ q” then ()
    else raise Fail ("Unexpected conclusion of finalised sib_thm: " ^
                     Parse.term_to_string (concl th))
  end
