(*  Cross-file suspend/resume test, part 1 of 2.

    This theory suspends a theorem with two labels; the downstream
    theory suspCrossB resumes both labels and finalises the result.
    See issue #1883.
*)

Theory suspCrossA[bare]

Libs HolKernel Parse boolLib markerLib

Theorem cross_thm:
  p ∧ (p ⇒ q) ⇒ p ∧ q
Proof
  strip_tac >> conj_tac
  >- suspend "p"
  >- suspend "q"
QED

(* Confirm that the suspended theorem has been saved as an exported
   theorem in this theory's segment, with both suspendlabel hypotheses
   intact. *)
val _ =
  let
    val th = DB.fetch "-" "cross_thm"
    val susp_names = boolLib.get_suspended_names th
  in
    if List.all (fn n => List.exists (fn m => m = n) ["p","q"]) susp_names
       andalso length susp_names = 2
    then ()
    else raise Fail ("Unexpected suspended hypothesis set: [" ^
                     String.concatWith "," susp_names ^ "]")
  end
