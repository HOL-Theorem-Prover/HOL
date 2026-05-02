Theory exclArithBug
Ancestors
  hol

open testutils

(* The first three Theorem blocks exercise the Theorem ... Proof[...] ... QED
   parser surface; the inline tests below exercise the underlying
   exclude_ssfrags / SF / ++ semantics via mk_tacmod. *)

Theorem works:
  10n < x ==> 6 < x
Proof
  simp[]
QED

Theorem test = EQT_ELIM (numLib.ARITH_CONV “10n < x ==> 6 < x”)

(* Original bug: the body's UNCHANGED leaked out, so this proof failed. *)
Theorem should_work:
  10n < x ==> 6 < x
Proof[exclude_frags = ARITH]
  numLib.ARITH_TAC
QED

local
  val arith_goal : goal = ([], “10n < x ==> 6 < x”)
  fun under_excl tac =
      let val {tacm, ...} = BasicProvers.mk_tacmod "[exclude_frags = ARITH]"
      in tacm tac end
  (* turn "tactic returned a non-empty subgoal list" into an exception so
     shouldfail can express "this proof attempt should not solve". *)
  exception NotSolved
  fun must_solve tac g =
      case tac g of
          ([], _) => ()
        | _      => raise NotSolved
  fun solved (Exn.Res (sgs, _)) = List.null sgs
    | solved (Exn.Exn _)        = false
  val printresult_solved = fn () => "(unexpectedly solved)"
in

val _ = shouldfail {
          printarg   = fn _ => "exclude_frags = ARITH disables simp[]",
          testfn     = must_solve (under_excl (bossLib.simp [])),
          printresult = printresult_solved,
          checkexn   = fn _ => true
        } arith_goal

val _ = tprint "simp[SF ARITH_ss] overrides exclude_frags = ARITH"
val _ = require_msg
          solved
          (fn _ => "(failed to solve despite SF override)")
          (under_excl (bossLib.simp [simpLib.SF numSimps.ARITH_ss]))
          arith_goal

val _ = let open simpLib in
  shouldfail {
    printarg = fn _ => "naked ++ ARITH_ss inside body is blocked by exclusion",
    testfn = must_solve
               (under_excl
                  (fn g => SIMP_TAC
                             (BasicProvers.srw_ss() ++ numSimps.ARITH_ss) [] g)),
    printresult = printresult_solved,
    checkexn = fn _ => true
  } arith_goal
end

end
