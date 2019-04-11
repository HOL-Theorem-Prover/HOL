open HolKernel Parse boolLib bossLib;

open delsimps1Theory

val _ = new_theory "delsimps2";

Theorem silly:
  ~(0 < foo x) ==> (x ** 2 = y ** 2)
Proof
  (* exported definition of foo should turn antecedent into ~(0 < x * 2 + 1);
     disch then rewrites this using theorem; fs shows this to be false
    - - -
     if delsimps hasn't worked, or has interacted badly with export of foo_def,
     then the ~(0 < x) will get applied too early and/or fs won't solve it.
  *)
  simp_tac (srw_ss()) [] >>
  disch_then
    (ASSUME_TAC o CONV_RULE (REWR_CONV arithmeticTheory.NOT_LT_ZERO_EQ_ZERO)) >>
  full_simp_tac (srw_ss()) []
QED

val _ =
    case Exn.capture (SIMP_CONV (srw_ss()) []) ``~(0 < x)`` of
        Exn.Res th => raise Fail "SIMP_CONV shouldn't have completed"
      | Exn.Exn Conv.UNCHANGED => ()
      | Exn.Exn e => raise Fail ("Unexpected exception: "^General.exnMessage e)

val _ = export_theory();
