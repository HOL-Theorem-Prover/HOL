open HolKernel Parse boolLib bossLib;

val _ = new_theory "delsimps1";

val foo_def = Define‘foo x = x * 2 + 1’;
val _ = export_rewrites ["foo_def"]

val _ = delsimps ["NOT_LT_ZERO_EQ_ZERO"]

val _ =
    case Exn.capture (SIMP_CONV (srw_ss()) []) ``~(0 < x)`` of
        Exn.Res th => raise Fail "SIMP_CONV shouldn't have completed"
      | Exn.Exn Conv.UNCHANGED => ()
      | Exn.Exn e => raise Fail ("Unexpected exception: "^General.exnMessage e)

val _ = export_theory();
