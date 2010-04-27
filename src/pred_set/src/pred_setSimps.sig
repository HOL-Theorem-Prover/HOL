signature pred_setSimps =
sig
  val SET_SPEC_ss : simpLib.ssfrag
  val PRED_SET_ss : simpLib.ssfrag
  val PRED_SET_AC_ss : simpLib.ssfrag
  val GSPEC_SIMP_CONV : Conv.conv
  val GSPEC_SIMP_ss : simpLib.ssfrag
end

(*
   [SET_SPEC_ss] contains just the conversion PGspec.SET_SPEC_CONV, which
   converts terms of the form x IN { z | ... }.

   [PRED_SET_ss] is a combination of the above with the rewrite theorems
   from pred_setTheory.pred_set_rwts.

   [PRED_SET_AC_ss] AC-normalises union and intersection terms.
*)
