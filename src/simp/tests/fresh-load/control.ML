(* Compiled only AFTER the explicit dynamic load. Not a launcher import. *)
val fresh_control_p = Term.mk_var ("fresh_control_p", Type.bool)
val fresh_control_tm = boolSyntax.mk_conj (boolSyntax.T, fresh_control_p)
val fresh_control_th =
  simpLib.SIMP_CONV boolSimps.bool_ss [] fresh_control_tm
val _ = testutils.tprint "ordinary simplification after dynamic load"
val _ =
  if null (Thm.hyp fresh_control_th) andalso
     Term.aconv (Thm.concl fresh_control_th)
       (boolSyntax.mk_eq (fresh_control_tm, fresh_control_p))
  then testutils.OK ()
  else testutils.die "ordinary simplification theorem mismatch"
val _ = print "OBS control.theorem=expected equality; hypotheses=[]\n"
