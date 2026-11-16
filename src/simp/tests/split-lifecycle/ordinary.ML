(* Loaded only after ordinary libraries. Check full kernel theorem shape. *)
val ordinary_p = mk_var ("ordinary_p",bool);
val ordinary_tm = boolSyntax.mk_conj (boolSyntax.T,ordinary_p);
val ordinary_th = simpLib.SIMP_CONV boolSimps.bool_ss [] ordinary_tm;
val _ = check "ordinary proof after namespace changes"
  (null (hyp ordinary_th) andalso
   aconv (concl ordinary_th) (boolSyntax.mk_eq (ordinary_tm,ordinary_p)));
