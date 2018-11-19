open HolKernel Parse boolLib testutils normalForms

val _ = let
  val p = mk_var("p", bool)
  val q = mk_var("q", bool)
  val v1 = genvar bool
  val v2 = genvar bool
  val t1 = mk_conj(p,q)
  val C = normalForms.PRETTIFY_VARS_CONV
  val gt1 = mk_abs(v1, mk_conj(v1, p))
  val gt2 = list_mk_abs([q, v1,v2], list_mk_conj([p,q,v1,q,v2]))
  fun test (t1,t2) = convtest ("PRETTIFY_CONV "^term_to_string t1, C, t1, t2)
in
  app test [(t1, t1), (mk_abs(p,t1), mk_abs(p,t1)),
            (v1, v1), (gt1, ``\v. v /\ p``),
            (gt2, ``\q v v0. p /\ q /\ v /\ q /\ v0``)]
end
