open HolKernel Parse boolLib bossLib;

open injected_strlitTheory

val _ = new_theory "injected_strlit2";

val _ = testutils.tpp "«foo bar»"                                      (* UOK *)

val _ = remove_strliteral_form {tmnm = "SINJ2"}


val _ = export_theory();
