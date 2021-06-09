open HolKernel Parse boolLib bossLib;
open foobarLib;

open ATheory BTheory;

val _ = new_theory "C";

Theorem bar_foo:
  bar (foo a) = a
Proof
  simp (foobar_thms())
QED

val _ = export_theory ()
