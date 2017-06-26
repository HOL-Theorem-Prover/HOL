open HolKernel Parse boolLib bossLib;

open ATheory

val _ = new_theory "B";

val bar_def = Define`bar x = foo x * 2`;


val _ = export_theory();
