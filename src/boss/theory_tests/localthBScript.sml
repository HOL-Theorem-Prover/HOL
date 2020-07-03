open HolKernel Parse boolLib bossLib;

open localthATheory
val _ = new_theory "localthB";

Theorem foo_bar = SIMP_CONV (srw_ss()) [] ``foo = bar``

val _ = if aconv (rhs (concl foo_bar)) “3 = bar” then ()
        else raise Fail ("Incorrect simplification produced: " ^
                         term_to_string (rhs (concl foo_bar)))

val _ = export_theory();
