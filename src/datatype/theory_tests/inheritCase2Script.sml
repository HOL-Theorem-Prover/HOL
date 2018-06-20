open HolKernel Parse boolLib

open inheritCase1Theory
val _ = new_theory "inheritCase2";
val _ = set_grammar_ancestry ["inheritCase1"]

val _ = current_backend := PPBackEnd.raw_terminal
val _ = new_constant("len", ``:'a list -> num``)
val s = PP.pp_to_string 70 pp_term
           ``case x of Nil => 0 | Cons h t => h + len t``

val _ = assert (equal "case x of Nil => 0 | Cons h t => h + len t") s

val _ = export_theory();
