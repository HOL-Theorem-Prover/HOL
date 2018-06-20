open HolKernel Parse boolLib

open Datatype

val _ = new_theory "inheritCase1";

val _ = Datatype`list = Nil | Cons 'a list`;

val _ = export_theory();
