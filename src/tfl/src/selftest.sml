open HolKernel Parse
open Defn

val def1 = Hol_defn "foo" `foo p <=> p /\ F`;

(* check parsability of quantified equation *)
val _ = Defn.parse_absyn(Absyn`∀x. bar x = foo x`)

val x_def = new_definition("x_def", ``x = \y. F``)

val def3 = Hol_defn "baz1" `baz1 x = x /\ F`
val def4 = Hol_defn "baz2" `baz2 x <=> x /\ F`
val def5 = Hol_defn "baz3" `baz3 (x:bool) <=> x /\ F`
val _ = Defn.parse_absyn(Absyn`!y. baz4 x y = x /\ y`)


