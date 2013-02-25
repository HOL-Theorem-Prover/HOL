open HolKernel Parse
open Defn

open testutils

fun test msg f x =
    (tprint msg;
     f x handle _ => die "FAILED!";
     print "OK\n")

val _ = print "\n"

val def1 = test "Defn with IFF" (Hol_defn "foo") `foo p <=> p /\ F`;

(* check parsability of quantified equation *)
val _ = test "Parse quantified eqn" Defn.parse_absyn (Absyn`∀x. bar x = foo x`)

val x_def = new_definition("x_def", ``x = \y. F``)

val def3 = test "Constant as parameter (=)" (Hol_defn "baz1") `baz1 x = x /\ F`
val def4 =
    test "Constant as parameter (<=>)" (Hol_defn "baz2") `baz2 x <=> x /\ F`
val def5 =
    test "Type-constrainted constant as parameter"
         (Hol_defn "baz3") `baz3 (x:bool) <=> x /\ F`
val _ =
    test "Constant as parameter under quantifier"
         Defn.parse_absyn (Absyn`!y. baz4 x y = x /\ y`)

val def6 = test "Case expression with multiple underscores"
                (Hol_defn "f1")
                `(f1 x y = case (x, y) of (T, _) => T | (_,_) => F)`
val def7 = test "Case expression with underscores of different types"
                (Hol_defn "f2")
                `(f2 x y = case (x, y) of (T, _) => T | _ => F)`

val def8 = test "Case expression with variables of different types"
                (Hol_defn "f3")
                `f3 x = case x of (f,T,_) => ~f | (_,F,f) => f F`;
