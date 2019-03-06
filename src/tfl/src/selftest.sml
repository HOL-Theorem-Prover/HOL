open HolKernel Parse
open Defn

open testutils

fun test msg f x = (tprint msg; f x handle _ => die "FAILED!"; OK())

val _ = print "\n"

val def1 = test "Defn with IFF" (Hol_defn "foo") `foo p <=> p /\ F`;

(* check parsability of quantified equation *)
val _ = test "Parse quantified eqn" Defn.parse_absyn (Absyn`∀x. bar x = foo x`)

val x_def = new_definition("x_def", ``x = \y. F``)

val def3 = test "Constant as parameter (=)" (Hol_defn "baz1") `baz1 x = (x /\ F)`
val def4 =
    test "Constant as parameter (<=>)" (Hol_defn "baz2") `baz2 x <=> x /\ F`
val def5 =
    test "Type-constrainted constant as parameter"
         (Hol_defn "baz3") `baz3 (x:bool) <=> x /\ F`
val _ =
    test "Constant as parameter under quantifier"
         Defn.parse_absyn (Absyn`!y. baz4 x y = (x /\ y)`)

val def6 = test "Case expression with multiple underscores"
                (Hol_defn "f1")
                `(f1 x y = case (x, y:'a) of (T, _) => T | (_,_) => F)`
val def7 = test "Case expression with underscores of different types"
                (Hol_defn "f2")
                `(f2 x y = case (x, y:'a) of (T, _) => T | _ => F)`

val def8 = test "Case expression with variables of different types"
                (Hol_defn "f3")
                `f3 x = case x of (f,T,_) => ~f | (_,F,f) => f F`;

val _ = overload_on ("=", ``T``)
val _ = test "Definition with overloaded =" (Hol_defn "f4") `f4 x y = (x /\ y)`

val _ = temp_overload_on("foo", ``bool$F``)
val _ = Hol_defn "F" `F f x <=> x \/ f x`;
val _ = tpp_expected{
  input="foo",
  output="foo",
  testf = (fn _ => "Printing after definition on unoverloaded name")
};

fun define q =
  let
    val (tm, names) = Defn.parse_absyn (Parse.Absyn q)
  in
    Defn.mk_defn (hd names) tm
  end
fun exnlookfor sl (Exn (HOL_ERR {message,...})) =
     if List.all (fn s => String.isSubstring s message) sl then OK()
     else
       die ("\nBad exception message:\n  "^message)
  | exnlookfor _ (Exn e) =
      die ("\nException not a HOL_ERR;\n  "^General.exnMessage e)
  | exnlookfor _ _ = die ("\nExecution unexpectedly successful")

fun badvarcheck r =
  exnlookfor ["Simple definition failed", "Free variables in rhs"] r

fun wfunivq r =
  exnlookfor ["Universally quantified equation as argument"] r

val _ = tprint "Excess vars on RHS of def reported correctly(=,no !)"
val _ = timed define badvarcheck `ll20180807A x = (x /\ y)`

val _ = tprint "Excess vars on RHS of def reported correctly(=,!)"
val _ = timed define badvarcheck `!x. ll20180807B x = (x /\ y)`;

val _ = tprint "Excess vars on RHS of def reported correctly(<=>,no !)"
val _ = timed define badvarcheck `ll20180807C x <=> x /\ y`;

val _ = tprint "Excess vars on RHS of def reported correctly(<=>,!)"
val _ = timed define badvarcheck `!x. ll20180807D x <=> x /\ y`;

val _ = tprint "Better message for use of q-fied eqn in wfrec def"
val _ = timed define wfunivq `!x. ll20180807E x <=> y /\ ll20180807E (x ==> y)`;
