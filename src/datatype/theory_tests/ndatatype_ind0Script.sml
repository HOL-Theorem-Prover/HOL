open HolKernel Parse boolLib

val _ = new_theory "ndatatype_ind0";

(* set up a type (that is a copy of lists, basically), with an
   induction and cases theorems, and register this type in the TypeBase.

   Check that this type supports various forms of Induct_on and Induct.
*)

val _ = new_type ("foo", 1)

val _ = new_constant("foonil", ``:'a foo``)
val _ = new_constant("foocons", ``:'a -> 'a foo -> 'a foo``)

val foo_ind = new_axiom (
  "foo_ind",
  ``!P. P foonil /\ (!t. P t ==> !a. P (foocons a t)) ==> !x. P x``);

val foo_cases = new_axiom (
  "foo_cases",
  ``!x. (x = foonil) \/ ?a t. x = foocons a t``);

val _ = TypeBase.write [
  TypeBasePure.mk_nondatatype_info
          (``:'a foo``,
           {encode = NONE, induction = SOME foo_ind,
            nchotomy = SOME foo_cases, size = NONE})
]

val c = ref 0
fun check (tac, t) = (tac([], t) before ignore (save_thm(
  "OK" ^ Int.toString (!c) before c := !c + 1,
  TRUTH)))

open BasicProvers
val _ = map check [
  (Induct_on `t`, ``foonil <> foocons (a:'a) t``),
  (Induct_on `t`, ``!t. foonil <> foocons (a:'a) t``),
  (Induct_on `foocons a t`, ``foonil <> foocons (a:'a) t``),
  (Induct, ``!t. foonil <> foocons (a:'a) t``)
]

val _ = export_theory();
