Theory nested_zero
Ancestors
  prim_rec

(*---------------------------------------------------------------------------
     Tortuous definition of constant 0 function
  ---------------------------------------------------------------------------*)

val foo_defn =
    Hol_defn
     "foo"
     `foo x = (if x = 0 then 0 else foo (x − 1) + foo (foo (x − 1)))`;

(*---------------------------------------------------------------------------
   Instantiate and simplify the auxiliary eqns and induction theorem.
  ---------------------------------------------------------------------------*)

val [fooFn_ind, fooFn_def] =
    Defn.instantiate_aux
       foo_defn “(<)”
         (SIMP_RULE bool_ss [WF_LESS, DECIDE ``x ≠ 0 ⇒ x − 1 < x``])

Overload fooFn[local] = “foo_aux (<)”

(*---------------------------------------------------------------------------
    Semantic property
  ---------------------------------------------------------------------------*)

Theorem fooFn_zero[local]:
  ∀n. fooFn n = 0
Proof
  recInduct fooFn_ind >> rw[] >> simp [Once fooFn_def]
QED

(*---------------------------------------------------------------------------*)
(* Termination                                                               *)
(*---------------------------------------------------------------------------*)

val (def,ind) = Defn.tprove (foo_defn, WF_REL_TAC ‘$<’ >> rw [fooFn_zero])

Theorem foo_def = def;
Theorem foo_ind = ind;

Theorem fooFn_equal_foo:
  ∀n. fooFn n = foo n
Proof
  simp [fooFn_zero] >>
  recInduct foo_ind >>
  rpt strip_tac >>
  rw [Once foo_def]
QED
