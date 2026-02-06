Theory eval_poly
Ancestors
  arithmetic list
Libs
  HOL_to_ACL2

(*---------------------------------------------------------------------------*)
(* A polynomial is a list of pairs (constant, exponent), sorted by           *)
(* decreasing order of exponent.  Example:                                   *)
(*                                                                           *)
(*  [(3,2); (5,0)] stands for 3x^2 + 5x^0 = 3x^2 + 5                         *)
(*---------------------------------------------------------------------------*)

Definition polyp_def:
 polyp [] = T /\
 polyp ((c,e)::r) = (polyp r /\ c <> 0 /\ (NULL r \/ SND(HD r) < e))
End

(*---------------------------------------------------------------------------*)
(* Evaluate the polynomial for x having the value v.  Example:               *)
(*                                                                           *)
(*  ⊢ eval_poly [(3,2); (5,0)] 4 = 53: thm                                   *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition eval_poly_def:
  eval_poly [] v = 0 ∧
  eval_poly ((c,e)::r) v = c * (v ** e) + eval_poly r v
End

(*---------------------------------------------------------------------------*)
(* Polynomial addition. Evaluating the sum of two polynomials is equal to    *)
(* the sum of evaluating the polynomials.                                    *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*  ⊢ sum_polys [(3,2); (5,0)]                                               *)
(*              [(4,2); (3,1); (2,0)] = [(7,2); (3,1); (7,0)]: thm           *)
(*                                                                           *)
(*  ⊢ eval_poly [(3,2); (5,0)] 4 = 53: thm                                   *)
(*  ⊢ eval_poly [(4,2); (3,1); (2,0)] 4 = 78: thm                            *)
(*                                                                           *)
(*  ⊢ eval_poly                                                              *)
(*      (sum_polys [(3,2); (5,0)] [(4,2); (3,1); (2,0)]) 4 = 131: thm        *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition sum_polys_def:
  sum_polys [] p = p ∧
  sum_polys p [] = p ∧
  sum_polys ((c1,e1)::r1) ((c2,e2)::r2) =
     if e1 = e2 then
        (c1+c2,e1)::sum_polys r1 r2 else
     if e1 < e2 then
       (c2,e2)::sum_polys ((c1,e1)::r1) r2
     else
       (c1,e1)::sum_polys r1 ((c2,e2)::r2)
End

(*---------------------------------------------------------------------------*)
(* Distributive property                                                     *)
(*---------------------------------------------------------------------------*)

Theorem eval_poly_sum_polys:
 ∀x y v.
    polyp x ∧ polyp y
     ⇒
    eval_poly (sum_polys x y) v
     =
    eval_poly x v + eval_poly y v
Proof
  recInduct sum_polys_ind >> rw[] >>
  gvs [eval_poly_def,sum_polys_def] >>
  `polyp r1 /\ polyp r2` by
     (Cases_on ‘r1’ >>
      Cases_on ‘r2’ >> gvs [polyp_def]) >>
  gvs[] >> rw[] >> gvs[eval_poly_def]
QED

(*---------------------------------------------------------------------------*)
(* Turns out the well-formedness condition isn't needed.                     *)
(*---------------------------------------------------------------------------*)

Theorem eval_poly_sum_polys_again:
 ∀x y v.
    eval_poly (sum_polys x y) v
     =
    eval_poly x v + eval_poly y v
Proof
  recInduct sum_polys_ind >> rw[] >>
  gvs [eval_poly_def,sum_polys_def] >>
  rw[] >> gvs[eval_poly_def]
QED

(*---------------------------------------------------------------------------*)
(* Make defhol forms for sending to ACL2. We send the proved theorem as a    *)
(* goal to be proved in ACL2(zfc)                                            *)
(*---------------------------------------------------------------------------*)

val defs = basis_defs @ [EXP, polyp_def, eval_poly_def, sum_polys_def];

val goals =
    [mk_named_goal "eval_sum_poly_distrib" (concl eval_poly_sum_polys)]

val _ = print_defhols_to_file "eval_poly.defhol" (defs @ goals);
