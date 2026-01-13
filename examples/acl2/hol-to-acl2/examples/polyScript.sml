open HolKernel boolLib bossLib arithmeticTheory listTheory;

val _ = new_theory "poly";

(*---------------------------------------------------------------------------*)
(* A polynomial is a list of pairs (constant, exponent), sorted by           *)
(* decreasing order of exponent.  Example:                                   *)
(*                                                                           *)
(*  [(3,2); (5,0)] stands for 3x^2 + 5x^0 = 3x^2 + 5                         *)
(*---------------------------------------------------------------------------*)

Definition polyp_def:
 (polyp [] = T) /\
 (polyp [(c,e)] = (0 < c /\ 0 <= e)) /\
 (polyp ((c1,e1)::(c2,e2)::r) =
      (0 < c1 /\ 0 <= e1 /\ e2 < e1 /\ polyp ((c2,e2)::r)))
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
 sum_polys [] [] = [] ∧
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
(* Prove it in general                                                       *)
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
     (Cases_on ‘r1’ >> Cases_on ‘r2’ >>
      TRY(Cases_on ‘h’) >> TRY (Cases_on ‘h'’) >>
      gvs [polyp_def]) >>
  gvs[] >> rw[] >> gvs[eval_poly_def]
QED

(*---------------------------------------------------------------------------*)
(* Turns out the well-formedness condition isn't needed, as we originally    *)
(* thought.                                                                  *)
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
(* Preservation of polyp by sum_polys                                        *)
(*---------------------------------------------------------------------------*)

Theorem sum_polys_nil[simp]:
  sum_polys [] p = p ∧
  sum_polys p [] = p
Proof
  Cases_on ‘p’ >> rw [sum_polys_def]
QED

load "pred_setLib"; open pred_setTheory;

Overload exps_of = “set o MAP SND”

Theorem exps_of_sum_polys[simp]:
  ∀p1 p2. exps_of (sum_polys p1 p2) = exps_of p1 ∪ exps_of p2
Proof
  recInduct sum_polys_ind >> rw[] >>
  gvs [sum_polys_def] >> rw[] >>
  gvs[] >> rw [EXTENSION] >> metis_tac[]
QED

Theorem polyp_thm:
  ∀p c e.
     polyp ((c,e)::p)
      ⇔
     polyp p ∧ 0 < c ∧ ∀a. a ∈ exps_of p ⇒ a < e
Proof
  Induct >> rw[]
  >- rw[polyp_def]
  >- (Cases_on ‘h’ >> gvs [polyp_def] >>
      rw[EQ_IMP_THM] >> metis_tac [LESS_TRANS])
QED

Theorem polyp_add_coeff[simp]:
  polyp ((c,e)::t) ⇒ polyp ((c+d,e)::t)
Proof
  rw [polyp_thm]
QED

Theorem eval_poly_sum_polys:
  ∀x y. polyp x ∧ polyp y ⇒ polyp (sum_polys x y)
Proof
  recInduct sum_polys_ind >> rw[] >>
  gvs [sum_polys_def,polyp_thm] >>
  rw[polyp_thm] >> gvs[] >>
  metis_tac[LESS_TRANS,DECIDE “a = b ∨ a < b ∨ b < a”]
QED

val _ = export_theory();
