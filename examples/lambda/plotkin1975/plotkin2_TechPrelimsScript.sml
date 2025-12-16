Theory plotkin2_TechPrelims

(* A translation of “Call-by-name, Call-by-value and the λ-Calculus” by
   Gordon Plotkin, Theoretical Computer Science 1 (1975), pp125–159.
   North Holland

   Section 2 "Technical Preliminaries": the base lambda calculus is already
   mechanised in the "cterm" theory, so we only need the notion of value.
*)

Ancestors
  cterm

(* p127: “A term is a *value* iff it is not a combination” *)
Definition is_value_def:
  is_value ct ⇔ ∀M N. ct ≠ M @@ N
End

Theorem is_value_thm[simp]:
  is_value (VAR s) ∧
  is_value (LAM v M) ∧
  is_value (CONST c) ∧
  ¬is_value (M @@ N)
Proof
  simp[is_value_def]
QED

Overload closed = “λct. cFV ct = {}”
