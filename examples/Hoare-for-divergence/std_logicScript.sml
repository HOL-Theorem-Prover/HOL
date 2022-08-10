open preamble while_langTheory;

val _ = new_theory "std_logic";

(* -- inference rules for a standard total-correctness Hoare logic -- *)

Inductive Hoare:
  (∀P.
    Hoare P Skip P)
  ∧
  (∀Q n x.
    Hoare (Q o subst n x) (Assign n x) Q)
  ∧
  (∀Q x.
    Hoare (Q o print x) (Print x) Q)
  ∧
  (∀p q P M Q.
    Hoare P p M ∧ Hoare M q Q ⇒
    Hoare P (Seq p q) Q)
  ∧
  (∀x p q P Q.
    Hoare (λs. P s ∧  guard x s) p Q ∧
    Hoare (λs. P s ∧ ~guard x s) q Q ⇒
    Hoare P (If x p q) Q)
  ∧
  (∀P x p R.
    (∀s0. Hoare (λs. P s ∧ guard x s ∧ s = s0) p (λs. P s ∧ R s s0)) ∧ WF R ⇒
    Hoare P (While x p) (λs. P s ∧ ~guard x s))
  ∧
  (∀P p Q P' Q'.
    (∀s. P s ⇒ P' s) ∧ Hoare P' p Q' ∧ (∀s. Q' s ⇒ Q s) ⇒
    Hoare P p Q)
End

(* -- semantics -- *)

Definition HoareSem_def:
  HoareSem P p Q ⇔
    ∀s. P s ⇒ ∃t. terminates s p t ∧ Q t
End

val _ = export_theory();
