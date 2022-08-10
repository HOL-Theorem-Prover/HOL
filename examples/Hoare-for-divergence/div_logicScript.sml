open preamble while_langTheory std_logicTheory;

val _ = new_theory "div_logic";

(* Explanation of the "Pohjola" name that's used below. I called the
   judgments of standard Floyd-Hoare logic "Hoare", which is short for
   "Hoare triple". The adaption of Hoare logic to diverging programs
   was done as a collaboration between Åman Pohjola, Rostedt and
   myself (Myreen). So I call these judgments "Pohjola", which is
   short for "Pohjola triple". *)

(* -- inference rules for a standard total-correctness Hoare logic -- *)

Definition FLAT_def:
  FLAT xs = LFLATTEN (LMAP fromList xs)
End

Definition ignores_output_def:
  ignores_output H ⇔
    ∀i s out1 out2. H i (s,out1) = H i (s,out2)
End

Inductive Pohjola:
  (∀p q P D.
    Pohjola P p D ⇒
    Pohjola P (Seq p q) D)
  ∧
  (∀p q P M D.
    Hoare P p M ∧ Pohjola M q D ⇒
    Pohjola P (Seq p q) D)
  ∧
  (∀x p q P D.
    Pohjola (λs. P s ∧  guard x s) p D ∧
    Pohjola (λs. P s ∧ ~guard x s) q D ⇒
    Pohjola P (If x p q) D)
  ∧
  (* proving that a non-terminating loop diverges *)
  (∀P x p (D: value llist -> bool).
    (∀s. P s ⇒
         ∃H ev.
           guard x s ∧ H 0 s ∧ ignores_output H ∧
           D (FLAT (output_of s ::: fromSeq ev)) ∧
           ∀i. Hoare (λs. H i s ∧ output_of s = []) p
                     (λs. H (i+1) s ∧ output_of s = ev i ∧ guard x s)) ⇒
    Pohjola P (While x p) D)
  ∧
  (* proving that the ith execution of the body of a loop causes
     something within the body to diverge *)
  (∀P x p R b.
    (∀s. P s ⇒ guard x s) ∧ WF R ∧
    (∀s0. Hoare (λs. P s ∧ b s ∧ s = s0) p (λs. P s ∧ R s s0)) ∧
    Pohjola (λs. P s ∧ ~b s) p D ⇒
    Pohjola P (While x p) D)
  ∧
  (* the next rule might seem pointless, but it is necessary for
     completeness *)
  (∀p D.
    Pohjola (λs. F) p D)
  ∧
  (∀P p D b.
    Pohjola (λs. P s ∧ b s) p D ∧
    Pohjola (λs. P s ∧ ~b s) p D ⇒
    Pohjola P p D)
  ∧
  (∀P p D P' D'.
    (∀s. P s ⇒ P' s) ∧ Pohjola P' p D' ∧ (∀s. D' s ⇒ D s) ⇒
    Pohjola P p D)
End

(* -- semantics -- *)

Definition PohjolaSem_def:
  PohjolaSem P p D ⇔
    ∀s. P s ⇒ ∃l. diverges s p l ∧ D l
End

val _ = export_theory();
