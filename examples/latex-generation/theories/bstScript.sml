Theory bst
Ancestors sampleTree pred_set

Type dict = “:('a # 'b) stree”

Definition keys_def[simp]:
  keys Lf = {} /\
  keys (Nd t1 (k,v) t2) = {k} ∪ keys t1 ∪ keys t2
End

Theorem keys_elems:
  keys d = IMAGE FST (elems d)
Proof
  Induct_on ‘d’ >> simp[pairTheory.FORALL_PROD]
QED

Inductive sorted_dict:
[~Lf:] sorted_dict R Lf
[~Nd:]
  sorted_dict R t1 ∧ sorted_dict R t2 ∧
  (∀e. e ∈ keys t1 ⇒ R e k) ∧
  (∀e. e ∈ keys t2 ⇒ R k e) ⇒
  sorted_dict R (Nd t1 (k,v) t2)
End
