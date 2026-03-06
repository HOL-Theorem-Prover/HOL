Theory sampleTree
Ancestors hol pred_set


Datatype: stree = Lf | Nd stree 'a stree
End

Definition inorder_def[simp]:
  inorder Lf = [] ∧
  inorder (Nd t1 a t2) = inorder t1 ++ [a] ++ inorder t2
End

Definition elemcount_def[simp]:
  elemcount Lf = 0 ∧
  elemcount (Nd t1 _ t2) = elemcount t1 + elemcount t2 + 1
End

Theorem elemcount_LENGTH_inorder:
  elemcount t = LENGTH (inorder t)
Proof
  Induct_on ‘t’ >> simp[]
QED

Definition flip_def[simp]:
  flip Lf = Lf ∧
  flip (Nd t1 a t2) = Nd (flip t2) a (flip t1)
End

Definition elems_def[simp]:
  elems Lf = {} ∧
  elems (Nd t1 a t2) = {a} ∪ elems t1 ∪ elems t2
End

Theorem elems_flip[simp]:
  elems (flip t) = elems t
Proof
  Induct_on ‘t’ >> simp[AC UNION_ASSOC UNION_COMM]
QED

Theorem elems_inorder:
  elems t = set (inorder t)
Proof
  Induct_on ‘t’ >> simp[AC UNION_ASSOC UNION_COMM]
QED

Theorem elemcount_flip[simp]:
  elemcount (flip t) = elemcount t
Proof
  Induct_on ‘t’ >> simp[]
QED

Theorem inorder_flip:
  inorder (flip t) = REVERSE (inorder t)
Proof
  Induct_on ‘t’ >> simp[]
QED

Inductive exists:
[~atNd:] P a ⇒ exists P (Nd t1 a t2)
[~atLeft:] exists P t1 ⇒ exists P (Nd t1 a t2)
[~atRight:] exists P t2 ⇒ exists P (Nd t1 a t2)
End

