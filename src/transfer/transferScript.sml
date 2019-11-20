open HolKernel Parse boolLib bossLib;

val _ = new_theory "transfer";

(* uniqueness, which might also be termed injectivity *)
Definition right_unique_def:
  right_unique (R : 'a -> 'b -> bool) <=>
    !a b1 b2. R a b1 /\ R a b2 ==> b1 = b2
End
Theorem right_unique_EQ[simp]: right_unique (=)
Proof simp[right_unique_def]
QED

Definition left_unique_def:
  left_unique (R: 'a -> 'b -> bool) <=>
    !a1 a2 b. R a1 b /\ R a2 b ==> a1 = a2
End
Theorem left_unique_EQ[simp]: left_unique (=)
Proof simp[left_unique_def]
QED

Definition bi_unique_def:
  bi_unique R <=> left_unique R /\ right_unique R
End

Theorem bi_unique_EQ[simp]: bi_unique (=)
Proof simp[bi_unique_def]
QED

(* totality or surjectivity *)
Definition total_def: total (R : 'a -> 'b -> bool) <=> !x:'a. ?y. R x y
End

Definition surj_def: surj (R : 'a -> 'b -> bool) <=> !y:'b. ?x. R x y
End

Definition bitotal_def: bitotal (R : 'a -> 'b -> bool) <=> total R /\ surj R
End

val _ =
    set_mapped_fixity {fixity = Infixr 490, term_name = "FUN_REL", tok = "===>"}

Definition FUN_REL_def:
  (AB ===> CD) (f : 'a -> 'c) (g : 'b -> 'd) <=>
    !a:'a b:'b. AB a b ==> CD (f a) (g b)
End

Theorem FUN_REL_COMB:
  (AB ===> CD) f g /\ AB a b ==> CD (f a) (g b)
Proof simp[FUN_REL_def]
QED

Theorem FUN_REL_ABS:
  (!a b. AB a b ==> CD (f a) (g b)) ==> (AB ===> CD) (\a. f a) (\b. g b)
Proof simp[FUN_REL_def]
QED

Theorem FUN_REL_EQ2[simp]:
  ((=) ===> (=)) = (=)
Proof simp[FUN_REL_def, FUN_EQ_THM]
QED

Definition PAIR_REL_def:  PAIR_REL AB CD (a,c) (b,d) <=> AB a b /\ CD c d
End
val _ =
    set_mapped_fixity {fixity = Infixr 601, term_name = "PAIR_REL", tok = "###"}

val _ = export_theory();
