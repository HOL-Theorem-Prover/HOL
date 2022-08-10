open HolKernel Parse boolLib bossLib;

val _ = new_theory "modalBasics";

Datatype:
  form = VAR num | DISJ form form | FALSE | NOT form | DIAM form
End

Datatype:
  frame = <| world : 'a set ;
             rel : 'a -> 'a -> bool
          |>
End

Datatype:
  model = <| frame : 'a frame;
             valt : num -> 'a -> bool
          |>
End

Definition satis_def[simp]:
  (satis M w (VAR p) <=> w ∈ M.frame.world /\ w ∈ M.valt p) /\
  (satis M w FALSE <=> F) /\
  (satis M w (NOT form) <=> w IN M.frame.world /\ ¬ satis M w form) ∧
  (satis M w (DISJ form1 form2) <=> satis M w form1 \/ satis M w form2) ∧
  (satis M w (DIAM form) <=>
   w IN M.frame.world /\
   ∃v. M.frame.rel w v /\ v IN M.frame.world /\ satis M v form)
End

Theorem satis_only_in_worlds:
  ∀w. satis M w f ⇒ w ∈ M.frame.world
Proof
  Induct_on ‘f’ >> simp[DISJ_IMP_THM]
QED

Datatype:
  nnfform =
    Var num | NVar num | Conj nnfform nnfform | Disj nnfform nnfform |
    Box nnfform | Dia nnfform
End
val _ = export_rewrites ["nnfform_size_def"]

Definition forces_def[simp]:
  (forces M w (Var n)      ⇔ w ∈ M.frame.world ∧ w ∈ M.valt n) ∧
  (forces M w (NVar n)     ⇔ w ∈ M.frame.world ∧ w ∉ M.valt n) ∧
  (forces M w (Conj f1 f2) ⇔ forces M w f1 ∧ forces M w f2) ∧
  (forces M w (Disj f1 f2) ⇔ forces M w f1 ∨ forces M w f2) ∧
  (forces M w (Box f)      ⇔
     w ∈ M.frame.world ∧
     ∀v. v ∈ M.frame.world ∧ M.frame.rel w v ⇒ forces M v f) ∧
  (forces M w (Dia f)      ⇔
     w ∈ M.frame.world ∧
     ∃v. v ∈ M.frame.world ∧ M.frame.rel w v ∧ forces M v f)
End

Theorem forces_only_in_worlds:
  ∀w. forces M w nfm ⇒ w ∈ M.frame.world
Proof
  Induct_on ‘nfm’ >> simp[DISJ_IMP_THM]
QED

Definition to_nnf_def[simp]:
  to_nnf p (VAR n) = (if p then Var n else NVar n) ∧
  to_nnf p FALSE = (if p then Conj else Disj) (Var 0) (NVar 0) ∧
  to_nnf p (NOT f) = to_nnf (¬p) f ∧
  to_nnf p (DISJ f1 f2) =
    (if p then Disj else Conj) (to_nnf p f1) (to_nnf p f2) ∧
  to_nnf p (DIAM f) = (if p then Dia else Box) (to_nnf p f)
End

Theorem to_nnf_correct:
  (forces M w (to_nnf p f) ⇔ if p then satis M w f
                             else ¬satis M w f ∧ w ∈ M.frame.world)
Proof
  map_every qid_spec_tac [‘w’, ‘p’] >> Induct_on ‘f’ >>
  rpt gen_tac >> Cases_on ‘p’ >> simp[SF CONJ_ss] >>
  metis_tac[satis_only_in_worlds]
QED

Overload NNF = “to_nnf T”

Theorem NNF_correct[simp]:
  forces M w (NNF f) ⇔ satis M w f
Proof
  simp[to_nnf_correct]
QED

Definition to_full_def[simp]:
  to_full (Var n) = VAR n ∧
  to_full (NVar n) = NOT (VAR n) ∧
  to_full (Conj f1 f2) = NOT (DISJ (NOT (to_full f1)) (NOT (to_full f2))) ∧
  to_full (Disj f1 f2) = DISJ (to_full f1) (to_full f2) ∧
  to_full (Box f) = NOT (DIAM (NOT (to_full f))) ∧
  to_full (Dia f) = DIAM (to_full f)
End

Theorem to_full_correct:
  ∀w. satis M w (to_full f) ⇔ forces M w f
Proof
  Induct_on ‘f’ >> simp[SF CONJ_ss] >>
  metis_tac[forces_only_in_worlds]
QED

Theorem NNF_RID[simp]:
  to_nnf T (to_full f) = f
Proof
  Induct_on ‘f’ >> simp[]
QED

Definition reflexive_M:
  reflexive_M m ⇔ ∀w. w ∈ m.frame.world ⇒ m.frame.rel w w
End

Definition transitive_M:
  transitive_M m ⇔
    ∀u v w. u ∈ m.frame.world ∧ v ∈ m.frame.world ∧ w ∈ m.frame.world ∧
            m.frame.rel u v ∧ m.frame.rel v w ⇒
            m.frame.rel u w
End

val _ = export_theory();
