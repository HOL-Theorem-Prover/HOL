open HolKernel Parse boolLib bossLib;

val _ = new_theory "transfer";

Overload flip[local] = “combin$C”

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

Theorem total_EQ[simp]:      total (=)
Proof simp[total_def]
QED

Theorem surj_EQ[simp]:       surj (=)
Proof simp[surj_def]
QED

Theorem bitotal_EQ[simp]:    bitotal (=)
Proof simp[bitotal_def]
QED

Definition equalityp_def:    equalityp A <=> A = (=)
End

Theorem eq_equalityp[simp]:  equalityp (=)
Proof simp[equalityp_def]
QED


Theorem equalityp_applied:   equalityp A ==> A x x
Proof simp[equalityp_def]
QED

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

Theorem FUN_REL_IFF_IMP:
  (AB ===> (=)) P Q ==> (AB ===> (==>)) P Q /\ (AB ===> combin$C (==>)) P Q
Proof
  simp[FUN_REL_def] >> metis_tac[]
QED

Theorem FUN_REL_EQ2[simp]:   ((=) ===> (=)) = (=)
Proof simp[FUN_REL_def, FUN_EQ_THM]
QED

Theorem equalityp_FUN_REL:
  equalityp AB /\ equalityp CD ==> equalityp (AB ===> CD)
Proof
  simp[equalityp_def, FUN_REL_def]
QED

Definition PAIR_REL_def:     PAIR_REL AB CD (a,c) (b,d) <=> AB a b /\ CD c d
End
val _ =
    set_mapped_fixity {fixity = Infixr 601, term_name = "PAIR_REL", tok = "###"}

Theorem equalityp_PAIR_REL:
  equalityp AB /\ equalityp CD ==> equalityp (AB ### CD)
Proof
  simp[equalityp_def, PAIR_REL_def, FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem equalityp_LIST_REL:
  equalityp AB ==> equalityp (LIST_REL AB)
Proof
  simp[equalityp_def]
QED

Theorem ALL_IFF:
  bitotal AB ==> ((AB ===> (=)) ===> (=)) (!) (!)
Proof
  simp[bitotal_def, FUN_REL_def, total_def, surj_def] >> rpt strip_tac >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_surj_RDOM:
  surj AB ==> ((AB ===> (=)) ===> (=)) (RES_FORALL (RDOM AB)) (!)
Proof
  simp[FUN_REL_def, surj_def] >> rpt strip_tac >>
  ‘b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  simp[RES_FORALL_THM, relationTheory.RDOM_DEF, IN_DEF] >>
  pop_assum SUBST1_TAC >> metis_tac[]
QED

Theorem ALL_surj_imp_imp:
  surj AB ==> ((AB ===> (==>)) ===> (==>)) (!) (!)
Proof
  simp[surj_def, FUN_REL_def] >> ntac 4 strip_tac >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_surj_iff_imp:
  surj AB ==> ((AB ===> (=)) ===> (==>)) (!) (!)
Proof
  simp[surj_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_total_RRANGE:
  total AB ==> ((AB ===> (=)) ===> (=)) (!) (RES_FORALL (RRANGE AB))
Proof
  simp[total_def, FUN_REL_def, RES_FORALL_THM, IN_DEF,
       relationTheory.RRANGE] >> strip_tac >> qx_gen_tac ‘a’ >>
  ‘a = (\x. a x)’ by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  metis_tac[]
QED

Theorem ALL_total_cimp_cimp:
  total AB ==> ((AB ===> flip (==>)) ===> flip (==>)) (!) (!)
Proof
  simp[total_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_total_iff_cimp:
  total AB ==> ((AB ===> (=)) ===> flip (==>)) (!) (!)
Proof
  simp[total_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

val _ = export_theory();
