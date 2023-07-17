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

Theorem bi_unique_implied:
  left_unique r /\ right_unique r ==> bi_unique r
Proof
  simp[bi_unique_def]
QED

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

Theorem bitotal_implied:
  total r /\ surj r ==> bitotal r
Proof
  simp[bitotal_def]
QED

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

Definition FUN_REL_def:
  FUN_REL AB CD (f : 'a -> 'c) (g : 'b -> 'd) <=>
    !a:'a b:'b. AB a b ==> CD (f a) (g b)
End

val _ = set_fixity "|==>" (Infixr 490)
Overload "|==>" = “FUN_REL”  (* co-existing with quotientTheory$|==> *)

Theorem FUN_REL_COMB:
  (AB |==> CD) f g /\ AB a b ==> CD (f a) (g b)
Proof simp[FUN_REL_def]
QED

Theorem FUN_REL_IFF_IMP:
  (AB |==> (=)) P Q ==> (AB |==> (==>)) P Q /\ (AB |==> combin$C (==>)) P Q
Proof
  simp[FUN_REL_def] >> metis_tac[]
QED

Theorem FUN_REL_EQ2[simp]:   ((=) |==> (=)) = (=)
Proof simp[FUN_REL_def, FUN_EQ_THM]
QED

Theorem equalityp_FUN_REL:
  equalityp AB /\ equalityp CD ==> equalityp (AB |==> CD)
Proof
  simp[equalityp_def, FUN_REL_def]
QED

Theorem EQ_bi_unique:
  bi_unique AB ==> (AB |==> AB |==> (=)) (=) (=)
Proof
  simp[FUN_REL_def, bi_unique_def, left_unique_def, right_unique_def] >>
  metis_tac[]
QED

(* ----------------------------------------------------------------------
    forall
   ---------------------------------------------------------------------- *)

Theorem ALL_IFF:
  bitotal AB ==> ((AB |==> (=)) |==> (=)) (!) (!)
Proof
  simp[bitotal_def, FUN_REL_def, total_def, surj_def] >> rpt strip_tac >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_surj_RDOM:
  surj AB ==> ((AB |==> (=)) |==> (=)) (RES_FORALL (RDOM AB)) (!)
Proof
  simp[FUN_REL_def, surj_def] >> rpt strip_tac >>
  ‘b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  simp[RES_FORALL_THM, relationTheory.RDOM_DEF, IN_DEF] >>
  pop_assum SUBST1_TAC >> metis_tac[]
QED

Theorem ALL_surj_imp_imp:
  surj AB ==> ((AB |==> (==>)) |==> (==>)) (!) (!)
Proof
  simp[surj_def, FUN_REL_def] >> ntac 4 strip_tac >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_surj_iff_imp:
  surj AB ==> ((AB |==> (=)) |==> (==>)) (!) (!)
Proof
  simp[surj_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem RRANGE_EQ[simp]:
  RRANGE (=) = K T
Proof
  simp[pred_setTheory.EXTENSION, IN_DEF, relationTheory.RRANGE]
QED

Theorem RDOM_EQ[simp]:
  RDOM (=) = K T
Proof
  simp[pred_setTheory.EXTENSION, IN_DEF, relationTheory.RDOM_DEF]
QED

Theorem ALL_total_RRANGE:
  total AB ==> ((AB |==> (=)) |==> (=)) (!) (RES_FORALL (RRANGE AB))
Proof
  simp[total_def, FUN_REL_def, RES_FORALL_THM, IN_DEF,
       relationTheory.RRANGE] >> strip_tac >> qx_gen_tac ‘a’ >>
  ‘a = (\x. a x)’ by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  metis_tac[]
QED

Theorem ALL_total_cimp_cimp:
  total AB ==> ((AB |==> flip (==>)) |==> flip (==>)) (!) (!)
Proof
  simp[total_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem ALL_total_iff_cimp:
  total AB ==> ((AB |==> (=)) |==> flip (==>)) (!) (!)
Proof
  simp[total_def, FUN_REL_def] >> strip_tac >>
  map_every qx_gen_tac [‘a’, ‘b’] >>
  ‘a = (\x. a x) /\ b = (\y. b y)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    exists
   ---------------------------------------------------------------------- *)

Theorem EXISTS_bitotal :
  bitotal AB ==> ((AB |==> (=)) |==> (=)) (?) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a) /\ bP = (\b. bP b)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem EXISTS_IFF_RDOM:
  surj AB ==> ((AB |==> (=)) |==> (=)) (RES_EXISTS (RDOM AB)) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def, RES_EXISTS_THM, IN_DEF] >>
  strip_tac >> qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘bP = (\b. bP b)’ by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  simp[relationTheory.RDOM_DEF] >> metis_tac[]
QED

Theorem EXISTS_IFF_RRANGE:
  total AB ==> ((AB |==> (=)) |==> (=)) (?) (RES_EXISTS (RRANGE AB))
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def, RES_EXISTS_THM, IN_DEF] >>
  strip_tac >> qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a)’ by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  simp[relationTheory.RRANGE] >> metis_tac[]
QED

Theorem EXISTS_total_iff_imp:
  total AB ==> ((AB |==> (=)) |==> $==>) (?) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a) /\ bP = (\b. bP b)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem EXISTS_total_imp_imp:
  total AB ==> ((AB |==> $==>) |==> $==>) (?) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a) /\ bP = (\b. bP b)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem EXISTS_surj_iff_cimp:
  surj AB ==> ((AB |==> $=) |==> flip $==>) (?) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a) /\ bP = (\b. bP b)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem EXISTS_surj_cimp_cimp:
  surj AB ==> ((AB |==> flip $==>) |==> flip $==>) (?) (?)
Proof
  simp[FUN_REL_def, bitotal_def, total_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘aP’, ‘bP’] >> strip_tac >>
  ‘aP = (\a. aP a) /\ bP = (\b. bP b)’ by simp[FUN_EQ_THM] >>
  ntac 2 (pop_assum SUBST1_TAC) >> metis_tac[]
QED

Theorem total_total_sets:
  total AB /\ left_unique AB ==> total (AB |==> $<=>)
Proof
  simp[FUN_REL_def, total_def, left_unique_def] >> rw[] >>
  qexists_tac ‘{ b | ?a. a IN x /\ AB a b }’  >> simp[IN_DEF] >> metis_tac[]
QED

Theorem surj_sets:
  surj AB /\ right_unique AB ==> surj (AB |==> $<=>)
Proof
  rw[FUN_REL_def, surj_def, right_unique_def] >>
  rename [‘AB _ _ ==> (_ _ <=> bset _)’] >>
  qexists_tac ‘{ a | ?b. bset b /\ AB a b }’ >> simp[] >>
  metis_tac[]
QED

Theorem cimp_imp:
  ((==>) |==> flip (==>) |==> flip (==>)) (==>) (==>)
Proof
  simp[FUN_REL_def, FORALL_BOOL]
QED

Theorem eq_imp:
  ((=) |==> (=) |==> (=)) (==>) (==>)
Proof
  simp[FUN_REL_def]
QED

Theorem imp_conj :
  ((==>) |==> (==>) |==> (==>)) (/\) (/\)
Proof
  simp[FUN_REL_def]
QED

Theorem imp_disj:
  ((==>) |==> (==>) |==> (==>)) (\/) (\/)
Proof
  simp[FUN_REL_def] >> metis_tac[]
QED

Theorem cimp_disj:
  (flip (==>) |==> flip (==>) |==> flip (==>)) (\/) (\/)
Proof
  simp[FUN_REL_def] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    LET
   ---------------------------------------------------------------------- *)

Theorem LET_rule:
  ((AB |==> CD) |==> (AB |==> CD)) LET LET
Proof
  simp[FUN_REL_def]
QED


(* ----------------------------------------------------------------------
    Pairs
   ---------------------------------------------------------------------- *)

Definition PAIR_REL_def:     PAIR_REL AB CD (a,c) (b,d) <=> AB a b /\ CD c d
End
val _ =
    set_mapped_fixity {fixity = Infixr 601, term_name = "PAIR_REL", tok = "###"}

Theorem equalityp_PAIR_REL:
  equalityp AB /\ equalityp CD ==> equalityp (AB ### CD)
Proof
  simp[equalityp_def, PAIR_REL_def, FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem FST_CORRECT:
  (PAIR_REL AB CD |==> AB) FST FST
Proof
  simp[PAIR_REL_def, FUN_REL_def, pairTheory.FORALL_PROD]
QED

Theorem SND_CORRECT:
  (PAIR_REL AB CD |==> CD) SND SND
Proof
  simp[PAIR_REL_def, FUN_REL_def, pairTheory.FORALL_PROD]
QED

Theorem COMMA_CORRECT:
  (AB |==> CD |==> PAIR_REL AB CD) $, $,
Proof
  simp[PAIR_REL_def, FUN_REL_def, pairTheory.FORALL_PROD]
QED

Definition PAIRU_def:
  PAIRU AB (a,()) b <=> AB a b
End

Theorem PAIRU_COMMA:
  (AB |==> (=) |==> PAIRU AB) $, K
Proof
  simp[PAIRU_def, pairTheory.FORALL_PROD, FUN_REL_def]
QED

Definition UPAIR_def:
  UPAIR AB ((),a) b <=> AB a b
End

Theorem UPAIR_COMMA:
  ((=) |==> AB |==> UPAIR AB) $, (K I)
Proof
  simp[UPAIR_def, pairTheory.FORALL_PROD, FUN_REL_def]
QED

(* ----------------------------------------------------------------------
    Unit
   ---------------------------------------------------------------------- *)

Theorem UREL_EQ:
  () = ()
Proof simp[]
QED

(* ----------------------------------------------------------------------
    Lists
   ---------------------------------------------------------------------- *)

Theorem equalityp_LIST_REL:
  equalityp AB ==> equalityp (LIST_REL AB)
Proof
  simp[equalityp_def]
QED

Theorem LIST_REL_right_unique:
  right_unique AB ==> right_unique (LIST_REL AB)
Proof
  simp[right_unique_def] >> strip_tac >> Induct >> simp[PULL_EXISTS] >>
  metis_tac[]
QED

Theorem LIST_REL_surj:
  surj AB ==> surj (LIST_REL AB)
Proof
  simp[surj_def] >> strip_tac >> Induct >> simp[PULL_EXISTS] >> metis_tac[]
QED

Theorem LIST_REL_total:
  total AB ==> total (LIST_REL AB)
Proof
  simp[total_def] >> strip_tac >> Induct >> simp[] >> metis_tac[]
QED

val _ = export_theory();
