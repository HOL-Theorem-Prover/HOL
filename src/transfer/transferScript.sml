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

(* ----------------------------------------------------------------------
    Implications
   ---------------------------------------------------------------------- *)

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
    COND
   ---------------------------------------------------------------------- *)

Theorem COND_rule:
  ((=) |==> AB |==> AB |==> AB) COND COND
Proof
  simp[FUN_REL_def] >> rw[] >> rw[]
QED

(* ----------------------------------------------------------------------
    Combinators: LET, FUNPOW, ...
   ---------------------------------------------------------------------- *)

Theorem LET_rule:
  ((AB |==> CD) |==> (AB |==> CD)) LET LET
Proof
  simp[FUN_REL_def]
QED

Theorem FUNPOW_rule:
  ((AB |==> AB) |==> (=) |==> AB |==> AB) FUNPOW FUNPOW
Proof
  simp[FUN_REL_def] >> rw[] >> rename [‘AB (FUNPOW f n a) (FUNPOW g n b)’] >>
  qpat_x_assum ‘AB a b’ mp_tac >>
  map_every qid_spec_tac [‘a’, ‘b’, ‘n’] >> Induct >>
  simp[arithmeticTheory.FUNPOW_SUC]
QED

(* ----------------------------------------------------------------------
    Pairs
   ---------------------------------------------------------------------- *)

Theorem PAIR_REL_def = pairTheory.PAIR_REL
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

Theorem pair_CASE_CONG:
  ((AB ### CD) |==> (AB |==> CD |==> EF) |==> EF) pair_CASE pair_CASE
Proof
  simp[FUN_REL_def, pairTheory.FORALL_PROD]
QED

(* ----------------------------------------------------------------------
    Unit
   ---------------------------------------------------------------------- *)

Theorem UREL_EQ:
  () = ()
Proof simp[]
QED

(* ----------------------------------------------------------------------
    Options
   ---------------------------------------------------------------------- *)

Theorem OPTREL_MAP:
  ((AB |==> CD) |==> OPTREL AB |==> OPTREL CD) OPTION_MAP OPTION_MAP
Proof
  simp[FUN_REL_def] >> simp[optionTheory.FORALL_OPTION]
QED

Theorem OPTREL_total:
  total AB ==> total (OPTREL AB)
Proof
  simp[optionTheory.OPTREL_def, total_def, EXISTS_OR_THM] >> strip_tac >>
  Cases >> simp[]
QED

Theorem OPTREL_surj:
  surj AB ==> surj (OPTREL AB)
Proof
  simp[optionTheory.OPTREL_def, surj_def, EXISTS_OR_THM] >> strip_tac >>
  Cases >> simp[]
QED

Theorem OPTREL_left_unique:
  left_unique AB ==> left_unique (OPTREL AB)
Proof
  simp[left_unique_def, optionTheory.OPTREL_def, optionTheory.FORALL_OPTION]
QED

Theorem OPTREL_right_unique:
  right_unique AB ==> right_unique (OPTREL AB)
Proof
  simp[right_unique_def, optionTheory.OPTREL_def, optionTheory.FORALL_OPTION]
QED

Theorem option_CASE_CONG:
  (OPTREL AB |==> CD |==> (AB |==> CD) |==> CD) option_CASE option_CASE
Proof
  simp[FUN_REL_def, optionTheory.FORALL_OPTION]
QED

Theorem OPTION_BIND_rule:
  (OPTREL AB |==> (AB |==> OPTREL CD) |==> OPTREL CD) OPTION_BIND OPTION_BIND
Proof
  simp[FUN_REL_def] >> rw[optionTheory.OPTREL_def]
QED

Theorem NONE_rule:
  OPTREL AB NONE NONE
Proof
  simp[]
QED

Theorem SOME_rule:
  (AB |==> OPTREL AB) SOME SOME
Proof
  simp[FUN_REL_def]
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

Theorem LIST_REL_left_unique:
  left_unique AB ==> left_unique (LIST_REL AB)
Proof
  simp[left_unique_def] >> strip_tac >> Induct_on ‘LIST_REL’ >>
  simp[PULL_EXISTS] >> metis_tac[]
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

Theorem list_CASE_CONG:
  (LIST_REL AB |==> CD |==> (AB |==> LIST_REL AB |==> CD) |==> CD)
    list_CASE
    list_CASE
Proof
  simp[FUN_REL_def, Once listTheory.FORALL_LIST, PULL_EXISTS]
QED

Theorem NIL_rule:
  LIST_REL AB [] []
Proof
  simp[]
QED

Theorem CONS_rule:
  (AB |==> LIST_REL AB |==> LIST_REL AB) CONS CONS
Proof
  simp[FUN_REL_def]
QED

Theorem TL_rule:
  (LIST_REL AB |==> LIST_REL AB) TL TL
Proof
  simp[FUN_REL_def] >> Cases >> Cases >> simp[]
QED

Theorem LENGTH_rule:
  (LIST_REL AB |==> (=)) LENGTH LENGTH
Proof
  simp[FUN_REL_def, SF SFY_ss, listTheory.EVERY2_LENGTH]
QED

Theorem FOLDL_rule:
  ((CD |==> AB |==> CD) |==> CD |==> LIST_REL AB |==> CD) FOLDL FOLDL
Proof
  simp[FUN_REL_def] >> rw[] >> rename [‘CD (FOLDL f A xs) (FOLDL g B ys)’] >>
  map_every (C qpat_x_assum mp_tac) [‘CD A B’, ‘LIST_REL _ _ _’] >>
  map_every qid_spec_tac [‘xs’, ‘ys’, ‘A’, ‘B’] >>
  Induct_on ‘LIST_REL’ >> simp[]
QED

Theorem FOLDR_rule:
  ((AB |==> CD |==> CD) |==> CD |==> LIST_REL AB |==> CD) FOLDR FOLDR
Proof
  simp[FUN_REL_def] >> rw[] >> rename [‘CD (FOLDR f A xs) (FOLDR g B ys)’] >>
  map_every (C qpat_x_assum mp_tac) [‘CD A B’, ‘LIST_REL _ _ _’] >>
  map_every qid_spec_tac [‘xs’, ‘ys’, ‘A’, ‘B’] >>
  Induct_on ‘LIST_REL’ >> simp[]
QED

Theorem MAP_rule:
  ((AB |==> CD) |==> LIST_REL AB |==> LIST_REL CD) MAP MAP
Proof
  simp[FUN_REL_def] >> rw[] >> rename [‘LIST_REL CD (MAP f xs) (MAP g ys)’] >>
  qpat_x_assum ‘LIST_REL _ _ _ ’ mp_tac >>
  Induct_on ‘LIST_REL’ >> simp[]
QED

Theorem ALL_DISTINCT_rule:
  left_unique AB ==> right_unique AB ==>
  (LIST_REL AB |==> (=)) ALL_DISTINCT ALL_DISTINCT
Proof
  rw[left_unique_def, right_unique_def, FUN_REL_def] >>
  qpat_x_assum ‘LIST_REL _ _ _ ’ mp_tac >> Induct_on ‘LIST_REL’ >>
  simp[] >> rw[] >> iff_tac >> rw[] >>
  metis_tac[listTheory.LIST_REL_MEM_IMP_R, listTheory.LIST_REL_MEM_IMP]
QED

val _ = export_theory();
