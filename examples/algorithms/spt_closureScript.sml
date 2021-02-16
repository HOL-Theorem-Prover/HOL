open HolKernel boolLib bossLib BasicProvers;
open sptreeTheory pred_setTheory arithmeticTheory relationTheory;

val _ = new_theory "spt_closure";


(******************** Definitions ********************)

Definition num_set_tree_union_def:
  (num_set_tree_union LN t2 = t2 : num_set num_map) /\
  (num_set_tree_union (LS a) t =
   case t of
     | LN => LS a
     | LS b => LS (union a b)
     | BN t1 t2 => BS t1 a t2
     | BS t1 b t2 => BS t1 (union a b) t2) /\
  (num_set_tree_union (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BS t1 a t2
       | BN t1' t2' =>
            BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2')
       | BS t1' a t2' =>
        BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')) /\
  (num_set_tree_union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS b => BS t1 (union a b) t2
       | BN t1' t2' =>
            BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')
       | BS t1' b t2' =>
            BS (num_set_tree_union t1 t1') (union a b)
                (num_set_tree_union t2 t2'))
End

Theorem domain_spt_fold_union:
  ! tree y.
    domain (spt_fold union y tree) =
    domain y UNION
    {n | ?k aSet. lookup k tree = SOME aSet /\ n IN domain aSet}
Proof
  Induct >> rw[] >>
  gvs[spt_fold_def, lookup_def, domain_def, domain_union]
  >- simp[UNION_COMM]
  >- (
    rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
    >- (
      disj2_tac >> qexists_tac `(k + 1) * 2` >> simp[] >>
      simp[EVEN_DOUBLE, LEFT_ADD_DISTRIB] >>
      once_rewrite_tac[MULT_COMM] >> simp[DIV_MULT]
      )
    >- (
      disj2_tac >> qexists_tac `k * 2 + 1` >> simp[] >>
      simp[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> simp[MULT_DIV]
      )
    >- (
      FULL_CASE_TAC >> gvs[]
      >- (disj1_tac >> disj2_tac >> goal_assum drule >> simp[])
      >- (disj2_tac >> goal_assum drule >> simp[])
      )
    )
  >- (
    rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
    >- (disj2_tac >> qexists_tac `0` >> simp[])
    >- (
      disj2_tac >> qexists_tac `(k + 1) * 2` >> simp[] >>
      simp[EVEN_DOUBLE, LEFT_ADD_DISTRIB] >>
      once_rewrite_tac[MULT_COMM] >> simp[DIV_MULT]
      )
    >- (
      disj2_tac >> qexists_tac `k * 2 + 1` >> simp[] >>
      simp[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> simp[MULT_DIV]
      )
    >- (
      EVERY_CASE_TAC >> gvs[]
      >- (disj1_tac >> disj2_tac >> disj2_tac >> goal_assum drule >> simp[])
      >- (disj2_tac >> goal_assum drule >> simp[])
      )
    )
QED

Definition closure_spt_def:
  closure_spt (reachable: num_set) tree =
    let sets = inter tree reachable in
    let nodes = spt_fold union LN sets in
    if subspt nodes reachable then reachable
    else closure_spt (union reachable nodes) tree
Termination
  WF_REL_TAC `measure (\ (r,t). size (difference (spt_fold union LN t) r))` >>
  rw[] >> gvs[subspt_domain, SUBSET_DEF] >>
  irule size_diff_less >>
  gvs[domain_union, domain_spt_fold_union, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[] >>
  simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
  goal_assum drule >> goal_assum drule >> simp[] >>
  goal_assum (drule_at Any) >> qexists_tac `k` >> simp[]
End


(******************** Proofs ********************)

Definition is_adjacent_def:
  is_adjacent tree x y =
  ? aSetx.
      ( lookup x tree = SOME aSetx ) /\ ( lookup y aSetx = SOME () )
End

Definition is_reachable_def:
  is_reachable tree = RTC (is_adjacent tree)
End

(***** num_set_tree_union *****)

Theorem num_set_tree_union_empty:
  ! t1 t2 . isEmpty (num_set_tree_union t1 t2) <=> isEmpty t1 /\ isEmpty t2
Proof
  Induct >> rw[num_set_tree_union_def] >> CASE_TAC >>
  rw[num_set_tree_union_def]
QED

Theorem wf_num_set_tree_union:
  ! t1 t2 result .
    wf t1 /\ wf t2
  ==> wf (num_set_tree_union t1 t2)
Proof
  Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >>
  CASE_TAC >> metis_tac[wf_def, num_set_tree_union_empty]
QED

Theorem domain_num_set_tree_union:
  ! t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 UNION domain t2
Proof
  Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
  rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >>
  rw[UNION_ASSOC] >> rw[UNION_COMM] >>
  metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
QED

Theorem num_set_tree_union_sym:
  ! t1 t2 .
    num_set_tree_union t1 t2 = num_set_tree_union t2 t1
Proof
  Induct >> rw[num_set_tree_union_def] >>
  Cases_on `t2` >> fs[num_set_tree_union_def] >>
  fs[union_num_set_sym]
QED

Theorem lookup_num_set_tree_union:
  !t1 t2 n.
    lookup n (num_set_tree_union t1 t2) =
    case lookup n t1 of
      SOME x => (
        case lookup n t2 of
          SOME y => SOME (union x y)
        | NONE => SOME x)
    | NONE => lookup n t2
Proof
  Induct >> rw[] >> gvs[lookup_def]
  >- simp[num_set_tree_union_def] >>
  IF_CASES_TAC >> gvs[lookup_def] >>
  Cases_on `t2` >> gvs[lookup_def, num_set_tree_union_def] >>
  EVERY_CASE_TAC >> gvs[]
QED


(***** wf *****)

Theorem wf_spt_fold_union:
  ! tree y.
    (! n x . (lookup n tree = SOME x) ==> wf x) /\ wf y
  ==> wf (spt_fold union y tree)
Proof
  Induct >> rw[] >> fs[spt_fold_def, wf_def]
  >- metis_tac[lookup_def, wf_union]
  >- (
    last_x_assum irule >> last_x_assum (irule_at Any) >> simp[] >>
    gvs[lookup_def] >> rw[] >>
    last_x_assum irule
    >- (
      qexists_tac `2 * n + 2` >>
      simp[EVEN_ADD, EVEN_DOUBLE] >>
      once_rewrite_tac [MULT_COMM] >> simp[DIV_MULT]
      )
    >- (
      qexists_tac `2 * n + 1` >>
      simp[EVEN_ADD, EVEN_DOUBLE] >>
      once_rewrite_tac [MULT_COMM] >> simp[MULT_DIV]
      )
    )
  >- (
    last_x_assum irule >> irule_at Any wf_union >>
    last_x_assum (irule_at Any) >> simp[] >> rw[] >>
    last_x_assum irule >> simp[lookup_def]
    >- (
      qexists_tac `2 * n + 2` >>
      simp[EVEN_ADD, EVEN_DOUBLE] >>
      once_rewrite_tac [MULT_COMM] >> simp[DIV_MULT]
      )
    >- (qexists_tac `0` >> simp[])
    >- (
      qexists_tac `2 * n + 1` >>
      simp[EVEN_ADD, EVEN_DOUBLE] >>
      once_rewrite_tac [MULT_COMM] >> simp[MULT_DIV]
      )
    )
QED

Theorem wf_closure_spt:
  ! reachable tree.
    wf reachable /\
    (! n x . lookup n tree = SOME x ==> wf x)
  ==> wf (closure_spt reachable tree)
Proof
  recInduct closure_spt_ind >> rw[] >>
  once_rewrite_tac [closure_spt_def] >> rw[] >> fs[] >>
  last_x_assum irule >> goal_assum drule >>
  irule wf_union >> simp[] >>
  irule wf_spt_fold_union >> simp[wf_def, lookup_inter] >>
  rw[] >> EVERY_CASE_TAC >> gvs[] >> res_tac
QED


(***** is_adjacent/is_reachable *****)

Theorem adjacent_domain:
  ! tree x y . is_adjacent tree x y ==> x IN domain tree
Proof
  rw[is_adjacent_def] >> rw[domain_lookup]
QED

Theorem reachable_domain:
  ! tree x y . is_reachable tree x y ==> (x = y \/ x IN domain tree)
Proof
  simp[is_reachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  metis_tac[adjacent_domain]
QED

Theorem reachable_LHS_NOTIN:
  !tree n x. is_reachable tree n x /\ n NOTIN domain tree ==> n = x
Proof
  rw[is_reachable_def] >> gvs[Once RTC_CASES1, is_adjacent_def, domain_lookup]
QED

Theorem rtc_is_adjacent:
  (! k . k IN t ==> ! n . (is_adjacent fullTree k n ==> n IN t)) ==>
  ! x y . RTC (is_adjacent fullTree) x y ==> x IN t ==> y IN t
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  fs[SUBSET_DEF] >> metis_tac []
QED

Theorem is_adjacent_num_set_tree_union:
  ! t1 t2 n m .
    is_adjacent t1 n m ==> is_adjacent (num_set_tree_union t1 t2) n m
Proof
  rw[is_adjacent_def, lookup_num_set_tree_union] >> simp[] >>
  EVERY_CASE_TAC >> gvs[lookup_union]
QED

Theorem is_reachable_num_set_tree_union:
  ! t1 t2 n m .
    is_reachable t1 n m
  ==> is_reachable (num_set_tree_union t1 t2) n m
Proof
  simp[is_reachable_def] >> strip_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
  simp[Once RTC_CASES2] >> disj2_tac >>
  goal_assum drule >> irule is_adjacent_num_set_tree_union >> simp[]
QED


(***** main results *****)

Theorem closure_spt_lemma:
  ! reachable tree closure (roots : num set).
    closure_spt reachable tree = closure /\
    roots ⊆ domain reachable /\
    (!k. k IN domain reachable ==> ?n. n IN roots /\ is_reachable tree n k)
  ==> domain closure = {a | ?n. n IN roots /\ is_reachable tree n a}
Proof
  recInduct closure_spt_ind >> rw[] >>
  once_rewrite_tac[closure_spt_def] >> simp[] >>
  IF_CASES_TAC >> gvs[]
  >- (
    gvs[subspt_domain, domain_spt_fold_union, EXTENSION,
        SUBSET_DEF, PULL_EXISTS] >>
    rw[] >> eq_tac >> rw[] >>
    irule rtc_is_adjacent >>
    gvs[is_reachable_def] >>
    goal_assum (drule_at Any) >> gvs[] >> rw[] >>
    first_x_assum irule >>
    gvs[lookup_inter, is_adjacent_def, domain_lookup] >>
    qexistsl_tac [`aSetx`,`k`] >> simp[]
    ) >>
  first_x_assum irule >> simp[] >> rw[] >> gvs[domain_union, SUBSET_DEF] >>
  gvs[domain_spt_fold_union, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[domain_lookup] >>
  first_x_assum drule >> strip_tac >>
  goal_assum drule >> gvs[is_reachable_def] >>
  irule (iffRL RTC_CASES2) >> DISJ2_TAC >>
  goal_assum drule >> simp[is_adjacent_def]
QED

Theorem closure_spt_thm:
  ! tree start.
    domain (closure_spt start tree) =
      {a | ?n. n IN domain start /\ is_reachable tree n a}
Proof
  rw[] >> irule closure_spt_lemma >>
  irule_at Any EQ_REFL >> simp[] >> rw[] >>
  goal_assum drule >> simp[is_reachable_def]
QED


val _ = export_theory();
