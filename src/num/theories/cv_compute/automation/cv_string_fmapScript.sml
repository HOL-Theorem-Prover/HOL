(*
  Set up cv translator for string |-> 'a
*)
Theory cv_string_fmap
Ancestors
  cv cv_type arithmetic words cv_rep cv_prim pair list option sum
  alist indexedLists rich_list sptree finite_set sorting cv_std
Libs
  dep_rewrite cv_typeLib cv_repLib cv_transLib

Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(*----------------------------------------------------------*
   string trie
 *----------------------------------------------------------*)

Datatype:
  str_trie = Nothing
           | Just 'a
           | Branch char str_trie str_trie
End

val _ = (cv_memLib.use_long_names := false);
val from_to_str_trie = cv_typeLib.from_to_thm_for “:'a str_trie”;
val _ = (cv_memLib.use_long_names := true);

Definition st_get_nil_def[simp]:
  st_get_nil (Branch _ _ rest) = st_get_nil rest ∧
  st_get_nil (Just x) = SOME x ∧
  st_get_nil Nothing = NONE
End

Definition st_get_def:
  st_get t [] = st_get_nil t ∧
  st_get t (x::xs) = st_get_cons t x xs ∧
  st_get_cons Nothing x xs = NONE ∧
  st_get_cons (Just _) x xs = NONE ∧
  st_get_cons (Branch c subtrie rest) x xs =
    if c > x then NONE else
    if c < x then st_get_cons rest x xs else
      st_get subtrie xs
End

Definition st_make_def[simp]:
  st_make [] y = Just y ∧
  st_make (x::xs) y = Branch x (st_make xs y) Nothing
End

Definition st_set_nil_def[simp]:
  st_set_nil (Branch c t rest) y = Branch c t (st_set_nil rest y) ∧
  st_set_nil _ y = Just y
End

Definition st_set_cons_def:
  st_set_cons Nothing x xs y = Branch x (st_make xs y) Nothing ∧
  st_set_cons (Just z) x xs y = Branch x (st_make xs y) (Just z) ∧
  st_set_cons (Branch c subtrie rest) x xs y =
    if c > x then
      Branch x (st_make xs y) (Branch c subtrie rest)
    else if c < x then
      Branch c subtrie (st_set_cons rest x xs y)
    else
      Branch c (case xs of
                | [] => st_set_nil subtrie y
                | (x::xs) => st_set_cons subtrie x xs y) rest
End

Definition st_set_def[simp]:
  st_set t [] y = st_set_nil t y ∧
  st_set t (x::xs) y = st_set_cons t x xs y
End

Definition st_sets_def[simp]:
  st_sets t [] = t ∧
  st_sets t ((s,a)::rest) = st_set (st_sets t rest) s a
End

Definition st_del_nil_def[simp]:
  st_del_nil (Branch x y rest) = Branch x y (st_del_nil rest) ∧
  st_del_nil _ = Nothing
End

Definition mk_Branch_def:
  mk_Branch c Nothing t2 = t2 ∧
  mk_Branch c (Just x) t2 = Branch c (Just x) t2 ∧
  mk_Branch c (Branch a b d) t2 = Branch c (Branch a b d) t2
End

Definition st_del_cons_def:
  st_del_cons Nothing x xs = Nothing ∧
  st_del_cons (Just z) x xs = Just z ∧
  st_del_cons (Branch c subtrie rest) x xs =
    if c > x then
      Branch c subtrie rest
    else if c < x then
      Branch c subtrie (st_del_cons rest x xs)
    else
      mk_Branch c (case xs of
                   | [] => st_del_nil subtrie
                   | (x::xs) => st_del_cons subtrie x xs) rest
End

Definition st_del_def[simp]:
  st_del t [] = st_del_nil t ∧
  st_del t (x::xs) = st_del_cons t x xs
End

Definition st_union_def:
  st_union Nothing t = t ∧
  st_union t Nothing = t ∧
  st_union (Just x) (Just y) = Just x ∧
  st_union (Just x) (Branch c t1 t2) = Branch c t1 (st_union (Just x) t2) ∧
  st_union (Branch c t1 t2) (Just x) = Branch c t1 (st_union t2 (Just x)) ∧
  st_union (Branch c1 t1 t2) (Branch c2 u1 u2) =
    if ORD c1 < ORD c2 then
      Branch c1 t1 (st_union t2 (Branch c2 u1 u2))
    else if ORD c2 < ORD c1 then
      Branch c2 u1 (st_union (Branch c1 t1 t2) u2)
    else
      Branch c1 (st_union t1 u1) (st_union t2 u2)
End

Definition st_inter_def:
  st_inter Nothing t = Nothing ∧
  st_inter t Nothing = Nothing ∧
  st_inter (Just x) (Just y) = Just x ∧
  st_inter (Just x) (Branch c t1 t2) = st_inter (Just x) t2 ∧
  st_inter (Branch c t1 t2) (Just x) = st_inter t2 (Just x) ∧
  st_inter (Branch c1 t1 t2) (Branch c2 u1 u2) =
    if ORD c1 < ORD c2 then
      st_inter t2 (Branch c2 u1 u2)
    else if ORD c2 < ORD c1 then
      st_inter (Branch c1 t1 t2) u2
    else
      mk_Branch c1 (st_inter t1 u1) (st_inter t2 u2)
End

Definition st_minus_def:
  st_minus Nothing t = Nothing ∧
  st_minus t Nothing = t ∧
  st_minus (Just x) (Just y) = Nothing ∧
  st_minus (Just x) (Branch c t1 t2) = st_minus (Just x) t2 ∧
  st_minus (Branch c t1 t2) (Just x) = Branch c t1 (st_minus t2 (Just x)) ∧
  st_minus (Branch c1 t1 t2) (Branch c2 u1 u2) =
    if ORD c1 < ORD c2 then
      Branch c1 t1 (st_minus t2 (Branch c2 u1 u2))
    else if ORD c2 < ORD c1 then
      st_minus (Branch c1 t1 t2) u2
    else
      mk_Branch c1 (st_minus t1 u1) (st_minus t2 u2)
End

Definition st_card_def:
  st_card Nothing = 0:num ∧
  st_card (Just x) = 1 ∧
  st_card (Branch c t1 t2) = st_card t1 + st_card t2
End

Definition st_submap_def:
  st_submap Nothing u = T ∧
  st_submap (Just x) Nothing = F ∧
  st_submap (Branch c t1 t2) Nothing = F ∧
  st_submap (Just x) (Just y) = (x = y) ∧
  st_submap (Just x) (Branch c u1 u2) = st_submap (Just x) u2 ∧
  st_submap (Branch c t1 t2) (Just y) = F ∧
  st_submap (Branch c1 t1 t2) (Branch c2 u1 u2) =
    if ORD c1 < ORD c2 then F
    else if ORD c2 < ORD c1 then st_submap (Branch c1 t1 t2) u2
    else st_submap t1 u1 ∧ st_submap t2 u2
End

Definition st_lex_def:
  st_lex t = (case st_get_nil t of
              | NONE => st_branches t
              | SOME v => ("",v) :: st_branches t) ∧
  st_branches Nothing = [] ∧
  st_branches (Just x) = [] ∧
  st_branches (Branch c t1 t2) =
    MAP (λ(k,v). (STRING c k, v)) (st_lex t1) ++ st_branches t2
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL t => str_trie_size (K 0) t * 2 + 1
                           | INR t => str_trie_size (K 0) t * 2)’
End

Definition st_lex_acc_def:
  st_lex_acc t rp acc =
    (case st_get_nil t of
     | NONE => st_branches_acc t rp acc
     | SOME v => (REVERSE rp, v) :: st_branches_acc t rp acc) ∧
  st_branches_acc Nothing rp acc = acc ∧
  st_branches_acc (Just x) rp acc = acc ∧
  st_branches_acc (Branch c t1 t2) rp acc =
    st_lex_acc t1 (c::rp) (st_branches_acc t2 rp acc)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (t,rp,acc) => str_trie_size (K 0) t * 2 + 1
                           | INR (t,rp,acc) => str_trie_size (K 0) t * 2)’
End

Definition st_to_list_def:
  st_to_list t = st_lex_acc t [] []
End

(* verification *)

Definition st_flat_def:
  st_flat Nothing = [] ∧
  st_flat (Just a) = [("",a)] ∧
  st_flat (Branch c t1 t2) = MAP (λ(k,v). (c::k,v)) (st_flat t1) ++ st_flat t2
End

Definition st_sorted_def:
  st_sorted Nothing = T ∧
  st_sorted (Just x) = T ∧
  st_sorted (Branch c t1 t2) = (t1 ≠ Nothing ∧ st_sorted t1 ∧
                                st_sorted t2 ∧
                                ∀c' t1' t2'. t2 = Branch c' t1' t2' ⇒ c < c')
End

Theorem st_sorted_base[simp]:
  st_sorted Nothing ∧ st_sorted (Just x)
Proof
  rw[st_sorted_def]
QED

Theorem st_make_not_nothing[simp]:
  st_make xs y ≠ Nothing
Proof
  Cases_on`xs` \\ rw[]
QED

Theorem st_sorted_st_make[simp]:
  ∀xs y. st_sorted (st_make xs y)
Proof
  Induct \\ rw[st_make_def, st_sorted_def]
QED

Theorem st_get_st_make:
  ∀xs y n. st_get (st_make xs y) n = if n = xs then SOME y else NONE
Proof
  Induct \\ rw[st_get_def, st_make_def, st_get_nil_def,
               stringTheory.char_lt_def, stringTheory.char_gt_def] >>
  qmatch_goalsub_rename_tac`st_get _ ls` >>
  Cases_on`ls` >> gvs[st_get_def, st_get_nil_def] >> rw[] >>
  gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] >>
  qpat_x_assum`_ <> _`mp_tac \\ rw[] >>
  irule $ iffLR stringTheory.ORD_11 >> simp[]
QED

Theorem st_get_Nothing[simp]:
  ∀xs. st_get Nothing xs = NONE
Proof
  Cases \\ fs [st_get_def, st_get_nil_def]
QED

Theorem st_del_Nothing[simp]:
  ∀xs. st_del Nothing xs = Nothing
Proof
  Cases \\ fs [st_del_def, st_del_nil_def, st_del_cons_def]
QED

Theorem st_sorted_st_set_nil[simp]:
  ∀t y. st_sorted t ⇒ st_sorted (st_set_nil t y)
Proof
  Induct \\ rw [st_set_nil_def, st_sorted_def] >>
  qmatch_asmsub_rename_tac`st_set_nil tt _ = _` >>
  Cases_on`tt` \\ gvs[st_set_nil_def]
QED

Theorem st_set_nil_not_nothing[simp]:
  st_set_nil t y ≠ Nothing
Proof
  Cases_on`t` \\ rw[]
QED

Theorem st_set_cons_not_nothing[simp]:
  st_set_cons t x xs y ≠ Nothing
Proof
  Cases_on`t` \\ rw[st_set_cons_def]
QED

Theorem st_sorted_st_set_cons[simp]:
  ∀t x xs y. st_sorted t ⇒ st_sorted (st_set_cons t x xs y)
Proof
  Induct \\ rw[st_set_cons_def, st_sorted_def]
  >> gvs[stringTheory.char_lt_def, stringTheory.char_gt_def]
  >- (
    qmatch_asmsub_rename_tac`st_set_cons tt _ _ _ = _` >>
    Cases_on`tt` \\ gvs[st_set_cons_def] >>
    gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] >>
    qmatch_asmsub_rename_tac`ORD c2 > _` >>
    qmatch_goalsub_rename_tac`_ < ORD c1` >>
    Cases_on`c1 = c2` >> gvs[] >>
    gvs[CaseEq"bool"]) >>
  CASE_TAC \\ gvs[]
QED

Theorem st_sorted_st_sets[simp]:
  st_sorted t ⇒ st_sorted (st_sets t xs)
Proof
  Induct_on`xs` \\ simp[st_sets_def] >>
  Cases >> simp[st_sets_def] >> rw[] >>
  qmatch_goalsub_rename_tac`st_set _ s _` >>
  Cases_on`s` >> gvs[st_set_def]
QED

(* When st_sorted t and t = Branch c t1 t2, looking up (h::rest) where
   h < c should give NONE, because all branches in the chain have chars ≥ c *)
Theorem st_get_cons_sorted_lt:
  ∀t h rest. st_sorted t ⇒
    (∀c' t1' t2'. t = Branch c' t1' t2' ⇒ h < c') ⇒
    st_get_cons t h rest = NONE
Proof
  Induct \\ rw [st_get_def, st_sorted_def]
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ first_x_assum irule \\ rw [st_sorted_def]
  \\ res_tac \\ fs []
QED

Theorem ALOOKUP_MAP_CONS_CONS[local]:
  ALOOKUP (MAP (λ(k,v). (c::k,v)) ls) (d::rest) =
  if c = d then ALOOKUP ls rest else NONE
Proof
  Induct_on`ls` \\ rw[] \\ pairarg_tac \\ gvs[]
QED

Theorem ALOOKUP_st_flat:
  st_sorted t ⇒ ALOOKUP (st_flat t) n = st_get t n
Proof
  qid_spec_tac `n` \\ Induct_on `t`
  \\ rw [st_flat_def, st_sorted_def]
  >- rw[st_get_def, st_get_nil_def]
  >- (Cases_on `n` \\ fs [st_get_def, st_get_nil_def])
  \\ Cases_on `n`
  >- (
    simp [ALOOKUP_APPEND, st_get_def, st_get_nil_def] >>
    CASE_TAC >> imp_res_tac ALOOKUP_MEM >>
    gvs[MEM_MAP, EXISTS_PROD] ) >>
  simp [ALOOKUP_APPEND, st_get_def, ALOOKUP_MAP_CONS_CONS] >>
  rw []
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]
  >- (
    CASE_TAC >>
    irule st_get_cons_sorted_lt >>
    rw[stringTheory.char_lt_def] )
  >- (
    irule st_get_cons_sorted_lt >>
    rw[stringTheory.char_lt_def] >>
    CCONTR_TAC >> gvs[NOT_LESS] ) >>
  `ORD c <> ORD h` by simp[stringTheory.ORD_11] >>
  gvs[]
QED

Theorem st_get_nil_st_set_nil[simp]:
  ∀t y. st_get_nil (st_set_nil t y) = SOME y
Proof
  Induct \\ rw [st_set_nil_def, st_get_nil_def]
QED

Theorem st_get_cons_st_set_nil[simp]:
  ∀t y x xs. st_get_cons (st_set_nil t y) x xs = st_get_cons t x xs
Proof
  Induct \\ rw [st_set_nil_def, st_get_def]
QED

Theorem st_get_nil_st_set_cons[simp]:
  ∀t x xs y. st_get_nil (st_set_cons t x xs y) = st_get_nil t
Proof
  Induct \\ rw [st_set_cons_def, st_get_nil_def]
  \\ gvs [st_get_nil_def]
QED

Theorem st_get_nil_st_make:
  ∀xs y. st_get_nil (st_make xs y) = if xs = [] then SOME y else NONE
Proof
  Cases \\ rw [st_make_def, st_get_nil_def]
QED

Theorem st_get_cons_st_set_cons:
  ∀t x xs y h rest.
    st_sorted t ⇒
    st_get_cons (st_set_cons t x xs y) h rest =
      if h = x ∧ rest = xs then SOME y
      else st_get_cons t h rest
Proof
  Induct \\ rw[st_set_cons_def, st_get_def]
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def, st_sorted_def]
  \\ gvs[st_get_st_make]
  \\ TRY (
    rw[] >> first_x_assum irule
    \\ irule $ iffLR stringTheory.ORD_11
    \\ gvs[] ) >>
  CASE_TAC \\ gvs[st_get_def] >>
  `ORD c = ORD x ∧ ORD c = ORD h` by gvs[] >>
  gvs[stringTheory.ORD_11]
  >- (Cases_on`rest` \\ gvs[st_get_def]) >>
  Cases_on`rest=[]` \\ gvs[st_get_def] >>
  Cases_on`rest` >- gvs[] >>
  simp[st_get_def] >> IF_CASES_TAC >> simp[] >> gvs[]
QED

Theorem st_get_st_set:
  ∀t k v n. st_sorted t ⇒
    st_get (st_set t k v) n = if n = k then SOME v else st_get t n
Proof
  rpt strip_tac
  \\ Cases_on `k` \\ Cases_on `n`
  \\ fs [st_set_def, st_get_def,
         st_get_nil_st_set_nil, st_get_cons_st_set_nil,
         st_get_nil_st_set_cons, st_get_cons_st_set_cons]
  \\ rw [] \\ gvs []
QED

Theorem st_get_st_sets:
  st_sorted t ⇒
  st_get (st_sets t xs) n = case ALOOKUP xs n of NONE => st_get t n | res => res
Proof
  strip_tac
  \\ Induct_on `xs` \\ fs [st_sets_def, FORALL_PROD]
  \\ rw []
  \\ DEP_REWRITE_TAC [st_get_st_set]
  \\ rw [] \\ fs []
QED

Theorem st_sorted_not_Nothing_get:
  ∀t. st_sorted t ∧ t ≠ Nothing ⇒ ∃k v. st_get t k = SOME v
Proof
  Induct \\ rw [st_sorted_def]
  >- (qexists_tac `[]` \\ simp [st_get_def, st_get_nil_def])
  >- (rename [`st_get (Branch c t1 t2)`]
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ qexists_tac `c::k` \\ simp [st_get_def]
      \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def])
QED

Theorem st_sorted_st_get_eq:
  ∀t1 t2. st_sorted t1 ∧ st_sorted t2 ∧
  (∀n. st_get t1 n = st_get t2 n) ⇒ t1 = t2
Proof
  Induct
  >- (Cases \\ rw [st_sorted_def]
      >- (qexists_tac`[]` \\ rw[st_get_def]) >>
      CCONTR_TAC \\ gvs[] >>
      drule_all st_sorted_not_Nothing_get >>
      simp[] >> rpt strip_tac >>
      first_x_assum(qspec_then`c::k`mp_tac) >>
      simp[st_get_def, stringTheory.char_gt_def, stringTheory.char_lt_def])
  >- (Cases_on`t2` \\ rw [st_sorted_def]
      >- (qexists_tac`[]` \\ rw[st_get_def])
      >- (first_x_assum (qspec_then `[]` mp_tac)
          \\ rw [st_get_def, st_get_nil_def]) >>
      CCONTR_TAC \\ gvs[] >>
      drule_all st_sorted_not_Nothing_get \\ rw[] >>
      first_x_assum (qspec_then `c::k` mp_tac)
      \\ simp [st_get_def, st_get_nil_def]
      \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]) >>
  Cases_on`t2` >> simp[st_sorted_def]
  >- (
    CCONTR_TAC \\ gvs[] >>
    drule_all st_sorted_not_Nothing_get >> rw[] >>
    first_x_assum (qspec_then `c::k` mp_tac)
    \\ simp [st_get_def, st_get_nil_def]
    \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def])
  >- (
    CCONTR_TAC \\ gvs[] >>
    drule_all st_sorted_not_Nothing_get >> rw[] >>
    first_x_assum (qspec_then `c::k` mp_tac)
    \\ simp [st_get_def, st_get_nil_def]
    \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]) >>
  gen_tac >> strip_tac >>
  Cases_on`char_lt c c'`
  >- (
    qspec_then`s`mp_tac st_sorted_not_Nothing_get >>
    impl_tac >- rw[] >> strip_tac >>
    first_assum(qspec_then`c::k`mp_tac) >>
    simp_tac(srw_ss())[st_get_def] >>
    gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] ) >>
  Cases_on`char_lt c' c`
  >- (
    qspec_then`t1`mp_tac st_sorted_not_Nothing_get >>
    impl_tac >- rw[] >> strip_tac >>
    first_assum(qspec_then`c'::k`mp_tac) >>
    simp_tac(srw_ss())[st_get_def] >>
    gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] ) >>
  `ORD c = ORD c'` by gvs[stringTheory.char_lt_def] >>
  gvs[stringTheory.ORD_11] >>
  conj_tac
  >- (
    first_x_assum irule \\ simp[] >>
    gen_tac >>
    first_x_assum(qspec_then`c::n`mp_tac) >>
    simp[st_get_def, stringTheory.char_gt_def] ) >>
  first_x_assum irule \\ simp[] >> gen_tac >>
  first_x_assum(qspec_then`n`mp_tac) >>
  Cases_on`n` \\ simp[st_get_def] >>
  Cases_on`char_lt c h` >> gvs[]
  >- gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] >>
  strip_tac >>
  gvs[stringTheory.char_lt_def, stringTheory.char_gt_def] >>
  qmatch_goalsub_abbrev_tac `sg1 = sg2` >>
  `sg1 = NONE ∧ sg2 = NONE` suffices_by rw[] >>
  unabbrev_all_tac >>
  conj_tac >> irule st_get_cons_sorted_lt >> gvs[] >>
  rpt strip_tac >> first_x_assum drule >>
  gvs[stringTheory.char_lt_def, stringTheory.char_gt_def]
QED

Theorem st_sets_eq:
  st_sorted t ⇒ ALOOKUP xs = ALOOKUP ys ⇒ st_sets t xs = st_sets t ys
Proof
  rw []
  \\ irule st_sorted_st_get_eq
  \\ rw []
  \\ DEP_REWRITE_TAC [st_get_st_sets] \\ fs []
QED

Theorem st_sorted_st_del_nil[simp]:
  ∀t. st_sorted t ⇒ st_sorted (st_del_nil t)
Proof
  Induct \\ rw [st_del_nil_def, st_sorted_def] >>
  Cases_on`t'` \\ gvs[]
QED

Theorem mk_Branch_thm:
  mk_Branch c t1 t2 = if t1 = Nothing then t2 else Branch c t1 t2
Proof
  Cases_on ‘t1’ \\ gvs [mk_Branch_def]
QED

Theorem st_sorted_mk_Branch:
  st_sorted (mk_Branch c t1 t2) ⇔
    st_sorted t1 ∧ st_sorted t2 ∧
    (t1 ≠ Nothing ⇒ ∀c' t1' t2'. t2 = Branch c' t1' t2' ⇒ c < c')
Proof
  rw [mk_Branch_thm, st_sorted_def] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem st_del_cons_not_Branch_Nothing:
  ∀t x xs c rest. st_sorted t ⇒
    st_del_cons t x xs ≠ Branch c Nothing rest
Proof
  Induct \\ rw [st_del_cons_def, st_sorted_def]
  \\ gvs [mk_Branch_thm, AllCaseEqs()]
  \\ gvs[stringTheory.char_gt_def, stringTheory.char_lt_def]
  \\ `ORD c = ORD x` by gvs[]
  \\ gvs[stringTheory.ORD_11]
  \\ CCONTR_TAC \\ gvs[]
  \\ gvs[Once(oneline st_del_nil_def),AllCaseEqs(),st_sorted_def]
QED

Theorem st_sorted_st_del_cons[simp]:
  ∀t x xs. st_sorted t ⇒ st_sorted (st_del_cons t x xs)
Proof
  Induct \\ rw [st_del_cons_def, st_sorted_def]
  \\ gvs [st_sorted_def, st_sorted_mk_Branch]
  \\ TRY (CASE_TAC \\ gvs [])
  \\ pop_assum mp_tac
  \\ simp[Once(oneline st_del_cons_def)]
  \\ BasicProvers.TOP_CASE_TAC \\ gvs[]
  \\ gvs[stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ rw[] \\ gvs[]
  \\ gvs[mk_Branch_thm, AllCaseEqs(), st_sorted_def]
  \\ Cases_on`s` \\ gvs[stringTheory.char_lt_def]
QED

Theorem st_sorted_st_del[simp]:
  ∀t k. st_sorted t ⇒ st_sorted (st_del t k)
Proof
  rpt strip_tac \\ Cases_on `k`
  \\ fs [st_del_def]
QED

Theorem st_get_nil_st_del_nil[simp]:
  ∀t. st_get_nil (st_del_nil t) = NONE
Proof
  Induct \\ rw [st_del_nil_def, st_get_nil_def]
QED

Theorem st_get_cons_st_del_nil[simp]:
  ∀t x xs. st_get_cons (st_del_nil t) x xs = st_get_cons t x xs
Proof
  Induct \\ rw [st_del_nil_def, st_get_def]
QED

Theorem st_get_nil_mk_Branch[simp]:
  ∀c t1 t2. st_get_nil (mk_Branch c t1 t2) = st_get_nil t2
Proof
  rw [mk_Branch_thm, st_get_nil_def]
QED

Theorem st_get_cons_mk_Branch:
  ∀c t1 t2 x xs.
    st_get_cons (mk_Branch c t1 t2) x xs =
    if t1 = Nothing then st_get_cons t2 x xs
    else st_get_cons (Branch c t1 t2) x xs
Proof
  rw [mk_Branch_thm]
QED

Theorem st_get_nil_st_del_cons[simp]:
  ∀t x xs. st_get_nil (st_del_cons t x xs) = st_get_nil t
Proof
  Induct \\ rw [st_del_cons_def, st_get_nil_def]
  \\ gvs [st_get_nil_def, mk_Branch_thm]
QED

Theorem st_get_cons_st_del_cons:
  ∀t x xs h rest.
    st_sorted t ⇒
    st_get_cons (st_del_cons t x xs) h rest =
      if h = x ∧ rest = xs then NONE
      else st_get_cons t h rest
Proof
  Induct
  \\ simp[st_del_cons_def, st_get_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def, st_sorted_def]
  \\ rw [st_get_cons_mk_Branch, st_get_def]
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ CASE_TAC \\ rw[]
  \\ gvs [st_get_def, st_get_nil_st_del_nil,
          st_get_cons_st_del_nil, st_get_nil_def]
  \\ TRY (
    simp[Once(oneline st_get_def)]
    \\ CASE_TAC
    \\ simp[stringTheory.char_lt_def, stringTheory.char_gt_def]
    \\ gvs[] \\ NO_TAC) >>
  gvs[NOT_LESS, NOT_GREATER] >>
  imp_res_tac LE_ANTISYM >>
  imp_res_tac stringTheory.ORD_11 >>
  rpt BasicProvers.VAR_EQ_TAC >> gvs[]
  >- (
    Cases_on`t` \\ gvs[st_get_def] >>
    drule st_get_cons_sorted_lt >>
    simp[stringTheory.char_lt_def] >>
    Cases_on`rest` \\ rw[st_get_def] )
  >- ( Cases_on`rest` \\ rw[st_get_def] )
  >- (
    qmatch_goalsub_abbrev_tac`sg1 = sg2` \\
    `sg1 = NONE ∧ sg2 = NONE` suffices_by rw[] \\
    unabbrev_all_tac \\
    conj_tac >- ( irule st_get_cons_sorted_lt \\ rw[stringTheory.char_lt_def] )
    >> Cases_on`rest` \\ gvs[st_get_def]
    >- (
      irule EQ_TRANS
      \\ `st_get_nil Nothing = NONE` by simp[]
      \\ goal_assum $ drule_at Any
      \\ qpat_assum`_ = Nothing`(SUBST1_TAC o SYM)
      \\ simp[] )
    \\ qmatch_asmsub_rename_tac`st_del_cons t h1 t2`
    \\ last_x_assum(qspecl_then[`h1`,`t2`]mp_tac)
    \\ simp[]
    \\ qmatch_goalsub_rename_tac`st_get_cons t h t3`
    \\ disch_then(qspecl_then[`h`,`t3`]mp_tac)
    \\ rw[st_get_def] ) >>
  Cases_on`rest` \\ gvs[st_get_def] >> rw[]
QED

Theorem st_get_st_del:
  ∀t k n. st_sorted t ⇒
    st_get (st_del t k) n = if n = k then NONE else st_get t n
Proof
  rpt strip_tac
  \\ Cases_on `k` \\ Cases_on `n`
  \\ fs [st_del_def, st_get_def,
         st_get_nil_st_del_nil, st_get_cons_st_del_nil,
         st_get_nil_st_del_cons, st_get_cons_st_del_cons]
  \\ rw [] \\ gvs []
QED

Theorem st_sorted_st_set[simp]:
  st_sorted t ⇒
  st_sorted (st_set t m x)
Proof
  Cases_on`m` \\ rw[]
QED

Theorem st_del_st_set:
  st_sorted t ⇒
  st_del (st_set t n x) m = if m = n then st_del t m
    else st_set (st_del t m) n x
Proof
  rw []
  \\ irule st_sorted_st_get_eq \\ rw []
  \\ DEP_REWRITE_TAC [st_get_st_del, st_get_st_set]
  \\ rw [] \\ gvs []
QED

Theorem st_del_st_sets:
  st_sorted t ⇒
  st_del (st_sets t xs) n = st_sets (st_del t n) (FILTER (λ(k,v). k ≠ n) xs)
Proof
  strip_tac
  \\ Induct_on `xs`
  \\ fs [st_sets_def, FORALL_PROD]
  \\ rw []
  \\ DEP_REWRITE_TAC [st_del_st_set]
  \\ rw []
  \\ simp [st_sets_def]
QED

Theorem st_union_eq_Nothing[simp]:
  st_union t u = Nothing ⇔ t = Nothing ∧ u = Nothing
Proof
  Cases_on ‘t’ \\ Cases_on ‘u’ \\ gvs [st_union_def] \\ rw []
QED

Theorem st_union_Branch:
  ∀t u c t1 t2.
    st_union t u = Branch c t1 t2 ⇒
    (∃x y. t = Branch c x y) ∨ (∃x y. u = Branch c x y)
Proof
  Cases \\ Cases \\ gvs [st_union_def] \\ rw [] \\ gvs []
QED

Theorem st_sorted_st_union[simp]:
  ∀t1 t2.
    st_sorted t1 ∧ st_sorted t2 ⇒
    st_sorted (st_union t1 t2)
Proof
  ho_match_mp_tac st_union_ind \\ rw [st_union_def, st_sorted_def]
  \\ gvs [st_sorted_def]
  \\ drule st_union_Branch \\ strip_tac \\ gvs []
  \\ res_tac \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_get_nil_st_union:
  ∀t u.
    st_get_nil (st_union t u) =
    case st_get_nil t of
    | SOME r => SOME r
    | NONE => st_get_nil u
Proof
  ho_match_mp_tac st_union_ind \\ rw [st_union_def]
  \\ CASE_TAC \\ gvs []
QED

Theorem option_case_id[local]:
  (case x of NONE => NONE | SOME r => SOME r) = x
Proof
  Cases_on ‘x’ \\ gvs []
QED

Theorem st_get_st_union:
  ∀t1 t2 n.
    st_sorted t1 ∧ st_sorted t2 ⇒
    st_get (st_union t1 t2) n =
    case st_get t1 n of
    | SOME r => SOME r
    | NONE => st_get t2 n
Proof
  ho_match_mp_tac st_union_ind \\ rpt strip_tac
  \\ Cases_on ‘n’
  \\ gvs [st_union_def, st_get_def, st_get_nil_st_union, option_case_id]
  \\ gvs [st_sorted_def]
  >- (rename [‘st_get_cons (st_union (Just x) u) h s’]
      \\ first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def])
  >- (rename [‘st_get_cons (st_union u (Just x)) h s’]
      \\ first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, option_case_id])
  \\ rename [‘st_get_cons (if ORD c1 < ORD c2 then _ else _) h s’]
  \\ Cases_on ‘ORD c1 < ORD c2’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [option_case_id])
  \\ Cases_on ‘ORD c2 < ORD c1’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [option_case_id])
  \\ ‘c1 = c2’ by gvs [GSYM stringTheory.ORD_11] \\ gvs []
  \\ rename [‘st_get_cons (Branch c (st_union l1 r1) (st_union l2 r2)) h s’]
  \\ qpat_x_assum ‘∀n. st_get (st_union l2 r2) n = _’
       (qspec_then ‘STRING h s’ mp_tac)
  \\ qpat_x_assum ‘∀n. st_get (st_union l1 r1) n = _’
       (qspec_then ‘s’ mp_tac)
  \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ rw [] \\ gvs [option_case_id]
QED

Theorem st_inter_Just_left[local]:
  ∀u x. st_inter (Just x) u =
        case st_get_nil u of
        | NONE => Nothing
        | SOME _ => Just x
Proof
  Induct \\ gvs [st_inter_def]
QED

Theorem st_inter_Just_right[local]:
  ∀t x. st_inter t (Just x) =
        case st_get_nil t of
        | NONE => Nothing
        | SOME y => Just y
Proof
  Induct \\ gvs [st_inter_def]
QED

Theorem st_inter_Branch_le[local]:
  ∀t u c' t1 t2.
    st_sorted t ∧ st_inter t u = Branch c' t1 t2 ⇒
    ∃d s1 s2. t = Branch d s1 s2 ∧ ORD d ≤ ORD c'
Proof
  ho_match_mp_tac st_inter_ind \\ rpt strip_tac
  \\ gvs [st_inter_def, st_inter_Just_left, st_inter_Just_right, AllCaseEqs()]
  \\ gvs [st_sorted_def, mk_Branch_thm, AllCaseEqs()]
  \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_sorted_st_inter[simp]:
  ∀t u.
    st_sorted t ∧ st_sorted u ⇒
    st_sorted (st_inter t u)
Proof
  ho_match_mp_tac st_inter_ind \\ rpt strip_tac
  \\ gvs [st_inter_def, st_inter_Just_left, st_inter_Just_right, AllCaseEqs()]
  \\ gvs [st_sorted_def]
  \\ rw [st_sorted_mk_Branch]
  \\ drule_all st_inter_Branch_le
  \\ rw [] \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_get_nil_st_inter:
  ∀t u.
    st_get_nil (st_inter t u) =
    case st_get_nil u of
    | NONE => NONE
    | SOME _ => st_get_nil t
Proof
  ho_match_mp_tac st_inter_ind \\ rw [st_inter_def]
  \\ CASE_TAC \\ gvs []
QED

Theorem st_get_st_inter:
  ∀t1 t2 n.
    st_sorted t1 ∧ st_sorted t2 ⇒
    st_get (st_inter t1 t2) n =
    case st_get t2 n of
    | NONE => NONE
    | SOME _ => st_get t1 n
Proof
  ho_match_mp_tac st_inter_ind \\ rpt strip_tac
  \\ Cases_on ‘n’
  \\ gvs [st_inter_def, st_get_def, st_get_nil_st_inter, option_case_id,
          st_inter_Just_left, st_inter_Just_right]
  \\ gvs [st_sorted_def]
  >- (rpt CASE_TAC \\ gvs [st_get_def])
  >- (rpt CASE_TAC \\ gvs [st_get_def])
  >- (rpt CASE_TAC \\ gvs [st_get_def])
  \\ rename [‘st_get_cons (if ORD c1 < ORD c2 then _ else _) h s’]
  \\ Cases_on ‘ORD c1 < ORD c2’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [] \\ rpt CASE_TAC \\ gvs [])
  \\ Cases_on ‘ORD c2 < ORD c1’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [] \\ rpt CASE_TAC \\ gvs [])
  \\ ‘c1 = c2’ by gvs [GSYM stringTheory.ORD_11] \\ gvs []
  \\ rename [‘st_get_cons (mk_Branch c (st_inter l1 r1) (st_inter l2 r2)) h s’]
  \\ qpat_x_assum ‘∀n. st_get (st_inter l2 r2) n = _’
       (qspec_then ‘STRING h s’ mp_tac)
  \\ qpat_x_assum ‘∀n. st_get (st_inter l1 r1) n = _’
       (qspec_then ‘s’ mp_tac)
  \\ gvs [st_get_cons_mk_Branch, st_get_def,
          stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ rw [] \\ gvs []
  \\ ‘st_get_cons l2 h s = NONE’ by
       (irule st_get_cons_sorted_lt
        \\ gvs [stringTheory.char_lt_def] \\ rw [] \\ res_tac \\ gvs [])
  \\ gvs [] \\ rpt CASE_TAC \\ gvs []
QED

Theorem st_minus_Just_left[local]:
  ∀u x. st_minus (Just x) u =
        case st_get_nil u of
        | NONE => Just x
        | SOME _ => Nothing
Proof
  Induct \\ gvs [st_minus_def]
QED

Theorem st_minus_Branch_le[local]:
  ∀t u c' t1 t2.
    st_sorted t ∧ st_minus t u = Branch c' t1 t2 ⇒
    ∃d s1 s2. t = Branch d s1 s2 ∧ ORD d ≤ ORD c'
Proof
  ho_match_mp_tac st_minus_ind \\ rpt strip_tac
  \\ gvs [st_minus_def, st_minus_Just_left, AllCaseEqs()]
  \\ gvs [st_sorted_def, mk_Branch_thm, AllCaseEqs()]
  \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_sorted_st_minus[simp]:
  ∀t u.
    st_sorted t ∧ st_sorted u ⇒
    st_sorted (st_minus t u)
Proof
  ho_match_mp_tac st_minus_ind \\ rpt strip_tac
  \\ gvs [st_minus_def, st_minus_Just_left, AllCaseEqs()]
  \\ gvs [st_sorted_def]
  \\ rw [st_sorted_mk_Branch, st_sorted_def]
  \\ drule_all st_minus_Branch_le
  \\ rw [] \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_get_nil_st_minus:
  ∀t u.
    st_get_nil (st_minus t u) =
    case st_get_nil u of
    | NONE => st_get_nil t
    | SOME _ => NONE
Proof
  ho_match_mp_tac st_minus_ind \\ rw [st_minus_def]
  \\ CASE_TAC \\ gvs []
QED

Theorem st_get_st_minus:
  ∀t1 t2 n.
    st_sorted t1 ∧ st_sorted t2 ⇒
    st_get (st_minus t1 t2) n =
    case st_get t2 n of
    | NONE => st_get t1 n
    | SOME _ => NONE
Proof
  ho_match_mp_tac st_minus_ind \\ rpt strip_tac
  \\ Cases_on ‘n’
  \\ gvs [st_minus_def, st_get_def, st_get_nil_st_minus, option_case_id,
          st_minus_Just_left]
  \\ gvs [st_sorted_def]
  >- (rpt CASE_TAC \\ gvs [st_get_def])
  >- (rpt CASE_TAC \\ gvs [st_get_def])
  >- (rename [‘st_get_cons (st_minus u (Just x)) h s’]
      \\ first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def])
  \\ rename [‘st_get_cons (if ORD c1 < ORD c2 then _ else _) h s’]
  \\ Cases_on ‘ORD c1 < ORD c2’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [] \\ rpt CASE_TAC \\ gvs [])
  \\ Cases_on ‘ORD c2 < ORD c1’ \\ gvs []
  >- (first_x_assum (qspec_then ‘STRING h s’ mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      \\ rw [] \\ gvs [] \\ rpt CASE_TAC \\ gvs [])
  \\ ‘c1 = c2’ by gvs [GSYM stringTheory.ORD_11] \\ gvs []
  \\ rename [‘st_get_cons (mk_Branch c (st_minus l1 r1) (st_minus l2 r2)) h s’]
  \\ qpat_x_assum ‘∀n. st_get (st_minus l2 r2) n = _’
       (qspec_then ‘STRING h s’ mp_tac)
  \\ qpat_x_assum ‘∀n. st_get (st_minus l1 r1) n = _’
       (qspec_then ‘s’ mp_tac)
  \\ gvs [st_get_cons_mk_Branch, st_get_def,
          stringTheory.char_lt_def, stringTheory.char_gt_def]
  \\ rw [] \\ gvs []
  \\ ‘st_get_cons l2 h s = NONE’ by
       (irule st_get_cons_sorted_lt
        \\ gvs [stringTheory.char_lt_def] \\ rw [] \\ res_tac \\ gvs [])
  \\ gvs [] \\ rpt CASE_TAC \\ gvs []
QED

Theorem st_card_st_flat[local]:
  ∀t. st_card t = LENGTH (st_flat t)
Proof
  Induct \\ gvs [st_card_def, st_flat_def]
QED

Theorem MEM_st_flat_lt[local]:
  ∀t c k v.
    st_sorted t ∧ (∀d t1 t2. t = Branch d t1 t2 ⇒ c < d) ∧
    MEM (k,v) (st_flat t) ⇒
    k = [] ∨ ∃d k'. k = STRING d k' ∧ c < d
Proof
  Induct \\ gvs [st_flat_def, st_sorted_def, MEM_MAP, EXISTS_PROD]
  \\ rw [] \\ gvs []
  \\ last_x_assum drule_all \\ rw [] \\ gvs [stringTheory.char_lt_def]
QED

Theorem MAP_FST_MAP_CONS[local]:
  MAP FST (MAP (λ(k,v). (STRING c k,v)) l) = MAP (STRING c) (MAP FST l)
Proof
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem ALL_DISTINCT_st_flat[local]:
  ∀t. st_sorted t ⇒ ALL_DISTINCT (MAP FST (st_flat t))
Proof
  Induct \\ gvs [st_flat_def, st_sorted_def]
  \\ rw [MAP_FST_MAP_CONS, ALL_DISTINCT_APPEND]
  >- (irule ALL_DISTINCT_MAP_INJ \\ gvs [])
  \\ gvs [MEM_MAP] \\ rw []
  \\ CCONTR_TAC \\ gvs [MEM_MAP, EXISTS_PROD]
  \\ drule MEM_st_flat_lt \\ disch_then drule \\ gvs []
  \\ Cases_on ‘y’ \\ gvs []
  \\ first_assum $ irule_at Any \\ gvs [stringTheory.char_lt_def]
QED

Theorem st_submap_thm:
  ∀t u.
    st_sorted t ∧ st_sorted u ⇒
    (st_submap t u ⇔ ∀k v. st_get t k = SOME v ⇒ st_get u k = SOME v)
Proof
  ho_match_mp_tac st_submap_ind \\ rpt strip_tac
  \\ gvs [st_submap_def, st_get_def, st_sorted_def]
  >- (qexists_tac ‘[]’ \\ gvs [st_get_def])
  >- (irule st_sorted_not_Nothing_get \\ gvs [st_sorted_def])
  >- (eq_tac \\ rw [] \\ gvs [st_get_def]
      \\ first_x_assum (qspecl_then [‘[]’,‘x’] mp_tac) \\ gvs [st_get_def])
  >- (eq_tac \\ rw [] \\ Cases_on ‘k’ \\ gvs [st_get_def]
      \\ first_x_assum (qspecl_then [‘[]’,‘v’] mp_tac) \\ gvs [st_get_def])
  >- (rename [‘Branch c l1 l2’]
      \\ qspec_then ‘l1’ mp_tac st_sorted_not_Nothing_get \\ gvs [] \\ rw []
      \\ qexists_tac ‘STRING c k’ \\ qexists_tac ‘v’
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def])
  \\ rename [‘st_get (Branch c1 l1 l2) _ = SOME _ ⇒
              st_get (Branch c2 r1 r2) _ = SOME _’]
  \\ Cases_on ‘ORD c1 < ORD c2’ \\ gvs []
  >- (qspec_then ‘l1’ mp_tac st_sorted_not_Nothing_get \\ gvs [] \\ rw []
      \\ qexists_tac ‘STRING c1 k’ \\ qexists_tac ‘v’
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def])
  \\ Cases_on ‘ORD c2 < ORD c1’ \\ gvs []
  >- (‘∀k v. st_get (Branch c1 l1 l2) k = SOME v ⇒
             st_get (Branch c2 r1 r2) k = st_get r2 k’ by
        (Cases \\ gvs [st_get_def, stringTheory.char_lt_def,
                       stringTheory.char_gt_def]
         \\ rw [] \\ gvs [])
      \\ eq_tac \\ rw [] \\ res_tac \\ gvs [])
  \\ ‘c1 = c2’ by gvs [GSYM stringTheory.ORD_11] \\ gvs []
  \\ ‘∀h rest. st_get_cons l2 h rest ≠ NONE ⇒ ORD c1 < ORD h’ by
       (rpt strip_tac \\ CCONTR_TAC
        \\ qspecl_then [‘l2’,‘h’,‘rest’] mp_tac st_get_cons_sorted_lt
        \\ gvs [] \\ rw [] \\ gvs [stringTheory.char_lt_def])
  \\ eq_tac \\ rw []
  >- (Cases_on ‘k’
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
      >- (qpat_x_assum ‘∀k v. st_get l2 k = _ ⇒ _’
            (qspecl_then [‘[]’,‘v’] mp_tac) \\ gvs [st_get_def])
      \\ rw []
      >- (qpat_x_assum ‘∀k v. st_get l2 k = _ ⇒ _’
            (qspecl_then [‘STRING h t’,‘v’] mp_tac) \\ gvs [st_get_def])
      \\ qpat_x_assum ‘∀k v. st_get l1 k = _ ⇒ _’
           (qspecl_then [‘t’,‘v’] mp_tac) \\ gvs [st_get_def])
  >- (first_x_assum (qspecl_then [‘STRING c1 k’,‘v’] mp_tac)
      \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def])
  \\ Cases_on ‘k’
  >- (first_x_assum (qspecl_then [‘[]’,‘v’] mp_tac) \\ gvs [st_get_def])
  \\ ‘ORD c1 < ORD h’ by
       (qpat_x_assum ‘∀h rest. st_get_cons l2 h rest ≠ NONE ⇒ _’
          (qspecl_then [‘h’,‘t’] mp_tac) \\ gvs [st_get_def])
  \\ first_x_assum (qspecl_then [‘STRING h t’,‘v’] mp_tac)
  \\ gvs [st_get_def, stringTheory.char_lt_def, stringTheory.char_gt_def]
QED

Theorem MEM_alookup[local]:
  ∀l x. MEM x (MAP FST l) ⇔ ALOOKUP l x ≠ NONE
Proof
  gvs [ALOOKUP_NONE]
QED

Theorem ALOOKUP_MAP_STRING[local]:
  ALOOKUP (MAP (λ(k,v). (STRING c k,v)) l) (STRING d rest) =
    (if c = d then ALOOKUP l rest else NONE) ∧
  ALOOKUP (MAP (λ(k,v). (STRING c k,v)) l) "" = NONE
Proof
  Induct_on ‘l’ \\ gvs [] \\ Cases \\ gvs [] \\ rw []
QED

Theorem ALOOKUP_st_lex:
  (∀t:'a str_trie. st_sorted t ⇒ ∀k. ALOOKUP (st_lex t) k = st_get t k) ∧
  (∀t:'a str_trie. st_sorted t ⇒
     ∀k. ALOOKUP (st_branches t) k = if k = "" then NONE else st_get t k)
Proof
  ho_match_mp_tac st_lex_ind \\ rw [st_lex_def, st_get_def, st_sorted_def]
  \\ Cases_on ‘k’
  \\ gvs [ALOOKUP_APPEND, ALOOKUP_MAP_STRING, st_get_def]
  \\ TRY (CASE_TAC \\ gvs [st_get_def] \\ NO_TAC)
  \\ ‘∀d rest. ORD d ≤ ORD c ⇒ st_get_cons t' d rest = NONE’ by
       (rw [] \\ irule st_get_cons_sorted_lt \\ gvs [] \\ rw []
        \\ res_tac \\ gvs [stringTheory.char_lt_def])
  \\ Cases_on ‘c = h’
  \\ gvs [stringTheory.char_lt_def, stringTheory.char_gt_def]
  >- (CASE_TAC \\ gvs [])
  \\ rw [] \\ gvs []
  \\ ‘ORD h = ORD c’ by DECIDE_TAC \\ gvs [stringTheory.ORD_11]
QED

Theorem st_lex_acc_thm[local]:
  (∀t:'a str_trie rp acc. st_lex_acc t rp acc =
     MAP (λ(k,v). (REVERSE rp ++ k, v)) (st_lex t) ++ acc) ∧
  (∀t:'a str_trie rp acc. st_branches_acc t rp acc =
     MAP (λ(k,v). (REVERSE rp ++ k, v)) (st_branches t) ++ acc)
Proof
  ho_match_mp_tac st_lex_acc_ind
  \\ rw [st_lex_acc_def, st_lex_def]
  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ CASE_TAC \\ gvs []
QED

Theorem st_to_list_thm:
  st_to_list t = st_lex t
Proof
  gvs [st_to_list_def, st_lex_acc_thm, pairTheory.ELIM_UNCURRY]
QED

Theorem MEM_st_lex[local]:
  ∀t k. st_sorted t ⇒
    (MEM k (MAP FST (st_lex t)) ⇔ st_get t k ≠ NONE) ∧
    (MEM k (MAP FST (st_branches t)) ⇔ k ≠ "" ∧ st_get t k ≠ NONE)
Proof
  rw [MEM_alookup] \\ gvs [ALOOKUP_st_lex] \\ rw [] \\ gvs []
QED

Theorem transitive_string_lt[local]:
  transitive string_lt
Proof
  gvs [relationTheory.transitive_def]
  \\ metis_tac [stringTheory.string_lt_trans]
QED

Theorem SORTED_MAP_STRING[local]:
  ∀l. SORTED string_lt (MAP (STRING c) l) ⇔ SORTED string_lt l
Proof
  Induct \\ gvs [] \\ Cases_on ‘l’
  \\ gvs [SORTED_DEF, stringTheory.string_lt_def, stringTheory.char_lt_def]
QED

Theorem SORTED_st_lex:
  (∀t:'a str_trie. st_sorted t ⇒ SORTED string_lt (MAP FST (st_lex t))) ∧
  (∀t:'a str_trie. st_sorted t ⇒ SORTED string_lt (MAP FST (st_branches t)))
Proof
  ho_match_mp_tac st_lex_ind \\ rw [st_lex_def, st_sorted_def]
  \\ gvs [SORTED_APPEND, transitive_string_lt, MAP_FST_MAP_CONS,
          SORTED_MAP_STRING]
  >- (CASE_TAC \\ gvs [SORTED_EQ, transitive_string_lt] \\ rw []
      \\ ‘y ≠ ""’ by (qspecl_then [‘t’,‘y’] mp_tac MEM_st_lex \\ gvs [])
      \\ Cases_on ‘y’ \\ gvs [stringTheory.string_lt_def])
  \\ ‘∀d rest. ORD d ≤ ORD c ⇒ st_get_cons t' d rest = NONE’ by
       (rw [] \\ irule st_get_cons_sorted_lt \\ gvs [] \\ rw []
        \\ res_tac \\ gvs [stringTheory.char_lt_def])
  \\ ‘∀y. MEM y (MAP FST (st_branches t')) ⇒
          ∃d k2. y = STRING d k2 ∧ char_lt c d’ by
       (rw [] \\ qspecl_then [‘t'’,‘y’] mp_tac MEM_st_lex \\ gvs [] \\ rw []
        \\ Cases_on ‘y’ \\ gvs []
        \\ CCONTR_TAC \\ gvs [st_get_def, stringTheory.char_lt_def]
        \\ ‘ORD h ≤ ORD c’ by DECIDE_TAC \\ res_tac \\ gvs [])
  \\ rw [] \\ gvs [MEM_MAP] \\ res_tac
  \\ gvs [stringTheory.string_lt_def]
QED

Theorem ALOOKUP_eq_NONE[local]:
  ∀l k v k'. SORTED string_lt (MAP FST ((k,v)::l)) ∧ ¬string_lt k k' ⇒
             ALOOKUP l k' = NONE
Proof
  rw [] \\ gvs [SORTED_EQ, transitive_string_lt]
  \\ CCONTR_TAC \\ gvs [GSYM MEM_alookup]
  \\ first_x_assum drule \\ gvs []
QED

Theorem sorted_alist_unique[local]:
  ∀l1 l2. SORTED string_lt (MAP FST l1) ∧ SORTED string_lt (MAP FST l2) ∧
          ALOOKUP l1 = ALOOKUP l2 ⇒ l1 = l2
Proof
  Induct \\ Cases_on ‘l2’ \\ gvs [] \\ strip_tac
  >- (Cases_on ‘h’ \\ gvs [FUN_EQ_THM]
      \\ first_x_assum (qspec_then ‘q’ mp_tac) \\ gvs [])
  >- (rw [] \\ Cases_on ‘h’ \\ gvs [FUN_EQ_THM]
      \\ first_x_assum (qspec_then ‘q’ mp_tac) \\ gvs [])
  \\ Cases_on ‘h’ \\ Cases_on ‘h'’ \\ strip_tac \\ gvs []
  \\ ‘q' = q’ by
       (CCONTR_TAC
        \\ ‘string_lt q' q ∨ string_lt q q'’ by
             metis_tac [stringTheory.string_lt_cases]
        \\ gvs [FUN_EQ_THM]
        >- (first_x_assum (qspec_then ‘q'’ mp_tac) \\ gvs []
            \\ qspecl_then [‘t’,‘q’,‘r’,‘q'’] mp_tac ALOOKUP_eq_NONE
            \\ impl_tac
            >- (gvs [] \\ metis_tac [stringTheory.string_lt_antisym])
            \\ gvs [])
        \\ first_x_assum (qspec_then ‘q’ mp_tac) \\ gvs []
        \\ qspecl_then [‘l1’,‘q'’,‘r'’,‘q’] mp_tac ALOOKUP_eq_NONE
        \\ impl_tac >- (gvs [] \\ metis_tac [stringTheory.string_lt_antisym])
        \\ gvs [])
  \\ gvs [FUN_EQ_THM]
  \\ ‘r' = r’ by (first_x_assum (qspec_then ‘q’ mp_tac) \\ gvs [])
  \\ gvs []
  \\ first_x_assum irule
  \\ gvs [SORTED_EQ, transitive_string_lt] \\ rw []
  \\ Cases_on ‘q = x’ \\ gvs []
  >- (Cases_on ‘ALOOKUP l1 q’ \\ Cases_on ‘ALOOKUP t q’ \\ gvs [MEM_alookup]
      \\ metis_tac [stringTheory.string_lt_nonrefl, optionTheory.NOT_SOME_NONE])
  \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ gvs []
QED

val _ = cv_trans st_get_nil_def;
val _ = cv_trans st_get_def;
val _ = cv_trans st_make_def;
val _ = cv_trans st_set_nil_def;
val _ = cv_trans st_set_cons_def;
val _ = cv_trans st_set_def;
val _ = cv_trans st_del_nil_def;
val _ = cv_trans mk_Branch_def;
val _ = cv_trans st_del_cons_def;
val _ = cv_trans st_del_def;

Theorem cv_size_cv_fst_cv_snd[local]:
  ∀x. cv_size (cv_fst x) + cv_size (cv_snd x) ≤ cv_size x
Proof
  Cases \\ gvs [cvTheory.cv_size_def, cvTheory.cv_fst_def, cvTheory.cv_snd_def]
QED

val _ = cv_trans_rec st_union_def
  (WF_REL_TAC ‘measure $ λ(x,y). cv_size x + cv_size y’
   \\ cv_termination_tac
   \\ rename [‘cv_size (cv_snd (cv_snd x)) + (cv_size (cv_snd (cv_snd y)) + 5)’]
   \\ qspec_then ‘x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘y’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd y’ assume_tac cv_size_cv_fst_cv_snd
   \\ gvs []);

val _ = cv_trans_rec st_inter_def
  (WF_REL_TAC ‘measure $ λ(x,y). cv_size x + cv_size y’
   \\ cv_termination_tac
   \\ rename [‘cv_size (cv_snd (cv_snd x)) + (cv_size (cv_snd (cv_snd y)) + 5)’]
   \\ qspec_then ‘x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘y’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd y’ assume_tac cv_size_cv_fst_cv_snd
   \\ gvs []);

val _ = cv_trans st_card_def;
val _ = cv_trans st_submap_def;

val st_lex_acc_pre_def = cv_trans_pre_rec "" st_lex_acc_def
  (WF_REL_TAC ‘measure (λx. case x of
                            | INL (cv,rp,acc) => cv_size cv * 2 + 1
                            | INR (cv,rp,acc) => cv_size cv * 2)’
   \\ cv_termination_tac);

Theorem st_lex_acc_pre[cv_pre]:
  (∀t:'a str_trie rp acc. st_lex_acc_pre t rp acc) ∧
  (∀t:'a str_trie rp acc. st_branches_acc_pre t rp acc)
Proof
  ho_match_mp_tac st_lex_acc_ind \\ rw [] \\ simp [Once st_lex_acc_pre_def]
QED

val _ = cv_trans st_to_list_def;

val _ = cv_trans_rec st_minus_def
  (WF_REL_TAC ‘measure $ λ(x,y). cv_size x + cv_size y’
   \\ cv_termination_tac
   \\ rename [‘cv_size (cv_snd (cv_snd x)) + (cv_size (cv_snd (cv_snd y)) + 5)’]
   \\ qspec_then ‘x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘y’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd x’ assume_tac cv_size_cv_fst_cv_snd
   \\ qspec_then ‘cv_snd y’ assume_tac cv_size_cv_fst_cv_snd
   \\ gvs []);

(*----------------------------------------------------------*
   string |-> 'a
 *----------------------------------------------------------*)

Definition from_string_fmap_def:
  from_string_fmap (f:'a -> cv) (m: string |-> 'a) =
    from_cv_string_fmap_str_trie f (st_sets Nothing (fmap_to_alist m))
End

Definition to_string_fmap_def:
  to_string_fmap (t:cv -> 'a) m =
    alist_to_fmap (st_flat (to_str_trie t m))
End

Theorem from_to_string_fmap[cv_from_to]:
  from_to (f0:'a -> cv) t0 ==>
  from_to (from_string_fmap f0) (to_string_fmap t0)
Proof
  strip_tac
  \\ drule (DISCH_ALL from_to_str_trie)
  \\ gvs [from_string_fmap_def,to_string_fmap_def,from_to_def] \\ rw []
  \\ gvs [finite_mapTheory.TO_FLOOKUP]
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ DEP_REWRITE_TAC [ALOOKUP_st_flat]
  \\ irule_at Any st_sorted_st_sets \\ simp [st_sorted_def]
  \\ gvs [st_get_st_sets,st_get_def,st_get_Nothing]
  \\ rename [‘FLOOKUP x y’] \\ Cases_on ‘FLOOKUP x y’ \\ fs []
QED

Theorem cv_rep_string_FEMPTY[cv_rep]:
  from_string_fmap f FEMPTY = Num 0
Proof
  EVAL_TAC \\ gvs [] \\ EVAL_TAC
QED

Theorem cv_rep_string_FLOOKUP[cv_rep]:
  from_option f (FLOOKUP m n) =
  cv_st_get (from_string_fmap f m) (from_list from_char n)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_get_thm"]
  \\ simp [st_get_st_sets, st_get_Nothing]
  \\ rename [‘FLOOKUP x y’] \\ Cases_on ‘FLOOKUP x y’ \\ fs []
QED

Theorem cv_rep_string_FUPDATE[cv_rep]:
  from_string_fmap f (m |+ (k,v)) =
  cv_st_set (from_string_fmap f m) (from_list from_char k) (f v)
Proof
  gvs [from_string_fmap_def,GSYM $ fetch "-" "cv_st_set_thm"] \\ AP_TERM_TAC
  \\ simp_tac std_ss [GSYM st_sets_def]
  \\ irule st_sets_eq \\ fs [finite_mapTheory.FLOOKUP_SIMP, FUN_EQ_THM]
QED

val FUPDATE_LIST_pre_def = finite_mapTheory.FUPDATE_LIST_THM
 |> SRULE [FORALL_PROD]
 |> INST_TYPE [alpha |-> “:string”]
 |> cv_trans_pre "FUPDATE_LIST_pre";

Theorem FUPDATE_LIST_pre[cv_pre]:
  ∀f ls. FUPDATE_LIST_pre f ls
Proof
  Induct_on`ls`
  \\ rw[Once FUPDATE_LIST_pre_def]
QED

Theorem cv_rep_string_DOMSUB[cv_rep]:
  from_string_fmap f (m \\ k) =
  cv_st_del (from_string_fmap f m) (from_list from_char k)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_del_thm"]
  \\ AP_TERM_TAC
  \\ simp [st_del_st_sets, st_del_Nothing]
  \\ irule st_sets_eq \\ fs [finite_mapTheory.FLOOKUP_SIMP, FUN_EQ_THM]
  \\ gvs [ALOOKUP_FILTER,finite_mapTheory.DOMSUB_FLOOKUP_THM]
  \\ rw []
QED

Theorem cv_rep_string_FUNION[cv_rep]:
  from_string_fmap f (m1 ⊌ m2) =
  cv_st_union (from_string_fmap f m1) (from_string_fmap f m2)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_union_thm"]
  \\ AP_TERM_TAC
  \\ irule st_sorted_st_get_eq
  \\ irule_at Any st_sorted_st_union
  \\ rw [st_sorted_st_sets, st_sorted_def]
  \\ DEP_REWRITE_TAC [st_get_st_union]
  \\ gvs [st_get_st_sets, st_get_Nothing, st_sorted_def, option_case_id,
          finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem cv_rep_string_FINTER[cv_rep]:
  from_string_fmap f (FINTER m1 m2) =
  cv_st_inter (from_string_fmap f m1) (from_string_fmap g m2)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_inter_thm"]
  \\ AP_TERM_TAC
  \\ irule st_sorted_st_get_eq
  \\ irule_at Any st_sorted_st_inter
  \\ rw [st_sorted_st_sets, st_sorted_def]
  \\ DEP_REWRITE_TAC [st_get_st_inter]
  \\ gvs [st_get_st_sets, st_get_Nothing, st_sorted_def, option_case_id,
          finite_mapTheory.FLOOKUP_FINTER]
QED

Theorem cv_rep_string_FMINUS[cv_rep]:
  from_string_fmap f (FMINUS m1 m2) =
  cv_st_minus (from_string_fmap f m1) (from_string_fmap g m2)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_minus_thm"]
  \\ AP_TERM_TAC
  \\ irule st_sorted_st_get_eq
  \\ irule_at Any st_sorted_st_minus
  \\ rw [st_sorted_st_sets, st_sorted_def]
  \\ DEP_REWRITE_TAC [st_get_st_minus]
  \\ gvs [st_get_st_sets, st_get_Nothing, st_sorted_def, option_case_id,
          finite_mapTheory.FLOOKUP_FMINUS]
QED

Theorem cv_rep_string_FCARD[cv_rep]:
  Num (FCARD m) = cv_st_card (from_string_fmap f m)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_card_thm"]
  \\ qmatch_goalsub_abbrev_tac ‘st_card t’
  \\ ‘st_sorted t’ by gvs [Abbr‘t’]
  \\ ‘ALOOKUP (st_flat t) = FLOOKUP m’ by
       (gvs [FUN_EQ_THM] \\ rw []
        \\ DEP_REWRITE_TAC [ALOOKUP_st_flat]
        \\ gvs [Abbr‘t’, st_get_st_sets]
        \\ CASE_TAC \\ gvs [])
  \\ ‘∀x. MEM x (MAP FST (st_flat t)) ⇔ ALOOKUP (st_flat t) x ≠ NONE’ by
       gvs [ALOOKUP_NONE]
  \\ ‘FDOM m = set (MAP FST (st_flat t))’ by
       (gvs [pred_setTheory.EXTENSION]
        \\ gvs [finite_mapTheory.FLOOKUP_DEF] \\ rw [])
  \\ gvs [st_card_st_flat, finite_mapTheory.FCARD_DEF]
  \\ DEP_REWRITE_TAC [ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ gvs [ALL_DISTINCT_st_flat]
QED

val submap_lemma = cv_rep_for [] “st_submap t u” |> DISCH_ALL;

Theorem cv_rep_string_SUBMAP[cv_rep]:
  from_to f_a t_a ⇒
  cv_rep T (cv_st_submap (from_string_fmap f_a m1) (from_string_fmap f_a m2))
        b2c (m1 ⊑ m2)
Proof
  qsuff_tac ‘m1 ⊑ m2 ⇔ st_submap (st_sets Nothing (fmap_to_alist m1))
                                 (st_sets Nothing (fmap_to_alist m2))’
  >- (simp [from_string_fmap_def]
      \\ mp_tac (submap_lemma |> Q.GENL [‘t’,‘u’]
                   |> Q.SPECL [‘st_sets Nothing (fmap_to_alist m1)’,
                               ‘st_sets Nothing (fmap_to_alist m2)’])
      \\ fs [])
  \\ DEP_REWRITE_TAC [st_submap_thm]
  \\ gvs [st_get_st_sets, option_case_id, finite_mapTheory.SUBMAP_FLOOKUP_EQN]
QED

(* the entries of a finite map, listed in increasing order of the keys *)
Definition fmap_to_sorted_list_def:
  fmap_to_sorted_list m =
    @l. ALOOKUP l = FLOOKUP m ∧ SORTED string_lt (MAP FST l)
End

Theorem fmap_to_sorted_list_eq:
  ALOOKUP l = FLOOKUP m ∧ SORTED string_lt (MAP FST l) ⇒
  fmap_to_sorted_list m = l
Proof
  rw [fmap_to_sorted_list_def] \\ SELECT_ELIM_TAC \\ rw []
  >- (qexists_tac ‘l’ \\ gvs [])
  \\ irule sorted_alist_unique \\ gvs []
QED

Theorem fmap_to_sorted_list_thm:
  ALOOKUP (fmap_to_sorted_list m) = FLOOKUP m ∧
  SORTED string_lt (MAP FST (fmap_to_sorted_list m))
Proof
  ‘∃l. ALOOKUP l = FLOOKUP m ∧ SORTED string_lt (MAP FST l)’ by
    (qexists_tac ‘st_lex (st_sets Nothing (fmap_to_alist m))’
     \\ qmatch_goalsub_abbrev_tac ‘st_lex t’
     \\ ‘st_sorted t’ by gvs [Abbr‘t’]
     \\ conj_tac
     >- (gvs [FUN_EQ_THM] \\ rw []
         \\ DEP_REWRITE_TAC [ALOOKUP_st_lex] \\ gvs [Abbr‘t’, st_get_st_sets]
         \\ CASE_TAC \\ gvs [])
     \\ irule (CONJUNCT1 SORTED_st_lex) \\ gvs [])
  \\ gvs [fmap_to_sorted_list_def] \\ SELECT_ELIM_TAC \\ rw []
  \\ metis_tac []
QED

Theorem LENGTH_fmap_to_sorted_list:
  LENGTH (fmap_to_sorted_list m) = FCARD m
Proof
  strip_assume_tac fmap_to_sorted_list_thm
  \\ ‘ALL_DISTINCT (MAP FST (fmap_to_sorted_list m))’ by
       (qspec_then ‘string_lt’ mp_tac (GEN_ALL SORTED_ALL_DISTINCT)
        \\ impl_tac
        >- gvs [transitive_string_lt, relationTheory.irreflexive_def,
                stringTheory.string_lt_nonrefl]
        \\ disch_then irule \\ gvs [])
  \\ ‘FDOM m = set (MAP FST (fmap_to_sorted_list m))’ by
       (‘∀x. MEM x (MAP FST (fmap_to_sorted_list m)) ⇔
             ALOOKUP (fmap_to_sorted_list m) x ≠ NONE’ by gvs [ALOOKUP_NONE]
        \\ gvs [pred_setTheory.EXTENSION]
        \\ gvs [finite_mapTheory.FLOOKUP_DEF] \\ rw [])
  \\ gvs [finite_mapTheory.FCARD_DEF]
  \\ DEP_REWRITE_TAC [ALL_DISTINCT_CARD_LIST_TO_SET] \\ gvs []
QED

Theorem cv_rep_string_fmap_to_sorted_list[cv_rep]:
  from_list (from_pair (from_list from_char) f) (fmap_to_sorted_list m) =
  cv_st_to_list (from_string_fmap f m)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_to_list_thm"]
  \\ AP_TERM_TAC
  \\ gvs [st_to_list_thm]
  \\ irule fmap_to_sorted_list_eq
  \\ qmatch_goalsub_abbrev_tac ‘st_lex t’
  \\ ‘st_sorted t’ by gvs [Abbr‘t’]
  \\ conj_tac
  >- (gvs [FUN_EQ_THM] \\ rw []
      \\ DEP_REWRITE_TAC [ALOOKUP_st_lex] \\ gvs [Abbr‘t’, st_get_st_sets]
      \\ CASE_TAC \\ gvs [])
  \\ irule (CONJUNCT1 SORTED_st_lex) \\ gvs []
QED
