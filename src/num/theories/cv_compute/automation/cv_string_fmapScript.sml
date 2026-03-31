(*
  Set up cv translator for string |-> 'a
*)
Theory cv_string_fmap
Ancestors
  cv cv_type arithmetic words cv_rep cv_prim pair list option sum
  alist indexedLists rich_list sptree finite_set cv_std
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
  mk_Branch x t1 t2 = if t1 = Nothing then t2 else Branch x t1 t2
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

Theorem st_sorted_mk_Branch:
  st_sorted (mk_Branch c t1 t2) ⇔
    st_sorted t1 ∧ st_sorted t2 ∧
    (t1 ≠ Nothing ⇒ ∀c' t1' t2'. t2 = Branch c' t1' t2' ⇒ c < c')
Proof
  rw [mk_Branch_def, st_sorted_def] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem st_del_cons_not_Branch_Nothing:
  ∀t x xs c rest. st_sorted t ⇒
    st_del_cons t x xs ≠ Branch c Nothing rest
Proof
  Induct \\ rw [st_del_cons_def, st_sorted_def]
  \\ gvs [mk_Branch_def, AllCaseEqs()]
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
  \\ gvs[mk_Branch_def, AllCaseEqs(), st_sorted_def]
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
  rw [mk_Branch_def, st_get_nil_def]
QED

Theorem st_get_cons_mk_Branch:
  ∀c t1 t2 x xs.
    st_get_cons (mk_Branch c t1 t2) x xs =
    if t1 = Nothing then st_get_cons t2 x xs
    else st_get_cons (Branch c t1 t2) x xs
Proof
  rw [mk_Branch_def]
QED

Theorem st_get_nil_st_del_cons[simp]:
  ∀t x xs. st_get_nil (st_del_cons t x xs) = st_get_nil t
Proof
  Induct \\ rw [st_del_cons_def, st_get_nil_def]
  \\ gvs [st_get_nil_def, mk_Branch_def]
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
  \\ cheat
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
  from_option f (FLOOKUP m n) = cv_st_get (from_string_fmap f m) (from_list from_char n)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_get_thm"]
  \\ simp [st_get_st_sets, st_get_Nothing]
  \\ rename [‘FLOOKUP x y’] \\ Cases_on ‘FLOOKUP x y’ \\ fs []
QED

Theorem cv_rep_string_FUPDATE[cv_rep]:
  from_string_fmap f (m |+ (k,v)) = cv_st_set (from_string_fmap f m) (from_list from_char k) (f v)
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
  from_to f t ⇒
  from_string_fmap f (m \\ k) = cv_st_del (from_string_fmap f m) (from_list from_char k)
Proof
  rw[from_string_fmap_def]
  \\ drule (GSYM (theorem "cv_st_del_thm" |> DISCH_ALL))
  \\ simp [] \\ disch_then kall_tac
  \\ AP_TERM_TAC
  \\ simp [st_del_st_sets, st_del_Nothing]
  \\ irule st_sets_eq \\ fs [finite_mapTheory.FLOOKUP_SIMP, FUN_EQ_THM]
  \\ gvs [ALOOKUP_FILTER,finite_mapTheory.DOMSUB_FLOOKUP_THM]
  \\ rw []
QED
