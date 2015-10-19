open HolKernel boolLib bossLib lcsymtacs Parse;
open listTheory rich_listTheory llistTheory pred_setTheory optionTheory;

val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = ParseExtras.temp_tight_equality();

val _ = new_theory "lprefix_lub";

val infinite_lnth_some = Q.store_thm ("infinite_lnth_some",
`!ll. ~LFINITE ll ⇔ !n. ?x. LNTH n ll = SOME x`,
 rw [LFINITE_LNTH_NONE] >>
 metis_tac [NOT_SOME_NONE, option_nchotomy]);

val lnth_some_down_closed = Q.store_thm ("lnth_some_down_closed",
`!ll x n1 n2.
  LNTH n1 ll = SOME x ∧
  n2 ≤ n1
  ⇒
  ?y. LNTH n2 ll = SOME y`,
 Induct_on `n1` >>
 rw [] >>
 `ll = [||] ∨ ?h t. ll = h:::t` by metis_tac [llist_CASES] >>
 fs [] >>
 Cases_on `n2` >>
 fs []);

val lnth_fromList = Q.store_thm ("lnth_fromList",
`!n l. n < LENGTH l ⇔ LNTH n (fromList l) = SOME (EL n l)`,
 Induct_on `l` >>
 rw [] >>
 Cases_on `n` >>
 rw [LNTH_THM] >>
 fs []);

val is_prefix_el = Q.store_thm ("is_prefix_el",
`!n l1 l2.
  isPREFIX l1 l2 ∧
  n < LENGTH l1 ∧ 
  n < LENGTH l2
  ⇒
  EL n l1 = EL n l2`,
 Induct_on `n` >>
 rw [] >>
 Cases_on `l1` >>
 Cases_on `l2` >>
 rw [] >>
 fs []);

val last_drop = Q.store_thm ("last_drop",
`!l n. n < LENGTH l ⇒ LAST (DROP n l) = LAST l`,
 Induct_on `l` >>
 rw [] >>
 Cases_on `l` >>
 fs [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [] >>
 first_x_assum (qspec_then `n - 1` mp_tac) >>
 simp []);

val LFINITE_LDROP_APPEND1 = Q.prove(
  `∀l. LFINITE l ⇒
      ∀n z. LDROP n l = SOME z ⇒
              ∀l2. LDROP n (LAPPEND l l2) = SOME (LAPPEND z l2)`,
  ho_match_mp_tac LFINITE_INDUCTION >> simp[] >>
  conj_tac >- ( Cases >> simp[] ) >>
  ntac 3 strip_tac >> Cases >> simp[] )

val NOT_LFINITE_DROP_LFINITE = Q.store_thm("NOT_LFINITE_DROP_LFINITE",
  `∀n l t. ¬LFINITE l ∧ LDROP n l = SOME t ⇒ ¬LFINITE t`,
  Induct >> simp[] >> gen_tac >>
  qspec_then`l`FULL_STRUCT_CASES_TAC llist_CASES >>
  simp[] >> metis_tac[])

val LDROP_APPEND1 = Q.store_thm("LDROP_APPEND1",
  `LDROP n l1 = SOME l ⇒
   LDROP n (LAPPEND l1 l2) = SOME (LAPPEND l l2)`,
  rw[] >>
  Cases_on`LFINITE l1` >- (
    metis_tac[LFINITE_LDROP_APPEND1] ) >>
  imp_res_tac NOT_LFINITE_DROP_LFINITE >>
  simp[NOT_LFINITE_APPEND])

val LDROP_fromList = Q.store_thm("LDROP_fromList",
  `∀ls n.
    LDROP n (fromList ls) =
    if n ≤ LENGTH ls then SOME (fromList (DROP n ls)) else NONE`,
  Induct >- ( Cases >> simp[] ) >>
  gen_tac >> Cases >> simp[])

val LFINITE_LDROP_SUC = Q.prove(
  `∀ls. LFINITE ls ⇒ ∀n. LDROP (SUC n) ls = OPTION_BIND (LDROP n ls) LTL`,
  ho_match_mp_tac LFINITE_INDUCTION >>
  simp[] >>
  conj_tac >- ( Cases >> simp[] ) >>
  ntac 3 strip_tac >>
  Cases >> simp[] );

val LDROP_SUC = Q.store_thm("LDROP_SUC",
  `LDROP (SUC n) ls = OPTION_BIND (LDROP n ls) LTL`,
  Cases_on`LFINITE ls` >- metis_tac[LFINITE_LDROP_SUC] >>
  `IS_SOME (LDROP n ls)` by (
    metis_tac[optionTheory.IS_SOME_DEF,NOT_LFINITE_DROP] ) >>
  `IS_SOME (LTAKE n ls)` by (
    metis_tac[IS_SOME_DEF,NOT_LFINITE_TAKE]) >>
  fs[IS_SOME_EXISTS] >>
  imp_res_tac LTAKE_DROP >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  imp_res_tac LTAKE_LENGTH >>
  simp[arithmeticTheory.ADD1] >>
  simp[LDROP_ADD] >>
  qmatch_assum_rename_tac`n = LENGTH l` >>
  `LDROP n (fromList l) = SOME [||]` by (
    simp[LDROP_fromList,rich_listTheory.DROP_LENGTH_NIL] ) >>
  var_eq_tac >>
  imp_res_tac LDROP_APPEND1 >> fs[LDROP1_THM])

val LNTH_NONE_MONO = Q.store_thm ("LNTH_NONE_MONO",
  `!m n l.
    LNTH m l = NONE ∧
    m ≤ n
    ⇒
    LNTH n l = NONE`,
  rw[] >> match_mp_tac(GEN_ALL LNTH_LLENGTH_NONE) >>
  `LFINITE l` by metis_tac[LFINITE_LNTH_NONE] >>
  `∃z. LLENGTH l = SOME z` by metis_tac[LFINITE_HAS_LENGTH] >>
  imp_res_tac LTAKE_LLENGTH_SOME >>
  imp_res_tac LTAKE_LENGTH >>
  `¬(m < z)` by metis_tac[LTAKE_LNTH_EL,NOT_SOME_NONE] >>
  rw[] >> decide_tac);

val less_opt_def = Define `
  (less_opt n NONE ⇔ T) ∧
  (less_opt n (SOME m) ⇔ n < m)`;

val less_opt_SUC_elim = Q.store_thm("less_opt_SUC_elim",
  `less_opt (SUC n) z ⇒ less_opt n z`,
  Cases_on`z`>>rw[less_opt_def]>>simp[])

val less_opt_LLENGTH_LNTH_SOME = Q.store_thm("less_opt_LLENGTH_LNTH_SOME",
  `less_opt n (LLENGTH l) ⇔ IS_SOME (LNTH n l)`,
  EQ_TAC >- (
    Cases_on`LFINITE l` >- (
      imp_res_tac LFINITE_HAS_LENGTH >>
      rw[less_opt_def] >>
      qmatch_assum_rename_tac`LLENGTH l = SOME z` >>
      `IS_SOME(LTAKE z l)` suffices_by
        metis_tac[optionTheory.IS_SOME_EXISTS,LTAKE_LNTH_EL] >>
      metis_tac[LFINITE_toList_SOME,optionTheory.THE_DEF,llistTheory.toList] ) >>
    imp_res_tac NOT_LFINITE_NO_LENGTH >>
    rw[less_opt_def] >>
    metis_tac[LFINITE_LNTH_NONE,optionTheory.option_CASES,optionTheory.IS_SOME_DEF]) >>
  rw[IS_SOME_EXISTS] >>
  Cases_on`LFINITE l` >- (
    imp_res_tac LFINITE_HAS_LENGTH >>
    simp[less_opt_def] >>
    metis_tac[
      LNTH_LLENGTH_NONE, LTAKE_LLENGTH_NONE,
      LTAKE_EQ_NONE_LNTH, NOT_NONE_SOME,
      arithmeticTheory.LESS_EQ,
      arithmeticTheory.LESS_EQ_REFL,
      arithmeticTheory.NOT_NUM_EQ])>>
  imp_res_tac NOT_LFINITE_NO_LENGTH >>
  rw[less_opt_def]);

val IS_SOME_LTAKE_less_opt_LLENGTH = Q.store_thm("IS_SOME_LTAKE_less_opt_LLENGTH",
  `IS_SOME (LTAKE n ll) ⇒ LLENGTH ll = SOME n ∨ less_opt n (LLENGTH ll)`,
  rw[IS_SOME_EXISTS] >>
  imp_res_tac LTAKE_LENGTH >> rw[] >>
  imp_res_tac LTAKE_IMP_LDROP >> rw[] >>
  rw[LLENGTH_APPEND] >> fs[LFINITE_fromList] >>
  simp[less_opt_def,LLENGTH_fromList])

val LPREFIX_NTH = Q.store_thm ("LPREFIX_NTH",
  `!ll1 ll2.
    LPREFIX ll1 ll2 ⇔ !n. less_opt n (LLENGTH ll1) ⇒ LNTH n ll1 = LNTH n ll2`,
  rw [LPREFIX_APPEND,EQ_IMP_THM]
  >- (
    imp_res_tac (#1(EQ_IMP_RULE less_opt_LLENGTH_LNTH_SOME)) >>
    fs [IS_SOME_EXISTS, LNTH_LAPPEND] >>
    every_case_tac >>
    fs [less_opt_def])
  >- (
    Cases_on `LLENGTH ll1`
    >- (
      `~LFINITE ll1` by metis_tac [LFINITE_HAS_LENGTH, NOT_SOME_NONE] >>
      fs [less_opt_def, NOT_LFINITE_APPEND] >>
      rw [LNTH_EQ])
    >- (
      fs [less_opt_def, LNTH_EQ, LNTH_LAPPEND] >>
      qexists_tac `THE (LDROP x ll2)` >>
      rw [] >>
      fs[arithmeticTheory.NOT_LESS,arithmeticTheory.LESS_EQ_EXISTS] >>
      simp[LNTH_ADD] >>
      Cases_on`LDROP x ll2`>>simp[] >>
      reverse(Cases_on`LTAKE x ll2`) >- (
        imp_res_tac LTAKE_IMP_LDROP >> fs[] ) >>
      `LFINITE ll2` by metis_tac[LFINITE_LNTH_NONE,LTAKE_EQ_NONE_LNTH] >>
      rw[] >>
      imp_res_tac LFINITE_HAS_LENGTH >>
      `∀x. n ≤ x ⇒ LNTH x ll2 = NONE` by metis_tac[LNTH_LLENGTH_NONE] >>
      `∀n. n < x ⇒ LNTH n ll1 ≠ NONE` by metis_tac[less_opt_def,less_opt_LLENGTH_LNTH_SOME,optionTheory.IS_SOME_DEF] >>
      `¬(n < x)` by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
      imp_res_tac to_fromList >>
      imp_res_tac LFINITE_toList >>
      fs[toList] >> rfs[] >>
      imp_res_tac LTAKE_LENGTH >> rw[] >>
      imp_res_tac LTAKE_TAKE_LESS >>
      metis_tac[arithmeticTheory.NOT_LESS,optionTheory.NOT_NONE_SOME])));

val lnth_some_length = Q.store_thm ("lnth_some_length",
`!ll n x. LNTH n ll = SOME x ⇒ less_opt n (LLENGTH ll)`,
 Induct_on `n` >>
 rw [] >>
 `ll = [||] ∨ ?h t. ll = h:::t` by metis_tac [llist_CASES] >>
 fs [less_opt_def]
 >- (
   Cases_on `LLENGTH t` >>
   fs [less_opt_def])
 >- (
   first_x_assum (qspec_then `t` mp_tac) >>
   simp [] >>
   Cases_on `LLENGTH t` >>
   fs [less_opt_def]));

val llist_shorter_def = Define `
  llist_shorter ll1 ll2 ⇔
    case (LLENGTH ll1, LLENGTH ll2) of
    | (NONE, NONE) => T
    | (SOME x, NONE) => T
    | (NONE, SOME x) => F
    | (SOME x, SOME y) => x ≤ y`;

val llist_shorter_lnth = Q.prove (
`!ll1 ll2.
  llist_shorter ll1 ll2
  ⇔
  !n x. LNTH n ll1 = SOME x ⇒ ?y. LNTH n ll2 = SOME y`,
 rw [llist_shorter_def] >>
 every_case_tac >>
 fs []
 >- metis_tac [NOT_SOME_NONE, LFINITE_LLENGTH, LFINITE_LNTH_NONE, option_nchotomy]
 >- metis_tac [NOT_SOME_NONE, LFINITE_LLENGTH, LFINITE_LNTH_NONE, option_nchotomy]
 >- metis_tac [NOT_SOME_NONE, LFINITE_LLENGTH, LFINITE_LNTH_NONE, option_nchotomy]
 >- (
   eq_tac >>
   rw []
   >- (
     imp_res_tac lnth_some_length >>
     rfs [less_opt_def] >>
     `n < x'` by decide_tac >>
     metis_tac [LTAKE_LNTH_EL, LTAKE_LLENGTH_SOME])
   >- (
     imp_res_tac LTAKE_LLENGTH_SOME >>
     Cases_on `x = 0` >>
     fs [] >>
     first_x_assum (qspecl_then [`x-1`, `EL (x-1) l'`] mp_tac) >>
     rw [] >>
     `x-1 < x` by decide_tac >>
     imp_res_tac LTAKE_LNTH_EL >>
     fs [lnth_fromList] >>
     imp_res_tac lnth_some_length >>
     rfs [less_opt_def] >>
     simp [])));

val llist_shorter_fromList = Q.store_thm ("llist_shorter_fromList",
`!l1 l2. llist_shorter (fromList l1) (fromList l2) ⇔ LENGTH l1 ≤ LENGTH l2`,
 rw [llist_shorter_def] >>
 every_case_tac >>
 fs [LLENGTH_fromList]);

val lprefix_chain_def = Define `
  lprefix_chain ls ⇔
    !ll1 ll2. ll1 ∈ ls ∧ ll2 ∈ ls ⇒ LPREFIX ll1 ll2 ∨ LPREFIX ll2 ll1`;

val lprefix_chain_subset = Q.store_thm("lprefix_chain_subset",
  `lprefix_chain ls ∧ y ⊆ ls ⇒ lprefix_chain y`,
  rw[lprefix_chain_def,SUBSET_DEF]);

val lprefix_chain_LNTHs_agree = Q.store_thm ("lprefix_chain_LNTHs_agree",
  `lprefix_chain ls ∧
   l1 ∈ ls ∧ l2 ∈ ls ∧
   LNTH n l1 = SOME x1 ∧
   LNTH n l2 = SOME x2 ⇒
   x1 = x2`,
  rw[] >>
  fs[lprefix_chain_def] >>
  first_x_assum(qspecl_then[`l1`,`l2`]mp_tac) >>
  rw[] >> fs[LPREFIX_APPEND] >> rw[] >>
  fs[LNTH_LAPPEND] >>
  every_case_tac >>
  fs[arithmeticTheory.NOT_LESS,arithmeticTheory.LESS_EQ_EXISTS] >>
  rw[] >> fsrw_tac[ARITH_ss][] >>
  metis_tac[LNTH_LLENGTH_NONE,arithmeticTheory.ADD_SYM,arithmeticTheory.LESS_EQ_ADD,optionTheory.NOT_NONE_SOME]);

val lprefix_chain_nth_def = Define `
  lprefix_chain_nth n ls =
    some x. ?l. l ∈ ls ∧ LNTH n l = SOME x`;

val exists_lprefix_chain_nth = Q.store_thm ("exists_lprefix_chain_nth",
  `!ls n x.
    lprefix_chain ls ∧
    (?l. l ∈ ls ∧ LNTH n l = SOME x) ⇒
    lprefix_chain_nth n ls = SOME x`,
  rw [some_def, lprefix_chain_nth_def] >>
  metis_tac [lprefix_chain_LNTHs_agree, SELECT_THM]);

val not_exists_lprefix_chain_nth = Q.store_thm ("not_exists_lprefix_chain_nth",
  `!ls n.
    lprefix_chain ls ∧
    (!l. l ∈ ls ⇒ LNTH n l = NONE) ⇒
    lprefix_chain_nth n ls = NONE`,
  rw [some_def, lprefix_chain_nth_def] >>
  metis_tac [NOT_SOME_NONE]);

val lprefix_chain_nth_none_mono = Q.store_thm ("lprefix_chain_nth_none_mono",
  `!m n ls.
    lprefix_chain ls ∧
    m ≤ n ∧
    lprefix_chain_nth m ls = NONE
    ⇒
    lprefix_chain_nth n ls = NONE`,
 rw [] >>
 match_mp_tac not_exists_lprefix_chain_nth >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 `LNTH m l ≠ NONE` by metis_tac [LNTH_NONE_MONO] >>
 metis_tac [exists_lprefix_chain_nth, NOT_SOME_NONE, option_nchotomy]);

val equiv_lprefix_chain_def = Define `
  equiv_lprefix_chain ls1 ls2 ⇔
    !n. lprefix_chain_nth n ls1 = lprefix_chain_nth n ls2`;

val equiv_lprefix_chain_thm = Q.store_thm ("equiv_lprefix_chain_thm",
  `!ls1 ls2.
    lprefix_chain ls1 ∧ lprefix_chain ls2
    ⇒
    (equiv_lprefix_chain ls1 ls2 ⇔
      (!ll1 n x. ll1 ∈ ls1 ∧ LNTH n ll1 = SOME x ⇒ ?ll2. ll2 ∈ ls2 ∧ LNTH n ll2 = SOME x) ∧
      (!ll2 n x. ll2 ∈ ls2 ∧ LNTH n ll2 = SOME x ⇒ ?ll1. ll1 ∈ ls1 ∧ LNTH n ll1 = SOME x))`,
  rw [equiv_lprefix_chain_def] >>
  eq_tac
  >- metis_tac [not_exists_lprefix_chain_nth, NOT_SOME_NONE, exists_lprefix_chain_nth, option_nchotomy] >>
  rw [] >>
  Cases_on `?s l. l ∈ ls1 ∧ LNTH n l = SOME x` >>
  fs [] >>
  metis_tac [not_exists_lprefix_chain_nth, NOT_SOME_NONE, exists_lprefix_chain_nth, option_nchotomy]);

val equiv_lprefix_chain_thm2 = Q.store_thm ("equiv_lprefix_chain_thm2",
`!ls1 ls2.
  lprefix_chain ls1 ∧ lprefix_chain ls2 ∧ (!ll2. ll2 ∈ ls2 ⇒ LFINITE ll2) ⇒
  (equiv_lprefix_chain ls1 ls2 ⇔
   (∀ll1 n x.
      ll1 ∈ ls1 ∧ LNTH n ll1 = SOME x ⇒
      ∃ll2. ll2 ∈ ls2 ∧ LNTH n ll2 = SOME x) ∧
   (!ll2 n x.
     ll2 ∈ ls2 ∧ ll2 ≠ [||] ⇒ ?ll1. ll1 ∈ ls1 ∧ llist_shorter ll2 ll1))`,
 rw [equiv_lprefix_chain_thm] >>
 eq_tac >>
 rw [llist_shorter_lnth]
 >- metis_tac []
 >- (
   Cases_on `?x. LLENGTH ll2 = SOME x` >>
   fs []
   >- (
     imp_res_tac LTAKE_LLENGTH_SOME >>
     Cases_on `x = 0` >>
     fs [] >>
     `x-1 < x` by decide_tac >>
     imp_res_tac LTAKE_LNTH_EL >>
     first_x_assum (qspecl_then [`ll2`, `x-1`, `EL (x-1) l`] mp_tac) >>
     rw [] >>
     qexists_tac `ll1` >>
     rw [] >>
     imp_res_tac lnth_some_length >>
     rfs [less_opt_def] >>
     `n ≤ x-1` by decide_tac >>
     metis_tac [lnth_some_down_closed])
   >- (
     `~LFINITE ll2` by fs [LLENGTH] >>
     metis_tac []))
 >- metis_tac []
 >- (
   `ll2 ≠ [||]` by (
     CCONTR_TAC >>
     fs []) >>
   metis_tac [lprefix_chain_LNTHs_agree]));

val lprefix_lub_def = Define `
  lprefix_lub ls lub ⇔
    (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)`;

val lprefix_lub_is_chain = Q.store_thm ("lprefix_lub_is_chain",
  `!ls ll. lprefix_lub ls ll ⇒ lprefix_chain ls`,
  rw[lprefix_lub_def,lprefix_chain_def] >>
  metis_tac[prefixes_lprefix_total]);

val lprefix_lub_nth = Q.store_thm ("lprefix_lub_nth",
  `!ls lub. lprefix_chain ls ⇒
    (lprefix_lub ls lub ⇔ !n. LNTH n lub = lprefix_chain_nth n ls)`,
  rw [lprefix_lub_def,EQ_IMP_THM] >- (
    Cases_on `LNTH n lub` >> rw []
    >- (
      `!l. l ∈ ls ⇒ LNTH n l = NONE` by (
         rw [] >>
         res_tac >>
         fs [LPREFIX_APPEND] >>
         fs [LNTH_LAPPEND] >>
         every_case_tac >>
         fs [] >>
         match_mp_tac LNTH_LLENGTH_NONE >>
         simp []) >>
      metis_tac [not_exists_lprefix_chain_nth])
    >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac exists_lprefix_chain_nth >>
      simp[] >>
      spose_not_then strip_assume_tac >>
      qpat_assum `∀ub. (∀ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub`
        (qspec_then `fromList (THE (LTAKE n lub))` mp_tac) >>
      rw [] >- (
        `IS_SOME (LTAKE n lub)` by metis_tac[LTAKE_EQ_NONE_LNTH,IF_NONE_EQUALS_OPTION] >>
        fs[IS_SOME_EXISTS] >>
        simp[LPREFIX_NTH] >>
        simp[LNTH_fromList] >>
        rw[] >- (
          `LPREFIX ll lub` by metis_tac[] >>
          pop_assum mp_tac >>
          simp_tac std_ss [LPREFIX_NTH] >>
          simp[] >>
          disch_then kall_tac >>
          imp_res_tac LTAKE_LNTH_EL >>
          last_x_assum(match_mp_tac) >>
          imp_res_tac LTAKE_LENGTH >>
          simp[] ) >>
        imp_res_tac LTAKE_LENGTH >>
        qmatch_assum_rename_tac`less_opt m (LLENGTH ll)` >>
        `n ≤ m` by decide_tac >>
        fs[less_opt_LLENGTH_LNTH_SOME] >>
        `IS_SOME (LNTH n ll)` by
          metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                    arithmeticTheory.NOT_LESS,
                    LFINITE_HAS_LENGTH,
                    less_opt_def,
                    NOT_LFINITE_NO_LENGTH,
                    less_opt_LLENGTH_LNTH_SOME] >>
        fs[IS_SOME_EXISTS] >>
        `less_opt n (LLENGTH ll)` by metis_tac[IS_SOME_DEF,less_opt_LLENGTH_LNTH_SOME] >>
        `LPREFIX ll lub` by metis_tac[] >> pop_assum mp_tac >>
        simp_tac std_ss [LPREFIX_NTH] >>
        qexists_tac`n`>>simp[]>>
        strip_tac >> rw[] >> metis_tac[]) >>
      simp[LPREFIX_def,from_toList] >>
      `IS_SOME (LTAKE n lub)` by metis_tac[LTAKE_EQ_NONE_LNTH,optionTheory.IF_NONE_EQUALS_OPTION] >>
      fs[IS_SOME_EXISTS] >>
      qmatch_assum_rename_tac`LTAKE n lub = SOME l` >>
      rw[toList] >- (
        imp_res_tac LFINITE_HAS_LENGTH >> simp[] >>
        imp_res_tac LTAKE_LLENGTH_SOME >> simp[] >>
        imp_res_tac to_fromList >> rfs[] >> rw[] >>
        fs[LLENGTH_fromList] >> rw[] >>
        imp_res_tac LTAKE_LENGTH >> rw[] >>
        strip_tac >> fs[IS_PREFIX_APPEND] >> fs[] >>
        imp_res_tac LTAKE_LENGTH >> fs[] >>
        `IS_SOME (LTAKE (LENGTH l) (fromList l'))` by simp[] >>
        imp_res_tac IS_SOME_LTAKE_less_opt_LLENGTH >>
        pop_assum mp_tac >>
        simp[LLENGTH_fromList,less_opt_def] >>
        Cases_on`l''`>>simp[] >> fs[] >> rw[] >>
        metis_tac[LLENGTH_fromList,LNTH_LLENGTH_NONE,NOT_SOME_NONE,
                  arithmeticTheory.LESS_EQ_ADD,
                  numeralTheory.numeral_distrib |> CONJUNCT2 |> CONJUNCT1]) >>
      metis_tac[LFINITE_fromList]))
  >- (
    rw [LPREFIX_NTH] >>
    imp_res_tac (#1(EQ_IMP_RULE less_opt_LLENGTH_LNTH_SOME)) >>
    fs [IS_SOME_EXISTS] >>
    metis_tac [exists_lprefix_chain_nth])
  >- (
    rw[LPREFIX_NTH] >>
    Cases_on`∃l x. l ∈ ls ∧ LNTH n l = SOME x` >- (
      fs[] >>
      `lprefix_chain_nth n ls = SOME x` by
        metis_tac[exists_lprefix_chain_nth] >>
      simp[] >>
      `LPREFIX l ub` by metis_tac[] >>
      pop_assum mp_tac >>
      simp_tac std_ss [LPREFIX_APPEND] >> rw[] >>
      simp[LNTH_LAPPEND] >>
      every_case_tac >> simp[] >>
      metis_tac[LNTH_LLENGTH_NONE,optionTheory.NOT_SOME_NONE,arithmeticTheory.NOT_LESS] ) >>
    `lprefix_chain_nth n ls = NONE` by
       metis_tac[not_exists_lprefix_chain_nth,optionTheory.IS_SOME_EXISTS,optionTheory.IF_NONE_EQUALS_OPTION] >>
    metis_tac[optionTheory.IS_SOME_DEF,less_opt_LLENGTH_LNTH_SOME]));

val unique_lprefix_lub = Q.store_thm ("unique_lprefix_lub",
  `!f ll1 ll2.
    lprefix_lub f ll1 ∧
    lprefix_lub f ll2
    ⇒
    ll1 = ll2`,
  rw[lprefix_lub_def] >>
  metis_tac[LPREFIX_ANTISYM,LPREFIX_REFL]);

val build_lprefix_lub_f_def = Define`
  build_lprefix_lub_f ls n =
    OPTION_MAP (λx. (n+1, x)) (lprefix_chain_nth n ls)`;

val build_lprefix_lub_def = Define `
  build_lprefix_lub ls =
    LUNFOLD (build_lprefix_lub_f ls) 0`;

val build_lprefix_lub_lem = Q.prove (
  `!ls. lprefix_chain ls ⇒ !m n. LNTH n (LUNFOLD (build_lprefix_lub_f ls) m) = lprefix_chain_nth (m + n) ls`,
  rpt gen_tac >>
  DISCH_TAC >>
  Induct_on `n` >>
  rw [Once LUNFOLD, build_lprefix_lub_f_def] >>
  Cases_on `lprefix_chain_nth m ls` >>
  fs []
  >- metis_tac [lprefix_chain_nth_none_mono, DECIDE ``m ≤ m + SUC n``]
  >- simp [arithmeticTheory.ADD1]);

val build_lprefix_lub_thm = Q.store_thm ("build_lprefix_lub_thm",
  `!ls. lprefix_chain ls ⇒ lprefix_lub ls (build_lprefix_lub ls)`,
  rw [lprefix_lub_nth, build_lprefix_lub_def] >>
  metis_tac [build_lprefix_lub_lem, DECIDE ``0 + x = x:num``])

val lprefix_lub_equiv_chain = Q.store_thm ("lprefix_lub_equiv_chain",
  `!ls1 ls2 ll.
    lprefix_chain ls1 ∧
    lprefix_chain ls2 ∧
    equiv_lprefix_chain ls1 ls2
    ⇒
    (lprefix_lub ls1 ll ⇔ lprefix_lub ls2 ll)`,
  rw [] >>
  imp_res_tac lprefix_lub_is_chain >>
  fs [lprefix_lub_nth, equiv_lprefix_chain_def]);

val lprefix_lub_equiv_chain2 = Q.store_thm ("lprefix_lub_equiv_chain2",
  `!ls1 ls2 ll1 ll2.
    lprefix_lub ls1 ll1 ∧
    lprefix_lub ls2 ll2
    ⇒
    (ll1 = ll2 ⇔ equiv_lprefix_chain ls1 ls2)`,
  rw [] >>
  imp_res_tac lprefix_lub_is_chain >>
  eq_tac >>
  rw [] >>
  fs [lprefix_lub_nth, equiv_lprefix_chain_def] >>
  simp [LNTH_EQ]);

val lprefix_lub_new_chain = Q.store_thm ("lprefix_lub_new_chain",
  `!ls1 ls2 ll.
    lprefix_chain ls2 ∧
    equiv_lprefix_chain ls1 ls2 ∧
    lprefix_lub ls1 ll
    ⇒
    lprefix_lub ls2 ll`,
  metis_tac [lprefix_lub_equiv_chain, lprefix_lub_is_chain]);

val _ = export_theory ();
