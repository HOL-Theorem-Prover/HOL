open HolKernel boolLib bossLib BasicProvers;
open sptreeTheory spt_closureTheory;
open listTheory rich_listTheory alistTheory pairTheory
     stringTheory pred_setTheory relationTheory;

val _ = new_theory "topological_sort";


(******************** Definitions ********************)

(* the algorithm is defined over num for efficiency *)

Definition needs_def:
  needs n m (reach:num_set num_map) =
    case lookup n reach of
    | NONE => F (* cannot happen *)
    | SOME s => IS_SOME (lookup m s)
End

Definition partition_def:
  partition n [] reach acc = acc /\
  partition n (k::ks) reach (xs,ys,zs) =
    if needs k n reach then
      if needs n k reach then
        partition n ks reach (xs,k::ys,zs)
      else
        partition n ks reach (xs,ys,k::zs)
    else
      partition n ks reach (k::xs,ys,zs)
End

Theorem partition_LENGTH[local]:
  !ks n reach xs ys zs xs1 ys1 zs1.
    partition n ks reach (xs,ys,zs) = (xs1,ys1,zs1) ==>
    LENGTH xs1 <= LENGTH xs + LENGTH ks /\
    LENGTH ys1 <= LENGTH ys + LENGTH ks /\
    LENGTH zs1 <= LENGTH zs + LENGTH ks
Proof
  Induct \\ fs [partition_def] \\ rw [] \\ res_tac \\ fs []
QED

Definition top_sort_aux_def:
  top_sort_aux [] reach acc = acc /\
  top_sort_aux (n::ns) reach acc =
    let (xs,ys,zs) = partition n ns reach ([],[],[]) in
      top_sort_aux xs reach ((n::ys) :: top_sort_aux zs reach acc)
Termination
  WF_REL_TAC `measure (LENGTH o FST)` \\ rw []
  \\ pop_assum (assume_tac o GSYM)
  \\ imp_res_tac partition_LENGTH \\ fs []
End

Definition trans_clos_def:
  (* computes the transitive closure for each node given nexts *)
  trans_clos nexts = map (\x. closure_spt x nexts) nexts
End

Definition top_sort_def:
  top_sort (let_bindings : (num (* name *) # num_set (* free vars *)) list) =
    let roots = MAP FST let_bindings in
    let nexts = fromAList let_bindings in
    let reach = trans_clos nexts in
      top_sort_aux roots reach []
End

Triviality top_sort_example:
   top_sort
     [(0,fromAList[]);               (* 0 has no deps *)
      (1,fromAList[(2,());(0,())]);  (* 1 depens on 2 and 0 *)
      (2,fromAList[(1,())]);         (* 2 depends on 1 *)
      (3,fromAList[(1,())])]         (* 3 depends on 1 *)
   =
   [[0]; [1; 2]; [3]]  (* 0 defined first, 1 and 2 are mutual, 3 is last *)
Proof
  EVAL_TAC
QED

(* generalisation to any type *)

Definition to_nums_def:
  to_nums b [] = LN /\
  to_nums b (x::xs) =
    case ALOOKUP b x of
    | NONE => to_nums b xs
    | SOME n => insert n () (to_nums b xs)
End

Definition top_sort_any_def:
  top_sort_any (lets : ('a # 'a list) list) =
    if NULL lets (* so that HD names, below, is well defined *) then [] else
      let names = MAP FST lets in
      let to_num = MAPi (\i n. (n,i)) names in
      let from_num = fromAList (MAPi (\i n. (i,n)) names) in
      let nesting = top_sort (MAPi (\i (n,ns). (i,to_nums to_num ns)) lets) in
        MAP
          (MAP (\n. case lookup n from_num of SOME m => m | _ => HD (names)))
          nesting
End

Triviality top_sort_any_example:
   top_sort_any
     [("A",[]);          (* A has no deps *)
      ("B",["C";"A"]);   (* B depens on C and A *)
      ("C",["B";"X"]);   (* C depends on B and X -- X is intentionally not defined here *)
      ("D",["B"])]       (* D depends on B *)
   =
   [["A"]; ["B"; "C"]; ["D"]]  (* A defined first, B and C are mutual, D is last *)
Proof
  EVAL_TAC
QED


(******************** Proofs ********************)

Theorem needs_eq_is_adjacent:
  !x y tree.
    needs x y tree <=> is_adjacent tree x y
Proof
  rw[needs_def, is_adjacent_def] >> EVERY_CASE_TAC >> gvs[] >>
  rename1 `lookup y z` >> Cases_on `lookup y z` >> gvs[]
QED

Theorem partition_lemma[local]:
  !n ks reach acc xas ybs zcs as bs cs.
    partition n ks reach acc = (xas,ybs,zcs) /\
    acc = (as,bs,cs)
  ==> ?xs ys zs. xas = xs ++ as /\ ybs = ys ++ bs /\ zcs = zs ++ cs /\
      (set (xs ++ ys ++ zs) = set ks) /\
      (!x. MEM x ks ==> (MEM x xs <=> ¬ needs x n reach)) /\
      (!y. MEM y ks ==> (MEM y ys <=> needs y n reach /\ needs n y reach)) /\
      (!z. MEM z ks ==> (MEM z zs <=> needs z n reach /\ ¬ needs n z reach))
Proof
  recInduct partition_ind >> once_rewrite_tac[partition_def] >> gvs[] >> rw[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[EXTENSION, GSYM DISJ_ASSOC] >> metis_tac[]
QED

Theorem partition_thm:
  !n ks reach as bs cs res.
    partition n ks reach (as, bs, cs) = res
  ==> ?xs ys zs.
      res = (xs ++ as, ys ++ bs, zs ++ cs) /\
      (set (xs ++ ys ++ zs) = set ks) /\
      (!x. MEM x ks ==> (MEM x xs <=> ¬ needs x n reach)) /\
      (!y. MEM y ks ==> (MEM y ys <=> needs y n reach /\ needs n y reach)) /\
      (!z. MEM z ks ==> (MEM z zs <=> needs z n reach /\ ¬ needs n z reach))
Proof
  rw[] >>
  qspecl_then [`n`,`ks`,`reach`,`(as,bs,cs)`] assume_tac partition_lemma >>
  qpat_abbrev_tac `p = partition n ks reach acc` >>
  PairCases_on `p` >> gvs[]
QED

Triviality ALL_DISTINCT_APPEND_SWAP:
  !l1 l2.  ALL_DISTINCT (l1 ++ l2) <=> ALL_DISTINCT (l2 ++ l1)
Proof
  rw[] >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem partition_ALL_DISTINCT:
  !n ks reach acc xs ys zs as bs cs.
    partition n ks reach acc = (xs,ys,zs) /\
    acc = (as,bs,cs) /\
    ALL_DISTINCT (ks ++ as ++ bs ++ cs)
  ==> ALL_DISTINCT (xs ++ ys ++ zs)
Proof
  recInduct partition_ind >> once_rewrite_tac[partition_def] >>
  rpt conj_tac >- simp[] >> rpt gen_tac >> rpt strip_tac >>
  EVERY_CASE_TAC >> gvs[] >> first_x_assum irule >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac
  >- (ntac 2 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[]))
  >- (ntac 3 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[]))
  >- (ntac 1 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[]))
  >- (ntac 3 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[]))
QED

Theorem top_sort_aux_correct:
  !ns reach acc resacc.
    top_sort_aux ns reach acc = resacc /\
    (!n m. TC (\a b. needs a b reach) n m ==> needs n m reach) /\
    ALL_DISTINCT ns
  ==> ?res.
      resacc = res ++ acc /\
      ALL_DISTINCT (FLAT res) /\
      set (FLAT res) = set ns /\
      !xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss /\ MEM y ys ==>
        (* for any defined dependencies of y *)
        !dep. needs y dep reach /\ MEM dep ns ==>
          (* mutual dependencies must by in ys, all others in xss *)
          (¬ needs dep y reach <=> MEM dep (FLAT xss)) /\
          (  needs dep y reach <=> MEM dep ys)
Proof
  recInduct top_sort_aux_ind >> simp[top_sort_aux_def] >> rw[] >>
  qpat_abbrev_tac `parts = partition _ _ _ _` >>
  PairCases_on `parts` >> gvs[] >>
  drule partition_thm >> strip_tac >> gvs[] >>
  gvs[EXTENSION, GSYM DISJ_ASSOC] >>
  drule partition_ALL_DISTINCT >> simp[] >> strip_tac >>
  `ALL_DISTINCT parts0 /\ ALL_DISTINCT parts2` by gvs[ALL_DISTINCT_APPEND] >>
  last_x_assum drule >> last_x_assum drule >> rw[] >> simp[] >>
  conj_asm1_tac >- (gvs[ALL_DISTINCT_APPEND] >> CCONTR_TAC >> metis_tac[]) >>
  conj_tac >- (gvs[ALL_DISTINCT_APPEND] >> CCONTR_TAC >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  `ALL_DISTINCT (FLAT (xss ++ [ys]))` by (
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[ALL_DISTINCT_APPEND]
    >- (rename1 `FLAT l1` >> Cases_on `l1` >> gvs[]) >- metis_tac[]) >>
  strip_tac >> gvs[] >> Cases_on `needs dep y reach` >> gvs[]
  >- (
    conj_asm2_tac >- (simp[] >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[]
    >- metis_tac[]
    >- (rename1 `_ ++ FLAT l1` >> Cases_on `l1` >> gvs[])
    >- metis_tac[]
    )
  >- (
    reverse conj_asm1_tac
    >- (simp[] >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[]
    >- metis_tac[] >>
    rename1 `_ ++ FLAT l1` >> Cases_on `l1` >> gvs[] >> metis_tac[]
    )
  >- (
    conj_asm2_tac >- (simp[] >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[]
    >- (
      qsuff_tac `MEM dep parts0` >- metis_tac[] >>
      CCONTR_TAC >> gvs[] >>
      `¬ needs y n reach` by metis_tac[] >>
      last_x_assum (qspecl_then [`y`,`n`] mp_tac) >> simp[] >>
      simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
      )
    >- (
      rename1 `_ ++ FLAT l1` >> Cases_on `l1` >> gvs[] >>
      simp[DISJ_EQ_IMP] >> strip_tac >>
      `needs y n reach /\ needs n y reach` by metis_tac[] >>
      CCONTR_TAC >> gvs[]
      >- (
        last_x_assum (qspecl_then [`dep`,`n`] mp_tac) >> simp[] >>
        simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
        )
      >- (
        last_x_assum (qspecl_then [`n`,`dep`] mp_tac) >> simp[] >>
        simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
        )
      )
    >- (
      qsuff_tac `MEM dep parts2` >- metis_tac[] >>
      `needs y n reach /\ ¬ needs n y reach` by metis_tac[] >>
      CCONTR_TAC >> gvs[]
      >- (
        last_x_assum (qspecl_then [`dep`,`n`] mp_tac) >> simp[] >>
        simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
        )
      >- (
        last_x_assum (qspecl_then [`n`,`y`] mp_tac) >> simp[] >>
        simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
        )
      )
    )
  >- (
    reverse conj_asm1_tac
    >- (simp[] >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[]
    >- (
      qsuff_tac `MEM dep parts0` >- metis_tac[] >>
      CCONTR_TAC >> gvs[] >>
      `¬ needs y n reach` by metis_tac[] >>
      last_x_assum (qspecl_then [`y`,`n`] mp_tac) >> simp[] >>
      simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
      )
    >- (
      rename1 `_ ++ FLAT l1` >> Cases_on `l1` >> gvs[] >>
      `needs y n reach /\ needs n y reach` by metis_tac[] >>
      CCONTR_TAC >> gvs[] >>
      last_x_assum (qspecl_then [`dep`,`y`] mp_tac) >> simp[] >>
      simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
      )
    >- (
      simp[DISJ_EQ_IMP] >> strip_tac >> gvs[] >>
      qsuff_tac `MEM dep parts2` >- metis_tac[] >>
      `needs y n reach /\ ¬ needs n y reach` by metis_tac[] >>
      CCONTR_TAC >> gvs[]
      )
    )
QED

Triviality domain_lookup_num_set:
  !t k. k IN domain t <=> lookup k t = SOME ()
Proof
  rw[domain_lookup]
QED

Theorem trans_clos_correct:
  !nexts n m.
    needs n m (trans_clos nexts) \/ n = m <=> is_reachable nexts n m
Proof
  rw[trans_clos_def, needs_eq_is_adjacent, is_adjacent_def] >>
  rw[lookup_map, PULL_EXISTS, GSYM domain_lookup_num_set] >>
  eq_tac >> rw[] >> gvs[is_reachable_def, closure_spt_thm]
  >- (
    irule (iffRL RTC_CASES1) >> DISJ2_TAC >>
    goal_assum (drule_at Any) >> gvs[is_adjacent_def, domain_lookup]
    )
  >- (
    gvs[Once RTC_CASES1, is_adjacent_def] >> DISJ1_TAC >>
    gvs[domain_lookup] >> goal_assum drule >> simp[]
    )
QED

Theorem trans_clos_correct_imp:
  !nexts n m.
    (TC (\x y. needs x y nexts)) n m ==> needs n m (trans_clos nexts)
Proof
  simp[trans_clos_def, needs_eq_is_adjacent] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> rw[] >> gvs[is_adjacent_def] >>
  rw[lookup_map, PULL_EXISTS, GSYM domain_lookup_num_set] >>
  gvs[Once TC_CASES1, closure_spt_thm, is_adjacent_def] >>
  gvs[domain_lookup] >>
  goal_assum drule >> simp[is_reachable_def] >>
  irule TC_RTC >> simp[]
QED

Theorem trans_clos_TC_closed:
  !t n m.
    TC (\a b. needs a b (trans_clos t)) n m ==> needs n m (trans_clos t)
Proof
  strip_tac >> ho_match_mp_tac TC_INDUCT >> simp[] >> rw[] >>
  imp_res_tac trans_clos_correct >> gvs[is_reachable_def] >>
  rename1 `RTC _ l m` >>
  Cases_on `l = m` >> gvs[] >> Cases_on `n = l` >> gvs[] >>
  gvs[RTC_CASES_TC] >>
  irule trans_clos_correct_imp >>
  irule (TC_RULES |> SPEC_ALL |> CONJUNCT2) >> gvs[needs_eq_is_adjacent] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  goal_assum drule >> simp[]
QED

Theorem top_sort_correct_weak:
  !lets res.
    ALL_DISTINCT (MAP FST lets) /\
    res = top_sort lets ==>
      ALL_DISTINCT (FLAT res) /\
      set (FLAT res) = set (MAP FST lets) /\
      !xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss /\ MEM y ys ==>
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        ?deps. ALOOKUP lets y = SOME deps /\
               !d. d IN domain deps /\ MEM d (MAP FST lets)
               ==> MEM d (FLAT xss ++ ys)
Proof
  simp[top_sort_def] >> gen_tac >> strip_tac >>
  drule_at Any top_sort_aux_correct >> simp[] >>
  disch_then (qspecl_then [`trans_clos (fromAList lets)`,`[]`] mp_tac) >>
  simp[trans_clos_TC_closed] >> strip_tac >> rw[] >>
  gvs[EXTENSION, GSYM DISJ_ASSOC] >>
  `MEM y (MAP FST lets)` by res_tac >>
  gvs[MEM_MAP, PULL_EXISTS] >>
  rename1 `MEM y _` >> PairCases_on `y` >> gvs[] >>
  drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[] >> rw[] >>
  first_x_assum (qspecl_then [`xss`,`ys`,`zss`] mp_tac) >> simp[] >>
  disch_then drule >> disch_then $ drule_at Any >>
  reverse impl_tac
  >- (qmatch_goalsub_abbrev_tac `¬foo <=> _` >> Cases_on `foo` >> gvs[]) >>
  irule trans_clos_correct_imp >>
  simp[Once TC_CASES1, needs_def] >> DISJ1_TAC >>
  simp[needs_def] >> gvs[domain_lookup, lookup_fromAList]
QED

Theorem top_sort_correct:
  !lets res.
    ALL_DISTINCT (MAP FST lets) /\
    res = top_sort lets ==>
      ALL_DISTINCT (FLAT res) /\
      set (FLAT res) = set (MAP FST lets) /\
      !xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss /\ MEM y ys ==>
        (* for any defined dependencies of y *)
        !dep. is_reachable (fromAList lets) y dep /\ MEM dep (MAP FST lets) ==>
          (¬ is_reachable (fromAList lets) dep y <=> MEM dep (FLAT xss)) /\
          (  is_reachable (fromAList lets) dep y <=> MEM dep ys)
Proof
  simp[top_sort_def] >> gen_tac >> strip_tac >>
  drule_at Any top_sort_aux_correct >> simp[] >>
  disch_then (qspecl_then [`trans_clos (fromAList lets)`,`[]`] mp_tac) >>
  simp[trans_clos_TC_closed] >> strip_tac >>
  rpt gen_tac >> ntac 3 strip_tac >>
  first_x_assum drule >> disch_then drule >>
  gvs[GSYM trans_clos_correct, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem to_nums_correct:
  !xs b res.
    to_nums b xs = res /\
    ALL_DISTINCT (MAP FST b)
  ==> domain res = {c | ?d. MEM d xs /\ ALOOKUP b d = SOME c}
Proof
  Induct >> rw[to_nums_def] >> CASE_TAC >> gvs[EXTENSION] >>
  rw[] >> eq_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Triviality ALL_DISTINCT_MAPi_ID:
  !l.  ALL_DISTINCT (MAPi (\i _. i) l)
Proof
  rw[EL_ALL_DISTINCT_EL_EQ]
QED

Triviality ALOOKUP_MAPi_ID:
  !l k. ALOOKUP (MAPi (\i n. (i,n)) l) k =
        if k < LENGTH l then SOME (EL k l) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality ALOOKUP_MAPi_ID_f:
  !l k. ALOOKUP (MAPi (\i n. (i,f n)) l) k =
        if k < LENGTH l then SOME (f (EL k l)) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality MAPi_MAP[simp]:
  !l. MAPi (\i n. f n) l = MAP f l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Triviality MEM_ALOOKUP:
  !l k v.
    ALL_DISTINCT (MAP FST l)
  ==> (MEM (k,v) l <=> ALOOKUP l k = SOME v)
Proof
  Induct >> rw[FORALL_PROD] >> gvs[] >>
  PairCases_on `h` >> gvs[] >>
  IF_CASES_TAC >> gvs[MEM_MAP, FORALL_PROD] >>
  eq_tac >> simp[]
QED

Theorem top_sort_any_correct_weak:
  !lets res.
    ALL_DISTINCT (MAP FST lets) /\
    res = top_sort_any lets ==>
      ALL_DISTINCT (FLAT res) /\
      set (FLAT res) = set (MAP FST lets) /\
      !xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss /\ MEM y ys ==>
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        ?deps. ALOOKUP lets y = SOME deps /\
               !d. MEM d deps /\ MEM d (MAP FST lets) ==> MEM d (FLAT xss ++ ys)
Proof
  once_rewrite_tac[top_sort_any_def] >>
  rpt gen_tac >> IF_CASES_TAC >- gvs[NULL_EQ] >>
  qabbrev_tac `names = MAP FST lets` >>
  qabbrev_tac `to_num = MAPi (\i n. (n,i)) names` >>
  qabbrev_tac `from_num = fromAList (MAPi (\i n. (i,n)) names)` >>
  qabbrev_tac `arg = MAPi (\i (n,ns). (i,to_nums to_num ns)) lets` >>
  gvs[] >> strip_tac >> gvs[] >>
  qspec_then `arg` assume_tac top_sort_correct_weak >> gvs[] >>
  pop_assum mp_tac >> impl_keep_tac
  >- (
    gvs[Abbr `arg`, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[ALL_DISTINCT_MAPi_ID, GSYM LAMBDA_PROD]
    ) >>
  strip_tac >> gvs[GSYM MAP_FLAT] >> rw[]
  >- (
    irule ALL_DISTINCT_MAP_INJ >> rw[] >> gvs[MEM_MAP] >>
    rename1 `_ (lookup (FST a) _) _ _ = _ (lookup (FST b) _) _ _` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    gvs[Abbr `from_num`, lookup_fromAList] >>
    gvs[Abbr `arg`, Abbr `names`, indexedListsTheory.MEM_MAPi] >>
    rename1 `(a0,_) = _ (EL c _)` >> rename1 `(b0,_) = _ (EL d _)` >>
    qabbrev_tac `cc = EL c lets` >> qabbrev_tac `dd = EL d lets` >>
    PairCases_on `cc` >> PairCases_on `dd` >> gvs[] >>
    gvs[ALOOKUP_MAPi_ID, EL_ALL_DISTINCT_EL_EQ]
    )
  >- (
    gvs[EXTENSION, MEM_MAP, PULL_EXISTS] >> rw[] >> eq_tac >> rw[]
    >- (
      gvs[Abbr `names`] >> CASE_TAC >- (Cases_on `lets` >> gvs[]) >>
      gvs[MEM_MAP, Abbr `from_num`, lookup_fromAList] >>
      drule ALOOKUP_MEM >> strip_tac >>
      gvs[indexedListsTheory.MEM_MAPi, EL_MAP] >>
      irule_at Any EQ_REFL >> simp[EL_MEM]
      ) >>
    pop_assum mp_tac >> pop_assum kall_tac >> rw[] >>
    imp_res_tac MEM_EL >> gvs[] >>
    gvs[Abbr `names`, Abbr `from_num`, MEM_MAP] >>
    PairCases_on `y` >> gvs[] >>
    simp[lookup_fromAList, ALOOKUP_MAPi_ID, EXISTS_PROD] >>
    qexists_tac `n` >> simp[] >>
    gvs[Abbr `arg`, indexedListsTheory.MEM_MAPi] >>
    goal_assum drule >> Cases_on `EL n lets` >> gvs[]
    ) >>
  gvs[MAP_EQ_APPEND, GSYM MAP_FLAT, MEM_MAP, PULL_EXISTS] >>
  rename1 `top_sort _ = left ++ [mid] ++ right` >>
  gvs[Abbr `from_num`, lookup_fromAList] >>
  gvs[ALOOKUP_MAPi_ID] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    irule FALSITY >>
    gvs[Abbr `names`, Abbr `arg`, EXTENSION, GSYM DISJ_ASSOC] >> res_tac >>
    gvs[indexedListsTheory.MEM_MAPi] >>
    rename1 `EL m lets` >> Cases_on `EL m lets` >> gvs[]
    ) >>
  gvs[MEM_MAP, MEM_FLAT, PULL_EXISTS] >>
  gvs[Abbr `names`, EL_MAP, ALOOKUP_ALL_DISTINCT_EL] >>
  simp[Once MEM_EL, PULL_EXISTS] >> rw[] >> rename1 `m < _` >>
  first_x_assum (drule_at Any) >> disch_then (qspec_then `left` mp_tac) >>
  simp[] >>
  `arg = MAPi (\i ns. (i, to_nums to_num (SND ns))) lets` by (
    gvs[Abbr `arg`] >> AP_THM_TAC >> AP_TERM_TAC >>
    irule EQ_EXT >> rw[] >> irule EQ_EXT >> rw[] >>
    rename1 `_ foo = _` >> PairCases_on `foo` >> gvs[]) >>
  gvs[ALOOKUP_MAPi_ID_f] >>
  qspecl_then [`SND (EL n lets)`,`to_num`] mp_tac to_nums_correct >> gvs[] >>
  impl_keep_tac >- gvs[Abbr `to_num`, combinTheory.o_DEF] >>
  strip_tac >> simp[PULL_EXISTS] >> simp[Once SWAP_FORALL_THM] >>
  disch_then (qspec_then `EL m (SND (EL n lets))` mp_tac) >> simp[EL_MEM] >>
  drule (GSYM MEM_ALOOKUP) >> strip_tac >> simp[] >>
  gvs[Abbr `to_num`, indexedListsTheory.MEM_MAPi, PULL_EXISTS] >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[Once MEM_EL] >> strip_tac >>
  rename1 `l < _` >> simp[GSYM CONJ_ASSOC] >> disch_then drule >> simp[] >>
  strip_tac
  >- (
    rename1 `MEM _ l2` >> DISJ1_TAC >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
  >- (
    DISJ2_TAC >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
QED

Definition depends_on_def:
  depends_on alist x y <=>
    RTC (\a b. ?deps.
      ALOOKUP alist a = SOME deps /\ MEM b deps /\ MEM b (MAP FST alist)) x y
End

Triviality top_sort_any_depends_on_weak:
  !lets res.
    (!xss ys zss y.
      res = xss ++ [ys] ++ zss /\ MEM y ys ==>
      ?deps. ALOOKUP lets y = SOME deps /\
             !d. MEM d deps /\ MEM d (MAP FST lets) ==> MEM d (FLAT xss ++ ys))
  ==> !a b. depends_on lets a b ==>
    !xss ys zss y.
      res = xss ++ [ys] ++ zss /\ MEM a ys ==>
      MEM b (FLAT xss ++ ys)
Proof
  ntac 3 strip_tac >> simp[depends_on_def] >>
  Induct_on `RTC` >> rw[] >> gvs[] >>
  rename1 `RTC _ c _` >>
  last_x_assum (drule_at Any) >>
  disch_then (qspecl_then [`xss`,`zss`] mp_tac) >> simp[] >>
  disch_then drule_all >> reverse strip_tac
  >- (first_x_assum irule >> simp[]) >>
  pop_assum mp_tac >> simp[Once MEM_FLAT] >> strip_tac >>
  qspecl_then [`xss`,`l`] assume_tac $ GEN_ALL MEM_SING_APPEND >>
  gvs[]
QED

Theorem top_sort_any_correct:
  !lets res.
    ALL_DISTINCT (MAP FST lets) /\
    res = top_sort_any lets ==>
      ALL_DISTINCT (FLAT res) /\
      set (FLAT res) = set (MAP FST lets) /\
      !xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss /\ MEM y ys ==>
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        !dep. depends_on lets y dep ==>
          MEM dep (FLAT xss ++ ys) /\
          (depends_on lets dep y ==> MEM dep ys)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all top_sort_any_correct_weak >> simp[] >> strip_tac >> rw[]
  >- (
    irule (top_sort_any_depends_on_weak |> SIMP_RULE (srw_ss()) []) >>
    qexistsl_tac [`y`,`lets`,`top_sort_any lets`,`zss`] >> simp[]
    ) >>
  qspecl_then [`lets`,`top_sort_any lets`]
    mp_tac top_sort_any_depends_on_weak >>
  rw[] >>
  first_assum (qspecl_then [`y`,`dep`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`xss`,`ys`,`zss`] mp_tac) >> dsimp[] >>
  simp[MEM_FLAT] >> strip_tac >>
  qspecl_then [`xss`,`l`] assume_tac $ GEN_ALL MEM_SING_APPEND >> gvs[] >>
  irule FALSITY >>
  first_x_assum drule >>
  disch_then (qspecl_then [`a`,`l`,`c ++ [ys] ++ zss`] mp_tac) >> simp[] >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED


val _ = export_theory();
