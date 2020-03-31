open HolKernel Parse boolLib bossLib

open listTheory rich_listTheory
open primrecfnsTheory

val _ = new_theory "recursivefns"

val minimise_def = Define`
  minimise f l =
    if (∃n. (f (n::l) = SOME 0) ∧ ∀i. i < n ⇒ ∃m. 0 < m ∧ (f (i::l) = SOME m))
    then
      SOME (@n. (f (n :: l) = SOME 0) ∧
                ∀i. i < n ⇒ ∃m. 0 < m ∧ (f (i::l) = SOME m))
    else NONE
`;

val recCn_def = Define`
  recCn (f:num list -> num option) gs l =
         let results = MAP (λg : num list -> num option. g l) gs
         in
           if EVERY (λr. r ≠ NONE) results then f (MAP THE results)
           else NONE
`;

val recPr_def = Define`
  recPr zf sf l =
    case l of
      [] => zf []
    | 0::t => zf t
    | SUC n::t => case recPr zf sf (n :: t) of
                    NONE => NONE
                  | SOME r => sf (n::r::t)
`;

val (recfn_rules, recfn_ind, recfn_cases) = Hol_reln`
  recfn (SOME o K 0) 1 ∧
  recfn (SOME o succ) 1 ∧
  (∀i n. i < n ⇒ recfn (SOME o proj i) n) ∧
  (∀f gs m. recfn f (LENGTH gs) ∧ EVERY (λg. recfn g m) gs ⇒
            recfn (recCn f gs) m) ∧
  (∀zf sf n. recfn zf (n - 1) ∧ recfn sf (n + 1) ⇒ recfn (recPr zf sf) n) ∧
  (∀f n. 0 < n ∧ recfn f (n + 1) ⇒ recfn (minimise f) n)
`;

val recfn_rulesl = CONJUNCTS recfn_rules
Theorem recfnCn = List.nth(recfn_rulesl, 3)
Theorem recfnPr = List.nth(recfn_rulesl, 4)

val primrec_recfn = store_thm(
  "primrec_recfn",
  ``∀f n. primrec f n ⇒ recfn (SOME o f) n``,
  Induct_on ‘primrec’ >> SRW_TAC [][recfn_rules] THENL [
    `SOME o Cn f gs = recCn (SOME o f) (MAP (λg. SOME o g) gs)`
       by SRW_TAC [][FUN_EQ_THM, recCn_def, LET_THM, MAP_MAP_o,
                     combinTheory.o_ABS_R, EVERY_MAP, Cn_def] THEN
    SRW_TAC [][] THEN MATCH_MP_TAC recfnCn THEN
    SRW_TAC [][EVERY_MAP] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM],

    `SOME o Pr f f' = recPr (SOME o f) (SOME o f')`
       by (SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `list` THEN
           `(list = []) ∨ ∃m ms. list = m :: ms`
              by (Cases_on `list` THEN SRW_TAC [][])
             THEN1 SRW_TAC [][Once recPr_def, Once Pr_def] THEN
           SRW_TAC [][] THEN
           Induct_on `m` THEN SRW_TAC [][Once recPr_def] THEN
           POP_ASSUM (SUBST1_TAC o SYM) THEN SRW_TAC [][]) THEN
    SRW_TAC [][] THEN MATCH_MP_TAC recfnPr THEN SRW_TAC [ARITH_ss][]
  ]);

val minimise_thm = Q.store_thm(
  "minimise_thm",
  `minimise f l =
     some n. (f (n::l) = SOME 0) ∧ (∀i. i<n ⇒ ∃m. 0<m ∧ (f (i::l) = SOME m))`,
  simp[minimise_def] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[]
  >- metis_tac[] >>
  SELECT_ELIM_TAC >> rw[] >>
  metis_tac[arithmeticTheory.LESS_LESS_CASES, prim_recTheory.LESS_REFL,
            optionTheory.SOME_11]);

val totalrec_def = Define`
  totalrec f n ⇔ recfn f n ∧ ∀l. (LENGTH l = n) ⇒ ∃m. f l = SOME m
`;

Definition rec1_def[simp]:
  (rec1 f [] = f 0 : num option) ∧
  (rec1 f (x::t) = f x)
End

Definition rec2_def[simp]:
  (rec2 f [] = f 0 0 : num option) ∧
  (rec2 f [x] = f x 0) ∧
  (rec2 f (x::y::t) = f x y)
End

val recfn_K = store_thm(
  "recfn_K[simp]",
  ``recfn (K (SOME i)) 1``,
  `recfn (SOME o K i) 1` by simp[primrec_recfn] >> fs[]);

val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

val recfn_short_extended = Q.store_thm(
  "recfn_short_extended",
  `∀f n. recfn f n ⇒
         ∀xs. LENGTH xs ≤ n ⇒
              (f (xs ++ GENLIST (K 0) (n - LENGTH xs)) = f xs)`,
  Induct_on `recfn` >> simp[] >> rpt strip_tac
  >- (Cases_on `xs` >> simp[succ_def])
  >- (qid_spec_tac`xs` >> Induct_on `n` >> simp[proj_def] >> rw[] >>
      simp[EL_APPEND_EQN])
  >- (simp[recCn_def] >> fs[EVERY_MEM] >> COND_CASES_TAC >> fs[MEM_MAP]
      >- (COND_CASES_TAC >- simp[Cong MAP_CONG'] >> fs[] >> metis_tac[])
      >- metis_tac[])
  >- (Cases_on `xs` >> simp_tac (srw_ss ())[]
      >- (ONCE_REWRITE_TAC[recPr_def] >> Cases_on `n` >> simp[GENLIST_CONS] >>
          last_x_assum (qspec_then `[]` mp_tac) >> simp[])
      >- (fs[] >> Induct_on`h` >> simp[]
          >- (ONCE_REWRITE_TAC[recPr_def] >>
              last_x_assum (qspec_then `t` mp_tac) >>
              simp[arithmeticTheory.ADD1]) >>
          ONCE_REWRITE_TAC[recPr_def] >> simp[] >>
          rename [‘option_CASE (recPr f g (h::t))’] >>
          Cases_on`recPr f g (h::t)` >> simp[] >>
          rename [‘g (h1::h2::(t ++ GENLIST _ _))’] >>
          first_x_assum(qspec_then `h1::h2::t`mp_tac) >>
          simp[arithmeticTheory.ADD1]))
  >- (simp[minimise_thm] >> rename [‘_ (xs ++ GENLIST (K 0) _)’] >>
      first_x_assum(qspec_then`j::xs` (mp_tac o Q.GEN`j`)) >>
      simp[arithmeticTheory.ADD1]))

val recfn_nonzero = Q.store_thm(
  "recfn_nonzero",
  ‘∀f n. recfn f n ⇒ n ≠ 0’,
  Induct_on ‘recfn’ >> rw[] >> rename [‘gs ≠ []’] >>
  Cases_on ‘gs’ >> fs[]);

val recfn_long_truncated = Q.store_thm(
  "recfn_long_truncated",
  `∀f n. recfn f n ⇒ ∀l. n ≤ LENGTH l ⇒ (f (TAKE n l) = f l)`,
  Induct_on`recfn` >> simp[] >> rpt strip_tac
  >- (Cases_on `l` >> fs[succ_def])
  >- (simp[proj_def,EL_TAKE])
  >- (simp[recCn_def] >> fs[EVERY_MEM] >> COND_CASES_TAC >> fs[MEM_MAP]
      >- (COND_CASES_TAC >-(simp[Cong MAP_CONG']) >> fs[] >> metis_tac[])
      >- metis_tac[])
  >- (rename [‘recfn f (n - 1)’, ‘recfn g (n + 1)’, ‘TAKE n l’] >>
      ‘n - 1 ≠ 0’ by metis_tac[recfn_nonzero] >> ‘2 ≤ n’ by simp[] >>
      ‘∃h t. l = h::t’ by (Cases_on ‘l’ >> fs[]) >> rw[] >> fs[] >>
      Induct_on ‘h’ >> ONCE_REWRITE_TAC [recPr_def] >> simp[] >>
      Cases_on ‘recPr f g (h::t)’ >> simp[] >>
      first_x_assum
        (qspec_then ‘h1::h2::t’
            (irule o
             SIMP_RULE (srw_ss() ++ ARITH_ss)
                       [listTheory.TAKE_def, ASSUME “2 ≤ n”] o
             Q.GENL [‘h1’, ‘h2’])) >> simp[])
  >- (simp[minimise_thm] >> rename [‘f (TAKE (n + 1) _)’, ‘n ≤ LENGTH xs’] >>
      first_x_assum(qspec_then`j::xs` (mp_tac o Q.GEN`j`)) >>
      simp[arithmeticTheory.ADD1]));

val unary_recfn_eq = Q.store_thm(
  "unary_recfn_eq",
  `recfn f 1 ∧ (∀n. f [n] = g n) ⇒ (f = rec1 g)`,
  strip_tac >> simp[FUN_EQ_THM] >> Cases >> simp[]
  >- (drule_then (qspec_then `[]` mp_tac) recfn_short_extended >> simp[])
  >- (drule_then (qspec_then ‘h::t’ mp_tac) recfn_long_truncated >> simp[]))

val recfn_rec1 = Q.store_thm(
  "recfn_rec1",
  `(∃g. recfn g 1 ∧ ∀n. g [n] = f n) ⇒ recfn (rec1 f) 1`,
  metis_tac[unary_recfn_eq]);

Theorem recfn_nzero:
  ∀f a. recfn f a ⇒ 0 < a
Proof
  Induct_on ‘recfn’ >> rw[] >> fs[EVERY_MEM] >>
  rename [‘recfn f (LENGTH gs)’] >> Cases_on ‘gs’ >> fs[]
QED

val _ = export_theory()
