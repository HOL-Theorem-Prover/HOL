open HolKernel Parse bossLib boolLib

open primrecfnsTheory numpairTheory arithmeticTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "prnlist" (* "primitive recursive number lists" *)

val primrec_ncons = Store_thm(
  "primrec_ncons",
  ``primrec (pr2 ncons) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Cn succ [Cn (pr2 npair) [proj 0; proj 1]]` THEN
  SRW_TAC [][primrec_rules, ncons_def, ADD1]);

(* nhd *)
val nhd_def = Define`nhd nl = nfst (nl - 1)`

val nhd_thm = Store_thm(
  "nhd_thm",
  ``nhd (ncons h t) = h``,
  SRW_TAC [][ncons_def, nhd_def]);

val primrec_nhd = Store_thm(
  "primrec_nhd",
  ``primrec (pr1 nhd) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `Cn (pr1 nfst) [Cn (pr2 $-) [proj 0; K 1]]` THEN
  SRW_TAC [][primrec_rules, nhd_def]);

(* ntl *)
val ntl_def = Define`ntl nlist = nsnd (nlist - 1)`

val ntl_thm = Store_thm(
  "ntl_thm",
  ``ntl (ncons h t) = t``,
  SRW_TAC [][ncons_def, ntl_def]);

val primrec_ntl = Store_thm(
  "primrec_ntl",
  ``primrec (pr1 ntl) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `Cn (pr1 nsnd) [Cn (pr2 $-) [proj 0; K 1]]` THEN
  SRW_TAC [][primrec_rules, ntl_def]);

(* ndrop *)
val ndrop_def = Define`
  (ndrop 0 nlist = nlist) ∧
  (ndrop (SUC n) nlist = ntl (ndrop n nlist))
`;

val primrec_ndrop = Store_thm(
  "primrec_ndrop",
  ``primrec (pr2 ndrop) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Pr (proj 0) (Cn (pr1 ntl) [proj 1])` THEN
  SRW_TAC [][primrec_rules] THEN
  Induct_on `m` THEN SRW_TAC [][ndrop_def]);

val ndrop_FUNPOW_ntl = store_thm(
  "ndrop_FUNPOW_ntl",
  ``∀n ms. ndrop n ms = FUNPOW ntl n ms``,
  Induct THEN SRW_TAC [][ndrop_def, FUNPOW_SUC]);

(* nel *)
val nel_def = Define`nel n nlist = nhd (ndrop n nlist)`

val nel_thm = Store_thm(
  "nel_thm",
  ``(nel 0 (ncons h t) = h) ∧
    (nel (SUC n) (ncons h t) = nel n t)``,
  SRW_TAC [][nel_def, ndrop_def] THEN
  SRW_TAC [][ndrop_FUNPOW_ntl] THEN
  SRW_TAC [][GSYM FUNPOW_SUC] THEN
  SRW_TAC [][FUNPOW])

val primrec_nel = Store_thm(
  "primrec_nel",
  ``primrec (pr2 nel) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Cn (pr1 nhd) [pr2 ndrop]` THEN
  SRW_TAC [][primrec_rules, nel_def]);

val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)


val nlist_of_def = Define`
  (nlist_of [] = 0) ∧
  (nlist_of (h::t) = ncons h (nlist_of t))
`;
val _ = export_rewrites ["nlist_of_def"]

val nel_nlist_of = store_thm(
  "nel_nlist_of",
  ``∀n l. n < LENGTH l ⇒ (nel n (nlist_of l) = EL n l)``,
  Induct THEN1 (Cases_on `l` THEN SRW_TAC [][]) THEN
  Q.X_GEN_TAC `list` THEN
  Cases_on `list` THEN SRW_TAC [][]);

open rich_listTheory

val primrec_napp = Store_thm(
  "primrec_napp",
  ``primrec (pr2 napp) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `
    Cn (pr1 nhd)
       [Pr (Cn (pr2 ncons) [proj 0; zerof])
           (* n, r, 2nd arg *)
           (let sucn = Cn succ [proj 0] in
            let tl = Cn (pr1 ntl) [sucn] in
            let hd = Cn (pr1 nhd) [sucn] in
            let pos = Cn (pr2 $-) [proj 0; tl] in
            let rres = Cn (pr2 nel) [pos; proj 1] in
            let res = Cn (pr2 ncons) [hd; rres]
            in
              Cn (pr2 ncons) [res; proj 1])]
  ` THEN
  CONJ_TAC THENL [
    SRW_TAC [][] THEN MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [][primrec_rules] THEN
    MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][primrec_rules] THEN
    MATCH_MP_TAC primrec_cn THEN SRW_TAC [][primrec_rules] THEN
    Q.UNABBREV_TAC `res` THEN
    MATCH_MP_TAC primrec_cn THEN
    `primrec sucn 3`
      by SRW_TAC [][primrec_rules, Abbr`sucn`] THEN
    SRW_TAC [][primrec_rules] THEN1
      SRW_TAC [][primrec_rules, Abbr`hd`] THEN
    Q.UNABBREV_TAC `rres` THEN MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [][primrec_rules] THEN
    `primrec tl 3` by SRW_TAC [][primrec_rules, Abbr`tl`] THEN
    SRW_TAC [][primrec_rules, Abbr`pos`],

    SIMP_TAC (srw_ss()) [] THEN
    Q.MATCH_ABBREV_TAC `∀m n. nhd (prf [m; n]) = napp m n` THEN
    Q_TAC SUFF_TAC
          `∀m n. prf [m;n] = nlist_of (GENLIST (λp. napp (m - p) n) (m + 1))`
          THEN1 SRW_TAC [][GENLIST_CONS, GSYM ADD1] THEN
    Induct THEN SRW_TAC [][Abbr`prf`, LET_THM] THEN
    SRW_TAC [][ADD_CLAUSES, GENLIST_CONS] THENL [
      POP_ASSUM (K ALL_TAC) THEN
      `∃h t. SUC m = ncons h t`
        by METIS_TAC [DECIDE ``0 ≠ SUC m``, nlist_cases] THEN
      `t < SUC m` by (FULL_SIMP_TAC (srw_ss()) [ncons_def, GSYM ADD1] THEN
                      `nsnd (h ⊗ t) = t` by SRW_TAC [][] THEN
                      `t ≤ h ⊗ t` by METIS_TAC [nsnd_le] THEN
                      DECIDE_TAC) THEN
      `(nhd (SUC m) = h) ∧ (ntl (SUC m) = t) ∧
       (napp (SUC m) n = ncons h (napp t n))` by SRW_TAC [][] THEN
      Q.PAT_ASSUM `SUC m = ncons h t` (K ALL_TAC) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [nel_nlist_of, LENGTH_GENLIST,
                                           EL_GENLIST],

      SRW_TAC [][combinTheory.o_DEF]
    ]
  ]);

val nlist_of_append = store_thm(
  "nlist_of_append",
  ``nlist_of (l1 ++ l2) = napp (nlist_of l1) (nlist_of l2)``,
  Induct_on `l1` THEN SRW_TAC [][]);

val nlist_of11 = Store_thm(
  "nlist_of11",
  ``∀l1 l2. (nlist_of l1 = nlist_of l2) ⇔ (l1 = l2)``,
  Induct THEN SRW_TAC [][] THEN Cases_on `l2` THEN SRW_TAC [][]);

val nlist_of_onto = store_thm(
  "nlist_of_onto",
  ``∀n. ∃l. nlist_of l = n``,
  HO_MATCH_MP_TAC nlist_ind THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
    Q.EXISTS_TAC `h::l` THEN SRW_TAC [][]
  ]);

val napp_nil2 = Store_thm(
  "napp_nil2",
  ``∀l1. napp l1 nnil = l1``,
  HO_MATCH_MP_TAC nlist_ind THEN SRW_TAC [][]);

val napp_ASSOC = store_thm(
  "napp_ASSOC",
  ``napp l1 (napp l2 l3) = napp (napp l1 l2) l3``,
  MAP_EVERY Q.ID_SPEC_TAC [`l3`, `l2`, `l1`] THEN
  HO_MATCH_MP_TAC nlist_ind THEN SRW_TAC [][])

val napp11 = Store_thm(
  "napp11",
  ``((napp l1 l2 = napp l1 l3) ⇔ (l2 = l3)) ∧
    ((napp l2 l1 = napp l3 l1) ⇔ (l2 = l3))``,
  MAP_EVERY
      (fn (nq, lq) => Q.SPEC_THEN nq (Q.X_CHOOSE_THEN lq (SUBST1_TAC o SYM))
                                  nlist_of_onto)
      [(`l3`,`ll3`), (`l2`,`ll2`), (`l1`,`ll1`)] THEN
  SRW_TAC [][GSYM nlist_of_append]);

val WFM_def = Define‘
  WFM M = Cn (pr2 nel) [
                proj 0;
                Pr1 (ncons (M (K 0) 0) 0)
                    (Cn (pr2 napp) [
                        proj 1;
                        Cn (pr2 ncons) [
                          pr2 (λn r. M (λi. if i ≤ n then nel i r else 0)
                                       (n + 1));
                          zerof
                        ]
                      ])
              ]
’;

val primrec_Cn = primrec_rules |> CONJUNCTS |> el 4

val restr_def = Define‘restr n r i = if i ≤ n then nel i r else 0’

val primrec_WFM = Q.store_thm(
  "primrec_WFM",
  ‘primrec (pr2 (λn r. M (restr n r) (n + 1))) 2 ⇒ primrec (WFM M) 1’,
  strip_tac >> simp[WFM_def] >> irule primrec_Cn >> simp[primrec_rules] >>
  irule primrec_Pr1 >> irule primrec_Cn >> simp[primrec_rules] >>
  irule primrec_Cn >> simp[primrec_rules, GSYM restr_def] >>
  asm_simp_tac (bool_ss ++ boolSimps.ETA_ss) []);

val primrec_FACT = Q.store_thm(
  "primrec_FACT",
  ‘primrec (WFM (λf n. if n = 0 then 1 else n * f(n - 1))) 1’,
  irule primrec_WFM >> simp[restr_def] >> irule primrec_pr2 >> simp[] >>
  qexists_tac ‘Cn (pr2 $*) [Cn succ [proj 0]; pr2 nel]’ >> simp[] >>
  irule primrec_Cn >> simp[primrec_rules]);

val nlen_nlist_of = Q.store_thm(
  "nlen_nlist_of[simp]",
  ‘nlen (nlist_of l) = LENGTH l’,
  Induct_on `l` >> simp[]);

val nlen_napp = Q.store_thm(
  "nlen_napp[simp]",
  ‘nlen (napp n1 n2) = nlen n1 + nlen n2’,
  qspec_then ‘n1’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  qspec_then ‘n2’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  simp[GSYM nlist_of_append]);

val nel_napp1 = Q.store_thm(
  "nel_napp1",
  ‘i < nlen m ⇒ (nel i (napp m n) = nel i m)’,
  qspec_then ‘m’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  qspec_then ‘n’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  simp[GSYM nlist_of_append, nel_nlist_of, EL_APPEND1]);

val nel_napp2 = Q.store_thm(
  "nel_napp2",
  ‘nlen m ≤ i ⇒ (nel i (napp m n) = nel (i - nlen m) n)’,
  qspec_then ‘m’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  qspec_then ‘n’ STRUCT_CASES_TAC (GSYM nlist_of_onto) >>
  simp[GSYM nlist_of_append] >> qid_spec_tac ‘i’ >> Induct_on ‘l’ >>
  simp[] >> Cases_on ‘i’ >> simp[]);

val WFM_correct = Q.store_thm(
  "WFM_correct",
  ‘WFM M [n] = M (λi. if i < n then WFM M [i] else 0) n’,
  simp[SimpLHS, WFM_def] >>
  qho_match_abbrev_tac ‘nel n (prt n) = M (ff n) n’ >>
  ‘prt 0 = nlist_of [M (K 0) 0]’ by simp[Abbr`prt`] >>
  ‘∀n. nlen (prt n) = n + 1’
    by (simp[Abbr`prt`] >> Induct_on ‘n’ >> simp[Pr1_correct]) >>
  ‘∀i. i ≤ n ⇒
       (nel i (prt n) = M (ff i) i) ∧ (nel i (prt i) = M (ff i) i)’
    suffices_by simp[] >>
  completeInduct_on ‘n’ >> simp[] >> rpt strip_tac >> fs[PULL_FORALL]
  >- (‘(n = 0) ∨ ∃n0. n = SUC n0’ by (Cases_on ‘n’ >> simp[])
      >- fs[Abbr`ff`, combinTheory.K_DEF] >>
      simp[] >>
      qpat_assum `Abbrev (prt = _)`
        (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      pop_assum
        (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
      simp_tac (srw_ss()) [Pr1_correct] >> rw[] >>
      Cases_on `i <= n0` >- simp[nel_napp1] >>
      ‘i = SUC n0’ by simp[] >> rw[] >> simp[nel_napp2] >>
      simp[ADD1] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      qpat_assum `Abbrev (ff = _)`
        (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      pop_assum
        (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [th]))) >>
      simp_tac (srw_ss()) [FUN_EQ_THM] >> gen_tac >> COND_CASES_TAC >>
      first_assum (fn th => simp_tac (srw_ss() ++ ARITH_ss) [th]) >>
      simp[WFM_def]) >>
  ‘(i = 0) ∨ ∃j. i = SUC j’ by (Cases_on ‘i’ >> simp[])
  >- simp[Abbr`ff`, combinTheory.K_DEF] >>
  rw[] >>
  qpat_assum `Abbrev (prt = _)`
    (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pop_assum
    (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac (srw_ss()) [Pr1_correct] >> simp[nel_napp2, ADD1] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  qpat_assum `Abbrev (ff = _)`
    (ASSUME_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pop_assum
    (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac (srw_ss()) [FUN_EQ_THM] >> gen_tac >> COND_CASES_TAC >>
  first_assum (fn th => simp_tac (srw_ss() ++ ARITH_ss) [th]) >>
  simp[WFM_def]);

val _ = export_theory ()
