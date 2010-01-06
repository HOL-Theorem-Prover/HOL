open HolKernel boolLib bossLib Parse

open prnlistTheory numpairTheory pure_dBTheory
open enumerationsTheory primrecfnsTheory
open rich_listTheory arithmeticTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "prterm"

(*
val prcons_exists = prove(
  ``∀f n. primrec f n ⇒
          1 < n ⇒ ∀m. ∃g. primrec g (n - 1) ∧ ∀l. g l = f (m::l)``,
  HO_MATCH_MP_TAC strong_primrec_ind THEN SRW_TAC [][] THENL [
    Cases_on `i` THEN SRW_TAC [][] THENL [
      Q.EXISTS_TAC `K m` THEN SRW_TAC [ARITH_ss][],
      Q.EXISTS_TAC `proj n'` THEN SRW_TAC [ARITH_ss][primrec_rules]
    ],
    FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM] THEN
    `∀m f. ∃g. MEM f gs ⇒ primrec g (n - 1) ∧ ∀l. g l = f (m::l)`
      by METIS_TAC [] THEN
    POP_ASSUM (Q.SPEC_THEN `m` (Q.X_CHOOSE_THEN `gf` STRIP_ASSUME_TAC o
                                CONV_RULE SKOLEM_CONV)) THEN
    Q.EXISTS_TAC `Cn f (MAP gf gs)` THEN
    SRW_TAC [][] THENL [
      MATCH_MP_TAC primrec_cn THEN
      SRW_TAC [][listTheory.EVERY_MEM, listTheory.MEM_MAP] THEN METIS_TAC [],
      SRW_TAC [][Cn_def, rich_listTheory.MAP_MAP_o] THEN
      SRW_TAC [][combinTheory.o_DEF] THEN
      AP_TERM_TAC THEN SRW_TAC [][MAP_EQ]
    ],

  *)



val prK = prove(
  ``0 < m ⇒ primrec (λl. n) m``,
  `(λl:num list. n) = K n` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][]);

val prCOND = prove(
  ``primrec f n ∧ primrec g n ∧ primrec (nB o P) n ∧ pr_predicate (nB o P) ⇒
    primrec (λl. if P l then f l else g l) n``,
  STRIP_TAC THEN
  `(λl. if P l then f l else g l) = pr_cond (nB o P) f g`
     by SRW_TAC [][pr_cond_def, FUN_EQ_THM] THEN
  SRW_TAC [][]);

val pr_eq = prove(
  ``primrec f n ∧ primrec g n ⇒ primrec (λl. nB (f l = g l)) n``,
  STRIP_TAC THEN
  `(λl. nB (f l = g l)) = Cn pr_eq [f; g]`
     by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);

val prproj = prove(
  ``i < n ⇒ primrec (λl. proj i l) n``,
  SRW_TAC [boolSimps.ETA_ss][primrec_rules]);

val _ = temp_overload_on ("'", ``λl i. proj i l``)

val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)

val prMOD = prove(
  ``0 < n ∧ primrec f m ⇒ primrec (λl. f l MOD n) m``,
  STRIP_TAC THEN
  `(λl. f l MOD n) = Cn pr_mod [f; K n]`
     by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][] THEN MATCH_MP_TAC primrec_cn THEN SRW_TAC [][] THEN
  METIS_TAC [primrec_K, primrec_nzero])

val prDIV = prove(
  ``0 < n ∧ primrec f m ⇒ primrec (λl. f l DIV n) m``,
  STRIP_TAC THEN
  `(λl. f l DIV n) = Cn pr_div [f; K n]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][] THEN MATCH_MP_TAC primrec_cn THEN SRW_TAC [][] THEN
  METIS_TAC [primrec_K, primrec_nzero]);

val prf2 = prove(
  ``primrec (pr2 f) 2 ∧ primrec g n ∧ primrec h n ⇒
    primrec (λl. f (g l) (h l)) n``,
  STRIP_TAC THEN
  `(λl. f (g l) (h l)) = Cn (pr2 f) [g; h]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);

val pr_is_abs_def = Define`
  pr_is_abs = (λl. nB (l ' 0 MOD 3 = 2))
`;

val primrec_is_abs = Store_thm(
  "primrec_is_abs",
  ``primrec pr_is_abs 1``,
  SRW_TAC [][pr_is_abs_def, prMOD, prproj, prK, pr_eq]);

val MOD3_thm = prove(
  ``((3 * n) MOD 3 = 0) ∧
    ((3 * n + r) MOD 3 = r MOD 3)``,
  Q.SPEC_THEN `3` (MP_TAC o ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM])
              arithmeticTheory.MOD_TIMES THEN
  SRW_TAC [][] THEN
  METIS_TAC [DECIDE ``0 < 3``, arithmeticTheory.MULT_COMM,
             arithmeticTheory.MOD_EQ_0]);

val prCn1 = prove(
  ``primrec f 1 ∧ primrec g n ⇒ primrec (λl. f [g l]) n``,
  STRIP_TAC THEN
  `(λl. f [g l]) = Cn f [g]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);

val prCn2 = prove(
  ``primrec f 2 ∧ primrec g n ∧ primrec h n ⇒ primrec (λl. f [g l; h l]) n``,
  STRIP_TAC THEN
  `(λl. f [g l; h l]) = Cn f [g; h]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);

val pr_is_abs_thm = Store_thm(
  "pr_is_abs_thm",
  ``(pr_is_abs [dBnum (dABS t)] = 1) ∧
    (pr_is_abs [dBnum (dAPP t1 t2)] = 0) ∧
    (pr_is_abs [dBnum (dV i)] = 0)``,
  SRW_TAC [][pr_is_abs_def, dBnum_def, MOD3_thm]);

val pr_is_abs_correct = store_thm(
  "pr_is_abs_correct",
  ``pr_is_abs [n] = nB (is_dABS (numdB n))``,
  SRW_TAC [][pr_is_abs_def, Once numdB_def] THEN
  `n MOD 3 < 3` by SRW_TAC [][MOD_LESS] THEN DECIDE_TAC);

val pr_bnf_def = Define`
  pr_bnf =
  (λl. nel
       (l ' 0)
       (Pr (λl. ncons 1 nnil)
           (λl. let n = l ' 0 + 1 in
                let rlist = l ' 1 in
                let m = n MOD 3
                in
                  if m = 0 then napp rlist (ncons 1 nnil)
                  else if m = 2 then
                    let subpos = n DIV 3 in
                    let rres = nel subpos rlist
                    in
                      napp rlist (ncons rres nnil)
                  else
                    let subpos = n DIV 3 in
                    let arg1 = nfst subpos in
                    let arg1r = nel (nfst subpos) rlist in
                    let arg2r = nel (nsnd subpos) rlist in
                    let res = (arg1r * arg2r * (1 - pr_is_abs [arg1]))
                    in
                      napp rlist (ncons res nnil))
           [l ' 0; 0]))
`;

fun i2 q = GEN_ALL (Q.INST [`f` |-> q] prf2)

val prf1 = prove(
  ``primrec g n ∧ primrec (pr1 f) 1 ⇒ primrec (λl. f (g l)) n``,
  STRIP_TAC THEN
  `(λl. f (g l)) = Cn (pr1 f) [g]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);
fun i1 q = GEN_ALL (Q.INST [`f` |-> q] prf1)

val prpred = prove(
  ``pr_predicate (λl. nB (f l = g l))``,
  SRW_TAC [][pr_predicate_def]);

val primrec_pr_bnf = Store_thm(
  "primrec_pr_bnf",
  ``primrec pr_bnf 1``,
  SIMP_TAC (srw_ss()) [pr_bnf_def] THEN
  HO_MATCH_MP_TAC (GEN_ALL (Q.INST [`f` |-> `nel`] prf2)) THEN
  SRW_TAC [][prK, prproj] THEN
  HO_MATCH_MP_TAC prCn2 THEN SRW_TAC [][prK, prproj] THEN
  HO_MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][i2 `ncons`, prK] THEN
  SRW_TAC [][LET_THM] THEN
  HO_MATCH_MP_TAC prCOND THEN
  SRW_TAC [][combinTheory.o_ABS_R, i2 `napp`, prproj, prK, i2 `ncons`, prMOD,
             pr_eq, prpred, i2 `$+`] THEN
  HO_MATCH_MP_TAC prCOND THEN
  SRW_TAC [][combinTheory.o_ABS_R, prMOD, pr_eq, prproj, prK, prpred,
             i2 `$+`] THEN1
    (HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [][prproj] THEN
     HO_MATCH_MP_TAC (i2 `ncons`) THEN
     SRW_TAC [][i2 `nel`, prDIV, prK, prproj, i2 `$+`]) THEN
  HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [][prproj] THEN
  HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [][prK] THEN
  HO_MATCH_MP_TAC (i2 `$*`) THEN SRW_TAC [][] THENL [
    HO_MATCH_MP_TAC (i2 `$*`) THEN SRW_TAC [][] THEN
    HO_MATCH_MP_TAC (i2 `nel`) THEN
    SRW_TAC [][i1 `nfst`, prproj, prDIV, prK, i1 `nsnd`, i2 `$+`],

    HO_MATCH_MP_TAC (i2 `$-`) THEN SRW_TAC [][prK] THEN
    HO_MATCH_MP_TAC prCn1 THEN SRW_TAC [][i1 `nfst`, prDIV, prK, prproj,
                                          i2 `$+`]
  ]);

val GENLIST_CONS = prove(
  ``GENLIST f (SUC n) = f 0 :: (GENLIST (f o SUC) n)``,
  Induct_on `n` THEN SRW_TAC [][GENLIST, SNOC]);
val GENLIST1 = prove(``GENLIST f 1 = [f 0]``,
                     SIMP_TAC bool_ss [ONE, GENLIST, SNOC]);

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

val pr_bnf_correct = Store_thm(
  "pr_bnf_correct",
  ``pr_bnf [n] = nB (bnf (toTerm (numdB n)))``,
  SRW_TAC [][pr_bnf_def] THEN
  Q.MATCH_ABBREV_TAC `nel n (f [n; 0]) = nB (dbnf (numdB n))` THEN
  Q_TAC SUFF_TAC
    `∀n. f [n; 0] = nlist_of (GENLIST (λp. nB (bnf (toTerm (numdB p))))
                                      (n + 1))`
    THEN1 SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST] THEN
  Induct THEN1
    SRW_TAC [][Abbr`f`, GENLIST1, Once numdB_def] THEN
  SRW_TAC [][Abbr`f`, LET_THM, GENLIST, ADD_CLAUSES, SNOC_APPEND,
             nlist_of_append] THEN
  Q.PAT_ASSUM `Pr f g X = Y` (K ALL_TAC) THENL [
    SRW_TAC [][Once numdB_def],
    SRW_TAC [][Once numdB_def, SimpRHS] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [ARITH_ss][nel_nlist_of, EL_GENLIST, DIV_LESS, LENGTH_GENLIST],

    SRW_TAC [][Once numdB_def, SimpRHS] THENL [
      `nfst ((n + 1) DIV 3) < n + 1 ∧
       nsnd ((n + 1) DIV 3) < n + 1`
         by (CONJ_TAC THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
             Q.EXISTS_TAC `(n + 1) DIV 3` THEN
             SRW_TAC [ARITH_ss][DIV_LESS, nfst_le, nsnd_le]) THEN
      SRW_TAC [][nel_nlist_of, EL_GENLIST, LENGTH_GENLIST, pr_is_abs_correct,
                 CONJ_ASSOC],

      `(n + 1) MOD 3 < 3` by SRW_TAC [][MOD_LESS] THEN DECIDE_TAC
    ]
  ]);

val _ = export_theory()
