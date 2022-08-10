open HolKernel boolLib bossLib Parse

open prnlistTheory numpairTheory pure_dBTheory
open enumerationsTheory primrecfnsTheory
open rich_listTheory arithmeticTheory
open pred_setTheory

open reductionEval churchnumTheory churchboolTheory normal_orderTheory
     dnoreductTheory stepsTheory recursivefnsTheory recfunsTheory
     churchlistTheory churchDBTheory nlistTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "prterm"

val _ = augment_srw_ss [rewrites [DISJ_IMP_EQ]]

Definition prtermrec_def:
  prtermrec v c a list =
    case list of
      [] => v []
    | n::t =>
        if n MOD 3 = 0 then v (n DIV 3 :: t) : num
        else if n MOD 3 = 1 then
          let t1 = nfst (n DIV 3) in
          let t2 = nsnd (n DIV 3)
          in
            c (t1 :: t2 ::
               prtermrec v c a (t1::t) :: prtermrec v c a (t2::t) :: t)
        else
          let t0 = n DIV 3
          in
            a (t0 :: prtermrec v c a (t0::t) :: t)
Termination
  WF_REL_TAC `measure (HD o SND o SND o SND)` THEN
   SRW_TAC [][] THEN
   `0 < n` by (Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []) THENL [
     MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n DIV 3` THEN
     SRW_TAC [][DIV_LESS, nsnd_le],
     MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n DIV 3` THEN
     SRW_TAC [][DIV_LESS, nfst_le],
     SRW_TAC [][DIV_LESS]
  ]
End

val prK = prove(
  ``0 < m ⇒ primrec (λl. n) m``,
  `(λl:num list. n) = K n` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][]);
val _ = augment_srw_ss [rewrites [prK]]

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
val _ = augment_srw_ss [rewrites [prproj]]
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
fun i2 q = GEN_ALL (Q.INST [`f` |-> q] prf2)

fun intro2 q = HO_MATCH_MP_TAC (i2 q)
val intro = HO_MATCH_MP_TAC

val prf1 = prove(
  ``primrec g n ∧ primrec (pr1 f) 1 ⇒ primrec (λl. f (g l)) n``,
  STRIP_TAC THEN
  `(λl. f (g l)) = Cn (pr1 f) [g]` by SRW_TAC [][FUN_EQ_THM] THEN
  SRW_TAC [][primrec_rules]);
fun i1 q = GEN_ALL (Q.INST [`f` |-> q] prf1)


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

val prCn3 = prove(
  ``primrec f 3 ∧ primrec g1 n ∧ primrec g2 n ∧ primrec g3 n ⇒
    primrec (λl. f [g1 l; g2 l; g3 l]) n``,
  STRIP_TAC THEN
  `(λl. f [g1 l; g2 l; g3 l]) = Cn f [g1; g2; g3]`
      by SRW_TAC [][FUN_EQ_THM, Cn_def] THEN
  SRW_TAC [][primrec_rules]);

val prCn4 = prove(
  ``primrec f 4 ∧ primrec g1 n ∧ primrec g2 n ∧ primrec g3 n ∧ primrec g4 n ⇒
    primrec (λl. f [g1 l; g2 l; g3 l; g4 l]) n``,
  STRIP_TAC THEN
  `(λl. f [g1 l; g2 l; g3 l; g4 l]) = Cn f [g1; g2; g3; g4]`
      by SRW_TAC [][FUN_EQ_THM, Cn_def] THEN
  SRW_TAC [][primrec_rules]);

val prCn5 = prove(
  ``primrec f 5 ∧ primrec g1 n ∧ primrec g2 n ∧ primrec g3 n ∧ primrec g4 n ∧
    primrec g5 n ⇒
    primrec (λl. f [g1 l; g2 l; g3 l; g4 l; g5 l]) n``,
  STRIP_TAC THEN
  `(λl. f [g1 l; g2 l; g3 l; g4 l; g5 l]) = Cn f [g1; g2; g3; g4; g5]`
      by SRW_TAC [][FUN_EQ_THM, Cn_def] THEN
  SRW_TAC [][primrec_rules]);

val prpred = prove(
  ``pr_predicate (λl. nB (P l))``,
  SRW_TAC [][pr_predicate_def]);

val MAP_EQ_GENLIST = prove(
  ``MAP f l = GENLIST (λi. f (EL i l)) (LENGTH l)``,
  Induct_on `l` THEN1 SRW_TAC [][GENLIST] THEN
  SRW_TAC [][GENLIST_CONS, combinTheory.o_DEF]);

val TAKE_EQ_GENLIST = store_thm(
  "TAKE_EQ_GENLIST",
  ``n ≤ LENGTH l ⇒ (TAKE n l = GENLIST (λi. l ' i) n)``,
  Q.ID_SPEC_TAC `n` THEN Induct_on `l` THEN SRW_TAC [][GENLIST] THEN
  Cases_on `n` >> simp[GENLIST_CONS, combinTheory.o_DEF]);

val swap2_def = Define`
  (swap2 f [] = f [0; 0]) ∧
  (swap2 f [n] = f [0; n]) ∧
  (swap2 f (h1::h2::t) = f (h2::h1::t))
`;

val primrec_swap2 = store_thm(
  "primrec_swap2",
  ``2 ≤ n ∧ primrec f n ⇒ primrec (swap2 f) n``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC `swap2 f = Cn f (proj 1 :: proj 0 ::
                                  GENLIST (λi. proj (i + 2)) (n - 2))`
  THENL [
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [ARITH_ss][LENGTH_GENLIST, primrec_rules, EVERY_GENLIST, ADD1],

    SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `l` THEN
    `(l = []) ∨ ∃m ms. l = m::ms` by (Cases_on `l` THEN SRW_TAC [][]) THENL [
      SRW_TAC [][Cn_def, MAP_GENLIST, combinTheory.o_DEF, swap2_def] THEN
      Cases_on `n = 2` THEN1 SRW_TAC [][GENLIST] THEN
      `2 < n` by DECIDE_TAC THEN
      IMP_RES_THEN (Q.SPEC_THEN `[0; 0]` MP_TAC) primrec_short THEN
      SRW_TAC [ARITH_ss][ADD1, combinTheory.K_DEF],

      `(ms = []) ∨ ∃p ps. ms = p::ps` by (Cases_on `ms` THEN SRW_TAC [][])
      THENL [
        SRW_TAC [][Cn_def, MAP_GENLIST, combinTheory.o_DEF, swap2_def] THEN
        Cases_on `n = 2` THEN1 SRW_TAC [][GENLIST] THEN
        `2 < n` by DECIDE_TAC THEN
        IMP_RES_THEN (Q.SPEC_THEN `[0; m]` MP_TAC) primrec_short THEN
        SRW_TAC [ARITH_ss][ADD1, combinTheory.K_DEF],

        SRW_TAC [][Cn_def, MAP_GENLIST, combinTheory.o_DEF, swap2_def] THEN
        SRW_TAC [ARITH_ss][] THEN
        `n ≤ LENGTH (p::m::ps) ∨ LENGTH (p::m::ps) < n` by DECIDE_TAC THENL [
          IMP_RES_THEN (Q.SPEC_THEN `p::m::ps` MP_TAC)
                       primrec_arg_too_long THEN
          FULL_SIMP_TAC(srw_ss() ++ ARITH_ss) [ADD1, TAKE_EQ_GENLIST],

          IMP_RES_THEN (Q.SPEC_THEN `p::m::ps` MP_TAC) primrec_short THEN
          SRW_TAC [ARITH_ss][ADD1] THEN AP_TERM_TAC THEN SRW_TAC [][] THEN
          FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ADD1] THEN
          ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [listTheory.LIST_EQ_REWRITE] THEN
          Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
          Cases_on `i < LENGTH ps` THEN1
            SRW_TAC [ARITH_ss][EL_APPEND1, proj_def] THEN
          `LENGTH ps ≤ i` by DECIDE_TAC THEN
          SRW_TAC [ARITH_ss][EL_APPEND2, proj_def]
        ]
      ]
    ]
  ]);

val primrec_cons = store_thm(
  "primrec_cons",
  ``primrec f n ⇒ primrec (λl. f (c::l)) n``,
  STRIP_TAC THEN
  `0 < n` by IMP_RES_TAC primrec_nzero THEN
  Q_TAC SUFF_TAC
        `(λl. f (c::l)) = Cn f (K c :: GENLIST proj (n - 1))`
  THENL [
    DISCH_THEN SUBST1_TAC THEN
    SRW_TAC [ARITH_ss][LENGTH_GENLIST, ADD1, EVERY_GENLIST, primrec_rules],

    SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `l` THEN
    SRW_TAC [][Cn_def, MAP_GENLIST, combinTheory.o_DEF] THEN
    `n ≤ LENGTH l + 1 ∨ LENGTH l + 1 < n` by DECIDE_TAC THENL [
      IMP_RES_THEN (Q.SPEC_THEN `c::l` MP_TAC) primrec_arg_too_long THEN
      SRW_TAC [ARITH_ss][ADD1, TAKE_EQ_GENLIST],

      IMP_RES_THEN (Q.SPEC_THEN `c::l` MP_TAC) primrec_short THEN
      SRW_TAC [ARITH_ss][ADD1] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [listTheory.LIST_EQ_REWRITE, LENGTH_GENLIST, EL_GENLIST]
                   THEN
      Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
      `i < LENGTH l ∨ LENGTH l ≤ i` by DECIDE_TAC THEN
      SRW_TAC [ARITH_ss][proj_def, EL_APPEND1, EL_APPEND2, EL_GENLIST]
    ]
  ]);



val prtermrec1_def = Define`
  prtermrec1 v c a =
   (λl. nel (l ' 0)
            (Pr (λl. ncons (v [0; l ' 0]) nnil)
              (λl.
                 let n = l ' 0 + 1 in
                 let r = l ' 1 in
                 let p = l ' 2 in
                 let m = n MOD 3
                 in
                   if m = 0 then napp r (ncons (v [n DIV 3; p]) nnil)
                   else if m = 1 then
                     let t1 = nfst (n DIV 3) in
                     let t2 = nsnd (n DIV 3) in
                     let r1 = nel t1 r in
                     let r2 = nel t2 r
                     in
                       napp r (ncons (c [t1; t2; r1; r2; p]) nnil)
                   else
                     let t0 = n DIV 3 in
                     let r0 = nel t0 r
                     in
                       napp r (ncons (a [t0; r0; p]) nnil))
              l))`

val nfst_snd_div3 = Store_thm(
  "nfst_snd_div3",
  ``0 < n ⇒ nfst (n DIV 3) < n ∧ nsnd (n DIV 3) < n``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
  Q.EXISTS_TAC `n DIV 3` THEN
  SRW_TAC [ARITH_ss][DIV_LESS, nfst_le, nsnd_le])

val prtermrec1_correct = store_thm(
  "prtermrec1_correct",
  ``prtermrec1 v c a [n; p] = prtermrec v c a [n; p]``,
  SRW_TAC [][prtermrec1_def] THEN
  Q.MATCH_ABBREV_TAC `nel n (f [n; p]) = prtermrec v c a [n; p]` THEN
  Q_TAC SUFF_TAC
    `∀n p. f [n; p] = nlist_of (GENLIST (λi. prtermrec v c a [i; p])
                                        (n + 1))`
    THEN1 SRW_TAC [][GSYM nel_correct] THEN
  Induct THEN1
    (SRW_TAC [][Abbr`f`, Once prtermrec_def]) THEN
  SRW_TAC [][Abbr`f`, LET_THM, ADD_CLAUSES, GENLIST, SNOC_APPEND]
  THENL [
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM, DIV_LESS] THEN
    SRW_TAC [ARITH_ss][GSYM nel_correct, EL_GENLIST,
                       LENGTH_GENLIST],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM] THEN
    SRW_TAC [ARITH_ss][GSYM nel_correct, DIV_LESS, LENGTH_GENLIST,
                       EL_GENLIST]
  ]);

val _ = overload_on ("nsnoc", “λn e. nlist_of (listOfN n ++ [e])”)

val primrec_termrec = Store_thm(
  "primrec_prtermrec",
  ``primrec v 2 ∧ primrec c 5 ∧ primrec a 3 ⇒
    primrec (prtermrec1 v c a) 2``,
  SRW_TAC [][prtermrec1_def] THEN
  intro2 `nel` THEN SRW_TAC [ARITH_ss][] THEN
  SRW_TAC [boolSimps.ETA_ss][] THEN
  MATCH_MP_TAC alt_Pr_rule THEN
  SRW_TAC [][LET_THM] THEN1
    SRW_TAC [][prCn2, i2 `ncons`] THEN
  intro prCOND THEN SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [
    ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN
    SRW_TAC [ARITH_ss][] THEN
    intro prCn2 THEN SRW_TAC [][] THEN
    SRW_TAC [][prDIV, i2 `$+`],

    intro prCOND THEN
    SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [
      ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC [][] THEN
      intro prCn5 THEN SRW_TAC [][] THEN
      SRW_TAC [][i1 `nfst`, prDIV, i2 `$+`, i1 `nsnd`] THEN
      intro2 `nel` THEN
      SRW_TAC [][i1 `nfst`, prDIV, i2 `$+`, i1 `nsnd`],

      ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC [][] THEN
      intro prCn3 THEN
      SRW_TAC [][i2 `nel`, i2 `$+`, prDIV],

      SRW_TAC [][pr_eq, prMOD, i2 `$+`]
    ],

    SRW_TAC [][pr_eq, prMOD, i2 `$+`]
  ]);

val nel_nlist_of = prove(
  “i < LENGTH l ⇒ (nel i (nlist_of l) = EL i l)”,
  simp[GSYM nel_correct]);

val MOD3_thm = prove(
  ``((3 * n) MOD 3 = 0) ∧
    ((3 * n + r) MOD 3 = r MOD 3)``,
  Q.SPEC_THEN `3` (MP_TAC o ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM])
              arithmeticTheory.MOD_TIMES THEN
  SRW_TAC [][] THEN
  METIS_TAC [DECIDE ``0 < 3``, arithmeticTheory.MULT_COMM,
             arithmeticTheory.MOD_EQ_0]);
val DIV3_thm = prove(
  ``((3 * n) DIV 3 = n) ∧
    ((3 * n + r) DIV 3 = n + r DIV 3)``,
  ONCE_REWRITE_TAC [MULT_COMM] THEN
  SRW_TAC [][ADD_DIV_ADD_DIV, MULT_DIV]);


val prtermrec1_thm = Store_thm(
  "prtermrec1_thm",
  ``(prtermrec1 v c a [dBnum (dV i); p] = v [i; p]) ∧
    (prtermrec1 v c a [dBnum (dAPP t1 t2); p] =
      c [dBnum t1; dBnum t2;
         prtermrec1 v c a [dBnum t1; p]; prtermrec1 v c a [dBnum t2; p]; p]) ∧
    (prtermrec1 v c a [dBnum (dABS t); p] =
      a [dBnum t; prtermrec1 v c a [dBnum t; p]; p])``,
  SRW_TAC [][prtermrec1_correct] THEN
  SRW_TAC [][SimpLHS, Once prtermrec_def, LET_THM, dBnum_def, MOD3_thm,
             DIV3_thm]);

val prtermrec0_def = Define`
  prtermrec0 v c a = Cn (prtermrec1 (Cn v [proj 0])
                                    (Cn c [proj 0; proj 1; proj 2; proj 3])
                                    (Cn a [proj 0; proj 1]))
                        [proj 0; K 0]
`;

val primrec_prtermrec0 = Store_thm(
  "primrec_prtermrec0",
  ``primrec v 1 ∧ primrec c 4 ∧ primrec a 2 ⇒ primrec (prtermrec0 v c a) 1``,
  SRW_TAC [][prtermrec0_def] THEN MATCH_MP_TAC primrec_cn THEN
  SRW_TAC [][primrec_rules]);

val prtermrec0_thm = Store_thm(
  "prtermrec0_thm",
  ``(prtermrec0 v c a [dBnum (dV i)] = v [i]) ∧
    (prtermrec0 v c a [dBnum (dAPP t1 t2)] =
       c [dBnum t1; dBnum t2; prtermrec0 v c a [dBnum t1];
          prtermrec0 v c a [dBnum t2]]) ∧
    (prtermrec0 v c a [dBnum (dABS t)] =
       a [dBnum t; prtermrec0 v c a [dBnum t]])``,
  SRW_TAC [][prtermrec0_def, Cn_def]);

val pr_is_abs_def = Define`
  pr_is_abs = (λl. nB (l ' 0 MOD 3 = 2))
`;

val primrec_is_abs = Store_thm(
  "primrec_is_abs",
  ``primrec pr_is_abs 1``,
  SRW_TAC [][pr_is_abs_def, prMOD, pr_eq]);

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
  prtermrec0 (K 1)
             (λl. let t1 = l ' 0 in
                  let r1 = l ' 2 in
                  let r2 = l ' 3
                  in
                    r1 * r2 * (1 - pr_is_abs [t1]))
             (proj 1)
`;

val primrec_pr_bnf = Store_thm(
  "primrec_pr_bnf",
  ``primrec pr_bnf 1``,
  SIMP_TAC (srw_ss()) [pr_bnf_def] THEN
  intro primrec_prtermrec0 THEN SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][LET_THM] THEN
  intro2 `$*` THEN
  SRW_TAC [][i2 `$*`, prK] THEN
  intro2 `$-` THEN
  SRW_TAC [][prCn1, primrec_is_abs]);


val pr_bnf_correct = Store_thm(
  "pr_bnf_correct",
  ``pr_bnf [n] = nB (bnf (toTerm (numdB n)))``,
  `∃d. n = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][pr_bnf_def, LET_THM] THEN
  Induct_on `d` THEN SRW_TAC [][pr_is_abs_correct, CONJ_ASSOC]);

val max_abs_def = Define`
  (max_abs (dV i) = 0) ∧
  (max_abs (dAPP t1 t2) = MAX (max_abs t1) (max_abs t2)) ∧
  (max_abs (dABS t) = 1 + max_abs t)
`;
val _ = export_rewrites ["max_abs_def"]

val primrec_MAX = Store_thm(
  "primrec_max",
  ``primrec (pr2 MAX) 2``,
  intro primrec_pr2 THEN
  Q.EXISTS_TAC `pr_cond (Cn pr_le [proj 0; proj 1]) (proj 1) (proj 0)` THEN
  SRW_TAC [][primrec_rules] THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [MAX_DEF]);

val primrec_max_abs = Store_thm(
  "primrec_max_abs",
  ``primrec (pr1 (max_abs o numdB)) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `prtermrec0 (K 0) (Cn (pr2 MAX) [proj 2; proj 3])
                               (Cn succ [proj 1])` THEN
  SRW_TAC [][] THENL [
    MATCH_MP_TAC primrec_prtermrec0 THEN SRW_TAC [][primrec_rules],
    `∃d. n = dBnum d` by METIS_TAC [dBnum_onto] THEN SRW_TAC [][] THEN
    Induct_on `d` THEN SRW_TAC [ARITH_ss][]
  ]);

(* ----------------------------------------------------------------------
    primitive recursive "lift"

    Recall the defining equations
       lift (dV i) k = if i < k then dV i else dV (i + 1)
       lift (dAPP s t) k = dAPP (lift s k) (lift t k)
       lift (dABS s) k = dABS (lift s (k + 1))
   ---------------------------------------------------------------------- *)

val maxf_def = Define`
  (maxf f 0 = f 0) ∧
  (maxf f (SUC n) = MAX (f (SUC n)) (maxf f n))
`;

val LE_maxf = store_thm(
  "LE_maxf",
  ``∀n m. m ≤ n ⇒ f m ≤ maxf f n``,
  Induct THEN SRW_TAC [][maxf_def] THEN
  `m ≤ n ∨ (m = SUC n)` by DECIDE_TAC THEN SRW_TAC [][]);

val primrec_maxf = Store_thm(
  "primrec_maxf",
  ``primrec (pr1 f) 1 ⇒ primrec (pr1 (maxf f)) 1``,
  STRIP_TAC THEN MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `
    Pr1 (f 0) (Cn (pr2 MAX) [Cn (pr1 f) [Cn succ [proj 0]]; proj 1])
  ` THEN CONJ_TAC THEN1 (MATCH_MP_TAC primrec_Pr1 THEN
                         SRW_TAC [][primrec_rules]) THEN
  Induct_on `n` THEN SRW_TAC [][maxf_def]);

val pr_lift_def = Define`
  pr_lift =
  (λns. let t = ns ' 0 in
        let k = ns ' 1 in
        let mx = pr1 (max_abs o numdB) [t] + k + 1
        in
          nel k
          (prtermrec1
             (λl. Pr (λl. let i = l ' 0
                          in
                            ncons (3 * (i + 1)) nnil)
                  (λl. let i = l ' 2 in
                       let k = l ' 0 + 1 in
                       let r = l ' 1
                       in
                         if ¬(k ≤ i) then napp r (ncons (3 * i) nnil)
                         else napp r (ncons (3 * (i + 1)) nnil))
                  [l ' 1; l ' 0])
             (λl. let t1 = l ' 0 in
                  let t2 = l ' 1 in
                  let r1 = l ' 2 in
                  let r2 = l ' 3 in
                  let gmx = l ' 4 in
                  let mx = MAX ((max_abs o numdB) t1) ((max_abs o numdB) t2)
                  in
                    Pr (λl. ncons
                              (3 * npair (nel 0 (l ' 0)) (nel 0 (l ' 1)) + 1)
                              nnil)
                       (λl. let r = l ' 1 in
                            let i = l ' 0 + 1 in
                            let rt1 = nel i (l ' 2) in
                            let rt2 = nel i (l ' 3)
                            in
                              napp r (ncons (3 * npair rt1 rt2 + 1) nnil))
                       [gmx - mx; r1; r2])
           (λl. let t = l ' 0 in
                let r = l ' 1 in
                let gmx = l ' 2 in
                let mx = (max_abs o numdB) t + 1
                in
                  Pr
                    (λl. ncons (3 * nel 1 (l ' 0) + 2) nnil)
                    (λl. let r = l ' 1 in
                         let i = l ' 0 + 2 in
                         let rt = nel i (l ' 2)
                         in
                           napp r (ncons (3 * rt + 2) nnil))
                    [gmx - mx; r])
           [t; mx]))
`;

val nsnd_le' = nsnd_le |> Q.INST [`n` |-> `x ⊗ y`]
                       |> SIMP_RULE (srw_ss()) []

val pr_lift_correct = Store_thm(
  "pr_lift_correct",
  ``pr_lift [tn; k] = dBnum (lift (numdB tn) k)``,
  SRW_TAC [][pr_lift_def] THEN
  `∃d. tn = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][LET_THM] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ABBREV_TAC `nel k (prtermrec1 v c a [dBnum d; mx]) =
                      dBnum (lift d k)` THEN
  Q_TAC SUFF_TAC `
    ∀d. max_abs d < mx ⇒
        (prtermrec1 v c a [dBnum d; mx] =
         nlist_of (GENLIST (λi. dBnum (lift d i)) (mx - max_abs d + 1)))
  ` THEN1 SRW_TAC [ARITH_ss][LENGTH_GENLIST, EL_GENLIST, nel_nlist_of,
                             Abbr`mx`] THEN
  Q.X_GEN_TAC `dd` THEN Induct_on `dd` THEN SRW_TAC [][] THENL [
    SRW_TAC [][Abbr`v`, NOT_LESS_EQUAL] THEN
    REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN Induct_on `mx` THEN
    SRW_TAC [][dBnum_def, ADD_CLAUSES, GENLIST, SNOC_APPEND],

    FULL_SIMP_TAC (srw_ss()) [] THEN Q.UNABBREV_TAC `c` THEN
    REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN
    SRW_TAC [][] THEN
    Q.MATCH_ABBREV_TAC `Pr zf sf [M;
                                  nlist_of (GENLIST gf (ddn + 1));
                                  nlist_of (GENLIST gf' (ddn' + 1))] =
                        nlist_of (GENLIST gfr (M + 1))` THEN
    `M ≤ ddn ∧ M ≤ ddn'`
      by (MAP_EVERY Q.UNABBREV_TAC [`M`, `ddn`, `ddn'`] THEN
          SRW_TAC [ARITH_ss][MAX_DEF]) THEN
    MAP_EVERY markerLib.RM_ABBREV_TAC ["M", "ddn", "ddn'"] THEN
    Induct_on `M` THENL [
      SRW_TAC [ARITH_ss][nel_nlist_of, Abbr`zf`,
                         dBnum_def, GENLIST_CONS, GSYM ADD1, Abbr`gf`,
                         Abbr`gf'`, Abbr`gfr`],
      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      SRW_TAC [ARITH_ss]
              [Abbr`sf`, Abbr`gf`, Abbr`gf'`, Abbr`gfr`, ADD_CLAUSES,
               GENLIST, SNOC_APPEND, nel_nlist_of,
               LENGTH_GENLIST, EL_GENLIST, dBnum_def]
    ],

    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    Q.UNABBREV_TAC `a` THEN markerLib.RM_ALL_ABBREVS_TAC THEN
    Q.PAT_X_ASSUM `prtermrec1 X Y Z L = FOO` (K ALL_TAC) THEN
    SRW_TAC [][] THEN
    Q.MATCH_ABBREV_TAC `Pr zf sf [M; nlist_of (GENLIST gf M1)] =
                        nlist_of (GENLIST gfr M2)` THEN
    `M2 = M + 1` by SRW_TAC [ARITH_ss][Abbr`M2`, Abbr`M`] THEN
    Q.RM_ABBREV_TAC `M2` THEN POP_ASSUM SUBST_ALL_TAC THEN
    `M + 2 ≤ M1` by SRW_TAC [ARITH_ss][Abbr`M`, Abbr`M1`] THEN
    Q.RM_ABBREV_TAC `M1` THEN
    Q.RM_ABBREV_TAC `M` THEN Induct_on `M` THEN
    SRW_TAC [ARITH_ss][Abbr`zf`, Abbr`sf`, Abbr`gf`, Abbr`gfr`] THENL [
      ASM_SIMP_TAC (bool_ss ++ ARITH_ss) [nel_nlist_of, LENGTH_GENLIST,
                                          EL_GENLIST] THEN
      SRW_TAC [][dBnum_def],

      SRW_TAC [ARITH_ss][GENLIST, ADD_CLAUSES, dBnum_def, SNOC_APPEND,
                         nel_nlist_of, LENGTH_GENLIST, EL_GENLIST]
    ]
  ]);

val primrec_not = Store_thm(
  "primrec_not",
  ``primrec (λl. nB (f l)) n ⇒ primrec (λl. nB (¬f l)) n``,
  STRIP_TAC THEN IMP_RES_TAC primrec_nzero THEN
  Q_TAC SUFF_TAC `(λl. nB (¬ f l)) = Cn (pr2 $-) [K 1; (λl. nB (f l))]`
  THEN1 SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][FUN_EQ_THM]);

val primrec_le = Store_thm(
  "primrec_le",
  ``primrec f n ∧ primrec g n ⇒ primrec (λl. nB (f l ≤ g l)) n``,
  STRIP_TAC THEN IMP_RES_TAC primrec_nzero THEN
  Q_TAC SUFF_TAC `(λl. nB (f l ≤ g l)) = Cn pr_le [f; g]` THEN1
    SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][FUN_EQ_THM]);

val prmxabs = SIMP_RULE (srw_ss()) [] (i1 `max_abs o numdB`)

val primrec_pr_lift = Store_thm(
  "primrec_pr_lift",
  ``primrec pr_lift 2``,
  SRW_TAC [][LET_THM, pr_lift_def] THEN
  intro2 `nel` THEN SRW_TAC [][] THEN
  intro prCn2 THEN SRW_TAC [][] THENL [
    MATCH_MP_TAC primrec_termrec THEN SRW_TAC [][] THENL [
      intro prCn2 THEN SRW_TAC [][] THEN
      MATCH_MP_TAC alt_Pr_rule THEN
      SRW_TAC [][i2 `ncons`, i2 `$+`, i2 `$*`] THEN
      intro prCOND THEN
      SRW_TAC [][combinTheory.o_ABS_R, i2 `nsnoc` |> BETA_RULE, i2 `$*`,
                 i2 `ncons`, prpred]
      THENL [
        ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN
        SRW_TAC [][i2 `$+`, i2 `$*`],
        SRW_TAC [][i2 `$+`]
      ],

      intro prCn3 THEN SRW_TAC [][] THENL [
        MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][] THENL [
          intro2 `ncons` THEN SRW_TAC [][prK] THEN
          intro2 `$+` THEN
          SRW_TAC [][i2 `$+`, i2 `$*`, i2 `npair`, i2 `nel`],
          ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC [][] THEN
          intro2 `$+` THEN SRW_TAC [][] THEN
          intro2 `$*` THEN SRW_TAC [][] THEN
          SRW_TAC [][i2 `$+`, i2 `$*`, i2 `npair`, i2 `nel`]
        ],
        intro2 `$-` THEN SRW_TAC [][] THEN
        intro2 `MAX` THEN SRW_TAC [][] THEN
        SRW_TAC [][prmxabs]
      ],

      intro prCn2 THEN
      SRW_TAC [][prmxabs, i2 `$-`, i2 `$+`] THEN
      MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][] THENL [
        intro2 `ncons` THEN
        SRW_TAC [][i2 `nel`, i2 `$*`, i2 `$+`],
        ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC [][] THEN
        intro2 `$+` THEN SRW_TAC [][] THEN
        SRW_TAC [][i2 `nel`, i2 `$+`, i2 `$*`]
      ]
    ],

    SRW_TAC [][prmxabs, i2 `$+`]
  ]);

val lift_larger = prove(
  ``∀t i. dBnum t ≤ dBnum (lift t i)``,
  Induct THEN SRW_TAC [][dBnum_def] THEN
  REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `i` MP_TAC)) THEN
  SRW_TAC [][LESS_EQ_LESS_EQ_MONO, npair_def]);

(* ----------------------------------------------------------------------
    de Bruijn Substitution à la Shankar, Huet and Nipkow:

      nsub s k (dV i) =
        if k < i then dV (i − 1) else if i = k then s else dV i

      nsub s k (dAPP t u) = dAPP (nsub s k t) (nsub s k u)

      nsub s k (dABS t) = dABS (nsub (lift s 0) (k + 1) t)
   ---------------------------------------------------------------------- *)

val primrec_FUNPOW = Store_thm(
  "primrec_FUNPOW",
  ``primrec (pr1 f) 1 ∧ primrec g n ∧ primrec cf n ⇒
    primrec (λl. FUNPOW f (cf l) (g l)) n``,
  STRIP_TAC THEN IMP_RES_TAC primrec_nzero THEN
  Q_TAC SUFF_TAC `(λl. FUNPOW f (cf l) (g l)) =
                  (λl. Pr (proj 0) (Cn (pr1 f) [proj 1]) [cf l; g l])`
  THEN1 (SRW_TAC [][] THEN MATCH_MP_TAC prCn2 THEN
         SRW_TAC [][primrec_rules]) THEN
  SRW_TAC [][FUN_EQ_THM] THEN
  Q.ABBREV_TAC `m = cf l` THEN Q.RM_ABBREV_TAC `m` THEN
  Induct_on `m` THEN1 SRW_TAC [][FUNPOW] THEN
  SRW_TAC [][FUNPOW_SUC]);

val _ = temp_overload_on ("sknlift",
                          ``FUNPOW (λt. dBnum (lift (numdB t) 0))``)

val pr_nsub_def = Define`
  pr_nsub =
  (λns. let s = ns ' 0 in
        let k = ns ' 1 in
        let t = ns ' 2 in
        let gmx = max_abs (numdB t) + 1
        in
          nel 0
              (prtermrec1
                 (λvs. let i = vs ' 0 in
                       let sk = nfst (vs ' 1) in
                       let gmx = nsnd (vs ' 1)
                       in
                         Pr (λzs. 0)
                            (λss. let n = ss ' 0 in
                                  let rs = ss ' 1 in
                                  let i = ss ' 2 in
                                  let sk = ss ' 3 in
                                  let s = sknlift n (nfst sk) in
                                  let k = nsnd sk + n in
                                  let r = if i = k then s
                                          else if k ≤ i then 3 * (i - 1)
                                          else 3 * i
                                  in
                                    napp rs (ncons r nnil))
                            [gmx; i; sk])
                 (λcs. let t1 = cs ' 0 in
                       let t2 = cs ' 1 in
                       let r1s = cs ' 2 in
                       let r2s = cs ' 3 in
                       let sk = nfst (cs ' 4) in
                       let gmx = nsnd (cs ' 4) in
                       let mx = MAX (max_abs (numdB t1)) (max_abs (numdB t2))
                       in
                         Pr
                           (λzs. 0)
                           (λss. let n = ss ' 0 in
                                 let r = ss ' 1 in
                                 let r1 = nel n (ss ' 2) in
                                 let r2 = nel n (ss ' 3)
                                 in
                                   napp r (ncons (3 * (r1 ⊗ r2) + 1) 0))
                           [gmx - mx; r1s; r2s])
                 (λabs. let t = abs ' 0 in
                        let rs = abs ' 1 in
                        let sk = nfst (abs ' 2) in
                        let gmx = nsnd (abs ' 2) in
                        let mx = max_abs (numdB (3 * t + 2))
                        in
                          Pr (λzs. 0)
                             (λss. let n = ss ' 0 in
                                   let r = ss ' 1 in
                                   let rs = ss ' 2 in
                                   let recresult = nel (n + 1) rs
                                   in
                                     napp r (ncons (3 * recresult + 2) 0))
                             [gmx - mx; rs])
                 [t; (s ⊗ k) ⊗ gmx]))
`;

val SUBSET_FINITE_I =
    SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO]
              SUBSET_FINITE

val _ = temp_add_rule {fixity = Closefix,
                  term_name = "lterange",
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "{", HardSpace 1, TM, BreakSpace(1,0),
                                 TOK "<..", BreakSpace(1,0), TM, HardSpace 1,
                                 TOK "}"]}
val _ = overload_on ("lterange", ``λm n. { i | m < i ∧ i ≤ n}``)

val tri_sub = prove(
  ``tri n - tri m = SUM_SET { m <.. n }``,
  Induct_on `n` THEN SRW_TAC [][] THEN
  SRW_TAC [boolSimps.CONJ_ss][SUM_SET_THM] THEN
  SRW_TAC [][tri_def] THEN
  Cases_on `m ≤ n` THENL [
    `{ m <.. SUC n} = (SUC n) INSERT { m <.. n}`
       by SRW_TAC [ARITH_ss][EXTENSION] THEN
    POP_ASSUM SUBST1_TAC THEN
    `FINITE { m <.. n}`
       by (MATCH_MP_TAC SUBSET_FINITE_I THEN Q.EXISTS_TAC `count (n + 1)` THEN
           SRW_TAC [ARITH_ss][SUBSET_DEF,
                              FINITE_COUNT,
                              IN_COUNT]) THEN
    SRW_TAC [][SUM_SET_THM] THEN
    `SUC n ∉ {m <.. n}` by SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
    `tri m ≤ tri n` by SRW_TAC [ARITH_ss][] THEN
    DECIDE_TAC,

    `{ m <.. SUC n} = {}`
       by SRW_TAC [ARITH_ss][EXTENSION] THEN
    `SUC n ≤ m` by DECIDE_TAC THEN
    `tri (SUC n) ≤ tri m` by SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [tri_def] THEN
    SRW_TAC [ARITH_ss][SUM_SET_THM]
  ]);

val npair_subx = prove(
  ``x₁ ⊗ y - x₂ ⊗ y = SUM_SET {x₂ + y <.. x₁ + y}``,
  SRW_TAC [][npair_def] THEN
  `∀x y z. (x + y) - (z + y) = x - z` by DECIDE_TAC THEN
  SRW_TAC [][tri_sub]);

val npair_suby = prove(
  ``x ⊗ y₁ - x ⊗ y₂ = SUM_SET { x + y₂ <.. x + y₁ } + (y₁ - y₂)``,
  SRW_TAC [][npair_def] THEN
  Cases_on `y₂ ≤ y₁` THENL [
    `tri (x + y₂) ≤ tri (x + y₁)` by SRW_TAC [][] THEN
    `tri (x + y₁) - tri (x + y₂) = SUM_SET { x + y₂ <.. x + y₁ }`
       by SRW_TAC [][tri_sub] THEN
    DECIDE_TAC,
    `¬(tri (x + y₂) ≤ tri (x + y₁))` by SRW_TAC [][] THEN
    `{ x + y₂ <.. x + y₁ } = {}` by
       SRW_TAC [ARITH_ss][EXTENSION] THEN
    SRW_TAC [ARITH_ss][SUM_SET_THM]
  ]);

val npair_sub = prove(
  ``a ≤ x ∧ b ≤ y ⇒ (x ⊗ y − a ⊗ b = SUM_SET { a + b <.. x + y } + (y - b))``,
  SRW_TAC [][npair_def] THEN
  `tri (a + b) ≤ tri (x + y)` by SRW_TAC [ARITH_ss][] THEN
  Q.MATCH_ABBREV_TAC `LHS = RHS` THEN
  `LHS = (tri (x + y) − tri (a + b)) + (y - b)`
     by SRW_TAC [ARITH_ss][Abbr`LHS`] THEN
  markerLib.UNABBREV_ALL_TAC THEN SRW_TAC [][tri_sub])

val FINITE_rangelte = prove(
  ``FINITE { x <.. y }``,
  MATCH_MP_TAC SUBSET_FINITE_I THEN Q.EXISTS_TAC `count (y + 1)` THEN
  SRW_TAC [ARITH_ss]
          [FINITE_COUNT, SUBSET_DEF,
           IN_COUNT]);

val SUM_SET_range_removetop = prove(
  ``lo < hi ⇒ (SUM_SET { lo <.. hi } = hi + SUM_SET { lo <.. (hi − 1)})``,
  STRIP_TAC THEN
  `({ lo <.. hi } = hi INSERT { lo <.. hi − 1 }) ∧ hi ∉ { lo <.. hi − 1 }`
     by SRW_TAC [ARITH_ss][EXTENSION] THEN
  SRW_TAC [][SUM_SET_THM, FINITE_rangelte] THEN
  FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT]);

val CARD_rangelte = prove(
  ``CARD { x <.. y } = y − x``,
  Induct_on `y` THEN1 SRW_TAC [ARITH_ss, boolSimps.CONJ_ss][] THEN
  Cases_on `x < SUC y` THENL [
    `{x <.. SUC y} = SUC y INSERT {x <.. y}`
       by SRW_TAC [ARITH_ss][EXTENSION] THEN
    `SUC y ∉ {x <.. y}` by SRW_TAC [][EXTENSION] THEN
    SRW_TAC [ARITH_ss][FINITE_rangelte],

    `{x <.. SUC y} = {}` by SRW_TAC [ARITH_ss][EXTENSION] THEN
    SRW_TAC [ARITH_ss][]
  ]);

val rangelte_empty = prove(
  ``hi ≤ lo ⇒ ({ lo <.. hi } = {})``,
  SRW_TAC [ARITH_ss][EXTENSION]);

val rangelte0 = prove(
  ``{ lo <.. 0 } = {}``,
  SRW_TAC [][rangelte_empty]);

val SUM_SET_extract = prove(
  ``SUM_SET { x + y <.. x + z } = (z - y) * x + SUM_SET {y <.. z}``,
  Induct_on `z` THEN1 SRW_TAC [][rangelte_empty] THEN
  Cases_on `SUC z ≤ y` THEN1
    SRW_TAC [ARITH_ss][rangelte_empty, SUM_SET_THM] THEN
  `y < SUC z ∧ x + y < x + SUC z` by DECIDE_TAC THEN
  SRW_TAC [(* put ARITH_ss here for BAD PERF *)]
          [SUM_SET_range_removetop,
           DECIDE ``x + SUC y − 1 = x + y``] THEN
  `x * y ≤ x * z` by SRW_TAC [ARITH_ss][] THEN
  SRW_TAC [ARITH_ss][LEFT_SUB_DISTRIB, MULT_CLAUSES]);

val SUM_SET_0arg1 = prove(
  ``SUM_SET { 0 <.. n } = tri n``,
  Induct_on `n` THEN
  SRW_TAC [][tri_def, SUM_SET_THM,
             rangelte_empty, SUM_SET_range_removetop]);


val nfstsnd0 = Store_thm(
  "nfstsnd0",
  ``(nfst 0 = 0) ∧ (nsnd 0 = 0)``,
  METIS_TAC [nfst_le, nsnd_le, DECIDE ``x ≤ 0 ⇔ (x = 0)``])

val SUM_SET_range_lowerbound = prove(
  ``lo < hi ⇒ hi ≤ SUM_SET { lo <.. hi}``,
  SRW_TAC [][SUM_SET_range_removetop]);

val pr_nsub_correct = Store_thm(
  "pr_nsub_correct",
  ``pr_nsub [s; k; t] = dBnum (nsub (numdB s) k (numdB t))``,
  SRW_TAC [][pr_nsub_def] THEN
  `∃d. t = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][LET_THM] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ABBREV_TAC `nel 0 (prtermrec1 v c a [dBnum d; (s ⊗ k) ⊗ gmx]) =
                      dBnum (nsub (numdB s) k d)` THEN
  Q_TAC SUFF_TAC `
    ∀dd. max_abs dd < gmx ⇒
         (prtermrec1 v c a [dBnum dd; (s ⊗ k) ⊗ gmx] =
          nlist_of (GENLIST
                     (λi. dBnum (nsub (numdB (sknlift i s)) (k + i) dd))
                     (gmx - max_abs dd)))
  ` THEN1 SRW_TAC [ARITH_ss][nel_nlist_of, Abbr`gmx`] THEN
  Induct_on `dd` THEN SRW_TAC [][] THENL [
    Q.UNABBREV_TAC `v` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    SRW_TAC [][] THEN
    Q.MATCH_ABBREV_TAC
        `Pr zf sf [gmx; n; s⊗k] = nlist_of (GENLIST gf gmx)` THEN
    Induct_on `gmx` THEN SRW_TAC [][GENLIST, SNOC_APPEND, Abbr`zf`] THEN
    SRW_TAC [ARITH_ss][Abbr`sf`, Abbr`gf`, dBnum_def],

    MAP_EVERY Q.RM_ABBREV_TAC [`v`, `a`] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (Q.PAT_X_ASSUM `prtermrec1 VV CC AA LL = RR` (K ALL_TAC)) THEN
    SRW_TAC [][Abbr`c`] THEN
    Q.MATCH_ABBREV_TAC `Pr zf sf [M; nlist_of (GENLIST gf1 M1);
                                  nlist_of (GENLIST gf2 M2)] =
                        nlist_of (GENLIST gfr M)` THEN
    `M ≤ M1 ∧ M ≤ M2`
      by SRW_TAC [ARITH_ss][Abbr`M`, Abbr`M1`, Abbr`M2`, MAX_DEF] THEN
    MAP_EVERY Q.RM_ABBREV_TAC [`M`, `M1`, `M2`] THEN
    Induct_on `M` THEN
    SRW_TAC [][Abbr`gf1`, Abbr`gf2`, Abbr`gfr`, Abbr`zf`, Abbr`sf`] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    Q.PAT_X_ASSUM `Pr ZZ FF LL = RR` (K ALL_TAC) THEN
    SRW_TAC [ARITH_ss][GENLIST, ADD_CLAUSES, nel_nlist_of,
                       SNOC_APPEND, dBnum_def],

    MAP_EVERY Q.RM_ABBREV_TAC [`v`, `c`] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    SRW_TAC [][Abbr`a`] THEN
    Q.PAT_X_ASSUM `pretermrec1 VV CC AA LL = RR` (K ALL_TAC) THEN
    SRW_TAC [][Once numdB_def, MOD3_thm, DIV3_thm] THEN
    Q.MATCH_ABBREV_TAC `Pr zf sf [M; nlist_of (GENLIST gf M1)] =
                        nlist_of (GENLIST gfr M2)` THEN
    `M2 = M` by SRW_TAC [ARITH_ss][Abbr`M`, Abbr`M2`] THEN
    Q.RM_ABBREV_TAC `M2` THEN POP_ASSUM SUBST_ALL_TAC THEN
    `M < M1` by SRW_TAC [ARITH_ss][Abbr`M`, Abbr`M1`] THEN
    Q.RM_ABBREV_TAC `M1` THEN
    Q.RM_ABBREV_TAC `M` THEN Induct_on `M` THEN
    SRW_TAC [][Abbr`zf`, Abbr`gf`, Abbr`gfr`, Abbr`sf`] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    Q.PAT_X_ASSUM `Pr ZZ SS LL = RR` (K ALL_TAC) THEN
    SRW_TAC [ARITH_ss][GENLIST, SNOC_APPEND, nel_nlist_of] THEN
    SRW_TAC [][GSYM ADD1, FUNPOW_SUC, dBnum_def]
  ]);

val primrec_pr_nsub = Store_thm(
  "primrec_pr_nsub",
  ``primrec pr_nsub 3``,
  SRW_TAC [][LET_THM, pr_nsub_def] THEN intro2 `nel` THEN SRW_TAC [][] THEN
  intro prCn2 THEN SRW_TAC [][i2 `npair`, prmxabs, i2 `$+`] THEN
  intro primrec_termrec THEN SRW_TAC [][] THENL [
    intro prCn3 THEN SRW_TAC [][i1 `nfst`, i1 `nsnd`] THEN
    intro alt_Pr_rule THEN SRW_TAC [][] THEN
    ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC[][] THEN
    intro prCOND THEN
    SRW_TAC [][combinTheory.o_ABS_R, prpred, pr_eq, i1`nsnd`, i2 `$+`] THENL [
      intro primrec_FUNPOW THEN SRW_TAC [][i1 `nfst`] THEN
      intro primrec_pr1 THEN Q.EXISTS_TAC `Cn pr_lift [proj 0; K 0]` THEN
      SRW_TAC [][primrec_rules],

      intro prCOND THEN SRW_TAC [][combinTheory.o_ABS_R, i2 `$*`, i2 `$-`,
                                   i2 `$+`, prpred, i1 `nsnd`]
    ],

    intro prCn3 THEN SRW_TAC [][] THENL [
      intro alt_Pr_rule THEN SRW_TAC[][] THEN
      ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC[][] THEN
      intro2 `$+` THEN
      SRW_TAC [][i2 `$*`, i2 `nel`, i2 `npair`],
      SRW_TAC [][i2 `$-`, i2 `MAX`, prmxabs, i1 `nsnd`]
    ],

    intro prCn2 THEN SRW_TAC [][] THENL [
      intro alt_Pr_rule THEN SRW_TAC[][] THEN
      ho_match_mp_tac (i2 `nsnoc` |> BETA_RULE) THEN SRW_TAC[][] THEN
      intro2 `$+` THEN
      SRW_TAC [][i2 `$*`, i2 `$+`, i2 `nel`],

      intro2 `$-` THEN
      SRW_TAC [][i1 `nsnd`, prmxabs, i2 `$*`, i2 `$+`]
    ]
  ]);

(* ----------------------------------------------------------------------
    pr_noreduct - calculate the normal order reduct of a term.

    Following treatment in the "Church" encoding, just return the identity
    if there isn't a reduct (i.e., if the term is in bnf).
   ---------------------------------------------------------------------- *)

val pr_noreduct_def = Define`
  pr_noreduct =
  prtermrec0
      (λvs. 3 * vs ' 0)
      (λcs. let t1 = cs ' 0 in
            let t2 = cs ' 1 in
            let r1 = cs ' 2 in
            let r2 = cs ' 3
            in
              if pr_is_abs [t1] = 1 then
                pr_nsub [t2; 0; prtermrec0 (proj 0) (proj 0) (proj 0) [t1]]
              else if pr_bnf [t1] = 1 then
                3 * (t1 ⊗ r2) + 1
              else 3 * (r1 ⊗ t2) + 1)
      (λabs. 3 * abs ' 1 + 2)
`;

val fv_exists = prove(
  ``∀d. ∃n. ∀m. n < m ⇒ m ∉ dFV d``,
  Induct THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `n` THEN SRW_TAC [][],
    Q.EXISTS_TAC `MAX n n'` THEN SRW_TAC [][],
    Q.EXISTS_TAC `n` THEN SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DECIDE_TAC
  ]);

val bnf_noreduct = prove(
  ``¬bnf t ⇒ ∃u. noreduct t = SOME u``,
  Cases_on `noreduct t` THEN FULL_SIMP_TAC (srw_ss())[noreduct_bnf]);

val pr_noreduct_correct = store_thm(
  "pr_noreduct_correct",
  ``pr_noreduct [n] =
      if dbnf (numdB n) then n
      else dBnum (THE (dnoreduct (numdB n)))``,
  ASM_SIMP_TAC (srw_ss()) [pr_noreduct_def] THEN
  `∃d. n = dBnum d` by METIS_TAC [dBnum_onto] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN POP_ASSUM SUBST_ALL_TAC THEN
  Induct_on `d` THEN ASM_SIMP_TAC (srw_ss()) [dBnum_def, LET_THM] THENL [
    REPEAT (Q.PAT_X_ASSUM `prtermrec0 VV CC AA L = RR` (K ALL_TAC)) THEN
    SIMP_TAC (srw_ss()) [pr_is_abs_correct] THEN
    Cases_on `is_dABS d` THEN SRW_TAC [][] THENL [
      `∃d0. d = dABS d0` by (Cases_on `d` THEN
                             FULL_SIMP_TAC (srw_ss()) []) THEN
      SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [],
      IMP_RES_TAC notbnf_dnoreduct THEN SRW_TAC [][dBnum_def],
      IMP_RES_TAC notbnf_dnoreduct THEN SRW_TAC [][dBnum_def]
    ],

    SRW_TAC [][] THEN IMP_RES_TAC notbnf_dnoreduct THEN
    SRW_TAC [][dBnum_def]
  ]);

val prnsub = store_thm(
  "prnsub",
  ``primrec f n ∧ primrec g n ∧ primrec h n ⇒
    primrec (λl. dBnum (nsub (numdB (f l)) (g l) (numdB (h l)))) n``,
  STRIP_TAC THEN Q.MATCH_ABBREV_TAC `primrec FF n` THEN
  Q_TAC SUFF_TAC `FF = Cn pr_nsub [f;g;h]` THEN1 SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][Abbr`FF`, FUN_EQ_THM]);

val prdbnf = store_thm(
  "prdbnf",
  ``primrec f n ⇒ primrec (λl. nB (dbnf (numdB (f l)))) n``,
  STRIP_TAC THEN Q.MATCH_ABBREV_TAC `primrec FF n` THEN
  Q_TAC SUFF_TAC `FF = Cn pr_bnf [f]` THEN SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][Abbr`FF`, FUN_EQ_THM]);

val primrec_noreduct = Store_thm(
  "primrec_noreduct",
  ``primrec pr_noreduct 1``,
  SRW_TAC [][pr_noreduct_def, LET_THM] THEN
  intro primrec_prtermrec0 THEN SRW_TAC [][i2 `$*`, i2 `$+`] THEN
  intro prCOND THEN SRW_TAC [][combinTheory.o_ABS_R, prpred] THENL [
    intro prnsub THEN
    SRW_TAC [][primrec_prtermrec0, primrec_rules, prCn1],
    intro prCOND THEN
    SRW_TAC [][prpred, combinTheory.o_ABS_R, i2 `$*`, i2 `npair`, i2 `$+`,
               prdbnf],
    intro pr_eq THEN SRW_TAC [][prCn1]
  ]);


(* ----------------------------------------------------------------------
    steps function
   ---------------------------------------------------------------------- *)

val pr_steps_def = Define`
  pr_steps =
  Pr (proj 0)
     (λl. let r = l ' 1
          in
            if pr_bnf [r] = 1 then r
            else pr_noreduct [r])
`;

val primrec_steps = Store_thm(
  "primrec_steps",
  ``primrec pr_steps 2``,
  SRW_TAC [][pr_steps_def] THEN MATCH_MP_TAC alt_Pr_rule THEN
  SRW_TAC [][LET_THM, primrec_rules] THEN
  intro prCOND THEN SRW_TAC [][prCn1, prpred, combinTheory.o_ABS_R, prdbnf]);

val pr_steps_correct = store_thm(
  "pr_steps_correct",
  ``pr_steps [n; t] = dBnum (fromTerm (steps n (toTerm (numdB t))))``,
  `∃d. t = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][pr_steps_def, LET_THM] THEN
  `∃M. d = fromTerm M` by METIS_TAC [fromTerm_onto] THEN SRW_TAC [][] THEN
  Induct_on `n` THEN SRW_TAC [][fromTerm_11] THENL [
    SRW_TAC [][bnf_steps_fixpoint],
    `∃N. noreduct M = SOME N` by METIS_TAC [bnf_noreduct] THEN
    SRW_TAC [][] THEN
    `steps n N = steps (SUC n) M` by SRW_TAC [][steps_def] THEN
    METIS_TAC [bnf_steps_upwards_closed, DECIDE ``n < SUC n``],
    METIS_TAC [bnf_steps_fixpoint],
    SRW_TAC [][pr_noreduct_correct] THEN
    `∃Mn' M'. (noreduct M = SOME M') ∧ (noreduct (steps n M) = SOME Mn')`
      by METIS_TAC [bnf_noreduct] THEN
    SRW_TAC [][fromTerm_11] THEN
    `Mn' = steps (1 + n) M`
       by (SRW_TAC [][steps_plus] THEN ASM_REWRITE_TAC [ONE, steps_def] THEN
           SRW_TAC [][]) THEN
    `M' = steps 1 M` by (ASM_REWRITE_TAC [ONE, steps_def] THEN
                         SRW_TAC [][]) THEN
    SRW_TAC [ARITH_ss][GSYM steps_plus]
  ]);

(* ----------------------------------------------------------------------
    bnf_of (requires minimisation - and thus recursivefnsTheory
   ---------------------------------------------------------------------- *)

val pr_steps_pred_def = Define`
  pr_steps_pred =
  Cn (pr2 $-) [K 1; Cn pr_bnf [pr_steps]]
`
val pr_steps_pred_correct = store_thm(
  "pr_steps_pred_correct",
  ``pr_steps_pred [n; t] = nB (¬dbnf (fromTerm (steps n (toTerm (numdB t)))))``,
  SRW_TAC [][pr_steps_pred_def, pr_steps_correct]);

val pr_steps_pred_EQ0 = store_thm(
  "pr_steps_pred_EQ0",
  ``(pr_steps_pred [n; t] = 0) ⇔ bnf (steps n (toTerm (numdB t)))``,
  SRW_TAC [][pr_steps_pred_correct]);

val primrec_steps_pred = Store_thm(
  "primrec_steps_pred",
  ``primrec pr_steps_pred 2``,
  SRW_TAC [][primrec_rules, pr_steps_pred_def]);


val recbnf_of_def = Define`
  recbnf_of =
  recCn (SOME o pr_steps)
        [minimise (SOME o pr_steps_pred); SOME o proj 0]
`;

val recfn_recbnf_of = Store_thm(
  "recfn_recbnf_of",
  ``recfn recbnf_of 1``,
  SRW_TAC [][recbnf_of_def] THEN MATCH_MP_TAC recfnCn THEN
  SRW_TAC [][primrec_recfn, primrec_rules, recfn_rules]);

val recbnf_of_correct = Store_thm(
  "recbnf_of_correct",
  ``recbnf_of [t] = OPTION_MAP (dBnum o fromTerm) (bnf_of (toTerm (numdB t)))``,
  SRW_TAC [][recbnf_of_def, recCn_def, LET_THM] THENL [
    FULL_SIMP_TAC (srw_ss()) [minimise_def, pr_steps_pred_EQ0] THEN
    Q.EXISTS_TAC `steps n (toTerm (numdB t))` THEN CONJ_TAC THENL [
      METIS_TAC [bnf_steps],
      Tactical.REVERSE (SRW_TAC [][])
         THEN1 (`∃i. i < n ∧ ¬(0 < pr_steps_pred [i; t])` by METIS_TAC[] THEN
                FULL_SIMP_TAC (srw_ss()) [pr_steps_pred_EQ0] THEN
                METIS_TAC[]) THEN
      SELECT_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
      Q.X_GEN_TAC `N` THEN REPEAT STRIP_TAC THEN
      SRW_TAC [][pr_steps_correct, fromTerm_11] THEN
      Q.MATCH_ABBREV_TAC
        `steps NN (toTerm (numdB t)) = steps MM (toTerm (numdB t))` THEN
      MAP_EVERY Q.RM_ABBREV_TAC [`NN`, `MM`] THEN
      Q_TAC SUFF_TAC `NN = MM` THEN1 SRW_TAC [][] THEN
      `NN < MM ∨ (NN = MM) ∨ MM < NN` by DECIDE_TAC THENL [
        `pr_steps_pred [NN; t] ≠ 0`
          by METIS_TAC [DECIDE ``0 < n ⇔ n ≠ 0``] THEN
        FULL_SIMP_TAC (srw_ss()) [pr_steps_pred_EQ0],
        `pr_steps_pred [MM; t] ≠ 0`
          by METIS_TAC [DECIDE ``0 < n ⇔ n ≠ 0``] THEN
        FULL_SIMP_TAC (srw_ss()) [pr_steps_pred_EQ0]
      ]
    ],

    FULL_SIMP_TAC (srw_ss()) [minimise_def, DECIDE ``¬(0 < n) ⇔ (n = 0)``,
                              pr_steps_pred_EQ0] THEN
    `∀n. ¬bnf (steps n (toTerm (numdB t)))`
       by (completeInduct_on `n` THEN METIS_TAC []) THEN
    METIS_TAC [optionTheory.option_CASES, bnf_steps]
  ]);

val pr_is_ichurch_def = Define`
  pr_is_ichurch = prtermrec0
                      (Cn pr_eq [proj 0; K 1])
                      (λls. let t1 = ls ' 0 in
                            let r2 = ls ' 3
                            in
                              nB (t1 = 0) * r2)
                      (K 0)
`;

val pr_is_ichurch_correct = store_thm(
  "pr_is_ichurch_correct",
  ``pr_is_ichurch [n] = nB (∃m. numdB n = FUNPOW (dAPP (dV 0)) m (dV 1))``,
  SRW_TAC [][pr_is_ichurch_def, LET_THM] THEN
  `∃d. n = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][] THEN Induct_on `d` THEN SRW_TAC [][] THENL [
    EQ_TAC THEN SRW_TAC [][] THEN1 (Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
    Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC],
    SRW_TAC [][EQ_IMP_THM] THENL [
      Q.EXISTS_TAC `SUC m` THEN SRW_TAC [][FUNPOW_SUC] THEN
      Cases_on `d` THEN FULL_SIMP_TAC (srw_ss()) [dBnum_def],
      Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [dBnum_def, FUNPOW_SUC],
      Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [dBnum_def, FUNPOW_SUC] THEN
      METIS_TAC []
    ],
    Cases_on `m` THEN SRW_TAC [][FUNPOW_SUC]
  ]);

val primrec_is_ichurch = Store_thm(
  "primrec_is_ichurch",
  ``primrec pr_is_ichurch 1``,
  SRW_TAC [][pr_is_ichurch_def] THEN MATCH_MP_TAC primrec_prtermrec0 THEN
  SRW_TAC [][primrec_rules, LET_THM] THEN intro2 `$*` THEN
  SRW_TAC [][pr_eq]);

val pr_is_church_def = Define`
  pr_is_church =
  prtermrec0 (K 0) (K 0)
             (Cn (prtermrec0 (K 0) (K 0) (Cn pr_is_ichurch [proj 0])) [proj 0])
`

val primrec_pr_is_church = Store_thm(
  "primrec_pr_is_church",
  ``primrec pr_is_church 1``,
  SRW_TAC [][pr_is_church_def] THEN
  MATCH_MP_TAC primrec_prtermrec0 THEN
  SRW_TAC [][primrec_prtermrec0, primrec_rules]);

val is_church_def = churchnumTheory.is_church_def
val pr_is_church_correct = Store_thm(
  "pr_is_church_correct",
  ``pr_is_church [t] = nB (is_church (toTerm (numdB t)))``,
  `∃d. t = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][pr_is_church_def] THEN
  Cases_on `d` THEN SRW_TAC [][] THENL [
    SRW_TAC [][is_church_def],
    SRW_TAC [][is_church_def],
    Q.MATCH_ABBREV_TAC `
      prtermrec0 (K 0) (K 0) (Cn pr_is_ichurch [proj 0]) [dBnum t] =
      nB (is_church (toTerm (dABS t)))
    ` THEN TRY (Q.RM_ABBREV_TAC `t`) THEN
    Cases_on `t` THEN SRW_TAC [][] THENL [
      `s2n (n2s n) + 1 ∉ dFV (dV n)` by SRW_TAC [ARITH_ss][] THEN
      IMP_RES_TAC toTerm_dABS THEN POP_ASSUM SUBST_ALL_TAC THEN
      SRW_TAC [][is_church_def, termTheory.LAM_eq_thm],

      Q.MATCH_ABBREV_TAC `¬is_church (toTerm (dABS (dAPP t1 t2)))` THEN
      MAP_EVERY (fn q => TRY (Q.RM_ABBREV_TAC q)) [`t1`, `t2`] THEN
      Q_TAC (binderLib.NEW_TAC "zz") `dFVs (dABS (dAPP t1 t2))` THEN
      FULL_SIMP_TAC (srw_ss()) [GSYM IN_dFV] THEN
      `s2n zz + 1 ∉ dFV (dAPP t1 t2)` by SRW_TAC [][] THEN
      POP_ASSUM (ASSUME_TAC o MATCH_MP (GEN_ALL toTerm_dABS)) THEN
      SRW_TAC [][termTheory.LAM_eq_thm, is_church_def],

      SRW_TAC[][pr_is_ichurch_correct] THEN
      Q.HO_MATCH_ABBREV_TAC `(∃n. t = FUNPOW (dAPP (dV 0)) n (dV 1)) ⇔
                             is_church (toTerm (dABS (dABS t)))` THEN
      Q.RM_ABBREV_TAC `t` THEN
      SRW_TAC [][is_church_def, toTerm_eqn,
                 churchDBTheory.fromTerm_funpow_app] THEN
      SRW_TAC [][dLAM_def] THEN EQ_TAC THENL [
        SRW_TAC [][] THEN
        MAP_EVERY Q.EXISTS_TAC [`n2s 2`, `n2s 3`, `n`] THEN SRW_TAC [][] THEN
        SRW_TAC [][churchDBTheory.fromTerm_funpow_app] THEN
        Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC],

        SRW_TAC [][] THEN Q.EXISTS_TAC `n` THEN SRW_TAC [ARITH_ss][] THEN
        Induct_on `n` THEN SRW_TAC [ARITH_ss][FUNPOW_SUC]
      ]
    ]
  ]);

(* size of a λ-term *)
val pr_dbsize_def = Define`
  pr_dbsize = prtermrec0 (K 1)
                         (Cn succ [Cn (pr2 $+) [proj 2; proj 3]])
                         (Cn succ [proj 1])
`;
val pr_dbsize_correct = Store_thm(
  "pr_dbsize_correct",
  ``pr_dbsize [n] = dbsize (numdB n)``,
  `∃d. n = dBnum d` by METIS_TAC [dBnum_onto] THEN
  SRW_TAC [][pr_dbsize_def] THEN Induct_on `d` THEN
  SRW_TAC [ARITH_ss][]);
val primrec_dbsize = Store_thm(
  "primrec_dbsize",
  ``primrec pr_dbsize 1``,
  SRW_TAC [][pr_dbsize_def] THEN intro primrec_prtermrec0 THEN
  SRW_TAC [][primrec_rules]);

(* turn a term into a number *)
val pr_forcenum_def = Define`
  pr_forcenum =
  (λl. if pr_is_church [l ' 0] = 1 then pr_dbsize [l ' 0] DIV 2 − 1 else 0)
`;
val pr_forcenum_correct = Store_thm(
  "pr_forcenum_correct",
  ``pr_forcenum [n] = force_num (toTerm (numdB n))``,
  SRW_TAC [][pr_forcenum_def, pr_is_church_correct,
             churchnumTheory.force_num_size] THEN
  SRW_TAC [][churchnumTheory.force_num_def]);

val primrec_forcenum = Store_thm(
  "primrec_forcenum",
  ``primrec pr_forcenum 1``,
  SRW_TAC [][pr_forcenum_def] THEN intro prCOND THEN
  SRW_TAC [][combinTheory.o_ABS_R, prpred] THENL [
    Q.MATCH_ABBREV_TAC `primrec f 1` THEN
    Q_TAC SUFF_TAC `f = Cn (pr2 $-) [Cn pr_div [Cn pr_dbsize [proj 0]; K 2];
                                     K 1]` THEN
    SRW_TAC [][primrec_rules] THEN
    SRW_TAC [][FUN_EQ_THM, Abbr`f`, pr_dbsize_correct],
    Q.MATCH_ABBREV_TAC `primrec f 1` THEN
    Q_TAC SUFF_TAC `f = Cn pr_is_church [proj 0]` THEN
    SRW_TAC [][primrec_rules] THEN
    SRW_TAC [][FUN_EQ_THM, Abbr`f`]
  ]);

(* Term constructors - abstractions *)
val pr_dABS_def = Define`
  pr_dABS = Cn (pr2 $+) [Cn (pr2 $*) [K 3; proj 0]; K 2]
`;
val primrec_pr_dABS = Store_thm(
  "primrec_pr_dABS",
  ``primrec pr_dABS 1``,
  SRW_TAC [][primrec_rules, pr_dABS_def]);
val pr_dABS_thm = Store_thm(
  "pr_dABS_thm",
  ``pr_dABS [n] = dBnum (dABS (numdB n))``,
  SRW_TAC [][pr_dABS_def, dBnum_def]);

(* Term constructors - applications *)
val pr_dAPP_def = Define`
  pr_dAPP = Cn (pr2 $+) [Cn (pr2 $*) [K 3; pr2 npair]; K 1]
`;
val primrec_dAPP = Store_thm(
  "primrec_dAPP",
  ``primrec pr_dAPP 2``,
  SRW_TAC [][pr_dAPP_def, primrec_rules]);
val pr_dAPP_thm = Store_thm(
  "pr_dAPP_thm",
  ``pr_dAPP [t1; t2] = dBnum (dAPP (numdB t1) (numdB t2))``,
  SRW_TAC [][pr_dAPP_def, dBnum_def]);

(* create a church numeral *)
val pr_church_def = Define`
  pr_church = Cn pr_dABS [Cn pr_dABS [Pr1 3 (Cn pr_dAPP [K 0; proj 1])]]
`;
val primrec_church = Store_thm(
  "primrec_church",
  ``primrec pr_church 1``,
  SRW_TAC [][pr_church_def] THEN intro primrec_cn THEN
  SRW_TAC [][primrec_rules]);
val pr_church_thm = Store_thm(
  "pr_church_thm",
  ``pr_church [n] = dBnum (fromTerm (church n))``,
  SRW_TAC [ARITH_ss][pr_church_def, churchnumTheory.church_def, dLAM_def,
                     churchDBTheory.fromTerm_funpow_app,
                     churchDBTheory.lift_funpow_dAPP,
                     churchDBTheory.sub_funpow_dAPP] THEN
  Q.MATCH_ABBREV_TAC `numdB N = D` THEN
  Q_TAC SUFF_TAC `N = dBnum D` THEN SRW_TAC [][] THEN
  markerLib.UNABBREV_ALL_TAC THEN
  Induct_on `n` THEN SRW_TAC [][dBnum_def, FUNPOW_SUC]);


val recPhi_def = Define`
  recPhi = recCn (SOME o pr_forcenum)
                 [recCn recbnf_of
                        [SOME o
                         Cn pr_dAPP [proj 0; Cn pr_church [proj 1]]]]
`

val recfn_recPhi = Store_thm(
  "recfn_recPhi",
  ``recfn recPhi 2``,
  SRW_TAC [][recPhi_def] THEN intro recfnCn THEN
  SRW_TAC [][primrec_recfn] THEN intro recfnCn THEN
  SRW_TAC [][primrec_recfn] THEN intro primrec_recfn THEN
  SRW_TAC [][primrec_rules]);

val recfn_recPhi_applied = Store_thm(
  "recfn_recPhi_applied",
  ``recfn (recPhi o CONS i) 1``,
  `recPhi o CONS i = recCn recPhi [K (SOME i); SOME o proj 0]`
     suffices_by (simp[] >> strip_tac >>
                  FIRST (map irule (CONJUNCTS recfn_rules)) >>
                  simp[recfn_recPhi, recfn_rules]) >>
  simp[FUN_EQ_THM, recCn_def] >> simp[recPhi_def, recCn_def]);


val recPhi_correct = store_thm(
  "recPhi_correct",
  ``recPhi [i; n] = Phi i n``,
  SRW_TAC [][Phi_def, recPhi_def, recCn_def, LET_THM] THEN
  Cases_on `bnf_of (toTerm (numdB i) @@ church n)` THEN
  FULL_SIMP_TAC (srw_ss()) []);

val recPhi_rec2Phi = store_thm(
  "recPhi_rec2Phi[simp]",
  ``recPhi = rec2 Phi``,
  simp[FUN_EQ_THM] >> Cases
  >- simp[recPhi_def, recCn_def, GSYM recPhi_correct] >>
  rename1 `recPhi (h::rest)` >> Cases_on `rest` >>
  simp[recPhi_def, recCn_def, GSYM recPhi_correct])

(* the other way - every recursive function can be emulated in the λ-calculus *)
val cnel_def = Define`
  cnel =
  natrec
    @@ (LAM "ns" (cis_zero @@ VAR "ns" @@ church 0
                           @@ (cnfst @@ (cminus @@ VAR "ns" @@ church 1))))
    @@ (LAM "n" (LAM "r" (LAM "ns" (
         cis_zero @@ VAR "ns" @@ church 0
                  @@ (VAR "r" @@ (cnsnd @@ (cminus @@ VAR "ns"
                                                   @@ church 1)))))))
`;

Theorem FV_cnel[simp]: FV cnel = {}
Proof simp[EXTENSION,cnel_def,DISJ_IMP_EQ]
QED

val cnel_equiv = brackabs.brackabs_equiv [] cnel_def

val cnel_behaviour = store_thm(
  "cnel_behaviour",
  ``cnel @@ church i @@ church n -n->* church (nel i n)``,
  SIMP_TAC (bsrw_ss()) [cnel_equiv] THEN
  Q.ID_SPEC_TAC `n` THEN Induct_on `i` THEN
  ASM_SIMP_TAC (bsrw_ss()) [natrec_behaviour, cis_zero_behaviour] THENL [
    Q.X_GEN_TAC `n` THEN
    Q.SPEC_THEN `n` STRUCT_CASES_TAC nlist_cases THENL [
      SIMP_TAC (bsrw_ss()) [cB_behaviour] ,
      SIMP_TAC (bsrw_ss()) [cB_behaviour, cminus_behaviour,
                            cnfst_behaviour] THEN
      SIMP_TAC (srw_ss() ++ ARITH_ss) [ncons_def]
    ],

    Q.X_GEN_TAC `n` THEN
    Q.SPEC_THEN `n` STRUCT_CASES_TAC nlist_cases THENL [
      SIMP_TAC (bsrw_ss()) [cB_behaviour],

      ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour, cminus_behaviour,
                                cnsnd_behaviour] THEN
      SRW_TAC [ARITH_ss][ncons_def]
    ]
  ]);
val nel_proj = prove(
  ``nel i (nlist_of l) = proj i l``,
  SRW_TAC [ARITH_ss][proj_def, nel_nlist_of] THEN
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `l` THEN Induct_on `i` THEN
  SRW_TAC [][] THEN
  Cases_on `l` THEN1 SRW_TAC [][nel_def, nhd_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []);

val cnlist_of_def = Define`
  cnlist_of =
  LAM "ns" (VAR "ns"
                @@ church 0
                @@ (LAM "h" (LAM "tr" (
                      csuc @@ (cnpair @@ VAR "h" @@ VAR "tr")))))
`;
val FV_cnlist_of = Store_thm(
  "FV_cnlist_of",
  ``FV cnlist_of = {}``,
  SRW_TAC [][cnlist_of_def, EXTENSION] THEN METIS_TAC []);

val cnlist_of_equiv = brackabs.brackabs_equiv [] cnlist_of_def

val cnlist_of_behaviour = store_thm(
  "cnlist_of_behaviour",
  ``cnlist_of @@ cvlist (MAP church ns) -n->* church (nlist_of ns)``,
  SIMP_TAC (bsrw_ss()) [cnlist_of_equiv] THEN Induct_on `ns` THEN1
    SIMP_TAC (bsrw_ss()) [cnil_def] THEN
  ASM_SIMP_TAC (bsrw_ss()) [wh_cvcons, cnpair_behaviour, csuc_behaviour,
                            ncons_def, arithmeticTheory.ADD1]);


val crecCn_def = Define`
  crecCn =
  LAM "f" (LAM "gs" (LAM "x" (
    VAR "gs"
        @@ (LAM "k" (cbnf_ofk
                       @@ cforce_num
                       @@ (cdAPP @@ (cnumdB @@ VAR "f")
                                 @@ (cchurch @@ (cfold @@ VAR "k")))))
        @@ (LAM "h" (LAM "tr" (LAM "k1" (
              (cbnf_ofk
                 @@ (LAM "k2" (VAR "tr" @@ (cappend
                                              @@ VAR "k1"
                                              @@ (ccons
                                                    @@ (cforce_num @@ VAR "k2")
                                                    @@ cnil))))
                 @@ (cdAPP @@ (cnumdB @@ VAR "h")
                           @@ (cchurch @@ VAR "x")))))))
        @@ cnil)))
`;

val FV_crecCn = Store_thm(
  "FV_crecCn",
  ``FV crecCn = {}``,
  SRW_TAC [][crecCn_def, EXTENSION]);

val crecCn_equiv = brackabs.brackabs_equiv [] crecCn_def

val crecCn_fails = store_thm(
  "crecCn_fails",
  ``∀i f gs x.
      MEM i gs ∧ (Phi i x = NONE) ⇒
      (bnf_of (crecCn @@ f @@ cvlist (MAP church gs) @@ church x) = NONE)``,
  SIMP_TAC (bsrw_ss()) [crecCn_equiv] THEN
  Q.HO_MATCH_ABBREV_TAC `
    ∀i f gs x. MEM i gs ∧ (Phi i x = NONE) ⇒
               (bnf_of (LL gs @@ NN f @@ CC x @@ cnil) = NONE)
  ` THEN
  Q_TAC SUFF_TAC `
    ∀i f gs k x. MEM i gs ∧ (Phi i x = NONE) ⇒
                 (bnf_of (LL gs @@ NN f @@ CC x @@ k) = NONE)
  ` THEN1 METIS_TAC [] THEN
  markerLib.UNABBREV_ALL_TAC THEN BETA_TAC THEN
  SIMP_TAC (bsrw_ss()) [cchurch_behaviour] THEN
  Induct_on `gs` THEN
  SIMP_TAC (bsrw_ss()) [wh_cvcons, cchurch_behaviour] THEN
  MAP_EVERY Q.X_GEN_TAC [`h`, `i`, `f`, `k`, `x`] THEN
  Cases_on `i = h` THEN1 SRW_TAC [][PhiNONE_cbnf_ofk] THEN
  SRW_TAC [][] THEN
  `(Phi h x = NONE) ∨ ∃n. Phi h x = SOME n`
      by (Cases_on `Phi h x` THEN SRW_TAC [][])
  THEN1 SRW_TAC [][PhiNONE_cbnf_ofk] THEN
  IMP_RES_TAC PhiSOME_cbnf_ofk THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []);


val crecCn_succeeds1 = store_thm(
  "crecCn_succeeds1",
  ``∀f gs x.
      (∀i. MEM i gs ⇒ ∃j. Phi i x = SOME j) ⇒
      (bnf_of (crecCn @@ f @@ cvlist (MAP church gs) @@ church x) =
       bnf_of
       (cbnf_ofk
          @@ cforce_num
          @@ (cdAPP @@ (cnumdB @@ f)
                    @@ (cchurch
                          @@ (cfold
                                @@ cvlist
                                     (MAP church
                                          (MAP (λg. THE (Phi g x))
                                               gs)))))))``,
  SIMP_TAC (bsrw_ss()) [crecCn_equiv, cchurch_behaviour,
                        cfold_correct] THEN
  Q.HO_MATCH_ABBREV_TAC `
    ∀f gs x.
      PRECOND gs x ⇒
      (bnf_of (LL gs @@ NN f @@ CC x @@ cnil) = RHS f gs x)` THEN
  Q_TAC SUFF_TAC `
    ∀f gs x ks.
      PRECOND gs x ⇒
      (bnf_of (LL gs @@ NN f @@ CC x @@ cvlist (MAP church ks)) =
       bnf_of (cbnf_ofk
                 @@ cforce_num
                 @@ (cdAPP @@ (cnumdB @@ f)
                           @@ (cDB (fromTerm (church
                                  (fold (ks ++
                                         MAP (λg. THE (Phi g x)) gs))))))))
  ` THEN1 (Q.UNABBREV_TAC `RHS` THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
           FIRST_X_ASSUM (Q.SPECL_THEN [`f`, `gs`, `x`, `[]`] MP_TAC) THEN
           SRW_TAC [][Abbr`LL`]) THEN
  markerLib.UNABBREV_ALL_TAC THEN BETA_TAC THEN Induct_on `gs` THEN1
    SIMP_TAC (bsrw_ss()) [cnil_def, cfold_correct, cchurch_behaviour] THEN
  SRW_TAC [][] THEN
  SIMP_TAC (bsrw_ss()) [wh_cvcons] THEN
  `∃j. Phi h x = SOME j` by METIS_TAC [] THEN
  IMP_RES_TAC PhiSOME_cbnf_ofk THEN
  ASM_SIMP_TAC (bsrw_ss()) [wh_ccons, wh_cvcons] THEN
  `∀i. MEM i gs ⇒ ∃j. Phi i x = SOME j` by METIS_TAC [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`f`, `x`, `ks ++ [force_num (toTerm v)]`]
                              MP_TAC) THEN
  ASM_SIMP_TAC (bsrw_ss()) [cappend_snoc] THEN
  DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]);

val MAP_CONG' = SPEC_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO] listTheory.MAP_CONG)

val cntl_def = Define`
  cntl = LAM "ns" (cnsnd @@ (cminus @@ VAR "ns" @@ church 1))
`;
val FV_cntl = Store_thm("FV_cntl", ``FV cntl = {}``,
                        SRW_TAC [][EXTENSION, cntl_def]);
val cntl_behaviour = store_thm(
  "cntl_behaviour",
  ``cntl @@ church n == church (ntl n)``,
  SIMP_TAC (bsrw_ss()) [cntl_def, cminus_behaviour, ntl_def, cnsnd_behaviour]);

val cnhd_def = Define`
  cnhd = LAM "ns" (cnfst @@ (cminus @@ VAR "ns" @@ church 1))
`;
val FV_cnhd = Store_thm("FV_cnhd", ``FV cnhd = {}``,
                        SRW_TAC [][EXTENSION, cnhd_def]);
val cnhd_behaviour = store_thm(
  "cnhd_behaviour",
  ``cnhd @@ church n == church (nhd n)``,
  SIMP_TAC (bsrw_ss()) [cnhd_def, cminus_behaviour, nhd_def, cnfst_behaviour]);

val cncons_def = Define`
  cncons = LAM "h" (LAM "t" (csuc @@ (cnpair @@ VAR "h" @@ VAR "t")))
`;
val cncons_equiv = brackabs.brackabs_equiv [] cncons_def
val FV_cncons = Store_thm(
  "FV_cncons",
  ``FV cncons = {}``,
  SRW_TAC [][EXTENSION, cncons_def]);

val cncons_behaviour = store_thm(
  "cncons_behaviour",
  ``cncons @@ church h @@ church (nlist_of t) == church (nlist_of (h::t))``,
  SIMP_TAC (bsrw_ss()) [cncons_equiv, cnpair_behaviour, ncons_def,
                        csuc_behaviour, ADD1]);

(* emulating primitive recursion.

   crecPr b s [] = b []
   crecPr b s (n::t) =
     "build a stack of pending evaluations, using cbnf_ofk giving us
      continuations off every evaluation saying what to do next.
      First call is to
        b t k
      and k is to do the appropriate number of s-steps.  Say, n is 3, then
      it will be
        b t (\n. s 0 n t (\n. s 1 n t (\n. s 2 n t I)))
      Each s-form is actually

         \n. s <number> n t k

      Constructing this recursively is a bit of a pain

        f 0 k = b t k
        f (SUC num) k = f num (s-form num t k)

      Check:
        f 1 I = f 0 (s-form 0 t I)
              = b t (\n. s 0 n t I)

        f 2 I = f 1 (s-form 1 t I)
              = f 0 (s-form 0 t (s-form 1 t I))
              = b t (s-form 0 t (\n. s 1 n t I))
              = b t (\n. s 0 n t (\n. s 1 n t I))

      So:

        f 0 = zero-case = \k. b t k (or just b t)
        f (SUC n) =
            suc-case = \n r k. r (s-form n t k)


*)

val PrSstep_def = Define`
  PrSstep =
  LAM "sdb" (LAM "t" (LAM "number" (LAM "k" (LAM "n" (
    cbnf_ofk @@ (B @@ VAR "k" @@ cforce_num)
             @@ (cdAPP
                   @@ VAR "sdb"
                   @@ (cchurch
                         @@ (cnpair
                               @@ VAR "number"
                               @@ (cnpair @@ VAR "n" @@ VAR "t")))))))))
`;

val PrSstep_eval = brackabs.brackabs_equiv [] PrSstep_def
val FV_PrSstep = Store_thm(
  "FV_PrSstep",
  ``FV PrSstep = {}``,
  SRW_TAC [][PrSstep_def, EXTENSION]);

val crecPr_def = Define`
  crecPr =
  LAM "b" (LAM "s" (LAM "ns" (
             natrec
                   @@ (LAM "k" (
                         cbnf_ofk
                           @@ (B @@ VAR "k" @@ cforce_num)
                           @@ (cdAPP @@ (cnumdB @@ VAR "b")
                                     @@ (cchurch @@ (cnsnd @@ VAR "ns")))))
                   @@ (LAM "n" (LAM "r" (LAM "k" (
                        VAR "r" @@
                            (PrSstep
                               @@ (cnumdB @@ VAR "s")
                               @@ (cnsnd @@ VAR "ns")
                               @@ VAR "n"
                               @@ VAR "k")))))
                   @@ (cnfst @@ VAR "ns")
                   @@ I)))
`;

val FV_crecPr = Store_thm(
  "FV_crecPr",
  ``FV crecPr = {}``,
  SRW_TAC [][EXTENSION, crecPr_def] );
val crecPr_equiv = brackabs.brackabs_equiv [] crecPr_def

val BIforcenum = bstore_thm(
  "BIforcenum",
  ``B @@ I @@ cforce_num == cforce_num``,
  SIMP_TAC (bsrw_ss()) [chap2Theory.B_def, cforce_num_def] THEN
  SIMP_TAC (bsrw_ss()) [chap2Theory.S_def] THEN
  Q.MATCH_ABBREV_TAC `T1 == T2` THEN
  Q_TAC SUFF_TAC `T1 = T2` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][termTheory.LAM_eq_thm, Abbr`T1`, Abbr`T2`, termTheory.tpm_fresh]);

val crecPr_cons0 = store_thm(
  "crecPr_cons0",
  ``crecPr @@ b @@ s @@ church (0 ⊗ t) ==
    cbnf_ofk @@ cforce_num @@ (cdAPP @@ (cnumdB @@ b)
                                     @@ cDB (fromTerm (church t)))``,
  SIMP_TAC (bsrw_ss()) [crecPr_equiv,
                        cnhd_behaviour, cntl_behaviour, natrec_behaviour,
                        cchurch_behaviour]);

val crecPr_consSUC = store_thm(
  "crecPr_consSUC",
  ``bnf_of (crecPr @@ church b @@ church s @@ church (SUC n ⊗ t)) =
      case bnf_of (crecPr
                     @@ church b
                     @@ church s
                     @@ church (n ⊗ t)) of
        NONE => NONE
      | SOME tm => OPTION_MAP church (Phi s (n ⊗ force_num tm ⊗ t))``,
  SIMP_TAC (bsrw_ss()) [crecPr_equiv, cis_zero_behaviour, cB_behaviour,
                        cntl_behaviour, cnhd_behaviour] THEN
  Q.HO_MATCH_ABBREV_TAC `
    bnf_of (natrec @@ ZZ @@ SS @@ church n @@ k) =
    case bnf_of (natrec @@ ZZ @@ SS @@ church n @@ I) of
      NONE => NONE
    | SOME tm => result_of tm
  ` >>
  `∀M R kk. SS @@ church M @@ R @@ kk ==
            R @@ (PrSstep
                    @@ cDB (numdB s)
                    @@ church t
                    @@ church M
                    @@ kk)`
    by asm_simp_tac (bsrw_ss()) [Abbr`SS`] >>
  `∀N k t.
     (bnf_of (natrec @@ ZZ @@ SS @@ church N @@ k) = SOME t) ⇒
     ∃m. (bnf_of (natrec @@ ZZ @@ SS @@ church N @@ I) = SOME (church m)) ∧
         ∀k'. bnf_of (natrec @@ ZZ @@ SS @@ church N @@ k') =
              bnf_of (k' @@ church m)`
    by (Induct >-
          (Q.UNABBREV_TAC `ZZ` THEN
           ASM_SIMP_TAC (bsrw_ss()) [] THEN
           Cases_on `Phi b t` >-
             asm_simp_tac (srw_ss()) [PhiNONE_cbnf_ofk] >>
           imp_res_tac PhiSOME_cbnf_ofk >>
           asm_simp_tac (bsrw_ss()) [bnf_bnf_of]) >>
        asm_simp_tac (bsrw_ss()) [] >>
        MAP_EVERY Q.X_GEN_TAC [`kk`, `tt`] >> strip_tac >>
        FIRST_ASSUM
          (Q.SPECL_THEN [`PrSstep @@ cDB (numdB s) @@ church t
                                  @@ church N @@ kk`, `tt`] MP_TAC) >>
        disch_then (fn imp => FIRST_ASSUM (fn th => STRIP_ASSUME_TAC
                                                      (MATCH_MP imp th))) >>
        asm_simp_tac (bsrw_ss()) [] >>
        asm_simp_tac (bsrw_ss()) [PrSstep_eval, cncons_behaviour] >>
        full_simp_tac (bsrw_ss()) [] >>
        Q.PAT_X_ASSUM `bnf_of (PrSstep @@ _ @@ _ @@ _ @@ _ @@ _) = SOME _`
          MP_TAC >>
        asm_simp_tac (bsrw_ss()) [PrSstep_eval] >>
        Cases_on `Phi s (N ⊗ m ⊗ t)` >-
          asm_simp_tac (bsrw_ss()) [PhiNONE_cbnf_ofk] >>
        IMP_RES_TAC PhiSOME_cbnf_ofk >>
        asm_simp_tac (bsrw_ss()) [bnf_bnf_of]) >>
  `∀N kk. (bnf_of (natrec @@ ZZ @@ SS @@ church N @@ I) = NONE) ⇒
          (bnf_of (natrec @@ ZZ @@ SS @@ church N @@ kk) = NONE)`
     by (SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
         Cases_on `bnf_of (natrec @@ ZZ @@ SS @@ church N @@ kk)` >-
           full_simp_tac (srw_ss()) [] >>
         res_tac >> full_simp_tac (srw_ss()) []) >>
  Cases_on `bnf_of (natrec @@ ZZ @@ SS @@ church n @@ I)` >-
    (res_tac >> srw_tac[][]) >>
  res_tac >> asm_simp_tac (bsrw_ss()) [] >>
  Q.UNABBREV_TAC `result_of` >>
  full_simp_tac (srw_ss()) [] >>
  srw_tac [][] >>
  simp_tac (bsrw_ss()) [Abbr`k`, PrSstep_eval] >>
  Cases_on `Phi s (n ⊗ m ⊗ t)` >-
    asm_simp_tac (bsrw_ss()) [PhiNONE_cbnf_ofk] >>
  imp_res_tac PhiSOME_cbnf_ofk >>
  asm_simp_tac (bsrw_ss()) [bnf_bnf_of]);

val cminimise_def = Define`
  cminimise =
  LAM "i" (LAM "x" (
    cfindleast
      @@ (LAM "n" (LAM "t" (LAM "f" (
            cbnf_ofk
              @@ (LAM "k" (
                    cis_zero @@ (cforce_num @@ VAR "k") @@ VAR "t" @@ VAR "f"))
              @@ (cdAPP @@ (cnumdB @@ VAR "i")
                        @@ (cchurch @@ (cnpair @@ VAR "n" @@ VAR "x")))))))
      @@ I))
`;

Theorem FV_cminimise[simp]:
  FV cminimise = {}
Proof SRW_TAC [][cminimise_def, EXTENSION]
QED

val cminimise_equiv = brackabs.brackabs_equiv [] cminimise_def

val cminimise_fail1 = store_thm(
  "cminimise_fail1",
  ``(Phi i (n ⊗ l) = NONE) ∧
    (∀m j. m < n ∧ (Phi i (m ⊗ l) = SOME j) ⇒ 0 < j) ⇒
    (bnf_of (cminimise @@ church i @@ church l) = NONE)``,
  simp_tac (bsrw_ss()) [cminimise_equiv, cfindleast_behaviour] >>
  strip_tac >>
  Q.MATCH_ABBREV_TAC `bnf_of (cfindbody P (church 0) I) = NONE` >>
  Q_TAC SUFF_TAC
    `∀N. N ≤ n ⇒ (bnf_of (cfindbody P (church N) I) = NONE)`
    >- metis_tac [DECIDE ``∀n. 0 ≤ n``] >>
  Induct_on `n - N`
   >- (rpt strip_tac >> `N = n` by DECIDE_TAC >>
       asm_simp_tac (bsrw_ss()) [Once cfindbody_thm] >>
       asm_simp_tac (bsrw_ss()) [Abbr`P`, PhiNONE_cbnf_ofk]) >>
  rpt strip_tac >>
  asm_simp_tac (bsrw_ss()) [Once cfindbody_thm] >>
  `∀mm res k.
      P @@ church mm @@ res @@ k ==
      cbnf_ofk
        @@ (C @@ (C @@ (B @@ cis_zero @@ (B @@ cforce_num @@ I))
                    @@ res)
              @@ k)
        @@ cDB (dAPP (numdB i) (fromTerm (church (mm ⊗ l))))`
    by simp_tac (bsrw_ss()) [Abbr`P`] >>
  Q.RM_ABBREV_TAC `P` >>
  asm_simp_tac (bsrw_ss()) [] >>
  Cases_on `Phi i (N ⊗ l)`
   >- asm_simp_tac (bsrw_ss()) [PhiNONE_cbnf_ofk] >>
  imp_res_tac PhiSOME_cbnf_ofk >>
  asm_simp_tac (bsrw_ss()) [] >>
  `N < n` by DECIDE_TAC >>
  `0 < x` by metis_tac [] >>
  srw_tac [ARITH_ss][] >>
  simp_tac (bsrw_ss()) [Cong cfindbody_cong] >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  FIRST_X_ASSUM MATCH_MP_TAC >>
  Q.EXISTS_TAC `n` >> asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  FIRST_X_ASSUM ACCEPT_TAC);

val appcongl = prove(
  ``(x = y) ==> (x @@ z = y @@ z)``,
  simp_tac bool_ss []);

val S' = prove(
  ``S = LAM "xx" (LAM "yy" (LAM "zz" (
          VAR "xx" @@ VAR "zz" @@ (VAR "yy" @@ VAR "zz"))))``,
  srw_tac [][termTheory.LAM_eq_thm, chap2Theory.S_def]);

val cminimise_fail2 = store_thm(
  "cminimise_fail2",
  ``(∀n j. (Phi i (n ⊗ l) = SOME j) ⇒ 0 < j) ⇒
    (bnf_of (cminimise @@ church i @@ church l) = NONE)``,
  strip_tac >>
  Cases_on `∃n. Phi i (n ⊗ l) = NONE`
   >- (MATCH_MP_TAC (GEN_ALL cminimise_fail1) >> metis_tac []) >>
  full_simp_tac (srw_ss()) [] >>
  simp_tac (bsrw_ss()) [cminimise_equiv] >>
  Q.MATCH_ABBREV_TAC `bnf_of (cfindleast @@ P @@ I) = NONE` >>
  Cases_on `bnf_of (cfindleast @@ P @@ I)` >> srw_tac [][] >>
  `∀n. P @@ church n == cB F`
     by (asm_simp_tac (bsrw_ss()) [Abbr`P`] >> gen_tac >>
         simp_tac (srw_ss()) [Cong appcongl, chap2Theory.C_def,
                              chap2Theory.S_def] >>
         simp_tac (bsrw_ss()) [chap2Theory.S_def, termTheory.lemma15a] >>
         simp_tac (srw_ss()) [Cong appcongl, chap2Theory.C_def,
                              chap2Theory.S_def] >>
         simp_tac (bsrw_ss()) [S'] >>
         Cases_on `Phi i (n ⊗ l)` >- metis_tac [] >>
         imp_res_tac PhiSOME_cbnf_ofk >>
         rename [‘Phi i (n ⊗ l) = SOME k’, ‘k = force_num _’] >>
         `0 < k` by metis_tac [] >>
         asm_simp_tac (bsrw_ss()) [] >> srw_tac [ARITH_ss][] >>
         simp_tac (bsrw_ss()) [] >>
         simp_tac (bsrw_ss()) [cB_def] >>
         Q.MATCH_ABBREV_TAC `M == N` >>
         Q_TAC SUFF_TAC `M = N` >- SRW_TAC [][] >>
         simp_tac (srw_ss()) [Abbr`M`, Abbr`N`, termTheory.LAM_eq_thm]) >>
   `∀n. ∃b. P @@ church n == cB b` by metis_tac [] >>
   `has_bnf (cfindleast @@ P @@ I)` by metis_tac [has_bnf_of] >>
   `∃r. cfindleast @@ P @@ I == r ∧ bnf r`
      by metis_tac [chap2Theory.has_bnf_def] >>
   `∃m. P @@ church m == cB T` by metis_tac [cfindleast_bnfE] >>
   POP_ASSUM MP_TAC >> asm_simp_tac (bsrw_ss()) []);

val cminimise_succeeds = store_thm(
  "cminimise_succeeds",
  ``(Phi i (j ⊗ l) = SOME 0) ∧
    (∀k. k < j ⇒ ∃r. (Phi i (k ⊗ l) = SOME r) ∧ 0 < r) ⇒
    (bnf_of (cminimise @@ church i @@ church l) = SOME (church j))``,
  strip_tac >>
  simp_tac (bsrw_ss()) [cminimise_equiv, cfindleast_behaviour] >>
  Q.MATCH_ABBREV_TAC `bnf_of (cfindbody P (church 0) I) = SOME (church j)` >>
  Q_TAC SUFF_TAC
     `∀N. N ≤ j ⇒ (bnf_of (cfindbody P (church N) I) = SOME (church j))`
     >- metis_tac [DECIDE ``0 ≤ n``] >>
  Induct_on `j - N`
    >- (rpt strip_tac >> `N = j` by DECIDE_TAC >>
        imp_res_tac PhiSOME_cbnf_ofk >>
        asm_simp_tac (bsrw_ss()) [Abbr`P`, cncons_behaviour,
                                  Once cfindbody_thm, bnf_bnf_of]) >>
  rpt strip_tac >>
  `N < j` by DECIDE_TAC >> RES_TAC >>
  Q.PAT_X_ASSUM `Phi i X = SOME r`
              (STRIP_ASSUME_TAC o MATCH_MP PhiSOME_cbnf_ofk) >>
  `∀mm res k.
      P @@ church mm @@ res @@ k ==
      cbnf_ofk
        @@ (C @@ (C @@ (B @@ cis_zero @@ (B @@ cforce_num @@ I))
                    @@ res)
              @@ k)
        @@ cDB (dAPP (numdB i) (fromTerm (church (mm ⊗ l))))`
    by simp_tac (bsrw_ss()) [Abbr`P`, cncons_behaviour] >>
  Q.RM_ABBREV_TAC `P` >>
  asm_simp_tac (bsrw_ss()) [Once cfindbody_thm] >> srw_tac [ARITH_ss][] >>
  simp_tac (bsrw_ss()) [Cong cfindbody_cong] >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  FIRST_X_ASSUM MATCH_MP_TAC >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) []);

Theorem recfns_in_Phi:
  ∀f n. recfn f n ⇒ ∃i. ∀l. LENGTH l = n ⇒ Phi i (fold l) = f l
Proof
  Induct_on ‘recfn’ >> SRW_TAC [][] THENL [
    Q.EXISTS_TAC `dBnum (fromTerm (LAM "x" (church 0)))` THEN
    SRW_TAC [][Phi_def] THEN
    SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

    Q.EXISTS_TAC ‘dBnum (fromTerm csuc) ’ >>
    rw[Phi_def] >> simp_tac (bsrw_ss()) [] >> Cases_on `l` >> fs[] >>
    SIMP_TAC (bsrw_ss() ++ ARITH_ss) [bnf_bnf_of],

    qexists_tac
      ‘dBnum (fromTerm (B @@ (cel @@ church i) @@ (cunfold @@ church n)))’ >>
    SRW_TAC [][Phi_def] THEN
    asm_simp_tac (bsrw_ss())
      [bnf_bnf_of, cunfold_correct, cel_correct, EL_MAP] >>
    simp[proj_def],

    FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM, PULL_EXISTS,
                              GSYM RIGHT_EXISTS_IMP_THM] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE (SKOLEM_CONV THENC
                                             RENAME_VARS_CONV ["gf"])) THEN
    Q.EXISTS_TAC `
      dBnum (fromTerm (crecCn @@ church i
                              @@ cvlist (MAP church (MAP gf gs))))
    ` THEN
    SRW_TAC [][Phi_def, recCn_def, LET_THM] THENL [
      `∀nopt : num option. (nopt ≠ NONE) ⇔ ∃j. nopt = SOME j`
         by SIMP_TAC (srw_ss()) [optionTheory.FORALL_OPTION] THEN
      FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MAP] THEN
      FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM] THEN
      `∀i. MEM i (MAP gf gs) ⇒ ∃j. Phi i (fold l) = SOME j`
         by (SRW_TAC [][listTheory.MEM_MAP] THEN METIS_TAC []) THEN
      POP_ASSUM (ASSUME_TAC o MATCH_MP crecCn_succeeds1) THEN
      POP_ASSUM (fn th => SIMP_TAC (srw_ss())[th]) THEN
      SIMP_TAC (bsrw_ss()) [cfold_correct, cchurch_behaviour] THEN
      SRW_TAC [][MAP_MAP_o, combinTheory.o_DEF, Cong MAP_CONG'] THEN
      Q.ABBREV_TAC `result = MAP (λx. THE (x l)) gs` THEN
      ‘LENGTH result = LENGTH gs’ by simp[Abbr‘result’] >>
      Cases_on `Phi i (fold result)` THENL [
        SRW_TAC [][PhiNONE_cbnf_ofk] THEN METIS_TAC [],
        IMP_RES_TAC PhiSOME_cbnf_ofk THEN
        ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of] THEN
        METIS_TAC []
      ],

      FULL_SIMP_TAC (srw_ss()) [listTheory.EXISTS_MEM, listTheory.MEM_MAP] THEN
      `Phi (gf g) (fold l) = NONE` by METIS_TAC [] THEN
      `MEM (gf g) (MAP gf gs)` by METIS_TAC [listTheory.MEM_MAP] THEN
      METIS_TAC [crecCn_fails]
    ],

    rename [‘recPr b s _’, ‘Phi i (fold _) = b _’, ‘Phi i' _ = s _’] >>
    ‘0 < n - 1’ by metis_tac[recfn_nzero] >> ‘2 ≤ n’ by simp[] >>
    Q.EXISTS_TAC `
      dBnum (fromTerm (crecPr @@ church i @@ church i'))
    ` THEN
    SRW_TAC [][Phi_def] THEN
    Cases_on `l` >> fs[] >>
    rename [‘fold (h::t)’] >>
    ‘fold (h::t) = h ⊗ fold t’ by (Cases_on ‘t’ >> fs[]) >> simp[] >>
    pop_assum kall_tac >>
    Induct_on `h` >-
      (SIMP_TAC (bsrw_ss()) [recPr_def, SIMP_RULE (srw_ss()) [] crecPr_cons0] >>
       Cases_on `Phi i (fold t)` >-
         (asm_simp_tac (bsrw_ss()) [PhiNONE_cbnf_ofk] >> metis_tac []) >>
       imp_res_tac PhiSOME_cbnf_ofk >>
       asm_simp_tac (bsrw_ss()) [bnf_bnf_of] >> metis_tac []) >>
    simp_tac (bsrw_ss()) [Once recPr_def,
                          SIMP_RULE (srw_ss()) [] crecPr_consSUC] >>
    full_simp_tac (srw_ss()) [] >>
    Cases_on `bnf_of (crecPr @@ church i @@ church i'
                             @@ church (h ⊗ fold t))`
    >- (full_simp_tac (srw_ss()) [] >>
        Q.PAT_X_ASSUM `NONE = FOO` (MP_TAC o SYM) >>
        simp_tac (srw_ss()) []) >>
    full_simp_tac (srw_ss()) [] >>
    Q.PAT_X_ASSUM `SOME (force_num XX) = YY` (MP_TAC o SYM) >>
    simp_tac (srw_ss()) [optionTheory.OPTION_MAP_COMPOSE] >>
    Q_TAC SUFF_TAC `∀nopt:num option. OPTION_MAP I nopt = nopt`
    >- (srw_tac [][] >>
        rename [‘h ⊗ force_num recr ⊗ fold t’] >>
        ‘h ⊗ force_num recr ⊗ fold t = fold (h :: force_num recr :: t)’
           suffices_by
             (disch_then SUBST1_TAC >> first_x_assum irule >> simp[]) >>
        Cases_on ‘t’ >> fs[]) >>
    Cases_on `nopt` >> srw_tac [][],

    Q.EXISTS_TAC `dBnum (fromTerm (cminimise @@ church i))` >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    asm_simp_tac (srw_ss())[Once Phi_def, minimise_def] >>
    gen_tac >> COND_CASES_TAC
      >- (pop_assum (Q.X_CHOOSE_THEN `m` strip_assume_tac) >>
          srw_tac [][] >>
          Q.EXISTS_TAC `church m` >>
          conj_tac
            >- (MATCH_MP_TAC cminimise_succeeds >>
                rfs[] >>
                ‘∀k. fold (k::l) = k ⊗ fold l’ by (Cases_on ‘l’ >> fs[]) >>
                fs[] >> metis_tac[]) >>
          SELECT_ELIM_TAC >> srw_tac [][] >- metis_tac [] >>
          `m < x ∨ (x = m) ∨ x < m` by DECIDE_TAC >>
          res_tac >> full_simp_tac (srw_ss() ++ ARITH_ss) []) >>
    full_simp_tac (srw_ss()) [DECIDE ``¬(0 < j) ⇔ (j = 0)``] >>
    (* qpat_x_assum `0 < n` (K ALL_TAC) >> *)
    strip_tac >> rw[] >>
    `∀q. Phi i (q ⊗ fold l) = SOME 0 ⇒
         ∃m. m < q ∧ Phi i (m ⊗ fold l) = NONE ∧
             ∀p. p < m ⇒ ∃r. Phi i (p ⊗ fold l) = SOME r ∧ 0 < r`
      by (completeInduct_on `q` >> strip_tac >>
          ‘∀N. N ⊗ fold l = fold (N::l)’ by (Cases_on ‘l’ >> fs[]) >> fs[] >>
          ‘∀N. f (N::l) = Phi i (fold (N::l))’ by simp[] >>
          `∃j. j < q ∧ ∀m. Phi i (j ⊗ fold l) = SOME m ⇒ (m = 0)`
             by metis_tac [] >>
          Cases_on `Phi i (j ⊗ fold l)`
            >- (Q.ABBREV_TAC
                  `JJ = LEAST j. Phi i (j ⊗ fold l) = NONE` >>
                `JJ ≤ j` by (Q.UNABBREV_TAC `JJ` >> numLib.LEAST_ELIM_TAC >>
                             metis_tac [DECIDE ``¬(x:num ≤ y) ⇔ y < x``]) >>
                Cases_on
                  `∀p. p < JJ ⇒
                       ∃r. (Phi i (p ⊗ fold l) = SOME r) ∧ 0 < r`
                  >- (Q_TAC SUFF_TAC
                            `(Phi i (JJ ⊗ fold l) = NONE) ∧ JJ < q`
                            >- metis_tac [] >>
                      conj_tac >-
                        (Q.UNABBREV_TAC `JJ` >> numLib.LEAST_ELIM_TAC >>
                         metis_tac []) >> DECIDE_TAC) >>
                full_simp_tac (srw_ss()) [DECIDE ``¬(0 < j) ⇔ (j = 0)``] >>
                Cases_on `Phi i (p ⊗ fold l)`
                  >- (Q_TAC SUFF_TAC `F` >- metis_tac [] >>
                      Q.PAT_X_ASSUM `p < JJ` MP_TAC >>
                      POP_ASSUM MP_TAC >> Q.UNABBREV_TAC `JJ` >>
                      numLib.LEAST_ELIM_TAC >> metis_tac []) >>
                `Phi i (p ⊗ fold l) = SOME 0`
                   by full_simp_tac (srw_ss()) [] >>
                `p < q` by DECIDE_TAC >>
                `∃M. M < p ∧ (Phi i (M ⊗ fold l) = NONE) ∧
                     ∀p. p < M ⇒ ∃r. (Phi i (p ⊗ fold l) = SOME r) ∧
                                      0 < r` by metis_tac [] >>
                Q.EXISTS_TAC `M` >> srw_tac [ARITH_ss][] >> metis_tac[]) >>
          rename [‘Phi i (j ⊗ fold l) = SOME x’] >>
          `x = 0` by srw_tac[][] >> srw_tac[][] >>
          `∃M. M < j ∧ Phi i (M ⊗ fold l) = NONE ∧
               ∀p. p < M ⇒ ∃r. Phi i (p ⊗ fold l) = SOME r ∧ 0 < r`
             by metis_tac [] >>
          Q.EXISTS_TAC `M` >> srw_tac [ARITH_ss][] >> metis_tac[]) >>
    Cases_on `∃n. Phi i (n ⊗ fold l) = SOME 0`
      >- (POP_ASSUM STRIP_ASSUME_TAC >> res_tac >>
          MATCH_MP_TAC (GEN_ALL cminimise_fail1) >>
          Q.EXISTS_TAC `m` >> srw_tac [][] >>
          metis_tac [optionTheory.SOME_11]) >>
    full_simp_tac (srw_ss()) [] >>
    MATCH_MP_TAC (GEN_ALL cminimise_fail2) >> srw_tac [][] >>
    first_x_assum (Q.SPEC_THEN `n` MP_TAC) >> srw_tac [ARITH_ss][]
  ]
QED

(* "universal machine index" *)
val UMi_def = new_specification(
  "UMi_def", ["UMi"],
  MATCH_MP recfns_in_Phi recfn_recPhi |> SIMP_RULE (srw_ss()) [])

Theorem UMi_works =
  UMi_def |> Q.SPEC `[m;n]` |> SIMP_RULE (srw_ss()) []

val _ = export_theory()
