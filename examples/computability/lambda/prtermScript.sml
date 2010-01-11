open HolKernel boolLib bossLib Parse

open prnlistTheory numpairTheory pure_dBTheory
open enumerationsTheory primrecfnsTheory
open rich_listTheory arithmeticTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "prterm"

val prtermrec_def = tDefine "prtermrec" `
  prtermrec v c a list =
    case list of
       [] -> v []
    || n::t ->
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
            a (t0 :: prtermrec v c a (t0::t) :: t)`
  (WF_REL_TAC `measure (HD o SND o SND o SND)` THEN
   SRW_TAC [][] THEN
   `0 < n` by (Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []) THENL [
     MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n DIV 3` THEN
     SRW_TAC [][DIV_LESS, nsnd_le],
     MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n DIV 3` THEN
     SRW_TAC [][DIV_LESS, nfst_le],
     SRW_TAC [][DIV_LESS]
   ])

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
fun i2 q = GEN_ALL (Q.INST [`f` |-> q] prf2)

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
  ``pr_predicate (λl. nB (f l = g l))``,
  SRW_TAC [][pr_predicate_def]);

val NTL_def = Define`(NTL [] = []) ∧ (NTL ((h:num)::t) = t)`

val strong_primrec_ind = IndDefLib.derive_strong_induction(primrec_rules,
                                                           primrec_ind)

val GENLIST_CONS = prove(
  ``GENLIST f (SUC n) = f 0 :: (GENLIST (f o SUC) n)``,
  Induct_on `n` THEN SRW_TAC [][GENLIST, SNOC]);
val GENLIST1 = prove(``GENLIST f 1 = [f 0]``,
                     SIMP_TAC bool_ss [ONE, GENLIST, SNOC]);
val MAP_EQ_GENLIST = prove(
  ``MAP f l = GENLIST (λi. f (EL i l)) (LENGTH l)``,
  Induct_on `l` THEN1 SRW_TAC [][GENLIST] THEN
  SRW_TAC [][GENLIST_CONS, combinTheory.o_DEF]);

val TAKE_EQ_GENLIST = store_thm(
  "TAKE_EQ_GENLIST",
  ``n ≤ LENGTH l ⇒ (TAKE n l = GENLIST (λi. l ' i) n)``,
  Q.ID_SPEC_TAC `n` THEN Induct_on `l` THEN SRW_TAC [][GENLIST] THEN
  `∃m. n = SUC m` by (Cases_on `n` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [GENLIST_CONS, combinTheory.o_DEF]);

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
          ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                       [listTheory.LIST_EQ_REWRITE, LENGTH_GENLIST,
                        EL_GENLIST] THEN
          Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
          Cases_on `i < LENGTH ps` THEN1
            SRW_TAC [ARITH_ss][EL_APPEND1, proj_def] THEN
          `LENGTH ps ≤ i` by DECIDE_TAC THEN
          SRW_TAC [ARITH_ss][EL_APPEND2, EL_GENLIST, proj_def]
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


val fcons_ntl2 = store_thm(
  "fcons_ntl2",
  ``primrec f n ∧ primrec g (n + 2) ⇒
    primrec (λl. f (g l :: NTL (NTL l))) (n + 2)``,
  STRIP_TAC THEN
  `0 < n` by METIS_TAC [primrec_nzero] THEN
  Q.MATCH_ABBREV_TAC `primrec h (n + 2)` THEN
  Q_TAC SUFF_TAC `h = Cn f (g::GENLIST (λi. proj (i + 2)) (n - 1))`
  THEN1
    (DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC primrec_cn THEN
     SRW_TAC [ARITH_ss][LENGTH_GENLIST, EVERY_GENLIST, ADD1,
                        primrec_rules]) THEN
  Q.UNABBREV_TAC `h` THEN SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `l` THEN SRW_TAC [][Cn_def,MAP_GENLIST, combinTheory.o_ABS_R] THEN
  Q.PAT_ASSUM `primrec g (n + 2)` (K ALL_TAC) THEN
  Cases_on `LENGTH (NTL (NTL l)) + 1 < n` THENL [
    IMP_RES_THEN (Q.SPEC_THEN `g l :: NTL (NTL l)` MP_TAC) primrec_short THEN
    SRW_TAC [ARITH_ss][ADD1] THEN AP_TERM_TAC  THEN SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [listTheory.LIST_EQ_REWRITE,
                                         LENGTH_GENLIST, EL_GENLIST] THEN
    Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
    Cases_on `l` THEN1 SRW_TAC [][EL_GENLIST, proj_def, NTL_def] THEN
    SRW_TAC [ARITH_ss][NTL_def] THEN
    Cases_on `t` THEN1 SRW_TAC [][EL_GENLIST, proj_def, NTL_def] THEN
    SRW_TAC [ARITH_ss][NTL_def, proj_def, EL_APPEND1, EL_APPEND2,
                       EL_GENLIST],

    IMP_RES_THEN (Q.SPEC_THEN `g l :: NTL (NTL l)` MP_TAC)
                 primrec_arg_too_long THEN
    SRW_TAC [ARITH_ss][ADD1, TAKE_EQ_GENLIST] THEN AP_TERM_TAC THEN
    SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [listTheory.LIST_EQ_REWRITE,
                                         LENGTH_GENLIST, EL_GENLIST] THEN
    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [NTL_def] THEN
    Cases_on `t` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [NTL_def]
  ]);


val primrec_consNTL = store_thm(
  "primrec_consNTL",
  ``primrec f n ⇒ primrec (λl. f (c::NTL l)) n``,
  STRIP_TAC THEN
  `0 < n` by METIS_TAC [primrec_nzero] THEN
  Q_TAC SUFF_TAC
    `(λl. f (c::NTL l)) = Cn f (K c::GENLIST (λi. proj (i + 1)) (n - 1))`
  THENL [
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [ARITH_ss][LENGTH_GENLIST, ADD1, EVERY_GENLIST, primrec_rules],

    SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `l` THEN
    SRW_TAC [][Cn_def, MAP_GENLIST, combinTheory.o_DEF] THEN
    `LENGTH l < n ∨ n ≤ LENGTH l` by DECIDE_TAC THENL [
       IMP_RES_THEN (Q.SPEC_THEN `c::NTL l` MP_TAC) primrec_short THEN
       `(l = []) ∨ ∃h t. l = h::t` by (Cases_on `l` THEN SRW_TAC [][]) THENL [
          SRW_TAC [][NTL_def] THEN
          `(n = 1) ∨ 1 < n` by DECIDE_TAC THEN
          SRW_TAC [][GENLIST, combinTheory.K_DEF],

          SRW_TAC [][NTL_def,ADD1] THEN
          FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ADD1] THEN
          AP_TERM_TAC THEN
          SRW_TAC [][] THEN
          ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                       [listTheory.LIST_EQ_REWRITE, LENGTH_GENLIST,
                        EL_GENLIST] THEN
          Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
          `i < LENGTH t ∨ LENGTH t ≤ i` by DECIDE_TAC THEN
          ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)[EL_APPEND1, EL_APPEND2, proj_def,
                                              EL_GENLIST]
       ],

       IMP_RES_THEN (Q.SPEC_THEN `c::NTL l` MP_TAC) primrec_arg_too_long THEN
       `LENGTH (NTL l) = LENGTH l - 1`
          by (Cases_on `l` THEN
              FULL_SIMP_TAC (srw_ss() ++ARITH_ss) [NTL_def]) THEN
       ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [TAKE_EQ_GENLIST] THEN
       DISCH_THEN (K ALL_TAC) THEN
       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [NTL_def]
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

val Pr1_def = Define`
  Pr1 n f = Cn (Pr (K n) (Cn f [proj 0; proj 1]))
               [proj 0; K 0]
`;

val Pr1_correct = Store_thm(
  "Pr1_correct",
  ``(Pr1 n f [0] = n) ∧
    (Pr1 n f [SUC m] = f [m; Pr1 n f [m]])``,
  SRW_TAC [][Pr1_def]);

val primrec_Pr1 = Store_thm(
  "primrec_Pr1",
  ``primrec f 2 ⇒ primrec (Pr1 n f) 1``,
  SRW_TAC [][Pr1_def, primrec_rules, alt_Pr_rule]);

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
    THEN1 SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST] THEN
  Induct THEN1
    (SRW_TAC [][Abbr`f`, GENLIST1, Once prtermrec_def]) THEN
  SRW_TAC [][Abbr`f`, LET_THM, ADD_CLAUSES, GENLIST, SNOC_APPEND,
             nlist_of_append, NTL_def]
  THENL [
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM, DIV_LESS] THEN
    SRW_TAC [ARITH_ss][nel_nlist_of, EL_GENLIST, LENGTH_GENLIST],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM] THEN
    SRW_TAC [ARITH_ss][nel_nlist_of, DIV_LESS, LENGTH_GENLIST, EL_GENLIST]
  ]);

val primrec_termrec = Store_thm(
  "primrec_prtermrec",
  ``primrec v 2 ∧ primrec c 5 ∧ primrec a 3 ⇒
    primrec (prtermrec1 v c a) 2``,
  SRW_TAC [][prtermrec1_def] THEN
  HO_MATCH_MP_TAC (i2 `nel`) THEN SRW_TAC [ARITH_ss][prproj] THEN
  SRW_TAC [boolSimps.ETA_ss][] THEN
  MATCH_MP_TAC alt_Pr_rule THEN
  SRW_TAC [][LET_THM] THEN1
    SRW_TAC [][prCn2, i2 `ncons`, prK, prproj] THEN
  HO_MATCH_MP_TAC prCOND THEN SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [
    HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [ARITH_ss][prproj] THEN
    HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [ARITH_ss][prK] THEN
    HO_MATCH_MP_TAC prCn2 THEN SRW_TAC [][] THEN
    SRW_TAC [][prDIV, i2 `$+`, prproj, prK],

    HO_MATCH_MP_TAC prCOND THEN
    SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [
      HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [][prproj] THEN
      HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [][prK] THEN
      HO_MATCH_MP_TAC prCn5 THEN SRW_TAC [][] THEN
      SRW_TAC [][i1 `nfst`, prDIV, prproj, prK, i2 `$+`, i1 `nsnd`] THEN
      HO_MATCH_MP_TAC (i2 `nel`) THEN
      SRW_TAC [][i1 `nfst`, prDIV, prproj, prK, i2 `$+`, i1 `nsnd`],

      HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [][prproj] THEN
      HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [][prK] THEN
      HO_MATCH_MP_TAC prCn3 THEN
      SRW_TAC [][i2 `nel`, i2 `$+`, prDIV, prproj, prK],

      SRW_TAC [][pr_eq, prK, prMOD, prproj, i2 `$+`]
    ],

    SRW_TAC [][pr_eq, prK, prMOD, prproj, i2 `$+`]
  ]);

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
  SRW_TAC [][pr_is_abs_def, prMOD, prproj, prK, pr_eq]);

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
  HO_MATCH_MP_TAC primrec_prtermrec0 THEN SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][LET_THM] THEN
  HO_MATCH_MP_TAC (i2 `$*`) THEN
  SRW_TAC [][prproj, i2 `$*`, prK] THEN
  HO_MATCH_MP_TAC (i2 `$-`) THEN
  SRW_TAC [][prCn1, prK, primrec_is_abs, prproj]);


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
  HO_MATCH_MP_TAC primrec_pr2 THEN
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

(* val pr_lift_def = Define`
  pr_lift =
  (λns. let t = ns ' 0 in
        let k = ns ' 1 in
        let mx = maxf (max_abs o numdB) t + k + 1
        in
          nel (t * mx + k)
          (Pr1
             (ncons 3 nnil)
             (λl. let n = l ' 0 + 1 in
                  let t = n DIV mx in
                  let k = n MOD mx in
                  let r = l ' 1
                  in
                    if t MOD 3 = 0 then
                      if ¬(k <= t DIV 3) then napp r (ncons t nnil)
                      else napp r (ncons (t + 3) nnil)
                    else if t MOD 3 = 1 then
                      let t1 = nfst (t DIV 3) in
                      let t2 = nsnd (t DIV 3) in
                      let t1k = t1 * mx + k in
                      let t2k = t2 * mx + k
                      in
                        napp r (ncons (3 * (npair (nel t1k r) (nel t2k r)) + 1)
                                      nnil)
                    else
                      let t0 = t DIV 3 in
                      let t0k = t0 * mx + k + 1
                      in
                        napp r (ncons (3 * nel t0k r + 2) nnil))
             [t * mx + k]))
`;

val pr_lift_correct = Store_thm(
  "pr_lift_correct",
  ``pr_lift [tn; k] = dBnum (lift (numdB tn) k)``,
  SRW_TAC [][pr_lift_def] THEN
  Q.MATCH_ABBREV_TAC `
    nel (tn * mx + k) (f [tn * mx + k]) = dBnum (lift (numdB tn) k)
  ` THEN
  `0 < mx ∧ k < mx` by SRW_TAC [ARITH_ss][Abbr`mx`] THEN
  `∀n. n ≤ tn ⇒ max_abs (numdB (n DIV mx)) + n MOD mx < mx`
     by (completeInduct_on `n` THEN
         `(n = 0) ∨ ∃m. n = SUC m` by (Cases_on `n` THEN SRW_TAC [][]) THEN1
           SRW_TAC [][Once numdB_def, ZERO_DIV] THEN
         STRIP_TAC THEN
         `∃d. n DIV mx = dBnum d` by METIS_TAC [dBnum_onto] THEN
         Cases_on `d` THENL [
           SRW_TAC [][],
           SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [ADD1] THEN



  Q_TAC SUFF_TAC `
    ∀n. (f [n] = nlist_of
                   (GENLIST (λi. dBnum (lift (numdB (i DIV mx)) (i MOD mx)))
                            (n + 1))) ∧
        (n ≤ tn ⇒ max_abs (numdB (n DIV mx)) + n MOD mx < mx)
  ` THEN1 SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST,
                     ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, MOD_TIMES] THEN
  `

  completeInduct_on `n` THEN
  `(n = 0) ∨ ∃m. n = SUC m` by (Cases_on `n` THEN SRW_TAC [][]) THEN1
    (CONJ_TAC THEN
     SRW_TAC [][ZERO_DIV, Once numdB_def, dBnum_def, Abbr`f`, GENLIST1]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SRW_TAC [][Abbr`f`, GENLIST, ADD_CLAUSES, SNOC_APPEND, LET_THM,
             nlist_of_append, NOT_LESS_EQUAL] THEN
  FIRST_X_ASSUM (fn th => th |> Q.SPEC `mm` |> UNDISCH |> CONJUNCT2
                             |> DISCH ``mm < SUC m`` |> Q.GEN `mm`
                             |> ASSUME_TAC) THEN
  Q.ABBREV_TAC `t = (m + 1) DIV mx` THEN
  Q.ABBREV_TAC `kk = (m + 1) MOD mx` THENL [
    SRW_TAC [][Once numdB_def, dBnum_def] THEN
    Q.SPEC_THEN `3` MP_TAC DIVISION THEN SIMP_TAC (srw_ss()) [] THEN
    DISCH_THEN (Q.SPEC_THEN `t` MP_TAC) THEN SRW_TAC [][Once MULT_COMM],

    SRW_TAC [][Once numdB_def, dBnum_def] THEN
    `t = 3 * (t DIV 3) + t MOD 3`
       by METIS_TAC [DECIDE ``0 < 3``, DIVISION, MULT_COMM] THEN
    POP_ASSUM (MP_TAC o SYM) THEN SRW_TAC [][LEFT_ADD_DISTRIB],

    `kk < mx ∧ (kk MOD mx = kk)` by SRW_TAC [][Abbr`kk`] THEN
    SRW_TAC [][Once numdB_def, dBnum_def, SimpRHS] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Q_TAC SUFF_TAC `nfst (t DIV 3) * mx + kk < m + 1 ∧
                    nsnd (t DIV 3) * mx + kk < m + 1`
    THEN1 SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST,
                     ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, MOD_TIMES] THEN
    `m + 1 = t * mx + kk`
       by (MAP_EVERY Q.UNABBREV_TAC [`t`, `kk`] THEN
           METIS_TAC [DIVISION]) THEN
    `0 < t` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][],

    FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
    `0 < t` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][Once numdB_def, dBnum_def, SimpRHS] THEN
    Q_TAC SUFF_TAC `t DIV 3 * mx + kk + 1 < m + 1` THEN1
      (SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST] THEN
       SIMP_TAC (srw_ss())[GSYM ADD_ASSOC] THEN
       SRW_TAC [][ADD_DIV_ADD_DIV, MOD_TIMES]
       by (MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC `t` THEN
           SRW_TAC [][DIV_LESS] THEN
           SRW_TAC [][Abbr`t`, DIV_LESS_EQ]) THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `t DIV 3` MP_TAC) THEN
    `kk + 1 < mx ∧ (kk MOD mx = kk)` by SRW_TAC [][Abbr`kk`] THEN
    Q_TAC SUFF_TAC `t DIV 3 * mx + kk + 1 < m + 1` THEN1
      (SRW_TAC [ARITH_ss][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST]






val primrec_pr_lift = Store_thm(
  "primrec_pr_lift",
  ``primrec pr_lift 2``,
  SRW_TAC [][LET_THM, pr_lift_def] THEN
  HO_MATCH_MP_TAC (i2 `nel`) THEN SRW_TAC



*)

val _ = export_theory()
