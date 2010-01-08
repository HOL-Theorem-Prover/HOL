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


val prtermrec0_def = Define`
  prtermrec0 v c a =
   (λl. nel (l ' 0)
            (Pr (λl. ncons (v (0::l)) nnil)
              (λl.
                 let n = l ' 0 + 1 in
                 let r = l ' 1 in
                 let m = n MOD 3 in
                 let t = NTL (NTL l)
                 in
                   if m = 0 then napp r (ncons (v (n DIV 3::t)) nnil)
                   else if m = 1 then
                     let t1 = nfst (n DIV 3) in
                     let t2 = nsnd (n DIV 3) in
                     let r1 = nel t1 r in
                     let r2 = nel t2 r
                     in
                       napp r (ncons (c (t1::t2::r1::r2::t)) nnil)
                   else
                     let t0 = n DIV 3 in
                     let r0 = nel t0 r
                     in
                       napp r (ncons (a (t0::r0::t)) nnil))
              l))`

val prtermrec0_correct = store_thm(
  "prtermrec0_correct",
  ``prtermrec0 v c a (n::t) = prtermrec v c a (n::t)``,
  SRW_TAC [][prtermrec0_def] THEN
  Q.MATCH_ABBREV_TAC `nel n (f (n::t)) = prtermrec v c a (n::t)` THEN
  Q_TAC SUFF_TAC
    `∀n t. f (n::t) = nlist_of (GENLIST (λp. prtermrec v c a (p::t))
                                        (n + 1))`
    THEN1 SRW_TAC [][nel_nlist_of, LENGTH_GENLIST, EL_GENLIST] THEN
  Induct THEN1
    (SRW_TAC [][Abbr`f`, GENLIST1, Once prtermrec_def]) THEN
  SRW_TAC [][Abbr`f`, LET_THM, ADD_CLAUSES, GENLIST, SNOC_APPEND,
             nlist_of_append, NTL_def]
  THENL [
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM] THEN
    `nfst ((n + 1) DIV 3) < n + 1 ∧
     nsnd ((n + 1) DIV 3) < n + 1`
       by (CONJ_TAC THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
           Q.EXISTS_TAC `(n + 1) DIV 3` THEN
           SRW_TAC [ARITH_ss][DIV_LESS, nsnd_le, nfst_le]) THEN
    SRW_TAC [][nel_nlist_of, EL_GENLIST, LENGTH_GENLIST],
    SRW_TAC [ARITH_ss][Once prtermrec_def, SimpRHS, LET_THM] THEN
    SRW_TAC [ARITH_ss][nel_nlist_of, DIV_LESS, LENGTH_GENLIST, EL_GENLIST]
  ]);

(* val primrec_termrec = Store_thm(
  "primrec_prtermrec",
  ``primrec v n ∧ primrec c (n + 4) ∧ primrec a (n + 2) ⇒
    primrec (prtermrec0 v c a) (n + 1)``,
  SRW_TAC [][] THEN
  `0 < n` by METIS_TAC [primrec_nzero] THEN
  SRW_TAC [][prtermrec0_def] THEN
  HO_MATCH_MP_TAC (i2 `nel`) THEN SRW_TAC [ARITH_ss][prproj] THEN
  SRW_TAC [boolSimps.ETA_ss][] THEN
  MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [ARITH_ss][] THEN1
    (HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [][prK, primrec_cons]) THEN
  SRW_TAC [][LET_THM] THEN
  HO_MATCH_MP_TAC prCOND THEN SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [
    HO_MATCH_MP_TAC (i2 `napp`) THEN SRW_TAC [ARITH_ss][prproj] THEN
    HO_MATCH_MP_TAC (i2 `ncons`) THEN SRW_TAC [ARITH_ss][prK] THEN
    HO_MATCH_MP_TAC fcons_ntl2 THEN
    SRW_TAC [ARITH_ss][prDIV, prproj, i2 `$+`, prK],

    HO_MATCH_MP_TAC prCOND THEN
    SRW_TAC [][prpred, combinTheory.o_ABS_R] THENL [



    SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN prtermrec_def



*)



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
