open HolKernel Parse boolLib bossLib

open numpairTheory
open arithmeticTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]
fun Save_thm (tup as (n,th)) = save_thm tup before export_rewrites [n]

val _ = new_theory "primrecfns"

val nB_def = Define`(nB T = 1) ∧ (nB F = 0)`
val _ = export_rewrites ["nB_def"]

val nB_11 = Store_thm(
  "nB_11",
  ``(nB b1 = nB b2) <=> (b1 <=> b2)``,
  Cases_on `b1` THEN Cases_on `b2` THEN SRW_TAC [][]);

val mult_nB = Store_thm(
  "mult_nB",
  ``nB p * nB q = nB (p ∧ q)``,
  Cases_on `p` THEN SRW_TAC [][]);

val nB_eq0 = Store_thm(
  "nB_eq0",
  ``(nB p = 0) ⇔ ¬p``,
  Cases_on `p` THEN SRW_TAC [][])

val nB_eq1 = Store_thm(
  "nB_eq1",
  ``(nB p = 1) ⇔ p``,
  Cases_on `p` THEN SRW_TAC [][]);

val nB_sub1 = Store_thm(
  "nB_sub1",
  ``1 - nB p = nB (¬p)``,
  Cases_on `p` THEN SRW_TAC [][]);

val proj_def = Define`
  proj n l = if LENGTH l <= n then 0 else EL n l
`;

val proj_thm = Store_thm(
  "proj_thm",
  ``(proj n [] = 0) ∧
    (proj n (h::t) = if n = 0 then h else proj (n - 1) t)``,
  SRW_TAC [ARITH_ss][proj_def] THEN
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []);

val succ_def = Define`(succ [] = 1) ∧ (succ (h::t) = SUC h)`
val _ = export_rewrites ["succ_def"]

val Cn_def = Define`
  Cn (f:num list -> num) (gs:(num list -> num) list) (l:num list) =
  f (MAP (λg. g l) gs)
`

val Cn0123 = Store_thm(
  "Cn0123",
  ``(Cn f [g] l = f [g l]) ∧
    (Cn f [g1; g2] l = f [g1 l; g2 l]) ∧
    (Cn f [g1; g2; g3] l = f [g1 l; g2 l; g3 l])``,
  SRW_TAC [][Cn_def]);

val Pr_def = Define `
  Pr b r l = case l of
                [] -> b []
             || (0::t) -> b t
             || (SUC n :: t) -> r (n :: Pr b r (n :: t) :: t)`

val Pr_thm = Store_thm(
  "Pr_thm",
  ``(Pr b r (0 :: t) = b t) ∧
    (Pr b r (SUC m :: t) = r (m :: Pr b r (m :: t) :: t)) ∧
    (Pr b r ((m + 1) :: t) = r (m :: Pr b r (m :: t) :: t)) ∧
    (Pr b r ((1 + m) :: t) = r (m :: Pr b r (m :: t) :: t))``,
  REPEAT CONJ_TAC THEN
  SIMP_TAC bool_ss [Once Pr_def, SimpLHS, ONE, ADD_CLAUSES] THEN
  SRW_TAC [][]);

val _ = overload_on ("zerof", ``K 0 : num list -> num``)

val (primrec_rules, primrec_ind, primrec_cases) = Hol_reln`
  primrec zerof 1 ∧
  primrec succ 1 ∧
  (∀i n. i < n ⇒ primrec (proj i) n) ∧
  (∀f gs m. primrec f (LENGTH gs) ∧ EVERY (λg. primrec g m) gs ⇒
            primrec (Cn f gs) m) ∧
  (∀b r n. primrec b n ∧ primrec r (n + 2) ⇒ primrec (Pr b r) (n + 1))
`;
val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)

val strong_primrec_ind = save_thm(
  "strong_primrec_ind",
  IndDefLib.derive_strong_induction(primrec_rules, primrec_ind))


val primrec_nzero = store_thm(
  "primrec_nzero",
  ``∀f k. primrec f k ⇒ 0 < k``,
  HO_MATCH_MP_TAC primrec_ind THEN SRW_TAC [ARITH_ss][] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val EL_TAKE = store_thm(
  "EL_TAKE",
  ``∀i n l. i < n ∧ n ≤ LENGTH l ⇒ (EL i l = EL i (TAKE n l))``,
  Induct THEN Cases_on `l` THEN SRW_TAC [ARITH_ss][]);

val MAP_EQ = store_thm(
  "MAP_EQ",
  ``∀f g l. (MAP f l = MAP g l) ⇔ ∀e. MEM e l ⇒ (f e = g e)``,
  Induct_on `l` THEN SRW_TAC [][] THEN METIS_TAC []);

val TAKE_ID = prove(
  ``∀l n. (LENGTH l = n) ⇒ (TAKE n l = l)``,
  Induct THEN SRW_TAC [ARITH_ss][]);

val primrec_arg_too_long = store_thm(
  "primrec_arg_too_long",
  ``∀f n. primrec f n ⇒
          ∀l. n ≤ LENGTH l ⇒ (f l = f (TAKE n l))``,
  HO_MATCH_MP_TAC primrec_ind THEN SRW_TAC [][] THENL [
    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [ARITH_ss][proj_def, EL_TAKE],
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    SRW_TAC [][Cn_def, TAKE_ID] THEN AP_TERM_TAC THEN
    SRW_TAC [][MAP_EQ] THEN
    FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM],

    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    `∃h t. l = h::t`
        by (Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
    Induct_on `h` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `h::Pr f f' (h::TAKE n t)::t`
                               MP_TAC) THEN
    ASM_SIMP_TAC bool_ss [TWO, ONE, listTheory.TAKE_def,
                          listTheory.LENGTH, ADD_CLAUSES] THEN
    SRW_TAC [][]
  ]);

open rich_listTheory

val GENLIST1 = prove(``GENLIST f 1 = [f 0]``,
                     SIMP_TAC bool_ss [ONE, GENLIST, SNOC]);
val GENLIST_CONS = prove(
  ``GENLIST f (SUC n) = f 0 :: (GENLIST (f o SUC) n)``,
  Induct_on `n` THEN SRW_TAC [][GENLIST, SNOC]);

val primrec_nil = store_thm(
  "primrec_nil",
  ``∀f n. primrec f n ⇒ (f [] = f (GENLIST (K 0) n))``,
  HO_MATCH_MP_TAC primrec_ind THEN SIMP_TAC (srw_ss()) [GENLIST1] THEN
  REPEAT CONJ_TAC THENL [
    SIMP_TAC bool_ss [Once EQ_SYM_EQ] THEN
    Induct_on `n` THEN SRW_TAC [][GENLIST_CONS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN DECIDE_TAC,

    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SRW_TAC [][Cn_def] THEN
    AP_TERM_TAC THEN Q.PAT_ASSUM `f X = f []` (K ALL_TAC) THEN
    Induct_on `gs` THEN SRW_TAC [][],

    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SRW_TAC [][] THEN
    SRW_TAC [][Once Pr_def, SimpRHS] THEN
    Cases_on `n` THEN SRW_TAC [][GENLIST1, ADD_CLAUSES, GENLIST_CONS] THEN
    SRW_TAC [][GSYM ADD1]
  ]);

val primrec_short = store_thm(
  "primrec_short",
  ``∀f n. primrec f n ⇒
          ∀l. LENGTH l < n ⇒ (f l = f (l ++ GENLIST (K 0) (n - LENGTH l)))``,
  HO_MATCH_MP_TAC strong_primrec_ind THEN SIMP_TAC (srw_ss()) [GENLIST1] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][] THEN
    `LENGTH l = 0` by DECIDE_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL, GENLIST1],

    SRW_TAC [][proj_def] THEN
    SRW_TAC [ARITH_ss][EL_GENLIST, EL_APPEND1, EL_APPEND2],

    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SRW_TAC [][Cn_def] THEN
    AP_TERM_TAC THEN
    Q.PAT_ASSUM `∀l. LENGTH l < N ⇒ (f X = f Y)` (K ALL_TAC) THEN
    Q.PAT_ASSUM `primrec f N` (K ALL_TAC) THEN
    Induct_on `gs` THEN SRW_TAC [][],

    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SRW_TAC [ARITH_ss][] THEN
    `(l = []) ∨ ∃m ms. l = m :: ms` by (Cases_on `l` THEN SRW_TAC [][]) THEN1
      (SRW_TAC [][] THEN METIS_TAC [primrec_nil, primrec_rules]) THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [DECIDE ``SUC x < y + 1 <=> x < y``] THEN
    SRW_TAC [ARITH_ss][ADD1] THEN
    Induct_on `m` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `m::Pr f f' (m::ms)::ms` MP_TAC) THEN
    SRW_TAC [ARITH_ss][ADD1]
  ]);

val alt_Pr_rule = Store_thm(
  "alt_Pr_rule",
  ``∀b r m. primrec b (m - 1) ∧ primrec r (m + 1) ⇒ primrec (Pr b r) m``,
  SRW_TAC [][] THEN
  Cases_on `m` THEN1 (IMP_RES_TAC primrec_nzero THEN
                      FULL_SIMP_TAC (srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ADD1, primrec_rules]);

val primrec_K = Store_thm(
  "primrec_K",
  ``∀n m. 0 < m ⇒ primrec (K n) m``,
  Induct THEN SRW_TAC [][primrec_rules] THENL [
    Q_TAC SUFF_TAC `zerof = Cn zerof [proj 0]` THEN1
      (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][primrec_rules]) THEN
    SRW_TAC [][FUN_EQ_THM],
    Q_TAC SUFF_TAC `K (SUC n) = Cn succ [K n]`
      THEN1 SRW_TAC [][primrec_rules] THEN
    SRW_TAC [][FUN_EQ_THM]
  ]);

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

val pr1_def = Define`
  (pr1 f [] = f 0: num) ∧
  (pr1 f (x::t) = f x)
`;
val _ = export_rewrites ["pr1_def"]

val unary_primrec_eq = store_thm(
  "unary_primrec_eq",
  ``primrec f 1 ∧ (∀n. f [n] = g n) ⇒ (f = pr1 g)``,
  SRW_TAC [][] THEN SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `l` THEN
  `(l = []) ∨ ∃n ns. l = n :: ns` by (Cases_on `l` THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THENL [
    IMP_RES_THEN MP_TAC primrec_nil THEN SRW_TAC [][GENLIST1],
    IMP_RES_THEN (Q.SPEC_THEN `n::ns` MP_TAC) primrec_arg_too_long THEN
    SRW_TAC [ARITH_ss][]
  ]);
val primrec_pr1 = store_thm(
  "primrec_pr1",
  ``(∃g. primrec g 1 ∧ (∀n. g [n] = f n)) ⇒ primrec (pr1 f) 1``,
  METIS_TAC [unary_primrec_eq]);

val pr2_def = Define`
  (pr2 f [] = f 0 0 : num) ∧
  (pr2 f [x] = f x 0) ∧
  (pr2 f (x::y::t) = f x y)
`;
val _ = export_rewrites ["pr2_def"]

val GENLIST2 = prove(
  ``GENLIST f 2 = [f 0; f 1]``,
  SIMP_TAC bool_ss [TWO, ONE, GENLIST, SNOC]);
val binary_primrec_eq = store_thm(
  "binary_primrec_eq",
  ``primrec f 2 ∧ (∀n m. f [n; m] = g n m) ⇒ (f = pr2 g)``,
  SRW_TAC [][] THEN SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `l` THEN
  `(l = []) ∨ ∃n ns. l = n :: ns` by (Cases_on `l` THEN SRW_TAC [][]) THENL [
    SRW_TAC [][] THEN
    `f [] = f (GENLIST (K 0) 2)` by METIS_TAC [primrec_nil] THEN
    SRW_TAC [][GENLIST2],

    `(ns = []) ∨ ∃m ms. ns = m::ms` by (Cases_on `ns` THEN SRW_TAC [][]) THEN
    SRW_TAC [][] THENL [
      IMP_RES_THEN (Q.SPEC_THEN `[n]` MP_TAC) primrec_short THEN
      SRW_TAC [][GENLIST1],

      IMP_RES_THEN (Q.SPEC_THEN `n::m::ms` MP_TAC) primrec_arg_too_long THEN
      SRW_TAC [ARITH_ss][]
    ]
  ])

val primrec_pr2 = store_thm(
  "primrec_pr2",
  ``(∃g. primrec g 2 ∧ (∀m n. g [m; n] = f m n)) ⇒ primrec (pr2 f) 2``,
  METIS_TAC [binary_primrec_eq]);

val primrec_pr_add = Store_thm(
  "primrec_pr_add",
  ``primrec (pr2 (+)) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Pr (proj 0) (Cn succ [proj 1])` THEN
  SRW_TAC [][primrec_rules, alt_Pr_rule] THEN
  Induct_on `m` THEN SRW_TAC [][ADD_CLAUSES]);
val _ = temp_set_fixity "+." (Infixl 500)
val _ = temp_overload_on ("+.", ``λn m. Cn (pr2 (+)) [n; m]``)

val primrec_pr_mult = Store_thm(
  "primrec_pr_mult",
  ``primrec (pr2 $*) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Pr zerof (proj 1 +. proj 2)` THEN
  SRW_TAC [][primrec_rules, alt_Pr_rule] THEN
  Induct_on `m` THEN SRW_TAC [][MULT_CLAUSES]);
val _ = temp_set_fixity "*." (Infixl 600)
val _ = temp_overload_on ("*.", ``λn m. Cn (pr2 $*) [n; m]``)

val primrec_pr_pred = Store_thm(
  "primrec_pr_pred",
  ``primrec (pr1 PRE) 1``,
  MATCH_MP_TAC primrec_pr1 THEN Q.EXISTS_TAC `Pr1 0 (proj 0)` THEN
  SRW_TAC [][primrec_rules] THEN
  Cases_on `n` THEN SRW_TAC [][]);

val _ = overload_on ("pr_iszero", ``pr1 (λn. nB (n = 0))``)

val primrec_pr_iszero = Store_thm(
  "primrec_pr_iszero",
  ``primrec pr_iszero 1``,
  MATCH_MP_TAC primrec_pr1 THEN Q.EXISTS_TAC `Pr1 1 (K 0)` THEN
  SRW_TAC [][primrec_rules] THEN
  Cases_on `n` THEN SRW_TAC [][]);

val cflip_def = Define`
  cflip f = Cn f [proj 1; proj 0]
`;

val cflip_thm = Store_thm(
  "cflip_thm",
  ``cflip f [n; m] = f [m; n]``,
  SRW_TAC [][cflip_def]);
val primrec_cflip = Store_thm(
  "primrec_cflip",
  ``primrec f 2 ⇒ primrec (cflip f) 2``,
  SRW_TAC [][primrec_rules, cflip_def]);

val primrec_pr_sub = Store_thm(
  "primrec_pr_sub",
  ``primrec (pr2 $-) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `cflip (Pr (proj 0) (Cn (pr1 PRE) [proj 1]))` THEN
  SRW_TAC [][primrec_rules] THEN Induct_on `n` THEN SRW_TAC [ARITH_ss][])
val _ = temp_set_fixity "-." (Infixl 500);
val _ = temp_overload_on ("-.", ``λn m. Cn (pr2 $-) [n; m]``)

val _ = overload_on ("pr_le", ``pr2 (λx y. nB (x ≤ y))``)
val _ = temp_set_fixity "<=." (Infix(NONASSOC, 450))
val _ = temp_overload_on ("<=.", ``λn m. Cn pr_le [n; m]``)

val primrec_pr_le = Store_thm(
  "primrec_pr_le",
  ``primrec pr_le 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Cn pr_iszero [pr2 $-]` THEN
  SRW_TAC [][primrec_rules]);

val pr_eq_def = Define`
  pr_eq = Cn (pr2 $*) [pr_le; cflip pr_le]
`;

val pr_eq_thm = Store_thm(
  "pr_eq_thm",
  ``pr_eq [n;  m] = nB (n = m)``,
  SRW_TAC [ARITH_ss][pr_eq_def]);

val primrec_pr_eq = Store_thm(
  "primrec_pr_eq",
  ``primrec pr_eq 2``,
  SRW_TAC [][pr_eq_def, primrec_rules]);

val _ = temp_set_fixity "=." (Infix(NONASSOC, 450))
val _ = temp_overload_on ("=.", ``λn m. Cn pr_eq [n; m]``)

val pr_cond_def = Define`
  pr_cond P f g =
    Cn (proj 0 *. proj 1 +. (K 1 -. proj 0) *. proj 2) [P;f;g]
`;

val pr_predicate_def = Define`
  pr_predicate P = ∀n. (P n = 0) ∨ (P n = 1)
`;

val Cn_pr_eq_predicate = Store_thm(
  "Cn_pr_eq_predicate",
  ``pr_predicate (Cn pr_eq [f; g])``,
  SRW_TAC [][pr_predicate_def, pr_eq_thm]);

val Cn_pr_le_predicate = Store_thm(
  "Cn_pr_le_predicate",
  ``pr_predicate (Cn pr_le [f;g])``,
  SRW_TAC [][pr_predicate_def]);

val pr_cond_thm = Store_thm(
  "pr_cond_thm",
  ``pr_predicate P ⇒
    (pr_cond P f g n = if P n = 1 then f n else g n)``,
  SRW_TAC [][pr_cond_def, pr_predicate_def] THEN
  `P n = 0` by METIS_TAC [] THEN
  SRW_TAC [][]);

val primrec_pr_cond = Store_thm(
  "primrec_pr_cond",
  ``primrec P n ∧ primrec f n ∧ primrec g n ⇒ primrec (pr_cond P f g) n``,
  SRW_TAC [][pr_cond_def] THEN
  MATCH_MP_TAC primrec_cn THEN SRW_TAC [][] THEN
  MATCH_MP_TAC primrec_cn THEN SRW_TAC [][] THEN
  MATCH_MP_TAC primrec_cn THEN SRW_TAC [][] THEN
  SRW_TAC [][primrec_rules]);

(* 0 div m = 0 /\
   (n + 1) div m = let r = n div m
                   in
                       if n + 1 - r * m = m then r + 1 else r

  In recursive case, h is called with (n, r, m)

*)
val pr_div_def = Define`
  pr_div =
  Pr (K 0)
     (pr_cond (proj 0 +. K 1 -. (proj 1 *. proj 2) =. proj 2)
              (Cn succ [proj 1])
              (proj 1))
`;

val primrec_pr_div = Store_thm(
  "primrec_pr_div",
  ``primrec pr_div 2``,
  SRW_TAC [][pr_div_def] THEN
  MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][] THEN
  MATCH_MP_TAC primrec_pr_cond THEN SRW_TAC [][primrec_rules]);

val pr_div_recursion = store_thm(
  "pr_div_recursion",
  ``(pr_div [0; m] = 0) ∧
    (pr_div [n + 1; m] = let r = pr_div [n; m]
                         in
                           if n + 1 - r * m = m then r + 1 else r)``,
  SIMP_TAC (srw_ss()) [pr_div_def, LET_THM, ADD1]);

val pr_div_thm = Store_thm(
  "pr_div_thm",
  ``0 < m ⇒ (pr_div [n; m] = n DIV m)``,
  STRIP_TAC THEN Induct_on `n` THEN1
    SRW_TAC [][pr_div_recursion, ZERO_DIV] THEN
  SRW_TAC [][pr_div_recursion, ADD1, LET_THM] THENL [
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC DIV_UNIQUE THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][RIGHT_ADD_DISTRIB],

    Q.SPEC_THEN `m` (IMP_RES_THEN MP_TAC) DIVISION THEN
    NTAC 2 (DISCH_THEN (Q.SPEC_THEN `n` ASSUME_TAC)) THEN
    Q.ABBREV_TAC `q = n DIV m` THEN
    Q.ABBREV_TAC `r = n MOD m` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q.PAT_ASSUM `pr_div X = Y` (K ALL_TAC) THEN
    SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC DIV_UNIQUE THEN
    Q.EXISTS_TAC `r + 1` THEN DECIDE_TAC
  ]);

val pr_mod_def = Define`pr_mod = proj 0 -. (pr_div *. proj 1)`

val pr_mod_eqn = store_thm(
  "pr_mod_eqn",
  ``pr_mod [n; m] = n - pr_div [n; m] * m``,
  SRW_TAC [][pr_mod_def]);

val pr_mod_thm = Store_thm(
  "pr_mod_thm",
  ``0 < m ⇒ (pr_mod [n; m] = n MOD m)``,
  SRW_TAC [][pr_mod_eqn] THEN
  Q.SPEC_THEN `m` (IMP_RES_THEN MP_TAC) DIVISION THEN
  NTAC 2 (DISCH_THEN (Q.SPEC_THEN `n` ASSUME_TAC)) THEN
  DECIDE_TAC);

val primrec_pr_mod = Store_thm(
  "primrec_pr_mod",
  ``primrec pr_mod 2``,
  SRW_TAC [][pr_mod_def, primrec_rules]);

(* ----------------------------------------------------------------------
    number pairing
   ---------------------------------------------------------------------- *)

(* triangular number calculation *)
val _ = temp_overload_on ("tri.", ``λn. Cn (pr1 tri) [n]``);

val primrec_tri = Store_thm(
  "primrec_tri",
  ``primrec (pr1 tri) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `Pr1 0 (proj 0 +. K 1 +. proj 1)` THEN
  SRW_TAC [][primrec_rules] THEN
  Induct_on `n` THEN SRW_TAC [][tri_def, ADD1]);

(* inverse triangular - start at the input value n, and try successively smaller
   values until an m <= n comes up such that tri (m) <= the original n *)
val _ = temp_overload_on ("invtri.", ``λn. Cn (pr1 tri⁻¹) [n]``)

val Pr_eval = prove(
  ``0 < m ==> (Pr b r (m :: t) = r (m - 1 :: Pr b r (m - 1 :: t) :: t))``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [Once Pr_def, SimpLHS] THEN
  Cases_on `m` THEN SRW_TAC [ARITH_ss][]);

val tri_eval = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV tri_def

val tri_bounds_lemma = prove(
  ``∀n. n + 3 ≤ tri (n + 2)``,
  Induct THEN SRW_TAC [ARITH_ss][ADD_CLAUSES, tri_eval, tri_def]);

val primrec_invtri = Store_thm(
  "primrec_invtri",
  ``primrec (pr1 tri⁻¹) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `
    Cn (Pr zerof (pr_cond (tri. (proj 0 +. K 1) <=. proj 2)
                          (proj 0 +. K 1)
                          (proj 1)))
       [proj 0; proj 0]
  ` THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [][primrec_rules] THEN
    MATCH_MP_TAC alt_Pr_rule THEN
    SRW_TAC [][primrec_rules] THEN
    MATCH_MP_TAC primrec_pr_cond THEN
    SRW_TAC [][primrec_rules],

    Q.X_GEN_TAC `n` THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    MATCH_MP_TAC invtri_unique THEN SRW_TAC [][] THENL [
      Q.MATCH_ABBREV_TAC `tri (Pr zerof recn [n;n]) ≤ n` THEN
      Q_TAC SUFF_TAC `∀n m. tri (Pr zerof recn [n;m]) ≤ m`
        THEN1 METIS_TAC [] THEN
      Induct THEN SRW_TAC [][tri_def] THEN
      markerLib.UNABBREV_ALL_TAC THEN
      SRW_TAC [][pr_cond_thm],

      Q.MATCH_ABBREV_TAC `n < tri (Pr zerof recn [n;n] + 1)` THEN
      Q_TAC SUFF_TAC
        `∀n m. (∀p. n < p /\ p ≤ m ⇒ m < tri p) ⇒
               m < tri (Pr zerof recn [n;m] + 1)`
        THEN1 (DISCH_THEN (Q.SPECL_THEN [`n`,`n`] STRIP_ASSUME_TAC) THEN
               FIRST_X_ASSUM MATCH_MP_TAC THEN DECIDE_TAC) THEN
      Induct THEN SRW_TAC [][] THENL [
        Cases_on `m = 0` THEN1
          (ASM_SIMP_TAC bool_ss [ONE, tri_def] THEN DECIDE_TAC) THEN
        `1 ≤ m ∧ 0 < 1` by DECIDE_TAC THEN METIS_TAC [],

        SRW_TAC [][] THEN markerLib.UNABBREV_ALL_TAC THEN
        SRW_TAC [][] THENL [
          Cases_on `n = 0` THENL [
            SRW_TAC [][tri_def] THEN
            Cases_on `m = 1` THEN1 SRW_TAC [][tri_eval] THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [tri_eval],

            FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [ARITH_ss][] THEN
            MATCH_MP_TAC LESS_EQ_TRANS THEN
            Q.EXISTS_TAC `tri (n + 1)` THEN
            SRW_TAC [][] THEN
            Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
            SRW_TAC [ARITH_ss][ADD_CLAUSES, ADD1, tri_bounds_lemma]
          ],

          Q.PAT_ASSUM `∀m. (∀p:num. P p) ⇒ Q m` MATCH_MP_TAC THEN
          SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQUAL] THEN
          Cases_on `p = n + 1` THEN1 SRW_TAC [][] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN DECIDE_TAC
        ]
      ]
    ]
  ]);

(* --- npair *)
val primrec_npair = Store_thm(
  "primrec_npair",
  ``primrec (pr2 npair) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `tri. (proj 0 +. proj 1) +. proj 1` THEN
  SRW_TAC [][primrec_rules, npair_def]);

(* --- nfst *)
val primrec_nfst = Store_thm(
  "primrec_nfst",
  ``primrec (pr1 nfst) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `tri. (invtri. (proj 0)) +. invtri. (proj 0) -. proj 0` THEN
  SRW_TAC [][primrec_rules, nfst_def] THEN
  MATCH_MP_TAC primrec_cn THEN SRW_TAC [][primrec_rules]);

(* --- nsnd *)
val primrec_nsnd = Store_thm(
  "primrec_nsnd",
  ``primrec (pr1 nsnd) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `proj 0 -. tri. (invtri. (proj 0))` THEN
  SRW_TAC [][primrec_rules, nsnd_def]);

(* ----------------------------------------------------------------------
    Proof that Ackermann function is not primitive recursive.

    Taken from
      http://home.manhattan.edu/~gregory.taylor/thcomp/pdf-files/ackerman.pdf
   ---------------------------------------------------------------------- *)

val Ackermann_def = Define`
  (Ackermann 0 m = m + 1) ∧
  (Ackermann (SUC n) 0 = Ackermann n 1) ∧
  (Ackermann (SUC n) (SUC m) = Ackermann n (Ackermann (SUC n) m))
`;
val H_ind = theorem "Ackermann_ind"
val H_thm = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV Ackermann_def

val _ = temp_overload_on ("H", ``Ackermann``);
val Alemma1 = prove(
  ``(H 1 n = n + 2) ∧ (H 2 n = 2 * n + 3)``,
  `∀n. H 1 n = n + 2`
    by (Induct_on `n` THEN SRW_TAC [][H_thm] THEN
        ONCE_REWRITE_TAC [ONE] THEN
        SRW_TAC [][Ackermann_def] THEN DECIDE_TAC) THEN
  SRW_TAC [][] THEN
  Induct_on `n` THEN SRW_TAC [][H_thm] THEN
  SIMP_TAC bool_ss [SimpLHS, TWO] THEN
  SRW_TAC [][Ackermann_def] THEN DECIDE_TAC);

val Alemma2 = prove(
  ``∀n m. m + 1 ≤ H n m``,
  HO_MATCH_MP_TAC H_ind THEN SRW_TAC [ARITH_ss][Ackermann_def]);

val Alemma2b = prove(
  ``∀n m p. p ≤ m + 2 ∧ 0 < n ⇒ p ≤ H n m``,
  HO_MATCH_MP_TAC H_ind THEN SRW_TAC [ARITH_ss][Ackermann_def] THENL [
    Cases_on `n = 0` THEN1 SRW_TAC [][Ackermann_def] THEN
    SRW_TAC [ARITH_ss][],
    Cases_on `n = 0` THEN1 SRW_TAC [ARITH_ss][Ackermann_def, Alemma1] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [ARITH_ss][] THEN
    ONCE_REWRITE_TAC [DECIDE ``x ≤ y + z ⇔ x - z ≤ y``] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN DECIDE_TAC
  ]);

val Alemma2' = prove(
  ``m < H n m``,
  METIS_TAC [Alemma2, DECIDE ``n + 1 ≤ m ⇔ n < m``]);



val Alemma3a = prove(
  ``∀n m. H n m < H n (m + 1)``,
  Cases_on `n` THEN Cases_on `m` THEN
  SRW_TAC [ARITH_ss][Ackermann_def, Alemma1, GSYM ADD1] THEN
  SIMP_TAC bool_ss [ONE, Ackermann_def, Alemma2']);

val MONO_THM = store_thm(
  "MONO_THM",
  ``(∀n. f n < f (n + 1)) ⇒
      (∀n1 n2. f n1 < f n2 ⇔ n1 < n2) ∧
      (∀n1 n2. (f n1 = f n2) ⇔ (n1 = n2)) ∧
      (∀n1 n2. f n1 ≤ f n2 ⇔ n1 ≤ n2)``,
  STRIP_TAC THEN
  `∀n1 n2. n1 < n2 ⇒ f n1 < f n2`
     by (Induct_on `n2 - n1` THEN SRW_TAC [][] THEN1 DECIDE_TAC THEN
         Cases_on `v` THENL [
           `n2 = n1 + 1` by DECIDE_TAC THEN SRW_TAC [][],
           MATCH_MP_TAC LESS_TRANS THEN
           Q.EXISTS_TAC `f (n1 + 1)` THEN SRW_TAC [ARITH_ss][]
         ]) THEN
  `∀n1 n2. f n1 < f n2 ⇔ n1 < n2`
     by (SRW_TAC [][EQ_IMP_THM] THEN
         `n1 < n2 ∨ (n1 = n2) ∨ n2 < n1` by DECIDE_TAC THEN
         SRW_TAC [ARITH_ss][] THEN
         RES_TAC THEN DECIDE_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `∀n1 n2. (f n1 = f n2) ⇔ (n1 = n2)`
     by (SRW_TAC [][EQ_IMP_THM] THEN
         `n1 < n2 ∨ (n1 = n2) ∨ n2 < n1` by DECIDE_TAC THEN
         SRW_TAC [ARITH_ss][] THEN
         METIS_TAC [DECIDE ``¬(x < x)``]) THEN
  SRW_TAC [][LESS_OR_EQ]);

val A_MONO2 = Save_thm(
  "A_MONO2",
  Alemma3a |> Q.SPEC `n` |> MATCH_MP MONO_THM);

val Alemma3b = prove(
  ``H n (m + 1) ≤ H (n + 1) m``,
  Cases_on `m` THEN SRW_TAC [ARITH_ss][Ackermann_def, GSYM ADD1] THEN
  MATCH_MP_TAC Alemma2b THEN DECIDE_TAC);

val Alemma2b_LT = Alemma2b |> Q.SPECL [`n`, `m`, `p + 1`]
                           |> REWRITE_RULE [DECIDE ``x + 1 ≤ y ⇔ x < y``]

val Alemma3c = prove(
  ``H n m < H (n + 1) m``,
  Cases_on `m` THEN SRW_TAC [][Ackermann_def, GSYM ADD1] THEN
  MATCH_MP_TAC Alemma2b_LT THEN DECIDE_TAC)

val lem = prove(``∀n. (λp. H p m) n < (λp. H p m) (n + 1)``,
                SRW_TAC [][Alemma3c])

val A_MONO1 = Save_thm(
  "A_MONO1",
  lem |> MATCH_MP MONO_THM |> BETA_RULE);

val Alemma4 = prove(
  ``H n1 m + H n2 m < H (MAX n1 n2 + 4) m``,
  `H n1 m + H n2 m ≤ H (MAX n1 n2) m + H (MAX n1 n2) m`
     by SRW_TAC [][LESS_EQ_LESS_EQ_MONO] THEN
  `H n1 m + H n2 m ≤ 2 * H (MAX n1 n2) m` by DECIDE_TAC THEN
  `H n1 m + H n2 m < 2 * H (MAX n1 n2) m + 3` by DECIDE_TAC THEN
  `H n1 m + H n2 m < H 2 (H (MAX n1 n2) m)` by SRW_TAC [][Alemma1] THEN
  `H 2 (H (MAX n1 n2) m) < H 2 (H (MAX n1 n2 + 3) m)`
    by SRW_TAC [ARITH_ss][MAX_DEF] THEN
  `H 2 (H (MAX n1 n2 + 3) m) ≤ H (MAX n1 n2 + 2) (H (MAX n1 n2 + 3) m)`
    by SRW_TAC [][] THEN
  `H (MAX n1 n2 + 2) (H (MAX n1 n2 + 3) m) = H (MAX n1 n2 + 3) (m + 1)`
    by (`MAX n1 n2 + 3 = SUC (MAX n1 n2 + 2)` by DECIDE_TAC THEN
        `m + 1 = SUC m` by DECIDE_TAC THEN
        SRW_TAC [][Ackermann_def]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `H (MAX n1 n2 + 3) (m + 1) ≤ H (MAX n1 n2 + 4) m`
    by (`MAX n1 n2 + 4 = (MAX n1 n2 + 3) + 1` by DECIDE_TAC THEN
        SRW_TAC [][Alemma3b]) THEN
  DECIDE_TAC);

val Alemma5 = prove(
  ``H n m + m < H (n + 4) m``,
  MATCH_MP_TAC LESS_TRANS THEN
  Q.EXISTS_TAC `H n m + H 0 m` THEN
  CONJ_TAC THEN1 SRW_TAC [ARITH_ss][Ackermann_def] THEN
  Q_TAC SUFF_TAC `n + 4 = MAX n 0 + 4`
    THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Alemma4]) THEN
  SRW_TAC [][]);

val EL_SUM = store_thm(
  "EL_SUM",
  ``∀i l. i < LENGTH l ⇒ (EL i l ≤ SUM l)``,
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  RES_TAC THEN DECIDE_TAC);


val SUM_MAP_LT_pwise = store_thm(
  "SUM_MAP_LT_pwise",
  ``0 < LENGTH l ∧ (∀e. MEM e l ⇒ (f1 e < f2 e)) ⇒
    SUM (MAP f1 l) < SUM (MAP f2 l)``,
  Induct_on `l` THEN SRW_TAC [][FORALL_AND_THM, DISJ_IMP_THM] THEN
  Cases_on `0 < LENGTH l` THEN1
    SRW_TAC [][DECIDE ``x < y ∧ a < b ⇒ x + a < y + b``] THEN
  `LENGTH l = 0` by DECIDE_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [listTheory.LENGTH_NIL]);

val MAXLIST_def= Define`
  (MAXLIST [] = 0) ∧
  (MAXLIST (h::t) = MAX h (MAXLIST t))
`;

val alem6_lem = prove(
  ``0 < LENGTH xs ⇒
    SUM (MAP (λx. H (f x) n) xs) ≤
    H (MAXLIST (MAP f xs) + 4 * (LENGTH xs - 1)) n``,
  Induct_on `xs` THEN SRW_TAC [][MAXLIST_def] THEN
  Cases_on `xs = []` THEN1 SRW_TAC [][MAXLIST_def] THEN
  `0 < LENGTH xs` by (Cases_on `xs` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ABBREV_TAC `H (f h) n + XX ≤ H JJ n` THEN
  Q.PAT_ASSUM `XX ≤ H J' n` MP_TAC THEN
  Q.MATCH_ABBREV_TAC `XX ≤ H J' n ⇒ H (f h) n + XX ≤ H JJ n` THEN
  Q_TAC SUFF_TAC `H (f h) n + H J' n ≤ H JJ n` THEN1 DECIDE_TAC THEN
  `H (f h) n + H J' n < H (MAX (f h) J' + 4) n` by METIS_TAC [Alemma4] THEN
  Q.ABBREV_TAC `X = MAXLIST (MAP f xs)` THEN
  Q_TAC SUFF_TAC `H (MAX (f h) J' + 4) n ≤ H JJ n` THEN1 DECIDE_TAC THEN
  SRW_TAC [][] THEN
  MAP_EVERY Q.UNABBREV_TAC [`J'`, `JJ`] THEN
  `∃N. LENGTH xs = N + 1`
    by (Cases_on `LENGTH xs` THEN FULL_SIMP_TAC (srw_ss()) [ADD1]) THEN
  SRW_TAC [ARITH_ss][LEFT_ADD_DISTRIB] THEN
  SRW_TAC [ARITH_ss][MAX_DEF]);

val Ackermann_grows_too_fast = store_thm(
  "Ackermann_grows_too_fast",
  ``∀f k. primrec f k ⇒ ∃J. ∀l. (LENGTH l = k) ⇒ f l < H J (SUM l)``,
  HO_MATCH_MP_TAC strong_primrec_ind THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][Ackermann_def],
    Q.EXISTS_TAC `1` THEN SRW_TAC [ARITH_ss][Alemma1] THEN
    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC,
    Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][Ackermann_def] THEN
    MATCH_MP_TAC (DECIDE ``p ≤ x ⇒ p < x + 1``) THEN
    SRW_TAC [ARITH_ss][proj_def, EL_SUM],

    `0 < LENGTH gs` by METIS_TAC [primrec_nzero] THEN
    `∀l. Cn f gs l = f (MAP (λg. g l) gs)`
       by (Cases_on `gs` THEN FULL_SIMP_TAC (srw_ss()) [Cn_def]) THEN
    `∀l. f (MAP (λg. g l) gs) < H J (SUM (MAP (λg. g l) gs))`
       by METIS_TAC [listTheory.LENGTH_MAP] THEN
    `∀g. MEM g gs ⇒ ∃Jg. ∀l. (LENGTH l = k) ⇒ g l < H Jg (SUM l)`
       by FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM] THEN
    POP_ASSUM (fn th => th |> SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM,
                                                    SKOLEM_THM]
                           |> Q.X_CHOOSE_THEN `gJ` STRIP_ASSUME_TAC) THEN
    `∀l. (LENGTH l = k) ⇒
         SUM (MAP (λg. g l) gs) < SUM (MAP (λg. H (gJ g) (SUM l)) gs)`
       by (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_MAP_LT_pwise THEN
           SRW_TAC [][]) THEN
    `∀l. (LENGTH l = k) ⇒
           H J (SUM (MAP (λg. g l) gs))
         <
           H J (SUM (MAP (λg. H (gJ g) (SUM l)) gs))`
       by SRW_TAC [][] THEN
    Q.ABBREV_TAC `JJ = MAXLIST (MAP gJ gs) + 4 * (LENGTH gs - 1)` THEN
    `∀n. (LENGTH n = k) ⇒
            H J (SUM (MAP (λg. H (gJ g) (SUM n)) gs)) ≤
            H J (H JJ (SUM n))`
      by SRW_TAC [][Abbr`JJ`, alem6_lem] THEN
    `∀n. (LENGTH n = k) ⇒ H J (H JJ (SUM n)) < H J (H (JJ+1) (SUM n))`
      by SRW_TAC [][] THEN
    `∀n. (LENGTH n = k) ⇒
            H J (H (JJ + 1) (SUM n)) ≤ H J (H (MAX J JJ + 1) (SUM n))`
      by SRW_TAC [][] THEN
    `∀n. (LENGTH n = k) ⇒
           H J (H (MAX J JJ + 1) (SUM n)) ≤
           H (MAX J JJ) (H (MAX J JJ + 1) (SUM n))`
      by SRW_TAC [][] THEN
    `∀n. (LENGTH n = k) ⇒
           (H (MAX J JJ) (H (MAX J JJ + 1) (SUM n)) =
            H (MAX J JJ + 1) (SUM n + 1))`
      by SRW_TAC [][GSYM ADD1, Ackermann_def] THEN
    POP_ASSUM (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th])) THEN
    `∀n. (LENGTH n = k) ⇒
         H (MAX J JJ + 1) (SUM n + 1) ≤ H (MAX J JJ + 2) (SUM n)`
      by SRW_TAC [][DECIDE ``x + 2 = (x + 1) + 1``, Alemma3b] THEN
    Q.EXISTS_TAC `MAX J JJ + 2` THEN
    Q.X_GEN_TAC `n` THEN SRW_TAC [][] THEN
    REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC)) THEN
    DECIDE_TAC,

    Q.ABBREV_TAC `JJ = MAX J (J'+3) + 5` THEN
    Q.ABBREV_TAC `ff = Pr f f'` THEN
    Q_TAC SUFF_TAC `∀m t. (LENGTH t = k) ⇒ ff (m :: t) < H JJ (SUM (m :: t))`
      THEN1 (STRIP_TAC THEN Q.EXISTS_TAC `JJ` THEN Cases_on `l` THEN
             SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
    `0 < k ∧ k ≠ 0` by METIS_TAC [primrec_nzero, DECIDE ``0 < n ⇔ n ≠ 0``] THEN
    Induct THENL [
      SRW_TAC [][Abbr`ff`, GSYM ADD1] THEN
      MATCH_MP_TAC LESS_TRANS THEN
      Q.EXISTS_TAC `H J (SUM t)` THEN
      SRW_TAC [][Abbr`JJ`] THEN SRW_TAC [ARITH_ss][MAX_DEF],

      `∀t m. ff (SUC m :: t) = f' (m :: ff (m :: t) :: t)`
          by SRW_TAC [][Abbr`ff`] THEN
      SRW_TAC [][] THEN
      `f' (m :: ff (m :: t) :: t) < H J' (SUM (m :: ff (m :: t) :: t))`
         by SRW_TAC [ARITH_ss][] THEN
      `SUM (m :: ff (m :: t) :: t) = m + ff (m :: t) + SUM t`
         by SRW_TAC [ARITH_ss][] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      Q.ABBREV_TAC `Σ = SUM t` THEN
      `H J' (m + ff (m::t) + Σ) < H J' (m + ff (m::t) + Σ + 1)`
         by SRW_TAC [][] THEN
      `H J' (m + ff (m::t) + Σ + 1) = H J' (H 0 (Σ + m) + ff (m::t))`
         by SRW_TAC [ARITH_ss][Ackermann_def] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `H J' (H 0 (Σ + m) + ff (m :: t)) <
       H J' (H 0 (Σ + m) + H JJ (Σ + m))`
         by (FULL_SIMP_TAC (srw_ss()) [] THEN
             SRW_TAC [][Abbr`Σ`] THEN METIS_TAC [ADD_COMM]) THEN
      `H J' (H 0 (Σ + m) + H JJ (Σ + m)) <
       H J' (H JJ (Σ + m) + H JJ (Σ + m))`
         by SRW_TAC [ARITH_ss][Abbr`JJ`] THEN
      `H J' (H JJ (Σ + m) + H JJ (Σ + m)) = H J' (2 * H JJ (Σ + m))`
         by SRW_TAC [ARITH_ss][] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `H J' (2 * H JJ (Σ + m)) < H J' (2 * H JJ (Σ + m) + 3)`
         by SRW_TAC [][] THEN
      `H J' (2 * H JJ (Σ + m) + 3) = H J' (H 2 (H JJ (Σ + m)))`
         by SRW_TAC [][Alemma1] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `H J' (H 2 (H JJ (Σ + m))) < H (J' + 3) (H 2 (H JJ (Σ + m)))`
         by SRW_TAC [][] THEN
      `H (J' + 3) (H 2 (H JJ (Σ + m))) < H (J' + 3) (H (J' + 4) (H JJ (Σ + m)))`
         by SRW_TAC [ARITH_ss][] THEN
      `H (J' + 3) (H (J' + 4) (H JJ (Σ + m))) = H (J' + 4) (H JJ (Σ + m) + 1)`
         by SRW_TAC [][Ackermann_def, DECIDE ``x + 4 = SUC (x + 3)``,
                       GSYM ADD1] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `H (J' + 4) (H JJ (Σ + m) + 1) ≤ H (J' + 5) (H JJ (Σ + m))`
         by SRW_TAC [][Alemma3b, DECIDE ``x + 5 = x + 4 + 1``] THEN
      `J' + 5 < JJ - 1` by SRW_TAC [ARITH_ss][MAX_DEF, Abbr`JJ`] THEN
      `H (J' + 5) (H JJ (Σ + m)) < H (JJ - 1) (H JJ (Σ + m))`
         by SRW_TAC [][] THEN
      `0 < JJ` by SRW_TAC [ARITH_ss][Abbr`JJ`] THEN
      `H (JJ - 1) (H JJ (Σ + m)) = H JJ (SUC m + Σ)`
         by (Cases_on `JJ` THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN
             SRW_TAC [ARITH_ss][ADD_CLAUSES, Ackermann_def]) THEN
      POP_ASSUM SUBST_ALL_TAC THEN DECIDE_TAC
    ]
  ]);

val Ackermann_not_primrec = store_thm(
  "Ackermann_not_primrec",
  ``¬∃f. primrec f 2 ∧ ∀n m. f [n; m] = H n m``,
  STRIP_TAC THEN
  Q.ABBREV_TAC `g = Cn f [proj 0; proj 0]` THEN
  `∀n. g [n] = H n n` by SRW_TAC [][Abbr`g`] THEN
  `primrec g 1` by SRW_TAC [][Abbr`g`, primrec_rules] THEN
  `∃J. ∀n. g [n] < H J n`
     by (IMP_RES_TAC Ackermann_grows_too_fast THEN
         Q.PAT_ASSUM `∀l. (LENGTH l = 1) ⇒ g l < H X Y`
                     (Q.SPEC_THEN `[n]` (MP_TAC o Q.GEN `n`)) THEN
         DISCH_THEN (ASSUME_TAC o SIMP_RULE (srw_ss()) []) THEN
         METIS_TAC []) THEN
  POP_ASSUM (Q.SPEC_THEN `J` MP_TAC) THEN SRW_TAC [][]);

val _ = export_theory()



