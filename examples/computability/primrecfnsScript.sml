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



val proj_def = Define`
  (proj 0 0 n = n) /\
  (proj 0 _ n = nfst n) /\
  (proj (SUC m) x n = proj m (x - 1) (nsnd n))
`

val proj123 = Store_thm(
  "proj123",
  ``(proj 0 0 n = n) ∧
    (proj 0 1 (n ⊗ m) = n) ∧
    (proj 1 1 (n ⊗ m) = m) ∧
    (proj 0 2 (n ⊗ m ⊗ p) = n) ∧
    (proj 1 2 (n ⊗ m ⊗ p) = m) ∧
    (proj 2 2 (n ⊗ m ⊗ p) = p)``,
  SIMP_TAC bool_ss [ONE, TWO, proj_def,
                    nfst_npair, nsnd_npair, SUB,
                    LESS_MONO_EQ, prim_recTheory.LESS_0,
                    prim_recTheory.NOT_LESS_0]);

val nway_list_def = Define`
  (nway_list 0 l = []) ∧
  (nway_list (SUC n) l = if n = 0 then [l]
                         else nfst l :: nway_list n (nsnd l))
`;

val LENGTH_nway_list = Store_thm(
  "LENGTH_nway_list",
  ``∀n l. LENGTH (nway_list n l) = n``,
  Induct_on `n` THEN SRW_TAC [][nway_list_def]);

val nmerge_def = Define`
  (nmerge [] = 0) ∧
  (nmerge [x] = x) ∧
  (nmerge (x::xs) = x ⊗ nmerge xs)
`;

val nmerge_nway_list = Store_thm(
  "nmerge_nway_list",
  ``∀n l. 0 < n ⇒ (nmerge (nway_list n l) = l)``,
  Induct THEN SRW_TAC [][nway_list_def, nmerge_def] THEN
  `LENGTH (nway_list n (nsnd l)) = n` by SRW_TAC [][] THEN
  `∃h t. nway_list n (nsnd l) = h::t` by (Cases_on `nway_list n (nsnd l)` THEN
                                          FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][nmerge_def] THEN
  METIS_TAC [npair, DECIDE ``0 < x <=> 0 ≠ x``]);

val nway_list_nmerge = Store_thm(
  "nway_list_nmerge",
  ``∀l. nway_list (LENGTH l) (nmerge l) = l``,
  Induct_on `l` THEN SIMP_TAC (srw_ss()) [nway_list_def] THEN
  SRW_TAC [][listTheory.LENGTH_NIL, nmerge_def] THEN
  `∃h t. l = h::t` by (Cases_on `l` THEN FULL_SIMP_TAC(srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss())[nmerge_def]);

val Cn_def = Define`
  (Cn f [] = f) ∧
  (Cn f (g::gs) = λn. f (nmerge (MAP (λg. g n) (g::gs))))
`;

val Cn0123 = Store_thm(
  "Cn0123",
  ``(Cn f [] n = f n) ∧
    (Cn f [g] n = f (g n)) ∧
    (Cn f [g1; g2] n = f (g1 n ⊗ g2 n)) ∧
    (Cn f [g1; g2; g3] n = f (g1 n ⊗ g2 n ⊗ g3 n))``,
  SRW_TAC [][Cn_def, nmerge_def]);

val Pr_def = tDefine "Pr" `
  Pr b r n = if nfst n = 0 then b (nsnd n)
             else r ((nfst n - 1) ⊗ Pr b r ((nfst n - 1) ⊗ nsnd n) ⊗ nsnd n)
`
(WF_REL_TAC `measure (nfst o SND o SND)` THEN SRW_TAC [ARITH_ss][]);


val Pr_thm = Store_thm(
  "Pr_thm",
  ``(Pr b r (0 ⊗ n) = b n) ∧
    (Pr b r (SUC m ⊗ n) = r (m ⊗ Pr b r (m ⊗ n) ⊗ n)) ∧
    (Pr b r ((m + 1) ⊗ n) = r (m ⊗ Pr b r (m ⊗ n) ⊗ n)) ∧
    (Pr b r ((1 + m) ⊗ n) = r (m ⊗ Pr b r (m ⊗ n) ⊗ n))``,
  SIMP_TAC (bool_ss ++ boolSimps.CONJ_ss) [ONE,
                                           ADD_CLAUSES] THEN
  CONJ_TAC THEN SRW_TAC [][Once Pr_def, SimpLHS]);

val _ = overload_on ("zerof", ``K 0 : num -> num``)

val (primrec_rules, primrec_ind, primrec_cases) = Hol_reln`
  primrec zerof 1 ∧
  primrec SUC 1 ∧
  (∀i n. i ≤ n ⇒ primrec (proj i n) (n + 1)) ∧
  (∀f gs m. primrec f (LENGTH gs) ∧ EVERY (λg. primrec g m) gs ⇒
            primrec (Cn f gs) m) ∧
  (∀b r n. primrec b n ∧ primrec r (n + 2) ⇒ primrec (Pr b r) (n + 1))
`;


val primrec_nzero = store_thm(
  "primrec_nzero",
  ``∀f k. primrec f k ⇒ 0 < k``,
  HO_MATCH_MP_TAC primrec_ind THEN SRW_TAC [ARITH_ss][] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val alt_Pr_rule = Store_thm(
  "alt_Pr_rule",
  ``∀b r m. primrec b (m - 1) ∧ primrec r (m + 1) ⇒ primrec (Pr b r) m``,
  SRW_TAC [][] THEN
  Cases_on `m` THEN1 (IMP_RES_TAC primrec_nzero THEN
                      FULL_SIMP_TAC (srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ADD1, primrec_rules]);

val alt_proj_rule = Store_thm(
  "alt_proj_rule",
  ``i ≤ m ∧ (n = m + 1) ⇒ primrec (proj i m) n``,
  SRW_TAC [][primrec_rules]);

val pr_add_def = Define`
  pr_add = Pr (proj 0 0) (Cn SUC [proj 1 2])
`;

val pr_add_is_addition = Store_thm(
  "pr_add_is_addition",
  ``pr_add (n ⊗ m) = n + m``,
  REWRITE_TAC [pr_add_def] THEN Induct_on `n` THEN SRW_TAC [ARITH_ss][]);

val primrec_pr_add = Store_thm(
  "primrec_pr_add",
  ``primrec pr_add 2``,
  SRW_TAC [][primrec_rules, pr_add_def]);

val pr_mult_def = Define`
  pr_mult = Pr zerof (Cn pr_add [proj 1 2; proj 2 2])
`;

val pr_mult_is_multiplication = Store_thm(
  "pr_mult_is_multiplication",
  ``pr_mult (n ⊗ m) = n * m``,
  SRW_TAC [][pr_mult_def] THEN
  Induct_on `n` THEN SRW_TAC [ARITH_ss][MULT_CLAUSES]);

val primrec_pr_mult = Store_thm(
  "primrec_pr_mult",
  ``primrec pr_mult 2``,
  SRW_TAC [][pr_mult_def, primrec_rules]);

val pr_pred0_def = Define`
  pr_pred0 = Pr zerof (proj 0 2)
`
val pr_pred0_thm = prove(
  ``pr_pred0 (n ⊗ m) = PRE n``,
  Cases_on `n` THEN SRW_TAC [][pr_pred0_def]);

val primrec_pred0 = prove(
  ``primrec pr_pred0 2``,
  SRW_TAC [][pr_pred0_def, primrec_rules]);

val pr_pred_def = Define`
  pr_pred = Cn pr_pred0 [proj 0 0; zerof]
`;

val pr_pred_thm = Store_thm(
  "pr_pred_thm",
  ``pr_pred n = PRE n``,
  SRW_TAC [][pr_pred0_thm, pr_pred_def]);

val primrec_pr_pred = Store_thm(
  "primrec_pr_pred",
  ``primrec pr_pred 1``,
  SRW_TAC [][primrec_rules, primrec_pred0, pr_pred_def]);

val pr_iszero_def = Define`
  pr_iszero = Cn (Pr (Cn SUC [zerof]) (Cn zerof [proj 0 2])) [proj 0 0; zerof]
`;

val pr_iszero = Store_thm(
  "pr_iszero",
  ``pr_iszero n = nB (n = 0)``,
  Cases_on `n` THEN SRW_TAC [][pr_iszero_def]);

val primrec_pr_iszero = Store_thm(
  "primrec_pr_iszero",
  ``primrec pr_iszero 1``,
  SRW_TAC [][pr_iszero_def, primrec_rules]);

val cflip_def = Define`
  cflip f = Cn f [proj 1 1; proj 0 1]
`;

val cflip_thm = Store_thm(
  "cflip_thm",
  ``cflip f (n ⊗ m) = f (m ⊗ n)``,
  SRW_TAC [][cflip_def]);
val primrec_cflip = Store_thm(
  "primrec_cflip",
  ``primrec f 2 ⇒ primrec (cflip f) 2``,
  SRW_TAC [][primrec_rules, cflip_def]);

val pr_sub_def = Define`
  pr_sub = cflip (Pr (proj 0 0) (Cn pr_pred [proj 1 2]))
`;

val pr_sub_thm = Store_thm(
  "pr_sub_thm",
  ``pr_sub (n ⊗ m) = n - m``,
  SRW_TAC [][pr_sub_def] THEN Induct_on `m` THEN SRW_TAC [ARITH_ss][]);

val primrec_pr_sub = Store_thm(
  "primrec_pr_sub",
  ``primrec pr_sub 2``,
  SRW_TAC [][primrec_rules, pr_sub_def])

val pr_le_def = Define`pr_le = Cn pr_iszero [pr_sub]`

val pr_le_thm = Store_thm(
  "pr_le_thm",
  ``pr_le (n ⊗ m) = nB (n ≤ m)``,
  SRW_TAC [ARITH_ss][pr_le_def, pr_iszero]);
val primrec_pr_le = Store_thm(
  "primrec_pr_le",
  ``primrec pr_le 2``,
  SRW_TAC [][primrec_rules, pr_le_def]);

val pr_eq_def = Define`
  pr_eq = Cn pr_mult [pr_le; cflip pr_le]
`;

val pr_eq_thm = Store_thm(
  "pr_eq_thm",
  ``pr_eq (n ⊗ m) = nB (n = m)``,
  SRW_TAC [ARITH_ss][pr_eq_def]);

val primrec_pr_eq = Store_thm(
  "primrec_pr_eq",
  ``primrec pr_eq 2``,
  SRW_TAC [][pr_eq_def, primrec_rules]);

val primrec_K = Store_thm(
  "primrec_K",
  ``∀n. primrec (K n) 1``,
  Induct THEN SRW_TAC [][primrec_rules] THEN
  Q_TAC SUFF_TAC `K (SUC n) = Cn SUC [K n]`
    THEN1 SRW_TAC [][primrec_rules] THEN
  SRW_TAC [][FUN_EQ_THM]);

(* need a function f (Pr,x,y) = Pr * x + (1 - Pr) * y
     Cn + [Cn * [p13, p12], Cn * [Cn - [K 1, p11]; p13]]
*)
val pr_cond_def = Define`
  pr_cond P f g =
    Cn (Cn pr_add [Cn pr_mult [proj 0 2; proj 1 2];
                   Cn pr_mult [Cn pr_sub [Cn (K 1) [proj 0 2]; proj 0 2];
                               proj 2 2]])
       [P;f;g]
`;

val pr_predicate_def = Define`
  pr_predicate P = ∀n. (P n = 0) ∨ (P n = 1)
`;

val Cn_pr_eq_predicate = Store_thm(
  "Cn_pr_eq_predicate",
  ``pr_predicate (Cn pr_eq [f; g])``,
  SRW_TAC [][pr_predicate_def, pr_eq_thm]);

val pr_cond_thm = Store_thm(
  "pr_cond_thm",
  ``pr_predicate P ⇒
    (pr_cond P f g n = if P n = 1 then f n else g n)``,
  SRW_TAC [][pr_cond_def, pr_predicate_def] THEN
  `P n = 0` by METIS_TAC [] THEN
  SRW_TAC [][]);


val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)

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
     (pr_cond (Cn pr_eq [Cn pr_sub [Cn pr_add [proj 0 2; Cn (K 1) [proj 0 2]];
                                    Cn pr_mult [proj 1 2; proj 2 2]];
                         proj 2 2])
              (Cn SUC [proj 1 2])
              (proj 1 2))
`;

val primrec_pr_div = Store_thm(
  "primrec_pr_div",
  ``primrec pr_div 2``,
  SRW_TAC [][pr_div_def] THEN
  MATCH_MP_TAC alt_Pr_rule THEN SRW_TAC [][] THEN
  MATCH_MP_TAC primrec_pr_cond THEN SRW_TAC [][primrec_rules] THEN
  MATCH_MP_TAC primrec_cn THEN SRW_TAC [][primrec_rules]);

val pr_div_recursion = store_thm(
  "pr_div_recursion",
  ``(pr_div (0 ⊗ m) = 0) ∧
    (pr_div ((n + 1) ⊗ m) = let r = pr_div (n ⊗ m)
                            in
                              if n + 1 - r * m = m then r + 1 else r)``,
  SIMP_TAC (srw_ss()) [pr_div_def, LET_THM] THEN
  SIMP_TAC (srw_ss()) [GSYM pr_div_def, ADD1]);

val pr_div_thm = Store_thm(
  "pr_div_thm",
  ``0 < m ⇒ (pr_div (n ⊗ m) = n DIV m)``,
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

val pr_mod_def = Define`
  pr_mod = Cn pr_sub [proj 0 1; Cn pr_mult [pr_div; proj 1 1]]
`;

val pr_mod_eqn = store_thm(
  "pr_mod_eqn",
  ``pr_mod (n ⊗ m) = n - pr_div (n ⊗ m) * m``,
  SRW_TAC [][pr_mod_def]);

val pr_mod_thm = Store_thm(
  "pr_mod_thm",
  ``0 < m ⇒ (pr_mod (n ⊗ m) = n MOD m)``,
  SRW_TAC [][pr_mod_eqn] THEN
  Q.SPEC_THEN `m` (IMP_RES_THEN MP_TAC) DIVISION THEN
  NTAC 2 (DISCH_THEN (Q.SPEC_THEN `n` ASSUME_TAC)) THEN
  DECIDE_TAC);

val primrec_pr_mod = Store_thm(
  "primrec_pr_mod",
  ``primrec pr_mod 2``,
  SRW_TAC [][pr_mod_def, primrec_rules]);

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

val nway_list1 = Store_thm(
  "nway_list1",
  ``nway_list 1 n = [n]``,
  SIMP_TAC bool_ss [nway_list_def, ONE]);

val proj_EL = store_thm(
  "proj_EL",
  ``∀i n l. i ≤ n ⇒ (proj i n l = EL i (nway_list (n + 1) l))``,
  Induct THEN Cases_on `n` THEN
  ASM_SIMP_TAC bool_ss [Once nway_list_def, proj_def, GSYM ADD1] THEN
  SRW_TAC [][ADD1]);

val EL_SUM = store_thm(
  "EL_SUM",
  ``∀i l. i < LENGTH l ⇒ (EL i l ≤ SUM l)``,
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  RES_TAC THEN DECIDE_TAC);

val strong_primrec_ind = IndDefLib.derive_strong_induction(primrec_rules,
                                                           primrec_ind)

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

val SUMk1_nway_list = prove(
  ``0 < n ⇒ (SUM (nway_list (n + 1) (x ⊗ y)) = x + SUM (nway_list n y))``,
  `n + 1 = SUC n` by DECIDE_TAC THEN
  SRW_TAC [][SimpLHS, Once nway_list_def]);

val SUMk2_nway_list = prove(
  ``0 < n ⇒ (SUM (nway_list (n + 2) (x ⊗ y ⊗ z)) =
              x + y + SUM (nway_list n z))``,
  `n + 2 = SUC (n + 1)` by DECIDE_TAC THEN
  SRW_TAC [ARITH_ss][SimpLHS, Once nway_list_def, SUMk1_nway_list])

val Ackermann_grows_too_fast = store_thm(
  "Ackermann_grows_too_fast",
  ``∀f k. primrec f k ⇒ ∃J. ∀n. f n < H J (SUM (nway_list k n))``,
  HO_MATCH_MP_TAC strong_primrec_ind THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][Ackermann_def],
    Q.EXISTS_TAC `1` THEN SRW_TAC [ARITH_ss][Alemma1],
    Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][Ackermann_def, proj_EL] THEN
    MATCH_MP_TAC (DECIDE ``p ≤ x ⇒ p < x + 1``) THEN
    MATCH_MP_TAC EL_SUM THEN SRW_TAC [ARITH_ss][],

    `0 < LENGTH gs` by METIS_TAC [primrec_nzero] THEN
    `∀n. Cn f gs n = f (nmerge (MAP (λg. g n) gs))`
       by (Cases_on `gs` THEN FULL_SIMP_TAC (srw_ss()) [Cn_def]) THEN
    `∀n. f (nmerge (MAP (λg. g n) gs)) < H J (SUM (MAP (λg. g n) gs))`
       by METIS_TAC [nway_list_nmerge, listTheory.LENGTH_MAP] THEN
    `∀g. MEM g gs ⇒ ∃Jg. ∀n. g n < H Jg (SUM (nway_list k n))`
       by FULL_SIMP_TAC (srw_ss()) [listTheory.EVERY_MEM] THEN
    POP_ASSUM (fn th => th |> SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM,
                                                    SKOLEM_THM]
                           |> Q.X_CHOOSE_THEN `gJ` STRIP_ASSUME_TAC) THEN
    `∀n. SUM (MAP (λg. g n) gs) <
         SUM (MAP (λg. H (gJ g) (SUM (nway_list k n))) gs)`
       by (STRIP_TAC THEN MATCH_MP_TAC SUM_MAP_LT_pwise THEN
           SRW_TAC [][]) THEN
    `∀n. H J (SUM (MAP (λg. g n) gs)) <
         H J (SUM (MAP (λg. H (gJ g) (SUM (nway_list k n))) gs))`
       by SRW_TAC [][] THEN
    Q.ABBREV_TAC `JJ = MAXLIST (MAP gJ gs) + 4 * (LENGTH gs - 1)` THEN
    `∀n. H J (SUM (MAP (λg. H (gJ g) (SUM (nway_list k n))) gs)) ≤
         H J (H JJ (SUM (nway_list k n)))`
      by SRW_TAC [][Abbr`JJ`, alem6_lem] THEN
    `∀n. H J (H JJ (SUM (nway_list k n))) <
         H J (H (JJ+1) (SUM (nway_list k n)))`
      by SRW_TAC [][] THEN
    `∀n. H J (H (JJ + 1) (SUM (nway_list k n))) ≤
         H J (H (MAX J JJ + 1) (SUM (nway_list k n)))`
      by SRW_TAC [][] THEN
    `∀n. H J (H (MAX J JJ + 1) (SUM (nway_list k n))) ≤
         H (MAX J JJ) (H (MAX J JJ + 1) (SUM (nway_list k n)))`
      by SRW_TAC [][] THEN
    `∀n. H (MAX J JJ) (H (MAX J JJ + 1) (SUM (nway_list k n))) =
         H (MAX J JJ + 1) (SUM (nway_list k n) + 1)`
      by SRW_TAC [][GSYM ADD1, Ackermann_def] THEN
    POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
    `∀n. H (MAX J JJ + 1) (SUM (nway_list k n) + 1) ≤
         H (MAX J JJ + 2) (SUM (nway_list k n))`
      by SRW_TAC [][DECIDE ``x + 2 = (x + 1) + 1``, Alemma3b] THEN
    Q.EXISTS_TAC `MAX J JJ + 2` THEN
    SRW_TAC [][] THEN
    REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC)) THEN
    DECIDE_TAC,

    Q.ABBREV_TAC `JJ = MAX J (J'+3) + 5` THEN
    Q.ABBREV_TAC `ff = Pr f f'` THEN
    Q_TAC SUFF_TAC
      `∀m n. ff (m ⊗ n) < H JJ (SUM (nway_list (k + 1) (m ⊗ n)))`
      THEN1 METIS_TAC [npair_cases] THEN
    `0 < k ∧ k ≠ 0` by METIS_TAC [primrec_nzero, DECIDE ``0 < n ⇔ n ≠ 0``] THEN
    Induct THENL [
      SRW_TAC [][Abbr`ff`, Once nway_list_def, GSYM ADD1] THEN
      MATCH_MP_TAC LESS_TRANS THEN
      Q.EXISTS_TAC `H J (SUM (nway_list k n))` THEN
      SRW_TAC [][Abbr`JJ`] THEN SRW_TAC [ARITH_ss][MAX_DEF],

      POP_ASSUM MP_TAC THEN SRW_TAC [][SUMk1_nway_list] THEN
      `∀n m. ff (SUC m ⊗ n) = f' (m ⊗ ff (m ⊗ n) ⊗ n)`
          by SRW_TAC [][Abbr`ff`] THEN
      SRW_TAC [][] THEN
      `f' (m ⊗ ff (m ⊗ n) ⊗ n) <
          H J' (SUM (nway_list (k + 2) (m ⊗ ff (m ⊗ n) ⊗ n)))`
         by SRW_TAC [][] THEN
      `SUM (nway_list (k + 2) (m ⊗ ff (m ⊗ n) ⊗ n)) =
       m + ff (m ⊗ n) + SUM (nway_list k n)`
         by SRW_TAC [][SUMk2_nway_list] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      Q.ABBREV_TAC `Σ = SUM (nway_list k n)` THEN
      `H J' (m + ff (m⊗n) + Σ) < H J' (m + ff (m⊗n) + Σ + 1)`
         by SRW_TAC [][] THEN
      `H J' (m + ff (m⊗n) + Σ + 1) = H J' (H 0 (Σ + m) + ff (m⊗n))`
         by SRW_TAC [ARITH_ss][Ackermann_def] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `H J' (H 0 (Σ + m) + ff (m ⊗ n)) <
       H J' (H 0 (Σ + m) + H JJ (Σ + m))`
         by (SRW_TAC [][Abbr`Σ`] THEN METIS_TAC [ADD_COMM]) THEN
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
  ``¬∃f. primrec f 2 ∧ ∀n m. f (n ⊗ m) = H n m``,
  STRIP_TAC THEN
  Q.ABBREV_TAC `g = Cn f [proj 0 0; proj 0 0]` THEN
  `∀n. g n = H n n` by SRW_TAC [][Abbr`g`] THEN
  `primrec g 1` by SRW_TAC [][Abbr`g`, primrec_rules] THEN
  `∃J. ∀n. g n < H J n`
     by (IMP_RES_TAC Ackermann_grows_too_fast THEN
         RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) THEN METIS_TAC []) THEN
  POP_ASSUM (Q.SPEC_THEN `J` MP_TAC) THEN SRW_TAC [][]);

val _ = export_theory()



