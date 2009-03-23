open HolKernel boolLib Parse

open arithmeticTheory BasicProvers TotalDefn SingleStep numSimps
     simpLib metisLib

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = set_trace "Unicode" 1

val _ = new_theory "numpair"

(* ---------------------------------------------------------------------- 
    Triangular numbers 
   ---------------------------------------------------------------------- *)

val tri_def = Define`
  (tri 0 = 0) ∧ 
  (tri (SUC n) = SUC n + tri n)
`;

val twotri_formula = store_thm(
  "twotri_formula",
  ``2 * tri n = n * (n + 1)``,
  Induct_on `n` THEN 
  SRW_TAC [ARITH_ss][tri_def, MULT_CLAUSES, LEFT_ADD_DISTRIB]);

val tri_formula = store_thm(
  "tri_formula",
  ``tri n = (n * (n + 1)) DIV 2``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC DIV_UNIQUE THEN 
  Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][twotri_formula]);

val tri_eq_0 = Store_thm(
  "tri_eq_0", 
  ``((tri n = 0) ⇔ (n = 0)) ∧ ((0 = tri n) ⇔ (n = 0))``,
  Cases_on `n` THEN SRW_TAC [ARITH_ss][tri_def]);

val DECIDE_TAC = SRW_TAC [ARITH_ss][]
val tri_LT_I = store_thm(
  "tri_LT_I",
  ``∀n m. n < m ⇒ tri n < tri m``,
  Induct THEN Cases_on `m` THEN SRW_TAC [ARITH_ss][tri_def] THEN 
  RES_TAC THEN DECIDE_TAC);

val tri_LT = Store_thm(
  "tri_LT",
  ``∀n m. tri n < tri m ⇔ n < m``,
  SRW_TAC [][EQ_IMP_THM, tri_LT_I] THEN 
  SPOSE_NOT_THEN ASSUME_TAC THEN 
  `(n = m) ∨ m < n` by DECIDE_TAC THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN 
  METIS_TAC [prim_recTheory.LESS_REFL, tri_LT_I, LESS_TRANS]);
  
val tri_11 = Store_thm(
  "tri_11",
  ``∀m n. (tri m = tri n) ⇔ (m = n)``,
  SRW_TAC [][EQ_IMP_THM] THEN 
  `m < n ∨ n < m ∨ (m = n)` by DECIDE_TAC THEN 
  METIS_TAC [tri_LT_I, prim_recTheory.LESS_REFL]);

val tri_LE = Store_thm(
  "tri_LE",
  ``∀m n. tri m ≤ tri n ⇔ m ≤ n``,
  SRW_TAC [][LESS_OR_EQ]);

val invtri0_def = Define`
  invtri0 n a = if n < a + 1 then (n,a) 
                else invtri0 (n - (a + 1)) (a + 1)
`;

val invtri_def = Define`invtri n = SND (invtri0 n 0)`;
val _ = Unicode.unicode_version {tmnm = "invtri", u = "tri⁻¹"}

val invtri0_thm = store_thm(
  "invtri0_thm",
  ``∀n a. tri (SND (invtri0 n a)) + FST (invtri0 n a) = n + tri a``,
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN 
  Cases_on `n < a + 1` THEN
  ONCE_REWRITE_TAC [invtri0_def] THEN SRW_TAC [ARITH_ss][] THEN 
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]);
    
val SND_invtri0 = store_thm(
  "SND_invtri0",
  ``∀n a. FST (invtri0 n a) < SUC (SND (invtri0 n a))``,
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN
  Cases_on `n < a + 1` THEN ONCE_REWRITE_TAC [invtri0_def] THEN 
  SRW_TAC [ARITH_ss][]);

val invtri_lower = store_thm(
  "invtri_lower",
  ``tri (tri⁻¹ n) ≤ n``,
  SRW_TAC [][invtri_def] THEN 
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN 
  SRW_TAC [ARITH_ss][tri_def]);

val invtri_upper = store_thm(
  "invtri_upper",
  ``n < tri (tri⁻¹ n + 1)``,
  SRW_TAC [][invtri_def, GSYM ADD1, tri_def] THEN 
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN 
  Q.SPECL_THEN [`n`, `0`] MP_TAC SND_invtri0 THEN 
  SRW_TAC [ARITH_ss][tri_def]);

val invtri_linverse = Store_thm(
  "invtri_linverse",
  ``tri⁻¹ (tri n) = n``,
  MAP_EVERY (MP_TAC o Q.INST [`n` |-> `tri n`]) 
            [invtri_upper, invtri_lower] THEN 
  SRW_TAC [ARITH_ss][]);

val invtri_unique = store_thm(
  "invtri_unique",
  ``tri y ≤ n ∧ n < tri (y + 1) ⇒ (tri⁻¹ n = y)``,
  STRIP_TAC THEN MAP_EVERY ASSUME_TAC [invtri_lower, invtri_upper] THEN 
  `tri⁻¹ n < y ∨ (tri⁻¹ n = y) ∨ y < tri⁻¹ n` by DECIDE_TAC THENL [
     `tri⁻¹ n + 1 ≤ y` by DECIDE_TAC THEN 
     `tri (tri⁻¹ n + 1) ≤ tri y` by SRW_TAC [][] THEN 
     DECIDE_TAC,
     `y + 1 ≤ tri⁻¹ n` by DECIDE_TAC THEN 
     `tri (y + 1) ≤ tri (tri⁻¹ n)` by SRW_TAC [][] THEN 
     DECIDE_TAC
  ]);
     
val invtri_linverse_r = store_thm(
  "invtri_linverse_r",
  ``y ≤ x ⇒ (tri⁻¹ (tri x + y) = x)``,
  STRIP_TAC THEN MATCH_MP_TAC invtri_unique THEN 
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]);

(* ----------------------------------------------------------------------
    Numeric pair, fst and snd
   ---------------------------------------------------------------------- *)

val npair_def = Define`
  npair m n = tri (m + n) + n
`;

val _ = set_fixity "*," (Infixr 601)
val _ = Unicode.unicode_version {tmnm = "*,", u = "⊗"}
val _ = overload_on ("*,", ``npair``)


val nfst_def = Define`
  nfst n = tri (tri⁻¹ n) + tri⁻¹ n - n
`;

val nsnd_def = Define`
  nsnd n = n - tri (tri⁻¹ n)
`;

val nfst_npair = Store_thm(
  "nfst_npair",
  ``nfst (x ⊗ y) = x``,
  SRW_TAC [][nfst_def, npair_def] THEN 
  SRW_TAC [ARITH_ss][invtri_linverse_r]);

val nsnd_npair = Store_thm(
  "nsnd_npair",
  ``nsnd (x ⊗ y) = y``,
  SRW_TAC [][nsnd_def, npair_def] THEN 
  SRW_TAC [ARITH_ss][invtri_linverse_r]);

val npair_cases = store_thm(
  "npair_cases",
  ``∀n. ∃x y. n = (x ⊗ y)``,
  STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC [`nfst n`, `nsnd n`] THEN 
  SRW_TAC [][nsnd_def, nfst_def, npair_def] THEN 
  `n ≤ tri (tri⁻¹ n) + tri⁻¹ n`
     by (ASSUME_TAC invtri_upper THEN 
         FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [GSYM ADD1, tri_def]) THEN 
  ASSUME_TAC invtri_lower THEN 
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val npair = Store_thm(
  "npair",
  ``∀n. (nfst n ⊗ nsnd n) = n``,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC npair_cases THEN 
  SRW_TAC [][]);

val npair_11 = Store_thm(
  "npair_11",
  ``(x₁ ⊗ y₁ = x₂ ⊗ y₂) ⇔ (x₁ = x₂) ∧ (y₁ = y₂)``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o Q.AP_TERM `nfst`) THEN SRW_TAC [][],
    POP_ASSUM (MP_TAC o Q.AP_TERM `nsnd`) THEN SRW_TAC [][]
  ]);

val _ = export_theory()

