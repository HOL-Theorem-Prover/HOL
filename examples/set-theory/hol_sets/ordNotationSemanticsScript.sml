open HolKernel Parse boolLib bossLib

open ordinalTheory cardinalTheory ordinalNotationTheory

val _ = new_theory "ordNotationSemantics"

val ordModel_def = Define`
  (ordModel (End n) = &n) ∧
  (ordModel (Plus e c t) = &c * ω ** ordModel e + ordModel t)
`

val _ = add_rule {fixity = Closefix, term_name = "ordModel",
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,2)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟦", TM, TOK "⟧"]}

val osyntax_EQ_0 = store_thm(
  "osyntax_EQ_0",
  ``∀a. is_ord a ⇒ (⟦a⟧ = 0) ⇒ (a = End 0)``,
  Induct_on `is_ord` THEN SRW_TAC [][ordModel_def] THEN
  `k ≠ 0` by DECIDE_TAC THEN SRW_TAC [][ordEXP_EQ_0]);

val ordModel_lt_epsilon0 = store_thm(
  "ordModel_lt_epsilon0",
  ``∀a. ⟦a⟧ < ε₀``,
  Induct_on `a` THEN
  SRW_TAC [][ordMUL_under_epsilon0, ordEXP_under_epsilon0,
             ordADD_under_epsilon0, ordModel_def]);

(*
val ord_less_models_ordlt = store_thm(
  "ord_less_models_ordlt",
  ``∀x y. ord_less x y ⇒ ⟦x⟧ < ⟦y⟧``,
  SIMP_TAC (srw_ss()) [ord_less_def] THEN
  completeInduct_on `MAX (osyntax_size x) (osyntax_size y)` THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN
  SIMP_TAC (srw_ss()) [Once oless_cases] THEN SRW_TAC [][] THEN
  SRW_TAC [][ordModel_def] THENL [
    MATCH_MP_TAC ordlte_TRANS THEN Q.EXISTS_TAC `ω` THEN SRW_TAC [][] THEN
    MATCH_MP_TAC ordle_TRANS THEN Q.EXISTS_TAC `&k2 * ω ** ⟦e2⟧` THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC ordle_TRANS THEN Q.EXISTS_TAC `ω ** ⟦e2⟧` THEN
    SRW_TAC [][] THENL [
      SIMP_TAC bool_ss [Once (GSYM ordEXP_1R), SimpR ``ordlt``] THEN
      MATCH_MP_TAC ordEXP_le_MONO_R THEN
      FULL_SIMP_TAC (srw_ss()) [is_ord_equations] THEN
      STRIP_TAC THEN
      `⟦e2⟧ = 0` by METIS_TAC [IFF_ZERO_lt] THEN METIS_TAC [osyntax_EQ_0],
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [is_ord_equations]
    ],

    FULL_SIMP_TAC (srw_ss()) [is_ord_equations, arithmeticTheory.MAX_LT]
    ...
*)

val _ = export_theory()
