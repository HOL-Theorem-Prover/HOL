open HolKernel Parse boolLib bossLib

open grammarTheory
open lcsymtacs
open pred_setTheory

val _ = new_theory "NTproperties"

val dsimp = simp_tac (srw_ss() ++ boolSimps.DNF_ss)

val nullable_def = Define`
  nullable G sf = derives G sf []
`

fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)

val APPEND_EQ_SING' = CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                                listTheory.APPEND_EQ_SING

val derives_TOK = store_thm(
  "derives_TOK",
  ``∀G p s t sf.
      derives G (p ++ [TOK t] ++ s) sf ⇒
      ∃ps ss. sf = ps ++ [TOK t] ++ ss ∧ derives G p ps ∧ derives G s ss``,
  gen_tac >>
  `∀sf0 sf. derives G sf0 sf ⇒
            ∀p s t. sf0 = p ++ [TOK t] ++ s ⇒
                    ∃ps ss. sf = ps ++ [TOK t] ++ ss ∧ derives G p ps ∧
                            derives G s ss` suffices_by metis_tac[] >>
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT >> dsimp[] >> conj_tac
  >- metis_tac [relationTheory.RTC_REFL] >>
  map_every qx_gen_tac [`sf0`, `sf`, `p`, `s`, `t`] >>
  simp[derive_def, Once listTheory.APPEND_EQ_APPEND_MID] >>
  disch_then (CONJUNCTS_THEN2 (qxchl [`p0`, `N`, `r`, `s0`] mp_tac)
                              strip_assume_tac) >>
  disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN (qxchl [`l`] strip_assume_tac))
                              strip_assume_tac) >>
  rw[] >| [
    qpat_assum `x = y` mp_tac >> simp[Once listTheory.APPEND_EQ_APPEND_MID] >>
    simp[APPEND_EQ_SING'] >> disch_then (qxchl [`l'`] strip_assume_tac) >>
    rw[] >> first_x_assum (qspecl_then [`p`, `l' ++ r ++ s0`, `t`] mp_tac),
    first_x_assum (qspecl_then [`p0 ++ r ++ l`, `s`, `t`] mp_tac)
  ] >>
  simp[] >> disch_then (qxchl [`ps`, `ss`] strip_assume_tac) >>
  map_every qexists_tac [`ps`, `ss`] >> simp[] >>
  match_mp_tac (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  simp[derive_def] >> metis_tac[])

val nullable_CONS_TOK = store_thm(
  "nullable_CONS_TOK",
  ``nullable G (TOK t :: rest) = F``,
  simp[nullable_def] >> strip_tac >>
  qspecl_then [`G`, `[]`, `rest`, `t`, `[]`] mp_tac derives_TOK >> simp[])
val _ = export_rewrites ["nullable_CONS_TOK"]

val _ = overload_on ("nullableNT", ``λG n. nullable G [NT n]``)

val paireq = prove(
  ``(x,y) = z ⇔ x = FST z ∧ y = SND z``, Cases_on `z` >> simp[])

val GSPEC_INTER = prove(
  ``GSPEC f ∩ Q =
    GSPEC (S ($, o FST o f) (S ($/\ o SND o f) (Q o FST o f)))``,
  simp[GSPECIFICATION, EXTENSION, SPECIFICATION] >> qx_gen_tac `e` >>
  simp[paireq] >> metis_tac[])

val _ = SIMP_CONV (srw_ss())[GSPEC_INTER, combinTheory.o_ABS_R, combinTheory.S_ABS_R, combinTheory.S_ABS_L, pairTheory.o_UNCURRY_R, pairTheory.S_UNCURRY_R] ``{ n + m | n > 10 ∧ m < 3 } ∩ Q``

val nullableML_def = tDefine "nullableML" `
  nullableML seen [] = T ∧
  nullableML seen (TOK t :: _) = F ∧
  nullableML seen (NT n :: rest) =
      if n ∈ FDOM G.rules ∧ n ∉ seen then
        if G.rules ' n ∩ nullableML (n INSERT seen) = ∅ then F
        else nullableML seen rest
      else F
`
  (WF_REL_TAC `measure (λs. CARD (FDOM G.rules DIFF s)) LEX measure LENGTH` >>
   rpt strip_tac >> simp[] >> DISJ1_TAC >> simp[CARD_DIFF_EQN] >>
   simp[Once INTER_COMM] >> simp[INSERT_INTER] >>
   simp[FINITE_INTER] >> simp[Once INTER_COMM] >>
   simp[arithmeticTheory.SUB_LEFT_LESS] >>
   match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
   qexists_tac `CARD (n INSERT FDOM G.rules ∩ seen)` >>
   conj_tac >- simp[] >>
   `FINITE (FDOM G.rules)` by simp[] >>
   pop_assum (MATCH_MP_TAC o MATCH_MP CARD_SUBSET) >>
   simp[SUBSET_DEF])

(*
val nullable_nullableML = store_thm(
  "nullable_nullableML",
  ``∀sn sf. nullable G sf ∧ (∀n. n ∈ sn ⇒ ¬nullable G [NT n]) ⇒
            nullableML G sn sf``,
  HO_MATCH_MP_TAC (theorem "nullableML_ind") >> simp[nullableML_def] >>
  rpt strip_tac

*)

val _ = export_theory()
