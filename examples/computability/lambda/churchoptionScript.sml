open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory pure_dBTheory
open reductionEval pred_setTheory termTheory chap3Theory
open normal_orderTheory churchDBTheory
open head_reductionTheory

val _ = new_theory "churchoption"


val cnone_def = Define`cnone = K`;
Theorem FV_cnone[simp]: FV cnone = ∅
Proof SRW_TAC [][cnone_def]
QED

val csome_def = Define‘
  csome = LAM "x" (LAM "n" (LAM "s" (VAR "s" @@ VAR "x")))
’;
Theorem FV_csome[simp]:
  FV csome = {}
Proof
  SRW_TAC [][EXTENSION, csome_def]
QED

val cvsome_def = Define‘
  cvsome x =
    let n = NEW (FV x) in
    let s = NEW (FV x ∪ {n})
    in
        LAM n (LAM s (VAR s @@ x))
’;

Theorem FV_cvsome[simp]:
  FV (cvsome h) = FV h
Proof
  rw[cvsome_def, LET_THM] >> NEW_ELIM_TAC >> rw[] >> NEW_ELIM_TAC >> rw[] >>
  rw[EXTENSION] >> metis_tac[]
QED

Theorem cvsome_fresh:
  n ∉ FV x ∧ s ∉ FV x ∧ s ≠ n ⇒
    (cvsome x = LAM n (LAM s (VAR s @@ x)))
Proof
  rw[cvsome_def, LET_THM] >> NEW_ELIM_TAC >> rw[] >> NEW_ELIM_TAC >> rw[] >>
  csimp[LAM_eq_thm, tpm_fresh]
QED

Theorem whnf_cvcons[simp]:
  whnf (cvsome x)
Proof
  simp[cvsome_def]
QED

Theorem SUB_cvsome[simp]:
  [N/v] (cvsome x) = cvsome ([N/v]x)
Proof
  Q_TAC (NEW_TAC "n") `{v} ∪ FV N ∪ FV x` >>
  Q_TAC (NEW_TAC "s") `{v;n} ∪ FV N ∪ FV x` >>
  `cvsome x = LAM n (LAM s (VAR s @@ x))` by simp[cvsome_fresh] >>
  ‘cvsome ([N/v]x) = LAM n (LAM s (VAR s @@ [N/v]x))’
    by simp[cvsome_fresh, chap2Theory.NOT_IN_FV_SUB] THEN
  simp[]
QED

Theorem wh_csome:
  csome @@ x -w->* cvsome x
Proof
  simp[csome_def] >> FRESH_TAC >>
  `cvsome x = LAM n (LAM s (VAR s @@ x))` by simp[cvsome_fresh] >>
  ASM_SIMP_TAC (whfy(srw_ss())) []
QED

Theorem wh_cvsome:
  cvsome x @@ n @@ s -w->* s @@ x
Proof
  unvarify_tac whstar_substitutive >>
  Q_TAC (NEW_TAC "ns") ‘FV n ∪ {xs;ss}’ >>
  ‘cvsome (VAR xs) = LAM ns (LAM ss (VAR ss @@ VAR xs))’ by rw[cvsome_fresh] >>
  asm_simp_tac (whfy(srw_ss())) []
QED

val lameq_sym = List.nth(CONJUNCTS chap2Theory.lameq_rules, 2)
val cvcons_eq_ccons =
    wh_csome |> MATCH_MP (GEN_ALL head_reductionTheory.whstar_lameq)
             |> MATCH_MP lameq_sym
Theorem cvsome_cong:
  M1 == M2 ⇒ cvsome M1 == cvsome M2
Proof
  simp_tac (bsrw_ss()) [cvcons_eq_ccons]
QED


val _ = export_theory()
