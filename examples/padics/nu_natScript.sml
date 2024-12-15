open HolKernel Parse boolLib bossLib;

val _ = new_theory "nu_nat";

open arithmeticTheory dividesTheory gcdTheory;

val _ = temp_set_fixity "divides" (Infix(NONASSOC, 450));

Definition NU_def:
  (nu 0 n = 0) ∧
  (nu 1 n = 0) ∧
  (nu p 0 = 0) ∧
  (nu p n = if p divides n then 1 + nu p (n DIV p) else 0)
End

Overload "ν" = “nu”;

Theorem NU_thm:
  ν p n = if p≤1 ∨ n=0 then 0
          else if p divides n then 1 + ν p (n DIV p)
          else 0
Proof
  Cases_on ‘p’
  >-(rw[NU_def])
  >-(Cases_on ‘n’
     >- simp[NU_def]
     >- rw[NU_def]
    )
QED

Theorem NU_P_ONE[simp]:
  ∀p. nu p 1 = 0
Proof
  once_rewrite_tac[NU_thm] >> simp[]
QED

Theorem NU_P_ZERO[simp]:
  ∀p. ν p 0 = 0
Proof
  once_rewrite_tac[NU_thm] >> simp[]
QED

Theorem NU_P_P[simp]:
  ∀p. 1<p ⇒ ν p p = 1
Proof
  once_rewrite_tac[NU_thm] >> simp[]
QED

Theorem NU_TRIV[simp]:
  ∀p n. p≤1 ⇒ ν p n = 0
Proof
  once_rewrite_tac[NU_thm] >> simp[]
QED

Theorem NU_NON_TRIVIAL:
  ∀p n. 1<p ∧ n≠0 ⇒ ν p n = if p divides n then 1 + nu p (n DIV p) else 0
Proof
  rw[] >> metis_tac[NU_thm,ADD_SYM,DECIDE “1<p ⇒ ~(p≤1)”]
QED

Theorem NU_NOT_DIV[simp]:
  ∀p n. ~(p divides n) ⇒ nu p n = 0
Proof
  once_rewrite_tac[NU_thm] >> simp[]
QED

Theorem NU_SUC:
  ∀p n v. ν p n = SUC v ⇒ p divides n ∧ ν p (n DIV p) = v
Proof
  rw[]
  >- (spose_not_then strip_assume_tac >> ‘ν p n = 0’ by metis_tac[NU_NOT_DIV] >>
      rw[])
  >- (‘p divides n’
        by (spose_not_then strip_assume_tac >>
            ‘ν p n = 0’ by metis_tac[NU_NOT_DIV] >> rw[])
      >> ‘1<p’ by (spose_not_then strip_assume_tac >> gs[NU_NON_TRIVIAL])
      >> ‘n≠0’ by (spose_not_then strip_assume_tac >> gs[NU_P_ZERO])
      >> ‘ν p n = 1 + ν p (n DIV p)’ by metis_tac[NU_NON_TRIVIAL]
      >> rw[]
     )
QED

Theorem NU_POS:
  ∀p n. 1<p ∧ n≠0 ⇒ (0 < ν p n ⇔ p divides n)
Proof
  rpt strip_tac >> iff_tac
  >- metis_tac[num_CASES,DECIDE “~(0<0:num)”,NU_SUC]
  >- (once_rewrite_tac[NU_thm] >> simp[])
QED

Theorem NU_DIVIDES:
  ∀p n k. 1 < p ∧ n ≠ 0 ⇒ (k ≤ ν p n ⇔ (p ** k) divides n)
Proof
  rpt strip_tac >> iff_tac
  >- (‘(p ** ν p n) divides n’
        suffices_by metis_tac[EXP_DIVIDES,DIVIDES_TRANS, DECIDE “1<p ⇒ p≠0”]
      >> Induct_on ‘ν p n’
      >- rw[]
      >- (rpt strip_tac
          >> rw[NU_SUC]
          >> ‘ν p (n DIV p) = v’ by rw[NU_SUC]
          >> ‘p divides n’ by metis_tac[NU_SUC]
          >> ‘n DIV p ≠ 0’ by metis_tac[DIVIDES_LEQ_OR_ZERO,DIV_EQ_0,NOT_LESS]
          >> ‘p ** (ν p (n DIV p)) divides (n DIV p)’ by simp[]
          >> ‘p ** (ν p (n DIV p) + 1) = p * p ** (ν p (n DIV p))’
            by simp[GSYM EXP, GSYM ADD1]
          >> ‘p ** ν p n = p * p ** ν p (n DIV p)’
            by metis_tac[NU_NON_TRIVIAL,NU_SUC,ADD_COMM]
          >> ‘n = p * (n DIV p)’
            by metis_tac[DIVIDES_DIV,NU_SUC, DECIDE “1<p ⇒ 0<p”]
          >> metis_tac[DIVIDES_COMMON_MULT_I]))
  >-(‘~(p ** (SUC (ν p n)) divides n)’
       by (Induct_on ‘ν p n’
           >- (rw[] >> CCONTR_TAC >>
               ‘ν p n ≠ 0’
                 by metis_tac[NU_thm, DECIDE “1 < p ⇒ ~(p≤1)”, SUC_NOT,
                              GSYM SUC_ONE_ADD])
           >- (rpt strip_tac
               >> ‘p divides n’ by metis_tac[NU_SUC]
               >> ‘n = p * (n DIV p)’
                 by metis_tac[DIVIDES_DIV, DECIDE “1 < p ⇒ 0 < p”]
               >> ‘ν p (n DIV p) = v’ by metis_tac[NU_SUC]
               >> ‘ν p n = 1 + ν p (n DIV p)’ by metis_tac[NU_NON_TRIVIAL]
               >> ‘p * p ** SUC (ν p (n DIV p)) divides p * (n DIV p)’
                 by metis_tac[EXP,ADD1,ADD_COMM]
               >> ‘p ** SUC (ν p (n DIV p)) divides n DIV p’
                 by metis_tac[DIVIDES_MULT_LCANCEL, DECIDE “1 < p ⇒ p ≠0”]
               >> ‘n DIV p ≠ 0’
                 by metis_tac[DIVIDES_LEQ_OR_ZERO,DIV_EQ_0,NOT_LESS]
               >> metis_tac[]))
     >> (once_rewrite_tac[MONO_NOT_EQ] >> rw[NOT_LESS_EQUAL] >> CCONTR_TAC
         >> ‘∃r. k = ν p n + SUC r’ by metis_tac[LESS_ADD_1,ADD1] >> rw[]
         >> Induct_on ‘r’
         >- (disch_then kall_tac >> rw[] >> CCONTR_TAC >> metis_tac[ADD1,ONE])
         >- (disch_then kall_tac >> gs[] >> CCONTR_TAC
             >> ‘p ** (ν p n + SUC r) divides p ** (ν p n + SUC (SUC r))’
               by metis_tac[DECIDE “a + b ≤ a + SUC b”, EXP_DIVIDES,
                            DECIDE “1 < p ⇒ p ≠ 0”]
             >> ‘p ** (ν p n + SUC r) divides n’
               by metis_tac[DIVIDES_TRANS, ADD_COMM]
             >> metis_tac[DECIDE “a < a + SUC b”,ADD_COMM]
          )
        )
    )
QED

Theorem NU_MULT:
  ∀p a b. a ≠ 0 ∧ b ≠ 0 ∧ prime p ⇒ ν p (a * b) = ν p a + ν p b
Proof
  rw[]
  >> ‘1 < p’ by metis_tac[ONE_LT_PRIME]
  >> ‘p ** (ν p a) divides a ∧ p ** (ν p b) divides b’
    by metis_tac[NU_DIVIDES, LESS_EQ_REFL]
  >> ‘~(p ** SUC (ν p a) divides a) ∧ ~(p ** SUC (ν p b) divides b)’
    by metis_tac[NU_DIVIDES, DECIDE “~(SUC a ≤ a)”]
  >> ‘p ** (ν p a + ν p b) divides (a*b)’ by metis_tac[DIVIDES_PROD,EXP_ADD]
  >> ‘ν p a + ν p b ≤ ν p (a*b)’
    by metis_tac[DIVIDES_PROD,EXP_ADD,NU_DIVIDES,MULT_EQ_0]
  >> ‘~(p ** SUC (ν p a + ν p b) divides a*b)’
    by (CCONTR_TAC
        >> ‘a = p ** (ν p a) * (a DIV (p ** (ν p a))) ∧
            b = p ** (ν p b) * (b DIV (p ** (ν p b)))’
          by metis_tac[DIVIDES_DIV, DECIDE “1<p ⇒ 0<p”, ZERO_LT_EXP]
        >> ‘a * b = (a DIV (p ** (ν p a))) * (b DIV (p ** (ν p b))) *
                    p ** (ν p a) * p ** (ν p b)’
          by metis_tac[MULT_COMM,MULT_ASSOC]
        >> ‘a * b = ((a DIV (p ** (ν p a))) * (b DIV (p ** (ν p b)))) *
                    p ** (ν p a + ν p b)’
          by metis_tac[EXP_ADD,MULT_ASSOC]
        >> ‘p * p ** (ν p a + ν p b) divides
               (a DIV (p ** (ν p a))) * (b DIV (p ** (ν p b))) *
               p ** (ν p a + ν p b)’ by metis_tac[EXP]
        >> ‘p ** (ν p a + ν p b) ≠ 0’
          by metis_tac[PRIME_POS,ZERO_LT_EXP, NOT_ZERO_LT_ZERO]
        >> ‘p divides (a DIV (p ** (ν p a))) * (b DIV (p ** (ν p b)))’
          by metis_tac[DIVIDES_MULT_RCANCEL,PRIME_POS,ZERO_LT_EXP,
                       NOT_ZERO_LT_ZERO]
        >> ‘p divides (a DIV (p ** (ν p a))) ∨ p divides (b DIV (p ** (ν p b)))’
          by metis_tac[P_EUCLIDES]
        >> metis_tac[DIVIDES_COMMON_MULT_I,DIVIDES_DIV,PRIME_POS,ZERO_LT_EXP,
                     ADD1,MULT_COMM,EXP])
  >> metis_tac[EQ_LESS_EQ,MULT_EQ_0,NOT_LESS,NU_DIVIDES,LESS_EQ_IFF_LESS_SUC]
QED

Theorem NU_SUM:
  ∀p a b. a ≠ 0 ∧ b ≠ 0 ∧ prime p ⇒ MIN (ν p a) (ν p b) ≤ ν p (a+b)
Proof
  rw[] >> ‘a+b ≠ 0’ by rw[ADD_EQ_0] >>  wlog_tac ‘ν p a ≤ ν p b’ [‘a’,‘b’]
  >- (‘ν p b ≤ ν p a’ by simp[] >> metis_tac[ADD_COMM])
  >- (‘ν p a ≤ ν p (a+b)’ suffices_by rw[]
      >> metis_tac[NU_DIVIDES, DECIDE “a≤a”, DIVIDES_ADD_1, ONE_LT_PRIME])
QED

Theorem NU_SUM_NEQ:
  ∀p a b. a ≠ 0 ∧ b ≠ 0 ∧ prime p ∧ ν p a ≠ ν p b ⇒
          MIN (ν p a) (ν p b) = ν p (a+b)
Proof
  rw[] >> ‘1<p’ by simp[ONE_LT_PRIME] >> wlog_tac ‘ν p a < ν p b’ [‘a’, ‘b’]
  >-(‘ν p b < ν p a’ by simp[LESS_CASES_IMP]
     >> ‘MIN (ν p b) (ν p a) = ν p (b+a)’ by simp[]
     >> metis_tac[MIN_COMM,ADD_COMM]
    )
  >-(simp[MIN_DEF]
     >> ‘p ** ν p a divides a ∧ p ** ν p a divides b’ by simp[GSYM NU_DIVIDES]
     >> ‘~(p ** (ν p a + 1) divides a)’ by simp[GSYM NU_DIVIDES]
     >> ‘p ** (ν p a + 1) divides b’ by simp[GSYM NU_DIVIDES]
     >> ‘~(p ** (ν p a + 1) divides (a+b))’ by (CCONTR_TAC >> metis_tac[DIVIDES_ADD_2,ADD_COMM])
     >> ‘p ** ν p a divides (a+b)’ by metis_tac[DIVIDES_ADD_1]
     >> ‘ν p a ≤ ν p (a+b)’ by simp[NU_DIVIDES]
     >> ‘~(ν p a + 1 ≤ ν p (a+b))’ by simp[NU_DIVIDES]
     >> ‘ν p (a+b) ≤ ν p a’ by simp[NOT_SUC_LESS_EQ,ADD1]
     >> simp[NU_DIVIDES,NOT_SUC_LESS_EQ,ADD1]
    )
QED

Theorem NU_ABS_DIFF:
  ∀p a b. prime p ∧ a≠0 ∧ b≠0 ∧ a≠b ⇒ MIN (ν p a) (ν p b) ≤ ν p (ABS_DIFF a b)
Proof
  rpt strip_tac >> irule (iffRL NU_DIVIDES) >> simp[ABS_DIFF_EQ_0,ONE_LT_PRIME]
  >> ‘p ** MIN (ν p a) (ν p b) divides a ∧ p ** MIN (ν p a) (ν p b) divides b’
    by (conj_tac >> irule (iffLR NU_DIVIDES) >>
        simp[ONE_LT_PRIME,MIN_LE,LESS_EQ_REFL])
  >> rw[ABS_DIFF_def,DIVIDES_SUB]
QED

Theorem NU_ABS_DIFF_NEQ:
  ∀p a b. prime p ∧ a≠0 ∧ b≠0 ∧ ν p a ≠ ν p b ⇒
          MIN (ν p a) (ν p b) = ν p (ABS_DIFF a b)
Proof
  rpt strip_tac >> ‘1<p’ by simp[ONE_LT_PRIME]
  >> wlog_tac ‘ν p a < ν p b’ [‘a’,‘b’]
  >- (‘ν p b < ν p a’ by simp[LESS_CASES_IMP] >>
      metis_tac[ABS_DIFF_COMM,MIN_COMM])
  >- (‘p ** ν p a divides a ∧ p ** ν p a divides b’ by simp[GSYM NU_DIVIDES]
      >> ‘~(p ** (ν p a + 1) divides a)’ by simp[GSYM NU_DIVIDES]
      >> ‘p ** (ν p a + 1) divides b’ by simp[GSYM NU_DIVIDES]
      >> ‘~(p ** (ν p a + 1) divides (ABS_DIFF a b))’
        by (rw[ABS_DIFF_def] >> CCONTR_TAC
            >> metis_tac[DIVIDES_SUB,DIVIDES_ADD_1,
                         DECIDE “a<b ⇒ a = b - (b - a)”,
                         DECIDE “~(a<b) ⇒ b + (a - b) = a”])
      >> ‘p ** ν p a divides (ABS_DIFF a b)’ by (rw[ABS_DIFF_def,DIVIDES_SUB])
      >> ‘ABS_DIFF a b ≠ 0’
        by (rw[ABS_DIFF_def,NOT_LESS_EQUAL] >> metis_tac[LESS_CASES_IMP])
      >> ‘ν p a ≤ ν p (ABS_DIFF a b)’ by simp[NU_DIVIDES]
      >> ‘~(ν p a + 1 ≤ ν p (ABS_DIFF a b))’ by simp[NU_DIVIDES]
      >> ‘ν p (ABS_DIFF a b) ≤ ν p a’ by simp[NOT_SUC_LESS_EQ,ADD1]
      >> simp[MIN_DEF])
QED

val _ = export_theory();
