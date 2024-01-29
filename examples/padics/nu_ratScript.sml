open HolKernel Parse boolLib bossLib;

open nu_natTheory ratTheory integerTheory fracTheory intExtensionTheory

val _ = new_theory "nu_rat";

val _ = temp_set_fixity "divides" (Infix(NONASSOC, 450))

Definition NU_FRAC_def:
  nufrac p f:int = if frac_nmr f = 0 then 0
                   else &(ν p (Num $ frac_nmr f)) - &(ν p (Num $ frac_dnm f))
End

Overload "ν"[local] = “nufrac”;

Theorem NUM_MULT:
  !a b. Num (a*b) = Num a * Num b
Proof
  Cases_on ‘a’ >> Cases_on ‘b’ >> rw[]
  >- simp[GSYM INT_NEG_RMUL]
  >- simp[GSYM INT_NEG_LMUL]
QED

Theorem NUM_EQ_0[simp]:
  Num x = 0 <=> x = 0
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem NU_FRAC_WELL_DEF:
  !p f1 f2. prime p ==> rat_equiv f1 f2 ==> ν p f1 = ν p f2
Proof
  rw[rat_equiv_def,NU_FRAC_def] >> rw[intLib.ARITH_PROVE “(i:int) - j = k - l <=> i+l = k+j”]
  >> pop_assum (mp_tac o AP_TERM “ν p o Num”)
  >> simp[NUM_MULT,NU_MULT] >> metis_tac [INT_ADD,arithmeticTheory.ADD_COMM]
QED

Theorem NU_FRAC_MUL:
  prime p /\ frac_nmr f1 <> 0 /\ frac_nmr f2 <> 0 ==> ν p (frac_mul f1 f2) = ν p f1 + ν p f2
Proof
  rw[frac_mul_def,NU_FRAC_def,NMR,INT_MUL_SIGN_CASES,FRAC_DNMPOS,DNM,NUM_MULT,NU_MULT]
  >> intLib.ARITH_TAC
QED

Definition NU_RAT_def:
  nu_rat p q = ν p (rep_rat q)
End

Theorem NU_RAT_MUL:
  prime p /\ q1 <> 0 /\ q2 <> 0 ==> nu_rat p (q1 * q2) = nu_rat p q1 + nu_rat p q2
Proof
  rw[NU_RAT_def, GSYM NU_FRAC_MUL,GSYM rat_nmr_def, GSYM RAT_EQ0_NMR] >> irule NU_FRAC_WELL_DEF >> simp[] >> rw[rat_equiv_rep_abs,rat_mul_def]
QED

Overload "ν" = “nu_rat”;

Theorem NU_RAT_0[simp]:
  ν p 0 = 0
Proof
  simp[NU_RAT_def,NU_FRAC_def,GSYM RAT_EQ0_NMR,GSYM rat_nmr_def]
QED

Theorem NU_RAT_1[simp]:
  ν p 1 = 0
Proof
  rw[NU_RAT_def,NU_FRAC_def]
  >> ‘∃j. 0<j ∧ rep_rat 1 = abs_frac (j,j)’ by metis_tac[rat_of_int_of_num,INT_MUL_RID,rep_rat_of_int]
  >> simp[NMR,DNM]
QED

Theorem NU_RAT_NEG1[simp]:
  prime p ==> ν p (-1) = 0
Proof
  strip_tac
  >> ‘1 = rat_minv 1’ by simp[GSYM RAT_MINV_1]
  >> ‘-rat_minv 1 = rat_minv (-1)’ by simp[RAT_AINV_MINV,RAT_1_NOT_0]
  >> ‘-1 <> 0’ by simp[]
  >> ‘1 = -1 * -1’ by metis_tac[RAT_MUL_RINV]
  >> ‘0 = ν p (-1) + ν p (-1)’ by metis_tac[NU_RAT_MUL,NU_RAT_1]
  >> ‘0 = 2 * ν p (-1)’ by (rewrite_tac[GSYM INT_DOUBLE] >> simp[])
  >> metis_tac[INT_ENTIRE, intLib.ARITH_PROVE “2:int≠0”]
QED

Theorem RAT_NEG:
  -r:rat = -1 * r
Proof
  ‘r+ -r = 0’ by simp[RAT_ADD_RINV]
  >> ‘1 * r + -1 * r = 0’ by simp[GSYM RAT_RDISTRIB,RAT_ADD_RINV]
  >> metis_tac[RAT_EQ_LADD,RAT_MUL_LID]
QED

Theorem NU_RAT_NEG[simp]:
  prime p ⇒ ν p (-n) = ν p n
Proof
  rw[]
  >> ‘-n = -1 * n’ by (once_rewrite_tac[RAT_NEG] >> simp[])
  >> Cases_on ‘n=0’
  >- simp[]
  >- (‘-1 ≠ 0’ by simp[]
      >> ‘ν p (-n) = ν p (-1) + ν p n’ by metis_tac[NU_RAT_MUL]
      >> rw[NU_RAT_NEG1]
     )
QED

Theorem NU_RAT_OF_NUM[simp]:
  prime p ⇒ ν p (rat_of_num n) = &ν p n
Proof
  strip_tac >> simp[NU_RAT_def]
  >> ‘∃j. 0<j ∧ rep_rat (&n) = abs_frac (j * (&n),j)’ by metis_tac[rep_rat_of_int,rat_of_int_of_num]
  >> ‘rat_equiv (rep_rat (&n)) (abs_frac (&n,1))’ by simp[rep_rat_of_int,rat_equiv_def,NMR,DNM,INT_MUL_COMM]
  >> ‘ν p (rep_rat (&n)) = ν p (abs_frac (&n,1))’ by simp[NU_FRAC_WELL_DEF]
  >> rw[NU_FRAC_def,NMR,DNM]
QED

Theorem RAT_EQUIV_RATND:
  rat_equiv (rep_rat r) (abs_frac (RATN r, &RATD r))
Proof
  simp[GSYM RAT_ABS_EQUIV,RAT,ABS_RATFRAC_RATND]
QED

Theorem NU_RAT_DIV:
  prime p ∧ a≠0 ∧ b≠0 ⇒ ν p (a/b) = ν p a - ν p b
Proof
  rw[] >> ‘ν p a = ν p (a/b * b)’ by simp[RAT_DIVMUL_CANCEL] >> ‘_ = ν p (a/b) + ν p b’ by simp[NU_RAT_MUL] >> intLib.ARITH_TAC
QED

Theorem NU_RAT_MINV:
  prime p ∧ r ≠ 0 ⇒ ν p (rat_minv r) = - ν p r
Proof
  simp[GSYM INT_RNEG_UNIQ,GSYM NU_RAT_MUL,RAT_MUL_RINV]
QED

Theorem NU_RAT_OF_INT[simp]:
  prime p ⇒ ν p (rat_of_int i) = &ν p (Num i)
Proof
  Cases_on ‘i’ >> simp[rat_of_int_ainv]
QED

Theorem NU_RAT_RATND:
  prime p ⇒ ν p (r:rat) = &(ν p (Num (RATN r))) - &(ν p (RATD r))
Proof
  rw[] >> ‘r = rat_of_int (RATN r) / &RATD r’ by simp[RATN_RATD_EQ_THM]
  >> Cases_on ‘r=0’
  >- simp[RATND_RAT_OF_NUM]
  >- metis_tac[RATN_EQ0,RATD_NZERO,NU_RAT_DIV,rat_of_int_11,rat_of_int_of_num,RAT_EQ_NUM_CALCULATE, NU_RAT_OF_INT,NU_RAT_OF_NUM]
QED

Theorem NUM_SUM:
  Num (a+b) = if SGN a = SGN b then Num a + Num b else ABS_DIFF (Num a) (Num b)
Proof
  Cases_on ‘a’ >> rw[]
  >- (gs[INT_POS,INT_SGN_CLAUSES,Once SGN_def] >> intLib.ARITH_TAC)
  >- (‘∃n. b = -&n’ by gs[NUM_NEGINT_EXISTS,INT_POS,INT_SGN_CLAUSES,Once SGN_def,INT_NOT_LT]
      >> rw[arithmeticTheory.ABS_DIFF_def,INT_ADD_CALCULATE])
  >- (‘∃n. b = -&n’ by gs[NUM_NEGINT_EXISTS,INT_POS,INT_SGN_CLAUSES,Once SGN_def,INT_NOT_LT]
      >> rw[INT_ADD_CALCULATE])
  >- (‘∃n. b = &n’ by gs[NUM_POSINT_EXISTS,INT_POS,INT_SGN_CLAUSES,Once SGN_def,INT_NOT_LT]
      >> rw[arithmeticTheory.ABS_DIFF_def,INT_ADD_CALCULATE])
QED

Theorem PULL_RAT_OF_INT:
  rat_of_int i * &n = rat_of_int (i * &n) ∧ &n * rat_of_int i = rat_of_int (&n*i) ∧ rat_of_int i * rat_of_int j = rat_of_int (i*j) ∧
  rat_of_int i + &n = rat_of_int (i + &n) ∧ &n + rat_of_int i = rat_of_int (&n+i) ∧ rat_of_int i + rat_of_int j = rat_of_int (i+j)
Proof
  simp[rat_of_int_MUL,rat_of_int_ADD] >> Cases_on ‘i’ >> simp[]
  >- simp[RAT_MUL_NUM_CALCULATE,INT_ADD,RAT_ADD_NUM_CALCULATE]
  >- simp[rat_of_int_ainv,GSYM INT_NEG_LMUL,GSYM INT_NEG_RMUL,GSYM RAT_AINV_LMUL,GSYM RAT_AINV_RMUL,RAT_MUL_NUM_CALCULATE,GSYM rat_of_int_ADD]
QED

Theorem SGN_OPP:
  ∀a b. a≠0 ∧ b≠0 ∧ SGN a ≠ SGN b ⇒ SGN a = - SGN b
Proof
  rw[] >> ‘(SGN a = 1 ∨ SGN a = -1) ∧ (SGN b = 1 ∨ SGN b = -1)’ by simp[INT_SGN_TOTAL,INT_SGN_CLAUSES,GSYM INT_NE_IMP_LTGT]
  >> gs[]
QED

Theorem NU_RAT_SUM:
  prime p ∧ a≠0 ∧ b≠0 ∧ a+b≠0 ⇒ int_min (ν p a) (ν p b) ≤ ν p (a+b)
Proof
  qabbrev_tac ‘an = RATN a’ >> qabbrev_tac ‘ad = RATD a’
  >> ‘a = rat_of_int an / &ad ∧ 0 < ad’ by metis_tac[RATND_THM]
  >> qabbrev_tac ‘bn = RATN b’ >> qabbrev_tac ‘bd = RATD b’ >> ‘b = rat_of_int bn / &bd ∧ 0<bd’ by metis_tac[RATND_THM]
  >> rw[NU_RAT_DIV,RAT_DIVDIV_ADD,NU_RAT_MUL,intLib.ARITH_PROVE “int_min x y ≤ z ⇔ x≤z ∨ y ≤ z”]
  >> simp[intLib.ARITH_PROVE “(x:int - y ≤ a - (y+z) ⇔ x+z≤a) ∧ (x - y ≤ a - (b+y) ⇔ x+b ≤ a)”]
  >> simp[PULL_RAT_OF_INT,INT_ADD]
  >> rw[NUM_SUM]
  >- (qspecl_then [‘p’,‘Num (an * &bd)’, ‘Num (bn * &ad)’] mp_tac NU_SUM >> simp[arithmeticTheory.MIN_LE,NUM_MULT,NU_MULT])
  >- (qspecl_then [‘p’,‘Num (an * &bd)’,‘Num (bn * &ad)’] mp_tac NU_ABS_DIFF >> simp[arithmeticTheory.MIN_LE,NUM_MULT,NU_MULT]
      >> ‘bd * Num an ≠ ad * Num bn’ by (
        ‘SGN an = - SGN bn’ by metis_tac[PULL_RAT_OF_INT,INT_SGN_MUL2,cj 3 INT_SGN_CLAUSES,INT_NZ_IMP_LT,iffRL arithmeticTheory.NOT_ZERO_LT_ZERO,INT_MUL_RID,SGN_OPP]
        >> ‘an * &bd ≠ - bn * &ad’ by metis_tac[PULL_RAT_OF_INT,rat_of_int_of_num,INT_LNEG_UNIQ,INT_NEG_LMUL]
        >> CCONTR_TAC >> gs[]
        >> ‘&bd * an * SGN an = &ad * bn * SGN bn’ by (once_rewrite_tac[GSYM INT_MUL_ASSOC] >> once_rewrite_tac[GSYM ABS_EQ_MUL_SGN] >> once_rewrite_tac[GSYM Num_EQ_ABS] >> simp[INT_MUL_CALCULATE])
        >> gs[GSYM INT_NEG_RMUL,INT_NEG_LMUL,INT_EQ_RMUL,INT_NOT0_SGNNOT0] >> gs[GSYM INT_NEG_LMUL,INT_NEG_EQ,INT_MUL_COMM]
        )
      >> simp[]
     )
QED

Theorem NU_RAT_DIFF:
  prime p ∧ a≠0 ∧ b≠0 ∧ a≠b ⇒ int_min (ν p a) (ν p b) ≤ ν p (a-b)
Proof
  rw[]
  >> ‘a + -b ≠ 0’ by simp[GSYM RAT_SUB_ADDAINV,RAT_EQ_SUB0]
  >> ‘int_min (ν p a) (ν p (-b)) ≤ ν p (a + (-b))’ by simp[NU_RAT_SUM,INT_NEG_EQ0]
  >> gs[RAT_SUB_ADDAINV]
QED

Overload exp[local] = “rat_exp”

Theorem NU_RAT_EXP:
  prime p ⇒ ν p (exp (&p) i) = i
Proof
  rw[] >> ‘&p ≠ 0’ by (simp[] >> metis_tac[dividesTheory.NOT_PRIME_0])
  >> Cases_on ‘i’
  >> simp[RAT_EXP_CALCULATE,NU_RAT_MINV,RAT_EXPN_R_NONZERO]
  >> pop_assum kall_tac
  >> Induct_on ‘n’
  >> simp[rat_expn_def,NU_RAT_MUL,RAT_EXPN_R_NONZERO,NU_P_P,
          dividesTheory.ONE_LT_PRIME,INT_ADD_CALCULATE]
QED

Theorem NU_RAT_P_DIV:
  prime p ∧ r≠0 ⇒ ∃q. ν p q = 0 ∧ r = q * (exp (&p) (ν p r))
Proof
  rw[] >> qexists_tac ‘r / (exp (&p) (ν p r))’
  >> ‘&p ≠ 0’ by (simp[] >>  metis_tac[dividesTheory.NOT_PRIME_0])
  >> simp[RAT_DIVMUL_CANCEL,RAT_EXP_R_NONZERO,NU_RAT_DIV,NU_RAT_EXP]
QED

Theorem NU_RAT_SUM_NEQ:
  prime p ∧ a≠0 ∧ b≠0 ∧ ν p a ≠ ν p b ⇒ int_min (ν p a) (ν p b) = ν p (a+b)
Proof
  rw[]
  >> qabbrev_tac ‘an = RATN a’ >> qabbrev_tac ‘ad = RATD a’
  >> qabbrev_tac ‘bn = RATN b’ >> qabbrev_tac ‘bd = RATD b’
  >> ‘a = rat_of_int an / &ad ∧ b = rat_of_int bn / &bd ∧ 0 < ad ∧ 0 < bd’ by metis_tac[RATND_THM]
  >> ‘a+b ≠ 0 ∧ a≠b’ by metis_tac[NU_RAT_NEG,RAT_ADD_RINV,RAT_EQ_LADD]
  >> ‘&ad ≠ 0 ∧ &bd ≠ 0’ by simp[RAT_EQ_NUM_CALCULATE]
  >> ‘rat_of_int an ≠ 0 ∧ rat_of_int bn ≠ 0’ by (simp[rat_of_int_11] >> metis_tac[RATN_EQ0])
  >> ‘rat_of_int an / &ad + rat_of_int bn / &bd = rat_of_int (an * &bd + bn * &ad) / &(ad * bd)’ by
    simp[RAT_DIVDIV_ADD,PULL_RAT_OF_INT,RAT_MUL_NUM_CALCULATE]
  >> ‘rat_of_int (an * &bd + bn * &ad) ≠ 0’ by metis_tac[RAT_DIVDIV_ADD,RAT_DIV_0]
  >> ‘&(ad * bd) ≠ 0’ by simp[RAT_MUL_NUM_CALCULATE]
  >> ‘an ≠ 0 ∧ bn ≠ 0’ by metis_tac[RATN_EQ0]
  >> ‘int_of_num (ν p (Num an)) + &ν p bd ≠ &ν p (Num bn) + &ν p ad’ by
    metis_tac[NU_RAT_OF_INT,NUM_OF_INT,rat_of_int_of_num,NU_RAT_DIV,intLib.ARITH_PROVE “a-b=c-d:int ⇔ a+d=c+b”]
  >> ‘ν p (Num (an * &bd)) ≠ ν p (Num (bn * &ad))’ by
    (simp[NUM_MULT,NU_MULT,NUM_EQ_0] >> metis_tac[INT_ADD,INT_ADD_COMM])
  >> ‘Num (an * &bd) ≠ 0 ∧ Num (bn * &bd) ≠ 0’ by simp[NUM_EQ_0]
  >> rw[RAT_DIVDIV_ADD,NU_RAT_DIV,NU_MULT,GSYM INT_ADD_CALCULATE,NUM_SUM]
  >> (simp[GSYM NU_ABS_DIFF_NEQ,GSYM NU_SUM_NEQ,NUM_MULT,NU_MULT] >> once_rewrite_tac[GSYM INT_MIN_NUM] >> intLib.ARITH_TAC)
QED

Theorem RAT_DIV_MUL:
  b≠0 ∧ c≠0 ⇒ a / (b*c) = a / b / c
Proof
  simp[RAT_DIV_MULMINV,RAT_MINV_MUL,RAT_MUL_ASSOC]
QED

Theorem RATND_COPRIME:
  d divides (Num $ RATN r) ∧ d divides RATD r ⇒ d=1
Proof
  rw[] >> qabbrev_tac ‘rn = RATN r’ >> qabbrev_tac ‘rd = RATD r’ >> Cases_on ‘r = 0’ >- (metis_tac[dividesTheory.DIVIDES_ONE,RATND_THM,RATN_EQ0])
  >- (
  ‘d≠0’ by metis_tac[dividesTheory.ZERO_DIVIDES,RATD_NZERO]
  >> ‘r = rat_of_int rn / &rd’ by metis_tac[RATND_THM]
  >> ‘∃n. Num rn = n * d’ by simp[GSYM dividesTheory.divides_def]
  >> ‘∃qn. rn = qn * &d’ by (Cases_on ‘rn’
                           >- (qexists_tac ‘&n’ >> gs[NUM_OF_INT])
                           >- (qexists_tac ‘-&n’ >> gs[NUM_OF_NEG_INT] >> simp[INT_MUL_CALCULATE])
                           >- (qexists_tac ‘0’ >> simp[])
                            )
  >> ‘∃nd. rd = nd * d’ by simp[GSYM dividesTheory.divides_def]
  >> ‘nd ≠ 0’ by metis_tac[arithmeticTheory.MULT_EQ_0,RATD_NZERO]
  >> ‘∃qd. &rd:int = qd * &d’ by (qexists_tac ‘&nd’ >> simp[INT_MUL_CALCULATE])
  >> ‘rn / &d = qn ∧ rd DIV d = nd’ by (conj_tac
                                        >- simp[INT_DIV_RMUL]
                                        >- metis_tac[arithmeticTheory.MULT_COMM, arithmeticTheory.MULT_DIV,arithmeticTheory.NOT_ZERO_LT_ZERO]
                                       )
  >> ‘r = rat_of_int qn / &nd’ by (simp[GSYM PULL_RAT_OF_INT,GSYM RAT_MUL_NUM_CALCULATE,Once RAT_MUL_COMM] >> simp[GSYM RAT_DIVDIV_MUL])
  >> ‘0<nd’ by simp[]
  >> ‘Num rn = Num qn * d’ by metis_tac[GSYM NUM_MULT,NUM_OF_INT]
  >> ‘Num rn ≤ Num qn’ by metis_tac[RATN_LEAST,Num_EQ_ABS,INT_LE]
  >> ‘rn ≠ 0’ by metis_tac[RATN_EQ0]
  >> ‘Num qn ≠ 0’ by (metis_tac[NUM_EQ_0,INT_ENTIRE])
  >> ‘d≤1’ by metis_tac[arithmeticTheory.LE_MULT_CANCEL_RBARE]
  >> simp[]
  )
QED

Theorem NU_RAT_EQ_0:
  prime p ∧ ν p r = 0 ∧ r≠0 ⇒
  ~(p divides (Num $ RATN r)) ∧ ~(p divides (RATD r))
Proof
  rpt strip_tac >> ‘r = rat_of_int (RATN r) / &RATD r’ by simp[RATND_THM]
  >> ‘ν p (Num (RATN r)) = ν p (RATD r)’
    by metis_tac[INT_SUB_0,NU_RAT_RATND,INT_INJ]
  >- (‘1 ≤ ν p (Num (RATN r))’
        by (irule (iffRL NU_DIVIDES) >> simp[dividesTheory.ONE_LT_PRIME])
      >> ‘p divides RATD r’
        by metis_tac[NU_SUC,arithmeticTheory.num_CASES, DECIDE “1≤n:num ⇒ n≠0”]
      >> ‘p=1’ by metis_tac[RATND_COPRIME]
      >> metis_tac[dividesTheory.ONE_LT_PRIME,DECIDE “~(1<1:num)”])
  >- (‘1 ≤ ν p (RATD r)’
        by (irule (iffRL NU_DIVIDES) >> simp[dividesTheory.ONE_LT_PRIME])
      >> ‘p divides (Num (RATN r))’
        by metis_tac[NU_SUC,arithmeticTheory.num_CASES, DECIDE “1≤n:num ⇒ n≠0”]
      >> ‘p=1’ by metis_tac[RATND_COPRIME]
      >> metis_tac[dividesTheory.ONE_LT_PRIME,DECIDE “~(1<1:num)”])
QED

Theorem NU_RAT_CASES:
  prime p ∧ r≠0 ⇒
  (0 ≤ ν p r ⇒ &ν p (Num (RATN r)) = ν p r ∧ ν p (RATD r) = 0) ∧
  (ν p r ≤ 0 ⇒ -&ν p (RATD r) = ν p r ∧ ν p (Num (RATN r)) = 0)
Proof
  strip_tac
  >> ‘ν p r = &ν p (Num (RATN r)) - &ν p (RATD r)’
    by simp[NU_RAT_RATND]
  >> ‘~(p divides Num (RATN r) ∧ p divides RATD r)’
    by metis_tac[RATND_COPRIME,dividesTheory.ONE_LT_PRIME,DECIDE “~(1<1:num)”]
  >> ‘ν p (Num (RATN r)) = 0 ∨ ν p (RATD r) = 0’
    by metis_tac[NU_POS,dividesTheory.ONE_LT_PRIME,RATN_EQ0,NUM_EQ_0,
                 arithmeticTheory.NOT_LT_ZERO_EQ_ZERO,RATD_NZERO]
  >> gs[]
QED

val _ = export_theory();
