open HolKernel Parse boolLib bossLib;

open nu_ratTheory ratTheory metricTheory real_of_ratTheory realTheory;

val _ = new_theory "padic_metric";

val _ = augment_srw_ss [
    rewrites[REAL_OF_RAT_NUM_CLAUSES,REAL_OF_RAT_ADD,REAL_OF_RAT_MUL]
  ]

Definition padic_abs_def:
  padic_abs p (r:rat) = if p=0 ∨ r=0 then 0 else real_of_rat ((&p) ** (- ν p r))
End

Overload "abs" = “padic_abs”

Definition padic_dist:
  padic_dist p (r,q) = padic_abs p (r-q)
End

Theorem PADIC_ABS_EQ_0:
  ∀p r. p≠0 ⇒ (abs p r = 0 ⇔ r = 0)
Proof
  rw[EQ_IMP_THM,padic_abs_def] >> irule RAT_EXP_R_NONZERO >> simp[]
QED

Theorem PADIC_ABS_POS:
  ∀p r. 0<p ⇒ 0 ≤ abs p r
Proof
  rw[padic_abs_def] >> irule RAT_LES_IMP_LEQ >> irule RAT_EXP_R_POS >> simp[]
QED

Theorem PADIC_ABS_MUL:
  ∀p r q. prime p ⇒ abs p (r*q) = abs p r * abs p q
Proof
  rw[] >> Cases_on ‘r*q=0’
  >- (‘r=0 ∨ q=0’ by metis_tac[RAT_NO_ZERODIV] >> simp[padic_abs_def])
  >- (simp[padic_abs_def]
      >> ‘p≠0’ by metis_tac[dividesTheory.NOT_PRIME_0]
      >> ‘r≠0 ∧ q≠0’ by simp[GSYM RAT_NO_ZERODIV_NEG]
      >> simp[NU_RAT_MUL,GSYM RAT_EXP_ADD,integerTheory.INT_NEG_ADD]
     )
QED

Theorem PADIC_ABS_NEG:
  ∀p r. prime p ⇒ abs p (-r) = abs p r
Proof
  simp[padic_abs_def,NU_RAT_NEG]
QED

Theorem RAT_MAX_REF[simp]:
  ∀r. rat_max r r = r
Proof
  simp[rat_max_def]
QED

Theorem RAT_MAX_SYM:
  ∀r1 r2. rat_max r1 r2 = rat_max r2 r1
Proof
  rw[rat_max_def]
  >- gs[RAT_LES_ANTISYM,rat_gre_def]
  >- gs[rat_gre_def,RAT_LEQ_LES,RAT_LEQ_ANTISYM]
QED

Theorem RAT_MAX_ADD:
  ∀r1 r2 r3. rat_max (r1 + r3) (r2+r3) = rat_max r1 r2 + r3
Proof
  rw[rat_max_def] >> gs[RAT_LES_RADD,rat_gre_def]
QED

Theorem RAT_MIN_REF[simp]:
  ∀r. rat_min r r = r
Proof
  simp[rat_min_def]
QED

Theorem RAT_MIN_SYM:
  ∀r1 r2. rat_min r1 r2 = rat_min r2 r1
Proof
  rw[rat_min_def] >> gs[RAT_LES_ANTISYM,RAT_LEQ_LES,RAT_LEQ_ANTISYM]
QED

Theorem RAT_MAX_NEG:
  ∀r1 r2. rat_max (-r1) (-r2) = -(rat_min r1 r2)
Proof
  rw[rat_max_def,rat_min_def,rat_gre_def,RAT_LES_AINV]
QED

Theorem RAT_MAX_LEQ:
  ∀r1 r2. r1 ≤ rat_max r1 r2 ∧ r2 ≤ rat_max r1 r2
Proof
  rw[rat_max_def] >> gs[rat_gre_def,RAT_LEQ_LES] >>
  simp[RAT_LEQ_REF,RAT_LES_IMP_LEQ]
QED

Theorem PADIC_ABS_ULTRAMETRIC:
  ∀p r q. prime p ⇒ abs p (r+q) ≤ max (abs p r) (abs p q)
Proof
  rw[padic_abs_def,NU_RAT_SUM,dividesTheory.NOT_PRIME_0,REAL_OF_RAT_MAX,
     REAL_OF_RAT_LE,REAL_MAX_REFL]
  >> ‘0 < rat_of_num p’
    by (simp[] >> metis_tac[dividesTheory.ONE_LT_PRIME,DECIDE “0:num<1”,
                            arithmeticTheory.LESS_TRANS])
  >- metis_tac[RAT_MAX_LEQ,RAT_LEQ_TRANS,RAT_EXP_R_POS,RAT_LES_IMP_LEQ]
  >- gs[]
  >- (simp[] >> once_rewrite_tac[GSYM REAL_OF_RAT_0] >>
      simp[RAT_MAX_LEQ,REAL_OF_RAT_MAX,REAL_OF_RAT_LE])
  >- (once_rewrite_tac[GSYM REAL_OF_RAT_0] >>
      simp[REAL_OF_RAT_MAX,RAT_MAX_LEQ,REAL_OF_RAT_LE])
  >- (gs[] >> ‘int_min (ν p r) (ν p q) ≤ ν p (r+q)’ by simp[NU_RAT_SUM]
      >> ‘ν p r ≤ ν p (r+q) ∨ ν p q ≤ ν p (r+q)’
        by metis_tac[integerTheory.INT_MIN]
      >- (‘-ν p (r+q) ≤ -ν p r’ by simp[integerTheory.INT_LE_NEG]
          >> ‘&p ** (-ν p (r+q)) ≤ &p ** (-ν p r)’
            by simp[RAT_EXP_LE,dividesTheory.ONE_LT_PRIME,RAT_OF_NUM_LES]
          >> metis_tac[RAT_MAX_LEQ,RAT_LEQ_TRANS]
         )
      >-(‘- ν p (r+q) ≤ -ν p q’ by metis_tac[integerTheory.INT_LE_NEG]
         >> ‘&p ** -ν p (r+q) ≤ &p ** -ν p q’
           by simp[RAT_EXP_LE,dividesTheory.ONE_LT_PRIME]
         >> metis_tac[RAT_MAX_LEQ,RAT_LEQ_TRANS]
        )
     )
QED

Theorem PADIC_ABS_TRIANGLE:
  ∀p r q. prime p ⇒ abs p (r+q) ≤ abs p r + abs p q
Proof
  rw[]
  >> ‘0≤abs p r ∧ 0≤abs p q’
    by metis_tac[PADIC_ABS_POS,dividesTheory.NOT_PRIME_0,
                 GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> ‘max (abs p r) (abs p q) ≤ abs p r + abs p q’ by simp[REAL_MAX_LE]
  >> metis_tac[PADIC_ABS_ULTRAMETRIC,REAL_LE_TRANS]
QED

Theorem PADIC_ABS_ULTRAMETRIC_NEQ:
  ∀p r q. prime p ∧ abs p r ≠ abs p q ⇒
          abs p (r+q) = max (abs p r) (abs p q)
Proof
  rpt strip_tac
  >> ‘p≠0 ∧ 0<p’ by metis_tac[dividesTheory.NOT_PRIME_0,arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> ‘r+q≠0’ by (‘r≠-q’ suffices_by metis_tac[RAT_ADD_LINV,RAT_EQ_RADD]
                 >> metis_tac[PADIC_ABS_NEG]
                )
  >> wlog_tac ‘abs p r < abs p q’ [‘q’,‘r’]
  >-(gs[REAL_NOT_LT,REAL_LE_LT] >> metis_tac[cj 1 REAL_MAX_ACI,RAT_ADD_COMM])
  >-(‘q≠0’ by (‘0 < abs p q’ suffices_by metis_tac[padic_abs_def,REAL_LT_IMP_NE]
               >> metis_tac[REAL_LET_TRANS,PADIC_ABS_POS]
              )
     >> ‘&p≠1’ by metis_tac[dividesTheory.ONE_LT_PRIME,prim_recTheory.LESS_NOT_EQ,REAL_INJ]
     >> ‘&p≠-1’ by metis_tac[eq_ints]
     >> ‘&p≠0’ by simp[]
     >> simp[max_def,REAL_LT_IMP_LE]
     >> Cases_on ‘r=0’
     >> simp[padic_abs_def,REAL_OF_RAT_INJ]
     >> gs[padic_abs_def,REAL_OF_RAT_LT,RAT_EXP_LT2,dividesTheory.ONE_LT_PRIME,REAL_LT,integerTheory.INT_LT_NEG]
     >> simp[RAT_EXP_INJ,GSYM NU_RAT_SUM_NEQ,integerTheory.INT_LT_IMP_NE,integerTheory.INT_MIN,integerTheory.INT_LT_GT]
    )
QED

Theorem PADIC_DIST_ISMET:
  prime p ⇒ ismet (padic_dist p)
Proof
  rw[] >> ‘p≠0’ by metis_tac[dividesTheory.NOT_PRIME_0]
  >> simp[ismet,padic_dist,PADIC_ABS_EQ_0,RAT_EQ_SUB0]
  >> rw[]
  >> ‘abs p ((y-x) + (x-z)) ≤ abs p (y-x) + abs p (x-z)’ by simp[PADIC_ABS_TRIANGLE]
  >> ‘(y-x)+(x-z)=y-z’ by metis_tac[RAT_SUB_ADDAINV, RAT_ADD_ASSOC,RAT_ADD_LINV,RAT_ADD_LID]
  >> metis_tac[PADIC_ABS_NEG,RAT_AINV_SUB]
QED

Definition padic_met_def:
  padic_met p = metric (padic_dist p)
End

Theorem PADIC_DIST_POS:
  ∀p r q. prime p ⇒ 0 ≤ padic_dist p (r,q)
Proof
  metis_tac[METRIC_POS,metric_tybij,PADIC_DIST_ISMET]
QED

Theorem PADIC_DIST_SYM:
  ∀p r q. prime p ⇒ padic_dist p (r,q) = padic_dist p (q,r)
Proof
  metis_tac[METRIC_SYM,metric_tybij,PADIC_DIST_ISMET]
QED

Theorem PADIC_MET_DIST:
  prime p ⇒ dist (padic_met p) = padic_dist p
Proof
  rw[PADIC_DIST_ISMET,iffLR $ cj 2 metric_tybij,padic_met_def]
QED

Theorem PADIC_DIST_FROM_0:
  prime p ⇒ dist (padic_met p) (x,0) = abs p x
Proof
  simp[PADIC_MET_DIST,padic_dist]
QED

Theorem PADIC_DIST_ULTRAMETRIC:
  prime p ⇒ padic_dist p (r,q) ≤ max (padic_dist p (r,s)) (padic_dist p (s,q))
Proof
  rw[padic_dist]
  >> ‘r-q = (r-s) + (s-q)’ by metis_tac[RAT_SUB_ADDAINV,RAT_ADD_ASSOC, RAT_ADD_COMM,RAT_ADD_LINV,RAT_ADD_LID]
  >> metis_tac[PADIC_ABS_ULTRAMETRIC]
QED

Definition cauchy_def:
  cauchy (f :num->'a) m = ∀ε. 0<ε ⇒ ∃n:num. ∀n'. n≤n' ⇒ (dist m)(f n,f n')<ε
End

Definition converges_to_def:
  converges_to (f :num->'a) (L:'a) m = ∀ε. 0<ε ⇒ ∃n. ∀n'. n≤n' ⇒ (dist m)(f n',L)<ε
End

Theorem CONVERGES_IMP_CAUCHY:
  ∀f m. (∃L. converges_to f L m) ⇒ cauchy f m
Proof
  rw[converges_to_def,cauchy_def]
  >> last_x_assum (qspec_then ‘ε/2’ assume_tac)
  >> gs[REAL_LT_RDIV_0]
  >> qexists_tac ‘n’
  >> rw[]
  >> ‘dist m (f n,L) < ε/2 ∧ dist m (f n',L) < ε/2’ by simp[]
  >> ‘dist m (f n, f n') ≤ dist m (f n,L) + dist m (f n',L)’ by metis_tac[METRIC_TRIANGLE,METRIC_SYM]
  >> metis_tac[REAL_HALF_DOUBLE,REAL_LET_TRANS,REAL_LT_ADD2]
QED

Theorem CONVERGES_CONSTANT:
  ∀k m. converges_to (λn. k) k m
Proof
  simp[converges_to_def,METRIC_SAME]
QED

Theorem CONSTANT_CAUCHY:
  ∀m k. cauchy (λn. k) m
Proof
  rw[cauchy_def,METRIC_SAME]
QED

Theorem CAUCHY_ALT:
  cauchy f m = ∀ε. 0<ε ⇒ ∃n:num. ∀n1 n2. n≤n1 ∧ n≤n2 ⇒ dist m (f n1, f n2) < ε
Proof
  rw[cauchy_def] >> iff_tac
  >-(rw[] >> last_x_assum (qspec_then ‘ε/2’ assume_tac) >> gs[REAL_LT_HALF1]
     >> qexists_tac ‘n’ >> rw[]
     >> ‘dist m (f n1,f n2) ≤ dist m (f n1, f n) + dist m (f n, f n2)’ by simp[METRIC_TRIANGLE]
     >> ‘dist m (f n1, f n) < ε/2 ∧ dist m (f n, f n2) < ε/2’ by simp[METRIC_SYM]
     >> metis_tac[REAL_LT_ADD2,REAL_HALF_DOUBLE,REAL_LET_TRANS]
    )
  >-(rw[] >> last_x_assum (qspec_then ‘ε’ assume_tac) >> gs[]
     >> qexists_tac ‘n’ >> rw[arithmeticTheory.LESS_EQ_REFL]
    )
QED

Theorem FINITE_IMP_BOUNDED_ABOVE:
  ∀A. FINITE A ⇒ ∃M. ∀a. A a ⇒ a≤M
Proof
  Induct_on ‘FINITE’
  >> rw[]
  >> qexists_tac ‘max e M’ >> simp[REAL_LE_MAX,IN_DEF] >> rw[] >> rw[]
QED

Theorem FINITE_BOUNDED_ITERATE:
  ∀n:num. FINITE {f n0 | n0 < n}
Proof
  Induct
  >- simp[]
  >- (simp[prim_recTheory.LESS_THM]
      >> ‘{f n0 | n0 = n ∨ n0 < n} = {f n} ∪ {f n0 | n0 < n}’ suffices_by simp[]
      >> simp[pred_setTheory.EXTENSION] >> metis_tac[]
     )
QED

Theorem CAUCHY_IMP_BOUNDED:
  ∀f m. cauchy f m ⇒ ∃M. ∀n. (dist m)(f n, f 0) ≤ M
Proof
  rw[cauchy_def]
  >> last_x_assum (qspec_then ‘1’ assume_tac) >> gs[]
  >> ‘∀n'. n≤ n' ⇒ dist m (f n', f 0) ≤ dist m (f n, f 0) + dist m (f n', f n)’ by
    metis_tac[METRIC_TRIANGLE,METRIC_SYM]
  >> ‘∀n'. n≤n' ⇒ dist m (f n, f 0) + dist m (f n', f n) < dist m (f n, f 0) + 1’ by
    simp[REAL_LT_LADD,METRIC_SYM]
  >> ‘∀n'. n≤n' ⇒ dist m (f n', f 0) < dist m (f n, f 0)+1’ by metis_tac[REAL_LET_TRANS]
  >> qabbrev_tac ‘A = {dist m (f 0, f n0) | n0 < n} ∪ {dist m (f 0, f n) + 1}’
  >> qexists_tac ‘sup A’
  >> qx_gen_tac ‘p’
  >> irule REAL_IMP_LE_SUP
  >> simp[DISJ_IMP_THM,FORALL_AND_THM]
  >> conj_tac
  >- (irule FINITE_IMP_BOUNDED_ABOVE >> simp[Abbr ‘A’,FINITE_BOUNDED_ITERATE]
     )
  >- (Cases_on ‘p < n’
      >-(irule_at Any REAL_LE_REFL >> simp[Abbr ‘A’] >> metis_tac[METRIC_SYM])
      >-(simp[Abbr ‘A’, SF DNF_ss] >> gs[arithmeticTheory.NOT_LESS] >> metis_tac[REAL_LE_LT,METRIC_SYM])
     )
QED


Definition rat_fn_add_def:
  rat_fn_add f g = (λx. rat_add (f x) (g x))
End

Definition rat_fn_mul_def:
  rat_fn_mul f g = (λx. rat_mul (f x) (g x))
End

Definition rat_fn_sub_def:
  rat_fn_sub f g = (λx. rat_sub (f x) (g x))
End

Definition rat_fn_ainv_def:
  rat_fn_ainv f = (λx. rat_ainv (f x))
End

Definition const_fn_def:
  const (x:rat) = (λa. x)
End

Definition const_rat_of_num_fn_def:
  const_rat_of_num = const o rat_of_num
End

Overload "+" = “rat_fn_add”;
Overload "*" = “rat_fn_mul”;
Overload "-" = “rat_fn_sub”;
Overload numeric_negate = “rat_fn_ainv”

val _ = add_numeral_form(#"f",SOME "const_rat_of_num")

Theorem RAT_FN_ADD_ASSOC:
  ∀(f:'a->rat) g h. f + (g + h) = f + g + h
Proof
  simp[rat_fn_add_def,RAT_ADD_ASSOC]
QED

Theorem RAT_FN_ADD_COMM:
  ∀(f:'a->rat) g. f + g = g + f
Proof
  simp[rat_fn_add_def,RAT_ADD_COMM]
QED

Theorem CONST_THM[simp]:
  const x a = x ∧ const_rat_of_num n a = &n
Proof
  simp[const_fn_def,const_rat_of_num_fn_def]
QED

Theorem RAT_FN_ADD_ID:
  ∀f. f + 0 = f ∧ 0 + f = f
Proof
  simp[rat_fn_add_def,ETA_THM]
QED

Theorem RAT_FN_ADDAINV:
  ∀(f:'a->rat). f + -f = 0 ∧ -f + f = 0
Proof
  simp[rat_fn_ainv_def,rat_fn_add_def,RAT_ADD_RINV,RAT_ADD_LINV,const_rat_of_num_fn_def,const_fn_def]
QED

Theorem RAT_FN_MUL_ASSOC:
  ∀f g h. f*(g*h)=f*g*h
Proof
  simp[rat_fn_mul_def,RAT_MUL_ASSOC]
QED

Theorem RAT_FN_MUL_COMM:
  ∀f g. f*g=g*f
Proof
  simp[rat_fn_mul_def,RAT_MUL_COMM]
QED

Theorem RAT_FN_MUL_ID:
  ∀f. f*1 = f ∧ 1*f = f
Proof
  simp[rat_fn_mul_def,ETA_THM]
QED

Theorem CONST_INJ:
  const m = const n ⇔ m=n
Proof
  metis_tac[const_fn_def]
QED

Theorem CONST_ADD:
  &m + &n = &(m+n)
Proof
  simp[rat_fn_add_def,const_rat_of_num_fn_def,RAT_ADD_NUM_CALCULATE,const_fn_def]
QED

Theorem CONST_MUL:
  &m * &n = &(m*n)
Proof
  simp[rat_fn_mul_def,const_rat_of_num_fn_def,RAT_MUL_NUM_CALCULATE,const_fn_def]
QED

Theorem CONST_AINV:
  -const c = const (-c)
Proof
  simp[FUN_EQ_THM,rat_fn_ainv_def]
QED

Theorem CONST_RAT_OF_NUM:
  const (&n) = &n
Proof
  simp[const_fn_def,const_rat_of_num_fn_def]
QED

Theorem RAT_FN_SUB_ADDAINV:
  ∀f g. f-g = f + -g
Proof
  simp[rat_fn_add_def,rat_fn_sub_def,rat_fn_ainv_def,RAT_SUB_ADDAINV]
QED

Theorem RAT_FN_AINV_SUB:
  ∀f g. -(f-g) = g-f
Proof
  rw[FUN_EQ_THM,rat_fn_sub_def,rat_fn_ainv_def,RAT_AINV_SUB]
QED

Theorem RAT_FN_DISTRIB:
  ∀f g h. f*(g+h) = f*g + f*h ∧ (g+h)*f = g*f + h*f
Proof
  simp[rat_fn_mul_def,rat_fn_add_def,RAT_LDISTRIB,RAT_RDISTRIB]
QED

Theorem RAT_FN_AINV_MINUS1:
  ∀g. -g = -1*g
Proof
  simp[rat_fn_ainv_def,rat_fn_mul_def,const_rat_of_num_fn_def] >> simp[Once RAT_NEG]
QED

Theorem RAT_FN_AINV_ADD:
  ∀f g. -(f+g)=-f-g
Proof
  simp[Once RAT_FN_AINV_MINUS1]
  >> simp[RAT_FN_DISTRIB] >> simp[GSYM RAT_FN_AINV_MINUS1,RAT_FN_SUB_ADDAINV]
QED

Theorem RAT_FN_AINV_MUL:
  ∀f g. -(f*g) = -f * g ∧ -(f*g) = f * -g
Proof
  simp[rat_fn_ainv_def,rat_fn_mul_def,GSYM RAT_AINV_LMUL, GSYM RAT_AINV_RMUL]
QED

Theorem RAT_FN_MUL_ZERO:
  ∀f. f*0 = 0 ∧ 0*f = 0
Proof
  simp[rat_fn_mul_def,const_rat_of_num_fn_def,const_fn_def]
QED

Theorem RAT_FN_SUB_DISTRIB:
  ∀f g h. f * (g - h) = f * g - f * h ∧ (g - h) * f = g * f - h * f
Proof
  metis_tac[RAT_FN_SUB_ADDAINV,RAT_FN_DISTRIB,RAT_FN_AINV_MUL]
QED

Theorem RAT_FN_AINV_ZERO:
  -0 = 0
Proof
  simp[rat_fn_ainv_def,RAT_AINV_0,const_rat_of_num_fn_def,const_fn_def]
QED

Definition pseqv_def:
  pseqv p f g = converges_to (f-g) 0 (padic_met p)
End

Theorem PADIC_SEQ_EQV_REFL:
  pseqv p f f
Proof
  simp[pseqv_def,rat_fn_sub_def] >> simp[CONVERGES_CONSTANT]
QED

Theorem PADIC_SEQ_EQV_SYM:
  prime p ⇒ (pseqv p f g ⇔ pseqv p g f)
Proof
  rw[] >> simp[EQ_IMP_THM] >> qid_spec_tac ‘g’ >> qid_spec_tac ‘f’ >> simp[FORALL_AND_THM] >> conj_asm1_tac
  >-(rw[pseqv_def,converges_to_def]
     >> qpat_x_assum ‘∀x. P’ (qspec_then ‘ε’ assume_tac) >> gs[]
     >> qexists_tac ‘n’
     >> rw[]
     >> ‘dist (padic_met p) ((g-f) n',0) = dist (padic_met p) ((f-g) n',0)’ by (
       simp[padic_met_def,iffLR $ cj 2 metric_tybij,PADIC_DIST_ISMET]
       >> simp[padic_dist,Once $ GSYM RAT_FN_AINV_SUB,rat_fn_ainv_def,PADIC_ABS_NEG]
       )
     >> simp[]
    )
  >- simp[]
QED

Theorem PADIC_SEQ_EQV_TRANS:
  ∀p f g h. prime p ∧ pseqv p f g ∧ pseqv p g h ⇒ pseqv p f h
Proof
  simp[pseqv_def,converges_to_def,PADIC_DIST_FROM_0,SF CONJ_ss]
  >> rpt strip_tac
  >> rpt (qpat_x_assum ‘∀ε. P’ (qspec_then ‘ε’ assume_tac))
  >> gs[]
  >> qexists_tac ‘MAX n n'’
  >> rw[]
  >> ‘f-h = (f-g)+(g-h)’ by (
    simp[FUN_EQ_THM,rat_fn_sub_def,rat_fn_add_def]
    >> metis_tac[RAT_ADD_ASSOC,RAT_SUB_ADDAINV,RAT_ADD_COMM,RAT_ADD_RID,RAT_ADD_RINV]
    )
  >> ‘abs p ((f-h) n'') ≤ max (abs p ((f-g) n'')) (abs p ((g-h) n''))’ by metis_tac[PADIC_ABS_ULTRAMETRIC,rat_fn_add_def]
  >> ‘max (abs p ((f-g) n'')) (abs p ((g-h) n'')) < ε’ by simp[REAL_MAX_LT]
  >> metis_tac[REAL_LET_TRANS]
QED

Theorem PADIC_SEQ_EQV_REL:
  prime p ⇒ (pseqv p) equiv_on (λx. T)
Proof
  rw[pred_setTheory.equiv_on_def]
  >- simp[PADIC_SEQ_EQV_REFL]
  >- simp[PADIC_SEQ_EQV_SYM]
  >- metis_tac[PADIC_SEQ_EQV_TRANS]
QED

(* setting up idea that we are quotienting by an ideal *)

Theorem PADIC_SEQ_CONVERGES_TO_ZERO_ADD:
  ∀p f g. prime p ∧ converges_to f 0 (padic_met p) ∧ converges_to g 0 (padic_met p) ⇒ converges_to (f+g) 0 (padic_met p)
Proof
  rw[converges_to_def]
  >> rpt (qpat_x_assum ‘∀e. _’ (qspec_then ‘ε’ assume_tac))
  >> gs[PADIC_DIST_FROM_0]
  >> qexists_tac ‘MAX n n'’
  >> rw[rat_fn_add_def]
  >> metis_tac[PADIC_ABS_ULTRAMETRIC,REAL_LE_MAX,REAL_LET_TRANS]
QED

Theorem CAUCHY_IMP_BOUNDED_PADIC:
  prime p ∧ cauchy f (padic_met p) ⇒ ∃M. ∀n. abs p (f n) ≤ M
Proof
  rw[GSYM PADIC_DIST_FROM_0]
  >> ‘∃M. ∀n. dist (padic_met p) (f n, f 0) ≤ M’ by metis_tac[CAUCHY_IMP_BOUNDED]
  >> qexists_tac ‘max M (dist (padic_met p) (f 0,0))’
  >> gs[PADIC_MET_DIST]
  >> metis_tac[REAL_LE_MAX,REAL_LE_TRANS,PADIC_DIST_ULTRAMETRIC,PADIC_DIST_SYM]
QED

Theorem PADIC_SEQ_CONVERGES_TO_ZERO_MUL:
  ∀p f g. prime p ∧ converges_to f 0 (padic_met p) ∧ cauchy g (padic_met p) ⇒ converges_to (f*g) 0 (padic_met p)
Proof
  rw[converges_to_def,PADIC_DIST_FROM_0,rat_fn_mul_def,PADIC_ABS_MUL]
  >> ‘∃M. ∀n. abs p (g n) < M ∧ 0<M’ by (
    ‘∃M1. ∀n. abs p (g n) ≤ M1’ by metis_tac[CAUCHY_IMP_BOUNDED_PADIC]
    >> qexists_tac ‘M1+1’
    >> metis_tac[REAL_LT_ADDR,REAL_LT_01,REAL_LET_TRANS,REAL_LT_IMP_LE,PADIC_ABS_POS,dividesTheory.PRIME_POS,REAL_LE_TRANS])
  >> qpat_x_assum ‘∀ε. 0<ε ⇒ _’ (qspec_then ‘ε/M’ assume_tac)
  >> gs[REAL_LT_DIV,PADIC_DIST_FROM_0]
  >> qexists_tac ‘n’
  >> metis_tac[REAL_DIV_RMUL,REAL_LT_IMP_NE,REAL_LT_MUL2,PADIC_ABS_POS,dividesTheory.PRIME_POS]
QED

val _ = export_theory();
