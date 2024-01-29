open HolKernel Parse boolLib bossLib;

open padic_metricTheory metricTheory ratTheory realTheory pred_setTheory
     fcpTheory;

val _ = new_theory "padic";


Definition primeits_def:
  primeits (:α) = let c = (CARD (univ (:α))) in
                    if FINITE (univ (:α)) ∧ prime c then c else 2
End

Theorem PRIMEITS_PRIME:
  prime (primeits (:α))
Proof
  rw[primeits_def]
QED

Theorem PRIMEITS_POS:
  0 < primeits (:α)
Proof
  simp[dividesTheory.PRIME_POS,PRIMEITS_PRIME]
QED

Definition pmet_def:
  pmet (:α) = padic_met (primeits (:α))
End

val _ = augment_srw_ss [rewrites[PRIMEITS_PRIME,pmet_def]];
Overload "pd" = “λx. dist (pmet x)”

Theorem PMET_ZERO:
  pd (:α) (x,y) = 0 ⇔ x=y
Proof
  simp[METRIC_ZERO]
QED

Theorem PMET_SAME:
  0 ≤ pd (:α) (x,y)
Proof
  simp[METRIC_POS]
QED

Theorem PMET_SYM:
  pd (:α) (x,y) = pd (:α) (y,x)
Proof
  simp[METRIC_SYM]
QED

Theorem PMET_TRIANGLE:
  pd (:α) (x,z) ≤ pd (:α) (x,y) + pd (:α) (y,z)
Proof
  simp[METRIC_TRIANGLE]
QED

Theorem PMET_ULTRAMETRIC:
  pd (:α) (x,z) ≤ max (pd (:α) (x,y)) (pd (:α) (y,z))
Proof
  simp[PADIC_MET_DIST,padic_dist]
  >> ‘x-z = (x-y) + (y-z)’
    by metis_tac[RAT_ADD_ASSOC,RAT_SUB_ADDAINV,RAT_ADD_LINV,RAT_ADD_RID]
  >> simp[PADIC_ABS_ULTRAMETRIC]
QED

Type rep[local,pp] = “:(num -> rat) # α itself”

Definition padic_pair_add_def:
  pair_add (f,(:α)) (g,(:α)) = (rat_fn_add f g,(:α))
End

Definition padic_pair_mul_def:
  pair_mul (f,(:α)) (g,(:α)) = (rat_fn_mul f g,(:α))
End

Definition padic_pair_ainv_def:
  pair_ainv (f,(:α)) = (-f,(:α))
End

Definition padic_pair_sub_def:
  pair_sub (f,(:α)) (g,(:α)) = (f-g,(:α))
End

Definition pair_of_rat_def:
  pair_of_rat r = (const r:num->rat,(:α))
End

Definition pcauchy_def:
  pcauchy (f,(:α)) = cauchy f (pmet (:α))
End

Theorem PCAUCHY_CONSECUTIVE_TERMS:
  pcauchy (f,(:α)) ⇔ converges_to (λn. f (SUC n) - f n) 0 (pmet (:α))
Proof
  simp[pcauchy_def,CAUCHY_ALT,converges_to_def]
  >> simp[PADIC_DIST_FROM_0,PRIMEITS_PRIME, GSYM padic_dist,GSYM PADIC_MET_DIST]
  >> iff_tac
  >- (rw[] >> last_x_assum (qspec_then ‘ε’ assume_tac) >> gs[]
      >> qexists_tac ‘n’ >> simp[])
  >- (rw[] >> last_x_assum (qspec_then ‘ε’ assume_tac) >> gs[]
      >> qexists_tac ‘n’ >> rw[]
      >> wlog_tac ‘n1 ≤ n2’ [‘n1’,‘n2’]
      >- metis_tac[arithmeticTheory.NOT_LESS_EQUAL,
                   arithmeticTheory.LESS_IMP_LESS_OR_EQ,METRIC_SYM]
      >- (‘∃m. n2 = n1 + m’ by metis_tac[arithmeticTheory.LESS_EQ_EXISTS]
          >> gvs[]
          >> Induct_on ‘m’
          >- simp[METRIC_SAME]
          >> qabbrev_tac ‘d = dist (padic_met (primeits (:α)))’
          >> ‘d (f n1, f (SUC m + n1)) ≤
                max (d (f n1, f (m+n1))) (d (f (SUC m+n1), f (m + n1))) ’
            by (simp[Abbr ‘d’,PRIMEITS_PRIME,PADIC_MET_DIST]
                >> metis_tac[PADIC_DIST_ULTRAMETRIC,PRIMEITS_PRIME,
                             PADIC_DIST_SYM])
          >> ‘SUC m + n1 = SUC (m+n1)’ by simp[]
          >> ‘n≤m+n1’ by simp[]
          >> metis_tac[REAL_LE_MAX,REAL_LET_TRANS]
         )
     )
QED

Theorem ITSELF_PAIR_THM:
  ∀p. ∃f. p = (f,(:α))
Proof
  metis_tac[pairTheory.ABS_PAIR_THM,ITSELF_UNIQUE]
QED

Overload "+" = “pair_add”;
Overload "*" = “pair_mul”;
Overload "-" = “pair_sub”;
Overload numeric_negate = “pair_ainv”;

Theorem PAIR_ADD_ASSOC:
  ∀x y z. x+(y+z) = x+y+z
Proof
  rw[]
  >> ‘∃f1 f2 f3. x = (f1,(:β)) ∧ y = (f2,(:β)) ∧ z = (f3,(:β))’
    by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_add_def,RAT_FN_ADD_ASSOC]
QED

Theorem PAIR_ADD_COMM:
  ∀x y z. x+y=y+x
Proof
  rw[] >> ‘∃f1 f2. x = (f1,(:β)) ∧ y = (f2,(:β))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_add_def,RAT_FN_ADD_COMM]
QED

Theorem PAIR_ADD_ID:
  ∀x. x + pair_of_rat 0 = x ∧ pair_of_rat 0 + x = x
Proof
  rw[] >> ‘∃f1. x = (f1,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_add_def,RAT_FN_ADD_ID,pair_of_rat_def,CONST_RAT_OF_NUM]
QED

Theorem PAIR_MUL_ASSOC:
  ∀x y z. x*(y*z) = x*y*z
Proof
  rw[]
  >> ‘∃f1 f2 f3. x = (f1,(:β)) ∧ y = (f2,(:β)) ∧ z = (f3,(:β))’
    by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_mul_def,RAT_FN_MUL_ASSOC]
QED

Theorem PAIR_MUL_COMM:
  ∀x y. x*y = y*x
Proof
  rw[] >> ‘∃f1 f2. x = (f1,(:β)) ∧ y = (f2,(:β))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_mul_def,RAT_FN_MUL_COMM]
QED

Theorem PAIR_MUL_ID:
  ∀x. x * pair_of_rat 1 = x ∧ pair_of_rat 1 * x = x
Proof
  rw[] >> ‘∃f1. x = (f1,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_mul_def,RAT_FN_MUL_ID,pair_of_rat_def,CONST_RAT_OF_NUM]
QED

Theorem PAIR_MUL_ZERO:
  ∀x. x * pair_of_rat 0 = pair_of_rat 0 ∧ pair_of_rat 0 * x = pair_of_rat 0
Proof
  rw[] >> ‘∃f1. x = (f1,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_mul_def,RAT_FN_MUL_ZERO,pair_of_rat_def,CONST_RAT_OF_NUM]
QED

Theorem PAIR_ADD_AINV:
  ∀x. x + -x = pair_of_rat 0 ∧ -x + x = pair_of_rat 0
Proof
  rw[] >> ‘∃f1. x = (f1,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_ainv_def,padic_pair_add_def,RAT_FN_ADDAINV,pair_of_rat_def,CONST_RAT_OF_NUM]
QED

Theorem PAIR_SUB_ADDAINV:
  ∀x y. x - y = x + -y
Proof
  rw[] >> ‘∃f1 f2. x = (f1,(:β)) ∧ y = (f2,(:β))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_ainv_def,padic_pair_add_def,padic_pair_sub_def,
          RAT_FN_SUB_ADDAINV]
QED

Theorem PAIR_AINV_MINUS1:
  ∀x. pair_of_rat (-1) * x = -x
Proof
  rw[] >> ‘∃f1. x = (f1,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_ainv_def,padic_pair_mul_def,GSYM RAT_FN_AINV_MINUS1,
          pair_of_rat_def,GSYM CONST_AINV,CONST_RAT_OF_NUM]
QED

Theorem PAIR_AINV_ZERO:
  - pair_of_rat 0 = pair_of_rat 0
Proof
  simp[padic_pair_ainv_def,RAT_FN_AINV_ZERO,pair_of_rat_def,CONST_RAT_OF_NUM]
QED

Theorem PAIR_DISTRIB:
  ∀x y z. x*(y+z) = x*y + x*z ∧ (x+y)*z = x*z + y*z
Proof
  rw[]
  >> ‘∃f1 f2 f3. x = (f1,(:β)) ∧ y = (f2,(:β)) ∧ z = (f3,(:β))’
    by metis_tac[ITSELF_PAIR_THM]
  >> simp[padic_pair_add_def,padic_pair_mul_def,RAT_FN_DISTRIB]
QED

Theorem PAIR_OF_RAT_ADD:
  pair_of_rat r1 + pair_of_rat r2 = pair_of_rat (r1 + r2)
Proof
  simp[pair_of_rat_def,padic_pair_add_def,const_fn_def,rat_fn_add_def]
QED

Theorem PAIR_OF_RAT_MUL:
  pair_of_rat r1 * pair_of_rat r2 = pair_of_rat (r1 * r2)
Proof
  simp[pair_of_rat_def,padic_pair_mul_def,const_fn_def,rat_fn_mul_def]
QED

Theorem PAIR_OF_RAT_INJ:
  pair_of_rat r1 = pair_of_rat r2 ⇔ r1 = r2
Proof
  rw[pair_of_rat_def,CONST_INJ]
QED

(* pm (:a) = pm (primeits (:a)), cseq' : a itself -> ...,
   cseq_add' : a itself -> ..., cseq_mul': a itself, prove equiv relation *)

Definition padic_seq_equiv_def:
  padic_seq_equiv (f,(:α)) (g,(:α)) ⇔
    pcauchy (f,(:α)) ∧ pcauchy (g,(:α)) ∧ pseqv (primeits (:α)) f g
End

Theorem PADIC_SEQ_EQUIV_THM:
  padic_seq_equiv (f,(:α)) (g,(:α)) ⇔
    pcauchy (f,(:α)) ∧ pcauchy (g,(:α)) ∧
    if FINITE univ (:α) ∧ prime (CARD (univ (:α))) then
      pseqv (CARD (univ (:α))) f g
    else pseqv 2 f g
Proof
  rw[padic_seq_equiv_def,pseqv_def,primeits_def]
QED

Theorem PADIC_SEQ_EQUIV_THM2:
  padic_seq_equiv x y ⇔
    pcauchy x ∧ pcauchy y ∧ pseqv (primeits (SND x)) (FST x) (FST y)
Proof
  ‘∃f a. x = (f,a) ∧ ∃g b. y = (g,b)’ by simp[pairTheory.ABS_PAIR_THM]
  >> ‘a=(:α) ∧ b = (:α)’ by simp[ITSELF_UNIQUE]
  >> gvs[]
  >> simp[padic_seq_equiv_def]
QED

Theorem PADIC_SEQ_EQUIV_REL:
  padic_seq_equiv equiv_on pcauchy
Proof
  rw[equiv_on_def]
  >> ‘∃ f. x = (f,(:α)) ∧ ∃g. y = (g,(:α)) ∧ ∃h. z = (h,(:α))’
    by rw[ITSELF_PAIR_THM] >> gvs[]
  >> gs[padic_seq_equiv_def,PADIC_SEQ_EQV_REFL,PADIC_SEQ_EQV_SYM,pcauchy_def,
        pred_setTheory.IN_APP]
  >> irule PADIC_SEQ_EQV_TRANS >> simp[] >> qexists_tac ‘g’ >> simp[]
QED

Theorem PCAUCHY_ADD:
  ∀x y. pcauchy x ∧ pcauchy y ⇒ pcauchy (x+y)
Proof
  rw[] >> ‘∃f1 f2. x = (f1,(:α)) ∧ y = (f2,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> gs[pcauchy_def,padic_pair_add_def,CAUCHY_ALT,PADIC_MET_DIST,padic_dist]
  >> rw[]
  >> rpt (qpat_x_assum ‘∀e. _’ (qspec_then ‘ε/2’ assume_tac))
  >> gs[REAL_LT_HALF1]
  >> qexists_tac ‘MAX n n'’ >> rw[]
  >> ‘(f1 + f2) n1 - (f1 + f2) n2 = (f1 n1 - f1 n2) + (f2 n1 - f2 n2)’
    by metis_tac[rat_fn_add_def,RAT_SUB_ADDAINV,RAT_ADD_ASSOC,RAT_ADD_COMM,
                 RAT_AINV_ADD]
  >> simp[]
  >> metis_tac[PADIC_ABS_TRIANGLE,PRIMEITS_PRIME,REAL_HALF_DOUBLE,REAL_LT_ADD2,
               REAL_LET_TRANS]
QED

Theorem PCAUCHY_IMP_BOUNDED:
  pcauchy (f,(:α)) ⇒ ∃M. ∀n. abs (primeits (:α)) (f n) ≤ M
Proof
  rw[pcauchy_def,GSYM PADIC_DIST_FROM_0,PRIMEITS_PRIME]
  >> ‘∃M. ∀n. dist (padic_met (primeits (:α))) (f n, f 0) ≤ M’
    by metis_tac[CAUCHY_IMP_BOUNDED]
  >> qexists_tac ‘M + dist (padic_met (primeits (:α))) (f 0,0)’
  >> metis_tac[REAL_LE_TRANS,REAL_LE_RADD,METRIC_TRIANGLE]
QED

Theorem REAL_DIVMUL_CANCEL2:
  c≠0:real ⇒ a/(b*c) * c = a/b
Proof
  simp[real_div,REAL_INV_MUL']
  >> metis_tac[REAL_MUL_ASSOC,REAL_MUL_LINV,REAL_MUL_RID]
QED

Theorem PCAUCHY_MUL:
  ∀x y. pcauchy x ∧ pcauchy y ⇒ pcauchy (x*y)
Proof
  rw[]
  >> ‘∃f1 f2. x = (f1,(:α)) ∧ y = (f2,(:α))’
    by metis_tac[ITSELF_PAIR_THM]
  >> rw[padic_pair_mul_def]
  >> ‘∃M. ∀n. abs (primeits (:α)) (f1 n) < M ∧ abs (primeits (:α)) (f2 n) < M’
    by (‘(∃M1. ∀n. abs (primeits (:α)) (f1 n) ≤ M1) ∧
         ∃M2. ∀n. abs (primeits (:α)) (f2 n) ≤ M2’
          by metis_tac[PCAUCHY_IMP_BOUNDED]
    >> qexists_tac ‘max M1 M2 + 1’
    >> metis_tac[REAL_LE_MAX,REAL_LT_ADDR,REAL_LT_01,REAL_LET_TRANS])
  >> gs[pcauchy_def,CAUCHY_ALT,PADIC_MET_DIST,PRIMEITS_PRIME,padic_dist,
        rat_fn_mul_def]
  >> rw[]
  >> rpt (qpat_x_assum ‘∀ε. 0<ε ⇒ _’ (qspec_then ‘ε/(2*M)’ assume_tac))
  >> ‘0<M’ by metis_tac[PADIC_ABS_POS,PRIMEITS_POS,REAL_LET_TRANS]
  >> ‘0<2*M’ by (irule REAL_LT_MUL >> simp[])
  >> gs[REAL_LT_RDIV_0]
  >> qexists_tac ‘MAX n n'’ >> rw[]
  >> ‘f1 n1 * f2 n1 - f1 n2 * f2 n2 =
      (f1 n1 * f2 n1 - f1 n1 * f2 n2) + (f1 n1 * f2 n2 - f1 n2 * f2 n2)’
    by metis_tac[RAT_SUB_ADDAINV,RAT_ADD_ASSOC,RAT_ADD_RID,RAT_ADD_LINV]
  >> ‘_ = f1 n1 * (f2 n1 - f2 n2) + f2 n2 * (f1 n1 - f1 n2)’
    by metis_tac[RAT_SUB_LDISTRIB,RAT_SUB_RDISTRIB,RAT_MUL_COMM]
  >> ‘abs (primeits (:α)) (f1 n1 * f2 n1 - f1 n2 * f2 n2) ≤
        abs (primeits (:α)) (f1 n1) * abs (primeits (:α)) (f2 n1 - f2 n2) +
        abs (primeits (:α)) (f2 n2) * abs (primeits (:α)) (f1 n1 - f1 n2)’
    by metis_tac[PADIC_ABS_TRIANGLE,PADIC_ABS_MUL,PRIMEITS_PRIME]
  >> ‘M * (ε/(2*M)) = ε/2’
    by (once_rewrite_tac[REAL_MUL_COMM]
        >> simp[REAL_DIVMUL_CANCEL2,REAL_LT_IMP_NE])
  >> ‘abs (primeits (:α)) (f1 n1) * abs (primeits (:α)) (f2 n1 - f2 n2) < ε/2 ∧
      abs (primeits (:α)) (f2 n2) * abs (primeits (:α)) (f1 n1 - f1 n2) < ε/2’
    by metis_tac[REAL_LT_MUL2,PADIC_ABS_POS,PRIMEITS_POS]
  >> metis_tac[PADIC_ABS_TRIANGLE,REAL_HALF_DOUBLE,REAL_LT_ADD2,REAL_LET_TRANS]
QED

Theorem PCAUCHY_PAIR_OF_RAT:
  ∀r. pcauchy (pair_of_rat r)
Proof
  PURE_REWRITE_TAC[pcauchy_def,pair_of_rat_def,const_fn_def,CONSTANT_CAUCHY] >> simp[]
QED

Theorem PCAUCHY_AINV:
  ∀x. pcauchy x ⇒ pcauchy (-x)
Proof
  simp[GSYM PAIR_AINV_MINUS1,const_rat_of_num_fn_def,CONST_AINV,PCAUCHY_MUL,PCAUCHY_PAIR_OF_RAT]
QED

Theorem PCAUCHY_SUB:
  ∀x y. pcauchy x ∧ pcauchy y ⇒ pcauchy (x-y)
Proof
  simp[PAIR_SUB_ADDAINV,PCAUCHY_AINV,PCAUCHY_ADD]
QED

(*Theorem PCAUCHY_MINV:
  ∀x. pcauchy x ∧ ~(padic_seq_equiv x (pair_of_rat 0)) ⇒ pcauchy (pair_minv x)
Proof
  strip_tac >> ‘∃f. x=(f,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> rw[PADIC_SEQ_EQUIV_THM2,PCAUCHY_PAIR_OF_RAT,pair_of_rat_def,pseqv_def,converges_to_def]
QED*)

Theorem PADIC_SEQ_EQUIV_MUL_RSP:
  padic_seq_equiv x1 x2 ∧ padic_seq_equiv y1 y2 ⇒
  padic_seq_equiv (x1*y1) (x2*y2)
Proof
  ‘∃f1 f2 g1 g2.
     x1 = (f1,(:α)) ∧ x2 = (f2,(:α)) ∧ y1 = (g1,(:α)) ∧ y2 = (g2,(:α))’
    by metis_tac[ITSELF_PAIR_THM]
  >> rw[padic_seq_equiv_def,pseqv_def,converges_to_def,PADIC_DIST_FROM_0,
        padic_pair_mul_def]
  >> simp[GSYM padic_pair_mul_def,PCAUCHY_MUL]
  >> ‘∃M. ∀n. abs (primeits (:α)) (f1 n) < M ∧ abs (primeits (:α)) (g2 n) < M’
    by (‘(∃M1. ∀n. abs (primeits (:α)) (f1 n) ≤ M1) ∧
         ∃M2. ∀n. abs (primeits (:α)) (g2 n) ≤ M2’
          by metis_tac[PCAUCHY_IMP_BOUNDED,pcauchy_def]
        >> qexists_tac ‘max M1 M2 + 1’
        >> metis_tac[REAL_LE_MAX,REAL_LT_ADDR,REAL_LT_01,REAL_LET_TRANS])
  >> rpt (qpat_x_assum ‘∀e. _’ (qspec_then ‘ε/(2*M)’ assume_tac))
  >> ‘0<M’ by metis_tac[PADIC_ABS_POS,PRIMEITS_POS,REAL_LET_TRANS]
  >> ‘0<2*M’ by (irule REAL_LT_MUL >> simp[])
  >> gs[REAL_LT_RDIV_0]
  >> qexists_tac ‘MAX n n'’
  >> ‘f1 * g1 - f2 * g2 = f1 * g1 - f1 * g2 + f1 * g2 - f2 * g2’ by
    metis_tac[RAT_FN_SUB_ADDAINV,RAT_FN_ADD_ASSOC,RAT_FN_ADDAINV,RAT_FN_ADD_ID]
  >> ‘_ = f1 * (g1 - g2) + g2 * (f1 - f2)’
    by metis_tac[RAT_FN_SUB_ADDAINV,RAT_FN_DISTRIB,RAT_FN_MUL_COMM,
                 RAT_FN_ADD_ASSOC,RAT_FN_AINV_MUL]
  >> rw[]
  >> ‘abs (primeits (:α)) ((f1 * (g1 - g2) + g2 * (f1 - f2)) n'') ≤
        abs (primeits (:α)) (f1 n'') * abs (primeits (:α)) ((g1 - g2) n'') +
        abs (primeits (:α)) (g2 n'') * abs (primeits (:α)) ((f1 - f2) n'')’
    by simp[GSYM PADIC_ABS_MUL,PRIMEITS_PRIME,rat_fn_mul_def,rat_fn_add_def,
            PADIC_ABS_TRIANGLE]
  >> ‘M * (ε/(2*M)) = ε/2’
    by (once_rewrite_tac[REAL_MUL_COMM]
        >> simp[REAL_DIVMUL_CANCEL2,REAL_LT_IMP_NE])
  >> ‘abs (primeits (:α)) (f1 n'') * abs (primeits (:α)) ((g1 - g2) n'') < ε/2 ∧
      abs (primeits (:α)) (g2 n'') * abs (primeits (:α)) ((f1 - f2) n'') < ε/2’
    by metis_tac[REAL_LT_MUL2,PADIC_ABS_POS,PRIMEITS_POS]
  >> metis_tac[PADIC_ABS_TRIANGLE,REAL_HALF_DOUBLE,REAL_LT_ADD2,REAL_LET_TRANS]
QED

Theorem PADIC_SEQ_EQUIV_ADD_RSP:
  padic_seq_equiv x1 x2 ∧ padic_seq_equiv y1 y2 ⇒
  padic_seq_equiv (x1+y1) (x2+y2)
Proof
  ‘∃f1 f2 g1 g2. x1 = (f1,(:α)) ∧ x2 = (f2,(:α)) ∧
                 y1 = (g1,(:α)) ∧ y2 = (g2,(:α))’ by metis_tac[ITSELF_PAIR_THM]
  >> rw[padic_seq_equiv_def,PADIC_DIST_FROM_0,pseqv_def,converges_to_def,
        padic_pair_add_def]
  >> rpt (last_x_assum (qspec_then ‘ε’ assume_tac))
  >> gs[pseqv_def,converges_to_def]
  >> simp[GSYM padic_pair_add_def,PCAUCHY_ADD]
  >> qexists_tac ‘MAX n n'’
  >> rw[]
  >> ‘f1 + g1 - (f2 + g2) = (f1 - f2) + (g1 - g2)’ by
    metis_tac[RAT_FN_SUB_ADDAINV,RAT_FN_ADD_ASSOC,RAT_FN_ADD_COMM,
              RAT_FN_AINV_ADD]
  >> ‘(f1 + g1 - (f2 + g2)) n'' = (f1 - f2) n'' + (g1 - g2) n''’
    by simp[rat_fn_add_def]
  >> ‘abs (primeits (:α)) ((f1 + g1 - (f2 + g2)) n'') ≤
        max (abs (primeits (:α)) ((f1 - f2) n''))
            (abs (primeits (:α)) ((g1 - g2) n''))’
    by metis_tac[PADIC_ABS_ULTRAMETRIC,PRIMEITS_PRIME]
  >> metis_tac[REAL_LET_TRANS,realaxTheory.real_max]
QED

Theorem PADIC_SEQ_EQUIV_CAUCHY:
  pcauchy (f1,(:α)) ∧ pseqv (primeits (:α)) f1 f2 ⇒ pcauchy (f2,(:α))
Proof
  rw[pcauchy_def,PADIC_DIST_FROM_0,CAUCHY_ALT,padic_seq_equiv_def,pseqv_def,
     converges_to_def]
  >> first_x_assum (qspec_then ‘ε’ assume_tac)
  >> last_x_assum (qspec_then ‘ε’ assume_tac) >> gs[REAL_LT_HALF1]
  >> qexists_tac ‘MAX n n'’
  >> ‘∀n. abs (primeits (:α)) ((f1 - f2) n) =
          padic_dist (primeits (:α)) (f1 n, f2 n)’
    by simp[padic_dist,rat_fn_sub_def]
  >> gs[PADIC_MET_DIST] >> rw[PADIC_MET_DIST]
  >> ‘padic_dist (primeits (:α)) (f2 n1, f2 n2) ≤
        max (padic_dist (primeits (:α)) (f2 n1, f1 n1))
            (padic_dist (primeits (:α)) (f1 n1, f2 n2))’
    by metis_tac[PRIMEITS_PRIME,PADIC_DIST_ULTRAMETRIC]
  >> metis_tac[PADIC_DIST_ULTRAMETRIC,REAL_MAX_LT,REAL_LET_TRANS,PADIC_DIST_SYM,
               PRIMEITS_PRIME,REAL_LE_MAX]
QED

Theorem PADIC_SEQ_EQUIV_SYM:
  ∀x y. padic_seq_equiv x y ⇔ padic_seq_equiv y x
Proof
  rw[] >> ‘∃f. x = (f,(:α)) ∧ ∃g. y = (g,(:α))’ by simp[ITSELF_PAIR_THM]
  >> rw[padic_seq_equiv_def]
  >> metis_tac[PADIC_SEQ_EQV_SYM,PRIMEITS_PRIME]
QED

Theorem PADIC_SEQ_EQUIV_REFL:
  ∀x. pcauchy x ⇒ padic_seq_equiv x x
Proof
  rw[] >> ‘∃f. x = (f,(:α)) ∧ ∃g. y = (g,(:α))’ by simp[ITSELF_PAIR_THM]
  >> rw[padic_seq_equiv_def,PADIC_SEQ_EQV_REFL]
QED

Theorem PADIC_SEQ_EQUIV_TRANS:
  ∀x y z. padic_seq_equiv x y ∧ padic_seq_equiv y z ⇒ padic_seq_equiv x z
Proof
  rw[]
  >> ‘∃f. x = (f,(:α)) ∧ ∃g. y = (g,(:α)) ∧ ∃h. z = (h,(:α))’
    by simp[ITSELF_PAIR_THM]
  >> gs[padic_seq_equiv_def] >> metis_tac[PRIMEITS_PRIME,PADIC_SEQ_EQV_TRANS]
QED

Theorem PADIC_SEQ_EQUIV_SCALING:
  ∀x y s. padic_seq_equiv x y ⇒
          padic_seq_equiv (pair_of_rat s * x) (pair_of_rat s * y)
Proof
  rw[]
  >> ‘padic_seq_equiv (pair_of_rat s) (pair_of_rat s)’
    by metis_tac[PADIC_SEQ_EQUIV_REFL,PCAUCHY_PAIR_OF_RAT]
  >> metis_tac[PADIC_SEQ_EQUIV_MUL_RSP]
QED

Theorem PADIC_SEQ_EQUIV_AINV_RSP:
  ∀x y. padic_seq_equiv x1 x2 ⇒ padic_seq_equiv (-x1) (-x2)
Proof
  rw[] >> once_rewrite_tac[GSYM PAIR_AINV_MINUS1]
  >> simp[const_rat_of_num_fn_def,CONST_AINV,PADIC_SEQ_EQUIV_SCALING]
QED

Theorem PADIC_SEQ_EQUIV_SUB_RSP:
  padic_seq_equiv x1 x2 ∧ padic_seq_equiv y1 y2 ⇒
  padic_seq_equiv (x1-y1) (x2-y2)
Proof
  rw[]
  >> ‘padic_seq_equiv (-y1) (-y2)’ by simp[PADIC_SEQ_EQUIV_AINV_RSP]
  >> simp[PAIR_SUB_ADDAINV,PADIC_SEQ_EQUIV_ADD_RSP]
QED

Theorem PADIC_SEQ_EQUIV_CLASSES:
  padic_seq_equiv x y ⇔
    padic_seq_equiv x x ∧ padic_seq_equiv y y ∧
    padic_seq_equiv x = padic_seq_equiv y
Proof
  rw[FUN_EQ_THM,EQ_IMP_THM]
  >> metis_tac[PADIC_SEQ_EQUIV_TRANS,PADIC_SEQ_EQUIV_SYM,PADIC_SEQ_EQUIV_REFL]
QED

Theorem Q_THM:
  (∃x. padic_seq_equiv x x) ∧
  (∀x y. padic_seq_equiv x y ⇔
           padic_seq_equiv x x ∧ padic_seq_equiv y y ∧
           (padic_seq_equiv x = padic_seq_equiv y))
Proof
  rw[]
  >- (qexists_tac ‘pair_of_rat 0’
      >> simp[PADIC_SEQ_EQUIV_REFL,PCAUCHY_PAIR_OF_RAT])
  >> iff_tac >> rw[]
  >> ‘pcauchy x ∧ pcauchy y’ by metis_tac[PADIC_SEQ_EQUIV_THM2]
  >> simp[PADIC_SEQ_EQUIV_REFL,FUN_EQ_THM]
  >> rw[] >> iff_tac >> metis_tac[PADIC_SEQ_EQUIV_TRANS,PADIC_SEQ_EQUIV_SYM]
QED

Theorem PAIR_OF_RAT_PADIC_SEQ_EQUIV_REFL:
  padic_seq_equiv (pair_of_rat q) (pair_of_rat q)
Proof
  irule PADIC_SEQ_EQUIV_REFL >> simp[PCAUCHY_PAIR_OF_RAT]
QED

Theorem REAL_POS_LT_EPSILON:
  ∀r. 0≤r ∧ (∀ε. 0<ε ⇒ r<ε) ⇔ r=0
Proof
  rw[] >> iff_tac
  >-(rw[] >> CCONTR_TAC >> ‘0<r’ by simp[REAL_LT_LE]
     >> qpat_x_assum ‘∀ε. _’ (qspec_then ‘r/2’ assume_tac)
     >> gs[REAL_LT_HALF1,REAL_LT_IMP_LE,REAL_DIV_ZERO,REAL_LT_HALF2,REAL_LT_GT]
    )
  >- simp[]
QED

Theorem RAT_POS_LT_EPSILON:
  ∀r:rat. 0 ≤ r ∧ (∀ε. 0 < ε ⇒ r < ε) ⇔ r = 0
Proof
  rw[] >> iff_tac
  >-(rw[] >> CCONTR_TAC >> ‘0<r’ by simp[RAT_LT_LE_NEQ]
     >> qpat_x_assum ‘∀ε. _’ (qspec_then ‘r/2’ assume_tac)
     >> gs[RAT_RDIV_LES_POS]
     >> metis_tac[RAT_TIMES2,RAT_MUL_COMM,RAT_ADD_LID,RAT_LES_RADD,
                  RAT_LES_ANTISYM]
    )
  >- simp[]
QED

Theorem PADIC_SEQ_EQUIV_PAIR_OF_RAT:
  padic_seq_equiv (pair_of_rat p) (pair_of_rat q) ⇔ p = q
Proof
  rw[PADIC_SEQ_EQUIV_THM2,PCAUCHY_PAIR_OF_RAT,pseqv_def,pair_of_rat_def,
     converges_to_def,const_fn_def,rat_fn_sub_def] >> iff_tac
  >- (rw[] >> ‘∀ε. 0<ε ⇒ dist (padic_met (primeits (:α))) (p-q,0) < ε’ by (
        rw[] >> last_x_assum (qspec_then ‘ε’ assume_tac) >> gs[]
        >> first_x_assum (qspec_then ‘n’ assume_tac) >> gs[]
        )
      >> gs[PADIC_DIST_FROM_0]
      >> ‘p-q=0’ by (irule (iffLR PADIC_ABS_EQ_0) >> qexists_tac ‘primeits (:α)’
                     >> simp[PRIMEITS_POS,REAL_LT_IMP_NE,
                             GSYM REAL_POS_LT_EPSILON,PADIC_ABS_POS]
                    )
      >> simp[Once $ GSYM RAT_EQ_SUB0]
     )
  >- simp[METRIC_SAME]
QED

val [ADD_ASSOC, ADD_COMM, MUL_ASSOC, MUL_COMM, SUB_DEF, DISTRIB, ADDID,
     AINV', AINV0, MULID, MUL0, ADD_INV_THM] = quotient.define_quotient_types
        {types = [{name = "adic",
                   equiv = INST_TYPE [alpha |-> “:β”] Q_THM}],
defs = [{def_name = "adic_plus_def",
         fname = "adic_plus", func = “pair_add:β rep -> β rep -> β rep”,
         fixity = NONE},
        {def_name = "adic_mul_def",
         fname = "adic_mul", func = “pair_mul:β rep -> β rep -> β rep”,
         fixity = NONE},
        {def_name = "adic_sub_def",
         fname = "adic_sub", func = “pair_sub:β rep -> β rep -> β rep”,
         fixity = NONE},
        {def_name = "adic_ainv_def",
         fname = "adic_ainv", func = “pair_ainv:β rep -> β rep”,
         fixity = NONE},
        {def_name = "adic_of_rat_def",
         fname = "adic_of_rat", func = “pair_of_rat”,
         fixity = NONE}],
tyop_equivs = [],
tyop_quotients = [quotientTheory.FUN_QUOTIENT],
tyop_simps = [quotientTheory.FUN_REL_EQ,quotientTheory.FUN_MAP_I],
respects = [PADIC_SEQ_EQUIV_ADD_RSP,PADIC_SEQ_EQUIV_MUL_RSP,
            PADIC_SEQ_EQUIV_SUB_RSP,PADIC_SEQ_EQUIV_AINV_RSP,
            PAIR_OF_RAT_PADIC_SEQ_EQUIV_REFL],
poly_preserves = [quotientTheory.FORALL_PRS,quotientTheory.EXISTS_PRS],
poly_respects = [quotientTheory.RES_FORALL_RSP,
                 quotientTheory.RES_EXISTS_RSP(*,STUPID*)],
old_thms = [INST_TYPE [alpha |-> “:num”] PAIR_ADD_ASSOC,
            INST_TYPE [alpha |-> “:num”] PAIR_ADD_COMM,
            INST_TYPE [alpha |-> “:num”] PAIR_MUL_ASSOC,
            INST_TYPE [alpha |-> “:num”] PAIR_MUL_COMM,
            INST_TYPE [alpha |-> “:num”] PAIR_SUB_ADDAINV,
            INST_TYPE [alpha |-> “:num”] PAIR_DISTRIB,
            PAIR_ADD_ID,
            PAIR_AINV_MINUS1,
            PAIR_AINV_ZERO,
            PAIR_MUL_ID,
            PAIR_MUL_ZERO,
            PAIR_ADD_AINV]};

Theorem PADIC_ADD_ASSOC = ADD_ASSOC
Theorem PADIC_ADD_COMM = ADD_COMM
Theorem PADIC_MUL_ASSOC = MUL_ASSOC
Theorem PADIC_SUB_DEF = SUB_DEF
Theorem PADIC_LDISTRIB = cj 1 DISTRIB
Theorem PADIC_RDISTRIB = cj 2 DISTRIB
Theorem PADIC_ADD_RID = cj 1 ADDID
Theorem PADIC_ADD_LID = cj 2 ADDID
Theorem PADIC_NEGATE_DEF = GSYM AINV'
Theorem PADIC_NEG0 = AINV0
Theorem PADIC_MUL_RID = cj 1 MULID
Theorem PADIC_MUL_LID = cj 2 MULID
Theorem PADIC_MUL0 = MUL0
Theorem PADIC_ADD_RINV = cj 1 ADD_INV_THM
Theorem PADIC_ADD_LINV = cj 2 ADD_INV_THM

val _ = export_theory();
