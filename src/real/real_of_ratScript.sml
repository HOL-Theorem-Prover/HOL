open HolKernel Parse boolLib bossLib;

open realaxTheory ratTheory integerTheory intrealTheory realTheory;

val _ = augment_srw_ss [intSimps.INT_ARITH_ss]

val _ = new_theory "real_of_rat";

Theorem REAL_NEG_EQ:
  -r1:real = -r2 <=> r1=r2
Proof
  metis_tac[REAL_NEG_NEG]
QED

Theorem NUM_OPP_SIGNS_COMPARE:
  i1 <= 0 /\ 0 <= i2 ==> (Num i1 < Num i2 <=> 0 < i1 + i2) /\ (Num i2 < Num i1 <=> i1 + i2 < 0) /\ (Num i1 = Num i2 <=> i1 + i2 = 0)
Proof
  rw[]
  >> ‘i1 = - ABS i1’ by (Cases_on ‘i1=0’ >- simp[] >- metis_tac[INT_ABS,INT_LE_LT,INT_NEGNEG])
  >> ‘i2 = ABS i2’ by simp[INT_ABS,INT_NOT_LT]
  >> metis_tac[int_arithTheory.lt_move_all_left,int_arithTheory.lt_move_all_right,INT_ADD_COMM,INT_LT,Num_EQ_ABS,INT_NEGNEG,INT_ADD_LINV,INT_LNEG_UNIQ,INT_RNEG_UNIQ,INT_INJ]
QED

Theorem ABS_SQUARE:
  !i. ABS i * ABS i = i*i
Proof
  Cases_on ‘i’ >> rw[]
QED

Theorem REAL_OF_NUM_SUB:
  !m n. m <= n ==> &(n-m):real = &n - &m
Proof
  rw[] >> ‘?d. n=m+d’ by (irule arithmeticTheory.LESS_EQUAL_ADD >> simp[])
  >> simp[arithmeticTheory.SUB_RIGHT_EQ]
  >> once_rewrite_tac[GSYM REAL_ADD]
  >> simp[REAL_ADD_RINV,AC REAL_ADD_ASSOC REAL_ADD_SYM,real_sub,REAL_ADD_LID']
QED

Theorem NUM_NEG:
  Num (-i) = Num i
Proof
  Cases_on ‘i’ >> simp[]
QED


Theorem NUM_LT_NEG:
  i1 <= 0 /\ i2 <= 0 ==> (Num i1 < Num i2 <=> i2 < i1)
Proof
  rw[] >> once_rewrite_tac[GSYM NUM_NEG] >> once_rewrite_tac[GSYM INT_LT_NEG] >> simp[NUM_LT,INT_NEG_GE0]
QED

Theorem EQUIV_NOT_POS:
  !A B. (~A<=>B)<=>(A<=>~B)
Proof
  rpt strip_tac >> iff_tac >> rw[] >> rw[NOT_CLAUSES]
QED

Definition real_of_rat_def:
  real_of_rat q = real_of_int (RATN q) / &RATD q
End

Theorem REAL_OF_RAT_0[simp]:
  real_of_rat 0 = 0
Proof
  simp[real_of_rat_def]
QED

Theorem REAL_OF_RAT_1[simp]:
  real_of_rat 1 = 1
Proof
  simp[real_of_rat_def]
QED

Theorem REAL_OF_RAT_OF_INT:
  real_of_rat (rat_of_int i) = real_of_int i
Proof
  simp[real_of_rat_def]
QED

Theorem RAT_LEMMA5_BETTER:
  y1 <> 0:real /\ y2 <> 0 ==> (x1 / y1 = x2 / y2 <=> x1 * y2 = x2 * y1)
Proof
  rw[] >> ‘y1*y2 <> 0’ by simp[] >> simp[real_div]
  >> ‘x1 * inv y1 = x2 * inv y2 <=> x1 * inv y1 * (y1 * y2) = x2 * inv y2 * (y1 * y2)’ by simp[REAL_EQ_RMUL]
  >> ‘x1 * inv y1 * (y1 * y2) = x2 * inv y2 * (y1 * y2) <=> x1 * y2 * (inv y1 * y1) = x2 * y1 * (inv y2 * y2)’ by
    metis_tac[REAL_MUL_ASSOC, REAL_MUL_SYM]
  >> ‘x1 * y2 * (inv y1 * y1) = x2 * y1 * (inv y2 * y2) <=> x1 * y2 = x2 * y1’ by simp[REAL_MUL_LINV]
  >> metis_tac[]
QED

Theorem RAT_DIV_LEMMA:
  q1 <> 0:rat /\ q2<>0:rat ==> (p1/q1=p2/q2 <=> p1*q2 = p2*q1)
Proof
  rw[] >> simp[RAT_DIV_MULMINV]
  >> ‘p1 * q2 = p1 * q2 * (rat_minv q1 * q1)’ by simp[RAT_MUL_LINV]
  >> ‘_ = p1 * rat_minv q1 * (q1 * q2)’ by metis_tac[RAT_MUL_ASSOC,RAT_MUL_COMM]
  >> ‘p2 * q1 = p2 * q1 * (rat_minv q2 * q2)’ by simp[RAT_MUL_LINV]
  >> ‘_ = p2 * rat_minv q2 * (q1 * q2)’ by metis_tac[RAT_MUL_ASSOC,RAT_MUL_COMM]
  >> simp[RAT_EQ_RMUL]
QED

Theorem REAL_OF_RAT_INJ:
  real_of_rat r1 = real_of_rat r2 <=> r1 = r2
Proof
  simp[EQ_IMP_THM] >> simp[real_of_rat_def]
  >> simp[RAT_LEMMA5_BETTER] >> once_rewrite_tac[GSYM real_of_int_num] >> once_rewrite_tac[GSYM real_of_int_mul]
  >> simp[real_of_int_11] >> once_rewrite_tac[GSYM rat_of_int_11] >> once_rewrite_tac[GSYM rat_of_int_MUL]
  >> simp[rat_of_int_of_num,GSYM RAT_DIV_LEMMA]
QED

Theorem RATND_ADD:
  rat_of_int (RATN r1 * &RATD r2 + &RATD r1 * RATN r2) / &(RATD r1 * RATD r2) = r1 + r2
Proof
  ‘r1 + r2 = rat_of_int (RATN r1) / &RATD r1 + rat_of_int (RATN r2) / &RATD r2’ by simp[GSYM RATN_RATD_EQ_THM]
  >> ‘_ = (rat_of_int (RATN r1) * &RATD r2 + rat_of_int (RATN r2) * &RATD r1)/(&RATD r1 * &RATD r2)’ by simp[RAT_DIVDIV_ADD]
  >> simp[]
  >> once_rewrite_tac[GSYM rat_of_int_of_num] >> simp[rat_of_int_MUL,rat_of_int_ADD] >> metis_tac[INT_MUL_COMM]
QED

Theorem RAT_DIV_PROD:
  b<>0 /\ d<>0 ==> a/b:rat * (c/d) = (a*c)/(b*d)
Proof
  simp[RAT_DIV_MULMINV,RAT_MINV_MUL] >> metis_tac[RAT_MUL_ASSOC,RAT_MUL_COMM]
QED

Theorem RATND_MUL:
  rat_of_int (RATN r1 * RATN r2) / &(RATD r1 * RATD r2) = r1 * r2
Proof
  ‘r1 * r2 = rat_of_int (RATN r1) / &RATD r1 * (rat_of_int (RATN r2) / &RATD r2)’ by simp[GSYM RATN_RATD_EQ_THM]
  >> ‘_ = rat_of_int (RATN r1 * RATN r2) / &(RATD r1 * RATD r2)’ by simp[RAT_DIV_PROD,rat_of_int_MUL,RAT_MUL_NUM_CALCULATE]
  >> simp[]
QED

Theorem REAL_OF_RAT_ADD:
  real_of_rat r1 + real_of_rat r2 = real_of_rat (r1 + r2)
Proof
  simp[real_of_rat_def,RAT_LEMMA5_BETTER,REAL_ADD_RAT] >> once_rewrite_tac[GSYM real_of_int_num]
  >> once_rewrite_tac[GSYM real_of_int_mul] >> once_rewrite_tac[GSYM real_of_int_add] >> once_rewrite_tac[GSYM real_of_int_mul]
  >> simp[real_of_int_11]
  >> once_rewrite_tac[GSYM rat_of_int_11] >> once_rewrite_tac[GSYM rat_of_int_MUL]
  >> simp[GSYM RAT_DIV_LEMMA]
  >> ‘r1 + r2 = rat_of_int (RATN r1) / &RATD r1 + rat_of_int (RATN r2) / &RATD r2’ by simp[GSYM RATN_RATD_EQ_THM]
  >> ‘_ = (rat_of_int (RATN r1) * &RATD r2 + rat_of_int (RATN r2) * &RATD r1)/(&RATD r1 * &RATD r2)’ by simp[RAT_DIVDIV_ADD]
  >> simp[]
  >> once_rewrite_tac[GSYM rat_of_int_of_num] >> simp[rat_of_int_MUL,rat_of_int_ADD] >> metis_tac[INT_MUL_COMM]
QED

Theorem REAL_DIV_PROD:
  a/b:real * (c/d) = (a*c)/(b*d)
Proof
  simp[real_div,REAL_INV_MUL'] >> metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
QED

val _ = temp_delsimps ["real_of_int_num"]

Theorem REAL_OF_RAT_MUL:
  real_of_rat r1 * real_of_rat r2 = real_of_rat (r1 * r2)
Proof
  simp[real_of_rat_def,REAL_DIV_PROD,RAT_LEMMA5_BETTER,GSYM real_of_int_num]
  >> once_rewrite_tac[GSYM real_of_int_mul]
  >> once_rewrite_tac[GSYM real_of_int_mul]
  >> simp[real_of_int_11] >> once_rewrite_tac[GSYM rat_of_int_11]
  >> once_rewrite_tac[GSYM rat_of_int_MUL]
  >> simp[rat_of_int_of_num]
  >> simp[RAT_EQ_NUM_CALCULATE,GSYM RAT_DIV_LEMMA,RATND_MUL]
QED

Theorem REAL_OF_RAT_NEG:
  -real_of_rat r = real_of_rat (-r)
Proof
  ‘real_of_rat r + real_of_rat (-r) = 0’ by simp[REAL_OF_RAT_ADD,RAT_ADD_RINV]
  >> ‘real_of_rat r + -real_of_rat r = 0’ by simp[REAL_ADD_RINV]
  >> metis_tac[REAL_EQ_LADD]
QED

Theorem REAL_OF_RAT_SUB:
  real_of_rat r1 - real_of_rat r2 = real_of_rat (r1 - r2)
Proof
  simp[real_sub,RAT_SUB_ADDAINV,REAL_OF_RAT_ADD,REAL_OF_RAT_NEG]
QED

Theorem REAL_OF_RAT_MINV:
  r<>0 ==> inv (real_of_rat r) = real_of_rat (rat_minv r)
Proof
  rw[] >> ‘real_of_rat r * real_of_rat (rat_minv r) = 1’ by simp[REAL_OF_RAT_MUL,RAT_MUL_RINV]
  >> ‘real_of_rat r <> 0’ by (once_rewrite_tac[GSYM REAL_OF_RAT_0] >> simp[REAL_OF_RAT_INJ])
  >> ‘real_of_rat r * inv (real_of_rat r) = 1’ by simp[REAL_MUL_RINV]
  >> metis_tac[REAL_EQ_MUL_LCANCEL]
QED

Theorem REAL_OF_RAT_DIV:
  r2<>0 ==> real_of_rat r1 / real_of_rat r2 = real_of_rat (r1/r2)
Proof
  rw[real_div,RAT_DIV_MULMINV,REAL_OF_RAT_MUL,REAL_OF_RAT_MINV]
QED

val _ = temp_delsimps ["RATN_DIV_RATD"]

Theorem REAL_DIV_LT:
  0<b*d:real ==> (a/b<c/d <=> a*d<c*b)
Proof
  rw[real_div]
  >> ‘b<>0 /\ d<>0’ by (CCONTR_TAC >> gs[])
  >> ‘a * inv b <c * inv d <=> a * inv b * (b*d) < c * inv d * (b*d)’ by simp[REAL_LT_RMUL]
  >> ‘a * inv b * (b*d) = a*d * (inv b * b)’ by metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
  >> ‘_ = a*d’ by simp[REAL_MUL_RID,REAL_MUL_LINV]
  >> ‘c * inv d * (b*d) = c*b * (inv d * d)’ by metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
  >> ‘_ = c*b’ by simp[REAL_MUL_RID,REAL_MUL_LINV]
  >> simp[]
QED

Theorem REAL_OF_RAT_OF_NUM:
  real_of_rat (&n) = &n
Proof
  simp[real_of_rat_def,real_of_int_num]
QED

Theorem REAL_OF_RAT_LT:
  real_of_rat r1 < real_of_rat r2 <=> r1 < r2
Proof
  once_rewrite_tac[RATN_RATD_EQ_THM] >> simp[GSYM REAL_OF_RAT_DIV,REAL_OF_RAT_OF_NUM]
  >> simp[REAL_NZ_IMP_LT,RATD_NZERO,REAL_DIV_LT,REAL_OF_RAT_OF_INT]
  >> once_rewrite_tac[GSYM real_of_int_num]
  >> once_rewrite_tac[GSYM real_of_int_mul]
  >> simp[real_of_int_lt,RAT_LDIV_LES_POS,RDIV_MUL_OUT,RAT_RDIV_LES_POS]
  >> once_rewrite_tac[GSYM rat_of_int_of_num]
  >> simp[rat_of_int_MUL]
QED

Theorem REAL_OF_RAT_LE:
  real_of_rat r1 <= real_of_rat r2 <=> r1 <= r2
Proof
  simp[REAL_LE_LT,rat_leq_def,REAL_OF_RAT_LT,REAL_OF_RAT_INJ]
QED

(* much, but not all, of the below is just for fun, mostly looking at proving Q is dense in R*)

Theorem INT_BI_INDUCTION:
  (P (0:int) /\ !x. (P x <=> P (x+1))) <=> !x. P x
Proof
  rw[EQ_IMP_THM] >> Cases_on ‘x’ >> simp[]
  >- (‘!m. P (&m)’ by (
       Induct_on ‘m’ >> simp[INT]
       )
      >> simp[]
     )
  >- (‘!m. P (-&m)’ by (
       Induct_on ‘m’
       >- simp[]
       >- (‘P ((-&m + -1) + 1)’ by simp[INT_ADD_LINV,GSYM INT_ADD_ASSOC] >> simp[INT,INT_NEG_ADD])
       )
      >> simp[]
     )
QED

Theorem INT_FLOOR_REAL_OF_INT:
  INT_FLOOR (real_of_int i) = i
Proof
  rw[real_of_int_def,INT_FLOOR_EQNS]
QED

Theorem IS_INT_REAL_OF_INT:
  is_int x <=> ?i. x = real_of_int i
Proof
  rw[EQ_IMP_THM,is_int_def]
  >-(qexists_tac ‘INT_FLOOR x’ >> simp[])
  >- simp[INT_FLOOR_REAL_OF_INT]
QED

Theorem IS_INT_NUM:
  is_int (&n)
Proof
  simp[is_int_def,INT_FLOOR_EQNS,real_of_int_num]
QED

Theorem IS_INT_ADD:
  is_int x /\ is_int y ==> is_int (x+y)
Proof
  rw[IS_INT_REAL_OF_INT] >> qexists_tac ‘i+i'’ >> simp[real_of_int_add]
QED

Theorem IS_INT_MUL:
  is_int x /\ is_int y ==> is_int (x*y)
Proof
  rw[IS_INT_REAL_OF_INT] >> qexists_tac ‘i * i'’ >> simp[real_of_int_mul]
QED

Theorem IS_INT_ADD2:
  is_int x /\ is_int (x+y) ==> is_int y
Proof
  rw[IS_INT_REAL_OF_INT] >> qexists_tac ‘i' - i’ >> simp[real_of_int_sub,REAL_EQ_SUB_LADD,Once REAL_ADD_SYM]
QED

Theorem INT_FLOOR_ADD:
  is_int x /\ is_int y ==> INT_FLOOR x + INT_FLOOR y = INT_FLOOR (x+y)
Proof
  rw[IS_INT_REAL_OF_INT] >> simp[INT_FLOOR_REAL_OF_INT]
QED

Theorem INT_FLOOR_MUL:
  is_int x /\ is_int y ==> INT_FLOOR x * INT_FLOOR y = INT_FLOOR (x*y)
Proof
  rw[IS_INT_REAL_OF_INT] >> once_rewrite_tac[GSYM real_of_int_mul] >> simp[INT_FLOOR_REAL_OF_INT]
QED

Theorem REAL_PYTH:
  !r1. ?x. is_int x /\ r1 < x
Proof
  rw[] >> qexists_tac ‘real_of_int (INT_FLOOR r1) + 1’
  >> ‘is_int 1’ by simp[is_int_def,INT_FLOOR_EQNS,real_of_int_num]
  >> simp[IS_INT_ADD,IS_INT_REAL_OF_INT]
  >> ‘1 = real_of_int 1’ by simp[real_of_int_num]
  >> simp[] >> once_rewrite_tac[GSYM real_of_int_add] >> simp[INT_FLOOR_BOUNDS]
QED

Theorem REAL_IS_INT_LT_LE:
  is_int a /\ is_int b ==> (a<b <=> a+1 <= b)
Proof
  rw[IS_INT_REAL_OF_INT] >> once_rewrite_tac[GSYM real_of_int_num] >> once_rewrite_tac[GSYM real_of_int_add] >> simp[]
QED

val _ = temp_delsimps["real_of_int_11"]

Theorem RAT_OF_INT_SUB:
  rat_of_int a - rat_of_int b = rat_of_int (a-b)
Proof
  simp[RAT_SUB_ADDAINV,int_sub,rat_of_int_ADD,GSYM rat_of_int_ainv]
QED

Theorem REAL_LT_SUB_SWAP:
  a:real < b-c <=> c<b-a
Proof
  simp[REAL_LT_SUB_LADD,REAL_ADD_SYM]
QED

Theorem REAL_Q_DENSE:
  !r1 r2. r1 < r2 ==> ?q:rat. r1 < real_of_rat q /\ real_of_rat q < r2
Proof
  rw[]
  >> ‘0 < r2 - r1’ by simp[REAL_SUB_LT]
  >> ‘?n. is_int n /\ 1/(r2-r1) < n’ by simp[REAL_PYTH]
  >> ‘0 < 1 / (r2 - r1)’ by simp[REAL_LT_DIV]
  >> ‘0 < n’ by metis_tac[REAL_LT_TRANS]
  >> ‘1/n < r2 - r1’ by (simp[REAL_LT_LDIV_EQ] >> once_rewrite_tac[REAL_MUL_SYM] >> simp[GSYM REAL_LT_LDIV_EQ])
  >> ‘?q. q = (rat_of_int (INT_FLOOR (r2*2*n)) - 1) / rat_of_int (INT_FLOOR (2*n))’ by simp[]
  >> qexists_tac ‘q’
  >> ‘is_int (2*n)’ by simp[IS_INT_MUL,IS_INT_NUM]
  >> ‘INT_FLOOR (2*n) <> 0’ by (
    ‘1 <= n’ by (PURE_REWRITE_TAC[Once $ GSYM REAL_ADD_LID] >> simp[GSYM REAL_IS_INT_LT_LE,IS_INT_NUM])
    >> once_rewrite_tac[GSYM real_of_int_11] >> simp[GSYM (iffLR is_int_def),real_of_int_num,REAL_LT_IMP_NE]
    )
  >> ‘r1 * (2*n) < r2 * (2 * n) - 2’ by (
    simp[Once $ REAL_LT_SUB_SWAP,GSYM REAL_SUB_RDISTRIB, Once $ REAL_MUL_RID]
    >> ‘2 = 1/n * (2*n)’ by (simp[real_div] >> simp[REAL_MUL_ASSOC,REAL_MUL_SYM,REAL_MUL_RINV,REAL_MUL_LID,REAL_LT_IMP_NE])
    >> metis_tac[REAL_LT_RMUL,REAL_LT_MUL',arithmeticTheory.TWO,REAL_POS_LT]
    )
  >> rw[]
  >> ‘rat_of_int (INT_FLOOR (2*n)) <> 0’ by simp[]
  >> once_rewrite_tac[SPEC “1:num” $ GEN_ALL $ GSYM rat_of_int_of_num]
  >> simp[RAT_OF_INT_SUB]
  >> simp[GSYM REAL_OF_RAT_DIV] >> PURE_REWRITE_TAC[REAL_OF_RAT_OF_INT] >> simp[GSYM $ iffLR is_int_def]
  >- (simp[REAL_LT_RDIV_EQ,REAL_LT_MUL',real_of_int_num]
      >> ‘r2 * (2*n) - 2 < real_of_int (INT_FLOOR (r2 * 2 * n)) - 1’ suffices_by metis_tac[REAL_LT_TRANS]
      >> once_rewrite_tac[SPECL [“x:real”,“y:real”,“1:real”] $ GSYM REAL_LT_RADD]
      >> PURE_REWRITE_TAC[REAL_SUB_ADD]
      >> ‘!x. x-2+1=x-1:real’ by simp[real_sub,GSYM REAL_ADD_ASSOC,add_ints]
      >> simp[REAL_MUL_ASSOC, INT_FLOOR_BOUNDS']
     )
  >- (simp[REAL_LT_LDIV_EQ,REAL_LT_MUL',real_of_int_num]
      >> ‘-1 < 0:real’ by simp[]
      >> metis_tac[REAL_ADD_RID,REAL_LTE_ADD2,INT_FLOOR_BOUNDS,REAL_ADD_SYM,REAL_MUL_ASSOC,real_sub]
     )
QED

Theorem REAL_OF_RAT_NUM_CLAUSES:
  (real_of_rat q = &n <=> q = &n) /\ (real_of_rat q = -&n <=> q = -&n) /\
  (real_of_rat q < &n <=> q < &n) /\ (real_of_rat q < -&n <=> q < -&n) /\
  (real_of_rat q <= &n <=> q <= &n) /\ (real_of_rat q <= -&n <=> q <= -&n) /\
  (&n < real_of_rat q <=> &n < q) /\ (-&n < real_of_rat q <=> -&n < q) /\
  (&n <= real_of_rat q <=> &n <= q) /\ (-&n <= real_of_rat q <=> -&n <= q)
Proof
  once_rewrite_tac[GSYM REAL_OF_RAT_OF_NUM] >> simp[REAL_OF_RAT_NEG,REAL_OF_RAT_INJ,REAL_OF_RAT_LT,REAL_OF_RAT_LE]
QED

Theorem REAL_OF_RAT_MAX:
  max (real_of_rat r) (real_of_rat q) = real_of_rat (rat_max r q)
Proof
  Cases_on ‘r <= q’ >> simp[REAL_OF_RAT_LE,real_max,rat_max_def,rat_gre_def,GSYM RAT_LES_LEQ]
QED

Theorem REAL_OF_RAT_MIN:
  min (real_of_rat r) (real_of_rat q) = real_of_rat (rat_min r q)
Proof
  Cases_on ‘r<q’ >> simp[Once $ cj 1 REAL_MIN_ACI,rat_min_def,GSYM REAL_NOT_LT,real_min,REAL_OF_RAT_LT]
QED

val _ = export_theory();
