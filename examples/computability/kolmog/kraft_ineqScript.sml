
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
open recfunsTheory;
open extNatTheory;
open prtermTheory;
open pred_setTheory;
open extrealTheory;
open realTheory;
open real_sigmaTheory;
open lebesgueTheory;
open transcTheory;
open boolListsTheory;

local open util_probTheory in end

val _ = new_theory "kraft_ineq";

val _ = intLib.deprecate_int()




Definition len_fun_def:
  len_fun (A:bool list set) n =
  let strs = {s | (LENGTH s = n) /\ s IN A}
  in
    EXTREAL_SUM_IMAGE (\s. Normal (2 rpow (- &(LENGTH s)))) strs
End

Theorem extreal_sum_image_finite_corr = extrealTheory.EXTREAL_SUM_IMAGE_FINITE_CONST;

Theorem bool_list_card[simp]:
  CARD {s | LENGTH (s:bool list) = n} = 2**n
Proof
  Induct_on‘n’>>simp[LENGTH_CONS] >> qmatch_abbrev_tac‘CARD s = 2**(SUC n)’>>
  ‘s = IMAGE (CONS T) {s | LENGTH s = n} ∪ IMAGE (CONS F) {s | LENGTH s = n}’
    by (simp[Abbr‘s’,EXTENSION,EQ_IMP_THM] >> rw[] ) >>
  simp[CARD_UNION_EQN,CARD_INJ_IMAGE,EXP] >>
  qmatch_abbrev_tac‘(x:num)-y=x’ >>
  ‘y=0’ suffices_by simp[] >> simp[Abbr‘y’,EXTENSION] >>Cases>>simp[]>>
  metis_tac[]
QED

Theorem len_fun_eq1:
  SIGMA (\s. Normal (2 rpow -&LENGTH s)) {s | (LENGTH (s:bool list) = n)} = 1
Proof
  irule EQ_TRANS >>
  qexists_tac‘&CARD {s | LENGTH (s:bool list) = n} * Normal(2 rpow (-&n))’ >>
  conj_tac
  >- (irule extreal_sum_image_finite_corr >> rw[])
  >- (simp[extreal_of_num_def,extreal_mul_def,GSYM realTheory.REAL_OF_NUM_POW,
           GEN_RPOW, GSYM RPOW_ADD,RPOW_0 ] )
QED

Theorem len_fun_le1:
  len_fun A n <= 1
Proof
  rw[len_fun_def] >>
  ‘{s | LENGTH s = n /\ s IN A} SUBSET {s|LENGTH s = n}’ by simp[SUBSET_DEF] >>
  ‘FINITE {s | LENGTH s = n /\ s IN A}’
    by metis_tac[SUBSET_FINITE_I,finite_bool_list_n] >>
  ASSUME_TAC len_fun_eq1 >> pop_assum(SUBST1_TAC o SYM)>>
  irule EXTREAL_SUM_IMAGE_MONO_SET >>
  simp[finite_bool_list_n] >> rw[extreal_of_num_def,extreal_le_def] >>
  ‘0r < 2 ’suffices_by(strip_tac >> drule RPOW_POS_LT >>
                       simp[realTheory.REAL_LE_LT]) >>
  simp[]
QED

(* Traditional bool list to num *)
Theorem rev_fpow[simp]: REVERSE (Fpow n) = Fpow n
Proof simp[Fpow_def,REVERSE_GENLIST,combinTheory.K_DEF]
QED

Theorem rev_tpow[simp]: REVERSE (Tpow n) = Tpow n
Proof simp[Tpow_def,REVERSE_GENLIST,combinTheory.K_DEF]
QED

(* binary numbers in little-endian format *)
Definition tbl2n_def[simp]:
  tbl2n [] = 0n /\
  tbl2n (T::t) = 2*tbl2n t + 1 /\
  tbl2n (F::t) = 2*tbl2n t
End

(* binary numbers in big-endian format *)
Overload TBL2N = “\l. tbl2n (REVERSE l)”

Definition inv_tbl2n_def:
  inv_tbl2n 0n = [] /\
  inv_tbl2n a = if EVEN a then [F]++(inv_tbl2n (a DIV 2))
                else [T]++(inv_tbl2n ((a-1) DIV 2 ))
Termination
  WF_REL_TAC‘$<’ >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac‘v’ >> ‘0<2n’ by simp[] >>
  rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ]
End

Theorem tbl2n_inv_tbl2n[simp]:
  tbl2n (inv_tbl2n n) = n
Proof
  completeInduct_on ‘n’ >> Cases_on‘n’ >> simp[tbl2n_def,inv_tbl2n_def] >>
  Cases_on‘EVEN (SUC n')’ >>
  simp[tbl2n_def]
  >- (‘2 * (SUC n' DIV 2) = (SUC n' DIV 2)*2’ by simp[MULT_COMM] >>
      ‘0<2n’ by simp[] >>
      ‘SUC n' MOD 2=0’ by metis_tac[EVEN_MOD2] >>
      ‘SUC n' DIV 2 * 2 + SUC n' MOD 2 = SUC n'’ by metis_tac[GSYM DIVISION] >>
      fs[])
  >- (‘0<2n’ by simp[] >> ‘n' DIV 2 <= n'’ by simp[DIV_LESS_EQ] >>
      ‘n' DIV 2 < SUC n'’ by
        simp[LESS_EQ_IMP_LESS_SUC] >> fs[] >>
      ‘EVEN n'’ by metis_tac[ODD,EVEN_OR_ODD] >>
      ‘2 * (n' DIV 2) =  (n' DIV 2)*2’ by simp[MULT_COMM] >> ‘0<2n’ by simp[] >>
      ‘n' MOD 2=0’ by metis_tac[EVEN_MOD2] >>
      ‘n' DIV 2 * 2 + n' MOD 2 = n'’ by metis_tac[GSYM DIVISION] >> fs[] )
QED

Definition interval_bl_def:
  interval_bl l = (&(TBL2N l) * (2 rpow -&LENGTH l), 2 rpow -&LENGTH l)
End

Definition disjoint_interval_def:
  disjoint_interval ((m:real),i) (n,j) <=>
  DISJOINT {r|m<=r /\ r<m+i} {r|n<=r /\ r<n+j}
End

Theorem tbl2n_exp2: tbl2n i * 2 ** n = tbl2n (Fpow n ++ i)
Proof
  rw[Fpow_def] >> Induct_on‘n’ >> simp[tbl2n_def,EXP,GENLIST_CONS]
QED

Theorem TBL2N_exp2: TBL2N i * 2 ** n = TBL2N (i ++ Fpow n)
Proof
  simp[REVERSE_APPEND] >> rw[Fpow_def] >> Induct_on‘n’ >>
  simp[tbl2n_def,EXP,GENLIST_CONS]
QED

Theorem tbl2n_lead0s[simp]: tbl2n (x ++ Fpow n) = tbl2n x
Proof
  Induct_on‘x’ >> simp[tbl2n_def]
  >- (‘tbl2n (Fpow n ++ []) = tbl2n (Fpow n )’ by simp[] >>
      ‘tbl2n (Fpow n ++ []) = (tbl2n []) *2**n’ by metis_tac[GSYM tbl2n_exp2] >>
      fs[tbl2n_def])
  >- (Cases_on ‘h’ >> simp[tbl2n_def])
QED

Theorem tbl2n_fpow[simp]: tbl2n (Fpow n) = 0
Proof simp[Fpow_def] >> Induct_on‘n’ >> simp[GENLIST_CONS]
QED

Theorem len_fpow[simp]: LENGTH (Fpow n) = n
Proof simp[Fpow_def]
QED

Theorem TBL2N_lead0s[simp]: TBL2N (Fpow n ++ x) = TBL2N x
Proof simp[REVERSE_APPEND]
QED

Theorem tbl2n_append_1:
  tbl2n (x++[e]) = if e then 2**(LENGTH x) + (tbl2n x) else tbl2n x
Proof
  Induct_on‘x’ >> simp[] >- (Cases_on‘e’ >> simp[]) >> Cases_on‘h’ >> simp[] >>
  rw[] >> simp[EXP]
QED

Theorem tbl2n_append: !y. tbl2n (x++y) = tbl2n x + 2**(LENGTH x) * tbl2n y
Proof
  Induct_on‘x’ >> simp[] >> Cases_on‘h’ >> simp[EXP]
QED

Theorem TBL2N_append:
  TBL2N (p++s) = 2**LENGTH s * (TBL2N p) +TBL2N s
Proof simp[REVERSE_APPEND,tbl2n_append]
QED

Theorem tbl2n_ub[simp]: tbl2n l < 2**(LENGTH l)
Proof Induct_on‘l’ >> simp[] >> Cases_on‘h’ >> simp[EXP]
QED

Theorem TBL2N_ub[simp]: TBL2N l < 2**(LENGTH l)
Proof metis_tac[tbl2n_ub,LENGTH_REVERSE]
QED

Theorem TBL2N_inj_len:
  !x y.(LENGTH x = LENGTH y) ==> (TBL2N x = TBL2N y <=> x=y)
Proof
  Induct_on‘x’ >> simp[] >> Cases_on‘y’ >> simp[] >> rw[tbl2n_append_1] >>
  ‘TBL2N t < 2** LENGTH t’ by  (metis_tac[tbl2n_ub,LENGTH_REVERSE]) >>
  ‘TBL2N x < 2** LENGTH t’ by  (metis_tac[tbl2n_ub,LENGTH_REVERSE]) >>simp[]
QED

Theorem TBL2N_lem1:
  !d. d<2**D ==>
      ?l. TBL2N l = d /\ LENGTH l = D /\
          TBL2N (i++Fpow D) +d = TBL2N (i++l)
Proof
  Induct_on‘D’ >- simp[Fpow_def] >> rw[EXP] >> Cases_on‘d<2**D’ >> fs[]
  >- (res_tac >> qexists_tac‘F::l’ >> simp[] >> fs[REVERSE_APPEND] >>
      simp[tbl2n_append])
  >- (qabbrev_tac‘d0=d-2**D’ >> ‘d0 < 2**D’ by simp[Abbr‘d0’] >> res_tac >>
      qexists_tac‘T::l’ >>
      simp[] >>fs[REVERSE_APPEND] >> simp[tbl2n_append] >> simp[Abbr‘d0’] )
QED

Theorem disjoint_pf_lem1:
  TBL2N i * 2 ** (LENGTH j - LENGTH i) <= TBL2N j /\
  TBL2N j < (TBL2N i + 1) * 2 ** (LENGTH j - LENGTH i) /\
  LENGTH i < LENGTH j ==>
  i ≺ j
Proof
  rw[TBL2N_exp2] >> qabbrev_tac‘D=LENGTH j − LENGTH i’ >>
  ‘TBL2N (i ++ Fpow D) + (TBL2N j-TBL2N (i ++ Fpow D)) = TBL2N j’ by simp[] >>
  qabbrev_tac‘d=TBL2N j-TBL2N (i ++ Fpow D)’ >>
  ‘d<2**D’
    by (fs[RIGHT_ADD_DISTRIB] >>
        ‘TBL2N j - TBL2N i * 2 ** D < 2 ** D’ by simp[] >>
        ‘TBL2N j − TBL2N (i ++ Fpow D) < 2**D’ by simp[GSYM TBL2N_exp2] >>
        fs[Abbr‘d’] ) >>
  ‘?l. TBL2N l = d /\ LENGTH l = D /\ TBL2N (i++Fpow D) +d = TBL2N (i++l)’
    by simp[TBL2N_lem1] >>
  ‘TBL2N (i ++ l) = TBL2N j’ by simp[] >>
  ‘LENGTH (i++l) = LENGTH j’ by simp[Abbr‘D’] >>
  ‘i++l = j’ by metis_tac[TBL2N_inj_len] >> ‘0<LENGTH l’ by simp[Abbr‘D’] >>
  metis_tac[prefix_lem1]
QED

Theorem powr_negexp:
  0 < a ⇒ (a:real) powr -&x = inv (a pow x)
Proof
  ‘-&x = 0r - &x’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[RPOW_SUB, RPOW_0, GSYM REAL_INV_1OVER, GSYM GEN_RPOW]
QED

Theorem disjoint_prefix_free:
  prefix_free P <=>
  let is = IMAGE interval_bl P
  in
    !i1 i2. i1 IN is /\ i2 IN is /\ i1<>i2 ==> disjoint_interval i1 i2
Proof
  rw[EQ_IMP_THM]
  >- (rename[‘interval_bl i = interval_bl j’] >>
      ‘~(i ≺ j) /\ ~(j ≺ i)/\ i<>j’ by metis_tac[prefix_free_def] >>
      fs[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION] >>
      rw[GSYM DISJ_ASSOC] >> rw[DECIDE“~p\/q <=> p==>q”] >> strip_tac >>
      ‘LENGTH i <> LENGTH j’
        by (strip_tac >> fs[] >> qabbrev_tac‘M = 2 rpow -&LENGTH j’ >>
            ‘&TBL2N i * M < &TBL2N j * M + M’ by metis_tac[REAL_LET_TRANS] >>
            ‘&TBL2N j * M < &TBL2N i * M + M’ by metis_tac[REAL_LET_TRANS] >>
            ‘&TBL2N i * M + M = (&TBL2N i + 1) * M’
              by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >>
            ‘&TBL2N j * M + M = (&TBL2N j + 1) * M’
              by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >> fs[] >>
            ‘(0:real)<2’ by fs[] >> ‘0<M’ by metis_tac[RPOW_POS_LT] >>
            ‘((&TBL2N i) :real) < &(TBL2N j + 1)’ by fs[REAL_LT_RMUL] >>
            ‘((&TBL2N j):real) < &(TBL2N i + 1)’ by fs[REAL_LT_RMUL] >> fs[]) >>
      wlog_tac ‘LENGTH i < LENGTH j’ [‘i’,‘j’,‘x’]
      >- (‘LENGTH j < LENGTH i’ by simp[] >> metis_tac[]) >>
      qabbrev_tac‘D=LENGTH j − LENGTH i’ >> qabbrev_tac‘ii= TBL2N i’ >>
      qabbrev_tac‘jj= TBL2N j’ >>
      fs[powr_negexp,RealArith.REAL_ARITH “(x:real) * y + y = (x + 1) * y”] >>
      ‘&ii * 2 pow LENGTH j ≤ x * 2 pow LENGTH i * 2 pow LENGTH j’ by simp[] >>
      ‘x * 2 pow LENGTH i * 2 pow LENGTH j < &(jj + 1) * 2 pow LENGTH i’
        by simp[] >>
      dxrule_all_then strip_assume_tac REAL_LET_TRANS >>
      dxrule_then (qspec_then ‘inv (2 pow LENGTH i)’ mp_tac) REAL_LT_RMUL_IMP >>
      impl_tac >- simp[REAL_POW_POS] >>
      REWRITE_TAC [GSYM REAL_MUL_ASSOC, REAL_INV_nonzerop, GSYM REAL_POW_INV] >>
      ASM_SIMP_TAC bool_ss [pow_inv_mul_invlt] >>
      simp[REAL_OF_NUM_POW, DECIDE “x < y + 1n ⇔ x ≤ y”] >> strip_tac >>
      ‘&jj * 2 pow LENGTH i ≤ x * 2 pow LENGTH i * 2 pow LENGTH j’ by simp[] >>
      ‘x * 2 pow LENGTH i * 2 pow LENGTH j < &(ii + 1) * 2 pow LENGTH j’
        by simp[] >>
      dxrule_all_then strip_assume_tac REAL_LET_TRANS >>
      dxrule_then (qspec_then ‘inv (2 pow LENGTH i)’ mp_tac) REAL_LT_RMUL_IMP >>
      impl_tac >- simp[REAL_POW_POS] >>
      REWRITE_TAC [GSYM REAL_MUL_ASSOC, REAL_INV_nonzerop, GSYM REAL_POW_INV] >>
      ASM_SIMP_TAC bool_ss [pow_inv_mul_invlt] >> simp[] >> strip_tac >>
      fs[REAL_OF_NUM_POW] >> metis_tac[disjoint_pf_lem1])
  >- (fs[prefix_free_def,PULL_EXISTS] >>rw[] >>
      strip_tac >>
      ‘interval_bl a <> interval_bl b’ by
        (fs[interval_bl_def] >> rw[] >>
         ‘LENGTH a < LENGTH b’ by simp[prefix_length_lt]>>
         ‘real_of_num (LENGTH a) < real_of_num (LENGTH b)’ by fs[REAL_LT] >>
         ‘-(real_of_num (LENGTH b)) < -(real_of_num(LENGTH a))’
           by fs[REAL_LT_NEG] >>
         ‘1<(2:real)’ by simp[]>>
         ‘2 rpow -&LENGTH b < 2 rpow -&LENGTH a’ by fs[RPOW_LT]>>
         fs[REAL_LT_IMP_NE])>>
      first_x_assum drule_all >>
      fs[interval_bl_def,disjoint_interval_def] >> rw[DISJOINT_DEF,EXTENSION] >>
      qexists_tac‘&TBL2N b * 2 rpow -&LENGTH b’ >> rw[]
      >- (fs[powr_negexp, prefix_append,TBL2N_append, REAL_OF_NUM_POW,
             RIGHT_ADD_DISTRIB] >>
          REWRITE_TAC [GSYM MULT_ASSOC, arithmeticTheory.EXP_ADD] >> simp[])
      >- (fs[powr_negexp, prefix_append,TBL2N_append] >>
          simp[POW_ADD, REAL_LDISTRIB] >> simp[REAL_OF_NUM_POW])
      >- (simp[powr_negexp, REAL_LDISTRIB]))
QED

Theorem size_of_interval_bl:
  Normal (SND (interval_bl y))  = Normal (2 rpow -&LENGTH y)
Proof rw[interval_bl_def]
QED

Theorem TBL2N_append_sing_ub:
  &(TBL2N (a++[h]) + 1)*2 rpow (-1) <= &(TBL2N a + 1)
Proof
  ‘&(2 * TBL2N a + 2) * 2 rpow -1 <= &(TBL2N a + 1)’
    by (‘&(2 * TBL2N a + 2) * 2 rpow -1 = &(2*(TBL2N a + 1)) * 2 rpow -1’
          by fs[GSYM LEFT_ADD_DISTRIB]>>
        ‘_ = 2 * &(TBL2N a + 1) * 2 rpow -1’ by fs[REAL_MUL] >>
        ‘_ = &(TBL2N a + 1)*(2 rpow 1 * 2 rpow -1)’
          by fs[AC REAL_MUL_ASSOC REAL_MUL_COMM,RPOW_1]>>
        ‘_ = &(TBL2N a + 1) * 2 rpow (1+ -1)’ by fs[RPOW_ADD] >>
        fs[RPOW_0,REAL_ADD_RINV]  ) >>
  Cases_on‘h’ >> rw[TBL2N_append] >>
  ‘&(2 * TBL2N a + 1) * 2 rpow -1 <= &(2 * TBL2N a + 2) * 2 rpow -1’
    by (irule REAL_LE_RMUL_IMP >> rw[RPOW_POS_LT,REAL_LE_LT]) >>
  irule REAL_LE_TRANS >> qexists_tac‘&(2 * TBL2N a + 2) * 2 rpow -1’ >> rw[]
QED

Theorem interval_bl_bounds:
  0 ≤ FST (interval_bl a) /\ FST (interval_bl a) + SND (interval_bl a) ≤ 1
Proof
  rw[]
  >- simp[interval_bl_def, powr_negexp]
  >- (simp[interval_bl_def, powr_negexp,
           RealArith.REAL_ARITH “x * y + y :real = (x + 1) * y”] >>
      simp[REAL_OF_NUM_POW] >>
      (TBL2N_ub |> Q.INST [‘l’|->‘a’] |> assume_tac) >> simp[])
QED

Definition bls_size_def:
  bls_size (P:bool list -> bool) n =
  SIGMA (\s. (2 rpow -&LENGTH s)) {x|x IN P /\ LENGTH x < n }
End

Theorem finite_and:
  FINITE {s| P s} ==> FINITE {s|  Q s /\ P s}
Proof
  rw[] >> ‘{s | Q s /\ P s} = {s | Q s}  INTER {s | P s}’ by fs[INTER_DEF] >>
  fs[FINITE_INTER]
QED

Theorem interval_bl_sigma:
  FINITE  {x | x IN P} ==>
  SIGMA (\a. SND (interval_bl a)) {x | x IN P} =
  SIGMA (\a. 2 rpow -&LENGTH a) {x | x IN P}
Proof
  rw[] >> irule REAL_SUM_IMAGE_EQ >> rw[] >> simp[interval_bl_def]
QED

fun fsr thl = full_simp_tac(srw_ss () ++ realSimps.REAL_ARITH_ss) thl;

Theorem disjoint_interval_thm:
  disjoint_interval (interval_bl i) (interval_bl j) ==>
  FST (interval_bl i) + SND (interval_bl i) <= FST (interval_bl j) \/
  FST (interval_bl j) + SND (interval_bl j) <= FST (interval_bl i)
Proof
  rw[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION,
     PULL_EXISTS] >>
  Cases_on‘&TBL2N i * 2 rpow -&LENGTH i + 2 rpow -&LENGTH i <
           &TBL2N j * 2 rpow -&LENGTH j’ >>
  fsr[]>>
  qabbrev_tac‘id=2 rpow -&LENGTH i’ >> qmatch_abbrev_tac‘_ \/ jj+jd<=ii:real’ >>
  spose_not_then assume_tac >>
  fsr[REAL_NOT_LT,REAL_NOT_LE]  >>
  first_x_assum(fn th => qspec_then‘jj’ assume_tac th >>
                qspec_then‘ii’ assume_tac th) >> fsr[]
  >- (‘id<= 0’ by metis_tac[REAL_LE_LADD,REAL_ADD_RID] >>
      ‘0<id’ suffices_by metis_tac[REAL_LET_TRANS,REAL_LT_REFL] >>
      simp[Abbr‘id’,RPOW_POS_LT])
  >- (‘jd<= 0’ by metis_tac[REAL_LE_LADD,REAL_ADD_RID] >>
      ‘0<jd’ suffices_by metis_tac[REAL_LET_TRANS,REAL_LT_REFL] >>
      simp[Abbr‘jd’,RPOW_POS_LT])
QED

Triviality max_rs_lemma:
  !s. FINITE s ==> s<>{} ==> ?x:real. x IN s /\ !y. y IN s ==> y<=x
Proof
  Induct_on‘FINITE’ >>rw[] >> Cases_on‘s={}’ >> fs[] >> qexists_tac‘max e x’ >>
  fsr[max_def] >> rw[]
  >- metis_tac[] >> Cases_on‘y=e’>> fsr[] >> RES_TAC >> fsr[]
QED

Triviality min_rs_lemma:
  !s. FINITE s ==> s<>{} ==> ?x:real. x IN s /\ !y. y IN s ==> x<=y
Proof
  Induct_on‘FINITE’ >>rw[] >> Cases_on‘s={}’ >> fs[] >> qexists_tac‘min e x’ >>
  fsr[min_def] >> rw[]>>
  Cases_on‘y=e’>> fsr[] >> RES_TAC >> fsr[]
QED

Theorem maxr_set_def = new_specification(
  "maxr_set_def",["maxr_set"],
  SIMP_RULE(srw_ss() )[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] max_rs_lemma
  );

Theorem minr_set_def = new_specification(
  "minr_set_def",["minr_set"],
  SIMP_RULE(srw_ss() )[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] min_rs_lemma);

Definition exten_def:
  exten s = (minr_set {FST k| k IN s},maxr_set {FST k + SND k|k IN s})
End

Theorem maxr_set_thm[simp]:
  maxr_set {e} = e /\
  (FINITE s /\ s<> {} ==> maxr_set (e INSERT s) = max e (maxr_set s))
Proof
  rw[] >- (qspec_then ‘{e}’ mp_tac maxr_set_def >> simp[]) >>
  qspec_then ‘e INSERT s’ mp_tac maxr_set_def  >> simp[] >> strip_tac >>
  qabbrev_tac‘m = maxr_set (e INSERT s)’ >> qspec_then‘s’ mp_tac maxr_set_def >>
  simp[] >>
  qabbrev_tac‘m0 = maxr_set s’ >> rw[] >> rw[max_def]
  >- (Cases_on‘e = m0’ >> rw[] >- (simp[Abbr‘m’,ABSORPTION_RWT]) >>
      Cases_on‘e=m’ >> rw[]
      >- (‘m0<=e’ by metis_tac[] >> fsr[]) >> metis_tac[REAL_LE_ANTISYM]  ) >>
  spose_not_then strip_assume_tac >> ‘m<=m0’ by fsr[] >> ‘m<e’ by fsr[] >>
  ‘e<=m’ by fsr[] >> fsr[]
QED

Theorem minr_set_thm[simp]:
  minr_set {e} = e /\
  (FINITE s /\ s<> {} ==> minr_set (e INSERT s) = min e (minr_set s))
Proof
  rw[] >- (qspec_then ‘{e}’ mp_tac minr_set_def >> simp[]) >>
  qspec_then ‘e INSERT s’ mp_tac minr_set_def  >> simp[] >> strip_tac >>
  qabbrev_tac‘m = minr_set (e INSERT s)’ >> qspec_then‘s’ mp_tac minr_set_def >>
  simp[] >>
  qabbrev_tac‘m0 = minr_set s’ >> rw[] >> rw[min_def]
  >- (Cases_on‘e = m0’ >> rw[] >- (simp[Abbr‘m’,ABSORPTION_RWT]) >>
      Cases_on‘e=m’ >> rw[] >>
      ‘m<=e’ by metis_tac[] >>‘m IN s’ by fs[] >>‘m0<=m’ by fs[] >>
      metis_tac[REAL_LE_ANTISYM]) >>
  spose_not_then strip_assume_tac >> ‘m<=m0’ by fsr[] >> ‘m0<e’ by fsr[] >>
  ‘m<=e’ by fsr[] >>
  Cases_on‘m=e’ >> fsr[] >> ‘m0 <= m’ by fsr[] >> fsr[]
QED

Theorem maxr_set_union:
  !s1. FINITE s1 ==>
       !s2. FINITE s2 ==>
            s1 <> EMPTY /\ s2 <> EMPTY ==>
            maxr_set (s1 UNION s2)=max (maxr_set s1) (maxr_set s2)
Proof
Induct_on‘FINITE’ >> strip_tac
>- (Induct_on‘FINITE’ >>rw[maxr_set_thm] )
>- (ntac 4 strip_tac >> Induct_on‘FINITE’ >> rw[maxr_set_thm] >>
    Cases_on‘s2 <> {}’ >> Cases_on‘s1 <> {}’ >> rw[] >>simp[maxr_set_thm]
    >- (Cases_on‘e<= maxr_set s1’ >> Cases_on‘e'<= maxr_set s2’ >>
        fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[]
        >- (Cases_on‘maxr_set s1 <= maxr_set s2’ >> fsr[])
        >- (Cases_on‘maxr_set s1 <= e'’ >> fsr[]) )
    >- (Cases_on‘e'<= maxr_set s2’ >>
        fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[])
    >- (Cases_on‘e<= maxr_set s1’ >> fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >>
        fsr[] >> Cases_on‘maxr_set s1 <= e'’ >> fsr[])
    >- (fs[max_def,maxr_set_thm,INSERT_UNION_EQ]) )
QED


Theorem minr_set_union:
  !s1. FINITE s1 ==>
       !s2. FINITE s2 ==> s1 <> EMPTY /\ s2 <> EMPTY ==>
            minr_set (s1 UNION s2)=min (minr_set s1) (minr_set s2)
Proof
Induct_on‘FINITE’ >> strip_tac
>- (Induct_on‘FINITE’ >>rw[minr_set_thm] )
>- (ntac 4 strip_tac >> Induct_on‘FINITE’ >> rw[minr_set_thm] >>
    Cases_on‘s2 <> {}’ >> Cases_on‘s1 <> {}’ >> rw[] >>simp[minr_set_thm]
    >- (Cases_on‘e<= minr_set s1’ >> Cases_on‘e'<= minr_set s2’ >>
        fs[min_def,minr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[]
        >- (Cases_on‘minr_set s1 <= e'’ >> fsr[])
        >- (Cases_on‘minr_set s1 <= minr_set s2’ >> fsr[]) )
    >- (Cases_on‘e<= minr_set s1’ >> fs[min_def,minr_set_thm,INSERT_UNION_EQ] >>
        rw[] >> fsr[] >> Cases_on‘minr_set s1 <= e'’ >> fsr[])
    >- (Cases_on‘e<= minr_set s1’ >> fs[min_def,minr_set_thm,INSERT_UNION_EQ] >>
        rw[] >> fsr[] >> Cases_on‘ minr_set s1 <= e'’ >>rw[] >> fsr[])
    >- (fs[min_def,minr_set_thm,INSERT_UNION_EQ]) )
QED

Theorem gspec_eq[simp]: GSPEC (\x. (f x,x=k)) = {f k}
Proof simp[EXTENSION]
QED

Theorem gspec_f_or[simp]:
  !P Q. {f x | P x \/ Q x} = {f x | P x} UNION {f x | Q x}
Proof
  rw[IN_UNION,EXTENSION] >> metis_tac[GSPECIFICATION_applied]
QED

Theorem exten_insert_thm:
  s ≠ ∅ /\ FINITE s ==>
  exten (e INSERT s) =  (min (FST e) ## max (FST e + SND e)) (exten s)
Proof
  simp[exten_def,maxr_set_thm,minr_set_thm] >> rw[]
  >- (‘{FST k | k <> e ==> k IN s} = {FST k | k = e \/ k IN s}’
        by fs[EXTENSION] >>
      ‘{FST k | k = e \/ k IN s} = {FST k | k = e} UNION {FST k | k IN s}’
        by fs[] >> rw[] >>
      ‘FINITE {FST e}’ by fs[] >> ‘{FST e} <> {}’ by fs[] >>
      ‘FINITE {FST k | k IN s}’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
      ‘{FST k | k IN s} <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF]>>
      rw[minr_set_union])
  >- (‘{FST k + SND k | k <> e ==> k IN s} = {FST k + SND k | k = e \/ k IN s}’
        by fs[EXTENSION] >>
      ‘{FST k + SND k | k = e ∨ k ∈ s} =
       {FST k + SND k | k = e} ∪ {FST k + SND k | k IN s}’ by fs[] >>
      rw[] >>
      ‘FINITE {FST e  + SND k}’ by fs[] >> ‘{FST e  + SND k} <> {}’ by fs[] >>
      ‘FINITE {FST k + SND k | k IN s}’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
      ‘{FST k + SND k | k IN s} <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF]>>
      rw[maxr_set_union] )
QED

Theorem TBL2N_ub2:
  &TBL2N x * 2 rpow -&LENGTH x +  2 rpow -&LENGTH x <= 1
Proof
  simp[powr_negexp, RealArith.REAL_ARITH “(x:real) * y + y = (x + 1) * y”,
       REAL_OF_NUM_POW] >>
  (TBL2N_ub |> Q.INST [‘l’|->‘x’] |> assume_tac) >> simp[TBL2N_ub]
QED

val rpow_len_lb = Q.store_thm("rpow_len_lb",
‘0<  2 rpow -&LENGTH x’,
fs[RPOW_POS_LT]);

Theorem TBL2N_lb:
  0 <= &TBL2N x * 2 rpow -&LENGTH x
Proof
  simp[powr_negexp]
QED

Theorem lemma11:
  !s. FINITE s ==>
      (!x dx y dy. (x,dx) IN s /\ (y,dy) IN s /\ x<>y ==> x+dx<=y \/ y+dy<=x) /\
      (!x d. (x,d) IN s ==> 0r<d) /\ (!x d. (x,d) IN s ==> 0<= x /\ x+d <=1) /\
      (s <> {})
      ==> 0 <= FST (exten s) /\ SND (exten s) <= 1
Proof
  Induct_on‘FINITE’ >> simp[] >>ntac 2 (gen_tac>>strip_tac) >>strip_tac >>
  Cases_on‘s={}’ >> fs[]
  >- (simp[maxr_set_def,minr_set_def,exten_def,ITSET_THM] >> Cases_on‘e’ >>
      fs[]) >>
  fs[exten_insert_thm] >> rw[max_def,min_def]
  >- (Cases_on‘e’ >> fsr[] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
QED

Theorem BETTER_RPOW_UNIQ_EXP[simp]:
  1r < a ==> (a rpow b = a rpow c <=> b = c)
Proof
  rw[] >> eq_tac >> simp[] >> rw[] >>
  pop_assum (mp_tac o AP_TERM “transc$ln”) >> fsr[LN_RPOW] >>
  disch_then irule >> ‘ln 1 < ln a’ by fsr[LN_MONO_LT] >> fsr[LN_1]
QED

Theorem interval_bl_11[simp]:
  interval_bl x = interval_bl y <=> x = y
Proof
  simp[interval_bl_def] >> eq_tac >> simp[] >> rw[] >>
  fsr[TBL2N_inj_len,RPOW_NZ]
QED

Theorem interval_bl_inj:
  INJ interval_bl P (IMAGE interval_bl P)
Proof
  simp[INJ_DEF]
QED

Theorem lemma12[local]:
  bls_size P n = SIGMA SND (IMAGE interval_bl {s|s IN P /\ LENGTH s < n})
Proof
  fs[bls_size_def,interval_bl_def,REAL_SUM_IMAGE_IMAGE,interval_bl_inj,
     finite_bool_list_lt_n,finite_and,combinTheory.o_DEF]
QED

Theorem exten_sing[simp]:
  exten {e} = (FST e,FST e + SND e)
Proof fs[exten_def]
QED

Theorem size_of_exten[local]:
  !s. FINITE s ==>
      (!x dx y dy. (x,dx) IN s /\ (y,dy) IN s /\ (x,dx)<>(y,dy) ==>
                   x+dx<=y \/ y+dy<=x) /\
      (!x d. (x,d) IN s ==> 0r<d) /\ (s <> {})
      ==> SIGMA SND s <= SND (exten s) - FST (exten s)
Proof
  HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION >> rw[] >>
  map_every qabbrev_tac [
      ‘Rs = {FST k + SND k | k IN s}’,‘Ls = {FST k |k IN s}’] >>
  ‘FINITE Ls’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
  ‘Ls <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>
  ‘?e1 e2. (e1,e2) IN s /\ !m. m IN Ls ==> e1<=m’
    by (qexists_tac ‘minr_set Ls’ >> qexists_tac‘@e'. (minr_set Ls,e') IN s’ >>
        reverse(rw[])
        >- (metis_tac[minr_set_def]) >> SELECT_ELIM_TAC >> simp[] >>
        ‘minr_set Ls IN Ls’ by metis_tac[minr_set_def] >> fs[Abbr‘Ls’] >>
        metis_tac[pairTheory.PAIR]) >>
  qabbrev_tac‘s0 = s DELETE (e1,e2)’ >> Cases_on‘s0={}’ >> simp[]
  >- (‘s = {(e1,e2)}’ by (metis_tac[DELETE_EQ_SING]) >>
      rw[REAL_SUM_IMAGE_THM] >> fsr[]) >>
  ‘s0 ⊂ s’ by (fs[Abbr‘s0’,PSUBSET_MEMBER]>> metis_tac[]) >>
  last_x_assum drule >> impl_tac
  >- (rw[Abbr‘s0’] >> metis_tac[]) >> ‘s = (e1,e2) INSERT s0’ by fs[Abbr‘s0’] >>
  ‘s0 DELETE (e1,e2) = s0’ by fs[Abbr‘s0’,ELT_IN_DELETE,DELETE_NON_ELEMENT] >>
  fsr[REAL_SUM_IMAGE_THM] >>
  ‘SND (exten s0) - FST (exten s0) ≤
   SND (exten ((e1,e2) INSERT s0)) − FST (exten ((e1,e2) INSERT s0)) - e2’
    suffices_by fsr[] >>
  fsr[exten_def,exten_insert_thm,REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >>
  map_every qabbrev_tac [‘MX = maxr_set {FST k + SND k | k IN s0}’,
                         ‘MN = minr_set  {FST k | k IN s0}’]>>
  map_every qabbrev_tac[‘Rs0 = {FST k + SND k | k IN s0}’,
                        ‘Ls0 = {FST k |k IN s0}’] >>
  ‘FINITE Ls0’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
  ‘Ls0 <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>
  ‘MN IN Ls0’ by metis_tac[minr_set_def] >>
  ‘?n. (MN,n) IN s0’ by
    (‘?p. p IN s0 /\ FST p = MN’ suffices_by
       (rw[] >> metis_tac[pairTheory.PAIR]) >>
     pop_assum MP_TAC >> simp[Abbr‘Ls0’] >> metis_tac[]) >>
  ‘MN IN Ls’ by (simp[Abbr‘Ls’] >>metis_tac[pairTheory.FST]) >>
  rw[max_def,min_def] >> fsr[]
  >- (‘e1 + e2 <= MN’ suffices_by fsr[] >>
      first_x_assum(qspecl_then[‘e1’,‘e2’,‘MN’,‘n’] MP_TAC) >> simp[] >>
      impl_tac
      >- (rpt strip_tac >> rw[] >> rw[Abbr‘s0’] >> fs[]) >> strip_tac >>
      ‘e1<=MN’ by fs[]>>
      ‘0<n’ suffices_by fsr[] >> metis_tac[]  )
  >- (‘MX < e1+e2’ by fsr[] >>
      ‘FINITE Rs0’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
      ‘Rs0 <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>
      ‘MX IN Rs0’ by metis_tac[maxr_set_def]>>
      ‘?i j. (i,j) IN s0 /\ MX = i+j’ by (pop_assum MP_TAC >> simp[Abbr‘Rs0’] >>
                                          metis_tac[pairTheory.PAIR]) >>
      first_x_assum(qspecl_then[‘e1’,‘e2’,‘i’,‘j’] MP_TAC) >> simp[] >> impl_tac
      >- (rpt strip_tac >> rw[] >> rw[Abbr‘s0’] >> fs[]) >> strip_tac
      >- (rw[] >> ‘0<j’ suffices_by fsr[] >> metis_tac[]) >> rw[] >>
      ‘i IN Ls’ by (simp[Abbr‘Ls’,pairTheory.EXISTS_PROD] >>metis_tac[])>>
      ‘e1<=i’ by simp[]>>
      ‘0<j’ suffices_by fsr[] >> metis_tac[]  )
QED

Theorem exten_member:
  FINITE s /\ s <> {} /\ exten (s) = (sn,sx) ==>
  ∃sn' sx' dx. (sn,sn') IN s /\ (sx',dx) IN s /\ sx'+dx=sx
Proof
  simp[exten_def] >> rw[] >>
  ‘{FST k|k IN s} = IMAGE FST s’ by simp[EXTENSION] >>
  ‘FINITE {FST k|k IN s} /\ {FST k | k IN s} <> {}’ by simp[] >>
  drule_all minr_set_def >>rw[] >>
  qexists_tac‘SND k’ >> simp[] >>
  ‘{FST k + SND k|k IN s} = IMAGE (\k. FST k+ SND k) s’ by simp[EXTENSION] >>
  ‘FINITE {FST k + SND k|k IN s} /\ {FST k + SND k | k IN s} <> {}’ by simp[] >>
  drule_all maxr_set_def >>
  rw[] >> rename[‘maxr_set _ = FST kk + SND kk’] >>
  map_every qexists_tac [‘FST kk’,‘SND kk’] >> simp[]
QED

Overload bpos = “λl. &TBL2N l * 2 rpow -&LENGTH l”

Theorem bpos_min:
  !s. FINITE s ==> s <> {} ==> ?l. l IN s /\ !m. m IN s ==> bpos l <= bpos m
Proof
  Induct_on‘FINITE’ >> simp[] >> rw[] >> Cases_on‘s={}’ >> simp[] >>fs[] >>
  Cases_on‘bpos e <= bpos l’>>
  fs[] >- (qexists_tac‘e’ >> simp[] >> metis_tac[REAL_LE_TRANS,REAL_LE_REFL]) >>
  qexists_tac‘l’ >> simp[] >> metis_tac[REAL_NOT_LE,REAL_LT_IMP_LE]
QED

Theorem exten_low_high:
  !s. FINITE s ∧ s <> {} ==>
      !low high. exten (IMAGE interval_bl s) = (low,high) ==> low <= high
Proof
  Induct_on‘FINITE’ >> simp[] >> rw[] >> Cases_on‘s={}’ >> simp[] >>fs[]
  >- (fs[interval_bl_def] >> rw[REAL_LE_ADDR] >> rw[RPOW_POS_LT,REAL_LE_LT]) >>
  qpat_x_assum‘exten _ = _’ mp_tac >> rfs[exten_insert_thm] >>
  Cases_on‘exten (IMAGE interval_bl s)’ >>
  fs[] >> fsr[interval_bl_def,min_def,max_def] >> rw[]>>fsr[]
QED

Theorem lemma13:
  ∀P. FINITE P ⇒
      P ≠ ∅ ∧
      (!x y. x ∈ P ∧ y ∈ P ∧ x ≠ y ==>
             disjoint_interval (interval_bl x) (interval_bl y)) ==>
      SIGMA (\s. 2 rpow -&LENGTH s) P + FST (exten (IMAGE interval_bl P) )
       <= SND (exten (IMAGE interval_bl P))
Proof
  HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION >> rw[] >>
  qmatch_abbrev_tac‘_ <= SND (exten s)’ >>
  ‘?l. l IN P /\ !m. m IN P ==> bpos l <= bpos m’ by metis_tac[bpos_min] >>
  qabbrev_tac‘P0 = P DELETE l’ >> Cases_on‘P0={}’ >> simp[]
  >- (‘P = {l}’ by metis_tac[DELETE_EQ_SING] >>
      fsr[REAL_SUM_IMAGE_THM,Abbr‘s’,interval_bl_def,TBL2N_lb,Abbr‘P0’]) >>
  ‘P0 ⊂ P’ by (fs[Abbr‘P0’,PSUBSET_MEMBER]>> metis_tac[]) >>
  last_x_assum drule >> impl_tac
  >- (rw[Abbr‘P0’] >> metis_tac[]) >> ‘P = l INSERT P0’ by fs[Abbr‘P0’] >>
  ‘P0 DELETE l = P0’ by fs[Abbr‘P0’,ELT_IN_DELETE,DELETE_NON_ELEMENT] >>
  fsr[REAL_SUM_IMAGE_THM,Abbr‘s’,exten_insert_thm] >>
  ‘∃en ex. exten (IMAGE interval_bl P0) = (en,ex)’
    by metis_tac[pairTheory.pair_CASES] >> simp[]>>
  ‘∃l0 d. interval_bl l = (l0,d)’ by metis_tac[pairTheory.pair_CASES] >> fs[] >>
  ‘2 rpow -&LENGTH l = d’ by fsr[interval_bl_def] >> fs[] >>
  ‘max (l0 + d) ex = d + max l0 (ex-d)’ by (fsr[max_def] >> rw[] >> fsr[]) >>
  fsr[GSYM REAL_ADD_ASSOC]>>
  ‘∃en'. (en,en') ∈ IMAGE interval_bl P0’
    by metis_tac[exten_member,IMAGE_FINITE,IMAGE_EQ_EMPTY]>> fs[]>>
  rename[‘(en,en') = interval_bl EN’] >>
  ‘l0+d<=en’
    by (first_x_assum (qspecl_then [‘l’,‘EN’] mp_tac) >>
        simp[] >> impl_tac >- (strip_tac >> fs[GSYM DELETE_NON_ELEMENT])  >>
        qpat_assum‘interval_bl _ = _’ (SUBST1_TAC o SYM) >> strip_tac >>
        drule disjoint_interval_thm >>
        qpat_x_assum‘_ = interval_bl _’ (assume_tac o SYM)>>
        simp[] >> strip_tac >>
        ‘&TBL2N l * d ≤ bpos EN’ by simp[] >> fs[interval_bl_def] >>rw[] >>
        ‘0<2 rpow -&LENGTH EN’ suffices_by fsr[] >> fs[RPOW_POS_LT]) >>
  ‘0 < d’ by (rw[] >> fsr[RPOW_POS_LT]) >>
  ‘l0 ≤ en’ by fsr[] >> simp[min_def] >>
  ‘en ≤ ex’ by metis_tac[exten_low_high] >>
  fsr[max_def]
QED

Theorem lemma1[local]:
  (let is = IMAGE interval_bl P
   in
     !i1 i2. i1 IN is /\ i2 IN is /\ i1<>i2 ==> disjoint_interval i1 i2)
  ==>
  !n. bls_size P n <= 1
Proof
  rw[EQ_IMP_THM,PULL_EXISTS] >> fs[bls_size_def,disjoint_interval_thm] >>
  ‘FINITE  {x | x IN P /\ LENGTH x < n}’
    by metis_tac[finite_and,finite_bool_list_lt_n] >>
  ‘FINITE {(\y. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y)) x |
           x IN {z | z IN P /\ LENGTH z <n}}’
    by metis_tac[IMAGE_FINITE,IMAGE_DEF] >> fs[] >>
  qabbrev_tac‘
   s = {(&TBL2N x * 2 rpow -&LENGTH x,2 rpow -&LENGTH x) |
        x IN P /\ LENGTH x < n}’ >>
  Cases_on‘s={}’
  >- (‘{x | x IN P /\ LENGTH x < n} = {}’
        by (fs[Abbr‘s’] >>
            ‘{(\y. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y))  x |
              x IN P /\ LENGTH x < n} = {}’
              by simp[] >>
            ‘IMAGE (\x. (&TBL2N x * 2 rpow -&LENGTH x,2 rpow -&LENGTH x))
               {x | x IN P /\ LENGTH x < n} =
             {(\y. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y))  x |
              x IN P /\ LENGTH x < n}’
              by fs[IMAGE_DEF] >> metis_tac[IMAGE_EQ_EMPTY]) >>
      fs[REAL_SUM_IMAGE_THM] ) >>
  ‘0<= FST (exten s) /\ SND (exten s) <= 1’ by
    (irule lemma11 >> rw[]>> fsr[Abbr‘s’,TBL2N_lb,rpow_len_lb,TBL2N_ub2] >>
     rw[] >> ‘x'<>x''’ by (metis_tac[FUN_EQ_THM]) >>
     ‘disjoint_interval (interval_bl x') (interval_bl x'')’ by simp[] >>
     ‘FST (interval_bl x') + SND (interval_bl x') <= FST (interval_bl x'') \/
      FST (interval_bl x'') + SND (interval_bl x'') <= FST (interval_bl x')’ by
       simp[disjoint_interval_thm]  >> fs[interval_bl_def] ) >>
  qmatch_abbrev_tac‘SIGMA f sn <= 1r’>>
  ‘SIGMA f sn <= SND (exten s)’ suffices_by fsr[] >>
  ‘s = IMAGE interval_bl sn’
    by (fs[Abbr‘sn’,Abbr‘s’,interval_bl_def,IMAGE_DEF]) >> rw[] >>
  ‘!x x'. x IN sn /\ x' IN sn /\ x <> x' ==>
          disjoint_interval (interval_bl x) (interval_bl x')’ by
    (‘sn = P INTER {x | LENGTH x < n}’ by fs[INTER_DEF] >> rw[]) >>
  Cases_on‘sn={}’ >> fs[REAL_SUM_IMAGE_THM] >>
  ‘SIGMA f sn + FST (exten (IMAGE interval_bl sn)) <=
   SND (exten (IMAGE interval_bl sn))’ by
    fs[Abbr‘f’,lemma13] >> fsr[]
QED

Theorem kraft_ineq1: ∀P. prefix_free P ==> (∀n. bls_size P n ≤ 1)
Proof
(* Could change to `?y0. y0<=1 /\ bls_size P --> y0` *)
  metis_tac[disjoint_prefix_free,lemma1]
QED


(*  TO DO AT SOME POINT

val numl_size_def = Define`numl_size L = FOLDR (\n A. A+(2 rpow -&n)) 0 L`

val kraft_conv_cw_def = Define`kraft_conv_cw C i =  `

val kraft_ineq_conv = Q.store_thm("kraft_ineq_conv",
`!L. numl_size L <= 1 ==>
(?P b. prefix_free P /\ BIJ b (count (LENGTH L) ) P  /\  !i. i < LENGTH L ==> LENGTH (b i) = EL i L)`,
rw[] >> `?CLIST. CLIST = SET_TO_LIST L` by fs[SET_TO_LIST_THM] >> qexists_tac`` )

*)





val _ = export_theory();
