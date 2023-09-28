
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
open realTheory;
open real_sigmaTheory;
open transcTheory;
open boolListsTheory;

val _ = new_theory "kraft_ineq";

val _ = intLib.deprecate_int()

val _ = hide "lg" (* transc$lg is now log base 2 *)

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
  0 < a ⇒ (a:real) rpow -&x = inv (a pow x)
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
      fs[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION,
         churchDBTheory.DISJ_IMP_EQ] >>
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
      ‘i ≺ j’suffices_by simp[] >>
      irule disjoint_pf_lem1 >>
      full_simp_tac (srw_ss() ++ realSimps.REAL_ARITH_ss)
                    [powr_negexp,
                     RealArith.REAL_ARITH “(x:real) * y + y = (x + 1) * y”] >>
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
      ASM_SIMP_TAC bool_ss [pow_inv_mul_invlt] >> simp[] >>
      simp[REAL_OF_NUM_POW])
  >- (fs[prefix_free_def,PULL_EXISTS] >> rw[] >> strip_tac >>
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
      fs[interval_bl_def,disjoint_interval_def,
         churchDBTheory.DISJ_IMP_EQ] >> rw[DISJOINT_DEF,EXTENSION] >>
      qexists_tac‘&TBL2N b * 2 rpow -&LENGTH b’ >> rw[]
      >- (fs[powr_negexp, prefix_append,TBL2N_append, REAL_OF_NUM_POW,
             RIGHT_ADD_DISTRIB] >>
          REWRITE_TAC [GSYM MULT_ASSOC, arithmeticTheory.EXP_ADD] >> simp[])
      >- (fs[powr_negexp, prefix_append,TBL2N_append] >>
          simp[POW_ADD, REAL_LDISTRIB] >> simp[REAL_OF_NUM_POW])
      >- (simp[powr_negexp,REAL_POW_POS]))
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

val maxr_set_def = new_specification(
  "maxr_set_def",["maxr_set"],
  SIMP_RULE(srw_ss() )[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] max_rs_lemma
  );

val minr_set_def = new_specification(
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
  qspec_then ‘e INSERT s’ mp_tac maxr_set_def  >>
  simp[churchDBTheory.DISJ_IMP_EQ] >> strip_tac >>
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
  qspec_then ‘e INSERT s’ mp_tac minr_set_def  >>
  simp[churchDBTheory.DISJ_IMP_EQ] >> strip_tac >>
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
  >- (‘FINITE {FST e}’ by fs[] >> ‘{FST e} <> {}’ by fs[] >>
      ‘FINITE {FST k | k IN s}’ by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
      ‘{FST k | k IN s} <> {}’ by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF]>>
      rw[minr_set_union])
  >- (‘FINITE {FST e  + SND k}’ by fs[] >> ‘{FST e  + SND k} <> {}’ by fs[] >>
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
  strip_tac >>
  ‘ln 1 < ln a’ by fsr[LN_MONO_LT] >> fsr[LN_1]
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
      ‘i IN Ls’
        by (simp[Abbr‘Ls’,pairTheory.EXISTS_PROD, Abbr‘Ls0’] >> metis_tac[])>>
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

Definition seq_size_def:
  seq_size f 0 = 0r ∧
  seq_size f (SUC n) = inv (2 pow (f n)) + seq_size f n
End

Theorem seq_size_positive[simp]:
  ∀n. 0 ≤ seq_size f n
Proof
  Induct >> rw[seq_size_def] >> irule REAL_LE_ADD >>
  simp[REAL_LE_LT]
QED

Theorem seq_size_EQ0[simp]:
  seq_size f n = 0 ⇔ n = 0
Proof
  Induct_on‘n’ >>
  simp[DECIDE “x < SUC y ⇔ x < y ∨ x = y”, DISJ_IMP_THM, FORALL_AND_THM,
       seq_size_def] >>
  irule (RealArith.REAL_ARITH “0r < x ∧ 0 ≤ y ==> x + y ≠ 0”) >>
  simp[REAL_POW_POS]
QED

Theorem INFINITE_ALLCARD_SUBSETS:
  INFINITE s ⇒ ∀n. ∃s0. FINITE s0 ∧ CARD s0 = n ∧ s0 ⊆ s
Proof
  strip_tac >> Induct >- (qexists_tac ‘∅’ >> simp[]) >>
  gs[] >>
  ‘∃e. e ∈ s ∧ e ∉ s0’ by metis_tac[IN_INFINITE_NOT_FINITE] >>
  qexists_tac ‘e INSERT s0’ >> simp[]
QED

Theorem seq_size_REAL_SUM_IMAGE:
  seq_size f n = REAL_SUM_IMAGE (λi. inv (2 pow (f i))) (count n)
Proof
  Induct_on ‘n’ >> simp[REAL_SUM_IMAGE_THM, COUNT_SUC, seq_size_def]
QED

Theorem seq_size_indices:
  (∀m. seq_size f m ≤ 1) ⇒
  ∀n. FINITE {i | f i = n}  ∧ CARD {i | f i = n} < 2 ** n
Proof
  strip_tac >> gen_tac >>
  ‘∀s0. FINITE s0 ∧ s0 ⊆ { i | f i = n} ⇒ CARD s0 < 2 ** n’
    by (rw[] >> CCONTR_TAC >> gs[NOT_LESS] >>
        qabbrev_tac ‘mx = MAX_SET s0’ >>
        ‘s0 ≠ ∅’ by (strip_tac >> gs[Abbr‘mx’]) >>
        ‘mx ∈ s0 ∧ ∀j. j ∈ s0 ⇒ j ≤ mx’ by metis_tac[MAX_SET_DEF] >>
        ‘1 < seq_size f (mx + 2)’ suffices_by metis_tac[REAL_NOT_LE] >>
        simp[seq_size_REAL_SUM_IMAGE] >>
        ‘s0 ⊆ count (mx + 2)’
          by (rw[count_def, SUBSET_DEF] >> first_x_assum drule >> simp[]) >>
        ‘count (mx + 2) = s0 ∪ (count (mx + 2) DIFF s0)’
          by simp[UNION_DIFF] >> pop_assum SUBST1_TAC >>
        ‘DISJOINT s0 (count (mx + 2) DIFF s0)’
          by (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
        simp[REAL_SUM_IMAGE_DISJOINT_UNION] >>
        ‘REAL_SUM_IMAGE (λi. inv (2 pow f i)) s0 = &CARD s0 * inv (2 pow n)’
          by (irule REAL_SUM_IMAGE_FINITE_CONST2 >> gs[SUBSET_DEF]) >>
        ‘∃d. CARD s0 = 2 ** n + d’ by metis_tac[LESS_EQ_EXISTS] >>
        simp[REAL_LT_ADDR, powr_negexp, GSYM REAL_ADD, Excl "REAL_ADD",
             REAL_LDISTRIB] >> simp[REAL_OF_NUM_POW] >> fsr[] >>
        qmatch_abbrev_tac ‘1r < AA + 1 + BB’ >>
        ‘0 ≤ AA ∧ 0 < BB’ suffices_by RealArith.REAL_ARITH_TAC >>
        simp[Abbr‘AA’, Abbr‘BB’] >>
        ‘count (mx + 2) DIFF s0 = (mx + 1) INSERT (count (mx + 1) DIFF s0)’
          by (simp[EXTENSION] >> qx_gen_tac ‘i’ >> Cases_on ‘i ∈ s0’ >> simp[]>>
              first_x_assum drule >> simp[]) >>
        simp[REAL_SUM_IMAGE_THM] >>
        qmatch_abbrev_tac ‘0r < AA + BB’ >>
        ‘0 < AA ∧ 0 ≤ BB’ suffices_by RealArith.REAL_ARITH_TAC >>
        simp[Abbr‘AA’, Abbr‘BB’] >> fsr[powr_negexp, REAL_OF_NUM_POW] >>
        irule REAL_SUM_IMAGE_POS >> fsr[]) >>
  csimp[] >> CCONTR_TAC >>
  drule_then (qspec_then ‘2 ** n’ strip_assume_tac)
             INFINITE_ALLCARD_SUBSETS >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Definition wfpfun_def:
  wfpfun f = { pf | prefix_free { w | ∃i:num. pf i = SOME w } ∧
                    (∀i p. pf i = SOME p ⇒
                           LENGTH p = f i ∧
                           ∀m j. m < LENGTH p ∧ f j = m ⇒ ∃q. pf j = SOME q) ∧
                    (∀i j. pf i = NONE ∧ j < i ∧ f j = f i ⇒ pf j = NONE)
             }
End

Theorem wfpfun_nonempty:
  wfpfun f ≠ ∅
Proof
  simp[wfpfun_def, EXTENSION] >> qexists_tac ‘K NONE’ >> simp[]
QED

Definition pfunle_def:
  pfunle f = { (pf1, pf2) | pf1 ∈ wfpfun f ∧ pf2 ∈ wfpfun f ∧
                            (∀i. pf1 i ≠ NONE ⇒ pf2 i = pf1 i) }
End

Theorem range_pfunle:
  range (pfunle f) = wfpfun f
Proof
  simp[set_relationTheory.range_def, EXTENSION, pfunle_def, EQ_IMP_THM,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem domain_pfunle:
  domain (pfunle f) = wfpfun f
Proof
  simp[set_relationTheory.domain_def, EXTENSION, pfunle_def, EQ_IMP_THM,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem partial_order_pfunle:
  partial_order (pfunle f) (wfpfun f)
Proof
  simp[set_relationTheory.partial_order_def, domain_pfunle, range_pfunle,
       set_relationTheory.transitive_def, set_relationTheory.reflexive_def,
       set_relationTheory.antisym_def] >>
  simp[pfunle_def, PULL_EXISTS] >> rw[] >>
  simp[FUN_EQ_THM] >> qx_gen_tac ‘i’ >> Cases_on ‘x i’ >> gs[] >>
  Cases_on ‘y i’ >> gs[]
QED

Theorem pfunle_chain_bounds:
  ∀t. chain t (pfunle f) ⇒ upper_bounds t (pfunle f) ≠ ∅
Proof
  simp[EXTENSION, set_relationTheory.upper_bounds_def, range_pfunle,
       set_relationTheory.chain_def] >> rw[] >>
  ‘∀pf. pf ∈ t ⇒ pf ∈ wfpfun f’
    by (gen_tac >> strip_tac >>
        first_x_assum $ qspecl_then [‘pf’, ‘pf’] mp_tac >> simp[] >>
        simp[pfunle_def]) >>
  qexists_tac ‘λi. case some pf. pf ∈ t ∧ pf i ≠ NONE of
                    NONE => NONE
                  | SOME pf => pf i’ >>
  conj_asm1_tac
  >- (simp[wfpfun_def, AllCaseEqs(), PULL_EXISTS] >> rpt conj_tac
      >- (simp[prefix_free_def, PULL_EXISTS] >>
          qx_genl_tac [‘w1’, ‘w2’, ‘i’, ‘pf1’, ‘j’, ‘pf2’] >>
          DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
          DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
          rw[] >> gs[] >>
          Cases_on ‘(pf1,pf2) ∈ pfunle f’
          >- (‘pf2 ∈ wfpfun f’ by metis_tac[] >>
              pop_assum mp_tac >> simp_tac (srw_ss()) [wfpfun_def] >>
              simp[prefix_free_def] >>
              ‘pf2 i = SOME w1 ∧ pf2 j = SOME w2’ suffices_by metis_tac[] >>
              pop_assum mp_tac >>
              simp_tac (srw_ss()) [pfunle_def] >> simp[]) >>
          first_x_assum $ qspecl_then [‘pf1’, ‘pf2’] mp_tac >> simp[] >>
          simp[pfunle_def] >> first_x_assum $ qspec_then ‘pf1’ mp_tac >>
          simp[wfpfun_def, prefix_free_def] >> rw[] >> first_x_assum irule >>
          metis_tac[optionTheory.NOT_NONE_SOME])
      >- (rpt gen_tac >> DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
          rw[]
          >- (first_x_assum $ qspec_then ‘pf’ mp_tac >> simp[wfpfun_def]) >>
          DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >> rw[]
          >- (rename [‘pf' ∈ t’, ‘pf' j ≠ NONE’, ‘pf' j = SOME _’,
                      ‘f j < LENGTH p’] >>
              Cases_on ‘pf' j’ >> gs[]) >>
          qexists_tac ‘pf’ >> simp[] >>
          first_x_assum $ qspec_then ‘pf’ mp_tac >> simp[wfpfun_def] >>
          metis_tac[optionTheory.NOT_NONE_SOME]) >>
      qx_genl_tac [‘i’, ‘j’] >>
      DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
      DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >> qx_gen_tac ‘pf’ >>
      Cases_on ‘pf ∈ t’ >> simp[] >> Cases_on ‘pf j’ >> simp[] >>
      Cases_on ‘f i = f j’ >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[wfpfun_def] >> rpt strip_tac >>
      first_x_assum (drule_at (Pos (el 2))) >> simp[] >> metis_tac[]) >>
  qx_gen_tac ‘pp’ >> Cases_on ‘pp ∈ t’ >> simp[] >>
  simp[pfunle_def] >> qx_gen_tac ‘i’ >> Cases_on ‘pp i’ >>
  simp[AllCaseEqs()] >> DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
  conj_tac
  >- (qx_gen_tac ‘pf’ >> Cases_on ‘pf i’ >> simp[] >> strip_tac >>
      first_x_assum $ qspecl_then [‘pp’, ‘pf’] mp_tac >> simp[] >>
      rw[pfunle_def] >>
      metis_tac[optionTheory.NOT_NONE_SOME, optionTheory.SOME_11]) >>
  qexists_tac ‘pp’ >> simp[]
QED

Theorem partial_wfpfun_FINITE:
  (∀n. seq_size f n ≤ 1) ∧ pf ∈ wfpfun f ∧ pf i = NONE ⇒
  FINITE { j | pf j ≠ NONE }
Proof
  simp[wfpfun_def] >> strip_tac >>
  qabbrev_tac ‘mxlen = f i’ >>
  ‘∀j p. pf j = SOME p ⇒ LENGTH p ≤ mxlen’
    by (CCONTR_TAC >> gs[NOT_LESS_EQUAL] >>
        ‘∃q. pf i = SOME q’ by metis_tac[] >> fs[]) >>
  CCONTR_TAC >>
  ‘∃len. INFINITE {i | f i = len}’ suffices_by metis_tac[seq_size_indices] >>
  CCONTR_TAC >> gs[] >>
  ‘{ j | pf j ≠ NONE } ⊆
   BIGUNION (IMAGE (λn. { i | f i = n }) (count (mxlen + 1)))’
    by (simp[SUBSET_DEF, PULL_EXISTS] >> qx_gen_tac ‘k’ >> Cases_on ‘pf k’ >>
        simp[GSYM LE_LT1] >> metis_tac[]) >>
  qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
  irule SUBSET_FINITE >>
  pop_assum (goal_assum o resolve_then (Pos last) mp_tac) >>
  simp[PULL_EXISTS]
QED

Definition TN2BL_def:
  TN2BL n = MAP ((=) 1) $ REVERSE $ num_to_bin_list n
End

Definition padL_def:
  padL n bl = Fpow (n - LENGTH bl) ++ bl
End

Theorem TBL2N_padL[simp]:
  TBL2N (padL n bl) = TBL2N bl
Proof
  simp[padL_def]
QED

Theorem TBL2N_TN2BL[simp]:
  TBL2N (TN2BL n) = n
Proof
  simp[TN2BL_def, numposrepTheory.num_to_bin_list_def] >>
  completeInduct_on ‘n’ >> simp[Once numposrepTheory.n2l_def] >> rw[]
  >- (Cases_on ‘n = 1’ >> simp[]) >>
  simp[TBL2N_append] >> Cases_on ‘n MOD 2 = 1’ >> simp[]
  >- metis_tac[DIVISION, DECIDE “0n < 2”, MULT_COMM] >>
  simp[bitTheory.DIV_MULT_THM2] >> ‘n MOD 2 = 0’ suffices_by simp[] >>
  ‘n MOD 2 < 2’ by simp[] >> simp[]
QED

Datatype:
  codetree = Empty | Item 'a | FullNode codetree codetree
End

Definition ctree_domain_def[simp]:
  ctree_domain Empty = ∅ ∧
  ctree_domain (Item x) = {[]} ∧
  ctree_domain (FullNode ctl ctr) =
   { F :: x | x ∈ ctree_domain ctl } ∪
   { T :: y | y ∈ ctree_domain ctr }
End

Theorem FINITE_GSPEC:
  FINITE (SND o f) ⇒ FINITE (GSPEC f)
Proof
  ‘GSPEC f = IMAGE (FST o f) (SND o f)’
    by (simp[GSPECIFICATION, EXTENSION] >> qx_gen_tac ‘a’ >>
        simp[IN_DEF, EQ_IMP_THM, PULL_EXISTS] >> conj_tac >> qx_gen_tac ‘b’ >>
        strip_tac >> qexists_tac ‘b’ >> Cases_on ‘f b’ >> gvs[]) >>
  simp[]
QED


Theorem FINITE_ctree_domain[simp]:
  FINITE (ctree_domain ct)
Proof
  Induct_on‘ct’ >>
  asm_simp_tac (srw_ss() ++ boolSimps.ETA_ss)
               [combinTheory.o_ABS_R, IN_DEF, FINITE_GSPEC]
QED

Definition used_space_def[simp]:
  used_space b e Empty = ∅ ∧
  used_space b e (Item _) = { x | b ≤ x ∧ x < b + inv (2r pow e) } ∧
  used_space b e (FullNode ctl ctr) =
    used_space b (e + 1) ctl ∪ used_space (b + inv (2 pow (e+1))) (e + 1) ctr
End

Theorem used_space_safe:
  used_space b e ct ⊆ { x | b ≤ x ∧ x < b + inv (2 pow e) }
Proof
  simp[SUBSET_DEF] >>
  map_every qid_spec_tac [‘b’, ‘e’] >> Induct_on ‘ct’ >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
  >- (strip_tac >> irule REAL_LT_TRANS >> first_assum (irule_at (Pos hd)) >>
      simp[] >> irule REAL_POW_MONO_LT >> simp[])
  >- (strip_tac >> irule REAL_LE_TRANS >> first_assum (irule_at Any) >>
      simp[REAL_LE_ADDR]) >>
  strip_tac >>
  ‘inv (2r pow (e + 1)) + inv (2 pow (e + 1)) = inv (2 pow e)’
    suffices_by metis_tac[REAL_ADD_ASSOC] >>
  simp[REAL_DOUBLE, REAL_POW_ADD]
QED

Definition free_size_def[simp]:
  free_size e Empty = 2r pow e ∧
  free_size e (Item x) = 0 ∧
  free_size e (FullNode ctl ctr) = free_size (e + 1) ctl + free_size (e + 1) ctr
End

Definition full_def[simp]:
  full Empty = F ∧
  full (Item x) = T ∧
  full (FullNode ctl ctr) = (full ctl ∧ full ctr)
End

Theorem full_free_size:
  full ct ⇒ ∀e. free_size e ct = 0
Proof
  Induct_on ‘ct’ >> simp[]
QED

Theorem full_used_space:
  ∀ct b e. full ct ⇒ used_space b e ct = { x | b ≤ x ∧ x < b + inv (2 pow e) }
Proof
  Induct >> simp[] >> rpt strip_tac >>
  rpt (first_x_assum $ drule_then assume_tac) >>
  ‘∀r:real. r + inv (2 pow (e + 1)) + inv (2 pow (e + 1)) = r + inv (2 pow e)’
    by (‘inv (2r pow (e + 1)) + inv (2 pow (e + 1)) = inv (2 pow e)’
          suffices_by metis_tac[REAL_ADD_ASSOC] >>
        simp[REAL_DOUBLE, REAL_POW_ADD]) >>
  simp[EXTENSION] >> rw[EQ_IMP_THM] >> fsr[]
  >- (irule REAL_LT_TRANS >> first_assum (irule_at Any) >>
      simp[REAL_POW_MONO_LT]) >>
  irule REAL_LE_TRANS >> first_assum (irule_at Any) >> simp[REAL_LE_ADDR]
QED

Definition omax_def[simp]:
  omax NONE NONE = NONE ∧
  omax (SOME i) NONE = SOME i ∧
  omax NONE (SOME j) = SOME j ∧
  omax (SOME i) (SOME j) = SOME (MAX i j)
End

Theorem omax_EQ_NONE[simp]:
  omax o1 o2 = NONE ⇔ o1 = NONE ∧ o2 = NONE
Proof
  map_every Cases_on [‘o1’, ‘o2’] >> simp[]
QED

Theorem omax_NONE[simp]:
  omax NONE x = x ∧ omax x NONE = x
Proof
  Cases_on ‘x’>> simp[]
QED

Definition omin_def[simp]:
  omin NONE NONE = NONE ∧
  omin NONE (SOME j) = SOME j ∧
  omin (SOME i) NONE = SOME i ∧
  omin (SOME i) (SOME j) = SOME (MIN i j)
End

Theorem omin_EQ_NONE[simp]:
  omin o1 o2 = NONE ⇔ o1 = NONE ∧ o2 = NONE
Proof
  map_every Cases_on [‘o1’, ‘o2’] >> simp[]
QED

Theorem omin_NONE[simp]:
  omin NONE x = x ∧ omin x NONE = x
Proof
  Cases_on ‘x’ >> simp[]
QED

Definition finest_gap_def[simp]:
  finest_gap Empty = SOME 0n ∧
  finest_gap (Item _) = NONE ∧
  finest_gap (FullNode ctl ctr) =
    OPTION_MAP SUC (omax (finest_gap ctl) (finest_gap ctr))
End

Definition open_paths_def[simp]:
  open_paths Empty = {[]} ∧
  open_paths (Item _) = ∅ ∧
  open_paths (FullNode ctl ctr) =
    IMAGE (CONS F) (open_paths ctl) ∪ IMAGE (CONS T) (open_paths ctr)
End

Theorem FINITE_open_paths[simp]:
  FINITE (open_paths ct)
Proof
  Induct_on ‘ct’ >> simp[]
QED

Theorem NIL_IN_open_paths[simp]:
  [] ∈ open_paths ct ⇔ ct = Empty
Proof
  Cases_on ‘ct’ >> simp[]
QED

Theorem MAX_SET_IMAGE_MONO:
  (∀x y. x ≤ y ⇒ f x ≤ f y) ∧ FINITE s ∧ s ≠ ∅ ⇒
  MAX_SET (IMAGE f s) = f (MAX_SET s)
Proof
  Cases_on ‘∀x y. x ≤ y ⇒ f x ≤ f y’ >> simp[] >>
  Induct_on ‘FINITE’ >> simp[MAX_SET_THM] >> rw[] >>
  Cases_on ‘s = ∅’ >> gvs[] >> simp[MAX_DEF] >>
  Cases_on ‘e < MAX_SET s’ >> simp[AllCaseEqs()]
  >- (csimp[] >> metis_tac[DECIDE “x:num ≤ y ⇔ x < y ∨ x = y”]) >>
  gvs[DECIDE “~(x:num < y) ⇔ y ≤ x”]
QED

Theorem MIN_SET_IMAGE_MONO:
  (∀x y. x ≤ y ⇒ f x ≤ f y) ∧ FINITE s ∧ s ≠ ∅ ⇒
  MIN_SET (IMAGE f s) = f (MIN_SET s)
Proof
  Cases_on ‘∀x y. x ≤ y ⇒ f x ≤ f y’ >> simp[] >>
  Induct_on ‘FINITE’ >> rw[] >> Cases_on ‘s = ∅’ >> gvs[MIN_SET_THM] >>
  ‘∃d s0. s = d INSERT s0 ∧ d ∉ s0’by metis_tac[SET_CASES] >>
  gvs[MIN_SET_THM] >> simp[MIN_DEF] >>
  Cases_on ‘e < MIN_SET (d INSERT s0)’ >> simp[AllCaseEqs()]
  >- (csimp[] >> metis_tac[DECIDE “x:num ≤ y ⇔ x < y ∨ x = y”]) >>
  gvs[DECIDE “~(x:num < y) ⇔ y ≤ x”]
QED

Theorem full_open_paths_EMPTY:
  full ct ⇔ open_paths ct = ∅
Proof
  Induct_on ‘ct’ >> simp[]
QED

Theorem finest_gap_open_paths:
  finest_gap ct = if full ct then NONE
                  else SOME (MAX_SET (IMAGE LENGTH (open_paths ct)))
Proof
  ‘∀x:bool. LENGTH o CONS x = SUC o LENGTH’ by simp[FUN_EQ_THM] >>
  Induct_on ‘ct’ >> simp[full_open_paths_EMPTY] >>
  rename [‘open_paths ctl = ∅ ∧ open_paths ctr = ∅’] >>
  map_every Cases_on [‘open_paths ctl = ∅’, ‘open_paths ctr = ∅’] >>
  simp[IMAGE_IMAGE] >>
  simp[GSYM IMAGE_IMAGE, MAX_SET_IMAGE_MONO, MAX_SET_UNION] >>
  simp[MAX_DEF]
QED

Definition largest_gap_def[nocompute]:
  largest_gap ct = if full ct then NONE
                   else SOME (MIN_SET (IMAGE LENGTH (open_paths ct)))
End

Theorem MIN_SET_0[simp]:
  MIN_SET (0 INSERT s) = 0
Proof
  DEEP_INTRO_TAC MIN_SET_ELIM >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem largest_gap_thm[simp,compute]:
  largest_gap Empty = SOME 0 ∧
  largest_gap (Item v) = NONE ∧
  largest_gap (FullNode ctl ctr) =
    OPTION_MAP SUC (omin (largest_gap ctl) (largest_gap ctr))
Proof
  ‘∀x:bool. LENGTH o CONS x = SUC o LENGTH’ by simp[FUN_EQ_THM] >>
  simp[largest_gap_def, MIN_SET_THM] >> rw[] >> fs[]
  >- (gvs[full_open_paths_EMPTY] >>
      simp[IMAGE_IMAGE] >> simp[GSYM IMAGE_IMAGE, MIN_SET_IMAGE_MONO])
  >- (gvs[full_open_paths_EMPTY] >>
      simp[IMAGE_IMAGE] >> simp[GSYM IMAGE_IMAGE, MIN_SET_IMAGE_MONO]) >>
  gvs[full_open_paths_EMPTY, MIN_SET_UNION, IMAGE_IMAGE] >>
  simp[GSYM IMAGE_IMAGE, MIN_SET_IMAGE_MONO] >> simp[MIN_DEF]
QED

Theorem finest_gap_EQ_NONE:
  ∀ct. finest_gap ct = NONE ⇔ full ct
Proof
  Induct_on ‘ct’ >> simp[]
QED

Definition packed_def:
  packed ct ⇔
  ∀p1 p2. p1 ∈ open_paths ct ∧ p2 ∈ open_paths ct ∧ LENGTH p1 = LENGTH p2 ⇒
          p1 = p2
End

Theorem full_packed:
  full ct ⇒ packed ct
Proof
  simp[full_open_paths_EMPTY, packed_def]
QED

Definition first_tree_def[simp]:
  first_tree 0 i = Item i ∧
  first_tree (SUC n) i = FullNode (first_tree n i) Empty
End

Theorem first_tree_EQ_Empty[simp]:
  first_tree n v ≠ Empty
Proof
  Cases_on ‘n’ >> simp[]
QED

Theorem open_paths_first_tree[simp]:
  open_paths (first_tree n v) = IMAGE (λm. Fpow m ++ [T]) (count n)
Proof
  Induct_on ‘n’ >>
  simp[EXTENSION, LT_SUC, PULL_EXISTS, LEFT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem packed_first_tree[simp]:
  packed (first_tree n v)
Proof
  simp[packed_def] >>
  Induct_on ‘n’ >> simp[] >> dsimp[]
QED

Theorem finest_gap_first_tree:
  finest_gap (first_tree k v) = if k = 0 then NONE else SOME k
Proof
  Induct_on ‘k’ >> simp[] >> rw[] >> simp[MAX_DEF]
QED

Definition insert_def[simp]:
  insert klen v Empty = SOME (first_tree klen v) ∧
  insert klen v (Item _) = NONE ∧
  insert klen v (FullNode ctl ctr) =
    if klen = 0 then NONE
    else
      case largest_gap ctl of
        NONE => OPTION_MAP (FullNode ctl) (insert (klen - 1) v ctr)
      | SOME i => if klen ≤ i then
                    OPTION_MAP (FullNode ctl) (insert (klen - 1) v ctr)
                  else
                    OPTION_MAP (λl. FullNode l ctr) (insert (klen - 1) v ctl)
End

Theorem packed_FullNode_E:
  packed (FullNode ctl ctr) ⇒ packed ctl ∧ packed ctr
Proof
  ONCE_REWRITE_TAC [packed_def] >> rpt strip_tac
  >- (first_x_assum $ qspecl_then [‘F::p1’, ‘F::p2’] mp_tac >> simp[]) >>
  first_x_assum $ qspecl_then [‘T::p1’, ‘T::p2’] mp_tac >> simp[]
QED

(*
val _ = temp_overload_on ("mass_insert",
                          “FOLDL (λa (k,v). THE (insert k v a)) Empty”)
EVAL “mass_insert [(1, "a"); (3,"b"); (2,"c")]”;
EVAL “mass_insert [(3, "a"); (1,"b"); (2,"c")]”;
EVAL “packed (mass_insert [(3, "a"); (1,"b"); (2,"c")])”
     |> CONV_RULE $ RAND_CONV $ SIMP_CONV (srw_ss()) [] |> EQT_ELIM;
EVAL “packed (mass_insert [(4, "a"); (1,"b"); (4,"c"); (3,"d"); (6,"e")])”
     |> CONV_RULE $ RAND_CONV $
           SIMP_CONV (srw_ss()) [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR]
     |> CONV_RULE $ RAND_CONV $ REWRITE_CONV [DISJ_IMP_THM]
     |> CONV_RULE $ RAND_CONV $ SIMP_CONV bool_ss [FORALL_AND_THM]
     |> CONV_RULE $ RAND_CONV $ SIMP_CONV (srw_ss()) []
     |> EQT_ELIM;
EVAL “packed (mass_insert [(4, "a"); (6, "e"); (1,"b"); (4,"c"); (3,"d");])”
     |> CONV_RULE $ RAND_CONV $
           SIMP_CONV (srw_ss()) [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR]
     |> CONV_RULE $ RAND_CONV $ REWRITE_CONV [DISJ_IMP_THM]
     |> CONV_RULE $ RAND_CONV $ SIMP_CONV bool_ss [FORALL_AND_THM]
     |> CONV_RULE $ RAND_CONV $ SIMP_CONV (srw_ss()) []
     |> EQT_ELIM;
*)
Theorem insert_fails:
  ∀ct klen v.
    insert klen v ct = NONE ⇔ full ct ∨ ∃g. largest_gap ct = SOME g ∧ klen < g
Proof
  Induct >> simp[AllCaseEqs()] >>
  simp[PULL_EXISTS] >>
  rename [‘omin (largest_gap ctl) (largest_gap ctr)’] >>
  Cases_on ‘largest_gap ctl’ >> simp[]
  >- (‘full ctl’ by gvs[full_open_paths_EMPTY, largest_gap_def] >>
      rpt gen_tac >> Cases_on ‘insert (klen - 1) v ctr’ >> simp[]
      >- gvs[] >>
      first_x_assum $ qspecl_then [‘klen - 1’, ‘v’] mp_tac >> simp[] >>
      strip_tac >> Cases_on ‘largest_gap ctr’ >> gvs[] >>
      gvs[largest_gap_def, full_open_paths_EMPTY]) >>
  rpt gen_tac >> rename [‘largest_gap ctl = SOME gl’] >>
  Cases_on ‘klen ≤ gl’ >> simp[]
  >- (Cases_on ‘insert (klen - 1) v ctr’ >> simp[]
      >- (pop_assum mp_tac >> simp[DISJ_IMP_THM, PULL_EXISTS] >> rw[]
          >- (Cases_on ‘largest_gap ctr’ >> simp[MIN_DEF] >>
              gvs[full_open_paths_EMPTY, largest_gap_def]) >>
          simp[MIN_DEF]) >>
      first_x_assum $ qspecl_then [‘klen - 1’, ‘v’] mp_tac >> simp[] >>
      rpt strip_tac >>
      Cases_on ‘largest_gap ctr’ >>
      gvs[full_open_paths_EMPTY, largest_gap_def] >>
      gvs[MIN_DEF]) >>
  ‘¬full ctl’ by gvs[full_open_paths_EMPTY, largest_gap_def] >> simp[] >>
  Cases_on ‘largest_gap ctr’ >> simp[] >> simp[MIN_DEF]
QED

Theorem insert_succeeds_gap_E:
  insert kl v ct0 = SOME ct ⇒
  ∃lg. largest_gap ct0 = SOME lg ∧ lg ≤ kl
Proof
  strip_tac >> CCONTR_TAC >> gvs[] >>
  ‘insert kl v ct0 ≠ NONE’ by (strip_tac >> gvs[]) >>
  pop_assum mp_tac >> simp_tac bool_ss [insert_fails] >>
  Cases_on ‘largest_gap ct0’  >- gvs[largest_gap_def] >>
  gvs[]
QED

Theorem largest_gt_finest:
  ¬full ct ⇒ ∃g f. largest_gap ct = SOME g ∧ finest_gap ct = SOME f ∧ g ≤ f
Proof
  Induct_on ‘ct’ >> simp[] >>
  strip_tac >> gvs[] >>
  rename [‘¬full ctt ⇒ _’] >> Cases_on ‘full ctt’ >> gvs[] >>
  ‘largest_gap ctt = NONE ∧ finest_gap ctt = NONE’ suffices_by simp[] >>
  gvs[largest_gap_def, full_open_paths_EMPTY, finest_gap_open_paths]
QED

Theorem largest_gt_finest_E:
  largest_gap ct = SOME lg ⇒ ∃fg. finest_gap ct = SOME fg ∧ lg ≤ fg
Proof
  strip_tac >>
  ‘¬full ct’ by (strip_tac >> gvs[largest_gap_def, full_open_paths_EMPTY]) >>
  drule largest_gt_finest >> simp[PULL_EXISTS]
QED

Theorem full_first_tree[simp]:
  full(first_tree k v) ⇔ k = 0
Proof
  Induct_on ‘k’ >> simp[]
QED

Theorem insert_becomes_full:
  ∀ct0 ct kl v.
    insert kl v ct0 = SOME ct ∧ full ct ⇒
    finest_gap ct0 = SOME kl ∧ largest_gap ct0 = SOME kl ∧
    ∃p. open_paths ct0 = {p} ∧ LENGTH p = kl
Proof
  Induct >> simp[] >> rw[] >> gvs[AllCaseEqs()]
  >- (‘finest_gap ct0 = NONE’ by simp[finest_gap_EQ_NONE] >> simp[] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
  >- (gvs[largest_gap_def, full_open_paths_EMPTY])
  >- (rename [‘full ctt’, ‘finest_gap ctt’] >>
      ‘finest_gap ctt = NONE’ by simp[finest_gap_EQ_NONE] >> simp[] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
  >- (first_x_assum $ drule_all_then strip_assume_tac >> simp[MIN_DEF])
  >- (first_x_assum $ drule_all_then strip_assume_tac >> simp[MIN_DEF])
  >- (rename [‘full ctt’, ‘largest_gap ctt’] >>
      ‘largest_gap ctt = NONE’ by gvs[largest_gap_def, full_open_paths_EMPTY] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
  >- (rename [‘full ctt’, ‘open_paths ctt’] >>
      ‘open_paths ctt = ∅’ by gvs[full_open_paths_EMPTY] >> simp[] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
  >- (rename [‘full ctt’, ‘open_paths ctt’] >>
      ‘open_paths ctt = ∅’ by gvs[full_open_paths_EMPTY] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
  >- (rename [‘full ctt’, ‘open_paths ctt’] >>
      ‘open_paths ctt = ∅’ by gvs[full_open_paths_EMPTY] >>
      first_x_assum $ drule_all_then strip_assume_tac >> simp[])
QED

Definition Lbiased_def[simp]:
  (Lbiased Empty ⇔ T) ∧
  (Lbiased (Item _) ⇔ T) ∧
  (Lbiased (FullNode ctl ctr) ⇔
   Lbiased ctl ∧ Lbiased ctr ∧
   ∀p1 p2. p1 ∈ open_paths ctl ∧ p2 ∈ open_paths ctr ⇒
           LENGTH p2 < LENGTH p1)
End

Theorem Lbiased_first_tree[simp]:
  Lbiased (first_tree n v)
Proof
  Induct_on ‘n’ >> simp[PULL_EXISTS]
QED

Theorem packed_equalities[simp]:
  packed Empty ∧ packed (Item v)
Proof
  simp[packed_def]
QED

Theorem packed_full_subtree:
  full ct1 ⇒ (packed (FullNode ct1 ct2) ⇔ packed ct2) ∧
             (packed (FullNode ct2 ct1) ⇔ packed ct2)
Proof
  simp[packed_def, full_open_paths_EMPTY, PULL_EXISTS]
QED

Theorem insert_EQ_Empty[simp]:
  insert klen v ct ≠ SOME Empty
Proof
  Induct_on ‘ct’ >> simp[AllCaseEqs()]
QED

Theorem Lbiased_packed:
  Lbiased ct ⇒ packed ct
Proof
  simp[packed_def] >> Induct_on ‘ct’ >> simp[] >> rw[] >> gvs[] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Definition fmpfree_def:
  fmpfree (fm : bool list |-> 'a) ⇔ prefix_free (FDOM fm)
End

Definition codetree_to_fmap_def[simp]:
  codetree_to_fmap Empty = FEMPTY ∧
  codetree_to_fmap (Item v) = FEMPTY |+ ([], v) ∧
  codetree_to_fmap (FullNode ctl ctr) =
  FUN_FMAP (λbl. case bl of
                   [] => ARB
                 | F::rest => codetree_to_fmap ctl ' rest
                 | T::rest => codetree_to_fmap ctr ' rest)
           (IMAGE (CONS F) (ctree_domain ctl) ∪
            IMAGE (CONS T) (ctree_domain ctr))
End



Theorem FDOM_codetree_to_fmap[simp]:
  FDOM (codetree_to_fmap ct) = ctree_domain ct
Proof
  Induct_on ‘ct’ >> simp[FUN_FMAP_DEF] >>
  simp[EXTENSION]
QED

Theorem pfree_ctree_domain[simp]:
  prefix_free (ctree_domain ct)
Proof
  Induct_on ‘ct’ >> simp[] >>
  gvs[prefix_free_def, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
      RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, prefix_def]
QED

Theorem packed_domain_empty:
  packed ct ∧ ctree_domain ct = ∅ ⇒ ct = Empty
Proof
  Induct_on ‘ct’ >> simp[EXTENSION] >>
  rename [‘packed (FullNode ctl ctr)’] >>
  Cases_on‘packed (FullNode ctl ctr)’ >> simp[] >>
  Cases_on‘ctree_domain ctl = ∅’ >>
  simp[EXISTS_OR_THM, MEMBER_NOT_EMPTY] >> strip_tac >>
  drule_then strip_assume_tac packed_FullNode_E >> gvs[] >>
  gvs[packed_def] >> first_x_assum $ qspecl_then [‘[F]’, ‘[T]’] mp_tac >>
  simp[]
QED

Theorem INJ_codetree_to_fmap:
  INJ codetree_to_fmap { ct | packed ct } { fm | fmpfree fm }
Proof
  simp[INJ_DEF, fmpfree_def] >> Induct >> simp[]
  >- (Cases >> simp[] >> simp[fmap_EXT, FUN_FMAP_DEF] >> strip_tac >>
      rename [‘packed (FullNode ctl ctr)’] >>
      Cases_on ‘ctree_domain ctl = ∅’ >> simp[] >>
      Cases_on ‘ctree_domain ctr = ∅’ >> simp[] >>
      drule_then strip_assume_tac packed_FullNode_E >>
      rpt (dxrule_all_then strip_assume_tac packed_domain_empty) >>
      gvs[packed_def] >> first_x_assum $ qspecl_then [‘[F]’, ‘[T]’] mp_tac >>
      simp[])
  >- (qx_gen_tac ‘a’ >> Cases >> simp[]
      >- (disch_then (mp_tac o C Q.AP_THM ‘[]’ o Q.AP_TERM ‘FAPPLY’) >>
          simp[]) >>
      strip_tac >> simp[fmap_EXT] >>
      strip_tac >> dxrule (SUBSET_ANTISYM_EQ |> iffRL |> cj 2) >>
      simp[SUBSET_DEF]) >>
  Cases >> simp[]
  >- (simp[fmap_EXT, FUN_FMAP_DEF] >> strip_tac >>
      rename [‘packed (FullNode ctl ctr)’] >>
      Cases_on ‘ctree_domain ctl = ∅’ >> simp[] >>
      Cases_on ‘ctree_domain ctr = ∅’ >> simp[] >>
      drule_then strip_assume_tac packed_FullNode_E >>
      rpt (dxrule_all_then strip_assume_tac packed_domain_empty) >> gvs[] >>
      qpat_x_assum ‘packed (FullNode Empty Empty)’ mp_tac >> simp[packed_def] >>
      qexistsl_tac [‘[T]’, ‘[F]’] >> simp[])
  >- (strip_tac >> simp[fmap_EXT] >> strip_tac >>
      dxrule (SUBSET_ANTISYM_EQ |> iffRL |> cj 2) >> simp[SUBSET_DEF]) >>
  strip_tac >> simp[fmap_EXT] >> rw[] >>
  first_x_assum irule (* 2 *)
  >- (reverse (rpt conj_tac) (* 3 *)
      >- (simp[fmap_EXT] >> conj_asm1_tac
          >- (qpat_x_assum ‘IMAGE _ _ ∪ _ = _’ mp_tac >>
              simp[EXTENSION] >> strip_tac >> qx_gen_tac ‘d’ >>
              pop_assum $ qspec_then ‘F::d’ mp_tac >> simp[]) >>
          qx_gen_tac ‘d’ >> strip_tac >>
          first_x_assum $ qspec_then ‘F::d’ mp_tac >>
          simp[FUN_FMAP_DEF] >> gvs[]) >>
      rpt (dxrule packed_FullNode_E) >> simp[]) >>
  reverse (rpt conj_tac) (* 3 *)
  >- (simp[fmap_EXT] >> conj_asm1_tac
      >- (qpat_x_assum ‘IMAGE _ _ ∪ _ = _’ mp_tac >>
          simp[EXTENSION] >> strip_tac >> qx_gen_tac ‘d’ >>
          pop_assum $ qspec_then ‘T::d’ mp_tac >> simp[]) >>
      qx_gen_tac ‘d’ >> strip_tac >>
      first_x_assum $ qspec_then ‘T::d’ mp_tac >>
      simp[FUN_FMAP_DEF] >> gvs[]) >>
  rpt (dxrule packed_FullNode_E) >> simp[]
QED

Theorem domain_open_paths_DISJOINT:
  DISJOINT (ctree_domain ct) (open_paths ct)
Proof
  simp[DISJOINT_DEF] >> Induct_on ‘ct’ >> simp[] >>
  gvs[EXTENSION] >> Cases >> simp[] >> metis_tac[]
QED

Theorem INJ_IMAGE_DELETE:
  (∀x y. f x = f y ⇔ x = y) ⇒
  IMAGE f (s DELETE e) = IMAGE f s DELETE f e
Proof
  csimp[EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem largest_gap_maximal:
  largest_gap ct = SOME lg ∧ p ∈ open_paths ct ⇒ lg ≤ LENGTH p
Proof
  simp[largest_gap_def, AllCaseEqs()] >> rw[] >> irule (cj 2 MIN_SET_LEM) >>
  simp[] >> metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem largest_gap_exists_as_path:
  largest_gap ct = SOME lg ⇒ ∃p. p ∈ open_paths ct ∧ LENGTH p = lg
Proof
  rw[largest_gap_def, full_open_paths_EMPTY] >>
  ‘IMAGE LENGTH (open_paths ct) ≠ ∅’ by simp[] >>
  drule (cj 1 MIN_SET_LEM) >> simp[] >> metis_tac[]
QED

Theorem insert_hitting_gap_preserves_Lbiased:
  ∀ct0 ct klen v p.
    Lbiased ct0 ∧ insert klen v ct0 = SOME ct ∧
    p ∈ open_paths ct0 ∧ LENGTH p = klen ⇒
    open_paths ct = open_paths ct0 DELETE p ∧
    Lbiased ct
Proof
  Induct >> simp[AllCaseEqs()] >> rw[] >> simp[] >> gvs[]
  >- gvs[largest_gap_def, full_open_paths_EMPTY]
  >- gvs[largest_gap_def, full_open_paths_EMPTY]
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE] >> dsimp[EXTENSION, PULL_EXISTS] >> csimp[])
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE])
  >- (drule_all largest_gap_maximal >> simp[])
  >- (drule_all largest_gap_maximal >> simp[])
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE] >> dsimp[EXTENSION, PULL_EXISTS] >> csimp[])
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE])
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE] >> dsimp[EXTENSION, PULL_EXISTS] >> csimp[])
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[INJ_IMAGE_DELETE])
  >- (drule_then strip_assume_tac largest_gap_exists_as_path >>
      first_x_assum drule_all >> simp[])
  >- (drule_then strip_assume_tac largest_gap_exists_as_path >>
      first_x_assum drule_all >> simp[])
QED

Theorem insert_open_path:
  ∀ct0 ct klen v p.
    insert klen v ct0 = SOME ct ∧ p ∈ open_paths ct ⇒
    p ∈ open_paths ct0 ∨ THE (largest_gap ct) ≤ LENGTH p ∧ LENGTH p ≤ klen
Proof
  Induct_on ‘ct0’ >> dsimp[AllCaseEqs()]
  >- (simp[largest_gap_def, IMAGE_IMAGE, combinTheory.o_ABS_R] >> rw[] >>
      irule (cj 2 MIN_SET_LEM) >> simp[] >> simp[EXTENSION] >>
      first_assum (irule_at Any)) >>
  rw[] >> first_x_assum $ drule_all_then strip_assume_tac >> simp[] >>
  rename [‘insert _ _ _ = SOME ctt’] >>
  Cases_on ‘largest_gap ctt’ >> gvs[]
  >- gvs [largest_gap_def, full_open_paths_EMPTY]
  >- gvs [largest_gap_def, full_open_paths_EMPTY]
  >- (rename [‘omin _ (largest_gap ctr)’] >>
      Cases_on ‘largest_gap ctr’ >> gvs[])
QED

Theorem insert_largest_gap_grows:
  ∀ct0 ct klen v lg0 lg.
    insert klen v ct0 = SOME ct ∧ largest_gap ct0 = SOME lg0 ∧
    largest_gap ct = SOME lg ⇒
    lg0 ≤ lg
Proof
  Induct_on ‘ct0’ >> dsimp[AllCaseEqs()] >> rw[]
  >- (gvs[] >> metis_tac[])
  >- (gvs[] >>
      rename [‘insert _ _ ctr0 = SOME ctr’, ‘largest_gap ctl = SOME llg’] >>
      Cases_on ‘largest_gap ctr0’
      >- (‘∀k v. insert k v ctr0 = NONE’
            by gvs[insert_fails, full_open_paths_EMPTY, largest_gap_def] >>
          gvs[]) >> gvs[] >>
      Cases_on ‘largest_gap ctr’ >> gvs[] >> first_x_assum drule >> simp[])
  >- (gvs[] >>
      rename [‘insert _ _ ctl0 = SOME ctl’, ‘largest_gap ctl0 = SOME llg’,
              ‘omin _ (largest_gap ctr)’] >>
      Cases_on ‘largest_gap ctl’ >> gvs[] >> first_x_assum drule_all >>
      Cases_on ‘largest_gap ctr’ >> gvs[])
QED


Theorem insert_preserves_Lbiased:
  ∀ct0 ct klen v.
    Lbiased ct0 ∧ insert klen v ct0 = SOME ct ⇒
    Lbiased ct
Proof
  Induct_on ‘ct0’ >> dsimp[AllCaseEqs()] >> rpt strip_tac
  >- metis_tac[]
  >- gvs[largest_gap_def, full_open_paths_EMPTY]
  >- metis_tac[]
  >- (drule_all_then strip_assume_tac insert_open_path
      >- metis_tac[] >>
      drule_all_then strip_assume_tac largest_gap_maximal >> simp[])
  >- metis_tac[]
  >- (drule_all_then strip_assume_tac insert_open_path
      >- metis_tac[] >>
      rename [‘THE (largest_gap ctl') ≤ LENGTH p1’] >>
      ‘∃lg. largest_gap ctl' = SOME lg’
        by (Cases_on ‘largest_gap ctl'’ >>
            gvs[largest_gap_def, full_open_paths_EMPTY]) >> gvs[] >>
      drule_all_then strip_assume_tac insert_largest_gap_grows >>
      rev_drule_all_then strip_assume_tac largest_gap_exists_as_path >>
      first_x_assum drule_all >> simp[])
QED

Definition free_space_def[simp]:
  free_space Empty = 1r ∧
  free_space (Item _) = 0r ∧
  free_space (FullNode ctl ctr) = (free_space ctl + free_space ctr) / 2
End


Theorem lemma[local] =
  pow_inv_mul |> ADD_ASSUM “x:real ≠ 0” |> DISCH_ALL
  |> underAIs (AP_TERM “inv : real -> real”)
  |> SIMP_RULE (srw_ss()) [REAL_INV_MUL, Excl "REAL_INV_INJ",
                           Excl "REALMULCANON", Excl "RMUL_EQNORM2",
                           REAL_INV_INV]
  |> ONCE_REWRITE_RULE [REAL_MUL_COMM]

Theorem free_space_first_tree[simp]:
  free_space (first_tree n v) = 1 - inv (2 pow n)
Proof
  Induct_on ‘n’ >> simp[] >> REWRITE_TAC [real_div] >>
  simp[RealArith.REAL_ARITH “1r - y + 1 = 2 - y”, REAL_SUB_LDISTRIB, lemma]
QED

Theorem free_space_open_paths:
  free_space ct = REAL_SUM_IMAGE (λp. 2 rpow -&LENGTH p) (open_paths ct)
Proof
  Induct_on ‘ct’ >> simp[REAL_SUM_IMAGE_THM, GSYM GEN_RPOW] >>
  rename [‘IMAGE (CONS F) (open_paths ctl) ∪ IMAGE (CONS T) (open_paths ctr)’] >>
  ‘DISJOINT (IMAGE (CONS F) (open_paths ctl)) (IMAGE (CONS T) (open_paths ctr))’
    by (simp[DISJOINT_DEF, EXTENSION] >>
        ‘∀l1 l2. F :: l1 ≠ T :: l2’ by simp[] >> metis_tac[]) >>
  drule_at (Pos (el 3)) REAL_SUM_IMAGE_DISJOINT_UNION >> simp[] >>
  disch_then kall_tac >> REWRITE_TAC[real_div] >> simp[REAL_LDISTRIB] >>
  simp[REAL_SUM_IMAGE_IMAGE, INJ_IFF, combinTheory.o_ABS_L] >>
  simp[GSYM REAL_SUM_IMAGE_CMUL, powr_negexp, lemma]
QED

Theorem free_space_bounds:
  0 ≤ free_space ct ∧ free_space ct ≤ 1
Proof
  Induct_on ‘ct’ >> simp[] >> REWRITE_TAC[real_div] >> simp[] >> gs[] >> fsr[]
QED

Theorem packed_free_spaceEQ1:
  packed ct ∧ free_space ct = 1 ⇒ ct = Empty
Proof
  Induct_on ‘ct’ >> simp[] >> rename [‘packed (FullNode ctl ctr)’] >>
  Cases_on ‘packed (FullNode ctl ctr)’ >> simp[] >>
  drule_then strip_assume_tac packed_FullNode_E >> REWRITE_TAC[real_div] >>
  simp[] >> strip_tac >>
  ‘0 ≤ free_space ctl ∧ 0 ≤ free_space ctr ∧ free_space ctl ≤ 1 ∧
   free_space ctr ≤ 1’ by simp[free_space_bounds] >>
  ‘free_space ctl = 1 ∧ free_space ctr = 1’ by fsr[] >>
  gvs[] >> gs[packed_def] >> pop_assum mp_tac >>
  simp[] >> qexistsl_tac [‘[F]’, ‘[T]’] >> simp[]
QED

Theorem open_paths_EMPTY_free_space:
  open_paths ct = ∅ ⇒ free_space ct = 0
Proof
  simp[free_space_open_paths, REAL_SUM_IMAGE_THM]
QED

Theorem largest_gap_lbounds_free_space:
  ∀ct lg. largest_gap ct = SOME lg ⇒ 1 ≤ free_space ct * 2 pow lg
Proof
  Induct >> simp[PULL_EXISTS] >>
  rename [‘omin (largest_gap ctl) (largest_gap ctr)’] >> REWRITE_TAC[real_div] >>
  simp[GSYM REAL_MUL_ASSOC] >>
  map_every Cases_on [‘largest_gap ctl’, ‘largest_gap ctr’] >> gvs[]
  >- (rename [‘largest_gap ctt = NONE’] >>
      ‘free_space ctt = 0’
        by gvs[largest_gap_def, open_paths_EMPTY_free_space,
               full_open_paths_EMPTY] >>
      simp[pow])
  >- (rename [‘largest_gap ctt = NONE’] >>
      ‘free_space ctt = 0’
        by gvs[largest_gap_def, open_paths_EMPTY_free_space,
               full_open_paths_EMPTY] >>
      simp[pow]) >>
  simp[pow] >> rw[MIN_DEF, REAL_LDISTRIB] >>
  rename [‘m < n’]
  >- (‘0 ≤ free_space ctr * 2 pow m’ suffices_by fsr[] >>
      irule REAL_LE_MUL >> simp[free_space_bounds])
  >- (‘0 ≤ free_space ctl * 2 pow n’ suffices_by fsr[] >>
      irule REAL_LE_MUL >> simp[free_space_bounds])
QED

Theorem packed_FullNode_flips:
  packed (FullNode ctl ctr) ⇔ packed (FullNode ctr ctl)
Proof
  simp[packed_def] >> eq_tac >> rpt strip_tac >>
  first_x_assum $ qspecl_then [‘case p1 of b :: rest => ¬b::rest | [] => []’,
                               ‘case p2 of b :: rest => ¬b::rest | [] => []’]
                mp_tac >> gvs[]
QED

Theorem REAL_SUM_IMAGE_SUBSET:
  ∀s t. FINITE t ∧ s ⊆ t ∧ (∀e. e ∈ t ⇒ 0 ≤ f e) ⇒
        REAL_SUM_IMAGE f s ≤ REAL_SUM_IMAGE f t
Proof
  Induct_on ‘FINITE’ >> simp[REAL_SUM_IMAGE_THM] >> rw[] >>
  rename [‘e ∉ t’, ‘s ⊆ e INSERT t’] >> Cases_on ‘e ∈ s’
  >- (‘s = e INSERT s’ by (simp[EXTENSION] >> metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      ‘FINITE s’ by metis_tac[SUBSET_FINITE, FINITE_INSERT] >>
      simp[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >>
      first_x_assum irule >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  simp[DELETE_NON_ELEMENT_RWT] >> irule REAL_LE_TRANS >>
  first_x_assum (irule_at Any) >> gvs[SUBSET_DEF]
QED

Theorem packed_largest_gap_ubounds_free_space:
  ∀ct lg. packed ct ∧ largest_gap ct = SOME lg ⇒ 2 pow lg * free_space ct < 2
Proof
  simp[free_space_open_paths, largest_gap_def] >> qx_gen_tac ‘ct’ >>
  strip_tac >> simp[powr_negexp] >>
  qabbrev_tac ‘mn = MIN_SET (IMAGE LENGTH (open_paths ct))’ >>
  qabbrev_tac ‘mx = MAX_SET (IMAGE LENGTH (open_paths ct))’ >>
  ‘SIGMA (λp. inv (2 pow LENGTH p)) (open_paths ct) =
   SIGMA (λn. inv (2 pow n)) (IMAGE LENGTH (open_paths ct))’
    by (‘INJ LENGTH (open_paths ct) (IMAGE LENGTH (open_paths ct))’
          by (simp[INJ_IFF] >> metis_tac[packed_def]) >>
        drule_at (Pos (el 2)) REAL_SUM_IMAGE_IMAGE >>
        simp[combinTheory.o_ABS_L]) >>
  pop_assum SUBST1_TAC >>
  irule REAL_LET_TRANS >> irule_at Any REAL_LE_RMUL_IMP >> simp[] >>
  irule_at Any REAL_SUM_IMAGE_SUBSET >>
  qexists_tac ‘{ l | mn ≤ l ∧ l ≤ mx }’ >> simp[SUBSET_DEF, PULL_EXISTS] >>
  rw[]
  >- (irule SUBSET_FINITE >> qexists_tac ‘count (mx + 1)’ >> simp[SUBSET_DEF])
  >- (simp[Abbr‘mn’] >> irule (cj 2 MIN_SET_LEM) >> gvs[full_open_paths_EMPTY])
  >- (simp[Abbr‘mx’] >> irule in_max_set >> simp[]) >>
  rpt (pop_assum (K ALL_TAC)) >>
  reverse (Cases_on ‘mn ≤ mx’ )
  >- (‘{ l | mn ≤ l ∧ l ≤ mx } = ∅’ by simp[EXTENSION] >>
      simp[REAL_SUM_IMAGE_THM]) >>
  ‘SIGMA (λn. inv (2 pow n)) { l | mn ≤ l ∧ l ≤ mx } =
   SIGMA (λn. inv (2 pow n)) (count (mx - mn + 1)) * inv (2 pow mn)’ suffices_by
    (simp[] >> disch_then (K ALL_TAC) >>
     ‘∀n. SIGMA (λm. inv (2 pow m)) (count n) = (2 pow n - 1) / 2 pow (n - 1)’
       suffices_by
       (disch_then (REWRITE_TAC o single) >> simp[real_div] >>
        simp[REAL_SUB_RDISTRIB, REAL_POW_ADD] >>
        Cases_on ‘mx = mn’ >> simp[] >>
        simp[GSYM pow_inv_mul_invlt, REAL_POW_ADD, REAL_SUB_LDISTRIB] >>
        simp[REAL_LT_SUB_RADD] >> simp[REAL_OF_NUM_POW]) >>
     Induct >> simp[REAL_SUM_IMAGE_THM, COUNT_SUC, pow] >>
     REWRITE_TAC[real_div] >>
     simp[REAL_LDISTRIB, REAL_SUB_LDISTRIB] >>
     Cases_on ‘n’ >> simp[pow] >> REWRITE_TAC[POW_2] >> simp[]>> fsr[]) >>
  Induct_on ‘mx’ >> simp[]
  >- (‘count 1 = {0}’ by simp[EXTENSION] >> simp[]) >>
  strip_tac >> Cases_on ‘mn = SUC mx’
  >- (‘{ l | mn ≤ l ∧ l ≤ SUC mx} = {mn}’ by simp[EXTENSION] >>
      simp[REAL_SUM_IMAGE_THM] >> ‘count 1 = {0}’ by simp[EXTENSION] >>
      simp[REAL_SUM_IMAGE_THM]) >>
  ‘mn ≤ mx’ by simp[] >> gvs[] >>
  ‘{ l | mn ≤ l ∧ l ≤ SUC mx } = SUC mx INSERT { l | mn ≤ l ∧ l ≤ mx}’
    by simp[EXTENSION] >>
  ‘FINITE { l | mn ≤ l ∧ l ≤ mx}’
    by (irule SUBSET_FINITE >> qexists_tac ‘count (mx + 1)’ >>
        simp[SUBSET_DEF]) >>
  simp[REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT, REAL_LDISTRIB] >>
  simp[ADD_CLAUSES, DECIDE “y ≤ x ⇒ SUC x - y = SUC (x - y)”,
       COUNT_SUC, REAL_SUM_IMAGE_THM] >>
  simp[GSYM pow_inv_mul_invlt, pow, REAL_POW_ADD]
QED

Theorem free_space_guarantees_insert:
  ∀ct n v. packed ct0 ∧ 2 rpow -&n ≤ free_space ct0 ⇒
           ∃ct. insert n v ct0 = SOME ct ∧
                free_space ct = free_space ct0 - 2 rpow -&n
Proof
  Induct_on ‘ct0’ >> gvs[powr_negexp] >> rw[] >>
  drule_then strip_assume_tac packed_FullNode_E >>
  RULE_ASSUM_TAC (REWRITE_RULE [real_div]) >> gvs[] >>
  dsimp[AllCaseEqs(), PULL_EXISTS] >> REWRITE_TAC [real_div] >>
  simp[REAL_SUB_LDISTRIB] >> Cases_on ‘n = 0’ >> gvs[]
  >- (rename [‘free_space ctl + free_space ctr’] >>
      ‘0 ≤ free_space ctl ∧ 0 ≤ free_space ctr ∧ free_space ctl ≤ 1 ∧
       free_space ctr ≤ 1’ by simp[free_space_bounds] >>
      ‘free_space ctl = 1 ∧ free_space ctr = 1’ by fsr[] >>
      rpt (dxrule_all_then SUBST_ALL_TAC packed_free_spaceEQ1) >>
      qpat_x_assum ‘packed _’ mp_tac >> simp[packed_def] >>
      qexistsl_tac [‘[F]’, ‘[T]’] >> simp[]) >>
  rename [‘packed (FullNode ctl ctr)’] >> Cases_on ‘largest_gap ctl’ >> simp[]
  >- (‘open_paths ctl = ∅’ by gvs[largest_gap_def, full_open_paths_EMPTY] >>
      gvs[open_paths_EMPTY_free_space] >> Cases_on ‘n’ >> gvs[] >>
      rename [‘2 pow SUC m’] >> gvs[pow] >> first_x_assum $ drule >>
      simp[REAL_INV_MUL]) >>
  rename [‘largest_gap ctl = SOME lg’] >> gvs[powr_negexp, lemma] >>
  simp[RealArith.REAL_ARITH “(x:real) + y = x + a - b ⇔ y = a - b”,
       RealArith.REAL_ARITH “(x:real) + y = a + y - b ⇔ x = a - b”] >>
  ‘∃m. n = m + 1’ by (Cases_on ‘n’ >> simp[ADD1]) >> gvs[REAL_POW_ADD] >>
  Cases_on ‘m + 1 ≤ lg’ >> simp[] >> first_x_assum irule
  >- (‘∃rg. largest_gap ctr = SOME rg ∧ rg ≤ m’
        suffices_by (strip_tac >> drule largest_gap_lbounds_free_space >>
                     strip_tac >> irule REAL_LE_TRANS >>
                     first_x_assum (irule_at Any) >>
                     irule REAL_LE_LMUL_IMP >>
                     simp[free_space_bounds, REAL_OF_NUM_POW]) >>
      drule_all_then strip_assume_tac packed_largest_gap_ubounds_free_space >>
      ‘free_space ctr ≠ 0’
        by (strip_tac >> gvs[] >>
            ‘free_space ctl * 2 pow lg < 2 * free_space ctl * 2 pow m’ by fsr[]>>
            ‘0 ≤ free_space ctl’ by simp[free_space_bounds] >> rgs[REAL_LE_LT] >>
            gvs[REAL_OF_NUM_POW, GSYM pow]) >>
      Cases_on ‘largest_gap ctr’ >> gvs[]
      >- gvs[largest_gap_def, full_open_paths_EMPTY, free_space_open_paths,
             REAL_SUM_IMAGE_THM] >>
      rename [‘largest_gap ctr = SOME rg’, ‘free_space ctr ≠ 0’] >>
      CCONTR_TAC >> gvs[NOT_LESS_EQUAL, DECIDE “x + 1n ≤ y ⇔ x < y”] >>
      map_every (C qpat_x_assum (K ALL_TAC)) [‘free_space ctr ≠ 0’, ‘∀n v. _’] >>
      wlog_tac ‘lg < rg’ [‘ctl’, ‘ctr’, ‘lg’, ‘rg’]
      >- (Cases_on ‘lg = rg’
          >- (rpt (dxrule_all largest_gap_exists_as_path) >>
              qpat_x_assum ‘packed (FullNode _ _)’ mp_tac >> simp[packed_def] >>
              rpt strip_tac >>
              rename [‘p1 ∈ open_paths ctl’, ‘free_space ctl + free_space ctr’,
                      ‘p2 ∈ open_paths ctr’] >>
              first_x_assum $ qspecl_then [‘F::p1’, ‘T::p2’] mp_tac >> simp[] >>
              metis_tac[]) >>
          ‘rg < lg’ by simp[] >>
          first_x_assum $ qspecl_then [‘ctr’, ‘ctl’, ‘rg’, ‘lg’] mp_tac >>
          simp[packed_FullNode_flips, REAL_ADD_COMM] >>
          drule_all packed_largest_gap_ubounds_free_space >>
          simp[]) >>
      ‘largest_gap (FullNode ctl ctr) = SOME (lg + 1)’ by simp[MIN_DEF] >>
      drule_at (Pos (el 2)) packed_largest_gap_ubounds_free_space >> simp[] >>
      REWRITE_TAC[real_div] >> simp[REAL_POW_ADD] >> strip_tac >>
      qabbrev_tac ‘FS = free_space ctl + free_space ctr’ >> gvs[] >>
      ‘inv (2 pow m) ≤ FS ∧ FS < 2 * inv (2 pow lg)’ by simp[] >>
      ‘inv (2 pow m) < 2 * inv (2 pow lg)’ by metis_tac[REAL_LET_TRANS] >>
      pop_assum mp_tac >> simp[REAL_NOT_LT] >> simp[GSYM pow] >>
      simp[REAL_OF_NUM_POW]) >>
  gvs[NOT_LESS_EQUAL] >> irule REAL_LE_TRANS >>
  drule_then (irule_at Any) largest_gap_lbounds_free_space >>
  irule REAL_LE_LMUL_IMP >> simp[free_space_bounds, REAL_OF_NUM_POW]
QED

Definition buildL_def[simp]:
  buildL i [] = SOME Empty ∧
  buildL i (w::ws) =
  case buildL (i + 1n) ws of
    NONE => NONE
  | SOME ct => insert w i ct
End

Theorem seq_sizeL:
  seq_size f 0 = 0 ∧
  seq_size f (SUC n) = inv (2 pow f 0) + seq_size (f o SUC) n
Proof
  simp[seq_size_def] >> Induct_on ‘n’ >> simp[seq_size_def] >> fsr[]
QED

Theorem buildL_succeeds:
  seq_size (flip EL ns) (LENGTH ns) ≤ 1 ⇒
  ∀n. ∃ct. buildL n ns = SOME ct ∧
           free_space ct = 1 - seq_size (flip EL ns) (LENGTH ns) ∧
           Lbiased ct
Proof
  Induct_on ‘ns’ >> simp[] >> rw[] >>
  gvs[seq_sizeL, combinTheory.o_DEF, combinTheory.C_DEF] >>
  ‘seq_size (λx. EL x ns) (LENGTH ns) ≤ 1’
    by (irule REAL_LE_TRANS >> first_assum $ irule_at Any >>
        simp[]) >>
  gvs[] >> first_x_assum $ qspec_then ‘n + 1’ strip_assume_tac >> simp[] >>
  qpat_x_assum ‘free_space _ = _’ (assume_tac o SYM) >>
  ‘inv (2 pow h) ≤ free_space ct’
    by (pop_assum (SUBST1_TAC o SYM) >> ASM_REWRITE_TAC[REAL_LE_SUB_LADD]) >>
  ‘packed ct’ by metis_tac[Lbiased_packed] >>
  drule free_space_guarantees_insert >> gvs[powr_negexp] >> disch_then drule >>
  disch_then $ qspec_then ‘n’ strip_assume_tac >> simp[] >> fsr[] >>
  metis_tac[insert_preserves_Lbiased]
QED

Theorem ctree_domain_first_tree[simp]:
  ctree_domain (first_tree n v) = {Fpow n}
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem codetree_to_fmap_first_tree[simp]:
  codetree_to_fmap (first_tree n v) = FEMPTY |+ (Fpow n, v)
Proof
  Induct_on ‘n’ >> simp[fmap_EXT, FUN_FMAP_DEF]
QED

Theorem insert_extends_domain:
  ∀ct0 w v ct.
    insert w v ct0 = SOME ct ⇒
    (∃p. ctree_domain ct = p INSERT ctree_domain ct0 ∧ p ∉ ctree_domain ct0 ∧
         LENGTH p = w ∧
         codetree_to_fmap ct ' p = v) ∧
    ∀q. q ∈ ctree_domain ct0 ⇒ codetree_to_fmap ct ' q = codetree_to_fmap ct0 ' q
Proof
  Induct >>
  simp[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, FUN_FMAP_DEF] >>
  rw[] >> simp[] >>
  first_x_assum $ drule_then $
    CONJUNCTS_THEN2 (qx_choose_then ‘p’ strip_assume_tac) strip_assume_tac
  >- (qexists_tac ‘T::p’ >> simp[FUN_FMAP_DEF] >> simp[EXTENSION] >>
      metis_tac[])
  >- (qexists_tac ‘T::p’ >> simp[FUN_FMAP_DEF] >> simp[EXTENSION] >>
      metis_tac[]) >>
  qexists_tac ‘F::p’ >> simp[FUN_FMAP_DEF] >> simp[EXTENSION] >>
  metis_tac[]
QED

Theorem buildL_bijection_props:
  ∀ws n ct.
    buildL n ws = SOME ct ⇒
    (∀p. p ∈ ctree_domain ct ⇒
         ∃i. i < LENGTH ws ∧ EL i ws = LENGTH p ∧
             codetree_to_fmap ct ' p = n + i) ∧
    ∀i. i < LENGTH ws ⇒
        ∃!p. p ∈ ctree_domain ct ∧ codetree_to_fmap ct ' p = n + i
Proof
  Induct_on ‘ws’ >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac>>
  drule_then (CONJUNCTS_THEN2 (qx_choose_then ‘hp’ strip_assume_tac)
              strip_assume_tac) insert_extends_domain >>
  dsimp[DISJ_IMP_THM, FORALL_AND_THM, LT_SUC] >> conj_tac
  >- (first_x_assum $ drule_all_then strip_assume_tac >>
      rpt strip_tac >> first_x_assum drule >> simp[ADD1] >>
      metis_tac[ADD_ASSOC, ADD_COMM]) >> conj_tac
  >- (simp[EXISTS_UNIQUE_THM] >> simp[EXISTS_OR_THM] >>
      dsimp[DISJ_IMP_THM, FORALL_AND_THM] >> csimp[] >>
      first_x_assum $ drule_then (assume_tac o CONJUNCT1) >> rpt strip_tac >>
      first_x_assum drule >> simp[]) >>
  csimp[] >> first_x_assum drule >> simp[ADD1]>>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem buildL_bijection:
  buildL 0 ws = SOME ct ⇒
  BIJ (FAPPLY (codetree_to_fmap ct)) (ctree_domain ct) (count (LENGTH ws))
Proof
  csimp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> strip_tac >>
  drule_then strip_assume_tac buildL_bijection_props >> rw[] >> gvs[]
  >- metis_tac[] >>
  PROVE_TAC[]
QED

Theorem seq_size_GENLIST:
  ∀f. seq_size f n = FOLDR (λn A. A + inv (2 pow n)) 0r (GENLIST f n)
Proof
  Induct_on ‘n’ >> simp[seq_sizeL, GENLIST_CONS] >> fsr[]
QED

Definition REAL_SUM_def:
  REAL_SUM [] = 0r ∧
  REAL_SUM (r::rs) = r + REAL_SUM rs
End

Theorem kraft_finite_ineq2:
  FOLDR (λn A. A + inv (2 pow n)) 0r ns ≤ 1 ⇒
  ∃(P : bool list set) b.
     prefix_free P ∧ BIJ b (count (LENGTH ns)) P ∧
     ∀i. i < LENGTH ns ⇒ LENGTH (b i) = EL i ns
Proof
  strip_tac >>
  ‘GENLIST (flip EL ns) (LENGTH ns) = ns’
    by simp[LIST_EQ, EL_GENLIST] >>
  ‘seq_size (flip EL ns) (LENGTH ns) ≤ 1’ by simp[seq_size_GENLIST] >>
  drule_then (qspec_then ‘0’ $ qx_choose_then ‘ct’ strip_assume_tac)
             buildL_succeeds >>
  drule_then assume_tac buildL_bijection>>
  drule_then assume_tac BIJ_LINV_BIJ >>
  first_assum $ irule_at Any >> simp[] >>
  qx_gen_tac ‘i’ >> strip_tac >>
  rev_drule_then strip_assume_tac (cj 1 $ iffLR BIJ_DEF) >>
  dxrule_then strip_assume_tac LINV_DEF >>
  drule_then strip_assume_tac buildL_bijection_props >>
  pop_assum drule >> simp[EXISTS_UNIQUE_THM] >> strip_tac >> rw[] >>
  gs[]
QED

Theorem REAL_SUM_FOLDR:
  FOLDR (λn A. A + f n) 0r ns = REAL_SUM (MAP f ns)
Proof
  Induct_on ‘ns’ >> simp[REAL_SUM_def, REAL_ADD_COMM]
QED

Theorem kraft_finite_converse =
  kraft_finite_ineq2 |> SIMP_RULE (srw_ss()) [REAL_SUM_FOLDR, GSYM powr_negexp]

val _ = export_theory();
