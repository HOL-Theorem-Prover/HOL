
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
open measureTheory;
open recfunsTheory;
open extNatTheory;
open prtermTheory;
open pred_setTheory;
open extrealTheory;
open realTheory;
open real_sigmaTheory;
open lebesgueTheory;
open transcTheory;
open kolmog_complexTheory;
val _ = new_theory "kraft_ineq";
val _ =ParseExtras.tight_equality();

val _ = intLib.deprecate_int()


val Tpow_def = Define`Tpow n = GENLIST (K T) n`

val Fpow_def = Define`Fpow n = GENLIST (K F) n`

val _ = set_mapped_fixity{fixity = Infix(NONASSOC,450),term_name = "prefix",tok="≺"}

val prefix_refl = Q.store_thm("prefix_refl[simp]",
`¬(l ≺ l)`,
simp[prefix_def])

val prefix_free_def = Define`prefix_free (s:α list set) = ∀a b. a ∈ s ∧ b∈s ==> ¬(a≺ b) `

val prefix_free_empty = Q.store_thm("prefix_free_empty[simp]",
`prefix_free ∅`,
rw[prefix_free_def])

val prefix_free_sing = Q.store_thm("prefix_free_sing[simp]",
`prefix_free {l}`,
rw[prefix_free_def])

val len_fun_def = Define`len_fun (A:bool list set) n = let strs = {s | (LENGTH s = n) ∧ s ∈ A} in EXTREAL_SUM_IMAGE (λs. Normal (2 rpow (- &(LENGTH s)))) strs`

val extreal_sum_image_finite_corr = Q.store_thm("extreal_sum_image_finite_corr",
`∀P. FINITE P ⇒ ∀f x. (∀y. (y ∈ P) ==> (f y = x)) ⇒ (SIGMA f P = &CARD P * x)`,
   REPEAT STRIP_TAC
   >> (MP_TAC o Q.SPECL [`P`]) extrealTheory.EXTREAL_SUM_IMAGE_FINITE_SAME
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.SPECL [`P`]) SET_CASES
   >> RW_TAC std_ss [] >-  rw[extrealTheory.EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, extrealTheory.mul_lzero]
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM MATCH_MP_TAC
   >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [IN_INSERT])


val bl2n_11 = Q.store_thm("bl2n_11[simp]",
`bl2n x = bl2n y <=> x = y`,
metis_tac[num_bool_inv])

val finite_bool_list_n = Q.store_thm("finite_bool_list_n[simp]",
`FINITE {s|LENGTH (s:bool list) = n}`,
irule (INST_TYPE[beta|->``:num``] FINITE_INJ) >> qexists_tac`bool_list_to_num` >>
          qexists_tac`count (2**(n+1)-1)` >> simp[INJ_DEF] >> qid_spec_tac`n` >> Induct_on`x`>>
          simp[bool_list_to_num_def] >> pop_assum(qspec_then`LENGTH x` MP_TAC) >>rw[] >> 
          simp[GSYM ADD1,Once EXP] >> irule (DECIDE``n<=2n ∧ b<x-1 ==> 2*b+n<2*x-1``) >> rw[ADD1])

val bool_list_card = Q.store_thm("bool_list_card[simp]",
`CARD {s | LENGTH (s:bool list) = n} = 2**n`,
Induct_on`n`>>simp[LENGTH_CONS] >> qmatch_abbrev_tac`CARD s = 2**(SUC n)`>> 
`s = IMAGE (CONS T) {s | LENGTH s = n} UNION IMAGE (CONS F) {s | LENGTH s = n}` by 
  (simp[Abbr`s`,EXTENSION,EQ_IMP_THM] >> rw[] ) >> simp[CARD_UNION_EQN,CARD_INJ_IMAGE,EXP] >> 
qmatch_abbrev_tac`(x:num)-y=x` >> `y=0`suffices_by simp[] >> simp[Abbr`y`,EXTENSION] >>Cases>>simp[]>>
metis_tac[]  )

val len_fun_eq1 = Q.store_thm("len_fun_eq1",
`SIGMA (λs. Normal (2 rpow -&LENGTH s)) {s | (LENGTH (s:bool list) = n)} = 1`,
irule EQ_TRANS >>qexists_tac`&CARD {s | LENGTH (s:bool list) = n} * Normal(2 rpow (-&n))` >> conj_tac
  >- (irule extreal_sum_image_finite_corr >> rw[])
  >- (simp[extreal_of_num_def,extreal_mul_def,GSYM realTheory.REAL_OF_NUM_POW,GEN_RPOW,
	   GSYM RPOW_ADD,RPOW_0 ] ))

val len_fun_le1 = Q.store_thm("len_fun_le1",
`len_fun A n <= 1`,
rw[len_fun_def] >> `{s | LENGTH s = n ∧ s ∈ A}⊆{s|LENGTH s = n}` by simp[SUBSET_DEF] >> 
`FINITE {s | LENGTH s = n ∧ s ∈ A}` by metis_tac[SUBSET_FINITE_I,finite_bool_list_n] >> 
ASSUME_TAC len_fun_eq1 >> pop_assum(SUBST1_TAC o SYM)>> irule EXTREAL_SUM_IMAGE_MONO_SET >> 
simp[finite_bool_list_n] >> rw[extreal_of_num_def,extreal_le_def] >> 
`0r < 2 `suffices_by(strip_tac >> drule RPOW_POS_LT >> simp[realTheory.REAL_LE_LT]) >>
simp[] )

(* Traditional bool list to num *)
val rev_fpow = Q.store_thm("rev_fpow[simp]",
`REVERSE (Fpow n) = Fpow n`,
simp[Fpow_def,listTheory.REVERSE_GENLIST,combinTheory.K_DEF])

val rev_tpow = Q.store_thm("rev_tpow[simp]",
`REVERSE (Tpow n) = Tpow n`,
simp[Tpow_def,listTheory.REVERSE_GENLIST,combinTheory.K_DEF])


val tbl2n_def = Define`tbl2n [] = 0n ∧ tbl2n (T::t) = 2*tbl2n t + 1 ∧ tbl2n (F::t) = 2*tbl2n t`

val _ = export_rewrites["tbl2n_def"]

val _ = overload_on("TBL2N",``λl. tbl2n (REVERSE l)``)

val inv_tbl2n_def = tDefine"inv_tbl2n"`inv_tbl2n 0n = [] ∧ 
                           inv_tbl2n a = if EVEN a 
                                         then [F]++(inv_tbl2n (a DIV 2))
                                         else [T]++(inv_tbl2n ((a-1) DIV 2 ))`
(WF_REL_TAC`$<` >> rw[]>>
irule LESS_EQ_LESS_TRANS >> qexists_tac`v` >> `0<2n` by simp[] >> rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ])

val tbl2n_inv_tbl2n = Q.store_thm("tbl2n_inv_tbl2n",
`tbl2n (inv_tbl2n n) = n`,
completeInduct_on `n` >> Cases_on`n` >> simp[tbl2n_def,inv_tbl2n_def] >> Cases_on`EVEN (SUC n')` >> 
simp[tbl2n_def] 
  >- (`2 * (SUC n' DIV 2) =  (SUC n' DIV 2)*2` by simp[MULT_COMM] >> `0<2n` by simp[] >> 
       `SUC n' MOD 2=0` by metis_tac[EVEN_MOD2] >>
       `SUC n' DIV 2 * 2 + SUC n' MOD 2 = SUC n'` by metis_tac[GSYM DIVISION] >> fs[])
  >- (`0<2n` by simp[] >> `n' DIV 2 <= n'` by simp[DIV_LESS_EQ] >> `n' DIV 2 < SUC n'` by 
        simp[LESS_EQ_IMP_LESS_SUC] >> fs[] >> `EVEN n'` by metis_tac[ODD,EVEN_OR_ODD] >>  
       `2 * (n' DIV 2) =  (n' DIV 2)*2` by simp[MULT_COMM] >> `0<2n` by simp[] >> 
       `n' MOD 2=0` by metis_tac[EVEN_MOD2] >>
       `n' DIV 2 * 2 + n' MOD 2 = n'` by metis_tac[GSYM DIVISION] >> fs[] ) )

val interval_bl_def = Define`interval_bl l = (&(TBL2N l) *(2 rpow -&LENGTH l),(2 rpow -&LENGTH l))`

val disjoint_interval_def = Define`disjoint_interval ((m:real),i) (n,j) <=> 
                                   DISJOINT {r|m<=r ∧ r<m+i} {r|n<=r ∧ r<n+j}`

val tbl2n_exp2 = Q.store_thm("tbl2n_exp2",
`tbl2n i * 2 ** n = tbl2n ((Fpow n)++i)`,
rw[Fpow_def] >> Induct_on`n` >> simp[tbl2n_def,EXP,GENLIST_CONS])

val TBL2N_exp2 = Q.store_thm("TBL2N_exp2",
`TBL2N i * 2 ** n = TBL2N (i++(Fpow n))`,
simp[REVERSE_APPEND] >> rw[Fpow_def] >> Induct_on`n` >> simp[tbl2n_def,EXP,GENLIST_CONS])


val tbl2n_lead0s = Q.store_thm("tbl2n_lead0s[simp]",
`tbl2n (x ++ Fpow n) = tbl2n x`,
Induct_on`x` >> simp[tbl2n_def] 
  >- (`tbl2n (Fpow n ++ []) = tbl2n (Fpow n )` by simp[] >> 
      `tbl2n (Fpow n ++ []) = (tbl2n []) *2**n` by metis_tac[GSYM tbl2n_exp2] >> fs[tbl2n_def])
  >- (Cases_on `h` >> simp[tbl2n_def])  )

val tbl2n_fpow = Q.store_thm("tbl2n_fpow[simp]",
`tbl2n (Fpow n) = 0`,
simp[Fpow_def] >> Induct_on`n` >> simp[GENLIST_CONS])

val len_fpow = Q.store_thm("len_fpow[simp]",
`LENGTH (Fpow n) = n`,
simp[Fpow_def])

val TBL2N_lead0s = Q.store_thm("TBL2N_lead0s[simp]",
`TBL2N (Fpow n ++ x) = TBL2N x`,
simp[REVERSE_APPEND]  )

val tbl2n_append_1 = Q.store_thm("tbl2n_append_1",
`tbl2n (x++[e]) = if e then 2**(LENGTH x) + (tbl2n x) else tbl2n x`,
Induct_on`x` >> simp[] >- (Cases_on`e` >> simp[]) >> Cases_on`h` >> simp[] >> rw[] >> simp[EXP] );

val tbl2n_append_full = Q.store_thm("tbl2n_append_full",
`∀y. tbl2n (x++y) = tbl2n x + 2**(LENGTH x) * tbl2n y`,
Induct_on`x` >> simp[] >> Cases_on`h` >> simp[EXP])

val tbl2n_ub = Q.store_thm("tbl2n_ub[simp]",
`tbl2n l < 2**(LENGTH l)`,
Induct_on`l` >> simp[] >> Cases_on`h` >> simp[EXP]);

val TBL2N_ub = Q.store_thm("TBL2N_ub[simp]",
`TBL2N l < 2**(LENGTH l)`,
metis_tac[tbl2n_ub,LENGTH_REVERSE]);


val TBL2N_inj_len = Q.store_thm("TBL2N_inj_len",
`∀x y.(LENGTH x = LENGTH y) ==> (TBL2N x = TBL2N y <=> x=y)`,
Induct_on`x` >> simp[] >> Cases_on`y` >> simp[] >> rw[tbl2n_append_1] >> 
`TBL2N t < 2** LENGTH t` by  (metis_tac[tbl2n_ub,LENGTH_REVERSE]) >>  
`TBL2N x < 2** LENGTH t` by  (metis_tac[tbl2n_ub,LENGTH_REVERSE]) >>simp[]);

val TBL2N_lem1 = Q.store_thm("TBL2N_lem1",
`∀δ. δ<2**Δ ==> ∃l. TBL2N l = δ ∧ LENGTH l = Δ ∧ TBL2N (i++Fpow Δ) +δ = TBL2N (i++l)`,
Induct_on`Δ` >- simp[Fpow_def] >> rw[EXP] >> Cases_on`δ<2**Δ` >> fs[]
  >- (res_tac >> qexists_tac`F::l` >> simp[] >> fs[REVERSE_APPEND] >> simp[tbl2n_append_full])
  >- (qabbrev_tac`δ0=δ-2**Δ` >> `δ0 < 2**Δ` by simp[Abbr`δ0`] >> res_tac >> qexists_tac`T::l` >>
      simp[] >>fs[REVERSE_APPEND] >> simp[tbl2n_append_full] >> simp[Abbr`δ0`] ) )

val prefix_lem1 = Q.store_thm("prefix_lem1",
`0<LENGTH b  ==> (a++b = c ==> a ≺c )`,
simp[prefix_def,rich_listTheory.IS_PREFIX_APPEND] >> rw[] >- (qexists_tac`b` >> simp[]) >> rw[]>>
metis_tac[listTheory.NOT_NIL_EQ_LENGTH_NOT_0]  )

val disjoint_pf_lem1 = Q.store_thm("disjoint_pf_lem1",
`(TBL2N i * 2 ** (LENGTH j - LENGTH i) <= TBL2N j) ∧ (TBL2N j < (TBL2N i + 1) * 2 ** (LENGTH j - LENGTH i)) ∧ (LENGTH i < LENGTH j) ==> i ≺ j`,
rw[TBL2N_exp2] >> qabbrev_tac`Δ=LENGTH j − LENGTH i` >> 
`TBL2N (i ++ Fpow Δ) + (TBL2N j-TBL2N (i ++ Fpow Δ)) = TBL2N j` by simp[] >> 
qabbrev_tac`δ=TBL2N j-TBL2N (i ++ Fpow Δ)` >> `δ<2**Δ` by (fs[RIGHT_ADD_DISTRIB] >> 
  `TBL2N j - TBL2N i * 2 ** Δ < 2 ** Δ` by simp[] >> 
  `TBL2N j − TBL2N (i ++ Fpow Δ) < 2**Δ` by simp[GSYM TBL2N_exp2] >> fs[Abbr`δ`] ) >> 
`∃l. TBL2N l = δ ∧ LENGTH l = Δ ∧ TBL2N (i++Fpow Δ) +δ = TBL2N (i++l)` by simp[TBL2N_lem1] >> 
`TBL2N (i ++ l) = TBL2N j` by simp[] >> `LENGTH (i++l) = LENGTH j` by simp[Abbr`Δ`] >> 
`i++l = j` by metis_tac[TBL2N_inj_len] >> `0<LENGTH l` by simp[Abbr`Δ`] >> metis_tac[prefix_lem1] )

val prefix_length_lt = Q.store_thm("prefix_length_lt",
`a ≺ b ==> LENGTH a < LENGTH b`,
rw[prefix_def] >> `LENGTH a <= LENGTH b` by fs[rich_listTheory.IS_PREFIX_LENGTH] >> 
Cases_on`LENGTH a = LENGTH b` >> simp[] >> metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI])


val tbl2n_append = Q.store_thm("tbl2n_append",
`tbl2n (p++s) = 2**LENGTH p * (tbl2n s) +tbl2n p`,
Induct_on`p` >> simp[] >> Cases_on`h` >> rw[GSYM ADD1,EXP,LEFT_ADD_DISTRIB] )

val TBL2N_append = Q.store_thm("TBL2N_append",
`TBL2N (p++s) = 2**LENGTH s * (TBL2N p) +TBL2N s`,
simp[REVERSE_APPEND,tbl2n_append])

val prefix_append= Q.store_thm("prefix_append",
`a ≺ b <=> ∃s. b=a++s ∧ s<>[]`,
simp[prefix_def] >> rw[rich_listTheory.IS_PREFIX_APPEND,EQ_IMP_THM] >> metis_tac[APPEND_NIL,APPEND_EQ_SELF])

val disjoint_prefix_free = Q.store_thm("disjoint_prefix_free",
`prefix_free P <=> let is = IMAGE interval_bl P in ∀i1 i2. i1 ∈ is ∧ i2∈is ∧ i1<>i2 ==> disjoint_interval i1 i2`,
rw[EQ_IMP_THM] 
>- (rename[`interval_bl i = interval_bl j`] >> 
    `¬(i ≺ j) ∧ ¬(j ≺ i)∧ i<>j` by metis_tac[prefix_free_def] >> 
    fs[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION] >> 
    rw[GSYM DISJ_ASSOC] >> rw[DECIDE``¬p∨q ⇔ p⇒q``] >> strip_tac >> 
    `LENGTH i <> LENGTH j` by (strip_tac >> fs[] >> qabbrev_tac`M = 2 rpow -&LENGTH j` >> 
      `&TBL2N i * M < &TBL2N j * M + M` by metis_tac[REAL_LET_TRANS] >>
      `&TBL2N j * M < &TBL2N i * M + M` by metis_tac[REAL_LET_TRANS] >>
      `&TBL2N i * M + M = (&TBL2N i + 1) * M` by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >>  
      `&TBL2N j * M + M = (&TBL2N j + 1) * M` by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >> fs[] >>
      `(0:real)<2` by fs[] >> `0<M` by metis_tac[RPOW_POS_LT] >>
      `((&TBL2N i) :real) < &(TBL2N j + 1)` by fs[REAL_LT_RMUL] >> 
      `((&TBL2N j):real) < &(TBL2N i + 1)` by fs[REAL_LT_RMUL] >> fs[] ) >> 
    wlog_tac `LENGTH i < LENGTH j` [`i`,`j`,`x`] >- (`LENGTH j < LENGTH i` by simp[] >> metis_tac[])>>
    `&TBL2N i * 2 rpow -&LENGTH i < &TBL2N j * 2 rpow -&LENGTH j + 2 rpow -&LENGTH j` by 
      metis_tac[REAL_LET_TRANS]>> 
    `&TBL2N i * 2 rpow -&LENGTH i < (&TBL2N j +1) * 2 rpow -&LENGTH j` by 
      metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >> `(0:real)<2` by fs[] >>
    `&TBL2N i * 2 rpow  -&LENGTH i * 2 rpow &LENGTH j < 
     (&TBL2N j +1)  * 2 rpow -&LENGTH j  * 2 rpow &LENGTH j` by 
       metis_tac[RPOW_POS_LT,REAL_LT_RMUL] >> 
    fs[GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,add_ints] >> rfs[]>>
    `&TBL2N j * 2 rpow -&LENGTH j < &TBL2N i * 2 rpow -&LENGTH i + 2 rpow -&LENGTH i` by 
      metis_tac[REAL_LET_TRANS] >>
    `&TBL2N j * 2 rpow -&LENGTH j < (&TBL2N i +1) * 2 rpow -&LENGTH i` by 
      metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >> `(0:real)<2` by fs[] >>
    `&TBL2N j * 2 rpow  -&LENGTH j * 2 rpow &LENGTH j < 
     (&TBL2N i +1)  * 2 rpow -&LENGTH i  * 2 rpow &LENGTH j` by 
       metis_tac[RPOW_POS_LT,REAL_LT_RMUL] >>
    fs[GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,add_ints] >> rfs[] >>
    qabbrev_tac`Δ=LENGTH j − LENGTH i` >> qabbrev_tac`ii= TBL2N i` >> 
    qabbrev_tac`jj= TBL2N j` >> fs[GSYM GEN_RPOW,REAL_OF_NUM_POW] >> 
    fs[disjoint_pf_lem1])
>- (fs[prefix_free_def,PULL_EXISTS] >>rw[] >>
  strip_tac >>`interval_bl a <> interval_bl b` by 
   (fs[interval_bl_def] >> rw[] >> `LENGTH a < LENGTH b` by simp[prefix_length_lt]>> 
    `real_of_num (LENGTH a) < real_of_num (LENGTH b)` by fs[REAL_LT] >> 
    `-(real_of_num (LENGTH b)) < -(real_of_num(LENGTH a))` by fs[REAL_LT_NEG] >> 
    `1<(2:real)` by simp[]>>`2 rpow -&LENGTH b < 2 rpow -&LENGTH a` by fs[RPOW_LT]>>
    fs[REAL_LT_IMP_NE])>>
  first_x_assum drule_all >>
  fs[interval_bl_def,disjoint_interval_def] >> rw[DISJOINT_DEF,EXTENSION] >> 
  qexists_tac`&TBL2N b * 2 rpow -&LENGTH b` >> rw[]
    >- (`0<2 rpow &LENGTH b` by fs[RPOW_POS_LT] >> 
        drule_then (ONCE_REWRITE_TAC o list_of_singleton o GSYM) REAL_LE_RMUL >> 
        fs[GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,add_ints]>>
        drule_then assume_tac prefix_length_lt >> simp[] >>
        fs[GSYM GEN_RPOW,REAL_OF_NUM_POW] >> fs[prefix_append,TBL2N_append]  )
    >- (`0<2 rpow &LENGTH b` by fs[RPOW_POS_LT] >> 
        drule_then (ONCE_REWRITE_TAC o list_of_singleton o GSYM) REAL_LT_RMUL >>
        drule_then assume_tac prefix_length_lt >>
        fs[GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,add_ints,
           REAL_ADD_RDISTRIB,GSYM GEN_RPOW,REAL_OF_NUM_POW] >>
        fs[prefix_append,TBL2N_append] )
    >- (rw[REAL_LT_ADDR] >> `0<(2:real)` by simp[] >> fs[RPOW_POS_LT]) ))


val size_of_interval_bl = Q.store_thm("size_of_interval_bl",
`Normal (SND (interval_bl y))  = Normal (2 rpow -&LENGTH y)`,
rw[interval_bl_def])

val TBL2N_append_sing_ub = Q.store_thm("TBL2N_append_sing_ub",
`&(TBL2N (a++[h]) + 1)*2 rpow (-1) <= &(TBL2N a + 1)`,
`&(2 * TBL2N a + 2) * 2 rpow -1 ≤ &(TBL2N a + 1)` by  
  (`&(2 * TBL2N a + 2) * 2 rpow -1 = &(2*(TBL2N a + 1)) * 2 rpow -1` by fs[GSYM LEFT_ADD_DISTRIB]>> 
   `_ = 2 * &(TBL2N a + 1) * 2 rpow -1` by fs[REAL_MUL] >> 
   `_ = &(TBL2N a + 1)*(2 rpow 1 * 2 rpow -1)`by 
     fs[AC REAL_MUL_ASSOC REAL_MUL_COMM,RPOW_1]>>
   `_ = &(TBL2N a + 1) * 2 rpow (1+ -1)` by fs[RPOW_ADD] >>
   fs[RPOW_0,REAL_ADD_RINV]  ) >>
Cases_on`h` >> rw[TBL2N_append] >> 
`&(2 * TBL2N a + 1) * 2 rpow -1 <= &(2 * TBL2N a + 2) * 2 rpow -1` by 
  (irule REAL_LE_RMUL_IMP >> rw[RPOW_POS_LT,REAL_LE_LT]) >> 
irule REAL_LE_TRANS >> qexists_tac`&(2 * TBL2N a + 2) * 2 rpow -1` >> rw[] )

val interval_bl_bounds = Q.store_thm("interval_bl_bounds",
`0<= FST (interval_bl a) ∧ FST (interval_bl a) + SND (interval_bl a) <= 1`,
rw[] >- (fs[interval_bl_def] >> `(0:real)<= &TBL2N a` by fs[tbl2n_def] >> `(0:real)<2` by simp[] >>
         `0<2 rpow -&LENGTH a` by fs[RPOW_POS_LT] >> 
         metis_tac[util_probTheory.REAL_LE_LT_MUL] )
     >- (fs[interval_bl_def] >>
         `&TBL2N a * 2 rpow -&LENGTH a + 2 rpow -&LENGTH a = (&TBL2N a +1)* 2 rpow -&LENGTH a` by 
         fs[REAL_RDISTRIB] >> pop_assum SUBST1_TAC >>  
         `0<2 rpow &LENGTH a` by fs[RPOW_POS_LT] >> 
        drule_then (ONCE_REWRITE_TAC o list_of_singleton o GSYM) REAL_LE_RMUL >> 
        simp[GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,GSYM GEN_RPOW,REAL_OF_NUM_POW] >> 
        (TBL2N_ub |> Q.INST [`l`|->`a`] |> assume_tac) >> simp[]  ) )

val bls_size_def = Define`bls_size (P:bool list -> bool) n = SIGMA (λs. (2 rpow -&LENGTH s)) {x|x ∈ P ∧ LENGTH x < n }`

val finite_bool_list_lt_n = Q.store_thm("finite_bool_list_lt_n",
`FINITE {(s:bool list) | LENGTH s < n}`,
Induct_on`n` >> simp[finite_bool_list_n] >> 
`FINITE {(s:bool list)|LENGTH s = n}` by fs[finite_bool_list_n] >> 
`FINITE ({(s:bool list) | LENGTH s < n ∨ LENGTH s = n}) ` by simp[FINITE_UNION,GSPEC_OR] >> 
`{(s:bool list) | LENGTH s < SUC n} = {s | LENGTH s < n ∨ LENGTH s = n}` by rw[EXTENSION] >>fs[])

val finite_and = Q.store_thm("finite_and",
`FINITE {s| P s} ==> FINITE {s|  Q s ∧ P s}`,
rw[] >> `{s | Q s ∧ P s} = {s | Q s}  ∩ {s | P s}` by fs[INTER_DEF] >> fs[FINITE_INTER])

val interval_bl_sigma = Q.store_thm("interval_bl_sigma",
`FINITE  {x | x ∈ P} ==> 
SIGMA (λa. SND (interval_bl a)) {x | x ∈ P} = SIGMA (λa. 2 rpow -&LENGTH a) {x | x ∈ P} `,
rw[] >> irule REAL_SUM_IMAGE_EQ >> rw[] >> simp[interval_bl_def]);


fun fsr thl = full_simp_tac(srw_ss () ++ realSimps.REAL_ARITH_ss) thl;



val disjoint_interval_thm = Q.store_thm("disjoint_interval_thm",
`disjoint_interval (interval_bl i) (interval_bl j) ==> 
FST (interval_bl i) + SND (interval_bl i) <= FST (interval_bl j) ∨ 
FST (interval_bl j) + SND (interval_bl j) <= FST (interval_bl i)`,
rw[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION,PULL_EXISTS] >> 
Cases_on` &TBL2N i * 2 rpow -&LENGTH i + 2 rpow -&LENGTH i < &TBL2N j * 2 rpow -&LENGTH j` >> 
fsr[]>> 
qabbrev_tac`id=2 rpow -&LENGTH i` >> qmatch_abbrev_tac`_ ∨ jj+jd<=ii:real` >>
spose_not_then assume_tac >>
fsr[REAL_NOT_LT,REAL_NOT_LE]  >> 
first_x_assum(fn th => qspec_then`jj` assume_tac th >> qspec_then`ii` assume_tac th) >> fsr[]
>- (`id<= 0` by metis_tac[REAL_LE_LADD,REAL_ADD_RID] >> 
    `0<id` suffices_by metis_tac[REAL_LET_TRANS,REAL_LT_REFL] >> simp[Abbr`id`,RPOW_POS_LT])
>- (`jd<= 0` by metis_tac[REAL_LE_LADD,REAL_ADD_RID] >> 
    `0<jd` suffices_by metis_tac[REAL_LET_TRANS,REAL_LT_REFL] >> simp[Abbr`jd`,RPOW_POS_LT]) )


val max_rs_lemma = Q.prove(`∀s. FINITE s ==> s<>{} ==> ∃x:real. x∈s ∧ ∀y. y∈s ==> y<=x`,
Induct_on`FINITE` >>rw[] >> Cases_on`s={}` >> fs[] >> qexists_tac`max e x` >> fsr[max_def] >> rw[]
>- metis_tac[] >> Cases_on`y=e`>> fsr[] >> RES_TAC >> fsr[] )

val min_rs_lemma = Q.prove(`∀s. FINITE s ==> s<>{} ==> ∃x:real. x∈s ∧ ∀y. y∈s ==> x<=y`,
Induct_on`FINITE` >>rw[] >> Cases_on`s={}` >> fs[] >> qexists_tac`min e x` >> fsr[min_def] >> rw[]>>
Cases_on`y=e`>> fsr[] >> RES_TAC >> fsr[] )

val maxr_set_def = new_specification("maxr_set_def",["maxr_set"],
SIMP_RULE(srw_ss() )[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] max_rs_lemma)

val minr_set_def = new_specification("minr_set_def",["minr_set"],
SIMP_RULE(srw_ss() )[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] min_rs_lemma)

val exten_def = Define`exten s = (minr_set {FST k| k ∈ s},maxr_set {FST k + SND k|k∈s})`

val maxr_set_thm = Q.store_thm("maxr_set_thm[simp]",
`maxr_set {e} = e ∧ (FINITE s ∧ s<> {} ==> maxr_set (e INSERT s) = max e (maxr_set s))`,
rw[] >- (qspec_then `{e}` mp_tac maxr_set_def >> simp[]) >> 
qspec_then `e INSERT s` mp_tac maxr_set_def  >> simp[] >> strip_tac >> 
qabbrev_tac`m = maxr_set (e INSERT s)` >> qspec_then`s` mp_tac maxr_set_def >> simp[] >> 
qabbrev_tac`m0 = maxr_set s` >> rw[] >> rw[max_def] 
>- (Cases_on`e = m0` >> rw[] >- (simp[Abbr`m`,ABSORPTION_RWT]) >> Cases_on`e=m` >> rw[]
    >- (`m0<=e` by metis_tac[] >> fsr[]) >> metis_tac[REAL_LE_ANTISYM]  ) >> 
spose_not_then strip_assume_tac >> `m<=m0` by fsr[] >> `m<e` by fsr[] >> `e<=m` by fsr[] >> fsr[])

val minr_set_thm = Q.store_thm("maxr_set_thm[simp]",
`minr_set {e} = e ∧ (FINITE s ∧ s<> {} ==> minr_set (e INSERT s) = min e (minr_set s))`,
rw[] >- (qspec_then `{e}` mp_tac minr_set_def >> simp[]) >> 
qspec_then `e INSERT s` mp_tac minr_set_def  >> simp[] >> strip_tac >> 
qabbrev_tac`m = minr_set (e INSERT s)` >> qspec_then`s` mp_tac minr_set_def >> simp[] >> 
qabbrev_tac`m0 = minr_set s` >> rw[] >> rw[min_def] 
>- (Cases_on`e = m0` >> rw[] >- (simp[Abbr`m`,ABSORPTION_RWT]) >> Cases_on`e=m` >> rw[] >>
    `m<=e` by metis_tac[] >>`m∈s` by fs[] >>`m0<=m` by fs[] >> metis_tac[REAL_LE_ANTISYM]) >> 
spose_not_then strip_assume_tac >> `m<=m0` by fsr[] >> `m0<e` by fsr[] >> `m<=e` by fsr[] >> 
Cases_on`m=e` >> fsr[] >> `m0 <= m` by fsr[] >> fsr[])

val maxr_set_union = Q.store_thm("maxr_set_union",
`∀s1. (FINITE s1) ==> ∀s2. (FINITE s2) ==> (s1 <> ∅ ∧  s2 <> ∅) ==> 
  maxr_set (s1 ∪ s2)=max (maxr_set s1) (maxr_set s2)`,
Induct_on`FINITE` >> strip_tac
>- (Induct_on`FINITE` >>rw[maxr_set_thm] )
>- (ntac 4 strip_tac >> Induct_on`FINITE` >> rw[maxr_set_thm] >> 
    Cases_on`s2 <> {}` >> Cases_on`s1 <> {}` >> rw[] >>simp[maxr_set_thm] 
    >- (Cases_on`e<= maxr_set s1` >> Cases_on`e'<= maxr_set s2` >> 
        fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[]
        >- (Cases_on`maxr_set s1 <= maxr_set s2` >> fsr[]) 
        >- (Cases_on`maxr_set s1 <= e'` >> fsr[]) )
    >- (Cases_on`e'<= maxr_set s2` >> 
        fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[])
    >- (Cases_on`e<= maxr_set s1` >> fs[max_def,maxr_set_thm,INSERT_UNION_EQ] >> rw[] >> 
        fsr[] >> Cases_on`maxr_set s1 <= e'` >> fsr[])
    >- (fs[max_def,maxr_set_thm,INSERT_UNION_EQ]) )
)


val minr_set_union = Q.store_thm("minr_set_union",
`∀s1. (FINITE s1) ==> ∀s2. (FINITE s2) ==> (s1 <> ∅ ∧  s2 <> ∅) ==> 
  minr_set (s1 ∪ s2)=min (minr_set s1) (minr_set s2)`,
Induct_on`FINITE` >> strip_tac
>- (Induct_on`FINITE` >>rw[minr_set_thm] )
>- (ntac 4 strip_tac >> Induct_on`FINITE` >> rw[minr_set_thm] >> 
    Cases_on`s2 <> {}` >> Cases_on`s1 <> {}` >> rw[] >>simp[minr_set_thm] 
    >- (Cases_on`e<= minr_set s1` >> Cases_on`e'<= minr_set s2` >> 
        fs[min_def,minr_set_thm,INSERT_UNION_EQ] >> rw[] >> fsr[]
        >- (Cases_on`minr_set s1 <= e'` >> fsr[]) 
        >- (Cases_on`minr_set s1 <= minr_set s2` >> fsr[]) )
    >- (Cases_on`e<= minr_set s1` >> fs[min_def,minr_set_thm,INSERT_UNION_EQ] >> rw[] >> 
        fsr[] >> Cases_on`minr_set s1 <= e'` >> fsr[])
    >- (Cases_on`e<= minr_set s1` >> fs[min_def,minr_set_thm,INSERT_UNION_EQ] >> rw[] >> 
        fsr[] >> Cases_on` minr_set s1 ≤ e'` >>rw[] >> fsr[])
    >- (fs[min_def,minr_set_thm,INSERT_UNION_EQ]) )
)


val gspec_eq = Q.store_thm("gspec_eq[simp]",
`GSPEC (λx. (f x,x=k)) = {f k}`,
simp[EXTENSION])

val gspec_in = Q.store_thm("gspec_in[simp]",
`GSPEC (λx. (f x,x∈k)) = {f x|x∈k}`,
simp[EXTENSION])

val gspec_f_or = Q.store_thm("gspec_f_or[simp]",
`∀P Q. {f x | P x ∨ Q x} = {f x | P x} ∪ {f x | Q x}`,
rw[IN_UNION,EXTENSION] >> metis_tac[GSPECIFICATION_applied])



val exten_insert_thm = Q.store_thm("exten_insert_thm",
`(s <> ∅ ∧ FINITE s) ==> exten (e INSERT s) =  (min (FST e) ## max (FST e + SND e)) (exten s)`,
simp[exten_def,maxr_set_thm,minr_set_thm] >> rw[] 
>- (`{FST k | k <> e ==> k ∈ s} = {FST k | k = e ∨ k ∈ s}` by fs[EXTENSION] >>
    `{FST k | k = e ∨ k ∈ s} = {FST k | k = e} ∪ {FST k | k ∈ s}` by fs[] >> rw[] >> 
    `FINITE {FST e}` by fs[] >> `{FST e} <> {}` by fs[] >> 
    `FINITE {FST k | k ∈ s}` by metis_tac[IMAGE_FINITE,IMAGE_DEF] >> 
    `{FST k | k ∈ s} <> {}` by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF]>>
    rw[minr_set_union])
>- (`{FST k + SND k | k <> e ==> k ∈ s} = {FST k + SND k | k = e ∨ k ∈ s}` by fs[EXTENSION] >>
    `{FST k + SND k | k = e ∨ k ∈ s} = {FST k + SND k | k = e} ∪ {FST k + SND k | k ∈ s}` by fs[] >> 
    rw[] >> 
    `FINITE {FST e  + SND k}` by fs[] >> `{FST e  + SND k} <> {}` by fs[] >> 
    `FINITE {FST k + SND k | k ∈ s}` by metis_tac[IMAGE_FINITE,IMAGE_DEF] >> 
    `{FST k + SND k | k ∈ s} <> {}` by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF]>>
    rw[maxr_set_union] ))

val TBL2N_ub2 = Q.store_thm("TBL2N_ub2",
`&TBL2N x * 2 rpow -&LENGTH x +  2 rpow -&LENGTH x <= 1`,
`0<2 rpow &LENGTH x` by fs[RPOW_POS_LT] >> 
drule_then (ONCE_REWRITE_TAC o list_of_singleton o GSYM) REAL_LE_RMUL >>
simp[REAL_ADD_RDISTRIB,GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,GSYM GEN_RPOW,REAL_OF_NUM_POW] >> 
(TBL2N_ub |> Q.INST [`l`|->`x`] |> assume_tac) >> simp[TBL2N_ub] )

val rpow_len_lb = Q.store_thm("rpow_len_lb",
`0<  2 rpow -&LENGTH x`,
fs[RPOW_POS_LT])

val TBL2N_lb = Q.store_thm("TBL2N_lb",
`0<= &TBL2N x * 2 rpow -&LENGTH x`,
`0<2 rpow &LENGTH x` by fs[RPOW_POS_LT] >> 
drule_then (ONCE_REWRITE_TAC o list_of_singleton o GSYM) REAL_LE_RMUL >> 
simp[REAL_ADD_RDISTRIB,GSYM REAL_MUL_ASSOC,GSYM RPOW_ADD,RPOW_0,GSYM GEN_RPOW,REAL_OF_NUM_POW])

val lemma11 = Q.store_thm("lemma11",
`∀s. FINITE s ==> (∀x dx y dy. (x,dx)∈s ∧ (y,dy) ∈ s ∧ x<>y ==> x+dx<=y ∨ y+dy<=x) ∧
              (∀x d. (x,d)∈s ==> 0r<d) ∧ (∀x d. (x,d)∈s ==> 0<= x ∧ x+d <=1) ∧ (s <> {}) 
          ==> (0<= FST (exten s) ∧ SND (exten s) <= 1)`,
Induct_on`FINITE` >> simp[] >>ntac 2 (gen_tac>>strip_tac) >>strip_tac >> Cases_on`s={}` >> fs[]
>- (simp[maxr_set_def,minr_set_def,exten_def,ITSET_THM] >> Cases_on`e` >> fs[]) >>
fs[exten_insert_thm] >> rw[max_def,min_def]
>- (Cases_on`e` >> fsr[] >> metis_tac[])
>- (metis_tac[])
>- (metis_tac[]) )

val BETTER_RPOW_UNIQ_EXP = Q.store_thm("BETTER_RPOW_UNIQ_EXP[simp]",
`1 < a ==> (a rpow b = a rpow c <=> b = c)`,
rw[] >> eq_tac >> simp[] >> rw[] >> pop_assum (mp_tac o AP_TERM ``ln``) >> fsr[LN_RPOW] >> 
disch_then irule >> `ln 1 < ln a` by fsr[LN_MONO_LT] >> fsr[LN_1] )


val interval_bl_11 = Q.store_thm("interval_bl_11[simp]",
`interval_bl x = interval_bl y <=> x = y`,
simp[interval_bl_def] >> eq_tac >> simp[] >> rw[] >> fsr[TBL2N_inj_len,RPOW_NZ])

val interval_bl_inj = Q.store_thm("interval_bl_inj",
`INJ interval_bl P (IMAGE interval_bl P)`,
simp[INJ_DEF])

val lemma12 = Q.prove(`bls_size P n = SIGMA SND (IMAGE interval_bl {s|s ∈ P ∧ LENGTH s < n})`,
fs[bls_size_def,interval_bl_def,REAL_SUM_IMAGE_IMAGE,interval_bl_inj,finite_bool_list_lt_n,finite_and,combinTheory.o_DEF])

val exten_sing = Q.store_thm("exten_sing[simp]",
`exten {e} = (FST e,FST e + SND e)`,
fs[exten_def])

val size_of_exten = Q.prove(
`∀s. FINITE s ==> (∀x dx y dy. (x,dx)∈s ∧ (y,dy) ∈ s ∧ (x,dx)<>(y,dy) ==> x+dx<=y ∨ y+dy<=x) ∧
              (∀x d. (x,d)∈s ==> 0r<d) ∧ (s <> {}) 
          ==> SIGMA SND s <= SND (exten s) - FST (exten s)`,
HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION >> rw[] >> 
map_every qabbrev_tac[`Rs = {FST k + SND k | k∈s}`,`Ls = {FST k |k∈s}`]>>
`FINITE Ls` by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
`Ls <> {}` by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>
`∃e1 e2. (e1,e2)∈s ∧ ∀m. m∈ Ls ==> e1<=m` 
  by (qexists_tac `minr_set Ls` >> qexists_tac`@e'. (minr_set Ls,e')∈s` >> reverse(rw[])
      >- (metis_tac[minr_set_def]) >> SELECT_ELIM_TAC >> simp[] >> 
      `minr_set Ls ∈ Ls` by metis_tac[minr_set_def] >> fs[Abbr`Ls`] >> 
      metis_tac[pairTheory.PAIR]) >>
qabbrev_tac`s0 = s DELETE (e1,e2)` >> Cases_on`s0={}` >> simp[] 
  >- (`s = {(e1,e2)}` by (metis_tac[DELETE_EQ_SING]) >> rw[REAL_SUM_IMAGE_THM] >> fsr[]) >> 
`s0 ⊂ s` by (fs[Abbr`s0`,PSUBSET_MEMBER]>> metis_tac[]) >> last_x_assum drule >> impl_tac
  >- (rw[Abbr`s0`] >> metis_tac[]) >> `s = (e1,e2) INSERT s0` by fs[Abbr`s0`] >> 
`s0 DELETE (e1,e2) = s0` by fs[Abbr`s0`,ELT_IN_DELETE,DELETE_NON_ELEMENT] >>
fsr[REAL_SUM_IMAGE_THM] >> 
`SND (exten s0) - FST (exten s0) <=  SND (exten ((e1,e2) INSERT s0)) − FST (exten ((e1,e2) INSERT s0)) - e2` suffices_by fsr[] >> 
fsr[exten_def,exten_insert_thm,REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >>
map_every qabbrev_tac [`MX = maxr_set {FST k + SND k | k ∈ s0}`,`MN = minr_set  {FST k | k ∈ s0}`]>>
map_every qabbrev_tac[`Rs0 = {FST k + SND k | k∈s0}`,`Ls0 = {FST k |k∈s0}`] >>
`FINITE Ls0` by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
`Ls0 <> {}` by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>
`MN ∈ Ls0` by metis_tac[minr_set_def] >>
`∃n. (MN,n)∈s0` by (`∃p. p∈s0 ∧ FST p = MN` suffices_by (rw[] >> metis_tac[pairTheory.PAIR]) >>
                    pop_assum MP_TAC >> simp[Abbr`Ls0`] >> metis_tac[]) >>
`MN ∈ Ls` by (simp[Abbr`Ls`] >>metis_tac[pairTheory.FST]) >>
rw[max_def,min_def] >> fsr[]
>- (`e1 + e2 <= MN` suffices_by fsr[] >> 
    first_x_assum(qspecl_then[`e1`,`e2`,`MN`,`n`] MP_TAC) >> simp[] >> impl_tac
    >- (rpt strip_tac >> rw[] >> rw[Abbr`s0`] >> fs[]) >> strip_tac >> `e1<=MN` by fs[]>>
     `0<n` suffices_by fsr[] >> metis_tac[]  )
>- (`MX < e1+e2` by fsr[] >> `FINITE Rs0` by metis_tac[IMAGE_FINITE,IMAGE_DEF] >>
    `Rs0 <> {}` by metis_tac[IMAGE_EQ_EMPTY,IMAGE_DEF] >>`MX ∈ Rs0` by metis_tac[maxr_set_def]>>
    `∃i j. (i,j)∈s0 ∧ MX = i+j` by (pop_assum MP_TAC >> simp[Abbr`Rs0`] >> 
                                    metis_tac[pairTheory.PAIR]) >> 
    first_x_assum(qspecl_then[`e1`,`e2`,`i`,`j`] MP_TAC) >> simp[] >> impl_tac
    >- (rpt strip_tac >> rw[] >> rw[Abbr`s0`] >> fs[]) >> strip_tac
    >- (rw[] >> `0<j` suffices_by fsr[] >> metis_tac[]) >> rw[] >> 
    `i∈Ls` by (simp[Abbr`Ls`,pairTheory.EXISTS_PROD] >>metis_tac[])>> `e1<=i` by simp[]>>
    `0<j` suffices_by fsr[] >> metis_tac[]  ) )

(*  In progress of proving *)

val lemma1 = Q.prove("lemma1",
`(let is = IMAGE interval_bl P in ∀i1 i2. i1 ∈ is ∧ i2∈is ∧ i1<>i2 ==> disjoint_interval i1 i2)
 ==>(∀n. bls_size P n <= 1)`,
rw[EQ_IMP_THM,PULL_EXISTS] >> fs[bls_size_def,disjoint_interval_thm] >> 
`FINITE  {x | x ∈ P ∧ LENGTH x < n}` by metis_tac[finite_and,finite_bool_list_lt_n] >>
`FINITE {(λy. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y)) x| x∈ {z | z ∈ P ∧ LENGTH z <n}}`
 by metis_tac[IMAGE_FINITE,IMAGE_DEF] >> fs[] >> 
qabbrev_tac`s = {(&TBL2N x * 2 rpow -&LENGTH x,2 rpow -&LENGTH x) |  x ∈ P ∧ LENGTH x < n}` >>
Cases_on`s={}` 
>- (`{x | x ∈ P ∧ LENGTH x < n} = {}` by (fs[Abbr`s`] >> 
      `{(λy. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y))  x | x ∈ P ∧ LENGTH x < n} = {}`
        by simp[] >> 
      `IMAGE (λx. (&TBL2N x * 2 rpow -&LENGTH x,2 rpow -&LENGTH x)) {x | x ∈ P ∧ LENGTH x < n}
        = {(λy. (&TBL2N y * 2 rpow -&LENGTH y,2 rpow -&LENGTH y))  x | x ∈ P ∧ LENGTH x < n}`
        by fs[IMAGE_DEF] >> metis_tac[IMAGE_EQ_EMPTY]) >> fs[REAL_SUM_IMAGE_THM] ) >> 
`0<= FST (exten s) ∧ SND (exten s) <= 1` by 
  (irule lemma11 >> rw[]>> fsr[Abbr`s`,TBL2N_lb,rpow_len_lb,TBL2N_ub2] >> 
   rw[] >> `x'<>x''` by (metis_tac[FUN_EQ_THM]) >> 
   `disjoint_interval (interval_bl x') (interval_bl x'')` by simp[] >> 
   `FST (interval_bl x') + SND (interval_bl x') ≤ FST (interval_bl x'') ∨
     FST (interval_bl x'') + SND (interval_bl x'') ≤ FST (interval_bl x')` by 
     simp[disjoint_interval_thm]  >> fs[interval_bl_def] ) >>
`SIGMA (λa. 2 rpow -&LENGTH a) {x|x∈{x | x ∈ P ∧ LENGTH x < n}}=
  SIGMA (λa. SND (interval_bl a)) {x|x∈{x | x ∈ P ∧ LENGTH x < n}}` by (fs[interval_bl_sigma]) >>
fs[] >> `SIGMA (λs. SND (interval_bl s)) {x | x ∈ P ∧ LENGTH x < n} = 
         SIGMA (λx. x) (IMAGE (λa. SND (interval_bl a)) {x | x ∈ P ∧ LENGTH x < n})` by 
         (irule REAL_SUM_IMAGE_IMAGE)

rw[Once interval_bl_def]
fs[interval_bl_def,disjoint_interval_def] >> simp[REAL_SUM_IMAGE_DISJOINT_UNION] )


val kraft_ineq1 = Q.store_thm("kraft_ineq1",
`∀P. prefix_free P ==> ∃y0. y0<=1 ∧ bls_size P --> y0`,
(* `∀P. prefix_free P <=> suminf bls_size P <= SOME 1`  *)
Let L(x) = [x*2**-LENGTH(x) , x*2**-LENGTH(x)+2**-LENGTH(x)] >> L(x) are disjoint cus prefix free >> length of L(x) is 2**-LENGTH(x) >> L(x) subste of [0,1] for all x >> sum <= length [0,1] =1 )
 
val numl_size_def = Define`numl_size L n = SIGMA (λs. (2 rpow -&s)) {x|x ∈ L ∧ x < n }`

val kraft_ineq_conv = Q.store_thm("kraft_ineq_conv",
`∀L. (∃y0. y0<=1 ∧ numl_size L --> y0) ==> 
(∃P. prefix_free P ∧ (∀p. p∈P ==> ∃l. l∈L ∧ LENGTH p = l) ∧ (∀l. l∈L ==> ∃p. p∈P ∧ LENGTH p=l ) )`,
) 


(* Have done initial Kolmog stuff *)

val prefix_machine_def = Define`prefix_machine (U:bool list -> extnat) = 
                                ∃P. prefix_free P∧(∀x. x ∈ P <=> ∃y. U x = SOME y)`

val monotone_machine_def = Define`monotone_machine (U:bool list -> extnat) = 
                     ∀p1 p2. ∃x1 x2. (U p1 = (SOME x1)) ∧ (U p2 = (SOME x2)) ==> (p1 ≼ p2 ==> (n2bl x1 ≼ n2bl x2 ∨ n2bl x2 ≼ n2bl x1) )`

val kolmog_complexity_def = Define`kolmog_complexity x U =
                       if  { p | U p = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | U p = SOME x})`;

val prefix_kolmog_complexity_def = Define`pkolmog_complexity x U = 
                                if prefix_machine U then kolmog_complexity x U else NONE`

(* Mono def not working right now  *)
val monotone_kolmog_complexity_def = Define`mkolmog_complexity x U = 
                                if monotone_machine U then 
                                  if ∀y. { p | (U p = SOME y) ∧ (x ≼ (n2bl y)) } = {} then NONE
                                   else SOME (MIN_SET {LENGTH p |∃y. (U p = SOME y) ∧(x ≼ n2bl y)}) 
                                else NONE`

val kolmog_def = Define`kolmog x = kolmog_complexity x universal_tm`


val bar_def = Define`bar x = (Tpow (LENGTH x)) ++ [F] ++ x`

val bl_len_def = Define`bl_len bl = n2bl (LENGTH bl)`

val dash_def = Define`dash x = (Tpow (LENGTH (bl_len x))) ++ [F] ++ (bl_len x) ++ x`

val pair_def = Define`pair x y = (dash x) ++ y`

val cond_kolmog_complexity_def = Define`cond_kolmog_complexity x y U = 
                       if  { p | U (pair y p) = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | U (pair y p) = SOME x})`

val cond_kolmog_def = Define`cond_kolmog x y = cond_kolmog_complexity x y universal_tm`


(** up to here **)
(* In Process of proving   *)



(*

val leastR_def = Define`leastR R A = @a. a IN A ∧ ∀b. b IN A ==> ~R b a`

val order_def = tDefine"order"`(order A R 0 = leastR R A) ∧
                (order A R (SUC n) = leastR R (A DIFF IMAGE (λi. order A R i) (count (SUC n))))`(WF_REL_TAC`measure (SND o SND)` >> simp[])

val tmorder_def = Define`tmorder x = order {p | universal_tm p = x} `

val listlex_def = Define`(listlex [] x <=> x<>[])∧(listlex (h::t) [] <=> F)∧
                         (listlex (h1::t1) (h2::t2) <=>
			 (LENGTH t1 < LENGTH t2) ∨ ((LENGTH t1 = LENGTH t2) ∧ ((h1=h2) ∧ listlex t1 t2 ∨ ~h1 ∧ h2 )  ) )`

val listlex_length = Q.store_thm("listlex_length",
`!a b. LENGTH a < LENGTH b ==> listlex a b`,
Cases_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def])

val listlex_length2 = Q.store_thm("listlex_length2",
`!a b. listlex a b ==> (LENGTH a <= LENGTH b)`,
Induct_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def] >> rpt strip_tac >>
simp[])

val listlex_empty = Q.store_thm("listlex_empty[simp]",
`listlex a [] <=> F`,
Cases_on `a` >> simp[listlex_def])

val listlex_same_length = Q.store_thm("listlex_same_length",
`!B l w. (!b. B b ==> (LENGTH b = l)) ∧ B w ==> ?v. B v ∧ (!b. listlex b v ==> ~B b)`,
Induct_on `l` >> simp[] >- (rw[] >> qexists_tac`[]` >> simp[] >> metis_tac[]) >>
rw[] >> Cases_on`?hf. B' hf ∧ (HD hf = F)`
>- (fs[] >>
    `?c. B' c ∧ (HD c= F) ∧ (!d. listlex d c ==> ~B' d)`
      by (first_x_assum(qspec_then`{t|B' (F::t)}`MP_TAC) >> simp[] >>
          disch_then(qspec_then`TL hf`MP_TAC) >> Cases_on `hf` >> simp[]
          >- (res_tac >> fs[]) >> fs[] >> impl_tac
	      >- (rw[] >> res_tac>> fs[]) >>
	      rw[] >> qexists_tac`F::v` >> simp[]>> rpt strip_tac >> Cases_on`d` >> fs[]
              >- (res_tac >> fs[])
              >- (fs[listlex_def] >- (res_tac >> fs[]) >> rw[] >> metis_tac[] ))>> metis_tac[])
>- (fs[] >>first_x_assum(qspec_then`{t|B' (T::t)}`MP_TAC) >> simp[] >> Cases_on `w`
    >- (res_tac >> fs[]) >> `h = T` by metis_tac[HD] >> rw[] >>
        pop_assum(qspec_then`t`MP_TAC) >> impl_tac
	>- (rw[] >> res_tac >> fs[]) >> rw[] >> qexists_tac`T::v` >> fs[] >> Cases_on `b`
	    >- (rpt strip_tac >> res_tac >> fs[]) >> rw[listlex_def] >> strip_tac
	        >- (res_tac >> fs[])
		>- (metis_tac[])
		>- (metis_tac[HD]) ) )

val WF_listlex = Q.store_thm("WF_listlex",`WF listlex`,
simp[relationTheory.WF_DEF] >> rw[] >>
`?v. B' v ∧ !v'. B' v' ==> LENGTH v <= LENGTH v'`
  by (`WF (inv_image $< (LENGTH:bool list -> num) )` by (simp[relationTheory.WF_inv_image])>>
  fs[relationTheory.WF_DEF] >> metis_tac[NOT_LESS])>>
  qspecl_then[`{l|B' l ∧ (LENGTH l = LENGTH v)}`,`LENGTH v`,`v`] MP_TAC listlex_same_length >>
  rw[] >> qexists_tac`v'` >> rw[] >> strip_tac >> `LENGTH b <> LENGTH v` by metis_tac[] >>
  `LENGTH v' < LENGTH b` by metis_tac[LESS_OR_EQ] >>
  `listlex v' b` by metis_tac[listlex_length] >>
  metis_tac[LESS_EQUAL_ANTISYM,listlex_length2,prim_recTheory.LESS_REFL] )

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
			    if n=0 then []
			    else if EVEN n then
				T::num_to_bool_list((n-2) DIV 2)
			    else
				F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC `$<` >> intLib.ARITH_TAC)

val solomonoff_prior_def = Define`
solomonoff_prior x = suminf (λn. let b = num_to_bool_list n in
				     if universal_tm b = x
				     then inv(2 pow (LENGTH b))
				     else 0) `


val existence_of_universal_semimeasure = Q.store_thm("existence_of_universal_semimeasure",
`∃M. (semimeasure M) ∧ (universal_semimeasure M setX) ∧ (continous M) ∧ (lower_semicompute M)`,
qexists_tac `solomonoff_prior` >> conj_tac)

val summed_square_error_a_def = Define`summed_square_a_error mu a n =
                                       sum for (x IN Bstar:length x = n-1)
                                       (mu x) *(sqrt (cond_M a x) - sqrt (cond_mu a x))**2`

val summed_square_error_def = Define`summed_square_error mu n =
                                     sum for (a in B) summed_square_a_error mu a n`

val KL_dis_def = Define`KL_dis P Q = sum for (a in B) P(a)*log (P(a)/Q(a))`

val hellinger_dis_def = Define`hellinger_dis P Q = sum for (a in B) (sqrt(P(a)) - sqrt(Q(a)))**2`

val KL_greater_hellinger = Q.store_thm("KL_greater_hellinger",
`hellinger_dis P Q <= KL_dis P Q`,
)

val KL_M_dis_def = Define`KL_M_dis mu x = KL_dis (λy. cond_M y x) (λy. cond_mu y x)`

val sum_KL_M_dis_def = Define`sum_KL_M_dis mu n = sum for (x:length x = n-1)
                                                  (mu x) * (KL_M_dis mu x)`

val solomonoff_thm_claim_1 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==> summed_square_error mu n <= sum_KL_M_dis mu n`,
 )

val solomonoff_thm_claim_11 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==>
 sum for (n in N) summed_square_error mu n <= sum for (n in N) sum_KL_M_dis mu n`,
rw[sum_of_stuff,solomonoff_thm_claim_1] )

val solomonoff_thm_claim_2 = Q.store_thm("solomonoff_thm_claim_2",
`(computable_measure mu) ==> sum for (n in N) sum_KL_M_dis mu n <= (kolmog_complexity mu)*(log 2)`,
  )

val solomonoff_theorem = Q.store_thm("solomonoff_theorem",
`(computable_measure mu) ==>
 (sum for (n in N) summed_square_error mu n <= (kolmog_complexity mu)*(log 2) )`
rw[LESS_EQ_TRANS,solomonoff_thm_claim_11,solomonoff_thm_claim_2])
 *)




val _ = export_theory();
