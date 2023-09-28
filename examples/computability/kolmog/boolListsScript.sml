open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pred_setTheory
open primrecfnsTheory unary_recfnsTheory recursivefnsTheory
     prtermTheory recfunsTheory
open reductionEval
val _ = new_theory "boolLists";

val _ = intLib.deprecate_int()

val _ = ParseExtras.tight_equality()

val prefix_def = Define`prefix a b <=> a≼b ∧ a <> b`

val _ = set_mapped_fixity{fixity = Infix(NONASSOC,450),term_name = "prefix",tok="≺"}

Theorem TWOMULTDIV[simp]:
  2 * x DIV 2 = x
Proof
  metis_tac[DECIDE “0 < 2n”, MULT_COMM, MULT_DIV]
QED

Theorem TWOMULTP1_DIV[simp]:
  (2 * x + 1) DIV 2 = x
Proof
  metis_tac[MULT_COMM, DIV_MULT, DECIDE “1 < 2n”]
QED

val prefix_lem1 = Q.store_thm("prefix_lem1",
`0<LENGTH b  ==> (a++b = c ==> a ≺ c )`,
simp[prefix_def,rich_listTheory.IS_PREFIX_APPEND] >> rw[] >- (qexists_tac`b` >> simp[]) >> rw[]>>
metis_tac[listTheory.NOT_NIL_EQ_LENGTH_NOT_0]  )

val prefix_length_lt = Q.store_thm("prefix_length_lt",
`a ≺ b ==> LENGTH a < LENGTH b`,
rw[prefix_def] >> `LENGTH a <= LENGTH b` by fs[rich_listTheory.IS_PREFIX_LENGTH] >>
Cases_on`LENGTH a = LENGTH b` >> simp[] >> metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI])

Theorem prefix_append:
  a ≺ b <=> ?s. b=a++s /\ s<>[]
Proof
  simp[prefix_def] >> rw[rich_listTheory.IS_PREFIX_APPEND,EQ_IMP_THM] >>
  metis_tac[APPEND_NIL,APPEND_EQ_SELF]
QED

Definition num_to_bool_list_def:
   num_to_bool_list n = if n=0 then []
                        else if EVEN n then T::num_to_bool_list((n-2) DIV 2)
                        else F::num_to_bool_list((n-1) DIV 2)
Termination
  WF_REL_TAC`$<` >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac`n DIV 2` >> rw[DIV_LE_MONOTONE,DIV_LESS]
End
Overload n2bl = ``num_to_bool_list``
Overload "ℓ" = ``λp. LENGTH (num_to_bool_list p) ``


Theorem n2bl_simps[simp]:
  n2bl 0 = [] ∧
  n2bl (2 * n + 1) = F :: n2bl n ∧
  n2bl (2 * n + 2) = T :: n2bl n
Proof
  rpt conj_tac >> simp[Once num_to_bool_list_def, SimpLHS, EVEN_ADD, EVEN_MULT]
QED

Definition bool_list_to_num_def[simp]:
  bool_list_to_num [] = 0n ∧
  bool_list_to_num (h::t) = (if h then 2 else 1) + 2 * bool_list_to_num t
End
Overload bl2n = ``bool_list_to_num``

Theorem num_bool_inv[simp]:
  num_to_bool_list (bool_list_to_num l) = l
Proof
  Induct_on `l` >> simp[Once num_to_bool_list_def] >> Cases_on `h` >>
  simp[EVEN_ADD,EVEN_MULT] >> metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``]
QED

val bool_num_inv = Q.store_thm("bool_num_inv[simp]",
`∀n. bool_list_to_num (num_to_bool_list n) = n`,
ho_match_mp_tac (theorem"num_to_bool_list_ind") >> rpt strip_tac >>
  rw[Once num_to_bool_list_def,bool_list_to_num_def]
  >- (MP_TAC(Q.INST[`n`|->`2`,`q`|->`1`,`m`|->`n`]DIV_SUB)>>fs[]>>impl_keep_tac
      >-(fs[EVEN_EXISTS])>>simp[LEFT_SUB_DISTRIB]>>Q.SPEC_THEN`2`MP_TAC DIVISION>>fs[]>>
      disch_then(Q.SPEC_THEN`n`(MP_TAC o SYM) ) >> fs[EVEN_MOD2] )
  >- (fs[GSYM ODD_EVEN,ODD_EXISTS] >>metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``,ADD1] ) )

Theorem ELL_TWOMULTP1[simp]:
  ℓ (2 * x + 1) = ℓ x + 1
Proof
  simp[]
QED

Theorem bl2n_append:
  ∀xs ys. bl2n(xs++ys) = bl2n xs + bl2n ys *2**LENGTH xs
Proof
Induct_on `xs` >> simp[bool_list_to_num_def] >> simp[LEFT_ADD_DISTRIB,EXP]
QED


val Tpow_def = Define`Tpow n = GENLIST (K T) n`

Theorem LENGTH_Tpow[simp]:
  LENGTH (Tpow n) = n
Proof
  simp[Tpow_def]
QED


Definition Fpow_def: Fpow n = GENLIST (K F) n
End

Theorem Fpow0_thm[simp]:
  Fpow 0 = [] ∧
  Fpow (SUC n) = F :: Fpow n
Proof
  simp[Fpow_def, GENLIST_CONS]
QED


val prefix_refl = Q.store_thm("prefix_refl[simp]",
`~(l ≺ l)`,
simp[prefix_def])

val prefix_free_def = Define`prefix_free (s:'a list set) = ∀a b. a ∈ s /\ b ∈ s ==> ¬(a ≺ b) `

val prefix_free_empty = Q.store_thm("prefix_free_empty[simp]",
`prefix_free EMPTY `,
rw[prefix_free_def])

val prefix_free_sing = Q.store_thm("prefix_free_sing[simp]",
`prefix_free {l}`,
rw[prefix_free_def])


val bar_def = Define`bar x = (Tpow (LENGTH x)) ++ [F] ++ x`

val bl_len_def = Define`bl_len bl = n2bl (LENGTH bl)`

val dash_def = Define`dash x = (Tpow (LENGTH (bl_len x))) ++ [F] ++ (bl_len x) ++ x`

val pair_def = Define`pair x y = (bar x) ++ y`

val tpow_append = Q.store_thm("tpow_append",
`Tpow (a+b) = Tpow a ++ Tpow b`,
ONCE_REWRITE_TAC[ADD_COMM] >> fs[Tpow_def,GENLIST_APPEND,combinTheory.K_DEF])

val tpow_suc = Q.store_thm("tpow_suc",
`Tpow (SUC a) = T::(Tpow a)`,
fs[Tpow_def,GENLIST_CONS])

val prefix_free_bar = Q.store_thm("prefix_free_bar",
`prefix_free (IMAGE bar s)`,
fs[prefix_free_def,PULL_EXISTS] >> rw[] >> rename[`bar x ≺ bar y`] >> simp[bar_def] >> strip_tac >>
fs[prefix_append] >>
`LENGTH x = LENGTH y` by
  (`¬(LENGTH x < LENGTH y) ∧¬(LENGTH y < LENGTH x)` suffices_by simp[] >> rpt strip_tac
   >-(`∃i. LENGTH y = LENGTH x + i ∧ 0<i` by intLib.ARITH_TAC >>
      full_simp_tac bool_ss[GSYM APPEND_ASSOC,APPEND_11,tpow_append] >> Cases_on`i` >> fs[tpow_suc])
   >-(`∃i. LENGTH x = LENGTH y + i ∧ 0<i` by intLib.ARITH_TAC >>
      full_simp_tac bool_ss[GSYM APPEND_ASSOC,APPEND_11,tpow_append] >> Cases_on`i` >> fs[tpow_suc]))>>full_simp_tac bool_ss[GSYM APPEND_ASSOC,APPEND_11] >>
first_x_assum(mp_tac o AP_TERM``LENGTH:bool list -> num``) >> simp[] >> Cases_on`s'` >> fs[]  )

val unbar_def = Define`unbar [] = [] ∧
                       unbar (T::x) = unbar x ∧
                       unbar (F::x) = x `;


val unbar_tpow = Q.store_thm("unbar_tpow",
`unbar (Tpow n ++ x) = unbar x`,
simp[Tpow_def] >> Induct_on`n` >> simp[unbar_def,GENLIST_CONS])

val unbar_bar_inv = Q.store_thm("bar_unbar_inv[simp]",
`∀x. unbar (bar x) = x `,
fs[bar_def] >> REWRITE_TAC[GSYM APPEND_ASSOC,unbar_tpow,APPEND,unbar_def])



Theorem length_bar[simp]:
  LENGTH (bar x) = 2 * LENGTH x + 1
Proof
  fs[bar_def]
QED

val prefix_free_subset = Q.store_thm("prefix_free_subset",
`prefix_free s ∧ t ⊆ s ==> prefix_free t`,
rw[prefix_free_def,SUBSET_DEF] )

val barred_def = Define`barred x = ∃y. x=bar y`

val bar2_def = Define`bar2 (x,y) = (bar x) ++ (bar y)`

val bar2ed_def = Define`bar2ed x = ∃y z. x = (bar y)++(bar z)`

Theorem bar2ed_bar2[simp]:
  bar2ed (bar2 p)
Proof
  Cases_on`p` >> simp[bar2ed_def,bar2_def] >> metis_tac[]
QED

val unbar2_def = Define`unbar2 i (T::rest) = unbar2 (i+1) rest ∧
                        unbar2 i (F::rest) = (TAKE i rest,unbar (DROP i rest))`

val unbar2_induct_bar2 = Q.store_thm("unbar2_induct_bar2",
`∀i. unbar2 i (Tpow j ++ F::rest) = (TAKE (i+j) rest,unbar (DROP (i+j) rest))`,
simp[Tpow_def] >> Induct_on`j` >> simp[unbar2_def,GENLIST_CONS,ADD1])

val bar_lt_bar_f = Q.store_thm("bar_lt_bar_f[simp]",
`bar x ≺ bar y <=> F`,
MP_TAC (Q.INST[`s`|->`{x;y}`]prefix_free_bar) >> simp[prefix_free_def,PULL_EXISTS])

val Tpow_LENGTH = Q.store_thm("Tpow_LENGTH[simp]",
`LENGTH (Tpow x) = x`,
fs[Tpow_def,LENGTH_GENLIST])

val bar_one_to_one =  Q.store_thm("bar_one_to_one[simp]",
`bar x = bar y <=> x=y`,
eq_tac >> fs[bar_def] >> Cases_on`LENGTH x = LENGTH y`>> fs[]>> rw[] >>
`LENGTH (Tpow (LENGTH x) ++ [F] ++ x) = LENGTH (Tpow (LENGTH y) ++ [F] ++ y)` by metis_tac[] >>
fs[LENGTH_APPEND] )

val bar_eq_bar_append = Q.store_thm("bar_eq_bar_append[simp]",
`bar x = bar y ++ l <=> x=y ∧ l=[]`,
eq_tac >> simp[] >> strip_tac >> `l=[]` by metis_tac[prefix_append,bar_lt_bar_f] >> fs[])

val bar_eq_nil = Q.store_thm("bar_eq_nil[simp]",
`bar a <> []`,
fs[bar_def])

val bar2_PF = Q.store_thm("bar2_PF",
`prefix_free (IMAGE bar2 s)`,
fs[prefix_free_def,PULL_EXISTS,pairTheory.FORALL_PROD,bar2_def] >> rw[] >> strip_tac >>
drule prefix_length_lt >> rw[] >> strip_tac >> fs[prefix_append] >>
rename[`bar p ++ bar q = bar a ++ bar b ++ r`]>> fs[APPEND_EQ_APPEND] >> rw[] >> fs[] >>
full_simp_tac bool_ss [GSYM APPEND_ASSOC,bar_eq_bar_append,APPEND_eq_NIL] >> rw[]>>fs[] )

val unbar2_bar2_inv = Q.store_thm("unbar2_bar_inv[simp]",
`unbar2 0 (bar2 x) = x`,
Cases_on`x` >> rw[bar2_def,bar_def] >>
REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,unbar2_induct_bar2,rich_listTheory.TAKE_LENGTH_APPEND,
             rich_listTheory.DROP_LENGTH_APPEND,ADD_CLAUSES] >> simp[GSYM bar_def] )

val bar2_one_to_one = Q.store_thm("bar2_one_to_one[simp]",
`bar2 (x,y) = bar2 (a,b) <=> x = a ∧ y = b`,
eq_tac  >> fs[bar2_def] >> rw[APPEND_EQ_APPEND] >> fs[] )

val bar2ed_plus_def = Define`bar2ed_plus x <=> ∃y i q. x=(bar y)++(bar i)++q`

val unbar2p_def = Define`unbar2p i (T::rest) = unbar2p (i+1) rest ∧
                         unbar2p i (F::rest) = (TAKE i rest, (DROP i rest))`

val unbar2_plus_def = Define`unbar2_plus x =
  (FST (unbar2 0 x), FST (unbar2p 0 (SND (unbar2p 0 x))), SND (unbar2p 0 (SND (unbar2p 0 x))) )`

Theorem unbar2p_induct:
  ∀i. unbar2p i (Tpow j ++ F::rest) =
       (TAKE (i + j) rest, (DROP (i + j) rest))
Proof
  simp[Tpow_def] >> Induct_on`j` >> simp[unbar2p_def,GENLIST_CONS,ADD1]
QED

Theorem unbar2_plus_corr:
  unbar2_plus ((bar y) ++ (bar i) ++q) = (y,i,q)
Proof
  fs[unbar2_plus_def] >>rw[bar2_def,bar_def] >>
  REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,unbar2_induct_bar2,unbar2p_induct,
               rich_listTheory.TAKE_LENGTH_APPEND, rich_listTheory.DROP_LENGTH_APPEND,ADD_CLAUSES]
QED

Theorem Tpow_F_eq[simp]:
  Tpow a ++ [F] = Tpow b ++ [F] <=> a=b
Proof
  `TAKE a (Tpow a ++ [F]) = Tpow a` by
    (fs[Tpow_def,TAKE_GENLIST] >> `LENGTH (GENLIST (K T) a) = a` by fs[] >>
     metis_tac[rich_listTheory.TAKE_LENGTH_APPEND] ) >>
  `TAKE b (Tpow b ++ [F]) = Tpow b` by
    (fs[Tpow_def,TAKE_GENLIST] >> `LENGTH (GENLIST (K T) b) = b` by fs[] >>
     metis_tac[rich_listTheory.TAKE_LENGTH_APPEND] ) >>
  fs[Tpow_def] >>
  `LENGTH (GENLIST (K T) a) = a` by fs[LENGTH_GENLIST] >>
  `LENGTH (GENLIST (K T) b) = b` by fs[LENGTH_GENLIST] >> metis_tac[]
QED

Theorem DROP_Tpow[simp]:
  DROP a (Tpow b) = Tpow (b-a)
Proof
  simp[Tpow_def,DROP_GENLIST]
QED

Theorem Tpow_Fapp_eq[simp]:
  Tpow a ++ [F] ++ x = Tpow b ++ [F] ++ y <=> a=b ∧ x=y
Proof
  wlog_tac `a<=b` []
  >- (`b<=a` by fs[] >> metis_tac[]) >> eq_tac>>simp[] >> strip_tac >>
  Cases_on`a=b`>> fs[] >> `a<b` by fs[] >>
  `DROP a (Tpow a ++ [F] ++ x) = [F]++x` by
    metis_tac[GSYM APPEND_ASSOC,APPEND,rich_listTheory.DROP_LENGTH_APPEND,Tpow_LENGTH] >>
  `DROP a (Tpow b ++ [F] ++ y) = Tpow (b-a) ++ [F]++y` by
    simp[rich_listTheory.DROP_APPEND1,Tpow_LENGTH] >>
  last_x_assum SUBST_ALL_TAC>>
  Cases_on`b-a`>>fs[tpow_suc]
QED

val bar2ped_def = Define`bar2ped x <=> ∃i q. x = (bar i) ++ q`


Theorem unbar2p_bar[simp]:
  unbar2p 0 (bar x) = (x,[])
Proof
  fs[bar_def] >> `Tpow (LENGTH x) ++ [F] ++ x = Tpow (LENGTH x) ++ F::x` by fs[] >>
  rw[unbar2p_induct] >> `DROP (LENGTH x) x = DROP (LENGTH x) (x++[])` by fs[] >>
  rw[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem unbar2p_0[simp]:
  unbar2p 0 (Tpow j ++ [F] ++ rest) = (TAKE j rest,DROP j rest)
Proof
  `Tpow j ++ [F] ++ rest = Tpow j ++ F::rest` by fs[] >> rw[unbar2p_induct]
QED

Theorem unbar2p_0_double[simp]:
 unbar2p 0 (Tpow j ++ [F] ++ rest1 ++ rest2) = (TAKE j (rest1 ++ rest2),DROP j (rest1++rest2))
Proof
  `Tpow j ++ [F] ++ rest1++rest2 = Tpow j ++ F::(rest1 ++ rest2)` by fs[] >> rw[unbar2p_induct]
QED

Theorem unbar2p_0_triple[simp]:
 unbar2p 0 (Tpow j ++ [F] ++ rest1 ++ rest2 ++ rest3) = (TAKE j (rest1 ++ rest2++rest3),DROP j (rest1++rest2++rest3))
Proof
  `Tpow j ++ [F] ++ rest1++rest2++rest3 = Tpow j ++ F::(rest1 ++ rest2 ++ rest3)` by fs[] >> rw[unbar2p_induct]
QED

Theorem drop_n2bl[simp]:
  DROP (ℓ x) (n2bl x) = []
Proof
  `n2bl x = n2bl x ++ []` by fs[] >> metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED


Theorem TAKE_LENGTH_APPEND2[simp]:
  TAKE (LENGTH l1) (l1 ++ l2 ++ l3) = l1
Proof
  `l1++l2++l3 = l1 ++ (l2++l3)` by fs[] >>
  REWRITE_TAC [APPEND,GSYM APPEND_ASSOC,rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem DROP_LENGTH_APPEND2[simp]:
  DROP (LENGTH l1) (l1 ++ l2 ++ l3) = l2++l3
Proof
  `l1++l2++l3 = l1 ++ (l2++l3)` by fs[] >>
  REWRITE_TAC [APPEND,GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND]
QED


val bl2n_11 = Q.store_thm("bl2n_11[simp]",
`bl2n x = bl2n y <=> x = y`,
metis_tac[num_bool_inv])

val finite_bool_list_n = Q.store_thm("finite_bool_list_n[simp]",
`FINITE {s|LENGTH (s:bool list) = n}`,
irule (INST_TYPE[beta|->``:num``] FINITE_INJ) >> qexists_tac`bool_list_to_num` >>
          qexists_tac`count (2n**(n+1)-1)` >> simp[INJ_DEF] >> qid_spec_tac`n` >> Induct_on`x`>>
          simp[bool_list_to_num_def] >> pop_assum(qspec_then`LENGTH x` MP_TAC) >>rw[] >>
          simp[GSYM ADD1,Once EXP] >> irule (DECIDE``n<=2n /\ b<x-1 ==> 2*b+n<2*x-1``) >> rw[ADD1])


val finite_bool_list_lt_n = Q.store_thm("finite_bool_list_lt_n",
`FINITE {(s:bool list) | LENGTH s < n}`,
Induct_on`n` >> simp[finite_bool_list_n] >>
`FINITE {(s:bool list)|LENGTH s = n}` by fs[finite_bool_list_n] >>
`FINITE ({(s:bool list) | LENGTH s < n \/ LENGTH s = n}) ` by simp[FINITE_UNION,GSPEC_OR] >>
`{(s:bool list) | LENGTH s < SUC n} = {s | LENGTH s < n \/ LENGTH s = n}` by rw[EXTENSION] >>fs[])

Definition on2bl_def:
  on2bl x = OPTION_MAP n2bl x
End

Theorem on2bl_SOME:
  on2bl x = SOME y <=> (∃z. x = SOME z ∧ y = n2bl z)
Proof
 simp[on2bl_def]
QED

Definition nblconcat_def:
  nblconcat a b = a + b * 2 ** (LENGTH (n2bl a))
End

Theorem nblconcat_correct[simp]:
  nblconcat (bl2n a) (bl2n b) = bl2n (a++b)
Proof
  fs[nblconcat_def,bl2n_append]
QED

Definition pr_log2_def:
  pr_log2 = WFM (λf n. if n<=1 then 1 else 1+(f (n DIV 2)) )
End


Theorem pr_log2_thm[compute]:
  pr_log2 [i] = if i <= 1 then 1 else 1 + pr_log2 [i DIV 2]
Proof
  fs[pr_log2_def,Once prnlistTheory.WFM_correct]
QED

Definition pr_ell:
  pr_ell = WFM (λf n. if n=0 then 0
                      else if EVEN n then 1 + f ((n-2) DIV 2)
                           else 1 + f ((n-1) DIV 2) )
End

Theorem pr_ell_thm:
  pr_ell [n] = if n=0 then 0
               else if EVEN n then 1 + pr_ell [(n-2) DIV 2]
                    else 1 + pr_ell [(n-1) DIV 2]
Proof
  fs[pr_ell,Once prnlistTheory.WFM_correct] >> rw[] >> intLib.ARITH_TAC
QED




Theorem primrec_ell:
  primrec (pr1 ℓ) 1
Proof
  irule primrec_pr1 >> qexists_tac‘pr_ell’ >> rw[]
  >- (fs[pr_ell] >> irule prnlistTheory.primrec_WFM >>
      rw[prnlistTheory.restr_def,DIV_LESS_EQ] >>
      ‘∀n. (n-1) DIV 2 <= n’ by (intLib.ARITH_TAC) >> simp[] >> irule primrec_pr2 >> simp[] >>
      qexists_tac‘pr_cond (Cn pr_mod [proj 0; K 2])
                          (Cn succ [Cn (pr2 nel) [Cn (pr_div) [Cn (pr2 $-) [proj 0;K 1]; K 2];proj 1]])
                          (Cn succ [Cn (pr2 nel) [Cn (pr_div) [proj 0; K 2];proj 1]])’ >> rw[]
      >- (irule primrec_pr_cond >> rw[] >> rpt (irule primrec_Cn >> simp[primrec_rules] ) ) >>
      rw[pr_cond_def] >- (‘m MOD 2 = 1’ suffices_by simp[] >> fs[EVEN_ADD,MOD_2]) >>
      ‘m MOD 2 = 0’ suffices_by simp[] >> fs[EVEN_ADD,MOD_2]  ) >>

  completeInduct_on‘n’ >> simp[Once pr_ell_thm,Once num_to_bool_list_def] >>  rw[ADD1]>>
  first_x_assum irule >> intLib.ARITH_TAC
QED


Theorem pair_11[simp]:
  pair a b = pair c d <=> a=c ∧ b=d
Proof
  rw[EQ_IMP_THM,pair_def,bar_def] >>
  ‘LENGTH a = LENGTH c ∧ a++b = c++d’ by
    (‘Tpow (LENGTH a) ++ [F] ++ (a ++ b) = Tpow (LENGTH c) ++ [F] ++ (c ++ d)’
       by metis_tac[APPEND_ASSOC] >> metis_tac[Tpow_Fapp_eq]) >>
  ‘DROP (LENGTH a) (a++b) = DROP (LENGTH c) (c++d)’ by fs[] >>
  ‘TAKE (LENGTH a) (a++b) = TAKE (LENGTH c) (c++d)’ by fs[] >>
  fs[rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem pair_LENGTH[simp]:
  LENGTH (pair a b) = 2*LENGTH a + 1 + LENGTH b
Proof
  simp[pair_def]
QED

Theorem Tpow_11[simp]:
  Tpow n = Tpow m ⇔ n = m
Proof
  simp[Tpow_def, EQ_IMP_THM, LIST_EQ_REWRITE]
QED


Theorem bar_prefix_append[simp]:
  bar x ≼ bar y ++ l ⇔ x = y
Proof
  simp[bar_def, EQ_IMP_THM, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  rename [‘_ ++ l = _ ++ m’] >>
  ‘y ++ l = x ++ m’  by metis_tac[Tpow_Fapp_eq, APPEND_ASSOC, APPEND_11] >>
  full_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND_11] >> fs[] >>
  ‘LENGTH l = LENGTH m’ by (pop_assum (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[])>>
  metis_tac[APPEND_LENGTH_EQ]
QED

Theorem Tpow_0[simp]:
  Tpow 0 = []
Proof
  fs[Tpow_def]
QED

Theorem pair_nil[simp]:
  pair [] x = F::x
Proof
  fs[pair_def,bar_def]
QED

Definition subndiv2_def:
  subndiv2 n = recCn (recCn (SOME o pr_div)
                            [SOME o proj 0;K (SOME 2)])
                     [recCn (SOME o (pr2 $-)) [SOME o proj 0;K (SOME n)]]
End

Theorem subndiv2_rec[simp]:
  recfn (subndiv2 n) 1
Proof
  simp[subndiv2_def] >> rpt (irule recfnCn >> rw[]) >>
  irule primrec_recfn >> fs[primrec_rules]
QED

Theorem subndiv2_correct[simp]:
  subndiv2 n [m] = SOME ((m-n) DIV 2)
Proof
  fs[subndiv2_def, recursivefnsTheory.recCn_def]
QED

Definition blsnd_def:
  blsnd l = let l' = dropWhile ((=) T) l; sz = LENGTH l - LENGTH l'; in DROP (sz+1) l'
End

Theorem dropWhile_Tpow:
  dropWhile ((=) T) (Tpow n ++ [F] ++ a ++ b) = [F]++a++b
Proof
  Induct_on‘n’ >> fs[tpow_suc]
QED

Theorem blsnd_pair[simp]:
  blsnd (pair a b) = b
Proof
  fs[blsnd_def,pair_def,bar_def,dropWhile_Tpow] >>
  qmatch_abbrev_tac‘DROP m _ = _’ >>
  ‘m = LENGTH a’ suffices_by fs[rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[Abbr‘m’]
QED

Definition nblsnd0_def:
  nblsnd0 x = if EVEN x ∧ x<>0 then let (nr) = nblsnd0 ((x-2) DIV 2) in
                ((nfst nr)+1) *, (nsnd nr)
              else 0 *, x
Termination
WF_REL_TAC‘$<’ >>rw[DIV_LT_X]
End

Theorem bl2n_eq0[simp]:
  bl2n x = 0 <=> x = []
Proof
  Cases_on‘x’ >> simp[bool_list_to_num_def] >> rw[]
QED

Theorem nblsnd0_correct[simp]:
  nblsnd0 (bl2n (Tpow n ++ [F] ++ x)) = n *, bl2n ([F] ++ x)
Proof
  Induct_on‘n’
  >- fs[Once nblsnd0_def,bool_list_to_num_def,tpow_suc,EVEN_ADD,EVEN_MULT] >>
  simp[tpow_suc, bool_list_to_num_def] >>
  simp[Once nblsnd0_def, EVEN_ADD, EVEN_MULT, bool_list_to_num_def]
QED

Theorem nblsnd0_correct'[simp] =
  nblsnd0_correct |> Q.INST [‘x’ |-> ‘a ++ b’]
                  |> SIMP_RULE std_ss [APPEND_ASSOC]

Definition nblsr_def[simp]:
  nblsr x 0 = x ∧
  nblsr x (SUC n) = nblsr ((x-1) DIV 2) n
End

Theorem nblsr0[simp]:
  nblsr 0 n = 0
Proof
  Induct_on‘n’ >> simp[]
QED



Theorem DROP_n2bl:
  ∀n x. DROP n (n2bl x) = n2bl (nblsr x n)
Proof
  Induct_on‘n’ >> simp[] >> rw[] >>
  Cases_on‘x=0’  >> simp[] >>
  Cases_on‘n2bl x’ >> simp[]
  >- (pop_assum (mp_tac o Q.AP_TERM ‘bl2n’) >>
      simp[bool_list_to_num_def,Excl"bl2n_11"] ) >>
  FIRST_X_ASSUM (qspecl_then [‘bl2n t’] mp_tac) >> rw[] >>
  ‘bl2n t = (x-1) DIV 2’ suffices_by fs[] >>
  pop_assum kall_tac >> pop_assum (mp_tac o Q.AP_TERM ‘bl2n’) >>
  simp[bool_list_to_num_def,Excl"bl2n_11"] >> rw[]
QED

Definition nblsnd_def:
  nblsnd x = let nr = nblsnd0 x; n = nfst nr; r = nsnd nr; in nblsr r (n+1)
End

Theorem nblsnd_correct:
  n2bl (nblsnd (bl2n (pair a b))) = b
Proof
  fs[nblsnd_def,GSYM DROP_n2bl,pair_def,bar_def] >>
  simp[Once num_to_bool_list_def, EVEN_ADD, EVEN_MULT,
       rich_listTheory.DROP_LENGTH_APPEND]
QED


Definition pr_nblsr_def:
  pr_nblsr = Pr (proj 0)
                (Cn (pr_div) [Cn (pr2 $-) [proj 1;K 1];K 2])
End

Theorem pr_nblsr_correct:
  ∀n r. pr_nblsr [n;r] = nblsr r n
Proof
  Induct_on‘n’ >> simp[pr_nblsr_def,nblsr_def] >> rw[] >>
  ‘ (Pr (proj 0) (Cn pr_div [Cn (pr2 $-) [proj 1; K 1]; K 2]) [n; r] − 1) DIV
        2 = pr_nblsr [n; (r − 1) DIV 2]’ suffices_by fs[] >> pop_assum kall_tac >>
  rw[pr_nblsr_def] >> Induct_on‘n’ >> simp[]
QED

Theorem primrec_pr_nblsr:
  primrec (pr_nblsr) 2
Proof
  simp[pr_nblsr_def,primrec_rules]
QED

Theorem recfn_pr_nblsr:
  recfn (SOME o pr_nblsr) 2
Proof
  irule primrec_recfn >> simp[pr_nblsr_def,primrec_rules]
QED





Definition pr_nblsnd0_def:
  pr_nblsnd0 =
  WFM (λf n. if (EVEN n ∧ n<>0) then (nfst (f ((n-2) DIV 2)) + 1) *, (nsnd (f ((n-2) DIV 2)))
             else 0 *, n)
End

Theorem n_sub2_div2:
  ¬((n-2) DIV 2 < n) ==> n=0
Proof
  rw[] >> ‘n <= (n-2) DIV 2’ by fs[] >> ‘2*n <= 2* ((n-2) DIV 2)’ by fs[] >>
  ‘2*n <= n-2’ by fs[X_LE_DIV] >> Cases_on‘n=0’ >> simp[]
QED

Theorem pr_nblsnd0_correct:
  pr_nblsnd0 [n] = (pr1 nblsnd0) [n]
Proof
  completeInduct_on‘n’ >>
  simp[Once pr_nblsnd0_def,Once nblsnd0_def,Once prnlistTheory.WFM_correct] >>
  rw[]
  >- (qmatch_abbrev_tac‘nfst a = nfst b’ >> ‘a=b’ suffices_by fs[] >>
      simp[Abbr‘a’,Abbr‘b’] >>
      ‘pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]’ by fs[] >> fs[] >>
      fs[Once pr_nblsnd0_def])
  >- (qmatch_abbrev_tac‘nsnd a = nsnd b’ >> ‘a=b’ suffices_by fs[] >>
      simp[Abbr‘a’,Abbr‘b’] >>
      ‘pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]’ by fs[] >> fs[] >>
      fs[Once pr_nblsnd0_def]) >>
  metis_tac[n_sub2_div2]
QED



Definition pr_pr_nblsnd0:
pr_pr_nblsnd0 = pr_cond (Cn pr_eq
                          [Cn pr_mod
                              [Cn succ
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair)
                          [Cn succ
                              [Cn (pr1 nfst)
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd)
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair)
                          [zerof;
                           Cn succ
                              [proj 0] ] )
End

Theorem primrec_restr_lem:
  primrec (λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) 3
Proof
  ‘(λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) = pr_cond (Cn pr_le [proj 2;proj 0]) (Cn (pr2 nel) [proj 2;proj 1]) (zerof)’ by (fs[FUN_EQ_THM] >> rw[prnlistTheory.restr_def]) >> rw[] >>
  irule primrec_pr_cond >> rw[primrec_rules]
QED

Theorem primrec_pr_nblsnd0:
  primrec pr_nblsnd0 1
Proof
  fs[pr_nblsnd0_def] >> irule prnlistTheory.primrec_WFM >> irule primrec_pr2 >> fs[] >>
  qexists_tac‘pr_cond (Cn pr_eq
                          [Cn pr_mod
                              [Cn succ
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair)
                          [Cn succ
                              [Cn (pr1 nfst)
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) )
                                       [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd)
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) )
                                  [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair)
                          [zerof;
                           Cn succ
                              [proj 0] ] )’ >> rw[]
  >- (irule primrec_pr_cond >> rw[primrec_rules] >> rpt (irule unary_recfnsTheory.primrec_Cn >>
      rw[primrec_rules]) >> fs[primrec_restr_lem] )
  >- (‘¬EVEN (SUC m)’ by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
  >- (‘EVEN (SUC m)’ by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
QED

Definition pr_nblsnd_def:
  pr_nblsnd = Cn pr_nblsr
                 [Cn succ [Cn (pr1 nfst)
                              [Cn pr_nblsnd0
                                  [proj 0]]];
                  Cn (pr1 nsnd)
                     [Cn pr_nblsnd0
                         [proj 0] ] ]
End

Theorem pr_nblsnd_correct:
  pr_nblsnd [n] = (pr1 nblsnd) [n]
Proof
  fs[pr_nblsnd_def,nblsnd_def] >>
  ‘nsnd (pr_nblsnd0 [n]) = nsnd (nblsnd0 n)’ by simp[pr_nblsnd0_correct] >>
  ‘SUC (nfst (pr_nblsnd0 [n])) = nfst (nblsnd0 n) + 1’ by simp[pr_nblsnd0_correct] >>
  simp[pr_nblsr_correct,Excl"nblsr_def"]
QED

Theorem primrec_nblsnd:
  primrec pr_nblsnd 1
Proof
  simp[pr_nblsnd_def] >>
  rpt (irule unary_recfnsTheory.primrec_Cn >>
       rw[primrec_rules,primrec_pr_nblsr,primrec_pr_nblsnd0])
QED

Theorem recfn_nblsnd:
  recfn (SOME o (pr1 nblsnd)) 1
Proof
  irule primrec_recfn >> irule primrecfnsTheory.primrec_pr1 >> qexists_tac‘pr_nblsnd’ >> rw[primrec_nblsnd,pr_nblsnd_correct]
QED

Theorem nblsnd_index:
  ∃i. ∀x. Phi i x = (SOME o (pr1 nblsnd)) [x]
Proof
  assume_tac recfn_nblsnd >> drule recfns_in_Phi >> rw[] >>
  qexists_tac‘i’ >> rw[] >>
  first_x_assum (qspec_then ‘[x]’ mp_tac) >> rw[]
QED

Theorem nblsnd_correct2[simp] =
  nblsnd_correct |> AP_TERM“bl2n” |> SIMP_RULE (srw_ss()) [Excl"bl2n_11"]


Definition nblft_def:
  nblft x 0 = 0n ∧
  nblft x (SUC n) = if x=0 then 0
                    else (if EVEN x then (2 + 2* (nblft ((x-2) DIV 2) n) )
                          else (1 + 2*(nblft ((x-1) DIV 2) n)))
End

Theorem nblft_zero[simp]:
  nblft 0 x = 0
Proof
  Induct_on‘x’ >> fs[nblft_def]
QED

Theorem n2bl_zero[simp]:
  n2bl 0 = []
Proof
  simp[Once num_to_bool_list_def]
QED


Theorem TAKE_n2bl:
  ∀n x. TAKE n (n2bl x) = n2bl (nblft x n)
Proof
  Induct_on‘n’ >> simp[] >> rw[]  >>
  simp[nblft_def] >>rw[] >> simp[Once num_to_bool_list_def] >> rw[]
QED

Definition nblfst_def:
  nblfst x = (let nr = nblsnd0 x;n=nfst nr;r = nsnd nr in nblft (nblsr r (1)) n)
End

Theorem DROP_bl2n:
  ∀x n. DROP n x = n2bl (nblsr (bl2n x) n)
Proof
  rw[] >>
  ‘DROP n (n2bl (bl2n x)) = n2bl (nblsr (bl2n (n2bl (bl2n x))) n)’ suffices_by
   (rw[] >> fs[bool_num_inv]) >>
  metis_tac[DROP_n2bl,bool_num_inv]
QED

Theorem recfn_rec2_Phi[simp]:
  recfn (rec2 Phi) 2
Proof
  mp_tac prtermTheory.recfn_recPhi >> rw[Excl"recfn_recPhi"]
QED

Theorem nblfst_correct[simp]:
  nblfst (bl2n (pair a b)) = bl2n a
Proof
  ‘n2bl (nblfst (bl2n (pair a b))) = a’ suffices_by
    (rw[] >> ‘bl2n (n2bl (nblfst (bl2n (pair a b)))) = bl2n a’ by fs[] >>
     metis_tac[bool_num_inv]) >>
  fs[nblfst_def,nblsnd_def,GSYM TAKE_n2bl,pair_def,bar_def,
     theorem "nblsr_compute", rich_listTheory.TAKE_LENGTH_APPEND]
QED

Definition lam_nblft_def:
  lam_nblft = LAM "x" (
    LAM "y" (
      VAR "y"
       @@ (K @@ church 0)
       @@ (LAM "r" (
             LAM "x'" (
               cis_zero @@ VAR "x'"
                        @@ church 0
                        @@ (cis_zero
                             @@ (cmod @@ VAR "x'" @@ church 2)
                             @@ (cplus @@ church 2
                                       @@ (cmult @@ church 2
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'"
                                                                                 @@ church 2)
                                                                      @@ church 2) )  ) )
                             @@ (cplus @@ church 1
                                       @@ (cmult @@ church 2
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'"
                                                                                 @@ church 1)
                                                                      @@ church 2) )  ) )  ) )))
       @@ VAR "x"
    )
  )
End

Theorem FV_lam_nblft:
  FV lam_nblft = {}
Proof
  simp[lam_nblft_def,EXTENSION] >> metis_tac[]
QED

Theorem lam_nblft_equiv = brackabs.brackabs_equiv [] lam_nblft_def

Theorem lam_nblft_behaviour:
   ∀x y. lam_nblft @@ church x @@ church y == church (nblft x y)
Proof
  Induct_on‘y’ >> simp_tac (bsrw_ss()) [lam_nblft_equiv,nblft_def] >> rw[] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >> fs[EVEN_MOD2] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >>
  full_simp_tac (bsrw_ss()) [lam_nblft_equiv] >> simp[]
QED

Theorem lam_nblft_phi:
  Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) (m *, n) =
  SOME (nblft m n)
Proof
  simp[Phi_def] >>
  simp_tac (bsrw_ss()) [lam_nblft_behaviour,normal_orderTheory.bnf_bnf_of]
QED

Theorem nblft_phiii:
  ∀z1 z2. rec2 (λx y. SOME (nblft x y)) [z1;z2] =
  recCn
    (recCn
       recPhi
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)] [z1;z2]
Proof
  rpt strip_tac >> simp[Excl"fromTerm_def",recPhi_correct,recCn_def,lam_nblft_phi ]
QED

Theorem nblft_phi_lem:
rec2 (λx y. SOME (nblft x y)) =
  recCn
    (recCn
       recPhi
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)]
Proof
  rw[FUN_EQ_THM,Excl"fromTerm_def"] >> Cases_on‘x’ >> rw[Excl"fromTerm_def"]
  >-(simp[recCn_def,Excl"fromTerm_def"] >> ‘SOME 0 =
     Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd))) (0 *, 0)’
       suffices_by simp[Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >>
  Cases_on‘t’ >> rw[Excl"fromTerm_def"]
  >-(simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >>
  simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]
QED

Theorem recfn_some_num:
  recfn (λx. SOME (a:num)) 1
Proof
  ‘(λ(x:num list). SOME a) = K (SOME a)’ by (simp[FUN_EQ_THM,combinTheory.K_THM]) >>
  ‘recfn (K (SOME a)) 1’ suffices_by simp[] >> simp[recfn_K]
QED

Theorem recfn_nblfst:
  recfn (rec1 (SOME o nblfst)) 1
Proof
  irule recfn_rec1 >> fs[nblfst_def] >>
  qexists_tac‘recCn (rec2 (λx y. SOME (nblft x y) )) [SOME o Cn pr_nblsr [K 1;Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 0]] ];
                    SOME o Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 0]] ]’ >> rw[]
  >- (irule recfnCn >> rw[recfn_rules]
      >- (irule primrec_recfn >>
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]) )
      >- (irule primrec_recfn >>
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]))
      >- (simp[nblft_phi_lem,Excl"fromTerm_def"] >> irule recfnCn >>
          rw[recfn_rules,Excl"fromTerm_def"]
          >- (irule primrec_recfn >> simp[primrec_npair]) >> irule recfnCn >>
         rw[recfn_rules,Excl"fromTerm_def"] >> simp[recfn_some_num] )  )
  >- (simp[recCn_def] >>  simp[pr_nblsr_correct,Excl"nblsr_def",ADD1,pr_nblsnd0_correct])
QED

Theorem unary_rec_fns_phi:
  recfn f 1 ==> ∃i. ∀x. Phi i x = f [x]
Proof
  rw[] >> drule_then strip_assume_tac recfns_in_Phi >> qexists_tac‘i’ >> rw[] >>
  ‘Phi i (fold [x]) = f [x]’ by fs[] >> fs[unary_recfnsTheory.fold_def]
QED

Theorem binary_rec_fns_phi:
  recfn f 2 ⇒ ∃i. ∀x y. Phi i (x ⊗ y) = f [x;y]
Proof
  rw[] >> drule_then strip_assume_tac recfns_in_Phi >> qexists_tac‘i’ >> rw[] >>
  pop_assum (simp o single o GSYM)
QED

val nblfst_i_def = new_specification(
  "nblfst_i_def", ["nblfst_i"],
  MATCH_MP unary_rec_fns_phi recfn_nblfst
);

Theorem nblfst_bar[simp]:
  nblfst (bl2n (bar x)) = bl2n x
Proof
  assume_tac (GEN_ALL nblfst_correct) >>
  full_simp_tac bool_ss [pair_def] >>
  metis_tac [APPEND_NIL]
QED

Definition checkbar_def:
  checkbar =
  minimise (λx. if proj 0 x = nblfst (proj 1 x) ∧
                   nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
                then
                  SOME 0
                else SOME 1)
End

Theorem EXISTS_bar[simp]:
  EXISTS ($~ o $= T) (bar x)
Proof
  simp[bar_def]
QED

Theorem checkbar_correct:
  checkbar [bl2n (pair a b)] = if b = [] then SOME (bl2n a) else NONE
Proof
  reverse (rw[checkbar_def, minimise_thm] >>
           DEEP_INTRO_TAC optionTheory.some_intro >> rw[pair_def])
  >- (fs[bar_def, ADD1] >> Cases_on ‘b’ >> fs[]) >>
  qexists_tac‘bl2n a’ >> rw[] >>
  fs[bar_def, ADD1]
QED

Theorem checkbar_correct'[simp] =
  checkbar_correct |> Q.INST [‘b’ |-> ‘[]’] |> SIMP_RULE (srw_ss()) [pair_def]

Definition recfn_cond_def:
  recfn_cond P f g = recCn
        (recCn (SOME o pr2 $+)
           [recCn (SOME o pr2 $* ) [SOME o proj 0; SOME o proj 1];
            recCn (SOME o pr2 $* ) [recCn (SOME o pr2 $-) [SOME o K 1; SOME o proj 0]; SOME o proj 2]]) [P; f; g]
End

Theorem recfn_recfn_cond:
  recfn P n ∧ recfn f n ∧ recfn g n ⇒ recfn (recfn_cond P f g) n
Proof
  rw[recfn_cond_def,GSYM (CONJUNCT2 combinTheory.K_o_THM),Excl"K_o_THM"] >> rpt (irule recfnCn >> rw[recfn_rules,GSYM (CONJUNCT2 combinTheory.K_o_THM),Excl"K_o_THM"]) >> irule primrec_recfn >> simp[]
QED

Theorem recfn_checkbar_lem1:
  recfn (λx. if proj 0 x = nblfst (proj 1 x) ∧
                nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
             then
                SOME 0
             else SOME 1) 2
Proof
  ‘(λx. if proj 0 x = nblfst (proj 1 x) ∧
                nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
        then SOME 0n
        else SOME 1) =
   recfn_cond (
     recCn (SOME o pr_eq) [
       SOME o proj 0;
       recCn (rec1 (SOME o nblfst)) [SOME o proj 1]
     ]
   ) (
     SOME o pr_cond (
       Cn pr_eq [
         Cn succ [Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 1]]];
         Cn (pr1 ℓ) [Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 1]]]
       ]
     ) (K 0) (K 1)
   )
   (K (SOME 1))’
     by (rw[FUN_EQ_THM, recfn_cond_def,recCn_def, pr_nblsnd_correct] >>
         rw[] >> fs[ADD1, pr_nblsnd0_correct] >>
         Cases_on ‘proj 0 x = nblfst (proj 1 x)’ >> simp[]) >>
  rw[] >>
  irule recfn_recfn_cond >> rw[]
  >- (irule recfnCn >> rw[recfn_rules, recfnCn, recfn_nblfst, primrec_recfn])
  >- (irule primrec_recfn >>
      rpt ((irule primrec_Cn ORELSE irule primrec_pr_cond) >>
           rw[primrec_rules, primrec_nblsnd, primrec_pr_nblsnd0,primrec_ell]))>>
  ‘(K (SOME 1) : num list -> num option) = SOME o K 1’ by simp[] >>
  pop_assum SUBST1_TAC >> irule primrec_recfn >> simp[]
QED

Theorem recfn_checkbar:
  recfn checkbar 1
Proof
 fs[checkbar_def] >> irule (last (CONJUNCTS recfn_rules)) >> rw[] >>
 simp[recfn_checkbar_lem1]
QED

val checkbar_i_def =  new_specification (
  "checkbar_i_def",["checkbar_i"],
  MATCH_MP unary_rec_fns_phi recfn_checkbar
);

Theorem bl2n_onto:
  !x. ?y. x = bl2n y
Proof
  metis_tac[bool_num_inv]
QED

Theorem nblsnd0_Tpow[simp]:
  nblsnd0 (bl2n (Tpow n)) = n ⊗ 0
Proof
  Induct_on ‘n’ >>
  simp[Once nblsnd0_def, tpow_suc, bool_list_to_num_def, EVEN_MULT, EVEN_ADD]
QED

Theorem checkbar_EQ_NONE[simp]:
  checkbar [x] = NONE ⇔ ∀y. x ≠ bl2n (bar y)
Proof
  rw[checkbar_def, minimise_thm] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[]
  >- (qspec_then ‘x’ strip_assume_tac bl2n_onto >> rw[] >> fs[] >>
      rename [‘bl2n bl’] >>
      Cases_on ‘MEM F bl’
      >- (fs[Once MEM_SPLIT_APPEND_first] >>
          ‘∃n. pfx = Tpow n’
            by (simp[Tpow_def] >>
                qexists_tac‘LENGTH pfx’ >> rw[LIST_EQ_REWRITE] >>
                CCONTR_TAC >> ‘EL x pfx = F’ by simp[] >>
                Q.UNDISCH_THEN ‘~MEM F pfx’ MP_TAC >> simp[MEM_EL] >>
                metis_tac[]) >>
          rw[] >> fs[nblsnd0_correct, ADD1] >>
          simp[bar_def]) >>
      ‘∃n. bl = Tpow n’
         by (simp[Tpow_def] >>
             qexists_tac‘LENGTH bl’ >> rw[LIST_EQ_REWRITE] >>
             CCONTR_TAC >> ‘EL x bl = F’ by simp[] >>
             Q.UNDISCH_THEN ‘~MEM F bl’ MP_TAC >> simp[MEM_EL] >>
             metis_tac[]) >>
      rw[] >> fs[]) >>
  fs[AllCaseEqs()] >>
  strip_tac >> rw[] >> fs[bar_def, nblsnd0_correct] >> rfs[]
QED

val nblsnd_i_def =  new_specification (
  "nblsnd_i_def",["nblsnd_i"],
  MATCH_MP unary_rec_fns_phi recfn_nblsnd
);

Theorem bar_decomp:
  (∃n x. p1 = bl2n (Tpow n ++ [F] ++ x)) ∨ (∃m. p1 = bl2n (Tpow m) )
Proof
  Cases_on ‘MEM F (n2bl p1)’
      >- (fs[Once MEM_SPLIT_APPEND_first] >>
          ‘∃n. pfx = Tpow n’
            by (simp[Tpow_def] >>
                qexists_tac‘LENGTH pfx’ >> rw[LIST_EQ_REWRITE] >>
                CCONTR_TAC >> ‘EL x pfx = F’ by simp[] >>
                Q.UNDISCH_THEN ‘~MEM F pfx’ MP_TAC >> simp[MEM_EL] >>
                metis_tac[]) >>
          Cases_on‘(∃n x. p1 = bl2n (Tpow n ++ [F] ++ x))’ >> fs[] >>
          ‘p1 <> (bl2n (Tpow n ++ [F] ++ sfx))’ by fs[] >>
          ‘bl2n (n2bl p1) = bl2n (Tpow n ++ [F] ++ sfx)’ by fs[] >> metis_tac[bool_num_inv] ) >>
      ‘∃n. (n2bl p1) = Tpow n’
         by (simp[Tpow_def] >>
             qexists_tac‘LENGTH (n2bl p1)’ >> rw[LIST_EQ_REWRITE] >>
             CCONTR_TAC >> ‘EL x (n2bl p1) = F’ by simp[] >>
             Q.UNDISCH_THEN ‘~MEM F (n2bl p1)’ MP_TAC >> simp[MEM_EL] >>
             metis_tac[]) >> Cases_on‘∃m. p1 = bl2n (Tpow m)’ >> fs[] >>
      ‘bl2n (n2bl p1) = bl2n (Tpow n)’ by fs[] >> metis_tac[bool_num_inv]
QED

Theorem n2bl_inj[simp]:
  n2bl x = n2bl y <=> x=y
Proof
  metis_tac[bool_num_inv]
QED

Theorem n2bl_eq_CONS:
  n2bl n = h::t <=> ∃m. n = 2 * m + (if h then 2 else 1) ∧ n2bl m = t
Proof
  Cases_on‘n’ >> simp[Once num_to_bool_list_def,AllCaseEqs ()] >> rw[EQ_IMP_THM] >>simp[] >>
  pop_assum MP_TAC >> intLib.ARITH_TAC
QED

Theorem nblsr_correct' = GSYM DROP_bl2n |> SPEC_ALL |> Q.AP_TERM ‘bl2n’ |> SIMP_RULE (srw_ss()) [Excl"bl2n_11"]


Theorem nblsnd_behav:
  ∀p1 x cr. nblsnd p1 = bl2n (bar x) ==>
            nblsnd (bl2n (n2bl p1 ++ cr)) = bl2n (bar x ++ cr)
Proof
  GEN_TAC >> strip_assume_tac bar_decomp >>
  rw[nblsnd_def,nblsnd0_Tpow,rich_listTheory.DROP_APPEND] >>
  fs[nblsr_def, GSYM ADD1, nblsr_correct'] >>
  ‘n <= LENGTH x’ suffices_by simp[rich_listTheory.DROP_APPEND1] >>
  CCONTR_TAC >> ‘LENGTH x < n’ by fs[] >>
  ‘DROP n x = []’ by fs[DROP_LENGTH_TOO_LONG] >>
  pop_assum SUBST_ALL_TAC >> fs[]
QED

Definition nblTpow_def:
  nblTpow = Cn (pr2 $-) [
    (λl. FUNPOW (λx. 2*x ) (Cn succ [proj 0] l) ((K 1n) l));
    K 2
  ]
End

Theorem nblTpow_compute:
  nblTpow [n] = 2**(n+1) - 2
Proof
  ‘nblTpow [n] + 2 = 2 ** (n + 1)’ suffices_by simp[] >>
  Induct_on‘n’ >> fs[nblTpow_def,FUNPOW_SUC,EXP,ADD_CLAUSES] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] >>
  ‘4n ≤ 4 * FUNPOW (λx. 2 * x) n 1’ suffices_by simp[] >>
  Induct_on‘n’ >> rw[FUNPOW_SUC]
QED

Theorem primrec_nblTpow:
  primrec nblTpow 1
Proof
  simp[nblTpow_def] >> irule primrec_Cn >> simp[] >>
  ho_match_mp_tac primrec_FUNPOW >> rw[]
  >- (irule primrec_pr1 >> qexists_tac ‘Cn (pr2 $* ) [K 2; proj 0]’ >>
      simp[primrec_rules, primrec_pr_mult])
  >- (‘(λl:num list. 1) = K 1n’ suffices_by simp[primrec_K] >> simp[FUN_EQ_THM]) >>
  ‘(λl. SUC (proj 0 l)) = Cn succ [proj 0]’ by simp[FUN_EQ_THM] >>
  simp[primrec_rules]
QED

Theorem nblTpow_correct:
  nblTpow [n] = bl2n (Tpow n)
Proof
  simp[Tpow_def,nblTpow_compute] >> Induct_on‘n’ >>
  simp[ADD_CLAUSES, EXP, GENLIST_CONS] >>
  ‘2 ≤ 2 ** (n + 1)’ by simp[X_LE_X_EXP] >>
  ‘2 ** (n + 1) = bl2n (GENLIST (K T) n) + 2’ by simp[] >> simp[]
QED

Definition checkpair_def:
  checkpair =
  minimise (λx. if proj 0 x = proj 1 x ∧
                   nfst (nblsnd0 (proj 1 x)) + 1 ≤ ℓ (nsnd (nblsnd0 (proj 1 x)))
                then
                  SOME 0
                else SOME 1)
End

Theorem checkpair_correct[simp]:
  checkpair [bl2n (pair a b)] = SOME (bl2n (pair a b))
Proof
  rw[checkpair_def, minimise_thm] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> rw[pair_def, bar_def] >>
  simp[AllCaseEqs()] >> csimp[]
QED

Theorem MEM_Tpow[simp]:
  MEM b (Tpow n) ⇔ 0 < n ∧ b
Proof
  Induct_on ‘n’ >> simp[tpow_suc, EQ_IMP_THM, DISJ_IMP_THM]
QED

Theorem checkpair_loops[simp]:
  checkpair [x] = NONE ⇔ ∀a b. x ≠ bl2n (pair a b)
Proof
  csimp[checkpair_def, minimise_thm, AllCaseEqs()] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >> conj_tac >>
  qspec_then ‘x’ STRUCT_CASES_TAC (bar_decomp |> GEN_ALL) >>
  simp[pair_def, bar_def]
  >- (strip_tac >> rename [‘n + 1 ≤ SUC (LENGTH l)’] >>
      map_every qexists_tac [‘TAKE n l’, ‘DROP n l’] >> simp[])
  >- (rpt strip_tac >>
      rename [‘Tpow n ++ [F] ++ l = Tpow (LENGTH a) ++ [F] ++ a ++ b’] >>
      ‘n = LENGTH a ∧ l = a ++ b’ by metis_tac[Tpow_Fapp_eq, APPEND_ASSOC] >>
      rw[] >> fs[]) >>
  rpt strip_tac >> pop_assum (mp_tac o Q.AP_TERM ‘MEM F’) >> simp[]
QED

Theorem pr_eq_predicate:
  pr_predicate pr_eq
Proof
  simp[pr_predicate_def, pr_eq_def, cflip_def] >>
  Cases >> simp[] >> rename [‘pr_le (h::t)’] >> Cases_on ‘t’ >> simp[]
QED

Theorem pr_ell_correct[simp]:
  pr_ell [n] = ℓ n
Proof
  completeInduct_on ‘n’ >>
  simp[Once pr_ell_thm, Once num_to_bool_list_def] >>
  rw[ADD1] >> first_x_assum irule >> intLib.ARITH_TAC
QED

Theorem recfn_checkpair[simp]:
  recfn checkpair 1
Proof
  simp[checkpair_def] >> irule (last (CONJUNCTS recfn_rules)) >> simp[] >>
  qmatch_abbrev_tac ‘recfn f 2’ >>
  ‘f =
   SOME o (
     pr_cond pr_eq (
       pr_cond (
         Cn pr_le [
           Cn (pr2 $+) [Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 1]]; K 1];
           Cn (pr1 ℓ) [Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 1]]]
         ]
       ) (K 0) (K 1)
     ) (K 1))’
     by (simp[FUN_EQ_THM,pr_cond_thm,Abbr‘f’, pr_eq_predicate, pr_nblsnd0_correct]>>
         rw[] >> fs[] >> rename [‘pr_eq x’] >> Cases_on ‘x’ >>
         fs[pr_eq_def, cflip_def] >>
         rename [‘pr_le (_ :: t)’] >> Cases_on ‘t’ >> fs[]) >>
  pop_assum SUBST1_TAC >> irule primrec_recfn >>
  rpt ((irule primrec_pr_cond ORELSE irule primrec_Cn) >>
       rw[primrec_rules, primrec_pr_nblsnd0, primrec_ell])
QED

Theorem checkpair_i_def[simp,allow_rebind] = new_specification(
  "checkpair_i_def", ["checkpair_i"],
  MATCH_MP unary_rec_fns_phi recfn_checkpair)

val _ = export_theory();
