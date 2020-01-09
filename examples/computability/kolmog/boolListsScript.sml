open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pred_setTheory

val _ = new_theory "boolLists";

val _ = ParseExtras.tight_equality()

val prefix_def = Define`prefix a b <=> a≼b ∧ a <> b`

val _ = set_mapped_fixity{fixity = Infix(NONASSOC,450),term_name = "prefix",tok="≺"}

val prefix_lem1 = Q.store_thm("prefix_lem1",
`0<LENGTH b  ==> (a++b = c ==> a ≺ c )`,
simp[prefix_def,rich_listTheory.IS_PREFIX_APPEND] >> rw[] >- (qexists_tac`b` >> simp[]) >> rw[]>>
metis_tac[listTheory.NOT_NIL_EQ_LENGTH_NOT_0]  )

val prefix_length_lt = Q.store_thm("prefix_length_lt",
`a ≺ b ==> LENGTH a < LENGTH b`,
rw[prefix_def] >> `LENGTH a <= LENGTH b` by fs[rich_listTheory.IS_PREFIX_LENGTH] >>
Cases_on`LENGTH a = LENGTH b` >> simp[] >> metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI])

val prefix_append= Q.store_thm("prefix_append",
`a ≺ b <=> ?s. b=a++s /\ s<>[]`,
simp[prefix_def] >> rw[rich_listTheory.IS_PREFIX_APPEND,EQ_IMP_THM] >> metis_tac[APPEND_NIL,APPEND_EQ_SELF])

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
                   if n=0 then []
                   else if EVEN n then T::num_to_bool_list((n-2) DIV 2)
                   else F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC`$<` >> rw[]>>
irule LESS_EQ_LESS_TRANS >> qexists_tac`n DIV 2` >> rw[DIV_LE_MONOTONE,DIV_LESS])

val bool_list_to_num_def = Define`
  (bool_list_to_num [] = 0n) ∧
  (bool_list_to_num (h::t) = (if h then 2 else 1)+2 * (bool_list_to_num t))`

val num_bool_inv = Q.store_thm("num_bool_inv[simp]",
  `num_to_bool_list (bool_list_to_num l) = l`,
  Induct_on `l` >> simp[Once num_to_bool_list_def,bool_list_to_num_def] >> Cases_on `h` >>
  simp[EVEN_ADD,EVEN_MULT] >> metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``] )

val bool_num_inv = Q.store_thm("bool_num_inv[simp]",
`∀n. bool_list_to_num (num_to_bool_list n) = n`,
ho_match_mp_tac (theorem"num_to_bool_list_ind") >> rpt strip_tac >>
  rw[Once num_to_bool_list_def,bool_list_to_num_def]
  >- (MP_TAC(Q.INST[`n`|->`2`,`q`|->`1`,`m`|->`n`]DIV_SUB)>>fs[]>>impl_keep_tac
      >-(fs[EVEN_EXISTS])>>simp[LEFT_SUB_DISTRIB]>>Q.SPEC_THEN`2`MP_TAC DIVISION>>fs[]>>
      disch_then(Q.SPEC_THEN`n`(MP_TAC o SYM) ) >> fs[EVEN_MOD2] )
  >- (fs[GSYM ODD_EVEN,ODD_EXISTS] >>metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``,ADD1] ) )

Overload "ℓ" = ``λp. LENGTH (num_to_bool_list p) ``

Overload bl2n = ``bool_list_to_num``
Overload n2bl = ``num_to_bool_list``

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


val Fpow_def = Define`Fpow n = GENLIST (K F) n`



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


val _ = export_theory();

