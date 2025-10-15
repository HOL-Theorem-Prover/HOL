Theory comparison
Ancestors
  option pair string list arithmetic toto
Libs
  BasicProvers

val _ = temp_tight_equality ();
val every_case_tac = BasicProvers.EVERY_CASE_TAC;

val comparison_distinct = TypeBase.distinct_of ``:ordering``
val comparison_case_def = TypeBase.case_def_of ``:ordering``
val comparison_nchotomy = TypeBase.nchotomy_of ``:ordering``
val _ = Parse.overload_on("Less",``LESS``)
val _ = Parse.overload_on("Equal",``EQUAL``)
val _ = Parse.overload_on("Greater",``GREATER``)

Definition good_cmp_def:
good_cmp cmp <=>
  (!x. cmp x x = Equal) /\
  (!x y. cmp x y = Equal ==> cmp y x = Equal) /\
  (!x y. cmp x y = Greater <=> cmp y x = Less) /\
  (!x y z. cmp x y = Equal /\ cmp y z = Less ==> cmp x z = Less) /\
  (!x y z. cmp x y = Less /\ cmp y z = Equal ==> cmp x z = Less) /\
  (!x y z. cmp x y = Equal /\ cmp y z = Equal ==> cmp x z = Equal) /\
  (!x y z. cmp x y = Less /\ cmp y z = Less ==> cmp x z = Less)
End

Theorem good_cmp_thm:
 !cmp.
  good_cmp cmp <=>
  (!x. cmp x x = Equal) /\
  (!x y z.
    (cmp x y = Greater <=> cmp y x = Less) /\
    (cmp x y = Less /\ cmp y z = Equal ==> cmp x z = Less) /\
    (cmp x y = Less /\ cmp y z = Less ==> cmp x z = Less))
Proof
 rw [good_cmp_def] >>
 metis_tac [comparison_distinct, comparison_nchotomy]
QED

Theorem cmp_thms = LIST_CONJ [comparison_distinct, comparison_case_def, comparison_nchotomy, good_cmp_def]

val _ = overload_on ("option_cmp", ``option_compare``);
Theorem option_cmp_def =
  ternaryComparisonsTheory.option_compare_def

Definition option_cmp2_def:
  (option_cmp2 cmp NONE NONE = Equal) /\
  (option_cmp2 cmp NONE (SOME x) = Greater) /\
  (option_cmp2 cmp (SOME x) NONE = Less) /\
  (option_cmp2 cmp (SOME x) (SOME y) = cmp x y)
End

val _ = overload_on ("list_cmp", ``list_compare``)
val list_cmp_def = ternaryComparisonsTheory.list_compare_def
val list_cmp_ind = ternaryComparisonsTheory.list_compare_ind

val _ = overload_on ("pair_cmp", ``pair_compare``)
Theorem pair_cmp_def =
  PART_MATCH lhs ternaryComparisonsTheory.pair_compare_def
     ``pair_cmp c1 c2 (FST x, SND x) (FST y, SND y)``
     |> REWRITE_RULE [pairTheory.PAIR];

val _ = overload_on ("bool_cmp", ``bool_compare``)
Theorem bool_cmp_def =
  ternaryComparisonsTheory.bool_compare_def

val _ = overload_on ("num_cmp", ``num_compare``)
Theorem num_cmp_def =
  ternaryComparisonsTheory.num_compare_def

Overload char_cmp = “char_compare”
Theorem char_cmp_def = stringTheory.char_compare_def

Overload string_cmp = “string_compare”
Theorem string_cmp_def = stringTheory.string_compare_def
(* relationship to toto *)

Theorem TotOrder_imp_good_cmp:
    !cmp. TotOrd cmp ==> good_cmp cmp
Proof
  rw[TotOrd,good_cmp_thm] >> metis_tac[]
QED

val _ = temp_overload_on ("invert", ``ternaryComparisons$invert_comparison``)

Theorem TO_inv_invert:
    !c. TotOrd c ==> TO_inv c = CURRY (invert o UNCURRY c)
Proof
  simp[FUN_EQ_THM,TO_inv] >> gen_tac >> strip_tac >>
  map_every qx_gen_tac[`x`,`y`] >>
  Cases_on`c x y`>>simp[]>>
  fs[TotOrd] >> metis_tac[]
QED

Theorem option_cmp2_TO_inv:
    !c. option_cmp2 c = TO_inv (option_cmp (TO_inv c))
Proof
  simp[FUN_EQ_THM,TO_inv] >>
  gen_tac >> Cases >> Cases >>
  simp[option_cmp2_def,option_cmp_def,TO_inv]
QED

Theorem list_cmp_ListOrd:
    !c. TotOrd c ==> list_cmp c = ListOrd (TO c)
Proof
  simp[FUN_EQ_THM,PULL_FORALL] >>
  ho_match_mp_tac list_cmp_ind >>
  simp[list_cmp_def,ListOrd,TO_of_LinearOrder,
       StrongLinearOrder_of_TO,TO_apto_TO_ID,listorder] >>
  rw[] >>
  fs[GSYM TO_apto_TO_ID,TotOrd] >>
  BasicProvers.CASE_TAC >>
  metis_tac[cmp_thms]
QED

Theorem TotOrd_list_cmp:
    !c. TotOrd c ==> TotOrd (list_cmp c)
Proof
  srw_tac[][] >> imp_res_tac list_cmp_ListOrd >> simp[TO_ListOrd]
QED

Theorem pair_cmp_lexTO:
    !R V. TotOrd R /\ TotOrd V ==> pair_cmp R V = R lexTO V
Proof
  simp[FUN_EQ_THM,lexTO_thm,pair_cmp_def,pairTheory.FORALL_PROD]
QED

Theorem num_cmp_numOrd:
    num_cmp = numOrd
Proof
  simp[FUN_EQ_THM,num_cmp_def,numOrd,TO_of_LinearOrder]
QED

Theorem char_cmp_charOrd:
    char_cmp = charOrd
Proof
  simp[FUN_EQ_THM,char_cmp_def,charOrd,num_cmp_numOrd]
QED

Theorem string_cmp_stringto:
    string_cmp = apto stringto
Proof
  simp[FUN_EQ_THM,stringto] >>
  Induct >- ( Cases >> simp[aplistoto,string_cmp_def,list_cmp_def] ) >>
  gen_tac >> Cases >>
  simp[aplistoto,string_cmp_def,list_cmp_def,apcharto_thm,char_cmp_charOrd] >>
  BasicProvers.CASE_TAC >>
  simp[MATCH_MP list_cmp_ListOrd TO_charOrd,listoto,charto] >>
  rpt AP_THM_TAC >>
  match_mp_tac (GSYM TO_apto_TO_IMP) >>
  simp[TO_ListOrd]
QED

(* cmps are good *)

Theorem option_cmp_good:
 !cmp. good_cmp cmp ==> good_cmp (option_cmp cmp)
Proof
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp_def, comparison_distinct]
QED

Theorem option_cmp2_good:
 !cmp. good_cmp cmp ==> good_cmp (option_cmp2 cmp)
Proof
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp2_def, comparison_distinct]
QED

Theorem list_cmp_good:
 !cmp. good_cmp cmp ==> good_cmp (list_cmp cmp)
Proof
 simp [good_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 rpt conj_tac >>
 Induct_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [list_cmp_def] >>
 rpt strip_tac >>
 every_case_tac >>
 metis_tac [list_cmp_def, comparison_distinct, comparison_case_def, comparison_nchotomy]
QED

Theorem pair_cmp_good:
 !cmp1 cmp2. good_cmp cmp1 /\ good_cmp cmp2 ==> good_cmp (pair_cmp cmp1 cmp2)
Proof
 simp [good_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [pair_cmp_def] >>
 rpt strip_tac >>
 every_case_tac >>
 metis_tac [pair_cmp_def, comparison_distinct, comparison_case_def, comparison_nchotomy]
QED

Theorem bool_cmp_good[simp]:
 good_cmp bool_cmp
Proof
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [bool_cmp_def] >>
 every_case_tac >>
 fs []
QED

Theorem num_cmp_good[simp]:
 good_cmp num_cmp
Proof
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [num_cmp_def] >>
 every_case_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) []
QED

Theorem char_cmp_good[simp]:
 good_cmp char_cmp
Proof
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [char_cmp_def, num_cmp_def] >>
 every_case_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) []
QED

Theorem string_cmp_good[simp]:
 good_cmp string_cmp
Proof
 metis_tac [string_cmp_def, char_cmp_good, list_cmp_good]
QED

Theorem list_cmp_cong[defncong]:
  !cmp l1 l2 cmp' l1' l2'.
    l1 = l1' /\ l2 = l2' /\
    (!x x'. MEM x l1' /\ MEM x' l2' ==> cmp x x' = cmp' x x')
    ==>
    list_cmp cmp l1 l2 = list_cmp cmp' l1' l2'
Proof
 ho_match_mp_tac list_cmp_ind >>
 rw [list_cmp_def] >>
 rw [list_cmp_def] >>
 every_case_tac >>
 rw []
QED

Theorem option_cmp_cong[defncong]:
  !cmp v1 v2 cmp' v1' v2'.
    v1 = v1' /\ v2 = v2' /\
    (!x x'. v1' = SOME x /\ v2' = SOME x' ==> cmp x x' = cmp' x x') ==>
    option_cmp cmp v1 v2 = option_cmp cmp' v1' v2'
Proof
 ho_match_mp_tac ternaryComparisonsTheory.option_compare_ind >>
 rw [option_cmp_def] >>
 rw [option_cmp_def]
QED

Theorem option_cmp2_cong[defncong]:
  !cmp v1 v2 cmp' v1' v2'.
    v1 = v1' /\ v2 = v2' /\
    (!x x'. v1' = SOME x /\ v2' = SOME x' ==> cmp x x' = cmp' x x')
    ==>
    option_cmp2 cmp v1 v2 = option_cmp2 cmp' v1' v2'
Proof
  ho_match_mp_tac (fetch "-" "option_cmp2_ind") >>
  rw [option_cmp2_def] >>
  rw [option_cmp2_def]
QED

Theorem pair_cmp_cong[defncong]:
  !cmp1 cmp2 v1 v2 cmp1' cmp2' v1' v2'.
    v1 = v1' /\
    v2 = v2' /\
    (!a b c d. v1' = (a,b) /\ v2' = (c,d) ==> cmp1 a c = cmp1' a c) /\
    (!a b c d. v1' = (a,b) /\ v2' = (c,d) ==> cmp2 b d = cmp2' b d)
  ==>
    pair_cmp cmp1 cmp2 v1 v2 = pair_cmp cmp1' cmp2' v1' v2'
Proof simp [pair_cmp_def, pairTheory.FORALL_PROD]
QED

Theorem good_cmp_trans:
 !cmp. good_cmp cmp ==> transitive (\ (k,v) (k',v'). cmp k k' = Less)
Proof
 rw [relationTheory.transitive_def] >>
 Cases_on `x` >>
 Cases_on `y` >>
 Cases_on `z` >>
 fs [] >>
 metis_tac [cmp_thms]
QED

Theorem good_cmp_Less_trans:
 !cmp. good_cmp cmp ==> transitive (\k k'. cmp k k' = Less)
Proof
 rw [relationTheory.transitive_def] >>
 fs [] >>
 metis_tac [cmp_thms]
QED

Theorem good_cmp_Less_irrefl_trans:
 !cmp. good_cmp cmp ==> (irreflexive (\k k'. cmp k k' = Less) /\
    transitive (\k k'. cmp k k' = Less))
Proof
 simp [good_cmp_Less_trans, relationTheory.irreflexive_def] >>
 simp [cmp_thms]
QED

Theorem bool_cmp_antisym[simp]:
 !x y. bool_cmp x y = Equal <=> x = y
Proof
 rw [] >>
 Cases_on `x` >>
 Cases_on `y` >>
 rw [bool_cmp_def]
QED

Theorem num_cmp_antisym[simp]:
 !x y. num_cmp x y = Equal <=> x = y
Proof
 rw [num_cmp_def]
QED

Theorem char_cmp_antisym[simp]:
 !x y. char_cmp x y = Equal <=> x = y
Proof
 rw [char_cmp_def, num_cmp_antisym] >>
 rw [ORD_11]
QED

Theorem list_cmp_antisym:
 !cmp x y. (!x y. cmp x y = Equal <=> x = y) ==> (list_cmp cmp x y = Equal <=> x = y)
Proof
 ho_match_mp_tac list_cmp_ind >>
 rw [list_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]
QED

Theorem string_cmp_antisym[simp]:
 !x y. string_cmp x y = Equal <=> x = y
Proof
 metis_tac [string_cmp_def, char_cmp_antisym, list_cmp_antisym]
QED

Theorem pair_cmp_antisym:
 !cmp1 cmp2 x y.
  (!x y. cmp1 x y = Equal <=> x = y) /\
  (!x y. cmp2 x y = Equal <=> x = y)
  ==>
  (pair_cmp cmp1 cmp2 x y = Equal <=> x = y)
Proof
 Cases_on `x` >>
 Cases_on `y` >>
 rw [pair_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]
QED

Theorem option_cmp_antisym:
 !cmp x y.
  (!x y. cmp x y = Equal <=> x = y)
  ==>
  (option_cmp cmp x y = Equal <=> x = y)
Proof
 Cases_on `x` >>
 Cases_on `y` >>
 rw [option_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]
QED

Theorem option_cmp2_antisym:
 !cmp x y.
  (!x y. cmp x y = Equal <=> x = y)
  ==>
  (option_cmp2 cmp x y = Equal <=> x = y)
Proof
 Cases_on `x` >>
 Cases_on `y` >>
 rw [option_cmp2_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]
QED

Definition resp_equiv_def:
resp_equiv cmp f <=> !k1 k2 v. cmp k1 k2 = Equal ==> f k1 v = f k2 v
End

Definition resp_equiv2_def:
resp_equiv2 cmp cmp2 f <=> (!k1 k2. cmp k1 k2 = Equal ==> cmp2 (f k1) (f k2) = Equal)
End

Definition equiv_inj_def:
equiv_inj cmp cmp2 f <=> (!k1 k2. cmp2 (f k1) (f k2) = Equal ==> cmp k1 k2 = Equal)
End

Theorem antisym_resp_equiv:
 !cmp f.
  (!x y. cmp x y = Equal ==> x = y)
  ==>
  resp_equiv cmp f /\ !cmp2. good_cmp cmp2 ==> resp_equiv2 cmp cmp2 f
Proof
 rw [resp_equiv_def, resp_equiv2_def] >>
 metis_tac [cmp_thms]
QED

Theorem list_cmp_equal_list_rel:
 !cmp l1 l2.
  list_cmp cmp l1 l2 = Equal <=> LIST_REL (\x y. cmp x y = Equal) l1 l2
Proof
 Induct_on `l1` >>
 rw [] >>
 Cases_on `l2` >>
 fs [list_cmp_def] >>
 every_case_tac >>
 fs []
QED

Theorem TO_of_LinearOrder_LLEX:
    !R. irreflexive R ==> (TO_of_LinearOrder (LLEX R) = list_cmp (TO_of_LinearOrder R))
Proof
  srw_tac[][relationTheory.irreflexive_def] >>
  simp[FUN_EQ_THM] >>
  Induct >- (
    Cases >> simp[list_cmp_def,TO_of_LinearOrder] ) >>
  gen_tac >> Cases >>
  simp[list_cmp_def,TO_of_LinearOrder] >>
  pop_assum(assume_tac o GSYM) >> simp[] >>
  srw_tac[][TO_of_LinearOrder] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
QED
