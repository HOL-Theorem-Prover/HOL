open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory stringTheory listTheory arithmeticTheory;
open lcsymtacs;

val _ = new_theory "comparison";

val _ = temp_tight_equality ();
val every_case_tac = BasicProvers.EVERY_CASE_TAC;

val _ = Datatype `comparison = Less | Greater | Equal`;

val comparison_distinct = fetch "-" "comparison_distinct";
val comparison_case_def = fetch "-" "comparison_case_def";
val comparison_nchotomy = fetch "-" "comparison_nchotomy";

val good_cmp_def = Define `
good_cmp cmp ⇔
  (!x. cmp x x = Equal) ∧
  (!x y. cmp x y = Equal ⇒ cmp y x = Equal) ∧
  (!x y. cmp x y = Greater ⇔ cmp y x = Less) ∧
  (!x y z. cmp x y = Equal ∧ cmp y z = Less ⇒ cmp x z = Less) ∧
  (!x y z. cmp x y = Less ∧ cmp y z = Equal ⇒ cmp x z = Less) ∧
  (!x y z. cmp x y = Equal ∧ cmp y z = Equal ⇒ cmp x z = Equal) ∧
  (!x y z. cmp x y = Less ∧ cmp y z = Less ⇒ cmp x z = Less)`;

val good_cmp_thm = Q.store_thm ("good_cmp_thm",
`!cmp. 
  good_cmp cmp ⇔
  (!x. cmp x x = Equal) ∧
  (!x y z.
    (cmp x y = Greater ⇔ cmp y x = Less) ∧
    (cmp x y = Less ∧ cmp y z = Equal ⇒ cmp x z = Less) ∧
    (cmp x y = Less ∧ cmp y z = Less ⇒ cmp x z = Less))`,
 rw [good_cmp_def] >>
 metis_tac [comparison_distinct, comparison_nchotomy]);

val cmp_thms = save_thm ("cmp_thms", LIST_CONJ [comparison_distinct, comparison_case_def, comparison_nchotomy, good_cmp_def])

val option_cmp_def = Define `
(option_cmp cmp NONE NONE = Equal) ∧
(option_cmp cmp NONE (SOME x) = Less) ∧
(option_cmp cmp (SOME x) NONE = Greater) ∧
(option_cmp cmp (SOME x) (SOME y) = cmp x y)`;

val option_cmp2_def = Define `
(option_cmp2 cmp NONE NONE = Equal) ∧
(option_cmp2 cmp NONE (SOME x) = Greater) ∧
(option_cmp2 cmp (SOME x) NONE = Less) ∧
(option_cmp2 cmp (SOME x) (SOME y) = cmp x y)`;

val list_cmp_def = Define `
(list_cmp cmp [] [] = Equal) ∧
(list_cmp cmp [] (x::y) = Less) ∧
(list_cmp cmp (x::y) [] = Greater) ∧
(list_cmp cmp (x1::y1) (x2::y2) =
  case cmp x1 x2 of
     | Equal => list_cmp cmp y1 y2
     | Less => Less
     | Greater => Greater)`;

val list_cmp_ind = fetch "-" "list_cmp_ind";

val pair_cmp_def = Define `
pair_cmp cmp1 cmp2 x y =
  case cmp1 (FST x) (FST y)  of
     | Equal => cmp2 (SND x) (SND y)
     | Less => Less
     | Greater => Greater`;

val bool_cmp_def = Define `
(bool_cmp T T = Equal) ∧
(bool_cmp F F = Equal) ∧
(bool_cmp T F = Greater) ∧
(bool_cmp F T = Less)`;

val num_cmp_def = Define `
num_cmp n1 n2 =
  if n1 = n2 then
    Equal
  else if n1 < n2 then
    Less
  else
    Greater`;

val char_cmp_def = Define `
char_cmp c1 c2 = num_cmp (ORD c1) (ORD c2)`;

val string_cmp_def = Define `
string_cmp = list_cmp char_cmp`;

val option_cmp_good = Q.store_thm ("option_cmp_good",
`!cmp. good_cmp cmp ⇒ good_cmp (option_cmp cmp)`,
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp_def, comparison_distinct]);

val option_cmp2_good = Q.store_thm ("option_cmp2_good",
`!cmp. good_cmp cmp ⇒ good_cmp (option_cmp2 cmp)`,
 rw [good_cmp_def] >>
 Cases_on `x` >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 metis_tac [option_cmp2_def, comparison_distinct]);

val list_cmp_good = Q.store_thm ("list_cmp_good",
`!cmp. good_cmp cmp ⇒ good_cmp (list_cmp cmp)`,
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
 metis_tac [list_cmp_def, comparison_distinct, comparison_case_def, comparison_nchotomy]);

val pair_cmp_good = Q.store_thm ("pair_cmp_good",
`!cmp1 cmp2. good_cmp cmp1 ∧ good_cmp cmp2 ⇒ good_cmp (pair_cmp cmp1 cmp2)`,
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
 metis_tac [pair_cmp_def, comparison_distinct, comparison_case_def, comparison_nchotomy]);

val bool_cmp_good = Q.store_thm ("bool_cmp_good[simp]",
`good_cmp bool_cmp`,
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [bool_cmp_def] >>
 every_case_tac >>
 fs []);

val num_cmp_good = Q.store_thm ("num_cmp_good[simp]",
`good_cmp num_cmp`,
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [num_cmp_def] >>
 every_case_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val char_cmp_good = Q.store_thm ("char_cmp_good[simp]",
`good_cmp char_cmp`,
 simp [good_cmp_def] >>
 rpt conj_tac >>
 TRY (Cases_on `x`) >>
 TRY (Cases_on `y`) >>
 TRY (Cases_on `z`) >>
 REWRITE_TAC [char_cmp_def, num_cmp_def] >>
 every_case_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val string_cmp_good = Q.store_thm ("string_cmp_good[simp]",
`good_cmp string_cmp`,
 metis_tac [string_cmp_def, char_cmp_good, list_cmp_good]);

val list_cmp_cong = Q.store_thm ("list_cmp_cong",
`!cmp l1 l2 cmp' l1' l2'.
  (l1 = l1') ∧
  (l2 = l2') ∧
  (!x x'. MEM x l1' ∧ MEM x' l2' ⇒ cmp x x' = cmp' x x')
  ⇒
  list_cmp cmp l1 l2 = list_cmp cmp' l1' l2'`,
 ho_match_mp_tac list_cmp_ind >>
 rw [list_cmp_def] >>
 rw [list_cmp_def] >>
 every_case_tac >>
 rw []);

val option_cmp_cong = Q.store_thm ("option_cmp_cong",
`!cmp v1 v2 cmp' v1' v2'.
  (v1 = v1') ∧
  (v2 = v2') ∧
  (!x x'. v1' = SOME x ∧ v2' = SOME x' ⇒ cmp x x' = cmp' x x')
  ⇒
  option_cmp cmp v1 v2 = option_cmp cmp' v1' v2'`,
 ho_match_mp_tac (fetch "-" "option_cmp_ind") >>
 rw [option_cmp_def] >>
 rw [option_cmp_def]);

val option_cmp2_cong = Q.store_thm ("option_cmp2_cong",
`!cmp v1 v2 cmp' v1' v2'.
  (v1 = v1') ∧
  (v2 = v2') ∧
  (!x x'. v1' = SOME x ∧ v2' = SOME x' ⇒ cmp x x' = cmp' x x')
  ⇒
  option_cmp2 cmp v1 v2 = option_cmp2 cmp' v1' v2'`,
 ho_match_mp_tac (fetch "-" "option_cmp2_ind") >>
 rw [option_cmp2_def] >>
 rw [option_cmp2_def]);

val pair_cmp_cong = Q.store_thm ("pair_cmp_cong",
`!cmp1 cmp2 v1 v2 cmp1' cmp2' v1' v2'.
  (v1 = v1') ∧
  (v2 = v2') ∧
  (!a b c d. v1' = (a,b) ∧ v2' = (c,d) ⇒ cmp1 a c = cmp1' a c) ∧
  (!a b c d. v1' = (a,b) ∧ v2' = (c,d) ⇒ cmp2 b d = cmp2' b d)
  ⇒
  pair_cmp cmp1 cmp2 v1 v2 = pair_cmp cmp1' cmp2' v1' v2'`,
 rw [pair_cmp_def] >>
 every_case_tac >>
 Cases_on `v1` >>
 Cases_on `v2` >>
 fs []);

val _ = DefnBase.export_cong "list_cmp_cong";
val _ = DefnBase.export_cong "option_cmp_cong";
val _ = DefnBase.export_cong "option_cmp2_cong";
val _ = DefnBase.export_cong "pair_cmp_cong";

val good_cmp_trans = Q.store_thm ("good_cmp_trans",
`!cmp. good_cmp cmp ⇒ transitive (λ(k,v) (k',v'). cmp k k' = Less)`,
 rw [relationTheory.transitive_def] >>
 Cases_on `x` >>
 Cases_on `y` >>
 Cases_on `z` >>
 fs [] >>
 metis_tac [cmp_thms]);

val bool_cmp_antisym = Q.store_thm ("bool_cmp_antisym[simp]",
`!x y. bool_cmp x y = Equal ⇔ x = y`,
 rw [] >>
 Cases_on `x` >>
 Cases_on `y` >>
 rw [bool_cmp_def]);

val num_cmp_antisym = Q.store_thm ("num_cmp_antisym[simp]",
`!x y. num_cmp x y = Equal ⇔ x = y`,
 rw [num_cmp_def]);

val char_cmp_antisym = Q.store_thm ("char_cmp_antisym[simp]",
`!x y. char_cmp x y = Equal ⇔ x = y`,
 rw [char_cmp_def, num_cmp_antisym] >>
 rw [ORD_11]);

val list_cmp_antisym = Q.store_thm ("list_cmp_antisym",
`!cmp x y. (!x y. cmp x y = Equal ⇔ x = y) ⇒ (list_cmp cmp x y = Equal ⇔ x = y)`,
 ho_match_mp_tac list_cmp_ind >>
 rw [list_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]);

val string_cmp_antisym = Q.store_thm ("string_cmp_antisym[simp]",
`!x y. string_cmp x y = Equal ⇔ x = y`,
 metis_tac [string_cmp_def, char_cmp_antisym, list_cmp_antisym]);

val pair_cmp_antisym = Q.store_thm ("pair_cmp_antisym",
`!cmp1 cmp2 x y. 
  (!x y. cmp1 x y = Equal ⇔ x = y) ∧
  (!x y. cmp2 x y = Equal ⇔ x = y) 
  ⇒ 
  (pair_cmp cmp1 cmp2 x y = Equal ⇔ x = y)`,
 Cases_on `x` >>
 Cases_on `y` >>
 rw [pair_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]);

val option_cmp_antisym = Q.store_thm ("option_cmp_antisym",
`!cmp x y. 
  (!x y. cmp x y = Equal ⇔ x = y) 
  ⇒ 
  (option_cmp cmp x y = Equal ⇔ x = y)`,
 Cases_on `x` >>
 Cases_on `y` >>
 rw [option_cmp_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]);

val option_cmp2_antisym = Q.store_thm ("option_cmp2_antisym",
`!cmp x y. 
  (!x y. cmp x y = Equal ⇔ x = y) 
  ⇒ 
  (option_cmp2 cmp x y = Equal ⇔ x = y)`,
 Cases_on `x` >>
 Cases_on `y` >>
 rw [option_cmp2_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [comparison_distinct]);

val resp_equiv_def = Define `
resp_equiv cmp f ⇔ !k1 k2 v. cmp k1 k2 = Equal ⇒ f k1 v = f k2 v`;

val resp_equiv2_def = Define `
resp_equiv2 cmp cmp2 f ⇔ (!k1 k2. cmp k1 k2 = Equal ⇒ cmp2 (f k1) (f k2) = Equal)`;

val equiv_inj_def = Define `
equiv_inj cmp cmp2 f ⇔ (!k1 k2. cmp2 (f k1) (f k2) = Equal ⇒ cmp k1 k2 = Equal)`;

val antisym_resp_equiv = Q.store_thm ("antisym_resp_equiv",
`!cmp f. 
  (!x y. cmp x y = Equal ⇒ x = y) 
  ⇒ 
  resp_equiv cmp f ∧ !cmp2. good_cmp cmp2 ⇒ resp_equiv2 cmp cmp2 f`,
 rw [resp_equiv_def, resp_equiv2_def] >>
 metis_tac [cmp_thms]);

val list_cmp_equal_list_rel = Q.store_thm ("list_cmp_equal_list_rel",
`!cmp l1 l2.
  list_cmp cmp l1 l2 = Equal ⇔ LIST_REL (\x y. cmp x y = Equal) l1 l2`,
 Induct_on `l1` >>
 rw [] >>
 Cases_on `l2` >>
 fs [list_cmp_def] >>
 every_case_tac >>
 fs []);

val _ = export_theory ();
