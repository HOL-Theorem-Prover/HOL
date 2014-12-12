open HolKernel boolLib bossLib BasicProvers Parse;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open balanced_mapTheory comparisonTheory;
open lcsymtacs;

val _ = new_theory "oset";

val _ = temp_tight_equality ();

(* oset for ordered set *)
val _ = type_abbrev ("oset", ``:('a,unit) balanced_map``);

(* Basic definitions, that correspond directly to balanced tree operations *)
val good_oset_def = Define `
good_oset cmp (s:'a oset) ⇔ good_cmp cmp ∧ invariant cmp s`;

val oempty_def = Define `
oempty = empty:'a oset`;

val osingleton_def = Define `
osingleton v = singleton v ()`;

val oin_def = Define `
oin cmp (v:'a) (s:'a oset) ⇔  member cmp v s`;

val oinsert_def = Define `
oinsert cmp v s = insert cmp v () s`;

val odelete_def = Define `
odelete cmp (s:'a oset) (v:'a) = delete cmp v s`;

val ounion_def = Define `
ounion cmp (s1:'a oset) s2 = union cmp s1 s2`;

val oimage_def = Define `
oimage cmp f (s:'a oset) = map_keys cmp f s`;

val osubset_def = Define `
osubset cmp (s1:'a oset) (s2:'a oset) ⇔ isSubmapOf cmp s1 s2`;

val ocompare_def = Define `
ocompare cmp (s1:'a oset) (s2:'a oset) = compare cmp (\x y. Equal) s1 s2`;

val oevery_def = Define `
oevery f (s:'a oset) ⇔  every (\x y. f x) s`;

val oexists_def = Define `
oexists f (s:'a oset) ⇔  exists (\x y. f x) s`;

val oset_def = Define `
oset cmp l = FOLDR (λx t. oinsert cmp x t) oempty l`;

val oresp_equiv_def = Define `
oresp_equiv cmp f = resp_equiv cmp (λx y:unit. f x)`;

(* operations preserve good_set *)

val good_oset_oempty = Q.store_thm ("good_oset_oempty",
`!cmp. good_cmp cmp ⇒ good_oset cmp oempty`,
 rw [empty_thm, good_oset_def, oempty_def]);

val good_oset_osingleton = Q.store_thm ("good_oset_osingleton",
`!cmp x. good_cmp cmp ⇒ good_oset cmp (osingleton x)`,
 rw [singleton_thm, good_oset_def, osingleton_def]);

val good_oset_oinsert = Q.store_thm ("good_oset_oinsert",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (oinsert cmp x s)`,
 rw [oinsert_def, good_oset_def] >>
 metis_tac [insert_thm]);

val good_oset_odelete = Q.store_thm ("good_oset_odelete",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (odelete cmp s x)`,
 rw [good_oset_def, odelete_def] >>
 metis_tac [delete_thm]);

val good_oset_ounion = Q.store_thm ("good_oset_ounion",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ good_oset cmp (ounion cmp s1 s2)`,
 rw [good_oset_def, ounion_def] >>
 metis_tac [union_thm]);

(*
val good_oset_oimage = Q.store_thm ("good_oset_oimage",
`!cmp f s. good_cmp cmp ⇒ good_oset cmp (oimage cmp f s)`,
 cheat);
 *)

val good_cmp_ocompare = Q.store_thm ("good_cmp_ocompare",
`!cmp f s. good_cmp cmp ⇒ good_cmp (ocompare cmp)`,
 rw [] >>
 `good_cmp (\(x:unit) (y:unit). Equal)` 
            by (rw [good_cmp_def, LAMBDA_PROD, FORALL_PROD] >>
                metis_tac [good_cmp_def]) >>
 imp_res_tac compare_good_cmp >>
 rw [ocompare_def, good_cmp_def] >>
 metis_tac [good_cmp_def]);

val good_oset_oset_help = Q.prove (
`!cmp s l. good_oset cmp s ⇒ good_oset cmp (FOLDR (λx t. oinsert cmp x t) s l)`,
 Induct_on `l` >>
 rw [] >>
 match_mp_tac good_oset_oinsert >>
 metis_tac []);

val good_oset_oset = Q.store_thm ("good_oset_oset",
`!cmp l. good_cmp cmp ⇒ good_oset cmp (oset cmp l)`,
 rw [oset_def] >>
 metis_tac [good_oset_oset_help, good_oset_oempty]);

(* oempty theorems *)

val oin_oempty = Q.store_thm ("oin_oinsert[simp]",
`!cmp x. oin cmp x oempty = F`,
 rw [oin_def, oempty_def, empty_def, member_def]); 

val oimage_oempty = Q.store_thm ("oimage_oempty[simp]",
`!cmp f. oimage cmp f oempty = oempty`,
 rw [oimage_def, oempty_def, map_keys_def, empty_def, fromList_def,
     toAscList_def, foldrWithKey_def]);

val oinsert_oempty = Q.store_thm ("oinsert_oempty[simp]",
`!cmp x. oinsert cmp x oempty = osingleton x`,
 rw [oinsert_def, oempty_def, osingleton_def, insert_def, empty_def, singleton_def]);

val odelete_oempty = Q.store_thm ("odelete_oempty[simp]",
`!cmp x. odelete cmp oempty x = oempty`,
 rw [odelete_def, oempty_def, delete_def, empty_def]);

val ounion_oempty = Q.store_thm ("ounion_oempty[simp]",
`!cmp s. ounion cmp oempty s = s ∧ ounion cmp s oempty = s`,
 rw [ounion_def, oempty_def, union_def, empty_def] >>
 Cases_on `s` >>
 rw [union_def]);

val oempty_subset = Q.store_thm ("oempty_subset[simp]",
`!cmp s. (osubset cmp oempty s ⇔ T) ∧ (osubset cmp s oempty ⇔ s = oempty)`,
 rw [osubset_def, oempty_def, isSubmapOf_def, isSubmapOfBy_def, empty_def, 
     submap'_def, size_def] >>
 Cases_on `s` >>
 rw [submap'_def, size_def]);

val oevery_oempty = Q.store_thm ("oevery_oempty[simp]",
`!f. oevery f oempty = T`,
 rw [oevery_def, oempty_def, every_def, empty_def]);

val oexists_oempty = Q.store_thm ("oexists_oempty[simp]",
`!f. oexists f oempty = F`,
 rw [oexists_def, oempty_def, exists_def, empty_def]);

val oset_empty = Q.store_thm ("oset_empty[simp]",
`!cmp. oset cmp [] = oempty`,
 rw [oset_def, oempty_def]);

(* singleton theorems *)

val oin_singleton = Q.store_thm ("oin_singleton[simp]",
`∀cmp x y. oin cmp x (osingleton y) ⇔ cmp x y = Equal`,
 rw [oin_def, osingleton_def, member_def, singleton_def] >>
 EVERY_CASE_TAC);

val oimage_osingleton = Q.store_thm ("oimage_osingleton[simp]",
`!cmp f x. oimage cmp f (osingleton x) = osingleton (f x)`,
 rw [oimage_def, osingleton_def, map_keys_def, singleton_def, fromList_def,
     toAscList_def, foldrWithKey_def, empty_def, insert_def]);

val odelete_osingleton = Q.store_thm ("odelete_osingleton[simp]",
`!cmp x y. good_cmp cmp ⇒ odelete cmp (osingleton x) y = if cmp x y = Equal then oempty else osingleton x`,
 rw [odelete_def, oempty_def, delete_def, empty_def, singleton_def, osingleton_def] >>
 EVERY_CASE_TAC >>
 rw [balanceR_def, balanceL_def, glue_def] >>
 metis_tac [cmp_thms]);

val oevery_osingleton = Q.store_thm ("oevery_osingleton[simp]",
`!f x. oevery f (osingleton x) = f x`,
 rw [oevery_def, osingleton_def, every_def, singleton_def]);

val oexists_osingleton = Q.store_thm ("oexists_osingleton[simp]",
`!f x. oexists f (osingleton x) = f x`,
 rw [oexists_def, osingleton_def, exists_def, singleton_def]);

val oset_singleton = Q.store_thm ("oset_singleton[simp]",
`!cmp x. oset cmp [x] = osingleton x`,
 rw [oset_def, osingleton_def]);

(* How oin interacts with other operations *)

val oin_oinsert = Q.store_thm ("oin_oinsert",
`∀cmp x y s. good_oset cmp s ⇒ (oin cmp x (oinsert cmp y s) ⇔ cmp x y = Equal ∨ oin cmp x s)`,
 rw [good_oset_def, oin_def, oinsert_def] >>
 imp_res_tac insert_thm >>
 last_x_assum (qspecl_then [`()`, `y`] assume_tac) >>
 imp_res_tac member_thm >>
 rw [FLOOKUP_UPDATE] >>
 rfs [key_set_eq] >>
 metis_tac [good_cmp_def]);

val oin_odelete = Q.store_thm ("oin_odelete",
`!cmp s x y. good_oset cmp s ⇒ (oin cmp x (odelete cmp s y) ⇔ oin cmp x s ∧ cmp x y ≠ Equal)`,
 rw [oin_def, odelete_def] >>
 imp_res_tac good_oset_odelete >>
 pop_assum (qspecl_then [`y`] assume_tac) >>
 fs [good_oset_def, odelete_def] >>
 imp_res_tac delete_thm >>
 imp_res_tac member_thm >>
 rw [FDOM_DRESTRICT, key_set_eq] >>
 eq_tac >>
 rw []);

val oin_ounion = Q.store_thm ("oin_ounion",
`!cmp x s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (oin cmp x (ounion cmp s1 s2) ⇔ oin cmp x s1 ∨ oin cmp x s2)`,
 rw [oin_def] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 fs [good_oset_def, ounion_def] >>
 imp_res_tac member_thm >>
 rw [] >>
 `to_fmap cmp (union cmp s1 s2) = to_fmap cmp s1 ⊌ to_fmap cmp s2` by metis_tac [union_thm] >>
 rw []);

(*
val oin_oimage = Q.store_thm ("oin_oimage",
`!cmp y s f. good_cmp cmp ⇒ (oin cmp y (oimage cmp f s) ⇔ ?x. cmp y (f x) = Equal ∧ oin cmp x s)`,
 cheat);
 *)

val osubset_thm = Q.store_thm ("osubset_thm",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (osubset cmp s1 s2 ⇔ (!x. oin cmp x s1 ⇒ oin cmp x s2))`,
 rw [osubset_def, good_oset_def, isSubmapOf_thm, oin_def] >>
 rw [member_thm, lookup_thm, FLOOKUP_DEF] >>
 eq_tac >>
 rw []);

val oextension = Q.store_thm ("oextension",
`!cmp s1 s2. 
  good_oset cmp s1 ∧ good_oset cmp s2
  ⇒ 
  (ocompare cmp s1 s2 = Equal ⇔ (!x. oin cmp x s1 ⇔ oin cmp x s2))`,
 rw [good_oset_def, ocompare_def] >>
 `good_cmp (\(x:unit) (y:unit). Equal)` 
            by (rw [good_cmp_def, LAMBDA_PROD, FORALL_PROD] >>
                metis_tac [good_cmp_def]) >>
 rw [compare_thm] >>
 rw [oin_def, member_thm, fmap_rel_OPTREL_FLOOKUP, OPTREL_def, FLOOKUP_DEF] >>
 eq_tac >>
 rw []
 >- metis_tac [] >>
 CCONTR_TAC >>
 fs [] >>
 imp_res_tac to_fmap_key_set >>
 fs [] >>
 metis_tac []);

val oevery_oin = Q.store_thm ("oevery_oin",
`!cmp f s. 
  good_oset cmp s ∧
  oresp_equiv cmp f
  ⇒ 
  (oevery f s ⇔ (!x. oin cmp x s ⇒ f x))`,
 rw [good_oset_def, oevery_def, oin_def, oresp_equiv_def] >>
 imp_res_tac every_thm >>
 rw [lookup_thm, flookup_thm, member_thm]);

val oexists_oin = Q.store_thm ("oexists_oin",
`!cmp f s. 
  good_oset cmp s ∧
  oresp_equiv cmp f
  ⇒ 
  (oexists f s ⇔ (?x. oin cmp x s ∧ f x))`,
 rw [oresp_equiv_def, good_oset_def, oexists_def, oin_def] >>
 imp_res_tac exists_thm >>
 rw [lookup_thm, flookup_thm, member_thm]);

val oin_oset_help = Q.prove (
`!cmp l x s. 
  good_oset cmp s
  ⇒
  (oin cmp x (FOLDR (λx t. oinsert cmp x t) s l) 
   ⇔ 
   oin cmp x s ∨ ?y. MEM y l ∧ cmp x y = Equal)`,
 Induct_on `l` >>
 rw [] >>
 imp_res_tac good_oset_oset_help >>
 rw [oin_oinsert] >>
 eq_tac >>
 rw [] >>
 res_tac >>
 fs [] >>
 metis_tac []);

val oin_oset = Q.store_thm ("oin_oset",
`!cmp l x. good_cmp cmp ⇒ (oin cmp x (oset cmp l) ⇔ ?y. MEM y l ∧ cmp x y = Equal)`,
 rw [oset_def] >>
 metis_tac [oin_oset_help, good_oset_oempty, oin_oempty]);

(* Theorems about oevery and oexists *)

val oevery_oinsert = Q.store_thm ("oevery_oinsert",
`!f cmp x s.
  good_oset cmp s ∧
  oresp_equiv cmp f
  ⇒
  (oevery f (oinsert cmp x s) ⇔ f x ∧ oevery f s)`,
 rw [] >>
 `good_oset cmp (oinsert cmp x s)` by metis_tac [good_oset_oinsert] >>
 imp_res_tac oevery_oin >>
 rw [oin_oinsert] >>
 eq_tac >>
 rw [] >>
 fs [oresp_equiv_def, resp_equiv_def] >>
 metis_tac [good_oset_def, cmp_thms]);

val oexists_oinsert = Q.store_thm ("oexists_oinsert",
`!f cmp x s.
  good_oset cmp s ∧
  oresp_equiv cmp f
  ⇒
  (oexists f (oinsert cmp x s) ⇔ f x ∨ oexists f s)`,
 rw [] >>
 `good_oset cmp (oinsert cmp x s)` by metis_tac [good_oset_oinsert] >>
 imp_res_tac oexists_oin >>
 rw [oin_oinsert] >>
 eq_tac >>
 rw [] >>
 fs [oresp_equiv_def, resp_equiv_def] >>
 metis_tac [good_oset_def, cmp_thms]);

val oevery_ounion = Q.store_thm ("oevery_ounion",
`!f cmp s1 s2.
  good_oset cmp s1 ∧
  good_oset cmp s2 ∧
  oresp_equiv cmp f
  ⇒
  (oevery f (ounion cmp s1 s2) ⇔ oevery f s1 ∧ oevery f s2)`,
 rw [] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 imp_res_tac oevery_oin >>
 rw [oin_ounion] >>
 eq_tac >>
 rw [] >>
 fs [oresp_equiv_def, resp_equiv_def]);

val oexists_ounion = Q.store_thm ("oexists_ounion",
`!f cmp s1 s2.
  good_oset cmp s1 ∧
  good_oset cmp s2 ∧
  oresp_equiv cmp f
  ⇒
  (oexists f (ounion cmp s1 s2) ⇔ oexists f s1 ∨ oexists f s2)`,
 rw [] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 imp_res_tac oexists_oin >>
 rw [oin_ounion] >>
 eq_tac >>
 rw [] >>
 fs [oresp_equiv_def, resp_equiv_def] >>
 metis_tac []);

val _ = export_theory ();
