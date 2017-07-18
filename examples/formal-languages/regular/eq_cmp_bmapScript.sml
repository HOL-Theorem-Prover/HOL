(*---------------------------------------------------------------------------*)
(* The balanced_map theory constructs balanced binary trees as a model for   *)
(* finite maps. Lookup of elements is done by use of a comparison function   *)
(* returning elements in {Less, Equal, Greater}. As a consequence, if a node *)
(* in the b-b-tree associates key k with value v, it is in actuality mapping *)
(* v from any k' such that cmp k k' = Equal (cmp is the comparison fn). Thus *)
(* the domain of such a map is made of *sets* of things equal to some key in *)
(* the tree.                                                                 *)
(*                                                                           *)
(* The specifications of b-b-tree operations are phrased in terms of the     *)
(* corresponding operations in finite_map theory. This seems to require a    *)
(* map from ('a,'b) balanced_map to 'a|->'b. But that isn't possible by the  *)
(* discussion above, and actually we have                                    *)
(*                                                                           *)
(*  to_fmap : ('a,'b) balanced_map -> (('a->bool) |-> 'b).                   *)
(*                                                                           *)
(* The major operations on b-b-trees are characterized in terms of to_fmap   *)
(* in balanced_mapTheory. However, to support refinement scenarios, whereby  *)
(* theorems phrased in terms of finite maps are converted to be over         *)
(* b-b-trees, there is a need to translate from finite_map to b-b-trees.     *)
(*                                                                           *)
(* This translation is based on the requirement that                         *)
(*                                                                           *)
(*  (cmp x y = Equal) ==> (x = y)                                            *)
(*                                                                           *)
(* This is useful for settings where there is no derived equality at work,   *)
(* for example regexp_compare.                                               *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib lcsymtacs;
open optionTheory listTheory pred_setTheory comparisonTheory
     balanced_mapTheory finite_mapTheory;

fun pat_elim q = Q.PAT_ASSUM q (K ALL_TAC);
val comparison_distinct = TypeBase.distinct_of ``:ordering``
val comparison_nchotomy = TypeBase.nchotomy_of ``:ordering``

val SET_EQ_THM = Q.prove
(`!s1 s2. (s1 = s2) = !x. s1 x = s2 x`,
 METIS_TAC [EXTENSION,IN_DEF]);

val LENGTH_NIL_SYM =
   GEN_ALL (CONV_RULE (LHS_CONV SYM_CONV) (SPEC_ALL LENGTH_NIL));

val list_ss = list_ss ++ rewrites [LENGTH_NIL, LENGTH_NIL_SYM];

val set_ss = list_ss ++ pred_setLib.PRED_SET_ss ++ rewrites [SET_EQ_THM,IN_DEF]

val _ = new_theory "eq_cmp_bmap";

val eq_cmp_def =
 Define
  `eq_cmp cmp = good_cmp cmp /\ !x y. (cmp x y = Equal) <=> (x=y)`;

val [frange_def,fdom_def] =
 TotalDefn.multiDefine
   `(fdom cmp bmap   = {a | ?x. lookup cmp a bmap = SOME x}) /\
    (frange cmp bmap = {x | ?a. lookup cmp a bmap = SOME x})`;

val bmap_of_list_def =
  Define
   `bmap_of_list cmp (fmap:'a|->'b) list =
        FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap)
              Tip list`;

val fdom_bmap_def =
 Define
   `bmap_of cmp fmap = bmap_of_list cmp fmap (SET_TO_LIST (FDOM fmap))`;

val bmap_of_def = Q.prove
(`bmap_of cmp fmap =
        FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap)
              Tip
              (SET_TO_LIST (FDOM fmap))`,
 metis_tac [bmap_of_list_def, fdom_bmap_def]);

val invariant_insert_list = Q.prove
(`!(list:'a list) fmap cmp.
   good_cmp cmp ==>
   invariant cmp (FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap) Tip list)`,
Induct >> rw [invariant_def] >> metis_tac [insert_thm])

val invariant_bmap_of = Q.store_thm
("invariant_bmap_of",
 `!fmap cmp. good_cmp cmp ==> invariant cmp (bmap_of cmp fmap)`,
 rw [bmap_of_def,invariant_insert_list]);

val eq_cmp_singleton_keyset = Q.store_thm
("eq_cmp_singleton_keyset",
 `!cmp k. eq_cmp cmp ==> (key_set cmp k = {k})`,
 rw_tac set_ss [eq_cmp_def,key_set_def]);

val eq_cmp_keyset = Q.store_thm
("eq_cmp_keyset",
 `!cmp k j. eq_cmp cmp ==> (key_set cmp k j <=> (k=j))`,
 rw_tac set_ss [eq_cmp_def,key_set_def] >> metis_tac[]);

val eq_cmp_lookup_thm = Q.store_thm
("eq_cmp_lookup_thm",
 `!bmap cmp.
    invariant cmp bmap /\ eq_cmp cmp
   ==>
       !x. lookup cmp x bmap = FLOOKUP (to_fmap cmp bmap) {x}`,
 rw [] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
       >> rw [lookup_thm]
       >> metis_tac [eq_cmp_singleton_keyset]);

val lookup_insert_equal = Q.prove
(`!bmap a b y. good_cmp cmp /\ invariant cmp bmap /\ (cmp a b = Equal)
             ==> (lookup cmp b (insert cmp a y bmap) = SOME y)`,
rw [insert_thm,lookup_thm,FLOOKUP_UPDATE]
 >> fs [key_set_def,EXTENSION]
 >> metis_tac [good_cmp_def,comparison_distinct]);

val lookup_insert_notequal = Q.prove
(`!bmap a b y.
     good_cmp cmp /\ invariant cmp bmap /\
     ((cmp a b = Less) \/ (cmp a b = Greater))
    ==> (lookup cmp b (insert cmp a y bmap) = lookup cmp b bmap)`,
rw [insert_thm,lookup_thm,FLOOKUP_UPDATE]
 >> fs [key_set_def,EXTENSION]
 >> metis_tac [good_cmp_def,comparison_distinct]);

val lookup_insert_thm = Q.store_thm
("lookup_insert_thm",
 `!bmap a b y.
     good_cmp cmp /\ invariant cmp bmap
    ==>
     (lookup cmp b (insert cmp a y bmap) =
        if cmp a b = Equal
          then SOME y
          else lookup cmp b bmap)`,
 metis_tac [lookup_insert_equal,lookup_insert_notequal,comparison_nchotomy]);

val lookup_bmap_of_list = Q.prove
(`!list fmap x.
   eq_cmp cmp /\ MEM x list
   ==>
    (lookup cmp x (bmap_of_list cmp fmap list) = SOME (fmap ' x))`,
Induct >> rw [bmap_of_list_def] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
 >- metis_tac [invariant_insert_list,good_cmp_thm,lookup_insert_equal]
 >- (rw [Once lookup_insert_thm,invariant_insert_list,GSYM bmap_of_list_def]
     >> metis_tac [eq_cmp_def]));

val lookup_bmap_of_list_notin = Q.prove
(`!list fmap x.
   eq_cmp cmp /\ ~MEM x list
   ==>
    (lookup cmp x (bmap_of_list cmp fmap list) = NONE)`,
Induct >> rw [bmap_of_list_def] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
 >- rw [lookup_def]
 >- (rw [Once lookup_insert_thm,invariant_insert_list,GSYM bmap_of_list_def]
     >> metis_tac [eq_cmp_def]));

val lookup_bmap_of = Q.store_thm
("lookup_bmap_of",
 `!list fmap x.
   eq_cmp cmp
   ==>
    (lookup cmp x (bmap_of cmp fmap) =
       if x IN FDOM fmap
          then SOME (fmap ' x)
          else NONE)`,
metis_tac [fdom_bmap_def,lookup_bmap_of_list,lookup_bmap_of_list_notin,
           MEM_SET_TO_LIST,FDOM_FINITE]);

val FLOOKUP_lookup = Q.store_thm
("FLOOKUP_lookup",
`!fmap. eq_cmp cmp ==> !x. FLOOKUP fmap x = lookup cmp x (bmap_of cmp fmap)`,
 metis_tac [FLOOKUP_DEF,lookup_bmap_of]);

val inj_lem = Q.prove
(`!fmap x. INJ (\x.{x}) (x INSERT FDOM fmap) (UNIV:('a->bool)->bool)`,
 rw[INJ_DEF]);

val map_keys_fupdate = MATCH_MP (SPEC_ALL MAP_KEYS_FUPDATE) (SPEC_ALL inj_lem);

val fdom_map_keys = Q.prove
(`!fmap. FDOM(MAP_KEYS (\x. {x}) fmap) = IMAGE (\x. {x}) (FDOM fmap)`,
 Induct >> rw[map_keys_fupdate]);

val FLOOKUP_MAP_KEYS = Q.prove
(`!fmap x. FLOOKUP (MAP_KEYS (\x. {x}) fmap) {x} = FLOOKUP fmap x`,
 Induct >> rw [map_keys_fupdate,FLOOKUP_UPDATE]);

val to_fmap_empty = Q.prove
(`!(bmap:('a,'b)balanced_map) (cmp:'a->'a->ordering).
     good_cmp cmp ==> (FLOOKUP (to_fmap cmp bmap) {} = NONE)`,
Induct >> rw [to_fmap_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,key_set_def,EXTENSION]
       >> metis_tac [good_cmp_thm])

val to_fmap_two = Q.prove
(`!(bmap:('a,'b)balanced_map) (cmp:'a->'a->ordering) a b s.
     eq_cmp cmp /\ a IN s /\ b IN s /\ ~(a=b) ==>
      (FLOOKUP (to_fmap cmp bmap) s = NONE)`,
Induct >> rw [to_fmap_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,key_set_def,EXTENSION,
              eq_cmp_def,GSYM IMP_DISJ_THM]
       >- metis_tac []
       >- (BasicProvers.CASE_TAC >> metis_tac[eq_cmp_def,NOT_SOME_NONE]));

val flookup_map_keys_empty = Q.prove
(`!fmap. FLOOKUP (MAP_KEYS (λx. {x}) fmap) {} = NONE`,
Induct >> rw [MAP_KEYS_FEMPTY,map_keys_fupdate,FLOOKUP_UPDATE,FLOOKUP_FUNION]);

val flookup_map_keys_two = Q.prove
(`!fmap a b s.
     ~(a=b) /\ a IN s /\ b IN s
       ==>
      (FLOOKUP (MAP_KEYS (λx. {x}) fmap) s = NONE)`,
Induct
  >> rw [MAP_KEYS_FEMPTY,map_keys_fupdate,FLOOKUP_UPDATE]
  >> `FLOOKUP (MAP_KEYS (λx. {x}) fmap) s = NONE` by metis_tac[]
  >> rw[]
  >> metis_tac [IN_SING]);

(*
val fmap_bmap = Q.store_thm
("fmap_bmap",
 `!fmap cmp. eq_cmp cmp ==> (to_fmap cmp (bmap_of cmp fmap) = MAP_KEYS (\x. {x}) fmap)`,
  rw [fmap_eq_flookup]
   >> `good_cmp cmp` by metis_tac[eq_cmp_def]
   >> STRIP_ASSUME_TAC (SPEC ``k:'a->bool`` SET_CASES)
       >- rw [to_fmap_empty,flookup_map_keys_empty]
       >- (STRIP_ASSUME_TAC (SPEC ``t:'a->bool`` SET_CASES)
            >> rw[FLOOKUP_MAP_KEYS]
               >- (pop_assum (K all_tac)
                    >> `invariant cmp (bmap_of cmp fmap)` by metis_tac [invariant_bmap_of]
                    >> rw [GSYM eq_cmp_lookup_thm]
                    >> metis_tac [FLOOKUP_lookup])
               >- metis_tac [IN_INSERT,flookup_map_keys_two,to_fmap_two]));
*)

val fdom_insert = Q.store_thm
("fdom_insert",
 `!bmap cmp k v.
      eq_cmp cmp /\
      invariant cmp bmap
     ==>
     (fdom cmp (insert cmp k v bmap) = $INSERT k (fdom cmp bmap))`,
rw_tac set_ss [fdom_def]
 >> `good_cmp cmp` by metis_tac [eq_cmp_def]
 >> rw_tac set_ss [Once lookup_insert_thm]
 >> metis_tac [eq_cmp_def]);

val FDOM_fdom = Q.store_thm
("FDOM_fdom",
 `!fmap. eq_cmp cmp ==> (FDOM fmap = fdom cmp (bmap_of cmp fmap))`,
rw [fdom_def,lookup_bmap_of])

val FRANGE_frange = Q.store_thm
("FRANGE_frange",
 `!fmap cmp. eq_cmp cmp ==> (FRANGE fmap = frange cmp (bmap_of cmp fmap))`,
 rw [frange_def,lookup_bmap_of,FRANGE_DEF]);


val _ = export_theory();
