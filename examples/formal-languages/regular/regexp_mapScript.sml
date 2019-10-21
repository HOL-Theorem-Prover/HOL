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
     balanced_mapTheory osetTheory finite_mapTheory regexpTheory;

fun pat_elim q = Q.PAT_X_ASSUM q (K ALL_TAC);

val simp_rule = SIMP_RULE;

val comparison_distinct = TypeBase.distinct_of ``:ordering``
val comparison_nchotomy = TypeBase.nchotomy_of ``:ordering``

Triviality SET_EQ_THM :
 !s1 s2. (s1 = s2) = !x. s1 x = s2 x
Proof
 METIS_TAC [EXTENSION,IN_DEF]
QED

Triviality INTER_DELETE :
  !A a. A INTER (A DELETE a) = A DELETE a
Proof
  SET_TAC []
QED

Triviality LENGTH_NIL_SYM =
   GEN_ALL (CONV_RULE (LHS_CONV SYM_CONV) (SPEC_ALL LENGTH_NIL));

val list_ss = list_ss ++ rewrites [LENGTH_NIL, LENGTH_NIL_SYM];

val set_ss = list_ss ++ pred_setLib.PRED_SET_ss ++ rewrites [SET_EQ_THM,IN_DEF]

val _ = new_theory "regexp_map";

Definition eq_cmp_def :
   eq_cmp cmp <=> good_cmp cmp /\ !x y. (cmp x y = Equal) <=> (x=y)
End

Theorem eq_cmp_regexp_compare :
  eq_cmp regexp_compare
Proof
  metis_tac [eq_cmp_def, regexp_compare_good,regexp_compare_eq]
QED

val [frange_def,fdom_def] =
 TotalDefn.multiDefine
   `(fdom cmp bmap   = {a | ?x. lookup cmp a bmap = SOME x}) /\
    (frange cmp bmap = {x | ?a. lookup cmp a bmap = SOME x})`;

Definition bmap_of_list_def :
     bmap_of_list cmp (fmap:'a|->'b) list =
        FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap)
              Tip list
End

Definition fdom_bmap_def :
    bmap_of cmp fmap = bmap_of_list cmp fmap (SET_TO_LIST (FDOM fmap))
End
;

Theorem bmap_of_def[local] :
 bmap_of cmp fmap =
        FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap)
              Tip
              (SET_TO_LIST (FDOM fmap))
Proof
 metis_tac [bmap_of_list_def, fdom_bmap_def]
QED

Theorem invariant_insert_list[local] :
 !(list:'a list) fmap cmp.
   good_cmp cmp ==>
   invariant cmp (FOLDR (\k bmap. balanced_map$insert cmp k (fmap ' k) bmap) Tip list)
Proof
 Induct >> rw [invariant_def] >> metis_tac [insert_thm]
QED

Theorem invariant_bmap_of :
 !fmap cmp. good_cmp cmp ==> invariant cmp (bmap_of cmp fmap)
Proof
 rw [bmap_of_def,invariant_insert_list]
QED

Theorem eq_cmp_singleton_keyset :
  !cmp k.
     eq_cmp cmp ==> (key_set cmp k = {k})
Proof
 rw_tac set_ss [eq_cmp_def,key_set_def]
QED

Theorem eq_cmp_keyset :
 !cmp k j. eq_cmp cmp ==> (key_set cmp k j <=> (k=j))
Proof
 rw_tac set_ss [eq_cmp_def,key_set_def] >> metis_tac[]
QED

Theorem eq_cmp_lookup_thm :
 !bmap cmp.
    invariant cmp bmap /\ eq_cmp cmp
   ==>
     !x. lookup cmp x bmap = FLOOKUP (to_fmap cmp bmap) {x}
Proof
 rw [] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
       >> rw [lookup_thm]
       >> metis_tac [eq_cmp_singleton_keyset]
QED

Theorem lookup_insert_equal[local] :
 !bmap a b y. good_cmp cmp /\ invariant cmp bmap /\ (cmp a b = Equal)
             ==> (lookup cmp b (insert cmp a y bmap) = SOME y)
Proof
rw [insert_thm,lookup_thm,FLOOKUP_UPDATE]
 >> fs [key_set_def,EXTENSION]
 >> metis_tac [good_cmp_def,comparison_distinct]
QED

Theorem lookup_insert_notequal[local] :
 !bmap a b y.
     good_cmp cmp /\ invariant cmp bmap /\
     ((cmp a b = Less) \/ (cmp a b = Greater))
    ==> (lookup cmp b (insert cmp a y bmap) = lookup cmp b bmap)
Proof
rw [insert_thm,lookup_thm,FLOOKUP_UPDATE]
 >> fs [key_set_def,EXTENSION]
 >> metis_tac [good_cmp_def,comparison_distinct]
QED

Theorem lookup_insert_thm :
 !bmap a b y.
     good_cmp cmp /\ invariant cmp bmap
    ==>
     (lookup cmp b (insert cmp a y bmap) =
        if cmp a b = Equal
          then SOME y
          else lookup cmp b bmap)
Proof
 metis_tac [lookup_insert_equal,lookup_insert_notequal,comparison_nchotomy]
QED

Theorem lookup_bmap_of_list[local] :
 !list fmap x.
   eq_cmp cmp /\ MEM x list
   ==>
    (lookup cmp x (bmap_of_list cmp fmap list) = SOME (fmap ' x))
Proof
Induct >> rw [bmap_of_list_def] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
 >- metis_tac [invariant_insert_list,good_cmp_thm,lookup_insert_equal]
 >- (rw [Once lookup_insert_thm,invariant_insert_list,GSYM bmap_of_list_def]
     >> metis_tac [eq_cmp_def])
QED

Theorem lookup_bmap_of_list_notin[local] :
 !list fmap x.
   eq_cmp cmp /\ ~MEM x list
   ==>
    (lookup cmp x (bmap_of_list cmp fmap list) = NONE)
Proof
Induct >> rw [bmap_of_list_def] >> `good_cmp cmp` by metis_tac [eq_cmp_def]
 >- rw [lookup_def]
 >- (rw [Once lookup_insert_thm,invariant_insert_list,GSYM bmap_of_list_def]
     >> metis_tac [eq_cmp_def])
QED

Theorem lookup_bmap_of :
 !list fmap x.
   eq_cmp cmp
   ==>
    (lookup cmp x (bmap_of cmp fmap) =
       if x IN FDOM fmap
          then SOME (fmap ' x)
          else NONE)
Proof
 metis_tac [fdom_bmap_def,lookup_bmap_of_list,
            lookup_bmap_of_list_notin, MEM_SET_TO_LIST,FDOM_FINITE]
QED

Theorem FLOOKUP_lookup :
 !fmap.
    eq_cmp cmp ==> !x. FLOOKUP fmap x = lookup cmp x (bmap_of cmp fmap)
Proof
 metis_tac [FLOOKUP_DEF,lookup_bmap_of]
QED

Theorem inj_lem[local] :
  !fmap x.
    INJ (\x.{x}) (x INSERT FDOM fmap) (UNIV:('a->bool)->bool)
Proof
 rw[INJ_DEF]
QED

Theorem map_keys_fupdate =
  MATCH_MP (SPEC_ALL MAP_KEYS_FUPDATE) (SPEC_ALL inj_lem);

Theorem fdom_map_keys[local] :
 !fmap. FDOM(MAP_KEYS (\x. {x}) fmap) = IMAGE (\x. {x}) (FDOM fmap)
Proof
 Induct >> rw[map_keys_fupdate]
QED

Theorem FLOOKUP_MAP_KEYS[local] :
 !fmap x. FLOOKUP (MAP_KEYS (\x. {x}) fmap) {x} = FLOOKUP fmap x
Proof
 Induct >> rw [map_keys_fupdate,FLOOKUP_UPDATE]
QED

Theorem to_fmap_empty[local] :
 !(bmap:('a,'b)balanced_map) (cmp:'a->'a->ordering).
     good_cmp cmp ==> (FLOOKUP (to_fmap cmp bmap) {} = NONE)
Proof
Induct
   >> rw [to_fmap_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,key_set_def,EXTENSION]
   >> metis_tac [good_cmp_thm]
QED

Theorem to_fmap_two[local] :
 !(bmap:('a,'b)balanced_map) (cmp:'a->'a->ordering) a b s.
     eq_cmp cmp /\ a IN s /\ b IN s /\ ~(a=b) ==>
      (FLOOKUP (to_fmap cmp bmap) s = NONE)
Proof
Induct >> rw [to_fmap_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,key_set_def,EXTENSION,
              eq_cmp_def,GSYM IMP_DISJ_THM]
       >- metis_tac []
       >- (BasicProvers.CASE_TAC >> metis_tac[eq_cmp_def,NOT_SOME_NONE])
QED

Theorem flookup_map_keys_empty[local] :
 !fmap. FLOOKUP (MAP_KEYS (\x. {x}) fmap) {} = NONE
Proof
  Induct >> rw [MAP_KEYS_FEMPTY,map_keys_fupdate,FLOOKUP_UPDATE,FLOOKUP_FUNION]
QED

Theorem flookup_map_keys_two[local] :
 !fmap a b s.
     ~(a=b) /\ a IN s /\ b IN s
       ==>
      (FLOOKUP (MAP_KEYS (\x. {x}) fmap) s = NONE)
Proof
Induct
  >> rw [MAP_KEYS_FEMPTY,map_keys_fupdate,FLOOKUP_UPDATE]
  >> `FLOOKUP (MAP_KEYS (\x. {x}) fmap) s = NONE` by metis_tac[]
  >> rw[]
  >> metis_tac [IN_SING]
QED

Theorem fdom_insert :
  !bmap cmp k v.
      eq_cmp cmp /\
      invariant cmp bmap
     ==>
     (fdom cmp (insert cmp k v bmap) = $INSERT k (fdom cmp bmap))
Proof
 rw_tac set_ss [fdom_def]
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> rw_tac set_ss [Once lookup_insert_thm]
  >> metis_tac [eq_cmp_def]
QED

Theorem FDOM_fdom :
 !fmap.
     eq_cmp cmp ==> (FDOM fmap = fdom cmp (bmap_of cmp fmap))
Proof
  rw [fdom_def,lookup_bmap_of]
QED

Theorem FRANGE_frange :
  !fmap cmp.
      eq_cmp cmp ==> (FRANGE fmap = frange cmp (bmap_of cmp fmap))
Proof
 rw [frange_def,lookup_bmap_of,FRANGE_DEF]
QED


(*---------------------------------------------------------------------------*)
(* Definitions and lemmas about balanced_map things                          *)
(*---------------------------------------------------------------------------*)

Definition fmap_inj_def :
  fmap_inj cmp bmap =
     !x y. x IN fdom cmp bmap /\
           (lookup cmp x bmap = lookup cmp y bmap)
            ==> (cmp x y = Equal)
End


Definition fapply_def :
  fapply cmp bmap x = THE (lookup cmp x bmap)
End

Definition submap_def :
  submap cmp t1 t2 =
     !x. x IN fdom cmp t1
          ==> x IN fdom cmp t2 /\
             (lookup cmp x t1 = lookup cmp x t2)
End

Theorem member_iff_lookup :
 !fmap cmp x.
     member cmp x fmap <=> ?y. lookup cmp x fmap = SOME y
Proof
  Induct
   >> rw_tac set_ss [member_def, lookup_def]
   >> BasicProvers.EVERY_CASE_TAC
QED

Theorem lookup_bin :
  !fmap fmap' n k v x.
      (lookup cmp r (Bin n k v fmap fmap') = SOME x)
      <=>
      ((cmp r k = Equal) /\ (v = x)) \/
      ((cmp r k = Less) /\ (lookup cmp r fmap = SOME x)) \/
      ((cmp r k = Greater) /\ (lookup cmp r fmap' = SOME x))
Proof
 RW_TAC list_ss [lookup_def] THEN BasicProvers.CASE_TAC
QED

Theorem key_less_lookup :
 !fmap cmp k1 k2 x.
     invariant cmp fmap /\ good_cmp cmp /\
     key_ordered cmp k1 fmap Less /\
     (lookup cmp k2 fmap = SOME x)
     ==>
     (cmp k1 k2 = Less)
Proof
 Induct
  >> rw_tac list_ss [key_ordered_def, lookup_def, invariant_def]
  >> every_case_tac
  >- metis_tac []
  >- metis_tac [good_cmp_def,comparison_distinct]
  >- metis_tac []
QED

Theorem key_greater_lookup :
 !fmap cmp k1 k2 x.
     invariant cmp fmap /\ good_cmp cmp /\
     key_ordered cmp k1 fmap Greater /\
     (lookup cmp k2 fmap = SOME x)
     ==>
     (cmp k2 k1 = Less)
Proof
 Induct
  >> rw_tac list_ss [key_ordered_def, lookup_def, invariant_def]
  >> every_case_tac
  >- metis_tac []
  >- metis_tac [good_cmp_def,comparison_distinct]
  >- metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* submap lemmas                                                             *)
(*---------------------------------------------------------------------------*)

Theorem submap_id :
  !t cmp. submap cmp t t
Proof
   rw [submap_def]
QED

Theorem submap_trans :
 !t1 t2 t3 cmp.
     submap cmp t1 t2 /\ submap cmp t2 t3 ==> submap cmp t1 t3
Proof
  rw [submap_def]
QED

Theorem submap_mono :
 !t1 t2 k v cmp.
    eq_cmp cmp /\ invariant cmp t2 /\ submap cmp t1 t2
    /\ k NOTIN fdom cmp t1
   ==>
   submap cmp t1 (insert cmp k v t2)
Proof
  rw [submap_def,fdom_insert]
  >> res_tac
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> rw [lookup_insert_thm]
  >> `k=x` by metis_tac [eq_cmp_def]
  >> rw []
  >> metis_tac[]
QED

Theorem submap_insert :
 !bmap t cmp x v.
    eq_cmp cmp /\ invariant cmp bmap /\
    x NOTIN fdom cmp bmap /\
    submap cmp (insert cmp x v bmap) t
    ==> submap cmp bmap t
Proof
 rw_tac set_ss [submap_def]
  >> `invariant cmp (insert cmp x v bmap)` by metis_tac [insert_thm,eq_cmp_def]
  >- (qpat_x_assum `$! M` (mp_tac o Q.ID_SPEC) >> rw_tac set_ss [fdom_insert])
  >- (`~(x' = x)` by (fs [fdom_def] >> metis_tac[])
       >> `fdom cmp (insert cmp x v bmap) x'` by rw [fdom_insert,IN_DEF]
       >> `good_cmp cmp` by metis_tac [eq_cmp_def]
       >> `lookup cmp x' (insert cmp x v bmap) = lookup cmp x' t` by metis_tac[]
       >> pop_assum (SUBST_ALL_TAC o SYM)
       >> pat_elim `$!M`
       >> rw_tac set_ss [lookup_insert_thm]
       >> metis_tac [eq_cmp_def])
QED

Theorem fdom_ounion :
 !a b.
   good_cmp cmp /\ invariant cmp a /\ invariant cmp b
   ==>
   (fdom cmp (ounion cmp a b) = (fdom cmp a) UNION (fdom cmp b))
Proof
 rw[fdom_def,ounion_def,SET_EQ_THM]
  >> metis_tac [regexp_compare_good,good_oset_def,
       SIMP_RULE std_ss [oin_def,ounion_def,
                         member_iff_lookup,oneTheory.one] oin_ounion]
QED

Theorem SING_IN_FDOM :
 !x bstmap cmp.
   eq_cmp cmp /\ invariant cmp bstmap
    ==>
   (x IN fdom cmp bstmap <=> {x} IN FDOM (to_fmap cmp bstmap))
Proof
 rw[fdom_def]
  >> drule_then assume_tac eq_cmp_singleton_keyset
  >> Induct_on `bstmap`
  >- rw [to_fmap_def,lookup_def]
  >- (rw [to_fmap_def,lookup_def,invariant_def]
       >> CASE_TAC
       >> rw[EQ_IMP_THM]
       >> fs[]
       >> metis_tac [eq_cmp_def, good_cmp_def,key_less_lookup,key_greater_lookup,
                     ternaryComparisonsTheory.ordering_distinct])
QED

Theorem deleteFindMin_thm :
 !t t' k v.
   invariant regexp_compare t /\ ~null t /\
   deleteFindMin t = ((k,v),t')
   ==> invariant regexp_compare t' /\
       (fdom regexp_compare t = {k} UNION fdom regexp_compare t')
Proof
 rw[]
  >> `good_cmp regexp_compare /\ eq_cmp regexp_compare`
       by metis_tac [eq_cmp_regexp_compare,eq_cmp_def]
  >> `invariant regexp_compare t'` by metis_tac [deleteFindMin]
  >> `FDOM (to_fmap regexp_compare t') =
      FDOM(DRESTRICT (to_fmap regexp_compare t)
            (FDOM (to_fmap regexp_compare t) DELETE key_set regexp_compare k))`
     by metis_tac [deleteFindMin]
  >> fs [FDOM_DRESTRICT,INTER_DELETE]
  >> rfs[eq_cmp_singleton_keyset]
  >> `k IN fdom regexp_compare t`
          by (rw [fdom_def,eq_cmp_lookup_thm]
               >> metis_tac[deleteFindMin,eq_cmp_singleton_keyset])
  >> rw [EXTENSION,SING_IN_FDOM]
  >> metis_tac[SING_IN_FDOM]
QED

Theorem invariant_oset :
 !l. good_cmp cmp ==> invariant cmp (oset cmp l)
Proof
 simp_tac std_ss [oset_def]
   >> Induct
   >> fs [oempty_def,empty_def,oinsert_def]
   >- metis_tac [invariant_def]
   >- metis_tac [insert_thm]
QED

Theorem in_dom_oset :
 !l x.
   eq_cmp cmp ==> (x IN fdom cmp (oset cmp l) <=> MEM x l)
Proof
 Induct >> rw []
  >- rw [oempty_def,empty_def,fdom_def,lookup_def]
  >- (`good_cmp cmp` by metis_tac [eq_cmp_def]
       >> imp_res_tac invariant_oset >> pop_assum (assume_tac o Q.SPEC `l`)
       >> rw [oset_def]
       >> rw [GSYM oset_def]
       >> rw [oinsert_def]
       >> rw_tac set_ss [fdom_insert])
QED

Theorem dom_oset_lem :
 !l.
    eq_cmp cmp ==> (fdom cmp (oset cmp l) = LIST_TO_SET l)
Proof
 rw [EXTENSION,in_dom_oset,eq_cmp_regexp_compare]
QED

Theorem member_insert :
 !bmap x y v.
    eq_cmp cmp /\ invariant cmp bmap ==>
    (member cmp x (insert cmp y v bmap) <=> (x=y) \/ member cmp x bmap)
Proof
 rw [member_iff_lookup,GSYM (SIMP_RULE set_ss [SET_EQ_THM] fdom_def)] >>
 rw [fdom_insert] >> metis_tac [IN_DEF]
QED

Theorem mem_foldrWithKey :
 !(bset:'a oset) acc a. eq_cmp cmp /\ invariant cmp bset ==>
     (MEM (a,()) (foldrWithKey (\k x xs. (k,())::xs) acc bset)
            <=>
      (a IN fdom cmp bset) \/ MEM (a,()) acc)
Proof
 simp_tac set_ss [fdom_def]
 >> Induct >> rw [foldrWithKey_def,invariant_def] >> fs []
 >- rw [lookup_def]
 >- (`good_cmp cmp` by metis_tac [eq_cmp_def]
      >> rw [lookup_bin,EQ_IMP_THM]
      >> metis_tac [key_greater_lookup,key_less_lookup,good_cmp_thm,eq_cmp_def])
QED

Theorem mem_foldrWithKey_lem =
    mem_foldrWithKey
      |> Q.SPEC `bset`
      |> Q.SPEC `[]`
      |> SIMP_RULE list_ss [];

Theorem invariant_ffoldr :
 !list aset f.
    good_cmp cmp /\ invariant cmp aset
    ==>
    invariant cmp (FOLDR (\(k,v) t. insert cmp (f k) v t) aset list)
Proof
  Induct >> rw [invariant_def]
         >> Cases_on `h` >> rw [] >> metis_tac [insert_thm]
QED

Theorem left_to_right_alt :
 eq_cmp (cmp:'b->'b->ordering)
   ==>
   !(list :('a # unit) list) (bset :'b oset) x f.
      invariant cmp bset /\
      (lookup cmp x (FOLDR (\(k,v:unit) t. insert cmp (f k) () t) bset list) = SOME ())
            ==>
           (?a. MEM (a,()) list /\ (x = f a))
           \/
           ((!a. MEM (a,()) list ==> (x <> f a)) /\ (lookup cmp x bset = SOME ()))
Proof
 strip_tac
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> Induct
     >- rw []
     >- (Cases_on `h` >> rw [] >> fs []
          >> pop_assum mp_tac
          >> `invariant cmp (FOLDR (\(k,v:unit) t. insert cmp (f k) () t) bset list)`
               by (Q.SPEC_TAC (`list`,`L`)
                     >> Induct >> rw [invariant_def]
                     >> Cases_on `h` >> rw [] >> metis_tac [insert_thm])
          >> rw [lookup_insert_thm]
          >> metis_tac [eq_cmp_def])
QED

Theorem left_to_right_lem =
    left_to_right_alt
      |> Q.GEN `cmp`
      |> Q.SPEC `cmp2`
      |> UNDISCH
      |> Q.SPEC `foldrWithKey (\(k:'a) (x:unit) xs. (k,())::xs) [] aset`
      |> Q.SPEC `Tip`
      |> Q.SPEC `x`
      |> Q.SPEC `f`
      |> DISCH_ALL;

Theorem oin_fdom :
 !aset x.
   oin cmp x aset <=> x IN fdom cmp aset
Proof
 rw [fdom_def, oin_def, member_iff_lookup]
QED

Theorem mem_oin :
 !list x aset.
     eq_cmp cmp /\ invariant cmp aset /\
     MEM (x,()) list
      ==>
     oin cmp (f x) (FOLDR (\(k,u) s. insert cmp (f k) () s) aset list)
Proof
 Induct >> rw [oin_fdom]
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> mp_tac (SPEC_ALL (invariant_ffoldr |> INST_TYPE [beta |-> ``:unit``, gamma |-> beta]))
  >| [all_tac, Cases_on `h`]
  >> rw[fdom_insert]
  >> metis_tac [oin_fdom,IN_DEF]
QED

Theorem mem_oin_inst =
   mem_oin
   |> SPEC_ALL
   |> Q.INST [`cmp` |-> `cmp2`, `aset` |-> `Tip`, `x` |-> `x'`]
   |> Q.GEN `list`;


Theorem fdom_oimage :
 !aset:'a oset.
     eq_cmp (cmp1:'a->'a->ordering) /\
     eq_cmp (cmp2:'b->'b->ordering) /\ invariant cmp1 aset
    ==> (fdom cmp2 (oimage cmp2 f aset) = {f x | oin cmp1 x aset})
Proof
 simp_tac set_ss
   [oimage_def,map_keys_def,balanced_mapTheory.fromList_def,fdom_def,
    toAscList_def,empty_def,
    rich_listTheory.FOLDR_MAP,pairTheory.LAMBDA_PROD,oneTheory.one]
 >> rw [EQ_IMP_THM]
    >- (mp_tac left_to_right_lem >> rw[invariant_def]
        >- (qexists_tac `a` >> rw[]
             >> pat_elim `lookup _ __ ___ = SOME ()`
             >> pat_elim `eq_cmp cmp2`
             >> `a IN fdom cmp1 aset` by metis_tac [mem_foldrWithKey_lem]
             >> pop_assum mp_tac
             >> rw[oin_def,member_iff_lookup,fdom_def])
        >- fs [lookup_def])
    >- (`MEM (x',()) (foldrWithKey (\k x xs. (k,())::xs) [] aset)`
          by metis_tac [oin_fdom,IN_DEF, mem_foldrWithKey_lem]
         >> mp_tac mem_oin_inst >> rw [invariant_def]
         >> res_tac
         >> fs [oin_def,member_iff_lookup,oneTheory.one])
QED

Theorem fdom_oimage_insert :
 !bset a f cmp1 cmp2.
    eq_cmp (cmp1:'a->'a->ordering) /\
     eq_cmp (cmp2:'b->'b->ordering) /\ invariant cmp1 bset
         ==> (fdom cmp2 (oimage cmp2 f (oinsert cmp1 a bset))
               =
              ((f a) INSERT fdom cmp2 (oimage cmp2 f bset)))
Proof
rpt strip_tac
 >> `invariant cmp1 (oinsert cmp1 a bset)`
       by metis_tac [insert_thm, eq_cmp_def,oinsert_def]
 >> mp_tac (fdom_oimage |> simp_rule set_ss [GSPECIFICATION_applied])
 >> asm_simp_tac bool_ss[]
 >> rw_tac set_ss []
 >> `good_cmp cmp1 /\ good_cmp cmp2` by metis_tac [eq_cmp_def]
 >> rw [oin_def, member_iff_lookup, oinsert_def]
 >> fs [eq_cmp_def,lookup_insert_thm]
 >> metis_tac[]
QED

Theorem fdom_oimage_inst =
   fdom_oimage
   |> INST_TYPE [alpha |-> ``:regexp``, beta |-> ``:num``]
   |> Q.INST [`cmp1` |-> `regexp_compare`, `cmp2` |-> `num_cmp`]
   |> SIMP_RULE std_ss [eq_cmp_regexp_compare,num_cmp_good,num_cmp_antisym,eq_cmp_def];


Theorem invariant_foldl :
  !list work f.
     invariant regexp_compare work
     ==>
      invariant regexp_compare
        (FOLDL (\B a. insert regexp_compare (f a) y B) work list)
Proof
 Induct
  >> rw[]
  >> `invariant regexp_compare (insert regexp_compare (f h) y work)`
          by metis_tac [insert_thm, regexp_compare_good]
  >> rw []
QED

Theorem oin_foldl_insert :
  !list bmap r f.
     invariant regexp_compare bmap
     ==>
    (oin regexp_compare r
         (FOLDL (\B a. insert regexp_compare (f a) () B) bmap list)
     <=>
     oin regexp_compare r bmap \/ MEM r (MAP f list))
Proof
 simp_tac std_ss [oin_def]
  >> Induct
  >> simp_tac list_ss []
  >> rpt gen_tac >> strip_tac
  >> `invariant regexp_compare (insert regexp_compare (f h) () bmap)`
        by metis_tac [regexp_compare_good,insert_thm]
  >> first_x_assum drule
  >> rw_tac list_ss [eq_cmp_regexp_compare,member_insert]
  >> metis_tac[]
QED

val _ = export_theory();
