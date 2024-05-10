(* ------------------------------------------------------------------------- *)
(* Finite Group Theory                                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "finiteGroup";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory dividesTheory numberTheory
     combinatoricsTheory;

open groupTheory monoidTheory groupOrderTheory;

open subgroupTheory;

(* val _ = load "groupProductTheory"; *)
open groupProductTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Group Theory Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   s1 o s2             = subset_cross (g:'a group) s1 s2
   h1 o h2             = subgroup_cross (g:'a group) h1 h2
   left z              = subset_cross_left g s1 s2 z
   right z             = subset_cross_right g s1 s2 z
   independent g a b   = (Gen a) INTER (Gen b) = {#e}
   sgbcross B          = subgroup_big_cross (g:'a group) B
   ssbcross B          = subset_big_cross (g:'a group) B
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Cross Product of Subset and Subgroup:
   make_group_def         |- !g s. make_group g s = <|carrier := s; op := $*; id := #e|>
   make_group_property    |- !g s. ((make_group g s).carrier = s) /\
                                   ((make_group g s).op = $* ) /\
                                   ((make_group g s).id = #e)

   subset_cross_def          |- !g s1 s2. s1 o s2 = {x * y | x IN s1 /\ y IN s2}
   subset_cross_element      |- !g s1 s2 x y. x IN s1 /\ y IN s2 ==> x * y IN s1 o s2
   subset_cross_element_iff  |- !g s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
   subset_cross_alt          |- !g s1 s2. s1 o s2 = IMAGE (\(x,y). x * y) (s1 CROSS s2)

   subgroup_cross_def        |- !g h1 h2. h1 o h2 = make_group g (h1.carrier o h2.carrier)
   subgroup_cross_property   |- !g h1 h2. ((h1 o h2).carrier = h1.carrier o h2.carrier) /\
                                          ((h1 o h2).op = $* ) /\ ((h1 o h2).id = #e)
   subgroup_test_by_cross    |- !g. Group g ==> !h. h <= g <=>
                                    H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE |/ H = H)

   Subset Cross Properties:
   subset_cross_assoc      |- !g. Group g ==>
                              !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
                                         ((s1 o s2) o s3 = s1 o s2 o s3)
   subset_cross_self       |- !g h. h <= g ==> (H o H = H)
   subset_cross_comm       |- !g. AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1)
   subset_cross_subset     |- !g. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> s1 o s2 SUBSET G
   subset_cross_inv        |- !g. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
                                              (IMAGE |/ (s1 o s2) = IMAGE |/ s2 o IMAGE |/ s1)
   subset_cross_finite     |- !g s1 s2. FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2)

   Subgroup Cross Properties:
   subgroup_cross_assoc    |- !g h1 h2 h3. h1 <= g /\ h2 <= g /\ h3 <= g ==> ((h1 o h2) o h3 = h1 o h2 o h3)
   subgroup_cross_self     |- !g h. h <= g ==> (h o h = h)
   subgroup_cross_comm     |- !g. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1)
   subgroup_cross_subgroup |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> h1 o h2 <= g
   subgroup_cross_group    |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2)
   abelian_subgroup_cross_subgroup   |- !g. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> h1 o h2 <= g
   subgroup_cross_finite   |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\ FiniteGroup h1 /\
                              FiniteGroup h2 ==> FiniteGroup (h1 o h2)
   abelian_subgroup_cross_finite     |- !g. AbelianGroup g ==>
                                        !h1 h2. h1 <= g /\ h2 <= g /\ FiniteGroup h1 /\ FiniteGroup h2 ==>
                                        FiniteGroup (h1 o h2)

   Subgroup Cross Cardinality:
   subset_cross_left_right_def         |- !g s1 s2 z. z IN s1 o s2 ==>
                                          left z IN s1 /\ right z IN s2 /\ (z = left z * right z)
   subset_cross_to_preimage_cross_bij  |- !g h1 h2. h1 <= g /\ h2 <= g ==>
                                          (let s1 = h1.carrier in let s2 = h2.carrier in
                                           let f (x,y) = x * y in
                                          !z. z IN s1 o s2 ==>
                                              BIJ (\d. (left z * d,|/ d * right z)) (s1 INTER s2)
                                                                    (preimage f (s1 CROSS s2) z))
   subset_cross_partition_property     |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                             (let s1 = h1.carrier in let s2 = h2.carrier in
                                              let f (x,y) = x * y in
                                          !t. t IN partition (feq f) (s1 CROSS s2) ==>
                                              (CARD t = CARD (s1 INTER s2)))
   subset_cross_element_preimage_card  |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                          (let s1 = h1.carrier in let s2 = h2.carrier in
                                           let f (x,y) = x * y in
                                          !z. z IN s1 o s2 ==>
                                          (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2)))
   subset_cross_preimage_inj   |- !g s1 s2. INJ (preimage (\(x,y). x * y) (s1 CROSS s2)) (s1 o s2)
                                                                            univ(:'a # 'a -> bool)
   subgroup_cross_card_eqn     |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                  (let s1 = h1.carrier in let s2 = h2.carrier in
                                   CARD (h1 o h2).carrier * CARD (s1 INTER s2) = CARD s1 * CARD s2)
   subgroup_cross_card         |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                  (let s1 = h1.carrier in let s2 = h2.carrier in
                                   CARD (h1 o h2).carrier = CARD s1 * CARD s2 DIV CARD (s1 INTER s2))

   Finite Group Generators:
   independent_sym                 |- !g a b. independent g a b <=> independent g b a
   independent_generated_eq        |- !g. Group g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                                                      ((gen a = gen b) <=> (a = b))
   independent_generator_2_card    |- !g. FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                                          (CARD (gen a o gen b).carrier = ord a * ord b)

   all_subgroups_def          |- !g. all_subgroups g = {h | h <= g}
   all_subgroups_element      |- !g h. h IN all_subgroups g <=> h <= g
   all_subgroups_subset       |- !g. Group g ==> IMAGE (\h. H) (all_subgroups g) SUBSET POW G
   all_subgroups_has_gen_id   |- !g. Group g ==> gen #e IN all_subgroups g
   all_subgroups_finite       |- !g. FiniteGroup g ==> FINITE (all_subgroups g)
   generated_image_subset_all_subgroups    |- !g. FiniteGroup g ==>
                                              !s. s SUBSET G ==> IMAGE gen s SUBSET all_subgroups g
   generated_image_subset_power_set       |- !g. Group g ==> !s. s SUBSET G ==> IMAGE (\a. Gen a) s SUBSET POW G

   subset_cross_closure_comm_assoc_fun    |- !g. AbelianGroup g ==> closure_comm_assoc_fun $o (POW G)
   subgroup_cross_closure_comm_assoc_fun  |- !g. AbelianGroup g ==> closure_comm_assoc_fun $o (all_subgroups g)

   Big Cross of Subsets:
   subset_big_cross_def         |- !g B. ssbcross B = ITSET $o B {#e}
   subset_big_cross_empty       |- !g. ssbcross {} = {#e}
   subset_big_cross_thm         |- !g. FiniteAbelianGroup g ==> !B. B SUBSET POW G ==>
                                   !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s))
   subset_big_cross_insert      |- !g. FiniteAbelianGroup g ==> !B. B SUBSET POW G ==>
                                   !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B)

   Big Cross of Subgroups:
   subgroup_big_cross_def       |- !g B. sgbcross B = ITSET $o B (gen #e)
   subgroup_big_cross_empty     |- !g. sgbcross {} = gen #e
   subgroup_big_cross_thm       |- !g. FiniteAbelianGroup g ==> !B. B SUBSET all_subgroups g ==>
                                   !h. h IN all_subgroups g ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h))
   subgroup_big_cross_insert    |- !g. FiniteAbelianGroup g ==> !B. B SUBSET all_subgroups g ==>
                                   !h. h IN all_subgroups g /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Cross Product of Subset and Subgroup                                      *)
(* ------------------------------------------------------------------------- *)

(* Given a Group g, and a subset s, make a group by inheriting op and id. *)
val make_group_def = Define`
    make_group (g:'a group) (s:'a -> bool) =
       <| carrier := s;
               op := g.op;
               id := g.id
        |>
`;

(* Theorem: Properties of make_group g s *)
(* Proof: by make_group_def *)
val make_group_property = store_thm(
  "make_group_property",
  ``!(g:'a group) s. ((make_group g s).carrier = s) /\
                    ((make_group g s).op = g.op) /\
                    ((make_group g s).id = g.id)``,
  rw[make_group_def]);

(* Given two subsets, define their cross-product, or direct product *)
val subset_cross_def = Define`
    subset_cross (g:'a group) (s1:'a -> bool) (s2:'a -> bool) =
       {x * y | x IN s1 /\ y IN s2}
`;

(* Overload subset cross product *)
val _ = overload_on("o", ``subset_cross (g:'a group)``);
(*
> subset_cross_def;
val it = |- !g s1 s2. s1 o s2 = {x * y | x IN s1 /\ y IN s2}: thm
*)

(* Theorem: x IN s1 /\ y IN s2 ==> x * y IN s1 o s2 *)
(* Proof: by subset_cross_def *)
val subset_cross_element = store_thm(
  "subset_cross_element",
  ``!g:'a group. !s1 s2. !x y. x IN s1 /\ y IN s2 ==> x * y IN s1 o s2``,
  rw[subset_cross_def] >>
  metis_tac[]);

(* Theorem: z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y) *)
(* Proof:
   By subset_cross_def, this ius to show:
      (?x y. (z = x * y) /\ x IN s1 /\ y IN s2) <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
   The candidates are just the x, y themselves.
*)
val subset_cross_element_iff = store_thm(
  "subset_cross_element_iff",
  ``!g:'a group. !s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)``,
  rw[subset_cross_def] >>
  metis_tac[]);

(* Theorem: s1 o s2 = IMAGE (\(x, y). x * y) (s1 CROSS s2) *)
(* Proof:
   By subset_cross_def, EXTENSION, this is to show:
   (1) x IN s1 /\ y IN s2 ==> ?x'. (x * y = (\(x,y). x * y) x') /\ FST x' IN s1 /\ SND x' IN s2
       Take x' = (x, y), this is true by function application.
   (2) FST x' IN s1 /\ SND x' IN s2 ==> ?x y. ((\(x,y). x * y) x' = x * y) /\ x IN s1 /\ y IN s2
       Let x = FST x', y = SND x', this is true y UNCURRY.
*)
val subset_cross_alt = store_thm(
  "subset_cross_alt",
  ``!(g:'a group) s1 s2. s1 o s2 = IMAGE (\(x, y). x * y) (s1 CROSS s2)``,
  rw[subset_cross_def, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `(x', y)` >>
    simp[],
    qexists_tac `FST x'` >>
    qexists_tac `SND x'` >>
    simp[pairTheory.UNCURRY]
  ]);

(* Given two subgroups, define their cross-product, or direct product *)
val subgroup_cross_def = Define`
    subgroup_cross (g:'a group) (h1:'a group) (h2:'a group) =
       make_group g (h1.carrier o h2.carrier)
`;

(* Overload subgroup cross product *)
val _ = overload_on("o", ``subgroup_cross (g:'a group)``);
(*
> subgroup_cross_def;
val it = |- !g h1 h2. h1 o h2 = make_group g (h1.carrier o h2.carrier): thm
*)

(* Theorem: ((h1 o h2).carrier = h1.carrier o h2.carrier) /\ ((h1 o h2).op = g.op) /\ ((h1 o h2).id = #e) *)
(* Proof: by subgroup_cross_def, make_group_def *)
val subgroup_cross_property = store_thm(
  "subgroup_cross_property",
  ``!(g h1 h2):'a group. ((h1 o h2).carrier = h1.carrier o h2.carrier) /\
                        ((h1 o h2).op = g.op) /\ ((h1 o h2).id = #e)``,
  rw[subgroup_cross_def, make_group_def]);

(* The following is a reformulation of:
subgroup_alt
|- !g. Group g ==> !h. h <= g <=>
                   H <> {} /\ H SUBSET G /\ (h.op = $* ) /\ (h.id = #e) /\
                   !x y. x IN H /\ y IN H ==> x * |/ y IN H: thm
*)

(* Theorem: Group g ==>
            !h. h <= g <=> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H) *)
(* Proof:
   If part: h <= g ==> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H)
      This is to show:
      (1) h <= g ==> H <> {}, true          by subgroup_carrier_nonempty
      (2) h <= g ==> H SUBSET G, true       by subgroup_carrier_subset
      (3) h <= g ==> h o h = h
          Note (h o h).op = $* = h.op       by subgroup_cross_property, Subgroup_def
           and (h o h).id = #e = h.id       by subgroup_cross_property, subgroup_id
          Need only to show: H o H = H      by monoid_component_equality
          By EXTENSION, this is to show:
          (3.1) x IN H /\ y IN H ==> x * y IN H
                Note x * y = h.op x y       by subgroup_property
                 and h.op x y IN H          by group_op_element
          (3.2) z IN H ==> ?x y. z = x * y /\ x IN H /\ y IN H
                Note h.id IN H              by group_id_element
                Take x = h.id, y = z
                Then x * y
                   = h.op (h.id) z          by subgroup_property
                   = z                      by group_id
      (4) h <= g ==> IMAGE ( |/) H = H
          By IN_IMAGE, EXTENSION, this is to show:
          (4.1) x IN H ==> |/ x IN H
                Note |/ x = h.inv x         by subgroup_inv
                 and (h.inv x) IN H         by group_inv_element
          (4.2) z IN H ==> ?x. (z = |/ x) /\ x IN H
                Take x = h.inv z
                Then x = h.inv z IN H       by group_inv_element
                     |/ x
                   = |/ (h.inv z)           by above
                   = h.inv (h.inv z)        by subgroup_inv
                   = z                      by group_inv_inv

   Only-if part: H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H) ==> h <= g
      By subgroup_alt, this is to show:
      (1) h o h = h ==> h.op = $*
            h.op
          = (h o h).op                      by monoid_component_equality
          = $*                              by subgroup_cross_property
      (2) h o h = h ==> h.id = #e
            h.id
          = (h o h).id                      by monoid_component_equality
          = #e                              by subgroup_cross_property
      (3) h o h = h /\ IMAGE |/ H = H /\ x IN H /\ y IN H ==> x * |/ y IN H
          Note |/ y IN IMAGE |/ H           by IN_IMAGE
            or |/ y IN H                    by H = IMAGE |/ H
            so x * |/ y IN H o H            by subset_cross_element
            or x * |/ y IN H                by subgroup_cross_property
*)
val subgroup_test_by_cross = store_thm(
  "subgroup_test_by_cross",
  ``!g:'a group. Group g ==>
   !h. h <= g <=> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H)``,
  rw[EQ_IMP_THM] >-
  metis_tac[subgroup_carrier_nonempty] >-
  rw[subgroup_carrier_subset] >-
 (pop_assum mp_tac >>
  stripDup[Subgroup_def] >>
  `h.id = #e` by rw[subgroup_id] >>
  rw[subgroup_cross_property, subset_cross_def, monoid_component_equality, EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_property, group_op_element] >>
  metis_tac[subgroup_property, group_id_element, group_id]) >-
 (pop_assum mp_tac >>
  stripDup[Subgroup_def] >>
  `h.id = #e` by rw[subgroup_id] >>
  rw[EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_inv, group_inv_element] >>
  metis_tac[subgroup_inv, group_inv_element, group_inv_inv]) >>
  rw[subgroup_alt] >-
  fs[subgroup_cross_property, monoid_component_equality] >-
  fs[subgroup_cross_property, monoid_component_equality] >>
  prove_tac[subgroup_cross_property, subset_cross_element, IN_IMAGE]);

(* ------------------------------------------------------------------------- *)
(* Subset Cross Properties                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g ==> !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
                        ((s1 o s2) o s3 = s1 o (s2 o s3)) *)
(* Proof:
   By subset_cross_def, EXTENSION this is to show:
   (?x' y. (x = x' * y) /\ (?x'' y. (x' = x'' * y) /\ x'' IN s1 /\ y IN s2) /\ y IN s3) <=>
    ?x' y. (x = x' * y) /\ x' IN s1 /\ ?x y'. (y = x * y') /\ x IN s2 /\ y' IN s3
   By SUBSET_DEF, the candidates are readily chosen, with equations valid by group_assoc.
*)
val subset_cross_assoc = store_thm(
  "subset_cross_assoc",
  ``!g:'a group. Group g ==> !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
       ((s1 o s2) o s3 = s1 o (s2 o s3))``,
  rw[subset_cross_def, EXTENSION] >>
  prove_tac[group_assoc, SUBSET_DEF]);

(* Theorem: h <= g ==> (h o h = h) *)
(* Proof:
   Note Group g /\ Group h         by subgroup_property
   By subset_cross_element_iff, EXTENSION, this is to show:
   (1) h <= g /\ x IN H /\ y IN H ==> x * y IN H
       Note x * y = h.op x y       by subgroup_op
        and h.op x y IN H          by group_op_element
   (2) z IN H ==> ?x y. x IN H /\ y IN H /\ (z = x * y)
       Let x = h.id, y = z.
       Then x IN H                 by group_id_element
       and x * y = h.op x y        by subgroup_op
                 = y               by group_id
                 = z               by above
*)
val subset_cross_self = store_thm(
  "subset_cross_self",
  ``!(g h):'a group. h <= g ==> (H o H = H)``,
  rpt strip_tac >>
  `Group g /\ Group h` by metis_tac[subgroup_property] >>
  rw[subset_cross_element_iff, EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_op, group_op_element] >>
  metis_tac[subgroup_id, subgroup_op, group_id_element, group_id]);

(* Theorem: AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1) *)
(* Proof:
   Note Group g                     by AbelianGroup_def
    and !x y. x IN G /\ y IN G
        ==> (x * y = y * x)         by AbelianGroup_def
    s1 o s2
  = {x * y | x IN s1 /\ y IN s2}    by subset_cross_def
  = {y * x | y IN s2 /\ x IN s1}    by above, SUBSET_DEF
  = s2 o s1                         by subset_cross_def
*)
val subset_cross_comm = store_thm(
  "subset_cross_comm",
  ``!g:'a group. AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1)``,
  rw[AbelianGroup_def] >>
  rw[subset_cross_def, EXTENSION] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2) SUBSET G *)
(* Proof:
   By subset_cross_def, SUBSET_DEF, this is to show:
       x IN s1 /\ y IN s2 ==> x * y IN G
   But x IN s1 ==> x IN G       by SUBSET_DEF, s1 SUBSET G
   and y IN s2 ==> y IN G       by SUBSET_DEF, s2 SUBSET G
   ==> x * y IN G               by group_op_element
*)
val subset_cross_subset = store_thm(
  "subset_cross_subset",
  ``!g:'a group. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2) SUBSET G``,
  rw[subset_cross_def, SUBSET_DEF, pairTheory.EXISTS_PROD] >>
  rw[]);

(* Theorem: Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
            (IMAGE ( |/) (s1 o s2) = (IMAGE ( |/) s2) o (IMAGE ( |/) s1)) *)
(* Proof:
   By subset_cross_def, SUBSET_DEF, this is to show:
      (?x'. (x = |/ x') /\ ?x y. (x' = x * y) /\ x IN s1 /\ y IN s2) <=>
      ?x' y. (x = x' * y) /\ (?x''. (x' = |/ x'') /\ x'' IN s2) /\ ?x. (y = |/ x) /\ x IN s1
   Both directions are satisfied by group_inv_op:
      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ( |/ (x * y) = |/ y * |/ x)
*)
val subset_cross_inv = store_thm(
  "subset_cross_inv",
  ``!g:'a group. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
         (IMAGE ( |/) (s1 o s2) = (IMAGE ( |/) s2) o (IMAGE ( |/) s1))``,
  rw[subset_cross_def, SUBSET_DEF, pairTheory.EXISTS_PROD, EXTENSION] >>
  metis_tac[group_inv_op]);

(* Theorem: FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2) *)
(* Proof:
   Note s1 o s2 = IMAGE (\(x,y). x * y) (s1 CROSS s2)    by subset_cross_alt
    and FINITE (s1 CROSS s2)                             by FINITE_CROSS
   Thus FINITE (s1 o s2)                                 by IMAGE_FINITE
*)
val subset_cross_finite = store_thm(
  "subset_cross_finite",
  ``!g:'a group. !s1 s2. FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2)``,
  rw[subset_cross_alt]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Cross Properties                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: h1 <= g /\ h2 <= g /\ h3 <= g ==> ((h1 o h2) o h3 = h1 o (h2 o h3)) *)
(* Proof:
   Note Group g              by subgroup_property
    and h1.carrier SUBSET G  by subgroup_carrier_subset, h1 <= g
    and h2.carrier SUBSET G  by subgroup_carrier_subset, h2 <= g
    and h3.carrier SUBSET G  by subgroup_carrier_subset, h3 <= g
   By subgroup_cross_property, monoid_component_equality, this is to show:
      (h1.carrier o h2.carrier) o h3.carrier = h1.carrier o (h2.carrier o h3.carrier)
   This is true by subset_cross_assoc.
*)
val subgroup_cross_assoc = store_thm(
  "subgroup_cross_assoc",
  ``!g:'a group. !h1 h2 h3. h1 <= g /\ h2 <= g /\ h3 <= g ==>
       ((h1 o h2) o h3 = h1 o (h2 o h3))``,
  rpt strip_tac >>
  `Group g` by metis_tac[subgroup_property] >>
  rw[subgroup_cross_property, monoid_component_equality, subgroup_carrier_subset, subset_cross_assoc]);

(* Theorem: h <= g ==> (h o h = h) *)
(* Proof:
   By subgroup_cross_property, monoid_component_equality, this is to show:
   (1) h <= g ==>  H o H = H, true    by subset_cross_self
   (2) h <= g ==> $* = h.op, true     by subgroup_op
   (3) h <= g ==> #e = h.id, true     by subgroup_id
*)
val subgroup_cross_self = store_thm(
  "subgroup_cross_self",
  ``!(g h):'a group. h <= g ==> (h o h = h)``,
  rw[subgroup_cross_property, monoid_component_equality] >-
  rw[subset_cross_self] >-
  rw[subgroup_op] >>
  rw[subgroup_id]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1) *)
(* Proof:
   Note Group g             by AbelianGroup_def
   Let s1 = h1.carrier, s2 = h2.carrier.
   By subgroup_cross_property, monoid_component_equality,
   this is to show: s1 o s2 = s2 o s1
   But s1 SUBSET G          by subgroup_carrier_subset
   and s2 SUBSET G          by subgroup_carrier_subset
   so s1 o s2 = s2 o s1     by subset_cross_comm
*)
val subgroup_cross_comm = store_thm(
  "subgroup_cross_comm",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1)``,
  rw[AbelianGroup_def, subgroup_cross_property,
     monoid_component_equality, subset_cross_comm, subgroup_carrier_subset]);

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> (h1 o h2) <= g *)
(* Proof:
   Note Group g                   by subgroup_property
    and Group h1 /\ Group h2      by subgroup_property
   By subgroup_test_by_cross, this is to show:
   (1) h1 <= g /\ h2 <= g ==> (h1 o h2).carrier <> {}
       Note h1.id IN h1.carrier                        by group_id_element
        and h2.id IN h2.carrier                        by group_id_element
       Thus h1.id * h2.id IN (h1.carrier o h2.carrier) by subset_cross_element
         or h1.id * h2.id IN (h1 o h2).carrier         by subgroup_cross_property
         or (h1 o h2).carrier <> {}                    by MEMBER_NOT_EMPTY
   (2) h1 <= g /\ h2 <= g ==> (h1 o h2).carrier SUBSET G
       Let z IN (h1 o h2).carrier
       Then ?x y. x IN h1.carrier /\ y IN h2.carrier
       giving z = x * y                                by subgroup_cross_property, subset_cross_element_iff
       But x IN G                                      by subgroup_carrier_subset, SUBSET_DEF, h1 <= g
       and y IN G                                      by subgroup_carrier_subset, SUBSET_DEF, h2 <= g
       ==> x * y IN G or z IN G                        by group_op_element
       Thus (h1 o h2).carrier SUBSET G                 by SUBSET_DEF
   (3) h1 <= g /\ h2 <= g ==> (h1 o h2) o (h1 o h2) = h1 o h2
       Let H = h1.carrier, K = h2.carrier.
       Note ((h1 o h2) o (h1 o h2)).op = (h1 o h2).op             by subgroup_cross_property
        and ((h1 o h2) o (h1 o h2)).id = (h1 o h2).id             by subgroup_cross_property
       Thus by monoid_component_equality, this is
            to show:
            ((h1 o h2) o (h1 o h2)).carrier = (h1 o h2).carrier   by subgroup_cross_property
         or to show: (H o K) o (H o K) = H o K                    by subgroup_cross_property
       Note H SUBSET G /\ K SUBSET G      by subgroup_carrier_subset
        and H o K = K o H                 by subgroup_cross_property, monoid_component_equality, h1 o h2 = h2 o h1
       Also (H o K) SUBSET G              by subset_cross_subset, H SUBSET G, K SUBSET G

            (H o K) o (H o K)
          = ((H o K) o H) o K             by subset_cross_assoc, (H o K) SUBSET G
          = (H o (K o H)) o K             by subset_cross_assoc
          = (H o (H o K)) o K             by above
          = ((H o H) o K) o K             by subset_cross_assoc
          = (H o K) o K                   by subset_cross_self, h1 <= g
          = H o (K o K)                   by subset_cross_assoc
          = H o K                         by subset_cross_self, h2 <= g
   (4) h1 <= g /\ h2 <= g ==> IMAGE |/ (h1 o h2).carrier = (h1 o h2).carrier
       Let H = h1.carrier, K = h2.carrier.
       Note H SUBSET G /\ K SUBSET G      by subgroup_carrier_subset
        and h1 <= g ==> IMAGE |/ H = H    by subgroup_test_by_cross
        and h2 <= g ==> IMAGE |/ K = K    by subgroup_test_by_cross

         IMAGE |/ (h1 o h2).carrier
       = IMAGE |/ (H o K)                 by subgroup_cross_property
       = (IMAGE |/ K) o (IMAGE |/ H)      by subset_cross_inv
       = K o H                            by above
       = H o K                            by subgroup_cross_property, monoid_component_equality, h1 o h2 = h2 o h1
       = (h1 o h2).carrier                by subgroup_cross_property
*)
val subgroup_cross_subgroup = store_thm(
  "subgroup_cross_subgroup",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> (h1 o h2) <= g``,
  rpt strip_tac >>
  `Group g /\ Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  rw[subgroup_test_by_cross] >-
  metis_tac[group_id_element, subgroup_cross_property, subset_cross_element, MEMBER_NOT_EMPTY] >-
 (rw[SUBSET_DEF] >>
  `?y z. y IN h1.carrier /\ z IN h2.carrier /\ (x = y * z)` by metis_tac[subgroup_cross_property, subset_cross_element_iff] >>
  `y IN G /\ z IN G` by metis_tac[subgroup_carrier_subset, SUBSET_DEF] >>
  rw[]) >-
 (qabbrev_tac `h = h1.carrier` >>
  qabbrev_tac `k = h2.carrier` >>
  `(h o k) o (h o k) = h o k` suffices_by rw[monoid_component_equality, subgroup_cross_property] >>
  `h SUBSET G /\ k SUBSET G` by rw[subgroup_carrier_subset, Abbr`h`, Abbr`k`] >>
  `h o k = k o h` by fs[subgroup_cross_property, monoid_component_equality, Abbr`h`, Abbr`k`] >>
  `(h o k) SUBSET G` by rw[subset_cross_subset] >>
  `(h o k) o (h o k) = ((h o k) o h) o k` by rw[subset_cross_assoc] >>
  `_ = (h o (k o h)) o k` by rw[GSYM subset_cross_assoc] >>
  `_ = (h o (h o k)) o k` by metis_tac[] >>
  `_ = ((h o h) o k) o k` by rw[subset_cross_assoc] >>
  `_ = (h o k) o k` by metis_tac[subset_cross_self] >>
  `_ = h o (k o k)` by rw[subset_cross_assoc] >>
  `_ = h o k` by metis_tac[subset_cross_self] >>
  rw[]) >>
  qabbrev_tac `h = h1.carrier` >>
  qabbrev_tac `k = h2.carrier` >>
  `h SUBSET G /\ k SUBSET G` by rw[subgroup_carrier_subset, Abbr`h`, Abbr`k`] >>
  `IMAGE |/ (h1 o h2).carrier = IMAGE |/ (h o k)` by rw[subgroup_cross_property, Abbr`h`, Abbr`k`] >>
  `_ = (IMAGE |/ k) o (IMAGE |/ h)` by rw[subset_cross_inv] >>
  `_ = k o h` by metis_tac[subgroup_test_by_cross] >>
  `_ = h o k` by metis_tac[subgroup_cross_property, monoid_component_equality] >>
  `_ = (h1 o h2).carrier` by rw[subgroup_cross_property, Abbr`h`, Abbr`k`] >>
  rw[]);

(* This is a milestone theorem for me! *)
(* This is just Lemma X.1 in Appendix of "Finite Group Theory" by Irving Martin Isaacs. *)

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2) *)
(* Proof: by subgroup_cross_subgroup, subgroup_property *)
val subgroup_cross_group = store_thm(
  "subgroup_cross_group",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2)``,
  metis_tac[subgroup_cross_subgroup, subgroup_property]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2) <= g *)
(* Proof: by subgroup_cross_comm, subgroup_cross_subgroup *)
val abelian_subgroup_cross_subgroup = store_thm(
  "abelian_subgroup_cross_subgroup",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2) <= g``,
  rw[subgroup_cross_comm, subgroup_cross_subgroup]);

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\
            FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2) *)
(* Proof:
   Note Group (h1 o h2)                           by subgroup_cross_group
    and FiniteGroup h1 ==> FINITE (h1.carrier)    by FiniteGroup_def
    and FiniteGroup h2 ==> FINITE (h2.carrier)    by FiniteGroup_def
    ==> FINITE (h1.carrier o h2.carrier)          by subset_cross_finite
     or FINITE (h1 o h2).carrier                  by subgroup_cross_property
*)
val subgroup_cross_finite = store_thm(
  "subgroup_cross_finite",
  ``!g:'a group. !h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\
                FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2)``,
  metis_tac[FiniteGroup_def, subgroup_cross_group, subset_cross_finite, subgroup_cross_property]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g /\
            FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2) *)
(* Proof: by subgroup_cross_finite, subgroup_cross_comm. *)
val abelian_subgroup_cross_finite = store_thm(
  "abelian_subgroup_cross_finite",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g /\
                FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2)``,
  rw[subgroup_cross_finite, subgroup_cross_comm]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Cross Cardinality                                                *)
(* ------------------------------------------------------------------------- *)

(* Split element of (s1 o s2) into a left-right pair *)

(*
subset_cross_element_iff
|- !g s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
*)
val lemma = prove(
  ``!g:'a group. !(s1 s2):'a -> bool. !z. ?x y. z IN (s1 o s2) ==> x IN s1 /\ y IN s2 /\ (z = x * y)``,
  metis_tac[subset_cross_element_iff]);

(* 2. Apply Skolemization *)
val subset_cross_left_right_def = new_specification(
   "subset_cross_left_right_def",
  ["subset_cross_left", "subset_cross_right"],
  SIMP_RULE bool_ss [SKOLEM_THM] lemma);

(* overload subset_cross_left and subset_cross_right *)
val _ = overload_on("left", ``subset_cross_left (g:'a group) (s1:'a -> bool) (s2:'a -> bool)``);
val _ = overload_on("right", ``subset_cross_right (g:'a group) (s1:'a -> bool) (s2:'a -> bool)``);

(*
> subset_cross_left_right_def;
val it = |- !g s1 s2 z. z IN s1 o s2 ==> left z IN s1 /\ right z IN s2 /\ (z = left z * right z): thm
*)

(* Picture of BIJECTION:
(s1 INTER s2) <-> (preimage f s z)
    #e        <-> (left z, right z)
    d         <-> ((left z) * d, ( |/ d) * (right z)))
*)

(* Theorem: h1 <= g /\ h2 <= g ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !z. z IN (s1 o s2) ==>
            BIJ (\d. ((left z) * d, ( |/ d) * (right z))) (s1 INTER s2) (preimage f (s1 CROSS s2) z) *)
(* Proof:
   Let s = s1 CROSS s2.
   Note Group g /\ Group h1 /\ Group h2     by subgroup_property
    and s1 SUBSET G /\ s2 SUBSET G          by subgroup_carrier_subset
    and left z IN s1 /\ right z IN s2       by subset_cross_left_right_def
    and !x. x IN s1 ==> x IN G              by SUBSET_DEF, s1 SUBSET G
    and !x. x IN s2 ==> x IN G              by SUBSET_DEF, s2 SUBSET G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN s1 /\ d IN s2 ==> (left z * d,|/ d * mright z) IN preimage f s z
       By in_preimage, IN_CROSS, this is to show:
       (1.1) left z * d IN s1
             Note (left z) * d
                = h.op (left z) d           by subgroup_op
             and  h.op (left z) d IN s1     by group_op_element, Group h1
       (1.2) |/ d * right z IN s2
             With         d IN s2           by given
              ==> (h.inv d) IN s2           by group_inv_element, Group h2
               or      |/ d IN s2           by subgroup_inv, h2 <= g
             Note |/ d * (right z)
                = h.op ( |/ d) (right z)                  by subgroup_op
             and  h.op ( |/ d) (right z) IN s2            by group_op_element, Group h2
       (1.3) left z * d * ( |/ d * right z) = z
             Note |/ d IN G                               by group_inv_element
                  (left z * d) * ( |/ d * right z)
                = ((left z * d) * |/ d) * right z         by group_assoc
                = (left z * (d * |/ d)) * right z         by group_assoc
                = left z * #e * right z                   by group_rinv
                = left z * right z                        by group_rid
                = z                                       by subset_cross_left_right_def
   (2) d IN s1, s2 /\ d' IN s1, s2 /\ left z * d = left z * d' ==> d = d'
       Note left z IN G /\ d IN G /\ d' IN G              by elements in s1 or s2
       Thus left z * d = left z * d' ==> d = d'           by group_lcancel
   (3) d IN s1 /\ d IN s2 ==> (left z * d,|/ d * mright z) IN preimage f s z, same as (1).
   (4) x IN preimage f s z ==> ?d. (d IN s1 /\ d IN s2) /\ ((left z * d,|/ d * right z) = x)
       The idea is:
       To get:  x = (FST x, SND x) = (left z * d, |/ d * right z)
       Use this to solve for d: d = |/ (left z) * FST x

       Note (left z) * (right z) = z      by subset_cross_left_right_def
        and x IN s /\ (f x = z)           by in_preimage
       Let x1 = FST x, x2 = SND x.
       Then x = (x1, x2)                  by PAIR
        and f x = x1 * x2 = z             by function application
        and x1 IN s1 /\ x2 IN s2          by IN_CROSS

       To produce an intersection element,
       Note z = (left z) * (right z) = x1 * x2
        ==>     left z = z * ( |/ (right z))            by group_lsolve
         or     left z = x1 * (x2 * ( |/ (right z)))    by group_assoc, z = x1 * x2
        ==> ( |/ x1) * (left z) = x2 * ( |/ (right z))  by group_rsolve, group_op_element, [1]
       Thus the common element is both IN s1 and IN s2.

       Let d = ( |/ (left z)) * x1, the inverse of common element
       To compute |/ d,
       Note |/ (left z) IN s1             by subgroup_inv, group_inv_element, h1 <= g
        and |/ (right z) IN s2            by subgroup_inv, group_inv_element, h2 <= g
            |/ d
          = |/ (( |/ (left z)) * x1)      by above
          = |/ x1 * (left z)              by group_inv_op, group_inv_inv
          = x2 * ( |/ (right z))          by above identity [1]

       Note d IN s1                       by subgroup_op, group_op_element, d = ( |/ (left z)) * x1
        and |/ d IN s2                    by subgroup_op, group_op_element, |/ d = x2 * ( |/ (right z))
        ==> |/ ( |/ d) = d IN s2          by subgroup_inv, group_inv_element, group_inv_inv

            (left z) * d
          = (left z) * ( |/ (left z)) * x1   by group_assoc
          = x1                               by group_rinv, group_lid
            ( |/ d) * right z
          = x2 * ( |/ (right z) * right z)   by group_assoc
          = x2                               by group_linv, group_rid
       Take this d, and the result follows.
*)
val subset_cross_to_preimage_cross_bij = store_thm(
  "subset_cross_to_preimage_cross_bij",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !z. z IN (s1 o s2) ==>
       BIJ (\d. ((left z) * d, ( |/ d) * (right z))) (s1 INTER s2) (preimage f (s1 CROSS s2) z)``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `Group g /\ Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  `s1 SUBSET G /\ s2 SUBSET G` by rw[subgroup_carrier_subset, Abbr`s1`, Abbr`s2`] >>
  `left z IN s1 /\ right z IN s2` by metis_tac[subset_cross_left_right_def] >>
  `!x. x IN s1 ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!x. x IN s2 ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!d. d IN s1 /\ d IN s2 ==> (left z * d, |/ d * right z) IN preimage f s z` by
  (rw[in_preimage, IN_CROSS, Abbr`s`, Abbr`f`] >-
  metis_tac[group_op_element, subgroup_op] >-
  metis_tac[group_inv_element, group_op_element, subgroup_inv, subgroup_op] >>
  `(left z * d) * ( |/ d * right z) = ((left z * d) * |/ d) * right z` by rw[group_assoc] >>
  `_ = (left z * (d * |/ d)) * right z` by rw[GSYM group_assoc] >>
  `_ = z` by rw[subset_cross_left_right_def] >>
  rw[]
  ) >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  metis_tac[group_lcancel] >>
  `(left z) * (right z) = z` by rw[subset_cross_left_right_def, Abbr`s`, Abbr`f`] >>
  `x IN s /\ (f x = z)` by metis_tac[in_preimage] >>
  qabbrev_tac `x1 = FST x` >>
  qabbrev_tac `x2 = SND x` >>
  `x = (x1, x2)` by rw[pairTheory.PAIR, Abbr`x1`, Abbr`x2`] >>
  `x1 * x2 = z` by rw[Abbr`f`] >>
  `x1 IN s1 /\ x2 IN s2` by metis_tac[IN_CROSS] >>
  `z IN G /\ |/ (left z) IN G /\ |/ (right z) IN G` by rw[] >>
  `left z = z * ( |/ (right z))` by rw[GSYM group_lsolve] >>
  `_ = x1 * (x2 * ( |/ (right z)))` by rw[GSYM group_assoc] >>
  `( |/ x1) * (left z) = x2 * ( |/ (right z))` by metis_tac[group_rsolve, group_op_element] >>
  qabbrev_tac `d = ( |/ (left z)) * x1` >>
  `|/ (left z) IN s1` by metis_tac[subgroup_inv, group_inv_element] >>
  `|/ (right z) IN s2` by metis_tac[subgroup_inv, group_inv_element] >>
  `|/ d = |/ x1 * (left z)` by rw[group_inv_op, group_inv_inv, Abbr`d`] >>
  `_ = x2 * ( |/ (right z))` by rw[] >>
  `d IN s1` by metis_tac[subgroup_op, group_op_element] >>
  `|/ d IN s2` by metis_tac[subgroup_op, group_op_element] >>
  `d IN s2` by metis_tac[subgroup_inv, group_inv_element, group_inv_inv] >>
  `(left z) * d = x1` by rw[GSYM group_assoc, Abbr`d`] >>
  `( |/ d) * right z = x2` by rw[group_assoc] >>
  metis_tac[]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !t. t IN partition (feq f) (s1 CROSS s2) ==> (CARD t = CARD (s1 INTER s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Note partition (feq f) s
      = IMAGE ((preimage f s) o f) s       by feq_partition
      = IMAGE (preimage f s) (IMAGE f s)   by IMAGE_COMPOSE
      = IMAGE (preimage f s) (s1 o s2)     by subset_cross_alt
   With t IN partition (feq f) s           by given
    ==> ?z. z IN (IMAGE f s) /\
            (preimage f s z = t)           by IN_IMAGE
    ==> ?m. BIJ m (s1 INTER s2) t          by subset_cross_to_preimage_cross_bij
   Note s1 SUBSET G /\ s2 SUBSET G         by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2             by SUBSET_FINITE, FINITE G
    ==> FINITE (s1 INTER s2)               by FINITE_INTER
   Thus CARD t = CARD (s1 INTER s2)        by FINITE_BIJ
*)
val subset_cross_partition_property = store_thm(
  "subset_cross_partition_property",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !t. t IN partition (feq f) (s1 CROSS s2) ==> (CARD t = CARD (s1 INTER s2))``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `partition (feq f) s = IMAGE (preimage f s) (IMAGE f s)` by rw[feq_partition, IMAGE_COMPOSE] >>
  `_ = IMAGE (preimage f s) (s1 o s2)` by rw[subset_cross_alt, Abbr`s`] >>
  `?z. z IN (s1 o s2) /\ (preimage f s z = t)` by metis_tac[IN_IMAGE] >>
  `?m. BIJ m (s1 INTER s2) t` by metis_tac[subset_cross_to_preimage_cross_bij] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `FINITE (s1 INTER s2)` by rw[] >>
  metis_tac[FINITE_BIJ]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !z. z IN (s1 o s2) ==> (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Then ?m. BIJ m (s1 INTER s2) (preimage f s z)     by subset_cross_to_preimage_cross_bij
   Note s1 SUBSET G /\ s2 SUBSET G                   by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2                       by SUBSET_FINITE, FINITE G
    ==> FINITE (s1 INTER s2)                         by FINITE_INTER
   Thus CARD (preimage f s z) = CARD (s1 INTER s2)   by FINITE_BIJ
*)
val subset_cross_element_preimage_card = store_thm(
  "subset_cross_element_preimage_card",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !z. z IN (s1 o s2) ==> (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2))``,
  metis_tac[subset_cross_to_preimage_cross_bij, subgroup_carrier_subset,
             SUBSET_FINITE, FINITE_INTER, FINITE_BIJ]);

(* Theorem: INJ (preimage (\(x, y). x * y) (s1 CROSS s2)) (s1 o s2) univ(:('a # 'a -> bool)) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN s1 o s2 ==> preimage (\(x,y). x * y) (s1 CROSS s2) x IN univ(:'a reln)
       Since type_of ``preimage (\(x,y). x * y) (s1 CROSS s2) x`` is :'a reln,
       This is true by IN_UNIV
   (2) x IN s1 o s2 /\ y IN s1 o s2 /\
       preimage (\(x,y). x * y) (s1 CROSS s2) x = preimage (\(x,y). x * y) (s1 CROSS s2) y ==> x = y
       Expand by preimage_def, pairTheory.FORALL_PROD, EXTENSION, this is to show:
       !p_1 p_2. (p_1 IN s1 /\ p_2 IN s2) /\ (p_1 * p_2 = x) <=>
                 (p_1 IN s1 /\ p_2 IN s2) /\ (p_1 * p_2 = y) ==> x = y
       Note ?x1 x2. x1 IN s1 /\ x2 IN s2 /\ (x = x1 * x2)   by subset_cross_element_iff
        ==> y = x1 * x2                                     by implication
         or x = y
*)
val subset_cross_preimage_inj = store_thm(
  "subset_cross_preimage_inj",
  ``!g:'a group. !(s1 s2):'a -> bool.
     INJ (preimage (\(x, y). x * y) (s1 CROSS s2)) (s1 o s2) univ(:('a # 'a -> bool))``,
  rw[INJ_DEF] >>
  fs[preimage_def, pairTheory.FORALL_PROD, EXTENSION] >>
  metis_tac[subset_cross_element_iff]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
                (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)) *)
(* Proof:
   Let s = s1 CROSS s2, f = f = (\(x, y). x * y).
   Note s1 SUBSET G /\ s2 SUBSET G         by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2             by SUBSET_FINITE, FINITE G
     so FINITE s                           by FINITE_CROSS
    ==> FINITE (partition (feq f) s)       by FINITE_partition

   Claim: CARD (partition (feq f) s) = CARD (s1 o s2)
   Proof:   partition (feq f) s
          = IMAGE (preimage f s o f) s                         by feq_partition
          = IMAGE (preimage f s) (IMAGE f s)                   by IMAGE_COMPOSE
          = IMAGE (preimage f s) (s1 o s2)                     by subset_cross_alt
          Note INJ (preimage f s) (s1 o s2) univ(:('a reln))   by subset_cross_preimage_inj
           and FINITE (s1 o s2)                                by subset_cross_finite
           ==> CARD (partition (feq f) s) = CARD (s1 o s2)     by INJ_CARD_IMAGE

   Note !t. t IN partition (feq f) s ==>
            (CARD t = CARD (s1 INTER s2))  by subset_cross_partition_property

      CARD s1 * CARD s2
    = CARD (s1 CROSS s2)                               by CARD_CROSS
    = CARD s                                           by notation
    = SIGMA CARD (partition (feq f) s)                 by finite_card_by_feq_partition
    = CARD (s1 INTER s2) * CARD (partition (feq f) s)  by SIGMA_CARD_CONSTANT
    = CARD (s1 INTER s2) * CARD (s1 o s2)              by Claim
    = CARD (s1 o s2) * CARD (s1 INTER s2)              by MULT_COMM
    = CARD (h1 o h2).carrier * CARD (s1 INTER s2)      by subgroup_cross_property
*)
val subgroup_cross_card_eqn = store_thm(
  "subgroup_cross_card_eqn",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
    (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2))``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `s1 SUBSET G /\ s2 SUBSET G` by rw[subgroup_carrier_subset, Abbr`s1`, Abbr`s2`] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `FINITE s` by rw[Abbr`s`] >>
  qabbrev_tac `f = (\(x:'a, y:'a). x * y)` >>
  `CARD (partition (feq f) s) = CARD (s1 o s2)` by
  (`partition (feq f) s = IMAGE (preimage f s) (IMAGE f s)` by rw[feq_partition, IMAGE_COMPOSE] >>
  `_ = IMAGE (preimage f s) (s1 o s2)` by rw[subset_cross_alt, Abbr`s`] >>
  metis_tac[subset_cross_finite, subset_cross_preimage_inj, INJ_CARD_IMAGE]) >>
  `FINITE (partition (feq f) s)` by rw[FINITE_partition] >>
  `CARD s1 * CARD s2 = CARD (s1 CROSS s2)` by rw[CARD_CROSS] >>
  `_ = SIGMA CARD (partition (feq f) s)` by rw[finite_card_by_feq_partition, Abbr`s`] >>
  `_ = CARD (s1 INTER s2) * CARD (s1 o s2)` by metis_tac[SIGMA_CARD_CONSTANT, subset_cross_partition_property] >>
  rw[subgroup_cross_property, Abbr`s1`, Abbr`s2`]);

(* Another proof of the same theorem *)

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
            (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Then s1 SUBSET G /\ s2 SUBSET G     by subgroup_carrier_subset
    ==> FINITE s1 /\ FINITE s2         by SUBSET_FINITE, FINITE G
   Thus FINITE s                       by FINITE_CROSS
    and FINITE (s1 o s2)               by subset_cross_finite

   Let f = (\(x:'a, y:'a). x * y),
   Note !z. z IN (s1 o s2) ==>
        ((CARD o t) z = CARD (s1 INTER s2))            by subset_cross_element_preimage_card, [1]

      CARD s1 * CARD s2
    = CARD s                                           by CARD_CROSS
    = SIGMA CARD (IMAGE (preimage f s o f) s)          by finite_card_by_image_preimage, FINITE s
    = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))    by IMAGE_COMPOSE
    = SIGMA CARD (IMAGE (preimage f s) (s1 o s2))      by subset_cross_alt
    = SIGMA (CARD o preimage f s) (s1 o s2)            by SUM_IMAGE_INJ_o, subset_cross_preimage_inj, FINITE (s1 o s2)
    = SIGMA (\z. CARD (s1 INTER s2)) (s1 o s2)         by SUM_IMAGE_CONG, [1]
    = CARD (s1 INTER s2) * CARD (s1 o s2)              by SIGMA_CONSTANT
    = CARD (s1 o s2) * CARD (s1 INTER s2)              by MULT_COMM
    = CARD (h1 o h2).carrier * CARD (s1 INTER s2)      by subgroup_cross_property
*)
Theorem subgroup_cross_card_eqn[allow_rebind]:
  !(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
    (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `FINITE s` by rw[Abbr`s`] >>
  `FINITE (s1 o s2)` by rw[subset_cross_finite] >>
  qabbrev_tac `f = (\(x:'a, y:'a). x * y)` >>
  qabbrev_tac `t = preimage f s` >>
  (`!z. z IN (s1 o s2) ==> ((CARD o t) z = CARD (s1 INTER s2))` by (rw[] >> metis_tac[subset_cross_element_preimage_card])) >>
  `CARD s1 * CARD s2 = CARD s` by rw[CARD_CROSS, Abbr`s`] >>
  `_ = SIGMA CARD (IMAGE (t o f) s)` by rw[finite_card_by_image_preimage, Abbr`t`] >>
  `_ = SIGMA CARD (IMAGE t (IMAGE f s))` by rw[IMAGE_COMPOSE] >>
  `_ = SIGMA CARD (IMAGE t (s1 o s2))` by rw[subset_cross_alt] >>
  `_ = SIGMA (CARD o t) (s1 o s2)` by metis_tac[SUM_IMAGE_INJ_o, subset_cross_preimage_inj] >>
  `_ = SIGMA (\z. CARD (s1 INTER s2)) (s1 o s2)` by rw[SUM_IMAGE_CONG] >>
  `_ = CARD (s1 INTER s2) * CARD (s1 o s2)` by rw[SIGMA_CONSTANT] >>
  rw[subgroup_cross_property]
QED

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
                (CARD (h1 o h2).carrier = ((CARD s1) * (CARD s2)) DIV (CARD (s1 INTER s2))) *)
(* Proof:
   Note Group h1 /\ Group h2        by subgroup_property
    and s1 SUBSET G /\ s2 SUBSET G  by subgroup_carrier_subset
    ==> FINITE s1 /\ FINITE s2      by SUBSET_FINITE
   Note #e IN s1 /\ #e IN s2        by subgroup_id, group_id_element
   Thus #e IN s1 INTER s2           by IN_INTER
    and FINITE (s1 INTER s2)        by FINITE_INTER
    ==> s1 INTER s2 <> {}           by MEMBER_NOT_EMPTY
     or CARD (s1 INTER s2) <> 0     by CARD_EQ_0
     or 0 < CARD (s1 INTER s2)      by NOT_ZERO_LT_ZERO
     By subgroup_cross_card_eqn,
        CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)
    Thus the result follows         by DIV_SOLVE, 0 < CARD (s1 INTER s2)
*)
val subgroup_cross_card = store_thm(
  "subgroup_cross_card",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
       (CARD (h1 o h2).carrier = ((CARD s1) * (CARD s2)) DIV (CARD (s1 INTER s2)))``,
  rw_tac std_ss[] >>
  `Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `#e IN s1 /\ #e IN s2` by metis_tac[subgroup_id, group_id_element] >>
  `#e IN s1 INTER s2` by rw[] >>
  `FINITE (s1 INTER s2)` by rw[] >>
  `CARD (s1 INTER s2) <> 0` by metis_tac[CARD_EQ_0, MEMBER_NOT_EMPTY] >>
  metis_tac[subgroup_cross_card_eqn, DIV_SOLVE, NOT_ZERO_LT_ZERO]);

(* Another milestone theorem for me! *)
(* This is just Lemma X.2 in Appendix of "Finite Group Theory" by Irving Martin Isaacs. *)

(* ------------------------------------------------------------------------- *)
(* Finite Group Generators                                                   *)
(* ------------------------------------------------------------------------- *)

(*
I thought that, given a IN G /\ b IN G, if a <> b, then (Gen a) INTER (Gen b) = {#e}.
However, a proof of this turns out to be elusive.
This comes down to showing:   a ** n = b ** m  is impossible for n < ord a, m < ord b.
But even for the case n = m, a = b is hard to conclude.
Eventually I realize that, (gen (a * a)) is a subgroup of (gen a), and a * a <> a!.
This gives (Gen (a * a)) SUBSET (Gen a), so (Gen (a * a)) INTER (Gen a) = (Gen (a * a)) <> {#e}.
Thus (Gen a) INTER (Gen b) = {#e} is a condition in elements a, b, called these independence.
*)

(* Overload the notion of independent group elements *)
val _ = overload_on("independent",
        ``\(g:'a group) a b. (Gen a) INTER (Gen b) = {#e}``);

(* Theorem: independent g a b = independent g b a *)
(* Proof:
       independent g a b
   <=> (Gen a) INTER (Gen b) = {#e}     by notation
   <=> (Gen b) INTER (Gen a) = {#e}     by INTER_COMM
   <=> independent g b a                by notation
*)
val independent_sym = store_thm(
  "independent_sym",
  ``!g:'a group. !a b. independent g a b = independent g b a``,
  rw[INTER_COMM]);

(* Theorem: Group g ==>
            !a b. a IN G /\ b IN G /\ independent g a b ==> ((gen a = gen b) <=> (a = b)) *)
(* Proof:
   If part: gen a = gen b ==> a = b
      Note Gen a = Gen b                  by Generated_def, monoid_component_equality
       and a IN (Gen a) /\ b IN (Gen b)   by generated_gen_element, Group g
      Note (Gen a) INTER (Gen b) = {#e}   by notation
       ==> a IN {#e} /\ b IN {#e}         by IN_INTER
        or a = #e /\ b = #e               by IN_SING
      Thus a = b.

   Only-if part: a = b ==> gen a = gen b, true trivially.
*)
val independent_generated_eq = store_thm(
  "independent_generated_eq",
  ``!g:'a group. Group g ==>
   !a b. a IN G /\ b IN G /\ independent g a b ==> ((gen a = gen b) <=> (a = b))``,
  rw[EQ_IMP_THM] >>
  `Gen a = Gen b` by rw[Generated_def, monoid_component_equality] >>
  metis_tac[generated_gen_element, IN_INTER, IN_SING]);

(* Theorem: FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                (CARD ((gen a) o (gen b)).carrier = (ord a) * (ord b)) *)
(* Proof:
   Note (gen a) <= g /\ (gen b) <= g     by generated_subgroup
    and CARD (Gen a) = ord a             by generated_group_card, group_order_pos
    and CARD (Gen b) = ord b             by generated_group_card, group_order_pos
    Now (Gen a) INTER (Gen b) = {#e}     by independent a b
    and CARD {#e} = 1                    by CARD_SING

        CARD ((gen a) o (gen b)).carrier
      = ((CARD (Gen a)) * (CARD (Gen b))) DIV (CARD ((Gen a) INTER (Gen b)))   by subgroup_cross_card
      = ((ord a) * (ord b)) DIV 1        by above
      = (ord a) * (ord b)                by DIV_1
*)
val independent_generator_2_card = store_thm(
  "independent_generator_2_card",
  ``!g:'a group. FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                (CARD ((gen a) o (gen b)).carrier = (ord a) * (ord b))``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(gen a) <= g /\ (gen b) <= g` by rw[generated_subgroup] >>
  `CARD {#e} = 1` by rw[] >>
  metis_tac[subgroup_cross_card, generated_group_card, group_order_pos, DIV_1]);

(* Define the set of all subgroups of a group. *)
val all_subgroups_def = Define`
    all_subgroups (g:'a group) = {h | h <= g}
`;

(* Theorem: h IN all_subgroups g <=> h <= g *)
(* Proof: by all_subgroups_def *)
val all_subgroups_element = store_thm(
  "all_subgroups_element",
  ``!g:'a group. !h. h IN all_subgroups g <=> h <= g``,
  rw[all_subgroups_def]);

(* Theorem: Group g ==> (IMAGE (\h:'a group. H) (all_subgroups g)) SUBSET (POW G) *)
(* Proof:
   Let s IN IMAGE (\h:'a group. H) (all_subgroups g)
   Then ?h. h IN (all_subgroups g) /\ (H = s)   by IN_IMAGE
     or ?h. h <= g  /\ (H = s)                  by all_subgroups_element
     or ?h. h <= g  /\ (H = s) /\ (H SUBSET G)  by subgroup_carrier_subset
     or s IN (POW G)                            by IN_POW
   The result follows                           by SUBSET_DEF
*)
val all_subgroups_subset = store_thm(
  "all_subgroups_subset",
  ``!g:'a group. Group g ==> (IMAGE (\h:'a group. H) (all_subgroups g)) SUBSET (POW G)``,
  rw[all_subgroups_element, SUBSET_DEF, IN_POW] >>
  metis_tac[subgroup_carrier_subset, SUBSET_DEF]);

(* Theorem: Group g ==> (gen #e) IN (all_subgroups g) *)
(* Proof:
   Note #e IN G                        by group_id_element, Group g
    and (gen #e) <= g                  by generated_id_subgroup, Group g
    ==> (gen #e) IN (all_subgroups g)  by all_subgroups_element
*)
val all_subgroups_has_gen_id = store_thm(
  "all_subgroups_has_gen_id",
  ``!g:'a group. Group g ==> (gen #e) IN (all_subgroups g)``,
  rw[generated_id_subgroup, all_subgroups_element]);

(* Theorem: FiniteGroup g ==> FINITE (all_subgroups g) *)
(* Proof:
   Note Group g /\ FINITE G      by FiniteGroup_def
   Let f = \h:'a group. H, s = all_subgroups g
   Then (IMAGE f s) SUBSET (POW G)     by all_subgroups_subset, Group g
    and FINITE (POW G)                 by FINITE_POW, FINITE G
    ==> FINITE (IMAGE f s)             by SUBSET_FINITE
   Claim: INJ f s (IMAGE f s)
   Proof: By INJ_DEF, this is to show:
          !h1 h2. h1 IN s /\ h2 IN s /\ (h1.carrier = h2.carrier) ==> h1 = h2.
          or      h1 <= g /\ h2 <= g /\ (h1.carrier = h2.carrier) ==> h1 = h2   by all_subgroups_element
          This is true                 by subgroup_eq

   With INJ f s (IMAGE f s)            by Claim
    and FINITE (IMAGE f s)             by above
    ==> FINITE s                       by FINITE_INJ
*)
val all_subgroups_finite = store_thm(
  "all_subgroups_finite",
  ``!g:'a group. FiniteGroup g ==> FINITE (all_subgroups g)``,
  rw[FiniteGroup_def] >>
  qabbrev_tac `f = \h:'a group. H` >>
  qabbrev_tac `s = all_subgroups g` >>
  `(IMAGE f s) SUBSET (POW G)` by rw[all_subgroups_subset, Abbr`f`, Abbr`s`] >>
  `FINITE (POW G)` by rw[FINITE_POW] >>
  `FINITE (IMAGE f s)` by metis_tac[SUBSET_FINITE] >>
  (`INJ f s (IMAGE f s)` by (rw[INJ_DEF, all_subgroups_element, Abbr`f`, Abbr`s`] >> metis_tac[subgroup_eq])) >>
  metis_tac[FINITE_INJ]);

(* Theorem: FiniteGroup g ==> !s. s SUBSET G ==> (IMAGE gen s) SUBSET all_subgroups g *)
(* Proof:
   Let h IN (IMAGE gen s)
   Then ?x. x IN s /\ (h = gen x)   by IN_IMAGE
     or ?x. x IN G /\ (h = gen x)   by SUBSET_DEF, s SUBSET G
     or h <= g                      by generated_subgroup, FiniteGroup g
   Thus h IN all_subgroups g        by all_subgroups_element
   The result follows               by SUBSET_DEF
*)
val generated_image_subset_all_subgroups = store_thm(
  "generated_image_subset_all_subgroups",
  ``!g:'a group. FiniteGroup g ==> !s. s SUBSET G ==> (IMAGE gen s) SUBSET all_subgroups g``,
  metis_tac[generated_subgroup, SUBSET_DEF, all_subgroups_element, IN_IMAGE]);

(* Theorem: Group g ==> !s. s SUBSET G ==> (IMAGE Gen s) SUBSET (POW G) *)
(* Proof:
   Let z IN (IMAGE Gen s)
   Then ?x. x IN s /\ (z = Gen x)   by IN_IMAGE
     or ?x. x IN G /\ (z = Gen x)   by SUBSET_DEF, s SUBSET G
     or z SUBSET G                  by generated_subset, FiniteGroup g
   Thus z IN POW G                  by IN_POW
   The result follows               by SUBSET_DEF
*)
val generated_image_subset_power_set = store_thm(
  "generated_image_subset_power_set",
  ``!g:'a group. Group g ==> !s. s SUBSET G ==> (IMAGE Gen s) SUBSET (POW G)``,
  rw[IN_POW, SUBSET_DEF] >>
  metis_tac[generated_subset, SUBSET_DEF]);

(* Theorem: AbelianGroup g ==> closure_comm_assoc_fun (subset_cross g) (POW G) *)
(* Proof:
   Note Group g              by AbelianGroup_def
   By closure_comm_assoc_fun_def, IN_POW, this is to show:
   (1) x SUBSET G /\ y SUBSET G ==> x o y SUBSET G
       This is true          by subset_cross_subset, Group g
   (2) x SUBSET G /\ y SUBSET G /\ z SUBSET G ==> x o (y o z) = y o (x o z)
         x o (y o z)
       = (x o y) o z         by subset_cross_assoc, Group g
       = (y o x) o z         by subset_cross_comm, AbelianGroup g
       = y o (x o z)         by subset_cross_assoc, Group g
*)
val subset_cross_closure_comm_assoc_fun = store_thm(
  "subset_cross_closure_comm_assoc_fun",
  ``!g:'a group. AbelianGroup g ==> closure_comm_assoc_fun (subset_cross g) (POW G)``,
  rpt strip_tac >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  rw[closure_comm_assoc_fun_def, IN_POW] >-
  rw[subset_cross_subset] >>
  `x o (y o z) = (x o y) o z` by rw[subset_cross_assoc] >>
  `_ = (y o x) o z` by rw[subset_cross_comm] >>
  rw[subset_cross_assoc]);

(* Theorem: AbelianGroup g ==> closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g) *)
(* Proof:
   Note Group g              by AbelianGroup_def
   By closure_comm_assoc_fun_def, all_subgroups_element, this is to show:
   (1) x <= g /\ y <= g ==> x o y <= g
       This is true          by abelian_subgroup_cross_subgroup, AbelianGroup g
   (2) x <= g /\ y <= g /\ z <= g ==> x o (y o z) = y o (x o z)
         x o (y o z)
       = (x o y) o z         by subgroup_cross_assoc
       = (y o x) o z         by subgroup_cross_comm, AbelianGroup g
       = y o (x o z)         by subgroup_cross_assoc
*)
val subgroup_cross_closure_comm_assoc_fun = store_thm(
  "subgroup_cross_closure_comm_assoc_fun",
  ``!g:'a group. AbelianGroup g ==> closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)``,
  rpt strip_tac >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  rw[closure_comm_assoc_fun_def, all_subgroups_element] >-
  rw[abelian_subgroup_cross_subgroup] >>
  `x o (y o z) = (x o y) o z` by rw[subgroup_cross_assoc] >>
  `_ = (y o x) o z` by rw[subgroup_cross_comm] >>
  rw[subgroup_cross_assoc]);

(* ------------------------------------------------------------------------- *)
(* Big Cross of Subsets.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define big cross product of subsets. *)
val subset_big_cross_def = Define`
    subset_big_cross (g:'a group) (B:('a -> bool) -> bool) = ITSET (subset_cross g) B {#e}
`;
(* overload big cross product of subsets. *)
val _ = overload_on("ssbcross", ``subset_big_cross (g:'a group)``);

(*
> subset_big_cross_def;
val it = |- !g B. ssbcross B = ITSET $o B {#e}: thm
*)

(* Theorem: ssbcross {} = {#e} *)
(* Proof:
     ssbcross {}
   = ITSET $o {} {#e}    by subset_big_cross_def
   = {#e}                by ITSET_EMPTY
*)
val subset_big_cross_empty = store_thm(
  "subset_big_cross_empty",
  ``!g:'a group. ssbcross {} = {#e}``,
  rw[subset_big_cross_def, ITSET_EMPTY]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
            !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s)) *)
(* Proof:
   Note AbelianGroup g /\ FINITE G      by FiniteAbelianGroup_def
    ==> Group g                         by AbelianGroup_def
   Note closure_comm_assoc_fun (subset_cross g) (POW G)
                                        by subset_cross_closure_comm_assoc_fun
    Now FINITE (POW G)                  by FINITE_POW
     so FINITE B                        by SUBSET_FINITE
   Also {#e} SUBSET G                   by group_id_element, SUBSET_DEF
     so {#e} IN (POW G)                 by IN_POW
    and s IN (POW G)                    by IN_POW, s SUBSET G

     (ssbcross (s INSERT B)
   = ITSET $o (s INSERT B) {#e}         by subset_big_cross_def
   = s o ITSET $o (B DELETE s) {#e}     by SUBSET_COMMUTING_ITSET_RECURSES
   = s o ssbcross (B DELETE s))         by subset_big_cross_def
*)
val subset_big_cross_thm = store_thm(
  "subset_big_cross_thm",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
   !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s))``,
  rw[FiniteAbelianGroup_def] >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  `closure_comm_assoc_fun (subset_cross g) (POW G)` by rw[subset_cross_closure_comm_assoc_fun] >>
  `FINITE B` by metis_tac[FINITE_POW, SUBSET_FINITE] >>
  `s IN (POW G)` by rw[IN_POW] >>
  `{#e} IN (POW G)` by rw[IN_POW] >>
  metis_tac[subset_big_cross_def, SUBSET_COMMUTING_ITSET_RECURSES]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
            !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B) *)
(* Proof: by subset_big_cross_thm, DELETE_NON_ELEMENT *)
val subset_big_cross_insert = store_thm(
  "subset_big_cross_insert",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
   !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B)``,
  rw[subset_big_cross_thm, DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)
(* Big Cross of Subgroups.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define big cross product of subgroups. *)
val subgroup_big_cross_def = Define`
    subgroup_big_cross (g:'a group) (B:('a group) -> bool) = ITSET (subgroup_cross g) B (gen #e)
`;
(* overload big cross product of subgroups. *)
val _ = overload_on("sgbcross", ``subgroup_big_cross (g:'a group)``);

(*
> subgroup_big_cross_def;
val it = |- !g B. sgbcross B = ITSET $o B (gen #e): thm
*)

(* Theorem: sgbcross {} = gen #e *)
(* Proof:
     sgbcross {}
   = ITSET $o {} (gen #e)    by subgroup_big_cross_def
   = gen #e                  by ITSET_EMPTY
*)
val subgroup_big_cross_empty = store_thm(
  "subgroup_big_cross_empty",
  ``!g:'a group. sgbcross {} = gen #e``,
  rw[subgroup_big_cross_def, ITSET_EMPTY]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
            !h. h IN (all_subgroups g) ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h)) *)
(* Proof:
   Note AbelianGroup g /\ FINITE G      by FiniteAbelianGroup_def
    ==> Group g                         by AbelianGroup_def
    and FiniteGroup g                   by FiniteGroup_def
   Note closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)
                                        by subgroup_cross_closure_comm_assoc_fun
    Now FINITE (all_subgroups g)        by all_subgroups_finite
     so FINITE B                        by SUBSET_FINITE
    and (gen #e) IN (all_subgroups g)   by all_subgroups_has_gen_id

     (sgbcross (h INSERT B)
   = ITSET $o (h INSERT B) (gen #e)     by subgroup_big_cross_def
   = h o ITSET $o (B DELETE h) (gen #e) by SUBSET_COMMUTING_ITSET_RECURSES
   = h o sgbcross (B DELETE h))         by subgroup_big_cross_def
*)
val subgroup_big_cross_thm = store_thm(
  "subgroup_big_cross_thm",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
   !h. h IN (all_subgroups g) ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h))``,
  rw[FiniteAbelianGroup_def] >>
  `Group g /\ FiniteGroup g` by metis_tac[AbelianGroup_def, FiniteGroup_def] >>
  `closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)` by rw[subgroup_cross_closure_comm_assoc_fun] >>
  `FINITE B` by metis_tac[all_subgroups_finite, SUBSET_FINITE] >>
  `(gen #e) IN (all_subgroups g)` by rw[all_subgroups_has_gen_id] >>
  metis_tac[subgroup_big_cross_def, SUBSET_COMMUTING_ITSET_RECURSES]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
            !h. h IN (all_subgroups g) /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B) *)
(* Proof: by subgroup_big_cross_thm, DELETE_NON_ELEMENT *)
val subgroup_big_cross_insert = store_thm(
  "subgroup_big_cross_insert",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
   !h. h IN (all_subgroups g) /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B)``,
  rw[subgroup_big_cross_thm, DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
