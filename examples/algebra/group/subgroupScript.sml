(* ------------------------------------------------------------------------- *)
(* Group Theory -- Subgroups.                                                *)
(* ------------------------------------------------------------------------- *)

(*

Subgroups
=========
Cosets
Lagrange's Theorem

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "subgroup";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory numberTheory combinatoricsTheory;

open groupMapTheory;
open groupTheory monoidTheory;

(* ------------------------------------------------------------------------- *)
(* Subgroup Documentation                                                    *)
(* ------------------------------------------------------------------------- *)
(* Data type group:
   The generic symbol for group data is g.
   g.carrier = Carrier set of group, overloaded as G.
   g.op      = Binary operation of group, overloaded as *.
   g.id      = Identity element of group, overloaded as #e.
   g.exp     = Iteration of g.op (added by monoid)
   g.inv     = Inverse of g.op   (added by monoid)

   The generic symbol for a subgroup is h, denoted by h <= g.
   h.carrier = Carrier set of subgroup, overloaded as H.
   h.op      = Binary operation of subgroup, same as g.op = *.
   h.id      = Identity element of subgroup, same as g.id = #e.

   Overloading (# is temporary):
   h <= g       = Subgroup h g
   a * H        = coset g a H
   H * a        = right_coset g H a
#  K            = k.carrier
#  x o y        = h.op x y
   sgbINTER g   = subgroup_big_intersect g
*)
(* Definitions and Theorems (# are exported):

   Subgroup of a Group:
   Subgroup_def       |- !h g.  h <= g <=> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )
   subgroup_property  |- !g h. h <= g ==> Group h /\ Group g /\ H SUBSET G /\
                        !x y. x IN H /\ y IN H ==> (h.op x y = x * y)
#  subgroup_element   |- !g h. h <= g ==> !z. z IN H ==> z IN G
   subgroup_homomorphism   |- !g h. h <= g ==> Group h /\ Group g /\ subgroup h g
   subgroup_carrier_subset |- !g h. h <= g ==> H SUBSET G
   subgroup_op        |- !g h. h <= g ==> (h.op = $* )
   subgroup_id        |- !g h. h <= g ==> (h.id = #e)
   subgroup_inv       |- !g h. h <= g ==> !x. x IN H ==> (h.inv x = |/ x)
   subgroup_has_groups|- !g h. h <= g ==> Group g /\ Group h
   subgroup_is_group  |- !g h. h <= g ==> Group h
   subgroup_is_submonoid   |- !g h. h <= g ==> h << g
   subgroup_exp       |- !g h. h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n
   subgroup_alt       |- !g. Group g ==> !h. h <= g <=> H <> {} /\ H SUBSET G /\
                            (h.op = $* ) /\ (h.id = #e) /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_thm       |- !g h. h <= g <=>
                               Group g /\ (h.op = $* ) /\ (h.id = #e) /\ H <> {} /\ H SUBSET G /\
                         !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_order     |- !g h. h <= g ==> !x. x IN H ==> (order h x = ord x)

   Subgroup Theorems:
   subgroup_refl      |- !g. Group g ==> g <= g
   subgroup_antisym   |- !g h. h <= g /\ g <= h ==> (h = g)
   subgroup_trans     |- !g h t. h <= t /\ t <= g ==> h <= g

   finite_subgroup_carrier_finite  |- !g. FiniteGroup g ==> !h. h <= g ==> FINITE H
   finite_subgroup_finite_group    |- !g. FiniteGroup g ==> !h. h <= g ==> FiniteGroup h
   abelian_subgroup_abelian        |- !g h. AbelianGroup g /\ h <= g ==> AbelianGroup h

   subgroup_groups            |- !g h. h <= g ==> Group h /\ Group g
   subgroup_property_all      |- !g h. h <= g ==>
                                       Group g /\ Group h /\ H <> {} /\ H SUBSET G /\
                                       (h.op = $* ) /\ (h.id = #e) /\
                                       (!x. x IN H ==> (h.inv x = |/ x)) /\
                                        !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_inv_closure       |- !g h. h <= g ==> !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_carrier_nonempty  |- !g h. h <= g ==> H <> {}
   subgroup_eq_carrier        |- !g h. h <= g /\ (H = G) ==> (h = g)
   subgroup_eq                |- !g h1 h2. h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier))

   Cosets, especially cosets of a subgroup:
   coset_def         |- !g X a. a * X = IMAGE (\z. a * z) X
   left_coset_def    |- !g X a. left_coset g X a = a * X
   right_coset_def   |- !g X a. X * a = IMAGE (\z. z * a) X
   coset_alt         |- !g a X. a * X = {a * z | z IN X}
   left_coset_alt    |- !g X a. left_coset g X a = {a * z | z IN X}
   right_coset_alt   |- !g X a. X * a = {z * a | z IN X}
   coset_property    |- !g a. Group g /\ a IN G ==> !X. X SUBSET G ==> a * X SUBSET G
   coset_empty       |- !g a. Group g /\ a IN G ==> (a * {} = {})
   coset_element     |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)
   in_coset          |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)
   group_coset_eq_itself      |- !g a. Group g /\ a IN G ==> (a * G = G)
   group_coset_is_permutation |- !g a. Group g /\ a IN G ==> (a * G = G)
   subgroup_coset_subset    |- !g h a x. h <= g /\ a IN G /\ x IN a * H ==> x IN G
   element_coset_property   |- !g X a. a IN G ==> !x. x IN X ==> a * x IN a * X
   subgroup_coset_nonempty  |- !h g. h <= g ==> !x. x IN G ==> x IN x * H
   subgroup_coset_eq        |- !g h. h <= g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> |/ y * x IN H)
   subgroup_to_coset_bij    |- !g h. h <= g ==> !a. a IN G ==> BIJ (\x. a * x) H (a * H)
   subgroup_coset_card      |- !g h. h <= g /\ FINITE H ==> !a. a IN G ==> (CARD (a * H) = CARD H)

   Lagrange's Theorem by Subgroups and Cosets:
   inCoset_def               |- !g h a b. inCoset g h a b <=> b IN a * H
   inCoset_refl              |- !g h. h <= g ==> !a. a IN G ==> inCoset g h a a
   inCoset_sym               |- !g h. h <= g ==> !a b. a IN G /\ b IN G /\
                                      inCoset g h a b ==> inCoset g h b a
   inCoset_trans             |- !g h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\
                                      inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c
   inCoset_equiv_on_carrier  |- !g h. h <= g ==> inCoset g h equiv_on G
   CosetPartition_def        |- !g h. CosetPartition g h = partition (inCoset g h) G
   carrier_card_by_coset_partition  |- !g h.  h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (CosetPartition g h))
   coset_partition_element   |- !g h. h <= g ==> (!e. e IN CosetPartition g h <=> ?a. a IN G /\ (e = a * H))
   coset_partition_element_card |- !g h. h <= g /\ FINITE G ==> !e. e IN CosetPartition g h ==> (CARD e = CARD H)
   Lagrange_identity         |- !g h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (CosetPartition g h))
   coset_partition_card      |- !g h. h <= g /\ FINITE G ==> (CARD (CosetPartition g h) = CARD G DIV CARD H)
   Lagrange_thm              |- !g h. h <= g /\ FINITE G ==> (CARD H) divides (CARD G)

   Alternate proof without using inCoset:
   subgroup_coset_sym        |- !g h. h <= g ==> !a b. a IN G /\ b IN G /\ b IN a * H ==> a IN b * H
   subgroup_coset_trans      |- !g h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\
                                                    b IN a * H /\ c IN b * H ==> c IN a * H
   subgroup_incoset_equiv  |- !g h. h <= g ==> left_coset g H equiv_on G
   carrier_card_by_subgroup_coset_partition |- !g h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (partition (left_coset g H) G))
   subgroup_coset_partition_element |- !g h. h <= g ==> (!e. e IN partition (left_coset g H) G <=> ?a. a IN G /\ (e = a * H))
   subgroup_coset_card_partition_element |- !g h. h <= g /\ FINITE G ==> !e. e IN partition (left_coset g H) G ==> (CARD e = CARD H)
   Lagrange_identity_alt   |- !g h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (partition (left_coset g H) G))

   Useful Coset theorems:
   subgroup_coset_in_partition     |- !g h. h <= g ==>
                                      !x. x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h
   coset_partition_eq_coset_image  |- !g h. h <= g ==> (CosetPartition g h = IMAGE (left_coset g H) G)
   coset_id_eq_subgroup            |- !g h. h <= g ==> (#e * H = H)

   Conjugate of sets and subgroups:
   conjugate_def                   |- !g a s. conjugate g a s = {a * z * |/ a | z IN s}
   conjugate_subgroup_def          |- !h g a. conjugate_subgroup h g a =
                                              <|carrier := conjugate g a H; id := #e; op := $* |>
   conjugate_subgroup_group        |- !g h. h <= g ==> !a. a IN G ==> Group (conjugate_subgroup h g a)
   conjugate_subgroup_subgroup     |- !g h. h <= g ==> !a::(G). conjugate_subgroup h g a <= g
   subgroup_conjugate_subgroup_bij |- !g h. h <= g ==> !a. a IN G ==>
                                            BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier

   Subgroup Intersection:
   subgroup_intersect_has_inv   |- !g h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K
   subgroup_intersect_group     |- !g h k. h <= g /\ k <= g ==> Group (h mINTER k)
   subgroup_intersect_inv       |- !g h k. h <= g /\ k <= g ==>
                                           !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)
   subgroup_intersect_property  |- !g h k. h <= g /\ k <= g ==>
                                           ((h mINTER k).carrier = H INTER K) /\
                                           (!x y. x IN H INTER K /\ y IN H INTER K ==>
                                            ((h mINTER k).op x y = x * y)) /\ ((h mINTER k).id = #e) /\
                                            !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)
   subgroup_intersect_subgroup  |- !g h k. h <= g /\ k <= g ==> (h mINTER k) <= g

   Subgroup Big Intersection:
   subgroup_big_intersect_def   |- !g. sgbINTER g =
                                       <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g}); op := $*; id := #e|>
   subgroup_big_intersect_property  |- !g. ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
                                           (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                                           ((sgbINTER g).op x y = x * y)) /\ ((sgbINTER g).id = #e)
   subgroup_big_intersect_element    |- !g x. x IN (sgbINTER g).carrier <=> !h. h <= g ==> x IN H
   subgroup_big_intersect_op_element |- !g x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                                               (sgbINTER g).op x y IN (sgbINTER g).carrier
   subgroup_big_intersect_has_id     |- !g. (sgbINTER g).id IN (sgbINTER g).carrier
   subgroup_big_intersect_has_inv    |- !g x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier
   subgroup_big_intersect_subset     |- !g. Group g ==> (sgbINTER g).carrier SUBSET G
   subgroup_big_intersect_group      |- !g. Group g ==> Group (sgbINTER g)
   subgroup_big_intersect_subgroup   |- !g. Group g ==> sgbINTER g <= g

   Subset Group:
   subset_group_def        |- !g s. subset_group g s = <|carrier := s; op := $*; id := #e|>
   subset_group_property   |- !g s. ((subset_group g s).carrier = s) /\
                                    ((subset_group g s).op = $* ) /\
                                    ((subset_group g s).id = #e)
   subset_group_exp        |- !g s x. x IN s ==> !n. (subset_group g s).exp x n = x ** n
   subset_group_order      |- !g s x. x IN s ==> (order (subset_group g s) x = ord x)
   subset_group_submonoid  |- !g s. Monoid g /\ #e IN s /\ s SUBSET G /\
                                    (!x y. x IN s /\ y IN s ==> x * y IN s) ==>
                                    subset_group g s << g
   subset_group_subgroup   |- !g s. Group g /\ s <> {} /\ s SUBSET G /\
                                    (!x y. x IN s /\ y IN s ==> x * |/ y IN s) ==>
                                    subset_group g s <= g
*)
(* ------------------------------------------------------------------------- *)
(* Subgroup of a Group.                                                      *)
(* ------------------------------------------------------------------------- *)

(* A Subgroup is a subset of a group that's a group itself, keeping op, id, inv. *)
val Subgroup_def = Define `
  Subgroup (h:'a group) (g:'a group) <=>
    Group h /\ Group g /\
    H SUBSET G /\ (h.op = g.op)
`;

(* Overload Subgroup *)
val _ = overload_on ("<=", ``Subgroup``);
(* already an infix symbol *)

(* Note: The requirement $o = $* is stronger than the following:
val _ = overload_on ("<<", ``\(h g):'a group. Group g /\ Group h /\ subgroup h g``);
Since subgroup h g is based on GroupHomo I g h, which only gives
!x y. x IN H /\ y IN H ==> (h.op x y = x * y))

This is not enough to satisfy monoid_component_equality,
hence cannot prove: h << g /\ g << h ==> h = g
*)

(*
val subgroup_property = save_thm(
  "subgroup_property",
  Subgroup_def
      |> SPEC_ALL
      |> REWRITE_RULE [ASSUME ``h:'a group <= g``]
      |> CONJUNCTS
      |> (fn thl => List.take(thl, 2) @ List.drop(thl, 3))
      |> LIST_CONJ
      |> DISCH_ALL
      |> Q.GEN `h` |> Q.GEN `g`);
val subgroup_property = |- !g h. h <= g ==> Group h /\ Group g /\ (h.op = $* )
*)

(* Theorem: properties of subgroup *)
(* Proof: Assume h <= g, then derive all consequences of definition *)
val subgroup_property = store_thm(
  "subgroup_property",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))``,
  rw_tac std_ss[Subgroup_def]);

(* Theorem: elements in subgroup are also in group. *)
(* Proof: since subgroup carrier is a subset of group carrier. *)
val subgroup_element = store_thm(
  "subgroup_element",
  ``!(g:'a group) (h:'a group). h <= g ==> !z. z IN H ==> z IN G``,
  rw_tac std_ss[Subgroup_def, SUBSET_DEF]);

(* Theorem: A subgroup h of g implies identity is a homomorphism from h to g.
        or  h <= g ==> Group h /\ Group g /\ GroupHomo I h g  *)
(* Proof: check definitions. *)
val subgroup_homomorphism = store_thm(
  "subgroup_homomorphism",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g /\ subgroup h g``,
  rw_tac std_ss[Subgroup_def, subgroup_def, GroupHomo_def, SUBSET_DEF]);

(* original:
g `!(g:'a group) h. h <= g = Group h /\ Group g /\ subgroup h g`;
e (rw_tac std_ss[Subgroup_def, subgroup_def, GroupHomo_def, SUBSET_DEF, EQ_IMP_THM]);

The only-if part (<==) cannot be proved:
Note Subgroup_def uses h.op = g.op,
but subgroup_def uses homomorphism I, and so cannot show this for any x y.
*)

(* Theorem: h <= g ==> H SUBSET G *)
(* Proof: by Subgroup_def *)
val subgroup_carrier_subset = store_thm(
  "subgroup_carrier_subset",
  ``!(g:'a group) h. h <= g ==> H SUBSET G``,
  rw[Subgroup_def]);

(* Theorem: h <= g ==> (h.op = $* ) *)
(* Proof: by Subgroup_def *)
val subgroup_op = store_thm(
  "subgroup_op",
  ``!(g:'a group) h. h <= g ==> (h.op = g.op)``,
  rw[Subgroup_def]);

(* Theorem: h <= g ==> h.id = #e *)
(* Proof:
   Since h.id IN H    by group_id_element
     h.id * h.id
   = h.op h.id h.id   by Subgroup_def
   = h.id             by group_id_id
   But h.id IN G      by SUBSET_DEF
   hence h.id = #e    by group_id_fix
   or
   by group_homo_id and subgroup_homomorphism.
*)
val subgroup_id = store_thm(
  "subgroup_id",
  ``!g h. h <= g ==> (h.id = #e)``,
  rpt strip_tac >>
  `!x. I x = x` by rw[] >>
  metis_tac[group_homo_id, subgroup_homomorphism, subgroup_def]);

(* Theorem: h <= g ==> h.inv x = |/x *)
(* Proof: by group_homo_inv and subgroup_homomorphism. *)
val subgroup_inv = store_thm(
  "subgroup_inv",
  ``!g h. h <= g ==> !x. x IN H ==> (h.inv x = |/ x)``,
  rpt strip_tac >>
  `!x. I x = x` by rw[] >>
  metis_tac[group_homo_inv, subgroup_homomorphism, subgroup_def]);

(* Theorem: h <= g ==> Group g /\ Group h *)
(* Proof: by Subgroup_def *)
val subgroup_has_groups = store_thm(
  "subgroup_has_groups",
  ``!g:'a group h. h <= g ==> Group g /\ Group h``,
  metis_tac[Subgroup_def]);

(* Theorem: h <= g ==> Group h *)
(* Proof: by Subgroup_def *)
val subgroup_is_group = store_thm(
  "subgroup_is_group",
  ``!g:'a group h. h <= g ==> Group h``,
  metis_tac[Subgroup_def]);

(* Theorem: h <= g ==> h << g *)
(* Proof:
   Since h <= g ==> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )  by Subgroup_def
   To satisfy Submonoid_def, need to show:
   (1) Group h ==> Monoid h, true by group_is_monoid
   (2) Group g ==> Monoid g, true by group_is_monoid
   (3) h <= g ==> h.id = #e, true by subgroup_id
*)
val subgroup_is_submonoid = store_thm(
  "subgroup_is_submonoid",
  ``!(g:'a group) h. h <= g ==> h << g``,
  rpt strip_tac >>
  `Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )` by metis_tac[Subgroup_def] >>
  rw_tac std_ss[Submonoid_def] >| [
    rw[],
    rw[],
    rw[subgroup_id]
  ]);

(* Theorem: h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n *)
(* Proof: by subgroup_is_submonoid, submonoid_exp *)
val subgroup_exp = store_thm(
  "subgroup_exp",
  ``!(g:'a group) h. h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n``,
  rw_tac std_ss[subgroup_is_submonoid, submonoid_exp]);

(* Theorem: h <= g <=> H <> {} /\ H SUBSET G /\ h.op = g.op /\ h.id = #e /\ !x y IN H, x * |/ y IN H *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group h ==> H <> {}
       True by group_id_element.
   (2) h <= g ==> h.id = #e
       True by subgroup_id.
   (3) Group h /\ x IN H /\ y IN H ==> x * |/ y IN H
       Since y IN H ==> |/ y IN H     by group_inv_element, subgroup_inv
       Hence x * |/ y IN H            by group_op_element
   (4) H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H ==> Group h
       Put y = x, x * |/ x = #e   IN H                  by group_rinv
       Put x = #e, y IN H ==> #e * |/ y = |/ y IN H     by group_lid
       x * y = x * |/ ( |/ y) IN H                      by group_inv_inv
       Verify by group_def_alt.
*)
val subgroup_alt = store_thm(
  "subgroup_alt",
  ``!g:'a group. Group g ==>
      !h. h <= g <=> (H <> {} /\ H SUBSET G /\ (h.op = g.op) /\ (h.id = #e) /\
                      !x y. x IN H /\ y IN H ==> x * |/ y IN H)``,
  rw[Subgroup_def, EQ_IMP_THM] >-
  metis_tac[group_id_element, MEMBER_NOT_EMPTY] >-
  rw[subgroup_id, Subgroup_def] >-
  metis_tac[group_inv_element, group_op_element, subgroup_inv, Subgroup_def] >>
  `?x. x IN H` by rw[MEMBER_NOT_EMPTY] >>
  `!x. x IN H ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `#e IN H` by metis_tac[group_rinv] >>
  `!y. y IN H ==> |/ y IN H` by metis_tac[group_lid, group_inv_element] >>
  `!x y. x IN H /\ y IN H ==> x * y IN H` by metis_tac[group_inv_inv] >>
  rw[group_def_alt] >-
  rw[group_assoc] >>
  metis_tac[group_linv]);

(* Theorem: h <= g <=>
       (Group g /\  (h.op = g.op) /\ (h.id = #e) /\
        H <> {} /\ H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H) *)
(* Proof: by Subgroup_def, subgroup_alt *)
val subgroup_thm = store_thm(
  "subgroup_thm",
  ``!g:'a group h. h <= g <=>
       (Group g /\  (h.op = g.op) /\ (h.id = #e) /\
        H <> {} /\ H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H)``,
  metis_tac[subgroup_alt, Subgroup_def]);

(* Theorem: h <= g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Group g /\ Group h /\ subgroup h g    by subgroup_homomorphism, h <= g
   Thus !x. x IN H ==> (order h x = ord x)    by subgroup_order_eqn
*)
val subgroup_order = store_thm(
  "subgroup_order",
  ``!g:'a group h. h <= g ==> !x. x IN H ==> (order h x = ord x)``,
  metis_tac[subgroup_homomorphism, subgroup_order_eqn]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Theorems                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: g <= g *)
(* Proof: by definition, this is to show:
   G SUBSET G, true by SUBSET_REFL.
*)
val subgroup_refl = store_thm(
  "subgroup_refl",
  ``!g:'a group. Group g ==> g <= g``,
  rw[Subgroup_def]);

(* Theorem: h <= g /\ g <= h ==> (h = g) *)
(* Proof:
   By monoid_component_equality, this is to show:
   (1) h <= g /\ g <= h ==> H = G
       By Subgroup_def, H SUBSET G /\ G SUBSET H,
       hence true by SUBSET_ANTISYM.
   (2) h <= g /\ g <= h ==> h.op = $*
       True by Subgroup_def.
   (3) h <= g /\ g <= h ==> h.id = #e
*)
val subgroup_antisym = store_thm(
  "subgroup_antisym",
  ``!(g:'a group) (h:'a group). h <= g /\ g <= h ==> (h = g)``,
  metis_tac[monoid_component_equality, Subgroup_def, SUBSET_ANTISYM, subgroup_id]);

(* Theorem: h <= t /\ t <= g ==> h <= g *)
(* Proof: by definition, this is to show:
   H SUBSET t.carrier /\ t.carrier SUBSET G ==> H SUBSET G
   True by SUBSET_TRANS.
*)
val subgroup_trans = store_thm(
  "subgroup_trans",
  ``!(g:'a group) (h:'a group) (t:'a group). h <= t /\ t <= g ==> h <= g``,
  rw[Subgroup_def] >>
  metis_tac[SUBSET_TRANS]);

(* Theorem: FiniteGroup g ==> !h. h <= g ==> FINITE H *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G               by FiniteGroup_def
     and h <= g ==> Group h /\ H SUBSET G  by Subgroup_def
   Hence FINITE H                          by SUBSET_FINITE
*)
val finite_subgroup_carrier_finite = store_thm(
  "finite_subgroup_carrier_finite",
  ``!g:'a group. FiniteGroup g ==> !h. h <= g ==> FINITE H``,
  metis_tac[FiniteGroup_def, Subgroup_def, SUBSET_FINITE]);

(* Theorem: FiniteGroup g ==> !h. h <= g ==> FiniteGroup h *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G               by FiniteGroup_def
     and h <= g ==> Group h /\ H SUBSET G  by Subgroup_def
   Hence FINITE H                          by SUBSET_FINITE
    thus FiniteGroup h                     by FiniteGroup_def
*)
val finite_subgroup_finite_group = store_thm(
  "finite_subgroup_finite_group",
  ``!g:'a group. FiniteGroup g ==> !h. h <= g ==> FiniteGroup h``,
  metis_tac[FiniteGroup_def, Subgroup_def, SUBSET_FINITE]);

(* Theorem: AbelianGroup g /\ h <= g ==> AbelianGroup h *)
(* Proof:
   Note AbelianGroup g
    <=> Group g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)  by AbelianGroup_def
   Also h <= g
    <=> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )       by Subgroup_def
   With Group h              by above
    and !x y. x IN H /\ y IN H
    ==> x IN G /\ y IN G              by SUBSET_DEF
    ==> x * y = y * x                 by above, commutativity
    ==> h.op x y = h.op y x           by above, h.op = $*
   Thus AbelianGroup h                by AbelianGroup_def
*)
val abelian_subgroup_abelian = store_thm(
  "abelian_subgroup_abelian",
  ``!(g:'a group) h. AbelianGroup g /\ h <= g ==> AbelianGroup h``,
  rw_tac std_ss[AbelianGroup_def, Subgroup_def, SUBSET_DEF]);

(* Theorem: h <= g ==> Group h /\ Group g *)
(* Proof: by subgroup_property *)
val subgroup_groups = store_thm(
  "subgroup_groups",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g``,
  metis_tac[subgroup_property]);

(* Theorem: h <= g ==> Group g /\ Group h /\ H <> {} /\ H SUBSET G /\ (h.op = $* ) /\ (h.id = #e) /\
                       (!x. x IN H ==> (h.inv x = |/ x)) /\
                       (!x y. x IN H /\ y IN H ==> x * ( |/ y) IN H) *)
(* Proof: by subgroup_property, subgroup_alt, subgroup_inv *)
val subgroup_property_all = store_thm(
  "subgroup_property_all",
  ``!(g:'a group) h. h <= g ==> Group g /\ Group h /\
    H <> {} /\ H SUBSET G /\ (h.op = g.op ) /\ (h.id = #e) /\
    (!x. x IN H ==> (h.inv x = |/ x)) /\
    (!x y. x IN H /\ y IN H ==> x * ( |/ y) IN H)``,
  metis_tac[subgroup_property, subgroup_inv, subgroup_alt]);

(* Theorem: h <= g ==> !x y. x IN H /\ y IN H ==> x * |/ y IN H *)
(* Proof: by subgroup_property_all *)
val subgroup_inv_closure = store_thm(
  "subgroup_inv_closure",
  ``!(g:'a group) h. h <= g ==> !x y. x IN H /\ y IN H ==> x * ( |/ y) IN H``,
  rw[subgroup_property_all]);

(* Theorem: h <= g ==> H <> {} *)
(* Proof: by subgroup_property_all, or
     h <= g ==> Group h     by Subgroup_def
            ==> H <> {}     by group_carrier_nonempty
*)
val subgroup_carrier_nonempty = store_thm(
  "subgroup_carrier_nonempty",
  ``!(g:'a group) h. h <= g ==> H <> {}``,
  rw[Subgroup_def, group_carrier_nonempty]);

(* Theorem: h <= g /\ (H = G) ==> (h = g) *)
(* Proof:
   By subgroup_antisym, this is to show:
   Note Group h /\ Group g         by subgroup_groups
   Note (1) G <> {}, true          by group_carrier_nonempty
        (2) $* = h.op, true        by subgroup_alt
        (3) #e = h.id, true        by subgroup_alt
        (4) x IN G /\ y IN G ==> h.op x (h.inv y) IN G,
            This is true           by subgroup_alt, subgroup_inv, group_op_element
   Thus g <= h.
   With given h <= g, h = g        by subgroup_antisym
*)
val subgroup_eq_carrier = store_thm(
  "subgroup_eq_carrier",
  ``!(g:'a group) h. h <= g /\ (H = G) ==> (h = g)``,
  rpt strip_tac >>
  (irule subgroup_antisym >> rpt conj_tac) >| [
    `Group h /\ Group g` by metis_tac[subgroup_groups] >>
    rw[subgroup_alt] >-
    rw[group_carrier_nonempty] >-
    metis_tac[subgroup_alt] >-
    metis_tac[subgroup_alt] >>
    metis_tac[subgroup_alt, subgroup_inv, group_op_element],
    rw[]
  ]);

(* Theorem: h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier)) *)
(* Proof:
   Note h1 <= g ==> h1.op = g.op /\ h1.id = #e    by subgroup_op, subgroup_id
    and h2 <= g ==> h2.op = g.op /\ h2.id = #e    by subgroup_op, subgroup_id
   Thus (h1 = h2) <=> (h1.carrier = h2.carrier)   by monoid_component_equality
*)
val subgroup_eq = store_thm(
  "subgroup_eq",
  ``!g:'a group. !h1 h2. h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier))``,
  metis_tac[subgroup_op, subgroup_id, monoid_component_equality]);

(* ------------------------------------------------------------------------- *)
(* Cosets, especially cosets of a subgroup.                                  *)
(* ------------------------------------------------------------------------- *)

(* Define (left) coset of subgroup with an element a. *)
val coset_def = Define `
  coset (g:'a group) a X = IMAGE (\z. a * z) X
`;

(* val _ = export_rewrites ["coset_def"]; *)

(* Define left coset of subgroup with an element a. *)
val left_coset_def = Define `
  left_coset (g:'a group) X a = coset g a X
`;

(* Define right coset of subgroup with an element a. *)
val right_coset_def = Define `
  right_coset (g:'a group) X a = IMAGE (\z. z * a) X
`;

(* set overloading after all above defintions. *)
val _ = overload_on ("*", ``coset g``);
val _ = overload_on ("*", ``right_coset g``);

(* Derive theorems. *)
val coset_alt = save_thm("coset_alt",
    coset_def |> SIMP_RULE bool_ss [IMAGE_DEF]);
(* val coset_alt = |- !g a X. a * X = {a * z | z IN X}: thm *)

val left_coset_alt = save_thm("left_coset_alt",
    left_coset_def |> REWRITE_RULE [coset_alt]);
(* val left_coset_alt = |- !g X a. left_coset g X a = {a * z | z IN X}: thm *)

val right_coset_alt = save_thm("right_coset_alt",
    right_coset_def |> SIMP_RULE bool_ss [IMAGE_DEF]);
(* val right_coset_alt = |- !g X a. X * a = {z * a | z IN X}: thm *)

(* Theorem: a * X SUBSET G *)
(* Proof: by definition. *)
val coset_property = store_thm(
  "coset_property",
  ``!(g:'a group) a. Group g /\ a IN G ==> !X. X SUBSET G ==> a * X SUBSET G``,
  rw[coset_def, SUBSET_DEF] >>
  metis_tac[group_op_element]);

(* Theorem: a * {} = {} *)
(* Proof: by definition. *)
val coset_empty = store_thm(
  "coset_empty",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * {} = {})``,
  rw[coset_def]);

(* Theorem: For x IN a * X <=> ?y IN X /\ x = a * y *)
(* Proof: by coset_def, x is IN IMAGE.
   Essentially this is to prove:
     z IN X <=> ?y. y IN X /\ (a * z = a * y)
   Take y = z.
*)
val coset_element = store_thm(
  "coset_element",
  ``!(g:'a group) X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)``,
  rw[coset_def] >>
  metis_tac[]);

(* Theorem alias *)
val in_coset = save_thm("in_coset", coset_element);
(*
val in_coset = |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y): thm
*)

(* Theorem: Group g, a IN G ==> a * G = G *)
(* Proof:
   By closure property of g.op.
   This is to prove:
   (1) a * z IN G, true by group_op_element.
   (2) ?z. (x = a * z) /\ z IN G, true by z = |/a * x, from group_rsolve.
*)
val group_coset_eq_itself = store_thm(
  "group_coset_eq_itself",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * G = G)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >>
  qexists_tac `|/a * x` >>
  rw[group_linv_assoc]);

(* Theorem: [Cosets of a group are permutations]
            (a * G) = G *)
(* Proof:
   Essentially this is to prove:
   (1) a IN G /\ x IN G ==> a*x IN G, true by group_op_element
   (2) a IN G /\ x IN G ==> ?z. (x = a * z) /\ z IN G, true by group_rsolve
*)
val group_coset_is_permutation = store_thm(
  "group_coset_is_permutation",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * G = G)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >| [
    rw_tac std_ss[group_op_element] >>
    rw[],
    `|/ a * x IN G` by rw[] >>
    metis_tac[group_rsolve]
  ]);

(* Theorem: Group g, h <= g, a IN G /\ x IN a * H ==> x IN G *)
(* Proof:
   Coset contains all  x = a*z  where a IN G and z IN H, so x IN G by group_op_element.
*)
val subgroup_coset_subset = store_thm(
  "subgroup_coset_subset",
  ``!(g:'a group) (h:'a group) a x. h <= g /\ a IN G /\ x IN a * H ==> x IN G``,
  rw_tac std_ss[coset_def, Subgroup_def, SUBSET_DEF, IMAGE_DEF, GSPECIFICATION] >>
  rw_tac std_ss[group_op_element]);

(* Theorem: For all x IN H, a * x IN a * H. *)
(* Proof: by coset definition
   or to prove: ?z. (a * x = a * z) /\ z IN H. Take z = x.
*)
val element_coset_property = store_thm(
  "element_coset_property",
  ``!(g:'a group) X a. a IN G ==> !x. x IN X ==> a * x IN a * X``,
  rw[coset_def]);

(* Theorem: For h <= g, x IN x * H *)
(* Proof:
   Since #e IN H   by subgroup_id
   and x * #e = x  by group_rid
   Essentially this is to prove:
   (1) ?z. (x = x * z) /\ z IN H, true by z = #e.
*)
val subgroup_coset_nonempty = store_thm(
  "subgroup_coset_nonempty",
  ``!(g:'a group) h. h <= g ==> !x. x IN G ==> x IN x * H``,
  rw[coset_def] >>
  metis_tac[subgroup_id, group_rid, group_id_element, Subgroup_def]);

(* eliminate "group" from default simpset *)
(* val groupSS = diminish_srw_ss ["group"]; *)
(* val mySS = diminish_srw_ss ["subgroup"]; *)

(* Theorem: For h <= g, y IN x * H ==> ?z IN H /\ x = y * z *)
(* Proof:
   This is to prove:
   x * z IN G /\ z IN H ==> ?z'. z' IN H /\ (x = x * z * z')
   Just take z' = |/z.
*)
val subgroup_coset_relate = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ y IN x * H ==> ?z. z IN H /\ (x = y * z)``,
  rw[coset_def] >>
  metis_tac[subgroup_inv, group_rinv_assoc, subgroup_element, group_inv_element, Subgroup_def]);

(* Theorem: For h <= g, |/y * x in H ==> x * H = y * H. *)
(* Proof:
   Essentially this is to prove:
   (1) |/ y * x IN H /\ z IN H ==> ?z'. (x * z = y * z') /\ z' IN H
       Solving, z' = |/y * (x * z) = ( |/y * x) * z, in H by group_op_element.
   (2) |/ y * x IN H /\ z IN H ==> ?z'. (y * z = x * z') /\ z' IN H
       Solving, z' = |/x * (y * z) = ( |/x * y) * z, and |/( |/y * x) = |/x * y IN H.
*)
val subgroup_coset_eq1 = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ ( |/y * x) IN H ==> (x * H = y * H)``,
  rpt strip_tac >>
  `Group h /\ Group g /\ !x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[Subgroup_def] >>
  rw[coset_def, EXTENSION, EQ_IMP_THM] >| [
    `z IN G` by metis_tac[subgroup_element] >>
    `y * ( |/y * x * z) = x * z` by rw[group_assoc, group_linv_assoc] >>
    metis_tac[group_op_element],
    `z IN G` by metis_tac[subgroup_element] >>
    `x * ( |/x * y * z) = y * z` by rw[group_assoc, group_linv_assoc] >>
    `|/( |/y * x) = |/x * y` by rw[group_inv_op] >>
    metis_tac[subgroup_inv, group_inv_element, group_op_element]
  ]);

(* Theorem: For h <= g, x * H = y * H ==> |/y * x in H. *)
(* Proof:   Since y IN y * H, always, by subgroup_coset_nonempty.
   we have y IN x * H, since the cosets are equal.
   hence ?z IN H /\  x = y * z  by subgroup_coset_relate.
   Solving, z = |/y * x, and z IN H.
*)
val subgroup_coset_eq2 = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ (x * H = y * H) ==> ( |/y * x) IN H``,
  rpt strip_tac >>
  `y IN x * H` by rw_tac std_ss[subgroup_coset_nonempty] >>
  `?z. z IN H /\ (x = y * z)` by rw_tac std_ss[subgroup_coset_relate] >>
  metis_tac[group_rsolve, Subgroup_def, subgroup_element]);

(* Theorem: For h <= g, x * H = y * H iff |/y * x in H *)
(* Proof:
   By subgroup_coset_eq1 and subgroup_coset_eq2.
*)
val subgroup_coset_eq = store_thm(
  "subgroup_coset_eq",
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> |/y * x IN H)``,
  metis_tac[subgroup_coset_eq1, subgroup_coset_eq2]);

(* Theorem: There is a bijection between subgroup and its cosets. *)
(* Proof:
   Essentially this is to prove:
   (1) x IN H ==> a * x IN a * H
       True by element_coset_property.
   (2) x IN H /\ x' IN H /\ a * x = a * x' ==> x = x'
       True by group_lcancel.
   (3) same as (1)
   (4) x IN a * H ==> ?x'. x' IN H /\ (a * x' = x)
       True by coset_element.
*)
val subgroup_to_coset_bij = store_thm(
  "subgroup_to_coset_bij",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> BIJ (\x. a * x) H (a * H)``,
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF, element_coset_property] >| [
    metis_tac[group_lcancel, subgroup_element, Subgroup_def],
    metis_tac[coset_element]
  ]);

(* Theorem: All cosets of subgroup are of the same size as the subgroup *)
(* Proof:
   Due to BIJ (\x. a*x) H (a * H), and sets are FINITE.
*)
(* Note: An infinite group can have a finite subgroup, e.g. the units of complex multiplication. *)
val subgroup_coset_card = store_thm(
  "subgroup_coset_card",
  ``!(g:'a group) h. h <= g /\ FINITE H  ==> !a. a IN G ==> (CARD (a * H) = CARD H)``,
  rpt strip_tac >>
  `BIJ (\x. a * x) H (a * H)` by rw_tac std_ss[subgroup_to_coset_bij] >>
  `FINITE (a * H)` by rw[coset_def] >>
  metis_tac[FINITE_BIJ_CARD_EQ]);

(* ------------------------------------------------------------------------- *)
(* Lagrange's Theorem by Subgroups and Cosets                                *)
(* ------------------------------------------------------------------------- *)

(* From subgroup_coset_card:
   `!g h a. Group g /\ h <= g /\ a IN G /\ FINITE H ==> (CARD (a * H) = CARD (H))`

   This can be used directly to prove Lagrange's Theorem for subgroup.
*)

(* Theorem: (Lagrange Theorem) For FINITE Group g, size of subgroup divides size of group. *)
(* Proof:
   For the action g.op h G

     CARD G
   = SIGMA CARD (TargetPartition g.op h G)  by CARD_TARGET_BY_PARTITION
   = (CARD H) * CARD (TargetPartition g.op h G)
           by SIGMA_CARD_CONSTANT, and (CARD e = CARD H) from CARD_subgroup_partition

   Hence (CARD H) divides (CARD G).
*)

(* Define b ~ a  when  b IN (a * H) *)
val inCoset_def = Define `
  inCoset (g:'a group) (h:'a group) a b <=> b IN (a * H)
`;

(* Theorem: inCoset is Reflexive:
            h <= g /\ a IN G ==> inCoset g h a a *)
(* Proof:
   Follows from subgroup_coset_nonempty.
*)
val inCoset_refl = store_thm(
  "inCoset_refl",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> inCoset g h a a``,
  rw_tac std_ss[inCoset_def, subgroup_coset_nonempty]);

(* Theorem: inCoset is Symmetric:
            h <= g /\ a IN G /\ b IN G ==> (inCoset g h a b ==> inCoset g h b a) *)
(* Proof:
       inCoset g h a b
   ==> b IN (a * H)          by definition
   ==> ?z in H. b = a * z    by coset_element
   ==> |/z in H              by h <= g, group_inv_element
   ==> b * ( |/z) = (a * z) * ( |/z)
                  = a        by group_rinv_assoc
   The result follows        by element_coset_property:
   !x. x IN H ==> b * x IN b * H  -- take x = |/z.
*)
val inCoset_sym = store_thm(
  "inCoset_sym",
  ``!(g:'a group) h. h <= g ==> !a b. a IN G /\ b IN G /\ inCoset g h a b ==> inCoset g h b a``,
  rw_tac std_ss[inCoset_def] >>
  `Group h/\ Group g /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `?z. z IN H /\ (b = a * z)` by rw_tac std_ss[GSYM coset_element] >>
  `|/z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
  metis_tac[element_coset_property, group_rinv_assoc]);

(* Theorem: inCoset is Transitive:
            h <= g /\ a IN G /\ b IN G /\ c IN G
            ==> (inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c) *)
(* Proof:
       inCoset g h a b
   ==> b IN (a * H)          by definition
   ==> ?y in H. b = a * y    by coset_element

       inCoset g h b c
   ==> c IN (b * H)          by definition
   ==> ?z in H. c = b * z    by coset_element

   Hence  c = b * z
            = (a * y)* z
            = a * (y * z)    by group_assoc
   Since y * z in H          by group_op_element
   Hence  c IN (a * H), the result follows from element_coset_property.
*)
val inCoset_trans = store_thm(
  "inCoset_trans",
  ``!(g:'a group) h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\ inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c``,
  rw_tac std_ss[inCoset_def] >>
  `Group h /\ Group g /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `?y. y IN H /\ (b = a * y) /\ ?z. z IN H /\ (c = b * z)` by rw_tac std_ss[GSYM coset_element] >>
  `c = a * (y * z)` by rw[group_assoc] >>
  metis_tac[element_coset_property, group_op_element, subgroup_property]);

(* Theorem: inCoset is an equivalence relation.
            Group g /\ h <= g ==> (inCoset g h) is an equivalent relation on G. *)
(* Proof:
   By inCoset_refl, inCoset_sym, and inCoset_trans.
*)
val inCoset_equiv_on_carrier = store_thm(
  "inCoset_equiv_on_carrier",
  ``!(g:'a group) h. h <= g ==> inCoset g h equiv_on G``,
  rw_tac std_ss[equiv_on_def] >>
  metis_tac[inCoset_refl, inCoset_sym, inCoset_trans]);

(* Define coset partitions of G by inCoset g h. *)
val CosetPartition_def = Define `
  CosetPartition g h = partition (inCoset g h) G
`;

(* Theorem: For FINITE Group g, h <= g ==>
            CARD G = SUM of CARD partitions in (CosetPartition g h) *)
(* Proof:
   Apply partition_CARD
    |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val carrier_card_by_coset_partition = store_thm(
  "carrier_card_by_coset_partition",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (CosetPartition g h))``,
  rw_tac std_ss[CosetPartition_def, inCoset_equiv_on_carrier, partition_CARD]);

(* Theorem: Elements in CosetPartition are cosets of some a In G *)
(* Proof:
   By definition, this is to show:
   h <= g /\ x IN G ==> ?a. a IN G /\ ({y | y IN G /\ y IN x * H} = a * H)
   Let a = x, then need to show: {y | y IN G /\ y IN x * H} = x * H
   Since y IN x * H ==> ?z. z IN H /\ (y = x * z)
   so need to show: x IN G /\ z IN G ==> y IN G, which is true by group_op_element.
*)
val coset_partition_element = store_thm(
  "coset_partition_element",
  ``!(g:'a group) h. h <= g ==> (!e. e IN CosetPartition g h <=> ?a. a IN G /\ (e = a * H))``,
  rpt strip_tac >>
  `!x z. x IN G /\ z IN H ==> x * z IN G` by metis_tac[group_op_element, Subgroup_def, subgroup_element] >>
  rw[CosetPartition_def, inCoset_def, partition_def, EQ_IMP_THM,
     coset_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For FINITE group, CARD element in CosetPartiton = CARD subgroup. *)
(* Proof:
   By coset_partition_element and subgroup_coset_card
*)
val coset_partition_element_card = store_thm(
  "coset_partition_element_card",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> !e. e IN CosetPartition g h ==> (CARD e = CARD H)``,
  metis_tac[coset_partition_element, subgroup_coset_card, Subgroup_def, SUBSET_FINITE]);

(* Theorem: (Lagrange Identity)
            For FINITE Group g and subgroup h,
            (size of group) = (size of subgroup) * (size of coset partition). *)
(* Proof:
   Since
   !e. e IN CosetPartition g h ==> (CARD e = CARD H)  by coset_partition_element_card

   CARD G
   = SIGMA CARD (CosetPartition g h)     by carrier_card_by_coset_partition
   = CARD H * CARD (CosetPartition g h)  by SIGMA_CARD_CONSTANT
*)
val Lagrange_identity = store_thm(
  "Lagrange_identity",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (CosetPartition g h))``,
  rpt strip_tac >>
  `FINITE (CosetPartition g h)` by metis_tac[CosetPartition_def, inCoset_equiv_on_carrier, FINITE_partition] >>
  metis_tac[carrier_card_by_coset_partition, SIGMA_CARD_CONSTANT, coset_partition_element_card]);

(* Theorem: (Coset Partition size)
            For FINITE Group g, size of coset partition = (size of group) div (size of subgroup). *)
(* Proof:
   By Lagrange_identity and MULT_DIV.
*)
val coset_partition_card = store_thm(
  "coset_partition_card",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD (CosetPartition g h) = CARD G DIV CARD H)``,
  rpt strip_tac >>
  `Group h /\ FINITE H` by metis_tac[Subgroup_def, SUBSET_FINITE] >>
  `0 < CARD H` by metis_tac[group_id_element, MEMBER_NOT_EMPTY, CARD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[Lagrange_identity, MULT_DIV, MULT_SYM]);

(* Theorem: (Lagrange Theorem)
            For FINITE Group g, size of subgroup divides size of group. *)
(* Proof:
   By Lagrange_identity and divides_def.
*)
val Lagrange_thm = store_thm(
  "Lagrange_thm",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD H) divides (CARD G)``,
  metis_tac[Lagrange_identity, MULT_SYM, dividesTheory.divides_def]);

(* ------------------------------------------------------------------------- *)
(* Alternate proof without using inCoset.                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Subgroup Coset membership is Symmetric:
            Group g /\ h <= g /\ a IN G /\ b IN G
            ==> b IN a * H ==> a IN b * H
   Proof:
       b IN (a * H)
   ==> ?z in H. b = a * z    by coset_element
   ==> |/z in H              by h <= g, group_inv_element
   ==> b * ( |/z) = (a * z) * ( |/z) = a
                             by group_rinv_assoc
   The result follows by element_coset_property:
   !x. x IN H ==> b * x IN b * H  -- take x = |/z.
*)
val subgroup_coset_sym = store_thm(
  "subgroup_coset_sym",
  ``!(g:'a group) h. h <= g ==> !a b. a IN G /\ b IN G /\ b IN (a * H) ==> a IN (b * H)``,
  rpt strip_tac >>
  `?z. z IN H /\ (b = a * z)` by rw_tac std_ss[GSYM coset_element] >>
  `Group g /\ Group h` by metis_tac[Subgroup_def] >>
  `|/ z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
  `z IN G /\ |/ z IN G` by metis_tac[subgroup_element] >>
  `b * |/ z = a` by rw_tac std_ss[group_rinv_assoc] >>
  metis_tac[element_coset_property]);

(* Theorem: Subgroup Coset membership is Transitive:
            Group g /\ h <= g /\ a IN G /\ b IN G /\ c IN G
            ==> b IN (a * H) /\ c IN (b * H) ==> c IN (a * H)
   Proof:
       b IN (a * H)          by definition
   ==> ?y in H. b = a * y    by coset_element
       c IN (b * H)          by definition
   ==> ?z in H. c = b * z    by coset_element

   Hence  c = b * z
            = (a * y)* z
            = a * (y * z)    by group_assoc
   Since y * z in H          by group_op_element
   Hence  c IN (a * H), the result follows from element_coset_property.
*)
val subgroup_coset_trans = store_thm(
  "subgroup_coset_trans",
  ``!(g:'a group) h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\ b IN (a * H) /\ c IN (b * H) ==> c IN (a * H)``,
  rpt strip_tac >>
  `?y. y IN H /\ (b = a * y) /\ ?z. z IN H /\ (c = b * z)` by rw_tac std_ss[GSYM coset_element] >>
  `Group g /\ Group h /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))` by metis_tac[subgroup_property] >>
  `y IN G /\ z IN G` by metis_tac[subgroup_element] >>
  `c = a * (y * z)` by rw_tac std_ss[group_assoc] >>
  `y * z IN H` by metis_tac[group_op_element] >>
  rw_tac std_ss[element_coset_property]);

(* Theorem: inCoset is an equivalence relation.
            h <= g ==> (inCoset g h) is an equivalent relation on G. *)
(* Proof:
   By subgroup_coset_nonempty, subgroup_coset_sym, and subgroup_coset_trans.
*)
val subgroup_incoset_equiv = store_thm(
  "subgroup_incoset_equiv",
  ``!(g:'a group) h. h <= g ==> (left_coset g H) equiv_on G``,
  rw_tac std_ss[left_coset_def, equiv_on_def] >| [
    metis_tac[subgroup_coset_nonempty, SPECIFICATION],
    metis_tac[subgroup_coset_sym, SPECIFICATION],
    metis_tac[subgroup_coset_trans, SPECIFICATION]
  ]);

(* Theorem: For FINITE Group g, h <= g ==>
            CARD G = SUM of CARD partitions by (left_coset g H) *)
(* Proof:
   Apply partition_CARD
    |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val carrier_card_by_subgroup_coset_partition = store_thm(
  "carrier_card_by_subgroup_coset_partition",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (partition (left_coset g H) G))``,
  rw_tac std_ss[subgroup_incoset_equiv, partition_CARD]);

(* Theorem: Elements in coset partition are cosets of some a In G *)
(* Proof:
   If-part: h <= g /\ e IN partition (left_coset g H) G ==> ?a. a IN G /\ (e = a * H)
      Since there is x such that x IN G /\ e = {y | y IN G /\ x * H y}  by partition_def
      Let a = x, need to show x * H = {y | y IN G /\ x * H y}
      This is true by SPECIFICATION.
   Only-if part: case: h <= g /\ a IN G ==> a * H IN partition (left_coset g H) G
      This is to show: ?x. x IN G /\ (a * H = {y | y IN G /\ x * H y})
      Let x = a, need to show a * H = {y | y IN G /\ a * H y}
      This is true by SPECIFICATION.
*)
val subgroup_coset_partition_element = store_thm(
  "subgroup_coset_partition_element",
  ``!(g:'a group) h. h <= g ==> (!e. e IN (partition (left_coset g H) G) <=> ?a. a IN G /\ (e = a * H))``,
  rpt strip_tac >>
  `!x z. x IN G /\ z IN H ==> x * z IN G` by metis_tac[Subgroup_def, SUBSET_DEF, group_op_element] >>
  rw[partition_def, EQ_IMP_THM, left_coset_def, coset_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For FINITE group, CARD element in subgroup coset partiton = CARD subgroup. *)
(* Proof:
   By subgroup_coset_partition_element and subgroup_coset_card
*)
val subgroup_coset_card_partition_element = store_thm(
  "subgroup_coset_card_partition_element",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> !e. e IN (partition (left_coset g H) G) ==> (CARD e = CARD H)``,
  rpt strip_tac >>
  `?a. a IN G /\ (e = a * H)` by rw_tac std_ss[GSYM subgroup_coset_partition_element] >>
  `FINITE H` by metis_tac[Subgroup_def, SUBSET_FINITE] >>
  metis_tac[subgroup_coset_card]);

(* Theorem: (Lagrange Identity)
            For FINITE Group g and subgroup h,
            (size of group) = (size of subgroup) * (size of coset partition). *)
(* Proof:
   Since
   !e. e IN coset partition g h ==> (CARD e = CARD H)  by subgroup_coset_card_partition_element

   CARD G
   = SIGMA CARD (CosetPartition g h)   by carrier_card_by_subgroup_coset_partition
   = CARD H * CARD (CosetPartition g h)  by SIGMA_CARD_CONSTANT
*)
val Lagrange_identity_alt = store_thm(
  "Lagrange_identity_alt",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (partition (left_coset g H) G))``,
  metis_tac[carrier_card_by_subgroup_coset_partition, subgroup_coset_card_partition_element,
             SIGMA_CARD_CONSTANT, FINITE_partition]);

(* ------------------------------------------------------------------------- *)
(* Useful Coset theorems.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: h <= g /\ x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h *)
(* Proof:
       x IN IMAGE (left_coset g H) G
   <=> ?y. y IN G /\ y = (left_coset g H) x   by IN_IMAGE
   <=> ?y. y IN G /\ y = x * H                by left_coset_def
   <=> x IN CosetPartition g h                   by coset_partition_element
*)
val subgroup_coset_in_partition = store_thm(
  "subgroup_coset_in_partition",
  ``!g h:'a group. h <= g ==> !x. x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h``,
  rw_tac std_ss[IN_IMAGE, left_coset_def, coset_partition_element] >>
  metis_tac[]);

(* Theorem: CosetPartition g h = IMAGE (left_coset g H) G *)
(* Proof:
      !e. e IN CosetPartition g h
   <=> ?a. a IN G /\ (e = a * H)      by coset_partition_element
   <=> e IN IMAGE (left_coset g H) G  by IN_IMAGE
*)
val coset_partition_eq_coset_image = store_thm(
  "coset_partition_eq_coset_image",
  ``!(g:'a group) h. h <= g ==> (CosetPartition g h = IMAGE (left_coset g H) G)``,
  rw[Once EXTENSION] >>
  metis_tac[left_coset_def, coset_partition_element]);

(* Theorem: #e * H = H *)
(* Proof:
     #e * H
   = IMAGE (\z. #e * z) H   by coset_def
   = IMAGE (\z. z) H        by group_lid, subgroup_id
   = H                      by IMAGE_ID
*)
Theorem coset_id_eq_subgroup:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  rw[coset_def, EXTENSION] >>
  metis_tac[subgroup_property, subgroup_id, group_lid, group_id_element]
QED

(* Michael's proof *)
Theorem IMAGE_ID_lemma[local]:
  (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)
Proof rw[EXTENSION] >> metis_tac[]
QED

Theorem coset_id_eq_subgroup[allow_rebind]:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  srw_tac[SatisfySimps.SATISFY_ss]
         [subgroup_property, subgroup_element, IMAGE_ID_lemma, coset_def]
QED

(* Rework of proof from outline:
   For the in-line IMAGE_ID', universally qualify all parameters :
   !f s. (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)
*)
Theorem coset_id_eq_subgroup[allow_rebind]:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  rpt strip_tac >>
  ‘!f s. (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)’
    by (rw[EXTENSION] >> metis_tac[]) >>
  ‘!x. x IN H ==> ((\z. #e * z) x = x)’
    by metis_tac[subgroup_property, subgroup_element, group_lid] >>
  full_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss)[coset_def]
QED

(* ------------------------------------------------------------------------- *)
(* Conjugate of sets and subgroups                                           *)
(* ------------------------------------------------------------------------- *)

(* Conjugate of a set s by a group element a in G is the set {a * z * |/a | z in s}. *)
val conjugate_def = Define `
  conjugate (g:'a group) (a: 'a) (s: 'a -> bool) = { a * z * |/a | z IN s}
`;

(* Conjugate of subgroup h <= g by a in G is the set {a * z * |/a | z in H}. *)
val conjugate_subgroup_def = Define `
  conjugate_subgroup (h:'a group) (g:'a group) a : 'a group =
      <| carrier := conjugate g a H;
              id := #e;
              op := g.op
       |>
`;
(* > val conjugate_subgroup_def =
  |- !h g a. conjugate_subgroup h g a = <|carrier := conjugate g a H; id := #e; op := $* |> : thm
*)

(*
- type_of ``conjugate_subgroup h g a``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: Group g, h <= g, a in G ==> Group (conjugate_subgroup h g a) *)
(* Proof:
   Closure: (a * z * |/a) * (a * z' * |/ a)
          = a * z * ( |/ a * a) * z' * |/ a
          = a * (z * z') * |/ a, and z * z' IN H.
   Associativity: inherits from group associativity
   Identity: #e in (conjugate_subgroup h g a) since #e IN H and a * #e * |/ a = #e.
   Inverse: |/ (a * z * |/a)
          = |/( |/a) * ( |/ z) * |/a
          = a * ( |/z) * |/a, and |/z IN H.
*)
val conjugate_subgroup_group = store_thm(
  "conjugate_subgroup_group",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> Group (conjugate_subgroup h g a)``,
  rpt strip_tac >>
  `Group h /\ Group g /\ !z. z IN H ==> z IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `#e IN H` by metis_tac[subgroup_id, group_id_element] >>
  `|/a IN G` by rw_tac std_ss[group_inv_element] >>
  `!p q. p IN G /\ q IN G ==> (a * p * |/ a * (a * q * |/ a) = a * (p * q) * |/a)` by
  (rpt strip_tac >>
  `a * p IN G /\ q * |/a IN G` by rw_tac std_ss[group_op_element] >>
  `a * p * |/ a * (a * q * |/ a) = a * p * ( |/ a * a * (q * |/ a))` by rw_tac std_ss[group_assoc, group_op_element] >>
  `_ = a * p * (q * |/a)` by rw_tac std_ss[group_linv, group_lid] >>
  rw_tac std_ss[group_assoc, group_op_element]) >>
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, group_def_alt, RES_FORALL_THM, RES_EXISTS_THM, GSPECIFICATION] >| [
    `z * z' IN H` by metis_tac[group_op_element, subgroup_property] >>
    metis_tac[],
    `!x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[group_op_element, subgroup_property] >>
    `a * z' * |/ a * (a * z'' * |/ a) * (a * z''' * |/ a) = a * (z' * z'') * |/ a * (a * z''' * |/ a)` by rw_tac std_ss[] >>
    `_ = a * ((z' * z'') * z''') * |/ a` by rw_tac std_ss[group_op_element] >>
    `_ = a * (z' * (z'' * z''')) * |/ a` by rw_tac std_ss[group_assoc] >>
    `_ = a * z' * |/ a * (a * (z'' * z''') * |/a)` by rw_tac std_ss[group_op_element] >>
    rw_tac std_ss[],
    metis_tac[group_rid, group_rinv],
    rw_tac std_ss[group_lid, group_op_element],
    `|/z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
    metis_tac[group_linv, group_rid, group_rinv]
  ]);

(* Theorem: Group g, h <= g, a in G ==> (conjugate_subgroup h g a) <= g *)
(* Proof:
   By conjugate_subgroup_group, and (conjugate_subgroup h g a).carrier SUBSET G.
*)
val conjugate_subgroup_subgroup = store_thm(
  "conjugate_subgroup_subgroup",
  ``!(g:'a group) h. h <= g ==> !a::G. (conjugate_subgroup h g a) <= g``,
  rw_tac std_ss[RES_FORALL_THM] >>
  `Group (conjugate_subgroup h g a)` by rw_tac std_ss[conjugate_subgroup_group] >>
  `Group g` by metis_tac[Subgroup_def] >>
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, Subgroup_def, SUBSET_DEF, GSPECIFICATION] >>
  metis_tac[group_inv_element, group_op_element, subgroup_element]);

(* Theorem: [Bijection between subgroup and its conjugate]
            Group g, h <= g, a in G ==>
            BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier *)
(* Proof:
   Essentially this is to prove:
   (1) z IN H ==> ?z'. (a * z * |/ a = a * z' * |/ a) /\ z' IN H
       True by taking z' = z.
   (2) z IN H /\ z' IN H /\ a * z * |/ a = a * z' * |/ a ==> z = z'
       True by group left/right cancellations.
   (3) z IN H ==> ?z'. (a * z * |/ a = a * z' * |/ a) /\ z' IN H
       True by taking z' = z.
   (4) z IN H ==> ?z'. z' IN H /\ (a * z' * |/ a = a * z * |/ a)
       True by taking z' = z.
*)
val subgroup_conjugate_subgroup_bij = store_thm(
  "subgroup_conjugate_subgroup_bij",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier``,
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, BIJ_DEF, INJ_DEF, SURJ_DEF, GSPECIFICATION] >| [
    metis_tac[],
    `Group g /\ z IN G /\ z' IN G` by metis_tac[subgroup_property, subgroup_element] >>
    `|/a IN G /\ a * z IN G /\ a * z' IN G` by rw_tac std_ss[group_inv_element, group_op_element] >>
    metis_tac[group_lcancel, group_rcancel],
    metis_tac[],
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Intersection                                                     *)
(* ------------------------------------------------------------------------- *)

(* Use K to denote k.carrier *)
val _ = temp_overload_on ("K", ``(k:'a group).carrier``);
(* Use o to denote h.op *)
val _ = temp_overload_on ("o", ``(h:'a group).op``);
(* Use #i to denote h.id *)
val _ = temp_overload_on ("#i", ``(h:'a monoid).id``);

(* Theorem: h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K *)
(* Proof:
   Since h <= g ==> Group h /\ Group g /\ h << g    by subgroup_homomorphism, subgroup_is_submonoid
     and k <= g ==> Group k /\ Group g /\ k << g    by subgroup_homomorphism, subgroup_is_submonoid
   x IN H INTER K ==> x IN H and x IN K             by IN_INTER
   Since x IN H, by h <= g, h.inv x = |/ x          by subgroup_inv
    also x IN K, by k <= g, k.inv x = |/ x          by subgroup_inv
    Therefore |/ x IN H INTER K                     by IN_INTER, group_inv_element
*)
val subgroup_intersect_has_inv = store_thm(
  "subgroup_intersect_has_inv",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K``,
  rpt strip_tac >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `x IN H /\ x IN K` by metis_tac[IN_INTER] >>
  `(h.inv x = |/ x) /\ (k.inv x = |/ x)` by rw[subgroup_inv] >>
  `Group h /\ Group k` by metis_tac[subgroup_homomorphism] >>
  metis_tac[IN_INTER, group_inv_element]);

(* Theorem: h <= g /\ k <= g ==> Group (h mINTER k) *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (h mINTER k)
       Since h <= g ==> h << g     by subgroup_is_submonoid
         and k <= g ==> k << g     by subgroup_is_submonoid
       Hence Monoid (h mINTER k)   by submonoid_intersect_monoid
   (2) monoid_invertibles (h mINTER k) = (h mINTER k).carrier
       By monoid_invertibles_def, this is to show:
       ?y. y IN (h mINTER k).carrier /\
        ((h mINTER k).op x y = (h mINTER k).id) /\ ((h mINTER k).op y x = (h mINTER k).id)
       Since h <= g ==> h << g     by subgroup_is_submonoid
         and k <= g ==> k << g     by subgroup_is_submonoid
       By submonoid_intersect_property, this is to show:
       ?y. y IN H INTER K /\ (x * y = #e) /\ (y * x = #e)
       Let y = |/ x.
       Then |/ x IN H INTER K            by subgroup_intersect_has_inv
       Since h <= g ==> Group g          by subgroup_homomorphism
         and x IN H and x IN K           by IN_INTER
             ==> x IN G                  by subgroup_element
       Hence x * y = #e and y * x = #e   by group_id
*)
val subgroup_intersect_group = store_thm(
  "subgroup_intersect_group",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> Group (h mINTER k)``,
  rpt strip_tac >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `Group h /\ Group k /\ Group g` by metis_tac[subgroup_homomorphism] >>
  rw[Group_def] >| [
    metis_tac[submonoid_intersect_monoid],
    rw[monoid_invertibles_def, EXTENSION, EQ_IMP_THM] >>
    pop_assum mp_tac >>
    `x IN H INTER K ==> ?y. y IN H INTER K /\ (x * y = #e) /\ (y * x = #e)` suffices_by metis_tac[submonoid_intersect_property] >>
    rpt strip_tac >>
    `|/ x IN H INTER K` by metis_tac[subgroup_intersect_has_inv] >>
    qexists_tac `|/ x` >>
    `x IN G` by metis_tac[IN_INTER, subgroup_element] >>
    rw[]
  ]);

(* Theorem: h <= g /\ k <= g ==> !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x) *)
(* Proof:
   Since h <= g ==> Group h /\ Group g     by subgroup_homomorphism
     and h <= g ==> h << g                 by subgroup_is_submonoid
     and k <= g ==> k << g                 by subgroup_is_submonoid
   Hence by submonoid_intersect_property,
        (h mINTER k).carrier = H INTER K
        !x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)
        (h mINTER k).id = #e
   Now, h <= g /\ k <= g ==> Group (h mINTER k)   by subgroup_intersect_group
   and  |/ x IN H INTER K                         by subgroup_intersect_has_inv
   also x IN G /\ |/ x IN G                       by IN_INTER, subgroup_element
   Therefore (h mINTER k).op ( |/ x) x = (h mINTER k).id     by group_linv
   Hence (h mINTER k).inv x = |/ x                by group_linv_unique
*)
val subgroup_intersect_inv = store_thm(
  "subgroup_intersect_inv",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)``,
  rpt strip_tac >>
  `Group g /\ Group h` by metis_tac[subgroup_homomorphism] >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `(h mINTER k).carrier = H INTER K` by metis_tac[submonoid_intersect_property] >>
  `!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)` by metis_tac[submonoid_intersect_property] >>
  `(h mINTER k).id = #e` by metis_tac[submonoid_intersect_property] >>
  `Group (h mINTER k)` by metis_tac[subgroup_intersect_group] >>
  `|/ x IN H INTER K` by rw[subgroup_intersect_has_inv] >>
  `x IN G /\ |/ x IN G` by metis_tac[IN_INTER, subgroup_element] >>
  metis_tac[group_linv, group_linv_unique]);

(* Theorem: properties of subgroup_intersect:
   h <= g /\ k <= g ==>
     ((h mINTER k).carrier = H INTER K) /\
     (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
     ((h mINTER k).id = #e) /\
     (!x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)) *)
(* Proof: by subgroup_is_submonoid, submonoid_intersect_property, subgroup_intersect_inv. *)
val subgroup_intersect_property = store_thm(
  "subgroup_intersect_property",
  ``!(g:'a group) h k. h <= g /\ k <= g ==>
     ((h mINTER k).carrier = H INTER K) /\
     (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
     ((h mINTER k).id = #e) /\
     (!x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x))``,
  metis_tac[subgroup_is_submonoid, submonoid_intersect_property, subgroup_intersect_inv]);

(* Theorem: h <= g /\ k <= g ==> (h mINTER k) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (h mINTER k), true by subgroup_intersect_group.
   (2) Group g, true by subgroup_homomorphism.
   (3) (h mINTER k).carrier SUBSET G
       Since (h mINTER k).carrier = H INTER K   by subgroup_intersect_property
         and (H INTER K) SUBSET H               by INTER_SUBSET
         and h <= g ==> H SUBSET G              by Subgroup_def
       Hence (h mINTER k).carrier SUBSET G      by SUBSET_TRANS
   (4) (h mINTER k).op = $*
       By monoid_intersect_def, this is to show: $o = $*
       which is true by Subgroup_def.
*)
val subgroup_intersect_subgroup = store_thm(
  "subgroup_intersect_subgroup",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> (h mINTER k) <= g``,
  rpt strip_tac >>
  rw[Subgroup_def] >| [
    metis_tac[subgroup_intersect_group],
    metis_tac[subgroup_homomorphism],
    `(h mINTER k).carrier = H INTER K` by metis_tac[subgroup_intersect_property] >>
    `(H INTER K) SUBSET H` by rw[INTER_SUBSET] >>
    `H SUBSET G` by metis_tac[Subgroup_def] >>
    metis_tac[SUBSET_TRANS],
    rw[monoid_intersect_def] >>
    metis_tac[Subgroup_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Big Intersection                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define intersection of subgroups of a group *)
val subgroup_big_intersect_def = Define `
   subgroup_big_intersect (g:'a group) =
      <| carrier := BIGINTER (IMAGE (\h. H) {h | h <= g});
              op := $*; (* g.op *)
              id := #e  (* g.id *)
       |>
`;

val _ = overload_on ("sgbINTER", ``subgroup_big_intersect``);
(*
> subgroup_big_intersect_def;
val it = |- !g. sgbINTER g =
     <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g}); op := $*; id := #e|>: thm
*)

(* Theorem: ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
   (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> ((sgbINTER g).op x y = x * y)) /\
   ((sgbINTER g).id = #e) *)
(* Proof: by subgroup_big_intersect_def. *)
val subgroup_big_intersect_property = store_thm(
  "subgroup_big_intersect_property",
  ``!g:'a group. ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
   (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> ((sgbINTER g).op x y = x * y)) /\
   ((sgbINTER g).id = #e)``,
  rw[subgroup_big_intersect_def]);

(* Theorem: x IN (sgbINTER g).carrier <=> (!h. h <= g ==> x IN H) *)
(* Proof:
       x IN (sgbINTER g).carrier
   <=> x IN BIGINTER (IMAGE (\h. H) {h | h <= g})          by subgroup_big_intersect_def
   <=> !P. P IN (IMAGE (\h. H) {h | h <= g}) ==> x IN P    by IN_BIGINTER
   <=> !P. ?h. (P = H) /\ h IN {h | h <= g}) ==> x IN P    by IN_IMAGE
   <=> !P. ?h. (P = H) /\ h <= g) ==> x IN P               by GSPECIFICATION
   <=> !h. h <= g ==> x IN H
*)
val subgroup_big_intersect_element = store_thm(
  "subgroup_big_intersect_element",
  ``!g:'a group. !x. x IN (sgbINTER g).carrier <=> (!h. h <= g ==> x IN H)``,
  rw[subgroup_big_intersect_def] >>
  metis_tac[]);

(* Theorem: x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> (sgbINTER g).op x y IN (sgbINTER g).carrier *)
(* Proof:
   Since x IN (sgbINTER g).carrier, !h. h <= g ==> x IN H   by subgroup_big_intersect_element
    also y IN (sgbINTER g).carrier, !h. h <= g ==> y IN H   by subgroup_big_intersect_element
     Now !h. h <= g ==> x o y IN H                          by Subgroup_def, group_op_element
                    ==> x * y IN H                          by subgroup_property
     Now, (sgbINTER g).op x y = x * y                       by subgroup_big_intersect_property
     Hence (sgbINTER g).op x y IN (sgbINTER g).carrier      by subgroup_big_intersect_element
*)
val subgroup_big_intersect_op_element = store_thm(
  "subgroup_big_intersect_op_element",
  ``!g:'a group. !x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                     (sgbINTER g).op x y IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> x IN H /\ y IN H` by metis_tac[subgroup_big_intersect_element] >>
  `!h. h <= g ==> x * y IN H` by metis_tac[Subgroup_def, group_op_element, subgroup_property] >>
  `(sgbINTER g).op x y = x * y` by rw[subgroup_big_intersect_property] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: (sgbINTER g).id IN (sgbINTER g).carrier *)
(* Proof:
   !h. h <= g ==> #i = #e                               by subgroup_id
   !h. h <= g ==> #i IN H                               by Subgroup_def, group_id_element
   Now (smbINTER g).id = #e                             by subgroup_big_intersect_property
   Hence !h. h <= g ==> (sgbINTER g).id IN H            by above
      or (sgbINTER g).id IN (sgbINTER g).carrier        by subgroup_big_intersect_element
*)
val subgroup_big_intersect_has_id = store_thm(
  "subgroup_big_intersect_has_id",
  ``!g:'a group. (sgbINTER g).id IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> (#i = #e)` by rw[subgroup_id] >>
  `!h. h <= g ==> #i IN H` by rw[Subgroup_def] >>
  `(sgbINTER g).id = #e` by metis_tac[subgroup_big_intersect_property] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: !x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier *)
(* Proof:
   Since x IN (sgbINTER g).carrier,
         !h. h <= g ==> x IN H             by subgroup_big_intersect_element
    also !h. h <= g ==> (h.inv x = |/ x)   by subgroup_inv, x IN H.
     Now !h. h <= g ==> Group h            by Subgroup_def
      so !h. h <= g ==> |/ x IN H          by group_inv_element
   Hence |/ x IN (sgbINTER g).carrier      by subgroup_big_intersect_element
*)
val subgroup_big_intersect_has_inv = store_thm(
  "subgroup_big_intersect_has_inv",
  ``!g:'a group. !x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> x IN H` by metis_tac[subgroup_big_intersect_element] >>
  `!h. h <= g ==> (h.inv x = |/ x)` by rw[subgroup_inv] >>
  `!h. h <= g ==> Group h` by rw[Subgroup_def] >>
  `!h. h <= g ==> |/ x IN H` by metis_tac[group_inv_element] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: Group g ==> (sgbINTER g).carrier SUBSET G *)
(* Proof:
   By subgroup_big_intersect_def, this is to show:
   Group g ==> BIGINTER (IMAGE (\h. H) {h | h <= g}) SUBSET G
   Let P = IMAGE (\h. H) {h | h <= g}.
   Since g <= g                    by subgroup_refl
      so G IN P                    by IN_IMAGE, definition of P.
    Thus P <> {}                   by MEMBER_NOT_EMPTY.
     Now h <= g ==> H SUBSET G     by Subgroup_def
   Hence P SUBSET G                by BIGINTER_SUBSET
*)
val subgroup_big_intersect_subset = store_thm(
  "subgroup_big_intersect_subset",
  ``!g:'a group. Group g ==> (sgbINTER g).carrier SUBSET G``,
  rw[subgroup_big_intersect_def] >>
  qabbrev_tac `P = IMAGE (\h. H) {h | h <= g}` >>
  (`!x. x IN P <=> ?h. (H = x) /\ h <= g` by (rw[Abbr`P`] >> metis_tac[])) >>
  `g <= g` by rw[subgroup_refl] >>
  `P <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `!h:'a group. h <= g ==> H SUBSET G` by rw[Subgroup_def] >>
  metis_tac[BIGINTER_SUBSET]);

(* Theorem: Group g ==> Group (smbINTER g) *)
(* Proof:
   Group g ==> (sgbINTER g).carrier SUBSET G                by subgroup_big_intersect_subset
   By Monoid_def, this is to show:
   (1) x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> (sgbINTER g).op x y IN (sgbINTER g).carrier
       True by subgroup_big_intersect_op_element.
   (2) (sgbINTER g).op ((sgbINTER g).op x y) z = (sgbINTER g).op x ((sgbINTER g).op y z)
       Since (sgbINTER g).op x y IN (sgbINTER g).carrier    by subgroup_big_intersect_op_element
         and (sgbINTER g).op y z IN (sgbINTER g).carrier    by subgroup_big_intersect_op_element
       So this is to show: (x * y) * z = x * (y * z)        by subgroup_big_intersect_property
       Since x IN G, y IN G and z IN G                      by SUBSET_DEF
       This follows by group_assoc.
   (3) (sgbINTER g).id IN (sgbINTER g).carrier
       This is true by subgroup_big_intersect_has_id.
   (4) x IN (sgbINTER g).carrier ==> (sgbINTER g).op (sgbINTER g).id x = x
       Since (sgbINTER g).id IN (sgbINTER g).carrier   by subgroup_big_intersect_op_element
         and (sgbINTER g).id = #e                      by subgroup_big_intersect_property
        also x IN G                                    by SUBSET_DEF
         (sgbINTER g).op (sgbINTER g).id x
       = #e * x                                        by subgroup_big_intersect_property
       = x                                             by group_id
   (5) x IN (sgbINTER g).carrier ==>
       ?y. y IN (sgbINTER g).carrier /\ ((sgbINTER g).op y x = (sgbINTER g).id)
       Since |/ x IN (sgbINTER g).carrier              by subgroup_big_intersect_has_inv
         and (sgbINTER g).id IN (sgbINTER g).carrier   by subgroup_big_intersect_op_element
         and (sgbINTER g).id = #e                      by subgroup_big_intersect_property
        also x IN G                                    by SUBSET_DEF
        Let y = |/ x, then y IN (sgbINTER g).carrier,
         (sgbINTER g).op y x
       = |/ x * x                                      by subgroup_big_intersect_property
       = #e                                            by group_linv
*)
val subgroup_big_intersect_group = store_thm(
  "subgroup_big_intersect_group",
  ``!g:'a group. Group g ==> Group (sgbINTER g)``,
  rpt strip_tac >>
  `(sgbINTER g).carrier SUBSET G` by rw[subgroup_big_intersect_subset] >>
  rw_tac std_ss[group_def_alt] >| [
    metis_tac[subgroup_big_intersect_op_element],
    `(sgbINTER g).op x y IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_op_element] >>
    `(sgbINTER g).op y z IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_op_element] >>
    `(x * y) * z = x * (y * z)` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[SUBSET_DEF] >>
    rw[group_assoc],
    metis_tac[subgroup_big_intersect_has_id],
    `(sgbINTER g).id = #e` by rw[subgroup_big_intersect_property] >>
    `(sgbINTER g).id IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_has_id] >>
    `#e * x = x` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[],
    `|/ x IN (sgbINTER g).carrier` by rw[subgroup_big_intersect_has_inv] >>
    `(sgbINTER g).id = #e` by rw[subgroup_big_intersect_property] >>
    `(sgbINTER g).id IN (sgbINTER g).carrier` by rw[subgroup_big_intersect_has_id] >>
    qexists_tac `|/ x` >>
    `|/ x * x = #e` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[]
  ]);

(* Theorem: Group g ==> (sgbINTER g) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (sgbINTER g)
       True by subgroup_big_intersect_group.
   (2) (sgbINTER g).carrier SUBSET G
       True by subgroup_big_intersect_subset.
   (3) (sgbINTER g).op = $*
       True by subgroup_big_intersect_def
*)
val subgroup_big_intersect_subgroup = store_thm(
  "subgroup_big_intersect_subgroup",
  ``!g:'a group. Group g ==> (sgbINTER g) <= g``,
  rw_tac std_ss[Subgroup_def] >| [
    rw[subgroup_big_intersect_group],
    rw[subgroup_big_intersect_subset],
    rw[subgroup_big_intersect_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subset Group (to be subgroup)                                             *)
(* ------------------------------------------------------------------------- *)

(* Define the subset group: takes a subset and gives a group candidate *)
val subset_group_def = Define`
    subset_group (g:'a group) (s:'a -> bool) =
    <| carrier := s;
            op := g.op;
            id := g.id
     |>
`;
(* val subset_group_def = |- !g s. subset_group g s = <|carrier := s; op := $*; id := #e|>: thm *)

(* Theorem: properties of subset_group *)
(* Proof: by subset_group_def *)
val subset_group_property = store_thm(
  "subset_group_property",
  ``!(g:'a group) s.
     ((subset_group g s).carrier = s) /\
     ((subset_group g s).op = g.op) /\
     ((subset_group g s).id = #e)``,
  rw_tac std_ss[subset_group_def]);

(* Theorem: x IN s ==> !n. (subset_group g s).exp x n = x ** n *)
(* Proof:
   By induction on n.
   Base: (subset_group g s).exp x 0 = x ** 0
          (subset_group g s).exp x 0
        = (subset_group g s).id        by group_exp_0
        = #0                           by subset_group_property
        = x ** 0                       by group_exp_0
   Step: x IN s /\ (subset_group g s).exp x n = x ** n ==>
         (subset_group g s).exp x (SUC n) = x ** SUC n
          (subset_group g s).exp x (SUC n)
        = (subset_group g s).op x ((subset_group g s).exp x n)   by group_exp_SUC
        = x * ((subset_group g s).exp x n)                       by subset_group_property
        = x * (x ** n)                 by induction hypothesis
        = x ** SUC n                   by group_exp_SUC
*)
val subset_group_exp = store_thm(
  "subset_group_exp",
  ``!(g:'a group) s. !x. x IN s ==> !n. (subset_group g s).exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[subset_group_property] >>
  rw[subset_group_property]);

(* Theorem: x IN s ==> (order (subset_group g s) x = order g x) *)
(* Proof:
   Note (subset_group g s).exp x k = x ** k      by subset_group_exp
    and (subset_group g s).id = #e               by subset_group_property
   Thus order (subset_group g s) x = order g x   by order_def, period_def
*)
val subset_group_order = store_thm(
  "subset_group_order",
  ``!(g:'a group) s. !x. x IN s ==> (order (subset_group g s) x = order g x)``,
  rw[order_def, period_def, subset_group_property, subset_group_exp]);

(* Theorem: Monoid g /\ #e IN s /\ (s SUBSET G) /\
           (!x y. x IN s /\ y IN s ==> x * y IN s)  ==> (subset_group g s) << g *)
(* Proof:
   Let h = subset_group g s
   Then H = s          by subset_group_property
   Thus h << g         by subset_group_property, submonoid_alt
*)
val subset_group_submonoid = store_thm(
  "subset_group_submonoid",
  ``!(g:'a monoid) s. Monoid g /\ #e IN s /\ (s SUBSET G) /\
           (!x y. x IN s /\ y IN s ==> x * y IN s)  ==> (subset_group g s) << g``,
  rw[submonoid_alt, subset_group_property]);

(* Theorem: Group g /\ s <> {} /\ (s SUBSET G) /\
            (!x y. x IN s /\ y IN s ==> x * ( |/ y) IN s) ==> (subset_group g s) <= g *)
(* Proof:
   Let h = subset_group g s
   Then H = s          by subset_group_property
   Thus h <= g         by subset_group_property, subgroup_alt
*)
val subset_group_subgroup = store_thm(
  "subset_group_subgroup",
  ``!(g:'a group) s. Group g /\ s <> {} /\ (s SUBSET G) /\
   (!x y. x IN s /\ y IN s ==> x * |/ y IN s) ==> (subset_group g s) <= g``,
  rw[subgroup_alt, subset_group_property]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
