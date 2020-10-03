(* ------------------------------------------------------------------------- *)
(* Group Action, Orbits and Fixed points.                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupAction";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "groupOrderTheory"; *)
open monoidTheory groupTheory;
open subgroupTheory groupOrderTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* val _ = load "helperListTheory"; *)
open helperNumTheory helperSetTheory helperListTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;


(*===========================================================================*)

(*

Group action
============
. action f is a map from Group g to Target set A, satisfying some conditions.
. The action induces an equivalence relation "reach" on Target set A.
. The equivalent classes of "reach" on A are called orbits.
. Due to this partition, CARD X = SIGMA CARD orbits.
. As equivalent classes are non-empty, minimum CARD orbit = 1.
. These singleton orbits have a 1-1 correspondence with a special set on A:
  the fixed_points. The main result is:
  CARD A = CARD fixed_points + SIGMA (CARD non-singleton orbits).

  Somewhere Zn enters into the picture. Where?

Rework
======
. action o, implicitly infix.
. keep a, b as group elements, x, y as set elements.
. orbits rather than TargetPartition.
. orbit is defined as image.

*)

(*===========================================================================*)

(* ------------------------------------------------------------------------- *)
(* Group Action Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (g act A) $o    = action $o g A
   (x ~~ y) $o g   = reach $o g x y
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Group action:
   action_def      |- ! $o g A. (g act A) $o <=>
                      !x. x IN A ==> (!a. a IN G ==> a o x IN A) /\
                                     (#e o x = x) /\
                                     !a b. a IN G /\ b IN G ==> (a o b o x = (a * b) o x)
   action_closure  |- ! $o g A. (g act A) $o ==> !a x. a IN G /\ x IN A ==> a o x IN A
   action_compose  |- ! $o g A. (g act A) $o ==>
                      !a b x. a IN G /\ b IN G /\ x IN A ==> (a o b o x = (a * b) o x)
   action_id       |- ! $o g A. (g act A) $o ==> !x. x IN A ==> (#e o x = x)
   action_reverse  |- ! $o g A. Group g /\ (g act A) $o ==>
                      !a x y. a IN G /\ x IN A /\ y IN A /\ (a o x = y) ==> ( |/ a o y = x)
   action_trans    |- ! $o g A. (g act A) $o ==>
                      !a b x y z. a IN G /\ b IN G /\ x IN A /\ y IN A /\ z IN A /\
                                  (a o x = y) /\ (b o y = z) ==> ((b * a) o x = z)

   Group action induces an equivalence relation:
   reach_def   |- ! $o g x y. (x ~~ y) $o g <=> ?a. a IN G /\ (a o x = y)
   reach_refl  |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==> (x ~~ x) $o g
   reach_sym   |- ! $o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN A /\
                                (x ~~ y) $o g ==> (y ~~ x) $o g
   reach_trans |- ! $o g A x y z. Group g /\ (g act A) $o /\ x IN A /\ y IN A /\ z IN A /\
                                  (x ~~ y) $o g /\ (y ~~ z) $o g ==> (x ~~ z) $o g
   reach_equiv |- ! $o g A. Group g /\ (g act A) $o ==> reach $o g equiv_on A

   Orbits as equivalence classes:
   orbit_def           |- ! $o g A x. orbit $o g A x = {a o x | a IN G}
   orbit_as_image      |- ! $o g A x. orbit $o g A x = IMAGE (\a. a o x) G
   orbit_element       |- ! $o g A x y. y IN orbit $o g A x <=> (x ~~ y) $o g
   orbit_has_action_element
                       |- ! $o g A a x. a IN G ==> a o x IN orbit $o g A x
   orbit_has_self      |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==> x IN orbit $o g A x
   orbit_subset_target |- ! $o g A x. (g act A) $o /\ x IN A ==> orbit $o g A x SUBSET A
   orbit_element_in_target
                       |- ! $o g A x y. (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==> y IN A
   orbit_finite        |- ! $o g A x. (g act A) $o /\ x IN A /\ FINITE A ==> FINITE (orbit $o g A x)
   orbit_as_equiv_class|- ! $o g A x. (g act A) $o /\ x IN A ==>
                                      (orbit $o g A x = equiv_class (reach $o g) A x)
   orbit_eq_orbit      |- ! $o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN A ==>
                                        ((orbit $o g A x = orbit $o g A y) <=> (x ~~ y) $o g)

   Partition by Group action:
   orbits_def          |- ! $o g A. orbits $o g A = {orbit $o g A x | x | x IN A}
   orbits_element      |- ! $o g A e. e IN orbits $o g A <=> ?x. x IN A /\ (e = orbit $o g A x)
   orbits_as_image     |- ! $o g A. orbits $o g A = IMAGE (orbit $o g A) A
   orbits_eq_partition |- ! $o g A. (g act A) $o ==> (orbits $o g A = partition (reach $o g) A)
   orbits_finite       |- ! $o g A. (g act A) $o /\ FINITE A ==> FINITE (orbits $o g A)
   orbits_element_finite
                       |- ! $o g A. (g act A) $o /\ FINITE A ==> EVERY_FINITE (orbits $o g A)
   orbits_element_nonempty
                       |- ! $o g A. Group g /\ (g act A) $o ==> !e. e IN orbits $o g A ==> e <> {}
   orbits_element_subset
                       |- ! $o g A. (g act A) $o ==> !e. e IN orbits $o g A ==> e SUBSET A
   orbits_element_element
                       |- ! $o g A. (g act A) $o ==> !e. e IN orbits $o g A ==> !x. x IN e ==> x IN A

   orbit_is_orbits_element
                       |- ! $o g A x. x IN A ==> orbit $o g A x IN orbits $o g A
   orbits_element_is_orbit
                       |- ! $o g A e. Group g /\ (g act A) $o /\ e IN orbits $o g A ==>
                          !x. x IN e ==> (e = orbit $o g A x)
   action_to_orbit_surj|- ! $o g A x. (g act A) $o /\ x IN A ==> SURJ (\a. a o x) G (orbit $o g A x)
   orbit_is_action_image
                       |- ! $o g A x. (g act A) $o /\ x IN A ==> (orbit $o g A x = IMAGE (\a. a o x) G)
   orbit_finite_inj_card
                       |- ! $o g A x. (g act A) $o /\ x IN A /\ FINITE A /\
                                      INJ (\a. a o x) G (orbit $o g A x) ==>
                                      (CARD (orbit $o g A x) = CARD G)
   target_card_by_partition
                       |- ! $o g A x. Group g /\ (g act A) $o /\ FINITE A ==>
                                      (CARD A = SIGMA CARD (orbits $o g A))
   orbits_equal_size_partition_equal_size
                       |- ! $o g A n. Group g /\ (g act A) $o /\ FINITE A /\
                                      (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==>
                                      !e. e IN orbits $o g A ==> (CARD e = n)
   orbits_equal_size_property
                       |- ! $o g A n. Group g /\ (g act A) $o /\ FINITE A /\
                                      (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==>
                                      n divides CARD A
   orbits_size_factor_partition_factor
                       |- ! $o g A n. Group g /\ (g act A) $o /\ FINITE A /\
                                      (!x. x IN A ==> n divides CARD (orbit $o g A x)) ==>
                                      !e. e IN orbits $o g A ==> n divides CARD e
   orbits_size_factor_property
                       |- ! $o g A n. Group g /\ (g act A) $o /\ FINITE A /\
                                      (!x. x IN A ==> n divides CARD (orbit $o g A x)) ==>
                                      n divides CARD A

   Stabilizer as invariant:
   stabilizer_def      |- ! $o g x. stabilizer $o g x = {a | a IN G /\ (a o x = x)}
   stabilizer_element  |- ! $o g A x a. a IN stabilizer $o g x <=> a IN G /\ (a o x = x)
   stabilizer_subset   |- ! $o g A x. stabilizer $o g x SUBSET G
   stabilizer_has_id   |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==> #e IN stabilizer $o g x
   stabilizer_nonempty |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==> stabilizer $o g x <> {}

   Stabilizer subgroup:
   StabilizerGroup_def |- ! $o g x. StabilizerGroup $o g x =
                                    <|carrier := stabilizer $o g x; op := $*; id := #e|>
   stabilizer_group_property
                       |- ! $o g x. ((StabilizerGroup $o g x).carrier = stabilizer $o g x) /\
                                    ((StabilizerGroup $o g x).op = $* ) /\
                                    ((StabilizerGroup $o g x).id = #e)
   stabilizer_group_group
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                                      Group (StabilizerGroup $o g x)
   stabilizer_group_subgroup
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                                      StabilizerGroup $o g x <= g
   stabilizer_group_finite_group
                       |- ! $o g A x. FiniteGroup g /\ (g act A) $o /\ x IN A ==>
                                      FiniteGroup (StabilizerGroup $o g x)
   stabilizer_card_divides
                       |- ! $o g A x. FiniteGroup g /\ (g act A) $o /\ x IN A ==>
                                      CARD (stabilizer $o g x) divides CARD G

   Orbit-Stabilizer Theorem:
   orbit_stabilizer_map_good
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                          !a b. a IN G /\ b IN G /\ (a o x = b o x) ==>
                                (a * stabilizer $o g x = b * stabilizer $o g x)
   orbit_stabilizer_map_inj
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                          !a b. a IN G /\ b IN G /\
                                (a * stabilizer $o g x = b * stabilizer $o g x) ==>
                                (a o x = b o x)
   action_match_condition
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                          !a b. a IN G /\ b IN G ==>
                                ((a o x = b o x) <=> |/ a * b IN stabilizer $o g x)
   stabilizer_conjugate|- ! $o g A x a. Group g /\ (g act A) $o /\ x IN A /\ a IN G ==>
                                (conjugate g a (stabilizer $o g x) = stabilizer $o g (a o x))
   act_by_def          |- ! $o g x y. (x ~~ y) $o g ==>
                                      act_by $o g x y IN G /\ (act_by $o g x y o x = y)
   action_reachable_coset_1
                       |- ! $o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
                            (act_by $o g x y * stabilizer $o g x = {a | a IN G /\ (a o x = y)})
   action_reachable_coset_2
                       |- ! $o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
                          !a. a IN G /\ (a o x = y) ==>
                              (a * stabilizer $o g x = {b | b IN G /\ (b o x = y)})
   orbit_stabilizer_cosets_bij_3
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                               BIJ (\y. act_by $o g x y * stabilizer $o g x)
                                   (orbit $o g A x) {a * stabilizer $o g x | a | a IN G}
   orbit_stabilizer_cosets_bij_4
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                               BIJ (\y. act_by $o g x y * stabilizer $o g x)
                                   (orbit $o g A x) (CosetPartition g (StabilizerGroup $o g x))
   orbit_stabilizer_thm|- ! $o g A x. FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
                              (CARD G = CARD (orbit $o g A x) * CARD (stabilizer $o g x))
   orbit_card_divides_target_card
                       |- ! $o g A x. FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
                               CARD (orbit $o g A x) divides CARD G

   Fixed Points of action:
   fixed_points_def    |- ! $o g A. fixed_points $o g A = {x | x IN A /\ !a. a IN G ==> (a o x = x)}
   fixed_points_element|- ! $o g A x. x IN fixed_points $o g A <=> x IN A /\ !a. a IN G ==> (a o x = x)
   fixed_points_subset |- ! $o g A. (g act A) $o ==> fixed_points $o g A SUBSET A
   fixed_points_element_element
                       |- !f g A x. x IN fixed_points f g A ==> x IN A
   fixed_points_orbit_sing
                       |- ! $o g A x. Group g /\ (g act A) $o ==>
                            (x IN fixed_points $o g A <=> x IN A /\ (orbit $o g A x = {x}))
   orbit_sing_fixed_points
                       |- ! $o g A x. (g act A) $o /\ x IN A /\ (orbit $o g A x = {x}) ==>
                                      x IN fixed_points $o g A
   fixed_points_orbit_is_sing
                       |- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==>
                            (x IN fixed_points $o g A <=> SING (orbit $o g A x))
   non_fixed_points_orbit_not_sing
                       |- ! $o g A x. Group g /\ (g act A) $o ==>
                            (x IN A DIFF fixed_points $o g A <=> x IN A /\ ~SING (orbit $o g A x))
   non_fixed_points_card
                       |- ! $o g A. (g act A) $o /\ FINITE A ==>
                            (CARD (A DIFF fixed_points $o g A) =
                             CARD A - CARD (fixed_points $o g A))

   Target Partition by orbits:
   sing_orbits_def     |- ! $o g A. sing_orbits $o g A = {e | e IN orbits $o g A /\ SING e}
   multi_orbits_def    |- ! $o g A. multi_orbits $o g A = {e | e IN orbits $o g A /\ ~SING e}
   sing_orbits_element |- ! $o g A e. e IN sing_orbits $o g A <=> e IN orbits $o g A /\ SING e
   sing_orbits_subset  |- ! $o g A. sing_orbits $o g A SUBSET orbits $o g A
   sing_orbits_finite  |- ! $o g A. (g act A) $o /\ FINITE A ==> FINITE (sing_orbits $o g A)
   sing_orbits_element_subset
                       |- ! $o g A e. (g act A) $o /\ e IN sing_orbits $o g A ==> e SUBSET A
   sing_orbits_element_finite
                       |- ! $o g A e. e IN sing_orbits $o g A ==> FINITE e
   sing_orbits_element_card
                       |- ! $o g A e. e IN sing_orbits $o g A ==> (CARD e = 1)
   sing_orbits_element_choice
                       |- ! $o g A e. Group g /\ (g act A) $o /\ e IN sing_orbits $o g A ==>
                                      CHOICE e IN fixed_points $o g A
   multi_orbits_element|- ! $o g A e. e IN multi_orbits $o g A <=> e IN orbits $o g A /\ ~SING e
   multi_orbits_subset |- ! $o g A. multi_orbits $o g A SUBSET orbits $o g A
   multi_orbits_finite |- ! $o g A. (g act A) $o /\ FINITE A ==> FINITE (multi_orbits $o g A)
   multi_orbits_element_subset
                       |- ! $o g A e. (g act A) $o /\ e IN multi_orbits $o g A ==> e SUBSET A
   multi_orbits_element_finite
                       |- ! $o g A e. (g act A) $o /\ FINITE A /\ e IN multi_orbits $o g A ==> FINITE e
   sing_multi_orbits_disjoint
                       |- ! $o g A. DISJOINT (sing_orbits $o g A) (multi_orbits $o g A)
   sing_multi_orbits_union
                       |- ! $o g A. orbits $o g A = sing_orbits $o g A UNION multi_orbits $o g A
   target_card_by_orbit_types
                       |- ! $o g A. Group g /\ (g act A) $o /\ FINITE A ==>
                                   (CARD A = CARD (sing_orbits $o g A) +
                                             SIGMA CARD (multi_orbits $o g A))
   sing_orbits_to_fixed_points_inj
                       |- ! $o g A. Group g /\ (g act A) $o ==>
                                    INJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)
   sing_orbits_to_fixed_points_surj
                       |- ! $o g A. Group g /\ (g act A) $o ==>
                                    SURJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)
   sing_orbits_to_fixed_points_bij
                       |- ! $o g A. Group g /\ (g act A) $o ==>
                                    BIJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)
   sing_orbits_card_eqn|- ! $o g A. Group g /\ (g act A) $o /\ FINITE A ==>
                                   (CARD (sing_orbits $o g A) = CARD (fixed_points $o g A))
   target_card_by_fixed_points
                       |- ! $o g A. Group g /\ (g act A) $o /\ FINITE A ==>
                                   (CARD A = CARD (fixed_points $o g A) +
                                             SIGMA CARD (multi_orbits $o g A))
   target_card_and_fixed_points_congruence
                       |- ! $o g A n. Group g /\ (g act A) $o /\ FINITE A /\ 0 < n /\
                                     (!e. e IN multi_orbits $o g A ==> (CARD e = n)) ==>
                                     (CARD A MOD n = CARD (fixed_points $o g A) MOD n)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Group action                                                              *)
(* ------------------------------------------------------------------------- *)
(* An action from group g to a set A is a map o: G x A -> A such that
   (0)   [is a map] (x in G) o (x IN A) in A
   (1)  [id action] (e in G) o (x IN A) = a
   (2) [composable] (x in G) o ((y in G) o (x IN A)) =
                    (g.op (x in G)(y in G)) o (x IN A)
*)
val action_def = Define`
    action (o) (g:'a group) (A:'b -> bool) =
       !x. x IN A ==> (!a. a IN G ==> a o x IN A) /\
                      (#e o x = x) /\
                      (!a b. a IN G /\ b IN G ==> (a o (b o x) = (a * b) o x))
`;

(* Overload on action *)
val _ = overload_on("act", ``\(g:'a group) (A:'b -> bool) (o). action (o) g A``);
val _ = set_fixity "act" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> action_def;
val it = |- ! $o g A. (g act A) $o <=>
            !x. x IN A ==>
                (!a. a IN G ==> a o x IN A) /\ (#e o x = x) /\
                 !a b. a IN G /\ b IN G ==> (a o b o x = (a * b) o x): thm
*)

(* ------------------------------------------------------------------------- *)
(* Action Properties                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Closure] (g act A) $o  ==> !a x. a IN G /\ x IN A ==> a o x IN A *)
(* Proof: by action_def. *)
val action_closure = store_thm(
  "action_closure",
  ``!$o g A. (g act A) $o  ==> !a x. a IN G /\ x IN A ==> a o x IN A``,
  simp[action_def]);

(* Theorem: [Compose] (g act A) $o ==> !a b x. a IN G /\ b IN G /\ x IN A ==> (a o (b o x) = (a * b) o x) *)
(* Proof: by action_def. *)
val action_compose = store_thm(
  "action_compose",
  ``!$o g A. (g act A) $o ==> !a b x. a IN G /\ b IN G /\ x IN A ==> (a o (b o x) = (a * b) o x)``,
  simp[action_def]);

(* Theorem: [Identity] (g act A) $o ==> !x. x IN A ==> (#e o x = x) *)
(* Proof: by action_def. *)
val action_id = store_thm(
  "action_id",
  ``!$o g A. (g act A) $o ==> !x. x IN A ==> (#e o x = x)``,
  simp[action_def]);
(* This is essentially reach_refl *)

(* Theorem: Group g /\ (g act A) $o ==>
            !a x y. a IN G /\ x IN A /\ y IN A /\ (a o x = y) ==> (( |/ a) o y = x)) *)
(* Proof:
   Note |/ a IN G        by group_inv_element
     ( |/ a) o y
   = ( |/ a) o (a o x)   by y = a o x
   = ( |/ a * a) o x     by action_compose
   = #e o x              by group_linv
   = x                   by action_id
*)
val action_reverse = store_thm(
  "action_reverse",
  ``!$o g A. Group g /\ (g act A) $o ==>
   !a x y. a IN G /\ x IN A /\ y IN A /\ (a o x = y) ==> (( |/ a) o y = x)``,
  simp[action_def]);
(* This is essentially reach_sym *)

(* Theorem: (g act A) $o ==> !a b x y z. a IN G /\ b IN G /\ x IN A /\ y IN A /\
                    z IN A /\ (a o x = y) /\ (b o y = z) ==> ((b * a) o x = z *)
(* Proof:
     (b * a) o x
   = b o (a o x)     by action_compose
   = b o y           by y = x o a
   = z               by z = b o y
*)
val action_trans = store_thm(
  "action_trans",
  ``!$o g A. (g act A) $o ==> !a b x y z. a IN G /\ b IN G /\
       x IN A /\ y IN A /\ z IN A /\ (a o x = y) /\ (b o y = z) ==> ((b * a) o x = z)``,
  simp[action_def]);
(* This is essentially reach_trans *)

(* ------------------------------------------------------------------------- *)
(* Group action induces an equivalence relation.                             *)
(* ------------------------------------------------------------------------- *)

(* Define reach to relate two points x and y in A *)
val reach_def = Define`
    reach $o (g:'a group) (x:'b) (y:'b) = ?a. a IN G /\ (a o x = y)
`;
(* Overload reach relation *)
val _ = temp_overload_on("~~", ``\(x:'b) (y:'b) $o (g:'a group). reach $o g x y``);
(* Make reach an infix. *)
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> reach_def;
val it = |- ! $o g x y. (x ~~ y) $o g <=> ?a. a IN G /\ (a o x = y): thm
*)

(* Theorem: [Reach is Reflexive] Group g /\ (g act A) $o /\
            x IN A ==> (x ~~ x) $o g *)
(* Proof:
   Note #e o x = x       by action_id
    and #e in G          by group_id_element
   Thus (x ~~ x) $o g    by reach_def, take a = #e.
*)
val reach_refl = store_thm(
  "reach_refl",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> (x ~~ x) $o g``,
  metis_tac[reach_def, action_id, group_id_element]);

(* Theorem: [Reach is Symmetric] Group g /\ (g act A) $o /\
            x IN A /\ y IN A /\ (x ~~ y) $o g ==> (y ~~ x) $o g *)
(* Proof:
   Note ?a. a IN G /\ a o x = y     by reach_def, (x ~~ y) $o g
    ==> ( |/ a) o y = x             by action_reverse
    and |/ a IN G                   by group_inv_element
   Thus (y ~~ x) $o g               by reach_def
*)
val reach_sym = store_thm(
  "reach_sym",
  ``!$o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN A /\
                (x ~~ y) $o g ==> (y ~~ x) $o g``,
  metis_tac[reach_def, action_reverse, group_inv_element]);

(* Theorem: [Reach is Transitive] Group g /\ (g act A) $o /\
            x IN A /\ y IN A /\ z IN A /\
            (x ~~ y) $o g /\ (y ~~ z) $o g ==> (x ~~ z) $o g *)
(* Proof:
   Note ?a. a IN G /\ a o x = y       by reach_def, (x ~~ y) $o g
    and ?b. b IN G /\ b o y = z       by reach_def, (y ~~ z) $o g
   Thus (b * a) o x = z               by action_trans
    and b * a IN G                    by group_op_element
    ==> (x ~~ z) $o g                 by reach_def
*)
val reach_trans = store_thm(
  "reach_trans",
  ``!$o g A x y z. Group g /\ (g act A) $o /\ x IN A /\ y IN A /\ z IN A /\
        (x ~~ y) $o g /\ (y ~~ z) $o g ==> (x ~~ z) $o g``,
  rw[reach_def] >>
  metis_tac[action_trans, group_op_element]);

(* Theorem: Reach is an equivalence relation on target set A.
            Group g /\ (g act A) $o ==> (reach $o g) equiv_on A *)
(* Proof: by equiv_on_def, reach_refl, reach_sym and reach_trans.
   By Reach being Reflexive, Symmetric and Transitive.
*)
val reach_equiv = store_thm(
  "reach_equiv",
  ``!$o g A. Group g /\ (g act A) $o ==> (reach $o g) equiv_on A``,
  rw_tac std_ss[equiv_on_def] >-
  metis_tac[reach_refl] >-
  metis_tac[reach_sym] >>
  metis_tac[reach_trans]);

(* ------------------------------------------------------------------------- *)
(* Orbits as equivalence classes of Group action.                            *)
(* ------------------------------------------------------------------------- *)

(* Orbit of action: those x in X that can be reached by a in X *)
val orbit_def = Define`
  orbit (o) (g:'a group) (A:'b -> bool) x = {a o x | a IN G}
`;
(* val orbit_def =
   val it = |- ! $o g A x. orbit $o g A x = {a o x | a IN G}: thm
*)

(* Theorem: orbit $o g A x = IMAGE (\a. a o x) G *)
(* Proof: by orbit_def, EXTENSION. *)
val orbit_as_image = store_thm(
  "orbit_as_image",
  ``!$o g A x. orbit $o g A x = IMAGE (\a. a o x) G``,
  simp[orbit_def, EXTENSION]);

(* Theorem: y IN orbit $o g A x <=> (x ~~ y) $o g *)
(* Proof: by orbit_def, reach_def *)
val orbit_element = store_thm(
  "orbit_element",
  ``!$o g A x y. y IN orbit $o g A x <=> (x ~~ y) $o g``,
  simp[orbit_def, reach_def] >>
  metis_tac[]);

(* Theorem: a IN G ==> a o x IN (orbit $o g A x) *)
(* Proof: by orbit_def *)
val orbit_has_action_element = store_thm(
  "orbit_has_action_element",
  ``!$o g A a x. a IN G ==> a o x IN (orbit $o g A x)``,
  simp[orbit_def] >>
  metis_tac[]);

(* Theorem: Group g /\ (g act A) $o /\ x IN A ==> a IN orbit $o g A x *)
(* Proof: by orbit_has_action_element, and #e o x = x *)
val orbit_has_self = store_thm(
  "orbit_has_self",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> x IN orbit $o g A x``,
  metis_tac[orbit_has_action_element, group_id_element, action_id]);;

(* Theorem: orbits are subsets of target set.
            (g act A) $o /\ x IN A ==> (orbit $o g A x) SUBSET A *)
(* Proof: orbit_def, SUBSET_DEF, action_closure. *)
val orbit_subset_target = store_thm(
  "orbit_subset_target",
  ``!$o g A x. (g act A) $o /\ x IN A ==> (orbit $o g A x) SUBSET A``,
  rw[orbit_def, SUBSET_DEF] >>
  metis_tac[action_closure]);

(* Theorem: orbits elements are in target set.
            (g act A) $o /\ x IN A /\ y IN (orbit $o g A x) ==> y IN A *)
(* Proof: orbit_subset_target, SUBSET_DEF. *)
val orbit_element_in_target = store_thm(
  "orbit_element_in_target",
  ``!$o g A x y. (g act A) $o /\ x IN A /\ y IN (orbit $o g A x) ==> y IN A``,
  metis_tac[orbit_subset_target, SUBSET_DEF]);

(* Theorem: (g act A) $o /\ x IN A /\ FINITE A ==> FINITE (orbit $o g A x) *)
(* Proof: by orbit_subset_target, SUBSET_FINITE. *)
val orbit_finite = store_thm(
  "orbit_finite",
  ``!$o g A x. (g act A) $o /\ x IN A /\ FINITE A ==> FINITE (orbit $o g A x)``,
  metis_tac[orbit_subset_target, SUBSET_FINITE]);

(* Theorem: (g act A) $o /\ x IN A ==>
            (orbit $o g A x = equiv_class (reach $o g) A x) *)
(* Proof: by orbit_def, reach_def, action_closure. *)
val orbit_as_equiv_class = store_thm(
  "orbit_as_equiv_class",
  ``!$o g A x. (g act A) $o /\ x IN A ==>
              (orbit $o g A x = {y | y IN A /\ (x ~~ y) $o g})``,
  simp[orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]);
val orbit_as_equiv_class = store_thm(
  "orbit_as_equiv_class",
  ``!$o g A x. (g act A) $o /\ x IN A ==>
              (orbit $o g A x = equiv_class (reach $o g) A x)``,
  simp[orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]);

(* Theorem: Group g /\ (g act A) $o /\ x IN A /\ y IN A ==>
                ((orbit $o g A x = orbit $o g A y) <=> (x ~~ y) $o g) *)
(* Proof: by orbit_as_equiv_class, reach_equiv, equiv_class_eq. *)
val orbit_eq_orbit = store_thm(
  "orbit_eq_orbit",
  ``!$o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN A ==>
                ((orbit $o g A x = orbit $o g A y) <=> (x ~~ y) $o g)``,
  metis_tac[orbit_as_equiv_class, reach_equiv, equiv_class_eq]);

(* ------------------------------------------------------------------------- *)
(* Partition by Group action.                                                *)
(* ------------------------------------------------------------------------- *)

(* The partitions by (reach $o g) are orbits. *)
val orbits_def = Define`
    orbits (o) (g:'a group) (A:'b -> bool) = {orbit $o g A x | x | x IN A}
`;
(* val orbits_def = |- ! $o g A. orbits $o g A = {orbit $o g A x | x | x IN A}: thm *)

(* Theorem: e IN orbits $o g A <=> ?x. x IN A /\ (e = orbit $o g A x) *)
(* Proof: by orbits_def. *)
val orbits_element = store_thm(
  "orbits_element",
  ``!$o g A e. e IN orbits $o g A <=> ?x. x IN A /\ (e = orbit $o g A x)``,
  simp[orbits_def] >>
  metis_tac[]);

(* Theorem: orbits $o g A = IMAGE (orbit $o g A) A *)
(* Proof: by orbits_def, EXTENSION. *)
val orbits_as_image = store_thm(
  "orbits_as_image",
  ``!$o g A. orbits $o g A = IMAGE (orbit $o g A) A``,
  simp[orbits_def, EXTENSION]);

(* Theorem: (g act A) $o ==> (orbits $o g A = partition (reach $o g) A) *)
(* Proof:
   By EXTENSION,
       e IN orbits $o g A
   <=> ?x. x IN A /\ e = orbit $o g A x    by orbits_def
   <=> ?x. x IN A /\ e = equiv_class (reach $o g) A x
                                           by orbit_as_equiv_class, (g act A) $o
   <=> e IN partition (reach $o g) A)      by partition_def
*)
val orbits_eq_partition = store_thm(
  "orbits_eq_partition",
  ``!$o g A. (g act A) $o ==> (orbits $o g A = partition (reach $o g) A)``,
  rw[EXTENSION] >>
  `x IN orbits o' g A <=> ?y. y IN A /\ (x = orbit o' g A y)` by metis_tac[orbits_as_image, IN_IMAGE] >>
  `_ = ?y. y IN A /\ (x = equiv_class (reach o' g) A y)` by metis_tac[orbit_as_equiv_class] >>
  fs[partition_def]);

(* Theorem: orbits = target partition is FINITE.
            (g act A) $o /\ FINITE A ==> FINITE (orbits $o g A) *)
(* Proof: by orbits_eq_partition, FINITE_partition *)
val orbits_finite = store_thm(
  "orbits_finite",
  ``!$o g A. (g act A) $o /\ FINITE A ==> FINITE (orbits $o g A)``,
  simp[orbits_eq_partition, FINITE_partition]);

(* Theorem: For e IN (orbits $o g A), FINITE A ==> FINITE e
            (g act A) $o /\ FINITE A ==> EVERY_FINITE (orbits $o g A) *)
(* Proof: by orbits_eq_partition, FINITE_partition. *)
val orbits_element_finite = store_thm(
  "orbits_element_finite",
  ``!$o g A. (g act A) $o /\ FINITE A ==> EVERY_FINITE (orbits $o g A)``,
  metis_tac[orbits_eq_partition, FINITE_partition]);
(*
orbit_finite =
|- ! $o g A x. (g act A) $o /\ x IN A /\ FINITE A ==> FINITE (orbit $o g A x)
*)

(* Theorem: For e IN (orbits $o g A), e <> EMPTY
            Group g /\ (g act A) $o ==> !e. e IN orbits $o g A ==> e <> EMPTY *)
(* Proof: by orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition. *)
val orbits_element_nonempty = store_thm(
  "orbits_element_nonempty",
  ``!$o g A. Group g /\ (g act A) $o ==> !e. e IN orbits $o g A ==> e <> EMPTY``,
  simp[orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition]);
(*
orbit_has_self:
|- ! $o g A x. Group g /\ (g act A) $o /\ x IN A ==> x IN orbit $o g A x
*)

(* Theorem: orbits elements are subset of target.
            (g act A) $o ==> !e. e IN orbits $o g A ==> e SUBSET A *)
(* Proof: by orbits_eq_partition, partition_SUBSET *)
val orbits_element_subset = store_thm(
  "orbits_element_subset",
  ``!$o g A. (g act A) $o ==> !e. e IN orbits $o g A ==> e SUBSET A``,
  metis_tac[orbits_eq_partition, partition_SUBSET]);
(*
orbit_subset_target
|- ! $o g A x. (g act A) $o /\ x IN A ==> orbit $o g A x SUBSET A
*)

(* Theorem: Elements in element of orbits are also in target.
            (g act A) $o ==> !e. e IN orbits $o g A ==> !x. x IN e ==> x IN A *)
(* Proof: by orbits_element_subset, SUBSET_DEF *)
val orbits_element_element = store_thm(
  "orbits_element_element",
  ``!$o g A. (g act A) $o ==> !e. e IN orbits $o g A ==> !x. x IN e ==> x IN A``,
  metis_tac[orbits_element_subset, SUBSET_DEF]);
(*
orbit_element_in_target
|- ! $o g A x y. (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==> y IN A
*)

(* Theorem: x IN A ==> (orbit $o g A x) IN orbits $o g A *)
(* Proof: by orbits_def *)
val orbit_is_orbits_element = store_thm(
  "orbit_is_orbits_element",
  ``!$o g A x. x IN A ==> (orbit $o g A x) IN orbits $o g A``,
  simp[orbits_def] >>
  metis_tac[]);

(* Theorem: Elements of orbits are orbits of its own element.
            Group g /\ (g act A) $o /\ e IN orbits $o g A ==>
            !x. x IN e ==> (e = orbit $o g A x) *)
(* Proof:
   By orbits_def, this is to show:
   x IN A /\ y IN orbit $o g A x ==> orbit $o g A x = orbit $o g A y

   Note y IN A                              by orbit_element_in_target
    and (x ~~ y) $o g                       by orbit_element
    ==> orbit $o g A x = orbit $o g A y     by orbit_eq_orbit
*)
val orbits_element_is_orbit = store_thm(
  "orbits_element_is_orbit",
  ``!$o g A e. Group g /\ (g act A) $o /\ e IN orbits $o g A ==>
   !x. x IN e ==> (e = orbit $o g A x)``,
  rw[orbits_def] >>
  metis_tac[orbit_element_in_target, orbit_element, orbit_eq_orbit]);
(*
orbits_element
|- ! $o g A e. e IN orbits $o g A <=> ?x. x IN A /\ (e = orbit $o g A x)
*)

(* Theorem: For action $o g A, all x in A are reachable, belong to some orbit,
            (g act A) $o /\ x IN A ==> SURJ (\a. a o x) G (orbit $o g A x). *)
(* Proof:
   This should follow from the fact that reach induces a partition, and
   the partition elements are orbits (orbit_is_orbits_element).

   By action_def, orbit_def, SURJ_DEF, this is to show:
   (1) x IN A /\ a IN G ==> ?b. (a o x = b o x) /\ b IN G
       True by taking b = a.
   (2) x IN A /\ x IN A ==> ?b. b IN G /\ (b o x = a o x)
       True by taking b = a.
*)
val action_to_orbit_surj = store_thm(
  "action_to_orbit_surj",
  ``!$o g A x. (g act A) $o /\ x IN A ==> SURJ (\a. a o x) G (orbit $o g A x)``,
  rw[action_def, orbit_def, SURJ_DEF] >>
  metis_tac[]);

(* Theorem: (g act A) $o /\ x IN A ==> (orbit $o g A x = IMAGE (\a. a o x) G) *)
(* Proof: by action_to_orbit_surj, IMAGE_SURJ. *)
val orbit_is_action_image = store_thm(
  "orbit_is_action_image",
  ``!$o g A x. (g act A) $o /\ x IN A ==> (orbit $o g A x = IMAGE (\a. a o x) G)``,
  rw[action_to_orbit_surj, GSYM IMAGE_SURJ]);
(* This is no good, as by definition:
orbit_as_image
|- ! $o g A x. orbit $o g A x = IMAGE (\a. a o x) G
*)

(* Theorem: If (\a. a o x) is INJ into orbit for action,
            then orbit is same size as the group.
            (g act A) $o /\ x IN A /\ FINITE A /\
            INJ (\a. a o x) G (orbit $o g A x) ==> (CARD (orbit $o g A x) = CARD G) *)
(* Proof:
   Note SURJ (\a. a o x) G (orbit $o g A x)     by action_to_orbit_surj
   With INJ (\a. a o x) G (orbit $o g A x)      by given
    ==> BIJ (\a. a o x) G (orbit $o g A x)      by BIJ_DEF
    Now (orbit $o g A x) SUBSET A               by orbit_subset_target
     so FINITE (orbit $o g A x)                 by SUBSET_FINITE, FINITE A
    ==> FINITE G                                by FINITE_INJ
   Thus CARD (orbit $o g A x) = CARD G          by FINITE_BIJ_CARD_EQ
*)
val orbit_finite_inj_card = store_thm(
  "orbit_finite_inj_card",
  ``!$o g A x. (g act A) $o /\ x IN A /\ FINITE A /\
      INJ (\a. a o x) G (orbit $o g A x) ==> (CARD (orbit $o g A x) = CARD G)``,
  metis_tac[action_to_orbit_surj, BIJ_DEF,
             orbit_subset_target, SUBSET_FINITE, FINITE_INJ, FINITE_BIJ_CARD_EQ]);

(* Theorem: For FINITE A, CARD A = SUM of CARD partitions in (orbits $o g A).
            Group g /\ (g act A) $o /\ FINITE A ==> (CARD A = SIGMA CARD (orbits $o g A)) *)
(* Proof:
   With orbits_eq_partition, reach_equiv, apply
   partition_CARD |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val target_card_by_partition = store_thm(
  "target_card_by_partition",
  ``!$o g A x. Group g /\ (g act A) $o /\ FINITE A ==>
         (CARD A = SIGMA CARD (orbits $o g A))``,
  metis_tac[orbits_eq_partition, reach_equiv, partition_CARD]);

(* Theorem: If for all x IN A, CARD (orbit $o g A x) = n,
            then orbits $o g A is equal size of n.
            Group g /\ (g act A) $o /\ FINITE A /\
            (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==>
            (!e. e IN orbits $o g A ==> (CARD e = n)) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit $o g A x)  by orbits_element_is_orbit
   Thus ?y. y IN e                           by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN A                               by orbits_element_element
     so CARD e = n                           by given implication.
*)
val orbits_equal_size_partition_equal_size = store_thm(
  "orbits_equal_size_partition_equal_size",
  ``!$o g A n. Group g /\ (g act A) $o /\ FINITE A /\
      (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==>
      (!e. e IN orbits $o g A ==> (CARD e = n))``,
  rpt strip_tac >>
  `!x. x IN e ==> (e = orbit o' g A x)` by rw[orbits_element_is_orbit] >>
  `?y. y IN e` by metis_tac[orbits_element_nonempty, MEMBER_NOT_EMPTY] >>
  metis_tac[orbits_element_element]);

(* Theorem: If for all x IN A, CARD (orbit $o g A x) = n, then n divides CARD A.
            Group g /\ (g act A) $o /\ FINITE A /\
            (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN orbits $o g A ==> (CARD e = n)  by orbits_equal_size_partition_equal_size
   Thus CARD A
      = n * CARD (partition (reach $o g) A)      by orbits_eq_partition, reach_equiv, equal_partition_CARD
      = CARD (partition (reach $o g) A) * n      by MULT_SYM
     so n divides (CARD A)                       by divides_def
*)
val orbits_equal_size_property = store_thm(
  "orbits_equal_size_property",
  ``!$o g A n. Group g /\ (g act A) $o /\ FINITE A /\
   (!x. x IN A ==> (CARD (orbit $o g A x) = n)) ==> n divides (CARD A)``,
  rpt strip_tac >>
  `!e. e IN orbits o' g A ==> (CARD e = n)` by metis_tac[orbits_equal_size_partition_equal_size] >>
  `CARD A = n * CARD (partition (reach o' g) A)` by rw[orbits_eq_partition, reach_equiv, equal_partition_CARD] >>
  metis_tac[divides_def, MULT_SYM]);

(* Theorem: If for all x IN A, n divides CARD (orbit $o g A x),
            then n divides size of elements in orbits $o g A.
            Group g /\ (g act A) $o /\ FINITE A /\
            (!x. x IN A ==> n divides (CARD (orbit $o g A x))) ==>
            (!e. e IN orbits $o g A ==> n divides (CARD e)) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit $o g A x)  by orbits_element_is_orbit
   Thus ?y. y IN e                           by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN A                               by orbits_element_element
     so n divides (CARD e)                   by given implication.
*)
val orbits_size_factor_partition_factor = store_thm(
  "orbits_size_factor_partition_factor",
  ``!$o g A n. Group g /\ (g act A) $o /\ FINITE A /\
      (!x. x IN A ==> n divides (CARD (orbit $o g A x))) ==>
      (!e. e IN orbits $o g A ==> n divides (CARD e))``,
  rpt strip_tac >>
  `!x. x IN e ==> (e = orbit o' g A x)` by rw[orbits_element_is_orbit] >>
  `?y. y IN e` by metis_tac[orbits_element_nonempty, MEMBER_NOT_EMPTY] >>
  metis_tac[orbits_element_element]);

(* Theorem: If for all x IN A, n divides (orbit $o g A x), then n divides CARD A.
            Group g /\ (g act A) $o /\ FINITE A /\
            (!x. x IN A ==> n divides (CARD (orbit $o g A x))) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN orbits $o g A ==> n divides (CARD e) by orbits_size_factor_partition_factor
    and reach $o g equiv_on A                         by reach_equiv
   Thus n divides (CARD A)                            by orbits_eq_partition, factor_partition_CARD
*)
val orbits_size_factor_property = store_thm(
  "orbits_size_factor_property",
  ``!$o g A n. Group g /\ (g act A) $o /\ FINITE A /\
   (!x. x IN A ==> n divides (CARD (orbit $o g A x))) ==> n divides (CARD A)``,
  metis_tac[orbits_size_factor_partition_factor, orbits_eq_partition, reach_equiv, factor_partition_CARD]);

(* ------------------------------------------------------------------------- *)
(* Stabilizer as invariant.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stabilizer of action: for x IN A, stabilizer = the group elemens that fixes x. *)
val stabilizer_def = Define`
  stabilizer (o) (g:'a group) (x:'b) = {a | a IN G /\ (a o x = x) }
`;
(*
val stabilizer_def =
   |- ! $o g x. stabilizer $o g x = {a | a IN G /\ (a o x = x)}: thm
*)

(* Theorem: a IN stabilizer $o g x <=> a IN G /\ (a o x = x) *)
(* Proof: by stabilizer_def *)
val stabilizer_element = store_thm(
  "stabilizer_element",
  ``!$o g A x a. a IN stabilizer $o g x <=> a IN G /\ (a o x = x)``,
  simp[stabilizer_def]);

(* Theorem: The (stabilizer $o g x) is a subset of G. *)
(* Proof: by stabilizer_element, SUBSET_DEF *)
val stabilizer_subset = store_thm(
  "stabilizer_subset",
  ``!$o g A x. (stabilizer $o g x) SUBSET G``,
  simp[stabilizer_element, SUBSET_DEF]);

(* Theorem: stabilizer $o g x has #e.
            Group g /\ (g act A) $o /\ x IN A ==> #e IN stabilizer $o g x *)
(* Proof:
   Note #e IN G                   by group_id_element
    and #e o x = x                by action_id
     so #e IN stabilizer $o g x   by stabilizer_element
*)
val stabilizer_has_id = store_thm(
  "stabilizer_has_id",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> #e IN stabilizer $o g x``,
  metis_tac[stabilizer_element, action_id, group_id_element]);
(* This means (stabilizer $o g x) is non-empty *)

(* Theorem: stabilizer $o g x is nonempty.
            Group g /\ (g act A) $o /\ x IN A ==> stabilizer $o g x <> EMPTY *)
(* Proof: by stabilizer_has_id, MEMBER_NOT_EMPTY. *)
val stabilizer_nonempty = store_thm(
  "stabilizer_nonempty",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> stabilizer $o g x <> EMPTY``,
  metis_tac[stabilizer_has_id, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Application:                                                              *)
(* Stabilizer subgroup.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the generator group, the exponential group of an element x of target. *)
val StabilizerGroup_def = Define`
    StabilizerGroup (o) (g:'a group) (x:'b) =
      <| carrier := stabilizer $o g x;
              op := g.op;
              id := #e
       |>
`;

(* Theorem: StabilizerGroup properties. *)
(* Proof: by StabilizerGroup_def. *)
val stabilizer_group_property = store_thm(
  "stabilizer_group_property",
  ``!$o g x. ((StabilizerGroup $o g x).carrier = stabilizer $o g x) /\
            ((StabilizerGroup $o g x).op = g.op) /\
            ((StabilizerGroup $o g x).id = #e)``,
  simp[StabilizerGroup_def]);

(* Theorem: If g is a Group, (o) g A is an action, StabilizerGroup $o g x is a Group.
            Group g /\ (g act A) $o /\ x IN A ==> Group (StabilizerGroup $o g x) *)
(* Proof:
   By group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, this is to show:
   (1) a IN G /\ b IN G /\ a o x = x /\ b o x = x ==> (a * b) o x = x
         (a * b) o x
       = a o (b o x)         by action_compose
       = a o x               by b o x = x
       = x                   by a o x = x
   (2) a IN G /\ a o x = x ==> ?b. (b IN G /\ (b o x = x)) /\ (b * a = #e)
       Let b = |/ a.
       Then b * a = #e       by group_linv
         b o x
       = ( |/ a) o x
       = ( |/ a) o (a o x)   by a o x = x
       = ( |/ a * a) o x     by action_compose
       = (#e) o x            by group_linv
       = x                   by action_id
*)
val stabilizer_group_group = store_thm(
  "stabilizer_group_group",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> Group (StabilizerGroup $o g x)``,
  rw_tac std_ss[group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, GSPECIFICATION] >>
  metis_tac[]);

(* Theorem: If g is Group, (o) g A is an action, then StabilizerGroup $o g x is a subgroup of g.
            Group g /\ (g act A) $o /\ x IN A ==> (StabilizerGroup $o g x) <= g *)
(* Proof:
   By Subgroup_def, stabilizer_group_property, this is to show:
   (1) x IN A ==> Group (StabilizerGroup $o g x), true by stabilizer_group_group
   (2) stabilizer $o g x SUBSET G, true                by stabilizer_subset
*)
val stabilizer_group_subgroup = store_thm(
  "stabilizer_group_subgroup",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==> (StabilizerGroup $o g x) <= g``,
  metis_tac[Subgroup_def, stabilizer_group_property, stabilizer_group_group, stabilizer_subset]);

(* Theorem: If g is FINITE Group, StabilizerGroup $o g x is a FINITE Group.
            FiniteGroup g /\ (g act A) $o /\ x IN A ==> FiniteGroup (StabilizerGroup $o g x) *)
(* Proof:
   By FiniteGroup_def, stabilizer_group_property, this is to show:
   (1) x IN A ==> Group (StabilizerGroup $o g x), true          by stabilizer_group_group
   (2) FINITE G /\ x IN A ==> FINITE (stabilizer $o g x), true  by stabilizer_subset and SUBSET_FINITE
*)
val stabilizer_group_finite_group = store_thm(
  "stabilizer_group_finite_group",
  ``!$o g A x. FiniteGroup g /\ (g act A) $o /\ x IN A ==>
              FiniteGroup (StabilizerGroup $o g x)``,
  rw_tac std_ss[FiniteGroup_def, stabilizer_group_property] >-
  metis_tac[stabilizer_group_group] >>
  metis_tac[stabilizer_subset, SUBSET_FINITE]);

(* Theorem: If g is FINITE Group, CARD (stabilizer $o g x) divides CARD G.
            FiniteGroup g /\ (g act A) $o /\ x IN A ==> CARD (stabilizer $o g x) divides (CARD G) *)
(* Proof:
   By Lagrange's Theorem, and (StabilizerGroup $o g x) is a subgroup of g.

   Note (StabilizerGroup $o g x) <= g                         by stabilizer_group_subgroup
    and (StabilizerGroup $o g x).carrier = stabilizer $o g x  by stabilizer_group_property
    but (stabilizer $o g x) SUBSET G                          by stabilizer_subset
   Thus CARD (stabilizer $o g x) divides (CARD G)             by Lagrange_thm
*)
val stabilizer_card_divides = store_thm(
  "stabilizer_card_divides",
  ``!$o (g:'a group) A x. FiniteGroup g /\ (g act A) $o /\ x IN A ==>
              CARD (stabilizer $o g x) divides (CARD G)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(StabilizerGroup o' g x) <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup o' g x).carrier = stabilizer o' g x` by rw[stabilizer_group_property] >>
  metis_tac[stabilizer_subset, Lagrange_thm]);

(* ------------------------------------------------------------------------- *)
(* Orbit-Stabilizer Theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The map from orbit to coset of stabilizer is well-defined.
            Group g /\ (g act A) $o /\ x IN A ==>
            !a b. a IN G /\ b IN G /\ (a o x = b o x) ==> (a * (stabilizer $o g x) = b * (stabilizer $o g x)) *)
(* Proof:
   Note StabilizerGroup $o g x <= g         by stabilizer_group_subgroup
    and (StabilizerGroup $o g x).carrier
      = stabilizer $o g x                   by stabilizer_group_property
   By subgroup_coset_eq, this is to show:
      ( |/b * a) IN (stabilizer $o g x)

   Note ( |/b * a) IN G          by group_inv_element, group_op_element
        ( |/b * a) o x
      = ( |/b) o (a o x)         by action_compose
      = ( |/b) o (b o x)         by given
      = ( |/b * b) o x           by action_compose
      = #e o x                   by group_linv
      = x                        by action_id
   Hence ( |/b * a) IN (stabilizer $o g x)  by stabilizer_element
*)
val orbit_stabilizer_map_good = store_thm(
  "orbit_stabilizer_map_good",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
   !a b. a IN G /\ b IN G /\ (a o x = b o x) ==>
   (a * (stabilizer $o g x) = b * (stabilizer $o g x))``,
  rpt strip_tac >>
  `StabilizerGroup o' g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup o' g x).carrier = stabilizer o' g x` by rw[stabilizer_group_property] >>
  fs[action_def] >>
  `( |/b * a) IN (stabilizer o' g x)` suffices_by metis_tac[subgroup_coset_eq] >>
  `o' ( |/b * a) x = o' ( |/b) (o' a x)` by rw[action_compose] >>
  `_ = o' ( |/b) (o' b x)` by asm_rewrite_tac[] >>
  `_ = o' ( |/b * b) x` by rw[] >>
  `_ = o' #e x` by rw[] >>
  `_ = x` by rw[] >>
  rw[stabilizer_element]);

(* Theorem: The map from orbit to coset of stabilizer is injective.
            Group g /\ (g act A) $o /\ x IN A ==>
            !a b. a IN G /\ b IN G /\ (a * (stabilizer $o g x) = b * (stabilizer $o g x)) ==> (a o x = b o x) *)
(* Proof:
   Note a * (stabilizer $o g x) = b * (stabilizer $o g x)
    ==> ( |/b * a) IN (stabilizer $o g x)  by subgroup_coset_eq
    ==> ( |/b * a) o x = x                 by stabilizer_element
       a o x
     = (#e * a) o x             by group_lid
     = ((b * |/ b) * a) o x     by group_rinv
     = (b * ( |/b * a)) o x     by group_assoc
     = b o (( |/b * a) o x)     by action_compose
     = b o x                    by above, x = ( |/b * a) o x
*)
val orbit_stabilizer_map_inj = store_thm(
  "orbit_stabilizer_map_inj",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
   !a b. a IN G /\ b IN G /\ (a * (stabilizer $o g x) = b * (stabilizer $o g x)) ==> (a o x = b o x)``,
  rpt strip_tac >>
  `StabilizerGroup o' g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup o' g x).carrier = stabilizer o' g x` by rw[stabilizer_group_property] >>
  `( |/b * a) IN (stabilizer o' g x)` by metis_tac[subgroup_coset_eq] >>
  `o' ( |/b * a) x = x` by fs[stabilizer_element] >>
  `|/b * a IN G` by rw[] >>
  `o' a x = o' (#e * a) x` by rw[] >>
  `_ = o' ((b * |/ b) * a) x` by rw_tac std_ss[group_rinv] >>
  `_ = o' (b * ( |/ b * a)) x` by rw[group_assoc] >>
  `_ = o' b (o' ( |/b * a) x)` by metis_tac[action_compose] >>
  metis_tac[]);

(* Theorem: For (g act A) $o /\ x IN A, !a, b in G, a o x = b o x <=> |/ a * b IN (stabilizer $o g x).
            Group g /\ (g act A) $o /\ x IN A ==>
            !a b. a IN G /\ b IN G ==> ((a o x = b o x) <=> ( |/ a * b) IN (stabilizer $o g x))  *)
(* Proof:
   If part: (a o x = b o x) ==> ( |/ a * b) IN (stabilizer $o g x)
      Note |/ a IN G                by group_inv_element
       and |/ a * b IN G            by group_op_element
       and b o x IN A               by action_closure
           ( |/ a * b) o x
         = ( |/ a) o (b o x)        by action_compose
         = x                        by action_reverse, y = b o x IN A
      Thus ( |/ a * b) IN (stabilizer $o g x)
                                    by stabilizer_element
   Only-if part: ( |/ a * b) IN (stabilizer $o g x) ==> (a o x = b o x)
      Note ( |/ a * b) IN G /\
           (( |/ a * b) o x = x)    by stabilizer_element
           a o x
         = a o (( |/a * b) o x)     by above
         = (a * ( |/ a * b)) o x    by action_compose
         = ((a * |/ a) * b) o x     by group_assoc, group_inv_element
         = (#e * b) o x             by group_rinv
         = b o x                    by group_lid
*)
val action_match_condition = store_thm(
  "action_match_condition",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
   !a b. a IN G /\ b IN G ==> ((a o x = b o x) <=> ( |/ a * b) IN (stabilizer $o g x))``,
  rw[EQ_IMP_THM] >| [
    `|/ a IN G /\ |/ a * b IN G` by rw[] >>
    `o' ( |/ a * b) x = o' ( |/ a) (o' b x)` by metis_tac[action_compose] >>
    `_ = x` by metis_tac[action_closure, action_reverse] >>
    rw[stabilizer_element],
    `( |/ a * b) IN G /\ (o' ( |/ a * b) x = x)` by metis_tac[stabilizer_element] >>
    `o' a x = o' a (o' ( |/ a * b) x)` by rw[] >>
    `_ = o' (a * ( |/ a * b)) x` by metis_tac[action_compose] >>
    `_ = o' ((a * |/ a) * b) x` by rw[group_assoc] >>
    rw[]
  ]);

(* Theorem: stabilizers of points in same orbit:
            stabilizer $o g (a o x) = a * (stabilizer $o g x) * 1/a.
            Group g /\ (g act A) $o /\ x IN A /\ a IN G ==>
            (conjugate g a (stabilizer $o g x) = stabilizer $o g (a o x)) *)
(* Proof:
   In Section 1.12 of Volume I of [Jacobson] N.Jacobson, Basic Algebra, 1980.
   [Artin] E. Artin, Galois Theory 1942.

   By conjugate_def, stabilizer_def, this is to show:
   (1) z IN G /\ z o x = x ==> a * z * |/ a IN G
       Note |/ a   IN G                  by group_inv_element
       Thus z * z * |/ a IN G            by group_op_element
   (2) z IN G /\ z o x = x ==> (a * z * |/ a) o (a o x) = a o
       Note a * z * |/ a IN G            by group_inv_element
         (a * z * |/ a) o (a o x)
       = (a * z * |/ a * a) o x          by action_compose
       = ((a * z) * ( |/ a * a)) o x     by group_assoc
       = ((a * z) * #e) o x              by group_linv
       = (a * z) o x                     by group_rid
       = a o (z o x)                     by action_compose
       = a o x                           by x = z o x
   (3) b IN G /\ b o (a o x) = a o x ==> ?z. (b = a * z * |/ a) /\ z IN G /\ (z o x = x)
       Let z = |/ a * b * a.
       Note |/ a IN G                    by group_inv_element
         so z IN G                       by group_op_element
         a * z * |/ a
       = a * ( |/ a * b * a) * |/ a      by notation
       = (a * ( |/ a)) * b * a * |/ a    by group_assoc
       = (a * ( |/ a)) * (b * a * |/ a)  by group_assoc
       = (a * |/ a) * b * (a * |/ b)     by group_assoc
       = #e * b * #e                     by group_rinv
       = b                               by group_lid, group_rid
         z o x
       = ( |/ a * b * a) o x             by notation
       = ( |/ a * (b * a)) o x           by group_assoc
       = ( |/ a) o ((b * a) o x)         by action_compose
       = ( |/ a) o (b o (a o x))         by action_compose
       = ( |/ a) o (a o x)               by given b o (a o x) = a o x
       = ( |/ a * a) o x                 by action_compose
       = #e o x                          by group_linv
       = x                               by action_id
*)
val stabilizer_conjugate = store_thm(
  "stabilizer_conjugate",
  ``!$o g A x a. Group g /\ (g act A) $o /\ x IN A /\ a IN G ==>
   (conjugate g a (stabilizer $o g x) = stabilizer $o g (a o x))``,
  rw[conjugate_def, stabilizer_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >-
 (`a * z * |/ a IN G` by rw[] >>
  `o' (a * z * |/ a) (o' a x) = o' (a * z * |/ a * a) x` by metis_tac[action_compose] >>
  `_ = o' ((a * z) * ( |/ a * a)) x` by rw[group_assoc] >>
  `_ = o' (a * z) x` by rw[] >>
  metis_tac[action_compose]) >>
  qexists_tac `|/a * x' * a` >>
  rw[] >| [
    `a * ( |/ a * x' * a) * |/ a = (a * |/ a) * x' * (a * |/ a)` by rw[group_assoc] >>
    rw[],
    `|/ a IN G /\ x' * a IN G` by rw[] >>
    `o' ( |/ a * x' * a) x = o' ( |/ a * (x' * a)) x` by rw[group_assoc] >>
    metis_tac[action_compose, group_linv, action_id]
  ]);

(* This is a major result. *)

(* Extract the existence element of reach *)
(* - reach_def;
> val it = |- !f g x y. reach $o g a b <=> ?x. x IN G /\ (a o x = y) :  thm
*)

(* Existence of act_by: the a in (x ~~ y) $o g, such that a IN G /\ a o x = y. *)
val lemma = prove(
  ``!$o (g:'a group) (x:'b) (y:'b). ?a. (x ~~ y) $o g ==> a IN G /\ (a o x = y)``,
  metis_tac[reach_def]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val act_by_def = new_specification(
    "act_by_def",
    ["act_by"],
    lemma |> SIMP_RULE bool_ss [SKOLEM_THM]
          |> CONV_RULE (RENAME_VARS_CONV ["t"] (* to allow rename of o' back to o *)
             THENC BINDER_CONV (RENAME_VARS_CONV ["o", "g", "x", "y"])));
(*
val act_by_def =
|- ! $o g x y. (x ~~ y) $o g ==> act_by $o g x y IN G /\ (act_by $o g x y o x = y): thm
*)

(* Theorem: The reachable set from x to y is the coset act_by y of (stabilizer x).
            Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
            ((act_by $o g x y) * (stabilizer $o g x) = {a | a IN G /\ (a o x = y)}) *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) c IN stabilizer $o g x ==> act_by $o g x y * c IN G
       Note act_by $o g x y IN G         by act_by_def
        and c IN G                       by stabilizer_element
         so act_by $o g x y * c IN G     by group_op_element
   (2) c IN stabilizer $o g x ==> (act_by $o g x y * c) o x = y
       Note act_by $o g x y IN G         by act_by_def
        and c IN G                       by stabilizer_element
         (act_by $o g x y * c) o x
       = (act_by $o g x y) o (c o x)     by action_compose
       = (act_by $o g x y) o x           by stabilizer_element
       = y                               by act_by_def
   (3) (x ~~ a o x) $o g /\ a IN G ==> ?c. (a = act_by $o g x (a o x) * c) /\ c IN stabilizer $o g x
       Let b = act_by $o g a (a o x)
       Then b IN G /\ (b o x = a o x)    by act_by_def
        and |/ b * a IN (stabilizer $o g x)
                                         by action_match_condition
        Let c = |/ b * a
           b * c
         = b * ( |/ b * a)        by notation
         = (b * |/ b) * a         by group_assoc
         = #e * a                 by group_rinv
         = a                      by group_lid
*)
val action_reachable_coset_1 = store_thm(
  "action_reachable_coset_1",
  ``!$o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
   ((act_by $o g x y) * (stabilizer $o g x) = {a | a IN G /\ (a o x = y)})``,
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[act_by_def, stabilizer_element, group_op_element] >-
  metis_tac[act_by_def, action_compose, stabilizer_element] >>
  qabbrev_tac `b = act_by o' g x (o' x' x)` >>
  `b IN G /\ (o' b x = o' x' x)` by rw[act_by_def, Abbr`b`] >>
  `|/ b * x' IN (stabilizer o' g x)` by metis_tac[action_match_condition] >>
  qexists_tac `|/ b * x'` >>
  `b * ( |/ b * x') = (b * |/ b) * x'` by rw[group_assoc] >>
  `_ = x'` by rw[] >>
  rw[]);

(* Another formulation of the same result. *)

(* Theorem: The reachable set from x to y is the coset act_by y of (stabilizer s).
            Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
            !a. a IN G /\ (a o x = y) ==> (a * (stabilizer $o g x) = {b | b IN G /\ (b o x = y)}) *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) c IN stabilizer $o g x ==> a * c IN G
       Note b IN G            by stabilizer_element
         so a * c IN G        by group_op_element
   (2) c IN stabilizer $o g x ==> (a * c) o x = a o x
       Note c o x = x         by stabilizer_element
         (a * c) o x
       = a o (c o x)          by action_compose
       = a o x                by above
   (3) b IN G /\ a o x = b o x ==> ?c. (b = a * c) /\ c IN stabilizer $o g x
       Let c = |/ a * b.
         a * c
       = a * ( |/ a * b)      by notation
       = (a * |/ a) * b       by group_assoc
       = #e * b               by group_rinv
       = b                    by group_lid
       For c IN stabilizer $o g x,
       Either directly        by action_match_condition, a o x = b o x
       or indirectly,
       Note c IN G            by group_inv_element, group_op_element
         c o x
       = ( |/ a * b) o x
       = ( |/ a) o (b o x)    by action_compose
       = x                    by action_reverse, y = b o x
       Hence c IN stabilizer $o g x   by stabilizer_element
*)
val action_reachable_coset_2 = store_thm(
  "action_reachable_coset_2",
  ``!$o g A x y. Group g /\ (g act A) $o /\ x IN A /\ y IN orbit $o g A x ==>
   !a. a IN G /\ (a o x = y) ==> (a * (stabilizer $o g x) = {b | b IN G /\ (b o x = y)})``,
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stabilizer_element, group_op_element] >-
  metis_tac[stabilizer_element, action_compose] >>
  qexists_tac `|/ a * x'` >>
  rpt strip_tac >-
  rw[GSYM group_assoc] >>
  metis_tac[action_match_condition]);

(* Theorem: Points of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act A) $o /\ x IN A ==>
            BIJ (\y. (act_by $o g x y) * (stabilizer $o g x)) (orbit $o g A x) {a * (stabilizer $o g x) | a IN G} *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit $o g A x ==> ?a. (act_by $o g x y * stabilizer $o g x = a * stabilizer $o g x) /\ a IN G
       Let a = act_by $o g x y.
       Note (x ~~ y) $o g        by orbit_element, y IN orbit $o g A x
       Thus a IN G               by act_by_def, a = act_by $o g x y
   (2) y IN orbit $o g A x /\ y' IN orbit $o g A x /\
       act_by $o g x y * stabilizer $o g x = act_by $o g x y' * stabilizer $o g x ==> y = y'
       Note (x ~~ y) $o g /\ (x ~~ y') $o g                 by orbit_element
        and act_by $o g x y IN G /\ act_by $o g x y' IN G   by act_by_def
       Thus y
          = (act_by $o g x y) o x       by act_by_def
          = (act_by $o g x y') o x      by orbit_stabilizer_map_inj
          = y'                          by act_by_def
   (3) same as (1)
   (4) a IN G ==> ?y. y IN orbit $o g A x /\ (act_by $o g x y * stabilizer $o g x = a * stabilizer $o g x)
       Let y = a o x.
       Then (x ~~ y) $o g               by reach_def
        and y IN A                      by action_closure
         so y IN orbit $o g A x         by orbit_element
       Let b = act_by $o g x y.
       Then a o x = y = b o x           by act_by_def
        ==> a * stabilizer $o g x = b * stabilizer $o g x
                                        by orbit_stabilizer_map_good
*)
val orbit_stabilizer_cosets_bij_3 = store_thm(
  "orbit_stabilizer_cosets_bij_3",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
   BIJ (\y. (act_by $o g x y) * (stabilizer $o g x)) (orbit $o g A x) {a * (stabilizer $o g x) | a IN G}``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
  metis_tac[orbit_element, act_by_def] >-
  metis_tac[orbit_stabilizer_map_inj, orbit_element, act_by_def] >-
  metis_tac[orbit_element, act_by_def] >>
  qexists_tac `o' a x` >>
  rpt strip_tac >-
  metis_tac[orbit_element, reach_def, action_closure] >>
  `(x ~~ (o' a x)) o' g` by metis_tac[reach_def] >>
  metis_tac[orbit_stabilizer_map_good, act_by_def]);

(* Next version is using CosetPartition *)

(* Theorem: Points of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act A) $o /\ x IN A ==>
   BIJ (\y. (act_by $o g x y) * (stabilizer $o g x)) (orbit $o g A x) (CosetPartition g (StabilizerGroup $o g x) *)
(* Proof:
   By CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit $o g A x ==>
          ?a. a IN G /\ (act_by $o g x y * stabilizer $o g x =
                         {b | b IN G /\ b IN a * stabilizer $o g x})
       Let a = act_by $o g x y.
       Note (x ~~ y) $o g       by orbit_element
        and a IN G              by act_by_def,
       By coset_def, IMAGE_DEF, EXTENSION, this is to show:
          a IN G /\ b IN stabilizer $o g x ==> a * b IN G
       Now b IN G               by stabilizer_element
       Thus a * b IN G          by group_op_element
   (2) y IN orbit $o g A x /\ y' IN orbit $o g A x /\
         act_by $o g x y * stabilizer $o g x = act_by $o g x y' * stabilizer $o g x ==> y = y'
       Note (x ~~ y) $o g /\ (x ~~ y') $o g                  by orbit_element
        and act_by $o g x y IN G /\ act_by $o g x y' IN G    by act_by_def
        ==> (act_by $o g x y) o x = (act_by $o g x y') o x   by orbit_stabilizer_map_inj
         so y = y'                                           by act_by_def
   (3) same as (1)
   (4) a IN G /\ s = {b | b IN G /\ b IN a * stabilizer $o g x} ==>
         ?y. y IN orbit $o g A x /\ (act_by $o g x y * stabilizer $o g x = s)
       Let y = a o x.
       Note (x ~~ y) $o g                    by reach_def
        and act_by $o g x y IN G /\
            (act_by $o g x y) o x = a o x    by act_by_def
        ==> act_by $o g x y * (stabilizer $o g x)
          = a * (stabilizer $o g x)          by orbit_stabilizer_map_good
      By EXTENSION, this is to show:
         !b. b IN a * stabilizer $o g x ==> b IN G
      Note b IN IMAGE (\c. a * c) (stabilizer $o g x)   by coset_def
      Thus ?c. c IN (stabilizer $o g x) /\ (b = a * z)  by IN_IMAGE
       Now c IN G                                       by stabilizer_element
      Thus b = a * c IN G                               by group_op_element
*)
val orbit_stabilizer_cosets_bij_4 = store_thm(
  "orbit_stabilizer_cosets_bij_4",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
   BIJ (\y. (act_by $o g x y) * (stabilizer $o g x)) (orbit $o g A x) (CosetPartition g (StabilizerGroup $o g x))``,
  rw[CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    qabbrev_tac `a = act_by o' g x y` >>
    qexists_tac `a` >>
    `(x ~~ y) o' g` by metis_tac[orbit_element] >>
    `a IN G` by rw[act_by_def, Abbr`a`] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    metis_tac[orbit_element, orbit_stabilizer_map_inj, act_by_def],
    qabbrev_tac `a = act_by o' g x y` >>
    qexists_tac `a` >>
    `(x ~~ y) o' g` by metis_tac[orbit_element] >>
    `a IN G` by rw[act_by_def, Abbr`a`] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    qexists_tac `o' x'' x` >>
    rpt strip_tac >-
    metis_tac[orbit_element, action_closure, reach_def] >>
    qabbrev_tac `y = o' x'' x` >>
    `(x ~~ y) o' g` by metis_tac[reach_def] >>
    `act_by o' g x y IN G /\ (o' (act_by o' g x y) x = o' x'' x)` by rw[act_by_def] >>
    `act_by o' g x y * (stabilizer o' g x) = x'' * (stabilizer o' g x)` by metis_tac[orbit_stabilizer_map_good] >>
    rw[EXTENSION, EQ_IMP_THM] >>
    metis_tac[coset_def, IN_IMAGE, stabilizer_element, group_op_element]
  ]);

(* Theorem: [Orbit-Stabilizer Theorem]
            FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
            (CARD G = CARD (orbit $o g A x) * CARD (stabilizer $o g x)) *)
(* Proof:
   Let h = StabilizerGroup $o g x
   Then h <= g                          by stabilizer_group_subgroup
    and H = stabilizer $o g x           by stabilizer_group_property
   Note CosetPartition g h
      = partition (inCoset g h) G       by CosetPartition_def
     so FINITE (CosetPartition g h)     by FINITE_partition
   Note orbit $o g A x
      = IMAGE (\a. a o x) G             by orbit_as_image
     so FINITE (orbit $o g A x)         by IMAGE_FINITE

     CARD G
   = CARD H * CARD (CosetPartition g h)                by Lagrange_identity, h <= g, FINITE G
   = CARD (stabilizer $o g x) * CARD (orbit $o g A x)  by orbit_stabilizer_cosets_bij_4, FINITE_BIJ_CARD_EQ
   = CARD (orbit $o g A x) * CARD (stabilizer $o g x)  by MULT_COMM
*)
val orbit_stabilizer_thm = store_thm(
  "orbit_stabilizer_thm",
  ``!$o (g:'a group) A x. FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
      (CARD G = CARD (orbit $o g A x) * CARD (stabilizer $o g x))``,
  rpt (stripDup[FiniteGroup_def]) >>
  `StabilizerGroup o' g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup o' g x).carrier = stabilizer o' g x` by rw[stabilizer_group_property] >>
  `FINITE (CosetPartition g (StabilizerGroup o' g x))` by metis_tac[CosetPartition_def, FINITE_partition] >>
  `FINITE (orbit o' g A x)` by rw[orbit_as_image] >>
  `CARD G = CARD (stabilizer o' g x) * CARD (CosetPartition g (StabilizerGroup o' g x))` by metis_tac[Lagrange_identity] >>
  `_ = CARD (stabilizer o' g x) * CARD (orbit o' g A x)` by metis_tac[orbit_stabilizer_cosets_bij_4, FINITE_BIJ_CARD_EQ] >>
  rw[]);

(* This is a milestone result. *)

(* Theorem: FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
            CARD (orbit $o g A x) divides CARD G *)
(* Proof:
   Let b = orbit $o g A x,
       c = stabilizer $o g x.
   Note CARD G = CARD b * CARD c      by orbit_stabilizer_thm
   Thus (CARD b) divides (CARD G)     by divides_def
*)
val orbit_card_divides_target_card = store_thm(
  "orbit_card_divides_target_card",
  ``! $o (g:'a group) A x. FiniteGroup g /\ (g act A) $o /\ x IN A /\ FINITE A ==>
               CARD (orbit $o g A x) divides CARD G``,
  prove_tac[orbit_stabilizer_thm, divides_def, MULT_COMM]);

(* ------------------------------------------------------------------------- *)
(* Fixed Points of action.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
Fixed Points have singleton orbits -- although it is not defined in this way,
this property is the theorem fixed_points_orbit_sing.

This important property of fixed points gives this simple trick:
to count how many singleton orbits, just count the set (fixed_points $o g A).

Since orbits are equivalent classes, they cannot be empty, hence singleton
orbits are the simplest type. For equivalent classes:

CARD Target = SUM CARD (orbits)
            = SUM CARD (singleton orbits) + SUM CARD (non-singleton orbits)
            = CARD (fixed_points) + SUM CARD (multi-orbits)
*)

(* Fixed points of action: f g A = {x IN A | !x in G. a o x = x} *)
val fixed_points_def = Define`
    fixed_points (o) (g:'a group) (A:'b -> bool) =
        {x | x IN A /\ (!a. a IN G ==> (a o x = x)) }
`;
(*
val fixed_points_def =
|- ! $o g A. fixed_points $o g A = {x | x IN A /\ !a. a IN G ==> (a o x = x)}: thm
*)


(* Theorem: Fixed point elements:
            x IN (fixed_points $o g A) <=> x IN A /\ !a. a IN G ==> (a o x = x) *)
(* Proof: by fixed_points_def. *)
val fixed_points_element = store_thm(
  "fixed_points_element",
  ``!$o g A x. x IN (fixed_points $o g A) <=> x IN A /\ !a. a IN G ==> (a o x = x)``,
  simp[fixed_points_def]);

(* Theorem: Fixed points are subsets of target set.
            (g act A) $o ==> (fixed_points $o g A) SUBSET A *)
(* Proof: by fixed_points_def, SUBSET_DEF. *)
val fixed_points_subset = store_thm(
  "fixed_points_subset",
  ``!$o g A. (g act A) $o ==> (fixed_points $o g A) SUBSET A``,
  simp[fixed_points_def, SUBSET_DEF]);

(* Theorem: x IN fixed_points f g A ==> x IN A *)
(* Proof: by fixed_points_def *)
val fixed_points_element_element = store_thm(
  "fixed_points_element_element",
  ``!f g A x. x IN fixed_points f g A ==> x IN A``,
  rw[fixed_points_def]);

(* ------------------------------------------------------------------------- *)
(* Fixed Points have singleton orbits.
   Or those points with stabilizer = whole group
   With ZP_ORBIT_DISTINCT,
   This gives the key result:
        fixpoints f (Z p) A <== bijective ==> (Z p).carrier
   This will make the computation of CARD (fixpoints f (Z p) A) easy.
*)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ (g act A) $o ==>
            (x IN fixed_points $o g A <=> (x IN A /\ (orbit $o g A x = {x}))) *)
(* Proof:
   By fixed_points_def, orbit_def, this is to show:
   (1) a IN G /\ (!a. a IN G ==> (a o x = x)) ==> a o x = x
       This is true                by the included implication
   (2) (!a. a IN G ==> (a o x = x)) ==> ?a. a IN G /\ (a o x = x)
       Take a = #e,
       Then a IN G                 by group_id_element
        and a o x = x              by implication
   (3) (g act A) $o /\ a IN G /\ x IN A ==> a o x = x
       This is true                by action_closure
*)
val fixed_points_orbit_sing = store_thm(
  "fixed_points_orbit_sing",
  ``!$o g A x. Group g /\ (g act A) $o ==>
       (x IN fixed_points $o g A <=> (x IN A /\ (orbit $o g A x = {x})))``,
  rw[fixed_points_def, orbit_def, EXTENSION, EQ_IMP_THM] >-
  fs[] >-
  metis_tac[group_id_element] >>
  metis_tac[action_closure]);

(* Theorem: For (g act A) $o, x IN A,
            (orbit $o g A x = {x}) ==> x IN fixed_points $o g A *)
(* Proof:
   This is to prove:
   (g act A) $o /\ x IN A /\ a IN G /\
    !y. y IN A /\ (?b. b IN G /\ (b o x = y)) <=> (y = x) ==> a o x = x
   This is true by action_closure.
*)
val orbit_sing_fixed_points = store_thm(
  "orbit_sing_fixed_points",
  ``!$o g A x. (g act A) $o /\ x IN A /\ (orbit $o g A x = {x}) ==> x IN fixed_points $o g A``,
  rw[fixed_points_def, orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]);
(* This is weaker than the previous theorem. *)

(* Theorem: Group g /\ (g act A) $o /\ x IN A ==>
            x IN fixed_points $o g A <=> SING (orbit $o g A x)) *)
(* Proof:
   By SING_DEF, this is to show:
   If part: x IN fixed_points $o g A ==> ?y. (orbit $o g A x) = {y}
      Take y = x, then true                 by fixed_points_orbit_sing
   Only-if part: (orbit $o g A x) = {y} ==> x IN fixed_points $o g A
      Note x IN (orbit $o g A x)            by orbit_has_self
      Thus y = x                            by IN_SING
        so x IN fixed_points $o g A         by fixed_points_orbit_sing
*)
val fixed_points_orbit_is_sing = store_thm(
  "fixed_points_orbit_is_sing",
  ``!$o g A x. Group g /\ (g act A) $o /\ x IN A ==>
              (x IN fixed_points $o g A <=> SING (orbit $o g A x))``,
  metis_tac[fixed_points_orbit_sing, orbit_has_self, SING_DEF, IN_SING]);

(* Theorem: Group g /\ (g act A) $o ==>
            (x IN (A DIFF fixed_points $o g A) <=> x IN A /\ ~SING (orbit $o g A x))) *)
(* Proof:
       x IN (A DIFF fixed_points $o g A)
   <=> x IN A /\ x NOTIN (fixed_points $o g A)   by IN_DIFF
   <=> x IN A /\ ~SING (orbit $o g A x))         by fixed_points_orbit_is_sing
*)
val non_fixed_points_orbit_not_sing = store_thm(
  "non_fixed_points_orbit_not_sing",
  ``!$o g A x. Group g /\ (g act A) $o ==>
        (x IN (A DIFF fixed_points $o g A) <=> (x IN A /\ ~SING (orbit $o g A x)))``,
  metis_tac[IN_DIFF, fixed_points_orbit_is_sing]);

(* Theorem: (g act A) $o /\ FINITE A ==>
            (CARD (A DIFF fixed_points $o g A) = CARD A - CARD (fixed_points $o g A)) *)
(* Proof:
   Note (fixed_points $o g A) SUBSET A                by fixed_points_def
   Thus A INTER (fixed_points $o g A)
      = (fixed_points $o g A)                         by SUBSET_INTER_ABSORPTION
     CARD (A DIFF fixed_points $o g A)
   = CARD A - CARD (A INTER (fixed_points $o g A)))   by CARD_DIFF
   = CARD A - CARD (fixed_points $o g A)              by SUBSET_INTER_ABSORPTION
*)
val non_fixed_points_card = store_thm(
  "non_fixed_points_card",
  ``!$o g A. (g act A) $o /\ FINITE A ==>
      (CARD (A DIFF fixed_points $o g A) = CARD A - CARD (fixed_points $o g A))``,
  metis_tac[CARD_DIFF, fixed_points_subset, SUBSET_INTER_ABSORPTION, SUBSET_FINITE, INTER_COMM]);

(* ------------------------------------------------------------------------- *)
(* Partition of Target into single orbits and non-single orbits.             *)
(* ------------------------------------------------------------------------- *)

(* Define singleton and non-singleton orbits *)
val sing_orbits_def = Define`
    sing_orbits (o) (g:'a group) (A:'b -> bool) = { e | e IN (orbits $o g A) /\ SING e }
`;
val multi_orbits_def = Define`
    multi_orbits (o) (g:'a group) (A:'b -> bool) = { e | e IN (orbits $o g A) /\ ~SING e }
`;
(*
val sing_orbits_def =
|- ! $o g A. sing_orbits $o g A = {e | e IN orbits $o g A /\ SING e}: thm
val multi_orbits_def =
|- ! $o g A. multi_orbits $o g A = {e | e IN orbits $o g A /\ ~SING e}: thm
*)

(* Theorem: e IN sing_orbits $o g A <=> e IN (orbits $o g A) /\ SING e *)
(* Proof: by sing_orbits_def *)
val sing_orbits_element = store_thm(
  "sing_orbits_element",
  ``!$o g A e. e IN sing_orbits $o g A <=> (e IN (orbits $o g A) /\ SING e)``,
  simp[sing_orbits_def]);

(* Theorem: (sing_orbits $o g A) SUBSET (orbits $o g A) *)
(* Proof: by sing_orbits_element, SUBSET_DEF *)
val sing_orbits_subset = store_thm(
  "sing_orbits_subset",
  ``!$o g A. (sing_orbits $o g A) SUBSET (orbits $o g A)``,
  simp[sing_orbits_element, SUBSET_DEF]);

(* Theorem: (g act A) $o /\ FINITE A ==> FINITE (sing_orbits $o g A)*)
(* Proof: by sing_orbits_subset, orbits_finite, SUBSET_FINITE *)
val sing_orbits_finite = store_thm(
  "sing_orbits_finite",
  ``!$o g A. (g act A) $o /\ FINITE A ==> FINITE (sing_orbits $o g A)``,
  metis_tac[sing_orbits_subset, orbits_finite, SUBSET_FINITE]);

(* Theorem: For (g act A) $o, elements of (sing_orbits $o g A) are subsets of A.
            (g act A) $o /\ e IN (sing_orbits $o g A) ==> e SUBSET A *)
(* Proof: by sing_orbits_element, orbits_element_subset *)
val sing_orbits_element_subset = store_thm(
  "sing_orbits_element_subset",
  ``!$o g A e. (g act A) $o /\ e IN (sing_orbits $o g A) ==> e SUBSET A``,
  metis_tac[sing_orbits_element, orbits_element_subset]);

(* Theorem: e IN (sing_orbits $o g A) ==> FINITE e *)
(* Proof: by sing_orbits_element, SING_FINITE *)
val sing_orbits_element_finite = store_thm(
  "sing_orbits_element_finite",
  ``!$o g A e. e IN (sing_orbits $o g A) ==> FINITE e``,
  simp[sing_orbits_element, SING_FINITE]);

(* Theorem: e IN (sing_orbits $o g A) ==> (CARD e = 1) *)
(* Proof: by sing_orbits_element, SING_DEF, CARD_SING *)
val sing_orbits_element_card = store_thm(
  "sing_orbits_element_card",
  ``!$o g A e. e IN (sing_orbits $o g A) ==> (CARD e = 1)``,
  metis_tac[sing_orbits_element, SING_DEF, CARD_SING]);

(* Theorem: Group g /\ (g act A) $o /\
            e IN (sing_orbits $o g A) ==> CHOICE e IN fixed_points $o g A *)
(* Proof:
   Note e IN orbits $o g A /\ SING e      by sing_orbits_element
   Thus ?x. e = {x}                       by SING_DEF
    ==> x IN e /\ (CHOICE e = x)          by IN_SING, CHOICE_SING
     so e = orbit $o g A x                by orbits_element_is_orbit, x IN e
    and x IN A                            by orbits_element_element
    ==> x IN fixed_points $o g A          by orbit_sing_fixed_points
*)
val sing_orbits_element_choice = store_thm(
  "sing_orbits_element_choice",
  ``!$o g A e. Group g /\ (g act A) $o /\
              e IN (sing_orbits $o g A) ==> CHOICE e IN fixed_points $o g A``,
  rw[sing_orbits_element] >>
  `?x. e = {x}` by rw[GSYM SING_DEF] >>
  `x IN e /\ (CHOICE e = x)` by rw[] >>
  `e = orbit o' g A x` by rw[orbits_element_is_orbit] >>
  metis_tac[orbit_sing_fixed_points, orbits_element_element]);

(* Theorem: e IN multi_orbits $o g A <=> e IN (orbits $o g A) /\ ~SING e *)
(* Proof: by multi_orbits_def *)
val multi_orbits_element = store_thm(
  "multi_orbits_element",
  ``!$o g A e. e IN multi_orbits $o g A <=> (e IN (orbits $o g A) /\ ~SING e)``,
  simp[multi_orbits_def]);

(* Theorem: (multi_orbits $o g A) SUBSET (orbits $o g A) *)
(* Proof: by multi_orbits_element, SUBSET_DEF *)
val multi_orbits_subset = store_thm(
  "multi_orbits_subset",
  ``!$o g A. (multi_orbits $o g A) SUBSET (orbits $o g A)``,
  simp[multi_orbits_element, SUBSET_DEF]);

(* Theorem: (g act A) $o /\ FINITE A ==> FINITE (multi_orbits $o g A)*)
(* Proof: by multi_orbits_subset, orbits_finite, SUBSET_FINITE *)
val multi_orbits_finite = store_thm(
  "multi_orbits_finite",
  ``!$o g A. (g act A) $o /\ FINITE A ==> FINITE (multi_orbits $o g A)``,
  metis_tac[multi_orbits_subset, orbits_finite, SUBSET_FINITE]);

(* Theorem: For (g act A) $o, elements of (multi_orbits $o g A) are subsets of A.
            (g act A) $o /\ e IN (multi_orbits $o g A) ==> e SUBSET A *)
(* Proof: by multi_orbits_element, orbits_element_subset *)
val multi_orbits_element_subset = store_thm(
  "multi_orbits_element_subset",
  ``!$o g A e. (g act A) $o /\ e IN (multi_orbits $o g A) ==> e SUBSET A``,
  metis_tac[multi_orbits_element, orbits_element_subset]);

(* Theorem: (g act A) $o /\ e IN (multi_orbits $o g A) ==> FINITE e *)
(* Proof: by multi_orbits_element, orbits_element_finite *)
val multi_orbits_element_finite = store_thm(
  "multi_orbits_element_finite",
  ``!$o g A e. (g act A) $o /\ FINITE A /\ e IN (multi_orbits $o g A) ==> FINITE e``,
  metis_tac[multi_orbits_element, orbits_element_finite]);

(* Theorem: sing_orbits and multi_orbits are disjoint.
            DISJOINT (sing_orbits $o g A) (multi_orbits $o g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def *)
val sing_multi_orbits_disjoint = store_thm(
  "sing_multi_orbits_disjoint",
  ``!$o g A. DISJOINT (sing_orbits $o g A) (multi_orbits $o g A)``,
  simp[sing_orbits_def, multi_orbits_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: orbits = sing_orbits + multi_orbits.
            orbits $o g A = (sing_orbits $o g A) UNION (multi_orbits $o g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def. *)
val sing_multi_orbits_union = store_thm(
  "sing_multi_orbits_union",
  ``!$o g A. orbits $o g A = (sing_orbits $o g A) UNION (multi_orbits $o g A)``,
  simp[sing_orbits_def, multi_orbits_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For (g act A) $o, CARD A = CARD sing_orbits + SIGMA CARD multi_orbits.
            Group g /\ (g act A) $o /\ FINITE A ==>
            (CARD A = CARD (sing_orbits $o g A) + SIGMA CARD (multi_orbits $o g A)) *)
(* Proof:
   Let s = sing_orbits $o g A, t = multi_orbits $o g A.
   Note FINITE s                   by sing_orbits_finite
    and FINITE t                   by multi_orbits_finite
   also s INTER t = {}             by sing_multi_orbits_disjoint, DISJOINT_DEF

     CARD A
   = SIGMA CARD (orbits $o g A)    by target_card_by_partition
   = SIGMA CARD (s UNION t)        by sing_multi_orbits_union
   = SIGMA CARD s + SIGMA CARD t   by SUM_IMAGE_UNION, SUM_IMAGE_EMPTY
   = 1 * CARD s + SIGMA CARD t     by sing_orbits_element_card, SIGMA_CARD_CONSTANT
   = CARD s + SIGMA CARD t         by MULT_LEFT_1
*)
val target_card_by_orbit_types = store_thm(
  "target_card_by_orbit_types",
  ``!$o g A. Group g /\ (g act A) $o /\ FINITE A ==>
      (CARD A = CARD (sing_orbits $o g A) + SIGMA CARD (multi_orbits $o g A))``,
  rpt strip_tac >>
  qabbrev_tac `s = sing_orbits o' g A` >>
  qabbrev_tac `t = multi_orbits o' g A` >>
  `FINITE s` by rw[sing_orbits_finite, Abbr`s`] >>
  `FINITE t` by rw[multi_orbits_finite, Abbr`t`] >>
  `s INTER t = {}` by rw[sing_multi_orbits_disjoint, GSYM DISJOINT_DEF, Abbr`s`, Abbr`t`] >>
  `CARD A = SIGMA CARD (orbits o' g A)` by rw_tac std_ss[target_card_by_partition] >>
  `_ = SIGMA CARD (s UNION t)` by rw_tac std_ss[sing_multi_orbits_union] >>
  `_ = SIGMA CARD s + SIGMA CARD t` by rw[SUM_IMAGE_UNION, SUM_IMAGE_EMPTY] >>
  `_ = 1 * CARD s + SIGMA CARD t` by metis_tac[sing_orbits_element_card, SIGMA_CARD_CONSTANT] >>
  simp[]);

(* Theorem: The map: e IN (sing_orbits $o g A) --> x IN (fixed_points $o g A)  where e = {a} is injective.
            Group g /\ (g act A) $o ==> INJ CHOICE (sing_orbits $o g A) (fixed_points $o g A) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) e IN sing_orbits $o g A ==> CHOICE e IN fixed_points $o g A
       This is true                    by sing_orbits_element_choice
   (2) e IN sing_orbits $o g A /\ e' IN sing_orbits $o g A /\ CHOICE e = CHOICE e' ==> e = e'
       Note SING e /\ SING e'          by sing_orbits_element
       Thus this is true               by SING_DEF, CHOICE_SING.
*)
val sing_orbits_to_fixed_points_inj = store_thm(
  "sing_orbits_to_fixed_points_inj",
  ``!$o g A. Group g /\ (g act A) $o ==>
      INJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)``,
  rw[INJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  metis_tac[sing_orbits_element, SING_DEF, CHOICE_SING]);

(* Theorem: The map: e IN (sing_orbits $o g A) --> x IN (fixed_points $o g A)  where e = {a} is surjective.
            Group g /\ (g act A) $o ==> SURJ CHOICE (sing_orbits $o g A) (fixed_points $o g A) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) e IN sing_orbits $o g A ==> CHOICE e IN fixed_points $o g A
       This is true                       by sing_orbits_element_choice
   (2) x IN fixed_points $o g A ==> ?e. e IN sing_orbits $o g A /\ (CHOICE e = x)
       Note x IN A                        by fixed_points_element
        and orbit f g A x = {x}           by fixed_points_orbit_sing
       Take e = {x},
       Then CHOICE e = x                  by CHOICE_SING
        and SING e                        by SING_DEF
        and e IN orbits $o g A            by orbit_is_orbits_element
        ==> e IN sing_orbits $o g A       by sing_orbits_element
*)
val sing_orbits_to_fixed_points_surj = store_thm(
  "sing_orbits_to_fixed_points_surj",
  ``!$o g A. Group g /\ (g act A) $o ==>
      SURJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)``,
  rw[SURJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  `x IN A` by metis_tac[fixed_points_element] >>
  `orbit o' g A x = {x}` by metis_tac[fixed_points_orbit_sing] >>
  qexists_tac `{x}` >>
  simp[sing_orbits_element] >>
  metis_tac[orbit_is_orbits_element]);

(* Theorem: The map: e IN (sing_orbits $o g A) --> x IN (fixed_points $o g A)  where e = {a} is bijective.
            Group g /\ (g act A) $o ==> BIJ CHOICE (sing_orbits $o g A) (fixed_points $o g A) *)
(* Proof: by sing_orbits_to_fixed_points_inj, sing_orbits_to_fixed_points_surj, BIJ_DEF.
          True since the map is shown to be both injective and surjective.
*)
val sing_orbits_to_fixed_points_bij = store_thm(
  "sing_orbits_to_fixed_points_bij",
  ``!$o g A. Group g /\ (g act A) $o ==>
      BIJ CHOICE (sing_orbits $o g A) (fixed_points $o g A)``,
  simp[BIJ_DEF, sing_orbits_to_fixed_points_surj, sing_orbits_to_fixed_points_inj]);

(* Theorem: For (g act A) $o, sing_orbits is the same size as fixed_points $o g A,
            Group g /\ (g act A) $o /\ FINITE A ==> (CARD (sing_orbits $o g A) = CARD (fixed_points $o g A)) *)
(* Proof:
   Let s = sing_orbits $o g A, t = fixed_points $o g A.
   Note s SUBSET (orbits $o g A)   by sing_orbits_def
    and t SUBSET A                 by fixed_points_def
   Also FINITE s                   by orbits_finite, SUBSET_FINITE
    and FINITE t                   by SUBSET_FINITE
   With BIJ CHOICE s t             by sing_orbits_to_fixed_points_bij
    ==> CARD s = CARD t            by FINITE_BIJ_CARD_EQ
*)
val sing_orbits_card_eqn = store_thm(
  "sing_orbits_card_eqn",
  ``!$o g A. Group g /\ (g act A) $o /\ FINITE A ==>
      (CARD (sing_orbits $o g A) = CARD (fixed_points $o g A))``,
  rpt strip_tac >>
  `(sing_orbits o' g A) SUBSET (orbits o' g A)` by rw[sing_orbits_def, SUBSET_DEF] >>
  `(fixed_points o' g A) SUBSET A` by rw[fixed_points_def, SUBSET_DEF] >>
  metis_tac[sing_orbits_to_fixed_points_bij, FINITE_BIJ_CARD_EQ, SUBSET_FINITE, orbits_finite]);

(* Theorem: For (g act A) $o, CARD A = CARD fixed_points + SIGMA CARD multi_orbits.
            Group g /\ (g act A) $o /\ FINITE A ==>
            (CARD A = CARD (fixed_points $o g A) + SIGMA CARD (multi_orbits $o g A)) *)
(* Proof:
   Let s = sing_orbits $o g A, t = multi_orbits $o g A.
     CARD A
   = CARD s + SIGMA CARD t                       by target_card_by_orbit_types
   = CARD (fixed_points $o g A) + SIGMA CARD t   by sing_orbits_card_eqn
*)
val target_card_by_fixed_points = store_thm(
  "target_card_by_fixed_points",
  ``!$o g A. Group g /\ (g act A) $o /\ FINITE A ==>
      (CARD A = CARD (fixed_points $o g A) + SIGMA CARD (multi_orbits $o g A))``,
  metis_tac[target_card_by_orbit_types, sing_orbits_card_eqn]);

(* Theorem:  Group g /\ (g act A) $o /\ FINITE A /\ 0 < n /\
             (!e. e IN multi_orbits $o g A ==> (CARD e = n)) ==>
             (CARD A MOD n = CARD (fixed_points $o g A) MOD n) *)
(* Proof:
   Let b = fixed_points $o g A,
       c = multi_orbits $o g A.
   Note FINITE c                         by multi_orbits_finite
       (CARD A) MOD n
     = (CARD b + SIGMA CARD c) MOD n     by target_card_by_fixed_points
     = (CARD b + n * CARD c) MOD n       by SIGMA_CARD_CONSTANT, FINITE c
     = (CARD c * n + CARD b) MOD n       by ADD_COMM, MULT_COMM
     = (CARD b) MOD n                    by MOD_TIMES
*)
val target_card_and_fixed_points_congruence = store_thm(
  "target_card_and_fixed_points_congruence",
  ``! $o (g:'a group) A n. Group g /\ (g act A) $o /\ FINITE A /\ 0 < n /\
               (!e. e IN multi_orbits $o g A ==> (CARD e = n)) ==>
               (CARD A MOD n = CARD (fixed_points $o g A) MOD n)``,
  rpt strip_tac >>
  imp_res_tac target_card_by_fixed_points >>
  `_ = CARD (fixed_points o' g A) + n * CARD (multi_orbits o' g A)` by rw[multi_orbits_finite, SIGMA_CARD_CONSTANT] >>
  fs[]);

(* This is a very useful theorem! *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
