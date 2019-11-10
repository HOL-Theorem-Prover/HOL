(* ------------------------------------------------------------------------- *)
(* Group Action, Orbits and Fixed points.                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupAction";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

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

*)

(*===========================================================================*)

(* ------------------------------------------------------------------------- *)
(* Group Action Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (g act A) f    = action f g A
   (a ~~ b) f g   = reach f g a b
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Group action:
   action_def       |- !f g A. (g act A) f <=> !a. a IN A ==>
                               (!x. x IN G ==> f x a IN A) /\ (f #e a = a) /\
                                !x y. x IN G /\ y IN G ==> (f x (f y a) = f (x * y) a)
   action_closure   |- !f g A. (g act A) f ==> !x a. x IN G /\ a IN A ==> f x a IN A
   action_compose   |- !f g A. (g act A) f ==>
                       !x y a. x IN G /\ y IN G /\ a IN A ==> (f x (f y a) = f (x * y) a)
   action_id        |- !f g A. (g act A) f ==> !a. a IN A ==> (f #e a = a)
   action_reverse   |- !f g A. Group g /\ (g act A) f ==>
                       !a b x. x IN G /\ a IN A /\ b IN A /\ (f x a = b) ==> (f ( |/ x) b = a)
   action_trans     |- !f g A. (g act A) f ==> !a b c x y. x IN G /\ y IN G /\
                       a IN A /\ b IN A /\ c IN A /\ (f x a = b) /\ (f y b = c) ==> (f (y * x) a = c)

   Group action induces an equivalence relation:
   reach_refl   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> (a ~~ a) f g
   reach_sym    |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ (a ~~ b) f g ==> (b ~~ a) f g
   reach_trans  |- !f g A a b c. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ c IN A /\
                                 (a ~~ b) f g /\ (b ~~ c) f g ==> (a ~~ c) f g
   reach_equiv  |- !f g A. Group g /\ (g act A) f ==> reach f g equiv_on A

   Partition by Group action:
   TargetPartition_def     |- !f g A. TargetPartition f g A = partition (reach f g) A
   target_partition_finite |- !f g A. (g act A) f /\ FINITE A ==> FINITE (TargetPartition f g A)
   target_partition_element_finite
                           |- !f g A. (g act A) f /\ FINITE A ==> EVERY_FINITE (TargetPartition f g A)
   target_partition_element_nonempty
                           |- !f g A. Group g /\ (g act A) f ==> !e. e IN TargetPartition f g A ==> e <> {}
   target_partition_element_subset
                           |- !f g A. (g act A) f ==> !e. e IN TargetPartition f g A ==> e SUBSET A
   target_partition_element_element
                           |- !f g A. (g act A) f ==> !e. e IN TargetPartition f g A ==> !a. a IN e ==> a IN A

   Orbits as equivalence classes:
   orbit_def                   |- !f g A a. orbit f g A a = equiv_class (reach f g) A a
   orbit_element               |- !f g A a b. b IN orbit f g A a <=> b IN A /\ (a ~~ b) f g
   orbit_as_image              |- !f g A a. (g act A) f /\ a IN A ==> (orbit f g A a = IMAGE (\x. f x a) G)
   orbit_description           |- !f g A a. (g act A) f /\ a IN A ==> (orbit f g A a = {f x a | x IN G})
   orbit_has_action_element    |- !f g A a x. (g act A) f /\ a IN A /\ x IN G ==> f x a IN orbit f g A a
   orbit_has_self              |- !f g A a x. Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g A a
   orbit_subset_target         |- !f g A a. (g act A) f /\ a IN A ==> orbit f g A a SUBSET A
   orbit_is_target_partition_element
                               |- !f g A a. a IN A ==> orbit f g A a IN TargetPartition f g A
   target_partition_element_is_orbit
                               |- !f g A e. Group g /\ (g act A) f /\ e IN TargetPartition f g A ==>
                                  !a. a IN e ==> (orbit f g A a = e)
   action_to_orbit_surj        |- !f g A a. (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g A a)
   orbit_is_action_image       |- !f g A a. (g act A) f /\ a IN A ==> (orbit f g A a = IMAGE (\x. f x a) G)
   orbit_finite_inj_card       |- !f g A a. (g act A) f /\ FINITE A /\ a IN A /\
                                  INJ (\x. f x a) G (orbit f g A a) ==> (CARD (orbit f g A a) = CARD G)
   target_card_by_partition    |- !f g A a. Group g /\ (g act A) f /\ FINITE A ==>
                                  (CARD A = SIGMA CARD (TargetPartition f g A))
   orbits_equal_size_partition_equal_size
                               |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                  (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==>
                                   !e. e IN TargetPartition f g A ==> (CARD e = n)
   orbits_equal_size_property  |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                  (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==> n divides CARD A
   orbits_size_factor_partition_factor
                               |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                  (!a. a IN A ==> n divides CARD (orbit f g A a)) ==>
                                   !e. e IN TargetPartition f g A ==> n divides CARD e
   orbits_size_factor_property |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                  (!a. a IN A ==> n divides CARD (orbit f g A a)) ==> n divides CARD A

   Stabilizer as invariant:
   stabilizer_def        |- !f g a. stabilizer f g a = {x | x IN G /\ (f x a = a)}
   stabilizer_element    |- !f g A a x. x IN stabilizer f g a <=> x IN G /\ (f x a = a)
   stabilizer_subset     |- !f g A a. stabilizer f g a SUBSET G
   stabilizer_has_id     |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a
   stabilizer_nonempty   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> {}

   Stabilizer subgroup:
   StabilizerGroup_def            |- !f g a. StabilizerGroup f g a =
                                             <|carrier := stabilizer f g a; op := $*; id := #e|>
   stabilizer_group_property      |- !f g a. ((StabilizerGroup f g a).carrier = stabilizer f g a) /\
                                             ((StabilizerGroup f g a).op = $* ) /\
                                             ((StabilizerGroup f g a).id = #e)
   stabilizer_group_group         |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> Group (StabilizerGroup f g a)
   stabilizer_group_subgroup      |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> StabilizerGroup f g a <= g
   stabilizer_group_finite_group  |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
                                               FiniteGroup (StabilizerGroup f g a)
   stabilizer_card_divides        |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
                                               CARD (stabilizer f g a) divides CARD G

   Orbit-Stabilizer Theorem:
   orbit_stabilizer_map_good |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                !x y. x IN G /\ y IN G /\ (f x a = f y a) ==>
                                      (x * stabilizer f g a = y * stabilizer f g a)
   orbit_stabilizer_map_inj  |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                !x y. x IN G /\ y IN G /\ (x * stabilizer f g a = y * stabilizer f g a) ==>
                                      (f x a = f y a)
   action_match_condition    |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                !x y. x IN G /\ y IN G ==> ((f x a = f y a) <=> |/ x * y IN stabilizer f g a)
   stabilizer_conjugate      |- !f g A a x. Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
                                            (conjugate g x (stabilizer f g a) = stabilizer f g (f x a))
   act_by_def                |- !f g a b. (a ~~ b) f g ==> act_by f g a b IN G /\ (f (act_by f g a b) a = b)
   action_reachable_coset_1  |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
                                (act_by f g a b * stabilizer f g a = {x | x IN G /\ (f x a = b)})
   action_reachable_coset_2  |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
                                !x. x IN G /\ (f x a = b) ==> (x * stabilizer f g a = {y | y IN G /\ (f y a = b)})
   orbit_stabilizer_cosets_bij_3   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                      BIJ (\b. act_by f g a b * stabilizer f g a)
                                          (orbit f g A a)
                                          {x * stabilizer f g a | x | x IN G}
   orbit_stabilizer_cosets_bij_4   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                      BIJ (\b. act_by f g a b * stabilizer f g a)
                                          (orbit f g A a)
                                          (CosetPartition g (StabilizerGroup f g a))
   orbit_stabilizer_thm      |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
                                          (CARD G = CARD (orbit f g A a) * CARD (stabilizer f g a))

   Fixed Points of action:
   fixed_points_def          |- !f g A. fixed_points f g A = {a | a IN A /\ !x. x IN G ==> (f x a = a)}
   fixed_points_element      |- !f g A a. a IN fixed_points f g A <=> a IN A /\ !x. x IN G ==> (f x a = a)
   fixed_points_subset       |- !f g A. (g act A) f ==> fixed_points f g A SUBSET A
   fixed_points_orbit_sing   |- !f g A. Group g /\ (g act A) f ==>
                                !a. a IN fixed_points f g A <=> (orbit f g A a = {a})
   orbit_sing_fixed_points   |- !f g A. (g act A) f ==>
                                !a. a IN A /\ (orbit f g A a = {a}) ==> a IN fixed_points f g A
   fixed_points_orbit_is_sing       |- !f g A. Group g /\ (g act A) f ==>
                                        !a. a IN A ==> (a IN fixed_points f g A <=> SING (orbit f g A a))
   non_fixed_points_orbit_not_sing  |- !f g A. Group g /\ (g act A) f ==>
                                       !a. a IN A DIFF fixed_points f g A <=> a IN A /\ ~SING (orbit f g A a)
   non_fixed_points_card            |- !f g A. (g act A) f /\ FINITE A ==>
                                       (CARD (A DIFF fixed_points f g A) = CARD A - CARD (fixed_points f g A))

   Target Partition by orbits:
   sing_orbits_def                  |- !f g A. sing_orbits f g A = {e | e IN TargetPartition f g A /\ SING e}
   multi_orbits_def                 |- !f g A. multi_orbits f g A = {e | e IN TargetPartition f g A /\ ~SING e}
   sing_orbits_element              |- !f g A e. e IN sing_orbits f g A <=> e IN TargetPartition f g A /\ SING e
   sing_orbits_subset               |- !f g A. sing_orbits f g A SUBSET TargetPartition f g A
   sing_orbits_finite               |- !f g A. (g act A) f /\ FINITE A ==> FINITE (sing_orbits f g A)
   sing_orbits_element_subset       |- !f g A e. (g act A) f /\ e IN sing_orbits f g A ==> e SUBSET A
   sing_orbits_element_finite       |- !f g A e. e IN sing_orbits f g A ==> FINITE e
   sing_orbits_element_card         |- !f g A e. e IN sing_orbits f g A ==> (CARD e = 1)
   sing_orbits_element_choice       |- !f g A. Group g /\ (g act A) f ==>
                                       !e. e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
   multi_orbits_element             |- !f g A e. e IN multi_orbits f g A <=> e IN TargetPartition f g A /\ ~SING e
   multi_orbits_subset              |- !f g A. multi_orbits f g A SUBSET TargetPartition f g A
   multi_orbits_finite              |- !f g A. (g act A) f /\ FINITE A ==> FINITE (multi_orbits f g A)
   multi_orbits_element_subset      |- !f g A e. (g act A) f /\ e IN multi_orbits f g A ==> e SUBSET A
   multi_orbits_element_finite      |- !f g A e. (g act A) f /\ FINITE A /\ e IN multi_orbits f g A ==> FINITE e
   target_orbits_disjoint           |- !f g A. DISJOINT (sing_orbits f g A) (multi_orbits f g A)
   target_eq_orbits_union           |- !f g A. TargetPartition f g A = sing_orbits f g A UNION multi_orbits f g A
   target_card_by_orbit_types       |- !f g A. Group g /\ (g act A) f /\ FINITE A ==>
                                       (CARD A = CARD (sing_orbits f g A) + SIGMA CARD (multi_orbits f g A))
   sing_orbits_to_fixed_points_inj  |- !f g A. Group g /\ (g act A) f ==>
                                               INJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)
   sing_orbits_to_fixed_points_surj |- !f g A. Group g /\ (g act A) f ==>
                                               SURJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g
   sing_orbits_to_fixed_points_bij  |- !f g A. Group g /\ (g act A) f ==>
                                               BIJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)
   sing_orbits_card_eqn             |- !f g A. Group g /\ (g act A) f /\ FINITE A ==>
                                               (CARD (sing_orbits f g A) = CARD (fixed_points f g A))
   target_card_by_fixed_points      |- !f g A. Group g /\ (g act A) f /\ FINITE A ==>
                                       (CARD A = CARD (fixed_points f g A) + SIGMA CARD (multi_orbits f g A))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Group action                                                              *)
(* ------------------------------------------------------------------------- *)

(* An action from group g to a set A is a map f: G x A -> A such that
   (0)   [is a map] f (x in G)(a in A) in A
   (1)  [id action] f (e in G)(a in A) = a
   (2) [composable] f (x in G)(f (y in G)(a in A)) =
                    f (g.op (x in G)(y in G))(a in A)
*)
val action_def = Define`
    action f (g:'a group) (A:'b -> bool) =
       !a. a IN A ==> (!x. x IN G ==> f x a IN A) /\
                      (f #e a = a) /\
                      (!x y. x IN G /\ y IN G ==> (f x (f y a) = f (x * y) a))
`;

(* Overload on action *)
val _ = overload_on("act", ``\(g:'a group) (A:'b -> bool) f. action f g A``);
val _ = set_fixity "act" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> action_def;
val it = |- !(f :'a -> 'b -> 'b) (g :'a group) (A :'b -> bool).
     (g act A) f <=> !(a :'b). a IN A ==>
       (!(x :'a). x IN G ==> f x a IN A) /\ (f #e a = a) /\
       !(x :'a) (y :'a). x IN G /\ y IN G ==> (f x (f y a) = f ((x * y) :'a) a): thm
*)

(* export simple result -- bad idea for huge expansion. *)
(* val _ = export_rewrites["action_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Action Properties                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Closure] (g act A) f ==> !x a. x IN G /\ a IN A ==> f x a IN A *)
(* Proof: by action_def. *)
val action_closure = store_thm(
  "action_closure",
  ``!f g (A:'b -> bool). (g act A) f ==> !x a. x IN G /\ a IN A ==> f x a IN A``,
  rw[action_def]);

(* Theorem: [Compose] (g act A) f ==> !x y a. x IN G /\ y IN G /\ a IN A ==> (f x (f y a) = f (x * y) a) *)
(* Proof: by action_def. *)
val action_compose = store_thm(
  "action_compose",
  ``!f g (A:'b -> bool). (g act A) f ==> !x y a. x IN G /\ y IN G /\ a IN A ==> (f x (f y a) = f (x * y) a)``,
  rw[action_def]);

(* Theorem: [Identity] (g act A) f ==> !a. a IN A ==> (f #e a = a) *)
(* Proof: by action_def. *)
val action_id = store_thm(
  "action_id",
  ``!f g (A:'b -> bool). (g act A) f ==> !a. a IN A ==> (f #e a = a)``,
  rw[action_def]);
(* This is essentially reach_refl *)

(* Theorem: Group g /\ (g act A) f ==>
           !a b x. x IN G /\ a IN A /\ b IN A /\(f x a = b) ==> (f ( |/ x) b = a) *)
(* Proof:
   Note |/ x IN G        by group_inv_element
     f ( |/ x) b
   = f ( |/ x) (f x a)   by b = f x a
   = f ( |/ x * x) a     by action_compose
   = f #e a              by group_linv
   = a                   by action_id
*)
val action_reverse = store_thm(
  "action_reverse",
  ``!f g (A:'b -> bool). Group g /\ (g act A) f ==>
   !a b x. x IN G /\ a IN A /\ b IN A /\(f x a = b) ==> (f ( |/ x) b = a)``,
  rw[action_def]);
(* This is essentially reach_sym *)

(* Theorem: (g act A) f ==> !a b c x y. x IN G /\ y IN G /\
            a IN A /\ b IN A /\ c IN A /\ (f x a = b) /\ (f y b = c) ==> (f (y * x) a = c) *)
(* Proof:
     f (y * x) a
   = f y (f x a)     by action_compose
   = f y b           by b = f x a
   = c               by c = f y b
*)
val action_trans = store_thm(
  "action_trans",
  ``!f g (A:'b -> bool). (g act A) f ==> !a b c x y. x IN G /\ y IN G /\
       a IN A /\ b IN A /\ c IN A /\ (f x a = b) /\ (f y b = c) ==> (f (y * x) a = c)``,
  rw[action_def]);
(* This is essentially reach_trans *)

(* ------------------------------------------------------------------------- *)
(* Group action induces an equivalence relation.                             *)
(* ------------------------------------------------------------------------- *)

(* Define reach to relate two action points a and b in A *)
val reach_def = Define`
    reach f (g:'a group) (a:'b) (b:'b) = ?x. x IN G /\ (f x a = b)
`;
(* Overload reach relation *)
val _ = temp_overload_on("~~", ``\(a:'b) (b:'b) f (g:'a group). reach f g a b``);
(* Make reach an infix. *)
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> reach_def;
val it = |- !f g a b. (a ~~ b) f g <=> ?x. x IN G /\ (f x a = b): thm
*)

(* Theorem: [Reach is Reflexive]
            Group g /\ (g act A) f /\ a IN A ==> (a ~~ a) f g  *)
(* Proof:
   Note f #e a = a         by action_id
    and #e in G            by group_id_element
   Thus (a reach a) f g    by reach_def, take x = #e.
*)
val reach_refl = store_thm(
  "reach_refl",
  ``!f g (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==> (a ~~ a) f g``,
  metis_tac[reach_def, action_id, group_id_element]);

(* Theorem: [Reach is Symmetric]
            Group g /\ (g act A) f /\ a IN A /\ b IN A /\ (a ~~ b) f g ==> (b ~~ a) f g *)
(* Proof:
   Note ?x. x IN G /\ f x a = b     by reach_def, (a ~~ b) f g
    ==> f ( |/ x) b = a             by action_reverse
    and |/ x IN G                   by group_inv_element
   Thus (b ~~ a) f g                by reach_def
*)
val reach_sym = store_thm(
  "reach_sym",
  ``!f g (A:'b -> bool) a b. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ (a ~~ b) f g ==> (b ~~ a) f g``,
  metis_tac[reach_def, action_reverse, group_inv_element]);

(* Theorem: [Reach is Transitive]
            Group g /\ (g act A) f /\ a IN A /\ b IN A /\ c IN A /\
            (a ~~ b) f g /\ (b ~~ c) f g ==> (a ~~ c) f g *)
(* Proof:
   Note ?x. x IN G /\ f x a = b       by reach_def, (a ~~ b) f g
    and ?y. y IN G /\ f y b = c       by reach_def, (b ~~ c) f g
   Thus f (y * x) a = c               by action_trans
    and y * x IN G                    by group_op_element
    ==> (a reach c) f g               by reach_def
*)
val reach_trans = store_thm(
  "reach_trans",
  ``!f g (A:'b -> bool) a b c. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ c IN A /\
        (a ~~ b) f g /\ (b ~~ c) f g ==> (a ~~ c) f g``,
  rw[reach_def] >>
  metis_tac[action_trans, group_op_element]);

(* Theorem: Reach is an equivalence relation on target set A.
            Group g /\ (g act A) f ==> (reach f g) equiv_on A *)
(* Proof:
   By Reach being Reflexive, Symmetric and Transitive.
*)
val reach_equiv = store_thm(
  "reach_equiv",
  ``!f g (A:'b -> bool). Group g /\ (g act A) f ==> (reach f g) equiv_on A``,
  rw_tac std_ss[equiv_on_def] >-
  metis_tac[reach_refl] >-
  metis_tac[reach_sym] >>
  metis_tac[reach_trans]);

(* ------------------------------------------------------------------------- *)
(* Partition by Group action.                                                *)
(* ------------------------------------------------------------------------- *)

(* Define partitions of Target set A by (reach f g). *)
val TargetPartition_def = Define`
    TargetPartition f (g:'a group) (A:'b -> bool) = partition (reach f g) A
`;

(* Theorem: Target partition is FINITE.
            (g act A) f /\ FINITE A ==> FINITE (TargetPartition f g A) *)
(* Proof: by TargetPartition_def, FINITE_partition *)
val target_partition_finite = store_thm(
  "target_partition_finite",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f /\ FINITE A ==> FINITE (TargetPartition f g A)``,
  rw[TargetPartition_def, FINITE_partition]);

(* Theorem: For e IN (TargetPartition f g A), FINITE A ==> FINITE e
            (g act A) f /\ FINITE A ==> EVERY_FINITE (TargetPartition f g A) *)
(* Proof: by TargetPartition_def, FINITE_partition. *)
val target_partition_element_finite = store_thm(
  "target_partition_element_finite",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f /\ FINITE A ==> EVERY_FINITE (TargetPartition f g A)``,
  metis_tac[TargetPartition_def, FINITE_partition]);

(* Theorem: For e IN (TargetPartition f g A), e <> EMPTY
            Group g /\ (g act A) f ==> !e. e IN TargetPartition f g A ==> e <> EMPTY *)
(* Proof: by TargetPartition_def, reach_equiv, EMPTY_NOT_IN_partition. *)
val target_partition_element_nonempty = store_thm(
  "target_partition_element_nonempty",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==> !e. e IN TargetPartition f g A ==> e <> EMPTY``,
  rw[TargetPartition_def, reach_equiv, EMPTY_NOT_IN_partition]);

(* Theorem: TargetPartition elements are subset of target.
            (g act A) f ==> !e. e IN TargetPartition f g A ==> e SUBSET A *)
(* Proof: by TargetPartition_def, partition_def, SUBSET_DEF *)
val target_partition_element_subset = store_thm(
  "target_partition_element_subset",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f ==> !e. e IN TargetPartition f g A ==> e SUBSET A``,
  rw[TargetPartition_def, partition_def] >>
  fs[SUBSET_DEF]);

(* Theorem: Elements in Element of TargetPartition are also in target.
            (g act A) f ==> !e. e IN TargetPartition f g A ==> !a. a IN e ==> a IN A *)
(* Proof: by target_partition_element_subset, SUBSET_DEF *)
val target_partition_element_element = store_thm(
  "target_partition_element_element",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f ==> !e. e IN TargetPartition f g A ==> !a. a IN e ==> a IN A``,
  metis_tac[target_partition_element_subset, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Orbits as equivalence classes.                                            *)
(* ------------------------------------------------------------------------- *)

(* Orbit of action: those x in X that can be reached by a in X *)
val orbit_def = Define`
  orbit f (g:'a group) (A:'b -> bool) a = equiv_class (reach f g) A a
`;
(* Same as:
   orbit f g A a = {b | b IN A /\ reach f g a b}
   orbit f g A a = {b | b IN A /\ (a ~~ b) f g}
*)

(* Theorem: b IN orbit f g A a ==> b IN A /\ (a ~~ b) f g *)
(* Proof: by orbit_def *)
val orbit_element = store_thm(
  "orbit_element",
  ``!f (g:'a group) (A:'b -> bool) a b. b IN orbit f g A a <=> b IN A /\ (a ~~ b) f g``,
  rw[orbit_def]);

(* Theorem: (g act A) f /\ a IN A ==> orbit f g A a = IMAGE (\x. f x a) G *)
(* Proof: by definitions. *)
val orbit_as_image = store_thm(
  "orbit_as_image",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ a IN A ==> (orbit f g A a = IMAGE (\x. f x a) G)``,
  (rw[action_def, orbit_def, reach_def, EXTENSION, EQ_IMP_THM] >> metis_tac[]));
(* Note: This is the same as: orbit_is_action_image *)

(* Theorem: (g act A) f /\ a IN A ==> (orbit f g A a = {f x a | x IN G} *)
(* Proof: by orbit_as_image, IMAGE_DEF. *)
val orbit_description = store_thm(
  "orbit_description",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ a IN A ==> (orbit f g A a = {f x a | x IN G})``,
  metis_tac[orbit_as_image, IMAGE_DEF]);

(* Theorem: (g act A) f /\ a IN A /\ x IN G ==> f x a IN (orbit f g A a) *)
(* Proof: by orbit_as_image, IN_IMAGE *)
val orbit_has_action_element = store_thm(
  "orbit_has_action_element",
  ``!f (g:'a group) (A:'b -> bool) a x. (g act A) f /\ a IN A /\ x IN G ==> f x a IN (orbit f g A a)``,
  rpt strip_tac >>
  qabbrev_tac `h = \x. f x a` >>
  `orbit f g A a = IMAGE h G` by rw[orbit_as_image, Abbr`h`] >>
  `!z. h z = f z a` by rw[Abbr`h`] >>
  metis_tac[IN_IMAGE]);

(* Theorem: Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g A a *)
(* Proof: by orbit_has_action_element, and f #e a = a *)
val orbit_has_self = store_thm(
  "orbit_has_self",
  ``!f (g:'a group) (A:'b -> bool) a x. Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g A a``,
  rw[orbit_def] >>
  metis_tac[reach_refl]);

(* Theorem: orbits are subsets of target set.
            (g act A) f /\ a IN A ==> (orbit f g A a) SUBSET A *)
(* Proof: orbit_def, SUBSET_DEF. *)
val orbit_subset_target = store_thm(
  "orbit_subset_target",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ a IN A ==> (orbit f g A a) SUBSET A``,
  rw[orbit_def, SUBSET_DEF]);

(* Theorem: a IN A ==> (orbit f g A a) IN TargetPartition f g A *)
(* Proof: by TargetPartition_def, partition_def, orbit_def *)
val orbit_is_target_partition_element = store_thm(
  "orbit_is_target_partition_element",
  ``!f (g:'a group) (A:'b -> bool) a. a IN A ==> (orbit f g A a) IN TargetPartition f g A``,
  rw[TargetPartition_def, partition_def, orbit_def] >>
  metis_tac[]);

(* Theorem: Elements of TargetPartition are orbits of its own element.
            Group g /\ (g act A) f /\ e IN TargetPartition f g A ==> !a. a IN e ==> (e = orbit f g A a) *)
(* Proof:
   By TargetPartition_def, partition_def, orbit_def, this is to show:
   (1) x' IN e ==> x' IN A, true            by e is a partition of A
   (2) (x ~~ a) f g /\ (x ~~ x') f g ==> (a ~~ x') f g
           (x ~~ a) f g /\ (x ~~ x') f g
       ==> (a ~~ x) f g /\ (x ~~ x') f g    by reach_sym
       ==> (a ~~ x') f g                    by reach_trans
   (3) a IN e /\ (a ~~ x') f g ==> x' IN e
       Note (x ~~ a) f g                    by orbit_def, a IN e
       So  (x ~~ a) f g /\ a ~~ x') f g
       ==> (x ~~ x') f g                    by reach_trans
       Therefore x' IN e                    by orbit_def
*)
val target_partition_element_is_orbit = store_thm(
  "target_partition_element_is_orbit",
  ``!f (g:'a group) (A:'b -> bool) e. Group g /\ (g act A) f /\ e IN TargetPartition f g A ==>
   !a. a IN e ==> (orbit f g A a = e)``,
  rw[TargetPartition_def, partition_def, orbit_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[reach_trans] >-
  metis_tac[] >>
  metis_tac[reach_sym, reach_trans]);

(* Theorem: For action f g A, all a in X are reachable, belong to some orbit,
            (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g A a). *)
(* Proof:
   This should follow from the fact that reach induces a partition, and
   the partition elements are orbits (orbit_is_target_partition_element).
   Is such a proof more complicated, or simpler, than the one below?

   By action_def, orbit_def, SURJ_DEF, this is to show:
   (1) a IN A /\ x IN G ==> (a ~~ f x a) f g
       Note (f x a) IN A              by action_def
       Thus (a ~~ f x a) f g          by reach_def
   (2) a IN A /\ x IN A /\ (a ~~ x) f g ==> ?x'. x' IN G /\ (f x' a = x)
       Note (a ~~ x) f g
        ==> ?z. z IN G /\ (f z a = x)  by reach_def
       so just take x' = z.
*)
val action_to_orbit_surj = store_thm(
  "action_to_orbit_surj",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g A a)``,
  rw[action_def, orbit_def, SURJ_DEF] >>
  metis_tac[reach_def]);

(* Theorem: (g act A) f /\ a IN A ==> (orbit f g A a = IMAGE (\x. f x a) G) *)
(* Proof: by action_to_orbit_surj, IMAGE_SURJ. *)
val orbit_is_action_image = store_thm(
  "orbit_is_action_image",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ a IN A ==> (orbit f g A a = IMAGE (\x. f x a) G)``,
  rw[action_to_orbit_surj, GSYM IMAGE_SURJ]);

(* Theorem: If (\x. f x a) is INJ into orbit for action, then orbit is same size as the group.
            (g act A) f /\ FINITE A /\ a IN A /\
            INJ (\x. f x a) G (orbit f g A a) ==> (CARD (orbit f g A a) = CARD G) *)
(* Proof:
   Note SURJ (\x. f x a) G (orbit f g A a)     by action_to_orbit_surj
   With INJ (\x. f x a) G (orbit f g A a)      by given
    ==> BIJ (\x. f x a) G (orbit f g A a)      by BIJ_DEF
    Now (orbit f g A a) SUBSET A               by orbit_subset_target
     so FINITE (orbit f g A a)                 by SUBSET_FINITE, FINITE A
    ==> FINITE G                               by FINITE_INJ
   Thus CARD (orbit f g A a) = CARD G          by FINITE_BIJ_CARD_EQ
*)
val orbit_finite_inj_card = store_thm(
  "orbit_finite_inj_card",
  ``!f (g:'a group) (A:'b -> bool) a. (g act A) f /\ FINITE A /\ a IN A /\
      INJ (\x. f x a) G (orbit f g A a) ==> (CARD (orbit f g A a) = CARD G)``,
  metis_tac[action_to_orbit_surj, BIJ_DEF,
             orbit_subset_target, SUBSET_FINITE, FINITE_INJ, FINITE_BIJ_CARD_EQ]);

(* Theorem: For FINITE A, CARD A = SUM of CARD partitions in (TargetPartition f g A).
            Group g /\ (g act A) f /\ FINITE A ==> (CARD A = SIGMA CARD (TargetPartition f g A)) *)
(* Proof:
   With TargetPartition_def, reach_equiv, apply
   partition_CARD |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val target_card_by_partition = store_thm(
  "target_card_by_partition",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ FINITE A ==>
         (CARD A = SIGMA CARD (TargetPartition f g A))``,
  metis_tac[TargetPartition_def, reach_equiv, partition_CARD]);

(* Theorem: If for all a IN A, CARD (orbit f g A a) = n, then TargetPartition f g A is equal size of n.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==>
            (!e. e IN TargetPartition f g A ==> (CARD e = n)) *)
(* Proof:
   Note !a. a IN e ==> (e = orbit f g A a)      by target_partition_element_is_orbit
   Thus ?y. y IN e                              by target_partition_element_nonempty, MEMBER_NOT_EMPTY
    But y IN A                                  by target_partition_element_element
     so CARD e = n                              by given implication.
*)
val orbits_equal_size_partition_equal_size = store_thm(
  "orbits_equal_size_partition_equal_size",
  ``!f (g:'a group) (A:'b -> bool) n. Group g /\ (g act A) f /\ FINITE A /\
      (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==>
      (!e. e IN TargetPartition f g A ==> (CARD e = n))``,
  rpt strip_tac >>
  `!a. a IN e ==> (e = orbit f g A a)` by rw[target_partition_element_is_orbit] >>
  `?y. y IN e` by metis_tac[target_partition_element_nonempty, MEMBER_NOT_EMPTY] >>
  metis_tac[target_partition_element_element]);

(* Theorem: If for all a IN A, CARD (orbit f g A a) = n, then n divides CARD A.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN TargetPartition f g A ==> (CARD e = n)  by orbits_equal_size_partition_equal_size
   Thus CARD A = n * CARD (partition (reach f g) A)      by TargetPartition_def, reach_equiv, equal_partition_CARD
               = CARD (partition (reach f g) A) * n      by MULT_SYM
     so n divides (CARD A)                               by divides_def
*)
val orbits_equal_size_property = store_thm(
  "orbits_equal_size_property",
  ``!f (g:'a group) (A:'b -> bool) n. Group g /\ (g act A) f /\ FINITE A /\
      (!a. a IN A ==> (CARD (orbit f g A a) = n)) ==> n divides (CARD A)``,
  rpt strip_tac >>
  `!e. e IN TargetPartition f g A ==> (CARD e = n)` by metis_tac[orbits_equal_size_partition_equal_size] >>
  `CARD A = n * CARD (partition (reach f g) A)` by rw[TargetPartition_def, reach_equiv, equal_partition_CARD] >>
  metis_tac[divides_def, MULT_SYM]);

(* Theorem: If for all a IN A, n divides CARD (orbit f g A a),
               then n divides size of elements in TargetPartition f g A.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> n divides (CARD (orbit f g A a))) ==>
            (!e. e IN TargetPartition f g A ==> n divides (CARD e)) *)
(* Proof:
   Note !a. a IN e ==> (e = orbit f g A a)      by target_partition_element_is_orbit
   Thus ?y. y IN e                              by target_partition_element_nonempty, MEMBER_NOT_EMPTY
    But y IN A                                  by target_partition_element_element
     so n divides CARD e                        by given implication.
*)
val orbits_size_factor_partition_factor = store_thm(
  "orbits_size_factor_partition_factor",
  ``!f (g:'a group) (A:'b -> bool) n. Group g /\ (g act A) f /\ FINITE A /\
      (!a. a IN A ==> n divides (CARD (orbit f g A a))) ==>
      (!e. e IN TargetPartition f g A ==> n divides (CARD e))``,
  rpt strip_tac >>
  `!a. a IN e ==> (e = orbit f g A a)` by rw[target_partition_element_is_orbit] >>
  `?y. y IN e` by metis_tac[target_partition_element_nonempty, MEMBER_NOT_EMPTY] >>
  metis_tac[target_partition_element_element]);

(* Theorem: If for all a IN A, n divides (orbit f g A a), then n divides CARD A.
            Group g /\ action f g A /\ FINITE A /\
            (!a. a IN A ==> n divides (CARD (orbit f g A a))) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN TargetPartition f g A ==> n divides (CARD e)   by orbits_size_factor_partition_factor
    and reach f g equiv_on A                                    by reach_equiv
   Thus n divides (CARD A)                                      by TargetPartition_def, factor_partition_CARD
*)
val orbits_size_factor_property = store_thm(
  "orbits_size_factor_property",
  ``!f (g:'a group) (A:'b -> bool) n. Group g /\ action f g A /\ FINITE A /\
   (!a. a IN A ==> n divides (CARD (orbit f g A a))) ==> n divides (CARD A)``,
  metis_tac[orbits_size_factor_partition_factor, TargetPartition_def, reach_equiv, factor_partition_CARD]);

(* ------------------------------------------------------------------------- *)
(* Stabilizer as invariant.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stabilizer of action: for a in A, stabilizer of a = {x in G | f x a = a} *)
val stabilizer_def = Define`
  stabilizer f (g:'a group) (a:'b) = {x | x IN G /\ (f x a = a) }
`;

(* Theorem: x IN stabilizer f g a ==> x IN G /\ (f x a = a) *)
(* Proof: by stabilizer_def *)
val stabilizer_element = store_thm(
  "stabilizer_element",
  ``!f (g:'a group) (A:'b -> bool) a x. x IN stabilizer f g a <=> x IN G /\ (f x a = a)``,
  rw[stabilizer_def]);

(* Theorem: The stabilizer (f g a) is a subset of G. *)
(* Proof: by stabilizer_element, SUBSET_DEF *)
val stabilizer_subset = store_thm(
  "stabilizer_subset",
  ``!f (g:'a group) (A:'b -> bool) a. (stabilizer f g a) SUBSET G``,
  rw[stabilizer_element, SUBSET_DEF]);

(* Theorem: stabilizer f g a has #e.
            Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a *)
(* Proof:
   Note #e IN G                   by group_id_element
    and f #e a = a                by action_id
     so #e IN stabilizer f g a    by stabilizer_element
*)
val stabilizer_has_id = store_thm(
  "stabilizer_has_id",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a``,
  metis_tac[stabilizer_element, action_id, group_id_element]);
(* This means (stabilizer f g a) is non-empty *)

(* Theorem: stabilizer f g a is nonempty.
            Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> EMPTY *)
(* Proof: by stabilizer_has_id, MEMBER_NOT_EMPTY. *)
val stabilizer_nonempty = store_thm(
  "stabilizer_nonempty",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> EMPTY``,
  metis_tac[stabilizer_has_id, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Application:                                                              *)
(* Stabilizer subgroup.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the generator group, the exponential group of an element a of group g *)
val StabilizerGroup_def = Define`
    StabilizerGroup f (g:'a group) (a:'b) =
      <| carrier := stabilizer f g a;
              op := g.op;
              id := #e
       |>
`;

(* Theorem: StabilizerGroup properties. *)
(* Proof: by StabilizerGroup_def. *)
val stabilizer_group_property = store_thm(
  "stabilizer_group_property",
  ``!f (g:'a group) (a:'b). ((StabilizerGroup f g a).carrier = stabilizer f g a) /\
      ((StabilizerGroup f g a).op = g.op) /\ ((StabilizerGroup f g a).id = #e)``,
  rw[StabilizerGroup_def]);

(* Theorem: If g is a Group, f g A is an action, StabilizerGroup f g a is a Group.
            Group g /\ (g act A) f /\ a IN A ==> Group (StabilizerGroup f g a) *)
(* Proof:
   By group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, this is to show:
   (1) x IN G /\ y IN G /\ f x a = a /\ f y a = a ==> f (x * y) a = a
         f (x * y) a
       = f x (f y a)         by action_compose
       = f x a               by f y a = a
       = a                   by f x a = a
   (2) x IN G /\ f x a = a ==> ?y. (y IN G /\ (f y a = a)) /\ (y * x = #e)
       Let y = |/ x.
       Then y * x = #e       by group_linv
         f ( |/x) a
       = f ( |/x) (f x a)    by f x a = a
       = f ( |/x * x) a      by action_def
       = f (#e) a            by group_linv
       = a                   by action_def
*)
val stabilizer_group_group = store_thm(
  "stabilizer_group_group",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==> Group (StabilizerGroup f g a)``,
  rw_tac std_ss[group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, GSPECIFICATION] >>
  metis_tac[]);

(* Theorem: If g is Group, f g A is an action, then StabilizerGroup f g a is a subgroup of g.
            Group g /\ (g act A) f /\ a IN A ==> (StabilizerGroup f g a) <= g *)
(* Proof:
   By Subgroup_def, stabilizer_group_property, this is to show:
   (1) a IN A ==> Group (StabilizerGroup f g a), true by stabilizer_group_group
   (2) stabilizer f g a SUBSET G, true                by stabilizer_subset
*)
val stabilizer_group_subgroup = store_thm(
  "stabilizer_group_subgroup",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==> (StabilizerGroup f g a) <= g``,
  metis_tac[Subgroup_def, stabilizer_group_property, stabilizer_group_group, stabilizer_subset]);

(* Theorem: If g is FINITE Group, StabilizerGroup f g a is a FINITE Group.
            FiniteGroup g /\ (g act A) f /\ a IN A ==> FiniteGroup (StabilizerGroup f g a) *)
(* Proof:
   By FiniteGroup_def, stabilizer_group_property, this is to show:
   (1) a IN A ==> Group (StabilizerGroup f g a), true          by stabilizer_group_group
   (2) FINITE G /\ a IN A ==> FINITE (stabilizer f g a), true  by stabilizer_subset and SUBSET_FINITE
*)
val stabilizer_group_finite_group = store_thm(
  "stabilizer_group_finite_group",
  ``!f (g:'a group) (A:'b -> bool) a.
   FiniteGroup g /\ (g act A) f /\ a IN A ==> FiniteGroup (StabilizerGroup f g a)``,
  rw_tac std_ss[FiniteGroup_def, stabilizer_group_property] >-
  metis_tac[stabilizer_group_group] >>
  metis_tac[stabilizer_subset, SUBSET_FINITE]);

(* Theorem: If g is FINITE Group, CARD (stabilizer f g a) divides CARD G.
            FiniteGroup g /\ (g act A) f /\ a IN A ==> CARD (stabilizer f g a) divides (CARD G) *)
(* Proof:
   By Lagrange's Theorem, and (StabilizerGroup f g a) is a subgroup of g.

   Note (StabilizerGroup f g a) <= g                         by stabilizer_group_subgroup
    and (StabilizerGroup f g a).carrier = stabilizer f g a   by stabilizer_group_property
    but (stabilizer f g a) SUBSET G                          by stabilizer_subset
  Thus CARD (stabilizer f g a) divides (CARD G)              by Lagrange_thm
*)
val stabilizer_card_divides = store_thm(
  "stabilizer_card_divides",
  ``!f (g:'a group) (A:'b -> bool) a.
   FiniteGroup g /\ (g act A) f /\ a IN A ==> CARD (stabilizer f g a) divides (CARD G)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(StabilizerGroup f g a) <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  metis_tac[stabilizer_subset, Lagrange_thm]);

(* ------------------------------------------------------------------------- *)
(* Orbit-Stabilizer Theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The map from orbit to coset of stabilizer is well-defined.
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\ (f x a = f y a) ==> (x * (stabilizer f g a) = y * (stabilizer f g a)) *)
(* Proof:
   Note StabilizerGroup f g a <= g         by stabilizer_group_subgroup
    and (StabilizerGroup f g a).carrier
      = stabilizer f g a                   by stabilizer_group_property
   By subgroup_coset_eq, this is to show:
      ( |/y * x) IN (stabilizer f g a)

   Note ( |/y * x) IN G          by group_inv_element, group_op_element
        f ( |/y * x) a
      = f ( |/y) (f x a)         by action_compose
      = f ( |/y) (f y a)         by given
      = f ( |/y * y) a           by action_compose
      = f #e a                   by group_linv
      = a                        by action_id
   Hence  ( |/y * x) IN (stabilizer f g a)  by stabilizer_element
*)
val orbit_stabilizer_map_good = store_thm(
  "orbit_stabilizer_map_good",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
   !x y. x IN G /\ y IN G /\ (f x a = f y a) ==>
   (x * (stabilizer f g a) = y * (stabilizer f g a))``,
  rpt strip_tac >>
  `StabilizerGroup f g a <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  fs[action_def] >>
  `( |/y * x) IN (stabilizer f g a)` suffices_by metis_tac[subgroup_coset_eq] >>
  `f ( |/y * x) a = f ( |/y) (f x a)` by rw[action_compose] >>
  `_ = f ( |/y) (f y a)` by asm_rewrite_tac[] >>
  `_ = f ( |/y * y) a` by rw[] >>
  `_ = f #e a` by rw[] >>
  `_ = a` by rw[] >>
  rw[stabilizer_element]);

(* Theorem: The map from orbit to coset of stabilizer is injective.
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\ (x * (stabilizer f g a) = y * (stabilizer f g a)) ==> (f x a = f y a) *)
(* Proof:
   Note x * (stabilizer f g a) = y * (stabilizer f g a)
    ==> ( |/y * x) IN (stabilizer f g a)   by subgroup_coset_eq
    ==> f ( |/y * x) a = a                 by stabilizer_element
       f x a
     = f (#e * x) a             by group_lid
     = f ((y * |/ y) * x) a     by group_rinv
     = f (y * ( |/y * x)) a     by group_assoc
     = f y (f ( |/y * x) a)     by action_compose
     = f y a                    by above, a = f ( |/y * x) a
*)
val orbit_stabilizer_map_inj = store_thm(
  "orbit_stabilizer_map_inj",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
   !x y. x IN G /\ y IN G /\ (x * (stabilizer f g a) = y * (stabilizer f g a)) ==> (f x a = f y a)``,
  rpt strip_tac >>
  `StabilizerGroup f g a <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  `( |/y * x) IN (stabilizer f g a)` by metis_tac[subgroup_coset_eq] >>
  `f ( |/y * x) a = a` by fs[stabilizer_element] >>
  `|/y * x IN G` by rw[] >>
  `f x a = f (#e * x) a` by rw[] >>
  `_ = f ((y * |/ y) * x) a` by rw_tac std_ss[group_rinv] >>
  `_ = f (y * ( |/ y * x)) a` by rw[group_assoc] >>
  `_ = f y (f ( |/y * x) a)` by metis_tac[action_compose] >>
  metis_tac[]);

(* Theorem: For action f g A /\ a IN A, !x, y in G, f x a = f y a <=> |/ x * y IN (stabilizer f g a).
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G ==> ((f x a = f y a) <=> ( |/ x * y) IN (stabilizer f g a))  *)
(* Proof:
   If part: (f x a = f y a) ==> ( |/ x * y) IN (stabilizer f g a)
      Note |/ x IN G                by group_inv_element
       and |/ x * y IN G            by group_op_element
           f ( |/ x * y) a
         = f ( |/ x) (f y a)        by action_compose
         = a                        by action_closure, action_reverse
      Thus ( |/ x * y) IN (stabilizer f g a)
                                    by stabilizer_element
   Only-if part: ( |/ x * y) IN (stabilizer f g a) ==> (f x a = f y a)
      Note ( |/ x * y) IN G /\
           (f ( |/ x * y) a = a)    by stabilizer_element
           f x a
         = f x (f ( |/x * y) a)     by above
         = f (x * ( |/ x * y)) a    by action_compose
         = f ((x * |/ x) * y) a     by group_assoc, group_inv_element
         = f (#e * y) a             by group_rinv
         = f y a                    by group_lid
*)
val action_match_condition = store_thm(
  "action_match_condition",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
   !x y. x IN G /\ y IN G ==> ((f x a = f y a) <=> ( |/ x * y) IN (stabilizer f g a))``,
  rw[EQ_IMP_THM] >| [
    `|/ x IN G /\ |/ x * y IN G` by rw[] >>
    `f ( |/ x * y) a = f ( |/ x) (f y a)` by metis_tac[action_compose] >>
    `_ = a` by metis_tac[action_closure, action_reverse] >>
    rw[stabilizer_element],
    `( |/ x * y) IN G /\ (f ( |/ x * y) a = a)` by metis_tac[stabilizer_element] >>
    `f x a = f x (f ( |/x * y) a)` by rw[] >>
    `_ = f (x * ( |/ x * y)) a` by metis_tac[action_compose] >>
    `_ = f ((x * |/ x) * y) a` by rw[group_assoc] >>
    rw[]
  ]);

(* Theorem: stabilizers of points in same orbit:
            stabilizer f g (f z a) = z * (stabilizer f g a) * 1/z.
            Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
            (conjugate g x (stabilizer f g a) = stabilizer f g (f x a)) *)
(* Proof:
   In Section 1.12 of Volume I of [Jacobson] N.Jacobson, Basic Algebra, 1980.
   [Artin] E. Artin, Galois Theory 1942.

   By conjugate_def, stabilizer_def, this is to show:
   (1) z IN G /\ f z a = a ==> x * z * |/ x IN G
       Note |/ x   IN G                  by group_inv_element
       Thus x * z * |/ x IN G            by group_op_element
   (2) z IN G /\ f z a = a ==> f (x * z * |/ x) (f x a) = f x a
       Note x * z * |/ x IN G            by group_inv_element
         f (x * z * |/ x) (f x a)
       = f (x * z * |/ x * x) a          by action_compose
       = f ((x * z) * ( |/ x * x)) a     by group_assoc
       = f ((x * z) * #e) a              by group_linv
       = f (x * z) a                     by group_rid
       = f x (f z a)                     by action_compose
       = f x a                           by a = f z a
   (3) x' IN G /\ f x' (f x a) = f x a ==> ?z. (x' = x * z * |/ x) /\ z IN G /\ (f z a = a)
       Let z = |/ x * x' * x.
       Note |/ x IN G                    by group_inv_element
         so z IN G                       by group_op_element
         x * z * |/ x
       = x * ( |/ x * x' * x) * |/ x     by notation
       = (x * ( |/ x)) * x' * x * |/ x   by group_assoc
       = (x * ( |/ x)) * (x' * x * |/ x) by group_assoc
       = (x * |/ x) * x' * (x * |/ x)    by group_assoc
       = #e * x' * #e                    by group_rinv
       = x'                              by group_lid, group_rid
         f z a
       = f ( |/ x * x' * x) a            by notation
       = f ( |/ x * (x' * x)) a          by group_assoc
       = f ( |/ x) (f (x' * x) a)        by action_compose
       = f ( |/ x) (f x' (f x a))        by action_compose
       = f ( |/ x) (f x a)               by given f x' (f x a) = f x a
       = f ( |/ x * x) a                 by action_compose
       = f #e a                          by group_linv
       = a                               by action_id
*)
val stabilizer_conjugate = store_thm(
  "stabilizer_conjugate",
  ``!f (g:'a group) (A:'b -> bool) a x. Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
   (conjugate g x (stabilizer f g a) = stabilizer f g (f x a))``,
  rw[conjugate_def, stabilizer_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >-
 (`x * z * |/ x IN G` by rw[] >>
  `f (x * z * |/ x) (f x a) = f (x * z * |/ x * x) a` by metis_tac[action_compose] >>
  `_ = f ((x * z) * ( |/ x * x)) a` by rw[group_assoc] >>
  `_ = f (x * z) a` by rw[] >>
  metis_tac[action_compose]) >>
  qexists_tac `|/x * x' * x` >>
  rw[] >| [
    `x * ( |/ x * x' * x) * |/ x = (x * |/ x) * x' * (x * |/ x)` by rw[group_assoc] >>
    rw[],
    `|/ x IN G /\ x' * x IN G` by rw[] >>
    `f ( |/ x * x' * x) a = f ( |/ x * (x' * x)) a` by rw[group_assoc] >>
    metis_tac[action_compose, group_linv, action_id]
  ]);

(* This is a major result. *)

(* Extract the existence element of reach *)
(* - reach_def;
> val it = |- !f g x y. reach f g a b <=> ?x. x IN G /\ (f x a = b) :  thm
*)

(* Existence of act_by: the x in reach f g a b, such that x IN G /\ f x a = b. *)
val lemma = prove(
  ``!f (g:'a group) (a:'b) (b:'b). ?x. reach f g a b ==> x IN G /\ (f x a = b)``,
  metis_tac[reach_def]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val act_by_def = new_specification(
    "act_by_def",
    ["act_by"],
    lemma |> SIMP_RULE bool_ss [SKOLEM_THM]
          |> CONV_RULE (RENAME_VARS_CONV ["t"] (* to allow rename of f' back to f *)
             THENC BINDER_CONV (RENAME_VARS_CONV ["f", "g", "a", "b"])));
(*
val act_by_def = |- !f g a b. (a ~~ b) f g ==> act_by f g a b IN G /\ (f (act_by f g a b) a = b): thm
*)

(* Theorem: The reachable set from a to b is the coset act_by b of (stabilizer a).
            Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
            ((act_by f g a b) * (stabilizer f g a) = {x | x IN G /\ (f x a = b)}) *)
(* Proof:
   By orbit_def, coset_def, this is to show:
   (1) z IN stabilizer f g a ==> act_by f g a b * z IN G
       Note act_by f g a b IN G          by act_by_def
        and z IN G                       by stabilizer_element
         so act_by f g a b * z IN G      by group_op_element
   (2) z IN stabilizer f g a ==> f (act_by f g a b * z) a = b
       Note act_by f g a b IN G          by act_by_def
        and z IN G                       by stabilizer_element
         f (act_by f g a b * z) a
       = f (act_by f g a b) (f z a)      by action_compose
       = f (act_by f g a b) a            by stabilizer_element
       = b                               by act_by_def
   (3) (a ~~ f x a) f g /\ x IN G ==> ?z. (x = act_by f g a (f x a) * z) /\ z IN stabilizer f g a
       Let y = act_by f g a (f x a)
       Then y IN G /\ (f y a = f x a)       by act_by_def
        and |/ y * x IN (stabilizer f g a)  by action_match_condition
        Let z = |/ y * x
           y * z
         = y * ( |/ y * x)        by notation
         = (y * |/ y) * x         by group_assoc
         = #e * x                 by group_rinv
         = x                      by group_lid
*)
val action_reachable_coset_1 = store_thm(
  "action_reachable_coset_1",
  ``!f (g:'a group) (A:'b -> bool) a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
   ((act_by f g a b) * (stabilizer f g a) = {x | x IN G /\ (f x a = b)})``,
  rw[orbit_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[act_by_def, stabilizer_element, group_op_element] >-
  metis_tac[act_by_def, action_compose, stabilizer_element] >>
  qabbrev_tac `y = act_by f g a (f x a)` >>
  `y IN G /\ (f y a = f x a)` by rw[act_by_def, Abbr`y`] >>
  `|/ y * x IN (stabilizer f g a)` by metis_tac[action_match_condition] >>
  qexists_tac `|/ y * x` >>
  `y * ( |/ y * x) = (y * |/ y) * x` by rw[group_assoc] >>
  `_ = x` by rw[] >>
  rw[]);

(* Another formulation of the same result. *)

(* Theorem: The reachable set from a to b is the coset act_by b of (stabilizer a).
            Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
            !x. x IN G /\ (f x a = b) ==> (x * (stabilizer f g a) = {y | y IN G /\ (f y a = b)}) *)
(* Proof:
   By orbit_def, coset_def, this is to show:
   (1) z IN stabilizer f g a ==> x * z IN G
       Note z IN G            by stabilizer_element
         so x * z IN G        by group_op_element
   (2) z IN stabilizer f g a ==> f (x * z) a = f x a
       Note f z a = a         by stabilizer_element
         f (x * z) a
       = f x (f z a)          by action_compose
       = f x a                by above
   (3) x' IN G /\ f x a = f x' a ==> ?z. (x' = x * z) /\ z IN stabilizer f g a
       Let z = |/ x * x'.
         x * z
       = x * ( |/ x * x')     by notation
       = (x * |/ x) * x'      by group_assoc
       = #e * x'              by group_rinv
       = x'                   by group_lid
       For z IN stabilizer f g a,
       Either directly        by action_match_condition, f x a = f x' a
       or indirectly,
       Note z IN G            by group_inv_element, group_op_element
         f z a
       = f ( |/ x * x') a
       = f ( |/ x) (f x' a)   by action_compose
       = a                    by action_reverse, f x a = f x' a
       Hence z IN stabilizer f g a   by stabilizer_element
*)
val action_reachable_coset_2 = store_thm(
  "action_reachable_coset_2",
  ``!f (g:'a group) (A:'b -> bool) a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g A a ==>
   !x. x IN G /\ (f x a = b) ==> (x * (stabilizer f g a) = {y | y IN G /\ (f y a = b)})``,
  rw[orbit_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stabilizer_element, group_op_element] >-
  metis_tac[stabilizer_element, action_compose] >>
  qexists_tac `|/ x * x'` >>
  rpt strip_tac >-
  rw[GSYM group_assoc] >>
  rw[stabilizer_element] >>
  metis_tac[action_compose, action_reverse, group_inv_element]);

(* Theorem: Points of (orbit a) and cosets of (stabilizer a) are one-to-one.
            Group g /\ (g act A) f /\ a IN A ==>
            BIJ (\b.  (act_by f g a b) * (stabilizer f g a)) (orbit f g A a) {x * (stabilizer f g a) | x IN G} *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) b IN orbit f g A a ==> ?x. (act_by f g a b * stabilizer f g a = x * stabilizer f g a) /\ x IN G
       Let x = act_by f g a b.
       Note (a ~~ b) f g         by orbit_element, b IN orbit f g A a
       Thus x IN G               by act_by_def, x = act_by f g a b
   (2) b IN orbit f g A a /\ b' IN orbit f g A a /\
       act_by f g a b * stabilizer f g a = act_by f g a b' * stabilizer f g a ==> b = b'
       Note (a ~~ b) f g /\ (a ~~ b') f g                 by orbit_element
        and act_by f g a b IN G /\ act_by f g a b' IN G   by act_by_def
       Thus b
          = f (act_by f g a b) a        by act_by_def
          = f (act_by f g a b') a       by orbit_stabilizer_map_inj
          = b'                          by act_by_def
   (3) same as (1)
   (4) x' IN G ==> ?b. b IN orbit f g A a /\ (act_by f g a b * stabilizer f g a = x' * stabilizer f g a)
       Let b = f x' a.
       Then (a ~~ b) f g                by reach_def
        and b IN A                      by action_closure
         so b IN orbit f g A a          by orbit_element
       Let x = act_by f g a b.
       Then f x a = b = f x' a          by act_by_def
        ==> x * stabilizer f g a = x' * stabilizer f g a
                                        by orbit_stabilizer_map_good
*)
val orbit_stabilizer_cosets_bij_3 = store_thm(
  "orbit_stabilizer_cosets_bij_3",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
   BIJ (\b.  (act_by f g a b) * (stabilizer f g a)) (orbit f g A a) {x * (stabilizer f g a) | x IN G}``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
  metis_tac[orbit_element, act_by_def] >-
  metis_tac[orbit_stabilizer_map_inj, orbit_element, act_by_def] >-
  metis_tac[orbit_element, act_by_def] >>
  qexists_tac `f x' a` >>
  rpt strip_tac >-
  metis_tac[orbit_element, reach_def, action_closure] >>
  `(a ~~ (f x' a)) f g` by metis_tac[reach_def] >>
  metis_tac[orbit_stabilizer_map_good, act_by_def]);

(* This version is not using CosetPartition *)

(* Theorem: Points of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act A) f /\ a IN A ==>
   BIJ (\b. (act_by f g a b) * (stabilizer f g a)) (orbit f g A a) (CosetPartition g (StabilizerGroup f g a) *)
(* Proof:
   By CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) b IN orbit f g A a ==>
          ?x. x IN G /\ (act_by f g a b * stabilizer f g a = {y | y IN G /\ y IN x * stabilizer f g a})
       Let z = act_by f g a b, and put x = z.
       Note (a ~~ b) f g        by orbit_element
        and z IN G              by act_by_def,
       By coset_def, IMAGE_DEF, EXTENSION, this is to show:
          z IN G /\ z' IN stabilizer f g a ==> z * z' IN G
       Now z' IN G              by stabilizer_element
       Thus z * z' IN G         by group_op_element
   (2) b IN orbit f g A a /\ b' IN orbit f g A a /\
         act_by f g a b * stabilizer f g a = act_by f g a b' * stabilizer f g a ==> b = b'
       Note (a ~~ b) f g /\ (a ~~ b') f g                  by orbit_element
        and act_by f g a b IN G /\ act_by f g a b' IN G    by act_by_def
        ==> f (act_by f g a b) a = f (act_by f g a b') a   by orbit_stabilizer_map_inj
         so b = b'                                         by act_by_def
   (3) same as (1)
   (4) x' IN G /\ x = {y | y IN G /\ y IN x' * stabilizer f g a} ==>
         ?b. b IN orbit f g A a /\ (act_by f g a b * stabilizer f g a = x)
       Let b = f x' a.
       Note (a ~~ b) f g        by reach_def
        and act_by f g a b IN G /\ (f (act_by f g a b) a = f x' a)  by act_by_def
        ==> act_by f g a b * (stabilizer f g a)
          = x' * (stabilizer f g a)   by orbit_stabilizer_map_good
      By EXTENSION, this is to show:
         !x''. x'' IN x' * stabilizer f g a ==> x'' IN G
      Note x'' IN IMAGE (\z. x'' * z) (stabilizer f g a)  by coset_def
      Thus ?z. z IN (stabilizer f g a) /\ (x'' = x' * z)  by IN_IMAGE
       Now z IN G                                         by stabilizer_element
      Thus x'' = x' * z IN G                              by group_op_element
*)
val orbit_stabilizer_cosets_bij_4 = store_thm(
  "orbit_stabilizer_cosets_bij_4",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
   BIJ (\b. (act_by f g a b) * (stabilizer f g a)) (orbit f g A a) (CosetPartition g (StabilizerGroup f g a))``,
  simp_tac (srw_ss()) [CosetPartition_def, partition_def, inCoset_def,
                        StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt strip_tac >| [
    qabbrev_tac `z = act_by f g a b` >>
    qexists_tac `z` >>
    `(a ~~ b) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    metis_tac[orbit_element, orbit_stabilizer_map_inj, act_by_def],
    qabbrev_tac `z = act_by f g a b` >>
    qexists_tac `z` >>
    `(a ~~ b) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    qexists_tac `f x' a` >>
    rpt strip_tac >-
    metis_tac[orbit_element, action_closure, reach_def] >>
    qabbrev_tac `b = f x' a` >>
    `(a ~~ b) f g` by metis_tac[reach_def] >>
    `act_by f g a b IN G /\ (f (act_by f g a b) a = f x' a)` by rw[act_by_def] >>
    `act_by f g a b * (stabilizer f g a) = x' * (stabilizer f g a)` by metis_tac[orbit_stabilizer_map_good] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    metis_tac[coset_def, IN_IMAGE, stabilizer_element, group_op_element]
  ]);
(* Michael's orginal proof *)
val orbit_stabilizer_cosets_bij_4 = store_thm(
  "orbit_stabilizer_cosets_bij_4",
  ``!f (g:'a group) (A:'b -> bool) a. Group g /\ (g act A) f /\ a IN A ==>
       BIJ (\b. (act_by f g a b) * (stabilizer f g a))
           (orbit f g A a)
           (CosetPartition g (StabilizerGroup f g a))``,
  SIMP_TAC (srw_ss()) [CosetPartition_def, partition_def, inCoset_def,
                       StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [
    Q.X_GEN_TAC `z` THEN STRIP_TAC THEN
    `reach f g a z` by metis_tac[orbit_element] THEN
    `act_by f g a z IN G` by rw[act_by_def] THEN
    qexists_tac `act_by f g a z` THEN
    ASM_SIMP_TAC (srw_ss()) [EXTENSION, EQ_IMP_THM] THEN Q.X_GEN_TAC `x'` THEN
    STRIP_TAC THEN
    `x' IN IMAGE (\z'. act_by f g a z * z') (stabilizer f g a)`
      by metis_tac[coset_def] THEN
    `?z'. z' IN (stabilizer f g a) /\ (x' = act_by f g a z * z')`
       by metis_tac[IN_IMAGE] THEN
    metis_tac[stabilizer_element, group_op_element],
    MAP_EVERY Q.X_GEN_TAC [`z`, `z'`] THEN rpt strip_tac THEN
    `reach f g a z /\ reach f g a z'` by metis_tac[orbit_element] THEN
    `act_by f g a z IN G /\ act_by f g a z' IN G` by rw[act_by_def] THEN
    `f (act_by f g a z) a = f (act_by f g a z') a` by metis_tac[orbit_stabilizer_map_inj] THEN
    metis_tac[act_by_def],
    Q.X_GEN_TAC `z` THEN rpt strip_tac THEN
    `reach f g a z` by metis_tac[orbit_element] THEN
    `act_by f g a z IN G` by rw[act_by_def] THEN
    qexists_tac `act_by f g a z` THEN
    ASM_SIMP_TAC (srw_ss())[EXTENSION, EQ_IMP_THM] THEN Q.X_GEN_TAC `x'` THEN
    STRIP_TAC THEN
    `x' IN IMAGE (\z'. act_by f g a z * z') (stabilizer f g a)` by metis_tac[coset_def] THEN
    `?z'. z' IN (stabilizer f g a) /\ (x' = act_by f g a z * z')` by metis_tac[IN_IMAGE] THEN
    metis_tac[stabilizer_element, group_op_element],
    Q.X_GEN_TAC `x'` THEN
    DISCH_THEN (Q.X_CHOOSE_THEN `x''` STRIP_ASSUME_TAC) THEN
    qexists_tac `f x'' a` THEN
    rw[] THENL [
      `reach f g a (f x'' a)` by metis_tac[reach_def] THEN
      `f x'' a IN A` by metis_tac[action_closure] THEN
      rw[orbit_def],
      `reach f g a (f x'' a)` by metis_tac[reach_def] THEN
      `act_by f g a (f x'' a) IN G /\ (f (act_by f g a (f x'' a)) a = (f x'' a))` by rw[act_by_def] THEN
      `(act_by f g a (f x'' a)) * (stabilizer f g a)  = x'' * (stabilizer f g a)` by metis_tac[orbit_stabilizer_map_good] THEN
      ASM_SIMP_TAC (srw_ss()) [EXTENSION, EQ_IMP_THM] THEN
      Q.X_GEN_TAC `x'` THEN STRIP_TAC THEN
      `x' IN IMAGE (\z. x'' * z) (stabilizer f g a)` by metis_tac[coset_def] THEN
      `?z. z IN (stabilizer f g a) /\ (x' = x'' * z)` by metis_tac[IN_IMAGE] THEN
      metis_tac[stabilizer_element, group_op_element]
    ]
  ]);

(* Theorem: [Orbit-Stabilizer Theorem]
            FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
            (CARD G = CARD (orbit f g A a) * CARD (stabilizer f g a)) *)
(* Proof:
   Let h = StabilizerGroup f g a
   Then h <= g                          by stabilizer_group_subgroup
    and H = stabilizer f g a            by stabilizer_group_property
   Note CosetPartition g h = partition (inCoset g h) G  by CosetPartition_def
     so FINITE (CosetPartition g h)     by FINITE_partition
   Note FINITE_partition = IMAGE (\x. f x a) G  by orbit_as_image
     so FINITE (orbit f g A a)          by IMAGE_FINITE

     CARD G
   = CARD H * CARD (CosetPartition g h)              by Lagrange_identity, h <= g
   = CARD (stabilizer f g a) * CARD (orbit f g A a)  by orbit_stabilizer_cosets_bij_4, FINITE_BIJ_CARD_EQ
   = CARD (orbit f g A a) * CARD (stabilizer f g a)  by MULT_COMM
*)
val orbit_stabilizer_thm = store_thm(
  "orbit_stabilizer_thm",
  ``!f (g:'a group) (A:'b -> bool) a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
      (CARD G = CARD (orbit f g A a) * CARD (stabilizer f g a))``,
  rpt (stripDup[FiniteGroup_def]) >>
  `StabilizerGroup f g a <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  `FINITE (CosetPartition g (StabilizerGroup f g a))` by metis_tac[CosetPartition_def, FINITE_partition] >>
  `FINITE (orbit f g A a)` by rw[orbit_as_image] >>
  `CARD G = CARD (stabilizer f g a) * CARD (CosetPartition g (StabilizerGroup f g a))` by metis_tac[Lagrange_identity] >>
  `_ = CARD (stabilizer f g a) * CARD (orbit f g A a)` by metis_tac[orbit_stabilizer_cosets_bij_4, FINITE_BIJ_CARD_EQ] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Fixed Points of action.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
Fixed Points have singleton orbits -- although it is not defined in this way,
this property is the theorem fixed_points_orbit_sing.

This important property of fixed points gives this simple trick:
to count how many singleton orbits, just count the set (fixed_points f g A).

Since orbits are equivalent classes, they cannot be empty, hence singleton
orbits are the simplest type. For equivalent classes:

CARD Target = SUM CARD (TargetPartitions)
            = SUM CARD (orbits)
            = SUM CARD (singleton orbits) + SUM CARD (non-singleton orbits)
            = CARD (fixed_points) + SUM CARD (non-singleton orbits)
*)

(* Fixed points of action: f g A = {a in A | !x in G. f x a = a} *)
val fixed_points_def = Define`
    fixed_points f (g:'a group) (A:'b -> bool) = {a | a IN A /\ (!x. x IN G ==> (f x a = a)) }
`;

(* Theorem: Fixed point elements: a IN (fixed_points f g A) <=> a IN A /\ !x. x IN G ==> (f x a = a) *)
(* Proof: by fixed_points_def. *)
val fixed_points_element = store_thm(
  "fixed_points_element",
  ``!f (g:'a group) (A:'b -> bool) a. a IN (fixed_points f g A) <=> a IN A /\ !x. x IN G ==> (f x a = a)``,
  rw[fixed_points_def]);

(* Theorem: Fixed points are subsets of target set.
            (g act A) f ==> (fixed_points f g A) SUBSET A *)
(* Proof: by fixed_points_def. *)
val fixed_points_subset = store_thm(
  "fixed_points_subset",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f ==> (fixed_points f g A) SUBSET A``,
  rw[fixed_points_def, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Fixed Points have singleton orbits.
   Or those points with stabilizer = whole group
   With ZP_ORBIT_DISTINCT,
   This gives the key result:
        fixpoints f (Z p) A <== bijective ==> (Z p).carrier
   This will make the computation of CARD (fixpoints f (Z p) A) easy.
*)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ (g act A) f ==>
           !a. a IN fixed_points f g A <=> (orbit f g A a = {a}) *)
(* Proof:
   By fixed_points_def, orbit_def, reach_def, this is to show:
   (1) x' IN G /\ (!x. x IN G ==> (f x a = a)) ==> f x' a = a
       This is true                by the included implication
   (2) (!x. x IN G ==> (f x a = a)) ==> ?x. x IN G /\ (f x a = a)
       Take x = #e,
       Then x IN G                 by group_id_element
        and f x a = a              by implication
   (3) (g act A) f /\ x IN G ==> f x a = a
       This is true                by action_closure
*)
val fixed_points_orbit_sing = store_thm(
  "fixed_points_orbit_sing",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
   !a. a IN fixed_points f g A <=> (orbit f g A a = {a})``,
  rw[fixed_points_def, orbit_def, reach_def, EXTENSION, EQ_IMP_THM] >-
  rw_tac std_ss [] >-
  metis_tac[group_id_element] >>
  metis_tac[action_closure]);

(* Theorem: For action f g A, a IN A, (orbit f g A a = {a}) ==> a IN fixed_points f g A *)
(* Proof:
   This is to prove:
   (g act A) f /\ a IN A /\ x IN G /\ !x. x IN A /\ (?x'. x' IN G /\ (f x' a = x)) <=> (x = a) ==> f x a = a
   This is true by action_closure.
*)
val orbit_sing_fixed_points = store_thm(
  "orbit_sing_fixed_points",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f ==>
    !a. a IN A /\ (orbit f g A a = {a}) ==> a IN fixed_points f g A``,
  rw[action_def, fixed_points_def, orbit_def, reach_def, EXTENSION] THEN
  metis_tac[]);
(* This is weaker than the previous theorem. *)

(* Theorem: Group g /\ (g act A) f ==> !a. a IN fixed_points f g A <=> SING (orbit f g A a)) *)
(* Proof:
   By SING_DEF, this is to show:
   If part: a IN fixed_points f g A ==>?x. (orbit f g A a) = {x}
      Take x = a, then true                by fixed_points_orbit_sing
   Only-if part: (orbit f g A a) = {x} ==> a IN fixed_points f g A
      Note a IN (orbit f g A a)            by orbit_has_self
      Thus x = a                           by IN_SING
        so a IN fixed_points f g A         by fixed_points_orbit_sing
*)
val fixed_points_orbit_is_sing = store_thm(
  "fixed_points_orbit_is_sing",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
    !a. a IN A ==> (a IN fixed_points f g A <=> SING (orbit f g A a))``,
  metis_tac[fixed_points_orbit_sing, orbit_has_self, SING_DEF, IN_SING]);

(* Theorem: Group g /\ (g act A) f ==>
            !a. a IN (A DIFF fixed_points f g A) <=> a IN A /\ ~ SING (orbit f g A a))  *)
(* Proof:
       a IN (A DIFF fixed_points f g A)
   <=> a IN A /\ a NOTIN (fixed_points f g A)    by IN_DIFF
   <=> a IN A /\ ~ SING (orbit f g A a))         by fixed_points_orbit_is_sing
*)
val non_fixed_points_orbit_not_sing = store_thm(
  "non_fixed_points_orbit_not_sing",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
   !a. a IN (A DIFF fixed_points f g A) <=> a IN A /\ ~ SING (orbit f g A a)``,
  metis_tac[IN_DIFF, fixed_points_orbit_is_sing]);

(* Theorem: (g act A) f /\ FINITE A ==>
            (CARD (A DIFF fixed_points f g A) = CARD A - CARD (fixed_points f g A)) *)
(* Proof:
   Note (fixed_points f g A) SUBSET A                        by fixed_points_def
   Thus A INTER (fixed_points f g A) = (fixed_points f g A)  by SUBSET_INTER_ABSORPTION
     CARD (A DIFF fixed_points f g A)
   = CARD A - CARD (A INTER (fixed_points f g A)))           by CARD_DIFF
   = CARD A - CARD (fixed_points f g A)                      by SUBSET_INTER_ABSORPTION
*)
val non_fixed_points_card = store_thm(
  "non_fixed_points_card",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f /\ FINITE A ==>
      (CARD (A DIFF fixed_points f g A) = CARD A - CARD (fixed_points f g A))``,
  metis_tac[CARD_DIFF, fixed_points_subset, SUBSET_INTER_ABSORPTION, SUBSET_FINITE, INTER_COMM]);

(* ------------------------------------------------------------------------- *)
(* Partition of Target into single orbits and non-single orbits.             *)
(* ------------------------------------------------------------------------- *)

(* Define singleton and non-singleton orbits *)
val sing_orbits_def = Define`
    sing_orbits f (g:'a group) (A:'b -> bool) = { e | e IN (TargetPartition f g A) /\ SING e }
`;
val multi_orbits_def = Define`
    multi_orbits f (g:'a group) (A:'b -> bool) = { e | e IN (TargetPartition f g A) /\ ~ SING e }
`;

(* Theorem: e IN sing_orbits f g A <=> e IN (TargetPartition f g A) /\ SING e *)
(* Proof: by sing_orbits_def *)
val sing_orbits_element = store_thm(
  "sing_orbits_element",
  ``!f (g:'a group) (A:'b -> bool) e. e IN sing_orbits f g A <=> e IN (TargetPartition f g A) /\ SING e``,
  rw[sing_orbits_def]);

(* Theorem: (sing_orbits f g A) SUBSET (TargetPartition f g A) *)
(* Proof: by sing_orbits_element, SUBSET_DEF *)
val sing_orbits_subset = store_thm(
  "sing_orbits_subset",
  ``!f (g:'a group) (A:'b -> bool). (sing_orbits f g A) SUBSET (TargetPartition f g A)``,
  rw[sing_orbits_element, SUBSET_DEF]);

(* Theorem: (g act A) f /\ FINITE A ==> FINITE (sing_orbits f g A)*)
(* Proof: by sing_orbits_subset, target_partition_finite, SUBSET_FINITE *)
val sing_orbits_finite = store_thm(
  "sing_orbits_finite",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f /\ FINITE A ==> FINITE (sing_orbits f g A)``,
  metis_tac[sing_orbits_subset, target_partition_finite, SUBSET_FINITE]);

(* Theorem: For (g act A) f, elements of (sing_orbits f g A) are subsets of A.
            (g act A) f /\ e IN (sing_orbits f g A) ==> e SUBSET A *)
(* Proof: by sing_orbits_element, target_partition_element_subset *)
val sing_orbits_element_subset = store_thm(
  "sing_orbits_element_subset",
  ``!f (g:'a group) (A:'b -> bool) e. (g act A) f /\ e IN (sing_orbits f g A) ==> e SUBSET A``,
  metis_tac[sing_orbits_element, target_partition_element_subset]);

(* Theorem: e IN (sing_orbits f g A) ==> FINITE e *)
(* Proof: by sing_orbits_element, SING_FINITE *)
val sing_orbits_element_finite = store_thm(
  "sing_orbits_element_finite",
  ``!f (g:'a group) (A:'b -> bool) e. e IN (sing_orbits f g A) ==> FINITE e``,
  rw[sing_orbits_element, SING_FINITE]);

(* Theorem: e IN (sing_orbits f g A) ==> (CARD e = 1) *)
(* Proof: by sing_orbits_element, SING_DEF, CARD_SING *)
val sing_orbits_element_card = store_thm(
  "sing_orbits_element_card",
  ``!f (g:'a group) (A:'b -> bool) e. e IN (sing_orbits f g A) ==> (CARD e = 1)``,
  metis_tac[sing_orbits_element, SING_DEF, CARD_SING]);

(* Theorem: Group g /\ (g act A) f ==>
            !e. e IN (sing_orbits f g A) ==> CHOICE e IN fixed_points f g A *)
(* Proof:
   Note e IN TargetPartition f g A /\ SING e    by sing_orbits_element
   Thus ?a. e = {a}                             by SING_DEF
    ==> a IN e /\ (CHOICE e = a)                by IN_SING, CHOICE_SING
     so e = orbit f g A a                       by target_partition_element_is_orbit, a IN e
    and a IN A                                  by target_partition_element_element
    ==> a IN fixed_points f g A                 by orbit_sing_fixed_points
*)
val sing_orbits_element_choice = store_thm(
  "sing_orbits_element_choice",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
   !e. e IN (sing_orbits f g A) ==> CHOICE e IN fixed_points f g A``,
  rw[sing_orbits_element] >>
  `?a. e = {a}` by rw[GSYM SING_DEF] >>
  `a IN e /\ (CHOICE e = a)` by rw[] >>
  `e = orbit f g A a` by rw[target_partition_element_is_orbit] >>
  metis_tac[orbit_sing_fixed_points, target_partition_element_element]);

(* Theorem: e IN multi_orbits f g A <=> e IN (TargetPartition f g A) /\ ~SING e *)
(* Proof: by multi_orbits_def *)
val multi_orbits_element = store_thm(
  "multi_orbits_element",
  ``!f (g:'a group) (A:'b -> bool) e. e IN multi_orbits f g A <=> e IN (TargetPartition f g A) /\ ~SING e``,
  rw[multi_orbits_def]);

(* Theorem: (multi_orbits f g A) SUBSET (TargetPartition f g A) *)
(* Proof: by multi_orbits_element, SUBSET_DEF *)
val multi_orbits_subset = store_thm(
  "multi_orbits_subset",
  ``!f (g:'a group) (A:'b -> bool). (multi_orbits f g A) SUBSET (TargetPartition f g A)``,
  rw[multi_orbits_element, SUBSET_DEF]);

(* Theorem: (g act A) f /\ FINITE A ==> FINITE (multi_orbits f g A)*)
(* Proof: by multi_orbits_subset, target_partition_finite, SUBSET_FINITE *)
val multi_orbits_finite = store_thm(
  "multi_orbits_finite",
  ``!f (g:'a group) (A:'b -> bool). (g act A) f /\ FINITE A ==> FINITE (multi_orbits f g A)``,
  metis_tac[multi_orbits_subset, target_partition_finite, SUBSET_FINITE]);

(* Theorem: For (g act A) f, elements of (multi_orbits f g A) are subsets of A.
            (g act A) f /\ e IN (multi_orbits f g A) ==> e SUBSET A *)
(* Proof: by multi_orbits_element, target_partition_element_subset *)
val multi_orbits_element_subset = store_thm(
  "multi_orbits_element_subset",
  ``!f (g:'a group) (A:'b -> bool) e. (g act A) f /\ e IN (multi_orbits f g A) ==> e SUBSET A``,
  metis_tac[multi_orbits_element, target_partition_element_subset]);

(* Theorem: (g act A) f /\ e IN (multi_orbits f g A) ==> FINITE e *)
(* Proof: by multi_orbits_element, target_partition_element_finite *)
val multi_orbits_element_finite = store_thm(
  "multi_orbits_element_finite",
  ``!f (g:'a group) (A:'b -> bool) e. (g act A) f /\ FINITE A /\ e IN (multi_orbits f g A) ==> FINITE e``,
  metis_tac[multi_orbits_element, target_partition_element_finite]);

(* Theorem: sing_orbits and multi_orbits are disjoint.
            DISJOINT (sing_orbits f g A) (multi_orbits f g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def *)
val target_orbits_disjoint = store_thm(
  "target_orbits_disjoint",
  ``!f (g:'a group) (A:'b -> bool). DISJOINT (sing_orbits f g A) (multi_orbits f g A)``,
  rw[sing_orbits_def, multi_orbits_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: TargetPartition = sing_orbits + multi_orbits.
            TargetPartition f g A = (sing_orbits f g A) UNION (multi_orbits f g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def. *)
val target_eq_orbits_union = store_thm(
  "target_eq_orbits_union",
  ``!f (g:'a group) (A:'b -> bool). TargetPartition f g A = (sing_orbits f g A) UNION (multi_orbits f g A)``,
  rw[sing_orbits_def, multi_orbits_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For (g act A) f, CARD A = CARD sing_orbits + SIGMA CARD multi_orbits.
            Group g /\ (g act A) f /\ FINITE A ==>
            (CARD A = CARD (sing_orbits f g A) + SIGMA CARD (multi_orbits f g A)) *)
(* Proof:
   Let s = sing_orbits f g A, t = multi_orbits f g A.
   Note FINITE s                           by sing_orbits_finite
    and FINITE t                           by multi_orbits_finite
   also s INTER t = {}                     by target_orbits_disjoint, DISJOINT_DEF

     CARD A
   = SIGMA CARD (TargetPartition f g A)    by target_card_by_partition
   = SIGMA CARD (s UNION t)                by target_eq_orbits_union
   = SIGMA CARD s + SIGMA CARD t           by SUM_IMAGE_UNION, SUM_IMAGE_EMPTY
   = 1 * CARD s + SIGMA CARD t             by sing_orbits_element_card, SIGMA_CARD_CONSTANT
   = CARD s + SIGMA CARD t                 by MULT_LEFT_1
*)
val target_card_by_orbit_types = store_thm(
  "target_card_by_orbit_types",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f /\ FINITE A ==>
      (CARD A = CARD (sing_orbits f g A) + SIGMA CARD (multi_orbits f g A))``,
  rpt strip_tac >>
  qabbrev_tac `s = sing_orbits f g A` >>
  qabbrev_tac `t = multi_orbits f g A` >>
  `FINITE s` by rw[sing_orbits_finite, Abbr`s`] >>
  `FINITE t` by rw[multi_orbits_finite, Abbr`t`] >>
  `s INTER t = {}` by rw[target_orbits_disjoint, GSYM DISJOINT_DEF, Abbr`s`, Abbr`t`] >>
  `CARD A = SIGMA CARD (TargetPartition f g A)` by rw_tac std_ss[target_card_by_partition] >>
  `_ = SIGMA CARD (s UNION t)` by rw_tac std_ss[target_eq_orbits_union] >>
  `_ = SIGMA CARD s + SIGMA CARD t` by rw[SUM_IMAGE_UNION, SUM_IMAGE_EMPTY] >>
  `_ = 1 * CARD s + SIGMA CARD t` by metis_tac[sing_orbits_element_card, SIGMA_CARD_CONSTANT] >>
  rw[]);

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)  where e = {a} is injective.
            Group g /\ (g act A) f ==> INJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
       This is true                    by sing_orbits_element_choice
   (2) e IN sing_orbits f g A /\ e' IN sing_orbits f g A /\ CHOICE e = CHOICE e' ==> e = e'
       Note SING e /\ SING e'          by sing_orbits_element
       Thus this is true               by SING_DEF, CHOICE_SING.
*)
val sing_orbits_to_fixed_points_inj = store_thm(
  "sing_orbits_to_fixed_points_inj",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
      INJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)``,
  rw[INJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  metis_tac[sing_orbits_element, SING_DEF, CHOICE_SING]);

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)  where e = {a} is surjective.
            Group g /\ (g act A) f ==> SURJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
       This is true                       by sing_orbits_element_choice
   (2) x IN fixed_points f g A ==> ?e. e IN sing_orbits f g A /\ (CHOICE e = x)
       Note x IN A                        by fixed_points_element
        and orbit f g A x = {x}           by fixed_points_orbit_sing
       Take e = {x},
       Then CHOICE e = x                  by CHOICE_SING
        and SING e                        by SING_DEF
        and e IN TargetPartition f g A    by orbit_is_target_partition_element
        ==> e IN sing_orbits f g A        by sing_orbits_element
*)
val sing_orbits_to_fixed_points_surj = store_thm(
  "sing_orbits_to_fixed_points_surj",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
      SURJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)``,
  rw[SURJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  `x IN A` by metis_tac[fixed_points_element] >>
  `orbit f g A x = {x}` by rw_tac std_ss[GSYM fixed_points_orbit_sing] >>
  qexists_tac `{x}` >>
  rw[sing_orbits_element] >>
  metis_tac[orbit_is_target_partition_element]);

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)  where e = {a} is bijective.
            Group g /\ (g act A) f ==> BIJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof: by sing_orbits_to_fixed_points_inj, sing_orbits_to_fixed_points_surj, BIJ_DEF.
          True since the map is shown to be both injective and surjective.
*)
val sing_orbits_to_fixed_points_bij = store_thm(
  "sing_orbits_to_fixed_points_bij",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f ==>
      BIJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)``,
  rw_tac std_ss[BIJ_DEF, sing_orbits_to_fixed_points_surj, sing_orbits_to_fixed_points_inj]);

(* Theorem: For (g act A) f, sing_orbits is the same size as fixed_points f g A,
            Group g /\ (g act A) f /\ FINITE A ==> (CARD (sing_orbits f g A) = CARD (fixed_points f g A)) *)
(* Proof:
   Let s = sing_orbits f g A, t = fixed_points f g A.
   Note s SUBSET (TargetPartition f g A)  by sing_orbits_def
    and t SUBSET A                        by fixed_points_def
   Also FINITE s                          by target_partition_finite, SUBSET_FINITE
    and FINITE t                          by SUBSET_FINITE
   With BIJ (\e. CHOICE e) s t            by sing_orbits_to_fixed_points_bij
    ==> CARD s = CARD t                   by FINITE_BIJ_CARD_EQ
*)
val sing_orbits_card_eqn = store_thm(
  "sing_orbits_card_eqn",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f /\ FINITE A ==>
      (CARD (sing_orbits f g A) = CARD (fixed_points f g A))``,
  rpt strip_tac >>
  `(sing_orbits f g A) SUBSET (TargetPartition f g A)` by rw[sing_orbits_def, SUBSET_DEF] >>
  `(fixed_points f g A) SUBSET A` by rw[fixed_points_def, SUBSET_DEF] >>
  metis_tac[sing_orbits_to_fixed_points_bij, FINITE_BIJ_CARD_EQ, SUBSET_FINITE, target_partition_finite]);

(* Theorem: For (g act A) f, CARD A = CARD fixed_points + SIGMA CARD multi_orbits.
            Group g /\ (g act A) f /\ FINITE A ==>
            (CARD A = CARD (fixed_points f g A) + SIGMA CARD (multi_orbits f g A)) *)
(* Proof:
   Let s = sing_orbits f g A, t = multi_orbits f g A.
     CARD A
   = CARD s + SIGMA CARD t                       by target_card_by_orbit_types
   = CARD (fixed_points f g A) + SIGMA CARD t    by sing_orbits_card_eqn
*)
val target_card_by_fixed_points = store_thm(
  "target_card_by_fixed_points",
  ``!f (g:'a group) (A:'b -> bool). Group g /\ (g act A) f /\ FINITE A ==>
      (CARD A = CARD (fixed_points f g A) + SIGMA CARD (multi_orbits f g A))``,
  metis_tac[target_card_by_orbit_types, sing_orbits_card_eqn]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
