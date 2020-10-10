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
. Due to this partition, CARD A = SIGMA CARD orbits.
. As equivalent classes are non-empty, minimum CARD orbit = 1.
. These singleton orbits have a 1-1 correspondence with a special set on A:
  the fixed_points. The main result is:
  CARD A = CARD fixed_points + SIGMA (CARD non-singleton orbits).

  When group action is applied to necklaces, Z[n] enters into the picture.
  The cyclic Z[n] of modular addition is the group for necklaces of n beads.

Rework
======
. keep x, y as group elements, a, b as set A elements.
. orbit is defined as image, with one less parameter.
. orbits is named, replacing TargetPartition.

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
   reach_def    |- !f g a b. (a ~~ b) f g <=> ?x. x IN G /\ f x a = b
   reach_refl   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> (a ~~ a) f g
   reach_sym    |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ (a ~~ b) f g ==> (b ~~ a) f g
   reach_trans  |- !f g A a b c. Group g /\ (g act A) f /\ a IN A /\ b IN A /\ c IN A /\
                                 (a ~~ b) f g /\ (b ~~ c) f g ==> (a ~~ c) f g
   reach_equiv  |- !f g A. Group g /\ (g act A) f ==> reach f g equiv_on A

   Orbits as equivalence classes of Group action:
   orbit_def           |- !f g a. orbit f g a = IMAGE (\x. f x a) G
   orbit_alt           |- !f g a. orbit f g a = {f x a | x IN G}
   orbit_element       |- !f g a b. b IN orbit f g a <=> (a ~~ b) f g
   orbit_has_action_element
                       |- !f g x a. x IN G ==> f x a IN orbit f g a
   orbit_has_self      |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g a
   orbit_subset_target |- !f g A a. (g act A) f /\ a IN A ==> orbit f g a SUBSET A
   orbit_element_in_target
                       |- !f g A a b. (g act A) f /\ a IN A /\ b IN orbit f g a ==> b IN A
   orbit_finite        |- !f g a. FINITE G ==> FINITE (orbit f g a)
   orbit_finite_by_target
                       |- !f g A a. (g act A) f /\ a IN A /\ FINITE A ==> FINITE (orbit f g a)
   orbit_eq_equiv_class|- !f g A a. (g act A) f /\ a IN A ==>
                                    orbit f g a = equiv_class (reach f g) A a
   orbit_eq_orbit      |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN A ==>
                                     (orbit f g a = orbit f g b <=> (a ~~ b) f g)

   Partition by Group action:
   orbits_def          |- !f g A. orbits f g A = IMAGE (orbit f g) A
   orbits_alt          |- !f g A. orbits f g A = {orbit f g a | a IN A}
   orbits_element      |- !f g A e. e IN orbits f g A <=> ?a. a IN A /\ e = orbit f g a
   orbits_eq_partition |- !f g A. (g act A) f ==> orbits f g A = partition (reach f g) A
   orbits_finite       |- !f g A. FINITE A ==> FINITE (orbits f g A)
   orbits_element_finite   |- !f g A. (g act A) f /\ FINITE A ==> EVERY_FINITE (orbits f g A)
   orbits_element_nonempty |- !f g A. Group g /\ (g act A) f ==> !e. e IN orbits f g A ==> e <> {}
   orbits_element_subset   |- !f g A e. (g act A) f /\ e IN orbits f g A ==> e SUBSET A
   orbits_element_element  |- !f g A e a. (g act A) f /\ e IN orbits f g A /\ a IN e ==> a IN A
   orbit_is_orbits_element |- !f g A a. a IN A ==> orbit f g a IN orbits f g A
   orbits_element_is_orbit |- !f g A e a. Group g /\ (g act A) f /\ e IN orbits f g A /\ a IN e ==>
                                          e = orbit f g a

   Target size and orbit size:
   action_to_orbit_surj        |- !f g A a. (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g a)
   orbit_finite_inj_card_eq    |- !f g A a. (g act A) f /\ a IN A /\ FINITE A /\
                                            INJ (\x. f x a) G (orbit f g a) ==>
                                            CARD (orbit f g a) = CARD G
   target_card_by_partition    |- !f g A a. Group g /\ (g act A) f /\ FINITE A ==>
                                            CARD A = SIGMA CARD (orbits f g A)
   orbits_equal_size_partition_equal_size
                               |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                           (!a. a IN A ==> CARD (orbit f g a) = n) ==>
                                            !e. e IN orbits f g A ==> CARD e = n
   orbits_equal_size_property  |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                           (!a. a IN A ==> CARD (orbit f g a) = n) ==>
                                            n divides CARD A
   orbits_size_factor_partition_factor
                               |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                           (!a. a IN A ==> n divides CARD (orbit f g a)) ==>
                                            !e. e IN orbits f g A ==> n divides CARD e
   orbits_size_factor_property |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\
                                           (!a. a IN A ==> n divides CARD (orbit f g a)) ==>
                                            n divides CARD A

   Stabilizer as invariant:
   stabilizer_def        |- !f g a. stabilizer f g a = {x | x IN G /\ (f x a = a)}
   stabilizer_element    |- !f g a x. x IN stabilizer f g a <=> x IN G /\ (f x a = a)
   stabilizer_subset     |- !f g a. stabilizer f g a SUBSET G
   stabilizer_has_id     |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a
   stabilizer_nonempty   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> {}
   stabilizer_as_image   |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                      stabilizer f g a = IMAGE (\x. if f x a = a then x else #e) G

   Stabilizer subgroup:
   StabilizerGroup_def            |- !f g a. StabilizerGroup f g a =
                                             <|carrier := stabilizer f g a; op := $*; id := #e|>
   stabilizer_group_property      |- !f g a. ((StabilizerGroup f g a).carrier = stabilizer f g a) /\
                                             ((StabilizerGroup f g a).op = $* ) /\
                                             ((StabilizerGroup f g a).id = #e)
   stabilizer_group_carrier       |- !f g a. (StabilizerGroup f g a).carrier = stabilizer f g a
   stabilizer_group_id            |- !f g a. (StabilizerGroup f g a).id = #e
   stabilizer_group_group         |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                               Group (StabilizerGroup f g a)
   stabilizer_group_subgroup      |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                               StabilizerGroup f g a <= g
   stabilizer_group_finite_group  |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
                                               FiniteGroup (StabilizerGroup f g a)
   stabilizer_group_card_divides  |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
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
   action_match_condition_alt|- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                !x y::G. f x a = f y a <=> |/ x * y IN stabilizer f g a
   stabilizer_conjugate      |- !f g A a x. Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
                                            (conjugate g x (stabilizer f g a) = stabilizer f g (f x a))
   act_by_def                |- !f g a b. (a ~~ b) f g ==> act_by f g a b IN G /\ (f (act_by f g a b) a = b)
   action_reachable_coset    |- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
                                (act_by f g a b * stabilizer f g a = {x | x IN G /\ (f x a = b)})
   action_reachable_coset_alt|- !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
                                !x. x IN G /\ (f x a = b) ==> (x * stabilizer f g a = {y | y IN G /\ (f y a = b)})
   orbit_stabilizer_cosets_bij     |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                      BIJ (\b. act_by f g a b * stabilizer f g a)
                                          (orbit f g a)
                                          {x * stabilizer f g a | x | x IN G}
   orbit_stabilizer_cosets_bij_alt |- !f g A a. Group g /\ (g act A) f /\ a IN A ==>
                                      BIJ (\b. act_by f g a b * stabilizer f g a)
                                          (orbit f g a)
                                          (CosetPartition g (StabilizerGroup f g a))
   orbit_stabilizer_thm      |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
                                          (CARD G = CARD (orbit f g a) * CARD (stabilizer f g a))
   orbit_card_divides_target_card
                             |- !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
                                          CARD (orbit f g a) divides CARD G

   Fixed Points of action:
   fixed_points_def          |- !f g A. fixed_points f g A = {a | a IN A /\ !x. x IN G ==> (f x a = a)}
   fixed_points_element      |- !f g A a. a IN fixed_points f g A <=>
                                          a IN A /\ !x. x IN G ==> (f x a = a)
   fixed_points_subset       |- !f g A. fixed_points f g A SUBSET A
   fixed_points_finite       |- !f g A. FINITE A ==> FINITE (fixed_points f g A)
   fixed_points_element_element
                             |- !f g A a. a IN fixed_points f g A ==> a IN A
   fixed_points_orbit_sing   |- !f g A. Group g /\ (g act A) f ==>
                                !a. a IN fixed_points f g A <=> <=> a IN A /\ orbit f g a = {a}
   orbit_sing_fixed_points   |- !f g A. (g act A) f ==>
                                !a. a IN A /\ orbit f g a = {a} ==> a IN fixed_points f g A
   fixed_points_orbit_iff_sing
                             |- !f g A. Group g /\ (g act A) f ==>
                                !a. a IN A ==> (a IN fixed_points f g A <=> SING (orbit f g a))
   non_fixed_points_orbit_not_sing
                             |- !f g A. Group g /\ (g act A) f ==>
                                !a. a IN A DIFF fixed_points f g A <=> a IN A /\ ~SING (orbit f g a)
   non_fixed_points_card     |- !f g A. FINITE A ==>
                                CARD (A DIFF fixed_points f g A) = CARD A - CARD (fixed_points f g A)

   Target Partition by orbits:
   sing_orbits_def                  |- !f g A. sing_orbits f g A = {e | e IN orbits f g A /\ SING e}
   multi_orbits_def                 |- !f g A. multi_orbits f g A = {e | e IN orbits f g A /\ ~SING e}
   sing_orbits_element              |- !f g A e. e IN sing_orbits f g A <=> e IN orbits f g A /\ SING e
   sing_orbits_subset               |- !f g A. sing_orbits f g A SUBSET orbits f g A
   sing_orbits_finite               |- !f g A. FINITE A ==> FINITE (sing_orbits f g A)
   sing_orbits_element_subset       |- !f g A e. (g act A) f /\ e IN sing_orbits f g A ==> e SUBSET A
   sing_orbits_element_finite       |- !f g A e. e IN sing_orbits f g A ==> FINITE e
   sing_orbits_element_card         |- !f g A e. e IN sing_orbits f g A ==> CARD e = 1
   sing_orbits_element_choice       |- !f g A. Group g /\ (g act A) f ==>
                                       !e. e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
   multi_orbits_element             |- !f g A e. e IN multi_orbits f g A <=> e IN orbits f g A /\ ~SING e
   multi_orbits_subset              |- !f g A. multi_orbits f g A SUBSET orbits f g A
   multi_orbits_finite              |- !f g A. FINITE A ==> FINITE (multi_orbits f g A)
   multi_orbits_element_subset      |- !f g A e. (g act A) f /\ e IN multi_orbits f g A ==> e SUBSET A
   multi_orbits_element_finite      |- !f g A e. (g act A) f /\ FINITE A /\ e IN multi_orbits f g A ==> FINITE e
   target_orbits_disjoint           |- !f g A. DISJOINT (sing_orbits f g A) (multi_orbits f g A)
   target_orbits_union              |- !f g A. orbits f g A = sing_orbits f g A UNION multi_orbits f g A
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
                                              (CARD A = CARD (fixed_points f g A) +
                                                        SIGMA CARD (multi_orbits f g A))
   target_card_and_fixed_points_congruence
                                    |- !f g A n. Group g /\ (g act A) f /\ FINITE A /\ 0 < n /\
                                                (!e. e IN multi_orbits f g A ==> CARD e = n) ==>
                                                 CARD A MOD n = CARD (fixed_points f g A) MOD n
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
> action_def |> ISPEC ``$o``;
val it = |- !g' A. (g' act A) $o <=>
            !a. a IN A ==>
              (!x. x IN g'.carrier ==> x o a IN A) /\ g'.id o a = a /\
               !x y. x IN g'.carrier /\ y IN g'.carrier ==> x o y o a = g'.op x y o a: thm
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
(* Orbits as equivalence classes.                                            *)
(* ------------------------------------------------------------------------- *)

(* Orbit of action for a: those that can be reached by taking x in G. *)
Definition orbit_def:
   orbit (f:'a -> 'b -> 'b) (g:'a group) (a:'b) = IMAGE (\x. f x a) G
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbit_def |> ISPEC ``$o``;
val it = |- !g' a. orbit $o g' a = IMAGE (\x. x o a) g'.carrier: thm
*)

(* Theorem: orbit f g a = {f x a | x IN G} *)
(* Proof: by orbit_def, EXTENSION. *)
Theorem orbit_alt:
  !f g a. orbit f g a = {f x a | x IN G}
Proof
  simp[orbit_def, EXTENSION]
QED

(* Theorem: b IN orbit f g a <=> (a ~~ b) f g *)
(* Proof:
       b IN orbit f g a
   <=> ?x. x IN G /\ (b = f x a)   by orbit_def, IN_IMAGE
   <=> (a ~~ b) f g                by reach_def
*)
Theorem orbit_element:
  !f g a b. b IN orbit f g a <=> (a ~~ b) f g
Proof
  simp[orbit_def, reach_def] >>
  metis_tac[]
QED

(* Theorem: x IN G ==> f x a IN (orbit f g a) *)
(* Proof: by orbit_def *)
Theorem orbit_has_action_element:
  !f g x a. x IN G ==> f x a IN (orbit f g a)
Proof
  simp[orbit_def] >>
  metis_tac[]
QED

(* Theorem: Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g a *)
(* Proof:
   Let b = orbit $o g a.
   Note #e IN G            by group_id_element
     so #e o a IN b        by orbit_has_action_element
    and #e o a = a         by action_id, a IN A
   thus a IN b             by above
*)
Theorem orbit_has_self:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g a
Proof
  metis_tac[orbit_has_action_element, group_id_element, action_id]
QED

(* Theorem: orbits are subsets of target set.
            (g act A) f /\ a IN A ==> (orbit f g a) SUBSET A *)
(* Proof: orbit_def, SUBSET_DEF, action_closure. *)
Theorem orbit_subset_target:
  !f g A a. (g act A) f /\ a IN A ==> (orbit f g a) SUBSET A
Proof
  rw[orbit_def, SUBSET_DEF] >>
  metis_tac[action_closure]
QED

(* Theorem: orbits elements are in target set.
             (g act A) f /\ a IN A /\ b IN (orbit f g a) ==> b IN A *)
(* Proof: orbit_subset_target, SUBSET_DEF. *)
Theorem orbit_element_in_target:
  !f g A a b. (g act A) f /\ a IN A /\ b IN (orbit f g a) ==> b IN A
Proof
  metis_tac[orbit_subset_target, SUBSET_DEF]
QED

(* Theorem: FINITE G ==> FINITE (orbit f g a) *)
(* Proof: by orbit_def, IMAGE_FINITE. *)
Theorem orbit_finite:
  !f (g:'a group) a. FINITE G ==> FINITE (orbit f g a)
Proof
  simp[orbit_def]
QED

(* Theorem: (g act A) f /\ a IN A /\ FINITE A ==> FINITE (orbit f g a) *)
(* Proof: by orbit_subset_target, SUBSET_FINITE. *)
Theorem orbit_finite_by_target:
  !f g A a. (g act A) f /\ a IN A /\ FINITE A ==> FINITE (orbit f g a)
Proof
  metis_tac[orbit_subset_target, SUBSET_FINITE]
QED

(* Theorem: (g act A) f /\ a IN A ==> (orbit f g a = equiv_class (reach f g) A a) *)
(* Proof: by orbit_def, reach_def, action_closure. *)
Theorem orbit_eq_equiv_class:
  !f g A a. (g act A) f /\ a IN A ==> (orbit f g a = equiv_class (reach f g) A a)
Proof
  simp[orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]
QED

(* Theorem: Group g /\ (g act A) f /\ a IN A /\ b IN A ==>
            (orbit f g a = orbit f g b <=> (a ~~ b) f g) *)
(* Proof: by orbit_eq_equiv_class, reach_equiv, equiv_class_eq. *)
Theorem orbit_eq_orbit:
  !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN A ==>
               (orbit f g a = orbit f g b <=> (a ~~ b) f g)
Proof
  metis_tac[orbit_eq_equiv_class, reach_equiv, equiv_class_eq]
QED

(* ------------------------------------------------------------------------- *)
(* Partition by Group action.                                                *)
(* ------------------------------------------------------------------------- *)

(* The collection of orbits of target points. *)
Definition orbits_def:
   orbits f (g:'a group) A = IMAGE (orbit f g) A
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbits_def |> ISPEC ``$o``;
val it = |- !g' A. orbits $o g' A = IMAGE (orbit $o g') A: thm
*)

(* Theorem: orbits f g A = {orbit f g a | a | a IN A} *)
(* Proof: by orbits_def, EXTENSION. *)
Theorem orbits_alt:
  !f g A. orbits f g A = {orbit f g a | a | a IN A}
Proof
  simp[orbits_def, EXTENSION]
QED

(* Theorem: e IN orbits f g A <=> ?a. a IN A /\ e = orbit f g a *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbits_element:
  !f g A e. e IN orbits f g A <=> ?a. a IN A /\ e = orbit f g a
Proof
  simp[orbits_def] >>
  metis_tac[]
QED

(* Theorem: (g act A) f ==> orbits f g A = partition (reach f g) A *)
(* Proof:
   By EXTENSION,
       e IN orbits f g A
   <=> ?a. a IN A /\ e = orbit f g a     by orbits_element
   <=> ?a. a IN A /\ e = equiv_class (reach f g) A a
                                         by orbit_eq_equiv_class, (g act A) f
   <=> e IN partition (reach f g) A)     by partition_element
*)
Theorem orbits_eq_partition:
  !f g A. (g act A) f ==> orbits f g A = partition (reach f g) A
Proof
  rw[EXTENSION] >>
  metis_tac[orbits_element, orbit_eq_equiv_class, partition_element]
QED

(* Theorem: orbits = target partition is FINITE.
            FINITE A ==> FINITE (orbits f g A) *)
(* Proof: by orbits_def, IMAGE_FINITE *)
Theorem orbits_finite:
  !f g A. FINITE A ==> FINITE (orbits f g A)
Proof
  simp[orbits_def]
QED

(* Theorem: For e IN (orbits f g A), FINITE A ==> FINITE e
            (g act A) f /\ FINITE A ==> EVERY_FINITE (orbits f g A) *)
(* Proof: by orbits_eq_partition, FINITE_partition. *)
Theorem orbits_element_finite:
  !f g A. (g act A) f /\ FINITE A ==> EVERY_FINITE (orbits f g A)
Proof
  metis_tac[orbits_eq_partition, FINITE_partition]
QED
(*
orbit_finite_by_target;
|- !f g A a. (g act A) f /\ a IN A /\ FINITE A ==> FINITE (orbit f g a): thm
*)

(* Theorem: For e IN (orbits f g A), e <> EMPTY
            Group g /\ (g act A) f ==> !e. e IN orbits f g A ==> e <> EMPTY *)
(* Proof: by orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition. *)
Theorem orbits_element_nonempty:
  !f g A. Group g /\ (g act A) f ==> !e. e IN orbits f g A ==> e <> EMPTY
Proof
  simp[orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition]
QED
(*
orbit_has_self;
|- !f g A a. Group g /\ (g act A) f /\ a IN A ==> a IN orbit f g a: thm
*)

(* Theorem: orbits elements are subset of target.
            (g act A) f /\ e IN orbits f g A ==> e SUBSET A *)
(* Proof: by orbits_eq_partition, partition_SUBSET. *)
Theorem orbits_element_subset:
  !f g A e. (g act A) f /\ e IN orbits f g A ==> e SUBSET A
Proof
  metis_tac[orbits_eq_partition, partition_SUBSET]
QED
(*
orbit_subset_target;
|- !f g A a. (g act A) f /\ a IN A ==> orbit f g a SUBSET A: thm
*)

(* Theorem: Elements in element of orbits are also in target.
            (g act A) f /\ e IN orbits f g A /\ a IN e ==> a IN A *)
(* Proof: by orbits_element_subset, SUBSET_DEF *)
Theorem orbits_element_element:
  !f g A e a. (g act A) f /\ e IN orbits f g A /\ a IN e ==> a IN A
Proof
  metis_tac[orbits_element_subset, SUBSET_DEF]
QED
(*
orbit_element_in_target;
|- !f g A a b. (g act A) f /\ a IN A /\ b IN orbit f g a ==> b IN A: thm
*)

(* Theorem: a IN A ==> (orbit f g a) IN (orbits f g A) *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbit_is_orbits_element:
  !f g A a. a IN A ==> (orbit f g a) IN (orbits f g A)
Proof
  simp[orbits_def]
QED

(* Theorem: Elements of orbits are orbits of its own element.
            Group g /\ (g act A) f /\ e IN orbits f g A /\ a IN e ==> e = orbit f g a *)
(* Proof:
   By orbits_def, this is to show:
   a IN A /\ b IN orbit f g a ==> orbit f g a = orbit f g b

   Note b IN A                       by orbit_element_in_target
    and (a ~~ b) f g                 by orbit_element
    ==> orbit f g a = orbit f g b    by orbit_eq_orbit
*)
Theorem orbits_element_is_orbit:
  !f g A e a. Group g /\ (g act A) f /\ e IN orbits f g A /\
               a IN e ==> e = orbit f g a
Proof
  rw[orbits_def] >>
  metis_tac[orbit_element_in_target, orbit_element, orbit_eq_orbit]
QED
(*
orbits_element;
|- !f g A e. e IN orbits f g A <=> ?a. a IN A /\ e = orbit f g a: thm
*)

(* ------------------------------------------------------------------------- *)
(* Target size and orbit size.                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For action f g A, all a in G are reachable, belong to some orbit,
            (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g a). *)
(* Proof:
   This should follow from the fact that reach induces a partition, and
   the partition elements are orbits (orbit_is_orbits_element).

   By action_def, orbit_def, SURJ_DEF, this is to show:
   (1) a IN A /\ x IN G ==> ?y. f x a = f y a /\ y IN G
       True by taking y = x.
   (2) a IN A /\ x IN G ==> ?y. y IN G /\ f y a = f x a
       True by taking y = x.
*)
Theorem action_to_orbit_surj:
  !f g A a. (g act A) f /\ a IN A ==> SURJ (\x. f x a) G (orbit f g a)
Proof
  rw[action_def, orbit_def, SURJ_DEF] >> metis_tac[]
QED

(* Theorem: If (\x. f x a) is INJ into orbit for action,
            then orbit is same size as the group.
            (g act A) f /\ FINITE A /\ a IN A /\
            INJ (\x. f x a) G (orbit f g a) ==> CARD (orbit f g a) = CARD G *)
(* Proof:
   Note SURJ (\x. f x a) G (orbit f g a)     by action_to_orbit_surj
   With INJ (\x. f x a) G (orbit f g a)      by given
    ==> BIJ (\x. f x a) G (orbit f g a)      by BIJ_DEF
    Now (orbit f g a) SUBSET A               by orbit_subset_target
     so FINITE (orbit f g a)                 by SUBSET_FINITE, FINITE A
    ==> FINITE G                             by FINITE_INJ
   Thus CARD (orbit f g a) = CARD G          by FINITE_BIJ_CARD_EQ
*)
Theorem orbit_finite_inj_card_eq:
  !f g A a. (g act A) f /\ a IN A /\ FINITE A /\
      INJ (\x. f x a) G (orbit f g a) ==> CARD (orbit f g a) = CARD G
Proof
  metis_tac[action_to_orbit_surj, BIJ_DEF,
            orbit_subset_target, SUBSET_FINITE, FINITE_INJ, FINITE_BIJ_CARD_EQ]
QED

(* Theorem: For FINITE A, CARD A = SUM of CARD partitions in (orbits f g A).
            Group g /\ (g act A) f /\ FINITE A ==> CARD A = SIGMA CARD (orbits f g A) *)
(* Proof:
   With orbits_eq_partition, reach_equiv, apply
   partition_CARD
   |- !R s. R equiv_on s /\ FINITE s ==> CARD s = SIGMA CARD (partition R s)
*)
Theorem target_card_by_partition:
  !f g A a. Group g /\ (g act A) f /\ FINITE A ==> CARD A = SIGMA CARD (orbits f g A)
Proof
  metis_tac[orbits_eq_partition, reach_equiv, partition_CARD]
QED

(* Theorem: If for all a IN A, CARD (orbit f g a) = n,
            then (orbits f g A) has pieces with equal size of n.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> CARD (orbit f g a) = n) ==>
            (!e. e IN orbits f g A ==> CARD e = n) *)
(* Proof:
   Note !a. a IN e ==> (e = orbit f g a)     by orbits_element_is_orbit
   Thus ?b. b IN e                           by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But b IN A                               by orbits_element_element
     so CARD e = n                           by given implication.
*)
Theorem orbits_equal_size_partition_equal_size:
  !f g A n. Group g /\ (g act A) f /\ FINITE A /\
             (!a. a IN A ==> CARD (orbit f g a) = n) ==>
             (!e. e IN orbits f g A ==> CARD e = n)
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all a IN A, CARD (orbit f g a) = n, then n divides CARD A.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> CARD (orbit f g a) = n) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN orbits f g A ==> CARD e = n by orbits_equal_size_partition_equal_size
   Thus CARD A
      = n * CARD (partition (reach f g) A)   by orbits_eq_partition, reach_equiv, equal_partition_CARD
      = CARD (partition (reach f g) A) * n   by MULT_SYM
     so n divides (CARD A)                   by divides_def
*)
Theorem orbits_equal_size_property:
  !f g A n. Group g /\ (g act A) f /\ FINITE A /\
             (!a. a IN A ==> (CARD (orbit f g a) = n)) ==> n divides (CARD A)
Proof
  rpt strip_tac >>
  imp_res_tac orbits_equal_size_partition_equal_size >>
  `CARD A = n * CARD (partition (reach f g) A)` by rw[orbits_eq_partition, reach_equiv, equal_partition_CARD] >>
  metis_tac[divides_def, MULT_COMM]
QED

(* Theorem: If for all a IN A, n divides CARD (orbit f g a),
            then n divides size of elements in orbits f g A.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> n divides (CARD (orbit f g a))) ==>
            (!e. e IN orbits f g A ==> n divides (CARD e)) *)
(* Proof:
   Note !a. a IN e ==> (e = orbit f g a) by orbits_element_is_orbit
   Thus ?b. b IN e                       by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But b IN A                           by orbits_element_element
     so n divides (CARD e)               by given implication.
*)
Theorem orbits_size_factor_partition_factor:
  !f g A n. Group g /\ (g act A) f /\ FINITE A /\
             (!a. a IN A ==> n divides (CARD (orbit f g a))) ==>
             (!e. e IN orbits f g A ==> n divides (CARD e))
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all a IN A, n divides (orbit f g a), then n divides CARD A.
            Group g /\ (g act A) f /\ FINITE A /\
            (!a. a IN A ==> n divides (CARD (orbit f g a))) ==> n divides (CARD A) *)
(* Proof:
   Note !e. e IN orbits f g A ==> n divides (CARD e)
                                   by orbits_size_factor_partition_factor
    and reach f g equiv_on A       by reach_equiv
   Thus n divides (CARD A)         by orbits_eq_partition, factor_partition_CARD
*)
Theorem orbits_size_factor_property:
  !f g A n. Group g /\ (g act A) f /\ FINITE A /\
             (!a. a IN A ==> n divides (CARD (orbit f g a))) ==> n divides (CARD A)
Proof
  metis_tac[orbits_size_factor_partition_factor,
            orbits_eq_partition, reach_equiv, factor_partition_CARD]
QED

(* ------------------------------------------------------------------------- *)
(* Stabilizer as invariant.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stabilizer of action: for a IN A, the group elements that fixes a. *)
val stabilizer_def = zDefine`
    stabilizer f (g:'a group) (a:'b) = {x | x IN G /\ f x a = a }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> stabilizer_def |> ISPEC ``$o``;
val it = |- !g' a. stabilizer $o g' a = {x | x IN g'.carrier /\ x o a = a}: thm
*)

(* Theorem: x IN stabilizer f g a ==> x IN G /\ (f x a = a) *)
(* Proof: by stabilizer_def *)
Theorem stabilizer_element:
  !f g a x. x IN stabilizer f g a <=> x IN G /\ (f x a = a)
Proof
  simp[stabilizer_def]
QED

(* Theorem: The (stabilizer f g a) is a subset of G. *)
(* Proof: by stabilizer_element, SUBSET_DEF *)
Theorem stabilizer_subset:
  !f g a. (stabilizer f g a) SUBSET G
Proof
  simp[stabilizer_element, SUBSET_DEF]
QED

(* Theorem: (stabilizer f g a) has #e.
            Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a *)
(* Proof:
   Note #e IN G                   by group_id_element
    and f #e a = a                by action_id
     so #e IN stabilizer f g a    by stabilizer_element
*)
Theorem stabilizer_has_id:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==> #e IN stabilizer f g a
Proof
  metis_tac[stabilizer_element, action_id, group_id_element]
QED
(* This means (stabilizer f g a) is non-empty *)

(* Theorem: (stabilizer f g a) is nonempty.
            Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> EMPTY *)
(* Proof: by stabilizer_has_id, MEMBER_NOT_EMPTY. *)
Theorem stabilizer_nonempty:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==> stabilizer f g a <> EMPTY
Proof
  metis_tac[stabilizer_has_id, MEMBER_NOT_EMPTY]
QED

(* Theorem: Group g /\ (g act A) f /\ a IN A ==>
            stabilizer f g a = IMAGE (\x. if (f x a = a) then x else #e) G *)
(* Proof:
   By stabilizer_def, EXTENSION, this is to show:
   (1) x IN G /\ f x a = a ==> ?y. x = (if f y a = a then y else #e) /\ y IN G
       This is true by taking y = x.
   (2) x IN G ==> (if f x a = a then x else #e) IN G, true   by group_id_element
   (3) f (if f x a = a then x else #e) a = a, true           by action_id
*)
Theorem stabilizer_as_image:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
             stabilizer f g a = IMAGE (\x. if (f x a = a) then x else #e) G
Proof
  (rw[stabilizer_def, EXTENSION] >> metis_tac[group_id_element, action_id])
QED

(* ------------------------------------------------------------------------- *)
(* Application:                                                              *)
(* Stabilizer subgroup.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the stabilizer group, the restriction of group G to stabilizer. *)
Definition StabilizerGroup_def:
    StabilizerGroup f (g:'a group) (a:'b) =
      <| carrier := stabilizer f g a;
              op := g.op;
              id := #e
       |>
End

(* Theorem: StabilizerGroup properties. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_property:
  !f g a. (StabilizerGroup f g a).carrier = stabilizer f g a /\
          (StabilizerGroup f g a).op = g.op /\
          (StabilizerGroup f g a).id = #e
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup carrier. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_carrier:
  !f g a. (StabilizerGroup f g a).carrier = stabilizer f g a
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup identity. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_id:
  !f g a. (StabilizerGroup f g a).id = g.id
Proof
  simp[StabilizerGroup_def]
QED

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
Theorem stabilizer_group_group:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==> Group (StabilizerGroup f g a)
Proof
  rw_tac std_ss[group_def_alt, StabilizerGroup_def, stabilizer_def,
                action_def, GSPECIFICATION] >> prove_tac[]
QED

(* Theorem: If g is Group, f g A is an action, then StabilizerGroup f g a is a subgroup of g.
            Group g /\ (g act A) f /\ a IN A ==> (StabilizerGroup f g a) <= g *)
(* Proof:
   By Subgroup_def, stabilizer_group_property, this is to show:
   (1) a IN A ==> Group (StabilizerGroup f g a), true by stabilizer_group_group
   (2) stabilizer f g a SUBSET G, true                by stabilizer_subset
*)
Theorem stabilizer_group_subgroup:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==> (StabilizerGroup f g a) <= g
Proof
  metis_tac[Subgroup_def, stabilizer_group_property, stabilizer_group_group, stabilizer_subset]
QED

(* Theorem: If g is FINITE Group, StabilizerGroup f g a is a FINITE Group.
            FiniteGroup g /\ (g act A) f /\ a IN A ==> FiniteGroup (StabilizerGroup f g a) *)
(* Proof:
   By FiniteGroup_def, stabilizer_group_property, this is to show:
   (1) a IN A ==> Group (StabilizerGroup f g a), true          by stabilizer_group_group
   (2) FINITE G /\ a IN A ==> FINITE (stabilizer f g a), true  by stabilizer_subset and SUBSET_FINITE
*)
Theorem stabilizer_group_finite_group:
  !f g A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
            FiniteGroup (StabilizerGroup f g a)
Proof
  rw_tac std_ss[FiniteGroup_def, stabilizer_group_property] >-
  metis_tac[stabilizer_group_group] >>
  metis_tac[stabilizer_subset, SUBSET_FINITE]
QED

(* Theorem: If g is FINITE Group, CARD (stabilizer f g a) divides CARD G.
            FiniteGroup g /\ (g act A) f /\ a IN A ==>
            CARD (stabilizer f g a) divides (CARD G) *)
(* Proof:
   By Lagrange's Theorem, and (StabilizerGroup f g a) is a subgroup of g.

   Note (StabilizerGroup f g a) <= g                         by stabilizer_group_subgroup
    and (StabilizerGroup f g a).carrier = stabilizer f g a   by stabilizer_group_property
    but (stabilizer f g a) SUBSET G                          by stabilizer_subset
  Thus CARD (stabilizer f g a) divides (CARD G)              by Lagrange_thm
*)
Theorem stabilizer_group_card_divides:
  !f (g:'a group) A a. FiniteGroup g /\ (g act A) f /\ a IN A ==>
                       CARD (stabilizer f g a) divides (CARD G)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `(StabilizerGroup f g a) <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  metis_tac[stabilizer_subset, Lagrange_thm]
QED

(* ------------------------------------------------------------------------- *)
(* Orbit-Stabilizer Theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The map from orbit to coset of stabilizer is well-defined.
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\ (f x a = f y a) ==>
                  x * (stabilizer f g a) = y * (stabilizer f g a) *)
(* Proof:
   Note StabilizerGroup f g a <= g         by stabilizer_group_subgroup
    and (StabilizerGroup f g a).carrier
      = stabilizer f g a                   by stabilizer_group_property
   By subgroup_coset_eq, this is to show:
      ( |/y * x) IN (stabilizer f g a)

   Note ( |/y * x) IN G        by group_inv_element, group_op_element
        f ( |/y * x) a
      = f ( |/y) (f x a)       by action_compose
      = f ( |/y) (f y a)       by given
      = f ( |/y * y) a         by action_compose
      = f #e a                 by group_linv
      = a                      by action_id
   Hence  ( |/y * x) IN (stabilizer f g a)
                               by stabilizer_element
*)
Theorem orbit_stabilizer_map_good:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\ f x a = f y a ==>
                  x * (stabilizer f g a) = y * (stabilizer f g a)
Proof
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
  rw[stabilizer_element]
QED

(* Theorem: The map from orbit to coset of stabilizer is injective.
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\
                  x * (stabilizer f g a) = y * (stabilizer f g a) ==> f x a = f y a *)
(* Proof:
   Note x * (stabilizer f g a) = y * (stabilizer f g a)
    ==> ( |/y * x) IN (stabilizer f g a)   by subgroup_coset_eq
    ==> f ( |/y * x) a = a                 by stabilizer_element
       f x a
     = f (#e * x) a            by group_lid
     = f ((y * |/ y) * x) a    by group_rinv
     = f (y * ( |/y * x)) a    by group_assoc
     = f y (f ( |/y * x) a)    by action_compose
     = f y a                   by above, a = f ( |/y * x) a
*)
Theorem orbit_stabilizer_map_inj:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G /\
                  x * (stabilizer f g a) = y * (stabilizer f g a) ==>
                  f x a = f y a
Proof
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
  metis_tac[]
QED

(* Theorem: For action f g A /\ a IN A,
            if x, y IN G, f x a = f y a <=> 1/x * y IN (stabilizer f g a).
            Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G ==>
                 (f x a = f y a <=> ( |/ x * y) IN (stabilizer f g a))  *)
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
Theorem action_match_condition:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
            !x y. x IN G /\ y IN G ==>
                  (f x a = f y a <=> ( |/ x * y) IN (stabilizer f g a))
Proof
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
  ]
QED

(* Alternative form of the same theorem. *)
Theorem action_match_condition_alt:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
            !x y::G. f x a = f y a <=> ( |/ x * y) IN (stabilizer f g a)
Proof
  metis_tac[action_match_condition]
QED

(* Theorem: stabilizers of points in same orbit:
            x * (stabilizer f g a) * 1/x = stabilizer f g (f x a).
            Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
            conjugate g x (stabilizer f g a) = stabilizer f g (f x a) *)
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
Theorem stabilizer_conjugate:
  !f g A a x. Group g /\ (g act A) f /\ a IN A /\ x IN G ==>
              conjugate g x (stabilizer f g a) = stabilizer f g (f x a)
Proof
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
  ]
QED

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
            Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
            (act_by f g a b) * (stabilizer f g a) = {x | x IN G /\ (f x a = b)} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
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
Theorem action_reachable_coset:
  !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
             (act_by f g a b) * (stabilizer f g a) = {x | x IN G /\ (f x a = b)}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[act_by_def, stabilizer_element, group_op_element] >-
  metis_tac[act_by_def, action_compose, stabilizer_element] >>
  qabbrev_tac `y = act_by f g a (f x a)` >>
  `y IN G /\ (f y a = f x a)` by rw[act_by_def, Abbr`y`] >>
  `|/ y * x IN (stabilizer f g a)` by metis_tac[action_match_condition] >>
  qexists_tac `|/ y * x` >>
  `y * ( |/ y * x) = (y * |/ y) * x` by rw[group_assoc] >>
  `_ = x` by rw[] >>
  rw[]
QED

(* Another formulation of the same result. *)

(* Theorem: The reachable set from a to b is the coset act_by b of (stabilizer a).
            Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
            !x. x IN G /\ (f x a = b) ==>
                x * (stabilizer f g a) = {y | y IN G /\ (f y a = b)} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
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
       Hence z IN stabilizer f g a,
                              by action_match_condition, f x a = f x' a
*)
Theorem action_reachable_coset_alt:
  !f g A a b. Group g /\ (g act A) f /\ a IN A /\ b IN orbit f g a ==>
              !x. x IN G /\ (f x a = b) ==>
                  x * (stabilizer f g a) = {y | y IN G /\ (f y a = b)}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stabilizer_element, group_op_element] >-
  metis_tac[stabilizer_element, action_compose] >>
  qexists_tac `|/ x * x'` >>
  rpt strip_tac >-
  rw[GSYM group_assoc] >>
  metis_tac[action_match_condition]
QED

(* Theorem: Elements of (orbit a) and cosets of (stabilizer a) are one-to-one.
            Group g /\ (g act A) f /\ a IN A ==>
            BIJ (\b.  (act_by f g a b) * (stabilizer f g a))
                (orbit f g a)
                {x * (stabilizer f g a) | x IN G} *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) b IN orbit f g a ==> ?x. (act_by f g a b * stabilizer f g a = x * stabilizer f g a) /\ x IN G
       Let x = act_by f g a b.
       Note (a ~~ b) f g         by orbit_element, b IN orbit f g a
       Thus x IN G               by act_by_def, x = act_by f g a b
   (2) b IN orbit f g a /\ b' IN orbit f g a /\
       act_by f g a b * stabilizer f g a = act_by f g a b' * stabilizer f g a ==> b = b'
       Note (a ~~ b) f g /\ (a ~~ b') f g                 by orbit_element
        and act_by f g a b IN G /\ act_by f g a b' IN G   by act_by_def
       Thus b
          = f (act_by f g a b) a        by act_by_def
          = f (act_by f g a b') a       by orbit_stabilizer_map_inj
          = b'                          by act_by_def
   (3) same as (1)
   (4) x' IN G ==> ?b. b IN orbit f g a /\ (act_by f g a b * stabilizer f g a = x' * stabilizer f g a)
       Let b = f x' a.
       Then (a ~~ b) f g                by reach_def
        and b IN A                      by action_closure
         so b IN orbit f g a            by orbit_element
       Let x = act_by f g a b.
       Then f x a = b = f x' a          by act_by_def
        ==> x * stabilizer f g a = x' * stabilizer f g a
                                        by orbit_stabilizer_map_good
*)
Theorem orbit_stabilizer_cosets_bij:
  !f g A a. Group g /\ (g act A) f /\ a IN A ==>
            BIJ (\b. (act_by f g a b) * (stabilizer f g a))
                (orbit f g a)
                {x * (stabilizer f g a) | x IN G}
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
  metis_tac[orbit_element, act_by_def] >-
  metis_tac[orbit_stabilizer_map_inj, orbit_element, act_by_def] >-
  metis_tac[orbit_element, act_by_def] >>
  qexists_tac `f x' a` >>
  rpt strip_tac >-
  metis_tac[orbit_element, reach_def, action_closure] >>
  `(a ~~ (f x' a)) f g` by metis_tac[reach_def] >>
  metis_tac[orbit_stabilizer_map_good, act_by_def]
QED

(* The above version is not using CosetPartition. *)

(* Theorem: Elements of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act A) f /\ a IN A ==>
            BIJ (\b. (act_by f g a b) * (stabilizer f g a))
                (orbit f g a)
                (CosetPartition g (StabilizerGroup f g a) *)
(* Proof:
   By CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) b IN orbit f g a ==>
          ?x. x IN G /\ (act_by f g a b * stabilizer f g a = {y | y IN G /\ y IN x * stabilizer f g a})
       Let z = act_by f g a b, and put x = z.
       Note (a ~~ b) f g        by orbit_element
        and z IN G              by act_by_def,
       By coset_def, IMAGE_DEF, EXTENSION, this is to show:
          z IN G /\ z' IN stabilizer f g a ==> z * z' IN G
       Now z' IN G              by stabilizer_element
       Thus z * z' IN G         by group_op_element
   (2) b IN orbit f g a /\ b' IN orbit f g a /\
         act_by f g a b * stabilizer f g a = act_by f g a b' * stabilizer f g a ==> b = b'
       Note (a ~~ b) f g /\ (a ~~ b') f g                  by orbit_element
        and act_by f g a b IN G /\ act_by f g a b' IN G    by act_by_def
        ==> f (act_by f g a b) a = f (act_by f g a b') a   by orbit_stabilizer_map_inj
         so b = b'                                         by act_by_def
   (3) same as (1)
   (4) x' IN G /\ x = {y | y IN G /\ y IN x' * stabilizer f g a} ==>
         ?b. b IN orbit f g a /\ (act_by f g a b * stabilizer f g a = x)
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
Theorem orbit_stabilizer_cosets_bij_alt:
  !f g A a.
     Group g /\ (g act A) f /\ a IN A ==>
     BIJ (\b. (act_by f g a b) * (stabilizer f g a))
         (orbit f g a)
         (CosetPartition g (StabilizerGroup f g a))
Proof
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
    rename [‘X ∈ G’, ‘_ ∈ X * stabilizer f g a’] >>
    qexists_tac `f X a` >>
    rpt strip_tac >- metis_tac[orbit_element, action_closure, reach_def] >>
    qabbrev_tac `b = f X a` >>
    `(a ~~ b) f g` by metis_tac[reach_def] >>
    `act_by f g a b IN G /\ (f (act_by f g a b) a = f X a)` by rw[act_by_def] >>
    `act_by f g a b * (stabilizer f g a) = X * (stabilizer f g a)`
      by metis_tac[orbit_stabilizer_map_good] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    metis_tac[coset_def, IN_IMAGE, stabilizer_element, group_op_element]
  ]
QED

(* Theorem: [Orbit-Stabilizer Theorem]
            FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
            CARD G = CARD (orbit f g a) * CARD (stabilizer f g a) *)
(* Proof:
   Let h = StabilizerGroup f g a
   Then h <= g                          by stabilizer_group_subgroup
    and H = stabilizer f g a            by stabilizer_group_property
   Note CosetPartition g h = partition (inCoset g h) G  by CosetPartition_def
     so FINITE (CosetPartition g h)     by FINITE_partition
   Note FINITE_partition = IMAGE (\x. f x a) G  by orbit_def
     so FINITE (orbit f g a)            by IMAGE_FINITE

     CARD G
   = CARD H * CARD (CosetPartition g h)            by Lagrange_identity, h <= g
   = CARD (stabilizer f g a) * CARD (orbit f g a)  by orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ
   = CARD (orbit f g a) * CARD (stabilizer f g a)  by MULT_COMM
*)
Theorem orbit_stabilizer_thm:
  !f (g:'a group) A a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
                       CARD G = CARD (orbit f g a) * CARD (stabilizer f g a)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `StabilizerGroup f g a <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g a).carrier = stabilizer f g a` by rw[stabilizer_group_property] >>
  `FINITE (CosetPartition g (StabilizerGroup f g a))` by metis_tac[CosetPartition_def, FINITE_partition] >>
  `FINITE (orbit f g a)` by rw[orbit_def] >>
  `CARD G = CARD (stabilizer f g a) * CARD (CosetPartition g (StabilizerGroup f g a))` by metis_tac[Lagrange_identity] >>
  `_ = CARD (stabilizer f g a) * CARD (orbit f g a)` by metis_tac[orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ] >>
  rw[]
QED

(* This is a major milestone! *)

(* Theorem: FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
            CARD (orbit f g a) divides CARD G *)
(* Proof:
   Let b = orbit f g a,
       c = stabilizer f g a.
   Note CARD G = CARD b * CARD c         by orbit_stabilizer_thm
   Thus (CARD b) divides (CARD G)        by divides_def
*)
Theorem orbit_card_divides_target_card:
  !f (g:'a group) A a. FiniteGroup g /\ (g act A) f /\ a IN A /\ FINITE A ==>
                       CARD (orbit f g a) divides CARD G
Proof
  prove_tac[orbit_stabilizer_thm, divides_def, MULT_COMM]
QED

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

CARD Target = SUM CARD (orbits)
            = SUM CARD (singleton orbits) + SUM CARD (non-singleton orbits)
            = CARD (fixed_points) + SUM CARD (non-singleton orbits)
*)

(* Fixed points of action: those points fixed by all group elements. *)
val fixed_points_def = zDefine`
   fixed_points f (g:'a group) (A:'b -> bool) =
      {a | a IN A /\ !x. x IN G ==> f x a = a }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> fixed_points_def |> ISPEC ``$o``;
|- !g' A. fixed_points $o g' A = {a | a IN A /\ !x. x IN g'.carrier ==> x o a = a}: thm
*)

(* Theorem: Fixed point elements:
            a IN (fixed_points f g A) <=> a IN A /\ !x. x IN G ==> f x a = a *)
(* Proof: by fixed_points_def. *)
Theorem fixed_points_element:
  !f g A a. a IN (fixed_points f g A) <=> a IN A /\ !x. x IN G ==> f x a = a
Proof
  simp[fixed_points_def]
QED

(* Theorem: Fixed points are subsets of target set.
            (fixed_points f g A) SUBSET A *)
(* Proof: by fixed_points_def, SUBSET_DEF. *)
Theorem fixed_points_subset:
  !f g A. (fixed_points f g A) SUBSET A
Proof
  simp[fixed_points_def, SUBSET_DEF]
QED

(* Theorem: Fixed points are finite.
            FINITE A ==> FINITE (fixed_points f g A) *)
(* Proof: by fixed_points_subset, SUBSET_FINITE. *)
Theorem fixed_points_finite:
  !f g A. FINITE A ==> FINITE (fixed_points f g A)
Proof
  metis_tac[fixed_points_subset, SUBSET_FINITE]
QED

(* Theorem: a IN fixed_points f g A ==> a IN A *)
(* Proof: by fixed_points_def *)
Theorem fixed_points_element_element:
  !f g A a. a IN fixed_points f g A ==> a IN A
Proof
  simp[fixed_points_def]
QED

(* Fixed Points have singleton orbits, or those with stabilizer = whole group. *)

(* Theorem: Group g /\ (g act A) f ==>
           !a. a IN fixed_points f g A <=> (a IN A /\ orbit f g a = {a}) *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to show:
   (1) x' IN G /\ (!x. x IN G ==> (f x a = a)) ==> f x' a = a
       This is true                by the included implication
   (2) (!x. x IN G ==> (f x a = a)) ==> ?x. x IN G /\ (f x a = a)
       Take x = #e,
       Then x IN G                 by group_id_element
        and f x a = a              by implication
   (3) (g act A) f /\ x IN G ==> f x a = a
       This is true                by action_closure
*)
Theorem fixed_points_orbit_sing:
  !f g A. Group g /\ (g act A) f ==>
          !a. a IN fixed_points f g A <=>
             (a IN A /\ orbit f g a = {a})
Proof
  rw[fixed_points_def, orbit_def, EXTENSION, EQ_IMP_THM] >-
  rw_tac std_ss[] >-
  metis_tac[group_id_element] >>
  metis_tac[action_closure]
QED

(* Theorem: For action f g A, a IN A, (orbit f g a = {a}) ==> a IN fixed_points f g A *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to prove:
   (g act A) f /\ a IN A /\ x IN G /\
     !x. x IN A /\ (?x'. x' IN G /\ (f x' a = x)) <=> (x = a) ==> f x a = a
   This is true by action_closure.
*)
Theorem orbit_sing_fixed_points:
  !f g A. (g act A) f ==>
          !a. a IN A /\ orbit f g a = {a} ==> a IN fixed_points f g A
Proof
  rw[fixed_points_def, orbit_def, EXTENSION] >>
  metis_tac[action_closure]
QED
(* This is weaker than the previous theorem. *)

(* Theorem: Group g /\ (g act A) f ==>
           !a. a IN fixed_points f g A <=> SING (orbit f g a)) *)
(* Proof:
   By SING_DEF, this is to show:
   If part: a IN fixed_points f g A ==>?x. (orbit f g a) = {x}
      Take x = a, then true              by fixed_points_orbit_sing
   Only-if part: (orbit f g a) = {x} ==> a IN fixed_points f g A
      Note a IN (orbit f g a)            by orbit_has_self
      Thus x = a                         by IN_SING
        so a IN fixed_points f g A       by fixed_points_orbit_sing
*)
Theorem fixed_points_orbit_iff_sing:
  !f g A. Group g /\ (g act A) f ==>
          !a. a IN A ==> (a IN fixed_points f g A <=> SING (orbit f g a))
Proof
  metis_tac[fixed_points_orbit_sing, orbit_has_self, SING_DEF, IN_SING]
QED

(* Theorem: Group g /\ (g act A) f ==>
            !a. a IN (A DIFF fixed_points f g A) <=>
                a IN A /\ ~ SING (orbit f g a))  *)
(* Proof:
       a IN (A DIFF fixed_points f g A)
   <=> a IN A /\ a NOTIN (fixed_points f g A)  by IN_DIFF
   <=> a IN A /\ ~ SING (orbit f g a))         by fixed_points_orbit_iff_sing
*)
Theorem non_fixed_points_orbit_not_sing:
  !f g A. Group g /\ (g act A) f ==>
          !a. a IN (A DIFF fixed_points f g A) <=>
              a IN A /\ ~ SING (orbit f g a)
Proof
  metis_tac[IN_DIFF, fixed_points_orbit_iff_sing]
QED

(* Theorem: FINITE A ==> CARD (A DIFF fixed_points f g A) =
                         CARD A - CARD (fixed_points f g A) *)
(* Proof:
   Let fp = fixed_points f g A.
   Note fp SUBSET A                by fixed_points_subset
   Thus A INTER fp = fp            by SUBSET_INTER_ABSORPTION
     CARD (A DIFF bp)
   = CARD A - CARD (A INTER fp)    by CARD_DIFF
   = CARD A - CARD fp              by SUBSET_INTER_ABSORPTION
*)
Theorem non_fixed_points_card:
  !f g A. FINITE A ==>
          CARD (A DIFF fixed_points f g A) =
          CARD A - CARD (fixed_points f g A)
Proof
  metis_tac[CARD_DIFF, fixed_points_subset,
            SUBSET_INTER_ABSORPTION, SUBSET_FINITE, INTER_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Partition of Target into single orbits and non-single orbits.             *)
(* ------------------------------------------------------------------------- *)

(* Define singleton and non-singleton orbits *)
val sing_orbits_def = zDefine`
    sing_orbits f (g:'a group) (A:'b -> bool) = { e | e IN (orbits f g A) /\ SING e }
`;
val multi_orbits_def = zDefine`
    multi_orbits f (g:'a group) (A:'b -> bool) = { e | e IN (orbits f g A) /\ ~ SING e }
`;
(* Note: use zDefine as this is not effective for computation. *)

(* Theorem: e IN sing_orbits f g A <=> e IN (orbits f g A) /\ SING e *)
(* Proof: by sing_orbits_def *)
Theorem sing_orbits_element:
  !f g A e. e IN sing_orbits f g A <=> e IN (orbits f g A) /\ SING e
Proof
  simp[sing_orbits_def]
QED

(* Theorem: (sing_orbits f g A) SUBSET (orbits f g A) *)
(* Proof: by sing_orbits_element, SUBSET_DEF *)
Theorem sing_orbits_subset:
  !f g A. (sing_orbits f g A) SUBSET (orbits f g A)
Proof
  simp[sing_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE A ==> FINITE (sing_orbits f g A) *)
(* Proof: by sing_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem sing_orbits_finite:
  !f g A. FINITE A ==> FINITE (sing_orbits f g A)
Proof
  metis_tac[sing_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act A) f, elements of (sing_orbits f g A) are subsets of A.
            (g act A) f /\ e IN (sing_orbits f g A) ==> e SUBSET A *)
(* Proof: by sing_orbits_element, orbits_element_subset *)
Theorem sing_orbits_element_subset:
  !f g A e. (g act A) f /\ e IN (sing_orbits f g A) ==> e SUBSET A
Proof
  metis_tac[sing_orbits_element, orbits_element_subset]
QED

(* Theorem: e IN (sing_orbits f g A) ==> FINITE e *)
(* Proof: by sing_orbits_element, SING_FINITE *)
Theorem sing_orbits_element_finite:
  !f g A e. e IN (sing_orbits f g A) ==> FINITE e
Proof
  simp[sing_orbits_element, SING_FINITE]
QED

(* Theorem: e IN (sing_orbits f g A) ==> CARD e = 1 *)
(* Proof: by sing_orbits_element, SING_DEF, CARD_SING *)
Theorem sing_orbits_element_card:
  !f g A e. e IN (sing_orbits f g A) ==> CARD e = 1
Proof
  metis_tac[sing_orbits_element, SING_DEF, CARD_SING]
QED

(* Theorem: Group g /\ (g act A) f ==>
            !e. e IN (sing_orbits f g A) ==> CHOICE e IN fixed_points f g A *)
(* Proof:
   Note e IN orbits f g A /\ SING e  by sing_orbits_element
   Thus ?a. e = {a}                  by SING_DEF
    ==> a IN e /\ (CHOICE e = a)     by IN_SING, CHOICE_SING
     so e = orbit f g a              by orbits_element_is_orbit, a IN e
    and a IN A                       by orbits_element_element
    ==> a IN fixed_points f g A      by orbit_sing_fixed_points
*)
Theorem sing_orbits_element_choice:
  !f g A. Group g /\ (g act A) f ==>
          !e. e IN (sing_orbits f g A) ==> CHOICE e IN fixed_points f g A
Proof
  rw[sing_orbits_element] >>
  `?a. e = {a}` by rw[GSYM SING_DEF] >>
  `a IN e /\ (CHOICE e = a)` by rw[] >>
  `e = orbit f g a` by metis_tac[orbits_element_is_orbit] >>
  metis_tac[orbit_sing_fixed_points, orbits_element_element]
QED

(* Theorem: e IN multi_orbits f g A <=> e IN (orbits f g A) /\ ~SING e *)
(* Proof: by multi_orbits_def *)
Theorem multi_orbits_element:
  !f g A e. e IN multi_orbits f g A <=> e IN (orbits f g A) /\ ~SING e
Proof
  simp[multi_orbits_def]
QED

(* Theorem: (multi_orbits f g A) SUBSET (orbits f g A) *)
(* Proof: by multi_orbits_element, SUBSET_DEF *)
Theorem multi_orbits_subset:
  !f g A. (multi_orbits f g A) SUBSET (orbits f g A)
Proof
  simp[multi_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE A ==> FINITE (multi_orbits f g A) *)
(* Proof: by multi_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem multi_orbits_finite:
  !f g A. FINITE A ==> FINITE (multi_orbits f g A)
Proof
  metis_tac[multi_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act A) f, elements of (multi_orbits f g A) are subsets of A.
            (g act A) f /\ e IN (multi_orbits f g A) ==> e SUBSET A *)
(* Proof: by multi_orbits_element, orbits_element_subset *)
Theorem multi_orbits_element_subset:
  !f g A e. (g act A) f /\ e IN (multi_orbits f g A) ==> e SUBSET A
Proof
  metis_tac[multi_orbits_element, orbits_element_subset]
QED

(* Theorem: (g act A) f /\ e IN (multi_orbits f g A) ==> FINITE e *)
(* Proof: by multi_orbits_element, orbits_element_finite *)
Theorem multi_orbits_element_finite:
  !f g A e. (g act A) f /\ FINITE A /\ e IN (multi_orbits f g A) ==> FINITE e
Proof
  metis_tac[multi_orbits_element, orbits_element_finite]
QED

(* Theorem: sing_orbits and multi_orbits are disjoint.
            DISJOINT (sing_orbits f g A) (multi_orbits f g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def, DISJOINT_DEF. *)
Theorem target_orbits_disjoint:
  !f g A. DISJOINT (sing_orbits f g A) (multi_orbits f g A)
Proof
  rw[sing_orbits_def, multi_orbits_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: orbits = sing_orbits + multi_orbits.
            orbits f g A = (sing_orbits f g A) UNION (multi_orbits f g A) *)
(* Proof: by sing_orbits_def, multi_orbits_def. *)
Theorem target_orbits_union:
  !f g A. orbits f g A = (sing_orbits f g A) UNION (multi_orbits f g A)
Proof
  rw[sing_orbits_def, multi_orbits_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: For (g act A) f, CARD A = CARD sing_orbits + SIGMA CARD multi_orbits.
            Group g /\ (g act A) f /\ FINITE A ==>
            (CARD A = CARD (sing_orbits f g A) + SIGMA CARD (multi_orbits f g A)) *)
(* Proof:
   Let s = sing_orbits f g A, t = multi_orbits f g A.
   Note FINITE s                   by sing_orbits_finite
    and FINITE t                   by multi_orbits_finite
   also s INTER t = {}             by target_orbits_disjoint, DISJOINT_DEF

     CARD A
   = SIGMA CARD (orbits f g A)     by target_card_by_partition
   = SIGMA CARD (s UNION t)        by target_orbits_union
   = SIGMA CARD s + SIGMA CARD t   by SUM_IMAGE_UNION, SUM_IMAGE_EMPTY
   = 1 * CARD s + SIGMA CARD t     by sing_orbits_element_card, SIGMA_CARD_CONSTANT
   = CARD s + SIGMA CARD t         by MULT_LEFT_1
*)
Theorem target_card_by_orbit_types:
  !f g A. Group g /\ (g act A) f /\ FINITE A ==>
          CARD A = CARD (sing_orbits f g A) + SIGMA CARD (multi_orbits f g A)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = sing_orbits f g A` >>
  qabbrev_tac `t = multi_orbits f g A` >>
  `FINITE s` by rw[sing_orbits_finite, Abbr`s`] >>
  `FINITE t` by rw[multi_orbits_finite, Abbr`t`] >>
  `s INTER t = {}` by rw[target_orbits_disjoint, GSYM DISJOINT_DEF, Abbr`s`, Abbr`t`] >>
  `CARD A = SIGMA CARD (orbits f g A)` by rw_tac std_ss[target_card_by_partition] >>
  `_ = SIGMA CARD (s UNION t)` by rw_tac std_ss[target_orbits_union] >>
  `_ = SIGMA CARD s + SIGMA CARD t` by rw[SUM_IMAGE_UNION, SUM_IMAGE_EMPTY] >>
  `_ = 1 * CARD s + SIGMA CARD t` by metis_tac[sing_orbits_element_card, SIGMA_CARD_CONSTANT] >>
  rw[]
QED

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)
               where e = {a} is injective.
            Group g /\ (g act A) f ==>
            INJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
       This is true                    by sing_orbits_element_choice
   (2) e IN sing_orbits f g A /\ e' IN sing_orbits f g A /\ CHOICE e = CHOICE e' ==> e = e'
       Note SING e /\ SING e'          by sing_orbits_element
       Thus this is true               by SING_DEF, CHOICE_SING.
*)
Theorem sing_orbits_to_fixed_points_inj:
  !f g A. Group g /\ (g act A) f ==>
          INJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)
Proof
  rw[INJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  metis_tac[sing_orbits_element, SING_DEF, CHOICE_SING]
QED

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)
               where e = {a} is surjective.
            Group g /\ (g act A) f ==>
            SURJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) e IN sing_orbits f g A ==> CHOICE e IN fixed_points f g A
       This is true                      by sing_orbits_element_choice
   (2) x IN fixed_points f g A ==> ?e. e IN sing_orbits f g A /\ (CHOICE e = x)
       Note x IN A                       by fixed_points_element
        and orbit f g x = {x}            by fixed_points_orbit_sing
       Take e = {x},
       Then CHOICE e = x                 by CHOICE_SING
        and SING e                       by SING_DEF
        and e IN orbits f g A            by orbit_is_orbits_element
        ==> e IN sing_orbits f g A       by sing_orbits_element
*)
Theorem sing_orbits_to_fixed_points_surj:
  !f g A. Group g /\ (g act A) f ==>
          SURJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)
Proof
  rw[SURJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  `x IN A` by metis_tac[fixed_points_element] >>
  `orbit f g x = {x}` by metis_tac[fixed_points_orbit_sing] >>
  qexists_tac `{x}` >>
  simp[sing_orbits_element] >>
  metis_tac[orbit_is_orbits_element]
QED

(* Theorem: The map: e IN (sing_orbits f g A) --> a IN (fixed_points f g A)
               where e = {a} is bijective.
            Group g /\ (g act A) f ==>
            BIJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A) *)
(* Proof:
   By sing_orbits_to_fixed_points_inj,
      sing_orbits_to_fixed_points_surj, BIJ_DEF.
   True since the map is shown to be both injective and surjective.
*)
Theorem sing_orbits_to_fixed_points_bij:
  !f g A. Group g /\ (g act A) f ==>
          BIJ (\e. CHOICE e) (sing_orbits f g A) (fixed_points f g A)
Proof
  simp[BIJ_DEF, sing_orbits_to_fixed_points_surj,
                sing_orbits_to_fixed_points_inj]
QED

(* Theorem: For (g act A) f, sing_orbits is the same size as fixed_points f g A,
            Group g /\ (g act A) f /\ FINITE A ==>
            CARD (sing_orbits f g A) = CARD (fixed_points f g A) *)
(* Proof:
   Let s = sing_orbits f g A, t = fixed_points f g A.
   Note s SUBSET (orbits f g A)    by sing_orbits_subset
    and t SUBSET A                 by fixed_points_subset
   Also FINITE s                   by orbits_finite, SUBSET_FINITE
    and FINITE t                   by SUBSET_FINITE
   With BIJ (\e. CHOICE e) s t     by sing_orbits_to_fixed_points_bij
    ==> CARD s = CARD t            by FINITE_BIJ_CARD_EQ
*)
Theorem sing_orbits_card_eqn:
  !f g A. Group g /\ (g act A) f /\ FINITE A ==>
          CARD (sing_orbits f g A) = CARD (fixed_points f g A)
Proof
  rpt strip_tac >>
  `(sing_orbits f g A) SUBSET (orbits f g A)` by rw[sing_orbits_subset] >>
  `(fixed_points f g A) SUBSET A` by rw[fixed_points_subset] >>
  metis_tac[sing_orbits_to_fixed_points_bij, FINITE_BIJ_CARD_EQ, SUBSET_FINITE, orbits_finite]
QED

(* Theorem: For (g act A) f, CARD A = CARD fixed_points + SIGMA CARD multi_orbits.
            Group g /\ (g act A) f /\ FINITE A ==>
            CARD A = CARD (fixed_points f g A) + SIGMA CARD (multi_orbits f g A) *)
(* Proof:
   Let s = sing_orbits f g A, t = multi_orbits f g A.
     CARD A
   = CARD s + SIGMA CARD t                       by target_card_by_orbit_types
   = CARD (fixed_points f g A) + SIGMA CARD t    by sing_orbits_card_eqn
*)
Theorem target_card_by_fixed_points:
  !f g A. Group g /\ (g act A) f /\ FINITE A ==>
          CARD A = CARD (fixed_points f g A) + SIGMA CARD (multi_orbits f g A)
Proof
  metis_tac[target_card_by_orbit_types, sing_orbits_card_eqn]
QED

(* Theorem:  Group g /\ (g act A) f /\ FINITE A /\ 0 < n /\
             (!e. e IN multi_orbits f g A ==> (CARD e = n)) ==>
             (CARD A MOD n = CARD (fixed_points f g A) MOD n) *)
(* Proof:
   Let s = fixed_points f g A,
       t = multi_orbits f g A.
   Note FINITE t                         by multi_orbits_finite
       (CARD A) MOD n
     = (CARD s + SIGMA CARD t) MOD n     by target_card_by_fixed_points
     = (CARD s + n * CARD t) MOD n       by SIGMA_CARD_CONSTANT, FINITE t
     = (CARD t * n + CARD s) MOD n       by ADD_COMM, MULT_COMM
     = (CARD s) MOD n                    by MOD_TIMES
*)
Theorem target_card_and_fixed_points_congruence:
  !f g A n. Group g /\ (g act A) f /\ FINITE A /\ 0 < n /\
            (!e. e IN multi_orbits f g A ==> (CARD e = n)) ==>
            CARD A MOD n = CARD (fixed_points f g A) MOD n
Proof
  rpt strip_tac >>
  imp_res_tac target_card_by_fixed_points >>
  `_ = CARD (fixed_points f g A) + n * CARD (multi_orbits f g A)`
     by rw[multi_orbits_finite, SIGMA_CARD_CONSTANT] >>
  fs[]
QED

(* This is a very useful theorem! *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
