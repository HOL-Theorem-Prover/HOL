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

open monoidTheory groupTheory;
open subgroupTheory groupOrderTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory dividesTheory
     gcdTheory combinatoricsTheory;

(*===========================================================================*)

(*

Group action
============
. action f is a map from Group g to target set X, satisfying some conditions.
. The action induces an equivalence relation "reach" on target set X.
. The equivalent classes of "reach" on A are called orbits.
. Due to this partition, CARD X = SIGMA CARD orbits.
. As equivalent classes are non-empty, minimum CARD orbit = 1.
. These singleton orbits have a 1-1 correspondence with a special set on A:
  the fixed_points. The main result is:
  CARD X = CARD fixed_points + SIGMA (CARD non-singleton orbits).

  When group action is applied to necklaces, Z[n] enters into the picture.
  The cyclic Z[n] of modular addition is the group for necklaces of n beads.

Rework
======
. name target set Xs X, with points x, y, use a, b as group elements.
. keep x, y as group elements, a, b as set A elements.
. orbit is defined as image, with one less parameter.
. orbits is named, replacing TargetPartition.

*)

(*===========================================================================*)

(* ------------------------------------------------------------------------- *)
(* Group Action Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (g act X) f    = action f g X
   (x ~~ y) f g   = reach f g x y
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Group action:
   action_def       |- !f g X. (g act X) f <=> !x. x IN X ==>
                               (!a. a IN G ==> f a x IN X) /\ f #e x = x /\
                                !a b. a IN G /\ b IN G ==> f a (f b x) = f (a * b) x
   action_closure   |- !f g X. (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X
   action_compose   |- !f g X. (g act X) f ==>
                       !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x
   action_id        |- !f g X. (g act X) f ==> !x. x IN X ==> f #e x = x
   action_reverse   |- !f g X. Group g /\ (g act X) f ==>
                       !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x
   action_trans     |- !f g X. (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
                       x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z

   Group action induces an equivalence relation:
   reach_def    |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = b
   reach_refl   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g
   reach_sym    |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g
   reach_trans  |- !f g X x y z. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
                                 (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g
   reach_equiv  xx|- !f g X. Group g /\ (g act X) f ==> reach f g equiv_on X

   Orbits as equivalence classes of Group action:
   orbit_def           |- !f g x. orbit f g x = IMAGE (\a. f a x) G
   orbit_alt           |- !f g x. orbit f g x = {f a x | a IN G}
   orbit_element       |- !f g x y. y IN orbit f g x <=> (x ~~ y) f g
   orbit_has_action_element
                       |- !f g x a. a IN G ==> f a x IN orbit f g x
   orbit_has_self      |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x
   orbit_subset_target |- !f g X x. (g act X) f /\ x IN X ==> orbit f g x SUBSET X
   orbit_element_in_target
                       |- !f g X x y. (g act X) f /\ x IN X /\ y IN orbit f g x ==> y IN X
   orbit_finite        |- !f g X. FINITE G ==> FINITE (orbit f g x)
   orbit_finite_by_target
                       |- !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x)
   orbit_eq_equiv_class|- !f g X x. (g act X) f /\ x IN X ==>
                                    orbit f g x = equiv_class (reach f g) X x
   orbit_eq_orbit      |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
                                     (orbit f g x = orbit f g y <=> (x ~~ y) f g)

   Partition by Group action:
   orbits_def          |- !f g X. orbits f g X = IMAGE (orbit f g) X
   orbits_alt          |- !f g X. orbits f g X = {orbit f g x | x IN X}
   orbits_element      |- !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x
   orbits_eq_partition |- !f g X. (g act X) f ==> orbits f g X = partition (reach f g) X
   orbits_finite       |- !f g X. FINITE X ==> FINITE (orbits f g X)
   orbits_element_finite   |- !f g X. (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X)
   orbits_element_nonempty |- !f g X. Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> {}
   orbits_element_subset   |- !f g X e. (g act X) f /\ e IN orbits f g X ==> e SUBSET X
   orbits_element_element  |- !f g X e x. (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X
   orbit_is_orbits_element |- !f g X x. x IN X ==> orbit f g x IN orbits f g X
   orbits_element_is_orbit |- !f g X e x. Group g /\ (g act X) f /\ e IN orbits f g X /\ x IN e ==>
                                          e = orbit f g x

   Target size and orbit size:
   action_to_orbit_surj        |- !f g X x. (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x)
   orbit_finite_inj_card_eq    |- !f g X x. (g act X) f /\ x IN X /\ FINITE X /\
                                            INJ (\a. f a x) G (orbit f g x) ==>
                                            CARD (orbit f g x) = CARD G
   target_card_by_partition    |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                          CARD X = SIGMA CARD (orbits f g X)
   orbits_equal_size_partition_equal_size
                               |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> CARD (orbit f g x) = n) ==>
                                            !e. e IN orbits f g X ==> CARD e = n
   orbits_equal_size_property  |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> CARD (orbit f g x) = n) ==>
                                            n divides CARD X
   orbits_size_factor_partition_factor
                               |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> n divides CARD (orbit f g x)) ==>
                                            !e. e IN orbits f g X ==> n divides CARD e
   orbits_size_factor_property |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> n divides CARD (orbit f g x)) ==>
                                            n divides CARD X

   Stabilizer as invariant:
   stabilizer_def        |- !f g x. stabilizer f g x = {a | a IN G /\ f a x = x}
   stabilizer_element    |- !f g x a. a IN stabilizer f g x <=> a IN G /\ f a x = x
   stabilizer_subset     |- !f g x. stabilizer f g x SUBSET G
   stabilizer_has_id     |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x
   stabilizer_nonempty   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> {}
   stabilizer_as_image   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      stabilizer f g x = IMAGE (\x. if f a x = x then a else #e) G

   Stabilizer subgroup:
   StabilizerGroup_def            |- !f g x. StabilizerGroup f g x =
                                             <|carrier := stabilizer f g x; op := $*; id := #e|>
   stabilizer_group_property      |- !f g X. ((StabilizerGroup f g x).carrier = stabilizer f g x) /\
                                             ((StabilizerGroup f g x).op = $* ) /\
                                             ((StabilizerGroup f g x).id = #e)
   stabilizer_group_carrier       |- !f g X. (StabilizerGroup f g x).carrier = stabilizer f g x
   stabilizer_group_id            |- !f g X. (StabilizerGroup f g x).id = #e
   stabilizer_group_group         |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                               Group (StabilizerGroup f g x)
   stabilizer_group_subgroup      |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                               StabilizerGroup f g x <= g
   stabilizer_group_finite_group  |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                                               FiniteGroup (StabilizerGroup f g x)
   stabilizer_group_card_divides  |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                                               CARD (stabilizer f g x) divides CARD G

   Orbit-Stabilizer Theorem:
   orbit_stabilizer_map_good |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                                      (a * stabilizer f g x = b * stabilizer f g x)
   orbit_stabilizer_map_inj  |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G /\ (a * stabilizer f g x = b * stabilizer f g x) ==>
                                      f a x = f b x
   action_match_condition    |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G ==> (f a x = f b x <=> |/ x * y IN stabilizer f g x)
   action_match_condition_alt|- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !x y::G. f a x = f b x <=> |/ x * y IN stabilizer f g x
   stabilizer_conjugate      |- !f g X x a. Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
                                            (conjugate g a (stabilizer f g x) = stabilizer f g (f a x))
   act_by_def                |- !f g x y. (x ~~ y) f g ==> act_by f g x y IN G /\ f (act_by f g x y) x = y
   action_reachable_coset    |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
                                (act_by f g x y * stabilizer f g x = {a | a IN G /\ f a x = y})
   action_reachable_coset_alt|- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
                                !a. a IN G /\ f a x = y ==> a * stabilizer f g x = {b | b IN G /\ f b x = y}
   orbit_stabilizer_cosets_bij     |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      BIJ (\y. act_by f g x y * stabilizer f g x)
                                          (orbit f g x)
                                          {a * stabilizer f g x | a | a IN G}
   orbit_stabilizer_cosets_bij_alt |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      BIJ (\y. act_by f g x y * stabilizer f g x)
                                          (orbit f g x)
                                          (CosetPartition g (StabilizerGroup f g x))
   orbit_stabilizer_thm      |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                                          (CARD G = CARD (orbit f g x) * CARD (stabilizer f g x))
   orbit_card_divides_target_card
                             |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                                          CARD (orbit f g x) divides CARD G

   Fixed Points of action:
   fixed_points_def          |- !f g X. fixed_points f g X = {x | x IN X /\ !a. a IN G ==> f a x = x}
   fixed_points_element      |- !f g X x. x IN fixed_points f g X <=>
                                          x IN X /\ !a. a IN G ==> f a x = x
   fixed_points_subset       |- !f g X. fixed_points f g X SUBSET X
   fixed_points_finite       |- !f g X. FINITE X ==> FINITE (fixed_points f g X)
   fixed_points_element_element
                             |- !f g X x. x IN fixed_points f g X ==> x IN X
   fixed_points_orbit_sing   |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN fixed_points f g X <=> <=> x IN X /\ orbit f g x = {x}
   orbit_sing_fixed_points   |- !f g X. (g act X) f ==>
                                !x. x IN X /\ orbit f g x = {x} ==> x IN fixed_points f g X
   fixed_points_orbit_iff_sing
                             |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN X ==> (x IN fixed_points f g X <=> SING (orbit f g x))
   non_fixed_points_orbit_not_sing
                             |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN X DIFF fixed_points f g X <=> x IN X /\ ~SING (orbit f g x)
   non_fixed_points_card     |- !f g X. FINITE X ==>
                                CARD (X DIFF fixed_points f g X) = CARD X - CARD (fixed_points f g X)

   Target Partition by orbits:
   sing_orbits_def                  |- !f g X. sing_orbits f g X = {e | e IN orbits f g X /\ SING e}
   multi_orbits_def                 |- !f g X. multi_orbits f g X = {e | e IN orbits f g X /\ ~SING e}
   sing_orbits_element              |- !f g X e. e IN sing_orbits f g X <=> e IN orbits f g X /\ SING e
   sing_orbits_subset               |- !f g X. sing_orbits f g X SUBSET orbits f g X
   sing_orbits_finite               |- !f g X. FINITE X ==> FINITE (sing_orbits f g X)
   sing_orbits_element_subset       |- !f g X e. (g act X) f /\ e IN sing_orbits f g X ==> e SUBSET X
   sing_orbits_element_finite       |- !f g X e. e IN sing_orbits f g X ==> FINITE e
   sing_orbits_element_card         |- !f g X e. e IN sing_orbits f g X ==> CARD e = 1
   sing_orbits_element_choice       |- !f g X. Group g /\ (g act X) f ==>
                                       !e. e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
   multi_orbits_element             |- !f g X e. e IN multi_orbits f g X <=> e IN orbits f g X /\ ~SING e
   multi_orbits_subset              |- !f g X. multi_orbits f g X SUBSET orbits f g X
   multi_orbits_finite              |- !f g X. FINITE X ==> FINITE (multi_orbits f g X)
   multi_orbits_element_subset      |- !f g X e. (g act X) f /\ e IN multi_orbits f g X ==> e SUBSET X
   multi_orbits_element_finite      |- !f g X e. (g act X) f /\ FINITE X /\ e IN multi_orbits f g X ==> FINITE e
   target_orbits_disjoint           |- !f g X. DISJOINT (sing_orbits f g X) (multi_orbits f g X)
   target_orbits_union              |- !f g X. orbits f g X = sing_orbits f g X UNION multi_orbits f g X
   target_card_by_orbit_types       |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                       (CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X))
   sing_orbits_to_fixed_points_inj  |- !f g X. Group g /\ (g act X) f ==>
                                               INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_to_fixed_points_surj |- !f g X. Group g /\ (g act X) f ==>
                                               SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g
   sing_orbits_to_fixed_points_bij  |- !f g X. Group g /\ (g act X) f ==>
                                               BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_card_eqn             |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                               (CARD (sing_orbits f g X) = CARD (fixed_points f g X))
   target_card_by_fixed_points      |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                              (CARD X = CARD (fixed_points f g X) +
                                                        SIGMA CARD (multi_orbits f g X))
   target_card_and_fixed_points_congruence
                                    |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
                                                (!e. e IN multi_orbits f g X ==> CARD e = n) ==>
                                                 CARD X MOD n = CARD (fixed_points f g X) MOD n
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Group action                                                              *)
(* ------------------------------------------------------------------------- *)

(* An action from group g to a set X is a map f: G x X -> X such that
   (0)   [is a map] f (a IN G)(x IN X) in X
   (1)  [id action] f (e in G)(x IN X) = x
   (2) [composable] f (a IN G)(f (b in G)(x IN X)) =
                    f (g.op (a IN G)(b in G))(x IN X)
*)
Definition action_def:
    action f (g:'a group) (X:'b -> bool) =
       !x. x IN X ==> (!a. a IN G ==> f a x IN X) /\
                      f #e x = x /\
                      (!a b. a IN G /\ b IN G ==> f a (f b x) = f (a * b) x)
End

(* Overload on action *)
val _ = overload_on("act", ``\(g:'a group) (X:'b -> bool) f. action f g X``);
val _ = set_fixity "act" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> action_def;
val it = |- !(f :'a -> 'b -> 'b) (g :'a group) (X :'b -> bool).
     (g act X) f <=> !(x :'b). x IN X ==>
       (!(a :'a). a IN G ==> f a x IN X) /\ f #e x = x /\
       !(a :'a) (b :'a). a IN G /\ b IN G ==> (f a (f b x) = f ((a * b) :'a) x): thm
> action_def |> ISPEC ``$o``;
val it = |- !g' X. (g' act A) $o <=>
            !x. x IN X ==>
              (!a. a IN g'.carrier ==> a o x IN X) /\ g'.id o x = x /\
               !a b. a IN g'.carrier /\ b IN g'.carrier ==> a o b o x = g'.op a b o x: thm
*)

(* ------------------------------------------------------------------------- *)
(* Action Properties                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Closure]
            (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X *)
(* Proof: by action_def. *)
Theorem action_closure:
  !f g X. (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X
Proof
  rw[action_def]
QED

(* Theorem: [Compose]
            (g act X) f ==> !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x *)
(* Proof: by action_def. *)
Theorem action_compose:
  !f g X. (g act X) f ==> !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x
Proof
  rw[action_def]
QED

(* Theorem: [Identity]
            (g act X) f ==> !x. x IN X ==> f #e x = x *)
(* Proof: by action_def. *)
Theorem action_id:
  !f g X. (g act X) f ==> !x. x IN X ==> f #e x = x
Proof
  rw[action_def]
QED
(* This is essentially reach_refl *)

(* Theorem: Group g /\ (g act X) f ==>
            !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x *)
(* Proof:
   Note |/ a IN G        by group_inv_element
     f ( |/ a) y
   = f ( |/ a) (f a x)   by y = f a x
   = f ( |/ a * a) x     by action_compose
   = f #e x              by group_linv
   = x                   by action_id
*)
Theorem action_reverse:
  !f g X. Group g /\ (g act X) f ==>
          !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x
Proof
  rw[action_def]
QED
(* This is essentially reach_sym *)

(* Theorem: (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
            x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z *)
(* Proof:
     f (b * a) x
   = f b (f a x)     by action_compose
   = f b y           by y = f a x
   = z               by z = f b y
*)
Theorem action_trans:
  !f g X. (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
          x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z
Proof
  rw[action_def]
QED
(* This is essentially reach_trans *)

(* ------------------------------------------------------------------------- *)
(* Group action induces an equivalence relation.                             *)
(* ------------------------------------------------------------------------- *)

(* Define reach to relate two action points a and y IN X *)
val reach_def = zDefine`
    reach f (g:'a group) (x:'b) (y:'b) = ?a. a IN G /\ f a x = y
`;
(* Note: use zDefine as this is not effective. *)

(* Overload reach relation *)
val _ = temp_overload_on("~~", ``\(x:'b) (y:'b) f (g:'a group). reach f g x y``);
(* Make reach an infix. *)
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> reach_def;
val it = |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = y
*)

(* Theorem: [Reach is Reflexive]
            Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g  *)
(* Proof:
   Note f #e x = x         by action_id
    and #e in G            by group_id_element
   Thus (x ~~ x) f g       by reach_def, take x = #e.
*)
Theorem reach_refl:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g
Proof
  metis_tac[reach_def, action_id, group_id_element]
QED

(* Theorem: [Reach is Symmetric]
            Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g *)
(* Proof:
   Note ?a. a IN G /\ f a x = y     by reach_def, (x ~~ y) f g
    ==> f ( |/ a) y = x             by action_reverse
    and |/ a IN G                   by group_inv_element
   Thus (y ~~ x) f g                by reach_def
*)
Theorem reach_sym:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g
Proof
  metis_tac[reach_def, action_reverse, group_inv_element]
QED

(* Theorem: [Reach is Transitive]
            Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
            (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g *)
(* Proof:
   Note ?a. a IN G /\ f a x = y       by reach_def, (x ~~ y) f g
    and ?b. b IN G /\ f b y = z       by reach_def, (y ~~ z) f g
   Thus f (b * a) x = z               by action_trans
    and b * a IN G                    by group_op_element
    ==> (x ~~ z) f g                  by reach_def
*)
Theorem reach_trans:
  !f g X x y z. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
                (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g
Proof
  rw[reach_def] >>
  metis_tac[action_trans, group_op_element]
QED

(* Theorem: Reach is an equivalence relation on target set X.
            Group g /\ (g act X) f ==> (reach f g) equiv_on X *)
(* Proof:
   By Reach being Reflexive, Symmetric and Transitive.
*)
Theorem reach_equiv:
  !f g X. Group g /\ (g act X) f ==> (reach f g) equiv_on X
Proof
  rw_tac std_ss[equiv_on_def] >-
  metis_tac[reach_refl] >-
  metis_tac[reach_sym] >>
  metis_tac[reach_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Orbits as equivalence classes.                                            *)
(* ------------------------------------------------------------------------- *)

(* Orbit of action for a: those that can be reached by taking a IN G. *)
Definition orbit_def:
   orbit (f:'a -> 'b -> 'b) (g:'a group) (x:'b) = IMAGE (\a. f a x) G
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbit_def |> ISPEC ``$o``;
val it = |- !g' x. orbit $o g' x = IMAGE (\a. a o x) g'.carrier: thm
*)

(* Theorem: orbit f g x = {f a x | a IN G} *)
(* Proof: by orbit_def, EXTENSION. *)
Theorem orbit_alt:
  !f g x. orbit f g x = {f a x | a IN G}
Proof
  simp[orbit_def, EXTENSION]
QED

(* Theorem: y IN orbit f g x <=> (x ~~ y) f g *)
(* Proof:
       y IN orbit f g x
   <=> ?a. a IN G /\ (y = f a x)   by orbit_def, IN_IMAGE
   <=> (x ~~ y) f g                by reach_def
*)
Theorem orbit_element:
  !f g x y. y IN orbit f g x <=> (x ~~ y) f g
Proof
  simp[orbit_def, reach_def] >>
  metis_tac[]
QED

(* Theorem: a IN G ==> f a x IN (orbit f g x) *)
(* Proof: by orbit_def *)
Theorem orbit_has_action_element:
  !f g x a. a IN G ==> f a x IN (orbit f g x)
Proof
  simp[orbit_def] >>
  metis_tac[]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x *)
(* Proof:
   Let b = orbit f g x.
   Note #e IN G            by group_id_element
     so #e o x IN b        by orbit_has_action_element
    and #e o x = x         by action_id, x IN X
   thus x IN b             by above
*)
Theorem orbit_has_self:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x
Proof
  metis_tac[orbit_has_action_element, group_id_element, action_id]
QED

(* Theorem: orbits are subsets of the target set.
            (g act X) f /\ x IN X ==> (orbit f g x) SUBSET X *)
(* Proof: orbit_def, SUBSET_DEF, action_closure. *)
Theorem orbit_subset_target:
  !f g X x. (g act X) f /\ x IN X ==> (orbit f g x) SUBSET X
Proof
  rw[orbit_def, SUBSET_DEF] >>
  metis_tac[action_closure]
QED

(* Theorem: orbits elements are in the target set.
            (g act X) f /\ x IN X /\ y IN (orbit f g x) ==> y IN X *)
(* Proof: orbit_subset_target, SUBSET_DEF. *)
Theorem orbit_element_in_target:
  !f g X x y. (g act X) f /\ x IN X /\ y IN (orbit f g x) ==> y IN X
Proof
  metis_tac[orbit_subset_target, SUBSET_DEF]
QED

(* Theorem: FINITE G ==> FINITE (orbit f g x) *)
(* Proof: by orbit_def, IMAGE_FINITE. *)
Theorem orbit_finite:
  !f (g:'a group) x. FINITE G ==> FINITE (orbit f g x)
Proof
  simp[orbit_def]
QED

(* Theorem: (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x) *)
(* Proof: by orbit_subset_target, SUBSET_FINITE. *)
Theorem orbit_finite_by_target:
  !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x)
Proof
  metis_tac[orbit_subset_target, SUBSET_FINITE]
QED

(* Theorem: (g act X) f /\ x IN X ==> orbit f g x = equiv_class (reach f g) X x *)
(* Proof: by orbit_def, reach_def, action_closure. *)
Theorem orbit_eq_equiv_class:
  !f g X x. (g act X) f /\ x IN X ==> orbit f g x = equiv_class (reach f g) X x
Proof
  simp[orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
            (orbit f g x = orbit f g y <=> (x ~~ y) f g) *)
(* Proof: by orbit_eq_equiv_class, reach_equiv, equiv_class_eq. *)
Theorem orbit_eq_orbit:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
              (orbit f g x = orbit f g y <=> (x ~~ y) f g)
Proof
  metis_tac[orbit_eq_equiv_class, reach_equiv, equiv_class_eq]
QED

(* ------------------------------------------------------------------------- *)
(* Partition by Group action.                                                *)
(* ------------------------------------------------------------------------- *)

(* The collection of orbits of target points. *)
Definition orbits_def:
   orbits f (g:'a group) X = IMAGE (orbit f g) X
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbits_def |> ISPEC ``$o``;
val it = |- !g' X. orbits $o g' X = IMAGE (orbit $o g') X: thm
*)

(* Theorem: orbits f g X = {orbit f g x | x | x IN X} *)
(* Proof: by orbits_def, EXTENSION. *)
Theorem orbits_alt:
  !f g X. orbits f g X = {orbit f g x | x | x IN X}
Proof
  simp[orbits_def, EXTENSION]
QED

(* Theorem: e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbits_element:
  !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x
Proof
  simp[orbits_def] >>
  metis_tac[]
QED

(* Theorem: (g act X) f ==> orbits f g X = partition (reach f g) X *)
(* Proof:
   By EXTENSION,
       e IN orbits f g X
   <=> ?x. x IN X /\ e = orbit f g x     by orbits_element
   <=> ?x. x IN X /\ e = equiv_class (reach f g) X x
                                         by orbit_eq_equiv_class, (g act X) f
   <=> e IN partition (reach f g) X)     by partition_element
*)
Theorem orbits_eq_partition:
  !f g X. (g act X) f ==> orbits f g X = partition (reach f g) X
Proof
  rw[EXTENSION] >>
  metis_tac[orbits_element, orbit_eq_equiv_class, partition_element]
QED

(* Theorem: orbits = target partition is FINITE.
            FINITE X ==> FINITE (orbits f g X) *)
(* Proof: by orbits_def, IMAGE_FINITE *)
Theorem orbits_finite:
  !f g X. FINITE X ==> FINITE (orbits f g X)
Proof
  simp[orbits_def]
QED

(* Theorem: For e IN (orbits f g X), FINITE X ==> FINITE e
            (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X) *)
(* Proof: by orbits_eq_partition, FINITE_partition. *)
Theorem orbits_element_finite:
  !f g X. (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X)
Proof
  metis_tac[orbits_eq_partition, FINITE_partition]
QED
(*
orbit_finite_by_target;
|- !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x): thm
*)

(* Theorem: For e IN (orbits f g X), e <> EMPTY
            Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> EMPTY *)
(* Proof: by orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition. *)
Theorem orbits_element_nonempty:
  !f g X. Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> EMPTY
Proof
  simp[orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition]
QED
(*
orbit_has_self;
|- !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x: thm
*)

(* Theorem: orbits elements are subset of target.
            (g act X) f /\ e IN orbits f g X ==> e SUBSET X *)
(* Proof: by orbits_eq_partition, partition_SUBSET. *)
Theorem orbits_element_subset:
  !f g X e. (g act X) f /\ e IN orbits f g X ==> e SUBSET X
Proof
  metis_tac[orbits_eq_partition, partition_SUBSET]
QED
(*
orbit_subset_target;
|- !f g X x. (g act X) f /\ x IN X ==> orbit f g x SUBSET X: thm
*)

(* Theorem: Elements in element of orbits are also in target.
            (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X *)
(* Proof: by orbits_element_subset, SUBSET_DEF *)
Theorem orbits_element_element:
  !f g X e x. (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X
Proof
  metis_tac[orbits_element_subset, SUBSET_DEF]
QED
(*
orbit_element_in_target;
|- !f g X x y. (g act X) f /\ x IN X /\ y IN orbit f g x ==> y IN X: thm
*)

(* Theorem: x IN X ==> (orbit f g x) IN (orbits f g X) *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbit_is_orbits_element:
  !f g X x. x IN X ==> (orbit f g x) IN (orbits f g X)
Proof
  simp[orbits_def]
QED

(* Theorem: Elements of orbits are orbits of its own element.
            Group g /\ (g act X) f /\ e IN orbits f g X /\ x IN e ==> e = orbit f g x *)
(* Proof:
   By orbits_def, this is to show:
   x IN X /\ y IN orbit f g x ==> orbit f g x = orbit f g y

   Note y IN X                       by orbit_element_in_target
    and (x ~~ y) f g                 by orbit_element
    ==> orbit f g x = orbit f g y    by orbit_eq_orbit
*)
Theorem orbits_element_is_orbit:
  !f g X e x. Group g /\ (g act X) f /\ e IN orbits f g X /\
              x IN e ==> e = orbit f g x
Proof
  rw[orbits_def] >>
  metis_tac[orbit_element_in_target, orbit_element, orbit_eq_orbit]
QED
(*
orbits_element;
|- !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x: thm
*)

(* ------------------------------------------------------------------------- *)
(* Target size and orbit size.                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For action f g X, all a in G are reachable, belong to some orbit,
            (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x). *)
(* Proof:
   This should follow from the fact that reach induces a partition, and
   the partition elements are orbits (orbit_is_orbits_element).

   By action_def, orbit_def, SURJ_DEF, this is to show:
   (1) x IN X /\ a IN G ==> ?b. f a x = f b x /\ b IN G
       True by taking b = a.
   (2) x IN X /\ a IN G ==> ?b. b IN G /\ f b x = f a x
       True by taking b = a.
*)
Theorem action_to_orbit_surj:
  !f g X x. (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x)
Proof
  rw[action_def, orbit_def, SURJ_DEF] >> metis_tac[]
QED

(* Theorem: If (\a. f a x) is INJ into orbit for action,
            then orbit is same size as the group.
            (g act X) f /\ FINITE X /\ x IN X /\
            INJ (\a. f a x) G (orbit f g x) ==> CARD (orbit f g x) = CARD G *)
(* Proof:
   Note SURJ (\a. f a x) G (orbit f g x)     by action_to_orbit_surj
   With INJ (\a. f a x) G (orbit f g x)      by given
    ==> BIJ (\a. f a x) G (orbit f g x)      by BIJ_DEF
    Now (orbit f g x) SUBSET X               by orbit_subset_target
     so FINITE (orbit f g x)                 by SUBSET_FINITE, FINITE X
    ==> FINITE G                             by FINITE_INJ
   Thus CARD (orbit f g x) = CARD G          by FINITE_BIJ_CARD_EQ
*)
Theorem orbit_finite_inj_card_eq:
  !f g X x. (g act X) f /\ x IN X /\ FINITE X /\
            INJ (\a. f a x) G (orbit f g x) ==> CARD (orbit f g x) = CARD G
Proof
  metis_tac[action_to_orbit_surj, BIJ_DEF,
            orbit_subset_target, SUBSET_FINITE, FINITE_INJ, FINITE_BIJ_CARD_EQ]
QED

(* Theorem: For FINITE X, CARD X = SUM of CARD partitions in (orbits f g X).
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD X = SIGMA CARD (orbits f g X) *)
(* Proof:
   With orbits_eq_partition, reach_equiv, apply
   partition_CARD
   |- !R s. R equiv_on s /\ FINITE s ==> CARD s = SIGMA CARD (partition R s)
*)
Theorem target_card_by_partition:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = SIGMA CARD (orbits f g X)
Proof
  metis_tac[orbits_eq_partition, reach_equiv, partition_CARD]
QED

(* Theorem: If for all x IN X, CARD (orbit f g x) = n,
            then (orbits f g X) has pieces with equal size of n.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==>
            (!e. e IN orbits f g X ==> CARD e = n) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit f g x)     by orbits_element_is_orbit
   Thus ?y. y IN e                           by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN X                               by orbits_element_element
     so CARD e = n                           by given implication.
*)
Theorem orbits_equal_size_partition_equal_size:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==>
            (!e. e IN orbits f g X ==> CARD e = n)
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all x IN X, CARD (orbit f g x) = n, then n divides CARD X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==> n divides (CARD X) *)
(* Proof:
   Let R = reach f g.
   Note !e. e IN orbits f g X ==> CARD e = n by orbits_equal_size_partition_equal_size
    and R equiv_on X                  by reach_equiv
    and orbits f g X = partition R X  by orbits_eq_partition
   Thus n divides CARD X
      = n * CARD (partition R X)      by equal_partition_card
      = CARD (partition R X) * n      by MULT_SYM
     so n divides (CARD X)            by divides_def
   The last part is simplified by:

equal_partition_factor;
|- !R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> CARD e = n) ==>
          n divides CARD s
*)
Theorem orbits_equal_size_property:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> (CARD (orbit f g x) = n)) ==> n divides (CARD X)
Proof
  rpt strip_tac >>
  imp_res_tac orbits_equal_size_partition_equal_size >>
  metis_tac[orbits_eq_partition, reach_equiv, equal_partition_factor]
QED

(* Theorem: If for all x IN X, n divides CARD (orbit f g x),
            then n divides size of elements in orbits f g X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==>
            (!e. e IN orbits f g X ==> n divides (CARD e)) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit f g x) by orbits_element_is_orbit
   Thus ?y. y IN e                       by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN X                           by orbits_element_element
     so n divides (CARD e)               by given implication.
*)
Theorem orbits_size_factor_partition_factor:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==>
            (!e. e IN orbits f g X ==> n divides (CARD e))
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all x IN X, n divides (orbit f g x), then n divides CARD X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==> n divides (CARD X) *)
(* Proof:
   Note !e. e IN orbits f g X ==> n divides (CARD e)
                                   by orbits_size_factor_partition_factor
    and reach f g equiv_on X       by reach_equiv
   Thus n divides (CARD X)         by orbits_eq_partition, factor_partition_card
*)
Theorem orbits_size_factor_property:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==> n divides (CARD X)
Proof
  metis_tac[orbits_size_factor_partition_factor,
            orbits_eq_partition, reach_equiv, factor_partition_card]
QED

(* ------------------------------------------------------------------------- *)
(* Stabilizer as invariant.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stabilizer of action: for x IN X, the group elements that fixes x. *)
val stabilizer_def = zDefine`
    stabilizer f (g:'a group) (x:'b) = {a | a IN G /\ f a x = x }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> stabilizer_def |> ISPEC ``$o``;
val it = |- !g' x. stabilizer $o g' x = {a | a IN G'.carrier /\ a o x = x}: thm
*)

(* Theorem: a IN stabilizer f g x ==> a IN G /\ f a x = x *)
(* Proof: by stabilizer_def *)
Theorem stabilizer_element:
  !f g x a. a IN stabilizer f g x <=> a IN G /\ f a x = x
Proof
  simp[stabilizer_def]
QED

(* Theorem: The (stabilizer f g x) is a subset of G. *)
(* Proof: by stabilizer_element, SUBSET_DEF *)
Theorem stabilizer_subset:
  !f g x. (stabilizer f g x) SUBSET G
Proof
  simp[stabilizer_element, SUBSET_DEF]
QED

(* Theorem: (stabilizer f g x) has #e.
            Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x *)
(* Proof:
   Note #e IN G                   by group_id_element
    and f #e x = x                by action_id
     so #e IN stabilizer f g x    by stabilizer_element
*)
Theorem stabilizer_has_id:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x
Proof
  metis_tac[stabilizer_element, action_id, group_id_element]
QED
(* This means (stabilizer f g x) is non-empty *)

(* Theorem: (stabilizer f g x) is nonempty.
            Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> EMPTY *)
(* Proof: by stabilizer_has_id, MEMBER_NOT_EMPTY. *)
Theorem stabilizer_nonempty:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> EMPTY
Proof
  metis_tac[stabilizer_has_id, MEMBER_NOT_EMPTY]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X ==>
            stabilizer f g x = IMAGE (\a. if f a x = x then a else #e) G *)
(* Proof:
   By stabilizer_def, EXTENSION, this is to show:
   (1) a IN G /\ f a x = x ==> ?b. a = (if f b x = x then b else #e) /\ b IN G
       This is true by taking b = a.
   (2) a IN G ==> (if f a x = x then a else #e) IN G, true   by group_id_element
   (3) f (if f a x = x then a else #e) x = x, true           by action_id
*)
Theorem stabilizer_as_image:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            stabilizer f g x = IMAGE (\a. if f a x = x then a else #e) G
Proof
  (rw[stabilizer_def, EXTENSION] >> metis_tac[group_id_element, action_id])
QED

(* ------------------------------------------------------------------------- *)
(* Application:                                                              *)
(* Stabilizer subgroup.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the stabilizer group, the restriction of group G to stabilizer. *)
Definition StabilizerGroup_def:
    StabilizerGroup f (g:'a group) (x:'b) =
      <| carrier := stabilizer f g x;
              op := g.op;
              id := #e
       |>
End

(* Theorem: StabilizerGroup properties. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_property:
  !f g x. (StabilizerGroup f g x).carrier = stabilizer f g x /\
          (StabilizerGroup f g x).op = g.op /\
          (StabilizerGroup f g x).id = #e
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup carrier. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_carrier:
  !f g x. (StabilizerGroup f g x).carrier = stabilizer f g x
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup identity. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_id:
  !f g x. (StabilizerGroup f g x).id = g.id
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: If g is a Group, f g X is an action, StabilizerGroup f g x is a Group.
            Group g /\ (g act X) f /\ x IN X ==> Group (StabilizerGroup f g x) *)
(* Proof:
   By group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, this is to show:
   (1) a IN G /\ b IN G /\ f a x = x /\ f b x = x ==> f (a * b) x = x
         f (a * b) x
       = f a (f b x)         by action_compose
       = f a x               by f b x = x
       = a                   by f a x = x
   (2) a IN G /\ f a x = x ==> ?b. b IN G /\ f b x = x /\ b * a = #e
       Let b = |/ a.
       Then b * a = #e       by group_linv
         f ( |/x) a
       = f ( |/x) (f a x)    by f a x = x
       = f ( |/x * x) a      by action_def
       = f (#e) a            by group_linv
       = a                   by action_def
*)
Theorem stabilizer_group_group:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> Group (StabilizerGroup f g x)
Proof
  rw_tac std_ss[group_def_alt, StabilizerGroup_def, stabilizer_def,
                action_def, GSPECIFICATION] >> prove_tac[]
QED

(* Theorem: If g is Group, f g X is an action, then StabilizerGroup f g x is a subgroup of g.
            Group g /\ (g act X) f /\ x IN X ==> (StabilizerGroup f g x) <= g *)
(* Proof:
   By Subgroup_def, stabilizer_group_property, this is to show:
   (1) x IN X ==> Group (StabilizerGroup f g x), true by stabilizer_group_group
   (2) stabilizer f g x SUBSET G, true                by stabilizer_subset
*)
Theorem stabilizer_group_subgroup:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> (StabilizerGroup f g x) <= g
Proof
  metis_tac[Subgroup_def, stabilizer_group_property, stabilizer_group_group, stabilizer_subset]
QED

(* Theorem: If g is FINITE Group, StabilizerGroup f g x is a FINITE Group.
            FiniteGroup g /\ (g act X) f /\ x IN X ==> FiniteGroup (StabilizerGroup f g x) *)
(* Proof:
   By FiniteGroup_def, stabilizer_group_property, this is to show:
   (1) x IN X ==> Group (StabilizerGroup f g x), true          by stabilizer_group_group
   (2) FINITE G /\ x IN X ==> FINITE (stabilizer f g x), true  by stabilizer_SUBSET, SUBSET_FINITE
*)
Theorem stabilizer_group_finite_group:
  !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
            FiniteGroup (StabilizerGroup f g x)
Proof
  rw_tac std_ss[FiniteGroup_def, stabilizer_group_property] >-
  metis_tac[stabilizer_group_group] >>
  metis_tac[stabilizer_subset, SUBSET_FINITE]
QED

(* Theorem: If g is FINITE Group, CARD (stabilizer f g x) divides CARD G.
            FiniteGroup g /\ (g act X) f /\ x IN X ==>
            CARD (stabilizer f g x) divides (CARD G) *)
(* Proof:
   By Lagrange's Theorem, and (StabilizerGroup f g x) is a subgroup of g.

   Note (StabilizerGroup f g x) <= g                         by stabilizer_group_subgroup
    and (StabilizerGroup f g x).carrier = stabilizer f g x   by stabilizer_group_property
    but (stabilizer f g x) SUBSET G                          by stabilizer_subset
  Thus CARD (stabilizer f g x) divides (CARD G)              by Lagrange_thm
*)
Theorem stabilizer_group_card_divides:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                       CARD (stabilizer f g x) divides (CARD G)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `(StabilizerGroup f g x) <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  metis_tac[stabilizer_subset, Lagrange_thm]
QED

(* ------------------------------------------------------------------------- *)
(* Orbit-Stabilizer Theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The map from orbit to coset of stabilizer is well-defined.
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                  a * (stabilizer f g x) = b * (stabilizer f g x) *)
(* Proof:
   Note StabilizerGroup f g x <= g         by stabilizer_group_subgroup
    and (StabilizerGroup f g x).carrier
      = stabilizer f g x                   by stabilizer_group_property
   By subgroup_coset_eq, this is to show:
      ( |/b * a) IN (stabilizer f g x)

   Note ( |/b * a) IN G        by group_inv_element, group_op_element
        f ( |/b * a) x
      = f ( |/b) (f a x)       by action_compose
      = f ( |/b) (f b x)       by given
      = f ( |/b * b) x         by action_compose
      = f #e x                 by group_linv
      = x                      by action_id
   Hence  ( |/b * a) IN (stabilizer f g x)
                               by stabilizer_element
*)
Theorem orbit_stabilizer_map_good:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                  a * (stabilizer f g x) = b * (stabilizer f g x)
Proof
  rpt strip_tac >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  fs[action_def] >>
  `( |/b * a) IN (stabilizer f g x)` suffices_by metis_tac[subgroup_coset_eq] >>
  `f ( |/b * a) x = f ( |/b) (f a x)` by rw[action_compose] >>
  `_ = f ( |/b) (f b x)` by asm_rewrite_tac[] >>
  `_ = f ( |/b * b) x` by rw[] >>
  `_ = f #e x` by rw[] >>
  `_ = x` by rw[] >>
  rw[stabilizer_element]
QED

(* Theorem: The map from orbit to coset of stabilizer is injective.
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\
                  a * (stabilizer f g x) = b * (stabilizer f g x) ==> f a x = f b x *)
(* Proof:
   Note a * (stabilizer f g x) = b * (stabilizer f g x)
    ==> ( |/b * a) IN (stabilizer f g x)   by subgroup_coset_eq
    ==> f ( |/b * a) x = x                 by stabilizer_element
       f a x
     = f (#e * x) a            by group_lid
     = f ((b * |/ b) * a) x    by group_rinv
     = f (b * ( |/b * a)) x    by group_assoc
     = f b (f ( |/b * a) x)    by action_compose
     = f b x                   by above, x = f ( |/b * a) x
*)
Theorem orbit_stabilizer_map_inj:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\
                  a * (stabilizer f g x) = b * (stabilizer f g x) ==>
                  f a x = f b x
Proof
  rpt strip_tac >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  `( |/b * a) IN (stabilizer f g x)` by metis_tac[subgroup_coset_eq] >>
  `f ( |/b * a) x = x` by fs[stabilizer_element] >>
  `|/b * a IN G` by rw[] >>
  `f a x = f (#e * a) x` by rw[] >>
  `_ = f ((b * |/ b) * a) x` by rw_tac std_ss[group_rinv] >>
  `_ = f (b * ( |/ b * a)) x` by rw[group_assoc] >>
  `_ = f b (f ( |/ b * a) x)` by metis_tac[action_compose] >>
  metis_tac[]
QED

(* Theorem: For action f g X /\ x IN X,
            if x, y IN G, f a x = f b x <=> 1/a * b IN (stabilizer f g x).
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G ==>
                 (f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x))  *)
(* Proof:
   If part: f a x = f b x ==> ( |/ a * b) IN (stabilizer f g x)
      Let y = f b x, so f a x = y.
      then y IN X                   by action_closure
       and f ( |/ a) y = x          by action_reverse [1]
      Note |/ a IN G                by group_inv_element
       and |/ a * b IN G            by group_op_element
           f ( |/ a * b) x
         = f ( |/ a) (f b x)        by action_compose
         = x                        by [1] above
      Thus ( |/ a * b) IN (stabilizer f g x)
                                    by stabilizer_element
   Only-if part: ( |/ a * b) IN (stabilizer f g x) ==> f a x = f b x
      Note ( |/ a * b) IN G /\
           f ( |/ a * b) x = x      by stabilizer_element
           f a x
         = f a (f ( |/a * b) x)     by above
         = f (a * ( |/ a * b)) x    by action_compose
         = f ((a * |/ a) * b) x     by group_assoc, group_inv_element
         = f (#e * b) x             by group_rinv
         = f b x                    by group_lid
*)
Theorem action_match_condition:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G ==>
                  (f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x))
Proof
  rw[EQ_IMP_THM] >| [
    `|/ a IN G /\ |/ a * b IN G` by rw[] >>
    `f ( |/ a * b) x = f ( |/ a) (f b x)` by metis_tac[action_compose] >>
    `_ = x` by metis_tac[action_closure, action_reverse] >>
    rw[stabilizer_element],
    `( |/ a * b) IN G /\ f ( |/ a * b) x = x` by metis_tac[stabilizer_element] >>
    `f a x = f a (f ( |/a * b) x)` by rw[] >>
    `_ = f (a * ( |/ a * b)) x` by metis_tac[action_compose] >>
    `_ = f ((a * |/ a) * b) x` by rw[group_assoc] >>
    rw[]
  ]
QED

(* Alternative form of the same theorem. *)
Theorem action_match_condition_alt:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b::G. f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x)
Proof
  metis_tac[action_match_condition]
QED

(* Theorem: stabilizers of points in same orbit:
            a * (stabilizer f g x) * 1/a = stabilizer f g (f a x).
            Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
            conjugate g a (stabilizer f g x) = stabilizer f g (f a x) *)
(* Proof:
   In Section 1.12 of Volume I of [Jacobson] N.Jacobson, Basic Algebra, 1980.
   [Artin] E. Artin, Galois Theory 1942.

   By conjugate_def, stabilizer_def, this is to show:
   (1) z IN G /\ f z x = x ==> a * z * |/ a IN G
       Note |/ a   IN G                  by group_inv_element
       Thus a * z * |/ a IN G            by group_op_element
   (2) z IN G /\ f z x = x ==> f (a * z * |/ a) (f a x) = f a x
       Note a * z * |/ a IN G            by group_inv_element
         f (a * z * |/ a) (f a x)
       = f (a * z * |/ a * a) x          by action_compose
       = f ((a * z) * ( |/ a * a)) x     by group_assoc
       = f ((a * z) * #e) x              by group_linv
       = f (a * z) x                     by group_rid
       = f a (f z x)                     by action_compose
       = f a x                           by x = f z x
   (3) b IN G /\ f b (f a x) = f a x ==> ?z. b = a * z * |/ a /\ z IN G /\ f z x = x
       Let z = |/ a * b * a.
       Note |/ a IN G                    by group_inv_element
         so z IN G                       by group_op_element
         a * z * |/ a
       = a * ( |/ a * b * a) * |/ a      by notation
       = (a * ( |/ a)) * b * a * |/ a    by group_assoc
       = (a * ( |/ a)) * (b * a * |/ a)  by group_assoc
       = (a * |/ a) * b * (a * |/ a)     by group_assoc
       = #e * b * #e                     by group_rinv
       = b                               by group_lid, group_rid
         f z x
       = f ( |/ a * b * a) x             by notation
       = f ( |/ a * (b * a)) x           by group_assoc
       = f ( |/ a) (f (b * a) x)         by action_compose
       = f ( |/ a) (f b (f a x))         by action_compose
       = f ( |/ a) (f a x)               by given f b (f a x) = f a x
       = f ( |/ a * a) x                 by action_compose
       = f #e x                          by group_linv
       = x                               by action_id
*)
Theorem stabilizer_conjugate:
  !f g X x a. Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
              conjugate g a (stabilizer f g x) = stabilizer f g (f a x)
Proof
  rw[conjugate_def, stabilizer_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >-
 (`a * z * |/ a IN G` by rw[] >>
  `f (a * z * |/ a) (f a x) = f (a * z * |/ a * a) x` by metis_tac[action_compose] >>
  `_ = f ((a * z) * ( |/ a * a)) x` by rw[group_assoc] >>
  `_ = f (a * z) x` by rw[] >>
  metis_tac[action_compose]) >>
  qexists_tac `|/a * x' * a` >>
  rw[] >| [
    `a * ( |/ a * x' * a) * |/ a = (a * |/ a) * x' * (a * |/ a)` by rw[group_assoc] >>
    rw[],
    `|/ a IN G /\ x' * a IN G` by rw[] >>
    `f ( |/ a * x' * a) x = f ( |/ a * (x' * a)) x` by rw[group_assoc] >>
    metis_tac[action_compose, group_linv, action_id]
  ]
QED

(* This is a major result. *)

(* Extract the existence element of reach *)
(* - reach_def;
> val it = |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = y:  thm
*)

(* Existence of act_by: the x in reach f g X b, such that a IN G /\ f a x = b. *)
val lemma = prove(
  ``!f (g:'a group) (x:'b) (y:'b). ?a. reach f g x y ==> a IN G /\ f a x = y``,
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
             THENC BINDER_CONV (RENAME_VARS_CONV ["f", "g", "x", "y"])));
(*
val act_by_def = |- !f g x y.
          (x ~~ y) f g ==> act_by f g x y IN G /\ f (act_by f g x y) x = y: thm
*)

(* Theorem: The reachable set from a to b is the coset act_by b of (stabilizer a).
            Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
            (act_by f g x y) * (stabilizer f g x) = {a | a IN G /\ f a x = y} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) z IN stabilizer f g x ==> act_by f g x y * z IN G
       Note act_by f g x y IN G          by act_by_def
        and z IN G                       by stabilizer_element
         so act_by f g x y * z IN G      by group_op_element
   (2) z IN stabilizer f g x ==> f (act_by f g x y * z) x = y
       Note act_by f g x y IN G          by act_by_def
        and z IN G                       by stabilizer_element
         f (act_by f g x y * z) x
       = f (act_by f g x y) (f z x)      by action_compose
       = f (act_by f g x y) x            by stabilizer_element
       = y                               by act_by_def
   (3) (x ~~ f a x) f g /\ a IN G ==> ?z. a = act_by f g x (f a x) * z /\ z IN stabilizer f g x
       Let b = act_by f g x (f a x)
       Then b IN G /\ (f b x = f a x)       by act_by_def
        and |/ b * a IN (stabilizer f g x)  by action_match_condition
        Let z = |/ b * a, to show: a = b * z.
           b * z
         = b * ( |/ b * a)        by notation
         = (b * |/ b) * a         by group_assoc
         = #e * a                 by group_rinv
         = a                      by group_lid
*)
Theorem action_reachable_coset:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
              (act_by f g x y) * (stabilizer f g x) = {a | a IN G /\ f a x = y}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[act_by_def, stabilizer_element, group_op_element] >-
  metis_tac[act_by_def, action_compose, stabilizer_element] >>
  qabbrev_tac `b = act_by f g x (f x' x)` >>
  `b IN G /\ (f b x = f x' x)` by rw[act_by_def, Abbr`b`] >>
  `|/ b * x' IN (stabilizer f g x)` by metis_tac[action_match_condition] >>
  qexists_tac `|/ b * x'` >>
  `b * ( |/ b * x') = (b * |/ b) * x'` by rw[group_assoc] >>
  `_ = x'` by rw[] >>
  rw[]
QED

(* Another formulation of the same result. *)

(* Theorem: The reachable set from x to y is the coset act_by y of (stabilizer x).
            Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
            !a. a IN G /\ f a x = y ==>
                a * (stabilizer f g x) = {b | b IN G /\ f b x = y} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) z IN stabilizer f g x ==> a * z IN G
       Note z IN G            by stabilizer_element
         so a * z IN G        by group_op_element
   (2) z IN stabilizer f g x ==> f (a * z) x = f a x
       Note f z x = x         by stabilizer_element
         f (a * z) x
       = f a (f z x)          by action_compose
       = f a x                by above
   (3) b IN G /\ f a x = f b a ==> ?z. b = a * z /\ z IN stabilizer f g x
       Let z = |/ a * b.
         a * z
       = a * ( |/ a * b)      by notation
       = (a * |/ a) * b       by group_assoc
       = #e * b               by group_rinv
       = b                    by group_lid
       Hence z IN stabilizer f g x,
                              by action_match_condition, f a x = f b x
*)
Theorem action_reachable_coset_alt:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
              !a. a IN G /\ f a x = y ==>
                  a * (stabilizer f g x) = {b | b IN G /\ f b x = y}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stabilizer_element, group_op_element] >-
  metis_tac[stabilizer_element, action_compose] >>
  qexists_tac `|/ a * x'` >>
  rpt strip_tac >-
  rw[GSYM group_assoc] >>
  metis_tac[action_match_condition]
QED

(* Theorem: Elements of (orbit a) and cosets of (stabilizer a) are one-to-one.
            Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                {a * (stabilizer f g x) | a IN G} *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit f g x ==> ?a. (act_by f g x y * stabilizer f g x = a * stabilizer f g x) /\ a IN G
       Take a = act_by f g x y.
       Note (x ~~ y) f g         by orbit_element, y IN orbit f g x
       Thus a IN G               by act_by_def
   (2) y IN orbit f g x /\ z IN orbit f g x /\
       act_by f g x y * stabilizer f g x = act_by f g x z * stabilizer f g x ==> y = z
       Note (x ~~ y) f g /\ (x ~~ z) f g                 by orbit_element
        and act_by f g x y IN G /\ act_by f g x z IN G   by act_by_def
       Thus y
          = f (act_by f g x y) x        by act_by_def
          = f (act_by f g x z) x        by orbit_stabilizer_map_inj
          = z                           by act_by_def
   (3) same as (1)
   (4) a IN G ==> ?y. y IN orbit f g x /\ (act_by f g x y * stabilizer f g x = a * stabilizer f g x)
       Take y = f a x.
       Then (x ~~ y) f g                by reach_def
        and y IN X                      by action_closure
         so y IN orbit f g x            by orbit_element
       Let b = act_by f g x y.
       Then f a x = y = f b x           by act_by_def
        ==> a * stabilizer f g x = b * stabilizer f g x
                                        by orbit_stabilizer_map_good
*)
Theorem orbit_stabilizer_cosets_bij:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                {a * (stabilizer f g x) | a IN G}
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
  metis_tac[orbit_element, act_by_def] >-
  metis_tac[orbit_stabilizer_map_inj, orbit_element, act_by_def] >-
  metis_tac[orbit_element, act_by_def] >>
  qexists_tac `f a x` >>
  rpt strip_tac >-
  metis_tac[orbit_element, reach_def, action_closure] >>
  `(x ~~ (f a x)) f g` by metis_tac[reach_def] >>
  metis_tac[orbit_stabilizer_map_good, act_by_def]
QED

(* The above version is not using CosetPartition. *)

(* Theorem: Elements of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                (CosetPartition g (StabilizerGroup f g x) *)
(* Proof:
   By CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit f g x ==>
          ?a. a IN G /\ (act_by f g x y * stabilizer f g x = {b | b IN G /\ b IN a * stabilizer f g x})
       Let c = act_by f g x y, and put a = c.
       Note (x ~~ y) f g        by orbit_element
        and c IN G              by act_by_def,
       By coset_def, EXTENSION, this is to show:
          (?z. a = c * z /\ z IN stabilizer f g x) <=>
          a IN G /\ ?z. a = c * z /\ z IN stabilizer f g x
       Need to show: c * z IN G.
       Now z IN G               by stabilizer_element
       Thus c * z IN G          by group_op_element
   (2) y IN orbit f g x /\ z IN orbit f g x /\
         act_by f g x y * stabilizer f g x = act_by f g x z * stabilizer f g x ==> y = z
       Note (x ~~ y) f g /\ (x ~~ z) f g                  by orbit_element
        and act_by f g x y IN G /\ act_by f g x z IN G    by act_by_def
        ==> f (act_by f g x y) x = f (act_by f g x z) x   by orbit_stabilizer_map_inj
         so y = z                                         by act_by_def
   (3) same as (1)
   (4) a IN G /\ s = {y | y IN G /\ y IN a * stabilizer f g x} ==>
         ?y. y IN orbit f g x /\ (act_by f g x y * stabilizer f g x = s)
       Let y = f a x.
       Note (x ~~ y) f g             by reach_def
        and act_by f g x y IN G /\ (f (act_by f g x y) x = f a x)  by act_by_def
        ==> act_by f g x y * (stabilizer f g x)
          = a * (stabilizer f g x)   by orbit_stabilizer_map_good
      By EXTENSION, this is to show:
         !b. b IN a * stabilizer f g x ==> b IN G
      Note b IN IMAGE (\z. a * z) (stabilizer f g x)     by coset_def
      Thus ?z. z IN (stabilizer f g x) /\ (b = a * z)    by IN_IMAGE
       Now z IN G                                        by stabilizer_element
      Thus b = a * z IN G                                by group_op_element
*)
Theorem orbit_stabilizer_cosets_bij_alt:
  !f g X x.
     Group g /\ (g act X) f /\ x IN X ==>
     BIJ (\y. (act_by f g x y) * (stabilizer f g x))
         (orbit f g x)
         (CosetPartition g (StabilizerGroup f g x))
Proof
  simp_tac (srw_ss()) [CosetPartition_def, partition_def, inCoset_def,
                       StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt strip_tac >| [
    qabbrev_tac `z = act_by f g x y` >>
    qexists_tac `z` >>
    `(x ~~ y) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    metis_tac[orbit_element, orbit_stabilizer_map_inj, act_by_def],
    qabbrev_tac `z = act_by f g x y` >>
    qexists_tac `z` >>
    `(x ~~ y) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    rename [‘x'' ∈ G’, ‘_ ∈ a * stabilizer f g x’] >>
    qexists_tac `f a x` >>
    rpt strip_tac >- metis_tac[orbit_element, action_closure, reach_def] >>
    qabbrev_tac `y = f a x` >>
    `(x ~~ y) f g` by metis_tac[reach_def] >>
    `act_by f g x y IN G /\ (f (act_by f g x y) x = f a x)` by rw[act_by_def] >>
    `act_by f g x y * (stabilizer f g x) = a * (stabilizer f g x)`
      by metis_tac[orbit_stabilizer_map_good] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    metis_tac[coset_def, IN_IMAGE, stabilizer_element, group_op_element]
  ]
QED

(* Theorem: [Orbit-Stabilizer Theorem]
            FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
            CARD G = CARD (orbit f g x) * CARD (stabilizer f g x) *)
(* Proof:
   Let h = StabilizerGroup f g x
   Then h <= g                          by stabilizer_group_subgroup
    and H = stabilizer f g x            by stabilizer_group_property
   Note CosetPartition g h = partition (inCoset g h) G  by CosetPartition_def
     so FINITE (CosetPartition g h)     by FINITE_partition
   Note FINITE_partition = IMAGE (\a. f a x) G  by orbit_def
     so FINITE (orbit f g x)            by IMAGE_FINITE

     CARD G
   = CARD H * CARD (CosetPartition g h)            by Lagrange_identity, h <= g
   = CARD (stabilizer f g x) * CARD (orbit f g x)  by orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ
   = CARD (orbit f g x) * CARD (stabilizer f g x)  by MULT_COMM
*)
Theorem orbit_stabilizer_thm:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                       CARD G = CARD (orbit f g x) * CARD (stabilizer f g x)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  `FINITE (CosetPartition g (StabilizerGroup f g x))` by metis_tac[CosetPartition_def, FINITE_partition] >>
  `FINITE (orbit f g x)` by rw[orbit_def] >>
  `CARD G = CARD (stabilizer f g x) * CARD (CosetPartition g (StabilizerGroup f g x))` by metis_tac[Lagrange_identity] >>
  `_ = CARD (stabilizer f g x) * CARD (orbit f g x)` by metis_tac[orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ] >>
  rw[]
QED

(* This is a major milestone! *)

(* Theorem: FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
            CARD (orbit f g x) divides CARD G *)
(* Proof:
   Let b = orbit f g x,
       c = stabilizer f g x.
   Note CARD G = CARD b * CARD c         by orbit_stabilizer_thm
   Thus (CARD b) divides (CARD G)        by divides_def
*)
Theorem orbit_card_divides_target_card:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                       CARD (orbit f g x) divides CARD G
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
to count how many singleton orbits, just count the set (fixed_points f g X).

Since orbits are equivalent classes, they cannot be empty, hence singleton
orbits are the simplest type. For equivalent classes:

CARD Target = SUM CARD (orbits)
            = SUM CARD (singleton orbits) + SUM CARD (non-singleton orbits)
            = CARD (fixed_points) + SUM CARD (non-singleton orbits)
*)

(* Fixed points of action: those points fixed by all group elements. *)
val fixed_points_def = zDefine`
   fixed_points f (g:'a group) (X:'b -> bool) =
      {x | x IN X /\ !a. a IN G ==> f a x = x }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> fixed_points_def |> ISPEC ``$o``;
|- !g' X. fixed_points $o g' X = {x | x IN X /\ !a. a IN G'.carrier ==> a o x = x}: thm
*)

(* Theorem: Fixed point elements:
            x IN (fixed_points f g X) <=> x IN X /\ !a. a IN G ==> f a x = x *)
(* Proof: by fixed_points_def. *)
Theorem fixed_points_element:
  !f g X x. x IN (fixed_points f g X) <=> x IN X /\ !a. a IN G ==> f a x = x
Proof
  simp[fixed_points_def]
QED

(* Theorem: Fixed points are subsets of target set.
            (fixed_points f g X) SUBSET X *)
(* Proof: by fixed_points_def, SUBSET_DEF. *)
Theorem fixed_points_subset:
  !f g X. (fixed_points f g X) SUBSET X
Proof
  simp[fixed_points_def, SUBSET_DEF]
QED

(* Theorem: Fixed points are finite.
            FINITE X ==> FINITE (fixed_points f g X) *)
(* Proof: by fixed_points_subset, SUBSET_FINITE. *)
Theorem fixed_points_finite:
  !f g X. FINITE X ==> FINITE (fixed_points f g X)
Proof
  metis_tac[fixed_points_subset, SUBSET_FINITE]
QED

(* Theorem: x IN fixed_points f g X ==> x IN X *)
(* Proof: by fixed_points_def *)
Theorem fixed_points_element_element:
  !f g X x. x IN fixed_points f g X ==> x IN X
Proof
  simp[fixed_points_def]
QED

(* Fixed Points have singleton orbits, or those with stabilizer = whole group. *)

(* Theorem: Group g /\ (g act X) f ==>
            !x. x IN fixed_points f g X <=> x IN X /\ orbit f g x = {x} *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to show:
   (1) a IN G /\ (!a. a IN G ==> f a x = x) ==> f a x = x
       This is true                by the included implication
   (2) (!a. a IN G ==> f a x = x) ==> ?a. a IN G /\ x = f a x
       Take a = #e,
       Then a IN G                 by group_id_element
        and f a x = x              by implication
   (3) (g act X) f /\ a IN G ==> f a x = x
       This is true                by action_closure
*)
Theorem fixed_points_orbit_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN fixed_points f g X <=>
             x IN X /\ orbit f g x = {x}
Proof
  rw[fixed_points_def, orbit_def, EXTENSION, EQ_IMP_THM] >-
  rw_tac std_ss[] >-
  metis_tac[group_id_element] >>
  metis_tac[action_closure]
QED

(* Theorem: For action f g X, x IN X, (orbit f g x = {x}) ==> x IN fixed_points f g X *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to prove:
   (g act X) f /\ x IN X /\ a IN G /\
     !x. x IN X /\ (?b. b IN G /\ (f b x = x) <=> a = b) ==> f a x = x
   This is true by action_closure.
*)
Theorem orbit_sing_fixed_points:
  !f g X. (g act X) f ==>
          !x. x IN X /\ orbit f g x = {x} ==> x IN fixed_points f g X
Proof
  rw[fixed_points_def, orbit_def, EXTENSION] >>
  metis_tac[action_closure]
QED
(* This is weaker than the previous theorem. *)

(* Theorem: Group g /\ (g act X) f ==>
           !x. x IN fixed_points f g X <=> SING (orbit f g x)) *)
(* Proof:
   By SING_DEF, this is to show:
   If part: x IN fixed_points f g X ==> ?z. (orbit f g x) = {a}
      Take z = x, then true              by fixed_points_orbit_sing
   Only-if part: (orbit f g x) = {x} ==> x IN fixed_points f g X
      Note a IN (orbit f g x)            by orbit_has_self
      Thus x = a                         by IN_SING
        so x IN fixed_points f g X       by fixed_points_orbit_sing
*)
Theorem fixed_points_orbit_iff_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN X ==> (x IN fixed_points f g X <=> SING (orbit f g x))
Proof
  metis_tac[fixed_points_orbit_sing, orbit_has_self, SING_DEF, IN_SING]
QED

(* Theorem: Group g /\ (g act X) f ==>
            !x. x IN (X DIFF fixed_points f g X) <=>
                x IN X /\ ~ SING (orbit f g x))  *)
(* Proof:
       x IN (X DIFF fixed_points f g X)
   <=> x IN X /\ x NOTIN (fixed_points f g X)  by IN_DIFF
   <=> x IN X /\ ~ SING (orbit f g x))         by fixed_points_orbit_iff_sing
*)
Theorem non_fixed_points_orbit_not_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN (X DIFF fixed_points f g X) <=>
              x IN X /\ ~ SING (orbit f g x)
Proof
  metis_tac[IN_DIFF, fixed_points_orbit_iff_sing]
QED

(* Theorem: FINITE X ==> CARD (X DIFF fixed_points f g X) =
                         CARD X - CARD (fixed_points f g X) *)
(* Proof:
   Let fp = fixed_points f g X.
   Note fp SUBSET X                by fixed_points_subset
   Thus X INTER fp = fp            by SUBSET_INTER_ABSORPTION
     CARD (X DIFF bp)
   = CARD X - CARD (X INTER fp)    by CARD_DIFF
   = CARD X - CARD fp              by SUBSET_INTER_ABSORPTION
*)
Theorem non_fixed_points_card:
  !f g X. FINITE X ==>
          CARD (X DIFF fixed_points f g X) =
          CARD X - CARD (fixed_points f g X)
Proof
  metis_tac[CARD_DIFF, fixed_points_subset,
            SUBSET_INTER_ABSORPTION, SUBSET_FINITE, INTER_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Partition of Target into single orbits and non-single orbits.             *)
(* ------------------------------------------------------------------------- *)

(* Define singleton and non-singleton orbits *)
val sing_orbits_def = zDefine`
    sing_orbits f (g:'a group) (X:'b -> bool) = { e | e IN (orbits f g X) /\ SING e }
`;
val multi_orbits_def = zDefine`
    multi_orbits f (g:'a group) (X:'b -> bool) = { e | e IN (orbits f g X) /\ ~ SING e }
`;
(* Note: use zDefine as this is not effective for computation. *)

(* Theorem: e IN sing_orbits f g X <=> e IN (orbits f g X) /\ SING e *)
(* Proof: by sing_orbits_def *)
Theorem sing_orbits_element:
  !f g X e. e IN sing_orbits f g X <=> e IN (orbits f g X) /\ SING e
Proof
  simp[sing_orbits_def]
QED

(* Theorem: (sing_orbits f g X) SUBSET (orbits f g X) *)
(* Proof: by sing_orbits_element, SUBSET_DEF *)
Theorem sing_orbits_subset:
  !f g X. (sing_orbits f g X) SUBSET (orbits f g X)
Proof
  simp[sing_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE X ==> FINITE (sing_orbits f g X) *)
(* Proof: by sing_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem sing_orbits_finite:
  !f g X. FINITE X ==> FINITE (sing_orbits f g X)
Proof
  metis_tac[sing_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act X) f, elements of (sing_orbits f g X) are subsets of X.
            (g act X) f /\ e IN (sing_orbits f g X) ==> e SUBSET X *)
(* Proof: by sing_orbits_element, orbits_element_subset *)
Theorem sing_orbits_element_subset:
  !f g X e. (g act X) f /\ e IN (sing_orbits f g X) ==> e SUBSET X
Proof
  metis_tac[sing_orbits_element, orbits_element_subset]
QED

(* Theorem: e IN (sing_orbits f g X) ==> FINITE e *)
(* Proof: by sing_orbits_element, SING_FINITE *)
Theorem sing_orbits_element_finite:
  !f g X e. e IN (sing_orbits f g X) ==> FINITE e
Proof
  simp[sing_orbits_element, SING_FINITE]
QED

(* Theorem: e IN (sing_orbits f g X) ==> CARD e = 1 *)
(* Proof: by sing_orbits_element, SING_DEF, CARD_SING *)
Theorem sing_orbits_element_card:
  !f g X e. e IN (sing_orbits f g X) ==> CARD e = 1
Proof
  metis_tac[sing_orbits_element, SING_DEF, CARD_SING]
QED

(* Theorem: Group g /\ (g act X) f ==>
            !e. e IN (sing_orbits f g X) ==> CHOICE e IN fixed_points f g X *)
(* Proof:
   Note e IN orbits f g X /\ SING e  by sing_orbits_element
   Thus ?x. e = {x}                  by SING_DEF
    ==> x IN e /\ (CHOICE e = x)     by IN_SING, CHOICE_SING
     so e = orbit f g x              by orbits_element_is_orbit, x IN e
    and x IN X                       by orbits_element_element
    ==> x IN fixed_points f g X      by orbit_sing_fixed_points
*)
Theorem sing_orbits_element_choice:
  !f g X. Group g /\ (g act X) f ==>
          !e. e IN (sing_orbits f g X) ==> CHOICE e IN fixed_points f g X
Proof
  rw[sing_orbits_element] >>
  `?x. e = {x}` by rw[GSYM SING_DEF] >>
  `x IN e /\ CHOICE e = x` by rw[] >>
  `e = orbit f g x` by metis_tac[orbits_element_is_orbit] >>
  metis_tac[orbit_sing_fixed_points, orbits_element_element]
QED

(* Theorem: e IN multi_orbits f g X <=> e IN (orbits f g X) /\ ~SING e *)
(* Proof: by multi_orbits_def *)
Theorem multi_orbits_element:
  !f g X e. e IN multi_orbits f g X <=> e IN (orbits f g X) /\ ~SING e
Proof
  simp[multi_orbits_def]
QED

(* Theorem: (multi_orbits f g X) SUBSET (orbits f g X) *)
(* Proof: by multi_orbits_element, SUBSET_DEF *)
Theorem multi_orbits_subset:
  !f g X. (multi_orbits f g X) SUBSET (orbits f g X)
Proof
  simp[multi_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE X ==> FINITE (multi_orbits f g X) *)
(* Proof: by multi_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem multi_orbits_finite:
  !f g X. FINITE X ==> FINITE (multi_orbits f g X)
Proof
  metis_tac[multi_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act X) f, elements of (multi_orbits f g X) are subsets of X.
            (g act X) f /\ e IN (multi_orbits f g X) ==> e SUBSET X *)
(* Proof: by multi_orbits_element, orbits_element_subset *)
Theorem multi_orbits_element_subset:
  !f g X e. (g act X) f /\ e IN (multi_orbits f g X) ==> e SUBSET X
Proof
  metis_tac[multi_orbits_element, orbits_element_subset]
QED

(* Theorem: (g act X) f /\ e IN (multi_orbits f g X) ==> FINITE e *)
(* Proof: by multi_orbits_element, orbits_element_finite *)
Theorem multi_orbits_element_finite:
  !f g X e. (g act X) f /\ FINITE X /\ e IN (multi_orbits f g X) ==> FINITE e
Proof
  metis_tac[multi_orbits_element, orbits_element_finite]
QED

(* Theorem: sing_orbits and multi_orbits are disjoint.
            DISJOINT (sing_orbits f g X) (multi_orbits f g X) *)
(* Proof: by sing_orbits_def, multi_orbits_def, DISJOINT_DEF. *)
Theorem target_orbits_disjoint:
  !f g X. DISJOINT (sing_orbits f g X) (multi_orbits f g X)
Proof
  rw[sing_orbits_def, multi_orbits_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: orbits = sing_orbits + multi_orbits.
            orbits f g X = (sing_orbits f g X) UNION (multi_orbits f g X) *)
(* Proof: by sing_orbits_def, multi_orbits_def. *)
Theorem target_orbits_union:
  !f g X. orbits f g X = (sing_orbits f g X) UNION (multi_orbits f g X)
Proof
  rw[sing_orbits_def, multi_orbits_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: For (g act X) f, CARD X = CARD sing_orbits + SIGMA CARD multi_orbits.
            Group g /\ (g act X) f /\ FINITE X ==>
            (CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X)) *)
(* Proof:
   Let s = sing_orbits f g X, t = multi_orbits f g X.
   Note FINITE s                   by sing_orbits_finite
    and FINITE t                   by multi_orbits_finite
   also s INTER t = {}             by target_orbits_disjoint, DISJOINT_DEF

     CARD X
   = SIGMA CARD (orbits f g X)     by target_card_by_partition
   = SIGMA CARD (s UNION t)        by target_orbits_union
   = SIGMA CARD s + SIGMA CARD t   by SUM_IMAGE_UNION, SUM_IMAGE_EMPTY
   = 1 * CARD s + SIGMA CARD t     by sing_orbits_element_card, SIGMA_CARD_CONSTANT
   = CARD s + SIGMA CARD t         by MULT_LEFT_1
*)
Theorem target_card_by_orbit_types:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = sing_orbits f g X` >>
  qabbrev_tac `t = multi_orbits f g X` >>
  `FINITE s` by rw[sing_orbits_finite, Abbr`s`] >>
  `FINITE t` by rw[multi_orbits_finite, Abbr`t`] >>
  `s INTER t = {}` by rw[target_orbits_disjoint, GSYM DISJOINT_DEF, Abbr`s`, Abbr`t`] >>
  `CARD X = SIGMA CARD (orbits f g X)` by rw_tac std_ss[target_card_by_partition] >>
  `_ = SIGMA CARD (s UNION t)` by rw_tac std_ss[target_orbits_union] >>
  `_ = SIGMA CARD s + SIGMA CARD t` by rw[SUM_IMAGE_UNION, SUM_IMAGE_EMPTY] >>
  `_ = 1 * CARD s + SIGMA CARD t` by metis_tac[sing_orbits_element_card, SIGMA_CARD_CONSTANT] >>
  rw[]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is injective.
            Group g /\ (g act X) f ==>
            INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
       This is true                    by sing_orbits_element_choice
   (2) e IN sing_orbits f g X /\ e' IN sing_orbits f g X /\ CHOICE e = CHOICE e' ==> e = e'
       Note SING e /\ SING e'          by sing_orbits_element
       Thus this is true               by SING_DEF, CHOICE_SING.
*)
Theorem sing_orbits_to_fixed_points_inj:
  !f g X. Group g /\ (g act X) f ==>
          INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  rw[INJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  metis_tac[sing_orbits_element, SING_DEF, CHOICE_SING]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is surjective.
            Group g /\ (g act X) f ==>
            SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
       This is true                      by sing_orbits_element_choice
   (2) x IN fixed_points f g X ==> ?e. e IN sing_orbits f g X /\ (CHOICE e = x)
       Note x IN X                       by fixed_points_element
        and orbit f g x = {x}            by fixed_points_orbit_sing
       Take e = {x},
       Then CHOICE e = x                 by CHOICE_SING
        and SING e                       by SING_DEF
        and e IN orbits f g X            by orbit_is_orbits_element
        ==> e IN sing_orbits f g X       by sing_orbits_element
*)
Theorem sing_orbits_to_fixed_points_surj:
  !f g X. Group g /\ (g act X) f ==>
          SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  rw[SURJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  `x IN X` by metis_tac[fixed_points_element] >>
  `orbit f g x = {x}` by metis_tac[fixed_points_orbit_sing] >>
  qexists_tac `{x}` >>
  simp[sing_orbits_element] >>
  metis_tac[orbit_is_orbits_element]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is bijective.
            Group g /\ (g act X) f ==>
            BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By sing_orbits_to_fixed_points_inj,
      sing_orbits_to_fixed_points_surj, BIJ_DEF.
   True since the map is shown to be both injective and surjective.
*)
Theorem sing_orbits_to_fixed_points_bij:
  !f g X. Group g /\ (g act X) f ==>
          BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  simp[BIJ_DEF, sing_orbits_to_fixed_points_surj,
                sing_orbits_to_fixed_points_inj]
QED

(* Theorem: For (g act X) f, sing_orbits is the same size as fixed_points f g X,
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD (sing_orbits f g X) = CARD (fixed_points f g X) *)
(* Proof:
   Let s = sing_orbits f g X, t = fixed_points f g X.
   Note s SUBSET (orbits f g X)    by sing_orbits_subset
    and t SUBSET X                 by fixed_points_subset
   Also FINITE s                   by orbits_finite, SUBSET_FINITE
    and FINITE t                   by SUBSET_FINITE
   With BIJ (\e. CHOICE e) s t     by sing_orbits_to_fixed_points_bij
    ==> CARD s = CARD t            by FINITE_BIJ_CARD_EQ
*)
Theorem sing_orbits_card_eqn:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD (sing_orbits f g X) = CARD (fixed_points f g X)
Proof
  rpt strip_tac >>
  `(sing_orbits f g X) SUBSET (orbits f g X)` by rw[sing_orbits_subset] >>
  `(fixed_points f g X) SUBSET X` by rw[fixed_points_subset] >>
  metis_tac[sing_orbits_to_fixed_points_bij, FINITE_BIJ_CARD_EQ, SUBSET_FINITE, orbits_finite]
QED

(* Theorem: For (g act X) f, CARD X = CARD fixed_points + SIGMA CARD multi_orbits.
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD X = CARD (fixed_points f g X) + SIGMA CARD (multi_orbits f g X) *)
(* Proof:
   Let s = sing_orbits f g X, t = multi_orbits f g X.
     CARD X
   = CARD s + SIGMA CARD t                       by target_card_by_orbit_types
   = CARD (fixed_points f g X) + SIGMA CARD t    by sing_orbits_card_eqn
*)
Theorem target_card_by_fixed_points:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = CARD (fixed_points f g X) + SIGMA CARD (multi_orbits f g X)
Proof
  metis_tac[target_card_by_orbit_types, sing_orbits_card_eqn]
QED

(* Theorem:  Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
             (!e. e IN multi_orbits f g X ==> (CARD e = n)) ==>
             (CARD X MOD n = CARD (fixed_points f g X) MOD n) *)
(* Proof:
   Let s = fixed_points f g X,
       t = multi_orbits f g X.
   Note FINITE t                         by multi_orbits_finite
       (CARD X) MOD n
     = (CARD s + SIGMA CARD t) MOD n     by target_card_by_fixed_points
     = (CARD s + n * CARD t) MOD n       by SIGMA_CARD_CONSTANT, FINITE t
     = (CARD t * n + CARD s) MOD n       by ADD_COMM, MULT_COMM
     = (CARD s) MOD n                    by MOD_TIMES
*)
Theorem target_card_and_fixed_points_congruence:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
            (!e. e IN multi_orbits f g X ==> (CARD e = n)) ==>
            CARD X MOD n = CARD (fixed_points f g X) MOD n
Proof
  rpt strip_tac >>
  imp_res_tac target_card_by_fixed_points >>
  `_ = CARD (fixed_points f g X) + n * CARD (multi_orbits f g X)`
     by rw[multi_orbits_finite, SIGMA_CARD_CONSTANT] >>
  fs[]
QED

(* This is a very useful theorem! *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
