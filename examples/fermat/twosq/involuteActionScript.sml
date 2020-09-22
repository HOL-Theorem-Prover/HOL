(* ------------------------------------------------------------------------- *)
(* Involution and Action                                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "involuteAction";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)

(* val _ = load "alphabetaTheory"; *)
open helperTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def, prime_def *)

(* val _ = load "involuteTheory"; *)
open involuteTheory;

(* val _ = load "groupInstancesTheory"; *)
open groupInstancesTheory; (* for add_mod_def *)

(* val _ = load "groupActionTheory"; *)
open groupActionTheory; (* for fixed_points_def *)


(* ------------------------------------------------------------------------- *)
(* Involution and Action Documentation                                       *)
(* ------------------------------------------------------------------------- *)
(*

   Helper Theorems:
   involute_permutes
                   |- !f A. f involute A ==> f PERMUTES A

   FUNPOW Action:
   funpow_action   |- !f A. f involute A ==> (Z2 act A) (FUNPOW f)
   funpow_reach    |- !f x y. reach (FUNPOW f) Z2 x y <=> ?a. a < 2 /\ (FUNPOW f a x = y)
   funpow_equiv    |- !f A. f involute A ==> reach (FUNPOW f) Z2 equiv_on A

   FUNPOW Orbits:
   funpow_orbits   |- !f A. orbits (FUNPOW f) Z2 A = {orbit (FUNPOW f) Z2 A x | x | x IN A}
   funpow_orbit    |- !f A x. orbit (FUNPOW f) Z2 A x = {FUNPOW f a x | a < 2}
   funpow_orbit_alt|- !f A x. orbit (FUNPOW f) Z2 A x = IMAGE (\a. FUNPOW f a x) (count 2)
   funpow_orbit_element
                   |- !f A x y. y IN orbit (FUNPOW f) Z2 A x <=> ?a. a < 2 /\ (FUNPOW f a x = y)
   funpow_orbit_in_orbits
                   |- !f A x. x IN A ==> orbit (FUNPOW f) Z2 A x IN orbits (FUNPOW f) Z2 A
   funpow_orbits_card_by_types
                   |- !f A. FINITE A /\ f involute A ==>
                           (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))
   funpow_orbits_card_eqn
                   |- !f A. FINITE A /\ f involute A ==>
                           (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))

   Involution Orbits:
   involute_orbit_element
                   |- !f A x y. f involute A /\ x IN A /\ y IN orbit (FUNPOW f) Z2 A x ==>
                                (y = x) \/ (y = f x)
   involute_orbit_has_self
                   |- !f A x. f involute A /\ x IN A ==> x IN orbit (FUNPOW f) Z2 A x
   involute_orbit_has_funpow
                   |- !f A x n. f involute A /\ x IN A /\ n < 2 ==>
                                FUNPOW f n x IN orbit (FUNPOW f) Z2 A x
   involute_orbit_has_image
                   |- !f A x. f involute A /\ x IN A ==> f x IN orbit (FUNPOW f) Z2 A x
   involute_orbit_as_image
                   |- !f A x. f involute A /\ x IN A ==>
                               (orbit (FUNPOW f) Z2 A x = IMAGE (\j. FUNPOW f j x) (count 2))
   involute_orbits_finite
                   |- !f A. FINITE A /\ f involute A ==> FINITE (orbits (FUNPOW f) Z2 A)
   involute_orbit_finite
                   |- !f A x. FINITE A /\ f involute A /\ x IN A ==>
                              FINITE (orbit (FUNPOW f) Z2 A x)
   involute_orbit_nonempty
                   |- !f A e. f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> {}
   involute_orbits_element_is_orbit
                   |- !f A e x. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\
                                x IN e ==> (e = orbit (FUNPOW f) Z2 A x)
   involute_orbits_element_element
                   |- !f A e x. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\
                                x IN e ==> x IN A
   involute_multi_orbits_finite
                   |- !f A. FINITE A /\ f involute A ==> FINITE (multi_orbits (FUNPOW f) Z2 A)

   Involution fixed points:
   involute_fixed_points
                   |- !f A x. f involute A /\ x IN fixed_points (FUNPOW f) Z2 A ==> (f x = x)
   involute_fixed_points_iff
                   |- !f A x. f involute A /\ x IN A ==>
                              (x IN fixed_points (FUNPOW f) Z2 A <=> (f x = x))
   involute_fixed_points_element_element
                   |- !f A x. x IN fixed_points (FUNPOW f) Z2 A ==> x IN A

   Involution Target Cardinality:
   involute_orbit_fixed
                   |- !f A x. f involute A /\ x IN A /\ (f x = x) ==>
                              (orbit (FUNPOW f) Z2 A x = {x})
   involute_orbit_not_fixed
                   |- !f A x. f involute A /\ x IN A /\ f x <> x ==>
                              (orbit (FUNPOW f) Z2 A x = {x; f x})
   involute_multi_orbits_element_card
                   |- !f A e. f involute A /\ e IN multi_orbits (FUNPOW f) Z2 A ==>
                              (CARD e = 2)
   involute_orbits_card_eqn
                   |- !f A. FINITE A /\ f involute A ==>
                           (CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                                     CARD (fixed_points (FUNPOW f) Z2 A))
   involute_fixed_points_both_even
                   |- !f A. FINITE A /\ f involute A ==>
                            (EVEN (CARD A) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 A)))
   involute_fixed_points_both_odd
                   |- !f A. FINITE A /\ f involute A ==>
                            (ODD (CARD A) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 A)))
   involute_two_fixed_points_both_even
                   |- !f g A. FINITE A /\ f involute A /\ g involute A ==>
                             (EVEN (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
                              EVEN (CARD (fixed_points (FUNPOW g) Z2 A)))
   involute_two_fixed_points_both_odd
                   |- !f g A. FINITE A /\ f involute A /\ g involute A ==>
                             (ODD (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
                              ODD (CARD (fixed_points (FUNPOW g) Z2 A)))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

val _ = ParseExtras.loose_equality(); (* ensure loose equality *)

(* Theorem alias *)
val involute_permutes = save_thm("involute_permutes",
    involute_bij |> SPEC ``f:'a -> 'a`` |> SPEC ``A:'a -> bool`` |> GEN_ALL);
(* val involute_permutes = |- !f A. f involute A ==> f PERMUTES A: thm *)


(* ------------------------------------------------------------------------- *)
(* FUNPOW Action                                                             *)
(* ------------------------------------------------------------------------- *)

(* Overload (ZN n).sum, which is add_mod *)
val _ = overload_on("ZG", ``add_mod``);

(* Note:
add_mod_group    |- !n. 0 < n ==> Group (ZG n)
add_mod_property |- !n. (!x. x IN (ZG n).carrier <=> x < n) /\ ((ZG n).id = 0) /\
                        (!x y. (ZG n).op x y = (x + y) MOD n) /\
                        FINITE (ZG n).carrier /\ (CARD (ZG n).carrier = n)
*)

(* The group for involution action. *)
val _ = overload_on("Z2", ``ZG 2``);

(* Theorem: f involute A ==> (Z2 act A) (FUNPOW f) *)
(* Proof:
   By action_def, add_mod_property, this is to show:
   (1) x IN A /\ a < 2 ==> FUNPOW f a x IN A
       Note f PERMUTES A              by involute_permutes
         so FUNPOW f a x IN A         by FUNPOW_closure
   (2) x IN A /\ a < 2 /\ b < 2 ==>
       FUNPOW f a (FUNPOW f b x) = FUNPOW f ((a + b) MOD 2) x
       Note  FUNPOW f a (FUNPOW f b x)
          = FUNPOW f (a + b) x        by FUNPOW_ADD
       If a = 0, b = 0, a + b = 0 = 0 MOD 2.
       If a = 0, b = 1, a + b = 1 = 1 MOD 2.
       If a = 1, b = 0, a + b = 1 = 1 MOD 2.
       If a = 1, b = 1, a + b = 2.  2 MOD 2 = 0.
        But FUNPOW f 2 x
          = f (f x)                   by FUNPOW_2
          = x                         by f involute A
          = FUNPOW f 0 x              by FUNPOW_0
*)
val funpow_action = store_thm(
  "funpow_action",
  ``!f A. f involute A ==> (Z2 act A) (FUNPOW f)``,
  rw[action_def, add_mod_property] >-
  rw[involute_permutes, FUNPOW_closure] >>
  `FUNPOW f a (FUNPOW f b x) = FUNPOW f (a + b) x` by rw[FUNPOW_ADD] >>
  (`((a = 0) \/ (a = 1)) /\ ((b = 0) \/ (b = 1))` by decide_tac >> simp[]) >>
  simp[FUNPOW_2]);

(* Adapt the general theory of group action to (FUNPOW f). *)
(* Note: Eventually, A = mills n, a set of triples (x,y,z), f = zagier or f = flip. *)

(* Extract theorems *)

val funpow_reach = save_thm("funpow_reach",
   reach_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> REWRITE_RULE [add_mod_property] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL
);
(* val funpow_reach =
|- !f x y. reach (FUNPOW f) Z2 x y <=> ?a. a < 2 /\ (FUNPOW f a x = y): thm *)

val funpow_equiv = save_thm("funpow_equiv",
   reach_equiv |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> ISPEC ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_equiv =
|- !f A. Group Z2 /\ (Z2 act A) (FUNPOW f) ==> reach (FUNPOW f) Z2 equiv_on A: thm *)

(* A better version *)

(* Theorem: f involute A ==> reach (FUNPOW f) Z2 equiv_on A *)
(* Proof:
   Note Group Z2                         by add_mod_group
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus reach (FUNPOW f) Z2 equiv_on A   by reach_equiv
*)
val funpow_equiv = store_thm(
  "funpow_equiv",
  ``!f A. f involute A ==> reach (FUNPOW f) Z2 equiv_on A``,
  rw[add_mod_group, funpow_action, reach_equiv]);

(* ------------------------------------------------------------------------- *)
(* FUNPOW Orbits                                                             *)
(* ------------------------------------------------------------------------- *)

val funpow_orbits = save_thm("funpow_orbits",
    orbits_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
     |> ISPEC ``A:'a -> bool`` |> GEN ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_orbits =
   |- !f A. orbits (FUNPOW f) Z2 A = {orbit (FUNPOW f) Z2 A x | x | x IN A} *)

val funpow_orbit = save_thm("funpow_orbit",
   orbit_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
     |> ISPEC ``A:'a -> bool`` |> SIMP_RULE bool_ss [add_mod_property]
     |> GEN ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_orbit =
   |- !f A x. orbit (FUNPOW f) Z2 A x = {FUNPOW f a x | a < 2}: thm *)

(* A better version *)

(* Theorem: orbit (FUNPOW f) Z2 A x = IMAGE (\a. FUNPOW f a x) (count 2) *)
(* Proof:
   Note orbit (FUNPOW f) Z2 A x
      = IMAGE (\a. FUNPOW f a x) Z2.carrier  by orbit_as_image
      = IMAGE (\a. FUNPOW f a x) (count 2)   by EXTENSION
*)
val funpow_orbit_alt = store_thm(
  "funpow_orbit_alt",
  ``!f A x. orbit (FUNPOW f) Z2 A x = IMAGE (\a. FUNPOW f a x) (count 2)``,
  rw[orbit_as_image, add_mod_property, EXTENSION]);

val funpow_orbit_element = save_thm("funpow_orbit_element",
   orbit_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> ISPEC ``A:'a -> bool``
                 |> SIMP_RULE (srw_ss()) [reach_def, add_mod_property]
                 |> GEN ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_orbit_element =
 |- !f A x y. y IN orbit (FUNPOW f) Z2 A x <=> ?a. a < 2 /\ (FUNPOW f a x = y): thm *)

val funpow_orbit_in_orbits = save_thm("funpow_orbit_in_orbits",
   orbit_is_orbits_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
     |> ISPEC ``A:'a -> bool`` |> GEN ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_orbit_in_orbits =
 |- !f A x. x IN A ==> orbit (FUNPOW f) Z2 A x IN orbits (FUNPOW f) Z2 A: thm *)

val funpow_orbits_card_by_types = save_thm("funpow_orbits_card_by_types",
    target_card_by_orbit_types |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
      |> ISPEC ``A:'a -> bool`` |> GEN_ALL
);
(* val funpow_orbits_card_by_types =
|- !f A. Group Z2 /\ (Z2 act A) (FUNPOW f) /\ FINITE A ==>
         (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                   SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)): thm *)

(* A better version *)

(* Theorem: FINITE A /\ f involute A ==>
            (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)) *)
(* Proof:
   Note Group Z2                         by add_mod_group
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)
                                         by target_card_by_orbit_types
*)
val funpow_orbits_card_by_types = store_thm(
  "funpow_orbits_card_by_types",
  ``!f A. FINITE A /\ f involute A ==>
    (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
              SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))``,
  simp[add_mod_group, funpow_action, target_card_by_orbit_types]);

(* Theorem: FINITE A /\ f involute A ==>
            (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)) *)
(* Proof:
   Note Group Z2                         by add_mod_group
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)
                                         by target_card_by_fixed_points
*)
val funpow_orbits_card_eqn = store_thm(
  "funpow_orbits_card_eqn",
  ``!f A. FINITE A /\ f involute A ==>
         (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                   SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))``,
  simp[add_mod_group, funpow_action, target_card_by_fixed_points]);

(* This will be very useful! *)


(* ------------------------------------------------------------------------- *)
(* Involution Orbits                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute A /\ x IN A /\
            y IN (orbit (FUNPOW f) Z2 A x) ==> ((y = x) \/ (y = f x)) *)
(* Proof:
   Note ?n. n < 2 /\ (y = FUNPOW f n x)  by funpow_orbit_element
   When n = 0, y = FUNPOW f 0 x = x      by FUNPOW_0
   When n = 1, y = FUNPOW f 1 x = f x    by FUNPOW_1
*)
val involute_orbit_element = store_thm(
  "involute_orbit_element",
  ``!f A x y. f involute A /\ x IN A /\
             y IN (orbit (FUNPOW f) Z2 A x) ==> ((y = x) \/ (y = f x))``,
  rpt strip_tac >>
  `?n. n < 2 /\ (y = FUNPOW f n x)` by metis_tac[funpow_orbit_element] >>
  (`(n = 0) \/ (n = 1)` by decide_tac >> simp[]));

(* Theorem: f involute A /\ x IN A ==> x IN orbit (FUNPOW f) Z2 A x *)
(* Proof:
   Note Group Z2                         by add_mod_group
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus x IN orbit (FUNPOW f) Z2 A x     by orbit_has_self
*)
val involute_orbit_has_self = store_thm(
  "involute_orbit_has_self",
  ``!f A x. f involute A /\ x IN A ==> x IN orbit (FUNPOW f) Z2 A x``,
  rw[add_mod_group, funpow_action, orbit_has_self]);

(* Theorem: f involute A /\ x IN A /\ n < 2 ==>
            (FUNPOW f n x) IN orbit (FUNPOW f) Z2 A x *)
(* Proof:
   Note Group Z2                        by add_mod_group
    and (Z2 act A) (FUNPOW f)           by funpow_action
    and n IN Z2.carrier                 by add_mod_property, n < 2
   Thus (FUNPOW f n x) IN orbit (FUNPOW f) Z2 A x
                                        by orbit_has_action_element
*)
val involute_orbit_has_funpow = store_thm(
  "involute_orbit_has_funpow",
  ``!f A x n. f involute A /\ x IN A /\ n < 2 ==>
             (FUNPOW f n x) IN orbit (FUNPOW f) Z2 A x``,
  rw[add_mod_group, funpow_action, orbit_has_action_element, add_mod_property]);

(* Theorem: f involute A /\ x IN A ==> f x IN orbit (FUNPOW f) Z2 A x *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 A x.
   Note (FUNPOW f 1 x) IN b    by involute_orbit_has_funpow
    and FUNPOW f 1 x = f x     by FUNPOW_1
*)
val involute_orbit_has_image = store_thm(
  "involute_orbit_has_image",
  ``!f A x. f involute A /\ x IN A ==> f x IN orbit (FUNPOW f) Z2 A x``,
  metis_tac[involute_orbit_has_funpow, FUNPOW_1, DECIDE``1 < 2``]);

(* Theorem: f involute A /\ x IN A ==>
            (orbit (FUNPOW f) Z2 A x = IMAGE (\j. FUNPOW f j x) (count 2)) *)
(* Proof:
   Note (Z2 act A) (FUNPOW f)                by funpow_action
    and Z2.carrier = count 2                 by add_mod_property, EXTENSION
     so orbit (FUNPOW f) Z2 A x
      = IMAGE (\j. FUNPOW f j x) (count 2)   by orbit_as_image
*)
val involute_orbit_as_image = store_thm(
  "involute_orbit_as_image",
  ``!f A x. f involute A /\ x IN A ==>
           (orbit (FUNPOW f) Z2 A x = IMAGE (\j. FUNPOW f j x) (count 2))``,
  rw[orbit_as_image, funpow_action, add_mod_property, EXTENSION]);

(* Theorem: FINITE A /\ f involute A ==> FINITE (orbits (FUNPOW f) Z2 A) *)
(* Proof:
   Note (Z2 act A) (FUNPOW f)            by funpow_action
   Thus FINITE (orbits (FUNPOW f) Z2 A)  by orbits_finite
*)
val involute_orbits_finite = store_thm(
  "involute_orbits_finite",
  ``!f A. FINITE A /\ f involute A ==> FINITE (orbits (FUNPOW f) Z2 A)``,
  rw[funpow_action, orbits_finite]);

(* Theorem: FINITE A /\ f involute A /\ x IN A ==>
            FINITE (orbit (FUNPOW f) Z2 A x) *)
(* Proof:
   Note (Z2 act A) (FUNPOW f)             by funpow_action
    and orbit (FUNPOW f) Z2 A a IN orbits (FUNPOW f) Z2 A
                                          by orbit_is_orbits_element
   Thus FINITE (orbit (FUNPOW f) Z2 A x)  by orbits_element_finite
*)
val involute_orbit_finite = store_thm(
  "involute_orbit_finite",
  ``!f A x. FINITE A /\ f involute A /\ x IN A ==>
           FINITE (orbit (FUNPOW f) Z2 A x)``,
  metis_tac[funpow_action, orbit_is_orbits_element, orbits_element_finite]);

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> EMPTY *)
(* Proof:
   Note Group Z2                        by add_mod_group
    and (Z2 act A) (FUNPOW f)           by funpow_action
   Thus e IN orbits (FUNPOW f) Z2 A ==> e <> EMPTY
                                        by orbits_element_nonempty
*)
val involute_orbit_nonempty = store_thm(
  "involute_orbit_nonempty",
  ``!f A e. f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> EMPTY``,
  metis_tac[add_mod_group, funpow_action, orbits_element_nonempty, DECIDE``0 < 2``]);

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ x IN e ==>
            (e = orbit (FUNPOW f) Z2 A x) *)
(* Proof:
   Note Group Z2                        by add_mod_group
    and (Z2 act A) (FUNPOW f)           by funpow_action
   Thus e IN orbits (FUNPOW f) Z2 A ==>
       !x. x IN e ==> e = orbit (FUNPOW f) Z2 A x
                                        by orbits_element_is_orbit
*)
val involute_orbits_element_is_orbit = store_thm(
  "involute_orbits_element_is_orbit",
  ``!f A e x. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ x IN e ==>
             (e = orbit (FUNPOW f) Z2 A x)``,
  rw[add_mod_group, funpow_action, orbits_element_is_orbit]);

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ x IN e ==> x IN A *)
(* Proof:
   Note (Z2 act A) (FUNPOW f)           by funpow_action
   Thus e IN orbits (FUNPOW f) Z2 A
    ==> !x. x IN e ==> x IN A           by orbits_element_element
*)
val involute_orbits_element_element = store_thm(
  "involute_orbits_element_element",
  ``!f A e x. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ x IN e ==> x IN A``,
  metis_tac[funpow_action, orbits_element_element]);

(* Theorem: FINITE A /\ f involute A ==> FINITE (multi_orbits (FUNPOW f) Z2 A) *)
(* Proof:
   Note (Z2 act A) (FUNPOW f)                 by funpow_action
   ThusFINITE (multi_orbits (FUNPOW f) Z2 A)  by multi_orbits_finite
*)
val involute_multi_orbits_finite = store_thm(
  "involute_multi_orbits_finite",
  ``!f A. FINITE A /\ f involute A ==> FINITE (multi_orbits (FUNPOW f) Z2 A)``,
  rw[funpow_action, multi_orbits_finite]);

(* ------------------------------------------------------------------------- *)
(* Involution fixed points                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute A /\ x IN fixed_points (FUNPOW f) Z2 A ==> (f x = x) *)
(* Proof:
   Note 1 IN Z2.carrier   by add_mod_property
     f x
   = FUNPOW f 1 x             by FUNPOW_1
   = x                        by fixed_points_element
*)
val involute_fixed_points = store_thm(
  "involute_fixed_points",
  ``!f A x. f involute A /\ x IN fixed_points (FUNPOW f) Z2 A ==> (f x = x)``,
  rw[fixed_points_def, add_mod_property] >>
  `FUNPOW f 1 x = x` by rw[] >>
  fs[]);

(* Theorem: f involute A /\ x IN A ==>
            (x IN fixed_points (FUNPOW f) Z2 A <=> (f x = x)) *)
(* Proof:
   By fixed_points_def, this is to show:
   If part: x IN A /\ !n. n < 2 /\ FUNPOW f n x = x ==> f x = x
      Since f x = FUNPOW 1 x               by FUNPOW_1
         so f x = x                        by f involute A
   Only-if part: x IN A /\ f x = x ==> !n. n < 2 ==> FUNPOW f n x = x
      When n = 0, FUNPOW f 0 x = x         by FUNPOW_0
      When n = 1, FUNPOW f 1 x = f x = x   by given
*)
val involute_fixed_points_iff = store_thm(
  "involute_fixed_points_iff",
  ``!f A x. f involute A /\ x IN A ==>
           (x IN fixed_points (FUNPOW f) Z2 A <=> (f x = x))``,
  rw[fixed_points_def, add_mod_property, EQ_IMP_THM] >-
  metis_tac[FUNPOW_1, DECIDE``1 < 2``] >>
  (`(a = 0) \/ (a = 1)` by decide_tac >> simp[]));

val involute_fixed_points_element_element = save_thm("involute_fixed_points_element_element",
    fixed_points_element_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
     |> ISPEC ``A:'a -> bool`` |> GEN ``A:'a -> bool`` |> GEN_ALL
);
(* val involute_fixed_points_element_element =
   |- !f A x. x IN fixed_points (FUNPOW f) Z2 A ==> x IN A: thm *)

(* ------------------------------------------------------------------------- *)
(* Involution Target Cardinality                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute A /\ x IN A /\ (f x = x) ==>
            (orbit (FUNPOW f) Z2 A x = {x}) *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 A x.
   Note x IN b                   by involute_orbit_has_self
    and !y. y IN A ==> (y = x)   by involute_orbit_element, f x = x.
   Thus b = {x}                  by EXTENSION
*)
val involute_orbit_fixed = store_thm(
  "involute_orbit_fixed",
  ``!f A x. f involute A /\ x IN A /\ (f x = x) ==>
           (orbit (FUNPOW f) Z2 A x = {x})``,
  rw[EXTENSION] >>
  metis_tac[involute_orbit_has_self, involute_orbit_element]);

(* Theorem: f involute A /\ x IN A /\ (f x <> x) ==>
            (orbit (FUNPOW f) Z2 A x = {x; f x}) *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 A x.
   Note x IN b                   by involute_orbit_has_self
    and f x IN b                 by involute_orbit_has_image
    and !y. y IN A ==> (y = x) \/ (y = f x)
                                 by involute_orbit_element, f x <> x.
   Thus s = {x; f x}             by EXTENSION
*)
val involute_orbit_not_fixed = store_thm(
  "involute_orbit_not_fixed",
  ``!f A x. f involute A /\ x IN A /\ (f x <> x) ==>
           (orbit (FUNPOW f) Z2 A x = {x; f x})``,
  rw[EXTENSION] >>
  `x IN (orbit (FUNPOW f) Z2 A x)` by rw[involute_orbit_has_self] >>
  `f x IN (orbit (FUNPOW f) Z2 A x)` by rw[involute_orbit_has_image] >>
  metis_tac[involute_orbit_element]);

(* Theorem: f involute A /\
            e IN (multi_orbits (FUNPOW f) Z2 A) ==> (CARD e = 2) *)
(* Proof:
   By multi_orbits_def, this is to show:
   !e. e IN orbits (FUNPOW f) Z2 A /\ ~SING e ==> CARD e = 2.
   Note e <> EMPTY                     by involute_orbit_nonempty
     so ?x. x IN e                     by MEMBER_NOT_EMPTY
    and e = orbit (FUNPOW f) Z2 A x    by involute_orbits_element_is_orbit
    now x IN A                         by involute_orbits_element_element
    If f x = x,
       then e = {x}                    by involute_orbit_fixed
       thus SING e                     by SING_DEF
       This contradicts ~SING e
    Otherwise, f x <> x.
       then e = {x; f x}               by involute_orbit_not_fixed
         so CARD e = 2                 by CARD_DEF
*)
val involute_multi_orbits_element_card = store_thm(
  "involute_multi_orbits_element_card",
  ``!f A e. f involute A /\
           e IN (multi_orbits (FUNPOW f) Z2 A) ==> (CARD e = 2)``,
  rw[multi_orbits_def] >>
  `?x. x IN e` by metis_tac[involute_orbit_nonempty, MEMBER_NOT_EMPTY] >>
  `e = orbit (FUNPOW f) Z2 A x` by rw[involute_orbits_element_is_orbit] >>
  `x IN A` by metis_tac[involute_orbits_element_element] >>
  Cases_on `f x = x` >| [
    `e = {x}` by rw[involute_orbit_fixed] >>
    metis_tac[SING_DEF],
    `e = {x; f x}` by rw[involute_orbit_not_fixed] >>
    rw[]
  ]);

(* Theorem: FINITE A /\ f involute A ==>
            (CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                      CARD (fixed_points (FUNPOW f) Z2 A)) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 A,
        b = fixed_points (FUNPOW f) Z2 A.
   Then FINITE a                 by involute_multi_orbits_finite
        CARD A
      = CARD b + SIGMA CARD a    by funpow_orbits_card_eqn
      = CARD b + 2 * CARD a      by SIGMA_CONSTANT, involute_multi_orbits_element_card
      = 2 * CARD a + CARD b      by ADD_COMM
*)
val involute_orbits_card_eqn = store_thm(
  "involute_orbits_card_eqn",
  ``!f A. FINITE A /\ f involute A ==>
         (CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                   CARD (fixed_points (FUNPOW f) Z2 A))``,
  rpt strip_tac >>
  qabbrev_tac `a = multi_orbits (FUNPOW f) Z2 A` >>
  qabbrev_tac `b = fixed_points (FUNPOW f) Z2 A` >>
  `FINITE a` by rw[involute_multi_orbits_finite, Abbr`a`] >>
  `CARD A = CARD b + SIGMA CARD a` by rw[funpow_orbits_card_eqn, Abbr`a`, Abbr`b`] >>
  `_ = CARD b + 2 * CARD a` by metis_tac[SIGMA_CONSTANT, involute_multi_orbits_element_card] >>
  simp[]);

(* Theorem: FINITE A /\ f involute A ==>
            (EVEN (CARD A) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 A))) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 A,
        b = fixed_points (FUNPOW f) Z2 A.
   Note CARD A = 2 * a + CARD b            by involute_orbits_card_eqn
     so EVEN (CARD A) <=> EVEN (CARD b)    by EQ_PARITY
*)
val involute_fixed_points_both_even = store_thm(
  "involute_fixed_points_both_even",
  ``!f A. FINITE A /\ f involute A ==>
         (EVEN (CARD A) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 A)))``,
  metis_tac[involute_orbits_card_eqn, EQ_PARITY]);

(* Theorem: FINITE A /\ f involute A ==>
            (ODD (CARD A) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 A))) *)
(* Proof: by involute_fixed_points_both_even, ODD_EVEN. *)
val involute_fixed_points_both_odd = store_thm(
  "involute_fixed_points_both_odd",
  ``!f A. FINITE A /\ f involute A ==>
         (ODD (CARD A) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 A)))``,
  rw[involute_fixed_points_both_even, ODD_EVEN]);

(* A useful corollary. *)

(* Theorem: FINITE A /\ f involute A /\ g involute A ==>
           (EVEN (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
            EVEN (CARD (fixed_points (FUNPOW g) Z2 A))) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 A,
        b = fixed_points (FUNPOW f) Z2 A,
        c = multi_orbits (FUNPOW g) Z2 A,
        d = fixed_points (FUNPOW g) Z2 A.
   Note EVEN (CARD A) <=> EVEN (CARD b)    by involute_fixed_points_both_even
    and EVEN (CARD A) <=> EVEN (CARD d)    by involute_fixed_points_both_even
   Thus EVEN (CARD b) <=> EVEN (CARD d)
*)
val involute_two_fixed_points_both_even = store_thm(
  "involute_two_fixed_points_both_even",
  ``!f g A. FINITE A /\ f involute A /\ g involute A ==>
          (EVEN (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
           EVEN (CARD (fixed_points (FUNPOW g) Z2 A)))``,
  metis_tac[involute_fixed_points_both_even]);

(* Theorem: FINITE A /\ f involute A /\ g involute A ==>
           (ODD (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
            ODD (CARD (fixed_points (FUNPOW g) Z2 A))) *)
(* Proof: by involute_two_fixed_points_both_even, ODD_EVEN. *)
val involute_two_fixed_points_both_odd = store_thm(
  "involute_two_fixed_points_both_odd",
  ``!f g A. FINITE A /\ f involute A /\ g involute A ==>
          (ODD (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
           ODD (CARD (fixed_points (FUNPOW g) Z2 A)))``,
  rw[involute_two_fixed_points_both_even, ODD_EVEN]);



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
