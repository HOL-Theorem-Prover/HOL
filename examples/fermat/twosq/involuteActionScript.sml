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

(* val _ = load "helperTwosqTheory"; *)
open helperTwosqTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def, prime_def *)

(* val _ = load "involuteTheory"; *)
open involuteTheory;

(* val _ = load "groupInstancesTheory"; *)
open groupInstancesTheory; (* for Zadd_def *)

(* val _ = load "groupActionTheory"; *)
open groupActionTheory; (* for fixed_points_def *)


(* ------------------------------------------------------------------------- *)
(* Involution and Action Documentation                                       *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   FUNPOW Action:
   funpow_action   |- !f X. f involute X ==> (Z2 act X) (FUNPOW f)
   funpow_reach    |- !f x y. reach (FUNPOW f) Z2 x y <=> ?a. a < 2 /\ FUNPOW f a x = y
   funpow_equiv    |- !f X. f involute X ==> reach (FUNPOW f) Z2 equiv_on X

   FUNPOW Orbits:
   funpow_orbits   |- !f X. orbits (FUNPOW f) Z2 X = IMAGE (orbit (FUNPOW f) Z2) X
   funpow_orbit    |- !f x. orbit (FUNPOW f) Z2 x = {FUNPOW f a x | a < 2}
   funpow_orbit_alt|- !f x. orbit (FUNPOW f) Z2 x = IMAGE (\a. FUNPOW f a x) (count 2)
   funpow_orbit_element
                   |- !f x y. y IN orbit (FUNPOW f) Z2 x <=> ?a. a < 2 /\ FUNPOW f a x = y
   funpow_orbit_in_orbits
                   |- !f X x. x IN X ==> orbit (FUNPOW f) Z2 x IN orbits (FUNPOW f) Z2 X
   funpow_orbit_finite
                   |- !f x. FINITE (orbit (FUNPOW f) Z2 x)
   funpow_orbits_finite
                   |- !f X. FINITE X ==> FINITE (orbits (FUNPOW f) Z2 X)
   funpow_multi_orbits_finite
                   |- !f X. FINITE X ==> FINITE (multi_orbits (FUNPOW f) Z2 X)

   Involution Orbits:
   involute_orbit_element
                   |- !f X x y. f involute X /\ x IN X /\ y IN orbit (FUNPOW f) Z2 x ==>
                                y = x \/ y = f x
   involute_orbit_has_self
                   |- !f X x. f involute X /\ x IN X ==> x IN orbit (FUNPOW f) Z2 x
   involute_orbit_has_funpow
                   |- !f X x n. f involute X /\ x IN X ==>
                                FUNPOW f n x IN orbit (FUNPOW f) Z2 x
   involute_orbit_has_image
                   |- !f X x. f involute X /\ x IN X ==> f x IN orbit (FUNPOW f) Z2 x
   involute_orbit_nonempty
                   |- !f X e. f involute X /\ e IN orbits (FUNPOW f) Z2 X ==> e <> {}
   involute_orbits_element_is_orbit
                   |- !f X e x. f involute X /\ e IN orbits (FUNPOW f) Z2 X /\
                                x IN e ==> e = orbit (FUNPOW f) Z2 x
   involute_orbits_element_element
                   |- !f X e x. f involute X /\ e IN orbits (FUNPOW f) Z2 X /\
                                x IN e ==> x IN X

   Involution fixed points:
   involute_fixed_points
                   |- !f X x. f involute X /\
                              x IN fixed_points (FUNPOW f) Z2 X ==> f x = x
   involute_fixed_points_iff
                   |- !f X x. f involute X /\ x IN X ==>
                              (x IN fixed_points (FUNPOW f) Z2 X <=> f x = x)
   involute_fixed_points_element_element
                   |- !f X x. x IN fixed_points (FUNPOW f) Z2 X ==> x IN X

   Involution Target Cardinality:
   involute_target_card_by_types
                   |- !f X. FINITE X /\ f involute X ==>
                            CARD X = CARD (sing_orbits (FUNPOW f) Z2 X) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 X)
   involute_target_card_eqn
                   |- !f X. FINITE X /\ f involute X ==>
                           (CARD A = CARD (fixed_points (FUNPOW f) Z2 X) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 X))
   involute_orbit_fixed
                   |- !f X x. f involute X /\ x IN X /\ f x = x ==>
                              orbit (FUNPOW f) Z2 x = {x}
   involute_orbit_not_fixed
                   |- !f X x. f involute X /\ x IN X /\ f x <> x ==>
                              orbit (FUNPOW f) Z2 x = {x; f x}
   involute_multi_orbits_element_card
                   |- !f X e. f involute X /\ e IN multi_orbits (FUNPOW f) Z2 X ==>
                              CARD e = 2
   involute_target_card_thm
                   |- !f X. FINITE X /\ f involute X ==>
                            CARD X = 2 * CARD (multi_orbits (FUNPOW f) Z2 X) +
                                     CARD (fixed_points (FUNPOW f) Z2 X)
   involute_fixed_points_both_even
                   |- !f X. FINITE X /\ f involute X ==>
                            (EVEN (CARD X) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 X)))
   involute_fixed_points_both_odd
                   |- !f X. FINITE X /\ f involute X ==>
                            (ODD (CARD X) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 X)))
   involute_two_fixed_points_both_even
                   |- !f g X. FINITE X /\ f involute X /\ g involute X ==>
                              (EVEN (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
                               EVEN (CARD (fixed_points (FUNPOW g) Z2 X)))
   involute_two_fixed_points_both_odd
                   |- !f g X. FINITE X /\ f involute X /\ g involute X ==>
                              (ODD (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
                               ODD (CARD (fixed_points (FUNPOW g) Z2 X)))
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* FUNPOW Action                                                             *)
(* ------------------------------------------------------------------------- *)

(* The group for involution action. *)
val _ = overload_on("Z2", ``Zadd 2``);

(*
Zadd_property;
|- !n. (!x. x IN (Zadd n).carrier <=> x < n) /\ (Zadd n).id = 0 /\
       (!x y. (Zadd n).op x y = (x + y) MOD n) /\
       FINITE (Zadd n).carrier /\ CARD (Zadd n).carrier = n
*)

(* Theorem: f involute X ==> (Z2 act X) (FUNPOW f) *)
(* Proof:
   By action_def, Zadd_property, this is to show:
   (1) x IN X /\ a < 2 ==> FUNPOW f a x IN X
       Note f PERMUTES X              by involute_permutes
         so FUNPOW f a x IN X         by FUNPOW_closure
   (2) x IN X /\ a < 2 /\ b < 2 ==>
       FUNPOW f a (FUNPOW f b x) = FUNPOW f ((a + b) MOD 2) x
       Note FUNPOW f a (FUNPOW f b x)
          = FUNPOW f (a + b) x        by FUNPOW_ADD
       If a = 0, b = 0, a + b = 0 = 0 MOD 2.
       If a = 0, b = 1, a + b = 1 = 1 MOD 2.
       If a = 1, b = 0, a + b = 1 = 1 MOD 2.
       If a = 1, b = 1, a + b = 2.  2 MOD 2 = 0.
       The goal becomes: FUNPOW f 2 x = x
        But FUNPOW f 2 x
          = f (f x)                   by FUNPOW_2
          = x                         by f involute X
          = FUNPOW f 0 x              by FUNPOW_0
*)
Theorem funpow_action:
  !f X. f involute X ==> (Z2 act X) (FUNPOW f)
Proof
  rw[action_def, Zadd_property] >-
  rw[involute_permutes, FUNPOW_closure] >>
  `FUNPOW f a (FUNPOW f b x) = FUNPOW f (a + b) x` by rw[FUNPOW_ADD] >>
  (`(a = 0 \/ a = 1) /\ (b = 0 \/ b = 1)` by decide_tac >> simp[]) >>
  simp[FUNPOW_2]
QED

(* Adapt the general theory of group action to (FUNPOW f). *)
(* Note: Eventually, X = mills n, a set of triples (x,y,z), f = zagier or f = flip. *)

(* Extract theorems *)

val funpow_reach = save_thm("funpow_reach",
   reach_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
             |> REWRITE_RULE[Zadd_property] |> GEN_ALL
);
(* val funpow_reach =
|- !f x y. reach (FUNPOW f) Z2 x y <=> ?a. a < 2 /\ FUNPOW f a x = y: thm *)

val funpow_equiv = save_thm("funpow_equiv",
   reach_equiv |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_equiv =
|- !f X. Group Z2 /\ (Z2 act X) (FUNPOW f) ==> reach (FUNPOW f) Z2 equiv_on X: thm *)

(* A better version *)

(* Theorem: f involute X ==> reach (FUNPOW f) Z2 equiv_on X *)
(* Proof:
   Note Group Z2                         by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)            by funpow_action
   Thus reach (FUNPOW f) Z2 equiv_on X   by reach_equiv
*)
Theorem funpow_equiv:
  !f X. f involute X ==> reach (FUNPOW f) Z2 equiv_on X
Proof
  rw[Zadd_group, funpow_action, reach_equiv]
QED

(* ------------------------------------------------------------------------- *)
(* FUNPOW Orbits                                                             *)
(* ------------------------------------------------------------------------- *)

val funpow_orbits = save_thm("funpow_orbits",
    orbits_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_orbits =
|- !f X. orbits (FUNPOW f) Z2 X = IMAGE (orbit (FUNPOW f) Z2) X: thm *)

val funpow_orbit = save_thm("funpow_orbit",
   orbit_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
             |> REWRITE_RULE[Zadd_carrier] |> GEN_ALL
);
(* val funpow_orbit =
|- !f x. orbit (FUNPOW f) Z2 x = IMAGE (\a. FUNPOW f a x) (count 2): thm *)

val funpow_orbit_element = save_thm("funpow_orbit_element",
   orbit_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
                 |> SIMP_RULE (srw_ss()) [reach_def, Zadd_carrier] |> GEN_ALL
);
(* val funpow_orbit_element =
|- !f x y. y IN orbit (FUNPOW f) Z2 x <=> ?a. a < 2 /\ FUNPOW f a x = y: thm *)

val funpow_orbit_in_orbits = save_thm("funpow_orbit_in_orbits",
   orbit_is_orbits_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_orbit_in_orbits =
|- !f X x. x IN X ==> orbit (FUNPOW f) Z2 x IN orbits (FUNPOW f) Z2 X: thm *)

(* Theorem: FINITE (orbit (FUNPOW f) Z2 x) *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 x.
   Note Z2.carrier = count 2      by Zadd_carrier
    and FINITE (count 2)          by FINITE_COUNT
     so FINITE b                  by orbit_finite
*)
Theorem funpow_orbit_finite:
  !f x. FINITE (orbit (FUNPOW f) Z2 x)
Proof
  simp[Zadd_carrier, orbit_finite]
QED

val funpow_orbits_finite = save_thm("funpow_orbits_finite",
    orbits_finite |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_orbits_finite =
|- !f X. FINITE X ==> FINITE (orbits (FUNPOW f) Z2 X): thm *)

val funpow_multi_orbits_finite = save_thm("funpow_multi_orbits_finite",
    multi_orbits_finite |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_multi_orbits_finite =
|- !f X. FINITE X ==> FINITE (multi_orbits (FUNPOW f) Z2 X): thm *)

(* ------------------------------------------------------------------------- *)
(* Involution Orbits                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute X /\ x IN X /\
            y IN (orbit (FUNPOW f) Z2 x) ==> y = x \/ y = f x *)
(* Proof:
   Note ?a. a < 2 /\ FUNPOW f a x = y    by funpow_orbit_element
   When n = 0, y = FUNPOW f 0 x = x      by FUNPOW_0
   When n = 1, y = FUNPOW f 1 x = f x    by FUNPOW_1
*)
Theorem involute_orbit_element:
  !f X x y. f involute X /\ x IN X /\
            y IN (orbit (FUNPOW f) Z2 x) ==> y = x \/ y = f x
Proof
  rpt strip_tac >>
  imp_res_tac funpow_orbit_element >>
  (`a = 0 \/ a = 1` by decide_tac >> fs[])
QED

(* Theorem: f involute X /\ x IN X ==> x IN orbit (FUNPOW f) Z2 x *)
(* Proof:
   Note Group Z2                       by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)          by funpow_action
   Thus x IN orbit (FUNPOW f) Z2 x     by orbit_has_self
*)
Theorem involute_orbit_has_self:
  !f X x. f involute X /\ x IN X ==> x IN orbit (FUNPOW f) Z2 x
Proof
  metis_tac[Zadd_group, funpow_action, orbit_has_self, DECIDE``0 < 2``]
QED

(* Theorem: f involute X /\ x IN X ==>
            FUNPOW f n a IN orbit (FUNPOW f) Z2 x *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 x, k = n MOD 2.
   Then k < 2                           by MOD_LESS, 0 < 2
    and FUNPOW f 2 x = x                by involute_alt
     so FUNPOW f n x = FUNPOW f k x     by FUNPOW_MOD, 0 < 2, [1]
   Note Group Z2                        by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)           by funpow_action
    and k IN Z2.carrier                 by Zadd_element, n < 2
   Thus (FUNPOW f k a) IN b             by orbit_has_action_element
     or (FUNPOW f n a) IN b             by above [1]
*)
Theorem involute_orbit_has_funpow:
  !f X x n. f involute X /\ x IN X ==>
            FUNPOW f n x IN orbit (FUNPOW f) Z2 x
Proof
  rpt strip_tac >>
  qabbrev_tac `k = n MOD 2` >>
  `k < 2` by rw[Abbr`k`] >>
  `FUNPOW f n x = FUNPOW f k x` by fs[involute_alt, FUNPOW_MOD, Abbr`k`] >>
  rw[Zadd_group, funpow_action, orbit_has_action_element, Zadd_element]
QED

(* Theorem: f involute X /\ x IN X ==> f x IN orbit (FUNPOW f) Z2 x *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 x.
   Note (FUNPOW f 1 x) IN b    by involute_orbit_has_funpow
    and FUNPOW f 1 x = f x     by FUNPOW_1
*)
Theorem involute_orbit_has_image:
  !f X x. f involute X /\ x IN X ==> f x IN orbit (FUNPOW f) Z2 x
Proof
  metis_tac[involute_orbit_has_funpow, FUNPOW_1, DECIDE``1 < 2``]
QED

(* Theorem: f involute X /\ e IN orbits (FUNPOW f) Z2 X ==> e <> EMPTY *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 X.
   Note Group Z2                   by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)      by funpow_action
   Thus e IN B ==> e <> EMPTY      by orbits_element_nonempty
*)
Theorem involute_orbit_nonempty:
  !f X e. f involute X /\ e IN orbits (FUNPOW f) Z2 X ==> e <> EMPTY
Proof
  metis_tac[Zadd_group, funpow_action, orbits_element_nonempty, DECIDE``0 < 2``]
QED

(* Theorem: f involute X /\ e IN orbits (FUNPOW f) Z2 X /\ x IN e ==>
            e = orbit (FUNPOW f) Z2 x *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 X.
   Note Group Z2                     by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)        by funpow_action
   Thus e = orbit (FUNPOW f) Z2 x    by orbits_element_is_orbit
*)
Theorem involute_orbits_element_is_orbit:
  !f X e x. f involute X /\ e IN orbits (FUNPOW f) Z2 X /\ x IN e ==>
            e = orbit (FUNPOW f) Z2 x
Proof
  metis_tac[Zadd_group, funpow_action, orbits_element_is_orbit, DECIDE``0 < 2``]
QED

(* Theorem: f involute X /\ e IN orbits (FUNPOW f) Z2 X /\ x IN e ==> x IN X *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 X.
   Note (Z2 act X) (FUNPOW f)      by funpow_action
   Thus x IN X                     by orbits_element_element
*)
Theorem involute_orbits_element_element:
  !f X e x. f involute X /\ e IN orbits (FUNPOW f) Z2 X /\ x IN e ==> x IN X
Proof
  metis_tac[funpow_action, orbits_element_element]
QED

(* ------------------------------------------------------------------------- *)
(* Involution fixed points                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute X /\ x IN fixed_points (FUNPOW f) Z2 X ==> f x = x *)
(* Proof:
   Note 1 IN Z2.carrier    by Zadd_element, 1 < 2
     f x
   = FUNPOW f 1 x          by FUNPOW_1
   = x                     by fixed_points_element
*)
Theorem involute_fixed_points:
  !f X x. f involute X /\ x IN fixed_points (FUNPOW f) Z2 X ==> f x = x
Proof
  rw[fixed_points_element, Zadd_element] >>
  metis_tac[FUNPOW_1, DECIDE``1 < 2``]
QED

(* Theorem: f involute X /\ x IN X ==>
            (x IN fixed_points (FUNPOW f) Z2 X <=> f x = x) *)
(* Proof:
   By fixed_points_element, this is to show:
   If part: x IN X /\ !a. a < 2 /\ FUNPOW f a x = x ==> f x = x
      Since f x = FUNPOW 1 x               by FUNPOW_1
         so f x = x                        by implication
   Only-if part: x IN X /\ f x = x ==> !a. a < 2 ==> FUNPOW f a x = x
      When a = 0, FUNPOW f 0 x = x         by FUNPOW_0
      When a = 1, FUNPOW f 1 x = f x = x   by FUNPOW_1, f involute X
*)
Theorem involute_fixed_points_iff:
  !f X x. f involute X /\ x IN X ==>
          (x IN fixed_points (FUNPOW f) Z2 X <=> f x = x)
Proof
  rw[fixed_points_element, Zadd_element, EQ_IMP_THM] >-
  metis_tac[FUNPOW_1, DECIDE``1 < 2``] >>
  (`a = 0 \/ a = 1` by decide_tac >> simp[])
QED

val involute_fixed_points_element_element =
    save_thm("involute_fixed_points_element_element",
    fixed_points_element_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val involute_fixed_points_element_element =
|- !f X x. x IN fixed_points (FUNPOW f) Z2 X ==> x IN X: thm *)

(* ------------------------------------------------------------------------- *)
(* Involution Target Cardinality                                             *)
(* ------------------------------------------------------------------------- *)

val involute_target_card_by_types = save_thm("involute_target_card_by_types",
    target_card_by_orbit_types |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val involute_target_card_by_types =
|- !f X. Group Z2 /\ (Z2 act X) (FUNPOW f) /\ FINITE X ==>
         CARD X = CARD (sing_orbits (FUNPOW f) Z2 X) +
                  SIGMA CARD (multi_orbits (FUNPOW f) Z2 X): thm *)

(* A better version *)

(* Theorem: FINITE X /\ f involute X ==>
            CARD X = CARD (sing_orbits (FUNPOW f) Z2 X) +
                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 X) *)
(* Proof:
   Note Group Z2                         by Zadd_group, 0 < 2
    and (Z2 act X) (FUNPOW f)            by funpow_action
   Thus CARD X = CARD (sing_orbits (FUNPOW f) Z2 X) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 X)
                                         by target_card_by_orbit_types
*)
Theorem involute_target_card_by_types:
  !f X. FINITE X /\ f involute X ==>
        CARD X = CARD (sing_orbits (FUNPOW f) Z2 X) +
                 SIGMA CARD (multi_orbits (FUNPOW f) Z2 X)
Proof
  simp[Zadd_group, funpow_action, target_card_by_orbit_types]
QED

(* Theorem: FINITE X /\ f involute X ==>
            CARD X = CARD (fixed_points (FUNPOW f) Z2 X) +
                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 X) *)
(* Proof:
   Note Group Z2                         by Zadd_group
    and (Z2 act X) (FUNPOW f)            by funpow_action
   Thus CARD X = CARD (fixed_points (FUNPOW f) Z2 X) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 X)
                                         by target_card_by_fixed_points
*)
Theorem involute_target_card_eqn:
  !f X. FINITE X /\ f involute X ==>
        CARD X = CARD (fixed_points (FUNPOW f) Z2 X) +
                 SIGMA CARD (multi_orbits (FUNPOW f) Z2 X)
Proof
  simp[Zadd_group, funpow_action, target_card_by_fixed_points]
QED

(* This will be very useful! *)

(* Theorem: f involute X /\ x IN X /\ f x = x ==>
            orbit (FUNPOW f) Z2 x = {x} *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 x.
   Note x IN b                   by involute_orbit_has_self
    and !b. b IN X ==> (b = x)   by involute_orbit_element, f x = x.
   Thus b = {x}                  by EXTENSION
*)
Theorem involute_orbit_fixed:
  !f X x. f involute X /\ x IN X /\ f x = x ==>
          orbit (FUNPOW f) Z2 x = {x}
Proof
  rw[EXTENSION] >>
  metis_tac[involute_orbit_has_self, involute_orbit_element]
QED

(* Theorem: f involute X /\ x IN X /\ f x <> x ==>
            orbit (FUNPOW f) Z2 x = {x; f x} *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 x.
   Note x IN b                   by involute_orbit_has_self
    and f x IN b                 by involute_orbit_has_image
    and !c. c IN X ==> (c = x) \/ (c = f x)
                                 by involute_orbit_element, f x <> x
   Thus b = {x; f x}             by EXTENSION
*)
Theorem involute_orbit_not_fixed:
  !f X x. f involute X /\ x IN X /\ f x <> x ==>
          orbit (FUNPOW f) Z2 x = {x; f x}
Proof
  rw[EXTENSION] >>
  imp_res_tac involute_orbit_has_self >>
  metis_tac[involute_orbit_has_image, involute_orbit_element]
QED

(* Theorem: f involute X /\
            e IN (multi_orbits (FUNPOW f) Z2 X) ==> CARD e = 2 *)
(* Proof:
   By multi_orbits_def, this is to show:
   !e. e IN orbits (FUNPOW f) Z2 X /\ ~SING e ==> CARD e = 2.
   Note e <> EMPTY                     by involute_orbit_nonempty
     so ?x. x IN e                     by MEMBER_NOT_EMPTY
    and e = orbit (FUNPOW f) Z2 x      by involute_orbits_element_is_orbit
    now x IN X                         by involute_orbits_element_element
    If f x = x,
       then e = {x}                    by involute_orbit_fixed
       thus SING e                     by SING_DEF
       This contradicts ~SING e
    Otherwise, f x <> x.
       then e = {x; f x}               by involute_orbit_not_fixed
         so CARD e = 2                 by CARD_DEF
*)
Theorem involute_multi_orbits_element_card:
  !f X e. f involute X /\
          e IN (multi_orbits (FUNPOW f) Z2 X) ==> CARD e = 2
Proof
  rw[multi_orbits_def] >>
  `?x. x IN e` by metis_tac[involute_orbit_nonempty, MEMBER_NOT_EMPTY] >>
  `e = orbit (FUNPOW f) Z2 x` by metis_tac[involute_orbits_element_is_orbit] >>
  `x IN X` by metis_tac[involute_orbits_element_element] >>
  Cases_on `f x = x` >-
  metis_tac[involute_orbit_fixed, SING_DEF] >>
  `e = {x; f x}` by metis_tac[involute_orbit_not_fixed] >>
  rw[]
QED

(* Theorem: FINITE X /\ f involute X ==>
            CARD X = 2 * CARD (multi_orbits (FUNPOW f) Z2 X) +
                      CARD (fixed_points (FUNPOW f) Z2 X) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 X,
        b = fixed_points (FUNPOW f) Z2 X.
   Then FINITE a                 by funpow_multi_orbits_finite
        CARD X
      = CARD b + SIGMA CARD a    by involute_target_card_eqn
      = CARD b + 2 * CARD a      by SIGMA_CONSTANT, involute_multi_orbits_element_card
      = 2 * CARD a + CARD b      by ADD_COMM
*)
Theorem involute_target_card_thm:
  !f X. FINITE X /\ f involute X ==>
        CARD X = 2 * CARD (multi_orbits (FUNPOW f) Z2 X) +
                 CARD (fixed_points (FUNPOW f) Z2 X)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = multi_orbits (FUNPOW f) Z2 X` >>
  qabbrev_tac `b = fixed_points (FUNPOW f) Z2 X` >>
  `FINITE a` by rw[funpow_multi_orbits_finite, Abbr`a`] >>
  `CARD X = CARD b + SIGMA CARD a` by rw[involute_target_card_eqn, Abbr`a`, Abbr`b`] >>
  `_ = CARD b + 2 * CARD a` by metis_tac[SIGMA_CONSTANT, involute_multi_orbits_element_card] >>
  simp[]
QED

(* Theorem: FINITE X /\ f involute X ==>
            (EVEN (CARD X) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 X))) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 X,
        b = fixed_points (FUNPOW f) Z2 X.
   Note CARD X = 2 * a + CARD b            by involute_target_card_thm
     so EVEN (CARD X) <=> EVEN (CARD b)    by EQ_PARITY
*)
Theorem involute_fixed_points_both_even:
  !f X. FINITE X /\ f involute X ==>
        (EVEN (CARD X) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 X)))
Proof
  metis_tac[involute_target_card_thm, EQ_PARITY]
QED

(* Theorem: FINITE X /\ f involute X ==>
            (ODD (CARD X) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 X))) *)
(* Proof: by involute_fixed_points_both_even, ODD_EVEN. *)
Theorem involute_fixed_points_both_odd:
  !f X. FINITE X /\ f involute X ==>
        (ODD (CARD X) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 X)))
Proof
  rw[involute_fixed_points_both_even, ODD_EVEN]
QED

(* A useful corollary. *)

(* Theorem: FINITE X /\ f involute X /\ g involute X ==>
           (EVEN (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
            EVEN (CARD (fixed_points (FUNPOW g) Z2 X))) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 X,
        b = fixed_points (FUNPOW f) Z2 X,
        c = multi_orbits (FUNPOW g) Z2 X,
        d = fixed_points (FUNPOW g) Z2 X.
   Note EVEN (CARD X) <=> EVEN (CARD b)    by involute_fixed_points_both_even
    and EVEN (CARD X) <=> EVEN (CARD d)    by involute_fixed_points_both_even
   Thus EVEN (CARD b) <=> EVEN (CARD d)
*)
Theorem involute_two_fixed_points_both_even:
  !f g X. FINITE X /\ f involute X /\ g involute X ==>
          (EVEN (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
           EVEN (CARD (fixed_points (FUNPOW g) Z2 X)))
Proof
  metis_tac[involute_fixed_points_both_even]
QED

(* Theorem: FINITE X /\ f involute X /\ g involute X ==>
           (ODD (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
            ODD (CARD (fixed_points (FUNPOW g) Z2 X))) *)
(* Proof: by involute_two_fixed_points_both_even, ODD_EVEN. *)
Theorem involute_two_fixed_points_both_odd:
  !f g X. FINITE X /\ f involute X /\ g involute X ==>
          (ODD (CARD (fixed_points (FUNPOW f) Z2 X)) <=>
           ODD (CARD (fixed_points (FUNPOW g) Z2 X)))
Proof
  rw[involute_two_fixed_points_both_even, ODD_EVEN]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
