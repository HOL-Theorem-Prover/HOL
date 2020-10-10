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

(* val _ = load "helperTheory"; *)
open helperTheory;
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
(*

   Helper Theorems:
   involute_permutes
                   |- !f A. f involute A ==> f PERMUTES A

   FUNPOW Action:
   funpow_action   |- !f A. f involute A ==> (Z2 act A) (FUNPOW f)
   funpow_reach    |- !f a b. reach (FUNPOW f) Z2 a b <=> ?x. x < 2 /\ FUNPOW f x a = b
   funpow_equiv    |- !f A. f involute A ==> reach (FUNPOW f) Z2 equiv_on A

   FUNPOW Orbits:
   funpow_orbits   |- !f A. orbits (FUNPOW f) Z2 A = IMAGE (orbit (FUNPOW f) Z2) A
   funpow_orbit    |- !f A x. orbit (FUNPOW f) Z2 x = {FUNPOW f a x | a < 2}
   funpow_orbit_alt|- !f A x. orbit (FUNPOW f) Z2 x = IMAGE (\a. FUNPOW f a x) (count 2)
   funpow_orbit_element
                   |- !f a b. b IN orbit (FUNPOW f) Z2 a <=> ?x. x < 2 /\ FUNPOW f x a = b
   funpow_orbit_in_orbits
                   |- !f A a. a IN A ==> orbit (FUNPOW f) Z2 a IN orbits (FUNPOW f) Z2 A
   funpow_orbit_finite
                   |- !f a. FINITE (orbit (FUNPOW f) Z2 a)
   funpow_orbits_finite
                   |- !f A. FINITE A ==> FINITE (orbits (FUNPOW f) Z2 A)
   funpow_multi_orbits_finite
                   |- !f A. FINITE A ==> FINITE (multi_orbits (FUNPOW f) Z2 A)

   Involution Orbits:
   involute_orbit_element
                   |- !f A a b. f involute A /\ a IN A /\
                                b IN orbit (FUNPOW f) Z2 a ==> b = a \/ b = f a
   involute_orbit_has_self
                   |- !f A a. f involute A /\ a IN A ==> a IN orbit (FUNPOW f) Z2 a
   involute_orbit_has_funpow
                   |- !f A a n. f involute A /\ a IN A /\ n < 2 ==>
                                FUNPOW f n a IN orbit (FUNPOW f) Z2 a
   involute_orbit_has_image
                   |- !f A a. f involute A /\ a IN A ==> f a IN orbit (FUNPOW f) Z2 a
   involute_orbit_nonempty
                   |- !f A e. f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> {}
   involute_orbits_element_is_orbit
                   |- !f A e a. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\
                                a IN e ==> e = orbit (FUNPOW f) Z2 a
   involute_orbits_element_element
                   |- !f A e a. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\
                                a IN e ==> a IN A

   Involution fixed points:
   involute_fixed_points
                   |- !f A a. f involute A /\
                              a IN fixed_points (FUNPOW f) Z2 A ==> f a = a
   involute_fixed_points_iff
                   |- !f A a. f involute A /\ a IN A ==>
                             (a IN fixed_points (FUNPOW f) Z2 A <=> f a = a)
   involute_fixed_points_element_element
                   |- !f A a. a IN fixed_points (FUNPOW f) Z2 A ==> a IN A

   Involution Target Cardinality:
   involute_target_card_by_types
                   |- !f A. FINITE A /\ f involute A ==>
                           (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))
   involute_target_card_eqn
                   |- !f A. FINITE A /\ f involute A ==>
                           (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                                     SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))
   involute_orbit_fixed
                   |- !f A a. f involute A /\ a IN A /\ f a = a ==>
                                orbit (FUNPOW f) Z2 a = {a}
   involute_orbit_not_fixed
                   |- !f A a. f involute A /\ a IN A /\ f a <> a ==>
                                orbit (FUNPOW f) Z2 a = {a; f a}
   involute_multi_orbits_element_card
                   |- !f A e. f involute A /\
                              e IN multi_orbits (FUNPOW f) Z2 A ==> CARD e = 2
   involute_target_card_thm
                   |- !f A. FINITE A /\ f involute A ==>
                            CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                                     CARD (fixed_points (FUNPOW f) Z2 A)
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

(* Theorem alias *)
val involute_permutes = save_thm("involute_permutes",
    involute_bij |> SPEC ``f:'a -> 'a`` |> SPEC ``A:'a -> bool`` |> GEN_ALL);
(* val involute_permutes = |- !f A. f involute A ==> f PERMUTES A: thm *)

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

(* Theorem: f involute A ==> (Z2 act A) (FUNPOW f) *)
(* Proof:
   By action_def, Zadd_property, this is to show:
   (1) a IN A /\ x < 2 ==> FUNPOW f x a IN A
       Note f PERMUTES A              by involute_permutes
         so FUNPOW f x a IN A         by FUNPOW_closure
   (2) a IN A /\ x < 2 /\ y < 2 ==>
       FUNPOW f x (FUNPOW f y a) = FUNPOW f ((x + y) MOD 2) a
       Note FUNPOW f x (FUNPOW f y a)
          = FUNPOW f (x + y) a        by FUNPOW_ADD
       If x = 0, y = 0, x + y = 0 = 0 MOD 2.
       If x = 0, y = 1, x + y = 1 = 1 MOD 2.
       If x = 1, y = 0, x + y = 1 = 1 MOD 2.
       If x = 1, y = 1, x + y = 2.  2 MOD 2 = 0.
       The goal becomes: FUNPOW f 2 a = a
        But FUNPOW f 2 a
          = f (f a)                   by FUNPOW_2
          = a                         by f involute A
          = FUNPOW f 0 a              by FUNPOW_0
*)
Theorem funpow_action:
  !f A. f involute A ==> (Z2 act A) (FUNPOW f)
Proof
  rw[action_def, Zadd_property] >-
  rw[involute_permutes, FUNPOW_closure] >>
  `FUNPOW f x (FUNPOW f y a) = FUNPOW f (x + y) a` by rw[FUNPOW_ADD] >>
  (`(x = 0 \/ x = 1) /\ (y = 0 \/ y = 1)` by decide_tac >> simp[]) >>
  simp[FUNPOW_2]
QED

(* Adapt the general theory of group action to (FUNPOW f). *)
(* Note: Eventually, A = mills n, a set of triples (x,y,z), f = zagier or f = flip. *)

(* Extract theorems *)

val funpow_reach = save_thm("funpow_reach",
   reach_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
             |> REWRITE_RULE[Zadd_property] |> GEN_ALL
);
(* val funpow_reach =
|- !f a b. reach (FUNPOW f) Z2 a b <=> ?x. x < 2 /\ FUNPOW f x a = b: thm *)

val funpow_equiv = save_thm("funpow_equiv",
   reach_equiv |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_equiv =
|- !f A. Group Z2 /\ (Z2 act A) (FUNPOW f) ==> reach (FUNPOW f) Z2 equiv_on A: thm *)

(* A better version *)

(* Theorem: f involute A ==> reach (FUNPOW f) Z2 equiv_on A *)
(* Proof:
   Note Group Z2                         by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus reach (FUNPOW f) Z2 equiv_on A   by reach_equiv
*)
Theorem funpow_equiv:
  !f A. f involute A ==> reach (FUNPOW f) Z2 equiv_on A
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
|- !f A. orbits (FUNPOW f) Z2 A = IMAGE (orbit (FUNPOW f) Z2) A *)

val funpow_orbit = save_thm("funpow_orbit",
   orbit_def |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
             |> REWRITE_RULE[Zadd_carrier] |> GEN_ALL
);
(* val funpow_orbit =
|- !f a. orbit (FUNPOW f) Z2 a = IMAGE (\x. FUNPOW f x a) (count 2): thm *)

val funpow_orbit_element = save_thm("funpow_orbit_element",
   orbit_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2``
                 |> SIMP_RULE (srw_ss()) [reach_def, Zadd_carrier] |> GEN_ALL
);
(* val funpow_orbit_element =
|- !f a b. b IN orbit (FUNPOW f) Z2 a <=> ?x. x < 2 /\ FUNPOW f x a = b: thm *)

val funpow_orbit_in_orbits = save_thm("funpow_orbit_in_orbits",
   orbit_is_orbits_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_orbit_in_orbits =
|- !f A a. a IN A ==> orbit (FUNPOW f) Z2 a IN orbits (FUNPOW f) Z2 A: thm *)

(* Theorem: FINITE (orbit (FUNPOW f) Z2 a) *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 a.
   Note Z2.carrier = count 2      by Zadd_carrier
    and FINITE (count 2)          by FINITE_COUNT
     so FINITE b                  by orbit_finite
*)
Theorem funpow_orbit_finite:
  !f a. FINITE (orbit (FUNPOW f) Z2 a)
Proof
  simp[Zadd_carrier, orbit_finite]
QED

val funpow_orbits_finite = save_thm("funpow_orbits_finite",
    orbits_finite |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_orbits_finite =
|- !f A. FINITE A ==> FINITE (orbits (FUNPOW f) Z2 A): thm *)

val funpow_multi_orbits_finite = save_thm("funpow_multi_orbits_finite",
    multi_orbits_finite |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val funpow_multi_orbits_finite =
|- !f A. FINITE A ==> FINITE (multi_orbits (FUNPOW f) Z2 A): thm *)

(* ------------------------------------------------------------------------- *)
(* Involution Orbits                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute A /\ a IN A /\
            b IN (orbit (FUNPOW f) Z2 a) ==> ((b = a) \/ (b = f a)) *)
(* Proof:
   Note ?x. x < 2 /\ FUNPOW f x a = b    by funpow_orbit_element
   When n = 0, y = FUNPOW f 0 x = x      by FUNPOW_0
   When n = 1, y = FUNPOW f 1 x = f x    by FUNPOW_1
*)
Theorem involute_orbit_element:
  !f A a b. f involute A /\ a IN A /\
            b IN (orbit (FUNPOW f) Z2 a) ==> ((b = a) \/ (b = f a))
Proof
  rpt strip_tac >>
  imp_res_tac funpow_orbit_element >>
  (`x = 0 \/ x = 1` by decide_tac >> fs[])
QED

(* Theorem: f involute A /\ a IN A ==> a IN orbit (FUNPOW f) Z2 a *)
(* Proof:
   Note Group Z2                       by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)          by funpow_action
   Thus a IN orbit (FUNPOW f) Z2 a     by orbit_has_self
*)
Theorem involute_orbit_has_self:
  !f A a. f involute A /\ a IN A ==> a IN orbit (FUNPOW f) Z2 a
Proof
  metis_tac[Zadd_group, funpow_action, orbit_has_self, DECIDE``0 < 2``]
QED

(* Theorem: f involute A /\ a IN A /\ n < 2 ==>
            (FUNPOW f n a) IN orbit (FUNPOW f) Z2 a *)
(* Proof:
   Note Group Z2                        by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)           by funpow_action
    and n IN Z2.carrier                 by Zadd_element, n < 2
   Thus (FUNPOW f n a) IN orbit (FUNPOW f) Z2 a
                                        by orbit_has_action_element
*)
Theorem involute_orbit_has_funpow:
  !f A a n. f involute A /\ a IN A /\ n < 2 ==>
            (FUNPOW f n a) IN orbit (FUNPOW f) Z2 a
Proof
  rw[Zadd_group, funpow_action, orbit_has_action_element, Zadd_element]
QED

(* Theorem: f involute A /\ a IN A ==> f a IN orbit (FUNPOW f) Z2 a *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 a.
   Note (FUNPOW f 1 a) IN b    by involute_orbit_has_funpow
    and FUNPOW f 1 a = f a     by FUNPOW_1
*)
Theorem involute_orbit_has_image:
  !f A a. f involute A /\ a IN A ==> f a IN orbit (FUNPOW f) Z2 a
Proof
  metis_tac[involute_orbit_has_funpow, FUNPOW_1, DECIDE``1 < 2``]
QED

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> EMPTY *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 A.
   Note Group Z2                   by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)      by funpow_action
   Thus e IN B ==> e <> EMPTY      by orbits_element_nonempty
*)
Theorem involute_orbit_nonempty:
  !f A e. f involute A /\ e IN orbits (FUNPOW f) Z2 A ==> e <> EMPTY
Proof
  metis_tac[Zadd_group, funpow_action, orbits_element_nonempty, DECIDE``0 < 2``]
QED

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ a IN e ==>
            e = orbit (FUNPOW f) Z2 a *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 A.
   Note Group Z2                     by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)        by funpow_action
   Thus e = orbit (FUNPOW f) Z2 a    by orbits_element_is_orbit
*)
Theorem involute_orbits_element_is_orbit:
  !f A e a. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ a IN e ==>
            e = orbit (FUNPOW f) Z2 a
Proof
  metis_tac[Zadd_group, funpow_action, orbits_element_is_orbit, DECIDE``0 < 2``]
QED

(* Theorem: f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ a IN e ==> a IN A *)
(* Proof:
   Let B = orbits (FUNPOW f) Z2 A.
   Note (Z2 act A) (FUNPOW f)      by funpow_action
   Thus a IN A                     by orbits_element_element
*)
Theorem involute_orbits_element_element:
  !f A e a. f involute A /\ e IN orbits (FUNPOW f) Z2 A /\ a IN e ==> a IN A
Proof
  metis_tac[funpow_action, orbits_element_element]
QED

(* ------------------------------------------------------------------------- *)
(* Involution fixed points                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute A /\ a IN fixed_points (FUNPOW f) Z2 A ==> (f a = a) *)
(* Proof:
   Note 1 IN Z2.carrier    by Zadd_element, 1 < 2
     f a
   = FUNPOW f 1 a          by FUNPOW_1
   = a                     by fixed_points_element
*)
Theorem involute_fixed_points:
  !f A a. f involute A /\ a IN fixed_points (FUNPOW f) Z2 A ==> (f a = a)
Proof
  rw[fixed_points_element, Zadd_element] >>
  metis_tac[FUNPOW_1, DECIDE``1 < 2``]
QED

(* Theorem: f involute A /\ a IN A ==>
            (a IN fixed_points (FUNPOW f) Z2 A <=> f a = a) *)
(* Proof:
   By fixed_points_element, this is to show:
   If part: a IN A /\ !x. x < 2 /\ FUNPOW f x a = a ==> f a = a
      Since f a = FUNPOW 1 a               by FUNPOW_1
         so f a = a                        by implication
   Only-if part: a IN A /\ f a = a ==> !x. x < 2 ==> FUNPOW f x a = a
      When x = 0, FUNPOW f 0 a = a         by FUNPOW_0
      When x = 1, FUNPOW f 1 a = f a = a   by f involute A
*)
Theorem involute_fixed_points_iff:
  !f A a. f involute A /\ a IN A ==>
          (a IN fixed_points (FUNPOW f) Z2 A <=> f a = a)
Proof
  rw[fixed_points_element, Zadd_element, EQ_IMP_THM] >-
  metis_tac[FUNPOW_1, DECIDE``1 < 2``] >>
  (`x = 0 \/ x = 1` by decide_tac >> simp[])
QED

val involute_fixed_points_element_element =
    save_thm("involute_fixed_points_element_element",
    fixed_points_element_element |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val involute_fixed_points_element_element =
|- !f A a. a IN fixed_points (FUNPOW f) Z2 A ==> a IN A: thm *)

(* ------------------------------------------------------------------------- *)
(* Involution Target Cardinality                                             *)
(* ------------------------------------------------------------------------- *)

val involute_target_card_by_types = save_thm("involute_target_card_by_types",
    target_card_by_orbit_types |> ISPEC ``FUNPOW f`` |> ISPEC ``Z2`` |> GEN_ALL
);
(* val involute_target_card_by_types =
|- !f A. Group Z2 /\ (Z2 act A) (FUNPOW f) /\ FINITE A ==>
         CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                  SIGMA CARD (multi_orbits (FUNPOW f) Z2 A): thm *)

(* A better version *)

(* Theorem: FINITE A /\ f involute A ==>
            (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)) *)
(* Proof:
   Note Group Z2                         by Zadd_group, 0 < 2
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)
                                         by target_card_by_orbit_types
*)
Theorem involute_target_card_by_types:
  !f A. FINITE A /\ f involute A ==>
        (CARD A = CARD (sing_orbits (FUNPOW f) Z2 A) +
                  SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))
Proof
  simp[Zadd_group, funpow_action, target_card_by_orbit_types]
QED

(* Theorem: FINITE A /\ f involute A ==>
            (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)) *)
(* Proof:
   Note Group Z2                         by Zadd_group
    and (Z2 act A) (FUNPOW f)            by funpow_action
   Thus CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                      SIGMA CARD (multi_orbits (FUNPOW f) Z2 A)
                                         by target_card_by_fixed_points
*)
Theorem involute_target_card_eqn:
  !f A. FINITE A /\ f involute A ==>
        (CARD A = CARD (fixed_points (FUNPOW f) Z2 A) +
                  SIGMA CARD (multi_orbits (FUNPOW f) Z2 A))
Proof
  simp[Zadd_group, funpow_action, target_card_by_fixed_points]
QED

(* This will be very useful! *)

(* Theorem: f involute A /\ a IN A /\ (f a = a) ==>
            orbit (FUNPOW f) Z2 a = {a} *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 a.
   Note x IN b                   by involute_orbit_has_self
    and !b. b IN A ==> (b = a)   by involute_orbit_element, f a = a.
   Thus b = {a}                  by EXTENSION
*)
Theorem involute_orbit_fixed:
  !f A a. f involute A /\ a IN A /\ (f a = a) ==>
          orbit (FUNPOW f) Z2 a = {a}
Proof
  rw[EXTENSION] >>
  metis_tac[involute_orbit_has_self, involute_orbit_element]
QED

(* Theorem: f involute A /\ a IN A /\ (f a <> a) ==>
            orbit (FUNPOW f) Z2 a = {a; f a} *)
(* Proof:
   Let b = orbit (FUNPOW f) Z2 a.
   Note a IN b                   by involute_orbit_has_self
    and f a IN b                 by involute_orbit_has_image
    and !c. c IN A ==> (c = a) \/ (c = f a)
                                 by involute_orbit_element, f a <> a.
   Thus b = {a; f a}             by EXTENSION
*)
Theorem involute_orbit_not_fixed:
  !f A a. f involute A /\ a IN A /\ (f a <> a) ==>
          orbit (FUNPOW f) Z2 a = {a; f a}
Proof
  rw[EXTENSION] >>
  imp_res_tac involute_orbit_has_self >>
  metis_tac[involute_orbit_has_image, involute_orbit_element]
QED

(* Theorem: f involute A /\
            e IN (multi_orbits (FUNPOW f) Z2 A) ==> CARD e = 2 *)
(* Proof:
   By multi_orbits_def, this is to show:
   !e. e IN orbits (FUNPOW f) Z2 A /\ ~SING e ==> CARD e = 2.
   Note e <> EMPTY                     by involute_orbit_nonempty
     so ?a. a IN e                     by MEMBER_NOT_EMPTY
    and e = orbit (FUNPOW f) Z2 a      by involute_orbits_element_is_orbit
    now a IN A                         by involute_orbits_element_element
    If f a = a,
       then e = {a}                    by involute_orbit_fixed
       thus SING e                     by SING_DEF
       This contradicts ~SING e
    Otherwise, f a <> a.
       then e = {a; f a}               by involute_orbit_not_fixed
         so CARD e = 2                 by CARD_DEF
*)
Theorem involute_multi_orbits_element_card:
  !f A e. f involute A /\
          e IN (multi_orbits (FUNPOW f) Z2 A) ==> CARD e = 2
Proof
  rw[multi_orbits_def] >>
  `?a. a IN e` by metis_tac[involute_orbit_nonempty, MEMBER_NOT_EMPTY] >>
  `e = orbit (FUNPOW f) Z2 a` by metis_tac[involute_orbits_element_is_orbit] >>
  `a IN A` by metis_tac[involute_orbits_element_element] >>
  Cases_on `f a = a` >-
  metis_tac[involute_orbit_fixed, SING_DEF] >>
  `e = {a; f a}` by metis_tac[involute_orbit_not_fixed] >>
  rw[]
QED

(* Theorem: FINITE A /\ f involute A ==>
            CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                      CARD (fixed_points (FUNPOW f) Z2 A) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 A,
        b = fixed_points (FUNPOW f) Z2 A.
   Then FINITE a                 by funpow_multi_orbits_finite
        CARD A
      = CARD b + SIGMA CARD a    by involute_target_card_eqn
      = CARD b + 2 * CARD a      by SIGMA_CONSTANT, involute_multi_orbits_element_card
      = 2 * CARD a + CARD b      by ADD_COMM
*)
Theorem involute_target_card_thm:
  !f A. FINITE A /\ f involute A ==>
        CARD A = 2 * CARD (multi_orbits (FUNPOW f) Z2 A) +
                 CARD (fixed_points (FUNPOW f) Z2 A)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = multi_orbits (FUNPOW f) Z2 A` >>
  qabbrev_tac `b = fixed_points (FUNPOW f) Z2 A` >>
  `FINITE a` by rw[funpow_multi_orbits_finite, Abbr`a`] >>
  `CARD A = CARD b + SIGMA CARD a` by rw[involute_target_card_eqn, Abbr`a`, Abbr`b`] >>
  `_ = CARD b + 2 * CARD a` by metis_tac[SIGMA_CONSTANT, involute_multi_orbits_element_card] >>
  simp[]
QED

(* Theorem: FINITE A /\ f involute A ==>
            (EVEN (CARD A) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 A))) *)
(* Proof:
    Let a = multi_orbits (FUNPOW f) Z2 A,
        b = fixed_points (FUNPOW f) Z2 A.
   Note CARD A = 2 * a + CARD b            by involute_target_card_thm
     so EVEN (CARD A) <=> EVEN (CARD b)    by EQ_PARITY
*)
Theorem involute_fixed_points_both_even:
  !f A. FINITE A /\ f involute A ==>
        (EVEN (CARD A) <=> EVEN (CARD (fixed_points (FUNPOW f) Z2 A)))
Proof
  metis_tac[involute_target_card_thm, EQ_PARITY]
QED

(* Theorem: FINITE A /\ f involute A ==>
            (ODD (CARD A) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 A))) *)
(* Proof: by involute_fixed_points_both_even, ODD_EVEN. *)
Theorem involute_fixed_points_both_odd:
  !f A. FINITE A /\ f involute A ==>
        (ODD (CARD A) <=> ODD (CARD (fixed_points (FUNPOW f) Z2 A)))
Proof
  rw[involute_fixed_points_both_even, ODD_EVEN]
QED

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
Theorem involute_two_fixed_points_both_even:
  !f g A. FINITE A /\ f involute A /\ g involute A ==>
          (EVEN (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
           EVEN (CARD (fixed_points (FUNPOW g) Z2 A)))
Proof
  metis_tac[involute_fixed_points_both_even]
QED

(* Theorem: FINITE A /\ f involute A /\ g involute A ==>
           (ODD (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
            ODD (CARD (fixed_points (FUNPOW g) Z2 A))) *)
(* Proof: by involute_two_fixed_points_both_even, ODD_EVEN. *)
Theorem involute_two_fixed_points_both_odd:
  !f g A. FINITE A /\ f involute A /\ g involute A ==>
          (ODD (CARD (fixed_points (FUNPOW f) Z2 A)) <=>
           ODD (CARD (fixed_points (FUNPOW g) Z2 A)))
Proof
  rw[involute_two_fixed_points_both_even, ODD_EVEN]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
