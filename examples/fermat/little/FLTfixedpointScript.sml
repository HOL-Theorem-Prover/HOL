(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Combinatorial proof.                            *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Combinatorial proof)
=============================================
Solomon W. Golomb (1956)
http://www.cimat.mx/~mmoreno/teaching/spring08/Fermats_Little_Thm.pdf

Original proof by J. Petersen in 1872:

Take p elements from q with repetitions in all ways, that is, in q^p ways.
The q sets with elements all alike are not changed by a cyclic permutation of the elements,
while the remaining q<sup>p</sup>-q sets are permuted in sets of p. Hence p divides q^p - q.

This is a combinatorial using Group action, via Fixed Points Congruence of Zp.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "FLTfixedpoint";

(* ------------------------------------------------------------------------- *)

(* open dependent theories *)
open arithmeticTheory pred_setTheory dividesTheory numberTheory
     combinatoricsTheory;

open cycleTheory;

(* val _ = load "groupInstancesTheory"; *)
(* val _ = load "groupActionTheory"; *)
open groupTheory;
open groupActionTheory;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Action Documentation                           *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   From groupInstances:
   Zadd_element        |- !n x. x IN (Zadd n).carrier <=> x < n
   Zadd_card           |- !n. CARD (Zadd n).carrier = n
   Zadd_group          |- !n. 0 < n ==> Group (Zadd n)
   Zadd_finite_group   |- !n. 0 < n ==> FiniteGroup (Zadd n)

   From groupAction:
   fixed_points_def        |- !f g X. fixed_points f g X =
                                      {x | x IN X /\ !a. a IN G ==> f a x = x}
   fixed_points_element    |- !f g X x. x IN fixed_points f g X <=>
                                        x IN X /\ !a. a IN G ==> f a x = x
   fixed_points_orbit_sing |- !f g X. Group g /\ (g act X) f ==>
                              !x. x IN fixed_points f g X <=>
                                  x IN X /\ orbit f g x = {x}
   orbit_sing_fixed_points |- !f g X. (g act X) f ==>
                              !x. x IN X /\ orbit f g x = {x} ==>
                                  x IN fixed_points f g X
   fixed_points_orbit_iff_sing
                           |- !f g X. Group g /\ (g act X) f ==>
                              !x. x IN X ==>
                                 (x IN fixed_points f g X <=> SING (orbit f g x))
   sing_orbits_def     |- !f g X. sing_orbits f g X = {e | e IN orbits f g X /\ SING e}
   multi_orbits_def    |- !f g X. multi_orbits f g X = {e | e IN orbits f g X /\ ~SING e}
   sing_orbits_to_fixed_points_inj
                       |- !f g X. Group g /\ (g act X) f ==>
                                  INJ CHOICE (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_to_fixed_points_surj
                       |- !f g X. Group g /\ (g act X) f ==>
                                  SURJ CHOICE (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_to_fixed_points_bij
                       |- !f g X. Group g /\ (g act X) f ==>
                                  BIJ CHOICE (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_card_eqn|- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                  CARD (sing_orbits f g X) = CARD (fixed_points f g X)
   target_card_by_fixed_points
                       |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                  CARD X = CARD (fixed_points f g X) +
                                           SIGMA CARD (multi_orbits f g X)
   target_card_and_fixed_points_congruence
                       |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
                                    (!e. e IN multi_orbits f g X ==> CARD e = n) ==>
                                    CARD X MOD n = CARD (fixed_points f g X) MOD n

   From FLTnecklace:
   monocoloured_cycle_1      |- !n a ls. ls IN monocoloured n a ==> cycle 1 ls = ls
   cycle_1_monocoloured      |- !n a ls. ls IN necklace n a /\ cycle 1 ls = ls ==>
                                         ls IN monocoloured n a
   monocoloured_iff_cycle_1  |- !n a ls. ls IN necklace n a ==>
                                        (ls IN monocoloured n a <=> cycle 1 ls = ls)

   From FLTactionTheory:
   cycle_action_on_necklace  |- !n a. 0 < n ==> (Zadd n act necklace n a) cycle

   Orbits when action group is (Zadd p), for prime p:
   multi_orbit_card_prime
                       |- !p f X e. prime p /\ (Zadd p act X) f /\ FINITE X /\
                                    e IN multi_orbits f (Zadd p) X ==> CARD e = p
   fixedpoint_prime_congruence
                       |- !p f X. prime p /\ (Zadd p act X) f /\ FINITE X ==>
                                  CARD X MOD p = CARD (fixed_points f (Zadd p) X) MOD p
   cycle_fixed_points  |- !n a. fixed_points cycle (Zadd n) (necklace n a) =
                                {ls | ls IN necklace n a /\ cycle 1 ls = ls}
   cycle_fixed_points_monocoloured
                       |- !n a. fixed_points cycle (Zadd n) (necklace n a) = monocoloured n a

   Application:
   fermat_little_thm   |- !p a. prime p ==> a ** p MOD p = a MOD p

*)

(* Part 1: Basic ----------------------------------------------------------- *)

val Zadd_element = groupInstancesTheory.Zadd_element;
(* |- !n x. x IN (Zadd n).carrier <=> x < n *)

val Zadd_card = groupInstancesTheory.Zadd_card;
(* |- !n. CARD (Zadd n).carrier = n *)

val Zadd_group = groupInstancesTheory.Zadd_group;
(* |- !n. 0 < n ==> Group (Zadd n) *)

val Zadd_finite_group = groupInstancesTheory.Zadd_finite_group;
(* |- !n. 0 < n ==> FiniteGroup (Zadd n) *)

(* Part 2: General Theory -------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Theory of necklaces                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Fixed Points of action.                                                   *)
(* ------------------------------------------------------------------------- *)

val fixed_points_def = groupActionTheory.fixed_points_def;
(* |- !f g X. fixed_points f g X = {x | x IN X /\ !a. a IN G ==> f a x = x} *)

val fixed_points_element = groupActionTheory.fixed_points_element;
(* |- !f g X x. x IN fixed_points f g X <=> x IN X /\ !a. a IN G ==> f a x = x *)

val fixed_points_orbit_sing = groupActionTheory.fixed_points_orbit_sing;
(* |- !f g X. Group g /\ (g act X) f ==>
              !x. x IN fixed_points f g X <=> x IN X /\ orbit f g x = {x} *)

val orbit_sing_fixed_points = groupActionTheory.orbit_sing_fixed_points;
(* |- !f g X. (g act X) f ==>
              !x. x IN X /\ orbit f g x = {x} ==> x IN fixed_points f g X *)

val fixed_points_orbit_iff_sing = groupActionTheory.fixed_points_orbit_iff_sing;
(* |- !f g X. Group g /\ (g act X) f ==>
              !x. x IN X ==> (x IN fixed_points f g X <=> SING (orbit f g x)) *)

val sing_orbits_def = groupActionTheory.sing_orbits_def;
(* |- !f g X. sing_orbits f g X = {e | e IN orbits f g X /\ SING e} *)

val multi_orbits_def = groupActionTheory.multi_orbits_def;
(* |- !f g X. multi_orbits f g X = {e | e IN orbits f g X /\ ~SING e} *)

val sing_orbits_to_fixed_points_inj = groupActionTheory.sing_orbits_to_fixed_points_inj;
(* |- !f g X. Group g /\ (g act X) f ==> INJ CHOICE (sing_orbits f g X) (fixed_points f g X) *)

val sing_orbits_to_fixed_points_surj = groupActionTheory.sing_orbits_to_fixed_points_surj;
(* |- !f g X. Group g /\ (g act X) f ==> SURJ CHOICE (sing_orbits f g X) (fixed_points f g X) *)

val sing_orbits_to_fixed_points_bij = groupActionTheory.sing_orbits_to_fixed_points_bij;
(* |- !f g X. Group g /\ (g act X) f ==> BIJ CHOICE (sing_orbits f g X) (fixed_points f g X): *)

val sing_orbits_card_eqn = groupActionTheory.sing_orbits_card_eqn;
(* |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
              CARD (sing_orbits f g X) = CARD (fixed_points f g X) *)

val target_card_by_fixed_points = groupActionTheory.target_card_by_fixed_points;
(* |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
              CARD X = CARD (fixed_points f g X) + SIGMA CARD (multi_orbits f g X) *)

val target_card_and_fixed_points_congruence = groupActionTheory.target_card_and_fixed_points_congruence;
(* |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
                (!e. e IN multi_orbits f g X ==> CARD e = n) ==>
                CARD X MOD n = CARD (fixed_points f g X) MOD n *)

(* ------------------------------------------------------------------------- *)
(* From FLTnecklace.                                                           *)
(* ------------------------------------------------------------------------- *)

val monocoloured_cycle_1 = FLTnecklaceTheory.monocoloured_cycle_1;
(* |- !n a ls. ls IN monocoloured n a ==> cycle 1 ls = ls *)

val cycle_1_monocoloured = FLTnecklaceTheory.cycle_1_monocoloured;
(* |- !n a ls. ls IN necklace n a /\ cycle 1 ls = ls ==> ls IN monocoloured n a *)

val monocoloured_iff_cycle_1 = FLTnecklaceTheory.monocoloured_iff_cycle_1;
(* |- !n a ls. ls IN necklace n a ==> (ls IN monocoloured n a <=> cycle 1 ls = ls) *)

(* ------------------------------------------------------------------------- *)
(* From FLTaction.                                                           *)
(* ------------------------------------------------------------------------- *)

val cycle_action_on_necklace = FLTactionTheory.cycle_action_on_necklace;
(* |- !n a. 0 < n ==> (Zadd n act necklace n a) cycle *)

(* Part 3: Actual Proof ---------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Combinatorial Proof via Group action.                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Orbits when action group is (Zadd p), for prime p.                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p /\ (Zadd p act X) f /\ FINITE X /\
            e IN (multi_orbits f (Zadd p) X) ==> CARD e = p *)
(* Proof:
   Note 0 < p                        by PRIME_POS
     so FiniteGroup (Zadd p)         by Zadd_finite_group, 0 < p
    and CARD (Zadd p).carrier = p    by Zadd_card
   Also FINITE e                     by orbits_element_finite
     so CARD e <> 1                  by SING_IFF_CARD1, FINITE e
   Thus ?x. x IN X /\
        e = orbit f (Zadd p) x       by orbits_element
    ==> CARD e divides p             by orbit_card_divides_target_card
   Hence CARD e = p                  by prime_def, CARD e <> 1
*)
Theorem multi_orbit_card_prime:
  !p f X e. prime p /\ (Zadd p act X) f /\ FINITE X /\
            e IN (multi_orbits f (Zadd p) X) ==> CARD e = p
Proof
  rw[multi_orbits_def] >>
  `0 < p` by rw[PRIME_POS] >>
  `FiniteGroup (Zadd p)` by rw[Zadd_finite_group] >>
  `CARD (Zadd p).carrier = p` by rw[Zadd_card] >>
  `FINITE e` by metis_tac[orbits_element_finite] >>
  `CARD e <> 1` by fs[SING_IFF_CARD1] >>
  `CARD e divides p` by metis_tac[orbits_element, orbit_card_divides_target_card] >>
  metis_tac[prime_def]
QED

(* Idea: (Fermat's Little Theorem by Group action)
         for prime p, a ** p = a (mod p). *)

(* Theorem: prime p /\ (Zadd p act X) f /\ FINITE A ==>
            CARD X MOD p = CARD (fixed_points f (Zadd p) X) MOD p *)
(* Proof:
   Let b = multi_orbits f (Zadd p) X,
       s = fixed_points f (Zadd p) X.
   Note 0 < p                            by PRIME_POS
   Then Group (Zadd p)                   by Zadd_group, 0 < p
    and !e. e IN b ==> CARD e = p        by multi_orbit_card_prime
   Thus CARD A MOD p = CARD s MOD p      by target_card_and_fixed_points_congruence

> target_card_and_fixed_points_congruence |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !X n. Group (Zadd p) /\ (Zadd p act X) cycle /\ FINITE X /\ 0 < n /\
          (!e. e IN multi_orbits cycle (Zadd p) X ==> CARD e = n) ==>
          CARD X MOD n = CARD (fixed_points cycle (Zadd p) X) MOD n: thm
*)
Theorem fixedpoint_prime_congruence:
  !p f X. prime p /\ (Zadd p act X) f /\ FINITE X ==>
          CARD X MOD p = CARD (fixed_points f (Zadd p) X) MOD p
Proof
  rpt strip_tac >>
  qabbrev_tac `g = Zadd p` >>
  `0 < p` by rw[PRIME_POS] >>
  `Group g` by rw[Zadd_group, Abbr`g`] >>
  `!e. e IN (multi_orbits f g X) ==> CARD e = p` by metis_tac[multi_orbit_card_prime] >>
  imp_res_tac target_card_and_fixed_points_congruence
QED

(* ------------------------------------------------------------------------- *)
(* Fixed Points of cycle are monocoloured necklaces.                         *)
(* ------------------------------------------------------------------------- *)

(* Idea: the fixed_points of cycle are necklaces of cycle 1 ls = ls. *)

(* Theorem: fixed_points cycle (Zadd n) (necklace n a) =
            {ls | ls IN (necklace n a) /\ cycle 1 ls = ls} *)
(* Proof:
   By fixed_points_def, Zadd_element, EXTENSION, this is to show:
   (1) x IN necklace n a /\ !a. a < n ==> (cycle a x = x) ==> cycle 1 x = x
       If n = 0,
          Note necklace 0 a = {[]}           by necklace_0
            so x = []                        by IN_SING
           and cycle 1 [] = []               by cycle_nil
       If n = 1,
          Then LENGTH x = 1                  by necklace_length
            so cycle 1 x = x                 by cycle_back
       Otherwise, 1 < n, so cycle 1 x = x    by implication
   (2) cycle 1 x = x /\ b < n ==> cycle b x = x
       This is true                          by cycle_1_fix
*)
Theorem cycle_fixed_points:
  !n a. fixed_points cycle (Zadd n) (necklace n a) =
        {ls | ls IN (necklace n a) /\ cycle 1 ls = ls}
Proof
  rw[fixed_points_def, Zadd_element, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    Cases_on `n = 0` >-
    fs[necklace_0, cycle_nil] >>
    Cases_on `n = 1` >-
    metis_tac[necklace_length, cycle_back] >>
    fs[],
    simp[cycle_1_fix]
  ]
QED

(* Idea: the fixed_points of cycle are monocoloured necklaces. *)

(* Theorem: fixed_points cycle (Zadd n) (necklace n a) = monocoloured n a *)
(* Proof:
     fixed_points cycle (Zadd n) (necklace n a)
   = {ls | ls IN (necklace n a) /\ cycle 1 ls = ls}   by cycle_fixed_points
   = monocoloured n a      by monocoloured_necklace, monocoloured_iff_cycle_1
*)
Theorem cycle_fixed_points_monocoloured:
  !n a. fixed_points cycle (Zadd n) (necklace n a) = monocoloured n a
Proof
  simp[cycle_fixed_points] >>
  rw[EXTENSION] >>
  metis_tac[monocoloured_necklace, monocoloured_iff_cycle_1]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (by Z^{*}[p] multiplicative group)                *)
(* ------------------------------------------------------------------------- *)

(* Idea: (Fermat's Little Theorem by Group action)
         for prime p, a ** p = a (mod p). *)

(* Theorem: prime p ==> a ** p MOD p = a MOD p *)
(* Proof:
   Let X = necklace p a,
       b = multi_orbits cycle (Zadd p) X,
       c = fixed_points cycle (Zadd p) X.
   Note FINITE X                         by necklace_finite
    and 0 < p                            by PRIME_POS
     so Group (Zadd p)                   by Zadd_group, 0 < p
    and (Zadd p act X) cycle             by cycle_action_on_necklace, 0 < p
   Also !e. e IN b ==> CARD e = p        by multi_orbit_card_prime
        (a ** p) MOD p
      = (CARD A) MOD p                   by necklace_card
      = (CARD c) MOD p                   by target_card_and_fixed_points_congruence
      = (CARD (monocoloured p a)) MOD p  by cycle_fixed_points_monocoloured
      = a MOD p                          by monocoloured_card

multi_orbit_card_prime |> ISPEC ``p:num`` |> ISPEC ``cycle``;
|- !X e. prime p /\ (Zadd p act X) cycle /\ FINITE X /\
         e IN multi_orbits cycle (Zadd p) X ==>
         CARD e = p

target_card_and_fixed_points_congruence |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !X n. Group (Zadd p) /\ (Zadd p act X) cycle /\ FINITE X /\ 0 < n /\
         (!e. e IN multi_orbits cycle (Zadd p) X ==> CARD e = n) ==>
         CARD X MOD n = CARD (fixed_points cycle (Zadd p) X) MOD n
*)
Theorem fermat_little_thm:
  !p a. prime p ==> a ** p MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `X = necklace p a` >>
  `FINITE X` by rw[necklace_finite, Abbr`X`] >>
  `Group (Zadd p)` by rw[Zadd_group] >>
  `(Zadd p act X) cycle` by rw[cycle_action_on_necklace, Abbr`X`] >>
  `!e. e IN multi_orbits cycle (Zadd p) X ==> CARD e = p` by metis_tac[multi_orbit_card_prime] >>
  `CARD X = a ** p` by rw[necklace_card, Abbr`X`] >>
  `CARD (fixed_points cycle (Zadd p) X) = CARD (monocoloured p a)` by rw[cycle_fixed_points_monocoloured, Abbr`X`] >>
  `_ = a` by rw[monocoloured_card] >>
  metis_tac[target_card_and_fixed_points_congruence]
QED

(* Another proof using fixedpoint_prime_congruence. *)

(* Theorem: prime p ==> a ** p MOD p = a MOD p *)
(* Proof:
   Let X = necklace p a,
       b = multi_orbits cycle (Zadd p) X,
       c = fixed_points cycle (Zadd p) X.
   Note FINITE X                         by necklace_finite
    and 0 < p                            by PRIME_POS
     so (Zadd p act X) cycle             by cycle_action_on_necklace, 0 < p

        (a ** p) MOD p
      = (CARD A) MOD p                   by necklace_card
      = (CARD c) MOD p                   by fixedpoint_prime_congruence
      = (CARD (monocoloured p a)) MOD p  by cycle_fixed_points_monocoloured
      = a MOD p                          by monocoloured_card

fixedpoint_prime_congruence |> ISPEC ``p:num`` |> ISPEC ``cycle``;
|- !X. prime p /\ (Zadd p act X) cycle /\ FINITE X ==>
       CARD X MOD p = CARD (fixed_points cycle (Zadd p) X) MOD p
*)
Theorem fermat_little_thm[allow_rebind]:
  !p a. prime p ==> a ** p MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `X = necklace p a` >>
  `FINITE X` by rw[necklace_finite, Abbr`X`] >>
  `(Zadd p act X) cycle` by rw[cycle_action_on_necklace, Abbr`X`] >>
  `CARD X = a ** p` by rw[necklace_card, Abbr`X`] >>
  `CARD (fixed_points cycle (Zadd p) X) = CARD (monocoloured p a)` by rw[cycle_fixed_points_monocoloured, Abbr`X`] >>
  `_ = a` by rw[monocoloured_card] >>
  metis_tac[fixedpoint_prime_congruence]
QED

(* Part 4: End ------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
