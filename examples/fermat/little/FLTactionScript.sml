(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Group Action proof.                             *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Combinatorial proof)
=============================================
Solomon W. Golomb (1956)
http://www.cimat.mx/~mmoreno/teaching/spring08/Fermats_Little_Thm.pdf

Original proof by Julius Petersen in 1872:

Take p elements from q with repetitions in all ways,
that is, in q^p ways. The q sets with elements all alike
are not changed by a cyclic permutation of the elements,
while the remaining q<sup>p</sup>-q sets are permuted
in sets of p. Hence p divides q^p - q.

This proof uses Group action of Zp on multicoloured necklaces.
The Necklace Theorem by Orbit-Stabilizer Theorem, then
Fermat's Little Theorem follows from Necklace Theorem.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "FLTaction";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* val _ = load "FLTnecklaceTheory"; *)
open helperNumTheory helperSetTheory;
open arithmeticTheory pred_setTheory;
open helperFunctionTheory; (* for prime_power_divisor, PRIME_EXP_FACTOR *)

open cycleTheory;
open necklaceTheory;

(* val _ = load "groupInstancesTheory"; *)
(* val _ = load "groupActionTheory"; *)
open groupTheory;
open groupActionTheory;

open dividesTheory; (* for divides_def, prime_def *)


(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Action Documentation                           *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(*

   From groupInstances:
   Zadd_def          |- !n. Zadd n = <|carrier := count n;
                                            id := 0;
                                            op := (\i j. (i + j) MOD n)|>
   Zadd_element      |- !n x. x IN (Zadd n).carrier <=> x < n
   Zadd_id           |- !n. (Zadd n).id = 0
   Zadd_group        |- !n. 0 < n ==> Group (Zadd n)
   Zadd_finite       |- !n. FINITE (Zadd n).carrier
   Zadd_finite_group |- !n. 0 < n ==> FiniteGroup (Zadd n)
   Zadd_card         |- !n. CARD (Zadd n).carrier = n
   Zadd_exp          |- !n. 0 < n ==> !x m. (Zadd n).exp x m = (x * m) MOD n

   From FLTnecklace:
   necklace_cycle      |- !n a ls k. ls IN necklace n a ==>
                                     cycle k ls IN necklace n a
   multicoloured_cycle |- !n a ls k. ls IN multicoloured n a ==>
                                     cycle k ls IN multicoloured n a
   multicoloured_not_cycle_1
                       |- !n a ls. ls IN multicoloured n a ==> cycle 1 ls <> ls
   monocoloured_cycle  |- !n a ls k. ls IN monocoloured n a ==>
                                     cycle k ls IN monocoloured n a
   monocoloured_cycle_1|- !n a ls. ls IN monocoloured n a ==> (cycle 1 ls = ls)
   cycle_1_monocoloured|- !n a ls. ls IN necklace n a /\ (cycle 1 ls = ls) ==>
                                   ls IN monocoloured n a
   monocoloured_iff_cycle_1
                       |- !n a ls. ls IN necklace n a ==>
                                  (ls IN monocoloured n a <=> (cycle 1 ls = ls))

   Cycle action on Necklaces:
   cycle_action_on_necklace
                       |- !n a. 0 < n ==> (Zadd n act necklace n a) cycle
   cycle_orbit_element |- !n a ls x. x IN orbit cycle (Zadd n) (necklace n a) ls <=>
                                     ?k. k < n /\ (x = cycle k ls)
   cycle_orbit_finite  |- !n a ls. FINITE (orbit cycle (Zadd n) (necklace n a) ls)
   cycle_orbit_card_divides_length
                       |- !n a ls. 0 < n /\ ls IN necklace n a ==>
                                   CARD (orbit cycle (Zadd n) (necklace n a) ls) divides n
   cycle_orbit_card_divides_length_prime
                       |- !p a ls. prime p /\ ls IN necklace p a ==>
                                  (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1) \/
                                  (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p)

   Cycle action on Multicoloured Necklaces:
   cycle_action_on_multicoloured
                       |- !n a. 0 < n ==> (Zadd n act multicoloured n a) cycle
   multicoloured_orbit_not_sing
                       |- !n a ls. ls IN multicoloured n a ==>
                                   ~SING (orbit cycle (Zadd n) (multicoloured n a) ls)
   multicoloured_orbit_card_not_1
                       |- !n a ls. ls IN multicoloured n a ==>
                                   CARD (orbit cycle (Zadd n) (multicoloured n a) ls) <> 1
   multicoloured_orbit_card_prime
                       |- !p a ls. prime p /\ ls IN multicoloured p a ==>
                                  (CARD (orbit cycle (Zadd p) (multicoloured p a) ls) = p)
   multicoloured_orbit_card_prime_exp
                       |- !p n a ls. prime p /\ ls IN multicoloured (p ** n) a ==>
                           p divides CARD (orbit cycle (Zadd (p ** n)) (multicoloured (p ** n) a) ls)

   Cycle action on Monocoloured Necklace:
   cycle_action_on_monocoloured
                       |- !n a. (Zadd n act monocoloured n a) cycle
   monocoloured_orbit_sing
                       |- !n a ls. 0 < n /\ ls IN monocoloured n a ==>
                                   SING (orbit cycle (Zadd n) (monocoloured n a) ls)
   monocoloured_orbit_card_1
                       |- !n a ls. 0 < n /\ ls IN monocoloured n a ==>
                                  (CARD (orbit cycle (Zadd n) (monocoloured n a) ls) = 1)
   monocoloured_iff_orbit_sing
                       |- !n a ls. 0 < n /\ ls IN necklace n a ==>
                                  (ls IN monocoloured n a <=>
                                   (orbit cycle (Zadd n) (necklace n a) ls = {ls}))
   monocoloured_iff_orbit_card_1
                       |- !n a ls. 0 < n /\ ls IN necklace n a ==>
                                  (ls IN monocoloured n a <=>
                                   (CARD (orbit cycle (Zadd n) (necklace n a) ls) = 1))

   Application 1: Fermat's Little Theorem (Petersen's proof):
   fermat_little_thm   |- !p a. prime p ==> p divides a ** p - a
   fermat_little_exp   |- !p n a. prime p ==> (a ** p ** n MOD p = a MOD p)

   Application 2: Classification of Necklace Orbits:
   necklace_orbit_theorem
                       |- !p a ls. prime p /\ ls IN necklace p a ==>
                                  (ls IN monocoloured p a <=>
                                   (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1)) /\
                                  (ls IN multicoloured p a <=>
                                   (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p))

*)

(* ------------------------------------------------------------------------- *)
(* Necklace Proof via Group action.                                          *)
(* ------------------------------------------------------------------------- *)

(* The goal: Necklace Orbit Theorem
   If ls is a Necklace of length prime p,
   then ls is monocoloured iff CARD (orbit cycle ls) = 1,
   and  ls is multicoloured iff CARD (orbit cycle ls) = p.
*)

(* ------------------------------------------------------------------------- *)
(* Zadd -- the additive group of modulo prime (simple cyclic clock).         *)
(* ------------------------------------------------------------------------- *)

val Zadd_def = groupInstancesTheory.Zadd_def;
(* |- !n. Zadd n = <|carrier := count n; id := 0; op := (\i j. (i + j) MOD n)|> *)

val Zadd_element = groupInstancesTheory.Zadd_element
(* |- !n x. x IN (Zadd n).carrier <=> x < n *)

val Zadd_id = groupInstancesTheory.Zadd_id
(* |- !n. (Zadd n).id = 0 *)

val Zadd_group = groupInstancesTheory.Zadd_group;
(* |- !n. 0 < n ==> Group (Zadd n) *)

val Zadd_finite = groupInstancesTheory.Zadd_finite;
(* |- !n. FINITE (Zadd n).carrier *)

val Zadd_finite_group = groupInstancesTheory.Zadd_finite_group;
(* |- !n. 0 < n ==> FiniteGroup (Zadd n) *)

val Zadd_card = groupInstancesTheory.Zadd_card;
(* |- !n. CARD (Zadd n).carrier = n *)

val Zadd_exp = groupInstancesTheory.Zadd_exp;
(* |- !n. 0 < n ==> !x m. (Zadd n).exp x m = (x * m) MOD n *)

(* ------------------------------------------------------------------------- *)
(* Cycle and Necklaces.                                                      *)
(* ------------------------------------------------------------------------- *)

val necklace_cycle = FLTnecklaceTheory.necklace_cycle;
(* |- !n a ls k. ls IN necklace n a ==> cycle k ls IN necklace n a *)

val multicoloured_cycle = FLTnecklaceTheory.multicoloured_cycle;
(* |- !n a ls k. ls IN multicoloured n a ==> cycle k ls IN multicoloured n a *)

val multicoloured_not_cycle_1 = FLTnecklaceTheory.multicoloured_not_cycle_1;
(* |- !n a ls. ls IN multicoloured n a ==> cycle 1 ls <> ls *)

val monocoloured_cycle = FLTnecklaceTheory.monocoloured_cycle;
(* |- !n a ls k. ls IN monocoloured n a ==> cycle k ls IN monocoloured n a *)

val monocoloured_cycle_1 = FLTnecklaceTheory.monocoloured_cycle_1;
(* |- !n a ls. ls IN monocoloured n a ==> (cycle 1 ls = ls) *)

val cycle_1_monocoloured = FLTnecklaceTheory.cycle_1_monocoloured;
(* |- !n a ls. ls IN necklace n a /\ (cycle 1 ls = ls) ==> ls IN monocoloured n a *)

val monocoloured_iff_cycle_1 = FLTnecklaceTheory.monocoloured_iff_cycle_1;
(* |- !n a ls. ls IN necklace n a ==> (ls IN monocoloured n a <=> (cycle 1 ls = ls)) *)

(* ------------------------------------------------------------------------- *)
(* Cycle action on Necklaces.                                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Apply Group action on necklaces.                                          *)
(* G = Zp, X = necklace n a. action = cycle.                                 *)
(* ------------------------------------------------------------------------- *)

(* Idea: cycle is a group action from Zn to necklace n a. *)

(* Theorem: 0 < n ==> (Zadd n act necklace n a) cycle *)
(* Proof:
   By action_def, Zadd_def, this is to show:
   (1) c < n ==> cycle c x IN necklace n a, true    by necklace_cycle
   (2) x IN necklace n a ==> cycle 0 x = x, true    by cycle_0
   (3) c < n /\ b < n ==> cycle c (cycle b x) = cycle ((c + b) MOD n) x
       Note LENGTH x = n      by necklace_length
       Hence the result       by cycle_addition
*)
val cycle_action_on_necklace = store_thm(
  "cycle_action_on_necklace",
  ``!n a. 0 < n ==> (Zadd n act necklace n a) cycle``,
  rw[action_def, Zadd_def] >-
  simp[necklace_cycle] >-
  simp[cycle_0] >>
  metis_tac[cycle_addition, necklace_length]);

(* Idea: an orbit of necklace ls consists of those it can cycle to. *)

(* Theorem: x IN (orbit cycle (Zadd n) (necklace n a) ls) <=>
              ?k. k < n /\ (x = cycle k ls) *)
(* Proof:
     orbit cycle (Zadd n) (necklace n a) ls
   = {cycle k ls | k IN (Zadd n).carrier}      by orbit_def
   = {cycle k ls | k < n}                      by Zadd_element
   Hence true by IN_IMAGE.
*)
val cycle_orbit_element = store_thm(
  "cycle_orbit_element",
  ``!n a ls x. x IN (orbit cycle (Zadd n) (necklace n a) ls) <=>
              ?k. k < n /\ (x = cycle k ls)``,
  rw[orbit_def, Zadd_element] >>
  metis_tac[]);

(* Idea: an orbit of necklace ls is finite. *)

(* Theorem: FINITE (orbit cycle (Zadd n) (necklace n a) ls) *)
(* Proof:
   Let b = orbit cycle (Zadd n) (necklace n a) ls,
       f = (\k. cycle k ls).
   Note b = IMAGE f (Zadd n).carrier     by orbit_as_image
    Now FINITE (Zadd n).carrier          by Zadd_finite
     so FINITE b                         by IMAGE_FINITE

orbit_as_image |> ISPEC ``cycle`` |> ISPEC ``Zadd n``;
|- !A x. orbit cycle (Zadd n) A x = IMAGE (\a. cycle a x) (Zadd n).carrier: thm
*)
val cycle_orbit_finite = store_thm(
  "cycle_orbit_finite",
  ``!n a ls. FINITE (orbit cycle (Zadd n) (necklace n a) ls)``,
  simp[orbit_as_image, Zadd_finite, IMAGE_FINITE]);

(* Idea: for necklace n a, action orbit of necklace ls has size a factor of n. *)
(* Proof: by orbit_stabilizer_theorem. *)

(* Theorem: 0 < n /\ ls IN (necklace n a) ==>
            (CARD (orbit cycle (Zadd n) (necklace n a) ls)) divides n *)
(* Proof:
   The aim is to apply:
   > orbit_stabilizer_thm |> ISPEC ``cycle`` |> ISPEC ``(Zadd n)``
       |> ISPEC ``necklace n a`` |> ISPEC ``ls:num list``;
   |- FiniteGroup (Zadd n) /\ (Zadd n act necklace n a) cycle /\
      ls IN necklace n a /\ FINITE (necklace n a) ==>
      (CARD (Zadd n).carrier =
       CARD (orbit cycle (Zadd n) (necklace n a) ls) *
       CARD (stabilizer cycle (Zadd n) ls)): thm

   Note FiniteGroup (Zadd n)             by Zadd_finite_group, 0 < n
    and (Zadd n act necklace n a) cycle  by cycle_action_on_necklace, 0 < n
    and FINITE (necklace n a)            by necklace_finite
    and CARD (Zadd n).carrier = n        by Zadd_card
   Let size = CARD (orbit cycle (Zadd n) (necklace n a) ls.
   Then size divides n                   by orbit_stabilizer_thm, divides_def
*)
val cycle_orbit_card_divides_length = store_thm(
  "cycle_orbit_card_divides_length",
  ``!n a ls. 0 < n /\ ls IN (necklace n a) ==>
            (CARD (orbit cycle (Zadd n) (necklace n a) ls)) divides n``,
  rpt strip_tac >>
  imp_res_tac Zadd_finite_group >>
  `(Zadd n act necklace n a) cycle` by rw[cycle_action_on_necklace] >>
  `FINITE (necklace n a)` by rw[necklace_finite] >>
  `CARD (Zadd n).carrier = n` by rw[Zadd_card] >>
  imp_res_tac orbit_stabilizer_thm >>
  metis_tac[divides_def, MULT_COMM]);

(* Idea: for necklace p a with prime p, action orbit of necklace ls has size 1 or p. *)

(* Theorem: prime p /\ ls IN (necklace p a) ==>
           (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1) \/
           (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p) *)
(* Proof:
   Let c = CARD (orbit cycle (Zadd p) (necklace p a) ls).
   Note 0 < p              by PRIME_POS
     so c divides p        by cycle_orbit_card_divides_length
   thus c = 1 or c = p     by prime_def
*)
val cycle_orbit_card_divides_length_prime = store_thm(
  "cycle_orbit_card_divides_length_prime",
  ``!p a ls. prime p /\ ls IN (necklace p a) ==>
           (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1) \/
           (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  imp_res_tac cycle_orbit_card_divides_length >>
  metis_tac[prime_def]);

(* ------------------------------------------------------------------------- *)
(* Cycle action on Multicoloured Necklaces.                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea: cycle is an action on multicoloured necklaces. *)

(* Theorem: 0 < n ==> (Zadd n act multicoloured n a) cycle *)
(* Proof:
   By action_def, Zadd_def, this is to show:
   (1) c < n ==> cycle c x IN multicoloured n a, true    by multicoloured_cycle
   (2) x IN multicoloured n a ==> cycle 0 x = x, true    by cycle_0
   (3) c < n /\ b < n ==> cycle c (cycle b x) = cycle ((c + b) MOD n) x
       Note x IN necklace n a      by multicoloured_necklace
        and LENGTH x = n           by necklace_length
       Hence the result            by cycle_addition
*)
val cycle_action_on_multicoloured = store_thm(
  "cycle_action_on_multicoloured",
  ``!n a. 0 < n ==> (Zadd n act multicoloured n a) cycle``,
  rw[action_def, Zadd_def] >-
  simp[multicoloured_cycle] >-
  simp[cycle_0] >>
  metis_tac[multicoloured_necklace, necklace_length, cycle_addition]);

(* Idea: for ls IN (multicoloured n a),
         NOT SING (orbit cycle (Zadd n) (multicoloured n a) ls). *)

(* Theorem: ls IN (multicoloured n a) ==>
            ~SING (orbit cycle (Zadd n) (multicoloured n a) ls) *)
(* Proof:
   Let b = orbit cycle (Zadd n) (multicoloured n a) ls.
   If n = 0,
      Note multicoloured 0 a = {}  by multicoloured_0
      so ls IN {} = F, hence true.
   If n = 1,
      Note multicoloured 1 a = {}  by multicoloured_1
      so ls IN {} = F, hence true.
   Otherwise, 0 < n and 1 < n.
   Note Group (Zadd n)             by Zadd_group, 0 < n
    and (Zadd n act multicoloured n a) cycle
                                   by cycle_action_on_multicoloured, 0 < n
    and ls IN b                    by orbit_has_self
     so b = {ls}                   by SING_DEF, IN_SING
    Now 1 IN (Zadd n).carrier      by Zadd_element, 1 < n
     so cycle 1 ls IN b            by orbit_has_action_element
    ==> cycle 1 ls = ls            by IN_SING
    But cycle 1 ls <> ls           by multicoloured_not_cycle_1

orbit_has_action_element |> ISPEC ``cycle`` |> ISPEC  ``Zadd n``
|- !A a x. a IN (Zadd n).carrier ==> cycle a x IN orbit cycle (Zadd n) A x
*)
val multicoloured_orbit_not_sing = store_thm(
  "multicoloured_orbit_not_sing",
  ``!n a ls. ls IN (multicoloured n a) ==>
            ~SING (orbit cycle (Zadd n) (multicoloured n a) ls)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  fs[multicoloured_0] >>
  Cases_on `n = 1` >-
  fs[multicoloured_1] >>
  `0 < n /\ 1 < n` by decide_tac >>
  `Group (Zadd n)` by rw[Zadd_group] >>
  `(Zadd n act multicoloured n a) cycle` by rw[cycle_action_on_multicoloured] >>
  `ls IN (orbit cycle (Zadd n) (multicoloured n a) ls)` by rw[orbit_has_self] >>
  `(orbit cycle (Zadd n) (multicoloured n a) ls) = {ls}` by metis_tac[SING_DEF, IN_SING] >>
  `1 IN (Zadd n).carrier` by rw[Zadd_element] >>
  metis_tac[orbit_has_action_element, multicoloured_not_cycle_1, IN_SING]);

(* Idea: (orbit cycle (Zadd n) (multicoloured n a) ls) is not a singleton. *)

(* Theorem: ls IN (multicoloured n a) ==>
            CARD (orbit cycle (Zadd n) (multicoloured n a) ls) <> 1 *)
(* Proof:
   Let b = orbit cycle (Zadd n) (multicoloured n a) ls.
   If n = 0,
      Note multicoloured 0 a = {}        by multicoloured_0
      so ls IN {} = F, hence true.
   Otherwise, n <> 0, so 0 < n.
      Note ~SING b                       by multicoloured_orbit_not_sing
       and FINITE (multicoloured n a)    by multicoloured_finite
       and (Zadd n act multicoloured n a) cycle
                                         by cycle_action_on_multicoloured, 0 < n
       ==> FINITE b                      by orbit_finite
        so SING b                        by CARD_EQ_1
      This contradicts ~SING b.

orbit_finite |> ISPEC ``cycle`` |> ISPEC ``Zadd n``;
|- !A x. (Zadd n act A) cycle /\ x IN A /\ FINITE A ==> FINITE (orbit cycle (Zadd n) A x)

CARD_EQ_1  |- !s. FINITE s ==> ((CARD s = 1) <=> SING s)
*)
val multicoloured_orbit_card_not_1 = store_thm(
  "multicoloured_orbit_card_not_1",
  ``!n a ls. ls IN (multicoloured n a) ==>
            CARD (orbit cycle (Zadd n) (multicoloured n a) ls) <> 1``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  fs[multicoloured_0] >>
  imp_res_tac multicoloured_orbit_not_sing >>
  `FINITE (multicoloured n a)` by rw[multicoloured_finite] >>
  `(Zadd n act multicoloured n a) cycle` by rw[cycle_action_on_multicoloured] >>
  metis_tac[orbit_finite, CARD_EQ_1]);

(* Idea: orbits of cycle action on multicoloured necklaces are of length p, for prime p *)

(* Theorem: prime p /\ ls IN (multicoloured p a) ==>
           (CARD (orbit cycle (Zadd p) (multicoloured p a) ls) = p) *)
(* Proof:
   Let A = multicoloured p a,
       b = orbit cycle (Zadd p) A ls,
       s = stabilizer cycle (Zadd p) ls.
   Note 0 < p                      by PRIME_POS
    and FINITE A                   by multicoloured_finite
    and FiniteGroup (Zadd p)       by Zadd_finite_group, 0 < p
    and (Zadd p act A) cycle       by cycle_action_on_multicoloured
   Then   p
        = CARD (Zadd p).carrier    by Zadd_card
        = CARD b * CARD s          by orbit_stabilizer_thm
   Thus (CARD b) divides p         by divides_def, MULT_COMM
    But CARD b <> 1                by multicoloured_orbit_card_not_1
     so CARD b = p                 by prime_def

orbit_stabilizer_thm |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !A x. FiniteGroup (Zadd p) /\ (Zadd p act A) cycle /\ x IN A /\ FINITE A ==>
          (CARD (Zadd p).carrier =
           CARD (orbit cycle (Zadd p) A x) *
           CARD (stabilizer cycle (Zadd p) x))
*)
val multicoloured_orbit_card_prime = store_thm(
  "multicoloured_orbit_card_prime",
  ``!p a ls. prime p /\ ls IN (multicoloured p a) ==>
           (CARD (orbit cycle (Zadd p) (multicoloured p a) ls) = p)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `A = multicoloured p a` >>
  `FINITE A` by rw[multicoloured_finite, Abbr`A`] >>
  `FiniteGroup (Zadd p)` by rw[Zadd_finite_group] >>
  `(Zadd p act A) cycle` by rw[cycle_action_on_multicoloured, Abbr`A`] >>
  `CARD (Zadd p).carrier = p` by rw[Zadd_card] >>
  `CARD (orbit cycle (Zadd p) A ls) <> 1` by rw[multicoloured_orbit_card_not_1, Abbr`A`] >>
  imp_res_tac orbit_stabilizer_thm >>
  metis_tac[divides_def, MULT_COMM, prime_def]);

(* Idea: orbits of cycle action on multicoloured necklaces of length p ** n
         have sizes divisible by p, for prime p. *)

(* Theorem: prime p /\ ls IN (multicoloured (p ** n) a) ==>
            p divides (CARD (orbit cycle (Zadd (p ** n))
                                         (multicoloured (p ** n) a) ls)) *)
(* Proof:
   Let q = p ** n,
       A = multicoloured q a,
       b = orbit cycle (Zadd q) A ls,
       s = stabilizer cycle (Zadd q) ls.
   Note 0 < p                      by PRIME_POS
     so 0 < q                      by ZERO_LT_EXP
   Note FINITE A                   by multicoloured_finite
    and FiniteGroup (Zadd q)       by Zadd_finite_group, 0 < q
   also (Zadd q act A) cycle       by cycle_action_on_multicoloured, 0 < q
   Then   q
        = CARD (Zadd q).carrier    by Zadd_card
        = CARD b * CARD s          by orbit_stabilizer_thm
   Thus (CARD b) divides q         by divides_def, MULT_COMM
    ==> ?j. j <= n /\
            (CARD b = p ** j)      by prime_power_divisor
    But CARD b <> 1                by multicoloured_orbit_card_not_1
     so p divides (CARD b)         by PRIME_EXP_FACTOR

orbit_stabilizer_thm |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !A x. FiniteGroup (Zadd p) /\ (Zadd p act A) cycle /\ x IN A /\ FINITE A ==>
          (CARD (Zadd p).carrier =
           CARD (orbit cycle (Zadd p) A x) *
           CARD (stabilizer cycle (Zadd p) x))
*)
val multicoloured_orbit_card_prime_exp = store_thm(
  "multicoloured_orbit_card_prime_exp",
  ``!p n a ls. prime p /\ ls IN (multicoloured (p ** n) a) ==>
    p divides (CARD (orbit cycle (Zadd (p ** n)) (multicoloured (p ** n) a) ls))``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** n` >>
  qabbrev_tac `A = multicoloured q a` >>
  `0 < q` by rw[PRIME_POS, ZERO_LT_EXP, Abbr`q`] >>
  `FINITE A` by rw[multicoloured_finite, Abbr`A`] >>
  `FiniteGroup (Zadd q)` by rw[Zadd_finite_group] >>
  `(Zadd q act A) cycle` by rw[cycle_action_on_multicoloured, Abbr`A`] >>
  `CARD (Zadd q).carrier = q` by rw[Zadd_card] >>
  `CARD (orbit cycle (Zadd q) A ls) <> 1` by rw[multicoloured_orbit_card_not_1, Abbr`A`] >>
  imp_res_tac orbit_stabilizer_thm >>
  qabbrev_tac `b = orbit cycle (Zadd q) A ls` >>
  `(CARD b) divides q` by metis_tac[divides_def, MULT_COMM] >>
  metis_tac[PRIME_EXP_FACTOR]);

(* ------------------------------------------------------------------------- *)
(* Cycle action on Monocoloured Necklaces.                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: cycle is an action on monocoloured necklaces *)

(* Theorem: action cycle (Zadd n) (monocoloured n a) *)
(* Proof:
   By action_def, Zadd_def, this is to show:
   (1) c < n ==> cycle c x IN monocoloured n a, true    by monocoloured_cycle
   (2) x IN monocoloured n a ==> cycle 0 x = x, true    by cycle_0
   (3) c < n /\ b < n ==> cycle c (cycle b x) = cycle ((c + b) MOD n) x
       Note x IN necklace n a  by monocoloured_necklace
        and LENGTH x = n       by necklace_length
       Hence the result        by cycle_addition
*)
val cycle_action_on_monocoloured = store_thm(
  "cycle_action_on_monocoloured",
  ``!n a. action cycle (Zadd n) (monocoloured n a)``,
  rw[action_def, Zadd_def] >-
  simp[monocoloured_cycle] >-
  simp[cycle_0] >>
  `x IN necklace n a` by rw[monocoloured_necklace] >>
  `LENGTH x = n` by metis_tac[necklace_length] >>
  fs[cycle_addition]);

(* Idea: monocoloured necklace orbits are singletons. *)

(* Theorem: 0 < n /\ ls IN (monocoloured n a) ==>
            SING (orbit cycle (Zadd n) (monocoloured n a) ls) *)
(* Proof:
   Let A = monocoloured n a,
       b = orbit cycle (Zadd n) A ls.
   By SING_DEF, to show: ?x. b = {x}.
   Take x = ls. By ONE_ELEMENT_SING, this is to show:
   (1) b <> {}
       By orbit_def, this is to find: ?k. k < n. Take x = 0.
   (2) !k. k IN b ==> (k = ls)
       By orbit_def, this is to show: !k. k < n ==> cycle k ls = ls.
       Note cycle 1 ls = ls           by monocoloured_cycle_1
         so cycle k ls = ls           by cycle_1_fix

> orbit_def |> ISPEC ``cycle`` |> ISPEC ``Zadd n`` |> SIMP_RULE bool_ss [Zadd_property];
|- !A x. orbit cycle (Zadd n) A x = {cycle a x | a < n}: thm
*)
val monocoloured_orbit_sing = store_thm(
  "monocoloured_orbit_sing",
  ``!n a ls. 0 < n /\ ls IN (monocoloured n a) ==>
            SING (orbit cycle (Zadd n) (monocoloured n a) ls)``,
  rw[SING_DEF] >>
  qexists_tac `ls` >>
  irule ONE_ELEMENT_SING >>
  rw[orbit_def] >-
  metis_tac[monocoloured_cycle_1, cycle_1_fix] >>
  rw[EXTENSION] >>
  metis_tac[]);

(* Idea: CARD (monocoloured necklace orbit) = 1. *)

(* Theorem: 0 < n /\ ls IN (monocoloured n a) ==>
            (CARD (orbit cycle (Zadd n) (monocoloured n a) ls) = 1) *)
(* Proof: by monocoloured_orbit_sing, SING_DEF, CARD_SING. *)
val monocoloured_orbit_card_1 = store_thm(
  "monocoloured_orbit_card_1",
  ``!n a ls. 0 < n /\ ls IN (monocoloured n a) ==>
            (CARD (orbit cycle (Zadd n) (monocoloured n a) ls) = 1)``,
  metis_tac[monocoloured_orbit_sing, SING_DEF, CARD_SING]);

(* Idea: ls IN (monocoloured n a) <=> CARD (orbit cycle (Zadd n) (necklace n a) ls) = 1 *)

(* Theorem: 0 < n /\ ls IN (necklace n a) ==>
     (ls IN (monocoloured n a) <=> (orbit cycle (Zadd n) (necklace n a) ls = {ls})) *)
(* Proof:
   Let A = monocoloured n a,
       s = necklace n a,
       b = orbit cycle (Zadd n) s ls.
   If part: ls IN A ==> b = {ls}
      By ONE_ELEMENT_SING, this is to show:
      (1) b <> {}
          Note ls IN b             by cycle_orbit_element, cycle_0, 0 < n
            so b <> {}             by MEMBER_NOT_EMPTY
      (2) !k. k IN b ==> (k = ls)
          Note cycle 1 ls = ls     by monocoloured_cycle_1, ls IN A
           and k IN b
           ==> ?j. k = cycle j ls  by cycle_orbit_element
                     = ls          by cycle_1_fix
   Only-if part: b = {ls} ==> ls IN A.
      If n = 1,
         Then A = s                by monocoloured_1
         hence ls IN A             by ls IN s
      If n <> 1, then 1 < n        by 0 < n, n <> 1
         Note cycle 1 ls IN b      by cycle_orbit_element
           so cycle 1 ls = ls      by IN_SING
          and ls <> []             by necklace_not_nil, 0 < n
          ==> SING (set ls)        by cycle_1_set_sing, ls <> []
         Thus ls IN A              by monocoloured_element
*)
val monocoloured_iff_orbit_sing = store_thm(
  "monocoloured_iff_orbit_sing",
  ``!n a ls. 0 < n /\ ls IN (necklace n a) ==>
     (ls IN (monocoloured n a) <=> (orbit cycle (Zadd n) (necklace n a) ls = {ls}))``,
  rpt strip_tac >>
  qabbrev_tac `A = monocoloured n a` >>
  qabbrev_tac `s = necklace n a` >>
  qabbrev_tac `b = orbit cycle (Zadd n) s ls` >>
  (rewrite_tac[EQ_IMP_THM] >> rpt strip_tac) >| [
    irule ONE_ELEMENT_SING >>
    `b <> {}` by metis_tac[cycle_orbit_element, cycle_0, MEMBER_NOT_EMPTY] >>
    `cycle 1 ls = ls` by metis_tac[monocoloured_cycle_1] >>
    metis_tac[cycle_orbit_element, cycle_1_fix],
    Cases_on `n = 1` >-
    fs[monocoloured_1, Abbr`A`, Abbr`s`] >>
    `1 < n` by decide_tac >>
    `cycle 1 ls = ls` by metis_tac[cycle_orbit_element, IN_SING] >>
    `ls <> []` by metis_tac[necklace_not_nil] >>
    `SING (set ls)` by rw[cycle_1_set_sing] >>
    simp[monocoloured_element, Abbr`A`]
  ]);

(* Theorem: 0 < n /\ ls IN (necklace n a) ==>
     (ls IN (monocoloured n a) <=> (CARD (orbit cycle (Zadd n) (necklace n a) ls) = 1)) *)
(* Proof:
   Let A = monocoloured n a,
       s = necklace n a,
       b = orbit cycle (Zadd n) s ls.
   If part: ls IN A ==> CARD b = 1
      Note b = {ls}        by monocoloured_iff_orbit_sing
        so CARD b = 1      by CARD_SING
   Only-if part: CARD b = 1 ==> ls IN A.
      Note FINITE b        by cycle_orbit_finite
       ==> SING b          by CARD_EQ_1, FINITE b
       Now ls IN b         by cycle_orbit_element, cycle_0, 0 < n
      Thus b = {ls}        by SING_DEF, IN_SING
       ==> ls IN A         by monocoloured_iff_orbit_sing
*)
val monocoloured_iff_orbit_card_1 = store_thm(
  "monocoloured_iff_orbit_card_1",
  ``!n a ls. 0 < n /\ ls IN (necklace n a) ==>
     (ls IN (monocoloured n a) <=> (CARD (orbit cycle (Zadd n) (necklace n a) ls) = 1))``,
  rw[EQ_IMP_THM] >-
  metis_tac[monocoloured_iff_orbit_sing, CARD_SING] >>
  qabbrev_tac `A = monocoloured n a` >>
  qabbrev_tac `s = necklace n a` >>
  qabbrev_tac `b = orbit cycle (Zadd n) s ls` >>
  `FINITE b` by metis_tac[cycle_orbit_finite] >>
  `SING b` by fs[CARD_EQ_1] >>
  `ls IN b` by metis_tac[cycle_orbit_element, cycle_0] >>
  `b = {ls}` by metis_tac[SING_DEF, IN_SING] >>
  simp[monocoloured_iff_orbit_sing, Abbr`A`]);

(* ------------------------------------------------------------------------- *)
(* Application 1: Fermat's Little Theorem (Petersen's proof).                *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Fermat's Little Theorem] -- line by line
         !p a. prime p ==> p divides (a ** p - a)   *)
(* Proof (J. Petersen in 1872):
   Take p elements from a with repetitions in all ways, that is, in a^p ways.
                   by necklace_card
   The a sets with elements all alike are not changed by a cyclic permutation of the elements,
                   by monocoloured_card
   while the remaining (a^p - a) sets are
                   by multicoloured_card
   permuted in sets of p.
                   by cycle_action_on_multicoloured, multicoloured_orbit_card_prime
   Hence p divides a^p - a.
                   by orbits_equal_size_property
*)

(* Theorem: prime p ==> p divides (a ** p - a) *)
(* Proof:
   Let A = multicoloured p a,
       b = (\ls. orbit cycle (Zadd p) A ls).
   Note 0 < p                      by PRIME_POS
    and FINITE A                   by multicoloured_finite
   with CARD A = a ** p - a        by multicoloured_card, 0 < p
   Also Group (Zadd p)             by Zadd_group, 0 < p
   with (Zadd p act A) cycle       by cycle_action_on_multicoloured, 0 < p
   then !ls. ls IN A ==>
             (CARD (b ls) = p)     by rw[multicoloured_orbit_card_prime
   thus p divides CARD A           by orbits_equal_size_property
     or p divides (a ** p - a)     by above

orbits_equal_size_property |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !A n. Group (Zadd p) /\ (Zadd p act A) cycle /\ FINITE A /\
         (!x. x IN A ==> (CARD (orbit cycle (Zadd p) A x) = n)) ==> n divides CARD A
*)
val fermat_little_thm = store_thm(
  "fermat_little_thm",
  ``!p a. prime p ==> p divides (a ** p - a)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `A = multicoloured p a` >>
  `FINITE A` by rw[multicoloured_finite, Abbr`A`] >>
  `CARD A = a ** p - a` by rw[multicoloured_card, Abbr`A`] >>
  `Group (Zadd p)` by rw[Zadd_group] >>
  `(Zadd p act A) cycle` by rw[cycle_action_on_multicoloured, Abbr`A`] >>
  metis_tac[multicoloured_orbit_card_prime, orbits_equal_size_property]);

(* Idea: Power version of Fermat's Little Theorem
         !p n a. prime p ==> (a ** (p ** n) MOD p = a MOD p). *)

(* Theorem: prime p ==> (a ** (p ** n) MOD p = a MOD p) *)
(* Proof:
   Let q = p ** n,
       A = multicoloured q a,
       b = (\ls. orbit cycle (Zadd q) A ls).
   Note 0 < p                      by PRIME_POS
     so 0 < q                      by ZERO_LT_EXP
   Note FINITE A                   by multicoloured_finite
    and Group (Zadd q)             by Zadd_group, 0 < q
   also (Zadd q act A) cycle       by cycle_action_on_multicoloured, 0 < q
    and CARD A = a ** q - a        by multicoloured_card, 0 < q
    and !ls. ls IN A ==>
        p divides (CARD (b ls))    by multicoloured_orbit_card_prime_exp
     so p divides (CARD A)         by orbits_size_factor_property
   Thus (a ** q - a) MOD p = 0     by DIVIDES_MOD_0, 0 < p
    Now a <= a ** q                by EXP_LE, 0 < q
    ==> a ** q MOD p = a MOD p     by MOD_EQ, 0 < p

orbits_size_factor_property |> ISPEC ``cycle`` |> ISPEC ``Zadd p``;
|- !A n. Group (Zadd p) /\ (Zadd p act A) cycle /\ FINITE A /\
         (!x. x IN A ==> n divides CARD (orbit cycle (Zadd p) A x)) ==>
         n divides CARD A
*)
val fermat_little_exp = store_thm(
  "fermat_little_exp",
  ``!p n a. prime p ==> (a ** (p ** n) MOD p = a MOD p)``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** n` >>
  qabbrev_tac `A = multicoloured q a` >>
  `0 < p` by rw[PRIME_POS] >>
  `0 < q` by rw[ZERO_LT_EXP, Abbr`q`] >>
  `FINITE A` by rw[multicoloured_finite, Abbr`A`] >>
  `Group (Zadd q)` by rw[Zadd_group] >>
  `(Zadd q act A) cycle` by rw[cycle_action_on_multicoloured, Abbr`A`] >>
  `CARD A = a ** q - a` by rw[multicoloured_card, Abbr`A`] >>
  `!ls. ls IN A ==> p divides (CARD (orbit cycle (Zadd q) A ls))` by rw[multicoloured_orbit_card_prime_exp, Abbr`A`, Abbr`q`] >>
  imp_res_tac orbits_size_factor_property >>
  `(a ** q - a) MOD p = 0` by metis_tac[DIVIDES_MOD_0] >>
  rfs[MOD_EQ, EXP_LE]);

(* ------------------------------------------------------------------------- *)
(* Application 2: Classification of Necklace Orbits.                         *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Necklace Orbit Theorem]
   If ls is a Necklace of length prime p,
   then ls is monocoloured iff CARD (orbit cycle ls) = 1,
   and  ls is multicoloured iff CARD (orbit cycle ls) = p.
*)

(* Theorem: prime p /\ ls IN (necklace p a) ==>
   (ls IN (monocoloured p a) <=> (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1)) /\
   (ls IN (multicoloured p a) <=> (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p)) *)
(* Proof:
   Note 0 < p              by PRIME_POS
    and p <> 1             by NOT_PRIME_1
   Let s = necklace p a,
       b = orbit cycle (Zadd p) s ls.
   This is to show:
   (1) ls IN monocoloured p a <=> (CARD b = 1)
       Note CARD b = 1        by monocoloured_iff_orbit_card_1, 0 < p
   (2) ls IN multicoloured p a <=> (CARD b = p)
       If part: ls IN multicoloured p a ==> (CARD b = p)
          Note ls NOTIN monocoloured p a    by multicoloured_not_monocoloured
            so CARD b <> 1                  by monocoloured_iff_orbit_card_1, 0 < p
           ==> CARD b = p                   by cycle_orbit_card_divides_length_prime, p <> 1
       Only-if part: (CARD b = p) ==> ls IN multicoloured p a
          Note CARD b <> 1                  by p <> 1
            so s NOTIN monocoloured p a     by monocoloured_iff_orbit_card_1, 0 < p
           ==> ls IN multicoloured p a      by multicoloured_or_monocoloured
*)
val necklace_orbit_theorem = store_thm(
  "necklace_orbit_theorem",
  ``!p a ls. prime p /\ ls IN (necklace p a) ==>
   (ls IN (monocoloured p a) <=> (CARD (orbit cycle (Zadd p) (necklace p a) ls) = 1)) /\
   (ls IN (multicoloured p a) <=> (CARD (orbit cycle (Zadd p) (necklace p a) ls) = p))``,
  ntac 4 strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  strip_tac >-
  simp[monocoloured_iff_orbit_card_1] >>
  rw[EQ_IMP_THM] >| [
    `ls NOTIN monocoloured p a` by rw[multicoloured_not_monocoloured] >>
    metis_tac[monocoloured_iff_orbit_card_1, cycle_orbit_card_divides_length_prime],
    metis_tac[monocoloured_iff_orbit_card_1, multicoloured_or_monocoloured]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
