(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Group-theoretic Proof.                          *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Group Theory)
======================================
Given a finite group G, consider an element a in G.

Since G is finite, element a has an order: (order a), and a^(order a) = e.

This also means that, the generated subgroup <a> has size (order a).

By Lagrange identity, size of group = k * size of subgroup.

Hence, |G| = k * |<a>|, and a^|<a>| = e.

This implies:   a^|G| = a^(k*|<a>|) = a^(|<a>*k) = (a^|<a>|)^k = e^k = e.

This is the group equivalent of Fermat's Little Theorem.

By putting G = Z*p, a IN Z*p means 0 < a < p,
then a^|G| mod p = 1, or a^(p-1) mod p = 1.

By putting G = Phi*n = {a | a < n /\ gcd(a,n) = 1 },
then a^|G| mod n = 1, or a^phi(n) mod n = 1.

which is Euler's generalization of Fermat's Little Theorem.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

open arithmeticTheory pred_setTheory dividesTheory numberTheory
     combinatoricsTheory;

open groupTheory; (* for FiniteGroup_def *)

val _ = new_theory "FLTgroup";

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Number Group Documentation                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   From helperNum:
   EUCLID_LEMMA        |- !p x y. prime p ==> ((x * y) MOD p = 0 <=>
                                              x MOD p = 0 \/ y MOD p = 0)
   MOD_MULT_INV_EXISTS |- !p x. prime p /\ 0 < x /\ x < p ==>
                            ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)
   MOD_MULT_INV_DEF    |- !p x. prime p /\ 0 < x /\ x < p ==>
                                0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\
                                (MOD_MULT_INV p x * x) MOD p = 1

   From Euler:
   residue_def     |- !n. residue n = {i | 0 < i /\ i < n}
   residue_count   |- !n. 0 < n ==> count n = 0 INSERT residue n
   residue_finite  |- !n. FINITE (residue n)
   residue_card    |- !n. 0 < n ==> CARD (residue n) = n - 1

   From groupInstances:
   Zstar_def     |- !p. Zstar p = <|carrier := residue p;
                                         id := 1;
                                         op := (\i j. (i * j) MOD p)|>
   Zstar_element |- !p x. x IN (Zstar p).carrier <=> 0 < x /\ x < p
   Zstar_id      |- !p. (Zstar p).id = 1
   Zstar_finite  |- !p. FINITE (Zstar p).carrier
   Zstar_card    |- !p. 0 < p ==> CARD (Zstar p).carrier = p - 1
   Zstar_group   |- !p. prime p ==> Group (Zstar p)
   Zstar_exp     |- !p a. prime p /\ a IN (Zstar p).carrier ==>
                      !n. (Zstar p).exp a n = a ** n MOD p

   Application:
   Fermat_Little_thm
                 |- !p a. prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1
*)

(* Part 1: Basic ----------------------------------------------------------- *)

(* Part 2: General Theory -------------------------------------------------- *)

(* Part 3: Actual Proof ---------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (by Z^{*}[p] multiplicative group)                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1 *)
(* Proof:
   Note a IN (Zstar p).carrier     by Zstar_element
    and Group (Zstar p)            by Zstar_group
    and FINITE (Zstar p).carrier   by Zstar_finite
     so FiniteGroup (Zstar p)      by FiniteGroup_def
   Also 0 < p                      by PRIME_POS

        a ** (p - 1) MOD p
      = (Zstar p).exp a (p - 1)    by Zstar_exp
      = (Zstar p).exp a (CARD (Zstar p).carrier)
                                   by Zstar_card, 0 < p
      = (Zstar p).id               by finite_group_Fermat
      = 1                          by Zstar_id
*)
Theorem Fermat_Little_thm:
  !p a. prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1
Proof
  rpt strip_tac >>
  `a IN (Zstar p).carrier` by rw[Zstar_element] >>
  `FiniteGroup (Zstar p)` by rw[FiniteGroup_def, Zstar_finite, Zstar_group] >>
  imp_res_tac finite_group_Fermat >>
  `0 < p` by rw[PRIME_POS] >>
  rfs[Zstar_card, Zstar_id, Zstar_exp]
QED

(* Part 4: End ------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
