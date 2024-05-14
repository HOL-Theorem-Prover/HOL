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

(* declare new theory at start *)
val _ = new_theory "FLTeuler";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory pred_setTheory dividesTheory gcdTheory numberTheory
     combinatoricsTheory;

open groupTheory; (* for FiniteGroup_def *)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Number Group Documentation                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   From helperFunction:
   coprime_mod         |- !m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)
   coprime_sym         |- !x y. coprime x y <=> coprime y x
   MOD_NONZERO_WHEN_GCD_ONE
                       |- !n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n
   PRODUCT_WITH_GCD_ONE|- !n x y. coprime n x /\ coprime n y ==> coprime n (x * y)
   MOD_WITH_GCD_ONE    |- !n x. 0 < n /\ coprime n x ==> coprime n (x MOD n)
   GCD_DIVIDES         |- !m n. 0 < n /\ 0 < m ==> 0 < gcd n m /\ n MOD gcd n m = 0 /\ m MOD gcd n m = 0
   GCD_ONE_PROPERTY    |- !n x. 1 < n /\ coprime n x ==> ?k. (k * x) MOD n = 1 /\ coprime n k
   GCD_MOD_MULT_INV    |- !n x. 1 < n /\ coprime n x /\ 0 < x /\ x < n ==>
                            ?y. 0 < y /\ y < n /\ coprime n y /\ (y * x) MOD n = 1
   GEN_MULT_INV_DEF    |- !n x. 1 < n /\ coprime n x /\ 0 < x /\ x < n ==>
                                0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\
                                coprime n (GCD_MOD_MUL_INV n x) /\
                                (GCD_MOD_MUL_INV n x * x) MOD n = 1

   From Euler:
   Euler_def         |- !n. Euler n = {i | 0 < i /\ i < n /\ coprime n i}
   totient_def       |- !n. totient n = CARD (Euler n)
   Euler_card_prime  |- !p. prime p ==> totient p = p - 1

   From groupInstances:
   Estar_def     |- !n. Estar n = <|carrier := Euler n; id := 1; op := (\i j. (i * j) MOD n)|>
   Estar_element |- !n x. x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x
   Estar_id      |- !n. (Estar n).id = 1
   Estar_group   |- !n. 1 < n ==> Group (Estar n)
   Estar_finite  |- !n. FINITE (Estar n).carrier
   Estar_card    |- !n. CARD (Estar n).carrier = totient n
   Estar_exp     |- !n a. 1 < n /\ a IN (Estar n).carrier ==>
                      !k. (Estar n).exp a k = a ** k MOD n

   Application:
   Euler_Fermat_thm  |- !n a. 1 < n /\ coprime a n ==> a ** totient n MOD n = 1
   Fermat_Little_thm |- !p a. prime p /\ coprime a p ==> a ** (p - 1) MOD p = 1
*)

(* Part 1: Basic ----------------------------------------------------------- *)

(* Part 2: General Theory -------------------------------------------------- *)

(* Part 3: Actual Proof ---------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (by E^{*}[n] multiplicative group)                *)
(* ------------------------------------------------------------------------- *)

(* Idea: For all a in Estar n, a ** (totient n) MOD n = 1 *)

(* Theorem: 1 < n /\ coprime a n ==> a ** (totient n) MOD n = 1 *)
(* Proof:
   Let b = a MOD n.
   Then b < n                        by MOD_LESS, 0 < n
    and coprime n a                  by coprime_sym
     so coprime n b                  by coprime_mod, 0 < n
   Also b <> 0                       by GCD_0R, coprime n b, n <> 1
   Thus b IN (Estar n).carrier       by Estar_element, 0 < b < n

   Note Group (Estar n)              by Estar_group, 1 < n
    and FINITE (Estar n).carrier     by Estar_finite
     so FiniteGroup (Estar n)        by FiniteGroup_def

        (a ** totient n) MOD n
      = (b ** totient n) MOD n       by MOD_EXP
      = (Zstar n).exp b (totient n)  by Estar_exp
      = (Zstar n).exp b (CARD (Zstar n).carrier)
                                     by Estar_card
      = (Zstar n).id                 by finite_group_Fermat
      = 1                            by Estar_id

> finite_group_Fermat |> ISPEC ``Zstar n`` |> ISPEC ``b:num``;
|- FiniteGroup (Zstar n) /\ b IN (Zstar n).carrier ==>
               ((Zstar n).exp b (CARD (Zstar n).carrier) = (Zstar n).id): thm
*)
Theorem Euler_Fermat_thm:
  !n a. 1 < n /\ coprime a n ==> a ** (totient n) MOD n = 1
Proof
  rpt strip_tac >>
  qabbrev_tac `b = a MOD n` >>
  `b < n` by rw[Abbr`b`] >>
  `coprime n b` by rw[coprime_mod, coprime_sym, Abbr`b`] >>
  `b <> 0` by metis_tac[GCD_0R, DECIDE``1 < n ==> n <> 1``] >>
  `a ** totient n MOD n = b ** totient n MOD n` by rw[MOD_EXP, Abbr`b`] >>
  `b IN (Estar n).carrier` by rw[Estar_element] >>
  `(Estar n).id = 1` by rw[Estar_id] >>
  `FiniteGroup (Estar n)` by rw[Estar_group, Estar_finite, FiniteGroup_def] >>
  `CARD (Estar n).carrier = totient n` by rw[Estar_card] >>
  metis_tac[finite_group_Fermat, Estar_exp]
QED

(* Theorem: prime p /\ coprime a p ==> a ** (p - 1) MOD p = 1 *)
(* Proof:
   Note 1 < p                  by ONE_LT_PRIME
     a ** (p - 1) MOD p
   = a ** (totient p) MOD p    by Euler_card_prime
   = 1                         by Euler_Fermat_thm
*)
Theorem Fermat_Little_thm:
  !p a. prime p /\ coprime a p ==> a ** (p - 1) MOD p = 1
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `totient p = p - 1` by rw[Euler_card_prime] >>
  metis_tac[Euler_Fermat_thm]
QED

(* Part 4: End ------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
