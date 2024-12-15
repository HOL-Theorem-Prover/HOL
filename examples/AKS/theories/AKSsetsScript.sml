(* ------------------------------------------------------------------------- *)
(* Introspective Sets                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSsets";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory dividesTheory
     gcdTheory gcdsetTheory logrootTheory numberTheory combinatoricsTheory
     primeTheory;

(* Get dependent theories local *)
open AKSintroTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory
     polyBinomialTheory;

open polyMonicTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;
open polyIrreducibleTheory;
open polyRootTheory;
open polyProductTheory;

open fieldInstancesTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Introspective Sets Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   N         = setN r k s
   P         = setP r k s
   M         = modN r k s
   Q z       = modP r k s z
   PM        = reduceP r k s
   NM p q n  = reduceN p q n
   PPM n     = reduceP_poly r n
*)
(* Definitions and Theorems (# are exported):

   Sets in AKS Proof:

   Set N = introspective exponents that are coprimes to k:
   setN_def       |- !r k s. N = {m | coprime m k /\ !c. 0 < c /\ c <= s ==> m intro X + |c|}
   setN_element   |- !r k s m. m IN N <=> coprime m k /\ !c. 0 < c /\ c <= s ==> m intro X + |c|
   setN_element_coprime  |- !r k s m. m IN N ==> coprime m k
   setN_closure          |- !r k s. Ring r /\ 0 < k ==> !m n. m IN N /\ n IN N ==> m * n IN N
   setN_has_product      |- !r k s. Ring r /\ 0 < k ==> !m n. m IN N /\ n IN N ==> m * n IN N
   setN_has_no_0         |- !r k s. 1 < k ==> 0 NOTIN N
   setN_has_1            |- !r k s. Ring r /\ 0 < k ==> 1 IN N
   setN_element_nonzero  |- !r k s. 1 < k ==> !m. m IN N ==> m <> 0
   setN_has_element_powers        |- !r k s. Ring r /\ 0 < k ==>
                                     !p. p IN N ==> !n. p ** n IN N
   setN_has_element_pair_powers   |- !r k s. Ring r /\ 0 < k ==>
                                     !p q. p IN N /\ q IN N ==>
                               !m n x y. (x,y) IN count m CROSS count n ==> p ** x * q ** y IN N
   setN_has_char              |- !r k s. FiniteField r /\ 0 < k /\ coprime (char r) k ==> char r IN N
   setN_has_char_and_cofactor |- !r k s n. FiniteField r /\ coprime k (CARD R) /\
                                           1 < ordz k (CARD R) /\ char r divides n /\ n IN N ==>
                                           char r IN N /\ n DIV char r IN N

   Set P = introspective polynomials with exponents in Set N:
   setP_def           |- !r k s. P = {p | poly p /\ !m. m IN N ==> m intro p}
   setP_element       |- !r k s p. p IN P <=> poly p /\ !m. m IN N ==> m intro p
#  setP_element_poly  |- !r k s p. p IN P ==> poly p
   setP_closure       |- !r k s. Ring r /\ 0 < k ==> !p q. p IN P /\ q IN P ==> p * q IN P
   setP_has_zero      |- !r k s. Ring r /\ 1 < k ==> |0| IN P
   setP_has_one       |- !r k s. Ring r /\ 0 < k ==> |1| IN P
   setP_has_X         |- !r k s. Ring r /\ 0 < k ==> X IN P
   setP_has_X_add_c   |- !r k s. Ring r ==> !c. 0 < c /\ c <= s ==> X + |c| IN P

   Set M = MOD k of elements in Set N:
   modN_def             |- !r k s. M = IMAGE (\m. m MOD k) N
   modN_alt             |- !r k s. M = {m MOD k | m | m IN N}
   modN_element         |- !r k s n. n IN M <=> ?m. (n = m MOD k) /\ m IN N
   modN_closure         |- !r k s. Ring r /\ 0 < k ==>
                           !x y. x IN M /\ y IN M ==> (x * y) MOD k IN M
   modN_subset_count    |- !r k s. 0 < k ==> M SUBSET count k
   modN_finite          |- !r k s. 0 < k ==> FINITE M
   modN_element_less    |- !r k s. 0 < k ==> !n. n IN M ==> n < k
   modN_has_1           |- !r k s. Ring r /\ 1 < k ==> 1 IN M
   modN_not_empty       |- !r k s. Ring r /\ 0 < k ==> M <> {}
   modN_has_no_0        |- !r k s. 1 < k ==> 0 NOTIN M
   setN_element_mod     |- !r k s m. m IN N ==> m MOD k IN M
   modN_subset_coprimes |- !r k s. 1 < k ==> M SUBSET coprimes k
   modN_subset_euler    |- !r k s. 1 < k ==> M SUBSET Euler k
   modN_has_1_field     |- !r k s. Field r /\ 1 < k ==> 1 IN M
   modN_not_empty_field |- !r k s. Field r /\ 0 < k ==> M <> {}

   Upper Bound of M:
   modN_card_upper_estimate |- !r k s. 0 < k ==> CARD M <= k
   modN_card_upper          |- !r k s. 1 < k ==> CARD M < k
   modN_card_upper_better   |- !r k s. 1 < k ==> CARD M <= phi k

   Lower Bound of M:
   modN_element_invertible  |- !r k s. 1 < k ==>
                               !n. n IN M ==> n IN (Invertibles (ZN k).prod).carrier
   modN_has_element_powers  |- !r k s. Ring r /\ 1 < k ==>
                               !x. x IN M ==> !n. (Invertibles (ZN k).prod).exp x n IN M
   modN_has_generator_of_element  |- !r k s. Ring r /\ 1 < k ==>
                 !n. n IN M ==> (Generated (Invertibles (ZN k).prod) n).carrier SUBSET M
   modN_card_lower          |- !r k s. Ring r /\ 1 < k ==>
                               !n. n IN N ==> ordz k n <= CARD M
   modN_card_bounds         |- !r k s. Ring r /\ 1 < k ==>
                               !n. n IN N ==> ordz k n <= CARD M /\ CARD M < k
   modN_card_bounds_better  |- !r k s. Ring r /\ 1 < k ==>
                               !n. n IN N ==> ordz k n <= CARD M /\ CARD M <= phi k
   modN_card_gt_1_condition |- !r k s. Ring r /\ 1 < k /\
                                (?n. 1 < n /\ n IN N /\ (2 * LOG2 n) ** 2 < order (ZN k).prod n) ==>
                                1 < CARD M
   modN_card_gt_1_by_LOG2  |- !r k n s.  Ring r /\ 1 < k /\ 1 < n /\ n IN N /\
                              TWICE (LOG2 n) ** 2 <= ordz k n ==> 1 < CARD M
   modN_card_gt_1_by_ulog  |- !r k n s. Ring r /\ 1 < k /\ 1 < n /\ n IN N /\
                              TWICE (ulog n) ** 2 <= ordz k n ==> 1 < CARD M

   Set (Q z) = MOD z of the polynomials in P:
   modP_def                |- !r k s z. Q z = IMAGE (\p. p % z) P
   modP_alt                |- !r k s z. Q z = {p % z | p | p IN P}
   modP_element            |- !r k s z p. p IN Q z <=> ?q. q IN P /\ (p = q % z)
   modP_element_poly       |- !r k s. Ring r ==>
                              !z. pmonic z ==> !p. p IN Q z ==> poly p /\ deg p < deg z
   modP_closure            |- !r k s z. Ring r /\ 0 < k /\ ulead z ==>
                              !p q. p IN Q z /\ q IN Q z ==> (p * q) % z IN Q z
   modP_subset_mod_factor  |- !r k s z. Ring r /\ pmonic z ==> Q z SUBSET Rz
   modP_has_zero           |- !r k s z. Ring r /\ 1 < k /\ ulead z ==> |0| IN Q z
   modP_has_one            |- !r k s z. Ring r /\ 0 < k /\ pmonic z ==> |1| IN Q z
   modP_has_X              |- !r k s z. Ring r /\ 0 < k /\ monic z /\ 1 < deg z ==> X IN Q z
   modP_finite             |- !r k s z. FiniteRing r /\ pmonic z ==> FINITE (Q z):
   setP_element_mod        |- !r k s p z. p IN P ==> p % z IN Q z

   The Reduced Set from P:
   reduceP_def           |- !r k s. PM = {p | p IN P /\ deg p < CARD M}
   reduceP_element       |- !r k s p. p IN PM <=> p IN P /\ deg p < CARD M
   reduceP_element_mod   |- !r k s z p. p IN PM ==> p % z IN Q z
#  reduceP_element_poly  |- !r k s p. p IN PM ==> poly p
   reduceP_subset_setP   |- !r k s. PM SUBSET P
   reduceP_finite        |- !r k s. FiniteRing r ==> FINITE PM
   reduceP_has_zero      |- !r k s. Ring r /\ 1 < k ==> |0| IN PM
   reduceP_has_X         |- !r k s. Ring r /\ 0 < k /\ 1 < CARD M ==> X IN PM

   The Reduced Set from N:
   reduceN_def               |- !p q n. NM p q n =
                                IMAGE (\(i,j). p ** i * q ** j) (count (SUC n) CROSS count (SUC n))
   reduceN_alt               |- !p q n. NM p q n = {p ** i * q ** j | i <= n /\ j <= n}
   reduceN_finite            |- !p q n. FINITE (NM p q n)
   reduceN_element           |- !p q n x. x IN NM p q n ==>
                                ?m1 m2. m1 <= n /\ m2 <= n /\ (x = p ** m1 * q ** m2)
   reduceN_subset_setN       |- !r k s. Ring r /\ 0 < k ==>
                                !p q. p IN N /\ q IN N ==> !n. NM p q n SUBSET N
   reduceN_element_in_setN   |- !r k s. Ring r /\ 0 < k ==>
                                !p q. p IN N /\ q IN N ==> !n x. x IN NM p q n ==> x IN N
   reduceN_mod_subset        |- !r k. Ring r /\ 0 < k ==> !p q. p IN N /\ q IN N ==>
                                      IMAGE (\x. x MOD k) (NM p q (SQRT (CARD M))) SUBSET M
   reduceN_element_upper        |- !p q. 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= MAX p q ** (2 * n)
   reduceN_element_upper_alt    |- !n p. 1 < p /\ p <= n ==> !e m. e IN NM p n m ==> e <= n ** (2 * m)
   reduceN_element_upper_better |- !p q. 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= (p * q) ** n

   Cardinality of Reduced Set of N:
   count_cross_to_setN_inj |- !r k s. Ring r /\ 0 < k ==>
                              !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~perfect_power q p ==>
                              !n. INJ (\(i,j). p ** i * q ** j) (count (SUC n) CROSS count (SUC n)) N
   reduceN_card            |- !r k s. Ring r /\ 0 < k ==>
                              !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~perfect_power q p ==>
                              !n. CARD (NM p q n) = SUC n ** 2
   reduceN_card_field      |- !r k s p q. Field r /\ 0 < k /\ p IN N /\ q IN N /\
                                          prime p /\ 1 < q /\ ~perfect_power q p ==>
                                      !n. CARD (NM p q n) = SUC n ** 2

   Upper Bound of (Q z):
   modP_card_upper_max     |- !r k s z. FiniteField r /\ mifactor z (unity k) ==>
                                        CARD (Q z) <= CARD R ** deg z

   Set of Polynomial Products on Sets of Monomials:
   reduceP_poly_def            |- !r n. PPM n =
                                        IMAGE (\s. PPROD (IMAGE (\c. X + |c|) s)) (PPOW (IMAGE SUC (count n)))
   reduceP_poly_element_poly   |- !r. Ring r ==> !p n. p IN PPM n ==> poly p
   reduceP_poly_element_monic  |- !r. Ring r ==> !p n. p IN PPM n ==> monic p
   reduceP_poly_has_no_zero    |- !r. Ring r /\ #1 <> #0 ==> !n. |0| NOTIN PPM n
   reduceP_poly_has_no_X       |- !r. Ring r /\ #1 <> #0 ==> !n. n < char r ==> X NOTIN PPM n
   reduceP_poly_finite         |- !r n. FINITE (PPM n)
   reduceP_poly_card           |- !r. Field r ==> !n. n < char r ==> (CARD (PPM n) = PRE (2 ** n))

*)

(* ------------------------------------------------------------------------- *)
(* Sets in AKS Proof                                                         *)
(* ------------------------------------------------------------------------- *)

(* from polyMonic.hol:
val _ = overload_on ("|c|", ``###c``);
*)

(* Define the sets N and P *)
(* Note: N and P are based on mod (p, X ** k - 1),
         where p is a prime factor of given n
         and ord_k(n) = order (ZN t) n > 4 (log n)^2
*)
(* Observation: both N and P are closed under multiplication *)

(* ------------------------------------------------------------------------- *)
(* Set N = coprimes of k that are introspective with X + |c| for 0 < c <= s  *)
(* ------------------------------------------------------------------------- *)

(* The set of introspective exponents *)
(* N = {m | gcd(m, k) = 1 /\ m intro p  where p = X + |c|, and for 0 < c <= s } *)
val setN_def = Define`
  setN (r:'a ring) (k:num) (s:num) = {m | coprime m k /\ (!c. 0 < c /\ c <= s ==> m intro X + |c|) }
`;

(* overload for setN *)
val _ = overload_on ("N", ``setN (r:'a ring) k s``);

(* Theorem: !m. m IN N <=> coprime m k /\ !c. 0 < c /\ c <= s ==> m intro X + |c| *)
(* Proof: by setN_def. *)
val setN_element = store_thm(
  "setN_element",
  ``!r:'a ring (k s):num. !m. m IN N <=> coprime m k /\ (!c. 0 < c /\ c <= s ==> m intro X + |c|)``,
  rw[setN_def]);

(* Theorem: !m. m IN N ==> coprime m k *)
(* Proof: by setN_element. *)
val setN_element_coprime = store_thm(
  "setN_element_coprime",
  ``!r:'a ring (k s):num. !m. m IN N ==> coprime m k``,
  rw[setN_element]);

(* Theorem: 0 < k ==> !m n. m IN N /\ n IN N ==> m * n IN N *)
(* Proof: by poly_intro_mult, coprime_product_coprime *)
val setN_closure = store_thm(
  "setN_closure",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> !m n. m IN N /\ n IN N ==> m * n IN N``,
  rw[setN_def, poly_intro_mult, coprime_product_coprime]);

(* Theorem alias *)
val setN_has_product = save_thm("setN_has_product", setN_closure);
(* val setN_has_product = |- !r k s. Ring r /\ 0 < k ==> !m n. m IN N /\ n IN N ==> m * n IN N: thm *)

(* Theorem: 1 < k ==> 0 NOTIN N *)
(* Proof:
   By contradiction. Let 0 IN N.
       0 IN N
   <=> coprime 0 k /\ poly_intro_range r k 0 s  by setN_element
   ==> k = 1                                    by GCD_0, coprime 0 k
   This contradicts 1 < k.
*)
val setN_has_no_0 = store_thm(
  "setN_has_no_0",
  ``!r:'a ring (k s):num. 1 < k ==> 0 NOTIN N``,
  rw[setN_element]);

(* Theorem: 0 < k ==> 1 IN N *)
(* Proof:
   This is to show:
   (1) coprime 1 k,       true by GCD_1
   (2) 1 intro (X + |c|), true by poly_intro_1, poly_X_add_c.
*)
val setN_has_1 = store_thm(
  "setN_has_1",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> 1 IN N``,
  rw[setN_def, poly_intro_1]);

(* Theorem: m IN N ==> m <> 0 *)
(* Proof: by setN_has_no_0 *)
val setN_element_nonzero = store_thm(
  "setN_element_nonzero",
  ``!r:'a ring (k s):num. 1 < k ==> !m. m IN N ==> m <> 0``,
  rw[setN_has_no_0]);

(* Theorem: p IN N ==> !n. p ** n IN N *)
(* Proof: by induction on n.
   Base case: p ** 0 IN N
     Since p ** 0 = 1          by EXP
     True by 1 IN N            by setN_has_1
   Step case: p ** n IN N ==> p ** SUC n IN N
     p ** SUC n = p * p ** n   by EXP
     p IN N                    by given
     p ** n IN N               by induction hypothesis
     Hence true                by setN_closure
*)
val setN_has_element_powers = store_thm(
  "setN_has_element_powers",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> !p. p IN N ==> !n. p ** n IN N``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[setN_has_1, EXP] >>
  rw[setN_closure, EXP]);

(* Theorem: p IN N /\ q IN N ==>
            !m n x y. (x, y) IN (count m) CROSS (count n) ==> p ** x * q ** y IN N *)
(* Proof:
   p ** x IN N    by setN_has_element_powers
   q ** y IN N    by setN_has_element_powers
   Hence true     by setN_closure
*)
val setN_has_element_pair_powers = store_thm(
  "setN_has_element_pair_powers",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> !p q. p IN N /\ q IN N ==>
   !m n x y. (x, y) IN (count m) CROSS (count n) ==> p ** x * q ** y IN N``,
  rw[setN_has_element_powers, setN_closure]);

(* Theorem: FiniteField r /\ 0 < k /\ coprime (char r) k ==> (char r) IN N *)
(* Proof: by setN_element, poly_intro_range_char. *)
val setN_has_char = store_thm(
  "setN_has_char",
  ``!r:'a field (k s):num. FiniteField r /\ 0 < k /\ coprime (char r) k ==> (char r) IN N``,
  metis_tac[setN_element, poly_intro_range_char]);

(* Theorem: FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
            char r divides n /\ n IN N ==> (char r) IN N /\ (n DIV char r) IN N *)
(* Proof:
   Note n IN N ==>
        coprime n k /\
        poly_intro_range r k n s     by setN_element
    Let p = char r, q = n DIV p.
   Note prime p                      by finite_field_char
     so 1 < p and 0 < p              by ONE_LT_PRIME
   Thus n = p * q                    by DIVIDES_EQN_COMM, 0 < p
    Now 1 < CARD R                   by finite_field_card_gt_1
     so 1 < k                        by ZN_order_with_coprime_1
   Also n <> 0                       by GCD_0, coprime n k
    and n <> 1                       by DIVIDES_ONE, p divides n
    ==> 1 < n                        by arithmetic

   Step 1: to show p IN N
   Note coprime p k                  by coprime_prime_factor_coprime, GCD_SYM, 1 < n, prime p, coprime n k
    and poly_intro_range r k p s     by poly_intro_X_add_c_prime_char_1, 0 < k, n intro X + |c|
    ==> p IN N                       by setN_element
   Step 2: to show q IN N
   Note coprime q k                  by coprime_product_coprime_iff], coprime p k, coprime (p * q) k
    and poly_intro_range r k q s     by poly_intro_X_add_c_prime_char_3, GCD_SYM, coprime k p, n intro X + |c|
    ==> q IN N                       by setN_element
*)
val setN_has_char_and_cofactor = store_thm(
  "setN_has_char_and_cofactor",
  ``!r:'a field (k s):num n. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N ==> (char r) IN N /\ (n DIV char r) IN N``,
  simp[setN_element] >>
  ntac 5 (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `q = n DIV p` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < p` by decide_tac >>
  `n = p * q` by metis_tac[DIVIDES_EQN_COMM] >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `n <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  `1 < n` by decide_tac >>
  `coprime p k` by metis_tac[coprime_prime_factor_coprime, GCD_SYM] >>
  `poly_intro_range r k p s` by rw[poly_intro_X_add_c_prime_char_1, Abbr`p`] >>
  `coprime q k` by metis_tac[coprime_product_coprime_iff] >>
  `poly_intro_range r k q s` by metis_tac[poly_intro_X_add_c_prime_char_3, GCD_SYM] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Set P = polynomials that are introspective to elements in Set N           *)
(* ------------------------------------------------------------------------- *)

(* P = {p | ((peval p X) ** m == peval p (X ** m)) (pm (X ** k - |1|)) for m IN N } *)
(* P = {p | m intro p, for m IN N } *)
val setP_def = Define`
  setP (r:'a ring) (k:num) (s:num) = {p | poly p /\ !m. m IN N ==> m intro p }
`;

(* overload for setP *)
val _ = overload_on ("P", ``setP (r:'a ring) k s``);

(* Theorem: !p. p IN P <=> poly p /\ !m. m IN N ==> m intro p *)
(* Proof: by setP_def. *)
val setP_element = store_thm(
  "setP_element",
  ``!r:'a ring (k s):num. !p. p IN P <=> poly p /\ (!m. m IN N ==> m intro p)``,
  rw[setP_def]);

(* Theorem: p IN P ==> poly p *)
(* Proof: by setP_def. *)
val setP_element_poly = store_thm(
  "setP_element_poly",
  ``!r:'a ring (k s):num. !p. p IN P ==> poly p``,
  rw[setP_def]);

(* export simple result *)
val _ = export_rewrites ["setP_element_poly"];

(* Theorem: 0 < k ==> !p q. p IN P /\ q IN P ==> p * q IN P *)
(* Proof: by poly_intro_compose *)
val setP_closure = store_thm(
  "setP_closure",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> !p q. p IN P /\ q IN P ==> p * q IN P``,
  rw[setP_def, poly_intro_compose]);

(* Theorem: Ring r /\ 1 < k ==> |0| IN P *)
(* Proof:
   By setP_element, poly_intro_def, this is to show:
   (1) poly |0|, true                    by poly_zero_poly
   (2) (|0| ** m == peval |0| (X ** m)) (pm (unity k))
       Note 0 NOTIN N                    by setN_has_no_0, 1 < k
         so m <> 0, or 0 < m             by m IN N
       Note m intro |0|                  by poly_intro_zero
*)
val setP_has_zero = store_thm(
  "setP_has_zero",
  ``!r:'a ring (k s):num. Ring r /\ 1 < k ==> |0| IN P``,
  rw_tac std_ss[setP_element] >-
  rw[] >>
  `0 NOTIN N` by rw[setN_has_no_0] >>
  `m <> 0` by metis_tac[] >>
  rw[poly_intro_zero]);

(* Theorem: 0 < k ==> |1| IN P *)
(* Proof:
   This is to show: m IN N ==> m intro |1|
   True by poly_intro_one, for any m.
*)
val setP_has_one = store_thm(
  "setP_has_one",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> |1| IN P``,
  rw[setP_def, poly_intro_one]);

(* Theorem: 0 < k ==> X IN P *)
(* Proof: by setP_element, poly_intro_X. *)
val setP_has_X = store_thm(
  "setP_has_X",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> X IN P``,
  rw[setP_element, poly_intro_X]);

(* Theorem: !c. 0 < c /\ c <= s ==>  X + |c| IN P *)
(* Proof:
   By setP_def and poly_intro_def, this is to show:
   (1) poly (X + |c|)
       Since poly X        by poly_X
         and poly |c|      by poly_sum_num_poly
        True by poly_add_poly
   (2) m IN N ==> m intro X + |c|
        True by setN_element
*)
val setP_has_X_add_c = store_thm(
  "setP_has_X_add_c",
  ``!r:'a ring (k s):num. Ring r ==> !c. 0 < c /\ c <= s ==> X + |c| IN P``,
  rw[setP_def] >>
  metis_tac[setN_element]);

(* ------------------------------------------------------------------------- *)
(* Define (finite) modulo versions of N and P: M and Q                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Set M = MOD k of the elements in Set N                                    *)
(* ------------------------------------------------------------------------- *)

(* Define M = IMAGE (MOD k) N. *)
val modN_def = Define`
  modN (r:'a ring) (k:num) (s:num) = IMAGE (\m. m MOD k) N
`;

(* overload for modN *)
val _ = overload_on ("M", ``modN (r:'a ring) k s``);

(* Theorem: M = { m MOD k | m IN N} *)
(* Proof: by modN_def. *)
val modN_alt = store_thm(
  "modN_alt",
  ``!r:'a ring k s:num. M = { m MOD k | m IN N}``,
  rw[modN_def, EXTENSION]);
(* presentation of M without IMAGE *)

(* Theorem: n IN M <=> ?m. (n = m MOD k) /\ m IN N *)
(* Proof: by modN_def. *)
val modN_element = store_thm(
  "modN_element",
  ``!r:'a ring (k s):num. !n. n IN M <=> ?m. (n = m MOD k) /\ m IN N``,
  rw[modN_def]);

(* Theorem: M is closed under MOD multiplication. *)
(* Proof:
   By modN_def,
   x IN M <=> ?m. m IN N /\ (x = m MOD k)
   y IN M <=> ?m'. m' IN N /\ (y = m' MOD k)
   Now,  (x * y) MOD k
       = ((m MOD k) * (m' MOD k)) MOD k       by above
       = (m * m') MOD k                       by MOD_TIMES2, 0 < k
   Since m * m' IN N                          by setN_closure
   hence (m * m') MOD k IN M                  by modN_def, IN_IMAGE
*)
val modN_closure = store_thm(
  "modN_closure",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==>
   !x y. x IN M /\ y IN M ==> (x * y) MOD k IN M``,
  rw[modN_def] >>
  rw[MOD_TIMES2] >>
  metis_tac[setN_closure]);

(* Theorem: 0 < k ==> M SUBSET (count k) *)
(* Proof: by image_mod_subset_count. *)
val modN_subset_count = store_thm(
  "modN_subset_count",
  ``!r:'a ring k s:num. 0 < k ==> M SUBSET (count k)``,
  rw[modN_def, image_mod_subset_count]);

(* Theorem: 0 < k ==> FINITE M *)
(* Proof: by modN_subset_count, SUBSET_FINITE, FINITE_count *)
val modN_finite = store_thm(
  "modN_finite",
  ``!r:'a ring (k s):num. 0 < k ==> FINITE M``,
  metis_tac[modN_subset_count, SUBSET_FINITE, FINITE_COUNT]);

(* Theorem: 0 < k ==> !n. n IN M ==> n < k *)
(* Proof:
   By modN_subset_count, SUBSET_DEF, IN_COUNT.
*)
val modN_element_less = store_thm(
  "modN_element_less",
  ``!r:'a ring (k s):num. 0 < k ==> !n. n IN M ==> n < k``,
  metis_tac[modN_subset_count, SUBSET_DEF, IN_COUNT]);

(* Theorem: 1 IN M *)
(* Proof:
   Since 1 IN N      by setN_has_1
   1 MOD k IN M      by modN_def, IN_IMAGE
   But 1 MOD k = 1   by ONE_MOD
   Hence true.
*)
val modN_has_1 = store_thm(
  "modN_has_1",
  ``!r:'a ring (k s):num. Ring r /\ 1 < k ==> 1 IN M``,
  rw[modN_def] >>
  metis_tac[setN_has_1, ONE_MOD, ONE_LT_POS]);

(* Theorem: 0 < k ==> M <> EMPTY *)
(* Proof:
   Note: modN_has_1 requires 1 < k, but this one takes 0 < k.
   Since 1 IN N                       by setN_has_1
   N <> EMPTY                         by MEMBER_NOT_EMPTY
   Since M = IMAGE (\m. m MOD k) N    by modN_def
   Hence M <> EMPTY                   by IMAGE_EQ_EMPTY
*)
val modN_not_empty = store_thm(
  "modN_not_empty",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k ==> M <> EMPTY``,
  rw[modN_def] >>
  metis_tac[setN_has_1, MEMBER_NOT_EMPTY]);
(* This version is better than using modN_has_1, as 1 < k is not required.
   Reason: at least modN has 1 MOD k, whatever k is.
*)

(* Theorem: 1 < k ==> 0 NOTIN M *)
(* Proof:
   By contradiction, let 0 IN M.
   Then ?m. (m MOD k = 0) /\ m IN N       by modN_def, IN_IMAGE
   Therefore gcd m k = k                  by GCD_MUTLIPLE
   But m IN N ==> coprime m k             by setN_element
   Hence k = 1, contradicting 1 < k.
*)
val modN_has_no_0 = store_thm(
  "modN_has_no_0",
  ``!r:'a ring (k s):num. 1 < k ==> 0 NOTIN M``,
  rw[modN_def, setN_def] >>
  spose_not_then strip_assume_tac >>
  `0 < k /\ k <> 1` by decide_tac >>
  metis_tac[GCD_MULTIPLE]);

(* Theorem: m IN N ==> m MOD k IN M *)
(* Proof: by modN_element *)
val setN_element_mod = store_thm(
  "setN_element_mod",
  ``!r:'a ring (k s):num. !m. m IN N ==> m MOD k IN M``,
  metis_tac[modN_element]);

(* Theorem: 1 < k ==> M SUBSET coprimes k *)
(* Proof:
   This is to show:
        !x. x IN M ==> x IN coprimes k     by SUBSET_DEF
    Now x IN M
    ==> ?m. (x = m MOD k) /\ m IN N        by modN_element
     so coprime m k                        by setN_element_coprime, m IN N
    ==> coprime x k                        by coprime_mod, coprime_sym, 0 < k
    and x < k                              by modN_element_less, 0 < k
   also x <> 0                             by modN_has_no_0, 1 < k
   Thus 0 < x /\ x <= k                    by arithmetic
    ==> x IN coprimes k                    by coprimes_element
*)
val modN_subset_coprimes = store_thm(
  "modN_subset_coprimes",
  ``!r:'a ring (k s):num. 1 < k ==> M SUBSET coprimes k``,
  rw[SUBSET_DEF] >>
  `?m. (x = m MOD k) /\ m IN N` by rw[GSYM modN_element] >>
  `0 < k` by decide_tac >>
  `coprime m k` by metis_tac[setN_element_coprime] >>
  `coprime x k` by metis_tac[coprime_mod, coprime_sym] >>
  `x < k` by metis_tac[modN_element_less] >>
  `x <> 0` by metis_tac[modN_has_no_0] >>
  `0 < x /\ x <= k` by decide_tac >>
  rw[coprimes_element]);

(* Theorem: 1 < k ==> M SUBSET Euler k *)
(* Proof:
   Note M SUBSET coprimes k     by modN_subset_coprimes, 1 < k
    and coprimes k = Euler k    by coprimes_eq_Euler, 1 < k
   The result follows.
*)
val modN_subset_euler = store_thm(
  "modN_subset_euler",
  ``!r:'a ring (k s):num. 1 < k ==> M SUBSET Euler k``,
  metis_tac[modN_subset_coprimes, coprimes_eq_Euler]);

(* Theorem: 1 < k ==> 1 IN M *)
(* Proof: by modN_has_1 *)
val modN_has_1_field = store_thm(
  "modN_has_1_field",
  ``!(r:'a field) k s:num. Field r /\ 1 < k ==> 1 IN M``,
  rw[modN_has_1]);

(* Theorem: 1 < k ==> M SUBSET Euler k *)
(* Proof: by modN_not_empty *)
val modN_not_empty_field = store_thm(
  "modN_not_empty_field",
  ``!(r:'a field) k s:num. Field r /\ 0 < k ==> M <> EMPTY``,
  rw[modN_not_empty]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound of M: Show M SUBSET (count k), eventually CARD M < k.         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < k ==> CARD M <= k *)
(* Proof:
   Since !n. n IN M ==> n < k        by modN_element_less
   Hence M SUBSET (count k)          by SUBSET_DEF, IN_COUNT
   Therefore  CARD M
           <= CARD (count k)         by CARD_SUBSET, FINITE_COUNT
            = k                      by CARD_COUNT
*)
val modN_card_upper_estimate = store_thm(
  "modN_card_upper_estimate",
  ``!r:'a ring k s:num. 0 < k ==> CARD M <= k``,
  metis_tac[modN_element_less, IN_COUNT, SUBSET_DEF, CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);
(* not used *)

(* Theorem: 1 < k ==> CARD M < k *)
(* Proof:
   Since   M SUBSET (count k)     by modN_subset_count
     and   FINITE (count k)       by FINITE_COUNT
     and   CARD (count k) = k     by CARD_COUNT
      So   CARD M <= k            by CARD_SUBSET

     But   0 IN (count k)         by IN_COUNT
     yet   0 NOTIN M              by modN_has_no_0
   Hence   M <> (count k)         by NOT_EQUAL_SETS
      So   CARD M <> k            by SUBSET_EQ_CARD
      or   CARD M < k             by arithmetic
*)
val modN_card_upper = store_thm(
  "modN_card_upper",
  ``!r:'a ring k s:num. 1 < k ==> CARD M < k``,
  rpt strip_tac >>
  `0 < k` by decide_tac >>
  `M SUBSET (count k)` by rw[modN_subset_count] >>
  `FINITE (count k) /\ (CARD (count k) = k) ` by rw[] >>
  `CARD M <= k` by metis_tac[CARD_SUBSET] >>
  `0 IN (count k)` by rw[] >>
  `0 NOTIN M` by rw[modN_has_no_0] >>
  `M <> (count k)` by metis_tac[NOT_EQUAL_SETS] >>
  `CARD M <> k` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  decide_tac);

(* Theorem: 1 < k ==> CARD M <= phi k *)
(* Proof:
   Note M SUBSET coprimes k           by modN_subset_coprimes
    and FINITE (coprimes k)           by coprimes_finite
    ==> CARD M <= CARD (coprimes k)   by CARD_SUBSET
     or CARD M <= phi k               by phi_def
*)
val modN_card_upper_better = store_thm(
  "modN_card_upper_better",
  ``!r:'a ring k s:num. 1 < k ==> CARD M <= phi k``,
  rpt strip_tac >>
  `M SUBSET coprimes k` by rw[modN_subset_coprimes] >>
  `FINITE (coprimes k)` by rw[coprimes_finite] >>
  rw[CARD_SUBSET, phi_def]);

(* ------------------------------------------------------------------------- *)
(* Lower Bound of M: Show Group M, eventually order (element) < CARD M       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < k ==> !n. n IN M ==> n IN (Invertibles (ZN k).prod).carrier *)
(* Proof:
   Since n IN M, ?m. (n = m MOD k) /\ m IN N     by modN_element
     but coprime m k                             by setN_element
   Hence n IN (Invertibles (ZN k).prod).carrier  by ZN_coprime_invertible
*)
val modN_element_invertible = store_thm(
  "modN_element_invertible",
  ``!r:'a ring k s:num. 1 < k ==>
      !n. n IN M ==> n IN (Invertibles (ZN k).prod).carrier``,
  metis_tac[modN_element, setN_element, ZN_coprime_invertible, coprime_sym]);

(* Theorem: !x y. x IN (Invertibles (ZN k).prod).carrier /\
                  y IN (Invertibles (ZN k).prod).carrier ==>
                  (x * y) MOD k IN (Invertibles (ZN k).prod).carrier *)

(* Theorem: 1 < k /\ x IN M ==> !n. (Invertibles (ZN k).prod).exp x n IN M *)
(* Proof:
   By induction on n.
   Base case: (Invertibles (ZN k).prod).exp x 0 IN M
        (Invertibles (ZN k).prod).exp x 0
      = (Invertibles (ZN k).prod).id          by monoid_exp_0
      = 1                                     by Invertibles_def, ZN_def
      But  1 IN M                             by modN_has_1
      Hence true.
   Step case: x IN M /\ (Invertibles (ZN k).prod).exp x n IN M ==>
              (Invertibles (ZN k).prod).exp x (SUC n) IN M
      Let y = ((Invertibles (ZN k).prod).exp x n)
      x IN M ==> x IN (Invertibles (ZN k).prod).carrier  by modN_element_invertible
      y IN M ==> y IN (Invertibles (ZN k).prod).carrier  by modN_element_invertible

        (Invertibles (ZN k).prod).exp x (SUC n)
      = (Invertibles (ZN k).prod).op x y      by monoid_exp_SUC
      = (x * y) MOD k                         by Invertibles_def, ZN_def, x y in carrier.
      But x IN M                              by given
          y IN M                              by induction hypothesis
       so (x * y) MOD k IN M                  by modN_closure
*)
val modN_has_element_powers = store_thm(
  "modN_has_element_powers",
  ``!r:'a ring k s:num. Ring r /\ 1 < k ==>
      !x. x IN M ==> !n. (Invertibles (ZN k).prod).exp x n IN M``,
  rpt strip_tac >>
  qabbrev_tac `t = (Invertibles (ZN k).prod).carrier` >>
  Induct_on `n` >| [
    `(Invertibles (ZN k).prod).id = 1` by rw[Invertibles_def, ZN_def, times_mod_def, monoid_exp_0] >>
    rw[modN_has_1],
    `!z. z IN M ==> z IN t` by metis_tac[modN_element_invertible] >>
    `!y z. y IN t /\ z IN t ==> ((Invertibles (ZN k).prod).op y z = (y * z) MOD k)`
  by rw_tac std_ss[Invertibles_def, monoid_invertibles_def, ZN_def, times_mod_def, Abbr`t`] >>
    `0 < k` by decide_tac >>
    rw_tac std_ss[monoid_exp_SUC, modN_closure]
  ]);

(* Theorem: !n. n IN M ==> (Generated (Invertibles (ZN k).prod) n).carrier SUBSET M *)
(* Proof:
   By Generated_def, SUBSET_DEF, this is to show:
   !m. (Invertibles (ZN k).prod).exp n m IN M
   which is true by modN_has_element_powers.
*)
val modN_has_generator_of_element = store_thm(
  "modN_has_generator_of_element",
  ``!r:'a ring k s:num. Ring r /\ 1 < k ==>
   !n. n IN M ==> (Generated (Invertibles (ZN k).prod) n).carrier SUBSET M``,
  rw[Generated_def, SUBSET_DEF] >>
  rw[modN_has_element_powers]);

(* Theorem: 1 < k ==> !n. n IN N ==> ordz k n <= CARD M  *)
(* Proof:
   Since     (n MOD k) IN M                           by setN_element_mod
   We have   (Generated (Invertibles (ZN k).prod) (n MOD k)).carrier
             SUBSET M                                 by modN_has_generator_of_element
   Also      (n MOD k) IN (Invertibles (ZN k).prod).carrier        by ZN_coprime_invertible
   Therefore
     ord z k n
   = order (ZN k).prod n                                           by notation
   = order (ZN k).prod (n MOD k)                                   by ZN_order_mod
   = order (Invertibles (ZN k).prod) (n MOD k)                     by monoid_inv_order
   = CARD (Generated (Invertibles (ZN k).prod) (n MOD k)).carrier  by generated_group_card, group_order_pos
   <= CARD M                                                       by CARD_SUBSET
*)
val modN_card_lower = store_thm(
  "modN_card_lower",
  ``!r:'a ring k s:num. Ring r /\ 1 < k ==>
   !n. n IN N ==> ordz k n <= CARD M``,
  rpt strip_tac >>
  `(n MOD k) IN M` by rw[setN_element_mod] >>
  `(Generated (Invertibles (ZN k).prod) (n MOD k)).carrier SUBSET M` by rw[modN_has_generator_of_element] >>
  `coprime k n` by metis_tac[setN_element, coprime_sym] >>
  `(n MOD k) IN (Invertibles (ZN k).prod).carrier` by rw[ZN_coprime_invertible] >>
  `0 < k` by decide_tac >>
  `FiniteGroup (Invertibles (ZN k).prod)` by rw[ZN_invertibles_finite_group] >>
  `Group (Invertibles (ZN k).prod)` by rw[finite_group_is_group] >>
  `CARD (Generated (Invertibles (ZN k).prod) (n MOD k)).carrier =
    order (Invertibles (ZN k).prod) (n MOD k)` by rw[GSYM generated_group_card, group_order_pos] >>
  `FINITE M` by rw[modN_finite] >>
  metis_tac[CARD_SUBSET, ZN_invertibles_order]);

(* Theorem: 1 < k ==> !n. n IN N ==> ordz k n <= CARD M /\ CARD M < k *)
(* Proof: by modN_card_lower, modN_card_upper. *)
val modN_card_bounds = store_thm(
  "modN_card_bounds",
  ``!r:'a ring k s:num. Ring r /\ 1 < k ==>
      !n. n IN N ==> ordz k n <= CARD M /\ CARD M < k``,
  rw[modN_card_lower, modN_card_upper]);

(* Theorem: 1 < k ==> !n. n IN N ==> ordz k n <= CARD M /\ CARD M <= phi k *)
(* Proof: by modN_card_lower, modN_card_upper_better. *)
val modN_card_bounds_better = store_thm(
  "modN_card_bounds_better",
  ``!r:'a ring k s:num. Ring r /\ 1 < k ==>
      !n. n IN N ==> ordz k n <= CARD M /\ CARD M <= phi k``,
  rw[modN_card_lower, modN_card_upper_better]);

(*
LOG_MOD   |- !n. 0 < n ==> (n = 2 ** LOG2 n + n MOD 2 ** LOG2 n)
LOG       |- !a n. 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
LOG_ADD1  |- !n a b. 0 < n /\ 1 < a /\ 0 < b ==> LOG a (a ** SUC n * b) = SUC (LOG a (a ** n * b))
LOG_BASE  |- !a. 1 < a ==> (LOG a a = 1)
LOG_EXP   |- !n a b. 1 < a /\ 0 < b ==> (LOG a (a ** n * b) = n + LOG a b)
*)

(* Theorem: 1 < k /\ (?n. 1 < n /\ n IN N /\ (2 * (LOG2 n)) ** 2 < ordz k n ==> 1 < CARD M *)
(* Proof:
       n IN N
   ==> order (ZN k).prod n <= CARD M   by modN_card_lower
   Given  (2 * (LOG2 (MAX p q))) ** 2 < ordz k n
     and  4 <= (2 * (LOG2 n)) ** 2
   Hence  1 < 4 <= CARD M              by LESS_LESS_EQ_TRANS
*)
val modN_card_gt_1_condition = store_thm(
  "modN_card_gt_1_condition",
  ``!r:'a ring k s:num. Ring r /\ 1 < k /\
    (?n. 1 < n /\ n IN N /\ (2 * (LOG2 n)) ** 2 < ordz k n) ==> 1 < CARD M``,
  rpt strip_tac >>
  `ordz k n <= CARD M` by rw[modN_card_lower] >>
  `4 <= (2 * (LOG2 n)) ** 2` by rw[LOG2_TWICE_SQ] >>
  decide_tac);

(* Theorem: Ring r /\ 1 < k /\ 1 < n /\ n IN N /\
            (2 * LOG2 n) ** 2 <= ordz k n ==> 1 < CARD M *)
(* Proof:
   Note ordz k n <= CARD M            by modN_card_lower, 1 < k, n IN N
   Given  (2 * (LOG2 n)) ** 2 <= ordz k n
     and  4 <= (2 * (LOG2 n)) ** 2    by LOG2_TWICE_SQ
   Hence  1 < 4 <= CARD M             by LESS_LESS_EQ_TRANS
*)
val modN_card_gt_1_by_LOG2 = store_thm(
  "modN_card_gt_1_by_LOG2",
  ``!(r:'a ring) k n s:num. Ring r /\
    1 < k /\ 1 < n /\ n IN N /\ (2 * LOG2 n) ** 2 <= ordz k n ==> 1 < CARD M``,
  rpt strip_tac >>
  `ordz k n <= CARD M` by rw[modN_card_lower] >>
  `4 <= (2 * (LOG2 n)) ** 2` by rw[LOG2_TWICE_SQ] >>
  decide_tac);

(* Theorem: Ring r /\ 1 < k /\ 1 < n /\ n IN N /\
            (2 * ulog n) ** 2 <= ordz k n ==> 1 < CARD M *)
(* Proof:
   Note ordz k n <= CARD M            by modN_card_lower, 1 < k, n IN N
   Given  (2 * ulog n) ** 2 <= ordz k n
     and  4 <= (2 * ulog n) ** 2      by ulog_twice_sq
   Hence  1 < 4 <= CARD M             by LESS_LESS_EQ_TRANS
*)
val modN_card_gt_1_by_ulog = store_thm(
  "modN_card_gt_1_by_ulog",
  ``!(r:'a ring) k n s:num. Ring r /\
    1 < k /\ 1 < n /\ n IN N /\ (2 * ulog n) ** 2 <= ordz k n ==> 1 < CARD M``,
  rpt strip_tac >>
  `ordz k n <= CARD M` by rw[modN_card_lower] >>
  `4 <= (2 * ulog n) ** 2` by rw[ulog_twice_sq] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Set (Q z) = MOD z of the polynomials in P                                 *)
(* ------------------------------------------------------------------------- *)

(* Define Q z = IMAGE (pmod z) P. *)
val modP_def = Define`
  modP (r:'a ring) (k:num) (s:num) (z:'a poly) = IMAGE (\p. p % z) P
`;
(* Note: s is hidden in set P for the range. *)
(* overload for modP *)
val _ = overload_on ("Q", ``modP (r:'a ring) k s``);

(* Theorem: Q z = { p % z | p IN P } *)
(* Proof: by modP_def *)
val modP_alt = store_thm(
  "modP_alt",
  ``!r:'a ring k:num s:num z. Q z = { p % z | p IN P }``,
  rw[modP_def, EXTENSION]);
(* presentation of (Q h) without IMAGE *)

(* Theorem: p IN (Q z) ==> ?q. q IN P /\ (p = q % z) *)
(* Proof: by modP_def, IN_IMAGE *)
val modP_element = store_thm(
  "modP_element",
  ``!r:'a ring (k s):num z. !p. p IN (Q z) <=> ?q. q IN P /\ (p = q % z)``,
  rw[modP_def] >>
  metis_tac[]);

(* Theorem: p IN (Q z) ==> poly p /\ deg p < deg z *)
(* Proof:
       p IN Q z
   ==> ?p'. p' IN P /\ (p = p' % z)    by modP_element
   ==> poly p' /\ (p = p' % z)         by setP_element_poly
   ==> poly p /\ deg p < deg z         by poly_mod_poly, poly_deg_mod_less
*)
val modP_element_poly = store_thm(
  "modP_element_poly",
  ``!r:'a ring (k s):num. Ring r ==>
   !z. pmonic z ==> !p. p IN (Q z) ==> poly p /\ deg p < deg z``,
  metis_tac[modP_element, setP_element_poly, poly_mod_poly, poly_deg_mod_less]);

(* Theorem: (Q z) is closed under poly_mod multiplication:
            0 < k /\ ulead z ==> !p q . p IN (Q z) /\ q IN (Q z) ==> (p * q) % z IN (Q z) *)
(* Proof:
   By modP_def,
   p IN (Q z)  <=> ?p'. p' IN P /\ (p = p' % z)
   q IN (Q z)  <=> ?q'. q' IN P /\ (q = q' % z)
   Since  p' IN P ==> poly p'              by setP_element_poly
     and  q' IN P ==> poly q'              by setP_element_poly
   Hence  p' % z * q' % z = (p' * q') % z  by poly_mod_mult, ulead z
     and  p' * q' IN P                     by setP_closure
*)
val modP_closure = store_thm(
  "modP_closure",
  ``!r:'a ring (k s):num z. Ring r /\ 0 < k /\ ulead z ==>
    !p q. p IN (Q z) /\ q IN (Q z) ==> (p * q) % z IN (Q z)``,
  rw[modP_def] >>
  metis_tac[poly_mod_mult, setP_closure, setP_element_poly]);

(* Theorem: pmonic z ==> (Q z) SUBSET (PolyModRing r z).carrier *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) p IN P ==> poly (p % z)
       p IN P ==> poly p                             by setP_element_poly
       poly p /\ pmonic z ==> poly (p % z)           by poly_mod_poly
   (2) p IN P ==> deg (p % z) < deg z
       p IN P ==> poly p                             by setP_element_poly
       poly p /\ pmonic z ==> deg (p % z) < deg z    by poly_deg_mod_less
*)
val modP_subset_mod_factor = store_thm(
  "modP_subset_mod_factor",
  ``!r:'a ring (k s):num z. Ring r /\ pmonic z ==> (Q z) SUBSET (PolyModRing r z).carrier``,
  rw[modP_def, poly_mod_ring_def, poly_remainders_def, SUBSET_DEF] >-
  metis_tac[setP_element_poly, poly_mod_poly] >>
  metis_tac[setP_element_poly, poly_deg_mod_less]);

(* Theorem: 1 < k /\ ulead z ==> |0| IN (Q z) *)
(* Proof:
   Note |0| IN P              by setP_has_zero, 1 < k
    and |0| % z = |0|         by poly_mod_zero, ulead z
   Thus |0| IN (Q z)          by modP_element
*)
val modP_has_zero = store_thm(
  "modP_has_zero",
  ``!r:'a ring (k s):num z. Ring r /\ 1 < k /\ ulead z ==> |0| IN (Q z)``,
  rpt strip_tac >>
  `|0| IN P` by rw[setP_has_zero] >>
  `|0| % z = |0|` by rw[poly_mod_zero] >>
  metis_tac[modP_element]);

(* Theorem: pmonic z ==> |1| IN (Q z) *)
(* Proof:
   Note |1| IN P              by setP_has_one, 0 < k
    and |1| % z = |1|         by poly_mod_one, pmonic z
   Thus |1| IN (Q z)          by modP_element
*)
val modP_has_one = store_thm(
  "modP_has_one",
  ``!r:'a ring (k s):num z. Ring r /\ 0 < k /\ pmonic z ==> |1| IN (Q z)``,
  rpt strip_tac >>
  `|1| IN P` by rw[setP_has_one] >>
  `|1| % z = |1|` by rw[poly_mod_one] >>
  metis_tac[modP_element]);

(* Theorem: 0 < k /\ monic z /\ 1 < deg z ==> X IN (Q z) *)
(* Proof:
   By modP_element, this is to show:
      ?q. q IN P /\ (X = q % z)
   Take q = X.
   Then X IN P      by setP_has_X
   Note #1 <> #0    by poly_deg_pos_ring_one_ne_zero, 0 < deg z
    and deg X = 1   by poly_deg_X, #1 <> #0
    and X = X % z   by poly_mod_less, deg X < deg z
*)
val modP_has_X = store_thm(
  "modP_has_X",
  ``!r:'a ring (k s):num z. Ring r /\ 0 < k /\ monic z /\ 1 < deg z ==> X IN (Q z)``,
  rw_tac std_ss[modP_element] >>
  `0 < deg z` by decide_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero, poly_monic_poly] >>
  qexists_tac `X` >>
  rw[setP_has_X, poly_mod_less]);

(* Theorem: FiniteRing r /\ pmonic z ==> FINITE (Q z) *)
(* Proof:
   pmonic z means 0 < deg z                                  by notation
   FiniteRing r /\ 0 < deg z
    ==> FINITE (PolyModRing r z).carrier                     by poly_mod_ring_finite
   Also, FiniteRing r
          ==> Ring r                                         by FiniteRing_def
   with pmonic z ==> (Q z) SUBSET (PolyModRing r z).carrier  by modP_subset_mod_factor
   Hence FINITE (Q z)                                        by SUBSET_FINITE
*)
val modP_finite = store_thm(
  "modP_finite",
  ``!r:'a ring (k s):num z. FiniteRing r /\ pmonic z ==> FINITE (Q z)``,
  metis_tac[modP_subset_mod_factor, poly_mod_ring_finite, FiniteRing_def, SUBSET_FINITE]);

(* Theorem: p IN P ==> p % z IN (Q z) *)
(* Proof: by modP_def, IN_IMAGE *)
val setP_element_mod = store_thm(
  "setP_element_mod",
  ``!r:'a ring (k s):num. !p z. p IN P ==> p % z IN (Q z)``,
  rw[modP_def] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* The Reduced Set from P.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the reduced set of poly IN P of deg < CARD A0 *)
val reduceP_def = Define`
  reduceP (r:'a ring) (k:num) (s:num) = {p | p IN P /\ deg p < CARD M }
`;

(* overload for reduceP *)
val _ = overload_on ("PM", ``reduceP (r:'a ring) k s``);

(* Theorem: !p. p IN PM <=> p IN P /\ deg p < CARD M *)
(* Proof: by reduceP_def *)
val reduceP_element = store_thm(
  "reduceP_element",
  ``!r:'a ring (k s):num p. p IN PM <=> p IN P /\ deg p < CARD M``,
  rw[reduceP_def]);

(* Theorem: p IN PM ==> p % z IN (Q z) *)
(* Proof:
       p IN PM
   ==> p IN P          by reduceP_element
   ==> p % z IN (Q z)  by setP_element_mod
*)
val reduceP_element_mod = store_thm(
  "reduceP_element_mod",
  ``!r:'a ring (k s):num z. !p. p IN PM ==> p % z IN (Q z)``,
  rw[reduceP_element, setP_element_mod]);

(* Theore: p IN PM ==> poly p *)
(* Proof:
       p IN PM
   ==> p IN P     by reduceP_element
   ==> poly p     by setP_element_poly
*)
val reduceP_element_poly = store_thm(
  "reduceP_element_poly",
  ``!r:'a ring (k s):num. !p. p IN PM ==> poly p``,
  metis_tac[reduceP_element, setP_element_poly]);

(* export simple result *)
val _ = export_rewrites ["reduceP_element_poly"];

(* Theorem: PM SUBSET P *)
(* Proof: by reduceP_def, SUBSET_DEF. *)
val reduceP_subset_setP = store_thm(
  "reduceP_subset_setP",
  ``!r:'a ring (k s):num. PM SUBSET P``,
  rw[reduceP_def, SUBSET_DEF]);

(* Theorem: FiniteRing r ==> FINITE PM *)
(* Proof:
   !p. p IN PM
   ==> p IN P /\ deg p < CARD M                            by reduceP_element
   ==> poly p /\ deg p < CARD M                            by setP_element_poly
   Let n = CARD M,
   Then PM SUBSET {p | poly p /\ ((p = []) \/ deg p < n)}  by SUBSET_DEF
   which is BIJ with {p | weak p /\ (LENGTH p = n)}        by weak_poly_poly_bij
   Since FINITE {p | weak p /\ (LENGTH p = n)}             by weak_poly_finite
      so FINITE {p | poly p /\ ((p = []) \/ deg p < n)}    by FINITE_BIJ
   Hence FINITE PM                                         by SUBSET_FINITE
*)
val reduceP_finite = store_thm(
  "reduceP_finite",
  ``!r:'a ring (k s):num. FiniteRing r ==> FINITE PM``,
  rpt (stripDup[FiniteRing_def]) >>
  qabbrev_tac `n = CARD M` >>
  `PM SUBSET {p | poly p /\ ((p = []) \/ deg p < n)}` by rw[SUBSET_DEF, reduceP_element, setP_element] >>
  `BIJ chop {p | weak p /\ (LENGTH p = n)} {p | poly p /\ ((p = []) \/ deg p < n)}` by rw[weak_poly_poly_bij] >>
  `FINITE {p | weak p /\ (LENGTH p = n)}` by rw[weak_poly_finite] >>
  `FINITE {p | poly p /\ ((p = []) \/ deg p < n)}` by metis_tac[FINITE_BIJ] >>
  metis_tac[SUBSET_FINITE]);

(* Theorem: 1 < k ==> |0| IN PM *)
(* Proof:
   By reduceP_element, this is to show:
   (1) |0| IN P
       By setP_element, this is to show:
       (1) poly |0|, true by poly_zero_poly
       (2) m IN N ==> m intro |0|
           m IN N ==> m <> 0              by setN_has_no_0
           or  0 < m, hence m intro |0|   by poly_intro_zero
   (2) deg |0| < CARD M
       Since deg |0| = 0                  by poly_deg_zero,
       and M <> {}                        by modN_not_empty
       Hence 0 < CARD M                   by CARD_EQ_0
*)
val reduceP_has_zero = store_thm(
  "reduceP_has_zero",
  ``!r:'a ring (k s):num. Ring r /\ 1 < k ==> |0| IN PM``,
  rpt strip_tac >>
  `0 < k` by decide_tac >>
  rw_tac std_ss[reduceP_element, setP_element, poly_zero_poly, poly_deg_zero] >-
  metis_tac[setN_has_no_0, poly_intro_zero, NOT_ZERO_LT_ZERO] >>
  metis_tac[modN_finite, modN_not_empty, CARD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < k /\ 1 < CARD M ==> X IN PM *)
(* Proof:
   By reduceP_element, this is to show:
   (1) X IN P, true                    by setP_has_X.
   (2) deg X < CARD M
       If #1 = #0,
          Then |1| = |0|               by poly_one_eq_poly_zero
            so |X| = |0|               by poly_one_eq_zero, poly_X
           and deg X = 0 < CARD M      by poly_deg_zero
       If #1 <> #0,
          Then deg X = 1 < CARD M      by poly_deg_X
*)
val reduceP_has_X = store_thm(
  "reduceP_has_X",
  ``!r:'a ring (k s):num. Ring r /\ 0 < k /\ 1 < CARD M ==> X IN PM``,
  rw_tac std_ss[reduceP_element] >-
  rw[setP_has_X] >>
  Cases_on `#1 = #0` >| [
    `X = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_X] >>
    rw[],
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* The Reduced Set from N.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the reduced set of exponents in N with indexes <= n, later n = sqrt(CARD M) *)
val reduceN_def = Define`
  reduceN (p:num) (q:num) n =
     IMAGE (\(i, j). p ** i * q ** j) ((count (SUC n)) CROSS (count (SUC n)))
`;
(* Note: indexes from 0 to n inclusive. *)

(* overload for reduceN *)
val _ = overload_on ("NM", ``reduceN``);

(* Theorem: NM p q n = {(p ** i) * (q ** j) | i, j | i <= n /\ j <= n} *)
(* Proof:
   By reduceN_def, this is to show:
   (1) FST x' < SUC n /\ SND x' < SUC n ==> ?i.j. ... i <= n /\ j <= n
       Take i = FST x', j = SND x'.
   (2) i <= n /\ j <= n ==> ?x'. FST y < SUC n /\ SND y < SUC n
       Take x' = (i, j)
*)
val reduceN_alt = store_thm(
  "reduceN_alt",
  ``!p q n. NM p q n = {(p ** i) * (q ** j) | i, j | i <= n /\ j <= n}``,
  rw[reduceN_def, EXTENSION, EQ_IMP_THM] >| [
    `FST x' <= n /\ SND x' <= n` by decide_tac >>
    qexists_tac `FST x'` >>
    qexists_tac `SND x'` >>
    rw[pairTheory.UNCURRY],
    `i < SUC n /\ j < SUC n` by decide_tac >>
    qexists_tac `(i,j)` >>
    rw[]
  ]);

(* Theorem: FINITE (NM p q n) *)
(* Proof:
   Let c = count (SUC n), f = \(i, j). p ** i * q ** j.
     FINITE (NM p q n)
   = FINITE (IMAGE f (c CROSS c))        by reduceN_def
   Since FINITE c                        by FINITE_COUNT
     ==> FINITE (c CROSS c)              by FINITE_CROSS
     ==> FINITE (IMAGE f (c CROSS c))    by IMAGE_FINITE
       = FINITE (NM p q n)               by above
*)
val reduceN_finite = store_thm(
  "reduceN_finite",
  ``!p q n. FINITE (NM p q n)``,
  rw[reduceN_def]);

(* Theorem: x IN NM p q n ==> ?m1 m2. m1 <= n /\ m2 <= n /\ (x = p ** m1 * q ** m2) *)
(* Proof: by reduceN_def, IN_IMAGE *)
val reduceN_element = store_thm(
  "reduceN_element",
  ``!p q n. !x. x IN NM p q n ==> ?m1 m2. m1 <= n /\ m2 <= n /\ (x = p ** m1 * q ** m2)``,
  rw[reduceN_def, IN_IMAGE] >>
  `FST x' <= n /\ SND x' <= n` by decide_tac >>
  Cases_on `x'` >>
  fs[] >>
  metis_tac[]);

(* Theorem: p IN N /\ q IN N ==> !n. (NM p q n) SUBSET N *)
(* Proof:
   Let x IN (NM p q n)
   then ?m1 m2. m1 <= n /\ m2 <= n /\ (x = p ** m1 * q ** m2)   by reduceN_element
   p ** m1 IN N       by setN_has_element_powers
   q ** m2 IN N       by setN_has_element_powers
   Hence x IB N       by setN_closure
*)
val reduceN_subset_setN = store_thm(
  "reduceN_subset_setN",
  ``!r:'a ring k s:num. Ring r /\ 0 < k ==>
   !p q. p IN N /\ q IN N ==> !n. (NM p q n) SUBSET (N)``,
  rw[SUBSET_DEF] >>
  `?m1 m2. m1 <= n /\ m2 <= n /\ (x = p ** m1 * q ** m2)` by rw[reduceN_element] >>
  rw[setN_has_element_powers, setN_closure]);

(* Theorem: 0 < k ==> !p q. p IN N /\ q IN N ==> !n x. x IN (NM p q n) ==> x IN N *)
(* Proof: by reduceN_subset_setN, SUBSET_DEF. *)
val reduceN_element_in_setN = store_thm(
  "reduceN_element_in_setN",
  ``!r:'a ring k s:num. Ring r /\ 0 < k ==>
   !p q. p IN N /\ q IN N ==> !n x. x IN (NM p q n) ==> x IN N``,
  rw[reduceN_subset_setN, GSYM SUBSET_DEF]);

(* Theorem: Ring r /\ 0 < k ==>
           !p q. p IN N /\ q IN N ==> IMAGE (\x. x MOD k) (NM p q (SQRT (CARD M))) SUBSET M *)
(* Proof: by reduceN_def, SUBSET_DEF, modN_element. *)
val reduceN_mod_subset = store_thm(
  "reduceN_mod_subset",
  ``!r:'a ring k. Ring r /\ 0 < k ==>
   !p q. p IN N /\ q IN N ==> IMAGE (\x. x MOD k) (NM p q (SQRT (CARD M))) SUBSET M``,
  rw[reduceN_def, SUBSET_DEF, pairTheory.EXISTS_PROD] >>
  `p ** p_1 * q ** p_2 IN N` by rw[setN_has_element_powers, setN_closure] >>
  metis_tac[modN_element]);

(* Theorem: 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= (MAX p q) ** (2 * n) *)
(* Proof:
   1 < p /\ 1 < q ==> 1 < MAX p q           by MAX_LT
   By reduceN_def, this is to show:
   FST x < SUC n /\ SND x < SUC n ==> p ** FST x * q ** SND x < MAX p q ** (2 * n)
   i.e.  FST x <= n /\ SND x <= n ==> p ** FST x * q ** SND x < MAX p q ** (2 * n)
   Now, p <= MAX p q, and q <= MAX p q,     by MAX_LE
    So  p ** FST x <= (MAX p q) ** FST x    by EXP_EXP_LE_MONO
                   <= (MAX p q) ** n        by EXP_BASE_LE_MONO
        q ** SND x <= (MAX p q) ** SND x    by EXP_EXP_LE_MONO
                   <= (MAX p q) ** n        by EXP_BASE_LE_MONO
       p ** FST x * q ** SND x
    <= (MAX p q) ** n * (MAX p q) ** n      by LE_MULT_LCANCEL, ZERO_LT_EXP, LESS_EQ_TRANS
    = (MAX p q) ** (n + n)                  by EXP_ADD
    = (MAX p q) ** (2 * n)                  by TIMES2
*)
val reduceN_element_upper = store_thm(
  "reduceN_element_upper",
  ``!p q. 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= (MAX p q) ** (2 * n)``,
  rw_tac std_ss[reduceN_def, IN_IMAGE, pairTheory.EXISTS_PROD] >>
  fs[] >>
  `p_1 <= n /\ p_2 <= n` by decide_tac >>
  `1 < MAX p q` by rw[] >>
  `p <= MAX p q` by rw[] >>
  `q <= MAX p q` by rw[] >>
  `p ** p_1 <= (MAX p q) ** p_1` by rw[] >>
  `(MAX p q) ** p_1 <= (MAX p q) ** n` by rw[EXP_BASE_LE_MONO] >>
  `p ** p_1 <= (MAX p q) ** n` by metis_tac[LESS_EQ_TRANS] >>
  `q ** p_2 <= (MAX p q) ** p_2` by rw[] >>
  `(MAX p q) ** p_2 <= (MAX p q) ** n` by rw[EXP_BASE_LE_MONO] >>
  `q ** p_2 <= (MAX p q) ** n` by metis_tac[LESS_EQ_TRANS] >>
  `0 < p /\ 0 < q` by decide_tac >>
  `p ** p_1 * q ** p_2 <= p ** p_1 * (MAX p q) ** n` by rw[LE_MULT_LCANCEL, ZERO_LT_EXP] >>
  `p ** p_1 * (MAX p q) ** n <= (MAX p q) ** n * (MAX p q) ** n` by rw[] >>
  `p ** p_1 * q ** p_2 <= (MAX p q) ** n * (MAX p q) ** n` by metis_tac[LESS_EQ_TRANS] >>
  rw_tac std_ss[EXP_ADD, TIMES2]);

(* Theorem: 1 < p /\ p <= n ==> !e m. e IN NM p n m ==> e <= n ** (2 * m) *)
(* Proof: by reduceN_element_upper. *)
val reduceN_element_upper_alt = store_thm(
  "reduceN_element_upper_alt",
  ``!n p. 1 < p /\ p <= n ==> !e m. e IN NM p n m ==> e <= n ** (2 * m)``,
  rpt strip_tac >>
  `1 < n` by decide_tac >>
  metis_tac[MAX_DEF, reduceN_element_upper, NOT_LESS, EQ_LESS_EQ]);

(* Theorem: 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= (p * q) ** n *)
(* Proof:
   By reduceN_def, this is to show:
   FST x < SUC n /\ SND x < SUC n ==> p ** FST x * q ** SND x < (p * q) ** n
   i.e., FST x <= n /\ SND x <= n ==> p ** FST x * q ** SND x < (p * q) ** n

   Now p ** FST x <= p ** n        by EXP_BASE_LE_MONO, 1 < p
   and q ** SND x <= q ** n        by EXP_BASE_LE_MONO, 1 < q
       p ** FST x * q ** SND x
    <= p ** n * q ** n             by LESS_MONO_MULT2
     = (p * q) ** n                by EXP_BASE_MULT
*)
val reduceN_element_upper_better = store_thm(
  "reduceN_element_upper_better",
  ``!p q. 1 < p /\ 1 < q ==> !m n. m IN NM p q n ==> m <= (p * q) ** n``,
  rw_tac std_ss[reduceN_def, IN_IMAGE, pairTheory.EXISTS_PROD] >>
  fs[] >>
  `p_1 <= n /\ p_2 <= n` by decide_tac >>
  `p ** p_1 <= p ** n` by rw[EXP_BASE_LE_MONO] >>
  `q ** p_2 <= q ** n` by rw[EXP_BASE_LE_MONO] >>
  `p ** p_1 * q ** p_2 <= p ** n * q ** n` by rw[LESS_MONO_MULT2] >>
  rw[EXP_BASE_MULT]);

(* ------------------------------------------------------------------------- *)
(* Cardinality of Reduced Set of N.                                          *)
(* ------------------------------------------------------------------------- *)

(*
   Let s = n INSERT (count n) = count (SUC n), by reduceN_def
   NM p q n = IMAGE (\(i,j). p ** i * q ** j) (count (SUC n) CROSS count (SUC n))
   Show that the map is injective if: prime p /\ 1 < q /\ ~(perfect_power q p)
*)

(* Theorem: Ring r /\ 0 < k ==>
            !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~(perfect_power q p) ==>
            !n. INJ (\(i, j). p ** i * q ** j) ((count (SUC n)) CROSS (count (SUC n))) N *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) p IN N /\ q IN N ==> p ** FST y * q ** SND y IN N, where y = (i, j)
       p IN N ==> p ** FST y IN N   by setN_has_element_powers
       q IN N ==> q ** FST y IN N   by setN_has_element_powers
       Hence true                   by setN_closure.
   (2) p IN N /\ q IN N /\
       p ** FST y * q ** SND y = p ** FST y' * q ** SND y' ==> y = y'
       Let y = (u, v), y' = (w, x), to show:
           p ** u * q ** v = p ** w * q ** x ==> u = w /\ v = x    by PAIR_FST_SND_EQ
       Note 1 < p, and 1 < q                  by ONE_LT_PRIME, given
         so 0 < p, and 0 < q, p <> 1, and q <> 1

       With given: p ** u * q ** v = p ** w * q ** x
       If u = w, to show v = x,
          Since 0 < p ** u                    by EXP_POS
          gives q ** v = q ** x               by MULT_LEFT_CANCEL
          hence v = x                         by EXP_BASE_INJECTIVE, with 1 < p
       If u < w,
          ?d. 0 < d and (q ** v = p ** d * q ** x)   by EXP_LCANCEL
          If v = x, this reduces to
              p ** d = 1                             by MULT_RIGHT_CANCEL
          But p ** d <> 1 since p <> 1               by EXP_EQ_1
          Hence a contradiction.
          If v < x,
             ?e. 0 < e /\ (1 = p ** d * q ** e)      by EXP_RCANCEL
          So  p ** d = 1                             by MULT_EQ_1
          But p ** d <> 1 since p <> 1               by EXP_EQ_1
          Hence a contradiction.
          If x < v,
            ?e. 0 < e /\ (p ** d = q ** e)           by EXP_RCANCEL
          So perfect_power q p                       by perfect_power_condition, prime p
          But this contradicts ~perfect_power q p.
      If w < u, the proof is symmetric (similar to u < w cases).
*)
val count_cross_to_setN_inj = store_thm(
  "count_cross_to_setN_inj",
  ``!r:'a ring k s:num. Ring r /\ 0 < k ==>
   !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~(perfect_power q p) ==>
   !n. INJ (\(i, j). p ** i * q ** j) ((count (SUC n)) CROSS (count (SUC n))) N``,
  rw[INJ_DEF] >| [
    Cases_on `x` >>
    fs[] >>
    rw[setN_has_element_powers, setN_closure],
    Cases_on `x` >>
    Cases_on `y` >>
    fs[] >>
    `!n. 0 < n <=> n <> 0` by decide_tac >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `0 < p /\ 0 < q /\ p <> 1 /\ q <> 1` by decide_tac >>
    `!h. 0 < p ** h /\ 0 < q ** h` by rw[EXP_POS] >>
    spose_not_then strip_assume_tac >>
    Cases_on `q' = q''` >| [
      `q ** r' = q ** r''` by metis_tac[MULT_LEFT_CANCEL] >>
      `r' = r''` by metis_tac[EXP_BASE_INJECTIVE] >>
      metis_tac[],
      Cases_on `q'' < q'` >| [
        `?d. 0 < d /\ (q ** r'' = p ** d * q ** r')` by metis_tac[EXP_LCANCEL] >>
        Cases_on `r' = r''` >| [
          `p ** d = 1` by metis_tac[MULT_RIGHT_CANCEL, MULT_LEFT_1] >>
          metis_tac[EXP_EQ_1],
          Cases_on `r'' < r'` >| [
            `?e. 0 < e /\ (1 = p ** d * q ** e)` by metis_tac[EXP_RCANCEL, MULT_LEFT_1] >>
            `p ** d = 1` by metis_tac[MULT_EQ_1] >>
            metis_tac[EXP_EQ_1],
            `r' < r'' ` by decide_tac >>
            `?e. 0 < e /\ (p ** d = q ** e)` by metis_tac[EXP_RCANCEL, MULT_LEFT_1] >>
            metis_tac[perfect_power_condition]
          ]
        ],
        `q' < q''` by decide_tac >>
        `?d. 0 < d /\ (q ** r' = p ** d * q ** r'')` by metis_tac[EXP_LCANCEL] >>
        Cases_on `r' = r''` >| [
          `p ** d = 1` by metis_tac[MULT_RIGHT_CANCEL, MULT_LEFT_1] >>
          metis_tac[EXP_EQ_1],
          Cases_on `r' < r''` >| [
            `?e. 0 < e /\ (1 = p ** d * q ** e)` by metis_tac[EXP_RCANCEL, MULT_LEFT_1] >>
            `p ** d = 1` by metis_tac[MULT_EQ_1] >>
            metis_tac[EXP_EQ_1],
            `r'' < r'` by decide_tac >>
            `?e. 0 < e /\ (p ** d = q ** e)` by metis_tac[EXP_RCANCEL, MULT_LEFT_1] >>
            metis_tac[perfect_power_condition]
          ]
        ]
      ]
    ]
  ]);

(* This is impressive! *)

(* Theorem: Ring r /\ 0 < k ==>
            !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~perfect_power q p ==>
            !n. CARD (NM p q n) = (SUC n) ** 2 *)
(* Proof:
   Let f = (\y. p ** i * q ** j)
       t = count (SUC n)
   Since INJ f (t CROSS t) (NM p q n)             by count_cross_to_setN_inj
     and NM p q n = IMAGE f (t CROSS t)           by reduceN_def
    Also FINITE t                                 by FINITE_COUNT
     and CARD t = SUC n                           by CARD_COUNT
      so FINITE (t CROSS t)                       by FINITE_CROSS
     and CARD (t CROSS t) = (SUC n) ** 2          by CARD_CROSS
         CARD (NM p q n) = CARD (t CROSS t)       by INJ_CARD_IMAGE_EQ
   Hence CARD (NM p q n) = (SUC n) ** 2.
*)
val reduceN_card = store_thm(
  "reduceN_card",
  ``!r:'a ring k s:num. Ring r /\ 0 < k ==>
   !p q. p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~perfect_power q p ==>
   !n. CARD (NM p q n) = (SUC n) ** 2``,
  rpt strip_tac >>
  qabbrev_tac `f = (\(i, j). p ** i * q ** j)` >>
  qabbrev_tac `t = count (SUC n)` >>
  `INJ f (t CROSS t) N` by rw_tac std_ss[count_cross_to_setN_inj, Abbr`f`, Abbr`t`] >>
  `NM p q n = IMAGE f (t CROSS t)` by rw_tac std_ss[reduceN_def, Abbr`f`, Abbr`t`] >>
  `FINITE t /\ (CARD t = SUC n)` by rw_tac std_ss[FINITE_COUNT, CARD_COUNT, Abbr`t`] >>
  `FINITE (t CROSS t) /\ (CARD (t CROSS t) = (SUC n) ** 2)` by rw_tac std_ss[FINITE_CROSS, CARD_CROSS, EXP_2] >>
  metis_tac[INJ_CARD_IMAGE_EQ]);

(*
If so, with suitable parameters,
MAX p q ** (2 * SQRT (CARD M)) < CARD (Q z) is satisfied,
and INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M

If prime p /\ p divides q /\ ~perfect_power q p,
      CARD (NM p q (SQRT (CARD M)))
    = (SUC (SQRT (CARD M))) ** 2
    > CARD M     by n < (SUC (SQRT n)) ** 2
By pigeonhole principle, no INJ is possible.
*)

(* Theorem: Field r /\ 0 < k /\ p IN N /\ q IN N /\ prime p /\ 1 < q /\
            ~perfect_power q p ==> !n. CARD (NM p q n) = SUC n ** 2 *)
(* Proof: by reduceN_card *)
val reduceN_card_field = store_thm(
  "reduceN_card_field",
  ``!(r:'a field) k s:num p q. Field r /\ 0 < k /\
       p IN N /\ q IN N /\ prime p /\ 1 < q /\ ~perfect_power q p ==>
       !n. CARD (NM p q n) = SUC n ** 2``,
  metis_tac[reduceN_card, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound of (Q z): Show (Q z) SUBSET (Z_p[x] mod z)                    *)
(* ------------------------------------------------------------------------- *)

(* val _ = overload_on ("mifactor", ``\h z. monic h /\ ipoly h /\ (z % h = |0|)``); *)

(* Theorem: mifactor z (unity k) ==> CARD (Q z) <= (CARD R) ** (deg z) *)
(* Proof:
   All polynomials in (Q z) are in (PolyModRing r z).carrier
   i.e. (Q z) SUBSET (PolyModRing r z).carrier  by modP_subset_mod_factor
   Hence    CARD (Q z)
         <= CARD (PolyModRing r z).carrier      by CARD_SUBSET
          = CARD R ** deg z                     by poly_mod_ring_card
*)
val modP_card_upper_max = store_thm(
  "modP_card_upper_max",
  ``!r:'a field (k s):num z. FiniteField r /\ mifactor z (unity k) ==>
      CARD (Q z) <= (CARD R) ** (deg z)``,
  rw_tac std_ss[FiniteField_def] >>
  `Ring r /\ FiniteRing r` by rw[FiniteRing_def] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `Q z SUBSET (PolyModRing r z).carrier` by rw[modP_subset_mod_factor] >>
  `FINITE (PolyModRing r z).carrier` by rw[poly_mod_ring_finite] >>
  `FINITE (Q z)` by metis_tac[SUBSET_FINITE] >>
  `CARD (Q z) <= CARD (PolyModRing r z).carrier` by rw[CARD_SUBSET] >>
  rw[GSYM poly_mod_ring_card]);

(*
This is the absolute upper bound: the size of the embedding quotient field.
From poly_unity_special_factor_exists, deg h = ordz n (CARD R).
Thus this absolute maximum is independent of the range s of polynomial checks.
*)

(* ------------------------------------------------------------------------- *)
(* Set of Polynomial Products on Sets of Monomials                           *)
(* ------------------------------------------------------------------------- *)

(* Define a simple set of polynomials in reduceP *)
val reduceP_poly_def = Define `
  reduceP_poly (r:'a ring) n =
    IMAGE (\s. PPROD (IMAGE (\c. X + |c|) s)) (PPOW (IMAGE SUC (count n)))
`;

(* overload for reduceP_poly *)
val _ = overload_on ("PPM", ``reduceP_poly r``);

(*
> EVAL ``PPOW (IMAGE SUC (count 2))``; = {{2}; {1}; {}}: thm
> EVAL ``PPOW (IMAGE SUC (count 3))``; = {{3; 2}; {3; 1}; {3}; {2; 1}; {2}; {1}; {}}: thm

Thus
PPM 2 = IMAGE (\s. PPROD (IMAGE (\c. X + |c|) s)) {{2}; {1}; {}}
      = {PPROD (X + 2); PPROD (X + 1); PPROD {}}
      = {(X + 2); (X + 1); |1|}

PPM 3 = IMAGE (\s. PPROD (IMAGE (\c. X + |c|) s)) {{3; 2}; {3; 1}; {3}; {2; 1}; {2}; {1}; {}}
      = {(X + 3) * (X + 2); (X + 3) * (X + 1); (X + 3); (X + 2) * (X + 1); (X + 2); (X + 1); |1|}
*)

(* Theorem: !p. p IN PPM n ==> poly p *)
(* Proof:
   By reduceP_poly_def, this is to show:
      s IN POW (IMAGE SUC (count n)) ==> poly (PPROD (IMAGE (\c. X + |c|) s))
   Since FINITE (count n)                                 by FINITE_COUNT
      so FINITE (IMAGE SUC (count n))                     by IMAGE_FINITE
    Also s SUBSET (IMAGE SUC (count n))                   by IN_POW
      so FINITE s                                         by SUBSET_FINITE
    with FINITE (IMAGE (\c. X + |c|) s)                   by IMAGE_FINITE
     Now !p. p IN (IMAGE (\c. X + |c|) s) ==> poly p      by poly_X_add_c_image_element
   Hence poly (PPROD (IMAGE (\c. X + |c|) s))             by poly_prod_set_poly
*)

Theorem reduceP_poly_element_poly:
  !r:'a ring. Ring r ==> !p n. p IN PPM n ==> poly p
Proof
  rw_tac std_ss[reduceP_poly_def, IN_IMAGE, IN_DIFF, IN_SING] >>
  rename [‘s ∈ POW(natural n)’]  >>
  ‘FINITE (IMAGE (\c. X + |c|) s)’
    by metis_tac[IN_POW, FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  metis_tac[poly_X_add_c_image_element, poly_prod_set_poly]
QED

(* Theorem: !p. p IN PPM n ==> monic p *)
(* Proof:
   By reduceP_poly_def, this is to show:
      s IN POW (IMAGE SUC (count n)) ==> monic (PPROD (IMAGE (\c. X + |c|) s))
   Since FINITE (count n)                                 by FINITE_COUNT
      so FINITE (IMAGE SUC (count n))                     by IMAGE_FINITE
    Also s SUBSET (IMAGE SUC (count n))                   by IN_POW
      so FINITE s                                         by SUBSET_FINITE
    with FINITE (IMAGE (\c. X + |c|) s)                   by IMAGE_FINITE
     Now !p. p IN (IMAGE (\c. X + |c|) s) ==> monic p     by poly_monic_X_add_c_image_element
   Hence monic (PPROD (IMAGE (\c. X + |c|) s))            by poly_monic_prod_set_monic
*)

Theorem reduceP_poly_element_monic:
  !r:'a ring. Ring r ==> !p n. p IN PPM n ==> monic p
Proof
  rw_tac std_ss[reduceP_poly_def, IN_IMAGE, IN_DIFF, IN_SING] >>
  rename [‘s ∈ POW (natural n)’] >>
  ‘FINITE (IMAGE (\c. X + |c|) s)’
    by metis_tac[IN_POW, FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  metis_tac[poly_monic_X_add_c_image_element, poly_monic_prod_set_monic]
QED

(* Theorem: #1 <> #0 ==> !n. |0| NOTIN (PPM n) *)
(* Proof:
   By contradiction, assume |0| IN PPM n,
   then monic |0|       by reduceP_poly_element_monic
   i.e. lead |0| = #1   by poly_monic_lead
    but lead |0| = #0   by poly_lead_zero
   Hence a contradiction.
*)
val reduceP_poly_has_no_zero = store_thm(
  "reduceP_poly_has_no_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. |0| NOTIN (PPM n)``,
  metis_tac[reduceP_poly_element_monic, poly_monic_lead, poly_lead_zero]);

(* Theorem: n < char r ==> X NOTIN PPM n *)
(* Proof:
   By contradiction, assume X IN PPM n.
   By reduceP_poly_def, this is to show:
      X = PPROD (IMAGE (\c. X + |c|) s) ==> F,
      where s SUBSET (IMAGE SUC (count n)).
   Since deg X = 1                                      by poly_deg_X
         deg (PPROD (IMAGE (\c. X + |c|) s)) = CARD s   by poly_prod_set_image_X_add_c_deg
   Together,  CARD s = 1
   so    s = {c} for some c                 by SING_IFF_CARD1
   Hence IMAGE (\c. X + |c|) s = {X + |c|}
   and   PPROD {X + |c|} = X + |c|          by poly_prod_set_sing
    Now  0 < char r                         by n < char r
         c < char r                         by MAX_SET_LESS
    Giving X = X + |0| = X + |c| ==> c = 0  by poly_X_add_c_eq
   This contradicts 0 NOTIN s               by s = (IMAGE SUC (count n))
*)

Theorem reduceP_poly_has_no_X:
  !r:'a ring. Ring r /\ #1 <> #0 ==> !n. n < char r ==> X NOTIN PPM n
Proof
  rw_tac std_ss[reduceP_poly_def, IN_IMAGE, IN_PPOW, IN_DIFF, IN_SING] >>
  spose_not_then strip_assume_tac >>
  rename [‘s ∈ POW (natural n)’] >>
  `s SUBSET (IMAGE SUC (count n))` by rw[GSYM IN_POW] >>
  `0 NOTIN IMAGE SUC (count n)` by rw[] >>
  `0 NOTIN s` by metis_tac[SUBSET_DEF] >>
  `FINITE (IMAGE SUC (count n))` by rw[IMAGE_FINITE] >>
  `FINITE s` by metis_tac[SUBSET_FINITE] >>
  `MAX_SET (IMAGE SUC (count n)) = n` by rw[MAX_SET_IMAGE_SUC_COUNT] >>
  `MAX_SET s < char r` by metis_tac[SUBSET_MAX_SET, LESS_EQ_LESS_TRANS] >>
  `CARD s = deg X` by metis_tac[poly_prod_set_image_X_add_c_deg] >>
  `_ = 1` by rw[] >>
  `?c. s = {c}` by metis_tac[SING_IFF_CARD1, SING_DEF] >>
  `IMAGE (\c. X + |c|) s SUBSET (PolyRing r).carrier` by rw[poly_X_add_c_image_poly_subset] >>
  `IMAGE (\c. X + |c|) s = {X + |c|}` by rw[] >>
  `PPROD {X + |c|} = X + |c|` by metis_tac[poly_prod_set_sing, FINITE_SING, poly_X_add_c] >>
  `(X = X + |0|) /\ ($###0 = |0|)` by rw[] >>
  `0 < char r` by decide_tac >>
  metis_tac[poly_X_add_c_eq, MAX_SET_LESS, IN_SING]
QED

(* Theorem: FiniteField r /\ n < char r ==> FINITE (PPM n) *)
(* Proof:
   Let f = \c. X + |c|, and g = \s. PPROD (IMAGE f s).
   By reduceP_poly_def, this is to show: FINITE (IMAGE g (PPOW (IMAGE SUC (count n))))
   Since  FINITE (count n)                                by FINITE_COUNT
      so  FINITE (IMAGE SUC (count n)))                   by IMAGE_FINITE
   hence  FINITE (PPOW (IMAGE SUC (count n)))             by FINITE_PPOW
    thus  FINITE (IMAGE g (PPOW (IMAGE SUC (count n))))   by IMAGE_FINITE
*)
val reduceP_poly_finite = store_thm(
  "reduceP_poly_finite",
  ``!(r:'a ring) n. FINITE (PPM n)``,
  rw[reduceP_poly_def, FINITE_PPOW]);

(* Theorem: Field r /\ n < char r ==> CARD (PPM n) = PRE (2 ** n) *)
(* Proof:
   Let f = \c. X + |c|, and g = \s. PPROD (IMAGE f s).
   By reduceP_poly_def, this is to show: CARD (IMAGE g (PPOW (IMAGE SUC (count n)))) = PRE (2 ** n)
   Since INJ g (PPOW (IMAGE SUC (count n))) (PolyRing r).carrier  by poly_prod_set_image_X_add_c_inj
     and FINITE (PPOW (IMAGE SUC (count n)))                      by FINITE_PPOW, IMAGE_FINITE
     CARD (IMAGE g (PPOW (IMAGE SUC (count n))))
   = CARD (PPOW (IMAGE SUC (count n)))               by INJ_CARD_IMAGE_EQ
   = PRE (2 ** CARD (IMAGE SUC (count n)))           by CARD_PPOW
   = PRE (2 ** n)                                    by CARD_INJ_IMAGE, CARD_COUNT
   Since SUC is injective, by prim_recTheory.INV_SUC_EQ.
*)
val reduceP_poly_card = store_thm(
  "reduceP_poly_card",
  ``!r:'a field. Field r ==> !n. n < char r ==> (CARD (PPM n) = PRE (2 ** n))``,
  rpt strip_tac >>
  rw_tac std_ss[reduceP_poly_def] >>
  qabbrev_tac `f = \c:num. X + |c|` >>
  qabbrev_tac `g = \s. PPROD (IMAGE f s)` >>
  `INJ g (PPOW (IMAGE SUC (count n))) (PolyRing r).carrier` by rw[poly_prod_set_image_X_add_c_inj, Abbr`g`, Abbr`f`] >>
  `FINITE (PPOW (IMAGE SUC (count n)))` by rw[FINITE_PPOW] >>
  `CARD (IMAGE g (PPOW (IMAGE SUC (count n)))) = CARD (PPOW (IMAGE SUC (count n)))` by metis_tac[INJ_CARD_IMAGE_EQ] >>
  rw[CARD_PPOW, CARD_INJ_IMAGE]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
