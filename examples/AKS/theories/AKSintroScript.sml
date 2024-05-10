(* ------------------------------------------------------------------------- *)
(* Introspective Relation for AKS Main Theorem.                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory listRangeTheory dividesTheory
     gcdTheory numberTheory combinatoricsTheory;

(* declare new theory at start *)
val _ = new_theory "AKSintro";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;
open ffConjugateTheory;
open ffExistTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;
open polyBinomialTheory polyEvalTheory;

open polyDividesTheory;
open polyMonicTheory;
open polyFieldTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyMapTheory;
open polyIrreducibleTheory;

open monoidTheory groupTheory ringTheory;
open fieldTheory fieldMapTheory;

open computeRingTheory; (* for overloads on x^, x+^, x^+, x^- *)

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Introspective Relation for AKS Theorem Documentation                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   n intro p                  = poly_intro r k n p
   poly_intro_range r k n m   = !c. 0 < c /\ c <= m ==> n intro (X + |c|)
   poly_intro_checks n k m    = !c. 0 < c /\ c <= m ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
*)
(* Definitions and Theorems (# are exported):

   Introspective Relation:
   poly_intro_def      |- !r k n p. n intro p <=> poly p /\ (p ** n == peval p (X ** n)) (pm (unity k))
   poly_intro_peval_alt    |- !r. Ring r ==> !k. 0 < k ==>
                              !n p. n intro p <=> poly p /\ (peval p X ** n == peval p (X ** n)) (pm (unity k))
   poly_intro_peval_X_exp  |- !r. Ring r ==> !k. 0 < k ==>
                              !p n. n intro p ==> (peval p (X ** n) == p ** n) (pm (unity k))
   poly_intro_trivial  |- !r. Ring r /\ (#1 = #0) ==> !k n p. 0 < k /\ poly p ==> n intro p
   poly_intro_mult     |- !r. Ring r ==> !k. 0 < k ==> !m n p. n intro p /\ m intro p ==> n * m intro p
   poly_intro_compose  |- !r. Ring r ==> !k. 0 < k ==> !p q n. n intro p /\ n intro q ==> n intro p * q
   poly_intro_1        |- !r. Ring r ==> !k. 0 < k ==> !p. poly p ==> 1 intro p
   poly_intro_one      |- !r. Ring r ==> !k. 0 < k ==> !n. n intro |1|
   poly_intro_zero     |- !r. Ring r ==> !k n. 0 < k /\ 0 < n ==> n intro |0|
   poly_intro_not_0_zero  |- !r. Ring r /\ #1 <> #0 ==> !k. 0 < k ==> ~(0 intro |0|)
   poly_intro_X        |- !r. Ring r ==> !k. 0 < k ==> !n. n intro X
   poly_intro_X_exp    |- !r. Ring r ==> !k. 0 < k ==> !n m. n intro X ** m
   poly_intro_X_add_c  |- !r. Ring r ==> !k. 0 < k ==>
                          !n c. n intro X + |c| <=> ((X + |c|) ** n == X ** n + |c|) (pm (unity k))
   poly_intro_X_add_c_0    |- !r. Ring r ==> !k. 0 < k ==> !c. 0 intro X + |c| <=> ( |c| = |0|)
   poly_intro_eval_alt     |- !r. Ring r ==> !k. 0 < k ==>
                              !n p. n intro p <=> poly p /\
                               (poly_eval (PolyRing r) (lift p) X ** n % unity k =
                                poly_eval (PolyRing r) (lift p) (X ** n) % unity k)
   poly_intro_alt_1        |- !r. Ring r ==> !k. 0 < k ==>
                              !n p. n intro p <=> poly p /\ unity k pdivides p ** n - peval p (X ** n)
   poly_intro_alt_2        |- !r. Ring r ==> !k. 0 < k ==>
                              !n p. n intro p <=> poly p /\ (p ** n - peval p (X ** n) == |0|) (pm (unity k))
   poly_intro_X_add_c_alt_1|- !r. Ring r ==> !k. 0 < k ==>
                              !n c. n intro X + |c| <=> unity k pdivides (X + |c|) ** n - (X ** n + |c|)
   poly_intro_X_add_c_alt_2|- !r. Ring r ==> !k. 0 < k ==>
                              !n c. n intro X + |c| <=> ((X + |c|) ** n - (X ** n + |c|) == |0|) (pm (unity k))
   poly_intro_X_add_c_prime_char
                           |- !r. Ring r /\ prime (char r) ==> !k c. 0 < k ==> char r intro X + |c|
   poly_intro_X_add_c_prime_char_alt
                           |- !r k c. Ring r /\ prime (char r) /\ 0 < k ==>
                                      ((X + |c|) ** char r == X ** char r + |c|) (pm (unity k))
   poly_intro_X_add_c_finite_field
                           |- !r k c. FiniteField r /\ 0 < k ==> char r intro X + |c|
   poly_intro_unity_roots_1|- !r. Ring r ==> !k. 0 < k ==> !n p. n intro p <=> poly p /\
                              !x. poly x /\ (x ** k == |1|) (pm (unity k)) ==>
                                 (peval p x ** n == peval p (x ** n)) (pm (unity k))
   poly_intro_unity_roots_2|- !r. Ring r ==> !k. 0 < k ==> !n p. n intro p <=> poly p /\
                              !x h. poly x /\ pmonic h /\ (unity k % h = |0|) /\
                                 (x ** k == |1|) (pm h) ==> (peval p x ** n == peval p (x ** n)) (pm h)

   Introspective Theorems:
   poly_intro_range_product |- !r k. Ring r /\ 0 < k ==>
                               !m n s. poly_intro_range r k m s /\ poly_intro_range r k n s ==>
                                       poly_intro_range r k (m * n) s
   poly_intro_checks_thm    |- !n k s. poly_intro_checks n k s <=>
                                       EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
                                             [1 .. s]
   ZN_intro_checks_def      |- !n k s. ZN_intro_checks n k s <=> poly_intro_checks n k s
   ZN_intro_eqn             |- !n k. 0 < k /\ 0 < n ==>
                                 !c. poly_intro (ZN n) k n (x+ n c) <=>
                                     (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
   ZN_intro_range_eqn       |- !n k. 0 < k /\ 0 < n ==>
                                 !m. poly_intro_range (ZN n) k n m <=> poly_intro_checks n k m

   ZN_intro_by_prime        |- !n k c. prime n /\ 0 < k ==> poly_intro (ZN n) k n (x+ n c)
   ZN_intro_range_by_prime  |- !n k m. prime n /\ 0 < k ==> poly_intro_range (ZN n) k n m
   ZN_intro_range_by_prime_alt
                            |- !n k c. prime n /\ 0 < k ==>
                                       (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
   ZN_intro_checks_by_prime |- !n k m. prime n /\ 0 < k ==> poly_intro_checks n k m
   ZN_intro_checks_imp      |- !n k s t. s <= t /\ poly_intro_checks n k t ==> poly_intro_checks n k s

   Introspective between Fields:
   subfield_poly_intro      |- !r s. s <<= r ==> !k. 0 < k ==>
                               !n c. n intro X + |c| <=>
                                     poly_intro s k n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c))
   field_iso_poly_intro     |- !r r_ f. (r === r_) f ==> !k. 0 < k ==>
                               !n c. n intro X + |c| <=> poly_intro r_ k n (X_ +_ |c|_)

   Introspective for Divisor:
   poly_intro_X_add_c_prime_char_1  |- !r. FiniteField r ==> !k. 0 < k ==> !c. char r intro X + |c|
   poly_intro_X_add_c_prime_char_1_alt
                                    |- !r k c. FiniteField r /\ 0 < k ==>
                                               ((X + |c|) ** char r == X ** char r + |c|) (pm (unity k))
   poly_intro_X_add_c_prime_char_2  |- !r. FiniteField r ==> !k. k divides CARD R+ ==>
                                       !n c. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|
   poly_intro_X_add_c_prime_char_3  |- !r. FiniteField r ==> !k. coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
                                       !n c. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|
   poly_intro_range_char            |- !r k s. FiniteField r /\ 0 < k ==> poly_intro_range r k (char r) s
   poly_intro_X_add_c_prime_char_cofactor_1
                                    |- !r k. FiniteField r /\ k divides CARD R+ ==>
                                       !n c. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|
   poly_intro_X_add_c_prime_char_cofactor_2
                                    |- !r k. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
                                       !n c. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|

   Introspective Relation based on pmonic modulus:
   introspective_def         |- !r z n p. introspective r z n p <=> (p ** n == peval p (X ** n)) (pm z)
   introspective_alt         |- !r. Ring r ==> !n p. poly p ==>
                                !z. introspective r z n p <=> (peval p X ** n == peval p (X ** n)) (pm z)
   poly_intro_introspective  |- !r. Ring r ==> !k. 0 < k ==>
                                !n p. n intro p <=> 0 < k /\ poly p /\ introspective r (unity k) n p
   introspective_trivial     |- !r. Ring r /\ (#1 = #0) ==> !z n p. poly p ==> introspective r z n p
   introspective_shift_factor|- !r p z. Ring r /\ ulead p /\ ulead z /\ z pdivides p ==>
                                !n q. poly q /\ introspective r p n q ==> introspective r z n q
   poly_intro_shift_factor   |- !r. Ring r ==> !k z. 0 < k /\ ulead z /\ z pdivides unity k ==>
                                !n p. n intro p ==> introspective r z n p
   introspective_unity_mult  |- !r. Ring r ==> !p k. poly p /\ 0 < k ==>
                 !n m. introspective r (unity k) n p /\ introspective r (unity k) m p ==>
                       introspective r (unity k) (n * m) p
   introspective_compose     |- !r. Ring r ==> !z p q. ulead z /\ poly p /\ poly q ==>
                 !n. introspective r z n p /\ introspective r z n q ==>
                     introspective r z n (p * q)
   introspective_1           |- !r. Ring r ==> !z p. poly z /\ poly p ==> introspective r z 1 p
   introspective_one         |- !r. Ring r ==> !z. poly z ==> !n. introspective r z n |1|
   introspective_zero        |- !r. Ring r ==> !z n. poly z /\ 0 < n ==> introspective r z n |0|
   introspective_not_0_zero  |- !r z. Ring r /\ pmonic z ==> ~introspective r z 0 |0|
   introspective_X           |- !r z. Ring r /\ poly z ==> !n. introspective r z n X
   introspective_X_add_c     |- !r z. Ring r /\ poly z ==>
                 !n c. introspective r z n (X + |c|) <=> ((X + |c|) ** n == X ** n + |c|) (pm z)
   introspective_X_add_c_alt |- !r z. Ring r /\ ulead z ==>
                 !n c. introspective r z n (X + |c|) <=> z pdivides (X + |c|) ** n - (X ** n + |c|)
   introspective_X_add_c_prime_char
                             |- !r. Ring r /\ prime (char r) ==> !z. poly z ==>
                                    introspective r z (char r) (X + |c|)
   introspective_X_add_c_prime_char_1
                             |- !r z. FiniteField r /\ poly z ==>
                                      introspective r z (char r) (X + |c|)
   introspective_unity_X_add_c_char
                             |- !r. FiniteField r ==>
                                !k. introspective r (unity k) (char r) (X + |c|)
   introspective_unity_X_add_c_char_cofactor_0
                             |- !r. FiniteField r ==>
                                    !k n c. k divides CARD R+ /\ char r divides n /\
                                            introspective r (unity k) n (X + |c|) ==>
                                            introspective r (unity k) (n DIV char r) (X + |c|)
   field_iso_introspective    |- !r r_ f. (r === r_) f ==> !p. ulead p ==>
          !n c. introspective r p n (X + |c|) <=> introspective r_ p_ n (X_ +_ |c|_)
   subring_introspective      |- !r s. s <= r ==> !z. Ulead s z ==>
          !n c. introspective r z n (X + |c|) <=>
                introspective s z n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c))
   introspective_unity_X_add_c_char_cofactor
                 |- !r. FiniteField r ==> !k n c. coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
                        char r divides n /\ introspective r (unity k) n (X + |c|) ==>
                        introspective r (unity k) (n DIV char r) (X + |c|):
*)

(* ------------------------------------------------------------------------- *)
(* Introspective Relation                                                    *)
(* ------------------------------------------------------------------------- *)

(* Introspective = when first substitution by X, then taking exponential
                   equals just substitution by exponential of X *)
val poly_intro_def = Define`
  poly_intro (r:'a ring) (k:num) (n:num) (p:'a poly) <=>
    poly p /\ (p ** n == peval p (X ** n)) (pm (unity k))
`;
(* Note: since peval p X = p, the definition means:
  (peval p X) ** n == peval p (X ** n) (pm z)  where z = X ** k - |1| = unity k
*)

val _ = overload_on ("intro", ``poly_intro r k``);
val _ = set_fixity "intro" (Infix(NONASSOC, 450)); (* same as relation *)

(* overload poly z condition *)
(* val _ = overload_on ("pmonic", ``\z. poly z /\ 0 < deg z /\ unit (lead z)``); *)

(* Theorem: n intro p <=> (poly p /\ ((peval p X) ** n == peval p (X ** n)) (pm (unity k))) *)
(* Proof:
   Let z = unity k.
       n intro p
   <=> poly p /\ (p ** n == peval p (X ** n)) (pm z)             by poly_intro_def
   <=> poly p /\ ((peval p X) ** n == peval p (X ** n)) (pm z)   by poly_peval_by_X
*)
val poly_intro_peval_alt = store_thm(
  "poly_intro_peval_alt",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. n intro p <=> (poly p /\ ((peval p X) ** n == peval p (X ** n)) (pm (unity k)))``,
  metis_tac[poly_intro_def, poly_peval_by_X]);

(* Theorem: n intro p ==> (peval p (X ** n) == p ** n) (pm z) *)
(* Proof:
   Let z = unity k.
       n intro p
   <=> poly p /\ ((peval p X) ** n == peval p (X ** n)) (pm z)   by poly_intro_peval_alt
   <=> poly p /\ (p ** n == peval p (X ** n)) (pm z)             by poly_peval_by_X
   <=> poly p /\ (peval p (X ** n) == p ** n) (pm z)             by poly_mod_symmetric
*)
val poly_intro_peval_X_exp = store_thm(
  "poly_intro_peval_X_exp",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !p n. n intro p ==> (peval p (X ** n) == p ** n) (pm (unity k))``,
  rw_tac std_ss[poly_intro_peval_alt] >>
  metis_tac[poly_peval_by_X, poly_mod_symmetric]);

(* Theorem: Ring r /\ (#1 = #0) ==> !k n p. 0 < k /\ poly p ==> n intro p *)
(* Proof:
   By poly_intro_def, this is to show:
      (p ** n == peval p (X ** n)) (pm (unity k))
   Note |1| = |0|                  by poly_one_eq_poly_zero
   Thus !p. poly p ==> (p = |0|)   by poly_one_eq_zero
    Now poly (p ** n)              by poly_exp_poly
    and poly (peval p (X ** n))    by poly_peval_poly, poly_X_exp
   Hence true                      by poly_mod_reflexive
*)
val poly_intro_trivial = store_thm(
  "poly_intro_trivial",
  ``!r:'a ring. Ring r /\ (#1 = #0) ==> !k n p. 0 < k /\ poly p ==> n intro p``,
  rw_tac std_ss[poly_intro_def] >>
  `!p. poly p ==> (p = |0|)` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  `poly (p ** n) /\ poly (peval p (X ** n))` by rw[] >>
  rw_tac std_ss[poly_mod_reflexive]);

(* Theorem: 0 < k ==> !m n p. n intro p /\ m intro p ==> (n * m) intro p *)
(* Proof:
   Let z = unity k, and ulead z       by poly_unity_deg, ring_unit_one
   Step 1: use (n intro p) to show: (p ** (n * m) == peval (p ** m)) (X ** n) (pm z)
      Since (p ** n == peval p (X ** n)) (pm z)                   by poly_intro_def
      Taking both sides to m-th power,
            ((p ** n) ** m == (peval p (X ** n)) ** m) (pm z)     by pmod_exp_eq
        LHS = (p ** n) ** m = p ** (n * m)                        by poly_exp_mult
        RHS = (peval p (X ** n)) ** m = peval (p ** m) (X ** n)   by poly_peval_exp
      Hence  (p ** (n * m) == peval (p ** m)) (X ** n) (pm z)

   Step 2: use (m intro p) to show: (peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)
      Since (p ** m == peval p (X ** m)) (pm z)                   by poly_intro_def
         so (p ** m - peval p (X ** m) == |0|) (pm z)             by poly_pmod_sub_eq_zero
      Hence ?q. poly q /\ (p ** m - peval p (X ** m) = q * z)     by pmod_eq_zero
      Evaluate LHS by X ** n,
         peval (p ** m - peval p (X ** m)) (X ** n)
       = peval (p ** m) (X ** n) - peval (peval p (X ** m)) (X ** n)  by poly_peval_sub
       = peval (p ** m) (X ** n) - peval p (X ** (m * n))  by poly_peval_peval_X_exp_X_exp
       = peval (p ** m) (X ** n) - peval p (X ** (n * m))  by MULT_COMM
      Evaluate RHS by X ** n,
         peval (q * z) (X ** n)
       = peval q (X ** n) * (peval z (X ** n))             by poly_peval_mult
      But  peval z (X ** n)
         = peval (unity k) (X ** n)                        by z = unity k
         = (X ** n) ** k - |1|                             by poly_peval_unity
         = unity (n * k)                                   by poly_exp_mult
         = unity (k * n)                                   by MULT_COMM
      Now, (unity k) pdivides (unity (k * n))              by poly_unity_divides
       so  ?t. poly t /\ (unity (k * n) = t * z)           by poly_divides_def
      Giving
        peval (p ** m) (X ** n) - peval p (X ** (n * m))
      = peval q (X ** n) * (t * z)                         by peval z (X ** n) = unity (k * n)
      = (peval q (X ** n) * t) * z                         by poly_mult_assoc
      Therefore
      (peval (p ** m) (X ** n) - peval p (X ** (n * m)) == |0|) (pm z)   by pmod_eq_zero
      or (peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)      by poly_pmod_sub_eq_zero

    Combining both steps,
       p ** (n * m) == peval p (X ** (n * m)) (pm z)       by poly_mod_transitive
    or n * m intro p                                       by poly_intro_def
*)
val poly_intro_mult = store_thm(
  "poly_intro_mult",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !m n p. n intro p /\ m intro p ==> n * m intro p``,
  rpt (stripDup[poly_intro_def]) >>
  qabbrev_tac `z = unity k` >>
  `!x. poly x ==> !n. poly (x ** n)` by rw[] >>
  `!p q. poly p /\ poly q ==> poly (peval p q)` by rw[] >>
  `poly X /\ ulead z` by rw[Abbr`z`] >>
  `(p ** (n * m) == peval (p ** m) (X ** n)) (pm z)` by rw_tac std_ss[pmod_exp_eq, poly_exp_mult, poly_peval_exp] >>
  `(peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)` by
  (`(p ** m - peval p (X ** m) == |0|) (pm z)` by rw[GSYM poly_pmod_sub_eq_zero] >>
  `?q. poly q /\ (p ** m - peval p (X ** m) = q * z)` by rw[GSYM pmod_eq_zero] >>
  `peval (p ** m - peval p (X ** m)) (X ** n) =
    peval (p ** m) (X ** n) - peval (peval p (X ** m)) (X ** n)` by rw_tac std_ss[poly_peval_sub] >>
  `_ = peval (p ** m) (X ** n) - peval p (X ** (m * n))` by rw_tac std_ss[poly_peval_peval_X_exp_X_exp] >>
  `_ = peval (p ** m) (X ** n) - peval p (X ** (n * m))` by rw_tac std_ss[MULT_COMM] >>
  `peval (q * z) (X ** n) = peval q (X ** n) * (peval z (X ** n))` by rw[poly_peval_mult] >>
  `peval z (X ** n) = (X ** n) ** k - |1|` by rw[poly_peval_unity, Abbr`z`] >>
  `_ = unity (n * k)` by rw[poly_exp_mult] >>
  `_ = unity (k * n)` by rw_tac std_ss[MULT_COMM] >>
  `(unity k) pdivides (unity (k * n))` by rw[poly_unity_divides] >>
  `?t. poly t /\ (unity (k * n) = t * z)` by rw[GSYM poly_divides_def, Abbr`z`] >>
  `peval (p ** m) (X ** n) - peval p (X ** (n * m)) = peval q (X ** n) * (t * z)` by metis_tac[] >>
  `_ = peval q (X ** n) * t * z` by rw_tac std_ss[poly_mult_assoc] >>
  `(peval (p ** m) (X ** n) - peval p (X ** (n * m)) == |0|) (pm z)` by metis_tac[pmod_eq_zero, poly_sub_poly, poly_mult_poly] >>
  rw_tac std_ss[poly_pmod_sub_eq_zero]) >>
  metis_tac[poly_mod_transitive, poly_intro_def]);

(* Theorem: 0 < k ==> !n p q. n intro p /\ n intro q ==> n intro (p * q) *)
(* Proof:
   If #1 = #0, true                         by poly_intro_trivial, poly_mult_poly, 0 < k.
   If #1 <> #0,
   Let z = unity k, and pmonic z            by poly_unity_pmonic, #1 <> #0
   By poly_intro_def, this is to show: ((p * q) ** n == peval (p * q) (X ** n)) (pm z)
   Now,
   (p ** n == peval p (X ** n)) (pm z)      by poly_intro_def, n intro p.
   (q ** n == peval q (X ** n)) (pm z)      by poly_intro_def, n intro q.
   Therefore,
   (p ** n * q ** n == peval p (X ** n) * peval q (X ** n)) (pm z)   by pmod_mult
   But  p ** n * q ** n = (p * q) ** n                               by poly_mult_exp
   and  peval p (X ** n) * peval q (X ** n) = peval (p * q) (X ** n) by poly_peval_mult
   Hence n intro (p * q)                                             by poly_intro_def
*)
val poly_intro_compose = store_thm(
  "poly_intro_compose",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !p q n. n intro p /\ n intro q ==> n intro p * q``,
  rpt (stripDup[poly_intro_def]) >>
  Cases_on `#1 = #0` >-
  rw_tac std_ss[poly_intro_trivial, poly_mult_poly] >>
  qabbrev_tac `z = unity k` >>
  `!x. poly x ==> !n. poly (x ** n)` by rw[] >>
  `!p q. poly p /\ poly q ==> poly (peval p q)` by rw[] >>
  `poly X /\ pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  rw_tac std_ss[poly_intro_def, poly_mult_poly, pmod_mult, poly_mult_exp, poly_peval_mult]);

(* Theorem: 0 < k ==> !p. poly p ==> 1 intro p *)
(* Proof:
   Let z = unity k
   By poly_intro_def, this is to show:
          (p ** 1 == peval p (X ** 1)) (pm z)
   or to show: (p == peval p X) (pm z)     by poly_X, poly_exp_1
   Now  peval p X = p                      by poly_peval_by_X
   Hence true                              by poly_mod_reflexive
   Another way:
   Note peval p X ** 1 = peval p X         by poly_exp_1
    and peval p (X ** 1) = peval p X       by poly_exp_1
    ==> (peval p X ** 1 == peval p (X ** 1)) (pm (unity k))
                                           by poly_mod_reflexive
   Thus 1 intro p                          by poly_intro_peval_alt
*)
val poly_intro_1 = store_thm(
  "poly_intro_1",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !p. poly p ==> 1 intro p``,
  rw[poly_intro_peval_alt]);

(* Theorem: 0 < k ==> !n. n intro |1| *)
(* Proof:
   Let z = unity k
   By poly_intro_def, this is to show:
      ( |1| ** n == peval |1| (X ** n)) (pm z)
     peval |1| (X ** n)
   = |1|                               by poly_peval_one
   = |1| ** n                          by poly_one_exp
   Hence true                          by poly_mod_reflexive
   Another way:
   Note peval |1| X ** n = |1| ** n    by poly_peval_one
                         = |1|         by poly_one_exp
    and peval |1| (X ** n) = |1|       by poly_peval_one
    ==> (peval |1| X ** n == peval |1| (X ** n)) (pm (unity k))
                                       by poly_mod_reflexive
   Also poly |1|                       by poly_one_poly
   Thus n intro |1|                    by poly_intro_peval_alt
*)
val poly_intro_one = store_thm(
  "poly_intro_one",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !n. n intro |1|``,
  rw[poly_intro_peval_alt]);

(* Theorem: 0 < k /\ 0 < n ==> !n. n intro |0| *)
(* Proof:
   Let z = unity k
   By poly_intro_def, this is to show:
      ( |0| ** n == peval |0| (X ** n)) (pm z)
     peval |0| (X ** n)
   = |0|                               by poly_peval_zero
   = |0| ** n                          by poly_zero_exp, n <> 0.
   Hence true                          by poly_mod_reflexive.
   Another way:
   Note peval |0| X ** n = |0| ** n    by poly_peval_zero
                         = |0|         by poly_zero_exp, 0 < n
    and peval |0| (X ** n) = |0|       by poly_peval_zero
    ==> (peval |0| X ** n == peval |0| (X ** n)) (pm (unity k))
                                       by poly_mod_reflexive
   Also poly |0|                       by poly_zero_poly
   Thus n intro |0|                    by poly_intro_peval_alt
*)
val poly_intro_zero = store_thm(
  "poly_intro_zero",
  ``!r:'a ring. Ring r ==> !k n. 0 < k /\ 0 < n ==> n intro |0|``,
  rw_tac std_ss[poly_intro_peval_alt, poly_peval_zero, poly_zero_poly, poly_zero_exp] >>
  fs[]);

(* Theorem: Ring r /\ #1 <> #0 ==> ~(0 intro |0|) *)
(* Proof:
   Let z = unity k, and pmonic z   by poly_unity_pmonic
   By poly_intro_def, this is to show: ~( |1| == |0|) (pm z)
   By contradiction, suppose ( |1| == |0|) (pm z).
       ( |1| == |0|) (pm z)
   <=> |1| % z = |0| % z           by pmod_def_alt
   <=> |1| = |0|                   by poly_mod_one, poly_mod_zero
   <=> #1 = #0                     by poly_one_eq_poly_zero
   which contradicts #1 <> #0.
*)
val poly_intro_not_0_zero = store_thm(
  "poly_intro_not_0_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k. 0 < k ==> ~(0 intro |0|)``,
  rw_tac std_ss[poly_intro_def, poly_zero_poly, poly_peval_zero, poly_zero_exp] >>
  qabbrev_tac `z = unity k` >>
  `poly X /\ pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  metis_tac[pmod_def_alt, poly_mod_one, poly_mod_zero, poly_one_eq_poly_zero]);

(* Theorem: 0 < k ==> !n. n intro X *)
(* Proof:
   Let z = unity k
   By poly_intro_def, this is to show:
         (X ** n == peval X (X ** n)) (pm z)
   Since peval X (X ** n) = X ** n  by poly_peval_X
   Hence true                       by poly_mod_reflexive.
   Another way:
   Note peval X X ** n = X ** n     by poly_peval_X
    and peval X (X ** n) = X ** n   by poly_peval_X
    ==> (peval X X ** n == peval X (X ** n)) (pm (unity k))
                                    by poly_mod_reflexive
   Also poly X                      by poly_X
   Thus n intro X                   by poly_intro_peval_alt
*)
val poly_intro_X = store_thm(
  "poly_intro_X",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !n. n intro X``,
  rw_tac std_ss[poly_intro_peval_alt, poly_peval_X, poly_mod_reflexive, poly_exp_poly, poly_X]);

(* Theorem: 0 < k ==> !n. n intro X ** m *)
(* Proof:
   Let z = unity k
   By poly_intro_def, this is to show:
      ((X ** m) ** n == peval (X ** m) (X ** n)) (pm z)
     peval (X ** m) (X ** n)
   = (peval X (X ** n)) ** m      by poly_peval_exp
   = (X ** n) ** m                by poly_peval_X
   = X ** (n * m)                 by poly_exp_mult
   = X ** (m * n)                 by MULT_COMM
   = (X ** m) ** n                by poly_exp_mult
   Hence true                     by poly_mod_reflexive.
   Another way:
   Note peval (X ** m) X ** n = (X ** m) ** m     by poly_peval_X_exp
                              = X ** (m * n)      by poly_exp_mult
    and peval (X ** m) (X ** n) = (X ** n) ** m   by poly_peval_X_exp
                                = X ** (n * m)    by poly_exp_mult
                                = X ** (m * n)    by MULT_COMM
    ==> (peval (X ** m) X ** n == peval (X ** m) (X ** n)) (pm (unity k))
                                    by poly_mod_reflexive
   Also poly (X ** m)               by poly_X_exp
   Thus n intro (X ** n)            by poly_intro_peval_alt
*)
val poly_intro_X_exp = store_thm(
  "poly_intro_X_exp",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !n m. n intro (X ** m)``,
  rpt strip_tac >>
  `peval (X ** m) X ** n = X ** (m * n)` by rw[poly_peval_X_exp, poly_exp_mult] >>
  `peval (X ** m) (X ** n) = X ** (n * m)` by rw[poly_peval_X_exp, poly_exp_mult] >>
  `_ = X ** (m * n)`by rw_tac bool_ss[MULT_COMM] >>
  rw[poly_intro_peval_alt, poly_mod_reflexive]);

(* Theorem: 0 < k ==> !n c. n intro (X + |c|) <=> ((X + |c|) ** n == (X ** n + |c|)) (pm (unity k)) *)
(* Proof:
   By poly_intro_def, this is to show:
   (1) poly (X + |c|),                          true by poly_X_add_c
   (2) peval (X + |c|) (X ** n) = X ** n + |c|, true by poly_peval_X_add_c
*)
val poly_intro_X_add_c = store_thm(
  "poly_intro_X_add_c",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n c:num. n intro (X + |c|) <=> ((X + |c|) ** n == (X ** n + |c|)) (pm (unity k))``,
  rw_tac std_ss[poly_intro_def] >>
  `poly (X + |c|)` by rw[] >>
  `peval (X + |c|) (X ** n) = X ** n + |c|` by rw[poly_peval_X_add_c] >>
  metis_tac[]);

(* Theorem: !c. 0 intro (X + |c|) <=> |c| = |0| *)
(* Proof:
   If #1 = #0,
      If part: 0 intro X + |c| ==> |c| = |0|
         Note |1| = |0|         by poly_one_eq_poly_zero
         poly |c|               by poly_sum_num_poly
         Thus |c| = |0|         by poly_one_eq_zero
      Only-if part: |c| = |0| ==> 0 intro X + |0|
         Note poly (X + |0|)    by poly_X_add_c
         Thus true              by poly_intro_trivial
   If #1 <> #0,
   Let z = unity k, and pmonic z             by poly_unity_pmonic, 0 < k, #1 <> #0
   By poly_intro_def, this is to show:
      poly (X + |c|) /\ ((X + |c|) ** 0 == peval (X + |c|) (X ** 0)) (pm z) <=> ( |c| = |0|)
   Since poly (X + |c|)                      by poly_sum_num_poly
   This is to show: ( |1| == peval (X + |c|) |1|) (pm z) <=> ( |c| = |0|)
    Also peval (X + |c|) |1| = |1| + |c|     by poly_peval_X_add_c_by_one
   This is to show: ( |1| == |1| + |c|) (pm z) <=> ( |c| = |0|)    by poly_exp_0
   Now,  ( |1| == |1| + |c|) (pm z)
     <=> ( |1| + |c| == |1|) (pm z)          by poly_mod_symmetric
     <=> ( |1| + |c| - |1| == |0|) (pm z)    by poly_pmod_sub_eq_zero
     <=> ( |c| == |0|) (pm z)                by poly_add_sub_comm
   This is to show:  ( |c| == |0|) (pm z) <=> ( |c| = |0|)
   which is true                             by poly_pmod_ring_sum_eq_zero
*)
val poly_intro_X_add_c_0 = store_thm(
  "poly_intro_X_add_c_0",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !c:num. 0 intro (X + |c|) <=> ( |c| = |0|)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >-
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_sum_num_poly] >>
    metis_tac[poly_intro_trivial, poly_X_add_c],
    rw_tac std_ss[poly_intro_def] >>
    qabbrev_tac `z = unity k` >>
    `poly X /\ poly |1| /\ poly |c| /\ poly (X + |c|) /\ pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
    rw_tac std_ss[poly_exp_0, poly_peval_X_add_c_by_one] >>
    `poly ( |1| + |c|)` by rw[] >>
    `( |1| + |c| == |1|) (pm z) <=> ( |c| = |0|)` suffices_by metis_tac[poly_mod_symmetric] >>
    `( |1| + |c| - |1| == |0|) (pm z) <=> ( |c| = |0|)` suffices_by metis_tac[poly_pmod_sub_eq_zero] >>
    `( |c| == |0|) (pm z) <=> ( |c| = |0|)` suffices_by metis_tac[poly_add_sub_comm] >>
    rw_tac std_ss[poly_pmod_ring_sum_eq_zero]
  ]);

(* Note: |c| = |0| <=> c = 0  by poly_sum_num_eq requires FiniteRing r *)

(*
> poly_exp_poly |> ISPEC ``(PolyModRing r z)``;
val it = |- Ring (PolyModRing r z) ==> !p. Poly (PolyModRing r z) p ==>
     !n. Poly (PolyModRing r z) ((PolyRing (PolyModRing r z)).prod.exp p n): thm
*)

(* Theorem: n intro p <=> poly p /\ (eval (lift p) X) ** n == (eval (lift p) (X ** n)) (pm z) *)
(* Proof:
   Let z = unity k.
       n intro p
   <=> poly p /\ (peval p X ** n == peval p (X ** n)) (pm z)      by poly_intro_peval_alt
   or  (peval p X ** n % z = peval p (X ** n) % z)                by pmod_def_alt
   or  ((poly_eval (PolyRing r) (lift p) X) ** n % z =
        (poly_eval (PolyRing r) (lift p) (X ** n)) % z)           by poly_peval_alt
*)
val poly_intro_eval_alt = store_thm(
  "poly_intro_eval_alt",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> !n p. n intro p <=> poly p /\
    (((poly_eval (PolyRing r) (lift p) X) ** n) % (unity k) =
     (poly_eval (PolyRing r) (lift p) (X ** n)) % (unity k))``,
  metis_tac[poly_intro_peval_alt, poly_peval_alt, pmod_def_alt, poly_X, poly_exp_poly]);

(* Note: the following cannot be proved,
   as X will be required to be an element in (PolyModRing r z), i.e. deg X < deg z.

g `!(r:'a ring) (z:'a poly). Ring r ==> !n p. n intro p <=> poly p /\
    (((PolyModRing r z).prod.exp (poly_eval (PolyModRing r z) (lift p) X) n) =
     (poly_eval (PolyModRing r z) (lift p) (X ** n)))`;
*)

(* Theorem: 0 < k ==> !n p. n intro p <=> poly p /\ (unity k) pdivides (p ** n - (peval p (X ** n))) *)
(* Proof:
   If #1 = #0,
      If part: n intro p ==> poly p /\ 0 < k /\ (unity k) pdivides (p ** n - (peval p (X ** n)))
         Note poly p                             by poly_intro_def
         Also poly (p ** n - peval p (X ** n))   by poly_exp_poly, poly_peval_poly, poly_sub_poly
          But |1| = |0|                          by poly_one_eq_poly_zero
         Thus p ** n - peval p (X ** n) = |0|    by poly_one_eq_zero
         Hence true                              by poly_divides_zero
      Only-if part: poly p /\ 0 < k /\ (unity k) pdivides (p ** n - (peval p (X ** n))) ==> n intro p
         This is true                            by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                         by poly_unity_pmonic, 0 < k, #1 <> #0
       n intro p
   <=> poly p /\ 0 < k /\ (p ** n == peval p (X ** n)) (pm (unity k))       by poly_intro_def
   <=> poly p /\ 0 < k /\ (unity k) pdivides (p ** n - (peval p (X ** n)))  by poly_divides_sub
*)
val poly_intro_alt_1 = store_thm(
  "poly_intro_alt_1",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. n intro p <=> poly p /\ (unity k) pdivides (p ** n - (peval p (X ** n)))``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >-
    fs[poly_intro_def] >-
   (`poly p` by fs[poly_intro_def] >>
    `poly (p ** n - peval p (X ** n))` by rw[] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_divides_zero]) >>
    rw_tac std_ss[poly_intro_trivial],
    metis_tac[poly_intro_def, poly_unity_pmonic, poly_divides_sub, poly_X, poly_exp_poly, poly_peval_poly]
  ]);

(* Theorem: 0 < k ==> !n p. n intro p <=> poly p /\ (p ** n - (peval p (X ** n)) == |0|) (pm (unity k)) *)
(* Proof:
   If #1 = #0,
      If part: n intro p ==> poly p /\ 0 < k /\ (p ** n - (peval p (X ** n)) == |0|) (pm (unity k))
         Note poly p                             by poly_intro_def
         Also poly (p ** n - peval p (X ** n))   by poly_exp_poly, poly_peval_poly, poly_sub_poly
          But |1| = |0|                          by poly_one_eq_poly_zero
         Thus p ** n - peval p (X ** n) = |0|    by poly_one_eq_zero
         Hence true                              by poly_mod_reflexive
      Only-if part: poly p /\ 0 < k /\ (p ** n - (peval p (X ** n)) == |0|) (pm (unity k)) ==> n intro p
         This is true                            by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                         by poly_unity_pmonic, 0 < k, #1 <> #0
       n intro p
   <=> poly p /\ 0 < k /\ (p ** n == peval p (X ** n)) (pm (unity k))          by poly_intro_def
   <=> poly p /\ 0 < k /\ (p ** n - (peval p (X ** n)) == |0|) (pm (unity k))  by poly_pmod_sub_eq_zero
*)
val poly_intro_alt_2 = store_thm(
  "poly_intro_alt_2",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. n intro p <=> poly p /\ (p ** n - (peval p (X ** n)) == |0|) (pm (unity k))``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >-
    fs[poly_intro_def] >-
   (`poly p` by fs[poly_intro_def] >>
    `poly (p ** n - peval p (X ** n))` by rw[] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mod_reflexive]) >>
    rw_tac std_ss[poly_intro_trivial],
    metis_tac[poly_intro_def, poly_unity_pmonic, poly_pmod_sub_eq_zero, poly_X, poly_exp_poly, poly_peval_poly]
  ]);

(* Theorem: 0 < k ==> !n c. n intro X + |c| <=> (unity k) pdivides ((X + |c|) ** n - (X ** n + |c|)) *)
(* Proof:
   If #1 = #0,
      If part: n intro (X + |c|) ==> 0 < k /\ (unity k) pdivides ((X + |c|) ** n - (X ** n + |c|))
         Note poly ((X + |c|) ** n - (X ** n + |c|))   by poly_exp_poly, poly_peval_poly, poly_sub_poly
          But |1| = |0|                                by poly_one_eq_poly_zero
         Thus (X + |c|) ** n - (X ** n + |c|) = |0|    by poly_one_eq_zero
         Hence true                                    by poly_divides_zero
      Only-if part: 0 < k /\ (unity k) pdivides ((X + |c|) ** n - (X ** n + |c|)) ==> n intro (X + |c|)
         Note poly (X + |c|)                           by poly_X_add_c
         This is true                                  by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                       by poly_unity_pmonic, 0 < k, #1 <> #0
   Note poly ((X + |c|) ** n)                  by poly_X_add_c, poly_exp_poly
    and poly (X ** n + |c|)                    by poly_X_exp_n_add_c_poly
    and 0 < k ==> pmonic (unity k)             by poly_unity_pmonic
    and (p == q) (pm z) <=> z pdivides p - q   by poly_divides_sub, pmonic z.
   Thus the result follows                     by poly_intro_X_add_c
*)
val poly_intro_X_add_c_alt_1 = store_thm(
  "poly_intro_X_add_c_alt_1",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n (c:num). n intro X + |c| <=> (unity k) pdivides ((X + |c|) ** n - (X ** n + |c|))``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >| [
      `poly ((X + |c|) ** n - (X ** n + |c|))` by rw[] >>
      metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_divides_zero],
      rw_tac std_ss[poly_intro_trivial, poly_X_add_c]
    ],
    rw_tac std_ss[poly_intro_X_add_c] >>
    `poly ((X + |c|) ** n)` by rw[] >>
    `poly (X ** n + |c|)` by rw[] >>
    metis_tac[poly_divides_sub, poly_unity_pmonic]
  ]);

(* Theorem: 0 < k ==> !n c. n intro X + |c| <=> ((X + |c|) ** n - (X ** n + |c|) == |0|) (pm (unity k)) *)
(* Proof:
   If #1 = #0,
      If part: n intro (X + |c|) ==> 0 < k /\ ((X + |c|) ** n - (X ** n + |c|) == |0|) (pm (unity k))
         Note poly ((X + |c|) ** n - (X ** n + |c|)) by poly_exp_poly, poly_peval_poly, poly_sub_poly, poly_X_add_c
          But |1| = |0|                              by poly_one_eq_poly_zero
         Thus (X + |c|) ** n - (X ** n + |c|) = |0|  by poly_one_eq_zero
         Hence true                                  by poly_mod_reflexive
      Only-if part: 0 < k /\ ((X + |c|) ** n - (X ** n + |c|) == |0|) (pm (unity k)) ==> n intro (X + |c|)
         Note poly (X + |c|)                         by poly_X_add_c
         This is true                                by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                             by poly_unity_pmonic, 0 < k, #1 <> #0
   Note poly ((X + |c|) ** n)                        by poly_X_add_c, poly_exp_poly
    and poly (X ** n + |c|)                          by poly_X_exp_n_add_c_poly
    and 0 < k ==> pmonic (unity k)                   by poly_unity_pmonic
    and (p == q) (pm z) <=> (p - q == |0|) (pm z)    by poly_pmod_sub_eq_zero, pmonic z.
   Thus the result follows                           by poly_intro_X_add_c
*)
val poly_intro_X_add_c_alt_2 = store_thm(
  "poly_intro_X_add_c_alt_2",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n (c:num). n intro X + |c| <=> ((X + |c|) ** n - (X ** n + |c|) == |0|) (pm (unity k))``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >| [
      `poly ((X + |c|) ** n - (X ** n + |c|))` by rw[] >>
      metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mod_reflexive],
      rw_tac std_ss[poly_intro_trivial, poly_X_add_c]
    ],
    rw_tac std_ss[poly_intro_X_add_c] >>
    `poly ((X + |c|) ** n)` by rw[] >>
    `poly (X ** n + |c|)` by rw[] >>
    metis_tac[poly_pmod_sub_eq_zero, poly_unity_pmonic]
  ]);

(* Theorem: prime (char r) ==> !k c. 0 < k ==> (char r) intro (X + |c|) *)
(* Proof:
   Let z = unity k, p = char r, with prime p.
   By poly_intro_def, this is to show:
   (1) poly (X + |c|), true             by poly_X_add_c
   (2) ((X + |c|) ** p == peval (X + |c|) (X ** p)) (pm z)
       LHS = (X + |c|) ** p
           = X ** p + |c| ** p          by poly_freshman_thm
           = X ** p + |c|               by poly_fermat_thm
       RHS = peval (X + |c|) (X ** p)
           = X ** p + |c|               by poly_peval_X_add_c
       Hence true                       by poly_mod_reflexive.
*)
val poly_intro_X_add_c_prime_char = store_thm(
  "poly_intro_X_add_c_prime_char",
  ``!r:'a ring. Ring r /\ prime (char r) ==>
   !k c:num. 0 < k ==> (char r) intro (X + |c|)``,
  rw_tac std_ss[poly_intro_def] >-
  rw[] >>
  qabbrev_tac `z = unity k` >>
  qabbrev_tac `p = char r` >>
  `poly X /\ poly |c| /\ poly (X + |c|) /\ poly (X ** p) /\ poly (X ** p + |c|)` by rw[] >>
  `(X + |c|) ** p = X ** p + |c|` by metis_tac[poly_freshman_thm, poly_fermat_thm] >>
  `peval (X + |c|) (X ** p) = X ** p + |c|` by rw[poly_peval_X_add_c] >>
  metis_tac[poly_mod_reflexive]);

(* Theorem: Ring r /\ prime (char r) /\ 0 < k ==>
            ((X + |c|) ** (char r) == (X ** (char r) + |c|)) (pm (unity k)) *)
(* Proof: by poly_intro_X_add_c_prime_char, poly_intro_def, poly_peval_X_add_c *)
val poly_intro_X_add_c_prime_char_alt = store_thm(
  "poly_intro_X_add_c_prime_char_alt",
  ``!r:'a ring k c:num. Ring r /\ prime (char r) /\ 0 < k ==>
           ((X + |c|) ** (char r) == (X ** (char r) + |c|)) (pm (unity k))``,
  rpt strip_tac >>
  imp_res_tac poly_intro_X_add_c_prime_char >>
  fs[poly_intro_def] >>
  qabbrev_tac `p = char r` >>
  `peval (X + |c|) (X ** p) = X ** p + |c|` by rw[poly_peval_X_add_c] >>
  metis_tac[]);

(* Theorem: FiniteField r /\ 0 < k ==> (char r) intro X + |c| *)
(* Proof: by poly_intro_X_add_c_prime_char, finite_field_char *)
val poly_intro_X_add_c_finite_field = store_thm(
  "poly_intro_X_add_c_finite_field",
  ``!r:'a field k c:num. FiniteField r /\ 0 < k ==> (char r) intro X + |c|``,
  rw[poly_intro_X_add_c_prime_char, finite_field_char, finite_field_is_field]);

(* Theorem: 0 < k ==> !n p. n intro p <=> poly p /\
            !x. poly x /\ (x ** k == |1|) (pm (unity k)) ==>
                ((peval p x) ** n == peval p (x ** n)) (pm (unity k)) *)
(* Proof:
   If #1 = #0,
      If part: n intro p ==> poly p /\ ...
         Note poly p                             by poly_intro_def
         Also poly ((peval p x) ** n)            by poly_exp_poly, poly_peval_poly
          and poly (peval p (x ** n))            by poly_exp_poly, poly_peval_poly
          But |1| = |0|                          by poly_one_eq_poly_zero
         Thus (peval p x) ** n = |0|             by poly_one_eq_zero
          and peval p (x ** n) = |0|             by by poly_one_eq_zero
         Hence true                              by poly_mod_reflexive
      Only-if part: poly p /\ ... ==> n intro p
         This is true                            by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                by poly_unity_pmonic, 0 < k, #1 <> #0
   Let z = unity k, then pmonic z       by poly_unity_pmonic, 0 < k.
   If part: n intro p ==> poly p /\ (peval p x ** n == peval p (x ** n)) (pm z)
         n intro p
     ==> poly p /\ 0 < k /\ (p ** n == peval p (X ** n)) (pm z)   by poly_intro_def
     and (x ** k == |1) (pm z)
     ==> (x ** k - |1| == |0|) (pm z)   by poly_pmod_sub_eq_zero
      or (peval z x == |0|) (pm z)      by poly_peval_unity
       peval p x ** n
     = peval (p ** n) x                 by poly_peval_exp
     == peval (peval p (X ** n)) x      by poly_mod_eq_peval_root_eq, (peval z x == |0|) (pm z)
     = peval p (x ** n)                 by poly_peval_peval_X_exp
     Overall result is true             by poly_mod_eq_eq
   Only-if part: poly p /\ (peval p x ** n == peval p (x ** n)) (pm z) ==> n intro p
     Since peval z X % z = |0|          by poly_mod_ring_has_root_X
        or (peval z X == |0|) (pm z)    by pmod_zero
      Now, peval z X = unity k          by poly_peval_unity
       so  (X ** k == |1|) (pm z)       by poly_pmod_sub_eq_zero
     Hence peval p X ** n == peval p (X ** n)) (pm z)   by implication
      With peval p X = p                by poly_peval_by_X
     Overall (p ** n == peval p (X ** n)) (pm z))  by poly_mod_reflexive, poly_mod_transitive
          or n intro p                  by poly_intro_def
*)
val poly_intro_unity_roots_1 = store_thm(
  "poly_intro_unity_roots_1",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. n intro p <=> poly p /\
   !x. poly x /\ (x ** k == |1|) (pm (unity k)) ==>
       ((peval p x) ** n == peval p (x ** n)) (pm (unity k))``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >-
    fs[poly_intro_def] >-
   (`poly p` by fs[poly_intro_def] >>
    `poly (peval p x ** n) /\ poly (peval p (x ** n))` by rw[] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mod_reflexive]) >>
    rw_tac std_ss[poly_intro_trivial],
    qabbrev_tac `z = unity k` >>
    `poly |1| /\ poly X` by rw[] >>
    rw_tac std_ss[poly_intro_def, EQ_IMP_THM] >| [
      `pmonic z` by rw[GSYM poly_unity_pmonic, Abbr`z`] >>
      `!z. poly z ==> !n. poly (z ** n)` by rw[] >>
      `(peval z x == |0|) (pm z)` by metis_tac[poly_pmod_sub_eq_zero, poly_peval_unity] >>
      `!z x. poly z /\ poly x ==> poly (peval z x)` by rw[] >>
      `(peval (p ** n) x == peval (peval p (X ** n)) x) (pm z)` by metis_tac[poly_mod_eq_peval_root_eq] >>
      `peval (p ** n) x = peval p x ** n` by rw[poly_peval_exp] >>
      `peval (peval p (X ** n)) x = peval p (x ** n)` by rw[poly_peval_peval_X_exp] >>
      metis_tac[poly_mod_eq_eq],
      `pmonic z` by rw[GSYM poly_unity_pmonic, Abbr`z`] >>
      `(peval z X == |0|) (pm z)` by rw[poly_mod_ring_has_root_X, pmod_zero] >>
      `peval z X = unity k` by rw[poly_peval_unity, Abbr`z`] >>
      `!z. poly z ==> !n. poly (z ** n)` by rw[] >>
      `(X ** k == |1|) (pm z)` by metis_tac[poly_pmod_sub_eq_zero] >>
      `!z x. poly z /\ poly x ==> poly (peval z x)` by rw[] >>
      metis_tac[poly_peval_by_X, poly_mod_reflexive, poly_mod_transitive]
    ]
  ]);

(* Note: This leads to an Injection Map without prime k *)

(* Theorem: 0 < k ==> !n p. n intro p <=> poly p /\
            !x h. poly x /\ pmonic h /\
              ((unity k) % h = |0|) /\ (x ** k == |1|) (pm h) ==>
              ((peval p x) ** n == peval p (x ** n)) (pm h) *)
(* Proof:
   If #1 = #0,
      If part: n intro p ==> poly p /\ 0 < k /\ ...
         Note poly p                             by poly_intro_def
         Also poly ((peval p x) ** n)            by poly_exp_poly, poly_peval_poly
          and poly (peval p (x ** n))            by poly_exp_poly, poly_peval_poly
          But |1| = |0|                          by poly_one_eq_poly_zero
         Thus (peval p x) ** n = |0|             by poly_one_eq_zero
          and peval p (x ** n) = |0|             by by poly_one_eq_zero
         Hence true                              by poly_mod_reflexive
      Only-if part: poly p /\ 0 < k /\ ,,, ==> n intro p
         This is true                            by poly_intro_trivial
   If #1 <> #0,
   Note pmonic (unity k)                         by poly_unity_pmonic, 0 < k, #1 <> #0
   Let z = unity k, the pmonic z.
   If part: by poly_intro_def, this is to show:
      0 < k /\ (p ** n == peval p (X ** n)) (pm z) /\
      pmonic h /\ (z % h = |0|) /\ (x ** k == |1|) (pm h) ==>
            ((peval p x) ** n == peval p (x ** n)) (pm h)
      Step 1: Show x is a root of z
         Given (x ** k == |1|) (pm h),
            so (x ** k - |1| == |0|) (pm h)    by poly_pmod_sub_eq_zero
            or (peval z x == |0|) (pm h)       by poly_peval_unity
      Step 2: Conclusion
         Since (peval (p ** n) x == peval (peval p (X ** n)) x) (pm h)  by poly_mod_eq_peval_root_eq_2
           and peval (p ** n) x = peval p x ** n               by poly_peval_exp
           and peval (peval p (X ** n)) x = peval p (x ** n)   by poly_peval_peval_X_exp
         Hence ((peval p x) ** n == peval p (x ** n)) (pm h)   by poly_mod_eq_eq
   Only-if part: by poly_intro_def, this is to show:
      0 < k /\ !x h. poly x /\ pmonic h /\ (z % h = |0|) /\
                (x ** k == |1|) (pm h) ==> (peval p x ** n == peval p (x ** n)) (pm h)
            ==> (p ** n == peval p (X ** n)) (pm z)
       Note (peval z X == |0|) (pm z)          by poly_mod_ring_has_root_X, pmod_zero
        and peval z X = unity k                by poly_peval_unity
       Thus (X ** k - |1| == |0|) (pm z)       by notation for unity k
         or (X ** k == |1|) (pm z)             by poly_pmod_sub_eq_zero
      Since z % z = |0|                        by poly_div_mod_id
      Putting x = X, h = z in the implication,
      therefore (peval p X ** n == peval p (X ** n)) (pm z)   by implication
            But peval p X = p                                 by poly_peval_by_X
          Hence (peval p X ** n == p ** n) (pm z)             by poly_mod_reflexive
            and (p ** n == peval p (X ** n)) (pm z)           by poly_mod_transitive
*)
val poly_intro_unity_roots_2 = store_thm(
  "poly_intro_unity_roots_2",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. n intro p <=> poly p /\
   !x h. poly x /\ pmonic h /\ ((unity k) % h = |0|) /\ (x ** k == |1|) (pm h) ==>
       ((peval p x) ** n == peval p (x ** n)) (pm h)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    rw_tac std_ss[EQ_IMP_THM] >-
    fs[poly_intro_def] >-
   (`poly p` by fs[poly_intro_def] >>
    `poly (peval p x ** n) /\ poly (peval p (x ** n))` by rw[] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mod_reflexive]) >>
    rw_tac std_ss[poly_intro_trivial],
    qabbrev_tac `z = unity k` >>
    `poly |1| /\ poly X` by rw[] >>
    rw_tac std_ss[poly_intro_def, EQ_IMP_THM] >| [
      `pmonic z` by rw[GSYM poly_unity_pmonic, Abbr`z`] >>
      `!z. poly z ==> !n. poly (z ** n)` by rw[] >>
      `(peval z x == |0|) (pm h)` by metis_tac[poly_pmod_sub_eq_zero, poly_peval_unity] >>
      `!z x. poly z /\ poly x ==> poly (peval z x)` by rw[] >>
      `(peval (p ** n) x == peval (peval p (X ** n)) x) (pm h)` by metis_tac[poly_mod_eq_peval_root_eq_2] >>
      `peval (p ** n) x = peval p x ** n` by rw[poly_peval_exp] >>
      `peval (peval p (X ** n)) x = peval p (x ** n)` by rw[poly_peval_peval_X_exp] >>
      metis_tac[poly_mod_eq_eq],
      `pmonic z` by rw[GSYM poly_unity_pmonic, Abbr`z`] >>
      `(peval z X == |0|) (pm z)` by rw[poly_mod_ring_has_root_X, pmod_zero] >>
      `peval z X = unity k` by rw[poly_peval_unity, Abbr`z`] >>
      `!z. poly z ==> !n. poly (z ** n)` by rw[] >>
      `(X ** k == |1|) (pm z)` by metis_tac[poly_pmod_sub_eq_zero] >>
      `!z x. poly z /\ poly x ==> poly (peval z x)` by rw[] >>
      `z % z = |0|` by rw[poly_div_mod_id] >>
      metis_tac[poly_peval_by_X, poly_mod_reflexive, poly_mod_transitive]
    ]
  ]);

(* If only we have this:
  Theorem: Given any poly p, there is "an extension field where p splits",
           which is a quotient field by one of its irreducible factor.
     i.e.  !r:'a field. Field r ==> !p. monic p ==>
           ?z. ipoly z /\ (p % z = |0|) /\ poly_splits (PolyModRing r z) (lift p)
  Let q = lift p, s = PolyModRing r z.
  Since poly_splits s q, q has (deg q) distinct roots.

  Applying this to q = unity k,
  since X ** j, j = 1 to k (or 0 to (k-1)) are all its roots, they must be distinct.

  Then, if AKS in mod (unity k) is moved to mod h, the special h that gives a splitting field for (unity k),
  then distinct j gives distinct X ** j, as long as j < k, which is true in (mod k).

  So we don't need prime k anymore.
*)

(* ------------------------------------------------------------------------- *)
(* Introspective Theorems                                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload introspective checks for a range of monomials *)
val _ = overload_on("poly_intro_range",
       ``\(r:'a ring) (k:num) n m.  (* k is implicit in MOD (unity k) *)
          !c. 0 < c /\ c <= m ==> n intro (X + |c|)``);

(* Theorem: poly_intro_range r k m s /\ poly_intro_range r k n s ==> poly_intro_range r k (m * n) s *)
(* Proof: by poly_intro_mult *)
val poly_intro_range_product = store_thm(
  "poly_intro_range_product",
  ``!r:'a ring k. Ring r /\ 0 < k ==>
   !m n s. poly_intro_range r k m s /\ poly_intro_range r k n s ==> poly_intro_range r k (m * n) s``,
  rw_tac std_ss[poly_intro_mult]);

(* Overload polynomial introspective checks for ZN polynomials. *)
val _ = overload_on("poly_intro_checks",
                    ``\n k m. !c. 0 < c /\ c <= m ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))``);
(* This is poly_intro_range in the ring (ZN n) *)

(* Using EVERY to perform poly_intro_checks:
EVAL ``let n = 7; k = 7 in EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))) [1 .. k]``;
<=> T
*)

(* Theorem: poly_intro_checks n k s <=>
            EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))) [1 .. s] *)
(* Proof: by listRangeINC_EVERY, overloading of poly_intro_checks *)
val poly_intro_checks_thm = store_thm(
  "poly_intro_checks_thm",
  ``!n k s. poly_intro_checks n k s <=>
           EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))) [1 .. s]``,
  rpt strip_tac >>
  `!c. 0 < c <=> 1 <= c` by decide_tac >>
  rw[listRangeINC_EVERY]);
(* cannot put into computeLib due to LHS is a lambda expression *)

(* Put poly_intro_checks as definition (for printing) *)
val ZN_intro_checks_def = Define`
    ZN_intro_checks n k s <=> poly_intro_checks n k s
`;

(* Theorem: 0 < k /\ 0 < n ==>
   !c. poly_intro (ZN n) k n (x+ n c) = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
(* Proof:
   Note Ring (ZN n)                      by ZN_ring, 0 < n
    and char (ZN n) = n                  by ZN_char, 0 < n
    ==> poly_intro (ZN n) k n (x+ n c) = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
                                         by poly_intro_X_add_c, 0 < k
*)
val ZN_intro_eqn = store_thm(
  "ZN_intro_eqn",
  ``!n k. 0 < k /\ 0 < n ==>
   !c. poly_intro (ZN n) k n (x+ n c) = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))``,
  rpt strip_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  rw[poly_intro_X_add_c]);

(* Theorem: 0 < k /\ 0 < n ==> !m. poly_intro_range (ZN n) k n m =
   (!c. 0 < c /\ c <= m ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))) *)
(* Proof:
      poly_intro_range (ZN n) k n m
    = !c. 0 < c /\ c <= m ==> poly_intro (ZN n) k n (x+ n c)                     by notation
    = !c. 0 < c /\ c <= m ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))   by ZN_intro_eqn
*)
val ZN_intro_range_eqn = store_thm(
  "ZN_intro_range_eqn",
  ``!n k. 0 < k /\ 0 < n ==> !m. poly_intro_range (ZN n) k n m =
   (!c. 0 < c /\ c <= m ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))``,
  rw_tac std_ss[ZN_intro_eqn]);

(* Theorem: prime n /\ 0 < k ==> poly_intro (ZN n) k n (x+ n c) *)
(* Proof:
   Note 1 < n                             by ONE_LT_PRIME, prime n
     so 0 < n                             by arithmetic
    ==> Ring (ZN n)                       by ZN_ring, 0 < n
    and (ZN n).prod.id <> (ZN n).sum.id   by ZN_ids_alt, 1 < n
   Also char (ZN n) = n                   by ZN_char, 0 < n
   The result follows                     by poly_intro_X_add_c_prime_char, 0 < k
*)
val ZN_intro_by_prime = store_thm(
  "ZN_intro_by_prime",
  ``!n k c. prime n /\ 0 < k ==> poly_intro (ZN n) k n (x+ n c)``,
  rpt strip_tac >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ring, ZN_ids_alt] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_intro_X_add_c_prime_char]);

(* Theorem: prime n /\ 0 < k ==> poly_intro_range (ZN n) k n m *)
(* Proof: by ZN_intro_by_prime *)
val ZN_intro_range_by_prime = store_thm(
  "ZN_intro_range_by_prime",
  ``!n k m. prime n /\ 0 < k ==> poly_intro_range (ZN n) k n m``,
  rw_tac std_ss[ZN_intro_by_prime]);

(* Theorem: prime n /\ 0 < k ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
(* Proof:
   Note 1 < n                             by ONE_LT_PRIME, prime n
     so 0 < n                             by arithmetic
    ==> Ring (ZN n)                       by ZN_ring, 0 < n, [1]
    and (ZN n).prod.id <> (ZN n).sum.id   by ZN_ids_alt, 1 < n, [2]
    Now poly_intro (ZN n) k n (x+ n c)    by ZN_intro_by_prime, by prime n, 0 < k
   Thus (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))    by poly_intro_X_add_c, [1], [2]
*)
val ZN_intro_range_by_prime_alt = store_thm(
  "ZN_intro_range_by_prime_alt",
  ``!n k c. prime n /\ 0 < k ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))``,
  rpt strip_tac >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ring, ZN_ids_alt] >>
  metis_tac[ZN_intro_by_prime, poly_intro_X_add_c]);

(* Theorem: prime n /\ 0 < k ==> poly_intro_checks n k m *)
(* Proof: by ZN_intro_range_by_prime_alt. *)
val ZN_intro_checks_by_prime = store_thm(
  "ZN_intro_checks_by_prime",
  ``!n k m. prime n /\ 0 < k ==> poly_intro_checks n k m``,
  rw_tac std_ss[ZN_intro_range_by_prime_alt]);

(* Theorem: s <= t /\ poly_intro_checks n k t ==> poly_intro_checks n k s *)
(* Proof: by LESS_EQ_TRANS *)
val ZN_intro_checks_imp = store_thm(
  "ZN_intro_checks_imp",
  ``!n k s t. s <= t /\ poly_intro_checks n k t ==> poly_intro_checks n k s``,
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Introspective between Fields                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s <<= r ==> !k. 0 < k ==> !n c. n intro X + |c| <=>
            poly_intro s k n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) *)
(* Proof:
   Note s <= r                                by subfield_is_subring
    and #1 <> #0 /\ s.prod.id <> s.sum.id     by field_one_ne_zero
    Now poly_shift s (poly_one s) 1 = X       by subring_poly_X
    and poly_num s c = |c|                    by subring_poly_sum_num
   also !k. Unity s k = unity k               by subring_poly_unity

   Claim: poly_sub s (poly_exp s (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) n)
                     (poly_add s (poly_exp s (poly_shift s (poly_one s) 1) n)
                                 (poly_num s c)) = (X + |c|) ** n - (X ** n + |c|)
   Proof: poly_add s X |c| = X + |c|                         by subring_poly_add
       so poly_exp s (poly_add s X |c|) n = (X + |c|) ** n   by subring_poly_exp
     Also poly_exp s X n = X ** n                            by subring_poly_exp
       so poly_add s (poly_exp s X n) |c| = X ** n + |c|     by subring_poly_add
      The result follows                                     by subring_poly_sub

   Note !k. 0 < k ==> monic (unity k)         by poly_unity_monic
    and !k. 0 < k ==> (deg (unity k) = k)     by poly_unity_deg
   Expand by poly_intro_X_add_c_alt_1,
   The result follows                         by subring_poly_divides_iff, poly_monic_pmonic, subring_poly_deg
*)
val subfield_poly_intro = store_thm(
  "subfield_poly_intro",
  ``!(r s):'a field. s <<= r ==> !k. 0 < k ==>
   !n c:num. n intro X + |c| <=> poly_intro s k n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c))``,
  rpt strip_tac >>
  `s <= r` by rw[subfield_is_subring] >>
  `#1 <> #0 /\ s.prod.id <> s.sum.id` by rw[] >>
  `poly_shift s (poly_one s) 1 = X` by rw[subring_poly_X] >>
  `poly_num s c = |c|` by rw[subring_poly_sum_num] >>
  `!k. Unity s k = unity k` by rw[subring_poly_unity] >>
  `poly_sub s (poly_exp s (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) n)
                  (poly_add s (poly_exp s (poly_shift s (poly_one s) 1) n)
                              (poly_num s c)) = (X + |c|) ** n - (X ** n + |c|)` by
  (`!r:'a ring. Ring r ==> poly X /\ poly |c|` by rw[] >>
  `!r:'a ring. Ring r ==> poly ((X + |c|) ** n) /\ poly (X ** n + |c|)` by rw[] >>
  `poly_exp s (poly_add s X |c|) n = (X + |c|) ** n` by metis_tac[subring_poly_add, subring_poly_exp, poly_add_poly] >>
  `poly_add s (poly_exp s X n) |c| = X ** n + |c|` by metis_tac[subring_poly_add, subring_poly_exp, poly_add_poly, poly_exp_poly] >>
  metis_tac[subring_poly_sub]) >>
  `!r:'a ring. Ring r ==> poly ((X + |c|) ** n - (X ** n + |c|))` by rw[] >>
  `!r:'a ring. Ring r /\ #1 <> #0 ==> !k. 0 < k ==> monic (unity k) /\ (deg (unity k) = k)` by rw[poly_unity_monic, poly_unity_deg] >>
  metis_tac[poly_intro_X_add_c_alt_1, subring_poly_divides_iff, poly_monic_pmonic, subring_poly_deg]);

(* Theorem: (r === r_) f ==> !k. 0 < k ==> !n c. n intro X + |c| <=> poly_intro r_ k n (X_ +_ |c|_) *)
(* Proof:
   Note MAP f X = X_                      by field_iso_poly_X
    and MAP f |c| = |c|_                  by field_iso_poly_sum_num
   also !k. MAP f (unity k) = unity_ k    by field_iso_poly_unity

   Claim: MAP f ((X + |c|) ** n - (X ** n + |c|)) = (X_ +_ |c|_) **_ n -_ (X_ **_ n +_ |c|_)
   Proof: MAP f (X + |c|) = X_ +_ |c|_                  by field_iso_poly_add
       so MAP f ((X + |c|) ** n) = (X_ +_ |c|_) **_ n   by field_iso_poly_exp
     Also MAP (X ** n) = X_ **_ n                       by field_iso_poly_exp
       so MAP f (X ** n + |c|) = X_ **_ n +_ |c|_       by field_iso_poly_add
      The result follows                                by field_iso_poly_sub

   Note !k. poly (unity k)                by poly_unity_poly
   Expand by poly_intro_X_add_c_alt_1,
   The result follows                     by field_iso_poly_divides_iff
*)
val field_iso_poly_intro = store_thm(
  "field_iso_poly_intro",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !k. 0 < k ==>
   !n c:num. n intro X + |c| <=> poly_intro r_ k n (X_ +_ |c|_)``,
  rpt strip_tac >>
  `Ring r /\ Ring r_` by rw[] >>
  `MAP f X = X_` by rw[field_iso_poly_X] >>
  `MAP f |c| = |c|_` by rw[field_iso_poly_sum_num] >>
  `!k. MAP f (unity k) = unity_ k` by rw_tac std_ss[field_iso_poly_unity] >>
  `MAP f ((X + |c|) ** n - (X ** n + |c|)) = (X_ +_ |c|_) **_ n -_ (X_ **_ n +_ |c|_)` by
  (`!r:'a ring. Ring r ==> poly X /\ poly |c|` by rw[] >>
  `!r:'a ring. Ring r ==> poly ((X + |c|) ** n) /\ poly (X ** n + |c|)` by rw[] >>
  `MAP f ((X + |c|) ** n) = (X_ +_ |c|_) **_ n` by metis_tac[field_iso_poly_add, field_iso_poly_exp, poly_add_poly] >>
  `MAP f (X ** n + |c|) = X_ **_ n +_ |c|_` by metis_tac[field_iso_poly_add, field_iso_poly_exp, poly_add_poly, poly_exp_poly] >>
  metis_tac[field_iso_poly_sub]) >>
  qabbrev_tac `p = unity k` >>
  qabbrev_tac `q = (X + |c|) ** n - (X ** n + |c|)` >>
  `poly p /\ poly q` by rw[Abbr`p`, Abbr`q`] >>
  metis_tac[poly_intro_X_add_c_alt_1, field_iso_poly_divides_iff]);

(* ------------------------------------------------------------------------- *)
(* Introspective for Divisor                                                 *)
(* ------------------------------------------------------------------------- *)

(*

Introspective for cofactor q = n DIV p:

Let F = F_p[X]/h(X) for some factor h(X) in F_p[X]
We see that:          (X + a)^n = X^n + a                 ... (1)
Meanwhile, we have:   (X + a)^p = X^p + a                 ... (2)
The two give:         (X^p + a)^(n/p) = (X^p)^(n/p) + a   ... (3)
... hence we have:    (X + a)^(n/p) = X^(n/p) + a         ... (4)

I can understand (1) and (2). I can get (3) by the following:
  (X^p + a)^(n/p)
= ((X + a)^p)^(n/p)    by (2)
= (X + a)^(p * n/p)    by multiplying exponents
= (X + a)^n
= X^n + a              by (1)
= (X^p)^(n/p) + a      by un-mulitplying exponents

However, I had trouble getting (4) from (3). Your explanation was:
"Note that the p-th power X^p of a primitive r-th root of unity X is again a primitive r-th root of unity (and conversely, every primitive r-th root arises in this fashion)"

This statement is true, and you did say:
"Let F be a field extension of F_p by a primitive r-th root of unity X"

But does it mean that therefore we can replace X^p by X in any polynomial identity of indeterminate X?

Terence Tao
tao@math.ucla.edu

If X is a primitive r-th root of unity, then X = Y^p for some primitive r-th root of unity Y,
and the field F generated by F_p and Y is the same as the field generated by F_p and X
(because X is also a power of Y).
From (3) we have (Y^p+a)^{n/p} = (Y^p)^{n/p} + a in F,
and so (X+a)^{n/p} = X^{n/p} + a in F as well.

Terry
(16/07/15)

A simple way: Since X^p = X   by some Fermat's Little Theorem, so (4) holds.
This won't work. Better use Tao's suggestion:
(1) show that x -> x ** p is an isomorphism, this is the Frobenius map.
(2) show that p = (X + a) ** q - (X ** q + a) is a "subfield" poly, preserved by the map: p_ = p.
(3) Note that p_ = (Y + a) ** q - (Y ** q + a) = |0|_,
    so p = |0| by ring_iso_eq_poly_zero, or (X + a) ** q = (X ** q + a).
*)

(* Theorem: FiniteField r ==> !k. 0 < k ==> !c. (char r) intro X + |c| *)
(* Proof:
   Note FiniteField r
    ==> Field r                   by finite_field_is_field
    and prime (char r)            by finite_field_char
     so (char r) intro X + |c|    by poly_intro_X_add_c_prime_char
*)
val poly_intro_X_add_c_prime_char_1 = store_thm(
  "poly_intro_X_add_c_prime_char_1",
  ``!r:'a field. FiniteField r ==> !k. 0 < k ==> !c:num. (char r) intro X + |c|``,
  rw[poly_intro_X_add_c_prime_char, finite_field_is_field, finite_field_char]);

(* Theorem: FiniteField r /\ 0 < k ==>
            ((X + |c|) ** (char r) == (X ** (char r) + |c|)) (pm (unity k)) *)
(* Proof: by poly_intro_X_add_c_prime_char_alt, finite_field_char *)
val poly_intro_X_add_c_prime_char_1_alt = store_thm(
  "poly_intro_X_add_c_prime_char_1_alt",
  ``!r:'a field k c:num. FiniteField r /\ 0 < k ==>
           ((X + |c|) ** (char r) == (X ** (char r) + |c|)) (pm (unity k))``,
  rw_tac std_ss[poly_intro_X_add_c_prime_char_alt, finite_field_char, finite_field_is_field, field_is_ring]);

(* Idea:
Let s be a subfield of r, possibly s is the prime subfield.
Let x NOTIN s, but (minimal x) is a subfield poly.
Let y be a conjugate of s, then (minimal y = minimal x)  by eq_conj_eq_poly_minimal.
Let z = minimal x = minimal y.
Then PolyModRing r z is a field with x y both root of z  by poly_minimal_has_element_root

I want:  In (PolyModRing r (minimal y)), (y + |c|) ** q == (y ** q + |c|) (pm u), that is q intro_in_y |X| + |c|
==>      In (PolyModRing r (minimal x)), (x + |c|) ** q == (x ** q + |c|) (pm u), or q intro_in_x |X| + |c|

*)

(* Picture:

Consider a Field r, with some nonlinear monic irreducible z.
This gives two fields: (t = PolyModRing r z), and (st = PolyModConst r z), with st <<= t.
  |0|  |1| .............|c| |  X ...................
  <-- PolyModConst r z ---->
  <----------------- PolyModRing r z -------------->

Now, for every poly p, map it to (p ** c)   where c = char r.
  |0| ** char r |1| ** char r       |c| ** char r  |  X ** char r ......

Since FieldIso up r (PolyModConst r z)   by poly_mod_const_iso_field_alt
CARD R = CARD (PolyModConst r z).carrier,
 and if CARD R = char r, then |c| ** char r = |c|.
Or f = \p:'a poly. p ** (char r)  keeps st unchanged, but in t, X --> X ** p.

The best I can come up with is this:

There are two finite fields, r and r (the same).
Let z be a nonlinear monic irreducible with order X = n, for (unity n).
Then (t = PolyModRing r z) is a finite field, with order X = n.
Let Y = X ** c, where c = char r, and prime c.
So X is not a primitive of t, then Y is also not a primitive of t.
But Y can be conjugate of X (assume CARD B = char r).
and z = minimal X = minimal Y.

So what is the difference between the finite field from X, and finite field from Y ?

((X ** p + |c|) ** q == (X ** p) ** q + |c|) (pm u)
means I know:   [c,..<p>.., #1] ** q == [0,..<p>..,#1] ** q + [c]  in division by u.  [1]

I want to say:  [c,#1] ** q == [0,#1] ** q + [c]    in division also by u. [2]

The reason offered is: in the world of Field of Y, [1] looks like [2], or [1] becomes [2], so q is introspective.

The AKS paper effectively takes this as a theorem:

Let c = char r.

(p ** c == q ** c) (pm u) ==> (p == q) (pm u)

I do have:

poly_distinct_irreducibles_mod_exp_char_eq
|- !r. FiniteField r ==> !s. FINITE s /\ miset s /\ s <> {} ==>
   !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (PPROD s)) ==> (p == q) (pm (PPROD s))
poly_unity_eq_poly_cyclo_product
|- !r. FiniteField r ==> !n. n divides CARD R+ ==> (unity n = PPIMAGE cyclo (divisors n))

*)

(* Theorem: FiniteField r ==> !k. k divides (CARD R+) ==>
        !n. (char r) divides n /\ n intro X + |c| ==> (n DIV (char r)) intro X + |c| *)
(* Proof:
   Let p = char r, q = n DIV p.
   Then prime p                  by finite_field_char
    and n = q * p                by DIVIDES_EQN, 0 < p
   Note 0 < CARD R+              by field_nonzero_card_pos
   Thud 0 < k                    by ZERO_DIVIDES

   Let u = (X + |c|) ** q, v = X ** q + |c|.
       u ** p
     = ((X + |c|) ** q) ** p     by notation
     = (X + |c|) ** n            by poly_exp_mult

       v ** p
     = (X ** q + |c|) ** p       by notation
     = X ** q ** p + |c| ** p    by poly_freshman_thm
     = X ** n + |c| ** p         by poly_exp_mult
     = X ** n + |c|              by poly_fermat_thm

   Note n intro X + |c|                     by given
     so (u ** p == v ** p) (pm (unity k))   by poly_intro_X_add_c
   With k divides (CARD R+)                 by given
   Thus (u == v) (pm (unity k))             by poly_unity_mod_exp_char_eq
     or q intro X + |c|                     by poly_intro_X_add_c
*)
val poly_intro_X_add_c_prime_char_2 = store_thm(
  "poly_intro_X_add_c_prime_char_2",
  ``!r:'a field. FiniteField r ==> !k. k divides (CARD R+) ==>
   !n c:num. (char r) divides n /\ n intro X + |c| ==> (n DIV (char r)) intro X + |c|``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `q = n DIV p` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `0 < p` by rw[PRIME_POS] >>
  `n = q * p` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `0 < k` by metis_tac[field_nonzero_card_pos, ZERO_DIVIDES, NOT_ZERO] >>
  qabbrev_tac `u = (X + |c|) ** q` >>
  qabbrev_tac `v = X ** q + |c|` >>
  `poly (X ** q) /\ poly |c|` by rw[] >>
  `poly u /\ poly v` by rw[Abbr`u`, Abbr`v`] >>
  `u ** p = (X + |c|) ** n` by rw[poly_exp_mult, Abbr`u`] >>
  `v ** p = (X ** q) ** p + |c| ** p` by rw_tac std_ss[poly_freshman_thm, Abbr`v`, Abbr`p`] >>
  `_ = X ** n + |c| ** p ` by rw[poly_exp_mult] >>
  `_ = X ** n + |c|` by rw_tac std_ss[poly_fermat_thm, Abbr`p`] >>
  metis_tac[poly_intro_X_add_c, poly_unity_mod_exp_char_eq]);

(* This is a good result, but need a better version to be useful. *)

(* Theorem: FiniteField r ==> !k. coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
            !n. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c| *)
(* Proof:
   Let d = ordz k (CARD R), then 0 < d          by given, 1 < d
   Note 1 < CARD R                              by finite_field_card_gt_1
     so 1 < k, then 0 < k                       by ZN_order_with_coprime_1

   Step 1: get a field/subfield pair
   Note FiniteField r /\ 0 < d
    ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists
    and pmonic z                                by poly_monic_irreducible_property

   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                           by poly_mod_irreducible_finite_field
     so Field t                                 by finite_field_is_field
    and Field st                                by poly_mod_const_field
   Also st <<= t                                by poly_mod_const_subfield_poly_mod
    and st <= t                                 by subfield_is_subring
    and (t <:> st) = deg z                      by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier                by poly_mod_const_subfield_card
    ==> k divides CARD (ring_nonzero t)         by subfield_card_coprime_iff

   The situation:
                                   t = PolyModRing r z, with k divides CARD (ring_nonzero t)
                                   |          n intro_ Xc_t ==> q intro_ Xc_t
                                   |                   /\            ||
                                   |                   ||            ||
       r <-- FieldIso, f = up --> st = PolyModConst r z||            ||
       start: n intro (X + |c|) ==> n intro_ Xc_st     ||            \/
         end: q intro (X + |c|) ----------------------------<== q intro_ Xc_st

   Step 2: apply poly_intro_X_add_c_prime_char_2
   Let q = n DIV (char r).
   Note char t = char r                         by poly_mod_ring_char, pmonic z
    and FieldIso up r st                        by poly_mod_const_iso_field

    Let Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)
    and Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)

   Note MAP up (X + |c|) = Xc_st                by field_iso_poly_X_add_c
   With n intro (X + |c|                        by given
     so poly_intro st k n Xc_st                 by field_iso_poly_intro, FieldIso up r st
    ==> poly_intro t k n Xc_t                   by subfield_poly_intro, st <<= t
    ==> poly_intro t k q Xc_t                   by poly_intro_X_add_c_prime_char_2
    ==> poly_intro st k q Xc_st                 by subfield_poly_intro, st <= t
    ==> q intro X + |c|                         by field_iso_poly_intro, FieldIso up r st
*)
val poly_intro_X_add_c_prime_char_3 = store_thm(
  "poly_intro_X_add_c_prime_char_3",
  ``!r:'a field. FiniteField r ==> !k. coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
   !n c:num. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz k (CARD R)` >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `0 < k /\ 0 < d /\ d <> 1` by decide_tac >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `t = PolyModRing r z` >>
  qabbrev_tac `st = PolyModConst r z` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `Field t` by rw[finite_field_is_field] >>
  `Field st` by rw[poly_mod_const_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod, Abbr`t`, Abbr`st`] >>
  `st <= t` by rw[subfield_is_subring] >>
  `(t <:> st) = deg z` by rw[poly_mod_const_subfield_dim, Abbr`t`, Abbr`st`] >>
  `CARD R = CARD st.carrier` by rw[poly_mod_const_subfield_card, Abbr`st`] >>
  `k divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  qabbrev_tac `q = n DIV (char r)` >>
  `char t = char r` by rw[poly_mod_ring_char, Abbr`t`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  qabbrev_tac `Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)` >>
  qabbrev_tac `Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)` >>
  `MAP up (X + |c|) = Xc_st` by rw[field_iso_poly_X_add_c, Abbr`Xc_st`] >>
  `poly_intro st k n Xc_st` by metis_tac[field_iso_poly_intro] >>
  `poly_intro t k n Xc_t` by metis_tac[subfield_poly_intro] >>
  `poly_intro t k q Xc_t` by metis_tac[poly_intro_X_add_c_prime_char_2] >>
  `poly_intro st k q Xc_st` by metis_tac[subfield_poly_intro] >>
  `q intro X + |c|` by metis_tac[field_iso_poly_intro]);

(* Yes! This is the theorem I always wanted. *)

(* Does the two above use Tao's argument: replacing X ** p by X? Seems not.
   It makes use of the fact: (f ** p == g ** p) gives (f == g), poly_unity_mod_exp_char_eq.
   This is based on k divides (CARD R+) to express (unity k) as distinct irreducibles,
   then use coprime k (CARD R) /\ 1 < ordz k (CARD R) for subfield transformation,
   can use coprime k (CARD R) /\ 1 < (CARD R) MOD k to imply 1 < ordz k (CARD R)
       by ZN_coprime_order_gt_1.
*)

(* These seem to be better than poly_ring_homo_intro *)

(* Theorem: FiniteField r /\ 0 < k ==> poly_intro_range r k (char r) s *)
(* Proof: by poly_intro_X_add_c_prime_char_1 *)
val poly_intro_range_char = store_thm(
  "poly_intro_range_char",
  ``!r:'a field k s. FiniteField r /\ 0 < k ==> poly_intro_range r k (char r) s``,
  rw[poly_intro_X_add_c_prime_char_1]);

(* Theorem: FiniteField r /\ k divides CARD R+ ==>
            !n c:num. char r divides n /\ n intro (X + |c|) ==> (n DIV char r) intro (X + |c|) *)
(* Proof:
   Let p = char r, q = n DIV p.
   Then prime p                  by finite_field_char
    and n = q * p                by DIVIDES_EQN, 0 < p
   Note 0 < CARD R+              by field_nonzero_card_pos
   Thud 0 < k                    by ZERO_DIVIDES

   Let u = (X + |c|) ** q, v = X ** q + |c|, z = unity k.
       u ** p
     = ((X + |c|) ** q) ** p     by notation
     = (X + |c|) ** n            by poly_exp_mult

       v ** p
     = (X ** q + |c|) ** p       by notation
     = X ** q ** p + |c| ** p    by poly_freshman_thm
     = X ** n + |c| ** p         by poly_exp_mult
     = X ** n + |c|              by poly_fermat_thm

   Note n intro X + |c|                     by given
     so (u ** p - v ** p == |0|) (pm z)     by poly_intro_X_add_c_alt_2
    Now ?s. FINITE s /\ miset s /\ (z = PPROD s)
                                            by poly_unity_by_distinct_irreducibles
   Thus (u - v == |0|) (pm z)               by poly_distinct_irreducibles_mod_exp_eq_zero
     or q intro X + |c|                     by poly_intro_X_add_c_alt_2
*)
val poly_intro_X_add_c_prime_char_cofactor_1 = store_thm(
  "poly_intro_X_add_c_prime_char_cofactor_1",
  ``!r:'a field k. FiniteField r /\ k divides CARD R+ ==>
   !n c:num. char r divides n /\ n intro (X + |c|) ==> (n DIV char r) intro (X + |c|)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `q = n DIV p` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `0 < p` by rw[PRIME_POS] >>
  `n = q * p` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `0 < k` by metis_tac[field_nonzero_card_pos, ZERO_DIVIDES, NOT_ZERO] >>
  qabbrev_tac `u = (X + |c|) ** q` >>
  qabbrev_tac `v = X ** q + |c|` >>
  `poly (X ** q) /\ poly |c|` by rw[] >>
  `poly u /\ poly v` by rw[Abbr`u`, Abbr`v`] >>
  `u ** p = (X + |c|) ** n` by rw[poly_exp_mult, Abbr`u`] >>
  `v ** p = (X ** q) ** p + |c| ** p` by rw_tac std_ss[poly_freshman_thm, Abbr`v`, Abbr`p`] >>
  `_ = X ** n + |c| ** p ` by rw[poly_exp_mult] >>
  `_ = X ** n + |c|` by rw_tac std_ss[poly_fermat_thm, Abbr`p`] >>
  qabbrev_tac `z = unity k` >>
  `((u - v) ** p == |0|) (pm z)` by metis_tac[poly_intro_X_add_c_alt_2, poly_freshman_thm_sub] >>
  `?s. FINITE s /\ miset s /\ s <> {} /\ (z = PPROD s)` by rw[poly_unity_by_distinct_irreducibles, Abbr`z`] >>
  `(u - v == |0|) (pm z)` by metis_tac[poly_distinct_irreducibles_mod_exp_eq_zero, poly_sub_poly] >>
  metis_tac[poly_intro_X_add_c_alt_2]);
(* This result is the same as: poly_intro_X_add_c_prime_char_2, different proof. *)

(* Theorem: FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
            !n. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c| *)
(* Proof:
   Let d = ordz k (CARD R), then 0 < d          by given, 1 < d
   Note 1 < CARD R                              by finite_field_card_gt_1
     so 1 < k, then 0 < k                       by ZN_order_with_coprime_1

   Step 1: get a field/subfield pair
   Note FiniteField r /\ 0 < d
    ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists
    and pmonic z                                by poly_monic_irreducible_property

   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                           by poly_mod_irreducible_finite_field
     so Field t                                 by finite_field_is_field
    and Field st                                by poly_mod_const_field
   Also st <<= t                                by poly_mod_const_subfield_poly_mod
    and st <= t                                 by subfield_is_subring
    and (t <:> st) = deg z                      by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier                by poly_mod_const_subfield_card
    ==> k divides CARD (ring_nonzero t)         by subfield_card_coprime_iff

   The situation:
                                   t = PolyModRing r z, with k divides CARD (ring_nonzero t)
                                   |          n intro_ Xc_t ==> q intro_ Xc_t
                                   |                   /\            ||
                                   |                   ||            ||
       r <-- FieldIso, f = up --> st = PolyModConst r z||            ||
       start: n intro (X + |c|) ==> n intro_ Xc_st     ||            \/
         end: q intro (X + |c|) ----------------------------<== q intro_ Xc_st

   Step 2: apply poly_intro_X_add_c_prime_char_cofactor_1
   Let q = n DIV (char r).
   Note char t = char r                         by poly_mod_ring_char, pmonic z
    and FieldIso up r st                        by poly_mod_const_iso_field

    Let Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)
    and Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)

   Note MAP up (X + |c|) = Xc_st                by field_iso_poly_X_add_c
   With n intro (X + |c|                        by given
     so poly_intro st k n Xc_st                 by field_iso_poly_intro, FieldIso up r st
    ==> poly_intro t k n Xc_t                   by subfield_poly_intro, st <<= t
    ==> poly_intro t k q Xc_t                   by poly_intro_X_add_c_prime_char_2
    ==> poly_intro st k q Xc_st                 by subfield_poly_intro, st <= t
    ==> q intro X + |c|                         by field_iso_poly_intro, FieldIso up r st
*)
val poly_intro_X_add_c_prime_char_cofactor_2 = store_thm(
  "poly_intro_X_add_c_prime_char_cofactor_2",
  ``!r:'a field k. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
   !n c:num. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz k (CARD R)` >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `0 < k /\ 0 < d /\ d <> 1` by decide_tac >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `t = PolyModRing r z` >>
  qabbrev_tac `st = PolyModConst r z` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `Field t` by rw[finite_field_is_field] >>
  `Field st` by rw[poly_mod_const_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod, Abbr`t`, Abbr`st`] >>
  `st <= t` by rw[subfield_is_subring] >>
  `(t <:> st) = deg z` by rw[poly_mod_const_subfield_dim, Abbr`t`, Abbr`st`] >>
  `CARD R = CARD st.carrier` by rw[poly_mod_const_subfield_card, Abbr`st`] >>
  `k divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  qabbrev_tac `q = n DIV (char r)` >>
  `char t = char r` by rw[poly_mod_ring_char, Abbr`t`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  qabbrev_tac `Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)` >>
  qabbrev_tac `Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)` >>
  `MAP up (X + |c|) = Xc_st` by rw[field_iso_poly_X_add_c, Abbr`Xc_st`] >>
  `poly_intro st k n Xc_st` by metis_tac[field_iso_poly_intro] >>
  `poly_intro t k n Xc_t` by metis_tac[subfield_poly_intro] >>
  `poly_intro t k q Xc_t` by metis_tac[poly_intro_X_add_c_prime_char_2] >>
  `poly_intro st k q Xc_st` by metis_tac[subfield_poly_intro] >>
  `q intro X + |c|` by metis_tac[field_iso_poly_intro]);
(* This result is the same as: poly_intro_X_add_c_prime_char_3, same proof almost. *)

(* Above two give Sutherland's argument: obtain (f == 0) from (f ** p == 0), poly_distinct_irreducibles_mod_exp_eq_zero.
   still based on k divides (CARD R+) to express (unity k) as distinct irreducibles,
   then use coprime k (CARD R) /\ 1 < ordz k (CARD R) by subfield transformation,
   can use coprime k (CARD R) /\ 1 < (CARD R) MOD k to imply 1 < ordz k (CARD R)
       by ZN_coprime_order_gt_1.
*)

(* ------------------------------------------------------------------------- *)
(* Introspective Relation based on pmonic modulus.                           *)
(* ------------------------------------------------------------------------- *)

(*
poly_intro_def
|- !r k n p. n intro p <=> poly p /\ (p ** n == peval p (X ** n)) (pm (unity k))
*)

(* Define introspective with respect to a modulus z polynomial *)
val introspective_def = Define`
    introspective (r:'a ring) (z:'a poly) n p <=> (p ** n == peval p (X ** n)) (pm z)
`;

(* Theorem: poly p ==> !z. introspective r z n p <=> ((peval p X) ** n == peval p (X ** n)) (pm z) *)
(* Proof: by introspective_def, poly_peval_by_X *)
val introspective_alt = store_thm(
  "introspective_alt",
  ``!r:'a ring. Ring r ==> !n p. poly p ==>
   !z. introspective r z n p <=> ((peval p X) ** n == peval p (X ** n)) (pm z)``,
  rw[introspective_def, poly_peval_by_X]);

(* Theorem: 0 < k ==> poly_intro r k n p <=> poly p /\ introspective r (unity k) n p *)
(* Proof: by poly_intro_def, introspective_def *)
val poly_intro_introspective = store_thm(
  "poly_intro_introspective",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
   !n p. poly_intro r k n p <=> poly p /\ introspective r (unity k) n p``,
  metis_tac[poly_intro_def, introspective_def]);

(* Theorem: Ring r /\ (#1 = #0) ==> !z n p. poly p ==> introspective r z n p *)
(* Proof:
   By introspective_def, this is to show:
      (p ** n == peval p (X ** n)) (pm z)
   Note |1| = |0|                  by poly_one_eq_poly_zero
   Thus !p. poly p ==> (p = |0|)   by poly_one_eq_zero
    Now poly (p ** n)              by poly_exp_poly
    and poly (peval p (X ** n))    by poly_peval_poly, poly_X_exp
   Hence true                      by poly_mod_reflexive
*)
val introspective_trivial = store_thm(
  "introspective_trivial",
  ``!r:'a ring. Ring r /\ (#1 = #0) ==> !z n p. poly p ==> introspective r z n p``,
  rw_tac std_ss[introspective_def] >>
  `!p. poly p ==> (p = |0|)` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  `poly (p ** n) /\ poly (peval p (X ** n))` by rw[] >>
  rw_tac std_ss[poly_mod_reflexive]);

(* Theorem: pmonic p /\ pmonic z /\ z pdivides p ==>
      !n q. poly q /\ introspective r p n q ==> introspective r z n q *)
(* Proof:
   Note poly (q ** n)                       by poly_exp_poly
    and poly (peval q (X ** n))             by poly_peval_poly, poly_X, poly_exp_poly
     introspective r p n q
   = (q ** n == peval q (X ** n)) (pm p)    by introspective_def
   = (q ** n == peval q (X ** n)) (pm z)    by poly_divides_pmod_eq, z pdivides p
   = introspective r z n q                  by introspective_def
*)
val introspective_shift_factor = store_thm(
  "introspective_shift_factor",
  ``!r:'a ring p z. Ring r /\ ulead p /\ ulead z /\ z pdivides p ==>
   !n q. poly q /\ introspective r p n q ==> introspective r z n q``,
  rw[introspective_def] >>
  qabbrev_tac `u = q ** n` >>
  qabbrev_tac `v = peval q (X ** n)` >>
  `poly u /\ poly v` by rw[Abbr`u`, Abbr`v`] >>
  metis_tac[poly_divides_pmod_eq]);

(* Theorem: 0 < k /\ ulead z /\ z pdivides (unity k) ==>
      !n p. poly_intro r k n p ==> introspective r z n p *)
(* Proof:
   Note ulead (unity k)                 by poly_unity_lead, 0 < k
       poly_intro r k n p
   ==> poly p /\
       introspective r (unity k) n p    by poly_intro_introspective
   ==> introspective r z n p            by introspective_shift_factor, z pdivides (unity k)
*)
val poly_intro_shift_factor = store_thm(
  "poly_intro_shift_factor",
  ``!r:'a ring. Ring r ==> !k z. 0 < k /\ ulead z /\ z pdivides (unity k) ==>
   !n p. poly_intro r k n p ==> introspective r z n p``,
  metis_tac[poly_intro_introspective, introspective_shift_factor, poly_unity_poly, poly_unity_lead, ring_unit_one]);

(*
ring_homo_intro_ZN_to_ZN_X_add_c
|- !n m. 0 < n /\ 1 < m /\ m divides n ==>
   !k s. 0 < k /\ s < m ==>
   !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c)
*)

(*
> poly_intro_shift_factor |> ISPEC ``ZN m``;
|- Ring (ZN m) /\ (ZN m).prod.id <> (ZN m).sum.id ==>
   !k z. 0 < k /\ Ulead (ZN m) z /\ poly_divides (ZN m) z (x^- m k) ==>
   !n p. poly_intro (ZN m) k n p ==> introspective (ZN m) z n p
*)

(*
Note: the introspective multiplicative property requires the modulus z = unity k,
      for poly_peval_unity to give: peval (unity n) p = p ** n - |1|
      thus making peval z (X ** n) = z
*)

(* Theorem: poly p /\ 0 < k ==>
      !n m. introspective r (unity k) n p /\ introspective r (unity k) m p ==>
            introspective r (unity k) (n * m) p *)
(* Proof:
   Let z = unity k, then ulead z                by poly_unity_lead, ring_unit_one
   Note (p ** n == peval p (X ** n)) (pm z)     by introspective_def
    and (p ** m == peval p (X ** m)) (pm z)     by introspective_def

   Step 1: use (introspective r z n p) to show:
           (p ** (n * m) == peval (p ** m) (X ** n)) (pm z)
      Note (p ** n == peval p (X ** n)) (pm z)                   by introspective_def
      Taking both sides to m-th power,
           ((p ** n) ** m == (peval p (X ** n)) ** m) (pm z)     by pmod_exp_eq
      LHS = (p ** n) ** m = p ** (n * m)                         by poly_exp_mult
      RHS = (peval p (X ** n)) ** m = peval (p ** m) (X ** n)    by poly_peval_exp
      Hence (p ** (n * m) == peval (p ** m) (X ** n)) (pm z)

   Step 2: use (introspective r z m p) to show:
           (peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)
      Since (p ** m == peval p (X ** m)) (pm z)                   by introspective_def
         so (p ** m - peval p (X ** m) == |0|) (pm z)             by poly_pmod_sub_eq_zero
      Hence ?q. poly q /\ (p ** m - peval p (X ** m) = q * z)     by pmod_eq_zero
      Evaluate LHS by X ** n,
         peval (p ** m - peval p (X ** m)) (X ** n)
       = peval (p ** m) (X ** n) - peval (peval p (X ** m)) (X ** n)  by poly_peval_sub
       = peval (p ** m) (X ** n) - peval p (X ** (m * n))  by poly_peval_peval_X_exp_X_exp
       = peval (p ** m) (X ** n) - peval p (X ** (n * m))  by MULT_COMM
      Evaluate RHS by X ** n,
         peval (q * z) (X ** n)
       = peval q (X ** n) * (peval z (X ** n))             by poly_peval_mult
      But  peval z (X ** n)
         = peval (unity k) (X ** n)                        by z = unity k
         = (X ** n) ** k - |1|                             by poly_peval_unity
         = unity (n * k)                                   by poly_exp_mult
         = unity (k * n)                                   by MULT_COMM
      Now, (unity k) pdivides (unity (k * n))              by poly_unity_divides
       so  ?t. poly t /\ (unity (k * n) = t * z)           by poly_divides_def
      Giving
        peval (p ** m) (X ** n) - peval p (X ** (n * m))
      = peval q (X ** n) * (t * z)                         by peval z (X ** n) = unity (k * n)
      = (peval q (X ** n) * t) * z                         by poly_mult_assoc
      Therefore
      (peval (p ** m) (X ** n) - peval p (X ** (n * m)) == |0|) (pm z)   by pmod_eq_zero
      or (peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)      by poly_pmod_sub_eq_zero

    Combining both steps,
       p ** (n * m) == peval p (X ** (n * m)) (pm z)       by poly_mod_transitive
    or n * m intro p                                       by introspective_def
*)
val introspective_unity_mult = store_thm(
  "introspective_unity_mult",
  ``!r:'a ring. Ring r ==> !p k. poly p /\ 0 < k ==>
   !n m. introspective r (unity k) n p /\ introspective r (unity k) m p ==>
         introspective r (unity k) (n * m) p``,
  rpt (stripDup[introspective_def]) >>
  qabbrev_tac `z = unity k` >>
  `ulead z` by rw[Abbr`z`] >>
  `(p ** (n * m) == peval (p ** m) (X ** n)) (pm z)` by
  (`((p ** n) ** m == (peval p (X ** n)) ** m) (pm z)` by rw[pmod_exp_eq] >>
  `(p ** n) ** m = p ** (n * m)` by rw[poly_exp_mult] >>
  `(peval p (X ** n)) ** m = peval (p ** m) (X ** n)` by rw[poly_peval_exp] >>
  metis_tac[]) >>
  `(peval (p ** m) (X ** n) == peval p (X ** (n * m))) (pm z)` by
    (`poly (p ** m) /\ poly (X ** n) /\ poly (peval p (X ** m))` by rw[] >>
  `(p ** m - peval p (X ** m) == |0|) (pm z)` by metis_tac[poly_pmod_sub_eq_zero] >>
  `?q. poly q /\ (p ** m - peval p (X ** m) = q * z)` by rw[GSYM pmod_eq_zero] >>
  `peval (p ** m - peval p (X ** m)) (X ** n)
    = peval (p ** m) (X ** n) - peval (peval p (X ** m)) (X ** n)` by rw_tac std_ss[poly_peval_sub] >>
  `_ = peval (p ** m) (X ** n) - peval p (X ** (m * n))` by rw_tac std_ss[poly_peval_peval_X_exp_X_exp] >>
  `_ = peval (p ** m) (X ** n) - peval p (X ** (n * m))` by rw_tac std_ss[MULT_COMM] >>
  `peval (q * z) (X ** n) = peval q (X ** n) * (peval z (X ** n))` by rw[poly_peval_mult] >>
  `peval z (X ** n) = (X ** n) ** k - |1|` by rw[poly_peval_unity, Abbr`z`] >>
  `_ = unity (n * k)` by rw[poly_exp_mult] >>
  `_ = unity (k * n)` by rw_tac std_ss[MULT_COMM] >>
  `?t. poly t /\ (unity (k * n) = t * z)` by metis_tac[poly_unity_divides, poly_divides_def] >>
  `peval (p ** m) (X ** n) - peval p (X ** (n * m)) = (peval q (X ** n)) * (t * z)` by metis_tac[poly_mult_assoc] >>
  `_ = (peval q (X ** n) * t) * z` by rw[poly_mult_assoc] >>
  `poly (peval (p ** m) (X ** n) - peval p (X ** (n * m))) /\ poly (peval q (X ** n) * t)` by rw[] >>
  `(peval (p ** m) (X ** n) - peval p (X ** (n * m)) == |0|) (pm z)` by metis_tac[pmod_eq_zero] >>
  rw[poly_pmod_sub_eq_zero]) >>
  `poly (p ** (n * m)) /\ poly (peval (p ** m) (X ** n)) /\ poly (peval p (X ** (n * m)))` by rw[] >>
  metis_tac[poly_mod_transitive, introspective_def]);

(* Theorem: ulead z /\ poly p /\ poly q ==>
        !n. introspective r z n p /\ introspective r z n q ==> introspective r z n (p * q) *)
(* Proof:
   By introspective_def, this is to show:
      ((p * q) ** n == peval (p * q) (X ** n)) (pm z)
   Note (p ** n == peval p (X ** n)) (pm z)    by introspective_def, introspective r z n p
    and (q ** n == peval q (X ** n)) (pm z)    by introspective_def, introspective r z n q
   Therefore,
   (p ** n * q ** n == peval p (X ** n) * peval q (X ** n)) (pm z)   by pmod_mult
   But  p ** n * q ** n = (p * q) ** n                               by poly_mult_exp
   and  peval p (X ** n) * peval q (X ** n) = peval (p * q) (X ** n) by poly_peval_mult
   Hence introspective r z n (p * q)                                 by introspective_def
*)
val introspective_compose = store_thm(
  "introspective_compose",
  ``!r:'a ring. Ring r ==> !z p q. ulead z /\ poly p /\ poly q ==>
   !n. introspective r z n p /\ introspective r z n q ==> introspective r z n (p * q)``,
  rw_tac std_ss[introspective_def] >>
  `(p ** n * q ** n == peval p (X ** n) * peval q (X ** n)) (pm z)` by rw[pmod_mult] >>
  `p ** n * q ** n = (p * q) ** n` by rw[poly_mult_exp] >>
  `peval (p * q) (X ** n) = peval p (X ** n) * peval q (X ** n)` by rw[poly_peval_mult] >>
  metis_tac[]);

(* Theorem: poly z /\ poly p ==> introspective r z 1 p *)
(* Proof:
   By introspective_def, this is to show:
      (p ** 1 == peval p (X ** 1)) (pm z)
   or to show:    (p == peval p X) (pm z)  by poly_X, poly_exp_1
   Now  peval p X = p                      by poly_peval_by_X
   Hence true                              by poly_mod_reflexive
*)
val introspective_1 = store_thm(
  "introspective_1",
  ``!r:'a ring. Ring r ==> !z p. poly z /\ poly p ==> introspective r z 1 p``,
  rw_tac std_ss[introspective_def] >>
  rw_tac std_ss[poly_exp_1, poly_X, poly_peval_by_X, poly_mod_reflexive]);

(* Theorem: poly z ==> !n. introspective r z n |1| *)
(* Proof:
   By introspective_def, this is to show:
      ( |1| ** n == peval |1| (X ** n)) (pm z)
     peval |1| (X ** n)
   = |1|                            by poly_peval_one
   = |1| ** n                       by poly_one_exp
   Hence true                       by poly_mod_reflexive
*)
val introspective_one = store_thm(
  "introspective_one",
  ``!r:'a ring. Ring r ==> !z. poly z ==> !n. introspective r z n |1|``,
  rw[introspective_def]);

(* Theorem: poly z /\ 0 < n ==> introspective r z n |0| *)
(* Proof:
   By introspective_def_def, this is to show:
      ( |0| ** n == peval |0| (X ** n)) (pm z)
     peval |0| (X ** n)
   = |0|                           by poly_peval_zero
   = |0| ** n                      by poly_zero_exp, n <> 0.
   Hence true                      by poly_mod_reflexive.
*)
val introspective_zero = store_thm(
  "introspective_zero",
  ``!r:'a ring. Ring r ==> !z n. poly z /\ 0 < n ==> introspective r z n |0|``,
  rw_tac std_ss[introspective_def] >>
  `n <> 0` by decide_tac >>
  rw_tac std_ss[poly_peval_zero, poly_zero_exp] >>
  rw_tac std_ss[poly_mod_reflexive, poly_zero_poly]);

(* Theorem: Ring r /\ pmonic z ==> ~(0 intro |0|) *)
(* Proof:
   By poly_intro_def, this is to show: ~( |1| == |0|) (pm z)
   By contradiction, suppose ( |1| == |0|) (pm z).
       ( |1| == |0|) (pm z)
   <=> |1| % z = |0| % z           by pmod_def_alt
   <=> |1| = |0|                   by poly_mod_one, poly_mod_zero
    => z = |0|                     by poly_one_eq_poly_zero
   which contradicts pmonic z      by poly_deg_pos_nonzero
*)
val introspective_not_0_zero = store_thm(
  "introspective_not_0_zero",
  ``!r:'a ring z. Ring r /\ pmonic z ==> ~(introspective r z 0 |0|)``,
  rw_tac std_ss[introspective_def, poly_zero_poly, poly_peval_zero, poly_zero_exp] >>
  spose_not_then strip_assume_tac >>
  `|1| = |0|` by metis_tac[pmod_def_alt, poly_mod_one, poly_mod_zero] >>
  `z = |0|` by metis_tac[poly_one_eq_zero] >>
  metis_tac[poly_deg_pos_nonzero]);

(* Theorem: poly z ==> !n. introspective r z n X *)
(* Proof:
   By introspective_def, this is to show:
      (X ** n == peval X (X ** n)) (pm z)
   Since peval X (X ** n) = X ** n  by poly_peval_X
   Hence true                       by poly_mod_reflexive.
*)
val introspective_X = store_thm(
  "introspective_X",
  ``!r:'a ring z. Ring r /\ poly z ==> !n. introspective r z n X``,
  rw_tac std_ss[introspective_def] >>
  rw_tac std_ss[poly_peval_X, poly_mod_reflexive, poly_X, poly_exp_poly]);

(* Theorem: poly z ==>
        !n c. introspective r z n (X + |c|) <=> ((X + |c|) ** n == X ** n + |c|) (pm z) *)
(* Proof:
       introspective r z n (X + |c|)
   <=> ((X + |c|) ** n == peval (X + |c|) (X ** n)) (pm z)   by introspective_def
   <=> ((X + |c|) ** n == (X ** n) + |c|) (pm z)             by poly_peval_X_add_c
*)
val introspective_X_add_c = store_thm(
  "introspective_X_add_c",
  ``!r:'a ring z. Ring r /\ poly z ==>
   !n c:num. introspective r z n (X + |c|) <=> ((X + |c|) ** n == X ** n + |c|) (pm z)``,
  rw_tac std_ss[introspective_def] >>
  rw[poly_peval_X_add_c]);

(* Theorem: ulead z ==>
      !n c. introspective r z n (X + |c|) <=> z pdivides ((X + |c|) ** n - (X ** n + |c|)) *)
(* Proof:
       introspective r z n (X + |c|)
   <=> ((X + |c|) ** n == (X ** n) + |c|) (pm z)   by introspective_X_add_c
   <=> z pdivides (X + |c|) ** n - (X ** n + |c|)  by poly_divides_sub, ulead z
*)
val introspective_X_add_c_alt = store_thm(
  "introspective_X_add_c_alt",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   !n c:num. introspective r z n (X + |c|) <=> z pdivides ((X + |c|) ** n - (X ** n + |c|))``,
  rw_tac std_ss[introspective_X_add_c] >>
  rw[poly_divides_sub]);

(* Theorem: prime (char r) ==> !z. poly z ==> introspective r z (char r) (X + |c|) *)
(* Proof:
   Let p = char r, with prime p.
   By introspective_def, this is to show:
      ((X + |c|) ** p == peval (X + |c|) (X ** p)) (pm z)
   LHS = (X + |c|) ** p
       = X ** p + |c| ** p          by poly_freshman_thm
       = X ** p + |c|               by poly_fermat_thm
   RHS = peval (X + |c|) (X ** p)
       = X ** p + |c|               by poly_peval_X_add_c
   Hence true                       by poly_mod_reflexive
*)
val introspective_X_add_c_prime_char = store_thm(
  "introspective_X_add_c_prime_char",
  ``!r:'a ring. Ring r /\ prime (char r) ==>
   !z. poly z ==> introspective r z (char r) (X + |c|)``,
  rw_tac std_ss[introspective_def] >>
  qabbrev_tac `p = char r` >>
  `poly X /\ poly |c| /\ poly (X + |c|) /\ poly (X ** p) /\ poly (X ** p + |c|)` by rw[] >>
  `(X + |c|) ** p = X ** p + |c|` by metis_tac[poly_freshman_thm, poly_fermat_thm] >>
  `peval (X + |c|) (X ** p) = X ** p + |c|` by rw[poly_peval_X_add_c] >>
  metis_tac[poly_mod_reflexive]);

(* Theorem: FiniteField r /\ poly z ==> introspective r z (char r) (X + |c|) *)
(* Proof:
   Note Ring r               by finite_field_is_field, field_is_ring
    and prime (char r)       by finite_field_char
   The result follows        by introspective_X_add_c_prime_char
*)
val introspective_X_add_c_prime_char_1 = store_thm(
  "introspective_X_add_c_prime_char_1",
  ``!r:'a field z. FiniteField r /\ poly z ==> introspective r z (char r) (X + |c|)``,
  rpt strip_tac >>
  `Ring r /\ prime (char r)` by rw[finite_field_is_field, finite_field_char] >>
  rw[introspective_X_add_c_prime_char]);

(* Theorem: FiniteField r ==> !k. introspective r (unity k) (char r) (X + |c|) *)
(* Proof:
   Note Ring r             by finite_field_is_field, field_is_ring
    and poly (unity k)     by poly_unity_poly
   The result follows      by introspective_X_add_c_prime_char_1
*)
val introspective_unity_X_add_c_char = store_thm(
  "introspective_unity_X_add_c_char",
  ``!r:'a field. FiniteField r ==> !k. introspective r (unity k) (char r) (X + |c|)``,
  rpt strip_tac >>
  `Ring r` by rw[finite_field_is_field, field_is_ring] >>
  metis_tac[introspective_X_add_c_prime_char_1, poly_unity_poly]);

(*
To show that: (char r) divides n /\ (n intro (X + |c|)) gives (n DIV (char r) intro (X + |c|))
We need two parts.
Part 1: This holds when k divides (CARD R+), a very specific requirement.
This is introspective_unity_X_add_c_char_cofactor_0.

In general, we only know: coprime k (CARD R) /\ 1 < ordz k (CARD R).
Part 2: In this finite field, we can construct a polynomial field t
        such that k divides (CARD T+), with constant subfield st.
        Then r <- iso -> st <<= t gives a round-trip to conclude
        (n DIV (char r)) is introspective.
This is introspective_unity_X_add_c_char_cofactor.
*)

(* Theorem: FiniteField r ==> !k n c. k divides (CARD R+) /\ (char r) divides n /\
            introspective r (unity k) n (X + |c|) ==>
            introspective r (unity k) (n DIV (char r)) (X + |c|) *)
(* Proof:
   Let p = char r, q = n DIV p.
   Then prime p                  by finite_field_char
    and n = q * p                by DIVIDES_EQN, 0 < p

   Let u = (X + |c|) ** q, v = X ** q + |c|.
       u ** p
     = ((X + |c|) ** q) ** p     by notation
     = (X + |c|) ** n            by poly_exp_mult

       v ** p
     = (X ** q + |c|) ** p       by notation
     = X ** q ** p + |c| ** p    by poly_freshman_thm, prime p
     = X ** n + |c| ** p         by poly_exp_mult
     = X ** n + |c|              by poly_fermat_thm, prime p

   Let z = unity k.
   Note 0 < CARD R+              by field_nonzero_card_pos
     so 0 < k                    by ZERO_DIVIDES, k divides (CARD R+)
    ==> ulead z                  by poly_unity_ulead, 0 < k
   Note introspective r z n (X + |c|)       by given
     so (u ** p == v ** p) (pm z)           by introspective_X_add_c

   With k divides (CARD R+)                 by given
   Thus (u == v) (pm z)                     by poly_unity_mod_exp_char_eq
     or introspective r z q (X + |c|)       by poly_intro_X_add_c
*)
val introspective_unity_X_add_c_char_cofactor_0 = store_thm(
  "introspective_unity_X_add_c_char_cofactor_0",
  ``!r:'a field. FiniteField r ==> !k n c:num. k divides (CARD R+) /\ (char r) divides n /\
         introspective r (unity k) n (X + |c|) ==>
         introspective r (unity k) (n DIV (char r)) (X + |c|)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `q = n DIV p` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `0 < p` by rw[PRIME_POS] >>
  `n = q * p` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `0 < k` by metis_tac[ZERO_DIVIDES, field_nonzero_card_pos, NOT_ZERO] >>
  qabbrev_tac `z = unity k` >>
  `ulead z` by rw[poly_unity_ulead, Abbr`z`] >>
  qabbrev_tac `u = (X + |c|) ** q` >>
  qabbrev_tac `v = X ** q + |c|` >>
  `poly u /\ poly v` by rw[Abbr`u`, Abbr`v`] >>
  `(u ** p == v ** p) (pm z)` by
  (`poly X /\ poly (X ** q) /\ poly |c|` by rw[] >>
  `u ** p = (X + |c|) ** n` by rw[poly_exp_mult, Abbr`u`] >>
  `v ** p = (X ** q) ** p + |c| ** p` by rw_tac std_ss[poly_freshman_thm, Abbr`v`, Abbr`p`] >>
  `_ = X ** n + |c| ** p ` by rw_tac std_ss[poly_exp_mult] >>
  `_ = X ** n + |c|` by rw_tac std_ss[poly_fermat_thm, Abbr`p`] >>
  metis_tac[introspective_X_add_c]) >>
  `(u == v) (pm z)` by rw[poly_unity_mod_exp_char_eq, Abbr`p`, Abbr`z`] >>
  rw[introspective_X_add_c]);

(* Theorem: (r === r_) f ==> !p. ulead p ==>
      !n c. introspective r p n (X + |c|) <=> introspective r_ p_ n (X_ +_ |c|_) *)
(* Proof:
   Note MAP f X = X_                      by field_iso_poly_X
    and MAP f |c| = |c|_                  by field_iso_poly_sum_num
   also ulead_ p_                         by field_iso_poly_ulead

   Claim: MAP f ((X + |c|) ** n - (X ** n + |c|)) = (X_ +_ |c|_) **_ n -_ (X_ **_ n +_ |c|_)
   Proof: MAP f (X + |c|) = X_ +_ |c|_                  by field_iso_poly_add
       so MAP f ((X + |c|) ** n) = (X_ +_ |c|_) **_ n   by field_iso_poly_exp
     Also MAP (X ** n) = X_ **_ n                       by field_iso_poly_exp
       so MAP f (X ** n + |c|) = X_ **_ n +_ |c|_       by field_iso_poly_add
      The result follows                                by field_iso_poly_sub

   Expand by introspective_X_add_c_alt,
   The result follows                     by field_iso_poly_divides_iff
*)
val field_iso_introspective = store_thm(
  "field_iso_introspective",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. ulead p ==>
   !n c:num. introspective r p n (X + |c|) <=> introspective r_ p_ n (X_ +_ |c|_)``,
  rw_tac std_ss[introspective_X_add_c_alt] >>
  rpt strip_tac >>
  `Ring r /\ Ring r_` by rw[] >>
  `MAP f X = X_` by rw[field_iso_poly_X] >>
  `MAP f |c| = |c|_` by rw[field_iso_poly_sum_num] >>
  `MAP f ((X + |c|) ** n - (X ** n + |c|)) = (X_ +_ |c|_) **_ n -_ (X_ **_ n +_ |c|_)` by
  (`poly X /\ poly |c| /\ poly ((X + |c|) ** n) /\ poly (X ** n + |c|)` by rw[] >>
  `MAP f ((X + |c|) ** n) = (X_ +_ |c|_) **_ n` by prove_tac[field_iso_poly_add, field_iso_poly_exp, poly_add_poly] >>
  `MAP f (X ** n + |c|) = X_ **_ n +_ |c|_` by prove_tac[field_iso_poly_add, field_iso_poly_exp, poly_add_poly, poly_exp_poly] >>
  metis_tac[field_iso_poly_sub]) >>
  `ulead_ p_` by metis_tac[field_iso_poly_ulead] >>
  qabbrev_tac `q = (X + |c|) ** n - (X ** n + |c|)` >>
  `poly q` by rw[Abbr`q`] >>
  metis_tac[introspective_X_add_c_alt, field_iso_poly_divides_iff]);

(* Theorem: s <= r ==> !z. Pmonic s z ==>
      !n c. introspective r z n (X + |c|) <=>
            introspective s z n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) *)
(* Proof:
   Note s <= r                                by subfield_is_subring
    and #1 <> #0 /\ s.prod.id <> s.sum.id     by field_one_ne_zero
    Now poly_shift s (poly_one s) 1 = X       by subring_poly_X
    and poly_num s c = |c|                    by subring_poly_sum_num
   also ulead z                               by subring_poly_ulead

   Claim: poly_sub s (poly_exp s (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) n)
                     (poly_add s (poly_exp s (poly_shift s (poly_one s) 1) n)
                                 (poly_num s c)) = (X + |c|) ** n - (X ** n + |c|)
   Proof: poly_add s X |c| = X + |c|                         by subring_poly_add
       so poly_exp s (poly_add s X |c|) n = (X + |c|) ** n   by subring_poly_exp
     Also poly_exp s X n = X ** n                            by subring_poly_exp
       so poly_add s (poly_exp s X n) |c| = X ** n + |c|     by subring_poly_add
      The result follows                                     by subring_poly_sub

   Expand by introspective_X_add_c_alt,
   The result follows                         by subring_poly_divides_iff, ulead z
*)
val subring_introspective = store_thm(
  "subring_introspective",
  ``!(r s):'a ring. s <= r ==> !z. Ulead s z ==>
   !n c:num. introspective r z n (X + |c|) <=>
             introspective s z n (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c))``,
  rpt strip_tac >>
  `poly_shift s (poly_one s) 1 = X` by rw[subring_poly_X] >>
  `poly_num s c = |c|` by rw[subring_poly_sum_num] >>
  `ulead z` by metis_tac[subring_poly_ulead] >>
  rw_tac std_ss[introspective_X_add_c_alt] >>
  `poly_sub s (poly_exp s (poly_add s (poly_shift s (poly_one s) 1) (poly_num s c)) n)
                  (poly_add s (poly_exp s (poly_shift s (poly_one s) 1) n)
                              (poly_num s c)) = (X + |c|) ** n - (X ** n + |c|)` by
  (`!r:'a ring. Ring r ==> poly X /\ poly |c|` by rw[] >>
  `!r:'a ring. Ring r ==> poly ((X + |c|) ** n) /\ poly (X ** n + |c|)` by rw[] >>
  `poly_exp s (poly_add s X |c|) n = (X + |c|) ** n` by metis_tac[subring_poly_add, subring_poly_exp, poly_add_poly] >>
  `poly_add s (poly_exp s X n) |c| = X ** n + |c|` by metis_tac[subring_poly_add, subring_poly_exp, poly_add_poly, poly_exp_poly] >>
  metis_tac[subring_poly_sub]) >>
  `!r:'a ring. Ring r ==> poly ((X + |c|) ** n - (X ** n + |c|))` by rw[] >>
  metis_tac[subring_poly_divides_iff]);

(* Theorem: FiniteField r ==> !k n c:num. coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
            char r divides n /\ introspective r (unity k) n (X + |c|) ==>
            introspective r (unity k) (n DIV char r) (X + |c|) *)
(* Proof:
   Let d = ordz k (CARD R), then 0 < d          by given, 1 < d
   Note 1 < CARD R                              by finite_field_card_gt_1
     so 1 < k, then 0 < k                       by ZN_order_with_coprime_1

   Step 1: get a field/subfield pair
   Note FiniteField r /\ 0 < d
    ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists
    and pmonic z                                by poly_monic_irreducible_property

   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                           by poly_mod_irreducible_finite_field
     so Field t                                 by finite_field_is_field
    and Field st                                by poly_mod_const_field
   Also st <<= t                                by poly_mod_const_subfield_poly_mod
    and st <= t                                 by subfield_is_subring
    and (t <:> st) = deg z                      by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier                by poly_mod_const_subfield_card
    ==> k divides CARD (ring_nonzero t)         by subfield_card_coprime_iff

   The situation: Let u = unity k.
                                   t = PolyModRing r z, with k divides CARD (ring_nonzero t)
                                   |     introspective t u_ n Xc_t ==> introspective t u_ q Xc_t
                                   |                          /\            ||
                                   |                          ||            ||
       r <-- FieldIso, f = up --> st = PolyModConst r z       ||            ||
       introspective r u n (X + |c|) ==> introspective st u_ n Xc_st        \/
       introspective r u q (X + |c|) ------------------------------<== introspective st u_ q Xc_st

   Step 2: apply poly_intro_X_add_c_prime_char_2
   Let q = n DIV (char r).
   Note char t = char r                         by poly_mod_ring_char, pmonic z
    and FieldIso up r st                        by poly_mod_const_iso_field

    Let Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)
    and Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)
    Let u_ = MAP up u.
    Then u_ = Unity st k                        by field_iso_poly_unity
            = Unity t k                         by subring_poly_unity
     and Xc_st = MAP up (X + |c|)               by field_iso_poly_X_add_c
     and Ulead st u_ /\ ulead (unity k)         by poly_unity_ulead

        introspective r u n (X + |c|)           by given
    ==> introspective st u_ n Xc_st             by field_iso_introspective, FieldIso up r st
    ==> introspective t u_ n Xc_t               by subring_introspective, st <= t
    ==> introspective t u_ q Xc_t               by introspective_unity_X_add_c_char_cofactor_0
    ==> introspective st u_ q Xc_st             by subring_introspective, st <= t
    ==> introspective r q (X + |c|)             by field_iso_introspective, FieldIso up r st
*)
val introspective_unity_X_add_c_char_cofactor = store_thm(
  "introspective_unity_X_add_c_char_cofactor",
  ``!r:'a field. FiniteField r ==> !k n c:num. coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
                char r divides n /\ introspective r (unity k) n (X + |c|) ==>
                introspective r (unity k) (n DIV char r) (X + |c|)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz k (CARD R)` >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `0 < k /\ 0 < d /\ d <> 1` by decide_tac >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `t = PolyModRing r z` >>
  qabbrev_tac `st = PolyModConst r z` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `Field t` by rw[finite_field_is_field] >>
  `Field st` by rw[poly_mod_const_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod, Abbr`t`, Abbr`st`] >>
  `st <= t` by rw[subfield_is_subring] >>
  `(t <:> st) = deg z` by rw[poly_mod_const_subfield_dim, Abbr`t`, Abbr`st`] >>
  `CARD R = CARD st.carrier` by rw[poly_mod_const_subfield_card, Abbr`st`] >>
  `k divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  qabbrev_tac `q = n DIV (char r)` >>
  `char t = char r` by rw[poly_mod_ring_char, Abbr`t`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  qabbrev_tac `Xc_st = poly_add st (poly_shift st (poly_one st) 1) (poly_num st c)` >>
  qabbrev_tac `Xc_t = poly_add t (poly_shift t (poly_one t) 1) (poly_num t c)` >>
  `MAP up (X + |c|) = Xc_st` by rw[field_iso_poly_X_add_c, Abbr`Xc_st`] >>
  qabbrev_tac `u_ = MAP up (unity k)` >>
  `u_ = Unity st k` by rw[field_iso_poly_unity, Abbr`u_`] >>
  `Unity st k = Unity t k` by rw[subring_poly_unity] >>
  `Ulead st u_ /\ ulead (unity k)` by rw[poly_unity_ulead] >>
  `introspective st u_ n Xc_st` by metis_tac[field_iso_introspective] >>
  `introspective t u_ n Xc_t` by metis_tac[subring_introspective] >>
  `introspective t u_ q Xc_t` by metis_tac[introspective_unity_X_add_c_char_cofactor_0] >>
  `introspective st u_ q Xc_st` by metis_tac[subring_introspective] >>
  metis_tac[field_iso_introspective]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
