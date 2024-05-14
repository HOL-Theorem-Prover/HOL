(* ------------------------------------------------------------------------- *)
(* Finite Field: Polynomials of Subfield                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffPoly";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory numberTheory dividesTheory
     gcdTheory combinatoricsTheory;

open ffAdvancedTheory ffBasicTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open fieldOrderTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;

open polyMonicTheory polyEvalTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;

open polyRootTheory;
open polyDividesTheory;

open polyGCDTheory;
open polyIrreducibleTheory;
open polyProductTheory;
open polyMultiplicityTheory;
open polyMapTheory;
open fieldMapTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Field Polynomials of Subfield Documentation                        *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   cpoly r s p  = common_poly r s p

   pfpoly       = Poly (PF r)
   pfzerop      = zero_poly (PF r)
   pfchop       = poly_chop (PF r)
   pfcmult      = poly_cmult (PF r)
   pfshift      = poly_shift (PF r)
   pfcoeff      = poly_coeff (PF r)
   pfdeg        = poly_deg (PF r)
   pflead       = poly_lead (PF r)
   pfadd        = (PolyRing (PF r)).sum.op
   pfmult       = (PolyRing (PF r)).prod.op
   pfneg        = (PolyRing (PF r)).sum.inv
   pfexp        = (PolyRing (PF r)).prod.exp
   pfcpoly      = pf_common_poly r

*)
(* Definitions and Theorems (# are exported):

   Subring Polynomials:
   subring_poly_property   |- !r s. s <= r ==> (!p. Poly s p <=> p IN (PolyRing s).carrier) /\
                                               (poly_zero s = |0|) /\ (poly_one s = |1|)
   subring_poly_element    |- !s p. Poly s p <=> p IN (PolyRing s).carrier
   subring_poly_ids        |- !r s. s <= r ==> (poly_zero s = |0|) /\ (poly_one s = |1|)
   subring_poly_zero       |- !r s. s <= r ==> (poly_zero s = |0|)
   subring_poly_one        |- !r s. s <= r ==> (poly_one s = |1|)
   subring_poly_zero_poly  |- !r s. s <= r ==> !p. zero_poly s p <=> zerop p
   subring_poly_poly       |- !r s. s <= r ==> !p. Poly s p ==> poly p
   subring_poly_carrier_subset  |- !r s. s <= r ==> (PolyRing s).carrier SUBSET (PolyRing r).carrier
   subring_poly_deg        |- !r s p. poly_deg s p = deg p
   subring_poly_lead       |- !r s. s <= r ==> !p. poly_lead s p = lead p
   subring_poly_coeff      |- !r s. s <= r ==> !p k. poly_coeff s p k = p ' k
   subring_poly_chop       |- !r s. s <= r ==> !p. poly_chop s p = chop p
   subring_poly_weak_add   |- !r s. s <= r ==> !p q. Weak s p /\ Weak s q ==> (weak_add s p q = p || q)
   subring_poly_weak_cmult |- !r s. s <= r ==> !p. Weak s p ==> !c. c IN B ==> (weak_cmult s c p = c o p)
   subring_poly_shift_1    |- !r s. s <= r ==> !p. poly_shift s p 1 = p >> 1
   subring_poly_shift      |- !r s. s <= r ==> !p n. poly_shift s p n = p >> n
   subring_poly_X          |- !r s. s <= r ==> (poly_shift s (poly_one s) 1 = X)
   subring_poly_weak_mult  |- !r s. s <= r ==> !p q. Weak s p /\ Weak s q ==> (weak_mult s p q = p o q)
   subring_poly_cmult      |- !r s. s <= r ==> !p. Poly s p ==> !c. c IN B ==> (poly_cmult s c p = c * p)
   subring_poly_add        |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_add s p q = p + q)
   subring_poly_mult       |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_mult s p q = p * q)
   subring_poly_subring    |- !r s. s <= r ==> PolyRing s <= PolyRing r
   subring_poly_neg        |- !r s. s <= r ==> !p. Poly s p ==> (poly_neg s p = -p)
   subring_poly_sub        |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_sub s p q = p - q)
   subring_poly_exp        |- !r s. s <= r ==> !p. Poly s p ==> !n. poly_exp s p n = p ** n
   subring_poly_sum_num    |- !r s. s <= r ==> !c. poly_num s c = |c|
   subring_poly_master     |- !r s. s <= r ==> !n. Master s n = master n
   subring_poly_unity      |- !r s. s <= r ==> !n. Unity s n = unity n
   subring_poly_monic      |- !r s. s <= r ==> !p. Monic s p ==> monic p
   subring_poly_monic_iff  |- !r s. s <= r ==> !p. Poly s p ==> (Monic s p <=> monic p)
   subring_poly_ulead      |- !r s. s <= r ==> !p. Ulead s p ==> ulead p
   subring_poly_pmonic     |- !r s. s <= r ==> !p. Pmonic s p ==> pmonic p
   subring_poly_division_all_eqn
                           |- !r s. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
                              ?u v. Poly s u /\ Poly s v /\ p = u * q + v /\
                                    if 0 < deg q then deg v < deg q else v = |0|
   subring_poly_division_eqn
                           |- !r s. s <= r ==> !p q. Poly s p /\ Pmonic s q ==>
                              ?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\ deg v < deg q
   subring_poly_div_mod     |- !r s. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
                                                (poly_div s p q = p / q) /\ (poly_mod s p q = p % q)
   subring_poly_div         |- !r s. s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_div s p q = p / q)
   subring_poly_mod         |- !r s. s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_mod s p q = p % q)
   subring_poly_divides     |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q /\ poly_divides s p q ==> p pdivides q
   subring_poly_divides_iff |- !r s. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
                                                (poly_divides s q p <=> q pdivides p)
   subring_poly_prod_set    |- !r s. s <= r ==> !t. FINITE t /\ poly_set s t ==> (poly_prod_set s t = PPROD t)
   subring_poly_prod_set_spoly  |- !r s. s <= r ==> !t f. FINITE t /\ t SUBSET R /\
                                                        (!x. x IN t ==> Poly s (f x)) ==> Poly s (PPIMAGE f t)
   subring_poly_factor      |- !r s. s <= r ==> !c. c IN B ==> (poly_factor s c = factor c)
   subring_poly_root        |- !r s. s <= r ==> !p x. Poly s p /\ x IN B /\ poly_root s p x ==> root p x
   subring_poly_roots       |- !r s. s <= r ==> !p. Poly s p ==> poly_roots s p SUBSET roots p

   Subring Polynomial (another view):
   poly_zero_spoly      |- !r s. s <= r ==> Poly s |0|
   poly_one_spoly       |- !r s. s <= r ==> Poly s |1|
   poly_X_spoly         |- !r s. s <= r ==> Poly s X
   poly_neg_spoly       |- !r s. s <= r ==> !p. Poly s p ==> Poly s (-p)
   poly_cmult_spoly     |- !r s. s <= r ==> !p c. Poly s p /\ c IN B ==> Poly s (c * p)
   poly_add_spoly       |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p + q)
   poly_sub_spoly       |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p - q)
   poly_mult_spoly      |- !r s. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p * q)
   poly_shift_spoly     |- !r s. s <= r ==> !p n. Poly s p ==> Poly s (p >> n)
   poly_exp_spoly       |- !r s. s <= r ==> !p n. Poly s p ==> Poly s (p ** n)
   poly_X_exp_n_spoly   |- !r s. s <= r ==> !n. Poly s (X ** n)
   poly_master_spoly    |- !r s. s <= r ==> !n. Poly s (master n)
   poly_unity_spoly     |- !r s. s <= r ==> !n. Poly s (unity n)
   poly_factor_spoly    |- !r s. s <= r /\ #1 <> #0 ==> !c. c IN B ==> Poly s (factor c)

   More Subring Theorems:
   subring_poly_root_multiplicity |- !r s. s <= r /\ #1 <> #0 ==> !p x. Poly s p /\ x IN B ==>
                                           (poly_root_multiplicity s p x = multiplicity p x)
   subring_poly_separable_reverse |- !r s. s <= r /\ #1 <> #0 ==>
                                     !p. Poly s p /\ separable p ==> poly_separable s p

   Common Polynomial:
   common_poly_def           |- !r s p. cpoly r s p <=> poly p /\ EVERY (\e. e IN B) p
   common_poly_poly          |- !p. cpoly r s p ==> poly p
   common_poly_alt           |- !r s. s <= r ==> !p. poly p ==> (cpoly r s p <=> !k. p ' k IN B)
   common_poly_subring_poly  |- !r s. s <= r ==> !p. cpoly r s p ==> Poly s p
   subring_poly_alt          |- !r s. s <= r ==> !p. Poly s p <=> cpoly r s p

   Polynomials of Prime Field:
   poly_prime_field_ring           |- !r. FiniteField r ==> Ring (PolyRing (PF r))
   poly_prime_field_is_subring     |- !r. FiniteField r ==> PolyRing (PF r) <= PolyRing r
   poly_prime_field_element        |- !p. pfpoly p <=> p IN (PolyRing (PF r)).carrier
   poly_prime_field_ids            |- !r. ((PolyRing (PF r)).sum.id = |0|) /\
                                          ((PolyRing (PF r)).prod.id = |1|)
   poly_prime_field_property       |- !r. (!p. pfpoly p <=> p IN (PolyRing (PF r)).carrier) /\
                                          ((PolyRing (PF r)).sum.id = |0|) /\
                                          ((PolyRing (PF r)).prod.id = |1|)
   poly_prime_field_zero_poly      |- !p. pfzerop p <=> zerop p
   poly_prime_field_element_poly   |- !r. Ring r ==> !p. pfpoly p ==> poly p
   poly_prime_field_carrier_subset |- !r. Ring r ==> (PolyRing (PF r)).carrier SUBSET (PolyRing r).carrier
   poly_prime_field_carriers       |- !r. FiniteField r ==>
                                          ((PolyRing (PF r)).sum.carrier = (PolyRing (PF r)).carrier) /\
                                          ((PolyRing (PF r)).prod.carrier = (PolyRing (PF r)).carrier)
   poly_prime_field_deg            |- !p. pfdeg p = deg p
   poly_prime_field_lead           |- !p. pflead p = lead p
   poly_prime_field_coeff          |- !p k. pfcoeff p k = p ' k
   poly_prime_field_chop           |- !p. pfchop p = chop p
   poly_prime_field_weak_add       |- !p q. weak_add (PF r) p q = p || q
   poly_prime_field_weak_cmult     |- !c p. weak_cmult (PF r) c p = c o p
   poly_prime_field_shift_1        |- !p. pfshift p 1 = p >> 1
   poly_prime_field_shift          |- !p n. pfshift p n = p >> n
   poly_prime_field_weak_mult      |- !p q. weak_mult (PF r) p q = p o q
   poly_prime_field_cmult          |- !c p. pfcmult c p = c * p
   poly_prime_field_add            |- !p q. pfadd p q = p + q
   poly_prime_field_mult           |- !p q. pfmult p q = p * q
   poly_prime_field_subring        |- !r. Ring r ==> subring (PolyRing (PF r)) (PolyRing r)

   Prime Field Common Polynomial:
   pf_common_poly_def         |- !r p. pfcpoly p <=> poly p /\ EVERY (\e. e IN Fp) p
   pf_common_poly_poly        |- !p. pfcpoly p ==> poly p
   pf_common_poly_pfpoly      |- !p. pfcpoly p ==> pfpoly p
   poly_prime_field_poly_alt  |- !r. Ring r ==> !p. pfpoly p <=> pfcpoly p

   poly_prime_field_neg    |- !r. FiniteField r ==> !p. pfpoly p ==> (pfneg p = -p)
   poly_prime_field_exp    |- !p n. pfexp p n = p ** n

   Freshman Theorems for Finite Field:
   poly_field_freshman_thm     |- !r. FiniteField r ==> !x y. poly x /\ poly y ==>
                                      ((x + y) ** char r = x ** char r + y ** char r)
   poly_field_freshman_thm_sub |- !r. FiniteField r ==> !x y. poly x /\ poly y ==>
                                      ((x - y) ** char r = x ** char r - y ** char r)
   poly_field_freshman_all     |- !r. FiniteField r ==> !x y. poly x /\ poly y ==>
                                  !n. (x + y) ** char r ** n = x ** char r ** n + y ** char r ** n
   poly_freshman_card          |- !r. FiniteField r ==> !x y. poly x /\ poly y ==>
                                      ((x + y) ** CARD R = x ** CARD R + y ** CARD R)
   poly_freshman_card_all      |- !r. FiniteField r ==> !x y. poly x /\ poly y ==>
                                  !n. (x + y) ** CARD R ** n = x ** CARD R ** n + y ** CARD R ** n
   poly_sum_freshman_card      |- !r. FiniteField r ==> !f. rfun f ==> !p. poly p ==>
                                  !n. poly_sum (GENLIST (\j. f j * p ** j) n) ** CARD R =
                                      poly_sum (GENLIST (\j. (f j * p ** j) ** CARD R) n)
   poly_sum_freshman_card_all  |- !r. FiniteField r ==> !f. rfun f ==> !p. poly p ==>
                                  !n k. poly_sum (GENLIST (\j. f j * p ** j) n) ** CARD R ** k =
                                        poly_sum (GENLIST (\j. (f j * p ** j) ** CARD R ** k) n)
   poly_peval_freshman_card      |- !r. FiniteField r ==> !p q. poly p /\ poly q ==>
                                        (peval p q ** CARD R = peval p (q ** CARD R))
   poly_peval_freshman_card_all  |- !r. FiniteField r ==> !p q. poly p /\ poly q ==>
                                    !n. peval p q ** CARD R ** n = peval p (q ** CARD R ** n)
   poly_peval_fermat_thm       |- !r. FiniteField r ==> !p. poly p ==>
                                      (p ** CARD R = peval p (X ** CARD R))
   poly_peval_fermat_all       |- !r. FiniteField r ==> !p. poly p ==>
                                  !n. p ** CARD R ** n = peval p (X ** CARD R ** n)
   ring_sum_freshman_card      |- !r. FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n. rsum (GENLIST (\j. f j * x ** j) n) ** CARD R =
                                      rsum (GENLIST (\j. (f j * x ** j) ** CARD R) n)
   ring_sum_freshman_card_all  |- !r. FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n k. rsum (GENLIST (\j. f j * x ** j) n) ** CARD R ** k =
                                        rsum (GENLIST (\j. (f j * x ** j) ** CARD R ** k) n)
   poly_eval_freshman_card     |- !r. FiniteField r ==> !p x. poly p /\ x IN R ==>
                                      (eval p x ** CARD R = eval p (x ** CARD R))
   poly_eval_freshman_card_all |- !r. FiniteField r ==> !p x. poly p /\ x IN R ==>
                                  !n. eval p x ** CARD R ** n = eval p (x ** CARD R ** n)

   Finite Field Polynomial Theorems:
   poly_char_exp_eq        |- !r. FiniteField r ==>
                              !p q. poly p /\ poly q /\ (p ** char r = q ** char r) ==> (p = q)
   poly_sum_fermat_thm     |- !r. FiniteField r ==> !p. poly p ==>
           (p ** CARD R = poly_sum (GENLIST (\k. p ' k ** CARD R * (X ** CARD R) ** k) (SUC (deg p))))
   poly_root_exp           |- !r. FiniteField r ==> !p z. poly p /\ z IN R /\
                                  root p z ==> !n. root p (z ** CARD R ** n)
   prime_field_fermat_thm  |- !r. FiniteField r ==> !x. x IN Fp ==> (x ** char r = x)
   prime_field_fermat_all  |- !r. FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x
   poly_eval_freshman_thm  |- !r. FiniteField r ==> !p x. pfpoly p /\ x IN R ==>
                                  (eval p x ** char r = eval p (x ** char r))
   poly_eval_freshman_all  |- !r. FiniteField r ==> !p x. pfpoly p /\ x IN R ==>
                              !n. eval p x ** char r ** n = eval p (x ** char r ** n)
   poly_peval_freshman_thm |- !r. FiniteField r ==> !p q. pfpoly p /\ poly q ==>
                                  (peval p q ** char r = peval p (q ** char r))
   poly_peval_freshman_all |- !r. FiniteField r ==> !p q. pfpoly p /\ poly q ==>
                              !n. peval p q ** char r ** n = peval p (q ** char r ** n)

   Roots of Prime Field Polynomials:
   poly_prime_field_roots  |- !r. FiniteField r ==>
                              !p z. pfpoly p /\ z IN R /\ root p z ==> !n. root p (z ** char r ** n)

   Roots of Subfield Polynomials:
   subfield_fermat_thm   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN B ==> (x ** CARD B = x)
   subfield_fermat_all   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN B ==> !n. x ** CARD B ** n = x
   subfield_poly_eval_freshman_thm  |- !r s. FiniteField r /\ s <<= r ==> !p. Poly s p ==>
                                       !x. x IN R ==> (eval p x ** CARD B = eval p (x ** CARD B))
   subfield_poly_eval_freshman_all  |- !r s. FiniteField r /\ s <<= r ==> !p. Poly s p ==>
                           !x. x IN R ==> !n. eval p x ** CARD B ** n = eval p (x ** CARD B ** n)
   subfield_poly_peval_freshman_thm  |- !r s. FiniteField r /\ s <<= r ==>
                       !p q. Poly s p /\ poly q ==> (peval p q ** CARD B = peval p (q ** CARD B))
   subfield_poly_peval_freshman_all  |- !r s. FiniteField r /\ s <<= r ==>
           !p q. Poly s p /\ poly q ==> !n. peval p q ** CARD B ** n = peval p (q ** CARD B ** n)

*)

(* ------------------------------------------------------------------------- *)
(* Subring Polynomials                                                       *)
(* ------------------------------------------------------------------------- *)

(* Overloads for subfield elements -- avoid too much confusion. *)
(*
val _ = overload_on("spoly", ``Poly s``);
val _ = overload_on("szerop", ``zero_poly s``);
val _ = overload_on("schop", ``poly_chop s``);
val _ = overload_on("scmult", ``poly_cmult s``);
val _ = overload_on("sshift", ``poly_shift s``);
val _ = overload_on("scoeff", ``poly_coeff s``);
val _ = overload_on("sdeg", ``poly_deg s``);
val _ = overload_on("slead", ``poly_lead s``);
*)

(* Theorem: Properties of polynomials in subring. *)
(* Proof:
   By subring_def, this is to show:
   (1) Poly s p <=> p IN (PolyRing s).carrier
       True by poly_ring_property.
   (2) RingHomo I s r ==> poly_zero s = |0|
         poly_zero s
       = (PolyRing s).sum.id        by notation
       = []                         by poly_ring_property
       = |0|                        by poly_ring_ids
   (3) RingHomo I s r ==> poly_one s = |1|
         poly_one s
       = (PolyRing s).prod.id       by notation
       = poly_chop s [s.prod.id]    by poly_ring_property
       = poly_chop s [#1]           by ring_homo_one
       = chop [#1]                  by poly_chop_def
       = |1|                        by poly_ring_ids
*)
val subring_poly_property = store_thm(
  "subring_poly_property",
  ``!(r s):'a ring. s <= r ==>
        (!p. Poly s p <=> p IN (PolyRing s).carrier) /\
        (poly_zero s = |0|) /\ (poly_one s = |1|)``,
  rw[subring_def] >-
  metis_tac[poly_ring_property] >>
  `s.sum.id = #0` by metis_tac[ring_homo_zero, combinTheory.I_THM] >>
  `s.prod.id = #1` by metis_tac[ring_homo_one, combinTheory.I_THM] >>
  rw[poly_ring_ids]);

(* Theorem: Poly s p <=> p IN (PolyRing s).carrier *)
(* Proof: by poly_ring_property *)
val subring_poly_element = store_thm(
  "subring_poly_element",
  ``!s p. Poly s p <=> p IN (PolyRing s).carrier``,
  rw[poly_ring_property]);

(* Theorem: s <= r ==> (poly_zero s = |0|) /\ (poly_one s = |1|) *)
(* Proof: by subring_poly_property *)
val subring_poly_ids = store_thm(
  "subring_poly_ids",
  ``!(r s):'a ring. s <= r ==> (poly_zero s = |0|) /\ (poly_one s = |1|)``,
  rw[subring_poly_property]);

(* Theorem: s <= r ==> (poly_zero s = |0|) *)
(* Proof: by subring_poly_ids *)
val subring_poly_zero = store_thm(
  "subring_poly_zero",
  ``!(r s):'a ring. s <= r ==> (poly_zero s = |0|)``,
  rw[subring_poly_ids]);

(* Theorem: s <= r ==> (poly_one s = |1|) *)
(* Proof: by subring_poly_ids *)
val subring_poly_one = store_thm(
  "subring_poly_one",
  ``!(r s):'a ring. s <= r ==> (poly_one s = |1|)``,
  rw[subring_poly_ids]);

(* Theorem: s <= r ==> !p. zero_poly s p <=> zerop p *)
(* Proof:
   By induction on p.
   Base case: zero_poly s [] <=> zerop []
      True by zero_poly_def
   Step case: zero_poly s p <=> zerop p ==>
              !h. zero_poly s (h::p) <=> zerop (h::p)
      True by zero_poly_cons, subring_ids.
*)
val subring_poly_zero_poly = store_thm(
  "subring_poly_zero_poly",
  ``!(r s):'a ring. s <= r ==> !p. zero_poly s p <=> zerop p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[zero_poly_cons] >>
  metis_tac[subring_ids]);

(* Theorem: s <= r ==> !p. Poly s p ==> poly p *)
(* Proof:
   By induction on p.
   Base case: Poly s [] ==> poly []
      True by zero_poly_poly.
   Step case: Poly s p ==> poly p ==> !h. Poly s (h::p) ==> poly (h::p)
      By Poly_def, zero_poly_def, this is to show:
      (1) h IN B ==> h IN R, true                      by subring_element
      (2) h <> s.sum.id ==> h <> #0 \/ ~zerop p, true  by subring_ids
      (3) ~zero_poly s p ==> h <> #0 \/ ~zerop p, true by subring_poly_zero_poly
*)
Theorem subring_poly_poly:
  !(r s):'a ring. s <= r ==> !p. Poly s p ==> poly p
Proof
  rpt strip_tac >>
  Induct_on `p` >- rw[] >>
  rw[] >- metis_tac[subring_element] >>
  metis_tac[subring_ids, subring_element, subring_poly_zero_poly]
QED

(* Theorem: s <= r ==> (PolyRing s).carrier SUBSET (PolyRing r).carrier *)
(* Proof:
   Since Poly s p <=> p IN (PolyRing s).carrier   by poly_ring_property
           poly p <=> p IN (PolyRing r).carrier   by poly_ring_property
     and Poly s p ==> poly p                      by subring_poly_poly
   Hence true                                     by SUBSET_DEF
*)
val subring_poly_carrier_subset = store_thm(
  "subring_poly_carrier_subset",
  ``!(r s):'a ring. s <= r ==> (PolyRing s).carrier SUBSET (PolyRing r).carrier``,
  metis_tac[poly_ring_property, SUBSET_DEF, subring_poly_poly]);

(* Theorem: poly_deg s p = deg p *)
(* Proof: by poly_deg_def *)
val subring_poly_deg = store_thm(
  "subring_poly_deg",
  ``!(r s):'a ring. !p. poly_deg s p = deg p``,
  rw[poly_deg_def]);

(* Theorem: s <= r ==> !p. poly_lead s p = lead p *)
(* Proof: by poly_lead_def, subring_ids *)
val subring_poly_lead = store_thm(
  "subring_poly_lead",
  ``!(r s):'a ring. s <= r ==> !p. poly_lead s p = lead p``,
  metis_tac[poly_lead_def, list_CASES, subring_ids]);

(* Theorem: s <= r ==> !p k. poly_coeff s p k = p ' k *)
(* Proof: by poly_coeff_def, subring_ids *)
val subring_poly_coeff = store_thm(
  "subring_poly_coeff",
  ``!(r s):'a ring. s <= r ==> !p k. poly_coeff s p k = p ' k``,
  rpt strip_tac >>
  Cases_on `p` >>
  rw[poly_coeff_def, subring_ids]);

(* Theorem: s <= r ==> !p. poly_chop s p = chop p *)
(* Proof:
   By induction on p.
   Base case: poly_chop s [] = chop []
      True by poly_chop_of_zero
   Step case: poly_chop s p = chop p ==> !h. poly_chop s (h::p) = chop (h::p)
      True by poly_chop_cons, subring_poly_zero_poly
*)
val subring_poly_chop = store_thm(
  "subring_poly_chop",
  ``!(r s):'a ring. s <= r ==> !p. poly_chop s p = chop p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  metis_tac[poly_chop_cons, subring_poly_zero_poly]);

(* Theorem: s <= r ==> !p q. weak_add s p q = p || q *)
(* Proof:
   By induction on p.
   Base case: Weak s [] /\ Weak s q ==> (weak_add s [] q = [] || q)
        weak_add s [] q
      = q                         by weak_add_def
      = [] || q                   by weak_add_def
   Step case: !q. weak_add s p q = p || q ==>
              !h q. weak_add s (h::p) q = (h::p) || q
      By induction on q.
      Base case: !h. Weak s (h::p) /\ Weak s [] ==> (weak_add s (h::p) [] = (h::p) || [])
           weak_add s (h::p) []
         = (h::p)                 by weak_add_def
         = (h::p) || []           by weak_add_def
      Step case: !q. Weak s p /\ Weak s q ==> (weak_add s p q = p || q) ==>
                 !h h'. Weak s (h'::p) /\ Weak s (h::q) ==> (weak_add s (h'::p) (h::q) = (h'::p) || (h::q))
           Note Weak s (h'::p) ==> h' IN B /\ Weak s p    by weak_cons
                Weak s (h::q)  ==> h IN B /\ Weak s q     by weak_cons
           weak_add s (h::p) (h'::q)
         = s.sum.op h h' :: weak_add s p q    by weak_add_def
         = h + h' :: weak_add s p q           by subring_property
         = h + h' :: p || q                   by induction hypothesis
         = (h::p) || (h'::q)                  by by weak_add_def
*)
val subring_poly_weak_add = store_thm(
  "subring_poly_weak_add",
  ``!(r s):'a ring. s <= r ==> !p q. Weak s p /\ Weak s q ==> (weak_add s p q = p || q)``,
  ntac 3 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  Induct_on `q` >-
  rw[] >>
  rw[] >>
  rw[subring_property]);

(* Theorem: s <= r ==> !p. Weak s p ==> !c. c IN B ==> (weak_cmult s c p = c o p) *)
(* Proof:
   By induction on p.
   Base case: Weak s [] ==> (weak_cmult s c [] = c o [])
        weak_cmult s c []
      = []                  by weak_cmult_of_zero
      = c o []              by weak_cmult_of_zero
   Step case: Weak s p ==> (weak_cmult s c p = c o p) ==>
             !h. Weak s (h::p) ==> (weak_cmult s c (h::p) = c o (h::p))
      Note Weak s (h::p) ==> h IN B /\ Weak s p   by weak_cons
        weak_cmult s c (h::p)
      = s.prod.op c h :: weak_cmult s c p         by weak_cmult_cons
      = c * h :: weak_cmult s c p                 by subring_property
      = c * h :: c o p                            by induction hypothesis
      = c o (h::p)                                by weak_cmult_cons
*)
val subring_poly_weak_cmult = store_thm(
  "subring_poly_weak_cmult",
  ``!(r s):'a ring. s <= r ==> !p. Weak s p ==> !c. c IN B ==> (weak_cmult s c p = c o p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  rw[subring_property]);

(* Theorem: s <= r ==> !p. poly_shift s p 1 = p >> 1 *)
(* Proof:
   If p = [], to show: poly_shift s [] 1 = [] >> 1
       poly_shift s [] 1
     = []           by poly_shift_def
     = [] >> 1      by poly_shift_def
   If p = h::t, to show: poly_shift s (h::t) 1 = (h::t) >> 1
       poly_shift s (h::t) 1
     = s.sum.id :: (h::t) >> 0       by poly_shift_def, ONE
     = #0::(h::t) >> 0               by subring_ids
     = #0::(h::t)                    by poly_shift_def
     = (h::t) >> 1                   by poly_shift_def, ONE
*)
val subring_poly_shift_1 = store_thm(
  "subring_poly_shift_1",
  ``!(r s):'a ring. s <= r ==> !p. poly_shift s p 1 = p >> 1``,
  rpt strip_tac >>
  Cases_on `p` >-
  rw[] >>
  metis_tac[poly_shift_def, subring_ids, ONE]);

(* Theorem: s <= r ==> !p n. poly_shift s p n = p >> n *)
(* Proof:
   If p = [], to show: poly_shift s [] n = [] >> n
         poly_shift s [] n
       = []              by poly_shift_of_zero
       = [] >> n         by poly_shift_of_zero
   If p = h::t, to show: poly_shift s (h::t) n = (h::t) >> n
   By induction on n.
   Base case: poly_shift s (h::t) 0 = (h::t) >> 0
         poly_shift s (h::t) 0
       = (h::t)                   by poly_shift_0
       = (h::t) >> 0              by poly_shift_0
   Step case: poly_shift s (h::t) n = (h::t) >> n ==> poly_shift s (h::t) (SUC n) = (h::t) >> SUC n
         poly_shift s (h::t) (SUC n)
       = s.sum.id :: poly_shift s (h::t) n  by poly_shift_def
       = #0 :: poly_shift s (h::t) n        by subring_ids
       = #0 :: (h::t) >> n                  by induction hypothesis
       = (h::t) >> SUC n                    by poly_shift_def
*)
val subring_poly_shift = store_thm(
  "subring_poly_shift",
  ``!(r s):'a ring. s <= r ==> !p n. poly_shift s p n = p >> n``,
  rpt strip_tac >>
  Cases_on `p` >-
  rw[] >>
  Induct_on `n` >-
  rw[] >>
  rw[poly_shift_def, subring_ids]);

(* Theorem: s <= r ==> (poly_shift s (poly_one s) 1 = X) *)
(* Proof:
    poly_shift s (poly_one s) 1
  = poly_shift s |1| 1            by subring_poly_one
  = |1| >> 1                      by subring_poly_shift_1
  = X                             by notation
*)
val subring_poly_X = store_thm(
  "subring_poly_X",
  ``!(r s):'a ring. s <= r ==> (poly_shift s (poly_one s) 1 = X)``,
  metis_tac[subring_poly_one, subring_poly_shift_1]);

(* Theorem: s <= r ==> !p q. Weak s p /\ Weak s q ==> (weak_mult s p q = p o q) *)
(* Proof:
   By induction on p.
   Base case: !q. Weak s [] /\ Weak s q ==> (weak_mult s [] q = [] o q)
       weak_mult s [] q
     = []                by weak_mult_of_zero
     = [] o q            by weak_mult_of_zero
   Step case: !q. Weak s p /\ Weak s q ==> (weak_mult s p q = p o q) ==>
              !h q. Weak s (h::p) /\ Weak s q ==> (weak_mult s (h::p) q = (h::p) o q)
      Note Weak s (h::p) ==> h IN B /\ Weak s p   by weak_cons
      By weak_mult_cons, this is to show:
        weak_add s (weak_cmult s h q) (poly_shift s (weak_mult s p q) 1) = h o q || p o q >> 1
        weak_add s (weak_cmult s h q) (poly_shift s (weak_mult s p q) 1)
      = weak_add s (weak_cmult s h q) (poly_shift s (p o q) 1)   by induction hypothesis
      = weak_add s (weak_cmult s h q) ((p o q) >> 1)             by subring_poly_shift
      = weak_add s (h o q) ((p o q) >> 1)                        by subring_poly_weak_cmult
      = (h o q) || ((p o q) >> 1)                                by subring_poly_weak_add
*)
val subring_poly_weak_mult = store_thm(
  "subring_poly_weak_mult",
  ``!(r s):'a ring. s <= r ==> !p q. Weak s p /\ Weak s q ==> (weak_mult s p q = p o q)``,
  ntac 3 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  (`weak_add s (weak_cmult s h q) (poly_shift s (p o q) 1)
    = weak_add s (weak_cmult s h q) ((p o q) >> 1)` by metis_tac[subring_poly_shift]) >>
  `_ = weak_add s (h o q) ((p o q) >> 1) ` by metis_tac[subring_poly_weak_cmult] >>
  `Ring r /\ Ring s` by rw[] >>
  `Weak s (h o q)` by metis_tac[weak_cmult_weak, subring_poly_weak_cmult] >>
  `Weak s ((p o q) >> 1)` by metis_tac[weak_mult_weak, poly_shift_weak, subring_poly_shift] >>
  rw[subring_poly_weak_add]);

(* Theorem: s <= r ==> !p. Poly s p ==> !c. c IN B ==> (poly_cmult s c p = c * p) *)
(* Proof:
      poly_cmult s c p
    = poly_chop s (weak_cmult s c p)   by poly_cmult_def
    = poly_chop s (c o p)              by subring_poly_weak_cmult
    = chop (c o p)                     by subring_poly_chop
    = c * p                            by poly_cmult_def
*)
val subring_poly_cmult = store_thm(
  "subring_poly_cmult",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p ==> !c. c IN B ==> (poly_cmult s c p = c * p)``,
  metis_tac[poly_cmult_def, subring_poly_weak_cmult, subring_poly_chop, poly_is_weak]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_add s p q = p + q) *)
(* Proof:
      poly_add s p q
    = poly_chop s (weak_add s p q)     by poly_add_def
    = poly_chop s (p || q)             by subring_poly_weak_add
    = chop (p || q)                    by subring_poly_chop
    = p + q                            by poly_add_def
*)
val subring_poly_add = store_thm(
  "subring_poly_add",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_add s p q = p + q)``,
  metis_tac[poly_add_def, subring_poly_weak_add, subring_poly_chop, poly_is_weak]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_mult s p q = p * q) *)
(* Proof:
      poly_mult s p q
    = poly_chop s (weak_mult s p q)   by poly_mult_def
    = poly_chop s (p o q)             by subring_poly_weak_mult
    = chop (p o q)                    by subring_poly_chop
    = p * q                           by poly_mult_def
*)
val subring_poly_mult = store_thm(
  "subring_poly_mult",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_mult s p q = p * q)``,
  metis_tac[poly_mult_def, subring_poly_weak_mult, subring_poly_chop, poly_is_weak]);

(*
> poly_ring_property |> ISPEC ``s:'a ring``;
val it = |- (!p. Poly s p <=> p IN (PolyRing s).carrier) /\
   (!p. Poly s p <=> p IN (PolyRing s).sum.carrier) /\
   (!p. Poly s p <=> p IN (PolyRing s).prod.carrier) /\
   (!p q. poly_add s p q = poly_chop s (weak_add s p q)) /\
   (!p q. poly_mult s p q = poly_chop s (weak_mult s p q)) /\
   (poly_zero s = []) /\ (poly_one s = poly_chop s [s.prod.id]): thm
*)

(* Theorem: s <= r ==> (PolyRing s) <= (PolyRing r) *)
(* Proof:
   By notation, this is to show:
   (1) Ring r ==> Ring (PolyRing r), true by poly_ring_ring
   (2) Ring s ==> Ring (PolyRing s), true by poly_ring_ring
   (3) subring s r ==> subring (PolyRing s) (PolyRing r)
       By subring_def, RingHomo_def, this is to show:
   (1) x IN (PolyRing s).carrier ==> x IN (PolyRing r).carrier
           x IN (PolyRing s).carrier
       ==> Poly s x                    by poly_ring_property
       ==> poly x                      by subring_poly_poly
       ==> x IN (PolyRing r).carrier   by poly_ring_property
   (2) GroupHomo I (PolyRing s).sum (PolyRing r).sum
       By GroupHomo_def, this is to show:
       (1) x IN (PolyRing s).sum.carrier ==> x IN (PolyRing r).sum.carrier
           x IN (PolyRing s).sum.carrier
       ==> Poly s x                        by poly_ring_property
       ==> poly x                          by subring_poly_poly
       ==> x IN (PolyRing r).sum.carrier   by poly_ring_property
       (2) poly_add s x y = x + y = x + y  by subring_poly_add
   (3) MonoidHomo I (PolyRing s).prod (PolyRing r).prod
       By MonoidHomo_def, subring_poly_ids, this is to show:
       (1) x IN (PolyRing s).prod.carrier ==> x IN (PolyRing r).prod.carrier
           x IN (PolyRing s).prod.carrier
       ==> Poly s x                        by poly_ring_property
       ==> poly x                          by subring_poly_poly
       ==> x IN (PolyRing r).prod.carrier  by poly_ring_property
       (2) poly_mult s x y = x * y         by subring_poly_mult
*)
val subring_poly_subring = store_thm(
  "subring_poly_subring",
  ``!(r s):'a ring. s <= r ==> (PolyRing s) <= (PolyRing r)``,
  rpt strip_tac >-
  rw[poly_ring_ring] >-
  rw[poly_ring_ring] >>
  rw_tac std_ss[subring_def, RingHomo_def] >-
  metis_tac[subring_poly_poly, poly_ring_property] >-
 (rw[GroupHomo_def] >-
  metis_tac[subring_poly_poly, poly_ring_property] >>
  metis_tac[subring_poly_add, poly_ring_property]) >>
  rw[MonoidHomo_def, subring_poly_ids] >-
  metis_tac[subring_poly_poly, poly_ring_property] >>
  metis_tac[subring_poly_mult, poly_ring_property]);

(* Theorem: s <= r ==> !p. Poly s p ==> (poly_neg s p = -p) *)
(* Proof:
   By induction on p.
   Base case: Poly s [] ==> (poly_neg s [] = -[])
       poly_neg s []
     = []                           by poly_neg_of_zero
     = -[]                          by poly_neg_of_zero
   Step case: Poly s p ==> (poly_neg s p = -p) ==>
              !h. Poly s (h::p) ==> (poly_neg s (h::p) = -(h::p))
     Note Poly s (h::p)
      ==> h IN B /\ Poly s p        by poly_cons_poly
      and Poly s p ==> poly p       by subring_poly_poly
       poly_neg s (h::p)
     = s.sum.inv h::poly_neg s p    by poly_neg_cons, Ring s, Poly s p
     = -h :: poly_neg s p           by subring_neg, h IN B
     = -h :: -p                     by induction hypothesis
     = -(h::p)                      by poly_neg_cons, Ring r, poly p
*)
val subring_poly_neg = store_thm(
  "subring_poly_neg",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p ==> (poly_neg s p = -p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt (stripDup[poly_cons_poly]) >>
  metis_tac[subring_neg, poly_neg_cons, subring_poly_poly]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_sub s p q = p - q) *)
(* Proof:
   Note Poly s (-q)                   by subring_poly_neg, poly_neg_poly
      poly_sub s p q
    = poly_add s p (poly_neg s q)     by poly_sub_def
    = poly_add s p (- q)              by subring_poly_neg
    = p + -q                          by subring_poly_add
    = p + q                           by poly_sub_def
*)
val subring_poly_sub = store_thm(
  "subring_poly_sub",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> (poly_sub s p q = p - q)``,
  metis_tac[poly_sub_def, subring_poly_neg, subring_poly_add, poly_neg_poly]);

(* Theorem: s <= r ==> !p. Poly s p ==> !n. poly_exp s p n = p ** n *)
(* Proof:
   By induction on n.
   Base case: poly_exp s p 0 = p ** 0
        poly_exp s p 0
      = s.prod.id           by poly_exp_0, Ring s
      = |1|                 by subring_poly_ids
      = p ** 0              by poly_exp_0, Ring r
   Step case: poly_exp s p n = p ** n ==> poly_exp s p (SUC n) = p ** SUC n
        poly_exp s p (SUC n)
      = poly_mult s p (poly_exp s p n)   by poly_exp_SUC, Ring s
      = poly_mult s p (p ** n)           by induction hypothesis
      = p * (p ** n)                     by subring_poly_mult
      = p ** SUC n                       by poly_exp_SUC, Ring r
*)
val subring_poly_exp = store_thm(
  "subring_poly_exp",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p ==> !n. poly_exp s p n = p ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[subring_poly_ids] >>
  metis_tac[subring_poly_mult, poly_exp_SUC, subring_poly_poly, poly_exp_poly]);

(* Theorem: s <= r ==> !c:num. poly_num s c = |c| *)
(* Proof:
   By induction on c.
   Base: poly_num s 0 = ### 0
         poly_num s 0
       = poly_zero s           by poly_ring_sum_0
       = |0|                   by subring_poly_zero
       = ###0                  by poly_ring_sum_0
   Step: poly_num s c = |c| ==> poly_num s (SUC c) = ### (SUC c)
         poly_num s (SUC c)
       = poly_add s (poly_one s) (poly_num s c)   by poly_sum_num_SUC
       = poly_add s (poly_one s) |c|              by induction hypothesis
       = poly_add s |1| |c|                       by subring_poly_one
       = |1| + |c|                                by subring_poly_add
       = ### (SUC c)                              by poly_sum_num_SUC
*)
val subring_poly_sum_num = store_thm(
  "subring_poly_sum_num",
  ``!(r s):'a ring. s <= r ==> !c:num. poly_num s c = |c|``,
  rpt strip_tac >>
  Induct_on `c` >-
  metis_tac[poly_ring_sum_0, subring_poly_zero] >>
  rw[poly_sum_num_SUC] >>
  metis_tac[subring_poly_one, subring_poly_add, poly_one_poly, poly_sum_num_poly]);

(* Proof:
     Master s n
   = poly_sub s (poly_exp s (poly_shift s (poly_one s) 1) n) (poly_shift s (poly_one s) 1)
                        by notation
   = poly_sub s (poly_exp s X n) X       by subring_poly_X
   = poly_sub s (X ** n) X               by subring_poly_exp
   = X ** n - X                          by subring_poly_sub
   = master n                            by notation
*)
val subring_poly_master = store_thm(
  "subring_poly_master",
  ``!(r s):'a ring. s <= r ==> !n. Master s n = master n``,
  metis_tac[subring_poly_X, subring_poly_exp, subring_poly_sub, poly_one_poly, poly_shift_poly, poly_exp_poly]);

(* Theorem: s <= r ==> !n. Unity s n = unity n *)
(* Proof:
     Unity s n
   = poly_sub s (poly_exp s (poly_shift s (poly_one s) 1) n) (poly_one s)
                                                by notation
   = poly_sub s (poly_exp s X n) (poly_one s)   by subring_poly_X
   = poly_sub s (X ** n) (poly_one s)           by subring_poly_exp
   = poly_sub s (X ** n) |1|                    by subring_poly_one
   = X ** n - |1|                               by subring_poly_sub
   = unity n                                    by notation
*)
val subring_poly_unity = store_thm(
  "subring_poly_unity",
  ``!(r s):'a ring. s <= r ==> !n. Unity s n = unity n``,
  metis_tac[subring_poly_X, subring_poly_exp, subring_poly_one, subring_poly_sub, poly_one_poly, poly_shift_poly, poly_exp_poly]);

(* Theorem: s <= r ==> !p. Monic s p ==> monic p *)
(* Proof:
       Monic s p
   <=> Poly s p /\ (poly_lead s p = s.prod.id)   by poly_monic_def
   <=> poly p /\ (poly_lead s p = s.prod.id)     by subring_poly_poly
   <=> poly p /\ (lead p = #1)                   by subring_poly_lead, subring_ids
   <=> monic p                                   by poly_monic_def
*)
val subring_poly_monic = store_thm(
  "subring_poly_monic",
  ``!(r s):'a ring. s <= r ==> !p. Monic s p ==> monic p``,
  metis_tac[poly_monic_def, subring_poly_poly, subring_poly_lead, subring_ids]);

(* Theorem: s <= r ==> !p. Poly s p ==> (Monic s p <=> monic p) *)
(* Proof:
   Note Poly s p ==> poly p                     by subring_poly_poly
       Monic s p
   <=> Poly s p /\ (poly_lead s p = s.prod.id)  by poly_monic_def
   <=> T /\ (poly_lead s p = #1)                by subring_ids
   <=> T /\ (lead p = #1)                       by subring_poly_lead
   <=> poly p /\ (lead p = #1)                  by poly p = T with Poly s p
   <=> monic p                                  by poly_monic_def
   Or,
   Since poly_lead s p = lead p      by subring_poly_lead
     and s.prod.id = #1              by subring_ids
     and Poly s p ==> poly p         by subring_poly_poly
   Hence the result follows          by poly_monic_def
*)
val subring_poly_monic_iff = store_thm(
  "subring_poly_monic_iff",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p ==> (Monic s p <=> monic p)``,
  metis_tac[poly_monic_def, subring_poly_poly, subring_poly_lead, subring_ids]);

(* Theorem: s <= r ==> !p. Ulead s p ==> ulead p *)
(* Proof:
   Note Poly s p ==> poly p                 by subring_poly_poly
    and Deg s p = deg p                     by subring_poly_deg
    and Lead s p = lead p                   by subring_poly_lead
   Thus Unit s (Lead s p) = unit (lead p)   by subring_unit
     or pmonic p                            by notation
*)
val subring_poly_ulead = store_thm(
  "subring_poly_ulead",
  ``!(r:'a ring) s. s <= r ==> !p. Ulead s p ==> ulead p``,
  rpt strip_tac >-
  metis_tac[subring_poly_poly] >>
  metis_tac[subring_poly_lead, subring_unit]);

(* Theorem: s <= r ==> !p. Pmonic s p ==> pmonic p *)
(* Proof:
   Note Poly s p ==> poly p                 by subring_poly_poly
    and Deg s p = deg p                     by subring_poly_deg
    and Lead s p = lead p                   by subring_poly_lead
   Thus Unit s (Lead s p) = unit (lead p)   by subring_unit
     or pmonic p                            by notation
*)
val subring_poly_pmonic = store_thm(
  "subring_poly_pmonic",
  ``!(r:'a ring) s. s <= r ==> !p. Pmonic s p ==> pmonic p``,
  rpt strip_tac >-
  metis_tac[subring_poly_poly] >-
  metis_tac[subring_poly_lead, subring_unit] >>
  metis_tac[subring_poly_deg]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Ulead s q ==>
            ?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\ deg v < deg q *)
(* Proof:
   Note ulead q                           by subring_poly_ulead
   Apply poly_division_all_eqn,
         ?u v. Poly s u /\ Poly s v /\
               (p = poly_add s (poly_mult s u q) v) /\
               if 0 < poly_deg s q then poly_deg s v < poly_deg s q else v = poly_zero s
   Hence deg v < deg q                    by subring_poly_deg
     and p = u * q + v                    by subring_poly_add, subring_poly_mult
   Take u, v as indicated, the result follows.
*)
val subring_poly_division_all_eqn = store_thm(
  "subring_poly_division_all_eqn",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
    ?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\
    if 0 < deg q then deg v < deg q else v = |0|``,
  rpt strip_tac >>
  `ulead q` by metis_tac[subring_poly_ulead] >>
  `?u v. Poly s u /\ Poly s v /\ (p = poly_add s (poly_mult s u q) v) /\
    if 0 < poly_deg s q then poly_deg s v < poly_deg s q else v = poly_zero s` by rw[poly_division_all_eqn] >>
  `if 0 < deg q then deg v < deg q else v = |0|` by metis_tac[subring_poly_deg, subring_poly_zero] >>
  `poly_add s (poly_mult s u q) v = u * q + v` by metis_tac[subring_poly_add, subring_poly_mult, poly_mult_poly] >>
  metis_tac[]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Pmonic s q ==>
            ?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\ deg v < deg q *)
(* Proof:
   Note pmonic q                          by subring_poly_pmonic
   Apply poly_division_eqn,
         ?u v. Poly s u /\ Poly s v /\
               (p = poly_add s (poly_mult s u q) v) /\ poly_deg s v < poly_deg s q
   Hence deg v < deg q                    by subring_poly_deg
     and p = u * q + v                    by subring_poly_add, subring_poly_mult
   Take u, v as indicated, the result follows.
*)
val subring_poly_division_eqn = store_thm(
  "subring_poly_division_eqn",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Pmonic s q ==>
    ?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\ deg v < deg q``,
  rpt strip_tac >>
  `pmonic q` by metis_tac[subring_poly_pmonic] >>
  `?u v. Poly s u /\ Poly s v /\ (p = poly_add s (poly_mult s u q) v) /\ poly_deg s v < poly_deg s q ` by rw[poly_division_eqn] >>
  metis_tac[subring_poly_add, subring_poly_mult, poly_mult_poly, subring_poly_deg]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Ulead s q ==>
            (poly_div s p q = p / q) /\ (poly_mod s p q = p % q) *)
(* Proof:
   Note RingHomo I s r     by subring_def
    and B SUBSET R         by subring_carrier_subset
   also INJ I B R          by INJ_DEF, SUBSET_DEF, I_THM
   Apply I_THM for ring_homo_poly_div_mod to get the result:

> ring_homo_poly_div_mod |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring`` |> ISPEC ``I``;
val it = |- (s ~r~ r) I /\ INJ I B R ==>
    !p q. Poly s p /\ Ulead s q ==>
     (MAP I (poly_div s p q) = MAP I p / MAP I q) /\
     (MAP I (poly_mod s p q) = MAP I p % MAP I q): thm
*)
val subring_poly_div_mod = store_thm(
  "subring_poly_div_mod",
  ``!(r:'a ring) s. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
     (poly_div s p q = p / q) /\ (poly_mod s p q = p % q)``,
  ntac 6 strip_tac >>
  `RingHomo I s r` by rw[GSYM subring_def] >>
  `B SUBSET R` by rw[subring_carrier_subset] >>
  `INJ I B R` by metis_tac[INJ_DEF, SUBSET_DEF, combinTheory.I_THM] >>
  metis_tac[ring_homo_poly_div_mod, MAP_ID]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_div s p q = p / q) *)
(* Proof: by subring_poly_div_mod *)
val subring_poly_div = store_thm(
  "subring_poly_div",
  ``!(r:'a ring) s. s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_div s p q = p / q)``,
  rw_tac std_ss[subring_poly_div_mod]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_mod s p q = p % q) *)
(* Proof: by subring_poly_div_mod *)
val subring_poly_mod = store_thm(
  "subring_poly_mod",
  ``!(r:'a ring) s. s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_mod s p q = p % q)``,
  rw_tac std_ss[subring_poly_div_mod]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q /\ poly_divides s p q ==> p pdivides q *)
(* Proof:
       poly_divides s p q
   ==> ?t. Poly s t /\ (q = poly_mult s t p)   by poly_divides_def
   ==> ?t. Poly s t /\ (q = t * p)             by subring_poly_mult
   ==> ?t. poly t /\ (q = t * p)               by subring_poly_poly
   ==> p pdivides q                            by poly_divides_def
*)
val subring_poly_divides = store_thm(
  "subring_poly_divides",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q /\ poly_divides s p q ==> p pdivides q``,
  prove_tac[poly_divides_def, subring_poly_poly, subring_poly_mult]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Ulead s q ==> (poly_divides s q p <=> q pdivides p) *)
(* Proof:
   Note Poly s p ==> poly p         by subring_poly_poly
    and Pmonic s q ==> pmonic q     by subring_poly_pmonic

        poly_divides s q p
    <=> poly_mod s p q = poly_zero s     by poly_divides_alt
    <=> poly_mod s p q = |0|             by subring_poly_zero
    <=> (p % q) = |0|                    by subring_poly_div_mod
    <=> q pdivides p                     by poly_divides_alt
*)
val subring_poly_divides_iff = store_thm(
  "subring_poly_divides_iff",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Ulead s q ==>
    (poly_divides s q p <=> q pdivides p)``,
  rpt strip_tac >>
  `poly p /\ ulead q` by metis_tac[subring_poly_poly, subring_poly_ulead] >>
  `poly_zero s = |0|` by rw[subring_poly_zero] >>
  metis_tac[poly_divides_alt, subring_poly_div_mod]);

(* This is a generalisation of subring_poly_mult *)

(* Theorem: s <= r ==> !t. FINITE t /\ (!p. p IN t ==> Poly s p) ==> (poly_prod_set s t = PPROD t) *)
(* Proof:
   By finite induction on set t.
   Base: poly_prod_set s {} = PPROD {}
         poly_prod_set s {}
       = poly_one s               by poly_prod_set_empty
       = |1|                      by subring_poly_one
       = PPROD {}                 by poly_prod_set_empty
   Step: poly_set s t ==> (poly_prod_set s t = PPROD t) ==>
         e NOTIN t /\ poly_set s (e INSERT t) ==> poly_prod_set s (e INSERT t) = PPROD (e INSERT t)

       Note poly_set s (e INSERT t)
        ==> Poly s e /\ poly_set s t          by IN_INSERT
        and Poly s (poly_prod_set s t)        by poly_prod_set_poly
        and pset t                            by subring_poly_poly

         poly_prod_set s (e INSERT t)
       = poly_mult s e (poly_prod_set s t)    by poly_prod_set_insert
       = poly_mult s e (PPROD t)              by induction hypothesis
       = e * PPROD t                          by subring_poly_mult
       = PPROD (e INSERT t)                   by poly_prod_set_insert
*)
val subring_poly_prod_set = store_thm(
  "subring_poly_prod_set",
  ``!(r s):'a ring. s <= r ==> !t. FINITE t /\ (!p. p IN t ==> Poly s p) ==> (poly_prod_set s t = PPROD t)``,
  ntac 3 strip_tac >>
  `!t. FINITE t ==> (!p. p IN t ==> Poly s p) ==> (poly_prod_set s t = PPROD t)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[poly_prod_set_empty, subring_poly_one] >>
  fs[IN_INSERT] >>
  `Poly s e /\ poly e` by metis_tac[subring_poly_poly] >>
  `Poly s (poly_prod_set s t)` by rw[poly_prod_set_poly] >>
  `pset t` by metis_tac[subring_poly_poly] >>
  `poly_prod_set s (e INSERT t) = poly_mult s e (PPROD t)` by rw[poly_prod_set_insert] >>
  `_ = e * PPROD t` by metis_tac[subring_poly_mult] >>
  `_ = PPROD (e INSERT t)` by rw[poly_prod_set_insert] >>
  rw[]);

(* Theorem: s <= r ==> !t f. FINITE t /\ t SUBSET R /\ (!x. x IN t ==> Poly s (f x)) ==> Poly s (PPIMAGE f t) *)
(* Proof:
   Note FINITE (IMAGE f t)                    by IMAGE_FINITE
    and poly_set s (IMAGE f t)                by IN_IMAGE
    ==> Poly s (poly_prod_set s (IMAGE f t))  by poly_prod_set_poly, Ring s
     or Poly s (PPROD (IMAGE f t))            by subring_poly_prod_set
     or Poly s (PPIMAGE f t)                  by notation
*)
val subring_poly_prod_set_spoly = store_thm(
  "subring_poly_prod_set_spoly",
  ``!(r s):'a ring. s <= r ==>
   !t f. FINITE t /\ t SUBSET R /\ (!x. x IN t ==> Poly s (f x)) ==> Poly s (PPIMAGE f t)``,
  rpt strip_tac >>
  `FINITE (IMAGE f t)` by rw[] >>
  `poly_set s (IMAGE f t)` by metis_tac[IN_IMAGE] >>
  metis_tac[poly_prod_set_poly, subring_poly_prod_set]);

(* Theorem: s <= r ==> !c. c IN B ==> (poly_factor s c = factor c) *)
(* Proof:
   By poly_factor_def, this is to show:
   (1) c IN B ==> s.sum.inv c = -c, true    by subring_neg
   (2) poly_one s = |1|                     by subring_poly_one
*)
val subring_poly_factor = store_thm(
  "subring_poly_factor",
  ``!(r:'a ring) s. s <= r ==> !c. c IN B ==> (poly_factor s c = factor c)``,
  rw_tac std_ss[poly_factor_def, subring_neg, subring_poly_one]);

(* Theorem: s <= r ==> !p x. Poly s p /\ x IN B /\ poly_root s p x ==> root p x *)
(* Proof:
   Note s <= r ==> RingHomo I s r                by subring_def
    and !x. x IN B /\ poly_root s p x
        ==> root (MAP I p) (I x)                 by ring_homo_poly_root
          = root p x                             by MAP_ID, I_THM
*)
val subring_poly_root = store_thm(
  "subring_poly_root",
  ``!(r:'a ring) s. s <= r ==> !p x. Poly s p /\ x IN B /\ poly_root s p x ==> root p x``,
  rpt strip_tac >>
  `RingHomo I s r` by rw[GSYM subring_def] >>
  metis_tac[ring_homo_poly_root, MAP_ID, combinTheory.I_THM]);

(* Theorem: s <= r ==> !p. Poly s p ==> (poly_roots s p) SUBSET (roots p) *)
(* Proof:
   Note s <= r ==> RingHomo I s r                by subring_def
    and !x. x IN B /\ poly_root s p x
        ==> root (MAP I p) (I x)                 by ring_homo_poly_root
          = root p x                             by MAP_ID, I_THM
   also !x. x IN B ==> x IN R                    by subring_element
   Thus !x. x poly_roots s p ==> x IN (roots p)  by poly_roots_member
     or (poly_roots s p) SUBSET (roots p)        by SUBSET_DEF
*)
val subring_poly_roots = store_thm(
  "subring_poly_roots",
  ``!(r:'a ring) s. s <= r ==> !p. Poly s p ==> (poly_roots s p) SUBSET (roots p)``,
  rpt strip_tac >>
  `RingHomo I s r` by rw[GSYM subring_def] >>
  rw[poly_roots_member, SUBSET_DEF] >-
  metis_tac[subring_element] >>
  metis_tac[ring_homo_poly_root, MAP_ID, combinTheory.I_THM]);

(* ------------------------------------------------------------------------- *)
(* Subring Polynomial (another view)                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s <= r ==> Poly s |0| *)
(* Proof:
       Poly s |0|
   <=> Poly s (poly_zero s)     by subring_poly_zero
   <=> T                        by poly_zero_poly
*)
val poly_zero_spoly = store_thm(
  "poly_zero_spoly",
  ``!(r s):'a ring. s <= r ==> Poly s |0|``,
  rw[]);

(* Theorem: s <= r ==> Poly s |1| *)
(* Proof:
       Poly s |1|
   <=> Poly s (poly_one s)     by subring_poly_one
   <=> T                       by poly_one_poly
*)
val poly_one_spoly = store_thm(
  "poly_one_spoly",
  ``!(r s):'a ring. s <= r ==> Poly s |1|``,
  metis_tac[subring_poly_one, poly_one_poly]);

(* Theorem: s <= r ==> Poly s X *)
(* Proof:
       Poly s X
   <=> Poly s (poly_shift s (poly_one s) 1)  by subring_poly_X
   <=> T                                     by poly_one_poly, poly_shift_poly
*)
val poly_X_spoly = store_thm(
  "poly_X_spoly",
  ``!(r s):'a ring. s <= r ==> Poly s X``,
  metis_tac[subring_poly_X, poly_one_poly, poly_shift_poly]);

(* Theorem: s <= r ==> !p. Poly s p ==> Poly s (-p) *)
(* Proof:
       Poly s (-p)
   <=> Poly s (poly_neg s p)    by subring_poly_neg
   <=> T                        by poly_neg_poly
*)
val poly_neg_spoly = store_thm(
  "poly_neg_spoly",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p ==> Poly s (-p)``,
  metis_tac[subring_poly_neg, poly_neg_poly]);

(* Theorem: s <= r ==> !p c. Poly s p /\ c IN B ==> Poly s (c * p) *)
(* Proof:
      Poly s (c * p)
  <=> Poly s (poly_cmult s c p)      by subring_poly_cmult
  <=> T                              by poly_cmult_poly
*)
val poly_cmult_spoly = store_thm(
  "poly_cmult_spoly",
  ``!(r s):'a ring. s <= r ==> !p c. Poly s p /\ c IN B ==> Poly s (c * p)``,
  metis_tac[subring_poly_cmult, poly_cmult_poly]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p + q) *)
(* Proof:
       Poly s (p + q)
   <=> Poly s (poly_add s p q)   by subring_poly_add
   <=> T                         by poly_add_poly
*)
val poly_add_spoly = store_thm(
  "poly_add_spoly",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p + q)``,
  metis_tac[subring_poly_add, poly_add_poly]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p - q) *)
(* Proof:
       Poly s (p - q)
   <=> Poly s (poly_sub s p q)   by subring_poly_sub
   <=> T                         by poly_sub_poly
*)
val poly_sub_spoly = store_thm(
  "poly_sub_spoly",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p - q)``,
  metis_tac[subring_poly_sub, poly_sub_poly]);

(* Theorem: s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p * q) *)
(* Proof:
       Poly s (p * q)
   <=> Poly s (poly_mult s p q)   by subring_poly_mult
   <=> T                          by poly_mult_poly
*)
val poly_mult_spoly = store_thm(
  "poly_mult_spoly",
  ``!(r s):'a ring. s <= r ==> !p q. Poly s p /\ Poly s q ==> Poly s (p * q)``,
  metis_tac[subring_poly_mult, poly_mult_poly]);

(* Theorem: s <= r ==> !p n. Poly s p ==> Poly s (p >> n) *)
(* Proof:
       Poly s (p >> n)
   <=> Poly s (poly_shift s p n)   by subring_poly_shift
   <=> T                           by poly_shift_poly
*)
val poly_shift_spoly = store_thm(
  "poly_shift_spoly",
  ``!(r s):'a ring. s <= r ==> !p n. Poly s p ==> Poly s (p >> n)``,
  metis_tac[subring_poly_shift, poly_shift_poly]);

(* Theorem: s <= r ==> !p n. Poly s p ==> Poly s (p ** n) *)
(* Proof:
       Poly s (p ** n)
   <=> Poly s (poly_exp s p n)   by subring_poly_exp
   <=> T                         by poly_exp_poly
*)
val poly_exp_spoly = store_thm(
  "poly_exp_spoly",
  ``!(r s):'a ring. s <= r ==> !p n. Poly s p ==> Poly s (p ** n)``,
  metis_tac[subring_poly_exp, poly_exp_poly]);

(* Theorem: s <= r ==> !n. Poly s (X ** n) *)
(* Proof: by poly_X_spoly, poly_exp_spoly *)
val poly_X_exp_n_spoly = store_thm(
  "poly_X_exp_n_spoly",
  ``!(r:'a ring) s. s <= r ==> !n. Poly s (X ** n)``,
  rw[poly_X_spoly, poly_exp_spoly]);

(* Theorem: s <= r ==> !n. Poly s (master n) *)
(* Proof:
   Note Poly s X               by poly_X_spoly
    ==> Poly s (X ** n)        by poly_exp_spoly
     so Poly s (X ** n - X)    by poly_sub_spoly
     or Poly s (master n)      by notation
*)
val poly_master_spoly = store_thm(
  "poly_master_spoly",
  ``!(r s):'a ring. s <= r ==> !n. Poly s (master n)``,
  metis_tac[poly_X_spoly, poly_exp_spoly, poly_sub_spoly]);

(* Theorem: s <= r ==> !n. Poly s (unity n) *)
(* Proof:
   Note Poly s |1|             by poly_one_spoly
    and Poly s X               by poly_X_spoly
    ==> Poly s (X ** n)        by poly_exp_spoly
     so Poly s (X ** n - |1|)  by poly_sub_spoly
     or Poly s (unity n)       by notation
*)
val poly_unity_spoly = store_thm(
  "poly_unity_spoly",
  ``!(r s):'a ring. s <= r ==> !n. Poly s (unity n)``,
  metis_tac[poly_one_spoly, poly_X_spoly, poly_exp_spoly, poly_sub_spoly]);

(* Theorem: s <= r /\ #1 <> #0 ==> !c. c IN B ==> Poly s (factor c) *)
(* Proof:
   Note factor c = X - c * |1|   by poly_factor_alt, subring_element
    and Poly s X                 by poly_X_spoly
    and Poly s (c * |1|)         by poly_cmult_spoly, c IN B
   Thus Poly s (X - c * |1|)     by poly_sub_spoly
     or Poly s (factor c)        by above
*)
val poly_factor_spoly = store_thm(
  "poly_factor_spoly",
  ``!(r:'a ring) s. s <= r /\ #1 <> #0 ==> !c. c IN B ==> Poly s (factor c)``,
  rpt strip_tac >>
  `factor c = X - c * |1|` by metis_tac[poly_factor_alt, subring_element] >>
  `Poly s X /\ Poly s (c * |1|)` by rw[poly_X_spoly, poly_one_spoly, poly_cmult_spoly] >>
  metis_tac[poly_sub_spoly]);

(* ------------------------------------------------------------------------- *)
(* More Subring Theorems                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s <= r /\ #1 <> #0 ==>
            !p x. Poly s p /\ x IN B ==> (poly_root_multiplicity s p x = multiplicity p x) *)
(* Proof:
   Note x IN R                       by subring_element
    and Poly s (factor x)            by poly_factor_spoly, #1 <> #0
   Thus poly_factor s x = factor x   by subring_poly_factor

   By poly_root_multiplicity_def, the result follows if:
      poly_root_multiplicity_set s p x = multiplicity_set p x
   By poly_root_multiplicity_set_def, EXTENSION, this is to show:
      !n. poly_divides s q p <=> q pdivides p,  where q = (factor x) ** n
      because q = poly_exp s (poly_factor s x) n    by subring_poly_exp
   Note monic (factor x)             by poly_factor_monic, #1 <> #0
    and deg (factor x) = 1           by poly_factor_deg, #1 <> #0
   Thus Monic s (factor x)           by subring_poly_monic_iff
    ==> monic q /\ Monic s q         by poly_monic_exp_monic
   Also deg q = n                    by poly_monic_deg_exp
   If n = 0,
      Then q = |1|                   by poly_monic_deg_0
       and q = poly_one s            by subring_poly_one
       and Poly s p ==> poly p       by subring_poly_poly
      Thus true                      by poly_one_divides_all
   If n <> 0,
      Then 0 < deg q                 by n = deg q
        or 0 < Deg s q               by subring_poly_deg
        so Pmonic q                  by poly_monic_pmonic
      Thus true                      by subring_poly_divides_iff
*)
val subring_poly_root_multiplicity = store_thm(
  "subring_poly_root_multiplicity",
  ``!(r:'a ring) s. s <= r /\ #1 <> #0 ==>
     !p x. Poly s p /\ x IN B ==> (poly_root_multiplicity s p x = multiplicity p x)``,
  rpt strip_tac >>
  `x IN R` by metis_tac[subring_element] >>
  `Poly s (factor x)` by rw[poly_factor_spoly] >>
  `poly_factor s x = factor x` by rw[subring_poly_factor] >>
  rw_tac std_ss[poly_root_multiplicity_def] >>
  `poly_root_multiplicity_set s p x = multiplicity_set p x` suffices_by rw[] >>
  rw[poly_root_multiplicity_set_def, EXTENSION] >>
  qabbrev_tac `q = (factor x) ** x'` >>
  `poly_exp s (poly_factor s x) x' = q` by rw[subring_poly_exp, Abbr`q`] >>
  `poly_divides s q p <=> q pdivides p` suffices_by rw[] >>
  `monic (factor x) /\ (deg (factor x) = 1)` by rw[poly_factor_monic, poly_factor_deg] >>
  `Monic s (factor x)` by metis_tac[subring_poly_monic_iff] >>
  `monic q /\ Monic s q` by metis_tac[poly_monic_exp_monic] >>
  `deg q = x'` by rw[poly_monic_deg_exp, Abbr`q`] >>
  Cases_on `x' = 0` >| [
    `q = |1|` by rw[GSYM poly_monic_deg_0] >>
    `q = poly_one s` by rw[subring_poly_one] >>
    metis_tac[poly_one_divides_all, subring_poly_poly],
    `0 < deg q` by decide_tac >>
    `Pmonic s q` by metis_tac[poly_monic_pmonic, subring_poly_deg] >>
    prove_tac[subring_poly_divides_iff]
  ]);

(* Theorem: s <= r /\ #1 <> #0 ==> !p. Poly s p /\ separable p ==> poly_separable s p *)
(* Proof:
   By poly_separable_def, this is to show:
   (1) p <> |0| ==> p <> poly_zero s, true   by subring_poly_zero
   (2) !c. c IN poly_roots s p ==> poly_root_multiplicity s p c = 1
       Note c IN B                     by poly_roots_element
        ==> c IN R                     by subring_element
        and poly p                     by subring_poly_poly
       Thus c IN poly_roots s p        by poly_roots_member
       Note (poly_roots s p) SUBSET (roots p)  by subring_poly_roots
        ==> c IN roots p               by SUBSET_DEF
            poly_root_multiplicity s p c
         = multiplicity p c            by subring_poly_root_multiplicity
         = 1                           by poly_separable_def, separable p
*)
val subring_poly_separable_reverse = store_thm(
  "subring_poly_separable_reverse",
  ``!(r:'a ring) (s:'a ring). s <= r /\ #1 <> #0 ==> !p. Poly s p /\ separable p ==> poly_separable s p``,
  rw_tac std_ss[poly_separable_def] >-
  fs[subring_poly_zero] >>
  `c IN B` by metis_tac[poly_roots_element] >>
  `c IN R` by metis_tac[subring_element] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `c IN roots p` by metis_tac[subring_poly_roots, SUBSET_DEF] >>
  metis_tac[subring_poly_root_multiplicity]);

(* ------------------------------------------------------------------------- *)
(* Common Polynomial = a polynomial in (PolyRing r) or (PolyRing s)          *)
(* ------------------------------------------------------------------------- *)

(* Define common polynomial *)
(* This definition depends on coefficient, with complications with degree:
val common_poly_def = Define`
   common_poly (r:'a ring) (s:'a ring) (p:'a poly) <=> poly p /\ !k. (p ' k) IN B
`;
*)
(* This definition uses EVERY, which is a List property. *)
val common_poly_def = Define`
   common_poly (r:'a ring) (s:'a ring) (p:'a poly) <=> poly p /\ EVERY (\e. e IN B) p
`;
(* overload on common poly *)
val _ = overload_on("cpoly", ``\r s. common_poly r s``);
(*
> common_poly_def;
val it = |- !r s p. cpoly r s p <=> poly p /\ EVERY (\e. e IN B) p thm
*)

(* Theorem: cpoly r s p ==> poly p *)
(* Proof: by common_poly_def *)
val common_poly_poly = store_thm(
  "common_poly_poly",
  ``!p. cpoly r s p ==> poly p``,
  rw[common_poly_def]);

(* Theorem: s <= r ==> !p. poly p ==> (cpoly r s p <=> !k. p ' k IN B) *)
(* Proof:
   By common_poly_def, this is to show: EVERY (\e. e IN B) p <=> !k. p ' k IN B
   If p = |0|,
      to show: EVERY (\e. e IN B) |0| <=> !k. |0| ' k IN B
      If part: EVERY (\e. e IN B) |0| ==> !k. |0| ' k IN B
         EVERY (\e. e IN B) |0|
       = EVERY (\e. e IN B) []           by poly_zero
       = T                               by EVERY_DEF
       Since |0| ' k = #0                by poly_coeff_zero
       and #0 IN B since #0 = s.sum.id   by ring_zero_element, subring_ids
      Only-if part: #0 IN B ==> EVERY (\e. e IN B) |0|
          EVERY (\e. e IN B) |0|
       <=> !n. n < LENGTH |0| ==> EL n |0| IN B    by EVERY_EL
       <=> !n. n < LENGTH []  ==> EL n |0| IN B    by poly_zero
       <=> !n. n < 0          ==> EL n |0| IN B    by LENGTH
       <=> F ==> EL n |0| IN B, which is T
   If p <> |0|, by EVERY_EL,
      to show: (!n. n < LENGTH p ==> EL n p IN B) <=> !k. p ' k IN B
      If part: !n. n < LENGTH p ==> EL n p IN B ==> p ' k IN B
         If k < LENGTH p,
            p ' k = EL k p      by poly_coeff_nonzero_alt, p <> |0|
            and EL k p IN B     by implication
         If ~(k < LENGTH p),
            p ' k = #0          by poly_coeff_nonzero_alt, p <> |0|
            and #0 IN B         by ring_zero_element, subring_ids
      Only-if part: !k. p ' k IN B /\ n < LENGTH p ==> EL n p IN B
         With n < LENGTH p,
            EL n p = p ' n      by poly_coeff_nonzero_alt
            and p ' n IN B      by implication
*)
val common_poly_alt = store_thm(
  "common_poly_alt",
  ``!(r s):'a ring. s <= r ==> !p. poly p ==> (cpoly r s p <=> !k. p ' k IN B)``,
  rw_tac std_ss[common_poly_def] >>
  Cases_on `p = |0|` >| [
    rw_tac std_ss[poly_coeff_zero, EQ_IMP_THM] >-
    metis_tac[ring_zero_element, subring_ids] >>
    rw[],
    rw_tac std_ss[EVERY_EL, EQ_IMP_THM] >| [
      Cases_on `k < LENGTH p` >>
      rw[poly_coeff_nonzero_alt] >>
      metis_tac[ring_zero_element, subring_ids],
      metis_tac[poly_coeff_nonzero_alt]
    ]
  ]);

(* Theorem: s <= r ==> !p. cpoly r s p ==> Poly s p *)
(* Proof:
   By induction on p.
   Base case: cpoly r s [] ==> Poly s []
      True since Poly s [] = T                      by zero_poly_poly
   Step case: cpoly r s p ==> Poly s p ==> !h. cpoly r s (h::p) ==> Poly s (h::p)
        cpoly r s (h::p)
      = poly (h::p) /\ EVERY (\e. e IN Fp) (h::p)   by common_poly_def
      = h IN R /\ poly p /\ ~zerop(h::p) /\
        EVERY (\e. e IN B) (h::p)                   by Poly_def
      = h IN R /\ poly p /\ ~zerop(h::p) /\
        (h IN B) /\ (EVERY (\e. e IN B) p)          by EVERY_DEF
      Now  h IN R /\ (EVERY (\e. e IN B) p)
       ==> cpoly p                                  by common_poly_def
       ==> poly p                                   by induction hypothesis
      Also ~zerop(h::p) ==> ~zero_poly s (h::p)     by subring_poly_zero_poly
       so h IN B /\ Poly s p /\ ~zero_poly s (h::p)
       ==> Poly s (h::p)                            by Poly_def
*)
val common_poly_subring_poly = store_thm(
  "common_poly_subring_poly",
  ``!(r s):'a ring. s <= r ==> !p. cpoly r s p ==> Poly s p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[common_poly_def, poly_cons_poly] >| [
    `!h t. EVERY (\e. e IN B) (h::t) <=> h IN B /\ EVERY (\e. e IN B) t` by rw[EVERY_DEF] >>
    metis_tac[],
    `!h t. EVERY (\e. e IN B) (h::t) <=> h IN B /\ EVERY (\e. e IN B) t` by rw[EVERY_DEF] >>
    metis_tac[common_poly_def],
    metis_tac[subring_poly_zero_poly]
  ]);

(* Theorem: s <= r ==> !p. Poly s p <=> cpoly r s p *)
(* Proof:
   If part: Poly s p ==> cpoly r s p
      By common_poly_def, this is to show:
      (1) Poly s p ==> poly p, true                by subring_poly_poly
      (2) pfpoly p ==> EVERY (\e. e IN Fp) p, true by poly_every_element
   Only-if part: cpoly r s p ==> Poly s p
      This is true by common_poly_subring_poly.
*)
val subring_poly_alt = store_thm(
  "subring_poly_alt",
  ``!(r s):'a ring. s <= r ==> !p. Poly s p <=> cpoly r s p``,
  rw[EQ_IMP_THM] >| [
    rw[common_poly_def] >-
    metis_tac[subring_poly_poly] >>
    rw[poly_every_element],
    metis_tac[common_poly_subring_poly]
  ]);

(*
Some prime_field theorem can be proved by subfield/subring.
Proofs below to be revised.
*)

(* ------------------------------------------------------------------------- *)
(* Polynomials of Prime Field                                                *)
(* ------------------------------------------------------------------------- *)

(*
Given a Field (r:'a field), its prime field (PF r) is also of type: 'a field:
> type_of ``PF (r:'a field)``;
val it = ``:'a field``: hol_type

prime_field_subfield |- !(r :'a field). FiniteField r ==> subfield (PF r) r

Of course, Field r is the extension field of (PF r), so this is extension of the same type.

Now, a polynomial with coefficients from (PF r), i.e. all ##n,
    can also be regarded as a polynomial in (Field r).
Let p be a polynomial.
As p IN (PF r)[x] = (PolyRing (PF r)), p can be irreducible.
But as p IN (Field r)[x] = (PolyRing r), p can have roots.

See if this can be done in HOL!
*)

(* Overloads for (PF r) elements *)
val _ = overload_on("pfpoly", ``Poly (PF r)``);
val _ = overload_on("pfzerop", ``zero_poly (PF r)``);
val _ = overload_on("pfchop", ``poly_chop (PF r)``);
val _ = overload_on("pfcmult", ``poly_cmult (PF r)``);
val _ = overload_on("pfshift", ``poly_shift (PF r)``);
val _ = overload_on("pfcoeff", ``poly_coeff (PF r)``);
val _ = overload_on("pfdeg", ``poly_deg (PF r)``);
val _ = overload_on("pflead", ``poly_lead (PF r)``);
val _ = overload_on("pfadd", ``(PolyRing (PF r)).sum.op``);
val _ = overload_on("pfmult", ``(PolyRing (PF r)).prod.op``);
val _ = overload_on("pfneg", ``(PolyRing (PF r)).sum.inv``);
val _ = overload_on("pfexp", ``(PolyRing (PF r)).prod.exp``);

(*
> PF_property;
val it = |- !r.
     (Fp = IMAGE $## univ(:num)) /\
     ((PF r).sum.carrier = IMAGE $## univ(:num)) /\
     ((PF r).sum.op = $+) /\ ((PF r).sum.id = #0) /\
     ((PF r).prod.carrier = IMAGE $## univ(:num)) /\
     ((PF r).prod.op = $* ) /\ ((PF r).prod.id = #1) /\
     ((PF r).prod.exp = $** ): thm
> poly_ring_property |> SPEC ``(PF r)``;
val it = |-
   (!p. pfpoly p <=> p IN (PolyRing (PF r)).carrier) /\
   (!p. pfpoly p <=> p IN (PolyRing (PF r)).sum.carrier) /\
   (!p. pfpoly p <=> p IN (PolyRing (PF r)).prod.carrier) /\
   (!p q. pfadd p q = pfchop (weak_add (PF r) p q)) /\
   (!p q. pfmult p q = pfchop (weak_mult (PF r) p q)) /\
   ((PolyRing (PF r)).sum.id = []) /\
   ((PolyRing (PF r)).prod.id = pfchop [(PF r).prod.id]): thm
*)

(* Theorem: FiniteField r ==> Ring (PolyRing (PF r)) *)
(* Proof:
   FiniteField r ==> Field (PF r)              by prime_field_field
                 ==> Ring (PolyRing (PF r))    by poly_ring_ring
*)
val poly_prime_field_ring = store_thm(
  "poly_prime_field_ring",
  ``!r:'a field. FiniteField r ==> Ring (PolyRing (PF r))``,
  rw[prime_field_field, poly_ring_ring]);

(* Theorem: FiniteField r ==> (PolyRing (PF r)) <= (PolyRing r) *)
(* Proof:
   FiniteField r ==> (PF r) <<= r         by prime_field_is_subfield
                 ==> (PF r) <= r          by subfield_is_subring
                 ==> (PolyRing (PF r)) <= (PolyRing r)   by subring_poly_subring
*)
val poly_prime_field_is_subring = store_thm(
  "poly_prime_field_is_subring",
  ``!r:'a field. FiniteField r ==> (PolyRing (PF r)) <= (PolyRing r)``,
  metis_tac[prime_field_is_subfield, subfield_is_subring, subring_poly_subring]);

(* Theorem: pfpoly p <=> p IN (PolyRing (PF r)).carrier *)
(* Proof: by poly_ring_property *)
val poly_prime_field_element = store_thm(
  "poly_prime_field_element",
  ``!p. pfpoly p <=> p IN (PolyRing (PF r)).carrier``,
  rw[poly_ring_property]);

(* Theorem: ((PolyRing (PF r)).sum.id = |0|) /\ ((PolyRing (PF r)).prod.id = |1|) *)
(* Proof: by poly_ring_property, PF_property *)
val poly_prime_field_ids = store_thm(
  "poly_prime_field_ids",
  ``!r:'a field. ((PolyRing (PF r)).sum.id = |0|) /\ ((PolyRing (PF r)).prod.id = |1|)``,
  rw[poly_ring_property, PF_property]);

(* Theorem: Properties of polynomials in Prime Field. *)
(* Proof: by poly_ring_property, PF_property *)
val poly_prime_field_property = store_thm(
  "poly_prime_field_property",
  ``!r:'a field. (!p. pfpoly p <=> p IN (PolyRing (PF r)).carrier) /\
                ((PolyRing (PF r)).sum.id = |0|) /\
                ((PolyRing (PF r)).prod.id = |1|)``,
  rw[poly_ring_property, PF_property]);

(* Theorem: pfzerop p <=> zerop p *)
(* Proof:
   By induction on p.
   Base case: pfzerop [] <=> zerop []
      True by zero_poly_def
   Step case: pfzerop p <=> zerop p ==>
              !h. pfzerop (h::p) <=> zerop (h::p)
      True by zero_poly_cons, PF_property.
*)
val poly_prime_field_zero_poly = store_thm(
  "poly_prime_field_zero_poly",
  ``!p. pfzerop p <=> zerop p``,
  Induct_on `p` >-
  rw[] >>
  rw[PF_property]);

(* Theorem: Ring r ==> !p. pfpoly p ==> poly p *)
(* Proof:
   By induction on p.
   Base case: pfpoly [] ==> poly []
      True by zero_poly_poly.
   Step case: pfpoly p ==> poly p ==> !h. pfpoly (h::p) ==> poly (h::p)
      By PF_property, this is to show:
      (1) ##x IN R, true by ring_num_element
      (2) ~zero_poly (PF r) p ==> ##x <> #0 \/ ~zerop p
          True by poly_prime_field_zero_poly
*)
Theorem poly_prime_field_element_poly:
  !r:'a ring. Ring r ==> !p. pfpoly p ==> poly p
Proof
  rpt strip_tac >>
  Induct_on `p` >- rw[] >>
  rw[PF_property] >- rw[ring_num_element] >>
  metis_tac[poly_prime_field_zero_poly]
QED

(* Theorem: Ring r ==> (PolyRing (PF r)).carrier SUBSET (PolyRing r).carrier *)
(* Proof:
   Since pfpoly p <=> p IN (PolyRing (PF r)).carrier   by poly_ring_property
          poly p <=> p IN (PolyRing r).carrier        by poly_ring_property
     and pfpoly p ==> poly p                           by poly_prime_field_element_poly
   Hence true                                         by SUBSET_DEF
*)
val poly_prime_field_carrier_subset = store_thm(
  "poly_prime_field_carrier_subset",
  ``!r:'a ring. Ring r ==> (PolyRing (PF r)).carrier SUBSET (PolyRing r).carrier``,
  metis_tac[poly_ring_property, SUBSET_DEF, poly_prime_field_element_poly]);

(* Theorem: FiniteField r ==>
         ((PolyRing (PF r)).sum.carrier = (PolyRing (PF r)).carrier) /\
         ((PolyRing (PF r)).prod.carrier = (PolyRing (PF r)).carrier) *)
(* Proof: by poly_prime_field_ring, ring_carriers *)
val poly_prime_field_carriers = store_thm(
  "poly_prime_field_carriers",
  ``!r:'a field. FiniteField r ==>
         ((PolyRing (PF r)).sum.carrier = (PolyRing (PF r)).carrier) /\
         ((PolyRing (PF r)).prod.carrier = (PolyRing (PF r)).carrier)``,
  rw[poly_prime_field_ring, ring_carriers]);

(* Theorem: pfdeg p = deg p *)
(* Proof: by poly_deg_def *)
val poly_prime_field_deg = store_thm(
  "poly_prime_field_deg",
  ``!p. pfdeg p = deg p``,
  rw[poly_deg_def]);

(* Theorem: pflead p = lead p *)
(* Proof: by poly_lead_def, PF_property *)
val poly_prime_field_lead = store_thm(
  "poly_prime_field_lead",
  ``!p. pflead p = lead p``,
  metis_tac[poly_lead_def, list_CASES, PF_property]);

(* Theorem: !k. pfcoeff p k = p ' k *)
(* Proof: by poly_coeff_def, PF_property *)
val poly_prime_field_coeff = store_thm(
  "poly_prime_field_coeff",
  ``!p k. pfcoeff p k = p ' k``,
  rpt strip_tac >>
  Cases_on `p` >>
  rw[poly_coeff_def, PF_property]);

(* Theorem: pfchop p = chop p *)
(* Proof:
   By induction on p.
   Base case: pfchop [] = chop []
      True by poly_chop_of_zero
   Step case: pfchop p = chop p ==>
              !h. pfchop (h::p) = chop (h::p)
      True by poly_chop_cons, poly_prime_field_zero_poly
*)
val poly_prime_field_chop = store_thm(
  "poly_prime_field_chop",
  ``!p. pfchop p = chop p``,
  Induct_on `p` >>
  rw[poly_prime_field_zero_poly]);

(* Theorem: weak_add (PF r) p q = p || q *)
(* Proof:
   By induction on p.
   Base case: !q. weak_add (PF r) [] q = [] || q
        weak_add (PF r) [] q
      = q                         by weak_add_def
      = [] || q                   by weak_add_def
   Step case: !q. weak_add (PF r) p q = p || q ==>
              !h q. weak_add (PF r) (h::p) q = (h::p) || q
      By induction on q.
      Base case: weak_add (PF r) (h::p) [] = (h::p) || []
           weak_add (PF r) (h::p) []
         = (h::p)                 by weak_add_def
         = (h::p) || []           by weak_add_def
      Step case: !q. weak_add (PF r) p q = p || q ==>
                 !h'. weak_add (PF r) (h::p) (h'::q) = (h::p) || (h'::q)
           weak_add (PF r) (h::p) (h'::q)
         = (PF r).sum.op h h' :: weak_add (PF r) p q    by weak_add_def
         = h + h' :: weak_add (PF r) p q                by PF_property
         = h + h' :: p || q                             by induction hypothesis
         = (h::p) || (h'::q)                            by by weak_add_def
*)
val poly_prime_field_weak_add = store_thm(
  "poly_prime_field_weak_add",
  ``!p q. weak_add (PF r) p q = p || q``,
  Induct_on `p` >-
  rw[] >>
  Induct_on `q` >-
  rw[] >>
  rw[weak_add_def, PF_property]);

(* Theorem: weak_cmult (PF r) c p = c o p *)
(* Proof:
   By induction on p.
   Base case: !c. weak_cmult (PF r) c [] = c o []
        weak_cmult (PF r) c []
      = []                      by weak_cmult_of_zero
      = c o []                  by weak_cmult_of_zero
   Step case: !c. weak_cmult (PF r) c p = c o p ==> !h c. weak_cmult (PF r) c (h::p) = c o (h::p)
        weak_cmult (PF r) c (h::p)
      = (PF r).prod.op c h :: weak_cmult (PF r) c p    by weak_cmult_cons
      = c * h :: weak_cmult (PF r) c p                 by PF_property
      = c * h :: c o p                                 by induction hypothesis
      = c o (h::p)                                     by weak_cmult_cons
*)
val poly_prime_field_weak_cmult = store_thm(
  "poly_prime_field_weak_cmult",
  ``!c p. weak_cmult (PF r) c p = c o p``,
  Induct_on `p` >>
  rw[PF_property]);

(* Theorem: pfshift p 1 = p >> 1 *)
(* Proof:
   If p = [], to show: pfshift [] 1 = [] >> 1
       pfshift [] 1
     = []           by poly_shift_def
     = [] >> 1      by poly_shift_def
   If p = h::t, to show: pfshift (h::t) 1 = (h::t) >> 1
       pfshift (h::t) 1
     = (PF r).sum.id :: (h::t) >> 0  by poly_shift_def, ONE
     = #0::(h::t) >> 0               by PF_property
     = #0::(h::t)                    by poly_shift_def
     = (h::t) >> 1                   by poly_shift_def, ONE
*)
val poly_prime_field_shift_1 = store_thm(
  "poly_prime_field_shift_1",
  ``!p. pfshift p 1 = p >> 1``,
  Cases_on `p` >>
  metis_tac[poly_shift_def, PF_property, ONE]);

(* Theorem: pfshift p n = p >> n *)
(* Proof:
   If p = [], to show: !n. pfshift [] n = [] >> n
         pfshift [] n
       = []              by poly_shift_of_zero
       = [] >> n         by poly_shift_of_zero
   If p = h::t, to show: !n. pfshift (h::t) n = (h::t) >> n
   By induction on n.
   Base case: pfshift (h::t) 0 = (h::t) >> 0
         pfshift p 0
       = p                   by poly_shift_0
       = p >> 0              by poly_shift_0
   Step case: pfshift (h::t) n = (h::t) >> n ==> pfshift (h::t) (SUC n) = (h::t) >> SUC n
         pfshift (h::t) (SUC n)
       = (PF r).sum.id :: pfshift (h::t) n  by poly_shift_def
       = #0 :: pfshift (h::t) n             by PF_property
       = #0 :: (h::t) >> n                  by induction hypothesis
       = (h::t) >> SUC n                    by poly_shift_def
*)
val poly_prime_field_shift = store_thm(
  "poly_prime_field_shift",
  ``!p n. pfshift p n = p >> n``,
  Cases_on `p` >-
  rw[] >>
  Induct_on `n` >>
  rw[poly_shift_def, PF_property]);

(* Theorem: weak_mult (PF r) p q = p o q *)
(* Proof:
   By induction on p.
   Base case: !q. weak_mult (PF r) [] q = [] o q
       weak_mult (PF r) [] q
     = []                        by weak_mult_of_zero
     = [] o q                    by weak_mult_of_zero
   Step case: !q. weak_mult (PF r) p q = p o q ==>
              !h q. weak_mult (PF r) (h::p) q = (h::p) o q
      By weak_mult_cons, this is to show:
         weak_add (PF r) (weak_cmult (PF r) h q) (pfshift (weak_mult (PF r) p q) 1) = h o q || p o q >> 1
        weak_add (PF r) (weak_cmult (PF r) h q) (pfshift (weak_mult (PF r) p q) 1)
      = weak_add (PF r) (weak_cmult (PF r) h q) (pfshift (p o q) 1)  by induction hypothesis
      = weak_add (PF r) (weak_cmult (PF r) h q) ((p o q) >> 1)       by poly_prime_field_shift
      = weak_add (PF r) (h o q) ((p o q) >> 1)                       by poly_prime_field_weak_cmult
      = (h o q) || ((p o q) >> 1)                                    by poly_prime_field_weak_add
*)
val poly_prime_field_weak_mult = store_thm(
  "poly_prime_field_weak_mult",
  ``!p q. weak_mult (PF r) p q = p o q``,
  Induct_on `p` >-
  rw[] >>
  rw[poly_prime_field_shift, poly_prime_field_weak_cmult, poly_prime_field_weak_add]);

(* Theorem: pfcmult c p = c * p *)
(* Proof:
      pfcmult c p
    = pfchop (weak_cmult (PF r) c p)    by poly_cmult_def
    = pfchop (c o p)                    by poly_prime_field_weak_cmult
    = chop (c o p)                      by poly_prime_field_chop
    = c * p                             by poly_cmult_def
*)
val poly_prime_field_cmult = store_thm(
  "poly_prime_field_cmult",
  ``!c p. pfcmult c p = c * p``,
  rw[poly_cmult_def, poly_prime_field_weak_cmult, poly_prime_field_chop]);

(* Theorem: pfadd p q = p + q *)
(* Proof:
      pfadd p q
    = pfchop (weak_add (PF r) p q)      by poly_add_def
    = pfchop (p || q)                   by poly_prime_field_weak_add
    = chop (p || q)                     by poly_prime_field_chop
    = p + q                             by poly_add_def
*)
val poly_prime_field_add = store_thm(
  "poly_prime_field_add",
  ``!p q. (PolyRing (PF r)).sum.op p q = p + q``,
  rw[poly_add_def, poly_prime_field_weak_add, poly_prime_field_chop]);

(* Theorem: pfmult p q = p * q *)
(* Proof:
      pfmult p q
    = pfchop (weak_mult (PF r) p q)    by poly_mult_def
    = pfchop (p o q)                   by poly_prime_field_weak_mult
    = chop (p o q)                     by poly_prime_field_chop
    = p * q                            by poly_mult_def
*)
val poly_prime_field_mult = store_thm(
  "poly_prime_field_mult",
  ``!p q. pfmult p q = p * q``,
  rw[poly_mult_def, poly_prime_field_weak_mult, poly_prime_field_chop]);

(*
> poly_ring_property |> SPEC ``(PF r)``;
val it =
   |- (!p. pfpoly p <=> p IN (PolyRing (PF r)).carrier) /\
   (!p. pfpoly p <=> p IN (PolyRing (PF r)).sum.carrier) /\
   (!p. pfpoly p <=> p IN (PolyRing (PF r)).prod.carrier) /\
   (!p q.
      (PolyRing (PF r)).sum.op p q =
      poly_chop (PF r) (weak_add (PF r) p q)) /\
   (!p q.
      (PolyRing (PF r)).prod.op p q =
      poly_chop (PF r) (weak_mult (PF r) p q)) /\
   ((PolyRing (PF r)).sum.id = []) /\
   ((PolyRing (PF r)).prod.id = poly_chop (PF r) [(PF r).prod.id]):
   thm
*)

(* Theorem: Ring r ==> subring (PolyRing (PF r)) (PolyRing r) *)
(* Proof:
   By subring_def, RingHomo_def, this is to show:
   (1) x IN (PolyRing (PF r)).carrier ==> x IN (PolyRing r).carrier
       True by poly_prime_field_carrier_subset, SUBSET_DEF.
   (2) GroupHomo I (PolyRing (PF r)).sum (PolyRing r).sum
       By GroupHomo_def, this is to show:
       (1) x IN (PolyRing (PF r)).sum.carrier ==> x IN (PolyRing r).sum.carrier
               x IN (PolyRing (PF r)).sum.carrier
           ==> x IN (PolyRing (PF r)).carrier   by poly_prime_field_carriers
           ==> x IN (PolyRing r).carrier        by poly_prime_field_carrier_subset, SUBSET_DEF
           ==> x IN (PolyRing r).sum.carrier    by poly_ring_carriers
       (2) pfadd x y = x + y, true              by poly_prime_field_add
   (3) MonoidHomo I (PolyRing (PF r)).prod (PolyRing r).prod
       By MonoidHomo_def, poly_prime_field_ids, this is to show:
       (1) x IN (PolyRing (PF r)).prod.carrier ==> x IN (PolyRing r).prod.carrier
               x IN (PolyRing (PF r)).prod.carrier
           ==> x IN (PolyRing (PF r)).carrier   by poly_prime_field_carriers
           ==> x IN (PolyRing r).carrier        by poly_prime_field_carrier_subset, SUBSET_DEF
           ==> x IN (PolyRing r).prod.carrier   by poly_ring_carriers
       (2) pfmult x y = x * y, true             by poly_prime_field_mult
*)
val poly_prime_field_subring = store_thm(
  "poly_prime_field_subring",
  ``!r:'a ring. Ring r ==> subring (PolyRing (PF r)) (PolyRing r)``,
  rw_tac std_ss[subring_def, RingHomo_def] >-
  metis_tac[poly_prime_field_carrier_subset, SUBSET_DEF] >-
 (rw[GroupHomo_def] >-
  metis_tac[poly_prime_field_carrier_subset, SUBSET_DEF, poly_prime_field_carriers, poly_ring_carriers] >>
  rw[poly_prime_field_add]) >>
  rw[MonoidHomo_def, poly_prime_field_ids] >-
  metis_tac[poly_prime_field_carrier_subset, SUBSET_DEF, poly_prime_field_carriers, poly_ring_carriers] >>
  rw[poly_prime_field_mult]);

(* ------------------------------------------------------------------------- *)
(* Prime Field Common Polynomial = a polynomial in (PolyRing r)              *)
(*                                              or (PolyRing (PF r))         *)
(* ------------------------------------------------------------------------- *)

(* Define common polynomial *)
(* This definition depends on coefficient, with complications with degree:
val pf_common_poly_def = Define`
   pf_common_poly (r:'a ring) (p:'a poly) = poly p /\ !k. (p ' k) IN Fp
`;
*)
(* This definition uses EVERY, with is a List property. *)
val pf_common_poly_def = Define`
   pf_common_poly (r:'a ring) (p:'a poly) <=> poly p /\ EVERY (\e. e IN Fp) p
`;
(* overload on common poly *)
val _ = overload_on("pfcpoly", ``pf_common_poly r``);
(*
> pf_common_poly_def;
val it = |- !r p. pfcpoly p <=> poly p /\ EVERY (\e. e IN Fp) p: thm
*)

(* Theorem: pfcpoly p ==> poly p *)
(* Proof: by pf_common_poly_def *)
val pf_common_poly_poly = store_thm(
  "pf_common_poly_poly",
  ``!p. pfcpoly p ==> poly p``,
  rw[pf_common_poly_def]);

(* Theorem: pfcpoly p ==> pfpoly p *)
(* Proof:
   By induction on p.
   Base case: pfcpoly [] ==> pfpoly []
      True since pfpoly [] = T         by zero_poly_poly
   Step case: pfcpoly p ==> pfpoly p ==> !h. pfcpoly (h::p) ==> pfpoly (h::p)
        pfcpoly (h::p)
      = poly (h::p) /\ EVERY (\e. e IN Fp) (h::p)   by pf_common_poly_def
      = h IN R /\ poly p /\ ~zerop(h::p) /\
        EVERY (\e. e IN Fp) (h::p)                  by Poly_def
      = h IN R /\ poly p /\ ~zerop(h::p) /\
        (h IN Fp) /\ (EVERY (\e. e IN Fp) p)        by EVERY_DEF
      Now  h IN R /\ (EVERY (\e. e IN Fp) p)
       ==> pfcpoly p                                by pf_common_poly_def
       ==> pfpoly p                                 by induction hypothesis
      Also ~zerop(h::p) ==> ~pfzerop(h::p)          by poly_prime_field_zero_poly
       so h IN Fp /\ pfpoly p /\ ~pfzerop(h::p)
       ==> pfpoly (h::p)                            by Poly_def
*)
val pf_common_poly_pfpoly = store_thm(
  "pf_common_poly_pfpoly",
  ``!p. pfcpoly p ==> pfpoly p``,
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[pf_common_poly_def, poly_cons_poly] >| [
    `!h t. EVERY (\e. e IN Fp) (h::t) <=> h IN Fp /\ EVERY (\e. e IN Fp) t` by rw[EVERY_DEF] >>
    metis_tac[],
    `!h t. EVERY (\e. e IN Fp) (h::t) <=> h IN Fp /\ EVERY (\e. e IN Fp) t` by rw[EVERY_DEF] >>
    metis_tac[pf_common_poly_def],
    metis_tac[poly_prime_field_zero_poly]
  ]);

(* Theorem: Ring r ==> !p. pfpoly p <=> pfcpoly p *)
(* Proof:
   If part: pfpoly p ==> pfcpoly p
      By pf_common_poly_def, this is to show:
      (1) pfpoly p ==> poly p, true by poly_prime_field_element_poly
      (2) pfpoly p ==> EVERY (\e. e IN Fp) p, true by poly_every_element
   Only-if part: pfcpoly p ==> pfpoly p
      This is true by pf_common_poly_pfpoly
*)
val poly_prime_field_poly_alt = store_thm(
  "poly_prime_field_poly_alt",
  ``!r:'a ring. Ring r ==> !p. pfpoly p <=> pfcpoly p``,
  rw[EQ_IMP_THM] >| [
    rw[pf_common_poly_def] >-
    rw[poly_prime_field_element_poly] >>
    rw[poly_every_element],
    rw[pf_common_poly_pfpoly]
  ]);

(* Theorem: FiniteField r ==> !p. pfpoly p ==> (pfneg p = -p) *)
(* Proof:
   Since FiniteField r
     ==> Field (PF r)               by prime_field_field
      so Ring (PF r) and Ring r     by field_is_ring
   By induction on p.
   Base case: pfpoly [] ==> (pfneg [] = -[])
       pfneg []
     = []                           by poly_neg_of_zero, Ring (PF r)
     = -[]                          by poly_neg_of_zero, Ring r
   Step case: pfpoly p ==> (pfneg p = -p) ==>
              !h. pfpoly (h::p) ==> (pfneg (h::p) = -(h::p))
     Note pfpoly (h::p)
      ==> h IN Fp /\ pfpoly p       by poly_cons_poly
      and pfpoly p ==> poly p       by poly_prime_field_element_poly
       pfneg (h::p)
     = (PF r).sum.inv h::pfneg p    by poly_neg_cons, Ring (PF r), pfpoly (h::p)
     = -h :: pfneg p                by prime_field_neg, h IN Fp
     = -h :: -p                     by induction hypothesis
     = -(h::p)                      by poly_neg_cons, Ring r, poly p
*)
val poly_prime_field_neg = store_thm(
  "poly_prime_field_neg",
  ``!r:'a field. FiniteField r ==> !p. pfpoly p ==> (pfneg p = -p)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring (PF r) /\ Ring r` by rw[prime_field_field] >>
  Induct_on `p` >-
  rw[] >>
  rpt (stripDup[poly_cons_poly]) >>
  rw_tac std_ss[prime_field_neg, poly_neg_cons, poly_prime_field_element_poly]);

(* Theorem: pfexp p n = p ** n *)
(* Proof:
   By induction on n.
   Base case: !p. pfexp p 0 = p ** 0
        pfexp p 0
      = (PolyRing (PF r)).prod.id   by poly_exp_0
      = |1|                         by poly_prime_field_ids
      = p ** 0                      by poly_exp_0
   Step case: !p. pfexp p n = p ** n ==>
              !p. pfexp p (SUC n) = p ** SUC n
        pfexp p (SUC n)
      = pfmult p (pfexp p n)        by poly_exp_SUC
      = pfmult p (p ** n)           by induction hypothesis
      = p * (p ** n)                by poly_prime_field_mult
      = p ** SUC n                  by poly_exp_SUC
*)
val poly_prime_field_exp = store_thm(
  "poly_prime_field_exp",
  ``!p n. pfexp p n = p ** n``,
  Induct_on `n` >-
  rw[poly_prime_field_ids] >>
  rw[poly_prime_field_mult]);

(* ------------------------------------------------------------------------- *)
(* Freshman Theorems for Finite Field                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x y. poly x /\ poly y ==>
            ((x + y) ** (char r) = x ** (char r) + y ** (char r)) *)
(* Proof:
   Since FiniteField r
     ==> Field r ==> Ring r         by FiniteField_def, field_is_ring
     and prime (char r)             by finite_field_char
   The result is true               by poly_freshman_thm
*)
val poly_field_freshman_thm = store_thm(
  "poly_field_freshman_thm",
  ``!r:'a field. FiniteField r ==> !x y. poly x /\ poly y ==>
       ((x + y) ** (char r) = x ** (char r) + y ** (char r))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  rw[poly_freshman_thm]);

(* Theorem: FiniteField r ==> !x y. poly x /\ poly y ==>
            ((x - y) ** (char r) = x ** (char r) - y ** (char r)) *)
(* Proof:
   Since FiniteField r
     ==> Field r ==> Ring r         by FiniteField_def, field_is_ring
     and prime (char r)             by finite_field_char
   The result is true               by poly_freshman_thm_sub
*)
val poly_field_freshman_thm_sub = store_thm(
  "poly_field_freshman_thm_sub",
  ``!r:'a field. FiniteField r ==> !x y. poly x /\ poly y ==>
       ((x - y) ** (char r) = x ** (char r) - y ** (char r))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  rw[poly_freshman_thm_sub]);

(* Theorem: FiniteField r ==> !x y. poly x /\ poly y ==>
            !n. (x + y) ** (char r ** n) = x ** (char r ** n) + y ** (char r ** n) *)
(* Proof:
   Since FiniteField r
     ==> Field r ==> Ring r         by FiniteField_def, field_is_ring
     and prime (char r)             by finite_field_char
   The result is true               by poly_freshman_all
*)
val poly_field_freshman_all = store_thm(
  "poly_field_freshman_all",
  ``!r:'a field. FiniteField r ==> !x y. poly x /\ poly y ==>
    !n. (x + y) ** (char r ** n) = x ** (char r ** n) + y ** (char r ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  rw[poly_freshman_all]);

(* Theorem: FiniteField r ==> !x y. poly x /\ poly y ==>
            ((x + y) ** (CARD R) = x ** (CARD R) + y ** (CARD R)) *)
(* Proof:
   Since FiniteField r
     ==> Field r ==> Ring r         by FiniteField_def, field_is_ring
     and prime (char r)             by finite_field_char
     and ?n. 0 < n /\ (CARD R = char r ** n)   by finite_field_card
   The result follows               by poly_freshman_all
   also result follows              by poly_field_freshman_all
*)
val poly_freshman_card = store_thm(
  "poly_freshman_card",
  ``!r:'a field. FiniteField r ==> !x y. poly x /\ poly y ==>
       ((x + y) ** (CARD R) = x ** (CARD R) + y ** (CARD R))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?n. 0 < n /\ (CARD R = char r ** n)` by rw[finite_field_card] >>
  rw[poly_freshman_all]);

(* Theorem: FiniteField r ==> !x y. poly x /\ poly y ==>
            !n. (x + y) ** (CARD R ** n) = x ** (CARD R ** n) + y ** (CARD R ** n) *)
(* Proof:
   Since FiniteField r
     ==> Field r ==> Ring r         by FiniteField_def, field_is_ring
     and prime (char r)             by finite_field_char
     and ?d. 0 < d /\ (CARD R = char r ** d)  by finite_field_card
   hence CARD R ** n
       = (char r ** d) ** n
       = char r ** (d * n)          by EXP_EXP_MULT
   The result follows               by poly_freshman_all
*)
val poly_freshman_card_all = store_thm(
  "poly_freshman_card_all",
  ``!r:'a field. FiniteField r ==> !x y. poly x /\ poly y ==>
   !n. (x + y) ** (CARD R ** n) = x ** (CARD R ** n) + y ** (CARD R ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?d. 0 < d /\ (CARD R = char r ** d)` by rw[finite_field_card] >>
  `CARD R ** n = char r ** (d * n)` by rw[EXP_EXP_MULT] >>
  rw[poly_freshman_all]);

(* Theorem: FiniteField r ==> !f. rfun f ==> !p. poly p ==>
            !n. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (CARD R)
               = poly_sum (GENLIST (\j. (f j * p ** j) ** (CARD R)) n) *)
(* Proof:
   Since prime (char r)                        by finite_field_char
     and ?d. 0 < d /\ (CARD R = char r ** d)   by finite_field_card
   The result follows                          by poly_sum_freshman_all
*)
val poly_sum_freshman_card = store_thm(
  "poly_sum_freshman_card",
  ``!r:'a field. FiniteField r ==> !f. rfun f ==> !p. poly p ==>
   !n. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (CARD R)
      = poly_sum (GENLIST (\j. (f j * p ** j) ** (CARD R)) n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?d. 0 < d /\ (CARD R = char r ** d)` by rw[finite_field_card] >>
  rw[poly_sum_freshman_all]);

(* Theorem: FiniteField r ==> !f. rfun f ==> !p. poly p ==>
            !n. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (CARD R)
               = poly_sum (GENLIST (\j. (f j * p ** j) ** (CARD R)) n) *)
(* Proof:
   Since prime (char r)                        by finite_field_char
     and ?d. 0 < d /\ (CARD R = char r ** d)   by finite_field_card
   hence CARD R ** n
       = (char r ** d) ** n
       = char r ** (d * n)          by EXP_EXP_MULT
   The result follows               by poly_sum_freshman_all
*)
val poly_sum_freshman_card_all = store_thm(
  "poly_sum_freshman_card_all",
  ``!r:'a field. FiniteField r ==> !f. rfun f ==> !p. poly p ==>
   !n k. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (CARD R ** k)
        = poly_sum (GENLIST (\j. (f j * p ** j) ** (CARD R ** k)) n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?d. 0 < d /\ (CARD R = char r ** d)` by rw[finite_field_card] >>
  `CARD R ** k = char r ** (d * k)` by rw[EXP_EXP_MULT] >>
  rw[poly_sum_freshman_all]);

(* Note: the following theorem needs two things:
   poly_sum_freshman_thm, a ring-theoretic theorem, true when (char r) is prime.
   finite_field_fermat_thm, a group-theoretic theorem, true for (CARD R), non-prime is Euler-Fermat.
   However, poly_sum_freshman_thm can be raised to poly_sum_freshman_card,
   since CARD R = (char r) ** d for a FiniteField r.
   Hence: FiniteRing r provides the environment to apply both theorems.
*)

(* Theorem: FiniteField r ==> !p q. poly p /\ poly q ==> (peval p q ** CARD R = peval p (q ** CARD R)) *)
(* Proof:
   Let m = CARD R.
   Note rfun (\k. p ' k)     by ring_fun_def, poly_coeff_element
    and !k. p ' k IN R       by poly_coeff_element
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_card
   = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))        by finite_field_fermat_thm
   = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val poly_peval_freshman_card = store_thm(
  "poly_peval_freshman_card",
  ``!r:'a field. FiniteField r ==>
   !p q. poly p /\ poly q ==> ((peval p q) ** CARD R = peval p (q ** CARD R))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R` >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by rw[poly_sum_freshman_card, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[finite_field_fermat_thm, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p q. poly p /\ poly q ==>
            !n. peval p q ** (CARD R ** n) = peval p (q ** (CARD R ** n)) *)
(* Proof:
   Let m = CARD R ** n.
   Note rfun (\k. p ' k)     by ring_fun_def, poly_coeff_element
    and !k. p ' k IN R       by poly_coeff_element
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_card_all
   = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))        by finite_field_fermat_all
   = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val poly_peval_freshman_card_all = store_thm(
  "poly_peval_freshman_card_all",
  ``!r:'a field. FiniteField r ==>
   !p q. poly p /\ poly q ==> !n. (peval p q) ** (CARD R ** n) = peval p (q ** (CARD R ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R ** n` >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by rw[poly_sum_freshman_card_all, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[finite_field_fermat_all, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p. poly p ==> (p ** (CARD R) = peval p (X ** (CARD R))) *)
(* Proof:
   Given FiniteField r
     ==> Ring r /\ #1 <> #0           by field_is_ring, field_one_ne_zero
      so poly X                       by poly_X
     and p = peval p X                by poly_peval_by_X
   The result follows by ptting q = X in poly_peval_freshman_card
*)
val poly_peval_fermat_thm = store_thm(
  "poly_peval_fermat_thm",
  ``!r:'a field. FiniteField r ==> !p. poly p ==> (p ** (CARD R) = peval p (X ** (CARD R)))``,
  metis_tac[poly_peval_freshman_card, poly_X, poly_peval_by_X,
   FiniteField_def, field_is_ring, field_one_ne_zero]);

(* Theorem: FiniteField r ==> !p. poly p ==> !n. p ** (CARD R ** n) = peval p (X ** (CARD R ** n)) *)
(* Proof:
   Given FiniteField r
     ==> Ring r /\ #1 <> #0           by field_is_ring, field_one_ne_zero
      so poly X                       by poly_X
     and p = peval p X                by poly_peval_by_X
   The result follows by ptting q = X in poly_peval_freshman_card_all
*)
val poly_peval_fermat_all = store_thm(
  "poly_peval_fermat_all",
  ``!r:'a field. FiniteField r ==> !p. poly p ==>
   !n. p ** (CARD R ** n) = peval p (X ** (CARD R ** n))``,
  metis_tac[poly_peval_freshman_card_all, poly_X, poly_peval_by_X,
            FiniteField_def, field_is_ring, field_one_ne_zero]);

(* Theorem: FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
            !n. rsum (GENLIST (\j. f j * x ** j) n) ** CARD R =
                rsum (GENLIST (\j. (f j * x ** j) ** CARD R) n) *)
(* Proof:
   Since prime (char r)                        by finite_field_char
     and ?d. 0 < d /\ (CARD R = char r ** d)   by finite_field_card
   The result follows                          by ring_sum_freshman_all
*)
val ring_sum_freshman_card = store_thm(
  "ring_sum_freshman_card",
  ``!r:'a field. FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
   !n. rsum (GENLIST (\j. f j * x ** j) n) ** CARD R =
       rsum (GENLIST (\j. (f j * x ** j) ** CARD R) n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?d. 0 < d /\ (CARD R = char r ** d)` by rw[finite_field_card] >>
  rw_tac std_ss[ring_sum_freshman_all]);

(* Theorem: FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
            !n k. (rsum (GENLIST (\j. f j * x ** j) n)) ** (CARD R ** k)
                 = rsum (GENLIST (\j. (f j * x ** j) ** (CARD R ** k)) n) *)
(* Proof:
   Since prime (char r)                        by finite_field_char
     and ?d. 0 < d /\ (CARD R = char r ** d)   by finite_field_card
   hence CARD R ** n
       = (char r ** d) ** n
       = char r ** (d * n)          by EXP_EXP_MULT
   The result follows               by ring_sum_freshman_all
*)
val ring_sum_freshman_card_all = store_thm(
  "ring_sum_freshman_card_all",
  ``!r:'a field. FiniteField r ==> !f. rfun f ==> !x. x IN R ==>
   !n k. (rsum (GENLIST (\j. f j * x ** j) n)) ** (CARD R ** k)
        = rsum (GENLIST (\j. (f j * x ** j) ** (CARD R ** k)) n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `prime (char r)` by rw[finite_field_char] >>
  `?d. 0 < d /\ (CARD R = char r ** d)` by rw[finite_field_card] >>
  `CARD R ** k = char r ** (d * k)` by rw[EXP_EXP_MULT] >>
  rw_tac std_ss[ring_sum_freshman_all]);

(* Theorem: FiniteField r ==> !p x. poly p /\ x IN R ==> (eval p x ** CARD R = eval p (x ** CARD R)) *)
(* Proof:
   Let m = CARD R.
   Note rfun (\k. p ' k)     by ring_fun_def, poly_coeff_element
    and !k. p ' k IN R       by poly_coeff_element
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_card
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by finite_field_fermat_thm
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val poly_eval_freshman_card = store_thm(
  "poly_eval_freshman_card",
  ``!r:'a field. FiniteField r ==> !p x. poly p /\ x IN R ==>
         ((eval p x) ** (CARD R) = eval p (x ** (CARD R)))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R` >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by rw[ring_sum_freshman_card, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[finite_field_fermat_thm, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p x. poly p /\ x IN R ==>
            !n. (eval p x) ** (CARD R ** n) = eval p (x ** (CARD R ** n)) *)
(* Proof:
   Let m = CARD R ** n.
   Note rfun (\k. p ' k)     by ring_fun_def, poly_coeff_element
    and !k. p ' k IN R       by poly_coeff_element
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_card_all
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by finite_field_fermat_all
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val poly_eval_freshman_card_all = store_thm(
  "poly_eval_freshman_card_all",
  ``!r:'a field. FiniteField r ==> !p x. poly p /\ x IN R ==>
   !n. (eval p x) ** (CARD R ** n) = eval p (x ** (CARD R ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R ** n` >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by rw[ring_sum_freshman_card_all, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[finite_field_fermat_all, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Polynomial Theorems                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==>
            !p q. poly p /\ poly q /\ (p ** (char r) = q ** (char r)) ==> (p = q) *)
(* Proof:
   Let m = char r.
   Given  p ** m = q ** m
      so  p ** m - q ** m = 0
      or (p - q) ** m = 0           by poly_freshman_thm_sub
   hence (p - q) = |0|              by poly_exp_eq_zero
      or p = q                      by poly_sub_eq_zero
*)
val poly_char_exp_eq = store_thm(
  "poly_char_exp_eq",
  ``!r:'a field. FiniteField r ==>
    !p q. poly p /\ poly q /\ (p ** (char r) = q ** (char r)) ==> (p = q)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = char r` >>
  `Ring r /\ prime m` by rw[finite_field_char, Abbr`m`] >>
  `|0| = (p - q) ** m` by metis_tac[poly_sub_eq_zero, poly_exp_poly, poly_freshman_thm_sub] >>
  metis_tac[poly_exp_eq_zero, poly_sub_poly, poly_sub_eq_zero]);

(* Theorem: FiniteField r ==> !p. poly p ==> (p ** CARD R =
            poly_sum (GENLIST (\k. (p ' k) ** (CARD R) * (X ** (CARD R)) ** k) (SUC (deg p)))) *)
(* Proof:
   Let m = CARD R, c = char r, n = SUC (deg p).
   Then prime c                       by finite_field_char
    and ?h. 0 < h /\ (m = c ** h)     by finite_field_card
   First, show: (\k. (p ' k * X ** k) ** m) = (\k. (p ' k) ** m * (X ** m) ** k)   [1]
      By FUN_EQ_THM, this is to show: (p ' k * X ** k) ** m = p ' k ** m * (X ** m) ** k
      Note p ' k IN R                  by poly_coeff_element
        (p ' k * X ** k) ** m
      = (p ' k) ** m * (X ** k) ** m   by poly_cmult_exp
      = (p * k) ** m * (X ** m) ** k   by poly_exp_mult_comm
   Let f = \k. p ' k.
   Then rfun f                                       by poly_coeff_ring_fun
    and (\j. f j * X ** j) = (\k. p ' k * X ** k)    by FUN_EQ_THM
   Hence  p ** m
        = (poly_sum (GENLIST (\k. p ' k * X ** k) n)) ** m          by poly_eq_poly_sum, rfun f
        = poly_sum (GENLIST (\k. (p ' k * X ** k) ** m) n)          by poly_sum_freshman_all
        = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)   by [1]
*)
val poly_sum_fermat_thm = store_thm(
  "poly_sum_fermat_thm",
  ``!r:'a field. FiniteField r ==> !p. poly p ==>
   (p ** CARD R = poly_sum (GENLIST (\k. (p ' k) ** (CARD R) * (X ** (CARD R)) ** k) (SUC (deg p))))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R` >>
  `poly X /\ poly (X ** m)` by rw[] >>
  qabbrev_tac `c = char r` >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `?h. 0 < h /\ (m = c ** h)` by rw[finite_field_card, Abbr`m`, Abbr`c`] >>
  qabbrev_tac `n = SUC (deg p)` >>
  `(\k. (p ' k * X ** k) ** m) = (\k. (p ' k) ** m * (X ** m) ** k)` by
  (rw_tac std_ss[FUN_EQ_THM] >>
  rw[poly_cmult_exp, poly_exp_mult_comm]) >>
  qabbrev_tac `f = \k. p ' k` >>
  `rfun f` by rw[poly_coeff_ring_fun, Abbr`f`] >>
  `(\j. f j * X ** j) = (\k. p ' k * X ** k)` by rw[Abbr`f`] >>
  `p = poly_sum (GENLIST (\k. p ' k * X ** k) n)` by rw[poly_eq_poly_sum, Abbr`n`] >>
  `p ** m = poly_sum (GENLIST (\k. (p ' k * X ** k) ** m) n)` by metis_tac[poly_sum_freshman_all] >>
  rw[]);


(* Theorem: FiniteField r ==> !p z. poly p /\ z IN R /\ root p z ==> !n. root p (z ** CARD R ** n) *)
(* Proof:
   Simply by finite_field_fermat_all,
   !r. FiniteField r ==> !x. x IN R ==> !n. x ** CARD R ** n = x
*)
val poly_root_exp = store_thm(
  "poly_root_exp",
  ``!r:'a field. FiniteField r ==> !p z. poly p /\ z IN R /\ root p z ==> !n. root p (z ** CARD R ** n)``,
  rw[finite_field_fermat_all]);

(* Note:
   This result is trivial: since by finite_field_fermat_all,
   |- !r. FiniteField r ==> !x. x IN R ==> !n. x ** CARD R ** n = x
   Indeed, by finite_field_fermat_thm, |- !r. FiniteField r ==> !x. x IN R ==> (x ** CARD R = x)
   It is trivially true that: poly p /\ z IN R /\ root p z ==> root p (z ** CARD R)

   However, by finite_field_card, |- !r. FiniteField r ==> ?d. CARD R = char r ** d
   This means: poly p /\ z IN R /\ root p z ==> root p (z ** char r ** d)   is trivial,
   But how about the elements: z, z ** char r, z ** char r ** 2, z ** char r ** 3, etc.
   until z ** char r ** d = z, when things wrap around?

   The fundamental result (or Fermat's little trick) is this:
   For pfpoly p, z IN R, if root p z, then root p (z ** char r ** j)  for j = 0..{d-1} (or 1..d).
   This is due to finite_field_prime_field_card, |- !r. FiniteField r ==> (CARD Fp = char r)
   Thus enabling the application of Freshman Theorem (for z IN R with exponent char r)
   and Fermat's Little Theorem (for p ' k in Fp with exponent CARD Fp = char r)
   at the same time.
*)

(* Next is nontrivial. *)
(* Note: pfpoly p, not poly p; and x IN R, not x IN Fp *)

(* Theorem: FiniteField r ==> !x. x IN Fp ==> (x ** char r = x) *)
(* Proof:
   Note FiniteField (PF r)        by prime_field_finite_field
    and CARD Fp = char r          by prime_field_card
    and (PF r).prod.exp = $**     by PF_property
   Hence x ** char r = x          by finite_field_fermat_thm
*)
val prime_field_fermat_thm = store_thm(
  "prime_field_fermat_thm",
  ``!r:'a field. FiniteField r ==> !x. x IN Fp ==> (x ** char r = x)``,
  metis_tac[prime_field_finite_field, prime_field_card, finite_field_fermat_thm, PF_property]);

(* Theorem: FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x *)
(* Proof:
   Note FiniteField (PF r)        by prime_field_finite_field
    and CARD Fp = char r          by prime_field_card
    and (PF r).prod.exp = $**     by PF_property
   Hence x ** char r ** n = x     by finite_field_fermat_all
*)
val prime_field_fermat_all = store_thm(
  "prime_field_fermat_all",
  ``!r:'a field. FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x``,
  metis_tac[prime_field_finite_field, prime_field_card, finite_field_fermat_all, PF_property]);

(* Theorem: FiniteField r ==> !p x. pfpoly p /\ x IN R ==> (eval p x ** char r = eval p (x ** char r)) *)
(* Proof:
   Let m = char r.
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note Ring (PF r)               by prime_field_field, field_is_ring
     and pfpoly p ==> poly p       by poly_prime_field_element_poly
     and pfcoeff p k = p ' k       by poly_prime_field_coeff
   Since pfcoeff p k IN Fp         by poly_coeff_element, Ring (PF r), prime m
    thus p ' k IN Fp               by p ' k = pfcoeff p k
     and !k. (p ' k) ** m = p ' k  by prime_field_fermat_thm, [1]
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_thm
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val poly_eval_freshman_thm = store_thm(
  "poly_eval_freshman_thm",
  ``!r:'a field. FiniteField r ==> !p x. pfpoly p /\ x IN R ==>
         ((eval p x) ** (char r) = eval p (x ** (char r)))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = char r` >>
  `prime m` by rw[finite_field_char, Abbr`m`] >>
  `poly p` by rw[poly_prime_field_element_poly] >>
  `Ring (PF r)` by rw[prime_field_field] >>
  `!k. p ' k IN Fp` by metis_tac[poly_coeff_element, poly_prime_field_coeff] >>
  `!k. (p ' k) ** m = p ' k` by metis_tac[prime_field_fermat_thm] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by rw[ring_sum_freshman_thm, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p x. pfpoly p /\ x IN R ==>
            !n. (eval p x) ** (char r ** n) = eval p (x ** (char r ** n)) *)
(* Proof:
   Let m = char r ** n.
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note Ring (PF r)               by prime_field_field, field_is_ring
     and pfpoly p ==> poly p       by poly_prime_field_element_poly
     and pfcoeff p k = p ' k       by poly_prime_field_coeff
   Since pfcoeff p k IN Fp         by poly_coeff_element, Ring (PF r), prime (char r)
    thus p ' k IN Fp               by p ' k = pfcoeff p k
     and !k. (p ' k) ** m = p ' k  by prime_field_fermat_all, [1]
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_all
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val poly_eval_freshman_all = store_thm(
  "poly_eval_freshman_all",
  ``!r:'a field. FiniteField r ==> !p x. pfpoly p /\ x IN R ==>
   !n. (eval p x) ** (char r ** n) = eval p (x ** (char r ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = char r ** n` >>
  `prime (char r)` by rw[finite_field_char] >>
  `poly p` by rw[poly_prime_field_element_poly] >>
  `Ring (PF r)` by rw[prime_field_field] >>
  `!k. p ' k IN Fp` by metis_tac[poly_coeff_element, poly_prime_field_coeff] >>
  `!k. (p ' k) ** m = p ' k` by metis_tac[prime_field_fermat_all] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by rw[ring_sum_freshman_all, Abbr`m`] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p q. pfpoly p /\ poly q ==>
            ((peval p q) ** (char r) = peval p (q ** (char r))) *)
(* Proof:
   Let m = char r.
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note Ring (PF r)               by prime_field_field, field_is_ring
     and pfpoly p ==> poly p       by poly_prime_field_element_poly
     and pfcoeff p k = p ' k       by poly_prime_field_coeff
   Since pfcoeff p k IN Fp         by poly_coeff_element, Ring (PF r), prime m
    thus p ' k IN Fp               by p ' k = pfcoeff p k
     and !k. (p ' k) ** m = p ' k  by prime_field_fermat_thm, [1]
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_thm
   = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))        by [1]
   = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val poly_peval_freshman_thm = store_thm(
  "poly_peval_freshman_thm",
  ``!r:'a field. FiniteField r ==> !p q. pfpoly p /\ poly q ==>
         ((peval p q) ** (char r) = peval p (q ** (char r)))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = char r` >>
  `prime m` by rw[finite_field_char, Abbr`m`] >>
  `poly p` by rw[poly_prime_field_element_poly] >>
  `Ring (PF r)` by rw[prime_field_field] >>
  `!k. p ' k IN Fp` by metis_tac[poly_coeff_element, poly_prime_field_coeff] >>
  `!k. (p ' k) ** m = p ' k` by metis_tac[prime_field_fermat_thm] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by rw[poly_sum_freshman_thm, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);

(* Theorem: FiniteField r ==> !p q. pfpoly p /\ poly q ==>
            !n. (peval p q) ** (char r ** n) = peval p (q ** (char r ** n)) *)
(* Proof:
   Let m = char r ** n.
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note Ring (PF r)               by prime_field_field, field_is_ring
     and pfpoly p ==> poly p       by poly_prime_field_element_poly
     and pfcoeff p k = p ' k       by poly_prime_field_coeff
   Since pfcoeff p k IN Fp         by poly_coeff_element, Ring (PF r), prime (char r)
    thus p ' k IN Fp               by p ' k = pfcoeff p k
     and !k. (p ' k) ** m = p ' k  by prime_field_fermat_all, [1]
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_all
   = poly_sum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = poly_sum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val poly_peval_freshman_all = store_thm(
  "poly_peval_freshman_all",
  ``!r:'a field. FiniteField r ==> !p q. pfpoly p /\ poly q ==>
   !n. (peval p q) ** (char r ** n) = peval p (q ** (char r ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = char r ** n` >>
  `prime (char r)` by rw[finite_field_char] >>
  `poly p` by rw[poly_prime_field_element_poly] >>
  `Ring (PF r)` by rw[prime_field_field] >>
  `!k. p ' k IN Fp` by metis_tac[poly_coeff_element, poly_prime_field_coeff] >>
  `!k. (p ' k) ** m = p ' k` by metis_tac[prime_field_fermat_all] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by rw[poly_sum_freshman_all, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Roots of Prime Field Polynomials                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !p z. pfpoly p /\ z IN R /\ root p z ==>
            !n. root p (z ** char r ** n) *)
(* Proof:
   Since FiniteField r
     ==> prime (char r)                 by finite_field_char
     ==> 0 < char r                     by PRIME_POS
     ==> char r ** n <> 0               by EXP_NONZERO, char r <> 0
   Given root p z
     ==> eval p z = #0                  by poly_root_def
     Now eval p (z ** char r ** n)
       = (eval p z) ** char r ** n      by poly_eval_freshman_all
       = #0 ** char r ** n              by above
       = #0                             by field_zero_exp, char r ** n <> 0
   Hence root p (z ** char r ** n)      by poly_root_def
*)
val poly_prime_field_roots = store_thm(
  "poly_prime_field_roots",
  ``!r:'a field. FiniteField r ==> !p z. pfpoly p /\ z IN R /\ root p z ==>
   !n. root p (z ** char r ** n)``,
  rw[poly_root_def, GSYM poly_eval_freshman_all] >>
  `prime (char r)` by rw[finite_field_char] >>
  `0 < char r` by rw[PRIME_POS] >>
  `char r <> 0` by decide_tac >>
  `char r ** n <> 0` by rw[EXP_NONZERO] >>
  `Field r` by metis_tac[FiniteField_def] >>
  rw[field_zero_exp]);

(*
> poly_irreducible_poly;
val it = |- !r p. ipoly p ==> poly p: thm
> poly_irreducible_poly |> SPEC ``PF r``;
val it = |- !p. irreducible (PolyRing (PF r)) p ==> pfpoly p: thm
val it = |- !p. pfipoly p ==> pfpoly p: thm
*)

(* ------------------------------------------------------------------------- *)
(* Roots of Subfield Polynomials                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN B ==> (x ** (CARD B) = x) *)
(* Proof:
   Note FiniteField s              by subfield_finite_field
   Hence s.exp x (CARD B) = x      by finite_field_fermat_thm
      or x ** (CARD B) = x         by subfield_exp
*)
val subfield_fermat_thm = store_thm(
  "subfield_fermat_thm",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN B ==> (x ** (CARD B) = x)``,
  metis_tac[subfield_finite_field, finite_field_fermat_thm, subfield_exp]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN B ==> !n. x ** (CARD B) ** n = x *)
(* Proof:
   Note FiniteField s                by subfield_finite_field
   Hence s.exp x (CARD B ** n) = x   by finite_field_fermat_all
      or x ** (CARD B) ** n = x      by subfield_exp
*)
val subfield_fermat_all = store_thm(
  "subfield_fermat_all",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN B ==> !n. x ** (CARD B) ** n = x``,
  metis_tac[subfield_finite_field, finite_field_fermat_all, subfield_exp]);

(* Theorem: FiniteField r /\ s <<= r ==> !p. Poly s p ==>
            !x. x IN R ==> ((eval p x) ** (CARD B) = eval p (x ** (CARD B))) *)
(* Proof:
   Let m = CARD B.
    Note ?d. 0 < d /\ (m = (char r) ** d)  by finite_field_subfield_card
     and prime (char r)            by finite_field_char
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note s <= r /\ Ring s          by subfield_is_subring
     and Poly s p ==> poly p       by subring_poly_poly
     and poly_coeff s p k = p ' k  by subring_poly_coeff
   Since poly_coeff s p k IN B     by poly_coeff_element, Ring s
    thus p ' k IN B                by p ' k = poly_coeff s p k
     and !k. (p ' k) ** m = p ' k  by subfield_fermat_thm, [1]
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_all
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val subfield_poly_eval_freshman_thm = store_thm(
  "subfield_poly_eval_freshman_thm",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. Poly s p ==>
   !x. x IN R ==> ((eval p x) ** (CARD B) = eval p (x ** (CARD B)))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD B` >>
  `?d. 0 < d /\ (m = (char r) ** d)` by rw[finite_field_subfield_card, Abbr`m`] >>
  `prime (char r)` by rw[finite_field_char] >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `!k. p ' k IN B` by metis_tac[poly_coeff_element, subring_poly_coeff] >>
  `!k. (p ' k) ** m = p ' k` by rw[subfield_fermat_thm, Abbr`m`] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by metis_tac[ring_sum_freshman_all] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* Theorem: FiniteField r /\ s <<= r ==> !p. Poly s p ==>
            !x. x IN R ==> !n. (eval p x) ** ((CARD B) ** n) = eval p (x ** ((CARD B) ** n)) *)
(* Proof:
   Let m = CARD B ** n.
    Note ?d. 0 < d /\ (CARD B = (char r) ** d)  by finite_field_subfield_card
      so m = (char r) ** (d * n)     by EXP_EXP_MULT
     and prime (char r)              by finite_field_char
    Note rfun (\k. p ' k)            by ring_fun_def, poly_coeff_element
    Note s <= r /\ Ring s            by subfield_is_subring
     and Poly s p ==> poly p         by subring_poly_poly
     and poly_coeff s p k = p ' k    by subring_poly_coeff
   Since poly_coeff s p k IN B       by poly_coeff_element, Ring s
    thus p ' k IN B                  by p ' k = poly_coeff s p k
     and !k. (p ' k) ** m = p ' k    by subfield_fermat_all, [1]
     (eval p x) ** m
   = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_eval_by_ring_sum
   = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by ring_sum_freshman_all
   = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by ring_mult_exp
   = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by ring_exp_mult, MULT_COMM
   = eval p (x ** m)                                                   by poly_eval_by_ring_sum
*)
val subfield_poly_eval_freshman_all = store_thm(
  "subfield_poly_eval_freshman_all",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. Poly s p ==>
   !x. x IN R ==> !n. (eval p x) ** ((CARD B) ** n) = eval p (x ** ((CARD B) ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD B ** n` >>
  `?d. 0 < d /\ (CARD B = (char r) ** d)` by rw[finite_field_subfield_card, Abbr`m`] >>
  `m = (char r) ** (d * n)` by rw[EXP_EXP_MULT, Abbr`m`] >>
  `prime (char r)` by rw[finite_field_char] >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `!k. p ' k IN B` by metis_tac[poly_coeff_element, subring_poly_coeff] >>
  `!k. (p ' k) ** m = p ' k` by rw[subfield_fermat_all, Abbr`m`] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(eval p x) ** m = (rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m` by rw[poly_eval_by_ring_sum] >>
  `_ = rsum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))` by metis_tac[ring_sum_freshman_all] >>
  `_ = rsum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))` by rw[ring_mult_exp] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = rsum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM ring_exp_mult, MULT_COMM] >>
  `_ = eval p (x ** m)` by rw[poly_eval_by_ring_sum] >>
  rw[]);

(* Theorem: FiniteField r /\ s <<= r ==> !p q. Poly s p /\ poly q ==>
            ((peval p q) ** (CARD B) = peval p (q ** (CARD B))) *)
(* Proof:
   Let m = CARD B.
    Note ?d. 0 < d /\ (m = (char r) ** d)  by finite_field_subfield_card
     and prime (char r)            by finite_field_char
    Note rfun (\k. p ' k)          by ring_fun_def, poly_coeff_element
    Note s <= r /\ Ring s          by subfield_is_subring
     and Poly s p ==> poly p       by subring_poly_poly
     and poly_coeff s p k = p ' k  by subring_poly_coeff
   Since poly_coeff s p k IN B     by poly_coeff_element, Ring s
    thus p ' k IN B                by p ' k = poly_coeff s p k
     and !k. (p ' k) ** m = p ' k  by subfield_fermat_thm, [1]
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_all
   = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))        by [1]
   = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val subfield_poly_peval_freshman_thm = store_thm(
  "subfield_poly_peval_freshman_thm",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p q. Poly s p /\ poly q ==>
         ((peval p q) ** (CARD B) = peval p (q ** (CARD B)))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD B` >>
  `?d. 0 < d /\ (m = (char r) ** d)` by rw[finite_field_subfield_card, Abbr`m`] >>
  `prime (char r)` by rw[finite_field_char] >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `!k. p ' k IN B` by metis_tac[poly_coeff_element, subring_poly_coeff] >>
  `!k. (p ' k) ** m = p ' k` by rw[subfield_fermat_thm, Abbr`m`] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by metis_tac[poly_sum_freshman_all, Abbr`m`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);

(* Theorem: FiniteField r /\ s <<= r ==> !p q. Poly s p /\ poly q ==>
            !n. (peval p q) ** (CARD B ** n) = peval p (q ** (CARD B ** n)) *)
(* Proof:
   Let m = CARD B ** n.
    Note ?d. 0 < d /\ (CARD B = (char r) ** d)  by finite_field_subfield_card
      so m = (char r) ** (d * n)     by EXP_EXP_MULT
     and prime (char r)              by finite_field_char
    Note rfun (\k. p ' k)            by ring_fun_def, poly_coeff_element
    Note s <= r /\ Ring s            by subfield_is_subring
     and Poly s p ==> poly p         by subring_poly_poly
     and poly_coeff s p k = p ' k    by subring_poly_coeff
   Since poly_coeff s p k IN B       by poly_coeff_element, Ring s
    thus p ' k IN B                  by p ' k = poly_coeff s p k
     and !k. (p ' k) ** m = p ' k    by subfield_fermat_all, [1]
     (peval p q) ** m
   = (poly_sum (GENLIST (\k. p ' k * x ** k) (SUC (deg p)))) ** m          by poly_peval_by_poly_sum
   = poly_sum (GENLIST (\k. (p ' k * x ** k) ** m) (SUC (deg p)))          by poly_sum_freshman_all
   = poly_sum (GENLIST (\k. (p ' k) ** m * (x ** k) ** m) (SUC (deg p)))   by poly_cmult_exp
   = poly_sum (GENLIST (\k. (p ' k) * (x ** k) ** m) (SUC (deg p)))        by [1]
   = poly_sum (GENLIST (\k. (p ' k) * (x ** m) ** k) (SUC (deg p)))        by poly_exp_mult, MULT_COMM
   = peval p (q ** m)                                                      by poly_peval_by_poly_sum
*)
val subfield_poly_peval_freshman_all = store_thm(
  "subfield_poly_peval_freshman_all",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p q. Poly s p /\ poly q ==>
   !n. (peval p q) ** (CARD B ** n) = peval p (q ** (CARD B ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD B ** n` >>
  `?d. 0 < d /\ (CARD B = (char r) ** d)` by rw[finite_field_subfield_card, Abbr`m`] >>
  `m = (char r) ** (d * n)` by rw[EXP_EXP_MULT, Abbr`m`] >>
  `prime (char r)` by rw[finite_field_char] >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `!k. p ' k IN B` by metis_tac[poly_coeff_element, subring_poly_coeff] >>
  `!k. (p ' k) ** m = p ' k` by rw[subfield_fermat_all, Abbr`m`] >>
  `rfun (\k. p ' k)` by metis_tac[ring_fun_def, poly_coeff_element] >>
  `(peval p q) ** m = (poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p)))) ** m` by rw[poly_peval_by_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * q ** k) ** m) (SUC (deg p)))` by metis_tac[poly_sum_freshman_all] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (q ** k) ** m) (SUC (deg p)))` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** k) ** m) (SUC (deg p)))` by rw[] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) * (q ** m) ** k) (SUC (deg p)))` by rw_tac std_ss[GSYM poly_exp_mult, MULT_COMM] >>
  `_ = peval p (q ** m)` by rw[poly_peval_by_poly_sum] >>
  rw[]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
