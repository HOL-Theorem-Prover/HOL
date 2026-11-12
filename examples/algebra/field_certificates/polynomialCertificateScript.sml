(* -------------------------------------------------------------------------
   Polynomial certificate checking theorems

   Documentation
   Check bounded identities instead of evaluating abstract polynomial
   division or expanding large powers. Polynomial lists have ascending
   coefficients and canonical zero []; the results below are over abstract
   rings/fields, with Poly and monicity obligations explicit in each theorem.

   Public interface
   - polynomial_certificate_remainder checks a = q*f+b and the degree bound.
   - polynomial_certificate_pow_even / polynomial_certificate_pow_odd and
     polynomial_certificate_frobenius_compose support modular powering.
   - polynomial_certificate_bezout and polynomial_certificate_no_roots
     turn checked Bezout/remainder witnesses into factor or root exclusions.
   - polynomial_certificate_rabin12 proves degree-twelve irreducibility
     over a FiniteField, using Frobenius tests at degrees 4, 6 and 12.

   ML supplies candidate quotients, remainders and Bezout coefficients;
   these theorems require their identities to be proved in HOL.
   ------------------------------------------------------------------------- *)

Theory polynomialCertificate
Ancestors
  ffMaster polyIrreducible polyDivides polyDivision polyRoot
  polyMonic polyRing polyRingModulo ffPoly fieldInstances arithmetic divides

open fieldTheory ringTheory polynomialTheory polyWeakTheory pred_setTheory

(* Only bounded polynomial identities are computed by the certificate library.
   The quotient/remainder operations themselves are specified abstractly in HOL. *)
Theorem polynomial_certificate_pow_even:
  !r:'a ring. Ring r ==> !a f n.
    Poly r a /\ poly_monic r f /\ 0 < poly_deg r f ==>
    (a ** (2*n)) % f = (((a ** n) % f) * ((a ** n) % f)) % f
Proof
  rpt strip_tac >>
  `2*n = n+n` by decide_tac >>
  asm_simp_tac std_ss [poly_exp_add] >>
  metis_tac[poly_mod_mult, poly_exp_poly, poly_monic_ulead]
QED

Theorem polynomial_certificate_pow_odd:
  !r:'a ring. Ring r ==> !a f n.
    Poly r a /\ poly_monic r f /\ 0 < poly_deg r f ==>
    (a ** (2*n+1)) % f =
      ((a % f) * ((((a ** n) % f) * ((a ** n) % f)) % f)) % f
Proof
  rpt strip_tac >>
  `2*n+1 = SUC (2*n)` by decide_tac >>
  asm_simp_tac std_ss [poly_exp_SUC] >>
  metis_tac[poly_mod_mult, polynomial_certificate_pow_even,
            poly_exp_poly, poly_monic_ulead]
QED

Theorem polynomial_certificate_remainder:
  !r:'a ring. Ring r ==> !a f q b.
    Poly r a /\ poly_monic r f /\ Poly r q /\ Poly r b /\
    a = q*f+b /\ poly_deg r b < poly_deg r f ==>
    a % f = b
Proof
  metis_tac[poly_mod_unique, poly_monic_ulead]
QED

(* Frobenius fixes every coefficient.  Thus two checked remainders at
   indices m and n compose to the remainder at m+n, without expanding
   the much larger exponent CARD r.carrier ** (m+n). *)
Theorem polynomial_certificate_frobenius_compose:
  !r:'a field. FiniteField r ==> !f a b m n.
    poly_monic r f /\ Poly r a /\ Poly r b /\
    (X ** (CARD r.carrier ** m)) % f = a /\
    (X ** (CARD r.carrier ** n)) % f = b ==>
    (X ** (CARD r.carrier ** (m+n))) % f =
      (poly_peval r a b) % f
Proof
  rpt strip_tac >>
  `Ring r /\ ulead f`
    by metis_tac[FiniteField_def, field_is_ring, poly_monic_ulead] >>
  `Poly r X /\ Poly r (X ** (CARD r.carrier ** m)) /\
   Poly r (X ** (CARD r.carrier ** n))` by simp[] >>
  `(X ** (CARD r.carrier ** (m+n))) % f =
   ((X ** (CARD r.carrier ** m)) ** (CARD r.carrier ** n)) % f`
    by simp[EXP_ADD, poly_exp_mult] >>
  `_ = (a ** (CARD r.carrier ** n)) % f`
    by metis_tac[poly_mod_exp] >>
  `_ = (poly_peval r a (X ** (CARD r.carrier ** n))) % f`
    by metis_tac[poly_peval_fermat_all] >>
  metis_tac[poly_peval_mod]
QED

Theorem polynomial_certificate_bezout:
  !r:'a field. Field r ==> !f a b u v h.
    poly_monic r f /\ poly_monic r h /\ 0 < poly_deg r h /\
    Poly r a /\ Poly r b /\ Poly r u /\ Poly r v /\
    h pdivides f /\ a % f = b % f /\ u*f+v*b = |1| ==>
    ~(h pdivides a)
Proof
  rpt strip_tac >>
  `Ring r /\ Poly r f /\ Poly r h /\ ulead f /\ ulead h`
    by metis_tac[field_is_ring, poly_monic_poly, poly_monic_ulead] >>
  `a % h = b % h` by metis_tac[poly_divides_mod_mod] >>
  `h pdivides b` by metis_tac[poly_divides_alt] >>
  `h pdivides |1|` by metis_tac[poly_divides_linear_comm] >>
  `h = |1|` by metis_tac[poly_monic_divides_one] >>
  fs[poly_deg_one]
QED

Theorem polynomial_certificate_master_remainder:
  !r:'a ring. Ring r ==> !f n b.
    poly_monic r f /\ Poly r b /\ (X ** n) % f = X+b ==>
    (master n) % f = b % f
Proof
  rpt strip_tac >>
  `ulead f` by metis_tac[poly_monic_ulead] >>
  `Poly r X /\ Poly r (X ** n)` by simp[] >>
  `X+b-X = b` by simp[poly_add_sub_comm] >>
  metis_tac[poly_mod_sub, poly_mod_mod, poly_mod_poly, poly_add_poly]
QED

Theorem polynomial_certificate_no_roots:
  !r:'a field. FiniteField r ==> !f b u v.
    poly_monic r f /\ Poly r b /\ Poly r u /\ Poly r v /\
    (X ** CARD r.carrier) % f = X+b /\ u*f+v*b = |1| ==>
    poly_roots r f = {}
Proof
  rpt strip_tac >>
  `Field r /\ Ring r /\ r.prod.id <> r.sum.id`
    by metis_tac[FiniteField_def, field_is_ring, field_one_ne_zero] >>
  `Poly r f /\ Poly r (master (CARD r.carrier))`
    by simp[poly_monic_poly] >>
  `(master (CARD r.carrier)) % f = b % f`
    by metis_tac[polynomial_certificate_master_remainder] >>
  simp_tac std_ss [EXTENSION, NOT_IN_EMPTY] >>
  rpt strip_tac >>
  `x IN r.carrier /\ (factor x) pdivides f`
    by metis_tac[poly_root_factor] >>
  `poly_monic r (factor x) /\ 0 < poly_deg r (factor x)`
    by simp[poly_factor_monic, poly_deg_factor] >>
  `x IN poly_roots r (master (CARD r.carrier))`
    by metis_tac[poly_master_roots_all] >>
  `(factor x) pdivides (master (CARD r.carrier))`
    by metis_tac[poly_root_factor] >>
  metis_tac[polynomial_certificate_bezout]
QED

Theorem degree12_divisor_tests[local]:
  !d. d divides 12 /\ ~(d divides 6) /\ ~(d divides 4) ==> d = 12
Proof
  rpt strip_tac >>
  `d <= 12` by metis_tac[DIVIDES_LE, DECIDE ``(0:num) < 12``] >>
  `d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/
   d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12`
    by decide_tac >>
  rpt (first_x_assum DISJ_CASES_TAC) >>
  fs[DIVIDES_MOD_0]
QED

(* Rabin's criterion specialized to 12: the only prime divisors of 12 are
   2 and 3, hence the proper-degree tests occur at 12/2 and 12/3. *)
Theorem polynomial_certificate_rabin12:
  !r:'a field. FiniteField r ==> !f b4 b6 u4 v4 u6 v6.
    poly_monic r f /\ poly_deg r f = 12 /\
    Poly r b4 /\ Poly r b6 /\
    Poly r u4 /\ Poly r v4 /\ Poly r u6 /\ Poly r v6 /\
    (X ** (CARD r.carrier ** 12)) % f = X /\
    (X ** (CARD r.carrier ** 4)) % f = X+b4 /\
    (X ** (CARD r.carrier ** 6)) % f = X+b6 /\
    u4*f+v4*b4 = |1| /\ u6*f+v6*b6 = |1| ==>
    irreducible (PolyRing r) f
Proof
  rpt strip_tac >>
  `Field r /\ Ring r` by metis_tac[FiniteField_def, field_is_ring] >>
  `Poly r f /\ 0 < poly_deg r f /\ ulead f`
    by metis_tac[poly_monic_poly, poly_monic_ulead, DECIDE ``(0:num) < 12``] >>
  `?h. poly_monic r h /\ irreducible (PolyRing r) h /\ h pdivides f`
    by metis_tac[poly_monic_irreducible_factor_exists] >>
  `Poly r h /\ 0 < poly_deg r h`
    by metis_tac[poly_monic_irreducible_property] >>
  `X % f = X` by simp[poly_mod_less] >>
  `f pdivides (master (CARD r.carrier ** 12))`
    by metis_tac[poly_ulead_divides_master_condition, pmod_def_alt] >>
  `h pdivides (master (CARD r.carrier ** 12))`
    by metis_tac[poly_divides_transitive, poly_master_poly] >>
  `poly_deg r h divides 12`
    by metis_tac[poly_irreducible_master_divisibility] >>
  `(master (CARD r.carrier ** 4)) % f = b4 % f /\
   (master (CARD r.carrier ** 6)) % f = b6 % f`
    by metis_tac[polynomial_certificate_master_remainder] >>
  `~(h pdivides (master (CARD r.carrier ** 4))) /\
   ~(h pdivides (master (CARD r.carrier ** 6)))`
    by (conj_tac >| [
      match_mp_tac (Q.SPECL
        [`f`, `master (CARD r.carrier ** 4)`, `b4`, `u4`, `v4`, `h`]
        (UNDISCH (Q.SPEC `r` polynomial_certificate_bezout))) >>
      ASM_SIMP_TAC bool_ss [poly_master_poly],
      match_mp_tac (Q.SPECL
        [`f`, `master (CARD r.carrier ** 6)`, `b6`, `u6`, `v6`, `h`]
        (UNDISCH (Q.SPEC `r` polynomial_certificate_bezout))) >>
      ASM_SIMP_TAC bool_ss [poly_master_poly]
    ]) >>
  `~(poly_deg r h divides 4) /\ ~(poly_deg r h divides 6)`
    by metis_tac[poly_irreducible_master_divisibility] >>
  `poly_deg r h = 12` by metis_tac[degree12_divisor_tests] >>
  `h = f` by metis_tac[poly_monic_divides_eq_deg_eq] >>
  metis_tac[]
QED
