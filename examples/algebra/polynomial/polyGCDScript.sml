(* ------------------------------------------------------------------------- *)
(* GCD and LCM of Polynomials                                                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyGCD";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "ringTheory"; *) *)
(* val _ = load "ringUnitTheory"; (* this overloads |/ as r*.inv *) *)
(* (* val _ = load "integralDomainTheory"; *) *)
(* val _ = load "fieldTheory"; (* see poly_roots_mult, this overload |/ as (r.prod excluding #0).inv *) *)
open monoidTheory groupTheory ringTheory ringUnitTheory fieldTheory;

open subgroupTheory;
open monoidOrderTheory groupOrderTheory;

(* (* val _ = load "polyWeakTheory"; *) *)
(* (* val _ = load "polyRingTheory"; *) *)
(* val _ = load "polyDividesTheory"; *)
open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory polyDividesTheory;

(* val _ = load "polyRootTheory"; *)
open polyRootTheory;
open polyMonicTheory;

(* val _ = load "polyFieldModuloTheory"; *)
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyIrreducibleTheory;

open ringDividesTheory;

(* val _ = load "polyEvalTheory"; *)
open polyEvalTheory;

(* val _ = load "polyProductTheory"; *)
open polyProductTheory;

(* val _ = load "polyDerivativeTheory"; *)
open polyDerivativeTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* val _ = load "helperListTheory"; *)
(* val _ = load "helperFunctionTheory"; *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* GCD and LCM of Polynomials Documentation                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   pgcd p q                    = poly_gcd r p q
   rcoprime x y                = unit (rgcd x y)
   pcoprime p q                = upoly (pgcd p q)
   mpgcd p q                   = poly_monic_gcd r p q
   plcm p q                    = poly_lcm r p q
   pcoprime_set s              = poly_coprime_set r s
   monic_irreducibles_set r s  = !p. p IN s ==> monic p /\ ipoly p
   miset s                     = monic_irreducibles_set r
*)
(* Definitions and Theorems (# are exported):

   Polynomial GCD:
   poly_gcd_def      |- !r p q. pgcd p q = ring_gcd (PolyRing r) (\p. norm p) p q
#  poly_gcd_poly     |- !r. Field r ==> !p q. poly p /\ poly q ==> poly (pgcd p q)
   poly_gcd_sym      |- !r. Field r ==> !p q. poly p /\ poly q ==> (pgcd p q = pgcd q p)
   poly_gcd_divides  |- !r. Field r ==> !p q. poly p /\ poly q ==>
                            pgcd p q pdivides p /\ pgcd p q pdivides q
   poly_gcd_property |- !r. Field r ==> !p q. poly p /\ poly q ==>
                        !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q
   poly_gcd_is_gcd   |- !r. Field r ==> !p q. poly p /\ poly q ==>
                            pgcd p q pdivides p /\ pgcd p q pdivides q /\
                        !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q
   poly_gcd_linear   |- !r. Field r ==> !p q. poly p /\ poly q ==>
                        ?s t. poly s /\ poly t /\ (pgcd p q = s * p + t * q)
   poly_gcd_zero     |- !r. Field r ==> !p. poly p ==> (pgcd p |0| = p) /\ (pgcd |0| p = p)
   poly_gcd_eq_zero          |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                ((pgcd p q = |0|) <=> (p = |0|) /\ (q = |0|))
   poly_divides_gcd_multiple |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                 s pdivides t * p /\ s pdivides t * q ==> s pdivides t * pgcd p q
   poly_gcd_one_factor       |- !r. Field r ==> !p q. poly p /\ poly q /\ (pgcd p q = |1|) ==>
                                                !t. poly t /\ p pdivides q * t ==> p pdivides t
   poly_gcd_condition        |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                !t. poly t /\ t pdivides p /\ t pdivides q /\
                                    (!s. poly s /\ s pdivides p /\ s pdivides q ==>
                                    s pdivides t) ==> pgcd p q ~~ t
   poly_gcd_unit_eq          |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                    (pgcd p q ~~ t <=> t pdivides p /\ t pdivides q /\
                                    !s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
   poly_gcd_reduction        |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                !t. poly t ==> pgcd p q ~~ pgcd p (q - t * p)
   poly_gcd_multiple         |- !r. Field r ==> !p q. poly p /\ poly q ==> pgcd p (q * p) ~~ p
   poly_divides_iff_gcd_fix  |- !r. Field r ==> !p q. poly p /\ poly q ==> (p pdivides q <=> pgcd p q ~~ p)
   poly_gcd_refl             |- !r. Field r ==> !p. poly p ==> pgcd p p ~~ p
   poly_gcd_common_factor    |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                                pgcd (t * p) (t * q) ~~ t * pgcd p q

   Polynomial Coprime:
   poly_gcd_one_coprime |- !r. Ring r ==> !p q. pcoprime p q <=> pgcd p q ~~ |1|
   poly_coprime_sym     |- !r. Field r ==> !p q. poly p /\ poly q ==> (pcoprime p q <=> pcoprime q p)
   poly_gcd_one         |- !r. Field r ==> !p. poly p ==> pgcd p |1| ~~ |1| /\ pgcd |1| p ~~ |1|
   poly_gcd_unit        |- !r. Field r ==> !p. poly p ==> !u. upoly u ==> pgcd p u ~~ |1| /\ pgcd u p ~~ |1|
   poly_irreducible_gcd |- !r. Field r ==> !p q. ipoly p /\ poly q ==> pcoprime p q \/ p pdivides q
   poly_irreducibles_coprime       |- !r. Field r ==> !p q. ipoly p /\ ipoly q ==> pcoprime p q \/ p ~~ q
   poly_monic_irreducibles_coprime |- !r. Field r ==> !p q. monic p /\ ipoly p /\ monic q /\ ipoly q ==>
                                                      pcoprime p q \/ (p = q)

   GCD divisibility condition for unity polynomials:
   poly_unity_gcd_reduction |- !r. Field r ==> !n m. 0 < m /\ m < n ==>
                                   pgcd (unity n) (unity m) ~~ pgcd (unity m) (unity (n - m))
   poly_unity_gcd_identity  |- !r. Field r ==> !n m. pgcd (unity n) (unity m) ~~ unity (gcd n m)
   poly_unity_divisibility  |- !r. Ring r /\ #1 <> #0 ==>
                               !n m. unity n pdivides unity m <=> n divides m

   GCD divisibility condition for master polynomials:
   poly_master_gcd_identity  |- !r. Field r ==>
                      !k n m. pgcd (master (k ** n)) (master (k ** m)) ~~ master (k ** gcd n m)
   poly_master_divisibility  |- !r. Field r ==> !k. 1 < k ==>
                                !n m. master (k ** n) pdivides master (k ** m) <=> n divides m

   Monic Polynomial GCD (except when both are zero):
   poly_monic_gcd_def        |- !r p q. mpgcd p q =
                                (let d = pgcd p q in if d = |0| then |0| else |/ (lead d) * d)
   poly_monic_gcd_zero_zero  |- !r p q. (pgcd p q = |0|) ==> (mpgcd p q = |0|)
   poly_monic_gcd_nonzero    |- !r p q. pgcd p q <> |0| ==> (mpgcd p q = |/ (lead (pgcd p q)) * pgcd p q)
   poly_monic_gcd_monic   |- !r. Field r ==> !p q. poly p /\ poly q /\
                                             ~((p = |0|) /\ (q = |0|)) ==> monic (mpgcd p q)
#  poly_monic_gcd_poly    |- !r. Field r ==> !p q. poly p /\ poly q ==> poly (mpgcd p q)
   poly_monic_gcd_eq_zero |- !r. Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |0|) <=> (pgcd p q = |0|))
   poly_monic_gcd_zero    |- !r. Field r ==> !p. monic p ==> (mpgcd p |0| = p) /\ (mpgcd |0| p = p)
   poly_monic_gcd_eq_one  |- !r. Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |1|) <=> pgcd p q ~~ |1|)
   poly_monic_gcd_one     |- !r. Field r ==> !p. poly p ==> (mpgcd p |1| = |1|) /\ (mpgcd |1| p = |1|)
   poly_monic_gcd_one_coprime    |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                    (pcoprime p q <=> (mpgcd p q = |1|))
   poly_gcd_unit_eq_monic_gcd_eq |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t ==>
                                                    (pgcd p q ~~ pgcd s t <=> (mpgcd p q = mpgcd s t))
   poly_monic_gcd_refl    |- !r. Field r ==> !p. monic p ==> (mpgcd p p = p)
   poly_monic_gcd_sym     |- !r. Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q = mpgcd q p)
   poly_monic_gcd_divides |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                   mpgcd p q pdivides p /\ mpgcd p q pdivides q
   poly_monic_gcd_is_monic_gcd  |- !r. Field r ==> !p q. poly p /\ poly q /\ monic (pgcd p q) ==>
                                                   (pgcd p q = mpgcd p q)
   poly_monic_gcd_eq_monic_gcd  |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                   !t. monic t /\ t ~~ pgcd p q ==> (t = mpgcd p q)
   poly_monic_gcd_is_gcd      |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                 mpgcd p q pdivides p /\ mpgcd p q pdivides q /\
                                 !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides mpgcd p q
   poly_monic_gcd_eq          |- !r. Field r ==> !p q t. poly p /\ poly q /\ monic t ==>
                                     ((mpgcd p q = t) <=> t pdivides p /\ t pdivides q /\
                                     !s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
   poly_monic_gcd_condition   |- !r. Field r ==> !p q t. poly p /\ poly q /\ monic t /\ p <> |0| ==>
                                     ((mpgcd p q = t) <=> t pdivides p /\ t pdivides q /\
                                    !s. monic s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
   poly_monic_gcd_factor_out  |- !r. Field r ==> !p q. poly p /\ poly q ==>
           ?s t. poly s /\ poly t /\ (p = s * mpgcd p q) /\ (q = t * mpgcd p q) /\ (mpgcd s t = |1|)
   poly_monic_gcd_linear      |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                 ?s t. poly s /\ poly t /\ (mpgcd p q = s * p + t * q)
   poly_divides_monic_gcd_multiple    |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                         s pdivides t * p /\ s pdivides t * q ==> s pdivides t * mpgcd p q
   poly_monic_gcd_one_factor          |- !r. Field r ==> !p q. poly p /\ poly q /\ (mpgcd p q = |1|) ==>
                                         !t. poly t /\ p pdivides q * t ==> p pdivides t
   poly_coprime_divides_product       |- !r. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
                                         !t. poly t /\ p pdivides q * t ==> p pdivides t
   poly_irreducible_divides_product   |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                         !t. ipoly t /\ t pdivides p * q ==> t pdivides p \/ t pdivides q
   poly_gcd_multiple_reduction        |- !r. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
                                         !t. poly t ==> pgcd p (q * t) ~~ pgcd p t
   poly_monic_gcd_multiple_reduction  |- !r. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
                                         !t. poly t ==> (mpgcd p (q * t) = mpgcd p t)
   poly_coprime_product_by_coprimes   |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                         !t. poly t /\ pcoprime t p /\ pcoprime t q ==> pcoprime t (p * q)

   Polynomiald LCM:
   poly_lcm_def       |- !r p q. plcm p q = if deg (mpgcd p q) = 0 then p * q else p * q / mpgcd p q
#  poly_lcm_poly      |- !r. Field r ==> !p q. poly p /\ poly q ==> poly (plcm p q)
   poly_lcm_eqn       |- !r. Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q * plcm p q = p * q)
   poly_lcm_zero      |- !r. Field r ==> !p. poly p ==> (plcm p |0| = |0|) /\ (plcm |0| p = |0|)
   poly_lcm_one       |- !r. Field r ==> !p. poly p ==> (plcm p |1| = p) /\ (plcm |1| p = p)
   poly_coprime_lcm   |- !r. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==> (plcm p q = p * q)
   poly_lcm_divisors  |- !r. Field r ==> !p q. poly p /\ poly q ==> p pdivides plcm p q /\ q pdivides plcm p q
   poly_lcm_is_lcm    |- !r. Field r ==> !p q. poly p /\ poly q ==>
                         !t. poly t /\ p pdivides t /\ q pdivides t ==> plcm p q pdivides t
   poly_coprime_product_divides   |- !r. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
                                     !t. poly t /\ p pdivides t /\ q pdivides t ==> p * q pdivides t

   Coprime Polynomial Sets:
   poly_coprime_set_def            |- !r s. pcoprime_set s <=>
                                   (!p. p IN s ==> poly p) /\ !p q. p IN s /\ q IN s /\ p <> q ==> pcoprime p q
   poly_coprime_poly_prod          |- !r. Field r ==> !s. FINITE s /\ (!q. q IN s ==> poly q) ==>
                     !p. poly p /\ p NOTIN s /\ (!q. q IN s ==> pcoprime p q) ==> pcoprime p (PPROD s)
   poly_coprime_set_insert         |- !r. Field r ==> !s p. FINITE s /\ p NOTIN s /\
                        pcoprime_set (p INSERT s) ==> poly p /\ pcoprime_set s /\ pcoprime p (PPROD s)
   poly_prod_coprime_set_divides   |- !r. Field r ==> !s. FINITE s /\ pcoprime_set s ==>
                                      !t. poly t /\ (!p. p IN s ==> p pdivides t) ==> PPROD s pdivides t
   poly_prod_coprime_image_divides |- !r. Field r ==> !f s. FINITE s /\ pcoprime_set (IMAGE f s) ==>
                                      !p. poly p /\ (!x. x IN s ==> f x pdivides p) ==> PPIMAGE f s pdivides p

   Monic Irreducible Sets:
   monic_irreducible_set_poly_set           |- !r s. miset s ==> pset s
   monic_irreducible_set_monic_set          |- !r s. miset s ==> mset s
   monic_irreducible_set_bigunion           |- !r s. (!x. x IN s ==> miset x) ==> miset (BIGUNION s)

   poly_prod_monic_irreducible_set_divisor  |- !r. Field r ==> !s. FINITE s /\ miset s ==>
                                               !p. monic p /\ ipoly p ==> (p pdivides PPROD s <=> p IN s)
   poly_prod_monic_irreducible_set_eq       |- !r. Field r ==> !s t. FINITE s /\ miset s /\
                                                   FINITE t /\ miset t ==> ((PPROD s = PPROD t) <=> (s = t))
   poly_prod_disjoint_bigunion              |- !r. Field r ==> !P. FINITE P /\ EVERY_FINITE P /\
                                                   PAIR_DISJOINT P /\ (!s. s IN P ==> miset s) ==>
                                                   (PPROD (BIGUNION P) = PPIMAGE PPROD P)
   poly_monic_irreducibles_coprime_set      |- !r. Field r ==> !s. miset s ==> pcoprime_set s
   poly_factor_image_monic_irreducibles_set |- !r. Field r ==> !s. s SUBSET R ==> miset (IMAGE factor s)
   poly_prod_factors_divides                |- !r. Field r ==> !p. poly p ==>
                                               !s. s SUBSET roots p ==> PIFACTOR s pdivides p

   Product of Monic Irreducible Sets:
   poly_prod_monic_irreducible_set_nonzero
                         |- !r. Field r ==> !s. FINITE s /\ miset s ==> PPROD s <> |0|
   poly_prod_monic_irreducible_set_divisibility
                         |- !r. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
                                (PPROD t pdivides PPROD s <=> t SUBSET s)
   poly_prod_monic_irreducible_set_coprime
                         |- !r. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t /\ DISJOINT s t ==>
                                pcoprime (PPROD s) (PPROD t)
   poly_prod_monic_irreducible_set_by_product
                         |- !r. Ring r ==> !s. FINITE s /\ miset s ==>
                            !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v)
   poly_prod_monic_irreducible_sets_product
                         |- !r. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
                                (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t)
   poly_prod_monic_irreducible_set_divisors
                         |- !r. Field r ==> !s. FINITE s /\ miset s ==>
                            !p q. monic p /\ monic q /\ (p * q = PPROD s) ==>
                            ?s1 s2. (s = s1 UNION s2) /\ DISJOINT s1 s2 /\ (p = PPROD s1) /\ (q = PPROD s2)
   poly_prod_monic_irreducible_set_divisor_form
                         |- !r. Field r ==> !s. FINITE s /\ miset s ==>
                            !p. monic p /\ p pdivides PPROD s ==> ?t. t SUBSET s /\ (p = PPROD t)
   poly_prod_factors_divides_poly_prod_factor
                         |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==>
                            !t. t SUBSET s ==> PIFACTOR t pdivides PIFACTOR s
   poly_prod_factors_monic_divisor
                         |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==>
                            !p. monic p ==> (p pdivides PIFACTOR s <=> ?t. t SUBSET s /\ (p = PIFACTOR t))
   poly_prod_factors_monic_common_divisor
                         |- !r. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
                            !p. monic p /\ p pdivides PIFACTOR s /\ p pdivides PIFACTOR t ==>
                                p pdivides PIFACTOR (s INTER t)
   poly_prod_factors_monic_gcd  |- !r. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
                                       (mpgcd (PIFACTOR s) (PIFACTOR t) = PIFACTOR (s INTER t))
   poly_prod_factors_eq         |- !r. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
                                       ((PIFACTOR s = PIFACTOR t) <=> (s = t))
   poly_prod_factors_product    |- !r. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
                                       (PIFACTOR (s UNION t) * PIFACTOR (s INTER t) = PIFACTOR s * PIFACTOR t)
   poly_prod_factors_ring_mult_fun    |- !r. Field r ==> ring_set_multiplicative_fun r (\s. PIFACTOR s)

   Coprime with Derivative:
   poly_coprime_diff_simple_divisor   |- !r. Field r ==> !p. poly p /\ pgcd p (diff p) ~~ |1| ==>
                                         !q. poly q /\ 0 < deg q /\ q pdivides p ==>
                                         !k. 1 < k ==> ~(q ** k pdivides p)
   poly_coprime_diff_nonzero          |- !r. Field r ==> !p. poly p /\ pcoprime p (diff p) ==> p <> |0|
   poly_coprime_diff_unit_eq_prod_set |- !r. Field r ==> !t. poly t /\ pcoprime t (diff t) ==>
                                         !s. FINITE s /\ pset s /\ PPROD s pdivides t /\
                                             (!p. monic p /\ ipoly p /\ p pdivides t ==> p IN s) ==> t ~~ PPROD s
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems (Reworks)                                                 *)
(* ------------------------------------------------------------------------- *)

(* Note:
   These theorems are rework of the proof of LCM_IS_LEAST_COMMON_MULTIPLE
   from source of gcdTheory. The purpose is to understand the proof to enable
   proving the corresponding theorem for polynomial LCM: poly_lcm_is_lcm.
*)

(* Theorem: m divides (lcm m n) /\ n divides (lcm m n) *)
(* Proof:
   Let d = gcd m n, e = lcm m n.
   If d = 0,
      Then (m = 0) /\ (n = 0)    by GCD_EQ_0
        so e = 0                 by LCM_0
       and 0 divides 0           by ZERO_DIVIDES
   If d <> 0,
      Note d * e = m * n         by GCD_LCM
       and d divides m           by GCD_IS_GREATEST_COMMON_DIVISOR
           d divides n           by GCD_IS_GREATEST_COMMON_DIVISOR
      thus ?x. m = x * d         by divides_def
       and ?y. n = y * d         by divides_def
     Hence d * e = (x * d) * n   by above
                 = (d * x) * n   by MULT_COMM
                 = d * (x * n)   by MULT_ASSOC
        or     e = x * n         by EQ_MULT_LCANCEL
      thus n divides e           by divides_def
      Also e * d = m * (y * d)   by above
                 = (m * y) * d   by MULT_ASSOC
                 = (y * m) * d   by MULT_COMM
        or     e = y * m         by EQ_MULT_RCANCEL
      thus m divides e           by divides_def
*)
val LCM_DIVISORS = prove(
  ``!m n. m divides (lcm m n) /\ n divides (lcm m n)``,
  ntac 2 strip_tac >>
  qabbrev_tac `d = gcd m n` >>
  qabbrev_tac `e = lcm m n` >>
  Cases_on `d = 0` >-
  metis_tac[GCD_EQ_0, LCM_0, ZERO_DIVIDES] >>
  `d * e = m * n` by rw[GCD_LCM, Abbr`d`, Abbr`e`] >>
  `d divides m /\ d divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `(?x. m = x * d) /\ (?y. n = y * d)` by rw[GSYM divides_def] >>
  `d * e = d * (x * n)` by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `e * d = (y * m) * d` by metis_tac[MULT_COMM, MULT_ASSOC] >>
  metis_tac[EQ_MULT_LCANCEL, EQ_MULT_RCANCEL, divides_def]);

(* Theorem: m divides p /\ n divides p ==> (lcm m n) divides p *)
(* Proof:
   Let d = gcd m n, e = lcm m n.
   If (m = 0) \/ (n = 0),
      If m = 0 then e = n              by LCM_0
      If n = 0 then e = m              by LCM_0
      Either case, e divides p         by given
   If (m <> 0) /\ (n <> 0),
      Then d <> 0                      by GCD_EQ_0
      Step 1: get a coprime pair
      Note ?x y. (m = x * d) /\ (n = y * d) /\
                 (gcd x y = 1)         by FACTOR_OUT_GCD, m <> 0 /\ n <> 0
      Step 2: equate two expressions for multiple p
      Since m divides p
        ==> ?u. p = u * m              by divides_def
                  = u * (x * d)        by above
                  = (u * x) * d        by MULT_ASSOC
       Also n divides p
        ==> ?v. p = v * n              by divides_def
                  = v * (y * d)        by above
                  = (v * y) * d        by MULT_ASSOC
       Equating p,
         (u * x) * d = (v * y) * d
           or  u * x = v * y           by EQ_MULT_RCANCEL, d <> 0
           or  x * u = v * y           by MULT_COMM
       Step 3: squeeze out a factor (x * y * d) from p
       This shows:
            y divides (x * u)          by divides_def
        But coprime x y                by gcd x y = 1
         so y divides u                by L_EUCLIDES
         or ?t. u = t * y              by divides_def
       Thus p = u * (x * d)            by above
              = (t * y) * (x * d)      by substituting u
              = t * (y * x * d)        by MULT_ASSOC
              = t * (x * y * d)        by MULT_COMM
       Step 4: show that e = x * y * d
       Now d * e = m * n               by GCD_LCM
        so d * e = (x * d) * (y * d)   by above
                 = (d * x) * (y * d)   by MULT_COMM
                 = d * (x * y * d)     by MULT_ASSOC
       Thus    e = x * y * d           by EQ_MULT_LCANCEL, d <> 0
       Step 5: conclude
       Hence p = t * e                 by step 3 and step 4
          or e divides p               by divides_def
*)
val LCM_IS_LCM = prove(
  ``!m n p. m divides p /\ n divides p ==> (lcm m n) divides p``,
  rpt strip_tac >>
  qabbrev_tac `d = gcd m n` >>
  qabbrev_tac `e = lcm m n` >>
  Cases_on `(m = 0) \/ (n = 0)` >-
  metis_tac[LCM_0] >>
  `(m <> 0) /\ (n <> 0) /\ (d <> 0)` by metis_tac[GCD_EQ_0] >>
  `?x y. (m = x * d) /\ (n = y * d) /\ (gcd x y = 1)` by rw[FACTOR_OUT_GCD, Abbr`d`] >>
  `?u. p = u * m` by rw[GSYM divides_def] >>
  `_ = (u * x) * d` by rw[MULT_ASSOC] >>
  `?v. p = v * n` by rw[GSYM divides_def] >>
  `_ = (v * y) * d` by metis_tac[MULT_ASSOC] >>
  `x * u = v * y` by metis_tac[EQ_MULT_RCANCEL, MULT_COMM] >>
  `y divides (x * u)` by metis_tac[divides_def] >>
  `y divides u` by metis_tac[L_EUCLIDES] >>
  `?t. u = t * y` by rw[GSYM divides_def] >>
  `p = t * (x * y * d)` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `e = x * y * d` by
  (`d * e = m * n` by rw[GCD_LCM, Abbr`d`, Abbr`e`] >>
  `_ = d * (x * y * d)` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[EQ_MULT_LCANCEL]) >>
  metis_tac[divides_def]);

(*
GCD_CANCEL_MULT
|- !m n k. coprime m k ==> (gcd m (k * n) = gcd m n)
*)

(* This is rework of gcdTheory source *)

(* Theorem: coprime m k ==> (gcd m (k * n) = gcd m n) *)
(* Proof:
   By GCD_PROPERTY, this is to show:
   (1) coprime m k ==> gcd m n divides m /\ gcd m n divides (k * n)
       Note gcd m n divides m             by GCD_IS_GREATEST_COMMON_DIVISOR
        and gcd m n divides n             by GCD_IS_GREATEST_COMMON_DIVISOR
        ==> gcd m n divides (k * n)       by DIVIDES_MULTIPLE
   (2) coprime m k /\ x divides m /\ x divides k * n ==> x divides gcd m n
       Claim: coprime k x
       Proof: by GCD_PROPERTY, this is to show:
              d divides k /\ d divides x ==> d = 1
              Since d divides x /\ x divides m
                ==> d divides m           by DIVIDES_TRANS
                and d divides m /\ d divides k
                ==> d divides gcd m k     by GCD_IS_GREATEST_COMMON_DIVISOR
              Hence d divides 1           by coprime m k
                 or d = 1                 by DIVIDES_ONE
       Hence coprime k x /\ x divides k * n
         ==> x divides n                  by L_EUCLIDES
        With x divides m /\ x divides n
         ==> x divides gcd m n            by GCD_IS_GREATEST_COMMON_DIVISOR
*)
val GCD_CANCEL_MULT = prove(
  ``!m n k. coprime m k ==> (gcd m (k * n) = gcd m n)``,
  rpt strip_tac >>
  rw[GCD_PROPERTY] >-
  rw[GCD_IS_GREATEST_COMMON_DIVISOR] >-
  rw[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_MULTIPLE] >>
  `coprime k x` by
  (rw[GCD_PROPERTY] >>
  prove_tac[DIVIDES_TRANS, GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ONE]) >>
  metis_tac[L_EUCLIDES, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* ------------------------------------------------------------------------- *)
(* Polynomial GCD                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define Polynomial GCD from Ring GCD *)
val poly_gcd_def = Define `
    poly_gcd (r:'a ring) (p:'a poly) (q:'a  poly) = ring_gcd (PolyRing r) (\p. norm p) p q
`;
(* overload on Polynomial GCD *)
val _ = overload_on("pgcd", ``poly_gcd r``);
(* > poly_gcd_def;
val it = |- !r p q. pgcd p q = ring_gcd (PolyRing r) (\p. norm p) p q: thm *)


(* Theorem: Field r ==> !p q. poly p /\ poly q ==> poly (pgcd p q) *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_element *)
val poly_gcd_poly = store_thm(
  "poly_gcd_poly",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> poly (pgcd p q)``,
  metis_tac[poly_gcd_def, poly_ring_euclid_ring, ring_gcd_element, poly_ring_element]);

(* export simple result *)
val _ = export_rewrites["poly_gcd_poly"];

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (pgcd p q = pgcd q p) *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_sym *)
val poly_gcd_sym = store_thm(
  "poly_gcd_sym",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (pgcd p q = pgcd q p)``,
  metis_tac[poly_gcd_def, poly_ring_euclid_ring, ring_gcd_sym, poly_ring_element]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> pgcd p q pdivides p /\ pgcd p q pdivides q *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_divides, poly_divides_is_ring_divides *)
val poly_gcd_divides = store_thm(
  "poly_gcd_divides",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> pgcd p q pdivides p /\ pgcd p q pdivides q``,
  metis_tac[poly_gcd_def, poly_ring_euclid_ring, ring_gcd_divides,
            poly_ring_element, poly_divides_is_ring_divides]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_property, poly_divides_is_ring_divides *)
val poly_gcd_property = store_thm(
  "poly_gcd_property",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q``,
  metis_tac[poly_gcd_def, poly_ring_euclid_ring, ring_gcd_property,
            poly_ring_element, poly_divides_is_ring_divides]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> pgcd p q pdivides p /\ pgcd p q pdivides q /\
            !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q *)
(* Proof: by poly_gcd_property, poly_gcd_divides *)
val poly_gcd_is_gcd = store_thm(
  "poly_gcd_is_gcd",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> pgcd p q pdivides p /\ pgcd p q pdivides q /\
   !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides pgcd p q``,
  rw[poly_gcd_property, poly_gcd_divides]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> ?s t. poly s /\ poly t /\ (pgcd p q = s * p + t * q) *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_linear *)
val poly_gcd_linear = store_thm(
  "poly_gcd_linear",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   ?s t. poly s /\ poly t /\ (pgcd p q = s * p + t * q)``,
  rpt strip_tac >>
  `EuclideanRing (PolyRing r) (\p. norm p)` by rw[poly_ring_euclid_ring] >>
  `p IN (PolyRing r).carrier /\ q IN (PolyRing r).carrier` by rw[poly_ring_element] >>
  `?s t. s IN (PolyRing r).carrier /\ t IN (PolyRing r).carrier /\
    (ring_gcd (PolyRing r) (\p. norm p) p q = s * p + t * q)` by rw[ring_gcd_linear] >>
  metis_tac[poly_gcd_def, poly_ring_element]);

(* Theorem: Field r ==> !p. poly p ==> (pgcd p |0| = p) /\ (pgcd |0| p = p) *)
(* Proof: by poly_ring_euclid_ring, ring_gcd_zero *)
val poly_gcd_zero = store_thm(
  "poly_gcd_zero",
  ``!r:'a field. Field r ==> !p. poly p ==> (pgcd p |0| = p) /\ (pgcd |0| p = p)``,
  metis_tac[poly_gcd_def, poly_ring_euclid_ring, ring_gcd_zero]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> ((pgcd p q = |0|) <=> (p = |0|) /\ (q = |0|)) *)
(* Proof:
   If part: (pgcd p q = |0|) ==> (p = |0|) /\ (q = |0|)
   Let d = pgcd p q.
    Then poly d                           by poly_gcd_poly
     and d pdivides p /\ d pdivides q     by poly_gcd_is_gcd
   Given d = |0|, so p = |0| /\ q = |0|   by poly_zero_divides
   Only-if part: (p = |0|) /\ (q = |0|) ==> (pgcd p q = |0|)
       pgcd |0| |0| = |0|                 by poly_gcd_zero
*)
val poly_gcd_eq_zero = store_thm(
  "poly_gcd_eq_zero",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> ((pgcd p q = |0|) <=> (p = |0|) /\ (q = |0|))``,
  rewrite_tac[EQ_IMP_THM] >>
  ntac 5 strip_tac >>
  conj_tac >| [
    strip_tac >>
    qabbrev_tac `d = pgcd p q` >>
    `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
    `d pdivides p /\ d pdivides q` by rw[poly_gcd_is_gcd, Abbr`d`] >>
    rw[GSYM poly_zero_divides],
    metis_tac[poly_gcd_zero]
  ]);

(* This is Auxillary Lemma for Euclid's Lemma. *)

(* Theorem: Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
            s pdivides (t * p) /\ s pdivides (t * q) ==> s pdivides (t * pgcd p q) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                               by poly_gcd_poly
     and ?x y. poly x /\ poly y /\
         (d = x * p + y * q)                  by poly_gcd_linear
    Thus t * d = t * (x * p) + t * (y * q)    by poly_mult_radd
               = x * (t * p) + y * (t * q)    by poly_mult_assoc_comm
    Since s pdivides (t * p)                  by given
      and s pdivides (t * q)                  by given
    Hence s pdivides (t * d)                  by poly_divides_linear_comm
*)
val poly_divides_gcd_multiple = store_thm(
  "poly_divides_gcd_multiple",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
    s pdivides (t * p) /\ s pdivides (t * q) ==> s pdivides (t * pgcd p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `?x y. poly x /\ poly y /\ (d = x * p + y * q)` by rw[poly_gcd_linear, Abbr`d`] >>
  `t * d = t * (x * p) + t * (y * q)` by rw[poly_mult_radd] >>
  `_ = x * (t * p) + y * (t * q)` by rw[poly_mult_assoc_comm] >>
  rw[poly_divides_linear_comm]);

(* This is Euclid's Lemma for polynomial factors. *)

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ (pgcd p q = |1|) ==>
            !t. poly t /\ p pdivides (q * t) ==> p pdivides t *)
(* Proof:
   Put s = p in poly_divides_gcd_multiple,
    Then p pdivides (t * p) /\ p pdivides (t * q) ==> p pdivides (t * pgcd p q)
   Since p pdivides (t * p)              by poly_divides_multiple, poly_divides_reflexive
     and p pdivides (t * q)              by poly_mult_comm, given p pdivides (q * t)
   Hence p pdivides (t * pgcd p q)       by poly_divides_monic_gcd_multiple
   Since pgcd p q = |1|, t * |1| = t     by poly_mult_rone
   Hence p pdivides t                    by above
*)
val poly_gcd_one_factor = store_thm(
  "poly_gcd_one_factor",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ (pgcd p q = |1|) ==>
   !t. poly t /\ p pdivides (q * t) ==> p pdivides t``,
  rpt strip_tac >>
  `p pdivides p` by rw[poly_divides_reflexive] >>
  `p pdivides (t * p)` by rw[poly_divides_multiple] >>
  `p pdivides (t * q)` by rw[poly_mult_comm] >>
  `t * |1| = t` by rw[] >>
  metis_tac[poly_divides_gcd_multiple]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. poly t /\ t pdivides p /\ t pdivides q /\
            (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t) ==> pgcd p q ~~ t *)
(* Proof:
   Let d = pgcd p q.
   Then poly d                        by poly_gcd_poly
    Now d pdivides p                  by poly_gcd_divides
    and d pdivides q                  by poly_gcd_divides
     so d pdivides t                  by implication
    but t pdivdes d                   by poly_gcd_property
    Thus d ~~ t                       by poly_field_divides_antisym
*)
val poly_gcd_condition = store_thm(
  "poly_gcd_condition",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ t pdivides p /\ t pdivides q /\
   (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t) ==> pgcd p q ~~ t``,
  rw[poly_gcd_divides, poly_gcd_property, poly_field_divides_antisym]);

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ poly t ==> (pgcd p q ~~ t <=>
            t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)) *)
(* Proof:
   Let d = pgcd p q,
   Then poly d             by poly_gcd_poly
   If part: d ~~ t ==>
            t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
     (1) Since d pdivides p      by poly_gcd_divides
           and d ~~ t            by given
            so t pdivides p      by poly_unit_eq_divides
     (2) Since d pdivides q      by poly_gcd_divides
           and d ~~ t            by given
            so t pdivides q      by poly_unit_eq_divides
     (3) If poly s /\ s pdivides p /\ s pdivides q,
          then s pdivides d      by poly_gcd_is_gcd
           and d ~~ t            by given
            so s pdivides t      by poly_unit_eq_divisor
   Only-if part: t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
             ==> d ~~ t, true    by poly_gcd_condition
*)
val poly_gcd_unit_eq = store_thm(
  "poly_gcd_unit_eq",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t ==>
   (pgcd p q ~~ t <=>
    t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  rw[EQ_IMP_THM] >| [
    metis_tac[poly_gcd_divides, poly_unit_eq_divides],
    metis_tac[poly_gcd_divides, poly_unit_eq_divides],
    metis_tac[poly_gcd_is_gcd, poly_unit_eq_divisor],
    metis_tac[poly_gcd_condition]
  ]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> !t. poly t ==> (pgcd p q ~~ pgcd p (q - t * p)) *)
(* Proof:
   Let d = pgcd p q, s = q - t * p.
   Then d pdivides p         by poly_gcd_divides
    and d pdivides q         by poly_gcd_divides
      Note s = |1| * q  - t * p      by poly_mult_lone
       and poly d                    by poly_gcd_poly
       Now d pdivides s              by poly_divides_linear_sub_comm

   Claim: !u. poly u /\ u pdivides p /\ u pdivides s ==> u pdivides d
   Proof: Since q = t * p + s        by poly_sub_eq_add
                  = t * p + |1| * s  by poly_mult_lone
          Given u pdivides p /\ u pdivides s
             so u pdivides q         by poly_divides_linear_comm
           With u pdivides p         by given
          Hence u pdivides d         by poly_gcd_property

   With !u. poly u /\ u pdivides p /\ u pdivides s ==> u pdivides d,
   Hence pgcd p s ~~ d               by poly_gcd_condition
      or d ~~ pgcd p s               by poly_unit_eq_sym
*)
val poly_gcd_reduction = store_thm(
  "poly_gcd_reduction",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> !t. poly t ==> (pgcd p q ~~ pgcd p (q - t * p))``,
  rpt strip_tac >>
  qabbrev_tac `s = q - t * p` >>
  qabbrev_tac `d = pgcd p q` >>
  `d pdivides p` by rw[poly_gcd_divides, Abbr`d`] >>
  `d pdivides q` by rw[poly_gcd_divides, Abbr`d`] >>
  `Ring r /\ poly |1| /\ poly s /\ (s = |1| * q  - t * p)` by rw[Abbr`s`] >>
  `poly d` by rw[Abbr`d`] >>
  `d pdivides s` by rw[poly_divides_linear_sub_comm] >>
  `!u. poly u /\ u pdivides p /\ u pdivides s ==> u pdivides d` by
  (rpt strip_tac >>
  qabbrev_tac `s = |1| * q - t * p` >>
  `q = t * p + s` by metis_tac[poly_sub_eq_add, poly_mult_poly] >>
  `_ = t * p + |1| * s` by rw[] >>
  `u pdivides q` by rw[poly_divides_linear_comm] >>
  rw[poly_gcd_property, Abbr`d`]) >>
  rw[poly_gcd_condition, poly_unit_eq_sym]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> pgcd p (q * p) ~~ p *)
(* Proof:
      pgcd p (q * p)
   ~~ pgcd p (q * p - q * p)   by poly_gcd_reduction
    = pgcd p |0|               by poly_sub_eq
    = p                        by poly_gcd_zero
*)
val poly_gcd_multiple = store_thm(
  "poly_gcd_multiple",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> pgcd p (q * p) ~~ p``,
  rpt strip_tac >>
  `pgcd p (q * p) ~~ pgcd p (q * p - q * p)` by rw[poly_gcd_reduction] >>
  `q * p - q * p = |0|` by rw[] >>
  metis_tac[poly_gcd_zero]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (p pdivides q <=> pgcd p q ~~ p) *)
(* Proof:
   If part: p pdivides q ==> pgcd p q ~~ p
      Note p pdivides q
       ==> ?t. poly t /\ (q = t * p)     by poly_divides_def
      pgcd p q = pgcd p (t * p)          by above
               ~~ p                      by poly_gcd_multiple
   Only-if part: pgcd p q ~~ p ==> p pdivides q
      Since (pgcd p q) pdivides q        by poly_gcd_divides
        and poly (pgcd p q)              by poly_gcd_poly
      Given pgcd p q ~~ p, p pdivides q  by poly_unit_eq_divides
*)
val poly_divides_iff_gcd_fix = store_thm(
  "poly_divides_iff_gcd_fix",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (p pdivides q <=> pgcd p q ~~ p)``,
  rw[EQ_IMP_THM] >-
  metis_tac[poly_divides_def, poly_gcd_multiple] >>
  metis_tac[poly_gcd_poly, poly_gcd_divides, poly_unit_eq_divides, field_is_ring]);

(* Theorem: Field r ==> !p. poly p ==> (pgcd p p ~~ p) *)
(* Proof:
   Since p pdivides p      by poly_divides_reflexive
      so pgcd p p ~~ p     by poly_divides_iff_gcd_fix
*)
val poly_gcd_refl = store_thm(
  "poly_gcd_refl",
  ``!r:'a field. Field r ==> !p. poly p ==> (pgcd p p ~~ p)``,
  rw[poly_divides_reflexive, GSYM poly_divides_iff_gcd_fix]);

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ poly t ==> pgcd (t * p) (t * q) ~~ t * pgcd p q *)
(* Proof:
   Let d = pgcd p q, e = pgcd (t * p) (t * q).
   Since d pdivides p            by poly_gcd_divides
      so t * d pdivides t * p    by poly_divides_common_multiple
    also d pdivides q            by poly_gcd_divides
    thus t * d pdivides t * q    by poly_divides_common_multiple
   Hence t * d pdivides e        by poly_gcd_is_gcd
     Now ?u v. poly u /\ poly v /\
         d = u * p + v * q       by poly_gcd_linear
      or t * d = t * (u * p + v * q)
               = t * (u * p) + t * (v * q)     by poly_mult_radd
               = u * (t * p) + v * (t * q)     by poly_mult_assoc_comm
    Thus if s pdivides (t * p)
        and s pdivides (t * q)
       then s pdivides (t * d)   by poly_divides_linear_comm
   Therefore e ~~ t * d          by poly_gcd_condition
*)
val poly_gcd_common_factor = store_thm(
  "poly_gcd_common_factor",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t ==> pgcd (t * p) (t * q) ~~ t * pgcd p q``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = pgcd p q` >>
  qabbrev_tac `e = pgcd (t * p) (t * q)` >>
  `poly d /\ poly e` by rw[poly_gcd_poly, Abbr`d`, Abbr`e`] >>
  `d pdivides p /\ d pdivides q` by rw[poly_gcd_divides, Abbr`d`] >>
  `t * d pdivides t * p /\ t * d pdivides t * q` by rw[poly_divides_common_multiple] >>
  `t * d pdivides e` by rw[poly_gcd_is_gcd, Abbr`e`] >>
  `?u v. poly u /\ poly v /\ (d = u * p + v * q)` by rw[poly_gcd_linear, Abbr`d`] >>
  `t * d = t * (u * p) + t * (v * q)` by rw[poly_mult_radd] >>
  `_ = u * (t * p) + v * (t * q)` by rw[poly_mult_assoc_comm] >>
  `!s. poly s /\ s pdivides (t * p) /\ s pdivides (t * q) ==> s pdivides (t * d)` by rw[poly_divides_linear_comm] >>
  rw[poly_gcd_condition, Abbr`e`]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Coprime.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Overload on ring coprime *)
val _ = overload_on("rcoprime", ``\(x y):'a. unit (rgcd x y)``);

(* Overload on polynomial coprime *)
val _ = overload_on("pcoprime", ``\(p q):'a poly. upoly (pgcd p q)``);

(* Theorem: Ring r ==> !p q. pcoprime p q <=> pgcd p q ~~ |1| *)
(* Proof:
       pcoprime p q
   <=> upoly (pgcd p q)                       by notation
   <=> ?u. upoly u /\ (pgcd p q = u)
   <=> ?u. upoly u /\ (pgcd p q = u * |1|)    by poly_mult_rone
   <=> pgcd p q ~~ |1|                        by poly_unit_eq_property
*)
val poly_gcd_one_coprime = store_thm(
  "poly_gcd_one_coprime",
  ``!r:'a ring. Ring r ==> !p q. pcoprime p q <=> pgcd p q ~~ |1|``,
  metis_tac[poly_unit_eq_property, poly_unit_poly, poly_mult_rone]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (pcoprime p q <=> pcoprime q p) *)
(* Proof:
       pcoprime p q
   <=> (pgcd p q ~~ |1|)    by poly_gcd_one_coprime
   <=> (pgcd q p ~~ |1|)    by poly_gcd_sym
   <=> pcoprime q p         by poly_gcd_one_coprime
*)
val poly_coprime_sym = store_thm(
  "poly_coprime_sym",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (pcoprime p q <=> pcoprime q p)``,
  rw[poly_gcd_one_coprime, poly_gcd_sym]);

(* Theorem: Field r ==> !p. poly p ==> pgcd p |1| ~~ |1| /\ pgcd |1| p ~~ |1| *)
(* Proof:
   Since |1| pdivides p                   by poly_one_divides_all
   Hence pgcd |1| p ~~ |1|                by poly_divides_iff_gcd_fix
     and pgcd p |1| = pgcd |1| p ~~ |1|   by poly_gcd_sym
*)
val poly_gcd_one = store_thm(
  "poly_gcd_one",
  ``!r:'a field. Field r ==> !p. poly p ==> pgcd p |1| ~~ |1| /\ pgcd |1| p ~~ |1|``,
  ntac 4 strip_tac >>
  `pgcd |1| p ~~ |1|` suffices_by rw[poly_gcd_sym] >>
  rw[poly_one_divides_all, GSYM poly_divides_iff_gcd_fix]);

(* Theorem: Field r ==> !p. poly p ==> !u. upoly u ==> pgcd p u ~~ |1| /\ pgcd u p ~~ |1| *)
(* Proof:
   Since upoly u ==> poly u           by poly_unit_poly
     and u pdivides p                 by poly_unit_divides_all
      so pgcd u p ~~ u                by poly_divides_iff_gcd_fix
    also u ~~ |1|                     by poly_unit_eq_one
   Hence pgcd u p ~~ |1|              by poly_unit_eq_trans, poly_gcd_poly
*)
val poly_gcd_unit = store_thm(
  "poly_gcd_unit",
  ``!r:'a field. Field r ==> !p. poly p ==> !u. upoly u ==> pgcd p u ~~ |1| /\ pgcd u p ~~ |1|``,
  ntac 6 strip_tac >>
  `poly u` by rw[poly_unit_poly] >>
  `pgcd u p ~~ |1|` suffices_by rw[poly_gcd_sym] >>
  `u pdivides p` by rw[poly_unit_divides_all] >>
  `pgcd u p ~~ u` by rw[GSYM poly_divides_iff_gcd_fix] >>
  `u ~~ |1|` by rw[GSYM poly_unit_eq_one] >>
  metis_tac[poly_gcd_poly, poly_unit_eq_trans, poly_one_poly, field_is_ring]);

(* Theorem: Field r ==> !p q. ipoly p /\ poly q ==> (pcoprime p q) \/ p pdivides q *)
(* Proof:
   Note ipoly p ==> poly p                        by poly_irreducible_poly
    and EuclideanRing (PolyRing r) (\p. norm p)   by poly_ring_euclid_ring
   Apply ring_irreducible_gcd |> ISPEC ``PolyRing r``;
   val it = |- !f. EuclideanRing (PolyRing r) f ==>
               !p. p IN (PolyRing r).carrier /\ ipoly p ==> !q. q IN (PolyRing r).carrier ==>
                upoly (ring_gcd (PolyRing r) f p q) \/ ring_divides (PolyRing r) p q: thm
   and use poly_gcd_def, poly_divides_is_ring_divides, poly_ring_element.
*)
val poly_irreducible_gcd = store_thm(
  "poly_irreducible_gcd",
  ``!r:'a field. Field r ==> !p q. ipoly p /\ poly q ==> (pcoprime p q) \/ p pdivides q``,
  metis_tac[poly_ring_euclid_ring, poly_irreducible_poly,
             ring_irreducible_gcd, poly_gcd_def, poly_divides_is_ring_divides, poly_ring_element]);

(* Theorem: Field r ==> !p q. ipoly p /\ ipoly q ==> pcoprime p q \/ (p ~~ q) *)
(* Proof:
    Note poly p /\ poly q                by poly_irreducible_poly
    With ipoly p /\ ipoly q              by given
     ==> pcoprime p q \/ p pdivides q    by poly_irreducible_gcd
     ==> pcoprime q p \/ q pdivides p    by poly_irreducible_gcd
   Since pcoprime p q <=> pcoprime q p   by poly_coprime_sym
   Hence p ~~ q                          by poly_field_divides_antisym
*)
val poly_irreducibles_coprime = store_thm(
  "poly_irreducibles_coprime",
  ``!r:'a field. Field r ==> !p q. ipoly p /\ ipoly q ==> pcoprime p q \/ (p ~~ q)``,
  metis_tac[poly_irreducible_poly, poly_irreducible_gcd, poly_field_divides_antisym, poly_coprime_sym]);

(* Theorem: Field r ==> !p q. monic p /\ ipoly p /\ monic q /\ ipoly q ==> pcoprime p q \/ (p = q) *)
(* Proof:
    Note ipoly p /\ ipoly q            by given
     ==> pcoprime p q \/ (p ~~ q)      by poly_irreducibles_coprime
    With monic p /\ monic q            by given
    then p ~~ q ==> (p = q)            by poly_unit_eq_monic_eq
*)
val poly_monic_irreducibles_coprime = store_thm(
  "poly_monic_irreducibles_coprime",
  ``!r:'a field. Field r ==> !p q. monic p /\ ipoly p /\ monic q /\ ipoly q ==> pcoprime p q \/ (p = q)``,
  metis_tac[poly_irreducibles_coprime, poly_unit_eq_monic_eq, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* GCD divisibility condition for unity polynomials.                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ m < n ==> (pgcd (unity n) (unity m) ~~ pgcd (unity m) (unity (n - m)) *)
(* Proof:
   Lemma (an identity for later use)
   To show: X ** n - |1| - X ** (n - m) * (X ** m - |1|) = X ** (n - m) - |1|
      Note m < n means m <= n                                  by LESS_IMP_LESS_OR_EQ
      Use assertion to prove the identity:
        X ** n - |1| - X ** (n - m) * (X ** m - |1|)
      = X ** n - |1| - (X ** (n - m) * X ** m - X ** (n - m))  by poly_mult_rsub, poly_mult_rone
      = X ** n - |1| - (X ** (n - m + m) - X ** (n - m))       by poly_exp_add
      = X ** n - |1| - (X ** n - X ** (n - m))                 by SUB_ADD, m <= n
      = X ** n - |1| - (X ** n - (X ** (n - m) - |1| + |1|))   by poly_sub_add
      = X ** n - |1| - (X ** n - ( |1| + (X ** (n - m) - |1|))) by poly_add_comm
      = X ** n - |1| - (X ** n - |1| - (X ** (n - m) - |1|))   by poly_sub_plus
      = X ** n - |1| - (X ** n - |1|) + (X ** (n - m) - |1|)   by poly_sub_minus
      = X ** (n - m) - |1|                                     by poly_sub_eq, poly_add_lzero

   Use lemma to prove the GCD identity:
        pgcd (X ** n - |1|) (X ** m - |1|)
      = pgcd (X ** m - |1|) (X ** n - |1|)                     by poly_gcd_sym
     ~~ pgcd (X ** m - |1|) ((X ** n - |1|) - X ** (n - m) * (X ** m - |1|))  by poly_gcd_reduction
      = pgcd (X ** m - |1|) (X ** (n - m) - |1|)               by lemma
*)
val poly_unity_gcd_reduction = store_thm(
  "poly_unity_gcd_reduction",
  ``!r:'a field. Field r ==> !n m. 0 < m /\ m < n ==>
    pgcd (unity n) (unity m) ~~ pgcd (unity m) (unity (n - m))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `m <= n` by decide_tac >>
  `!k. poly (X ** k) /\ poly (X ** k - |1|)` by rw[] >>
  `poly X /\ poly |1|` by rw[] >>
  `(X ** n - |1|) - X ** (n - m) * (X ** m - |1|) = X ** (n - m) - |1|` by
  (`X ** n - |1| - X ** (n - m) * (X ** m - |1|) = X ** n - |1| - (X ** (n - m) * X ** m - X ** (n - m))` by rw_tac std_ss[poly_mult_rsub, poly_mult_rone] >>
  `_ = X ** n - |1| - (X ** (n - m + m) - X ** (n - m))` by rw_tac std_ss[poly_exp_add] >>
  `_ = X ** n - |1| - (X ** n - X ** (n - m))` by rw_tac std_ss[SUB_ADD] >>
  `_ = X ** n - |1| - (X ** n - (X ** (n - m) - |1| + |1|))` by rw_tac std_ss[poly_sub_add] >>
  `_ = X ** n - |1| - (X ** n - ( |1| + (X ** (n - m) - |1|)))` by rw_tac std_ss[poly_add_comm] >>
  `_ = X ** n - |1| - (X ** n - |1| - (X ** (n - m) - |1|))` by rw_tac std_ss[poly_sub_plus] >>
  `_ = X ** n - |1| - (X ** n - |1|) + (X ** (n - m) - |1|)` by rw_tac std_ss[poly_sub_minus] >>
  `_ = X ** (n - m) - |1|` by rw_tac std_ss[poly_sub_eq, poly_add_lzero] >>
  rw_tac std_ss[]) >>
  metis_tac[poly_gcd_sym, poly_gcd_reduction]);

(* Theorem: Field r ==> !n m. pgcd (unity n) (unity m) ~~ (unity (gcd n m)) *)
(* Proof:
   By complete induction on (n + m):
   Induction hypothesis: !m'. m' < n + m ==>
                         !n m. (m' = n + m) ==> (pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|)
   Idea: if 0 < m, n < n + m. Put last n = m, m = n - m. That is m' = m + (n - m) = n.
   Also  if 0 < n, m < n + m. Put last n = n, m = m - n. That is m' = n + (m - n) = m.

   Anyway, to apply poly_unity_gcd_reduction, need 0 < n or 0 < m.
   So take care of these special cases first.

   Case: n = 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
         LHS = pgcd (X ** 0 - |1|) (X ** m - |1|)
             = pgcd ( |1| - |1|) (X ** m - |1|)     by poly_exp_0
             = pgcd |0| (X ** m - |1|)              by poly_sub_eq
             = X ** m - |1|                         by poly_gcd_zero
             = X ** (gcd 0 m) - |1| = RHS           by GCD_0L
         Hence they are unit-equal                  by poly_eq_unit_eq
   Case: m = 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
         LHS = pgcd (X ** n - |1|) (X ** 0 - |1|)
             = pgcd (X ** n - |1|) ( |1| - |1|)     by poly_exp_0
             = pgcd (X ** n - |1|) |0|              by poly_sub_eq
             = X ** n - |1|                         by poly_gcd_zero
             = X ** (gcd n 0) - |1| = RHS           by GCD_0R
         Hence they are unit-equal                  by poly_eq_unit_eq
   Case: m <> 0 /\ n <> 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
      That is, 0 < n, and 0 < m
          also n < n + m, and m < n + m             by arithmetic

      Use trichotomy of numbers:                    by LESS_LESS_CASES
      Case: n = m /\ m <> 0 /\ n <> 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
         LHS = pgcd (X ** m - |1|) (X ** m - |1|)
             ~~ X ** m - |1|                        by poly_gcd_refl
             = X ** (gcd m m) - |1| = RHS           by GCD_REF
         Hence they are unit-equal                  by poly_eq_unit_eq

      Case: m < n /\ m <> 0 /\ n <> 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
         Since n < n + m                            by 0 < m
           and m + (n - m) = (n - m) + m            by ADD_COMM
                           = n                      by SUB_ADD, m <= n
            pgcd (X ** n - |1|) (X ** m - |1|)
         ~~ pgcd ((X ** m - |1|)) (X ** (n - m) - |1|) by poly_unity_gcd_reduction
         ~~ X ** gcd m (n - m) - |1|                by induction hypothesis, m + (n - m) = n
         = X ** gcd m n - |1|                       by GCD_SUB_R, m <= n
         = X ** gcd n m - |1|                       by GCD_SYM
         Hence they are unit-equal                  by poly_eq_unit_eq

      Case: n < m /\ m <> 0 /\ n <> 0 ==> pgcd (X ** n - |1|) (X ** m - |1|) ~~ X ** gcd n m - |1|
         Since m < n + m                            by 0 < n
           and n + (m - n) = (m - n) + n            by ADD_COMM
                           = m                      by SUB_ADD, n <= m
           pgcd (X ** n - |1|) (X ** m - |1|)
        =  pgcd (X ** m - |1|) (X ** n - |1|)          by poly_gcd_sym
        ~~ pgcd ((X ** n - |1|)) (X ** (m - n) - |1|)  by poly_unity_gcd_reduction
        ~~ X ** gcd n (m - n) - |1|                 by induction hypothesis, n + (m - n) = m
        = X ** gcd n m - |1|                        by GCD_SUB_R, n <= m
*)
val poly_unity_gcd_identity = store_thm(
  "poly_unity_gcd_identity",
  ``!r:'a field. Field r ==> !n m. pgcd (unity n) (unity m) ~~ (unity (gcd n m))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `!k. poly (X ** k - |1|)` by rw[] >>
  completeInduct_on `n + m` >>
  rw_tac std_ss[] >>
  Cases_on `n = 0` >| [
    `pgcd (X ** n - |1|) (X ** m - |1|) = pgcd |0| (X ** m - |1|)` by rw[] >>
    `_ = X ** m - |1|` by rw[poly_gcd_zero] >>
    rw[poly_eq_unit_eq],
    Cases_on `m = 0` >| [
      `pgcd (X ** n - |1|) (X ** m - |1|) = pgcd (X ** n - |1|) |0|` by rw[] >>
      `_ = X ** n - |1|` by rw[poly_gcd_zero] >>
      rw[poly_eq_unit_eq],
      `(n = m) \/ (m < n) \/ (n < m)` by metis_tac[LESS_LESS_CASES] >| [
        `pgcd (X ** m - |1|) (X ** m - |1|) ~~ X ** m - |1|` by rw[poly_gcd_refl] >>
        metis_tac[poly_eq_unit_eq, GCD_REF],
        `0 < m /\ n < n + m` by decide_tac >>
        `m <= n` by decide_tac >>
        `m + (n - m) = n` by metis_tac[SUB_ADD, ADD_COMM] >>
        `pgcd (X ** n - |1|) (X ** m - |1|) ~~ pgcd ((X ** m - |1|)) (X ** (n - m) - |1|)` by rw[poly_unity_gcd_reduction] >>
        `pgcd ((X ** m - |1|)) (X ** (n - m) - |1|) ~~ X ** gcd m (n - m) - |1|` by metis_tac[] >>
        `X ** gcd m (n - m) - |1| = X ** gcd m n - |1|` by rw[GCD_SUB_R] >>
        metis_tac[poly_eq_unit_eq, poly_unit_eq_trans, poly_gcd_poly, GCD_SYM],
        `0 < n /\ m < n + m` by decide_tac >>
        `n <= m` by decide_tac >>
        `n + (m - n) = m` by metis_tac[SUB_ADD, ADD_COMM] >>
        `pgcd (X ** n - |1|) (X ** m - |1|) = pgcd (X ** m - |1|) (X ** n - |1|)` by rw[poly_gcd_sym] >>
        `pgcd (X ** m - |1|) (X ** n - |1|) ~~ pgcd ((X ** n - |1|)) (X ** (m - n) - |1|)` by rw[poly_unity_gcd_reduction] >>
        `pgcd ((X ** n - |1|)) (X ** (m - n) - |1|) ~~ X ** gcd n (m - n) - |1|` by metis_tac[] >>
        `X ** gcd n (m - n) - |1| = X ** gcd n m - |1|` by rw[GCD_SUB_R] >>
        metis_tac[poly_eq_unit_eq, poly_unit_eq_trans, poly_gcd_poly]
      ]
    ]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n m. (unity n) pdivides (unity m) <=> n divides m *)
(* Proof:
   If part: X ** n - |1| pdivides X ** m - |1| ==> n divides m
      If n = 0,
         X ** n - |1| = |0|                       by poly_unity_eq_zero
         and |0| pdivides (X ** m - |1|)
         ==> X ** m - |1| = |0|                   by poly_zero_divides
         so m = 0                                 by poly_unity_eq_zero
         and 0 divides 0 is true                  by ZERO_DIVIDES
      If n <> 0, 0 < n.
      Let m = q * n + k   for some q, with k < n  by DA (division algorithm), 0 < n

         X ** m - |1|
       = X ** (q * n + k) - |1|                               by above
       = X ** (q * n) * X ** k - |1|                          by poly_exp_add
       = X ** (q * n) * X ** k + (-(X ** k) + X ** k) - |1|   by poly_add_lneg
       = X ** ((q * n) * X ** k - (X ** k) + X ** k) - |1|    by poly_add_assoc, poly_sub_def
       = X ** (q * n) * X ** k - (X ** k) + (X ** k - |1|)    by poly_add_sub_assoc
       = X ** (q * n) * X ** k - |1| * (X ** k) + (X ** k - |1|)     by poly_mult_lone
       = (X ** (q * n) - |1|) * X ** k + (X ** k - |1|)       by poly_mult_lsub
      Hence
         X ** k - |1|
       = (X ** m - |1|) - (X ** (q * n) - |1|) * X ** k                 by poly_sub_eq_add
       = (X ** m - |1|) * |1| + -((X ** (q * n) - |1|) * X ** k)        by poly_mult_rone, poly_sub_def
       = (X ** m - |1|) * |1| + (X ** (q * n) - |1|) * (-(X ** k))      by poly_neg_mult
       = (X ** m - |1|) * |1| + (X ** (q * n) - |1|) * (-(X ** k))      by MULT_COMM

      Show: k = 0
         By contradiction, assum k <> 0.
         Then X ** k - |1| <> |0|                           by poly_unity_eq_zero, k <> 0
         also X ** n - |1| <> |0|                           by poly_unity_eq_zero, n <> 0
      Now  (X ** n - |1|) pdivides (X ** m - |1|)           by given
      and  (X ** n - |1|) pdivides (X ** (n * q) - |1|)     by poly_unity_1_divides
      Hence (X ** n - |1|) pdivides (X ** k - |1|)          by poly_divides_linear
        and monic (X ** n - |1|) /\ monic (X ** k - |1|)    by poly_monic_X_exp_n_sub_c, 0 < k
      Giving  deg (X ** n - |1|) <= deg (X ** k - |1|)      by poly_monic_divides_deg_le, unity k <> |0|
         or                    n <= k                       by poly_deg_X_exp_n_sub_c
      which contradicts k < n.

      Hence k = 0, i.e. m = q * n                           by ADD_0
         or n divides m                                     by divides_def

  Only-if part: n divides m ==> X ** n - |1| pdivides X ** m - |1|
     Let m = q * n  for some q                              by divides_def
     Then (X ** n - |1|) pdivides (X ** (n * q) - |1|       by poly_unity_divides
       or (X ** n - |1|) pdivides (X ** m - |1|)            by MULT_COMM
*)
val poly_unity_divisibility = store_thm(
  "poly_unity_divisibility",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n m. (unity n) pdivides (unity m) <=> n divides m``,
  rpt strip_tac >>
  `!k. poly (X ** k - |1|)` by rw[] >>
  `poly X /\ poly (X ** n) /\ ( |1| = ###1)` by rw[poly_ring_sum_1] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    Cases_on `n = 0` >-
    metis_tac[poly_unity_eq_zero, poly_zero_divides, ZERO_DIVIDES] >>
    `0 < n` by decide_tac >>
    `?q k. (m = q * n + k) /\ k < n` by metis_tac[DA] >>
    `poly X /\ !k. poly (X ** k)` by rw[] >>
    `X ** m - |1| = X ** (q * n + k) - |1|` by rw[] >>
    `_ = X ** (q * n) * X ** k - |1|` by rw_tac std_ss[poly_exp_add] >>
    `_ = X ** (q * n) * X ** k + (-(X ** k) + X ** k) - |1|` by rw_tac std_ss[poly_add_lneg, poly_add_rzero, poly_mult_poly] >>
    `_ = X ** (q * n) * X ** k - (X ** k) + X ** k - |1|` by rw_tac std_ss[poly_add_assoc, poly_sub_def, poly_neg_poly, poly_mult_poly] >>
    `_ = X ** (q * n) * X ** k - (X ** k) + (X ** k - |1|)` by rw_tac std_ss[poly_add_sub_assoc, poly_sub_poly, poly_mult_poly, poly_one_poly] >>
    `_ = X ** (q * n) * X ** k - |1| * (X ** k) + (X ** k - |1|)` by rw_tac std_ss[poly_mult_lone] >>
    `_ = (X ** (q * n) - |1|) * X ** k + (X ** k - |1|)` by rw_tac std_ss[poly_mult_lsub, poly_one_poly] >>
    `X ** k - |1| = (X ** m - |1|) - (X ** (q * n) - |1|) * X ** k` by metis_tac[poly_sub_eq_add, poly_mult_poly] >>
    `_ = (X ** m - |1|) * |1| + (X ** (n * q) - |1|) * (-(X ** k))` by metis_tac[poly_mult_rone, poly_sub_def, poly_neg_mult, MULT_COMM] >>
    `k = 0` by
  (spose_not_then strip_assume_tac >>
    `0 < k` by decide_tac >>
    `X ** k - |1| <> |0| /\ X ** n - |1| <> |0|` by metis_tac[poly_unity_eq_zero] >>
    `(X ** n - |1|) pdivides (X ** (n * q) - |1|)` by rw[poly_unity_divides] >>
    `(X ** n - |1|) pdivides (X ** k - |1|)` by metis_tac[poly_divides_linear, poly_one_poly, poly_neg_poly] >>
    `monic (X ** n - |1|) /\ monic (X ** k - |1|)` by metis_tac[poly_monic_X_exp_n_sub_c] >>
    `deg (X ** n - |1|) <= deg (X ** k - |1|)` by rw[poly_monic_divides_deg_le] >>
    `n <= k` by metis_tac[poly_deg_X_exp_n_sub_c] >>
    decide_tac) >>
    metis_tac[divides_def, ADD_0],
    full_simp_tac std_ss[divides_def, poly_unity_divides, MULT_COMM]
  ]);

(* ------------------------------------------------------------------------- *)
(* GCD divisibility condition for master polynomials.                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !k n m. pgcd (master (k ** n)) (master (k ** m)) ~~ master (k ** gcd n m) *)
(* Proof:
   If k = 0, need to consider cases of ZERO_EXP.
      If n = 0,
         Then X ** k ** n - X = |0|           by ZERO_EXP, poly_exp_1
          and gcd n m = m                     by GCD_0L
              pgcd |0| (X ** (k ** m) - X)
            = (X ** (k ** m) - X)             by poly_gcd_zero
            ~~ X ** (k ** (gcd n m)) - X      by poly_unit_eq_refl
      If m = 0, similar considerations        by GCD_0R
      If n <> 0, m <> 0
         Then gcd n m <> 0                    by GCD_EQ_0
          and X ** k ** n - X = |1| - X       by ZERO_EXP, poly_exp_0
          and X ** k ** m - X = |1| - X       by ZERO_EXP, poly_exp_0
          and X ** k ** (gcd n m) - X = |1| - X       by ZERO_EXP, poly_exp_0
        Hence pgcd ( |1| - X) ( |1| - X) ~~ ( |1| - X)   by poly_gcd_refl
   If k <> 0, 0 < k.
   Note 0 < k ==> !h. 0 < k ** h         by EXP_POS
    and !h. 0 < h ==> SUC (h - 1) = h    by ADD1, SUB_ADD
     pgcd (X ** (k ** n) - X) (X ** (k ** m) - X)
   = pgcd X * (X ** (k ** n - 1) - |1|) X * (X ** (k ** m - 1) - |1|)   by poly_master_factors
   ~~ X * pgcd (X ** (k ** n - 1) - |1|) (X ** (k ** m - 1) - |1|)      by poly_gcd_common_factor
   ~~ X * (X ** (gcd (k ** n - 1) (k ** m - 1)) - |1|)     by poly_unity_gcd_identity
    = X * (X ** (k ** (gcd n m) - 1) - |1|)                by power_predecessor_gcd_identity
    = X * X ** (k ** (gcd n m) - 1) - X * |1|              by poly_mult_rsub
    = X * X ** (k ** (gcd n m) - 1) - X                    by poly_mult_rone
    = X ** SUC (k ** (gcd n m) - 1) - X                    by poly_exp_SUC
    = X ** (k ** (gcd n m)) - X                            by above
*)
val poly_master_gcd_identity = store_thm(
  "poly_master_gcd_identity",
  ``!r:'a field. Field r ==>
    !k n m. pgcd (master (k ** n)) (master (k ** m)) ~~ master (k ** gcd n m)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  Cases_on `k = 0` >| [
    Cases_on `n = 0` >| [
      `X ** k ** n - X = |0|` by rw_tac std_ss[ZERO_EXP, poly_exp_1, poly_X, poly_sub_eq] >>
      `gcd n m = m` by rw[] >>
      `poly (X ** k ** m - X)` by rw[] >>
      metis_tac[poly_gcd_zero, poly_unit_eq_refl],
      Cases_on `m = 0` >| [
        `X ** k ** m - X = |0|` by rw_tac std_ss[ZERO_EXP, poly_exp_1, poly_X, poly_sub_eq] >>
        `gcd n m = n` by rw[] >>
        `poly (X ** k ** n - X)` by rw[] >>
        metis_tac[poly_gcd_zero, poly_unit_eq_refl],
        `gcd n m <> 0` by rw[] >>
        `X ** k ** n - X = |1| - X` by rw_tac std_ss[ZERO_EXP, poly_exp_0] >>
        `X ** k ** m - X = |1| - X` by rw_tac std_ss[ZERO_EXP, poly_exp_0] >>
        `X ** k ** (gcd n m) - X = |1| - X` by rw_tac std_ss[ZERO_EXP, poly_exp_0] >>
        `poly ( |1| - X)` by rw[] >>
        metis_tac[poly_gcd_refl]
      ]
    ],
    `0 < k` by decide_tac >>
    `!h. 0 < k ** h` by rw[EXP_POS] >>
    `!h. 0 < h ==> (SUC (h - 1) = h)` by decide_tac >>
    qabbrev_tac `p = (X ** (k ** n - 1) - |1|)` >>
    qabbrev_tac `q = (X ** (k ** m - 1) - |1|)` >>
    `X ** (k ** n) - X = X * p` by rw_tac std_ss[poly_master_factors, Abbr`p`] >>
    `X ** (k ** m) - X = X * q` by rw_tac std_ss[poly_master_factors, Abbr`q`] >>
    `poly X /\ !h. poly (X ** h) /\ poly (X ** h - |1|)` by rw[] >>
    `poly p /\ poly q` by rw[Abbr`p`, Abbr`q`] >>
    `pgcd (X * p) (X * q) ~~ X * pgcd p q` by rw[poly_gcd_common_factor] >>
    `X * pgcd p q ~~ X * (X ** (gcd (k ** n - 1) (k ** m - 1)) - |1|)` by rw[poly_unity_gcd_identity, poly_unit_eq_mult_comm, Abbr`p`, Abbr`q`] >>
    `X * (X ** (gcd (k ** n - 1) (k ** m - 1)) - |1|) = X * (X ** (k ** (gcd n m) - 1) - |1|)` by rw_tac std_ss[power_predecessor_gcd_identity] >>
    `_ = X * X ** (k ** (gcd n m) - 1) - X` by rw[poly_mult_rsub] >>
    `_ = X ** SUC (k ** (gcd n m) - 1) - X` by rw[poly_exp_SUC] >>
    metis_tac[poly_eq_unit_eq, poly_unit_eq_trans, poly_gcd_poly, poly_mult_poly]
  ]);

(* Theorem: Field r ==> !k. 1 < k ==>
            !n m. master (k ** n) pdivides master (k ** m) <=> n divides m *)
(* Proof:
   If part: (X ** (k ** n) - X) pdivides (X ** (k ** m) - X) ==> n divides m
   Note 1 < k means 0 < k,
    and 1 < k ==> !h. 0 < h ==> 1 < k ** h  by ONE_LT_EXP
   If n = 0,
      then k ** n = 1                    by EXP
      then X ** (k ** n) - X
         = X ** 1 - X                    by k ** n = 1
         = X - X                         by poly_exp_1, poly_X
         = |0|                           by poly_sub_eq
      Hence X ** (k ** m) - X = |0|      by poly_zero_divides
         or X ** (k ** m) = X            by poly_sub_eq_zero
                          = X ** 1       by poly_exp_1
       thus        k ** m = 1            by poly_X_exp_eq, #1 <> #0
      Giving       k ** m = k ** n       by k ** n = 1
         or             m = n            by EXP_BASE_INJECTIVE, 1 < k.
         so        n divides m           by DIVIDES_REFL
   If n <> 0, 0 < n
      thus 1 < k ** n                    by above, ONE_LT_EXP
      also gcd n m <> 0 since n <> 0     by GCD_EQ_0
      thus 1 < k ** gcd n m              by above, ONE_LT_EXP
       (X ** (k ** n) - X) pdivides (X ** (k ** m) - X)
   <=> pgcd (X ** (k ** n) - X) (X ** (k ** m) - X) ~~ X ** (k ** n) - X         by poly_divides_iff_gcd_fix
   But pgcd (X ** (k ** n) - X) (X ** (k ** m) - X) ~~ X ** (k ** gcd n m) - X   by poly_master_gcd_identity
    so X ** (k ** n) - X ~~ X ** (k ** gcd n m) - X    by poly_unit_eq_sym, poly_unit_eq_trans, poly_gcd_poly

   Since monic (X ** (k ** n) - X)                     by poly_master_monic, 1 < k ** n
     and monic (X ** (k ** gcd n m) - X)               by poly_master_monic, 1 < k ** gcd n m
      so X ** (k ** n) - X = X ** (k ** gcd n m) - X   by poly_unit_eq_monic_eq
    Thus     X ** (k ** n) = X ** (k ** gcd n m)       by poly_sub_add
   Giving           k ** n = k ** gcd n m              by poly_X_exp_eq, #1 <> #0
      or                 n = gcd n m                   by EXP_BASE_INJECTIVE, 1 < k
      so                 n divides m                   by divides_iff_gcd_fix
   Only-if part: n divides m ==> (X ** (k ** n) - X) pdivides (X ** (k ** m) - X)
      Just reverse the above steps.
      Since n divides m ==> gcd n m = n                        by divides_iff_gcd_fix
      Hence pgcd (X ** (k ** n) - X) (X ** (k ** m) - X)
         ~~ X ** (gcd n m) - X                                 by poly_unity_gcd_identity
          = X ** n - X                                         by above
         or (X ** (k ** n) - X) pdivides (X ** (k ** m) - X)   by poly_divides_iff_gcd_fix
*)
val poly_master_divisibility = store_thm(
  "poly_master_divisibility",
  ``!r:'a field. Field r ==> !k. 1 < k ==>
   !n m. master (k ** n) pdivides master (k ** m) <=> n divides m``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly X /\ !k. poly (X ** k) /\ poly (X ** k - |1|) /\ poly(X ** k - X)` by rw[] >>
  Cases_on `n = 0` >| [
    rw_tac std_ss[EXP, poly_exp_1, poly_sub_eq, EQ_IMP_THM] >| [
      `X ** k ** m - X = |0|` by rw[GSYM poly_zero_divides] >>
      `X ** k ** m = X ** 1` by metis_tac[poly_sub_eq_zero, poly_exp_1] >>
      `k ** m = 1` by metis_tac[poly_X_exp_eq] >>
      `k <> 1` by decide_tac >>
      `m = 0` by metis_tac[EXP_EQ_1] >>
      rw[ZERO_DIVIDES],
      `m = 0` by rw[GSYM ZERO_DIVIDES] >>
      `X ** k ** 0 - X = |0|` by rw_tac std_ss[EXP, poly_exp_1, poly_sub_eq] >>
      rw[poly_zero_divides]
    ],
    `0 < n /\ 0 < k` by decide_tac >>
    `!h. 0 < h ==> 1 < k ** h` by rw[ONE_LT_EXP] >>
    `gcd n m <> 0` by rw[GCD_EQ_0] >>
    `0 < gcd n m` by decide_tac >>
    rw_tac std_ss[EQ_IMP_THM] >| [
      `pgcd (X ** (k ** n) - X) (X ** (k ** m) - X) ~~ X ** (k ** n) - X` by rw[GSYM poly_divides_iff_gcd_fix] >>
      `pgcd (X ** (k ** n) - X) (X ** (k ** m) - X) ~~ X ** (k ** gcd n m) - X` by rw[poly_master_gcd_identity] >>
      `X ** (k ** n) - X ~~ X ** (k ** gcd n m) - X` by metis_tac[poly_unit_eq_sym, poly_unit_eq_trans, poly_gcd_poly] >>
      `monic (X ** (k ** n) - X)` by rw[poly_master_monic] >>
      `monic (X ** (k ** gcd n m) - X)` by rw[poly_master_monic] >>
      `X ** (k ** n) - X = X ** (k ** gcd n m) - X` by metis_tac[poly_unit_eq_monic_eq] >>
      `X ** (k ** n) = X ** (k ** gcd n m)` by metis_tac[poly_sub_add] >>
      `k ** n = k ** gcd n m` by metis_tac[poly_X_exp_eq] >>
      `n = gcd n m` by metis_tac[EXP_BASE_INJECTIVE] >>
      rw[divides_iff_gcd_fix],
      `n = gcd n m` by rw[GSYM divides_iff_gcd_fix] >>
      `pgcd (X ** (k ** n) - X) (X ** (k ** m) - X) ~~ X ** (k ** n) - X` by metis_tac[poly_master_gcd_identity] >>
      rw[poly_divides_iff_gcd_fix]
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Monic Polynomial GCD (except when both are zero)                          *)
(* ------------------------------------------------------------------------- *)

(* Need to define a monic polynomial gcd. Take care of zero gcd. *)
val poly_monic_gcd_def = Define`
    poly_monic_gcd (r:'a ring) p q = let d = pgcd p q in if (d = |0|) then |0| else ( |/ (lead d)) * d
`;
(* Overload monic polynomial gcd similar to poly_gcd *)
val _ = overload_on("mpgcd", ``poly_monic_gcd r``);

(* Theorem: (pgcd p q = |0|) ==> (mpgcd p q = |0|) *)
(* Proof: by poly_monic_gcd_def *)
val poly_monic_gcd_zero_zero = store_thm(
  "poly_monic_gcd_zero_zero",
  ``!r:'a ring. !p q. (pgcd p q = |0|) ==> (mpgcd p q = |0|)``,
  rw_tac std_ss[poly_monic_gcd_def]);
(* Note: (pgcd p q = |0|) <=> (mpgcd p q = |0|) is poly_monic_gcd_eq_zero, need more conditions. *)

(* Theorem: pgcd p q <> |0| ==> (mpgcd p q = |/ (lead (pgcd p q)) * pgcd p q) *)
(* Proof: by poly_monic_gcd_def *)
val poly_monic_gcd_nonzero = store_thm(
  "poly_monic_gcd_nonzero",
  ``!r:'a ring. !p q. pgcd p q <> |0| ==> (mpgcd p q = |/ (lead (pgcd p q)) * pgcd p q)``,
  rw[poly_monic_gcd_def]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ ~((p = |0|) /\ (q = |0|)) ==> monic (mpgcd p q) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                         by poly_gcd_poly
   Since not both p, q are |0|,
     ==> d <> |0|                       by poly_gcd_eq_zero
    Thus mpgcd p q = |/ (lead d) * d    by poly_monic_gcd_def
   Hence monic (mpgcd p q)              by poly_monic_by_cmult
*)
val poly_monic_gcd_monic = store_thm(
  "poly_monic_gcd_monic",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ ~((p = |0|) /\ (q = |0|)) ==> monic (mpgcd p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `d <> |0|` by metis_tac[poly_gcd_eq_zero] >>
  rw_tac std_ss[poly_monic_gcd_def] >>
  rw_tac std_ss[poly_monic_by_cmult]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> poly (mpgcd p q) *)
(* Proof:
   If (p = |0|) /\ (q = |0|),
      Then pgcd p q = |0|          by poly_gcd_eq_zero
      Thus mpgcd p q = |0|         by poly_monic_gcd_def
       and poly |0|                by poly_zero_poly
   If (p <> |0|) \/ (q <> |0|),
      Then monic (mpgcd p q)       by poly_monic_gcd_monic
        so poly (mpgcd p q)        by poly_monic_poly
*)
val poly_monic_gcd_poly = store_thm(
  "poly_monic_gcd_poly",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> poly (mpgcd p q)``,
  rpt strip_tac >>
  Cases_on `(p = |0|) /\ (q = |0|)` >| [
    `pgcd p q = |0|` by rw[poly_gcd_eq_zero] >>
    rw_tac std_ss[poly_monic_gcd_def, poly_zero_poly],
    metis_tac[poly_monic_gcd_monic, poly_monic_poly]
  ]);

(* export simple result *)
val _ = export_rewrites["poly_monic_gcd_poly"];

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |0|) <=> (pgcd p q = |0|)) *)
(* Proof:
   Let d = pgcd p q.
   If part: (mpgcd p q = |0|) ==> (pgcd p q = |0|)
        If d = |0|,
           Then mpgcd p q = |0|    by poly_monic_gcd_def
             so T ==> T
        If d <> |0|,
      Then poly d                  by poly_gcd_poly
       and (lead d) <> #0          by poly_lead_nonzero
      with (lead d) IN R           by poly_lead_element
        so (lead d) IN R+          by field_nonzero_eq
      Thus |/ (lead d) IN R        by field_inv_element
       and ( |/ (lead d) * (lead d) = #1)        by field_mult_linv
      Hence mpgcd p q = |/ (lead d) * d <> |0|   by poly_cmult_eq_zero

   Only-if part: (pgcd p q = |0|) ==> (mpgcd p q = |0|)
      Note d = |0| ==> mpgcd p q = |0|           by poly_monic_gcd_def
*)
val poly_monic_gcd_eq_zero = store_thm(
  "poly_monic_gcd_eq_zero",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |0|) <=> (pgcd p q = |0|))``,
  rw_tac std_ss[poly_monic_gcd_def] >>
  rw_tac std_ss[EQ_IMP_THM] >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `(lead d) IN R+` by rw[field_nonzero_eq] >>
  `|/ (lead d) IN R /\ ( |/ (lead d) * (lead d) = #1)` by metis_tac[field_inv_element, field_mult_linv] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  metis_tac[poly_cmult_eq_zero]);

(* Theorem: Field r ==> !p. monic p ==> (mpgcd p |0| = p) /\ (mpgcd |0| p = p) *)
(* Proof:
   Since (pgcd p |0| = p) /\ (pgcd |0| p = p)   by poly_gcd_zero
     and monic p ==> p <> |0|                   by poly_monic_nonzero
   Hence mpgcd p |0| = |/ (lead p) * p
                     = ( |/ #1) * p             by poly_monic_lead
                     = #1 * p                   by field_inv_one
                     = p                        by poly_cmult_lone
     and mpgcd |0| p = |/ (lead p) * p = p      by the same argument
*)
val poly_monic_gcd_zero = store_thm(
  "poly_monic_gcd_zero",
  ``!r:'a field. Field r ==> !p. monic p ==> (mpgcd p |0| = p) /\ (mpgcd |0| p = p)``,
  rw[poly_gcd_zero, poly_monic_nonzero, poly_monic_gcd_def]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |1|) <=> (pgcd p q ~~ |1|)) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d         by poly_gcd_poly
   If part: mpgcd p q = |1| ==> d ~~ |1|
      Since mpgcd p q <> |0|                   by poly_one_ne_poly_zero
         so d <> |0|                           by poly_monic_gcd_eq_zero
       then mpgcd p q = |/ (lead d) * d        by poly_monic_gcd_def
       Thus |/ (lead d) * d = |1|              by mpgcd p q = |1|
      Since (lead d) <> #0                     by poly_lead_nonzero
       with (lead d) IN R                      by poly_lead_element
         so (lead d) IN R+                     by field_nonzero_eq
       Thus |/ (lead d) IN R                   by field_inv_element
        and |/ (lead d) IN R+                  by field_inv_nonzero
         or |/ (lead d) <> #0                  by field_nonzero_eq
       Hence deg d = deg ( |/ (lead d) * d)    by poly_field_deg_cmult
                   = deg |1| = 0               by poly_deg_one
        Thus upoly d                           by poly_field_units
          or d ~~ |1|                          by poly_unit_eq_one
   Only-if part: d ~~ |1| ==> mpgcd p q = |1|
    Since d ~~ |1|
      ==> upoly d                              by poly_unit_eq_one
      ==> d <> |0| /\ (deg d = 0)              by poly_field_units
     Thus mpgcd p q = |/ (lead d) * d          by poly_monic_gcd_def, d <> |0|
      and goal is: |/ (lead d) * d = |1|

      Now d <> |0| /\ (deg d = 0)
      ==> ?c. c IN R /\ c <> #0 /\ (d = [c])   by poly_deg_eq_0
       so lead d = c                           by poly_lead_const
      and c IN R+                              by field_nonzero_eq
     with |/c * c = #1                         by field_mult_linv
          |/ (lead d) * d
        = |/ c * [c]                           by above
        = [|/c * c]                            by poly_cmult_const_nonzero
        = [#1]                                 by above
        = |1|                                  by poly_one, #1 <> #0.
*)
val poly_monic_gcd_eq_one = store_thm(
  "poly_monic_gcd_eq_one",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> ((mpgcd p q = |1|) <=> (pgcd p q ~~ |1|))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0 /\ |1| <> |0|` by rw[] >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  (`d <> |0| ==> (mpgcd p q = |/ (lead d) * d)` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `d <> |0|` by metis_tac[poly_monic_gcd_eq_zero] >>
    `|/ (lead d) * d = |1|` by metis_tac[] >>
    `(lead d) IN R+` by rw[field_nonzero_eq] >>
    `|/ (lead d) IN R /\ |/ (lead d) <> #0` by metis_tac[field_inv_element, field_inv_nonzero, field_nonzero_eq] >>
    `deg d = 0` by metis_tac[poly_field_deg_cmult, poly_deg_one] >>
    `upoly d` by rw[poly_field_units] >>
    rw[GSYM poly_unit_eq_one],
    `upoly d` by rw[poly_unit_eq_one] >>
    `d <> |0| /\ (deg d = 0)` by metis_tac[poly_field_units] >>
    rw_tac std_ss[poly_monic_gcd_def] >>
    rw_tac std_ss[] >>
    `?c. c IN R /\ c <> #0 /\ (d = [c])` by rw[GSYM poly_deg_eq_0] >>
    `lead d = c` by rw[] >>
    `c IN R+` by rw[field_nonzero_eq] >>
    `|/c * c = #1` by rw[field_mult_linv] >>
    metis_tac[poly_cmult_const_nonzero, poly_one]
  ]);

(* Theorem: Field r ==> !p. poly p ==> (mpgcd p |1| = |1|) /\ (mpgcd |1| p = |1|) *)
(* Proof:
   Since pgcd p |1| ~~ |1| /\ pgcd |1| p ~~ |1|      by poly_gcd_one
      so (mpgcd p |1| = |1|) /\ (mpgcd |1| p = |1|)  by poly_monic_gcd_eq_one
*)
val poly_monic_gcd_one = store_thm(
  "poly_monic_gcd_one",
  ``!r:'a field. Field r ==> !p. poly p ==> (mpgcd p |1| = |1|) /\ (mpgcd |1| p = |1|)``,
  rw[poly_gcd_one, poly_monic_gcd_eq_one]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (pcoprime p q <=> (mpgcd p q = |1|)) *)
(* Proof:
       pcoprime p q
   <=> pgcd p q ~~ |1|     by poly_gcd_one_coprime
   <=> (mpgcd p q = |1|)   by poly_monic_gcd_eq_one
*)
val poly_monic_gcd_one_coprime = store_thm(
  "poly_monic_gcd_one_coprime",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (pcoprime p q <=> (mpgcd p q = |1|))``,
  rw[poly_gcd_one_coprime, poly_monic_gcd_eq_one]);

(* Theorem: Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t ==>
                        (pgcd p q ~~ pgcd s t <=> (mpgcd p q = mpgcd s t)) *)
(* Proof:
   Let d = pgcd p q, e = pgcd s t.
   Note poly d                   by poly_gcd_poly
    and poly e                   by poly_gcd_poly
   If part: d ~~ e ==> mpgcd p q = mpgcd s t
      If (s = |0|) /\ (t = |0|),
         Then e = |0|            by poly_gcd_eq_zero
          and d = |0|            by poly_unit_eq_zero
         Thus mpgcd p q = |0| = mpgcd s t    by poly_monic_gcd_def
      If ~((s = |0|) /\ (t = |0|)),
         Then e <> |0|           by poly_gcd_eq_zero
          and d <> |0|           by poly_unit_eq_zero, poly_unit_eq_sym
         Thus lead d <> #0 /\ lead e <> #0    by poly_lead_nonzero
           so lead d IN R+ /\ lead e IN R+    by field_nonzero_eq
         also ?u. upoly u /\ (d = u * e)      by poly_unit_eq_property
          Now lead d = lead u * lead e        by poly_lead_mult
           so lead u <> #0, or lead u IN R+   by field_mult_eq_zero
           so mpgcd p q = |/ (lead d) * d     by poly_monic_gcd_def
                        = |/ (lead u * lead e) * (u * e)          by above
                        = |/ (lead u) * |/ (lead e) * (u * e)     by field_inv_mult
                        = |/ (lead u) * ( |/ (lead e) * (u * e))  by poly_cmult_cmult
                        = |/ (lead u ) * (u * ( |/ (lead e) * e)) by poly_mult_cmult
                        = |/ (lead u) * u * ( |/ (lead e) * e)    by poly_cmult_mult
                        = |/ (lead u) * u * mpgcd s t             by poly_monic_gcd_def
          But ?c. c IN R /\ c <> #0 /\ (u = [c])     by poly_field_unit_alt
          and lead u = c                             by poly_lead_const
           so |/ (lead u) * u = |/ c * [c]
                              = [|/ c * c]           by poly_cmult_const_nonzero
                              = [#1]                 by field_mult_linv
                              = |1|                  by poly_one_alt
          Hence mpgcd p q = mpgcd s t                by poly_mult_lone, poly_monic_gcd_poly

   Only-if part: mpgcd p q = mpgcd s t ==> d ~~ e
      If d = |0|,
         Then mpgcd p q = |0|        by poly_monic_gcd_eq_zero
          and mpgcd s t = |0|        by equality
         Thus e = |0|                by poly_monic_gcd_eq_zero
          and |0| ~~ |0|             by poly_unit_eq_zero
      If d <> |0|,
         Then mpgcd p q <> |0|       by poly_monic_gcd_eq_zero
          and mpgcd s t <> |0|       by equality
           so e <> |0|               by poly_monic_gcd_eq_zero
         Also mpgcd p q = |/ (lead d) * d     by poly_monic_gcd_nonzero
          and mpgcd s t = |/ (lead e) * e     by poly_monic_gcd_nonzero
         Equality makes
              |/ (lead d) * d = |/ (lead e) * e
         or                 d = (lead d) * |/ (lead e) * e   by field_mult_rinv, poly_cmult_cmult
         or                 d = [c] * e       where c = (lead d) * |/ (lead e) by poly_mult_lconst
         Since c IN R                 by field_mult_element
           and c <> #0,               by field_mult_eq_zero
            so upoly [c]              by poly_field_unit_alt
         Thus d ~~ e                  by poly_unit_eq_property
*)
val poly_gcd_unit_eq_monic_gcd_eq = store_thm(
  "poly_gcd_unit_eq_monic_gcd_eq",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t ==>
      (pgcd p q ~~ pgcd s t <=> (mpgcd p q = mpgcd s t))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = pgcd p q` >>
  qabbrev_tac `e = pgcd s t` >>
  `poly d /\ poly e` by rw[poly_gcd_poly, Abbr`d`, Abbr`e`] >>
  rw[EQ_IMP_THM] >| [
    Cases_on `(s = |0|) /\ (t = |0|)` >| [
      `e = |0|` by rw[poly_gcd_eq_zero, Abbr`e`] >>
      `d = |0|` by rw[GSYM poly_unit_eq_zero] >>
      rw[poly_monic_gcd_def],
      `e <> |0|` by rw[poly_gcd_eq_zero, Abbr`e`] >>
      `d <> |0|` by metis_tac[poly_unit_eq_zero, poly_unit_eq_sym] >>
      `?u. upoly u /\ (d = u * e)` by rw[GSYM poly_unit_eq_property] >>
      `poly u /\ (lead d = lead u * lead e)` by rw[poly_unit_poly] >>
      `?c. c IN R /\ c <> #0 /\ (u = [c])` by rw[GSYM poly_field_unit_alt] >>
      `(lead u = c) /\ lead u IN R+` by rw[field_nonzero_eq] >>
      `lead e IN R+` by rw[field_nonzero_eq] >>
      qabbrev_tac `a = |/ (lead u)` >>
      qabbrev_tac `b = |/ (lead e)` >>
      `a IN R /\ b IN R /\ a <> #0 /\ b <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
      `|/ (lead d) = a * b` by metis_tac[field_inv_mult] >>
      `a * u = |1|` by
  (`a * u = |/ c * [c]` by metis_tac[] >>
      `_ = [|/ c * c]` by rw[poly_cmult_const_nonzero] >>
      `_ = [#1]` by rw[field_mult_linv] >>
      rw[poly_one_alt]) >>
      `mpgcd s t = b * e` by rw[poly_monic_gcd_def] >>
      `mpgcd p q = |/ (lead d) * d` by rw[poly_monic_gcd_def] >>
      `_ = (a * b) * (u * e)` by rw[] >>
      `_ = a * (b * (u * e))` by rw[poly_cmult_cmult] >>
      `_ = a * (u * (b * e))` by rw[poly_mult_cmult] >>
      `_ = a * u * (b * e)` by rw[poly_cmult_mult] >>
      `_ = |1| * mpgcd s t` by metis_tac[] >>
      rw[poly_monic_gcd_poly]
    ],
    Cases_on `d = |0|` >-
    metis_tac[poly_monic_gcd_eq_zero, poly_unit_eq_zero] >>
    `e <> |0|` by metis_tac[poly_monic_gcd_eq_zero] >>
    `lead d IN R+ /\ lead e IN R+ /\ lead d <> #0` by rw[field_nonzero_eq] >>
    `|/ (lead d) IN R /\ |/ (lead e) IN R /\ |/ (lead e) <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
    qabbrev_tac `c = lead d * |/ (lead e)` >>
    `|/ (lead d) * d = |/ (lead e) * e` by metis_tac[poly_monic_gcd_nonzero] >>
    `(lead d) * ( |/ (lead d) * d) = (lead d) * ( |/ (lead e) * e)` by rw[] >>
    `(lead d) * ( |/ (lead d) * d) = (lead d * |/ (lead d) * d)` by rw[GSYM poly_cmult_cmult] >>
    `_ = d` by rw[] >>
    `(lead d) * ( |/ (lead e) * e) = (lead d * |/ (lead e) * e)` by rw[GSYM poly_cmult_cmult] >>
    `(lead d) * ( |/ (lead e) * e) = c * e` by rw_tac std_ss[GSYM poly_cmult_cmult, Abbr`c`] >>
    `_ = [c] * e` by rw[poly_mult_lconst, Abbr`c`] >>
    `c IN R /\ c <> #0` by rw[Abbr`c`, field_mult_eq_zero] >>
    `upoly [c]` by rw[poly_field_unit_alt] >>
    metis_tac[poly_unit_eq_property]
  ]);

(* This looks like an elementary property, but the proof is not that short, like a milestone! *)

(* Theorem: Field r ==> !p. monic p ==> (mpgcd p p = p) *)
(* Proof:
   Let d = pgcd p p.
   If d = |0|,
      Then p = |0|                by poly_gcd_eq_zero, poly_monic_poly
     Hence mpgcd p p|
         = |0|                    by poly_monic_gcd_def, d = |0|
         = p                      by above, p = |0|.
   If d <> |0|,
      Note d ~~ p                 by poly_gcd_refl
       and poly d                 by poly_gcd_poly
       ==> ?c. c IN R /\ c <> #0 /\ (d = c * p)   by poly_field_unit_eq_alt
       ==> c IN R+                by field_nonzero_eq
       and |/ c IN R              by field_inv_element
       and |/ c * c = #1          by field_mult_linv
      Also lead d = c * lead p    by poly_lead_cmult
                  = c * #1        by poly_lead_monic
     Hence mpgcd p p
         = |/ (lead d) * d        by poly_monic_gcd_def
         = |/ c * (c * p)         by above
         = ( |/ c * c) * p        by poly_cmult_cmult
         = #1 * p                 by above, |/ c * c = #1
         = p                      by poly_mult_lone
*)
val poly_monic_gcd_refl = store_thm(
  "poly_monic_gcd_refl",
  ``!r:'a field. Field r ==> !p. monic p ==> (mpgcd p p = p)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p p` >>
  Cases_on `d = |0|` >| [
    `p = |0|` by metis_tac[poly_gcd_eq_zero, poly_monic_poly] >>
    rw_tac std_ss[poly_monic_gcd_def],
    `d ~~ p` by rw[poly_gcd_refl, Abbr`d`] >>
    `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
    `?c. c IN R /\ c <> #0 /\ (d = c * p)` by rw[poly_field_unit_eq_alt] >>
    `|/ c IN R /\ ( |/ c * c = #1)` by metis_tac[field_inv_element, field_mult_linv, field_nonzero_eq] >>
    `lead d = c` by rw[] >>
    (`mpgcd p p = |/ (lead d) * d` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
    `_ = |/ c * (c * p)` by metis_tac[] >>
    rw[poly_cmult_cmult]
  ]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q = mpgcd q p) *)
(* Proof:
   Let d = pgcd p q,
   Then d = pgcd q p                 by poly_gcd_sym
   If d = |0|,
      mpgcd p q = |0|                by poly_monic_gcd_def
                = mpgcd q p          by poly_monic_gcd_def
   If d <> |0|,
      mpgcd p q = |/ (lead d) * d    by poly_monic_gcd_def
                = mpgcd q p          by poly_monic_gcd_def
*)
val poly_monic_gcd_sym = store_thm(
  "poly_monic_gcd_sym",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q = mpgcd q p)``,
  metis_tac[poly_monic_gcd_def, poly_gcd_sym]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> mpgcd p q pdivides p /\ mpgcd p q pdivides q *)
(* Proof:
   Let d = pgcd p q,
   If d = |0|,
      Then mpgcd p q = |0|                    by poly_monic_gcd_def
       But p = |0| /\ q = |0|                 by poly_gcd_eq_zero
       and |0| pdivides |0|                   by poly_zero_divides
   If d <> |0|,
      Then mpgcd p q = ( |/ (lead d) * d)     by poly_monic_gcd_def
      Since lead d <> #0                      by poly_lead_nonzero, d <> |0|
         so lead d IN R+                      by field_nonzero_eq
        and |/ (lead d) IN R+                 by field_inv_nonzero
      Since d pdivides p /\ d pdivides q      by poly_gcd_divides
       thus ( |/ (lead d) * d) pdivides p     by poly_field_cmult_divides
        and ( |/ (lead d) * d) pdivides q     by poly_field_cmult_divides
*)
val poly_monic_gcd_divides = store_thm(
  "poly_monic_gcd_divides",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> mpgcd p q pdivides p /\ mpgcd p q pdivides q``,
  ntac 5 strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `Ring r` by rw[] >>
  Cases_on `d = |0|` >-
  metis_tac[poly_monic_gcd_eq_zero, poly_gcd_eq_zero, poly_zero_divides] >>
  (`mpgcd p q = |/ (lead d) * d` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
  `lead d <> #0` by rw[poly_lead_nonzero] >>
  `lead d IN R+ /\ |/ (lead d) IN R+` by rw[field_nonzero_eq, field_inv_nonzero] >>
  metis_tac[poly_gcd_divides, poly_field_cmult_divides, field_nonzero_eq]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ monic (pgcd p q) ==> (pgcd p q = mpgcd p q) *)
(* Proof:
   Let d = pgcd p q.
   Since monic d ==> d <> |0|          by poly_monic_nonzero
   Hence mpgcd p q = |/ (lead d) * d   by poly_monic_gcd_def
                   = |/ #1 * d         by poly_monic_lead
                   = #1 * d            by field_inv_one
                   = d                 by field_mult_lone
*)
val poly_monic_gcd_is_monic_gcd = store_thm(
  "poly_monic_gcd_is_monic_gcd",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ monic (pgcd p q) ==> (pgcd p q = mpgcd p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `d <> |0|` by rw[poly_monic_nonzero, Abbr`d`] >>
  rw_tac std_ss[poly_monic_gcd_def] >>
  rw_tac std_ss[] >>
  rw[]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. monic t /\ t ~~ pgcd p q ==> (t = mpgcd p q) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                       by poly_gcd_poly
   Since t ~~ d
     ==> ?u. upoly u /\ (t = u * d)   by poly_unit_eq_property
     ==> ?c. c IN R /\ c <> #0 /\ (u = [c])   by poly_field_unit_alt
    Thus c IN R+                      by field_nonzero_eq
     and |/ c IN R                    by field_inv_element
     and |/ ( |/ c) = c               by field_inv_inv
   Hence t = [c] * d                  by above
     <=> d = [|/ c] * t               by poly_mult_lconst_swap
           = |/ c * t                 by poly_mult_lconst
    Thus lead d = |/ c * lead t       by poly_cmult_lead
                = |/ c * #1           by poly_monic_lead
                = |/ c                by field_mult_rone
   Since |/ c <> #0                   by field_inv_nonzero, field_nonzero_eq
      so d <> |0|                     by poly_lead_zero
     Or, monic t ==> t <> |0|         by poly_monic_zero, #1 <> #0
      so d <> |0|                     by poly_mult_eq_zero
   Hence mpgcd p q
       = |/ (lead d) * d              by poly_monic_gcd_def
       = |/ ( |/ c) * d               by above
       = c * d                        by above, field_inv_inv
       = [c] * d                      by poly_mult_lconst
       = t                            by above
*)
val poly_monic_gcd_eq_monic_gcd = store_thm(
  "poly_monic_gcd_eq_monic_gcd",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. monic t /\ t ~~ pgcd p q ==> (t = mpgcd p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `?u. upoly u /\ (t = u * d)` by rw[GSYM poly_unit_eq_property] >>
  `?c. c IN R /\ c <> #0 /\ (u = [c])` by rw[GSYM poly_field_unit_alt] >>
  `c IN R+ /\ |/ c IN R` by rw[field_nonzero_eq, field_inv_element] >>
  `d = [|/ c] * t` by rw[GSYM poly_mult_lconst_swap] >>
  `_ = |/ c * t` by rw[poly_mult_lconst] >>
  `lead d = |/ c` by rw[] >>
  `d <> |0|` by metis_tac[poly_lead_zero, field_inv_nonzero, field_nonzero_eq] >>
  (`mpgcd p q = |/ (lead d) * d` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
  `_ = c * d` by rw[field_inv_inv] >>
  `_ = [c] * d` by rw[poly_mult_lconst] >>
  rw[]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
       mpgcd p q pdivides p /\ mpgcd p q pdivides q /\
       !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides mpgcd p q *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                          by poly_gcd_poly
   If d = |0|,
      Then mpgcd p q = |0|               by poly_monic_gcd_def
      also (p = |0|) /\ (q = |0|)        by poly_gcd_eq_zero
       and |0| pdivides |0|              by poly_zero_divides
   If d <> |0|,
     Then (lead d) <> #0                 by poly_lead_nonzero
      and (lead d) IN R                  by poly_lead_element
       so (lead d) IN R+                 by field_nonzero_eq
     thus |/ (lead d) IN R               by field_inv_element
      Now t pdivides d                   by poly_gcd_is_gcd
       so t pdivides ( |/ (lead d) * d)  by poly_divides_cmult
       or t pdivides mpgcd p q           by poly_monic_gcd_def, d <> |0|
*)
val poly_monic_gcd_is_gcd = store_thm(
  "poly_monic_gcd_is_gcd",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
       mpgcd p q pdivides p /\ mpgcd p q pdivides q /\
       !t. poly t /\ t pdivides p /\ t pdivides q ==> t pdivides mpgcd p q``,
  rw_tac std_ss[poly_monic_gcd_divides] >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  Cases_on `d = |0|` >| [
    `mpgcd p q = |0|` by rw[poly_monic_gcd_def] >>
    metis_tac[poly_gcd_eq_zero, poly_zero_divides],
    rw_tac std_ss[poly_monic_gcd_def] >>
    rw_tac std_ss[] >>
    `t pdivides d` by rw[poly_gcd_is_gcd, Abbr`d`] >>
    `(lead d) IN R+` by rw[field_nonzero_eq] >>
    `|/ (lead d) IN R` by rw[field_inv_element] >>
    rw[poly_divides_cmult]
  ]);

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ monic t ==>
   ((mpgcd p q = t) <=> t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)) *)
(* Proof:
   Let d = mpgcd p q
   Then poly d                by poly_monic_gcd_poly
   If part: d = t ==> t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
      (1) d pdivides p        by poly_monic_gcd_divides
      (2) d pdivides q        by poly_monic_gcd_divides
      (3) !s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides d   by poly_monic_gcd_is_gcd
   Only-if part: t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t) ==> d = t
      Since monic t ==> poly t                   by poly_monic_poly
      The conditions give: pgcd p q ~~ t         by poly_gcd_unit_eq
                        or t ~~ pgcd p q         by poly_unit_eq_sym
      With monic t /\ t ~~ pgcd p q ==> (t = d)  by poly_monic_gcd_eq_monic_gcd
*)
val poly_monic_gcd_eq = store_thm(
  "poly_monic_gcd_eq",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ monic t ==>
   ((mpgcd p q = t) <=>
    t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = mpgcd p q` >>
  `poly d` by rw[poly_monic_gcd_poly, Abbr`d`] >>
  rw[EQ_IMP_THM] >-
  rw[poly_monic_gcd_divides, Abbr`d`] >-
  rw[poly_monic_gcd_divides, Abbr`d`] >-
  rw[poly_monic_gcd_is_gcd, Abbr`d`] >>
  `pgcd p q ~~ t` by rw[poly_gcd_unit_eq] >>
  `t ~~ pgcd p q` by rw[poly_unit_eq_sym] >>
  rw[poly_monic_gcd_eq_monic_gcd, poly_gcd_poly, Abbr`d`]);

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ monic t /\ p <> |0| ==>
            ((mpgcd p q = t) <=> t pdivides p /\ t pdivides q /\
                                (!s. monic s /\ s pdivides p /\ s pdivides q ==> s pdivides t)) *)
(* Proof:
   Let d = mpgcd p q
   Then poly d                by poly_monic_gcd_poly
   If part: d = t ==> t pdivides p /\ t pdivides q /\ (!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t)
      (1) d pdivides p        by poly_monic_gcd_divides
      (2) d pdivides q        by poly_monic_gcd_divides
      (3) !s. monic s /\ s pdivides p /\ s pdivides q ==> s pdivides d   by poly_monic_gcd_is_gcd, poly_monic_poly
   Only-if part: t pdivides p /\ t pdivides q /\ (!s. monic s /\ s pdivides p /\ s pdivides q ==> s pdivides t) ==> d = t
      Claim: !s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t
      Proof: Note s <> |0|    by poly_zero_divides, p <> |0|
              Let c = |/ (lead s), ss = c * s
             Then monic ss      by poly_monic_by_cmult
             Also lead s IN R /\ lead s <> #0    by poly_lead_element, poly_lead_nonzero
               or lead s IN R+                   by field_nonzero_eq
              ==> s = (lead s) * ss              by poly_cmult_inv_eq, poly_monic_poly
             Note c IN R+                        by field_nonzero_eq
               or c IN R /\ c <> #0              by field_inv_nonzero
              ==> ss pdivides p /\ ss pdivides q by rw[poly_field_cmult_divides, c IN R /\ c <> #0
               so ss pdivides t                  by implication
              ==>  s pdivides t                  by poly_field_cmult_divides, lead s IN R /\ lead s <> #0

      Thus d = t                                 by poly_monic_gcd_eq
*)
val poly_monic_gcd_condition = store_thm(
  "poly_monic_gcd_condition",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ monic t /\ p <> |0| ==>
   ((mpgcd p q = t) <=> t pdivides p /\ t pdivides q /\
       (!s. monic s /\ s pdivides p /\ s pdivides q ==> s pdivides t))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = mpgcd p q` >>
  `poly d` by rw[poly_monic_gcd_poly, Abbr`d`] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_monic_gcd_divides, Abbr`d`] >-
  rw[poly_monic_gcd_divides, Abbr`d`] >-
  rw[poly_monic_gcd_is_gcd, Abbr`d`] >>
  `!s. poly s /\ s pdivides p /\ s pdivides q ==> s pdivides t` by
  (rpt strip_tac >>
  `s <> |0|` by metis_tac[poly_zero_divides] >>
  qabbrev_tac `c = |/ (lead s)` >>
  qabbrev_tac `ss = c * s` >>
  `monic ss` by rw[poly_monic_by_cmult, Abbr`c`, Abbr`ss`] >>
  `lead s IN R /\ lead s <> #0` by rw[poly_lead_nonzero] >>
  `s = (lead s) * ss` by metis_tac[poly_cmult_inv_eq, poly_monic_poly, field_nonzero_eq] >>
  `c IN R /\ c <> #0` by metis_tac[field_nonzero_eq, field_inv_nonzero] >>
  metis_tac[poly_field_cmult_divides, poly_monic_poly]) >>
  metis_tac[poly_monic_gcd_eq]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> ?s t. poly s /\ poly t /\
            (p = s * (mpgcd p q)) /\ (q = t * (mpgcd p q)) /\ (mpgcd s t = |1|) *)
(* Proof:
   If (p = |0|) /\ (q = |0|),
      Then pgcd |0| |0| = |0|           by poly_gcd_zero
       and mpgcd |0| |0| = |0|          by poly_monic_gcd_def
      Let s = |1|, t = |1|.
      Then |0| = |1| * |0|              by poly_mult_rzero
       and mpgcd |1| |1| = |1|          by poly_monic_gcd_one
   If ~(p = |0| /\ q = |0|),
      Let d = mpgcd p q.
       Then poly d                      by poly_monic_gcd_poly
        and d pdivides p                by poly_monic_gcd_divides
            d pdivides q                by poly_monic_gcd_divides
       thus ?s. poly s /\ (p = s * d)   by poly_divides_def
            ?t. poly t /\ (q = t * d)   by poly_divides_def
       Take these s and t, need to show: mpgcd s t = |1|
      Let e = mpgcd s t.
       Then poly e                      by poly_monic_gcd_poly
        and e pdivides s                by poly_monic_gcd_divides
            e pdivides t                by poly_monic_gcd_divides
       thus ?u. poly u /\ (s = u * e)   by poly_divides_def
            ?v. poly v /\ (t = v * e)   by poly_divides_def
      Hence p = (u * e) * d             by above
              = u * (e * d)             by poly_mult_assoc
         so e * d pdivides p            by poly_divides_def
       Also q = (v * e) * d             by above
              = v * (e * d)             by poly_mult_assoc
         so e * d pdivides q            by poly_divides_def
       Thus e * d pdivides d            by poly_monic_gcd_is_gcd
      Since ~(p = |0| /\ q = |0|),
       thus ~((s = |0|) /\ (t = |0|))   by poly_mult_lzero
        and d <> |0|                    by poly_zero_divides, ~(p = |0| /\ q = |0|)
       With e * d pdivides d
        ==> upoly e                     by poly_mult_divides_factor, d <> |0|
       Also monic e                     by poly_monic_gcd_monic, ~((s = |0|) /\ (t = |0|))
      Hence e = |1|                     by poly_unit_monic
*)
val poly_monic_gcd_factor_out = store_thm(
  "poly_monic_gcd_factor_out",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> ?s t. poly s /\ poly t /\
    (p = s * (mpgcd p q)) /\ (q = t * (mpgcd p q)) /\ (mpgcd s t = |1|)``,
  rpt strip_tac >>
  Cases_on `(p = |0|) /\ (q = |0|)` >| [
    MAP_EVERY qexists_tac [`|1|`, `|1|`] >>
    `poly |1| /\ ( |0| = |1| * |0|)` by rw[] >>
    `pgcd |0| |0| = |0|` by rw[poly_gcd_zero] >>
    `mpgcd |0| |0| = |0|` by rw[poly_monic_gcd_eq_zero] >>
    `mpgcd |1| |1| = |1|` by rw[poly_monic_gcd_one] >>
    metis_tac[],
    qabbrev_tac `d = mpgcd p q` >>
    `poly d` by rw[Abbr`d`] >>
    `d pdivides p` by rw[poly_monic_gcd_divides, Abbr`d`] >>
    `d pdivides q` by rw[poly_monic_gcd_divides, Abbr`d`] >>
    `?s. poly s /\ (p = s * d)` by rw[GSYM poly_divides_def] >>
    `?t. poly t /\ (q = t * d)` by rw[GSYM poly_divides_def] >>
    MAP_EVERY qexists_tac [`s`, `t`] >>
    `mpgcd s t = |1|` suffices_by rw[] >>
    qabbrev_tac `e = mpgcd s t` >>
    `poly e` by rw[Abbr`e`] >>
    `e pdivides s` by rw[poly_monic_gcd_divides, Abbr`e`] >>
    `e pdivides t` by rw[poly_monic_gcd_divides, Abbr`e`] >>
    `?u. poly u /\ (s = u * e)` by rw[GSYM poly_divides_def] >>
    `?v. poly v /\ (t = v * e)` by rw[GSYM poly_divides_def] >>
    `p = u * (e * d)` by rw[poly_mult_assoc] >>
    `e * d pdivides p` by metis_tac[poly_divides_def] >>
    `q = v * (e * d)` by rw[poly_mult_assoc] >>
    `e * d pdivides q` by metis_tac[poly_divides_def] >>
    `poly (e * d)` by rw[] >>
    `e * d pdivides d` by metis_tac[poly_monic_gcd_is_gcd] >>
    `monic e` by metis_tac[poly_monic_gcd_monic, poly_mult_lzero] >>
    metis_tac[poly_zero_divides, poly_mult_divides_factor, poly_unit_monic, field_is_ring]
  ]);

(* This is Bézout's identity for monic polynomial GCD. *)

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            ?s t. poly s /\ poly t /\ (mpgcd p q = s * p + t * q) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                          by poly_gcd_poly
   If d = |0|,
      Then (p = |0|) /\ (q = |0|)        by poly_gcd_eq_zero
       and mpgcd |0| |0| = |0|           by poly_monic_gcd_def
      Take s = |1|, t = |1|,
      Then |0| = |1| * |0| + |1| * |0|   by poly_mult_lone, poly_add_zero_zero
   If d <> |0|,
     Then (lead d) IN R                  by poly_lead_element
      and (lead d) <> #0                 by poly_lead_nonzero, d <> |0|
      ==> (lead d) IN R+                 by field_nonzero_eq
     Thus |/ (lead d) IN R               by field_inv_element
      Let c = |/ (lead d).
      Now ?s t. poly s /\ poly t /\
          (d = s * p + t * q)            by poly_gcd_linear
          mpgcd p q
        = c * d                          by poly_monic_gcd_def
        = c * (s * p + t * q)            by above
        = c * (s * p) + c * (t * q)      by poly_cmult_add
        = (c * s) * p + (c * t) * q      by poly_cmult_mult
    Since poly (c * s) /\ poly (c * t)   by poly_cmult_poly
     Take s = c * s, t = c * t, and we are done.
*)
val poly_monic_gcd_linear = store_thm(
  "poly_monic_gcd_linear",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
       ?s t. poly s /\ poly t /\ (mpgcd p q = s * p + t * q)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  Cases_on `d = |0|` >| [
    `(p = |0|) /\ (q = |0|)` by metis_tac[poly_gcd_eq_zero] >>
    MAP_EVERY qexists_tac [`|1|`, `|1|`] >>
    rw[poly_monic_gcd_def],
    `(lead d) IN R+` by rw[field_nonzero_eq] >>
    `|/ (lead d) IN R` by rw[field_inv_element] >>
    `?s t. poly s /\ poly t /\ (d = s * p + t * q)` by rw[poly_gcd_linear, Abbr`d`] >>
    qabbrev_tac `c = |/ (lead d)` >>
    (`mpgcd p q = c * d` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
    `_ = c * (s * p) + c * (t * q)` by rw_tac std_ss[poly_cmult_add, poly_mult_poly] >>
    `_ = (c * s) * p + (c * t) * q` by rw_tac std_ss[poly_cmult_mult] >>
    `poly (c * s) /\ poly (c * t)` by rw[] >>
    metis_tac[]
  ]);

(* This is Auxillary Lemma for Euclid's Lemma. *)

(* Theorem: Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
            s pdivides (t * p) /\ s pdivides (t * q) ==> s pdivides (t * mpgcd p q) *)
(* Proof:
   Let d = pgcd p q.
    Then poly d                         by poly_gcd_poly
   If (p = |0|) /\ (q = |0|),
      Then d = |0|                      by poly_gcd_eq_zero
       and mpgcd p q = |0|              by poly_monic_gcd_eq_zero
      thus t * mpgcd p q = |0|          by poly_mult_rzero
     Hence s pdivides |0|               by poly_divides_zero
   If ~((p = |0|) /\ (q = |0|)),
      Then d <> |0|                     by poly_gcd_eq_zero
       and mpgcd p q = |/ (lead d) * d  by poly_monic_gcd_def
       Now (lead d) IN R                by poly_lead_element
       and (lead d) <> #0               by poly_lead_nonzero, d <> |0|
        so (lead d) IN R+               by field_nonzero_eq
      thus |/ (lead d) IN R             by field_inv_element
       Let c = |/ (lead d).
      Then t * mpgcd p q
         = t * (c * d)                  by above
         = c * (t * d)                  by poly_mult_cmult
     Since s pdivides t * d             by poly_divides_gcd_multiple
     Hence s pdivides (t * mpgcd p q)   by poly_divides_cmult
*)
val poly_divides_monic_gcd_multiple = store_thm(
  "poly_divides_monic_gcd_multiple",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
    s pdivides (t * p) /\ s pdivides (t * q) ==> s pdivides (t * mpgcd p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = pgcd p q` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  Cases_on `(p = |0|) /\ (q = |0|)` >| [
    `d = |0|` by metis_tac[poly_gcd_eq_zero] >>
    `mpgcd p q = |0|` by rw[poly_monic_gcd_eq_zero] >>
    metis_tac[poly_divides_zero, poly_mult_rzero, field_is_ring],
    `d <> |0|` by metis_tac[poly_gcd_eq_zero] >>
    (`mpgcd p q = |/ (lead d) * d` by (rw_tac std_ss[poly_monic_gcd_def] >> rw_tac std_ss[])) >>
    `(lead d) IN R+` by rw[field_nonzero_eq] >>
    `|/ (lead d) IN R` by rw[field_inv_element] >>
    qabbrev_tac `c = |/ (lead d)` >>
    `s pdivides t * d` by rw[poly_divides_gcd_multiple, Abbr`d`] >>
    rw[poly_divides_cmult, poly_mult_cmult]
  ]);

(* This is Euclid's Lemma for polynomial factors. *)

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ (mpgcd p q = |1|) ==>
            !t. poly t /\ p pdivides (q * t) ==> p pdivides t *)
(* Proof:
   Put s = p in poly_divides_monic_gcd_multiple,
    Then p pdivides (t * p) /\ p pdivides (t * q) ==> p pdivides (t * mpgcd p q)
   Since p pdivides (t * p)              by poly_divides_multiple, poly_divides_reflexive
     and p pdivides (t * q)              by poly_mult_comm, p pdivides (q * t)
   Hence p pdivides (t * mpgcd p q)      by poly_divides_monic_gcd_multiple
   Since mpgcd p q = |1|, t * |1| = t    by poly_mult_rone
   Hence p pdivides t                    by above
*)
val poly_monic_gcd_one_factor = store_thm(
  "poly_monic_gcd_one_factor",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ (mpgcd p q = |1|) ==>
   !t. poly t /\ p pdivides (q * t) ==> p pdivides t``,
  rpt strip_tac >>
  `p pdivides p` by rw[poly_divides_reflexive] >>
  `p pdivides (t * p)` by rw[poly_divides_multiple] >>
  `p pdivides (t * q)` by rw[poly_mult_comm] >>
  `t * |1| = t` by rw[] >>
  metis_tac[poly_divides_monic_gcd_multiple]);


(* Theorem: Field r ==> !p q. poly p /\ poly q /\ (pcoprime p q) ==>
            !t. poly t /\ p pdivides (q * t) ==> p pdivides t *)
(* Proof:
   Since pcoprime p q <=> mpgcd p q = |1|    by poly_monic_gcd_one_coprime
   Hence result follows                      by poly_monic_gcd_one_factor
*)
val poly_coprime_divides_product = store_thm(
  "poly_coprime_divides_product",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ (pcoprime p q) ==>
   !t. poly t /\ p pdivides (q * t) ==> p pdivides t``,
  metis_tac[poly_monic_gcd_one_coprime, poly_monic_gcd_one_factor]);

(* This is GCD_CANCEL_MULT for polynomial GCD *)

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. ipoly t /\ t pdivides (p * q) ==> (t pdivides p) \/ (t pdivides q) *)
(* Proof:
   If t pdivides p, then true trivially.
   If ~(t pdivides p),
      Then pcoprime t p         by poly_irreducible_gcd
      Note poly t               by poly_irreducible_poly
       ==> t pdivides q         by poly_coprime_divides_product
*)
val poly_irreducible_divides_product = store_thm(
  "poly_irreducible_divides_product",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. ipoly t /\ t pdivides (p * q) ==> (t pdivides p) \/ (t pdivides q)``,
  metis_tac[poly_irreducible_gcd, poly_irreducible_poly, poly_coprime_divides_product]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
            !t. poly t ==> (pgcd p (q * t) ~~ pgcd p t) *)
(* Proof:
   Let d = pgcd p t,
    Then poly d               by poly_gcd_poly
    with d pdivides p         by poly_gcd_divides      [1]
     and d pdivides t         by poly_gcd_divides
      so d pdivides (q * t)   by poly_divides_multiple [2]
   Claim: !s. poly s /\ s pdivides p /\ s pdivides (q * t) ==> s pdivides d  [3]
   Proof: Claim: mpgcd s q = |1|
          Proof: by poly_monic_gcd_eq, this is to show:
          (1) |1| pdivides s, true   by poly_one_divides_all
          (2) |1| pdivides q, true   by poly_one_divides_all
          (3) poly s' /\ s' pdivides s /\ s' pdivides q ==> s' pdivides |1|
              Since s' pdivides s              by given
                and s pdivides p               by given
                ==> s' pdivides p              by poly_divides_transitive
               With s' pdivides q              by given
                ==> s' pdivides (mpgcd p q)    by poly_monic_gcd_is_gcd
                 or s' pdivides |1|            by poly_monic_gcd_one_coprime, pcoprime p q
         Thus mpgcd s q = |1|      by (1),(2),(3)
         From mpgcd s q = |1|
          ==> pcoprime s q         by poly_monic_gcd_one_coprime
        Hence s pdivides t         by poly_coprime_divides_product
        Given s pdivides p
          ==> s pdivides d         by poly_gcd_is_gcd
   From the claim, d ~~ t          by poly_gcd_condition, [1], [2], [3]
*)
val poly_gcd_multiple_reduction = store_thm(
  "poly_gcd_multiple_reduction",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
   !t. poly t ==> (pgcd p (q * t) ~~ pgcd p t)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = pgcd p t` >>
  `poly d` by rw[poly_gcd_poly, Abbr`d`] >>
  `d pdivides p /\ d pdivides t` by rw[poly_gcd_divides, Abbr`d`] >>
  `d pdivides (q * t)` by rw[poly_divides_multiple] >>
  `!s. poly s /\ s pdivides p /\ s pdivides (q * t) ==> s pdivides d` by
  (rpt strip_tac >>
  `mpgcd s q = |1|` by
    (rw[poly_monic_gcd_eq, poly_one_divides_all] >>
  `s' pdivides p` by metis_tac[poly_divides_transitive] >>
  `s' pdivides (mpgcd p q)` by rw[poly_monic_gcd_is_gcd] >>
  metis_tac[poly_monic_gcd_one_coprime]) >>
  `pcoprime s q` by rw_tac std_ss[poly_monic_gcd_one_coprime] >>
  `s pdivides t` by metis_tac[poly_coprime_divides_product] >>
  rw[poly_gcd_is_gcd, Abbr`d`]) >>
  rw[poly_gcd_condition]);

(* This is GCD_CANCEL_MULT for monic polynomial GCD *)

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
            !t. poly t ==> (mpgcd p (q * t) = mpgcd p t) *)
(* Proof:
   Since the conditions give:
         pgcd p (q * t) ~~ pgcd p t     by poly_gcd_multiple_reduction
   Hence mpgcd p (q * t) = mpgcd p t    by poly_gcd_unit_eq_monic_gcd_eq
*)
val poly_monic_gcd_multiple_reduction = store_thm(
  "poly_monic_gcd_multiple_reduction",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
   !t. poly t ==> (mpgcd p (q * t) = mpgcd p t)``,
  rw[poly_gcd_multiple_reduction, GSYM poly_gcd_unit_eq_monic_gcd_eq]);

(* This is coprime_product_coprime_sym for polynomials. *)

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. poly t /\ pcoprime t p /\ pcoprime t q ==> pcoprime t (p * q) *)
(* Proof:
   Since pcoprime t p ==> mpgcd t (p * q) = mpgcd t q    by poly_monic_gcd_multiple_reduction
    With pcoprime t q <=> mpgcd t q = |1|                by poly_monic_gcd_one_coprime
      so mpgcd t (p * q) = |1| <=> coprime t (p * q)     by poly_monic_gcd_one_coprime
*)
val poly_coprime_product_by_coprimes = store_thm(
  "poly_coprime_product_by_coprimes",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ pcoprime t p /\ pcoprime t q ==> pcoprime t (p * q)``,
  metis_tac[poly_monic_gcd_multiple_reduction, poly_monic_gcd_one_coprime, poly_mult_poly, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Polynomiald LCM                                                           *)
(* ------------------------------------------------------------------------- *)

(* Need to define polynomial lcm. Note: division by zero or a unit is not defined. *)
val poly_lcm_def = Define`
    poly_lcm (r:'a ring) p q = if (deg (mpgcd p q) = 0) then (p * q) else (p * q) / (mpgcd p q)
`;
(* Overload poly_lcm similar to poly_gcd *)
val _ = overload_on("plcm", ``poly_lcm r``);
(*
> poly_lcm_def;
val it = |- !r p q. plcm p q = if deg (mpgcd p q) = 0 then p * q else p * q / mpgcd p q: thm
*)

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> poly (plcm p q) *)
(* Proof:
   Let d = mpgcd p q.
    Then poly d                      by poly_monic_gcd_poly
    If deg d = 0,
       Then plcm p q = p * q         by poly_lcm_def
         so poly (plcm p q)          by poly_mult_poly
    If deg d <> 0,
       Then plcm p q = (p * q) / d   by poly_lcm_def
       Since poly (p * q)            by poly_mult_poly
          so poly (plcm p q)         by poly_field_div_poly, d <> 0
*)
val poly_lcm_poly = store_thm(
  "poly_lcm_poly",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> poly (plcm p q)``,
  rpt strip_tac >>
  qabbrev_tac `d = mpgcd p q` >>
  `poly d` by rw[Abbr`d`] >>
  Cases_on `deg d = 0` >| [
    rw_tac std_ss[poly_lcm_def] >>
    rw[],
    rw_tac std_ss[poly_lcm_def] >>
    `0 < deg d` by decide_tac >>
    rw[poly_field_div_poly]
  ]);

(* export simple result *)
val _ = export_rewrites["poly_lcm_poly"];

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q * plcm p q = p * q) *)
(* Proof:
   Let d = mpgcd p q.
   If (p = |0|) /\ (q = |0|),
      Then pgcd |0| |0| = |0|          by poly_gcd_eq_zero
       and d = |0|                     by poly_monic_gcd_eq_zero
      Thus |0| * plcm p q = |0| * |0|  by poly_mult_lzero
   If ~((p = |0|) /\ (q = |0|)),
      Then monic d                     by poly_monic_gcd_monic
      If deg d = 0,
         Then d = |1|                  by poly_monic_deg_0

          d * plcm p q
        = d * (p * q)                  by poly_lcm_def
        = |1| * (p * q)                by above
        = p * q                        by poly_mult_lone
      If deg d <> 0,
          Then 0 < deg d               by NOT_ZERO
          thus pmonic d                by poly_monic_pmonic
         Since d pdivides q            by poly_monic_gcd_divides
            so d pdivides (p * q)      by poly_divides_multiple
            or (p * q) % d = |0|       by poly_divides_alt

          d * plcm p q
        = d * (p * q / d)              by poly_lcm_def
        = p * q                        by poly_div_multiple_alt, (p * q) % d = |0|
*)
val poly_lcm_eqn = store_thm(
  "poly_lcm_eqn",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (mpgcd p q * plcm p q = p * q)``,
  rpt strip_tac >>
  qabbrev_tac `d = mpgcd p q` >>
  Cases_on `(p = |0|) /\ (q = |0|)` >| [
    `pgcd |0| |0| = |0|` by rw[poly_gcd_eq_zero] >>
    `d = |0|` by rw_tac std_ss[poly_monic_gcd_eq_zero, Abbr`d`] >>
    rw_tac std_ss[poly_mult_lzero],
    `monic d` by metis_tac[poly_monic_gcd_monic] >>
    Cases_on `deg d = 0` >| [
      rw_tac std_ss[poly_lcm_def] >>
      `d = |1|` by rw[GSYM poly_monic_deg_0] >>
      rw[],
      rw_tac std_ss[poly_lcm_def] >>
      `0 < deg d` by decide_tac >>
      `pmonic d` by rw[poly_monic_pmonic] >>
      `d pdivides q` by rw[poly_monic_gcd_divides, Abbr`d`] >>
      `d pdivides (p * q)` by rw[poly_divides_multiple] >>
      `(p * q) % d = |0|` by rw[GSYM poly_divides_alt] >>
      rw[poly_div_multiple_alt]
    ]
  ]);

(* Theorem: Field r ==> !p. poly p ==> (plcm p |0| = |0|) /\ (plcm |0| p = |0|) *)
(* Proof:
   Let d = mpgcd p |0|,
     Then d = mpgcd |0| p                  by poly_monic_gcd_sym
   If deg d = 0,
      Then plcm p |0| = p * |0|            by poly_lcm_def
                      = |0|                by poly_mult_rzero
       and plcm |0| p = |0| * p            by poly_lcm_def
                      = |0|                by poly_mult_lzero
      Hence plcm p |0| = plcm |0| p
   If deg d <> 0,
      Then 0 < deg d                       by NOT_ZERO
      Then plcm p |0| = p * |0| / d        by poly_lcm_def
                      = |0| / d            by poly_mult_rzero
       and plcm |0| p = |0| * p / d        by poly_lcm_def
                      = |0| / d            by poly_mult_lzero
       Now p <> |0|, because
           If p = |0|,
           Then d = pgcd |0| |0|           by poly_monic_gcd_eq_zero
                  = |0|                    by poly_gcd_eq_zero
           which contradicts deg d <> |0|  by poly_deg_zero
      Thus monic d                         by poly_monic_gcd_monic, p <> |0|
       ==> ulead d                         by poly_monic_ulead
      Also |0| / d = |0|                   by poly_zero_div, ulead d
     Hence plcm p |0| = plcm |0| p
*)
val poly_lcm_zero = store_thm(
  "poly_lcm_zero",
  ``!r:'a field. Field r ==> !p. poly p ==> (plcm p |0| = |0|) /\ (plcm |0| p = |0|)``,
  ntac 4 strip_tac >>
  qabbrev_tac `d = mpgcd p |0|` >>
  `d = mpgcd |0| p` by rw[poly_monic_gcd_sym] >>
  Cases_on `deg d = 0` >| [
    `plcm p |0| = p * |0|` by rw_tac std_ss[poly_lcm_def] >>
    `plcm |0| p = |0| * p` by rw_tac std_ss[poly_lcm_def] >>
    rw[],
    `plcm p |0| = p * |0| / d` by rw_tac std_ss[poly_lcm_def] >>
    `plcm |0| p = |0| * p / d` by rw_tac std_ss[poly_lcm_def] >>
    `p <> |0|` by metis_tac[poly_monic_gcd_eq_zero, poly_gcd_eq_zero, poly_deg_zero] >>
    `monic d` by rw[poly_monic_gcd_monic, Abbr`d`] >>
    `ulead d` by rw[] >>
    `|0| / d = |0|` by rw[poly_zero_div] >>
    rw_tac std_ss[poly_mult_zero]
  ]);

(* Theorem: Field r ==> !p. poly p ==> (plcm p |1| = p) /\ (plcm |1| p = p) *)
(* Proof:
   Let d = mpgcd p |1|.
   Then d = mpgcd |1| p         by poly_monic_gcd_sym
    Now d = |1|                 by poly_monic_gcd_one
   thus deg d = 0               by poly_deg_one
   Hence plcm p |1| = p * |1|   by poly_lcm_def
                    = p         by poly_mult_rone
     and plcm |1| p = |1| * p   by poly_lcm_def
                    = p         by poly_mult_lone
*)
val poly_lcm_one = store_thm(
  "poly_lcm_one",
  ``!r:'a field. Field r ==> !p. poly p ==> (plcm p |1| = p) /\ (plcm |1| p = p)``,
  ntac 4 strip_tac >>
  qabbrev_tac `d = mpgcd p |1|` >>
  `d = mpgcd |1| p` by rw[poly_monic_gcd_sym] >>
  `d = |1|` by rw[poly_monic_gcd_one] >>
  `deg d = 0` by rw[] >>
  metis_tac[poly_lcm_def, poly_mult_one, field_is_ring]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==> (plcm p q = p * q) *)
(* Proof:
   Let d = mpgcd p q.
   Since pcoprime p q ==> d = |1|     by poly_monic_gcd_one_coprime
     and deg d = deg |1| = 0          by poly_deg_one
   Hence plcm p q = p * q             by poly_lcm_def
*)
val poly_coprime_lcm = store_thm(
  "poly_coprime_lcm",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==> (plcm p q = p * q)``,
  rpt strip_tac >>
  `mpgcd p q = |1|` by rw[GSYM poly_monic_gcd_one_coprime] >>
  rw[poly_lcm_def]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> p pdivides (plcm p q) /\ q pdivides (plcm p q) *)
(* Proof:
   Let d = mpgcd p q.
    Then poly d                      by poly_monic_gcd_poly
   If deg d = 0,
      Then plcm p q = p * q          by poly_lcm_def
        so p divides (q * p)         by poly_divides_def
        or p divides (p * q)         by poly_mult_comm
       and q divides (p * q)         by poly_divides_def
   If deg d <> 0,
      Then ~((p = |0|) /\ (q = |0|)) by poly_monic_gcd_eq_zero, poly_gcd_eq_zero, poly_deg_zero
      thus monic d                   by poly_monic_gcd_monic, ~((p = |0|) /\ (q = |0|))
      Then ulead d                   by poly_monic_ulead
       and plcm p q = p * q / d      by poly_lcm_def
     Since d pdivides q              by poly_monic_gcd_divides
        so q % d = |0|               by poly_divides_alt
      thus p * q / d = q * p / d     by poly_mult_comm
                     = (q / d) * p   by poly_mult_div_alt
     Hence p pdivdes plcm p q        by poly_divides_def, poly_div_poly
     Since d pdivides p              by poly_monic_gcd_divides
        so p % d = |0|               by poly_divides_alt
      thus p * q / d = (p / d) * q   by poly_mult_div_alt
     Hence q pdivdes plcm p q        by poly_divides_def, poly_div_poly
*)
val poly_lcm_divisors = store_thm(
  "poly_lcm_divisors",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> p pdivides (plcm p q) /\ q pdivides (plcm p q)``,
  ntac 5 strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = mpgcd p q` >>
  `poly d` by rw[Abbr`d`] >>
  Cases_on `deg d = 0` >| [
    rw_tac std_ss[poly_lcm_def] >-
    metis_tac[poly_divides_def, poly_mult_comm] >>
    metis_tac[poly_divides_def],
    `~((p = |0|) /\ (q = |0|))` by metis_tac[poly_monic_gcd_eq_zero, poly_gcd_eq_zero, poly_deg_zero] >>
    `monic d` by metis_tac[poly_monic_gcd_monic] >>
    `ulead d` by rw[] >>
    rw_tac std_ss[poly_lcm_def] >| [
      `d pdivides q` by rw[poly_monic_gcd_divides, Abbr`d`] >>
      `q % d = |0|` by rw[GSYM poly_divides_alt] >>
      `p * q / d = (q / d) * p` by metis_tac[poly_mult_div_alt, poly_mult_comm] >>
      metis_tac[poly_divides_def, poly_div_poly],
      `d pdivides p` by rw[poly_monic_gcd_divides, Abbr`d`] >>
      metis_tac[poly_divides_alt, poly_mult_div_alt, poly_divides_def, poly_div_poly]
    ]
  ]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !t. poly t /\ p pdivides t /\ q pdivides t ==> (plcm p q) pdivides t *)
(* Proof:
   Let d = mpgcd p q, e = plcm p q.
     Then poly d            by poly_monic_gcd_poly
      and poly e            by poly_lcm_poly

   If d = |0|,
      Then pgcd p q = |0|             by poly_monic_gcd_eq_zero
       ==> (p = |0|) /\ (q = |0|)     by poly_gcd_eq_zero
      Thus t = |0|                    by poly_zero_divides
      In fact, e = plcm |0| |0| = |0| by poly_lcm_zero
      But any e pdivides |0|          by poly_divides_zero
   If d <> |0|,
      Then pgcd p q <> |0|            by poly_monic_gcd_eq_zero
       ==> ~((p = |0|) /\ (q = |0|))  by poly_gcd_eq_zero
     Hence monic d                    by poly_monic_gcd_monic

   Step 1: get a coprime pair
     Note ?x y. poly x /\ poly y /\
                (p = x * d) /\
                (q = y * d) /\
                (mpgcd x y = |1|)      by poly_monic_gcd_factor_out

   Step 2: equate two expressions for multiple t
     Since p pdivides t
       ==> ?u. poly u /\ (t = u * p)   by poly_divides_def
        or t = u * (x * d)             by above
             = (u * x) * d             by poly_mult_assoc
      Also q pdivides t
       ==> ?v. poly v /\ (t = v * q)   by poly_divides_def
        or t = v * (y * d)             by above
             = (v * y) * d             by poly_mult_assoc
     Equating t,
         (u * x) * d = (v * y) * d
           or  u * x = v * y           by poly_mult_rcancel, d <> |0|
           or  x * u = v * y           by poly_mult_comm

   Step 3: squeeze out a factor (x * y * d) from t
      This shows y pdivides (x * u)     by poly_divides_def
     Since mpgcd y x = mpgcd x y = |1|  by poly_monic_gcd_sym
      Thus y pdivides u                 by poly_monic_gcd_one_factor
       ==> ?s. poly s /\ (u = s * y)    by poly_divides_def
      Thus t = u * (x * d)              by above
             = (s * y) * (x * d)        by substituting u
             = s * (y * x * d)          by poly_mult_assoc
             = s * (x * y * d)          by poly_mult_comm
   Step 4: show that e = x * y * d
    Now d * e = p * q               by poly_lcm_eqn
     so d * e = (x * d) * (y * d)   by above
              = (d * x) * (y * d)   by poly_mult_comm
              = d * (x * y * d)     by poly_mult_assoc
    Thus    e = x * y * d           by poly_mult_lcancel, d <> |0|
   Step 5: conclude
    Hence p = t * e                 by step 3 and step 4
       or e pdivides p              by pdivides_def
*)
val poly_lcm_is_lcm = store_thm(
  "poly_lcm_is_lcm",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ p pdivides t /\ q pdivides t ==> (plcm p q) pdivides t``,
  rpt strip_tac >>
  qabbrev_tac `d = mpgcd p q` >>
  qabbrev_tac `e = plcm p q` >>
  `poly d` by rw[Abbr`d`] >>
  `poly e` by rw[Abbr`e`] >>
  Cases_on `d = |0|` >| [
    `(p = |0|) /\ (q = |0|)` by metis_tac[poly_monic_gcd_eq_zero, poly_gcd_eq_zero] >>
    `t = |0|` by rw[GSYM poly_zero_divides] >>
    rw[poly_divides_zero],
    `~((p = |0|) /\ (q = |0|))` by metis_tac[poly_monic_gcd_eq_zero, poly_gcd_eq_zero] >>
    `monic d` by metis_tac[poly_monic_gcd_monic] >>
    `?x y. poly x /\ poly y /\ (p = x * d) /\ (q = y * d) /\ (mpgcd x y = |1|)` by rw[poly_monic_gcd_factor_out, Abbr`d`] >>
    `?u. poly u /\ (t = u * p)` by rw[GSYM poly_divides_def] >>
    `_ = (u * x) * d` by rw[poly_mult_assoc] >>
    `?v. poly v /\ (t = v * q)` by rw[GSYM poly_divides_def] >>
    `_ = (v * y) * d` by rw[poly_mult_assoc] >>
    `poly (x * u) /\ poly (u * x) /\ poly (v * y)` by rw[] >>
    `v * y = u * x` by metis_tac[poly_mult_rcancel] >>
    `_ = x * u` by rw[poly_mult_comm] >>
    `y pdivides (x * u)` by metis_tac[poly_divides_def] >>
    `y pdivides u` by metis_tac[poly_monic_gcd_one_factor, poly_monic_gcd_sym] >>
    `?s. poly s /\ (u = s * y)` by rw[GSYM poly_divides_def] >>
    `Ring r /\ poly (s * y) /\ poly (x * d) /\ poly (x * y * d)` by rw[] >>
    `t = (s * y) * x * d` by rw[] >>
    `_ = (s * y) * (x * d)` by prove_tac[poly_mult_assoc] >>
    `_ = s * (y * x * d)` by prove_tac[poly_mult_assoc] >>
    `_ = s * (x * y * d)` by metis_tac[poly_mult_comm] >>
    `(x * y * d) pdivides t` by metis_tac[poly_divides_def] >>
    `d * e = p * q` by rw[poly_lcm_eqn, Abbr`d`, Abbr`e`] >>
    `_ = (x * d) * (y * d)` by rw[] >>
    `_ = (d * x) * (y * d)` by rw[poly_mult_comm] >>
    `_ = d * (x * y * d)` by rw[poly_mult_assoc] >>
    metis_tac[poly_mult_lcancel]
  ]);

(* This is a milestone theorem. *)

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
            !t. poly t /\ p pdivides t /\ q pdivides t ==> (p * q) pdivides t *)
(* Proof:
   Since pcoprime p q
     ==> mpgcd p q = |1|     by poly_monic_gcd_one_coprime
     ==> plcm p q = p * q    by poly_coprime_lcm
   Hence (p * q) pdivides t  by poly_lcm_is_lcm
*)
val poly_coprime_product_divides = store_thm(
  "poly_coprime_product_divides",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ pcoprime p q ==>
   !t. poly t /\ p pdivides t /\ q pdivides t ==> (p * q) pdivides t``,
  metis_tac[poly_monic_gcd_one_coprime, poly_coprime_lcm, poly_lcm_is_lcm]);

(* ------------------------------------------------------------------------- *)
(* Coprime Polynomial Sets                                               *)
(* ------------------------------------------------------------------------- *)

(* Define a set of coprime polynomials *)
val poly_coprime_set_def = Define`
    poly_coprime_set (r:'a ring) s <=>
       (!p. p IN s ==> poly p) /\
       (!p q. p IN s /\ q IN s /\ (p <> q) ==> pcoprime p q)
`;
(* overload on set of coprime polynomials *)
val _ = overload_on("pcoprime_set", ``poly_coprime_set r``);
(*
> poly_coprime_set_def;
val it = |- !r s. pcoprime_set s <=> (!p. p IN s ==> poly p) /\
            !p q. p IN s /\ q IN s /\ p <> q ==> pcoprime p q: thm
*)

(* Theorem: Field r ==> !s. FINITE s /\ (!q. q IN s ==> poly q) ==>
            !p. poly p /\ p NOTIN s /\ (!q. q IN s ==> pcoprime p q) ==> pcoprime p (PPROD s) *)
(* Proof:
   By finite induction on s.
   Base: pcoprime p (PPROD {})
      Since PPROD {} = |1|            by poly_prod_set_empty
      Hence pgcd p |1| ~~ |1|         by poly_gcd_one
         or pcoprime p |1|            by poly_gcd_one_coprime
   Step: e NOTIN s /\ p NOTIN e INSERT s ==> pcoprime p (PPROD (e INSERT s))
      Since PPROD (e INSERT s)
          = e * PPROD (s DELETE e)    by poly_prod_set_thm
          = e * PPROD s               by DELETE_NON_ELEMENT
        Now pcoprime p e              by IN_INSERT
        and pcoprime p (PPROD s)      by induction hypothesis
       With poly e                    by IN_INSERT
        and poly (PPROD s)            by poly_prod_set_poly
      Hence pcoprime p (e * PPROD s)  by poly_coprime_product_by_coprimes
*)
val poly_coprime_poly_prod = store_thm(
  "poly_coprime_poly_prod",
  ``!r:'a field. Field r ==> !s. FINITE s /\ (!q. q IN s ==> poly q) ==>
   !p. poly p /\ p NOTIN s /\ (!q. q IN s ==> pcoprime p q) ==> pcoprime p (PPROD s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> (!q. q IN s ==> poly q) ==>
   !p. poly p /\ p NOTIN s /\ (!q. q IN s ==> pcoprime p q) ==> pcoprime p (PPROD s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[poly_prod_set_empty, poly_gcd_one, poly_gcd_one_coprime] >>
  `PPROD (e INSERT s) = e * PPROD (s DELETE e)` by rw[poly_prod_set_thm] >>
  `_ = e * PPROD s` by metis_tac[DELETE_NON_ELEMENT] >>
  fs[IN_INSERT] >>
  rw[poly_coprime_product_by_coprimes, poly_prod_set_poly]);

(* Theorem: Field r ==> !s p. FINITE s /\ p NOTIN s /\ pcoprime_set (p INSERT s) ==>
            poly p /\ pcoprime_set s /\ pcoprime p (PPROD s) *)
(* Proof:
   By poly_coprime_set_def,
   !x. x IN (p INSERT s) ==> poly x /\
   !x y. x IN (p INSERT s) /\ y IN (p INSERT s) /\ x <> y ==> pcoprime x y
   Hence
   (1) p IN (p INSERT s) ==> poly p                       by IN_INSERT
   (2) !x. x IN s ==> poly x                              by IN_INSERT
       !x y. x IN s /\ y IN s /\ x <> y ==> pcoprime x y  by IN_INSERT
       These gives pcoprime_set s                         by poly_coprime_set_def
   (3) poly p /\ !x. x IN s ==> poly x                    by IN_INSERT
       !x. x IN s ==> pcoprime p x                        by IN_INSERT
       Hence pcoprime p (PPROD s)                         by poly_coprime_poly_prod
*)
val poly_coprime_set_insert = store_thm(
  "poly_coprime_set_insert",
  ``!r:'a field. Field r ==> !s p. FINITE s /\ p NOTIN s /\ pcoprime_set (p INSERT s) ==>
         poly p /\ pcoprime_set s /\ pcoprime p (PPROD s)``,
  ntac 5 strip_tac >>
  `!x. x IN (p INSERT s) ==> poly x /\
    !x y. x IN (p INSERT s) /\ y IN (p INSERT s) /\ x <> y ==> pcoprime x y` by metis_tac[poly_coprime_set_def] >>
  fs[IN_INSERT] >>
  rw[poly_coprime_set_def] >>
  `!x. x IN s ==> pcoprime p x` by metis_tac[] >>
  rw[poly_coprime_poly_prod]);

(* Theorem: Field r ==> !s. FINITE s /\ pcoprime_set s ==>
            !t. poly t /\ (!p. p IN s ==> p pdivides t) ==> (PPROD s) pdivides t *)
(* Proof:
   By finite induction on s.
   Base: PPROD {} pdivides t
      Since PPROD {} = |1|    by poly_prod_set_empty
        and |1| pdivides t    by poly_one_divides_all
   Step: e NOTIN s /\ pcoprime_set (e INSERT s) ==> PPROD (e INSERT s) pdivides t
      Since pcoprime_set (e INSERT s)
        ==> poly e /\ pcoprime_set s /\ pcoprime e (PPROD s)  by poly_coprime_set_insert
       From pcoprime_set s                   by above
        and !p. p IN s ==> p pdivides t      by IN_INSERT
        ==> PPROD s pdivides t               by induction hypothesis
       Also !p. p IN s ==> poly p            by poly_coprime_set_def
       Thus PPROD (e INSERT s)
          = e * PPROD (s DELETE e)           by poly_prod_set_thm
          = e * PPROD s                      by DELETE_NON_ELEMENT
       From poly e                           by above
        and poly (PPROD s)                   by poly_prod_set_poly
        and pcoprime e (PPROD s)             by above
      Hence (e * PPROD s) pdivides t         by poly_coprime_product_divides
*)
val poly_prod_coprime_set_divides = store_thm(
  "poly_prod_coprime_set_divides",
  ``!r:'a field. Field r ==> !s. FINITE s /\ pcoprime_set s ==>
   !t. poly t /\ (!p. p IN s ==> p pdivides t) ==> (PPROD s) pdivides t``,
  ntac 2 strip_tac >>
  `Ring r` by rw[] >>
  `!s. FINITE s ==> pcoprime_set s ==>
    !t. poly t /\ (!p. p IN s ==> p pdivides t) ==> PPROD s pdivides t` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[poly_prod_set_empty, poly_one_divides_all] >>
  fs[IN_INSERT] >>
  `poly e /\ pcoprime_set s /\ pcoprime e (PPROD s)` by metis_tac[poly_coprime_set_insert] >>
  `PPROD s pdivides t` by rw[] >>
  `!p. p IN s ==> poly p` by metis_tac[poly_coprime_set_def] >>
  `PPROD (e INSERT s) = e * PPROD (s DELETE e)` by rw[poly_prod_set_thm] >>
  `_ = e * PPROD s` by metis_tac[DELETE_NON_ELEMENT] >>
  `poly (PPROD s)` by rw[poly_prod_set_poly] >>
  rw[poly_coprime_product_divides]);

(* This is a milestone theorem. *)

(* Theorem: Field r ==> !f s. FINITE s /\ pcoprime_set (IMAGE f s) ==>
            !p. poly p /\ (!x. x IN s ==> (f x) pdivides p) ==> (PPIMAGE f s) pdivides p *)
(* Proof:
   Note FINITE (IMAGE f s)                     by IMAGE_FINITE
    and !y. y IN (IMAGE f s) ==> y pdivides p  by IN_IMAGE
   with pcoprime_set (IMAGE f s)               by given
    ==> PPROD (IMAGE f s) pdivides p           by poly_prod_coprime_set_divides
     or (PPIMAGE f s) pdivides p               by notation
*)
val poly_prod_coprime_image_divides = store_thm(
  "poly_prod_coprime_image_divides",
  ``!r:'a field. Field r ==> !f s. FINITE s /\ pcoprime_set (IMAGE f s) ==>
   !p. poly p /\ (!x. x IN s ==> (f x) pdivides p) ==> (PPIMAGE f s) pdivides p``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE f s` >>
  `FINITE t` by rw[Abbr`t`] >>
  `!y. y IN t ==> y pdivides p` by metis_tac[IN_IMAGE] >>
  rw[poly_prod_coprime_set_divides]);

(* ------------------------------------------------------------------------- *)
(* Monic Irreducible Sets                                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload for a set with every element monic and irreducible *)
val _ = overload_on("monic_irreducibles_set", ``\(r:'a ring) s. (!p. p IN s ==> monic p /\ ipoly p)``);

(* Overload monic_irreducibles_set r *)
val _ = overload_on("miset", ``monic_irreducibles_set r``);

(* Theorem: miset s ==> pset s *)
(* Proof: by poly_monic_poly *)
val monic_irreducible_set_poly_set = store_thm(
  "monic_irreducible_set_poly_set",
  ``!(r:'a ring) s. miset s ==> pset s``,
  rw[]);

(* Theorem: miset s ==> mset s *)
(* Proof: by notation *)
val monic_irreducible_set_monic_set = store_thm(
  "monic_irreducible_set_monic_set",
  ``!(r:'a ring) s. miset s ==> mset s``,
  rw[]);

(* Theorem: (!x. x IN s ==> miset x) ==> miset (BIGUNION s) *)
(* Proof: by IN_BIGUNION *)
val monic_irreducible_set_bigunion = store_thm(
  "monic_irreducible_set_bigunion",
  ``!(r:'a ring) s. (!x. x IN s ==> miset x) ==> miset (BIGUNION s)``,
  metis_tac[IN_BIGUNION]);

(* Theorem: Field r ==> !s. FINITE s /\ miset s ==>
            !p. monic p /\ ipoly p ==> (p pdivides PPROD s <=> p IN s) *)
(* Proof:
   By finite induction on s.
   Base: p pdivides PPROD {} <=> p IN {}
         p pdivides PPROD {}
     <=> p pdivides |1|                      by poly_prod_set_empty
     <=> upoly p                             by poly_divides_one
     Since ipoly ==> ~(upoly p)              by poly_irreducible_not_unit
     Hence LHS = F                           by contradiction
       and RHS = F                           by MEMBER_NOT_EMPTY
   Step: e NOTIN s ==> p pdivides PPROD (e INSERT s) <=> p IN e INSERT s
    Note monic e /\ ipoly e /\ miset s       by IN_INSERT
     and pset s                              by monic_irreducible_set_poly_set
    Also poly p /\ poly e /\ poly (PPROD s)  by poly_prod_set_poly, poly_monic_poly
    Thus PPROD (e INSERT s) = e * PPROD s    by poly_prod_set_insert
    Hence the goal becomes:
         p pdivides e * PPROD s <=> (p = e) \/ (p IN s)   by IN_INSERT
    If part: p pdivides e * PPROD s ==> (p = e) \/ (p IN s)
       By contradiction, suppose (p <> e) /\ (p NOTIN s).
       Then pcoprime p e                     by poly_monic_irreducibles_coprime, p <> e
         so mpgcd p e = |1|                  by poly_monic_gcd_one_coprime
       thus p pdivides (PPROD s)             by poly_monic_gcd_one_factor
        ==> p IN s                           by induction hypothesis
       This contradicts (p NOTIN s).
    Only-if part: (p = e) \/ (p IN s) ==> p pdivides e * PPROD s
       If p = e,
          Since e * PPROD s = PPROD s * e    by poly_mult_comm
          Hence e pdivides (PPROD s * e)     by poly_divides_def
       If p IN s,
          Since p pdivides (PPROD s)         by poly_prod_set_element_divides
          Hence p pdivides e * PPROD s       by poly_divides_multiple
*)
val poly_prod_monic_irreducible_set_divisor = store_thm(
  "poly_prod_monic_irreducible_set_divisor",
  ``!r:'a field. Field r ==> !s. FINITE s /\ miset s ==>
       !p. monic p /\ ipoly p ==> (p pdivides PPROD s <=> p IN s)``,
  ntac 2 strip_tac >>
  `Ring r` by rw[] >>
  `!s. FINITE s ==>
    !p. miset s /\ monic p /\ ipoly p ==> (p pdivides PPROD s <=> p IN s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >| [
    rw[poly_prod_set_empty, EQ_IMP_THM] >>
    spose_not_then strip_assume_tac >>
    `poly p` by rw[] >>
    `upoly p` by metis_tac[poly_divides_one] >>
    metis_tac[poly_irreducible_not_unit],
    `monic e /\ ipoly e /\ miset s` by metis_tac[IN_INSERT] >>
    `poly p /\ poly e /\ poly (PPROD s)` by rw[poly_prod_set_poly] >>
    `pset s` by rw[] >>
    `PPROD (e INSERT s) = e * PPROD s` by rw[poly_prod_set_insert] >>
    rw[EQ_IMP_THM] >| [
      spose_not_then strip_assume_tac >>
      `pcoprime p e` by metis_tac[poly_monic_irreducibles_coprime] >>
      `p pdivides (PPROD s)` by metis_tac[poly_monic_gcd_one_factor, poly_monic_gcd_one_coprime] >>
      `p IN s` by metis_tac[],
      metis_tac[poly_divides_def, poly_mult_comm],
      rw[poly_prod_set_element_divides, poly_divides_multiple]
    ]
  ]);

(* Theorem: Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
            ((PPROD s = PPROD t) <=> (s = t)) *)
(* Proof:
   Note miset s ==> pset s                by monic_irreducible_set_poly_set
   If part: (PPROD s = PPROD t) ==> (s = t)
      Claim: s SUBSET t
      For any p IN s, monic p /\ ipoly p  by miset s
         Then p pdivides (PPROD s)        by poly_prod_set_element_divides
           or p pdivides (PPROD t)        by given
         thus p IN t                      by poly_prod_monic_irreducible_set_divisor
      Claim: t SUBSET s                   by symmetric argument
      Hence s = t                         by SUBSET_ANTISYM

   Only-if part: (s = t) ==> (PPROD s = PPROD t)
      This is trivially true.
*)
val poly_prod_monic_irreducible_set_eq = store_thm(
  "poly_prod_monic_irreducible_set_eq",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
      ((PPROD s = PPROD t) <=> (s = t))``,
  rw[EQ_IMP_THM] >>
  (irule SUBSET_ANTISYM >> rpt conj_tac) >| [
    rw[SUBSET_DEF] >>
    `pset s` by rw[] >>
    `x pdivides (PPROD t)` by metis_tac[poly_prod_set_element_divides, field_is_ring] >>
    metis_tac[poly_prod_monic_irreducible_set_divisor],
    rw[SUBSET_DEF] >>
    `pset t` by rw[] >>
    `x pdivides (PPROD s)` by metis_tac[poly_prod_set_element_divides, field_is_ring] >>
    metis_tac[poly_prod_monic_irreducible_set_divisor]
  ]);

(* This is a milestone theorem. *)

(* Theorem: Field r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\
            (!s. s IN P ==> miset s) ==> (PPROD (BIGUNION P) = PPIMAGE PPROD P) *)
(* Proof:
   Note poly_set_multiplicative_fun r PPROD    by poly_prod_set_mult_fun
    and EVERY_PSET P                           by monic_irreducible_set_poly_set

   Claim: INJ PPROD P univ(:'a poly)
   Proof: By INJ_DEF, this is to show:
          x IN P /\ y IN P /\ PPROD x = PPROD y ==> x = y
     Note FINITE x and FINITE y                by EVERY_FINITE P
      and miset x and miset y                  by given implication
       so PPROD x = PPROD y ==> x = y          by poly_prod_monic_irreducible_set_eq

   The result follows with PPROD as f          by poly_disjoint_bigunion_mult_fun
*)
val poly_prod_disjoint_bigunion = store_thm(
  "poly_prod_disjoint_bigunion",
  ``!r:'a field. Field r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\
   (!s. s IN P ==> miset s) ==> (PPROD (BIGUNION P) = PPIMAGE PPROD P)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `poly_set_multiplicative_fun r PPROD` by rw_tac std_ss[poly_prod_set_mult_fun] >>
  `EVERY_PSET P` by metis_tac[monic_irreducible_set_poly_set] >>
  (`INJ PPROD P univ(:'a poly)` by (rw[INJ_DEF] >> metis_tac[poly_prod_monic_irreducible_set_eq])) >>
  metis_tac[poly_disjoint_bigunion_mult_fun]);

(* Theorem: Field r ==> !s. miset s ==> pcoprime_set s *)
(* Proof:
   By poly_coprime_set_def, this is to show:
   (1) pset s, or !x. x IN s ==> poly s, true                  by poly_monic_poly
   (2) !p q. p IN s /\ q IN s /\ p <> q ==> pcoprime p q, true by poly_monic_irreducibles_coprime
*)
val poly_monic_irreducibles_coprime_set = store_thm(
  "poly_monic_irreducibles_coprime_set",
  ``!r:'a field. Field r ==> !s. miset s ==> pcoprime_set s``,
  rw[poly_coprime_set_def] >>
  metis_tac[poly_monic_irreducibles_coprime]);

(* Theorem: Field r ==> !s. s SUBSET R ==> miset (IMAGE factor s) *)
(* Proof:
   By notation of miset, this is to show:
   (1) !x. x IN s ==> monic (factor x), true  by poly_factor_monic
   (2) !x. x IN s ==> ipoly (factor x), true  by poly_deg_factor, poly_deg_1_irreducible
*)
val poly_factor_image_monic_irreducibles_set = store_thm(
  "poly_factor_image_monic_irreducibles_set",
  ``!r:'a field. Field r ==> !s. s SUBSET R ==> miset (IMAGE factor s)``,
  (rw[SUBSET_DEF] >> rw[poly_factor_monic, poly_deg_factor, poly_deg_1_irreducible]));

(* Theorem: Field r ==> !p. poly p ==> !s. s SUBSET (roots p) ==> (PIFACTOR s) pdivides p *)
(* Proof:
   If p = |0|,
      Then any (poly p) pdivides |0|          by poly_divides_zero
   If p <> |0|,
      Apply poly_prod_coprime_set_divides, this is to show:
      (1) x IN s /\ s SUBSET (roots p) ==> (factor x) pdivides p
          Note x IN (roots p)                 by SUBSET_DEF
          Thus (factor x) pdivides p          by poly_root_factor
      (2) s SUBSET (roots p) ==> FINITE (IMAGE factor s)
          Note FINITE (roots p)               by poly_roots_finite, p <> |0|
          thus FINITE s                       by SUBSET_FINITE
           ==> FINITE (IMAGE factor s)        by IMAGE_FINITE
      (3) s SUBSET roots p ==> pcoprime_set (IMAGE factor s)
          Note (roots p) SUBSET               by poly_roots_def, SUBSET_DEF
          thus s SUBSET R                     by SUBSET_TRANS
           ==> miset (IMAGE factor s)         by poly_factor_image_monic_irreducibles_set
           ==> pcoprime_set (IMAGE factor s)  by poly_monic_irreducibles_coprime_set
*)
val poly_prod_factors_divides = store_thm(
  "poly_prod_factors_divides",
  ``!r:'a field. Field r ==> !p. poly p ==> !s. s SUBSET (roots p) ==> (PIFACTOR s) pdivides p``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[poly_divides_zero] >>
  (irule poly_prod_coprime_set_divides >> rpt conj_tac >> simp[]) >-
  metis_tac[poly_root_factor, SUBSET_DEF, field_is_ring, field_one_ne_zero] >-
 (`FINITE (roots p)` by rw[poly_roots_finite] >>
  metis_tac[SUBSET_FINITE, IMAGE_FINITE]) >>
  `(roots p) SUBSET R` by rw[poly_roots_def, SUBSET_DEF] >>
  `s SUBSET R` by metis_tac[SUBSET_TRANS] >>
  `miset (IMAGE factor s)` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
  rw[poly_monic_irreducibles_coprime_set]);

(* ------------------------------------------------------------------------- *)
(* Product of Monic Irreducible Sets                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !s. FINITE s /\ miset s ==> PPROD s <> |0| *)
(* Proof:
   Note pset s                    by monic_irreducible_set_poly_set
    and !p. p IN s ==> ipoly p    by miset s
                   ==> p <> |0|   by poly_irreducible_nonzero
   Hence PPROD s <> |0|           by poly_prod_set_nonzero
*)
val poly_prod_monic_irreducible_set_nonzero = store_thm(
  "poly_prod_monic_irreducible_set_nonzero",
  ``!r:'a field. Field r ==> !s. FINITE s /\ miset s ==> PPROD s <> |0|``,
  rpt strip_tac >>
  `pset s` by rw[monic_irreducible_set_poly_set] >>
  `!p. p IN s ==> p <> |0|` by rw[poly_irreducible_nonzero] >>
  metis_tac[poly_prod_set_nonzero]);

(* Theorem: Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
            ((PPROD t) pdivides (PPROD s) <=> (t SUBSET s)) *)
(* Proof:
   Let p = PPROD t, q = PPROD s.
   Note pset s /\ pset t       by monic_irreducible_set_poly_set
    ==> poly p /\ poly q       by poly_prod_set_poly

   If part: p pdivides q ==> t SUBSET s
      Let x IN t.
      Then x pdivides p        by poly_prod_set_element_divides
        so x pdivides q        by poly_divides_transitive
      Note monic x /\ ipoly x  by x IN t, miset t
       ==> x IN s              by poly_prod_monic_irreducible_set_divisor
      Thus t SUBSET s          by SUBSET_DEF

   Only-if part: t SUBSET s ==> p pdivides q
     Note pcoprime_set t       by poly_monic_irreducibles_coprime_set, miset t
      Let x IN t,
     then x IN s               by SUBSET_DEF
       so x pdivides q         by poly_prod_set_element_divides
     Thus !x. x IN t ==> x pdivides q    by above
      ==> p pdivides q         by poly_prod_coprime_set_divides
*)
val poly_prod_monic_irreducible_set_divisibility = store_thm(
  "poly_prod_monic_irreducible_set_divisibility",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
       ((PPROD t) pdivides (PPROD s) <=> (t SUBSET s))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `p = PPROD t` >>
  qabbrev_tac `q = PPROD s` >>
  `pset s /\ pset t` by rw[monic_irreducible_set_poly_set] >>
  `poly p /\ poly q` by rw[poly_prod_set_poly, Abbr`p`, Abbr`q`] >>
  rw[EQ_IMP_THM] >| [
    rw[SUBSET_DEF] >>
    `monic x /\ ipoly x` by rw[] >>
    `x pdivides p` by rw[poly_prod_set_element_divides, Abbr`p`] >>
    `x pdivides q` by metis_tac[poly_divides_transitive, poly_monic_poly] >>
    metis_tac[poly_prod_monic_irreducible_set_divisor],
    `pcoprime_set t` by rw[poly_monic_irreducibles_coprime_set] >>
    `!x. x IN t ==> x pdivides q` by metis_tac[poly_prod_set_element_divides, SUBSET_DEF] >>
    rw[poly_prod_coprime_set_divides, Abbr`p`]
  ]);

(* Theorem: Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t /\
            DISJOINT s t ==> pcoprime (PPROD s) (PPROD t) *)
(* Proof:
   Let p = PPROD s, q = PPROD t, m = mpgcd p q.
   Then monic p /\ monic q        by poly_monic_prod_set_monic
     so p <> |0| /\ q <> |0|      by poly_monic_nonzero
    ==> monic m                   by poly_monic_gcd_monic, p <> |0| /\ q <> |0|

   Claim: deg m = 0
   Proof: by contradiction, suppose deg m <> 0
   That is 0 < deg m                               by NOT_ZERO
      ==> ?i. monic i /\ ipoly i /\ i pdivides m   by poly_monic_irreducible_factor_exists
     Thus m pdivides p /\ m pdivides q             by poly_monic_gcd_divides
       so i pdivides p /\ i pdivides q             by poly_divides_transitive, poly_monic_poly
      ==> i IN s /\ i IN t                         by poly_prod_monic_irreducible_set_divisor
       or i IN s INTER t                           by IN_INTER
       or (s INTER t) <> {}                        by MEMBER_NOT_EMPTY
     This contradicts DISJOINT s t                 by DISJOINT_DEF

   Thus deg m = 0, and monic m,
    ==> m = |1|                                    by poly_monic_deg_0
     or pcoprime p q                               by poly_monic_gcd_one_coprime, poly_monic_poly
*)
val poly_prod_monic_irreducible_set_coprime = store_thm(
  "poly_prod_monic_irreducible_set_coprime",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t /\
      DISJOINT s t ==> pcoprime (PPROD s) (PPROD t)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `p = PPROD s` >>
  qabbrev_tac `q = PPROD t` >>
  qabbrev_tac `m = mpgcd p q` >>
  `monic p /\ monic q` by rw[poly_monic_prod_set_monic, Abbr`p`, Abbr`q`] >>
  `p <> |0| /\ q <> |0|` by rw[poly_monic_nonzero] >>
  `monic m` by rw[poly_monic_gcd_monic, Abbr`m`] >>
  `deg m = 0` by
  (spose_not_then strip_assume_tac >>
  `0 < deg m` by decide_tac >>
  `?i. monic i /\ ipoly i /\ i pdivides m` by rw[poly_monic_irreducible_factor_exists] >>
  `m pdivides p /\ m pdivides q` by rw[poly_monic_gcd_divides, Abbr`m`] >>
  `i pdivides p /\ i pdivides q` by metis_tac[poly_divides_transitive, poly_monic_poly] >>
  `i IN s /\ i IN t` by metis_tac[poly_prod_monic_irreducible_set_divisor] >>
  metis_tac[DISJOINT_DEF, IN_INTER, MEMBER_NOT_EMPTY]) >>
  metis_tac[poly_monic_deg_0, poly_monic_gcd_one_coprime, poly_monic_poly]);

(* This improved version makes the next one obsolete. *)

(* Theorem: Ring r ==> !s. FINITE s /\ miset s ==> !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v) *)
(* Proof:
   Note miset s ==> pset s    by monic_irreducible_set_poly_set
   The result follows         by poly_prod_set_by_partition
*)
val poly_prod_monic_irreducible_set_by_product = store_thm(
  "poly_prod_monic_irreducible_set_by_product",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ miset s ==> !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v)``,
  metis_tac[poly_prod_set_by_partition, monic_irreducible_set_poly_set]);


(* Theorem: Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
            (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t) *)
(* Proof:
   Let u = s UNION t, st = s INTER t.

   Step 1: partition s UNION t = s UNION (t DIFF s)
      Note u = s UNION (t DIFF s)                 by EXTENSION, IN_UNION, IN_DIFF
       and DISJOINT s (t DIFF s)                  by DISJOINT_DIFF
      Also FINITE u                               by FINITE_UNION
       and miset u                                by IN_UNION
       ==> PPROD u = PPROD s * PPROD (t DIFF s)   by poly_prod_monic_irreducible_set_by_product

   Step 2: partition t = (t DIFF s) UNION st
      Note t = (t DIFF s) UNION st                by EXTENSION, IN_DIFF, IN_UNION
       and DISJOINT (t DIFF s) st                 by DISJOINT_DEF, EXTENSION
      Also FINITE (t DIFF s)                      by FINITE_DIFF
       and FINITE st                              by FINITE_INTER
       and miset (t DIFF s) /\ miset st           by IN_DIFF, IN_INTER
       ==> PPROD t = PPROD (t DIFF s) * PPROD st  by poly_prod_monic_irreducible_set_by_product

   Step 3: conclude
     Note !s. FINITE s /\ miset s ==> poly (PPROD s)  by monic_irreducible_set_poly_set, poly_prod_set_poly
          PPROD (s UNION t) * PPROD (s INTER t)
        = PPROD u * PPROD st                      by notation
        = PPROD s * PPROD (t DIFF s) * PPROD st   by Step 1
        = PPROD s * (PPROD (t DIFF s) * PPROD st) by poly_mult_assoc
        = PPROD s * PPROD t                       by Step 2
*)
val poly_prod_monic_irreducible_sets_product = store_thm(
  "poly_prod_monic_irreducible_sets_product",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ miset s /\ FINITE t /\ miset t ==>
    (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `u = s UNION t` >>
  qabbrev_tac `st = s INTER t` >>
  (`u = s UNION (t DIFF s)` by (rw[EXTENSION, Abbr`u`] >> metis_tac[])) >>
  `DISJOINT s (t DIFF s)` by rw[DISJOINT_DIFF] >>
  `FINITE u` by rw[Abbr`u`] >>
  `miset u` by metis_tac[IN_UNION] >>
  `PPROD u = PPROD s * PPROD (t DIFF s)` by rw[poly_prod_monic_irreducible_set_by_product] >>
  (`t = (t DIFF s) UNION st` by (rw[Abbr`st`, EXTENSION] >> metis_tac[])) >>
  (`DISJOINT (t DIFF s) st` by (rw[DISJOINT_DEF, Abbr`st`, EXTENSION] >> metis_tac[])) >>
  `FINITE (t DIFF s) /\ FINITE st` by rw[Abbr`st`] >>
  `miset (t DIFF s) /\ miset st` by metis_tac[IN_DIFF, IN_INTER] >>
  `PPROD t = PPROD (t DIFF s) * PPROD st` by rw[poly_prod_monic_irreducible_set_by_product] >>
  `!s. FINITE s /\ miset s ==> poly (PPROD s)` by rw[monic_irreducible_set_poly_set, poly_prod_set_poly] >>
  rw[poly_mult_assoc]);

(* Theorem: Field r ==> !s. FINITE s /\ miset s ==> !p q. monic p /\ monic q /\ (p * q = PPROD s) ==>
            ?s1 s2. (s = s1 UNION s2) /\ (DISJOINT s1 s2) /\ (p = PPROD s1) /\ (q = PPROD s2) *)
(* Proof:
    Let s1 = {x | x IN s /\ x pdivides p}, s2 = s DIFF s1.
   Then s1 SUBSET s, s2 SUBSET s.
        s1 UNION s2 = s                          by UNION_DIFF
        and DISJOINT s1 s2                       by DISJOINT_DIFF
   Thus PPROD s = (PPROD s1) * (PPROD s2)        by poly_prod_monic_irreducible_set_by_product

   Step 1: show p = ps * (PPROD s1)
   Note FINITE s1 /\ FINITE s2                   by SUBSET_FINITE
    and miset s1 /\ miset s2                     by SUBSET_DEF
   also pcoprime_set s1 /\ pcoprime_set s2       by poly_monic_irreducibles_coprime_set

    Now !x. x IN s1 ==> x pdivides p             by EXTENSION of s1
    ==> (PPROD s1) pdivides p                    by poly_prod_coprime_set_divides
     or ?ps. poly ps /\ (p = ps * (PPROD s1))    by poly_divides_def

   Step 2: show q = qs * (PPROD s2)
    Claim: !x. x IN s2 ==> x pdivides q
    Proof: !x. x IN s2,
       ==> x IN s /\ ~(x pdivides p)
      Note x IN s ==> ipoly x                    by miset s
       and x IN s ==> x pdivides (PPROD s)       by poly_prod_set_element_divides
        or x pdivides (p * q)                    by PPROD s = p * q
       ==> x pdivides q                          by poly_irreducible_divides_product

    Thus (PPROD s2) pdivides q                   by poly_prod_coprime_set_divides
      or q = qs * (PPROD s2)                     by poly_divides_def

   Step 3: conclude
    Therefore                 PPROD s = p * q
      becomes (PPROD s1) * (PPROD s2) = ps * (PPROD s1) * qs * (PPROD s2)
    Note (PPROD s) <> |0|                        by poly_prod_monic_irreducible_set_nonzero, miset s
     ==> ps * qs = |1|                           by poly_mult_assoc, poly_mult_comm, poly_mult_rcancel
    Thus upoly ps /\ upoly qs                    by poly_unit_partner, poly_mult_comm
      or (deg ps = 0) /\ (deg qs = 0)            by poly_field_unit_deg
    Note monic ps /\ monic qs                    by poly_monic_monic_mult, poly_mult_comm
     ==> (ps = |1|) /\ (qs = |1|)                by poly_monic_deg_0
      or (p = PPROD s1) /\ (q = PPROD s2)        by poly_mult_lone
    Take these s1 and s2, the result follows.
*)
val poly_prod_monic_irreducible_set_divisors = store_thm(
  "poly_prod_monic_irreducible_set_divisors",
  ``!r:'a field. Field r ==> !s. FINITE s /\ miset s ==>
   !p q. monic p /\ monic q /\ (p * q = PPROD s) ==>
   ?s1 s2. (s = s1 UNION s2) /\ (DISJOINT s1 s2) /\ (p = PPROD s1) /\ (q = PPROD s2)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `s1 = {x | x IN s /\ x pdivides p}` >>
  qabbrev_tac `s2 = s DIFF s1` >>
  `s1 SUBSET s /\ s2 SUBSET s` by rw[Abbr`s1`, Abbr`s2`, SUBSET_DEF] >>
  `s1 UNION s2 = s` by rw[UNION_DIFF, Abbr`s2`] >>
  `DISJOINT s1 s2` by rw[DISJOINT_DIFF, Abbr`s2`] >>
  qabbrev_tac `t = PPROD s` >>
  qabbrev_tac `tp = PPROD s1` >>
  qabbrev_tac `tq = PPROD s2` >>
  `t = tp * tq` by rw[poly_prod_monic_irreducible_set_by_product, Abbr`t`, Abbr`tp`, Abbr`tq`] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `miset s1 /\ miset s2` by rw[] >>
  `pcoprime_set s1 /\ pcoprime_set s2` by rw[poly_monic_irreducibles_coprime_set] >>
  `!x. x IN s1 ==> x pdivides p` by rw[Abbr`s1`] >>
  `tp pdivides p` by rw[poly_prod_coprime_set_divides, Abbr`tp`] >>
  `?ps. poly ps /\ (p = ps * tp)` by rw[GSYM poly_divides_def] >>
  `!x. x IN s2 ==> x pdivides q` by
  (rpt strip_tac >>
  `!x. x IN s1 <=> x IN s /\ x pdivides p` by rw[Abbr`s1`] >>
  `x IN s /\ ~(x pdivides p)` by metis_tac[IN_DIFF] >>
  `ipoly x` by rw[] >>
  `pset s` by metis_tac[monic_irreducible_set_poly_set] >>
  `x pdivides t` by rw_tac std_ss[poly_prod_set_element_divides, Abbr`t`] >>
  metis_tac[poly_irreducible_divides_product, poly_monic_poly]) >>
  `tq pdivides q` by rw[poly_prod_coprime_set_divides, Abbr`tq`] >>
  `?qs. poly qs /\ (q = qs * tq)` by rw[GSYM poly_divides_def] >>
  `t <> |0|` by rw[poly_prod_monic_irreducible_set_nonzero, Abbr`t`] >>
  `monic t /\ monic tp /\ monic tq /\ poly t /\ poly tp /\ poly tq` by rw[poly_monic_prod_set_monic, Abbr`t`, Abbr`tp`, Abbr`tq`] >>
  `poly |1| /\ poly (ps * tp) /\ poly (qs * ps) /\ poly (tp * tq)` by rw[] >>
  `|1| * (tp * tq) = (ps * tp) * (qs * tq)` by rw[] >>
  `_ = ((ps * tp) * qs) * tq` by prove_tac[poly_mult_assoc] >>
  `_ = qs * (ps * tp) * tq` by rw[poly_mult_comm] >>
  `_ = (qs * ps) * (tp * tq)` by prove_tac[poly_mult_assoc] >>
  `qs * ps = |1|` by prove_tac[poly_mult_rcancel] >>
  `upoly ps /\ upoly qs` by prove_tac[poly_unit_partner, poly_mult_comm] >>
  `monic ps /\ monic qs` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
  `(ps = |1|) /\ (qs = |1|)` by rw[poly_field_unit_deg, GSYM poly_monic_deg_0] >>
  `(p = tp) /\ (q = tq)` by rw[] >>
  metis_tac[]);

(* Theorem: Field r ==> !s. FINITE s /\ miset s ==>
            !p. monic p /\ p pdivides (PPROD s) ==> ?t. t SUBSET s /\ (p = PPROD t) *)
(* Proof:
   Note monic (PPROD s)                     by poly_monic_prod_set_monic, miset s
    ==> ?q. poly q /\ (PPROD s = q * p)     by poly_divides_def
     or PPROD s = p * q                     by poly_mult_comm
   Thus monic q                             by poly_monic_monic_mult, poly_monic_poly
    ==> ?s1 s2. (s = s1 UNION s2) /\ DISJOINT s1 s2 /\
        (p = PPROD s1) /\ (q = PPROD s2)    by poly_prod_monic_irreducible_set_divisors
   Note s1 SUBSET s                         by SUBSET_UNION
   Hence take t = s1, and the result follows.
*)
val poly_prod_monic_irreducible_set_divisor_form = store_thm(
  "poly_prod_monic_irreducible_set_divisor_form",
  ``!r:'a field. Field r ==> !s. FINITE s /\ miset s ==>
   !p. monic p /\ p pdivides (PPROD s) ==> ?t. t SUBSET s /\ (p = PPROD t)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `monic (PPROD s)` by rw[poly_monic_prod_set_monic] >>
  `?q. poly q /\ (PPROD s = q * p)` by rw[GSYM poly_divides_def] >>
  `_ = p * q` by rw[poly_mult_comm] >>
  `monic q` by metis_tac[poly_monic_monic_mult, poly_monic_poly] >>
  `?s1 s2. (s = s1 UNION s2) /\ DISJOINT s1 s2 /\ (p = PPROD s1) /\ (q = PPROD s2)` by rw[poly_prod_monic_irreducible_set_divisors] >>
  `s1 SUBSET s` by rw[] >>
  metis_tac[]);

(* Note: The following is slightly better than poly_prod_factors_divisibility:
|- !r. Field r ==> !s t. FINITE s /\ s SUBSET R /\ FINITE t /\ t SUBSET R ==>
                         (PIFACTOR t pdivides PIFACTOR s <=> t SUBSET s)
*)

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==>
            !t. t SUBSET s ==> (PIFACTOR t) pdivides (PIFACTOR s) *)
(* Proof:
   Note poly (PIFACTOR s)                   by poly_prod_factors_poly
    and roots (PIFACTOR s) = s              by poly_prod_factors_roots
   Thus t SUBSET roots (PIFACTOR s)         by given, t SUBSET s
    ==> (PIFACTOR t) pdivides (PIFACTOR s)  by poly_prod_factors_divides
*)
val poly_prod_factors_divides_poly_prod_factor = store_thm(
  "poly_prod_factors_divides_poly_prod_factor",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==>
   !t. t SUBSET s ==> (PIFACTOR t) pdivides (PIFACTOR s)``,
  rw[poly_prod_factors_poly, poly_prod_factors_roots, poly_prod_factors_divides]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==>
            !p. monic p ==> (p pdivides (PIFACTOR s) <=> ?t. t SUBSET s /\ (p = PIFACTOR t)) *)
(* Proof:
   If part: p pdivides PIFACTOR s ==> ?t. t SUBSET s /\ (p = PIFACTOR t)
      Note FINITE (IMAGE factor s)       by IMAGE_FINITE
       and miset (IMAGE factor s)        by poly_factor_image_monic_irreducibles_set, s SUBSET R
       ==> ?tt. tt SUBSET (IMAGE factor s) /\ (p = PPROD tt)  by poly_prod_monic_irreducible_set_divisor_form
       Let t = {x | x IN s /\ factor x IN tt}
      Then t SUBSET s                    by SUBSET_DEF
       and IMAGE factor t = tt           by EXTENSION, SUBSET_DEF, IN_IMAGE
      Take this t,
      then p = PPROD tt = PIFACTOR t     by notation

   Only-if part: ?t. t SUBSET s /\ (p = PIFACTOR t) ==> p pdivides s
      True by poly_prod_factors_divides_poly_prod_factor
*)
val poly_prod_factors_monic_divisor = store_thm(
  "poly_prod_factors_monic_divisor",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==>
   !p. monic p ==> (p pdivides (PIFACTOR s) <=> ?t. t SUBSET s /\ (p = PIFACTOR t))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  rw[EQ_IMP_THM] >| [
    `FINITE (IMAGE factor s)` by rw[] >>
    `miset (IMAGE factor s)` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
    `?tt. tt SUBSET (IMAGE factor s) /\ (p = PPROD tt)` by rw[poly_prod_monic_irreducible_set_divisor_form] >>
    qabbrev_tac `t = {x | x IN s /\ factor x IN tt}` >>
    `!x. x IN t <=> x IN s /\ (factor x IN tt)` by rw[Abbr`t`] >>
    `t SUBSET s` by rw[SUBSET_DEF] >>
    (`IMAGE factor t = tt` by (rw[EXTENSION] >> metis_tac[SUBSET_DEF, IN_IMAGE])) >>
    metis_tac[],
    rw[poly_prod_factors_divides_poly_prod_factor]
  ]);

(* Theorem: Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
            !p. monic p /\ p pdivides (PIFACTOR s) /\ p pdivides (PIFACTOR t) ==> p pdivides PIFACTOR (s INTER t) *)
(* Proof:
   Note p pdivides (PIFACTOR s)
    ==> ?u. u SUBSET s /\ (p = PIFACTOR u)   by poly_prod_factors_monic_divisor
   Note FINITE u                             by SUBSET_FINITE
   Note u SUBSET R                           by SUBSET_TRANS, s SUBSET R
   Also p pdivides (PIFACTOR t)
    ==> u SUBSET t                           by poly_prod_factors_divisibility
   Thus u SUBSET (s INTER t)                 by SUBSET_INTER
    and FINITE (s INTER t)                   by FINITE_INTER
    and (s INTER t) SUBSET R                 by INTER_SUBSET, SUBSET_TRANS
    ==> p pdivides (PPROD (s INTER t))       by poly_prod_factors_divides_poly_prod_factor
*)
val poly_prod_factors_monic_common_divisor = store_thm(
  "poly_prod_factors_monic_common_divisor",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
   !p. monic p /\ p pdivides (PIFACTOR s) /\ p pdivides (PIFACTOR t) ==> p pdivides PIFACTOR (s INTER t)``,
  rpt strip_tac >>
  `?u. u SUBSET s /\ (p = PIFACTOR u)` by rw[GSYM poly_prod_factors_monic_divisor] >>
  `FINITE u` by metis_tac[SUBSET_FINITE] >>
  `u SUBSET R` by metis_tac[SUBSET_TRANS] >>
  `u SUBSET t` by metis_tac[poly_prod_factors_divisibility] >>
  `u SUBSET (s INTER t)` by rw[] >>
  `FINITE (s INTER t)` by rw[] >>
  `(s INTER t) SUBSET R` by metis_tac[INTER_SUBSET, SUBSET_TRANS] >>
  rw[poly_prod_factors_divides_poly_prod_factor]);

(* Theorem: Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
            (mpgcd (PIFACTOR s) (PIFACTOR t) = PIFACTOR (s INTER t)) *)
(* Proof:
   Let st = s INTER t.
   Then FINITE st                     by FINITE_INTER
    and st SUBSET R                   by IN_INTER, SUBSET_DEF
    and st SUBSET s /\ st SUBSET t    by INTER_SUBSET
   Note monic (PIFACTOR s)            by poly_prod_factors_monic
    and monic (PIFACTOR t)            by poly_prod_factors_monic
    and monic (PIFACTOR st)           by poly_prod_factors_monic
    Now (PIFACTOR st) pdivides (PIFACTOR s)   by poly_prod_factors_divisibility
    and (PIFACTOR st) pdivides (PIFACTOR t)   by poly_prod_factors_divisibility
   Also PIFACTOR s <> |0|                     by poly_monic_nonzero
    and !p. monic p /\ p pdivides PIFACTOR s /\ p pdivides PIFACTOR t ==>
         p pdivides PIFACTOR (s INTER t)                 by poly_prod_factors_monic_common_divisor
   Thus mpgcd (PIFACTOR s) (PIFACTOR t) = (PIFACTOR st)  by poly_monic_gcd_condition
*)
val poly_prod_factors_monic_gcd = store_thm(
  "poly_prod_factors_monic_gcd",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
    (mpgcd (PIFACTOR s) (PIFACTOR t) = PIFACTOR (s INTER t))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (s INTER t)` by rw[] >>
  `(s INTER t) SUBSET R` by metis_tac[IN_INTER, SUBSET_DEF] >>
  `(s INTER t) SUBSET s /\ (s INTER t) SUBSET t` by rw[] >>
  `monic (PIFACTOR s) /\ monic (PIFACTOR t)` by rw[poly_prod_factors_monic] >>
  `monic (PIFACTOR (s INTER t))` by rw[poly_prod_factors_monic] >>
  rw[poly_prod_factors_divisibility, poly_prod_factors_monic_common_divisor, poly_monic_gcd_condition, poly_monic_nonzero]);

(* Theorem: Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
             ((PIFACTOR s = PIFACTOR t) <=> (s = t)) *)
(* Proof:
   Note FINITE (IMAGE factor s) /\ FINITE (IMAGE factor t)    by IMAGE_FINITE
    and miset (IMAGE factor s) /\ miset (IMAGE factor t)      by poly_factor_image_monic_irreducibles_set
                   PIFACTOR s = PIFACTOR t
   <=> PPROD (IMAGE factor s) = PPROD (IMAGE factor t)        by notation
   <=>         IMAGE factor s = IMAGE factor t                by poly_prod_monic_irreducible_set_eq
   <=>                      s = t                             by poly_factor_image_eq
*)
val poly_prod_factors_eq = store_thm(
  "poly_prod_factors_eq",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
    ((PIFACTOR s = PIFACTOR t) <=> (s = t))``,
  rpt strip_tac >>
  `FINITE (IMAGE factor s) /\ FINITE (IMAGE factor t)` by rw[] >>
  `miset (IMAGE factor s) /\ miset (IMAGE factor t)` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
  rw[poly_prod_monic_irreducible_set_eq, poly_factor_image_eq]);

(* Theorem: Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
            (PIFACTOR (s UNION t) * PIFACTOR (s INTER t) = (PIFACTOR s) * (PIFACTOR t)) *)
(* Proof:
    Let fs = IMAGE factor s, ft = IMAGE factor t.
   Note INJ factor R univ(:'a poly)                by poly_factor_injective
    ==> IMAGE factor (s INTER t) = fs INTER ft     by INJ_IMAGE_INTER
   Also IMAGE factor (s INTER t) = fs UNION ft     by IMAGE_UNION
   Note FINITE fs /\ FINITE ft                     by IMAGE_FINITE
    and miset fs /\ miset ft                       by poly_factor_image_monic_irreducibles_set
    ==> PPROD (ss UNION tt) * PPROD (ss INTER tt)
      = PPROD ss * PPROD tt                        by poly_prod_monic_irreducible_sets_product
*)
val poly_prod_factors_product = store_thm(
  "poly_prod_factors_product",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
    (PIFACTOR (s UNION t) * PIFACTOR (s INTER t) = (PIFACTOR s) * (PIFACTOR t))``,
  rpt strip_tac >>
  qabbrev_tac `fs = IMAGE factor s` >>
  qabbrev_tac `ft = IMAGE factor t` >>
  `INJ factor R univ(:'a poly)` by rw[poly_factor_injective] >>
  `IMAGE factor (s INTER t) = fs INTER ft` by metis_tac[INJ_IMAGE_INTER] >>
  rw[IMAGE_UNION] >>
  `FINITE fs /\ FINITE ft` by rw[Abbr`fs`, Abbr`ft`] >>
  `miset fs /\ miset ft` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
  rw[poly_prod_monic_irreducible_sets_product]);


(* Theorem: Field r ==> ring_set_multiplicative_fun r PIFACTOR *)
(* Proof:
   By ring_set_multiplicative_fun_def, this is to show:
   (1) PPROD {} = |1|, true                    by poly_prod_set_empty
   (2) s SUBSET R ==> poly (PIFACTOR s), true  by poly_prod_factors_poly
   (3) FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==>
       PIFACTOR (s UNION t) * PIFACTOR (s INTER t) = PIFACTOR s * PIFACTOR t
       This is true                            by poly_prod_factors_product
*)
val poly_prod_factors_ring_mult_fun = store_thm(
  "poly_prod_factors_ring_mult_fun",
  ``!r:'a field. Field r ==> ring_set_multiplicative_fun r PIFACTOR``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw_tac std_ss[ring_set_multiplicative_fun_def] >-
  rw[poly_prod_set_empty] >-
  rw[poly_prod_factors_poly] >>
  rw[poly_prod_factors_product]);

(* ------------------------------------------------------------------------- *)
(* Coprime with Derivative                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !p. poly p /\ pgcd p (diff p) ~~ |1| ==>
            !q. poly q /\ 0 < deg q /\ q pdivides p ==> !k. 1 < k ==> ~(q ** k pdivides p) *)
(* Proof:
   By contradiction, assume q ** k pdivides p.
   Then ?s. poly s /\ (p = s * (q ** k))     by poly_divides_def

   Step 1: compute diff p.
       diff p = (diff s) * (q ** k) + s * (diff (q ** k))                 by poly_diff_mult
              = (diff s) * (q ** k) + s * (##k * q ** (PRE k) * diff q)   by poly_diff_exp
        Now 1 < k ==> PRE k <> 0 /\ k <> 0                                by arithmetic
       Thus ?m n. (PRE k = SUC m) /\ (k = SUC n)                          by num_CASES
       Hence diff s * q ** k
           = diff s * (q ** n * q)                  by poly_exp_suc
           = diff s * q ** n * q                    by poly_mult_assoc
        Also s * (##k * q ** (PRE k) * diff q)
           = ##k * (s * (q ** (SUC m) * diff q))    by poly_mult_cmult, poly_cmult_mult
           = ##k * (s * (diff q * q ** (SUC m)))    by poly_mult_comm
           = ##k * (s * (diff q * (q ** m * q)))    by poly_exp_suc
           = ##k * s * diff q * q ** m * q          by poly_cmult_mult, poly_mult_assoc
       Therefore
       diff p = (diff s * q ** n + ##k * s * diff q * q ** m) * q         by poly_mult_ladd
   Step 2: conclude by divisibility
       Hence q pdivides (diff p)                    by poly_divides_def, poly_add_poly
         ==> q pdivides (pgcd p (diff p))           by poly_gcd_is_gcd
       Since upoly (pgcd p (diff p))                by poly_unit_eq_one
          so upoly q                                by poly_divides_unit
       giving deg q = 0                             by poly_field_unit_deg
       which contradicts 0 < deg q.
*)
val poly_coprime_diff_simple_divisor = store_thm(
  "poly_coprime_diff_simple_divisor",
  ``!r:'a field. Field r ==> !p. poly p /\ pgcd p (diff p) ~~ |1| ==>
   !q. poly q /\ 0 < deg q /\ q pdivides p ==> !k. 1 < k ==> ~(q ** k pdivides p)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `?s. poly s /\ (p = s * (q ** k))` by rw[GSYM poly_divides_def] >>
  `diff p = (diff s) * (q ** k) + s * (diff (q ** k))` by rw[poly_diff_mult] >>
  `_ = (diff s) * (q ** k) + s * (##k * q ** (PRE k) * diff q)` by rw_tac std_ss[poly_diff_exp] >>
  `PRE k <> 0 /\ k <> 0` by decide_tac >>
  `?m n. (PRE k = SUC m) /\ (k = SUC n)` by metis_tac[num_CASES] >>
  `diff s * q ** k = diff s * (q ** n * q)` by rw[poly_exp_suc] >>
  `_ = diff s * q ** n * q` by rw[poly_mult_assoc] >>
  `s * (##k * q ** (PRE k) * diff q) = ##k * (s * (q ** (SUC m) * diff q))` by rw[poly_mult_cmult, poly_cmult_mult] >>
  `_ = ##k * (s * (diff q * q ** (SUC m)))` by rw[poly_mult_comm] >>
  `_ = ##k * (s * (diff q * (q ** m * q)))` by rw[poly_exp_suc] >>
  `_ = ##k * s * diff q * q ** m * q` by rw[poly_cmult_mult, poly_mult_assoc] >>
  `poly (diff s * q ** n) /\ poly (##k * s * diff q * q ** m)` by rw[] >>
  `diff p = (diff s * q ** n + ##k * s * diff q * q ** m) * q` by rw_tac std_ss[poly_mult_ladd] >>
  `q pdivides (diff p)` by metis_tac[poly_divides_def, poly_add_poly] >>
  `q pdivides (pgcd p (diff p))` by rw[poly_gcd_is_gcd] >>
  `upoly (pgcd p (diff p))` by rw[poly_unit_eq_one] >>
  `upoly q` by metis_tac[poly_divides_unit] >>
  `deg q = 0` by rw[poly_field_unit_deg] >>
  decide_tac);

(* Theorem: Field r ==> !p. poly p /\ pcoprime p (diff p) ==> p <> |0| *)
(* Proof:
   Note mpgcd p (diff p) = |1|                by poly_monic_gcd_one_coprime
   By contradiction, suppose p = |0|.
   Then diff |0| = |0|                        by poly_diff_zero
     so pgcd |0| |0| = |0|                    by poly_gcd_zero
    and mpgcd |0| |0| = |0|                   by poly_monic_gcd_zero_zero
   This is a contradiction since |0| <> |1|   by poly_one_ne_poly_zero
*)
val poly_coprime_diff_nonzero = store_thm(
  "poly_coprime_diff_nonzero",
  ``!r:'a field. Field r ==> !p. poly p /\ pcoprime p (diff p) ==> p <> |0|``,
  rpt strip_tac >>
  qabbrev_tac `q = diff p` >>
  `poly q` by rw[poly_diff_poly, Abbr`q`] >>
  `mpgcd p q = |1|` by rw[GSYM poly_monic_gcd_one_coprime] >>
  `q = |0|` by rw[poly_diff_zero, Abbr`q`] >>
  `Ring r /\ |1| <> |0| /\ poly |0|` by rw[] >>
  metis_tac[poly_gcd_zero, poly_monic_gcd_zero_zero]);

(* Theorem: Field r ==> !t. poly t /\ pcoprime t (diff t) ==>
            !s. FINITE s /\ (!p. p IN s ==> poly p) /\
           (PPROD s) pdivides t /\ (!p. monic p /\ ipoly p /\ p pdivides t ==> p IN s) ==>  t ~~ PPROD s *)
(* Proof:
   Let p = PPROD s.
   Then poly p             by poly_prod_set_poly
   Note p pdivides t
    ==> ?u. poly u /\ (t = u * p)    by poly_divides_def
    ==> u pdivides t       by poly_divides_def, poly_mult_comm
   If upoly u,
      t ~~ p               by poly_unit_eq_property
   If ~(upoly u),
      Since t <> |0|       by poly_coprime_diff_nonzero
       then u <> |0|       by poly_mult_eq_zero
         so deg u <> 0     by poly_field_units
         ?q. monic q /\ ipoly q /\ q pdivides u        by poly_monic_irreducible_factor_exists
         or  monic q /\ ipoly q /\ q pdivides t        by poly_divides_transitive
        thus q IN s                                    by implication
       Hence q pdivides p                              by poly_prod_set_element_divides
      Now q pdivides u ==> ?x. poly x /\ (u = x * q)   by poly_divides_def
      and q pdivides p ==> ?y. poly y /\ (p = y * q)   by poly_divides_def
   Thus   t = u * p
            = (x * q) * (y * q)    by above
            = (x * y) * (q * q)    by poly_mult_assoc, poly_mult_comm
            = (x * y) * (q ** 2)   by poly_exp_2
    Note pgcd t (diff t) ~~ |1|    by poly_gcd_one_coprime
     and 0 < deg q                 by poly_irreducible_deg_nonzero
    thus q ** 2 pdivides t         by poly_divides_def
     But ~(q ** 2 pdivides t)      by poly_coprime_diff_simple_divisor
   This is a contradiction.
*)
val poly_coprime_diff_unit_eq_prod_set = store_thm(
  "poly_coprime_diff_unit_eq_prod_set",
  ``!r:'a field. Field r ==> !t. poly t /\ pcoprime t (diff t) ==>
   !s. FINITE s /\ pset s /\ (PPROD s) pdivides t /\
    (!p. monic p /\ ipoly p /\ p pdivides t ==> p IN s) ==>  t ~~ PPROD s``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  qabbrev_tac `p = PPROD s` >>
  `poly p` by rw[poly_prod_set_poly, Abbr`p`] >>
  `?u. poly u /\ (t = u * p)` by rw[GSYM poly_divides_def] >>
  `u pdivides t` by metis_tac[poly_divides_def, poly_mult_comm] >>
  Cases_on `upoly u` >-
  metis_tac[poly_unit_eq_property] >>
  `t <> |0|` by rw[poly_coprime_diff_nonzero] >>
  `u <> |0|` by metis_tac[poly_mult_eq_zero] >>
  `deg u <> 0` by metis_tac[poly_field_units] >>
  `0 < deg u` by simp[] >>
  `?q. monic q /\ ipoly q /\ q pdivides u` by rw[poly_monic_irreducible_factor_exists] >>
  `poly q` by rw[] >>
  `q pdivides t` by metis_tac[poly_divides_transitive] >>
  `q IN s` by rw[] >>
  `q pdivides p` by metis_tac[poly_prod_set_element_divides] >>
  `?x. poly x /\ (u = x * q) /\ ?y. poly y /\ (p = y * q)` by rw[GSYM poly_divides_def] >>
  `t = (x * q) * (y * q)` by rw[] >>
  `_ = (x * (q * y)) * q` by rw[poly_mult_assoc] >>
  `_ = (x * (y * q)) * q` by metis_tac[poly_mult_comm] >>
  `_ = (x * y) * (q * q)` by prove_tac[poly_mult_assoc, poly_mult_poly] >>
  `_ = (x * y) * (q ** 2)` by rw[poly_exp_2] >>
  `pgcd t (diff t) ~~ |1|` by rw[GSYM poly_gcd_one_coprime] >>
  `0 < deg q` by rw[poly_irreducible_deg_nonzero] >>
  `q ** 2 pdivides t` by metis_tac[poly_divides_def, poly_mult_poly] >>
  metis_tac[poly_coprime_diff_simple_divisor, DECIDE``1 < 2``]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
