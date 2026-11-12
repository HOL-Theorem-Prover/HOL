(* -------------------------------------------------------------------------
   Quadratic-to-degree-twelve field embeddings

   Documentation
   bn254_fp2_to_fp12_def and bls12381_fp2_to_fp12_def substitute i in
   canonical ascending polynomial representatives and reduce modulo the
   degree-twelve polynomial. Here w = X, and i = w^6-9 for BN254 or
   i = w^6-1 for BLS12-381. Zero is [], including in constant inclusions.

   Public interface
   - *_fp12_w_def and *_fp12_i_def name the distinguished representatives;
     *_fp12_i_relation and *_fp2_modulus_vanishes justify substitution.
   - bn254_fp2_to_fp12_field_homo, bls12381_fp2_to_fp12_field_homo and
     matching *_inj theorems prove homomorphism and carrier injectivity.
   - *_fp2_to_fp12_constant fixes residues c < p, *_fp2_to_fp12_i maps
     [0;1] to i, and *_fp12_w_sixth computes w^6.

   Homomorphism and injectivity concern the named field carriers, not
   arbitrary lists; concrete computations use checked quotient conversions.
   ------------------------------------------------------------------------- *)

Theory pairingFieldEmbeddings
Ancestors
  namedPrimes namedPrimeFields fieldInstances
  pairingQuadraticFields pairingDegree12Fields
  bn254Degree12Certificate bls12381Degree12Certificate
  polyRingModulo polyRing polyMap polyEval polyDivision polyMonic fieldMap
Libs
  polynomialCertificateLib pairingFieldCertificateLib

open fieldTheory ringTheory polynomialTheory groupTheory monoidTheory
     pred_setTheory polyDivisionTheory polyEvalTheory polyModuloRingTheory
     polyMonicTheory polyRingTheory

(* Substitution descends through a polynomial quotient precisely when the
   defining polynomial vanishes.  This proves preservation of operations for
   every polynomial, rather than testing representatives coefficientwise. *)
Theorem polynomial_quotient_substitution_remainder[local]:
  !(r:'a ring) z h t.
    Ring r /\ poly_monic r z /\ 0 < poly_deg r z /\
    poly_monic r h /\ 0 < poly_deg r h /\ Poly r t /\
    poly_mod r (poly_peval r z t) h = [] ==>
    !p. Poly r p ==>
      poly_mod r (poly_peval r (poly_mod r p z) t) h =
      poly_mod r (poly_peval r p t) h
Proof
  rpt strip_tac >>
  `pmonic z /\ pmonic h` by metis_tac[poly_monic_pmonic] >>
  mp_tac (Q.SPECL [`r`, `p`, `z`] poly_div_mod_def) >>
  ASM_REWRITE_TAC [] >> STRIP_TAC >>
  `Poly r (poly_mult r (poly_div r p z) z)` by metis_tac[poly_mult_poly] >>
  `poly_peval r p t =
   poly_add r
     (poly_mult r (poly_peval r (poly_div r p z) t)
                  (poly_peval r z t))
     (poly_peval r (poly_mod r p z) t)`
    by
      (qpat_x_assum
         `p = poly_add r (poly_mult r (poly_div r p z) z) (poly_mod r p z)`
         (fn eq => CONV_TAC
           (LAND_CONV (RATOR_CONV (RAND_CONV (REWR_CONV eq))))) >>
       ASM_SIMP_TAC bool_ss [poly_peval_add, poly_peval_mult]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  `Poly r (poly_peval r (poly_div r p z) t) /\
   Poly r (poly_peval r z t) /\
   Poly r (poly_peval r (poly_mod r p z) t)` by
    metis_tac[poly_peval_poly] >>
  ASM_SIMP_TAC bool_ss [Once poly_mod_add, poly_mult_poly] >>
  ASM_SIMP_TAC bool_ss
    ([Once poly_mod_mult, poly_mod_poly, poly_mod_mod] @
     map (REWRITE_RULE [polynomialTheory.poly_zero])
       [poly_zero_mod, poly_mult_rzero, poly_add_lzero])
QED

Theorem polynomial_quotient_substitution_homo[local]:
  !(r:'a ring) z h t.
    Ring r /\ poly_monic r z /\ 0 < poly_deg r z /\
    poly_monic r h /\ 0 < poly_deg r h /\ Poly r t /\
    poly_mod r (poly_peval r z t) h = [] ==>
    RingHomo (\p. poly_mod r (poly_peval r p t) h)
      (PolyModRing r z) (PolyModRing r h)
Proof
  rpt strip_tac >>
  `pmonic z /\ pmonic h` by metis_tac[poly_monic_pmonic] >>
  `poly_deg r z <> 0 /\ poly_deg r h <> 0` by decide_tac >>
  `!p. Poly r p ==>
    poly_mod r (poly_peval r (poly_mod r p z) t) h =
    poly_mod r (poly_peval r p t) h`
    by metis_tac[polynomial_quotient_substitution_remainder] >>
  rw[RingHomo_def, GroupHomo_def, MonoidHomo_def,
     poly_mod_ring_property, poly_peval_poly, poly_deg_mod_less] >-
    rw[poly_peval_add, GSYM poly_mod_add] >>
  rw[poly_peval_mult, GSYM poly_mod_mult]
QED

Definition bn254_fp12_w_def:
  bn254_fp12_w = [0n;1]
End
Definition bls12381_fp12_w_def:
  bls12381_fp12_w = [0n;1]
End

(* i = w^6 - 9 and i = w^6 - 1, respectively. *)
Definition bn254_fp12_i_def:
  bn254_fp12_i = [bn254_p-9;0;0;0;0;0;1]
End
Definition bls12381_fp12_i_def:
  bls12381_fp12_i = [bls12381_p-1;0;0;0;0;0;1]
End

Definition bn254_fp2_to_fp12_def:
  bn254_fp2_to_fp12 =
    \p. poly_mod (GF bn254_p) (poly_peval (GF bn254_p) p bn254_fp12_i)
      bn254_fp12_poly
End
Definition bls12381_fp2_to_fp12_def:
  bls12381_fp2_to_fp12 =
    \p. poly_mod (GF bls12381_p) (poly_peval (GF bls12381_p) p bls12381_fp12_i)
      bls12381_fp12_poly
End

Theorem bn254_fp12_w_member:
  bn254_fp12_w IN bn254_fp12.carrier /\ bn254_fp12_w <> bn254_fp12.sum.id
Proof
  REWRITE_TAC [bn254_fp12_w_def, bn254_fp12_def, bn254_fp12_poly_def,
               bn254_p_def, poly_mod_ring_element, poly_mod_ring_ids] >>
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED
Theorem bls12381_fp12_w_member:
  bls12381_fp12_w IN bls12381_fp12.carrier /\
  bls12381_fp12_w <> bls12381_fp12.sum.id
Proof
  REWRITE_TAC [bls12381_fp12_w_def, bls12381_fp12_def, bls12381_fp12_poly_def,
               bls12381_p_def, poly_mod_ring_element, poly_mod_ring_ids] >>
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED

Theorem bn254_fp12_i_relation:
  bn254_fp12.sum.op bn254_fp12_i [9] =
    bn254_fp12.prod.exp bn254_fp12_w 6
Proof
  REWRITE_TAC [bn254_fp12_i_def, bn254_fp12_w_def, bn254_fp12_def,
               bn254_fp12_poly_def, bn254_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))
QED
Theorem bls12381_fp12_i_relation:
  bls12381_fp12.sum.op bls12381_fp12_i [1] =
    bls12381_fp12.prod.exp bls12381_fp12_w 6
Proof
  REWRITE_TAC [bls12381_fp12_i_def, bls12381_fp12_w_def, bls12381_fp12_def,
               bls12381_fp12_poly_def, bls12381_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))
QED

Theorem bn254_fp2_modulus_vanishes:
  poly_mod (GF bn254_p)
    (poly_peval (GF bn254_p) bn254_fp2_poly bn254_fp12_i)
    bn254_fp12_poly = []
Proof
  REWRITE_TAC [bn254_fp2_poly_def, bn254_fp12_i_def,
               bn254_fp12_poly_def, bn254_p_def] >>
  CONV_TAC certificateComputeLib.NAT_CONV >>
  CONV_TAC (LAND_CONV (polynomialCertificateLib.REMAINDER_CONV
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))) >> REFL_TAC
QED
Theorem bls12381_fp2_modulus_vanishes:
  poly_mod (GF bls12381_p)
    (poly_peval (GF bls12381_p) bls12381_fp2_poly bls12381_fp12_i)
    bls12381_fp12_poly = []
Proof
  REWRITE_TAC [bls12381_fp2_poly_def, bls12381_fp12_i_def,
               bls12381_fp12_poly_def, bls12381_p_def] >>
  CONV_TAC certificateComputeLib.NAT_CONV >>
  CONV_TAC (LAND_CONV (polynomialCertificateLib.REMAINDER_CONV
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))) >> REFL_TAC
QED

Theorem bn254_fp2_to_fp12_field_homo:
  FieldHomo bn254_fp2_to_fp12 bn254_fp2 bn254_fp12
Proof
  REWRITE_TAC [FieldHomo_def, bn254_fp2_def, bn254_fp12_def,
               bn254_fp2_to_fp12_def] >>
  irule polynomial_quotient_substitution_homo >>
  simp[GF_field, field_is_ring, bn254_p_prime, bn254_fp2_poly_monic,
       bn254_fp12_poly_monic, bn254_fp2_poly_degree,
       bn254_fp12_poly_degree, bn254_fp2_modulus_vanishes] >>
  REWRITE_TAC [bn254_fp12_i_def, bn254_p_def] >>
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED
Theorem bls12381_fp2_to_fp12_field_homo:
  FieldHomo bls12381_fp2_to_fp12 bls12381_fp2 bls12381_fp12
Proof
  REWRITE_TAC [FieldHomo_def, bls12381_fp2_def, bls12381_fp12_def,
               bls12381_fp2_to_fp12_def] >>
  irule polynomial_quotient_substitution_homo >>
  simp[GF_field, field_is_ring, bls12381_p_prime, bls12381_fp2_poly_monic,
       bls12381_fp12_poly_monic, bls12381_fp2_poly_degree,
       bls12381_fp12_poly_degree, bls12381_fp2_modulus_vanishes] >>
  REWRITE_TAC [bls12381_fp12_i_def, bls12381_p_def] >>
  CONV_TAC polynomialCertificateLib.ARITH_CONV
QED

Theorem bn254_fp2_to_fp12_inj:
  INJ bn254_fp2_to_fp12 bn254_fp2.carrier bn254_fp12.carrier
Proof
  metis_tac[field_homo_map_inj, bn254_fp2_to_fp12_field_homo,
            bn254_fp2_finite_field, bn254_fp12_finite_field, FiniteField_def]
QED
Theorem bls12381_fp2_to_fp12_inj:
  INJ bls12381_fp2_to_fp12 bls12381_fp2.carrier bls12381_fp12.carrier
Proof
  metis_tac[field_homo_map_inj, bls12381_fp2_to_fp12_field_homo,
            bls12381_fp2_finite_field, bls12381_fp12_finite_field, FiniteField_def]
QED

(* The prime-field inclusion is the canonical constant polynomial; zero
   must be [], never [0]. *)
Theorem polynomial_quotient_substitution_constant[local]:
  !(r:'a ring) z t c.
    Ring r /\ poly_monic r z /\ 0 < poly_deg r z /\ c IN r.carrier ==>
    poly_mod r (poly_peval r (if c = r.sum.id then [] else [c]) t) z =
      if c = r.sum.id then [] else [c]
Proof
  rpt strip_tac >>
  `pmonic z` by metis_tac[poly_monic_pmonic] >>
  Cases_on `c = r.sum.id` >>
  simp[poly_peval_const, poly_mod_const,
       REWRITE_RULE [polynomialTheory.poly_zero] poly_zero_mod]
QED

Theorem bn254_fp2_to_fp12_constant:
  !c. c < bn254_p ==>
    bn254_fp2_to_fp12 (if c = 0 then [] else [c]) =
      if c = 0 then [] else [c]
Proof
  rpt strip_tac >> REWRITE_TAC [bn254_fp2_to_fp12_def] >>
  mp_tac (ISPECL [``GF bn254_p``, ``bn254_fp12_poly``, ``bn254_fp12_i``, ``c:num``]
    polynomial_quotient_substitution_constant) >>
  simp[GF_zero, GF_element, GF_field, field_is_ring, bn254_p_prime,
       bn254_fp12_poly_monic, bn254_fp12_poly_degree]
QED
Theorem bls12381_fp2_to_fp12_constant:
  !c. c < bls12381_p ==>
    bls12381_fp2_to_fp12 (if c = 0 then [] else [c]) =
      if c = 0 then [] else [c]
Proof
  rpt strip_tac >> REWRITE_TAC [bls12381_fp2_to_fp12_def] >>
  mp_tac (ISPECL [``GF bls12381_p``, ``bls12381_fp12_poly``, ``bls12381_fp12_i``, ``c:num``]
    polynomial_quotient_substitution_constant) >>
  simp[GF_zero, GF_element, GF_field, field_is_ring, bls12381_p_prime,
       bls12381_fp12_poly_monic, bls12381_fp12_poly_degree]
QED

Theorem bn254_fp12_w_sixth:
  bn254_fp12.prod.exp bn254_fp12_w 6 = [0;0;0;0;0;0;1]
Proof
  REWRITE_TAC [bn254_fp12_w_def, bn254_fp12_def,
               bn254_fp12_poly_def, bn254_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))
QED
Theorem bls12381_fp12_w_sixth:
  bls12381_fp12.prod.exp bls12381_fp12_w 6 = [0;0;0;0;0;0;1]
Proof
  REWRITE_TAC [bls12381_fp12_w_def, bls12381_fp12_def,
               bls12381_fp12_poly_def, bls12381_p_def] >>
  CONV_TAC (pairingFieldCertificateLib.QUOTIENT_CONV
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))
QED

Theorem bn254_fp2_to_fp12_i:
  bn254_fp2_to_fp12 [0;1] = bn254_fp12_i
Proof
  REWRITE_TAC [bn254_fp2_to_fp12_def, bn254_fp12_i_def,
               bn254_fp12_poly_def, bn254_p_def] >>
  CONV_TAC (LAND_CONV BETA_CONV) >>
  CONV_TAC certificateComputeLib.NAT_CONV >>
  CONV_TAC (LAND_CONV (polynomialCertificateLib.REMAINDER_CONV
    (REWRITE_RULE [bn254_p_def] bn254_p_prime)
    (rhs (concl (EVAL ``bn254_fp12_poly``))))) >> REFL_TAC
QED
Theorem bls12381_fp2_to_fp12_i:
  bls12381_fp2_to_fp12 [0;1] = bls12381_fp12_i
Proof
  REWRITE_TAC [bls12381_fp2_to_fp12_def, bls12381_fp12_i_def,
               bls12381_fp12_poly_def, bls12381_p_def] >>
  CONV_TAC (LAND_CONV BETA_CONV) >>
  CONV_TAC certificateComputeLib.NAT_CONV >>
  CONV_TAC (LAND_CONV (polynomialCertificateLib.REMAINDER_CONV
    (REWRITE_RULE [bls12381_p_def] bls12381_p_prime)
    (rhs (concl (EVAL ``bls12381_fp12_poly``))))) >> REFL_TAC
QED

val _ = export_theory();
