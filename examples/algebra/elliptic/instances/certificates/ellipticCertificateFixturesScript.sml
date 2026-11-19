(* Supporting facts for the certificate selftests. The regression proofs
   exercising the certificate tactics remain in selftest.sml. *)
Theory ellipticCertificateFixtures
Ancestors
  shortWeierstrass shortWeierstrassSmall ellipticCertificates
  field fieldInstances group pred_set ring polyFieldModulo
  pairingQuadraticFields
Libs
  pairingCurveCertificateLib

Theorem certificate_GF5_member:
  ECAffine 2 2 IN sw_points (GF 5) 0 1
Proof
  SIMP_TAC bool_ss
    [sw_GF5_points, IN_INSERT, NOT_IN_EMPTY]
QED

Theorem certificate_GF49_field:
  Field (PolyModRing (GF 7) [1n;0;1])
Proof
  metis_tac
    [FiniteField_def, poly_mod_irreducible_finite_field,
     GF_finite_field, PRIME_7, prime_3mod4_quadratic_irreducible,
     EQT_ELIM (EVAL ``7 MOD 4 = 3``)]
QED

Theorem certificate_GF49_char[local]:
  ring$char (PolyModRing (GF 7) [1n;0;1]) = 7
Proof
  simp[poly_mod_ring_char_alt, GF_field, PRIME_7, GF_prime_char,
       prime_3mod4_quadratic_monic, prime_3mod4_quadratic_degree]
QED

val quadratic_arithmetic = pairingCurveCertificateLib.FIELD_CONV
  PRIME_7 certificate_GF49_field;

Theorem certificate_GF49_curve:
  ShortWeierstrassCurve (PolyModRing (GF 7) [1n;0;1]) [] [1n]
Proof
  SIMP_TAC bool_ss
    [ShortWeierstrassCurve_def, certificate_GF49_field,
     certificate_GF49_char] >>
  CONV_TAC (REWRITE_CONV [sw_discriminant_def] THENC quadratic_arithmetic)
QED

Theorem certificate_GF49_member:
  ECAffine [0n;1] [3n;1] IN
    sw_points (PolyModRing (GF 7) [1n;0;1]) [] [1n]
Proof
  CONV_TAC (REWRITE_CONV
    [sw_points_member, sw_on_curve_def, sw_curve_rhs_def] THENC
    quadratic_arithmetic)
QED
