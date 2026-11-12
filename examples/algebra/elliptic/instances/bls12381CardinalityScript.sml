(* BLS12-381 G1: full rational-point cardinality and full cofactor.

   Documentation
   This concerns y^2 = x^3 + 4 over bls12381_base_field, not merely the
   standard generator's subgroup. A product of two generated subgroups,
   with independence established using complex multiplication, supplies
   the cardinality divisor; the elementary point bound fixes the count.

   Certificate data: bls12381_full_cofactor_def, bls12381_torsion_factor_def,
   bls12381_large_order_def, bls12381_large_point_def,
   bls12381_second_point_def, bls12381_cm_beta_def.
   Arithmetic and product: bls12381_full_cofactor_factorization,
   bls12381_full_certificate_subgroup_def,
   bls12381_full_certificate_subgroup_product_card,
   bls12381_full_certificate_subgroup_card.
   Main interface: bls12381_g1_full_cardinality,
   bls12381_g1_full_cofactor, bls12381_g1_prime_subgroup_not_full.

   The full cofactor is not an effective hash-to-curve cofactor.
   Coordinates and primality witnesses are proof inputs, not trusted
   external point-count or primality verdicts. *)

Theory bls12381Cardinality
Ancestors
  namedPrimes bls12381CofactorPrimes
  bls12381G1Instance ellipticCardinality ellipticCMMap ellipticCMCertificates
  prime number gcd ring
  namedPrimeFields fieldInstances shortWeierstrass shortWeierstrassGroup
  ellipticTorsion
Libs
  ellipticCertificateLib Grobner Omega

open arithmeticTheory dividesTheory pred_setTheory groupTheory monoidTheory
     fieldTheory ringTheory fieldInstancesTheory primeTheory numberTheory gcdTheory

(* The full cofactor is 3*d^2, not the effective hash-to-curve cofactor.
   Two cyclic factors are necessary: a point of order h*r or h*r/3
   does not exist. All coordinates and Lucas witnesses below are untrusted
   certificate data; their asserted properties are checked in HOL. *)
Definition bls12381_full_cofactor_def:
  bls12381_full_cofactor :num = 76329603384216526031706109802092473003
End

Definition bls12381_torsion_factor_def:
  bls12381_torsion_factor :num = 5044125407647214251
End

Definition bls12381_large_order_def:
  bls12381_large_order :num = 793479390729215512516507951283169066088130679960393952059283337873017453583023682367384822284289
End

Definition bls12381_large_point_def:
  bls12381_large_point = ECAffine
    (547267894408768087084154039555760353521479753946258632875036726158932984746527535614714820052060149146314557270019:num)
    (1835063209175869974242139117441761755355391001264886580587881843166918857183334906933623397100805888438647438806516:num)
End

Definition bls12381_second_point_def:
  bls12381_second_point = ECAffine
    (3858090099720686728417485250591617790007549725898262042292787773251801161414924166623599824090938137111696763759792:num)
    (163271841639119587171174696652600132121318062989845671486906499701356099729440404580392597287975441777888549222973:num)
End

Definition bls12381_cm_beta_def:
  bls12381_cm_beta :num = 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350
End


Theorem bls12381_full_cofactor_factorization:
  bls12381_torsion_factor = 11 * 10177 * 859267 * 52437899 /\
  bls12381_full_cofactor = 3 * bls12381_torsion_factor ** 2 /\
  bls12381_large_order = 3 * bls12381_torsion_factor * bls12381_n /\
  bls12381_full_cofactor * bls12381_n =
    bls12381_large_order * bls12381_torsion_factor
Proof
  EVAL_TAC
QED

Theorem bls12381_large_point_member:
  bls12381_large_point IN sw_points bls12381_base_field 0 4
Proof
  REWRITE_TAC [sw_points_member, sw_on_curve_def, sw_curve_rhs_def,
    bls12381_base_field_def, bls12381_p_def, bls12381_large_point_def,
    GF_eval, monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem bls12381_second_point_member:
  bls12381_second_point IN sw_points bls12381_base_field 0 4
Proof
  REWRITE_TAC [sw_points_member, sw_on_curve_def, sw_curve_rhs_def,
    bls12381_base_field_def, bls12381_p_def, bls12381_second_point_def,
    GF_eval, monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

val cardinality_definitions =
  [bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def,
   bls12381_base_field_def, bls12381_p_def, bls12381_n_def,
   bls12381_large_point_def, bls12381_second_point_def,
   bls12381_large_order_def, bls12381_torsion_factor_def,
   bls12381_full_cofactor_def, bls12381_cm_beta_def];
fun cardinality_numeric th =
  CONV_RULE certificateComputeLib.NAT_CONV
    (REWRITE_RULE cardinality_definitions th);
val cardinality_prime = cardinality_numeric bls12381_p_prime;
val cardinality_curve = cardinality_numeric bls12381_g1_curve;
val large_scalar_certificate = ellipticCertificateLib.SCALAR_CERTIFICATE_TAC 4
  cardinality_prime cardinality_curve
  (cardinality_numeric bls12381_large_point_member);
val large_scalar_step = ellipticCertificateLib.SCALAR_STEP_TAC cardinality_prime
  cardinality_curve (cardinality_numeric bls12381_large_point_member);
val second_scalar_certificate = ellipticCertificateLib.SCALAR_CERTIFICATE_TAC 4
  cardinality_prime cardinality_curve
  (cardinality_numeric bls12381_second_point_member);
val second_scalar_step = ellipticCertificateLib.SCALAR_STEP_TAC cardinality_prime
  cardinality_curve (cardinality_numeric bls12381_second_point_member);
val cardinality_scalar_normalize = REWRITE_TAC cardinality_definitions >>
  CONV_TAC certificateComputeLib.NAT_CONV;
val cardinality_scalar_finish =
  REWRITE_TAC [sw_cm_map_def, bls12381_base_field_def, bls12381_p_def,
               GF_eval] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ());

(* Explicit four-bit milestones give each checked window its own deadline.
   CM comparisons evaluate their two scalar occurrences in residual branches. *)
Theorem bls12381_large_scalar_annihilation[local]:
  bls12381_g1_group.exp bls12381_large_point bls12381_large_order = ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step]
QED
Theorem bls12381_large_scalar_div3[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 3) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_large_scalar_div11[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_large_scalar_div10177[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_large_scalar_div859267[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_large_scalar_div52437899[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_large_scalar_divn[local]:
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV bls12381_n) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED

Theorem bls12381_large_point_scalar_tests:
  bls12381_g1_group.exp bls12381_large_point bls12381_large_order = ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 3) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV bls12381_n) <> ECInfinity
Proof
  simp[bls12381_large_scalar_annihilation, bls12381_large_scalar_div3,
       bls12381_large_scalar_div11, bls12381_large_scalar_div10177,
       bls12381_large_scalar_div859267, bls12381_large_scalar_div52437899,
       bls12381_large_scalar_divn]
QED

Theorem bls12381_second_scalar_annihilation[local]:
  bls12381_g1_group.exp bls12381_second_point bls12381_torsion_factor = ECInfinity
Proof
  cardinality_scalar_normalize >>
  second_scalar_certificate >| [ second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step]
QED
Theorem bls12381_second_scalar_div11[local]:
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 11) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  second_scalar_certificate >| [ second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_second_scalar_div10177[local]:
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 10177) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  second_scalar_certificate >| [ second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_second_scalar_div859267[local]:
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 859267) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  second_scalar_certificate >| [ second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      cardinality_scalar_finish]
QED
Theorem bls12381_second_scalar_div52437899[local]:
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 52437899) <> ECInfinity
Proof
  cardinality_scalar_normalize >>
  second_scalar_certificate >| [ second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      second_scalar_step,
      cardinality_scalar_finish]
QED

Theorem bls12381_second_point_scalar_tests:
  bls12381_g1_group.exp bls12381_second_point bls12381_torsion_factor = ECInfinity /\
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 11) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 10177) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 859267) <> ECInfinity /\
  bls12381_g1_group.exp bls12381_second_point (bls12381_torsion_factor DIV 52437899) <> ECInfinity
Proof
  simp[bls12381_second_scalar_annihilation, bls12381_second_scalar_div11,
       bls12381_second_scalar_div10177, bls12381_second_scalar_div859267,
       bls12381_second_scalar_div52437899]
QED

Theorem bls12381_torsion_prime_divisors:
  prime q /\ q divides bls12381_torsion_factor ==>
  q = 11 \/ q = 10177 \/ q = 859267 \/ q = 52437899
Proof
  strip_tac >>
  `q divides (11 * 10177 * 859267 * 52437899)` by
    metis_tac[bls12381_full_cofactor_factorization] >>
  metis_tac[gcdTheory.P_EUCLIDES, prime_divides_only_self,
            bls12381_cofactor_primes]
QED

Theorem bls12381_large_order_prime_divisors:
  prime q /\ q divides bls12381_large_order ==>
  q = 3 \/ q = 11 \/ q = 10177 \/ q = 859267 \/ q = 52437899 \/ q = bls12381_n
Proof
  strip_tac >>
  `q divides (3 * bls12381_torsion_factor * bls12381_n)` by
    metis_tac[bls12381_full_cofactor_factorization] >>
  metis_tac[gcdTheory.P_EUCLIDES, prime_divides_only_self,
            PRIME_3, bls12381_n_prime, bls12381_torsion_prime_divisors]
QED

Theorem bls12381_large_point_order:
  order bls12381_g1_group bls12381_large_point = bls12381_large_order
Proof
  rw[bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def] >>
  `0 < bls12381_large_order` by EVAL_TAC >>
  irule sw_exact_order_certificate >>
  simp[REWRITE_RULE [bls12381_g1_a_def, bls12381_g1_b_def] bls12381_g1_curve,
       bls12381_large_point_member] >>
  metis_tac[bls12381_large_order_prime_divisors,
    REWRITE_RULE [bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def]
      bls12381_large_point_scalar_tests]
QED

Theorem bls12381_second_point_order:
  order bls12381_g1_group bls12381_second_point = bls12381_torsion_factor
Proof
  rw[bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def] >>
  `0 < bls12381_torsion_factor` by EVAL_TAC >>
  irule sw_exact_order_certificate >>
  simp[REWRITE_RULE [bls12381_g1_a_def, bls12381_g1_b_def] bls12381_g1_curve,
       bls12381_second_point_member] >>
  metis_tac[bls12381_torsion_prime_divisors,
    REWRITE_RULE [bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def]
      bls12381_second_point_scalar_tests]
QED


fun natural_ring_tac (asl,w) =
  let
    val th = Grobner.NUM_RING w
    val proof = if aconv (concl th) w then th else EQT_ELIM th
  in ACCEPT_TAC proof (asl,w) end;

Theorem bls12381_cubic_product[local]:
  ((t:num) + a) * (t + b) * (t + c) =
  t ** 3 + (a + b + c) * t ** 2 +
  (a * b + a * c + b * c) * t + a * b * c
Proof
  natural_ring_tac
QED

Theorem bls12381_cube_roots_10177[local]:
  t < 10177 /\ t ** 3 MOD 10177 = 1 ==>
  t = 1 \/ t = 4773 \/ t = 5403
Proof
  strip_tac >>
  `((t + 10176) * (t + 5404) * (t + 4774)) MOD 10177 = 0` by
    (simp[bls12381_cubic_product, MOD_PLUS, MOD_TIMES2] >>
     ONCE_REWRITE_TAC [GSYM MOD_PLUS] >> asm_simp_tac (srw_ss()) []) >>
  `prime 10177` by metis_tac[bls12381_cofactor_primes] >>
  `10177 divides ((t + 10176) * (t + 5404) * (t + 4774))` by
    asm_simp_tac bool_ss [DIVIDES_MOD_0, DECIDE ``(0:num) < 10177``] >>
  `10177 divides (t + 10176) \/ 10177 divides (t + 5404) \/
   10177 divides (t + 4774)` by
    metis_tac[gcdTheory.P_EUCLIDES] >>
  fs[DIVIDES_MOD_0, DECIDE ``(0:num) < 10177``] >> Omega.OMEGA_TAC
QED

Theorem bls12381_cube_roots_859267[local]:
  t < 859267 /\ t ** 3 MOD 859267 = 1 ==>
  t = 1 \/ t = 119571 \/ t = 739695
Proof
  strip_tac >>
  `((t + 859266) * (t + 739696) * (t + 119572)) MOD 859267 = 0` by
    (simp[bls12381_cubic_product, MOD_PLUS, MOD_TIMES2] >>
     ONCE_REWRITE_TAC [GSYM MOD_PLUS] >> asm_simp_tac (srw_ss()) []) >>
  `prime 859267` by metis_tac[bls12381_cofactor_primes] >>
  `859267 divides ((t + 859266) * (t + 739696) * (t + 119572))` by
    asm_simp_tac bool_ss [DIVIDES_MOD_0, DECIDE ``(0:num) < 859267``] >>
  `859267 divides (t + 859266) \/ 859267 divides (t + 739696) \/
   859267 divides (t + 119572)` by
    metis_tac[gcdTheory.P_EUCLIDES] >>
  fs[DIVIDES_MOD_0, DECIDE ``(0:num) < 859267``] >> Omega.OMEGA_TAC
QED

Theorem bls12381_torsion_cubic_roots:
  prime q /\ q divides bls12381_torsion_factor /\
  t < q /\ t ** 3 MOD q = 1 ==>
  (q = 11 /\ t = 1) \/
  (q = 10177 /\ (t = 1 \/ t = 4773 \/ t = 5403)) \/
  (q = 859267 /\ (t = 1 \/ t = 119571 \/ t = 739695)) \/
  (q = 52437899 /\ t = 1)
Proof
  strip_tac >>
  `q = 11 \/ q = 10177 \/ q = 859267 \/ q = 52437899` by
    metis_tac[bls12381_torsion_prime_divisors] >>
  fs[] >>
  metis_tac[bls12381_cube_roots_10177, bls12381_cube_roots_859267,
            cm_cube_root_coprime,
            EVAL ``coprime 3 (11 - 1)``,
            EVAL ``coprime 3 (52437899 - 1)``]
QED

Theorem bls12381_base_field_zero[local]:
  bls12381_base_field.sum.id = 0
Proof
  EVAL_TAC
QED

Theorem bls12381_cm_beta_certificate:
  bls12381_cm_beta IN bls12381_base_field.carrier /\
  bls12381_base_field.prod.exp bls12381_cm_beta 3 =
    bls12381_base_field.prod.id
Proof
  REWRITE_TAC [bls12381_base_field_def, bls12381_p_def, bls12381_cm_beta_def,
    GF_eval, monoid_exp_def] >>
  CONV_TAC (certificateComputeLib.EVAL_CONV ())
QED

Theorem bls12381_cm_endo:
  GroupEndo (sw_cm_map bls12381_base_field bls12381_cm_beta)
    bls12381_g1_group
Proof
  metis_tac[sw_cm_map_group_endo, bls12381_cm_beta_certificate,
            bls12381_g1_curve, bls12381_base_field_zero,
            bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def]
QED

Theorem bls12381_cm_third:
  !P. P IN bls12381_g1_group.carrier ==>
  sw_cm_map bls12381_base_field bls12381_cm_beta
    (sw_cm_map bls12381_base_field bls12381_cm_beta
      (sw_cm_map bls12381_base_field bls12381_cm_beta P)) = P
Proof
  metis_tac[sw_cm_map_third, bls12381_cm_beta_certificate,
            bls12381_base_field_field, bls12381_g1_group_def,
            sw_group_carrier]
QED

Theorem bls12381_large_scalar_mult[local]:
  bls12381_g1_group.exp (bls12381_g1_group.exp bls12381_large_point m) n =
  bls12381_g1_group.exp bls12381_large_point (m * n)
Proof
  metis_tac[group_exp_mult, bls12381_g1_finite_group,
            FiniteAbelianGroup_def_alt, FiniteGroup_def,
            bls12381_large_point_member, bls12381_g1_group_def,
            bls12381_g1_a_def, bls12381_g1_b_def, sw_group_carrier]
QED

Theorem bls12381_cm_large_scalar[local]:
  bls12381_g1_group.exp
    (sw_cm_map bls12381_base_field bls12381_cm_beta bls12381_large_point) n =
  sw_cm_map bls12381_base_field bls12381_cm_beta
    (bls12381_g1_group.exp bls12381_large_point n)
Proof
  metis_tac[group_homo_exp, GroupEndo_def, bls12381_cm_endo,
            bls12381_g1_finite_group, FiniteAbelianGroup_def_alt,
            FiniteGroup_def, bls12381_large_point_member,
            bls12381_g1_group_def, bls12381_g1_a_def,
            bls12381_g1_b_def, sw_group_carrier]
QED

Theorem bls12381_second_point_cm_expression:
  bls12381_second_point = bls12381_g1_group.exp
    (sw_cm_map bls12381_base_field bls12381_cm_beta bls12381_large_point)
    (bls12381_large_order DIV bls12381_torsion_factor)
Proof
  rw[bls12381_cm_large_scalar] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]
QED

Theorem bls12381_cm_check_11[local]:
  !t. t = 1 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11)) t
Proof
  gen_tac >> DISCH_THEN SUBST1_TAC >>
  (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])
QED
Theorem bls12381_cm_check_10177[local]:
  !t. t = 1 \/ t = 4773 \/ t = 5403 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177)) t
Proof
  gen_tac >> DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)
  >| [(REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]),
      (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      (large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])]),
      (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      (large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])])]
QED
Theorem bls12381_cm_check_859267[local]:
  !t. t = 1 \/ t = 119571 \/ t = 739695 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267)) t
Proof
  gen_tac >> DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)
  >| [(REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish]),
      (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      (large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])]),
      (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      (large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])])]
QED
Theorem bls12381_cm_check_52437899[local]:
  !t. t = 1 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899)) t
Proof
  gen_tac >> DISCH_THEN SUBST1_TAC >>
  (REWRITE_TAC [bls12381_large_scalar_mult] >>
  cardinality_scalar_normalize >>
  large_scalar_certificate >| [ large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      large_scalar_step,
      cardinality_scalar_finish])
QED

Theorem bls12381_cm_eigenvalue_checks:
  (!t. t = 1 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 11)) t) /\
  (!t. t = 1 \/ t = 4773 \/ t = 5403 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 10177)) t) /\
  (!t. t = 1 \/ t = 119571 \/ t = 739695 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 859267)) t) /\
  (!t. t = 1 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV 52437899)) t)
Proof
  ACCEPT_TAC (LIST_CONJ
    [bls12381_cm_check_11, bls12381_cm_check_10177,
     bls12381_cm_check_859267, bls12381_cm_check_52437899])
QED

Theorem bls12381_cm_no_eigenvalue:
  !q t. prime q /\ q divides bls12381_torsion_factor /\
    t < q /\ t ** 3 MOD q = 1 ==>
    sw_cm_map bls12381_base_field bls12381_cm_beta
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV q)) <>
    bls12381_g1_group.exp
      (bls12381_g1_group.exp bls12381_large_point (bls12381_large_order DIV q)) t
Proof
  metis_tac[bls12381_torsion_cubic_roots, bls12381_cm_eigenvalue_checks]
QED

Theorem bls12381_certificate_finite_group[local]:
  FiniteGroup bls12381_g1_group
Proof
  metis_tac[bls12381_g1_finite_group, FiniteAbelianGroup_def_alt]
QED

Theorem bls12381_certificate_points_member[local]:
  bls12381_large_point IN bls12381_g1_group.carrier /\
  bls12381_second_point IN bls12381_g1_group.carrier
Proof
  simp[bls12381_g1_group_def, bls12381_g1_a_def, bls12381_g1_b_def,
       bls12381_large_point_member, bls12381_second_point_member]
QED

Theorem bls12381_certificate_arithmetic[local]:
  0 < bls12381_large_order /\ 0 < bls12381_torsion_factor /\
  bls12381_torsion_factor divides bls12381_large_order /\
  0 < bls12381_full_cofactor * bls12381_n /\
  2 * bls12381_p + 1 < 2 * (bls12381_full_cofactor * bls12381_n)
Proof
  EVAL_TAC
QED

Definition bls12381_full_certificate_subgroup_def:
  bls12381_full_certificate_subgroup =
    subgroup_cross bls12381_g1_group
      (Generated bls12381_g1_group bls12381_large_point)
      (Generated bls12381_g1_group bls12381_second_point)
End

Theorem bls12381_full_certificate_subgroup:
  Subgroup bls12381_full_certificate_subgroup bls12381_g1_group
Proof
  rw[bls12381_full_certificate_subgroup_def] >>
  irule abelian_subgroup_cross_subgroup >>
  metis_tac[bls12381_g1_finite_group, FiniteAbelianGroup_def,
            bls12381_certificate_finite_group,
            bls12381_certificate_points_member, generated_subgroup]
QED

Theorem bls12381_full_certificate_subgroup_product_card:
  CARD bls12381_full_certificate_subgroup.carrier =
    bls12381_large_order * bls12381_torsion_factor
Proof
  REWRITE_TAC [bls12381_full_certificate_subgroup_def] >>
  irule cm_independent_product_card >>
  SIMP_TAC bool_ss
    [bls12381_certificate_finite_group, bls12381_certificate_points_member,
     bls12381_large_point_order, bls12381_certificate_arithmetic] >>
  qexists_tac `sw_cm_map bls12381_base_field bls12381_cm_beta` >>
  SIMP_TAC bool_ss
    [bls12381_cm_endo, bls12381_cm_third,
     bls12381_second_point_cm_expression, bls12381_cm_no_eigenvalue]
QED

Theorem bls12381_full_certificate_subgroup_card:
  CARD bls12381_full_certificate_subgroup.carrier =
    bls12381_full_cofactor * bls12381_n
Proof
  metis_tac[bls12381_full_certificate_subgroup_product_card,
            bls12381_full_cofactor_factorization]
QED

Theorem bls12381_cardinality_multiple[local]:
  0 < C /\ 0 < N /\ N divides C /\ C < 2 * N ==> C = N
Proof
  strip_tac >>
  `?k. C = k * N` by metis_tac[divides_def] >>
  `0 < k` by (Cases_on `k` >> fs[]) >>
  `k < 2` by
    (spose_not_then strip_assume_tac >>
     `2 <= k` by decide_tac >>
     `2 * N <= k * N` by metis_tac[LESS_MONO_MULT] >>
     decide_tac) >>
  `k = 1` by decide_tac >> fs[]
QED

(* The elementary two-points-per-x bound is already strictly below 2N:
   N = p - x > p. No Hasse theorem or assumed curve-order formula is used. *)
Theorem bls12381_g1_full_cardinality:
  CARD (sw_points bls12381_base_field 0 4) =
    bls12381_full_cofactor * bls12381_n
Proof
  irule bls12381_cardinality_multiple >>
  `ShortWeierstrassCurve bls12381_base_field 0 4` by
    metis_tac[bls12381_g1_curve, bls12381_g1_a_def, bls12381_g1_b_def] >>
  `bls12381_full_cofactor * bls12381_n divides
     CARD (sw_points bls12381_base_field 0 4)` by
    metis_tac[Lagrange_thm, bls12381_full_certificate_subgroup,
              bls12381_full_certificate_subgroup_card,
              bls12381_certificate_finite_group, FiniteGroup_def,
              bls12381_g1_group_def, bls12381_g1_a_def,
              bls12381_g1_b_def, sw_group_carrier] >>
  `CARD (sw_points bls12381_base_field 0 4) <= 2 * bls12381_p + 1` by
    metis_tac[sw_points_card_bound, bls12381_base_field_card,
              bls12381_base_field_finite_field] >>
  `0 < CARD (sw_points bls12381_base_field 0 4)` by
    metis_tac[sw_points_card_positive, bls12381_base_field_finite_field] >>
  metis_tac[bls12381_certificate_arithmetic, LESS_EQ_LESS_TRANS]
QED

Theorem bls12381_g1_full_cofactor:
  CARD (sw_points bls12381_base_field 0 4) DIV bls12381_n =
    76329603384216526031706109802092473003
Proof
  rw[bls12381_g1_full_cardinality, bls12381_full_cofactor_def,
     bls12381_n_def] >> EVAL_TAC
QED

Theorem bls12381_g1_prime_subgroup_not_full:
  bls12381_g1_subgroup.carrier <> sw_points bls12381_base_field 0 4
Proof
  strip_tac >>
  `bls12381_n = bls12381_full_cofactor * bls12381_n` by
    metis_tac[bls12381_g1_subgroup_card, bls12381_g1_full_cardinality] >>
  fs[bls12381_full_cofactor_def, bls12381_n_def]
QED

