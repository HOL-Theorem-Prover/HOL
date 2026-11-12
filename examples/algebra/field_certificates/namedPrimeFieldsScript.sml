(* -------------------------------------------------------------------------
   Named prime fields

   Documentation
   Named GF field records for the base and scalar moduli of secp256k1,
   P-256, BN254 and BLS12-381, imported from namedPrimes. Elements of GF p
   are natural-number residues less than p; scalar fields use n instead.

   Public interface
   - namedPrimes supplies the modulus constants and their primality proofs.
   - For each prefix secp256k1, p256, bn254, bls12381, the definitions
     *_base_field_def and *_scalar_field_def name the records; theorems
     ending in _field, _finite_field, _card and _char describe them.

   The primality certificates are checked in primality/examples/namedPrimes;
   this theory neither duplicates their data nor re-exports their theorems.
   Naming a scalar field does not itself prove a curve's order.
   ------------------------------------------------------------------------- *)

Theory namedPrimeFields
Ancestors
  namedPrimes fieldInstances divides

Definition secp256k1_base_field_def:
  secp256k1_base_field = GF secp256k1_p
End

Theorem secp256k1_base_field_field:
  Field secp256k1_base_field
Proof
  simp[secp256k1_base_field_def, GF_field, secp256k1_p_prime]
QED

Theorem secp256k1_base_field_finite_field:
  FiniteField secp256k1_base_field
Proof
  simp[secp256k1_base_field_def, GF_finite_field, secp256k1_p_prime]
QED

Theorem secp256k1_base_field_card:
  CARD secp256k1_base_field.carrier = secp256k1_p
Proof
  simp[secp256k1_base_field_def, GF_card]
QED

Theorem secp256k1_base_field_char:
  char secp256k1_base_field = secp256k1_p
Proof
  simp[secp256k1_base_field_def, GF_char, ONE_LT_PRIME, secp256k1_p_prime]
QED

Definition secp256k1_scalar_field_def:
  secp256k1_scalar_field = GF secp256k1_n
End

Theorem secp256k1_scalar_field_field:
  Field secp256k1_scalar_field
Proof
  simp[secp256k1_scalar_field_def, GF_field, secp256k1_n_prime]
QED

Theorem secp256k1_scalar_field_finite_field:
  FiniteField secp256k1_scalar_field
Proof
  simp[secp256k1_scalar_field_def, GF_finite_field, secp256k1_n_prime]
QED

Theorem secp256k1_scalar_field_card:
  CARD secp256k1_scalar_field.carrier = secp256k1_n
Proof
  simp[secp256k1_scalar_field_def, GF_card]
QED

Theorem secp256k1_scalar_field_char:
  char secp256k1_scalar_field = secp256k1_n
Proof
  simp[secp256k1_scalar_field_def, GF_char, ONE_LT_PRIME, secp256k1_n_prime]
QED

Definition p256_base_field_def:
  p256_base_field = GF p256_p
End

Theorem p256_base_field_field:
  Field p256_base_field
Proof
  simp[p256_base_field_def, GF_field, p256_p_prime]
QED

Theorem p256_base_field_finite_field:
  FiniteField p256_base_field
Proof
  simp[p256_base_field_def, GF_finite_field, p256_p_prime]
QED

Theorem p256_base_field_card:
  CARD p256_base_field.carrier = p256_p
Proof
  simp[p256_base_field_def, GF_card]
QED

Theorem p256_base_field_char:
  char p256_base_field = p256_p
Proof
  simp[p256_base_field_def, GF_char, ONE_LT_PRIME, p256_p_prime]
QED

Definition p256_scalar_field_def:
  p256_scalar_field = GF p256_n
End

Theorem p256_scalar_field_field:
  Field p256_scalar_field
Proof
  simp[p256_scalar_field_def, GF_field, p256_n_prime]
QED

Theorem p256_scalar_field_finite_field:
  FiniteField p256_scalar_field
Proof
  simp[p256_scalar_field_def, GF_finite_field, p256_n_prime]
QED

Theorem p256_scalar_field_card:
  CARD p256_scalar_field.carrier = p256_n
Proof
  simp[p256_scalar_field_def, GF_card]
QED

Theorem p256_scalar_field_char:
  char p256_scalar_field = p256_n
Proof
  simp[p256_scalar_field_def, GF_char, ONE_LT_PRIME, p256_n_prime]
QED

Definition bn254_base_field_def:
  bn254_base_field = GF bn254_p
End

Theorem bn254_base_field_field:
  Field bn254_base_field
Proof
  simp[bn254_base_field_def, GF_field, bn254_p_prime]
QED

Theorem bn254_base_field_finite_field:
  FiniteField bn254_base_field
Proof
  simp[bn254_base_field_def, GF_finite_field, bn254_p_prime]
QED

Theorem bn254_base_field_card:
  CARD bn254_base_field.carrier = bn254_p
Proof
  simp[bn254_base_field_def, GF_card]
QED

Theorem bn254_base_field_char:
  char bn254_base_field = bn254_p
Proof
  simp[bn254_base_field_def, GF_char, ONE_LT_PRIME, bn254_p_prime]
QED

Definition bn254_scalar_field_def:
  bn254_scalar_field = GF bn254_n
End

Theorem bn254_scalar_field_field:
  Field bn254_scalar_field
Proof
  simp[bn254_scalar_field_def, GF_field, bn254_n_prime]
QED

Theorem bn254_scalar_field_finite_field:
  FiniteField bn254_scalar_field
Proof
  simp[bn254_scalar_field_def, GF_finite_field, bn254_n_prime]
QED

Theorem bn254_scalar_field_card:
  CARD bn254_scalar_field.carrier = bn254_n
Proof
  simp[bn254_scalar_field_def, GF_card]
QED

Theorem bn254_scalar_field_char:
  char bn254_scalar_field = bn254_n
Proof
  simp[bn254_scalar_field_def, GF_char, ONE_LT_PRIME, bn254_n_prime]
QED

Definition bls12381_base_field_def:
  bls12381_base_field = GF bls12381_p
End

Theorem bls12381_base_field_field:
  Field bls12381_base_field
Proof
  simp[bls12381_base_field_def, GF_field, bls12381_p_prime]
QED

Theorem bls12381_base_field_finite_field:
  FiniteField bls12381_base_field
Proof
  simp[bls12381_base_field_def, GF_finite_field, bls12381_p_prime]
QED

Theorem bls12381_base_field_card:
  CARD bls12381_base_field.carrier = bls12381_p
Proof
  simp[bls12381_base_field_def, GF_card]
QED

Theorem bls12381_base_field_char:
  char bls12381_base_field = bls12381_p
Proof
  simp[bls12381_base_field_def, GF_char, ONE_LT_PRIME, bls12381_p_prime]
QED

Definition bls12381_scalar_field_def:
  bls12381_scalar_field = GF bls12381_n
End

Theorem bls12381_scalar_field_field:
  Field bls12381_scalar_field
Proof
  simp[bls12381_scalar_field_def, GF_field, bls12381_n_prime]
QED

Theorem bls12381_scalar_field_finite_field:
  FiniteField bls12381_scalar_field
Proof
  simp[bls12381_scalar_field_def, GF_finite_field, bls12381_n_prime]
QED

Theorem bls12381_scalar_field_card:
  CARD bls12381_scalar_field.carrier = bls12381_n
Proof
  simp[bls12381_scalar_field_def, GF_card]
QED

Theorem bls12381_scalar_field_char:
  char bls12381_scalar_field = bls12381_n
Proof
  simp[bls12381_scalar_field_def, GF_char, ONE_LT_PRIME, bls12381_n_prime]
QED

