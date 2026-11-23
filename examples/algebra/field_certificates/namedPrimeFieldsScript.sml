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

Theorem prime_field_properties[local]:
  !p. prime p ==>
    Field (GF p) /\ FiniteField (GF p) /\
    CARD (GF p).carrier = p /\ char (GF p) = p
Proof
  simp[GF_field, GF_finite_field, GF_card, GF_prime_char]
QED

fun named_field_properties definition prime =
  case CONJUNCTS (REWRITE_RULE [GSYM definition]
    (MATCH_MP prime_field_properties prime)) of
    [field,finite,card,characteristic] => (field,finite,card,characteristic)
  | _ => raise Fail "Expected four prime-field properties";

Definition secp256k1_base_field_def:
  secp256k1_base_field = GF secp256k1_p
End

local
  val (field,finite,card,characteristic) =
    named_field_properties secp256k1_base_field_def secp256k1_p_prime
in
Theorem secp256k1_base_field_field = field;
Theorem secp256k1_base_field_finite_field = finite;
Theorem secp256k1_base_field_card = card;
Theorem secp256k1_base_field_char = characteristic;
end

Definition secp256k1_scalar_field_def:
  secp256k1_scalar_field = GF secp256k1_n
End

local
  val (field,finite,card,characteristic) =
    named_field_properties secp256k1_scalar_field_def secp256k1_n_prime
in
Theorem secp256k1_scalar_field_field = field;
Theorem secp256k1_scalar_field_finite_field = finite;
Theorem secp256k1_scalar_field_card = card;
Theorem secp256k1_scalar_field_char = characteristic;
end

Definition p256_base_field_def:
  p256_base_field = GF p256_p
End

local
  val (field,finite,card,characteristic) =
    named_field_properties p256_base_field_def p256_p_prime
in
Theorem p256_base_field_field = field;
Theorem p256_base_field_finite_field = finite;
Theorem p256_base_field_card = card;
Theorem p256_base_field_char = characteristic;
end

Definition p256_scalar_field_def:
  p256_scalar_field = GF p256_n
End

local
  val (field,finite,card,characteristic) =
    named_field_properties p256_scalar_field_def p256_n_prime
in
Theorem p256_scalar_field_field = field;
Theorem p256_scalar_field_finite_field = finite;
Theorem p256_scalar_field_card = card;
Theorem p256_scalar_field_char = characteristic;
end

Definition bn254_base_field_def:
  bn254_base_field = GF bn254_p
End

local
  val (field,finite,card,characteristic) =
    named_field_properties bn254_base_field_def bn254_p_prime
in
Theorem bn254_base_field_field = field;
Theorem bn254_base_field_finite_field = finite;
Theorem bn254_base_field_card = card;
Theorem bn254_base_field_char = characteristic;
end

Definition bn254_scalar_field_def:
  bn254_scalar_field = GF bn254_n
End

local
  val (field,finite,card,characteristic) =
    named_field_properties bn254_scalar_field_def bn254_n_prime
in
Theorem bn254_scalar_field_field = field;
Theorem bn254_scalar_field_finite_field = finite;
Theorem bn254_scalar_field_card = card;
Theorem bn254_scalar_field_char = characteristic;
end

Definition bls12381_base_field_def:
  bls12381_base_field = GF bls12381_p
End

local
  val (field,finite,card,characteristic) =
    named_field_properties bls12381_base_field_def bls12381_p_prime
in
Theorem bls12381_base_field_field = field;
Theorem bls12381_base_field_finite_field = finite;
Theorem bls12381_base_field_card = card;
Theorem bls12381_base_field_char = characteristic;
end

Definition bls12381_scalar_field_def:
  bls12381_scalar_field = GF bls12381_n
End

local
  val (field,finite,card,characteristic) =
    named_field_properties bls12381_scalar_field_def bls12381_n_prime
in
Theorem bls12381_scalar_field_field = field;
Theorem bls12381_scalar_field_finite_field = finite;
Theorem bls12381_scalar_field_card = card;
Theorem bls12381_scalar_field_char = characteristic;
end

