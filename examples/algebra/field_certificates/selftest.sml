open HolKernel boolLib testutils;
open polynomialCertificateTheory fieldInstancesTheory polyModuloRingTheory
     polyRingTheory;

val _ = new_theory "scratch";
val failures = ref 0;
val _ = diemode := Remember failures;

fun conversion_test name conv tm expected =
  let
    fun check th = null (hyp th) andalso
      aconv (concl th) (mk_eq (tm,expected))
  in
    tprint name;
    require_msg (check_result check) thm_to_string conv tm
  end;

fun reject name conv tm =
  (tprint name;
   shouldfail
     {testfn = conv, printresult = thm_to_string,
      printarg = term_to_string,
      checkexn = fn HOL_ERR _ => true | _ => false} tm);

val _ = conversion_test "Shared modular power" certificateComputeLib.MODPOW_CONV
  ``2 ** 1000 MOD 17`` ``1n``;
val _ = conversion_test "Normalize modular power arguments"
  certificateComputeLib.MODPOW_CONV ``(1 + 1) ** (3 + 2) MOD (10 + 7)`` ``15n``;
val _ = conversion_test "Modulus zero follows HOL arithmetic"
  certificateComputeLib.MODPOW_CONV ``2 ** 5 MOD 0`` ``32n``;
val _ = conversion_test "Zero exponent at modulus one"
  certificateComputeLib.MODPOW_CONV ``2 ** 0 MOD 1`` ``0n``;
val _ = reject "Reject non-modular power" certificateComputeLib.MODPOW_CONV
  ``2 ** 5``;
val _ = reject "Reject open modular power" certificateComputeLib.MODPOW_CONV
  ``2 ** n MOD 17``;

val prime = dividesTheory.PRIME_3;
val modulus = ``[1n;0;1]``;
val remainder = polynomialCertificateLib.REMAINDER_CONV prime modulus;
val power = polynomialCertificateLib.MODPOW_CONV prime modulus;
val quotient = pairingFieldCertificateLib.QUOTIENT_CONV prime modulus;

val _ = conversion_test "Checked polynomial remainder" remainder
  ``poly_mod (GF 3) [2n;0;1] [1n;0;1]`` ``[1n]``;
val _ = conversion_test "Checked polynomial modular power" power
  ``poly_mod (GF 3) ((PolyRing (GF 3)).prod.exp [0n;1] 4) [1n;0;1]``
  ``[1n]``;
val _ = conversion_test "Checked quotient addition" quotient
  ``(PolyModRing (GF 3) [1n;0;1]).sum.op [2n;1] [2n;2]`` ``[1n]``;
val _ = conversion_test "Checked quotient zero" quotient
  ``(PolyModRing (GF 3) [1n;0;1]).sum.id`` ``[]:num list``;
val _ = reject "Reject a different coefficient field" remainder
  ``poly_mod (GF 5) [2n;0;1] [1n;0;1]``;
val _ = reject "Reject a different modulus" remainder
  ``poly_mod (GF 3) [2n;0;1] [2n;0;1]``;
val _ = reject "Reject non-polynomial input" remainder ``3n``;

val _ = reject "Reject a hypothetical primality theorem"
  (fn tm => polynomialCertificateLib.REMAINDER_CONV
    (ASSUME (concl prime)) modulus tm)
  ``poly_mod (GF 3) [2n;0;1] [1n;0;1]``;
val _ = reject "Reject a non-primality theorem"
  (fn tm => polynomialCertificateLib.REMAINDER_CONV TRUTH modulus tm)
  ``poly_mod (GF 3) [2n;0;1] [1n;0;1]``;
val _ = reject "Reject a hypothetical quotient premise"
  (fn tm => pairingFieldCertificateLib.QUOTIENT_CONV
    (ASSUME (concl prime)) modulus tm)
  ``(PolyModRing (GF 3) [1n;0;1]).sum.id``;
val _ = reject "Reject a constant modulus"
  (fn tm => polynomialCertificateLib.REMAINDER_CONV prime ``[1n]`` tm)
  ``poly_mod (GF 3) [2n;0;1] [1n]``;
val _ = reject "Reject a noncanonical modulus"
  (fn tm => polynomialCertificateLib.REMAINDER_CONV prime ``[1n;0;1;0]`` tm)
  ``poly_mod (GF 3) [2n;0;1] [1n;0;1;0]``;

val _ = exit_count0 failures;
