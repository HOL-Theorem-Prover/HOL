(* Primality proofs copied from hol4_algebra/elliptic/instances/prime_field/bls12381CardinalityScript.sml. *)
Theory bls12381CofactorPrimes
Libs
  primeCertificateLib

val cofactor_prime_certificates : primeCertificateLib.certificate list = [
  ("5","2",[("2",2)]),
  ("7","3",[("2",1),("3",1)]),
  ("11","2",[("2",1),("5",1)]),
  ("13","2",[("2",2),("3",1)]),
  ("17","3",[("2",4)]),
  ("43","3",[("2",1),("3",1),("7",1)]),
  ("53","2",[("2",2),("13",1)]),
  ("97","5",[("2",5),("3",1)]),
  ("449","3",[("2",6),("7",1)]),
  ("10177","7",[("2",6),("3",1),("53",1)]),
  ("47737","5",[("2",3),("3",3),("13",1),("17",1)]),
  ("609743","5",[("2",1),("7",1),("97",1),("449",1)]),
  ("859267","2",[("2",1),("3",2),("47737",1)]),
  ("52437899","2",[("2",1),("43",1),("609743",1)])
];

val cofactor_prime_conv =
  primeCertificateLib.PRIME_CERT_CONV cofactor_prime_certificates;

Theorem bls12381_cofactor_primes:
  prime 11 /\ prime 10177 /\ prime 859267 /\ prime 52437899
Proof
  rpt conj_tac >> CONV_TAC cofactor_prime_conv
QED
