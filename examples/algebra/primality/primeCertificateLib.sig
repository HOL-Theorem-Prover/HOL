signature primeCertificateLib =
sig
  (* Decimal n, Lucas witness, and complete prime factorisation of n-1.
     Candidate and factor keys are parsed once as arbitrary-precision numbers,
     so leading zeroes do not affect lookup. The supplied data are untrusted
     and all equations are kernel checked. *)
  type certificate = string * string * (string * int) list
  (* Convert prime <numeral> to T. Include recursive certificates for all
     factors except the built-in primes 2 and 3. Successful proofs are cached
     per converter; absent certificates or failed checks do not prove a result. *)
  val PRIME_CERT_CONV : certificate list -> Abbrev.conv
end