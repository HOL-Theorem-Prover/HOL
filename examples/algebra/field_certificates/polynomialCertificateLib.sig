signature polynomialCertificateLib =
sig
  (* The prime theorem is a closed |- prime p, with p a numeral; the polynomial
     is a canonical ascending num list. All candidate arithmetic is rechecked. *)
  (* Bounded addition/multiplication/list predicates only; no abstract inverses. *)
  val ARITH_CONV : Abbrev.conv
  (* Capture once for repeated bounded calculations in a certificate context. *)
  val BOUNDED_CONV : unit -> Abbrev.conv
  (* With prime p and modulus f, prove poly_mod (GF p) a f = b by checking
     a quotient/remainder identity. f must be monic and have positive degree. *)
  val REMAINDER_CONV : Thm.thm -> Term.term -> Abbrev.conv
  (* Prove the remainder of (PolyRing (GF p)).prod.exp a n for literal n,
     using binary powering and checked bounded remainders. *)
  val MODPOW_CONV : Thm.thm -> Term.term -> Abbrev.conv
  (* Return irreducible (PolyRing (GF p)) f for a degree-twelve monic f,
     after checking the degree-4, degree-6 and degree-12 Frobenius tests. *)
  val RABIN12_RULE : Thm.thm -> Term.term -> Thm.thm
  (* Return poly_roots (GF p) f = {} from a checked Frobenius/Bezout
     certificate; failure to find or check that certificate raises an error. *)
  val NO_ROOTS_RULE : Thm.thm -> Term.term -> Thm.thm
end
