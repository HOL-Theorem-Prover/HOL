signature pairingFieldCertificateLib =
sig
  include Abbrev
  (* PolyModRing (GF p) f with a closed proof of prime p and a canonical,
     nonconstant monic literal f. Addition, multiplication, powers and
     polynomial substitution remainders are checked by kernel certificates;
     abstract quotient inverses are deliberately not evaluated. *)
  val QUOTIENT_CONV : thm -> term -> conv
end
