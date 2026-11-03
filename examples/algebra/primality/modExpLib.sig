signature modExpLib =
sig
  (* Normalize certificate subtraction, division, multiplication, less-than,
     and numeral equality. Surrounding Boolean connectives are unchanged. *)
  val NAT_CONV : Abbrev.conv

  (* Closed a ** e MOD n: one complete kernel CV program evaluation, without
     constructing a ** e. Certificate arithmetic in a, e and n is normalized
     first. *)
  val MODPOW_CONV : Abbrev.conv
end
