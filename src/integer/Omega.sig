signature Omega =
sig

  include Abbrev
  val OMEGA_CONV : conv
  val OMEGA_PROVE : conv
  val OMEGA_TAC : tactic

end;
