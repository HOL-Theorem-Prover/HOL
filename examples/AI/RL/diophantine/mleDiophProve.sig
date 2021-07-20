signature mleDiophProve =
sig

  include Abbrev

  val LESS16 : thm
  val MOD16 : thm
  val PRED16 : thm
  val PQSET16 : thm
  val DIOPH_PROVE : term * int list -> thm

end
