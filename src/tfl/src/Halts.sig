signature Halts =
sig

  type hol_type = Type.hol_type
  type term     = Term.term
  type conv     = Abbrev.conv
  type tactic   = Abbrev.tactic
  type defn     = Defn.defn

   val prover        : tactic
   val guessR        : defn -> term list
   val try_proof     : defn -> tactic -> term -> defn
   val proveTotal0   : tactic -> defn -> defn 
   val proveTotal    : defn -> defn
   val TC_SIMP_CONV  : conv
end
