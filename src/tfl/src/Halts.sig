signature Halts =
sig

  type hol_type = Type.hol_type
  type term     = Term.term
  type tactic   = Abbrev.tactic
  type defn     = Defn.defn

   val guess_termination_relation : hol_type -> term list -> term list
   val prover : tactic
   val proveTotal0 : tactic -> defn -> defn
   val proveTotal  : defn -> defn
end
