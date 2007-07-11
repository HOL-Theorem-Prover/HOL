signature SALGen =
sig
 include Abbrev
 val VarType : hol_type ref
 val printSAL : term -> unit
 val certified_gen : thm -> {code : term, thm : thm}
end
