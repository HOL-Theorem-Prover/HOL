signature SALGen =
sig
 include Abbrev
 val forward_reason : term -> thm
 val certified_gen : thm -> thm
end
