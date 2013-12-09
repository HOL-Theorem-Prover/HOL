signature tripleLib =
sig
   val CODE_CONV: Conv.conv -> Conv.conv
   val POST_CONV: Conv.conv -> Conv.conv
   val PRE_CONV: Conv.conv -> Conv.conv

   val spec_to_triple_rule: Term.term * Thm.thm * Thm.thm -> Thm.thm -> Thm.thm
end
