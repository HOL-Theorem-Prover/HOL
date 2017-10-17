signature integer_wordLib =
sig
   val add_integer_word_compset : computeLib.compset -> unit
   val Cases_on_i2w : Term.term frag list -> Tactical.tactic
   val INT_SIZES_CONV : Conv.conv
   val INT_WORD_GROUND_CONV : Conv.conv
   val WORD_DECIDE : Conv.conv (* Decision procedure, based on COOPER_PROVE *)
end
