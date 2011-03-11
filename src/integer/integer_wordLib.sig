signature integer_wordLib =
sig
    include Abbrev

    val Cases_on_i2w     : term frag list -> tactic
    val INT_SIZES_CONV   : conv
    val WORD_DECIDE      : conv (* Decision procedure, based on COOPER_PROVE *)

end
