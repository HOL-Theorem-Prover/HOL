signature integer_wordLib =
sig
    include Abbrev

    val add_integer_word_compset : computeLib.compset -> unit

    val Cases_on_i2w     : term frag list -> tactic
    val INT_SIZES_CONV   : conv
    val WORD_DECIDE      : conv (* Decision procedure, based on COOPER_PROVE *)

end
