signature wordsLib =
sig
    include Abbrev

    val words_compset : unit -> computeLib.compset

    val SIZES_ss      : simpLib.ssfrag

    val mk_index_type : int -> unit
    val mk_word_type  : int -> unit

    val WORDS_CONV    : conv
    val WORDS_RULE    : rule
    val WORDS_TAC     : tactic

    val Cases_on_word : term frag list -> tactic
    val Cases_word    : tactic
end
