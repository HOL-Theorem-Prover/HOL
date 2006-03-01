signature wordsLib =
sig
    include Abbrev

    val words_compset : unit -> computeLib.compset

    val SIZES_ss      : simpLib.ssfrag

    val mk_index_size : int -> unit
    val mk_word_size  : int -> unit

    val WORDS_CONV    : conv
    val WORDS_RULE    : rule
    val WORDS_TAC     : tactic

    val Cases_on_word : term frag list -> tactic
    val Cases_word    : tactic

    val pp_word       : (hol_type -> StringCvt.radix) -> unit

    val pp_word_bin   : unit -> unit
    val pp_word_oct   : unit -> unit
    val pp_word_hex   : unit -> unit
    val pp_word_dec   : unit -> term_pp_types.userprinter option
end
