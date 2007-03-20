signature wordsLib =
sig
    include Abbrev

    val words_compset : unit -> computeLib.compset

    val SIZES_ss      : simpLib.ssfrag

    val mk_word_size  : int -> unit

    val WORDS_CONV    : conv
    val WORDS_RULE    : rule
    val WORDS_TAC     : tactic

    val WORDS_EMIT_RULE : rule

    val Cases_on_word : term frag list -> tactic
    val Cases_word    : tactic

    val pp_word       : (hol_type -> StringCvt.radix) -> unit

    val pp_word_bin   : unit -> unit
    val pp_word_oct   : unit -> unit
    val pp_word_hex   : unit -> unit
    val pp_word_dec   : unit -> term_pp_types.userprinter option

    val notify_word_length_guesses : bool ref
    val guess_word_lengths         : term -> term
    val guess_lengths              : unit -> unit
end
