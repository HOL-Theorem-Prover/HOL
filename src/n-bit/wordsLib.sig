signature wordsLib =
sig
    include Abbrev

    val words_compset     : unit -> computeLib.compset

    val SIZES_ss          : simpLib.ssfrag
    val BIT_ss            : simpLib.ssfrag

    val WORD_ARITH_ss     : simpLib.ssfrag
    val WORD_LOGIC_ss     : simpLib.ssfrag
    val WORD_SHIFT_ss     : simpLib.ssfrag
    val WORD_ARITH_EQ_ss  : simpLib.ssfrag
    val WORD_BIT_EQ_ss    : simpLib.ssfrag
    val WORD_EXTRACT_ss   : simpLib.ssfrag
    val WORD_MUL_LSL_ss   : simpLib.ssfrag

    val WORD_ss           : simpLib.ssfrag

    val SIZES_CONV        : conv

    val WORD_ARITH_CONV   : conv
    val WORD_LOGIC_CONV   : conv
    val WORD_MUL_LSL_CONV : conv
    val WORD_CONV         : conv
    val WORD_BIT_EQ_CONV  : conv

    val WORD_DP           : conv -> conv
    val WORD_DECIDE       : conv
    val WORD_DECIDE_TAC   : tactic

    val WORD_EVAL_CONV    : conv
    val WORD_EVAL_RULE    : rule
    val WORD_EVAL_TAC     : tactic

    val WORDS_EMIT_RULE   : rule

    val Cases_on_word     : term frag list -> tactic
    val Cases_word        : tactic
    val Induct_word       : tactic

    val mk_word_size      : int -> unit

    val prefer_word       : unit -> unit
    val deprecate_word    : unit -> unit

    val output_words_as     : (int * Arbnum.num -> StringCvt.radix) -> unit
    val output_words_as_bin : unit -> unit
    val output_words_as_oct : unit -> unit
    val output_words_as_hex : unit -> unit
    val output_words_as_dec : unit -> unit

    val notify_word_length_guesses : bool ref
    val guess_word_lengths         : term -> term
    val guess_lengths              : unit -> unit
    val dont_guess_lengths         : unit -> unit
end
