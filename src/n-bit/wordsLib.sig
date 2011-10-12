signature wordsLib =
sig
    include Abbrev

    val words_compset       : unit -> computeLib.compset

    val SIZES_ss            : simpLib.ssfrag
    val BIT_ss              : simpLib.ssfrag
    val BITS_INTRO_ss       : simpLib.ssfrag

    val WORD_ARITH_ss       : simpLib.ssfrag
    val WORD_LOGIC_ss       : simpLib.ssfrag
    val WORD_SUB_ss         : simpLib.ssfrag
    val WORD_SHIFT_ss       : simpLib.ssfrag
    val WORD_ARITH_EQ_ss    : simpLib.ssfrag
    val WORD_CANCEL_ss      : simpLib.ssfrag
    val WORD_BIT_EQ_ss      : simpLib.ssfrag
    val WORD_EXTRACT_ss     : simpLib.ssfrag
    val WORD_MUL_LSL_ss     : simpLib.ssfrag

    val WORD_ss             : simpLib.ssfrag

    val SIZES_CONV          : conv
    val word_EQ_CONV        : conv

    val BITS_INTRO_CONV     : conv
    val WORD_ARITH_CONV     : conv
    val WORD_CANCEL_CONV    : conv
    val WORD_LOGIC_CONV     : conv
    val WORD_SUB_CONV       : conv
    val WORD_MUL_LSL_CONV   : conv
    val WORD_DIV_LSR_CONV   : conv
    val WORD_MOD_BITS_CONV  : conv
    val WORD_CONV           : conv
    val WORD_BIT_EQ_CONV    : conv
    val EXTEND_EXTRACT_CONV : conv
    val EXPAND_REDUCE_CONV  : conv

    val n2w_INTRO_TAC       : int -> tactic

    val WORD_DP             : conv -> conv -> conv
    val WORD_ARITH_PROVE    : conv
    val WORD_DECIDE         : conv
    val WORD_DECIDE_TAC     : tactic

    val WORD_EVAL_CONV      : conv
    val WORD_EVAL_RULE      : rule
    val WORD_EVAL_TAC       : tactic

    val Induct_word         : tactic
    val Cases_word          : tactic
    val Cases_word_value    : tactic
    val Cases_on_word       : term frag list -> tactic
    val Cases_on_word_value : term frag list -> tactic

    val mk_word_size        : int -> unit
    val dest_word_literal   : term -> Arbnum.num

    val prefer_word         : unit -> unit
    val deprecate_word      : unit -> unit

    val word_pp_mode        : int ref
    val output_words_as     : (int * Arbnum.num -> StringCvt.radix) -> unit
    val output_words_as_bin : unit -> unit
    val output_words_as_oct : unit -> unit
    val output_words_as_hex : unit -> unit
    val output_words_as_dec : unit -> unit
    val remove_word_printer : unit -> unit

    val add_word_cast_printer       : unit -> unit
    val remove_word_cast_printer    : unit -> unit

    val guessing_word_lengths       : bool ref
    val notify_on_word_length_guess : bool ref
    val inst_word_lengths           : term -> term
    val guess_lengths               : unit -> unit
end
