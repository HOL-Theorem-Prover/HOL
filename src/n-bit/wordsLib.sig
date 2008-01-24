signature wordsLib =
sig
    include Abbrev

    val words_compset     : unit -> computeLib.compset

    val SIZES_ss          : simpLib.ssfrag
    val BIT_ss            : simpLib.ssfrag

    val WORD_GROUND_ss    : simpLib.ssfrag
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
    val WORD_EVAL_CONV    : conv

    val WORD_DP           : conv -> conv
    val WORD_DECIDE       : conv

    val mk_word_size      : int -> unit

    val WORD_EVAL_RULE    : rule
    val WORD_EVAL_TAC     : tactic

    val WORDS_EMIT_RULE   : rule

    val Cases_on_word     : term frag list -> tactic
    val Cases_word        : tactic

    val pp_word           : (hol_type -> StringCvt.radix) -> unit

    val pp_word_bin       : unit -> unit
    val pp_word_oct       : unit -> unit
    val pp_word_hex       : unit -> unit
    val pp_word_dec       : unit -> term_pp_types.userprinter option

    val prefer_word       : unit -> unit
    val deprecate_word    : unit -> unit

    val notify_word_length_guesses : bool ref
    val guess_word_lengths         : term -> term
    val guess_lengths              : unit -> unit

(*
    [SIZES_ss] evaluates dimindex(:N), dimword(:N) etc.

    [BIT_ss] converts BIT n N to set membership e.g.
             ``BIT n 3`` to ``n IN {0; 1}``

    [WORD_GROUND_ss] does some ground evaluation

    [WORD_ARITH_ss] AC simplification for *, +, - etc.

    [WORD_LOGIC_ss] AC simplification for &&, !!, ~ etc.

    [WORD_SHIFT_ss] is a basic simpset for word shifts

    [WORD_ss] contains all of the above simpsets

    [WORD_ARITH_EQ_ss] simplifies (a = b) to (a - b = 0w)

    [WORD_BIT_EQ_ss] converts word equality to bitwise equality e.g.
       ``a !! b << 2 = c:word3`` goes to
       ``(a %% 2 \/ b %% 0 = c %% 2) /\ (a %% 1 = c %% 1) /\
         (a %% 0 = c %% 0)``

    [WORD_EXTRACT_ss] is a fairly aggressive simpset for bit extractions
       ><, <>, --, w2w, sw2w, >>>, >>, #>>, @@ etc.

    [WORD_MUL_LSL_ss] converts products to left shifts e.g. ``4w * a`` goes
       to ``a << 2`` and ``5w * a`` to ``a << 2 + a``.

    [WORD_ARITH_CONV] is bases on WORD_ARITH_ss and WORD_ARITH_EQ_ss

    [WORD_LOGIC_CONV] is bases on WORD_LOGIC_ss

    [WORD_CONV] is based on WORD_ss

    [WORD_DECIDE] is a decision procedure based on DECIDE

    [WORDS_EMIT_RULE] apply to word theorems when exporting with EmitML
*)

end
