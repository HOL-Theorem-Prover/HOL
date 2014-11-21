signature bitstringLib =
sig
    include Abbrev

    val add_bitstring_compset : computeLib.compset -> unit

    val Cases_on_v2w : term frag list -> tactic

    type bitify_boolify =
        { bitify_def : thm,
          bitify_tm : term,
          mk_bitify : term -> term,
          dest_bitify : term -> term,
          is_bitify : term -> bool,
          boolify_def : thm,
          boolify_tm : term,
          mk_boolify : term -> term,
          dest_boolify : term -> term,
          is_boolify : term -> bool }

    val FIX_CONV : conv
    val FIX_v2w_CONV : conv
    val v2n_CONV : conv
    val v2w_n2w_CONV : conv
    val n2w_v2w_CONV : conv
    val v2w_eq_CONV : conv
    val word_eq_CONV : conv
    val extract_v2w_CONV : conv
    val word_bit_CONV : conv

    val bitify_num : int -> Arbnum.num -> term list

    val bitify_boolify : int -> bitify_boolify
end
