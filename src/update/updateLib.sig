signature updateLib =
sig
    include Abbrev

    val strip_list_update        : term -> (term * term) list

    val UPDATE_APPLY_CONV       : conv -> conv

    val LIST_UPDATE_INTRO_CONV  : conv
    val LIST_UPDATE_ELIM_CONV   : conv

    val OVERRIDE_UPDATES_CONV   : hol_type -> conv -> conv
    val SORT_UPDATES_CONV       : term -> computeLib.compset -> conv -> conv
    val SORT_UPDATES_MAPTO_CONV : term -> term -> computeLib.compset -> conv ->
                                  conv

    val SORT_NUM_UPDATES_CONV   : conv
    val SORT_WORD_UPDATES_CONV  : hol_type -> conv
    val SORT_ENUM_UPDATES_CONV  : hol_type -> conv
end
