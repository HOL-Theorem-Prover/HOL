signature updateLib =
sig
    include Abbrev

    val dest_list_update        : term -> (term * term) list

    val LIST_UPDATE_INTRO_CONV  : conv
    val LIST_UPDATE_ELIM_CONV   : conv

    val OVERRIDE_UPDATES_CONV   : hol_type -> thm list -> conv
    val SORT_UPDATES_CONV       : term -> thm list -> conv
    val SORT_UPDATES_MAPTO_CONV : term -> term -> thm list -> conv

    val SORT_NUM_UPDATES_CONV   : conv
    val SORT_WORD_UPDATES_CONV  : hol_type -> conv
    val SORT_ENUM_UPDATES_CONV  : hol_type -> conv

end
