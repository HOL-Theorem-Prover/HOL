open simpLib optionTheory

val OPTION_ss =
  rewrites (TypeBase.simpls_of (valOf (TypeBase.read "option")) @
            [option_APPLY_DEF, option_JOIN_THM, THE_DEF]);
