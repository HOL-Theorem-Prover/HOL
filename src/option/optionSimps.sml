open simpLib optionTheory

val OPTION_ss =
  rewrites (TypeBase.simpls_of (valOf (TypeBase.read "option")) @
            [option_APPLY_DEF, THE_DEF]);
