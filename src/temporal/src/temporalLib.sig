signature temporalLib = 
  sig
    val smv_call    : string ref
    val smv_path    : string ref
    val smv_tmp_dir : string ref

    type term = Term.term
    type thm = Thm.thm
    type conv = Abbrev.conv

    val TEMP_NORMALIZE_CONV : term -> thm
    val TEMP_DEFS_CONV : term -> thm
    val LTL2OMEGA_CONV : term -> thm
    val LTL_CONV : conv
    val UNSAFE_TEMP_DEFS_CONV : term -> thm
    val UNSAFE_LTL2OMEGA_CONV : term -> thm
    val UNSAFE_LTL_CONV : conv
    val SMV_AUTOMATON_CONV : term -> thm
    val SMV_RUN_FILE : string -> bool
    val SMV_RUN : string -> bool
  end
