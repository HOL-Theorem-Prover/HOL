signature ExistsFuns =
sig
type term = Term.term;
type thm = Thm.thm;

    val EXISTS_FROM_EXISTS_RULE : {exists_thm:thm, forall_imp_thm:thm} -> thm
    val GEN_EXISTS_FROM_EXISTS_RULE : {coercion_funs:term list, exists_thm:thm,
                                       forall_imp_thm:thm}
                                      -> thm
end;
