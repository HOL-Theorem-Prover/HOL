signature ListConv2 =
sig
  type term = Term.term;
  type thm = Thm.thm;
  type conv = Abbrev.conv;

  val LIST_CONV : conv
  val X_LIST_CONV : {Aux_thms:thm list, Fold_thms:thm list} -> conv
  val PURE_LIST_CONV : {Aux_thms:thm list, Fold_thms:thm list} -> conv
  val set_list_thm_database : {Aux_thms:thm list, Fold_thms:thm list} -> unit
  val list_thm_database : unit -> {Aux_thms:thm list, Fold_thms:thm list}
end;

