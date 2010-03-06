signature listLib =
sig
  type term = Term.term
  type thm = Thm.thm
  type tactic = Abbrev.tactic
  type conv  = Abbrev.conv

  (* listSimps *)
  val LIST_ss  : simpLib.ssfrag
  val LIST_EQ_ss : simpLib.ssfrag

  val NORM_CONS_APPEND_CONV : conv
  val LIST_EQ_SIMP_CONV : conv

  val list_rws : computeLib.compset -> unit
  val list_compset : unit -> computeLib.compset

  (* rich_listSimps *)
  val RICH_LIST_ss : simpLib.ssfrag

  (* ListConv1 *)
  val LIST_INDUCT : thm * thm -> thm
  val LIST_INDUCT_TAC : tactic
  val SNOC_INDUCT_TAC : tactic
  val EQ_LENGTH_INDUCT_TAC : tactic
  val EQ_LENGTH_SNOC_INDUCT_TAC : tactic
  val new_list_rec_definition : string * term -> thm
  val list_EQ_CONV : conv -> conv
  val LENGTH_CONV : conv
  val APPEND_CONV : conv
  val MAP_CONV : conv -> conv
  val FOLDR_CONV : conv -> conv
  val FOLDL_CONV : conv -> conv
  val list_FOLD_CONV : thm -> conv -> conv
  val SUM_CONV : conv
  val FILTER_CONV : conv -> conv
  val SNOC_CONV : conv
  val REVERSE_CONV : conv
  val FLAT_CONV : conv
  val EL_CONV : conv
  val ELL_CONV : conv
  val MAP2_CONV : conv -> conv
  val ALL_EL_CONV : conv -> conv
  val SOME_EL_CONV : conv -> conv
  val IS_EL_CONV : conv -> conv
  val AND_EL_CONV : conv
  val OR_EL_CONV : conv
  val LAST_CONV : conv
  val BUTLAST_CONV : conv
  val SEG_CONV : conv
  val LASTN_CONV : conv
  val BUTLASTN_CONV : conv
  val BUTFIRSTN_CONV : conv
  val FIRSTN_CONV : conv
  val SCANL_CONV : conv -> conv
  val SCANR_CONV : conv -> conv
  val REPLICATE_CONV : conv
  val GENLIST_CONV : conv -> conv

end
