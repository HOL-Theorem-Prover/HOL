(* ===================================================================== *)
(* FILE          : unwindLib.sig                                         *)
(* DESCRIPTION   : Signature for a library to manipulate existential and *)
(*                 universal quantifiers in goals, terms, etc. Useful    *)
(*                 for unravelling hardware device descriptions.         *)
(*                                                                       *)
(* ===================================================================== *)

signature unwindLib =
sig
   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv

  val CONJ_FORALL_CONV :conv
  val CONJ_FORALL_ONCE_CONV :conv
  val CONJ_FORALL_RIGHT_RULE :thm -> thm
  val DEPTH_EXISTS_CONV :conv -> conv
  val DEPTH_FORALL_CONV :conv -> conv
  val EXISTS_DEL1_CONV :conv
  val EXISTS_DEL_CONV :conv
  val EXISTS_EQN_CONV :conv
  val EXPAND_ALL_BUT_CONV :string list -> thm list -> conv
  val EXPAND_ALL_BUT_RIGHT_RULE :string list -> thm list -> thm -> thm
  val EXPAND_AUTO_CONV :thm list -> conv
  val EXPAND_AUTO_RIGHT_RULE :thm list -> thm -> thm
  val FLATTEN_CONJ_CONV :conv
  val FORALL_CONJ_CONV :conv
  val FORALL_CONJ_ONCE_CONV :conv
  val FORALL_CONJ_RIGHT_RULE :thm -> thm
  val PRUNE_CONV :conv
  val PRUNE_ONCE_CONV :conv
  val PRUNE_ONE_CONV :string -> conv
  val PRUNE_RIGHT_RULE :thm -> thm
  val PRUNE_SOME_CONV :string list -> conv
  val PRUNE_SOME_RIGHT_RULE :string list -> thm -> thm
  val UNFOLD_CONV :thm list -> conv
  val UNFOLD_RIGHT_RULE :thm list -> thm -> thm
  val UNWIND_ALL_BUT_CONV :string list -> conv
  val UNWIND_ALL_BUT_RIGHT_RULE :string list -> thm -> thm
  val UNWIND_AUTO_CONV :conv
  val UNWIND_AUTO_RIGHT_RULE :thm -> thm
  val UNWIND_CONV :(term -> bool) -> conv
  val UNWIND_ONCE_CONV :(term -> bool) -> conv
  val line_name :term -> string
  val line_var :term -> term
end
