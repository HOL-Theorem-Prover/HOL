signature cv_transLib =
sig
  include Abbrev

  val cv_trans          : thm -> unit
  val cv_trans_pre      : thm -> thm
  val cv_trans_pre_rec  : thm -> tactic -> thm
  val cv_trans_rec      : thm -> tactic -> unit

  val cv_auto_trans          : thm -> unit
  val cv_auto_trans_pre      : thm -> thm
  val cv_auto_trans_pre_rec  : thm -> tactic -> thm
  val cv_auto_trans_rec      : thm -> tactic -> unit

  (* The conv should evaluate `from <deep_embedding>` *)
  val cv_trans_deep_embedding : conv -> thm -> unit

  datatype pat = Raw
               | Eval of conv
               | Name of string
               | Tuple of pat list
               | Some of pat;

  val cv_eqs_for  : term -> thm list
  val cv_eval     : term -> thm
  val cv_eval_raw : term -> thm
  val cv_eval_pat : pat -> term -> thm

  val cv_termination_tac  : tactic

  val measure_args : int list -> thm -> thm

end
