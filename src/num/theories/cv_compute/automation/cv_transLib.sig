signature cv_transLib =
sig
  include Abbrev

  val cv_trans          : thm -> unit
  val cv_trans_pre      : (* pre name *) string -> thm -> thm
  val cv_trans_pre_rec  : (* pre name *) string -> thm -> tactic -> thm
  val cv_trans_rec      : thm -> tactic -> unit

  val cv_auto_trans          : thm -> unit
  val cv_auto_trans_pre      : (* pre name *) string -> thm -> thm
  val cv_auto_trans_pre_rec  : (* pre name *) string -> thm -> tactic -> thm
  val cv_auto_trans_rec      : thm -> tactic -> unit

  (* The conv should evaluate `from <deep_embedding>` *)
  val cv_trans_deep_embedding : conv -> thm -> unit

  (* Removes a stored translation ("thy.name", or "name" in the current
     theory), here and in descendant theories, so that another can be
     added in its place *)
  val cv_rep_delete : string -> unit

  datatype pat = datatype cv_trans_dtype.pat

  val cv_eqs_for  : term -> thm list
  val cv_eval     : term -> thm
  val cv_eval_raw : term -> thm
  val cv_eval_pat : pat -> term -> thm

  val cv_termination_tac  : tactic

  val measure_args : int list -> thm -> thm

end
