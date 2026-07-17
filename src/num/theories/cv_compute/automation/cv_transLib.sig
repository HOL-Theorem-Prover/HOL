signature cv_transLib =
sig
  include Abbrev

  val cv_trans          : thm -> unit
  (* Like cv_trans / cv_auto_trans, but report a generated precondition as
     SOME <pre definition> instead of failing.  On SOME, the guarded
     [cv_rep] results and the <name>_pre constants have already been defined. *)
  val cv_trans_opt_pre  : thm -> thm option
  val cv_trans_pre      : (* pre name *) string -> thm -> thm
  val cv_trans_pre_rec  : (* pre name *) string -> thm -> tactic -> thm
  val cv_trans_rec      : thm -> tactic -> unit

  val cv_auto_trans          : thm -> unit
  val cv_auto_trans_opt_pre  : thm -> thm option
  val cv_auto_trans_pre      : (* pre name *) string -> thm -> thm
  val cv_auto_trans_pre_rec  : (* pre name *) string -> thm -> tactic -> thm
  val cv_auto_trans_rec      : thm -> tactic -> unit

  (* The conv should evaluate `from <deep_embedding>` *)
  val cv_trans_deep_embedding : conv -> thm -> unit

  datatype pat = datatype cv_trans_dtype.pat

  val cv_eqs_for  : term -> thm list
  val cv_eval     : term -> thm
  val cv_eval_raw : term -> thm
  val cv_eval_pat : pat -> term -> thm

  val cv_termination_tac  : tactic

  val measure_args : int list -> thm -> thm

end
