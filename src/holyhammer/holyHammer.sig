signature holyHammer =
sig

  datatype PREDICTOR = KNN | Mepo | NBayes | Geo | Kepo
  datatype ATP = Eprover | Vampire | Z3

  val hh      : Thm.thm list -> Term.term -> unit
  val hh_try  : Thm.thm list -> Term.term -> int -> unit
  val hh_atp  : ATP -> Thm.thm list -> Term.term -> unit
  val hh_goal : Thm.thm list -> Term.term list * Term.term -> unit

  val set_minimization : bool -> unit
  val set_timeout      : int -> unit
  val set_predictors   : PREDICTOR -> unit
  val reset_hh         : unit -> unit
  val set_prediction   : ATP -> int -> unit
  val set_predictor    : ATP -> PREDICTOR -> unit
  val atp_settings     : ATP -> (PREDICTOR * int * int)

end
