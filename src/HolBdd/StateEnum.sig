signature StateEnum = sig

  type term = Term.term
  type thm = Thm.thm

  val intToTerm : int -> term
  val mk_bool_var : string -> term
  val mk_primed_bool_var : string -> term
  val PGEN_EXT : thm -> thm

  val MakeSimpReachByRecThm : thm * thm -> thm
  val MakeSimpReachInRecThm : thm * thm -> thm
  val ComputeReachable : 
   thm * thm -> {ReachThm : thm, iterations : int}
  val ComputeSimpReachable : 
   thm * thm -> {ReachThm : thm, SimpTransThm : thm, iterations : int}
  val FindRefutationTrace : thm * thm * thm -> thm list

  val PROVE_ABS_THMS : thm -> thm -> thm
  val define_rep : thm -> {abs_spec : thm, range_def : thm, rep_spec : thm}
  val ABS_EXISTS_THM : thm
end
