signature test_cases =
sig

  include Abbrev
  val test_term : conv -> (string * term * bool) -> unit
  val test_goal : tactic -> (string * goal) -> unit

  val terms_to_test : (string * term * bool) list
  val omega_test_terms : (string * term * bool) list
  val cooper_test_terms : (string * term * bool) list
  val goals_to_test : (string * goal) list
  val perform_tests : conv -> tactic -> unit
  val perform_omega_tests : conv -> unit
  val perform_cooper_tests : conv -> unit

end
