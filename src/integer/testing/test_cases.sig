signature test_cases =
sig

  include Abbrev
  val test_term : conv -> (string * term * bool) -> bool
  val test_goal : tactic -> (string * goal) -> bool

  val terms_to_test : (string * term * bool) list
  val goals_to_test : (string * goal) list
  val perform_tests : conv -> tactic -> bool

end;
