signature test_cases =
sig

  include Abbrev
  val test_term : conv -> (string * term * bool) -> unit
  val terms_to_test : (string * term * bool) list
  val perform_tests : conv -> unit

end;
