signature test_cases =
sig

  include Abbrev
  val test_term : conv -> (string * term) -> unit
  val terms_to_test : (string * term) list
  val perform_tests : conv -> unit

end;
