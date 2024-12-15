signature ltl2omega =
sig
    include Abbrev;

    val ltl2omega_test : (term -> thm) * term * term -> unit;
    val ltl2omega_test_simple : (term -> 'a) * term -> unit;

end
