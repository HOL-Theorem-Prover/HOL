open HolKernel boolLib Parse relationTheory testutils

(* Pretty-printing of the relation suffixes (HOL issue #486).  The
   transitive (^+), reflexive-transitive, equivalence and transpose (^T)
   suffixes all share precedence level 2100, so a suffix whose argument is
   printed by another rule at that same level is parenthesised.  A single
   suffix at the top is left bare. *)
val _ = List.app
          (fn (s1,s2) => tpp_expected
                           {testf=standard_tpp_message, input=s1, output=s2})
          [("TC R", "R⁺"),
           ("inv R", "Rᵀ"),
           ("inv (TC R)", "(R⁺)ᵀ"),
           ("TC (inv R)", "(Rᵀ)⁺"),
           ("TC (TC R)", "(R⁺)⁺")]
