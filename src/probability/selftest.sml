open testutils extrealTheory

val _ = tpp "¬p ∧ q"

val _ = tpp_expected {input = "-y * z : extreal", output = "-y * z",
                      testf = standard_tpp_message}

val _ = tpp_expected {input = "~y * z : extreal", output = "-y * z",
                      testf = standard_tpp_message}
