structure optionSimps :> optionSimps =
struct

open simpLib optionTheory

val OPTION_ss = rewrites [option_CLAUSES, OPTION_MAP_EQ_SOME,
                          OPTION_MAP_EQ_NONE]

end;
