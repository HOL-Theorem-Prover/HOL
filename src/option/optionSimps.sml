structure optionSimps :> optionSimps =
struct

open simpLib optionTheory

val OPTION_ss = rewrites [option_CLAUSES];

end;
