signature closure =
sig
 include Abbrev
 val abs_fvars : term -> term
 val close_one_by_one : thm -> thm
 val identify_fun : term -> term
 val abs_all_fvars : term -> term
 val close_all : thm -> thm
 val TOP_LEVEL_RULE : thm -> thm
 val closure_convert : thm -> thm
end
