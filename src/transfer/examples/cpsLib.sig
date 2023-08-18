signature cpsLib =
sig

include Abbrev
val cwcp : term -> thm
val contify_CONV : thm list -> conv

end
