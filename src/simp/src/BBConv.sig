signature BBConv =
sig

include Abbrev
type bbconv = thm -> thm

val NO_BBCONV : bbconv
val FIRST_BBCONV : bbconv list -> bbconv
val BBCONV_RULE : bbconv -> bbconv
val ORELSEBBC : bbconv * bbconv -> bbconv

val c2bbc : conv -> bbconv

end
