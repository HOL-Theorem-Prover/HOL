signature treeSyntax =
sig

include Abbrev;


val node_term : term
val dest_node : term -> term *  term
val is_node   : term -> bool

val leaf_term : term
val is_leaf   : term -> bool


end

