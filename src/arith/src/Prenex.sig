signature Prenex =
sig
   val is_prenex : Term.term -> bool
   val PRENEX_CONV : Abbrev.conv
end
