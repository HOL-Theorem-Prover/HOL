signature Prenex =
sig
  local type int = arbint.int in


   val is_prenex : Term.term -> bool
   val PRENEX_CONV : Abbrev.conv
  end
end
