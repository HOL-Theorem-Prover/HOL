signature HOLgrammars =
sig

  exception GrammarError of string
  datatype associativity = LEFT | RIGHT | NONASSOC

  val assocToString : associativity -> string
end
