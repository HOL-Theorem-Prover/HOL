structure HOLgrammars :> HOLgrammars =
struct

exception GrammarError of string
datatype associativity = LEFT | RIGHT | NONASSOC

fun assocToString x =
  case x of
    LEFT => "HOLgrammars.LEFT"
  | RIGHT => "HOLgrammars.RIGHT"
  | NONASSOC => "HOLgrammars.NONASSOC"

end
