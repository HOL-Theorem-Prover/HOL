structure HOLgrammars =
struct

exception GrammarError of string
datatype associativity = LEFT | RIGHT | NONASSOC

fun assocToString x =
  case x of
    LEFT => "HOLgrammars.LEFT"
  | RIGHT => "HOLgrammars.RIGHT"
  | NONASSOC => "HOLgrammars.NONASSOC"

datatype rule_element = TOK of string | TM
type block_info = Portable.break_style * int

datatype pp_element =
         PPBlock of pp_element list * block_info
       | EndInitialBlock of block_info
       | BeginFinalBlock of block_info
       | HardSpace of int
       | BreakSpace of (int * int)
       | RE of rule_element
       | LastTM
       | FirstTM   (* these last two only used internally *)

datatype PhraseBlockStyle =
         AroundSameName
       | AroundSamePrec
       | AroundEachPhrase
       | NoPhrasing

datatype ParenStyle =
         Always
       | OnlyIfNecessary
       | NotEvenIfRand
       | ParoundName
       | ParoundPrec

end
