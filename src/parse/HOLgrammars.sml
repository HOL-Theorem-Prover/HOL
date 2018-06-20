structure HOLgrammars =
struct

exception GrammarError of string
datatype associativity = LEFT | RIGHT | NONASSOC

fun assocToString x =
  case x of
    LEFT => "HOLgrammars.LEFT"
  | RIGHT => "HOLgrammars.RIGHT"
  | NONASSOC => "HOLgrammars.NONASSOC"

fun assoc_encode LEFT = "L"
  | assoc_encode RIGHT = "R"
  | assoc_encode NONASSOC = "N"

val assoc_reader =
    let
      open optmonad Coding
      infix >> ||
    in
      (literal "L" >> return LEFT) ||
      (literal "R" >> return RIGHT) ||
      (literal "N" >> return NONASSOC)
    end

type mini_lspec = {nilstr:string,cons:string,sep:string}
datatype rule_element =
         TOK of string
       | TM
       | ListTM of mini_lspec
type block_info = HOLPP.break_style * int

datatype pp_element =
         PPBlock of pp_element list * block_info
       | EndInitialBlock of block_info
       | BeginFinalBlock of block_info
       | HardSpace of int
       | BreakSpace of (int * int)
       | RE of rule_element
       | ListForm of {
           separator : pp_element list,
           block_info: block_info,
           cons      : string,
           nilstr    : string
         }
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
