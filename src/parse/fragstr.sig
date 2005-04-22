signature fragstr = 
sig
  type 'a frag = 'a Portable.frag

  type ('a,'b) Parser = ('a,'b) monadic_parse.Parser
  val antiq : ('a, 'a frag) Parser
  val item : char -> (char, 'a frag) Parser
  val itemP : (char -> bool) -> (char, 'a frag) Parser
  val many_charP : (char -> bool) -> (string, 'a frag) Parser
  val many1_charP : (char -> bool) -> (string, 'a frag) Parser
  val string : string -> (string, 'a frag) Parser
  val normal_alpha_ident : (string, 'a frag) Parser
  val eof : (unit, 'a frag) Parser

  (* removes leading white space *)
  val token : ('a, 'b frag) Parser -> ('a, 'b frag) Parser
  (* removes trailing white space and requires all input to be consumed *)
  val parse : ('a, 'b frag) Parser -> ('a, 'b frag) Parser

  val grab_whitespace : (unit, 'b frag) Parser
  val comment : (unit, 'b frag) Parser

  (* looks for the given string after having had white space first
   removed - this is the only parser of those here which has been
   tokenized in this way *)
  val symbol : string -> (string, 'a frag) Parser

end
