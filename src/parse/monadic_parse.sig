signature monadic_parse =
sig

type ('a,'b) Parser = ('b list, 'a) optmonad.optmonad

val get : ('a, 'a) Parser
val peek : ('a, 'a) Parser
val pushback : 'a -> (unit, 'a) Parser

val item : ''a -> (''a, ''a) Parser
val itemP : ('a -> bool) -> ('a, 'a) Parser
val eof : (unit, 'a) Parser

val sepby  : ('sep, 'b) Parser -> ('a, 'b) Parser -> ('a list, 'b) Parser
val sepby1 : ('sep, 'b) Parser -> ('a, 'b) Parser -> ('a list, 'b) Parser
val chainl :
  ('b, 'c) Parser -> ('b -> 'b -> 'b, 'c) Parser -> 'b -> ('b, 'c) Parser
val chainl1 : ('b, 'c) Parser -> ('b -> 'b -> 'b, 'c) Parser -> ('b, 'c) Parser
val chainr :
  ('b, 'c) Parser -> ('b -> 'b -> 'b, 'c) Parser -> 'b -> ('b, 'c) Parser
val chainr1 : ('b, 'c) Parser -> ('b -> 'b -> 'b, 'c) Parser -> ('b, 'c) Parser

val string : string -> (string, char) Parser
val number : (int, char) Parser

(* these two are similar; they strip white-space on one side or another
   of an occurence of what the passed parser is looking for.
   token strips leading whitespace, parse strip trailing whitespace *)
val token : ('a, char) Parser -> ('a, char) Parser
val parse : ('a, char) Parser -> ('a, char) Parser

(* just like string, but tokenized by token above *)
val symbol : string -> (string, char) Parser

(* grabs an identifier (no tokenising) *)
val ident : (string, char) Parser

(* produces a token that is an identifier, using the usual criteria:
   first character alphabetic, rest alphabetic or numeric or "_" *)
val T_ident : (string, char) Parser
(* produces a token that is a symbolic identifier, using SML like
   criteria *)
val T_ident_op : (string, char) Parser

(* applies a parser and then requires it to be followed by eof *)
val wholething : ('a, 'b) Parser -> ('a, 'b) Parser


exception NoParseResult of string
val apply_to_file : ('a, char) Parser -> string -> 'a
val apply_to_string : ('a, char) Parser -> string -> 'a

end
