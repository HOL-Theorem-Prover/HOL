(* ========================================================================= *)
(* PARSER COMBINATORS                                                        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibParser =
sig

(* Recommended fixities
  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
*)

type 'a pp = 'a mlibUseful.pp
type 'a stream = 'a mlibStream.stream

(* Generic *)
exception Noparse
val ++         : ('a -> 'b * 'a) * ('a -> 'c * 'a) -> 'a -> ('b * 'c) * 'a
val >>         : ('a -> 'b * 'a) * ('b -> 'c) -> 'a -> 'c * 'a
val >>++       : ('a -> 'b * 'a) * ('b -> 'a -> 'c * 'a) -> 'a -> 'c * 'a
val ||         : ('a -> 'b * 'a) * ('a -> 'b * 'a) -> 'a -> 'b * 'a
val smany      : ('s -> 'a -> 's * 'a) -> 's -> 'a -> 's * 'a
val many       : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val atleastone : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
val nothing    : 'a -> unit * 'a
val optional   : ('a -> 'b * 'a) -> 'a -> 'b option * 'a

(* mlibStream-based *)
type ('a,'b) parser = 'a stream -> 'b * 'a stream
val everything : ('a, 'b list) parser -> 'a stream -> 'b stream
val maybe      : ('a -> 'b option) -> ('a,'b) parser
val finished   : ('a,unit) parser
val some       : ('a -> bool) -> ('a,'a) parser
val any        : ('a,'a) parser
val exact      : ''a -> (''a,''a) parser

(* Parsing and pretty-printing for infix operators *)
type infixities  = {tok : string, prec : int, left_assoc : bool} list
type 'a con = string * 'a * 'a -> 'a
type 'a des = 'a -> (string * 'a * 'a) option
type 'a iparser = (string,'a) parser
type 'a iprinter = ('a * bool) pp
val optoks            : infixities -> string list
val parse_left_infix  : string list -> 'a con -> 'a iparser -> 'a iparser
val parse_right_infix : string list -> 'a con -> 'a iparser -> 'a iparser
val parse_infixes     : infixities  -> 'a con -> 'a iparser -> 'a iparser
val pp_left_infix     : string list -> 'a des -> 'a iprinter -> 'a iprinter
val pp_right_infix    : string list -> 'a des -> 'a iprinter -> 'a iprinter
val pp_infixes        : infixities  -> 'a des -> 'a iprinter -> 'a iprinter

(* Lexing *)
val space    : char -> bool
val digit    : char -> bool
val lower    : char -> bool
val upper    : char -> bool
val alpha    : char -> bool
val alphanum : char -> bool             (* alpha + digit + _ + ' *)
val symbol   : char -> bool             (* <>=-*+/\?@|!$%&~#^: *)
val punct    : char -> bool             (* ()[]{}.,; *)

(* Quotations *)
type 'a quotation = 'a frag list
val quotation_parser : (string -> 'a) -> 'b pp -> 'b quotation -> 'a

end
