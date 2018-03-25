signature HOLPP =
sig
(* PP -- pretty-printing -- from the SML/NJ library *)

datatype pretty = datatype PolyML.pretty

type 'a pprinter = 'a -> pretty

datatype break_style =
    CONSISTENT
  | INCONSISTENT

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
type 'a quotation = 'a frag list

val prettyPrint : (string -> unit) * int -> pretty -> unit
val pp_to_string : int -> ('a -> pretty) -> 'a -> string

val add_string : string -> pretty
val add_stringsz : string * int -> pretty
val add_break : int * int -> pretty
val NL : pretty
val add_newline : pretty
val block : break_style -> int -> pretty list -> pretty

val pr_list : 'a pprinter -> pretty list -> 'a list -> pretty list
val tabulateWith : (int -> 'a) -> 'a list -> int -> 'a list

val pp_pretty : pretty pprinter


end
