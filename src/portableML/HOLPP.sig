signature HOLPP =
sig
(* PP -- pretty-printing -- from the SML/NJ library *)

datatype pretty = datatype PrettyImpl.pretty

type 'a pprinter = 'a -> pretty

datatype break_style =
    CONSISTENT
  | INCONSISTENT

(* For backwards compatibility; these types are not otherwise used in HOLPP.
   See instead HOLquotation.
 *)
datatype frag = datatype quotation_dtype.frag
type 'a quotation = 'a quotation_dtype.quotation

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
