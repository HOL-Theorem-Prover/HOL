(* PP -- Oppen-style prettyprinters.
 *
 * Modified for Moscow ML from SML/NJ Library version 0.2
 *
 * COPYRIGHT (c) 1992 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *)

(* the functions and data for actually doing printing. *)
structure HOLPP :> HOLPP =
struct

datatype pretty = datatype PolyML.pretty
type ppstream = pretty list

type ('a,'st) printer = 'st -> 'a * 'st * ppstream

datatype break_style =
    CONSISTENT
  | INCONSISTENT

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
type 'a quotation = 'a frag list

val prettyPrint = PolyML.prettyPrint

end; (* struct *)
