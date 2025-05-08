(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParserContext:
sig
  type t

  val make:
    { parseError: Source.range -> string -> unit
    , successorML: bool
    }
    -> t

  val topExp: t -> bool
  val optBar: t -> bool
  val recordPun: t -> bool
  val orPat: t -> bool
  val extendedText: t -> bool
  val sigWithtype: t -> bool
end =
struct
  datatype t =
    T of
      { parseError: Source.range -> string -> unit
      , successorML: bool
      }

  fun make x = T x
  fun topExp _ = true
  fun optBar (T x) = #successorML x
  fun recordPun (T x) = #successorML x
  fun orPat (T x) = #successorML x
  fun extendedText _ = true
  fun sigWithtype _ = true
end
