(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParserContext:
sig
  type t

  val make:
    { topExp: bool
    , optBar: bool
    , recordPun: bool
    , orPat: bool
    , extendedText: bool
    , sigWithtype: bool
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
      { topExp: bool
      , optBar: bool
      , recordPun: bool
      , orPat: bool
      , extendedText: bool
      , sigWithtype: bool
      }

  fun make x = T x
  fun topExp (T x) = #topExp x
  fun optBar (T x) = #optBar x
  fun recordPun (T x) = #recordPun x
  fun orPat (T x) = #orPat x
  fun extendedText (T x) = #extendedText x
  fun sigWithtype (T x) = #sigWithtype x
end
