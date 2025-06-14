(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** A maybe-long thing can be prefaced by structure identifiers, like
  * `Hello.World.thing` but also just `thing` (which has no qualifiers)
  *)
structure MaybeLongToken :>
sig
  type t
  val make: Token.t -> t
  val getToken: t -> Token.t
  val isLong: t -> bool
end =
struct
  type t = Token.t

  fun make (tok: Token.t) : t =
    if Token.isMaybeLongIdentifier tok then
      tok
    else
      raise Fail
        ("MaybeLongToken.make: given non-identifier ("
         ^ Token.classToString (Token.getClass tok) ^ ")")

  fun getToken tok = tok

  fun isLong tok = Token.isLongIdentifier tok
end
