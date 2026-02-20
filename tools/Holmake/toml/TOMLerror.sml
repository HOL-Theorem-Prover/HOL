(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
structure TOMLerror =
struct
  datatype error =
    UNEXPECTED of {encountered: string, expected: string}
  | PREFIX_ZERO
  | INVALID_UNICODE_SCALAR
  | INVALID_DATE
  | INVALID_TIME
  | DUPLICATE_KEY of string list
  local
    fun prettyKey "" = "\"\""
      | prettyKey s =
          if
            CharVector.all
              (fn c => Char.isAlphaNum c orelse c = #"-" orelse c = #"_") s
          then s
          else "\"" ^ s ^ "\""
  in
    fun toString (UNEXPECTED {encountered, expected}) =
          "unexpected " ^ encountered ^ ", expected " ^ expected
      | toString PREFIX_ZERO = "prefix 0 is disallowed"
      | toString INVALID_UNICODE_SCALAR = "invalid Unicode scalar"
      | toString INVALID_DATE = "invalid date"
      | toString INVALID_TIME = "invalid time"
      | toString (DUPLICATE_KEY path) =
          "duplicate key at " ^ String.concatWith "." (List.map prettyKey path)
  end
  exception ParseError of error
end
