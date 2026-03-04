(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
structure TOMLvalue :> TOMLvalue =
struct
  open TOMLvalue_dtype
  structure Integer = IntInf
  val string = STRING
  val integer = INTEGER
  fun float s =
    FLOAT (Option.valOf (Real.fromString s))
  val bool = BOOL
  val datetime = DATETIME
  val localDatetime = LOCAL_DATETIME
  val date = DATE
  val time = TIME
  val array = ARRAY
  val subtable = TABLE
  val table = fn xs => xs
end
