(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
signature TOMLvalue =
sig
  datatype value = datatype TOMLvalue_dtype.value
  type table = (string * value) list
  structure Integer:
  sig
    type int = IntInf.int
    val + : int * int -> int
    val * : int * int -> int
    val fromInt: Int.int -> int
    val fromString: string -> int option
  end
  val string: string -> value
  val integer: Integer.int -> value
  val float: string -> value
  val bool: bool -> value
  val datetime: string -> value
  val localDatetime: string -> value
  val date: string -> value
  val time: string -> value
  val array: value list -> value
  val subtable: table -> value
  val table: (string * value) list -> table
end
