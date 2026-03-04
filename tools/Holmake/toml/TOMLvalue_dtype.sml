(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)

structure TOMLvalue_dtype =
struct
  datatype value =
    STRING of string (* UTF-8 encoded *)
  | INTEGER of IntInf.int
  | FLOAT of real
  | BOOL of bool
  | DATETIME of string (* 2024-01-12T19:20:21[.123]+09:00 *)
  | LOCAL_DATETIME of string (* 2024-01-12T19:20:21[.123] *)
  | DATE of string (* 2024-01-12 *)
  | TIME of string (* 19:20:21.99999 *)
  | ARRAY of value list
  | TABLE of table
  withtype table = (string * value) list
end
