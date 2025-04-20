(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ExnHistory:
sig
  val history: exn -> string list
end =
struct
  fun history _ = []
end
