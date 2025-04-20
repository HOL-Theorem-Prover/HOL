(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure SimplePromise:
sig
  type 'a t
  val new: (unit -> 'a) -> 'a t
  val get: 'a t -> 'a
end =
struct

  type 'a t = unit -> 'a

  fun new f = f
  fun get f = f ()

end
