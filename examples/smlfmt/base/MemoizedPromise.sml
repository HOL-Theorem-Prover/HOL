(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure MemoizedPromise:
sig
  type 'a t
  val new: (unit -> 'a) -> 'a t
  val get: 'a t -> 'a
end =
struct

  datatype 'a contents = Delayed of (unit -> 'a) | Ready of 'a

  type 'a t = 'a contents ref

  fun new f =
    ref (Delayed f)

  fun get m =
    case !m of
      Delayed f => let val x = f () in m := Ready x; x end
    | Ready x => x

end
