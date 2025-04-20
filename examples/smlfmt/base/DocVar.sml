(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure DocVar:
sig
  type t
  val new: unit -> t
  val toString: t -> string
  val compare: t * t -> order
end =
struct

  datatype t = DocVar of {id: int}

  val counter = ref 0

  fun new () =
    let val result = DocVar {id = !counter}
    in counter := !counter + 1; result
    end

  fun toString (DocVar {id}) =
    "[v" ^ Int.toString id ^ "]"

  fun compare (DocVar {id = id1}, DocVar {id = id2}) = Int.compare (id1, id2)

end
