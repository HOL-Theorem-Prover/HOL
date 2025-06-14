(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Util:
sig
  val equalLists: ('a * 'a -> bool) -> 'a list * 'a list -> bool

  val loop: (int * int) -> 'a -> ('a * int -> 'a) -> 'a
  val for: (int * int) -> (int -> unit) -> unit

  val all: (int * int) -> (int -> bool) -> bool
  val exists: (int * int) -> (int -> bool) -> bool

  val getTime: (unit -> 'a) -> 'a * Time.time

  val gtOfCmp: ('a * 'a -> order) -> ('a * 'a -> bool)
end =
struct

  fun getTime f =
    let
      val t0 = Time.now ()
      val result = f ()
      val t1 = Time.now ()
    in
      (result, Time.- (t1, t0))
    end

  fun equalLists eq ([], []) = true
    | equalLists eq (x :: xs, y :: ys) =
        eq (x, y) andalso equalLists eq (xs, ys)
    | equalLists _ _ = false

  fun loop (lo, hi) b f =
    if lo >= hi then b else loop (lo + 1, hi) (f (b, lo)) f

  fun all (lo, hi) f =
    let
      fun allFrom i =
        (i >= hi) orelse (f i andalso allFrom (i + 1))
    in
      allFrom lo
    end

  fun exists (lo, hi) f =
    let
      fun existsFrom i =
        i < hi andalso (f i orelse existsFrom (i + 1))
    in
      existsFrom lo
    end

  fun for (lo, hi) f =
    if lo >= hi then () else (f lo; for (lo + 1, hi) f)

  fun gtOfCmp cmp (x, y) =
    case cmp (x, y) of
      GREATER => true
    | _ => false
end
