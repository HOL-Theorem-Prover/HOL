(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Seq :>
sig
  type 'a t = 'a ArraySlice.slice
  type 'a seq = 'a t

  val length: 'a seq -> int
  val nth: 'a seq -> int -> 'a

  val subseq: 'a seq -> (int * int) -> 'a seq
  val take: 'a seq -> int -> 'a seq
  val drop: 'a seq -> int -> 'a seq
  val first: 'a seq -> 'a
  val last: 'a seq -> 'a

  val empty: unit -> 'a seq
  val singleton: 'a -> 'a seq
  val fromList: 'a list -> 'a seq
  val fromRevList: 'a list -> 'a seq
  val toList: 'a seq -> 'a list
  val toString: ('a -> string) -> 'a seq -> string
  val equal: ('a * 'a -> bool) -> 'a seq * 'a seq -> bool

  val S : 'a -> 'a seq
  val % : 'a list -> 'a seq

  val append: 'a seq * 'a seq -> 'a seq
  val append3: 'a seq * 'a seq * 'a seq -> 'a seq
  val rev: 'a seq -> 'a seq

  val tabulate: (int -> 'a) -> int -> 'a seq
  val map: ('a -> 'b) -> 'a seq -> 'b seq
  val mapIdx: (int * 'a -> 'b) -> 'a seq -> 'b seq
  val zipWith: ('a * 'b -> 'c) -> 'a seq * 'b seq -> 'c seq
  val zip: 'a seq * 'b seq -> ('a * 'b) seq
  val filter: ('a -> bool) -> 'a seq -> 'a seq

  val iterate: ('b * 'a -> 'b) -> 'b -> 'a seq -> 'b

  val applyIdx: 'a seq -> (int * 'a -> unit) -> unit

end =
struct
  structure AS = ArraySlice
  structure A = Array

  type 'a t = 'a ArraySlice.slice
  type 'a seq = 'a t

  fun length s = AS.length s

  fun nth s i = AS.sub (s, i)

  fun empty () =
    AS.full (A.fromList [])
  fun singleton x =
    AS.full (A.array (1, x))
  val S = singleton
  fun toString f s =
    "<" ^ String.concatWith "," (List.tabulate (length s, f o nth s)) ^ ">"

  fun fromList l =
    AS.full (A.fromList l)
  val % = fromList
  fun toList s =
    SeqBasis.foldl (fn (list, x) => x :: list) [] (0, length s) (fn i =>
      nth s (length s - i - 1))


  fun fromRevList l =
    case l of
      [] => empty ()
    | x :: _ =>
        let
          val n = List.length l
          val output = A.array (n, x)
          fun loop i xs =
            case xs of
              [] => ()
            | x :: xs' => (A.update (output, i - 1, x); loop (i - 1) xs')
        in
          loop n l;
          AS.full output
        end


  fun empty () =
    AS.full (Array.fromList [])

  fun tabulate f n =
    AS.full (Array.tabulate (n, f))

  fun map f s =
    tabulate (f o nth s) (length s)

  fun mapIdx f s =
    tabulate (fn i => f (i, nth s i)) (length s)

  fun zipWith f (s, t) =
    tabulate (fn i => f (nth s i, nth t i)) (Int.min (length s, length t))

  fun iterate f b s =
    SeqBasis.foldl f b (0, length s) (nth s)

  fun equal eq (s, t) =
    length s = length t
    andalso
    SeqBasis.foldl (fn (a, b) => a andalso b) true (0, length s) (fn i =>
      eq (nth s i, nth t i))

  fun append (s, t) =
    let
      val (ns, nt) = (length s, length t)
      fun ith i =
        if i < ns then nth s i else nth t (i - ns)
    in
      tabulate ith (ns + nt)
    end

  fun append3 (a, b, c) =
    let
      val (na, nb, nc) = (length a, length b, length c)
      fun ith i =
        if i < na then nth a i
        else if i < na + nb then nth b (i - na)
        else nth c (i - na - nb)
    in
      tabulate ith (na + nb + nc)
    end

  fun zip (s, t) =
    zipWith (fn xx => xx) (s, t)

  fun rev s =
    tabulate (fn i => nth s (length s - 1 - i)) (length s)

  fun filter p s =
    AS.full (SeqBasis.filter (0, length s) (nth s) (p o nth s))

  fun applyIdx s f =
    Util.for (0, length s) (fn i => f (i, nth s i))

  fun subseq s (i, k) =
    AS.subslice (s, i, SOME k)
  fun take s n = subseq s (0, n)
  fun drop s n =
    subseq s (n, length s - n)
  fun first s = nth s 0
  fun last s =
    nth s (length s - 1)

end
