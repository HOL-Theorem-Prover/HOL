structure IntPairTable :> IntPairTable = struct

(* Open-addressing hash table: (int * int) -> int.
   Uses three parallel arrays (k1, k2, value) with linear probing.
   Empty slots marked by k1 = ~1. *)

type table = {
  k1: int array ref,
  k2: int array ref,
  v:  int array ref,
  count: int ref
}

val empty_marker = ~1

fun create size = let
  (* Round up to ensure odd capacity for better probing *)
  val cap = if size < 16 then 16 else size
  val cap = if cap mod 2 = 0 then cap + 1 else cap
in {
  k1 = ref (Array.array(cap, empty_marker)),
  k2 = ref (Array.array(cap, 0)),
  v  = ref (Array.array(cap, 0)),
  count = ref 0
} end

fun hash (a: int, b: int) : int = let
  val w = Word.+(Word.*(Word.fromInt a, 0w2654435761),
                 Word.*(Word.fromInt b, 0w2246822519))
in Word.toInt(Word.andb(w, 0wx7FFFFFFF)) end

fun lookup ({k1, k2, v, ...}: table) (a, b) = let
  val arr1 = !k1 val arr2 = !k2 val arrv = !v
  val cap = Array.length arr1
  val start = hash(a, b) mod cap
  fun probe i =
    if Array.sub(arr1, i) = empty_marker then NONE
    else if Array.sub(arr1, i) = a andalso Array.sub(arr2, i) = b
    then SOME (Array.sub(arrv, i))
    else let val j = i + 1 in
      probe (if j = cap then 0 else j)
    end
in probe start end

fun resize ({k1, k2, v, count}: table) = let
  val old1 = !k1 val old2 = !k2 val oldv = !v
  val oldcap = Array.length old1
  val newcap = oldcap * 2 + 1
  val n1 = Array.array(newcap, empty_marker)
  val n2 = Array.array(newcap, 0)
  val nv = Array.array(newcap, 0)
  fun reinsert i =
    if i >= oldcap then ()
    else if Array.sub(old1, i) = empty_marker then reinsert (i + 1)
    else let
      val a = Array.sub(old1, i)
      val b = Array.sub(old2, i)
      val start = hash(a, b) mod newcap
      fun probe j =
        if Array.sub(n1, j) = empty_marker
        then (Array.update(n1, j, a);
              Array.update(n2, j, b);
              Array.update(nv, j, Array.sub(oldv, i)))
        else let val jj = j + 1 in
          probe (if jj = newcap then 0 else jj)
        end
    in probe start; reinsert (i + 1) end
in k1 := n1; k2 := n2; v := nv; reinsert 0 end

fun insert (t as {k1, k2, v, count}) (a, b) value = let
  val arr1 = !k1
  val cap = Array.length arr1
  val start = hash(a, b) mod cap
  fun probe i =
    if Array.sub(arr1, i) = empty_marker
    then (Array.update(!k1, i, a);
          Array.update(!k2, i, b);
          Array.update(!v, i, value);
          count := !count + 1)
    else let val j = i + 1 in
      probe (if j = cap then 0 else j)
    end
  val () = probe start
in if !count * 10 > cap * 7 then resize t else () end

end
