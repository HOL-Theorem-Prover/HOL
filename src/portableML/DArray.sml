structure DArray :> DArray =
struct

type 'a darray = ('a array * int * 'a) ref

fun new (cap, v) = ref (Array.array (cap, v), 0, v)

val base = !

fun clear (r as ref (a, _, dflt)) = r := (a, 0, dflt)

fun sub (ref (a, sz, _), i) = if i < sz then Array.sub (a, i) else raise Subscript

fun update (ref (a, sz, _), i, v) = if i < sz then Array.update (a, i, v) else raise Subscript

fun cloneCore ((a, sz, dflt), cap) = let
  val a' = Array.array (cap, dflt)
  val _ = ArraySlice.copy {src = ArraySlice.slice (a, 0, SOME sz), dst = a', di = 0}
  in (a', sz, dflt) end

fun clone (ref a, cap) = ref (cloneCore (a, cap))

fun ensureCapacity (r as (a, _, _), cap) =
  if cap <= Array.length a then r else let
    val cap' = Int.max (cap, Array.length a * 3 div 2)
    val cap' = if cap' <= Array.maxLen then cap' else
      if cap <= Array.maxLen then Array.maxLen else raise Overflow
    in cloneCore (r, cap') end

fun push (r as ref (a as (_, sz, _:'a)), v) = let
  val (a, sz, dflt) = ensureCapacity (a, sz + 1)
  val _ = Array.update (a, sz, v)
  in r := (a, sz+1, dflt) end

fun size (ref (_, sz, _)) = sz

fun isEmpty a = size a = 0

fun capacity (ref (a, _, _)) = Array.length a

fun last a = case size a of 0 => NONE | sz => SOME (sub (a, sz-1))

fun setLast (a, v) = update (a, size a - 1, v)

fun array a = #1 (base (clone (a, size a)))

fun fromArray (a, dflt) = ref (a, Array.length a, dflt)

fun fromArray1 a = fromArray (a, Array.sub (a, 0))

fun fromList (a, dflt) = fromArray (Array.fromList a, dflt)

fun fromList1 a = fromArray1 (Array.fromList a)

fun tabulate (dflt, n, f) = fromArray (Array.tabulate (n, f), dflt)

type 'a slice = 'a ArraySlice.slice

fun full (ref (a, sz, _)) = ArraySlice.slice (a, 0, SOME sz)

fun slice (ref (a, sz, _), i, SOME len) =
    if i+len <= sz then ArraySlice.slice (a, i, SOME len) else raise Subscript
  | slice (ref (a, sz, _), i, NONE) =
    if i <= sz then ArraySlice.slice (a, i, SOME (sz - i)) else raise Subscript

fun copy {src, dst = ref (a, sz, _), di} =
  if di + ArraySlice.length src > sz then raise Subscript
  else ArraySlice.copy {src = src, dst = a, di = di}

fun copyVec {src, dst = ref (a, sz, _), di} =
  if di + VectorSlice.length src > sz then raise Subscript
  else ArraySlice.copyVec {src = src, dst = a, di = di}

fun append (r as ref (a as (_, sz, _)), v) = (
  r := ensureCapacity (a, sz + ArraySlice.length v);
  ArraySlice.copy {src = v, dst = #1 (!r), di = sz})

fun replace (r, ref a) = r := a

fun app f a = ArraySlice.app f (full a)
fun appi f a = ArraySlice.appi f (full a)
fun all f a = ArraySlice.all f (full a)
fun exists f a = ArraySlice.exists f (full a)
fun collate f (a, b) = ArraySlice.collate f (full a, full b)
fun find f a = ArraySlice.find f (full a)
fun findi f a = ArraySlice.findi f (full a)
fun foldl f b a = ArraySlice.foldl f b (full a)
fun foldli f b a = ArraySlice.foldli f b (full a)
fun foldr f b a = ArraySlice.foldr f b (full a)
fun foldri f b a = ArraySlice.foldri f b (full a)
fun modify f a = ArraySlice.modify f (full a)
fun modifyi f a = ArraySlice.modifyi f (full a)
fun vector a = ArraySlice.vector (full a)

end
