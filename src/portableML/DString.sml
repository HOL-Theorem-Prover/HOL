structure DString :> DString =
struct

type array = Word8Array.array
type dstring = (array * int) ref

fun new cap = ref (Word8Array.array (cap, 0w0), 0)

val base = !

fun clear (r as ref (a, _)) = r := (a, 0)

fun sub (ref (a, sz), i) =
  if i < sz then Byte.byteToChar (Word8Array.sub (a, i)) else raise Subscript

fun update (ref (a, sz), i, v) =
  if i < sz then Word8Array.update (a, i, Byte.charToByte v) else raise Subscript

fun cloneCore ((a, sz), cap) = let
  val a' = Word8Array.array (cap, 0w0)
  val _ = Word8ArraySlice.copy {src = Word8ArraySlice.slice (a, 0, SOME sz), dst = a', di = 0}
  in (a', sz) end

fun clone (ref a, cap) = ref (cloneCore (a, cap))

fun ensureCapacity (r as (a, _), cap) =
  if cap <= Word8Array.length a then r else let
    val cap' = Int.max (cap, Word8Array.length a * 3 div 2)
    val cap' = if cap' <= Word8Array.maxLen then cap' else
      if cap <= Word8Array.maxLen then Word8Array.maxLen else raise Overflow
    in cloneCore (r, cap') end

fun push (r as ref (a as (_, sz)), v) = let
  val (a, sz) = ensureCapacity (a, sz + 1)
  val _ = Word8Array.update (a, sz, Byte.charToByte v)
  in r := (a, sz+1) end

fun size (ref (_, sz)) = sz

fun isEmpty a = size a = 0

fun capacity (ref (a, _)) = Word8Array.length a

fun last a = case size a of 0 => NONE | sz => SOME (sub (a, sz-1))

fun setLast (a, v) = update (a, size a - 1, v)

fun array a = #1 (base (clone (a, size a)))

fun fromArray a = ref (a, Word8Array.length a)

fun tabulate (n, f) = fromArray (Word8Array.tabulate (n, Byte.charToByte o f))

type slice = Word8ArraySlice.slice

fun full (ref (a, sz)) = Word8ArraySlice.slice (a, 0, SOME sz)

fun slice (ref (a, sz), i, SOME len) =
    if i+len <= sz then Word8ArraySlice.slice (a, i, SOME len) else raise Subscript
  | slice (ref (a, sz), i, NONE) =
    if i <= sz then Word8ArraySlice.slice (a, i, SOME (sz - i)) else raise Subscript

val extract = Byte.unpackString o slice
fun toString a = extract (a, 0, NONE)

fun copy {src, dst = ref (a, sz), di} =
  if di + Word8ArraySlice.length src > sz then raise Subscript
  else Word8ArraySlice.copy {src = src, dst = a, di = di}

fun copyVec {src, dst = ref (a, sz), di} =
  if di + Word8VectorSlice.length src > sz then raise Subscript
  else Word8ArraySlice.copyVec {src = src, dst = a, di = di}

fun copySubstr {src, dst, di} = let
  val (str, lo, len) = Substring.base src
  val src = Word8VectorSlice.slice (Byte.stringToBytes str, lo, SOME len)
  in copyVec {src = src, dst = dst, di = di} end

fun copyStr {src, dst, di} = copySubstr {src = Substring.full src, dst = dst, di = di}

fun appendSubstr (r as ref (a as (_, sz)), ss) = let
  val (a, sz) = ensureCapacity (a, sz + Substring.size ss)
  val _ = Byte.packString (a, sz, ss)
  in r := (a, sz + Substring.size ss) end

fun appendStr (r, s) = appendSubstr (r, Substring.full s)

fun append (r as ref (a as (_, sz)), v) = (
  r := ensureCapacity (a, sz + Word8ArraySlice.length v);
  Word8ArraySlice.copy {src = v, dst = #1 (!r), di = sz})

fun replace (r, ref a) = r := a

fun fromList a = let
  val cs = ref a
  fun f _ = case !cs of c :: cs' => (cs := cs'; c) | [] => raise Bind
  in tabulate (length a, f) end

fun app f a = Word8ArraySlice.app (f o Byte.byteToChar) (full a)
fun appi f a = Word8ArraySlice.appi (fn (i, a) => f (i, Byte.byteToChar a)) (full a)
fun all f a = Word8ArraySlice.all (f o Byte.byteToChar) (full a)
fun exists f a = Word8ArraySlice.exists (f o Byte.byteToChar) (full a)
fun collate f (a, b) = Word8ArraySlice.collate
  (fn (a, b) => f (Byte.byteToChar a, Byte.byteToChar b)) (full a, full b)
fun find f a = Option.map Byte.byteToChar (Word8ArraySlice.find (f o Byte.byteToChar) (full a))
fun findi f a = Option.map (fn (i, a) => (i, Byte.byteToChar a))
  (Word8ArraySlice.findi (fn (i, a) => f (i, Byte.byteToChar a)) (full a))
fun foldl f b a = Word8ArraySlice.foldl (fn (a, b) => f (Byte.byteToChar a, b)) b (full a)
fun foldli f b a = Word8ArraySlice.foldli (fn (i, a, b) => f (i, Byte.byteToChar a, b)) b (full a)
fun foldr f b a = Word8ArraySlice.foldr (fn (a, b) => f (Byte.byteToChar a, b)) b (full a)
fun foldri f b a = Word8ArraySlice.foldri (fn (i, a, b) => f (i, Byte.byteToChar a, b)) b (full a)
fun modify f a = Word8ArraySlice.modify (Byte.charToByte o f o Byte.byteToChar) (full a)
fun modifyi f a = Word8ArraySlice.modifyi
  (fn (i, a) => Byte.charToByte (f (i, Byte.byteToChar a))) (full a)
fun vector a = Word8ArraySlice.vector (full a)

fun toList a = foldr op:: [] a

end
