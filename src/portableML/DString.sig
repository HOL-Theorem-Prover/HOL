signature DString = sig

type dstring

type array = Word8Array.array

(* `new n` constructs a new array with capacity `n` *)
val new: int -> dstring

(* Returns the underlying array and the size *)
val base: dstring -> array * int

(* Empty the array without deallocating *)
val clear: dstring -> unit

(* a[i] *)
val sub: dstring * int -> char

(* a[i] := v *)
val update: dstring * int * char -> unit

(* `clone (a, n)` creates a copy of `a` with capacity `n` *)
val clone: dstring * int -> dstring

(* `push (a, v)` adds an element at the end of the array, growing if needed *)
val push: dstring * char -> unit

(* `size a` returns the number of stored elements *)
val size: dstring -> int

(* `capacity a` returns the size of the underlying allocation *)
val capacity: dstring -> int

(* returns `size a = 0` *)
val isEmpty: dstring -> bool

(* `last a` returns the last element, or NONE if empty *)
val last: dstring -> char option

(* `setLast (a, v)` sets the last element (raises Subscript on empty) *)
val setLast: dstring * char -> unit

type slice = Word8ArraySlice.slice

(* Constructs an array slice out of a dstring (without copying) *)
val slice: dstring * int * int option -> slice

(* Constructs a string from a slice of a dstring *)
val extract: dstring * int * int option -> string

(* Constructs an array slice out of a darray *)
val full: dstring -> slice

(* Block copy of an array slice into `dst` starting at position `di` *)
val copy: {src: slice, dst: dstring, di: int} -> unit

(* Block copy of a vector slice into `dst` starting at position `di` *)
val copyVec: {src: Word8VectorSlice.slice, dst: dstring, di: int} -> unit

(* Block copy of a substring into `dst` starting at position `di` *)
val copySubstr: {src: substring, dst: dstring, di: int} -> unit

(* Block copy of a substring into `dst` starting at position `di` *)
val copyStr: {src: string, dst: dstring, di: int} -> unit

(* Append a slice to the end of a darray *)
val append: dstring * slice -> unit

(* `appendSubstr (a, ss)` appends a substring to the end of the array, growing if needed *)
val appendSubstr: dstring * substring -> unit

(* `appendStr (a, s)` appends a string to the end of the array, growing if needed *)
val appendStr: dstring * string -> unit

(* `replace (a, a')` sets `a` to be an alias of `a'`, i.e. `a := !a'`. *)
val replace: dstring * dstring -> unit

(* runs `f(a[i])` for each `i` *)
val app: (char -> unit) -> dstring -> unit

(* runs `f(i, a[i])` for each `i` *)
val appi: (int * char -> unit) -> dstring -> unit

(* True if all elements in the darray are true *)
val all: (char -> bool) -> dstring -> bool

(* True if any element in the darray is true *)
val exists: (char -> bool) -> dstring -> bool

(* compare two arrays *)
val collate: (char * char -> order) -> dstring * dstring -> order

(* returns the first `a[i]` for which `f a[i]` is true *)
val find: (char -> bool) -> dstring -> char option

(* returns the first `(i, a[i])` for which `f (i, a[i])` is true *)
val findi: (int * char -> bool) -> dstring -> (int * char) option

(* returns `f(a[n-1], ..., f(a[0], b))` *)
val foldl: (char * 'b -> 'b) -> 'b -> dstring -> 'b

(* returns `f(n-1, a[n-1], ..., f(0, a[0], b))` *)
val foldli: (int * char * 'b -> 'b) -> 'b -> dstring -> 'b

(* returns `f(a[0], ..., f(a[n-1], b))` *)
val foldr: (char * 'b -> 'b) -> 'b -> dstring -> 'b

(* returns `f(0, a[0], ..., f(n-1, a[n-1], b))` *)
val foldri: (int * char * 'b -> 'b) -> 'b -> dstring -> 'b

(* applies `f` to every element of the array *)
val modify: (char -> char) -> dstring -> unit

(* applies `f` to every element of the array *)
val modifyi: (int * char -> char) -> dstring -> unit

(* copies the dstring into a new array *)
val array: dstring -> array

(* copies the dstring into a new vector *)
val vector: dstring -> Word8Vector.vector

(* Constructs a new dstring wrapping the given array without copying *)
val fromArray: array -> dstring

(* Constructs a dstring from a list *)
val fromList: char list -> dstring

(* Make a char list from a dstring *)
val toList: dstring -> char list

(* Make a string from a dstring *)
val toString: dstring -> string

(* Constructs a darray of length `n` with `a[i] = f i` (with given default element) *)
val tabulate: int * (int -> char) -> dstring

end
