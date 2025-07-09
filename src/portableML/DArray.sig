signature DArray = sig

type 'a darray

(* `new (n, a)` constructs a new array with capacity `n` and default value `a`
   (the value `a` will not be visible) *)
val new: int * 'a -> 'a darray

(* Returns the underlying array, the size, and the default element *)
val base: 'a darray -> 'a array * int * 'a

(* Empty the array without deallocating *)
val clear: 'a darray -> unit

(* a[i] *)
val sub: 'a darray * int -> 'a

(* a[i] := v *)
val update: 'a darray * int * 'a -> unit

(* `clone (a, n)` creates a copy of `a` with capacity `n` *)
val clone: 'a darray * int -> 'a darray

(* `push (a, v)` adds an element at the end of the array, growing if needed *)
val push: 'a darray * 'a -> unit

(* `size a` returns the number of stored elements *)
val size: 'a darray -> int

(* `capacity a` returns the size of the underlying allocation *)
val capacity: 'a darray -> int

(* returns `size a = 0` *)
val isEmpty: 'a darray -> bool

(* `last a` returns the last element, or NONE if empty *)
val last: 'a darray -> 'a option

(* `setLast (a, v)` sets the last element (raises Subscript on empty) *)
val setLast: 'a darray * 'a -> unit

type 'a slice = 'a ArraySlice.slice
(* Constructs an array slice out of a darray *)
val slice: 'a darray * int * int option -> 'a slice

(* Constructs an array slice out of a darray *)
val full: 'a darray -> 'a slice

(* Block copy of an array slice into `dst` starting at position `di` *)
val copy: {src: 'a slice, dst: 'a darray, di: int} -> unit

(* Block copy of a vector slice into `dst` starting at position `di` *)
val copyVec: {src: 'a VectorSlice.slice, dst: 'a darray, di: int} -> unit

(* Append a slice to the end of a darray *)
val append: 'a darray * 'a slice -> unit

(* `replace (a, a')` sets `a` to be an alias of `a'`, i.e. `a := !a'`. *)
val replace: 'a darray * 'a darray -> unit

(* runs `f(a[i])` for each `i` *)
val app: ('a -> unit) -> 'a darray -> unit

(* runs `f(i, a[i])` for each `i` *)
val appi: (int * 'a -> unit) -> 'a darray -> unit

(* True if all elements in the darray are true *)
val all: ('a -> bool) -> 'a darray -> bool

(* True if any element in the darray is true *)
val exists: ('a -> bool) -> 'a darray -> bool

(* compare two arrays *)
val collate: ('a * 'a -> order) -> 'a darray * 'a darray -> order

(* returns the first `a[i]` for which `f a[i]` is true *)
val find: ('a -> bool) -> 'a darray -> 'a option

(* returns the first `(i, a[i])` for which `f (i, a[i])` is true *)
val findi: (int * 'a -> bool) -> 'a darray -> (int * 'a) option

(* returns `f(a[n-1], ..., f(a[0], b))` *)
val foldl: ('a * 'b -> 'b) -> 'b -> 'a darray -> 'b

(* returns `f(n-1, a[n-1], ..., f(0, a[0], b))` *)
val foldli: (int * 'a * 'b -> 'b) -> 'b -> 'a darray -> 'b

(* returns `f(a[0], ..., f(a[n-1], b))` *)
val foldr: ('a * 'b -> 'b) -> 'b -> 'a darray -> 'b

(* returns `f(0, a[0], ..., f(n-1, a[n-1], b))` *)
val foldri: (int * 'a * 'b -> 'b) -> 'b -> 'a darray -> 'b

(* applies `f` to every element of the array *)
val modify: ('a -> 'a) -> 'a darray -> unit

(* applies `f` to every element of the array *)
val modifyi: (int * 'a -> 'a) -> 'a darray -> unit

(* copies the darray into a new array *)
val array: 'a darray -> 'a array

(* copies the darray into a new vector *)
val vector: 'a darray -> 'a vector

(* Constructs a new darray wrapping the given array without copying (with given default element) *)
val fromArray: 'a array * 'a -> 'a darray

(* Constructs a new darray wrapping the given array without copying. Fails if the array is empty *)
val fromArray1: 'a array -> 'a darray

(* Constructs a darray from a list (with given default element) *)
val fromList: 'a list * 'a -> 'a darray

(* Constructs a darray from a nonempty list *)
val fromList1: 'a list -> 'a darray

(* Constructs a darray of length `n` with `a[i] = f i` (with given default element) *)
val tabulate: 'a * int * (int -> 'a) -> 'a darray

end
