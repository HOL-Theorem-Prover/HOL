(* Hasht.sig *)

(* Hash tables and hash functions *)

(* Hash tables are hashed association tables, with in-place modification. *)

type ('a, 'b) t;
        (* The type of hash tables from type ['a] to type ['b]. *)

val new : int -> ('_a, '_b) t;
        (* [new n] creates a new, empty hash table, with initial size [n].
           The table grows as needed, so [n] is just an initial guess.
           Better results are said to be achieved when [n] is a prime
           number. *)

val clear : ('a, 'b) t -> unit;
        (* Empty a hash table. *)

val insert : (''_a, '_b) t -> ''_a -> '_b -> unit;
        (* [insert tbl x y] adds a binding of [x] to [y] in table [tbl].
           The previous binding for [x] is removed (if any). *)

val find : (''a, 'b) t -> ''a -> 'b;
        (* [find tbl x] returns the current binding of [x] in [tbl],
           or raises [Subscript] if no such binding exists. *)

val peek : (''a, 'b) t -> ''a -> 'b option;
        (* [peek tbl x] returns SOME v, where v is the current binding of
           x in tbl, if any; otherwise returns NONE. *)

val remove : (''a, 'b) t -> ''a -> unit;
        (* [remove tbl x] removes the current binding of [x] in [tbl].
           It does nothing if [x] is not bound in [tbl]. *)

val apply : ('a -> 'b -> unit) -> ('a, 'b) t -> unit;
        (* [apply f tbl] applies [f] to all bindings in table [tbl].
           [f] receives the key as first argument, and the associated
           value as second argument. The order in which the bindings
           are passed to [f] is unpredictable. *)

val fold : ('a -> 'b -> 'c -> 'c) -> 'c -> ('a, 'b) t -> 'c
        (* [fold f e tbl] computes f k1 d1 (f k2 d2 (...(f kn dn c)...)) 
           where (k1, d1), (k2, d2), ..., (kn, dn) are the bindings of 
	   tbl in some unpredictable order. *)

(*** The polymorphic hash primitive *)

val hash : 'a -> int;
        (* [hash x] associates a positive integer to any value of
           any type. It is guaranteed that
                if [x = y], then [hash x = hash y].
           Moreover, [hash] always terminates, even on cyclic
           structures. *)

prim_val hash_param : int -> int -> 'a -> int = 3 "hash_univ_param";
        (* [hash_param n m x] computes a hash value for [x], with the
           same properties as for [hash]. The two extra parameters
           [n] and [m] give more precise control over hashing.
           Hashing performs a depth-first, right-to-left traversal of
           the structure [x], stopping after [n] meaningful nodes
           were encountered, or [m] nodes, meaningful or not, were
           encountered. Meaningful nodes are: integers;
           floating-point numbers; strings; characters; booleans; and
           constant constructors. Larger values of [m] and [n] means
           that more nodes are taken into account to compute the
           final hash value, and therefore collisions are less likely
           to happen.  However, hashing takes longer. The parameters
           [m] and [n] govern the tradeoff between accuracy and
           speed. *)
