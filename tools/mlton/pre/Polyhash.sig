(* Polyhash -- polymorphic hashtables as in the SML/NJ Library *)

signature Polyhash =
sig

type ('key, 'data) hash_table

val mkTable     : ('_key -> int) * ('_key * '_key -> bool) -> int * exn 
                  -> ('_key, '_data) hash_table
val numItems    : ('key, 'data) hash_table -> int
val insert      : ('_key, '_data) hash_table -> '_key * '_data -> unit
val peekInsert  : ('_key, '_data) hash_table -> '_key * '_data 
                  -> '_data option
val find        : ('key, 'data) hash_table -> 'key -> 'data
val peek        : ('key, 'data) hash_table -> 'key -> 'data option
val remove      : ('key, 'data) hash_table -> 'key -> 'data
val listItems   : ('key, 'data) hash_table -> ('key * 'data) list
val apply       : ('key * 'data -> unit) -> ('key, 'data) hash_table -> unit
val map         : ('_key * 'data -> '_res) -> ('_key, 'data) hash_table 
                  -> ('_key, '_res) hash_table
val filter      : ('key * 'data -> bool) -> ('key, 'data) hash_table -> unit
val transform   : ('data -> '_res) -> ('_key, 'data) hash_table 
                  -> ('_key, '_res) hash_table
val copy        : ('_key, '_data) hash_table -> ('_key, '_data) hash_table
val bucketSizes : ('key, 'data) hash_table -> int list

(* Polymorphic hash primitives from Caml Light *)

val hash        : 'key -> int
val hash_param  : int -> int -> 'key -> int
val mkPolyTable : int * exn -> (''_key, '_data) hash_table

(* 
   [('key, 'data) hash_table] is the type of hashtables with keys of type
   'key and data values of type 'data.

   [mkTable (hashVal, sameKey) (sz, exc)] returns a new hashtable,
   using hash function hashVal and equality predicate sameKey.  The sz
   is a size hint, and exc is the exception raised by function find.
   It must be the case that sameKey(k1, k2) implies hashVal(k1) =
   hashVal(k2) for all k1,k2.

   [numItems htbl] is the number of items in the hash table.

   [insert htbl (k, d)] inserts data d for key k.  If k already had an
   item associated with it, then the old item is overwritten.

   [find htbl k] returns d, where d is the data item associated with key k, 
   or raises the exception (given at creation of htbl) if there is no such d.

   [peek htbl k] returns SOME d, where d is the data item associated with 
   key k, or NONE if there is no such d.

   [peekInsert htbl (k, d)] inserts data d for key k, if k is not
   already in the table, returning NONE.  If k is already in the
   table, and the associated data value is d', then returns SOME d'
   and leaves the table unmodified.

   [remove htbl k] returns d, where d is the data item associated with key k, 
   removing d from the table; or raises the exception if there is no such d.

   [listItems htbl] returns a list of the (key, data) pairs in the hashtable.

   [apply f htbl] applies function f to all (key, data) pairs in the 
   hashtable, in some order.

   [map f htbl] returns a new hashtable, whose data items have been
   obtained by applying f to the (key, data) pairs in htbl.  The new
   tables have the same keys, hash function, equality predicate, and
   exception, as htbl.

   [filter p htbl] deletes from htbl all data items which do not
   satisfy predicate p.

   [transform f htbl] as map, but only the (old) data values are used
   when computing the new data values.

   [copy htbl] returns a complete copy of htbl.

   [bucketSizes htbl] returns a list of the sizes of the buckets.
   This is to allow users to gauge the quality of their hashing
   function.  

   [hash k] returns the hash value of k, as a positive integer. If
   k1=k2 then hash(k1) = hash(k2), so this function can be used when
   creating hashtables.  The application hash(k) always terminates,
   even on cyclic structures.  (From the Caml Light implementation).

   [hash_param n m k] computes a hash value for k with the same
   properties as for hash. The parameters n and m give more precise
   control over hashing.  Hashing performs a depth-first,
   right-to-left traversal of the structure k, stopping after n
   meaningful nodes were encountered, or m nodes, meaningful or not,
   were encountered. Meaningful nodes are: integers, floating-point
   numbers, strings, characters, booleans, references, and constant
   constructors. 

   [mkPolyTable (sz, exc)] creates a new hashtable using the
   polymorphic hash function (hash) and ML equality (op =); the integer 
   sz is a size hint and the exception exc is to be raised by find.  
*)

end
