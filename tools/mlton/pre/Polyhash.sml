(* Modified for Moscow ML from SML/NJ Library version 0.2
 *
 * COPYRIGHT (c) 1992 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *
 * Original author: John Reppy, AT&T Bell Laboratories, Murray Hill, NJ 07974
 *)

structure Polyhash :> Polyhash =
struct

datatype ('key, 'data) bucket_t
  = NIL
  | B of int * 'key * 'data * ('key, 'data) bucket_t

datatype ('key, 'data) hash_table = 
    HT of {hashVal   : 'key -> int,
	   sameKey   : 'key * 'key -> bool,
	   not_found : exn,
	   table     : ('key, 'data) bucket_t Array.array ref,
	   n_items   : int ref}

local
(*
    prim_val andb_      : int -> int -> int = 2 "and";
    prim_val lshift_    : int -> int -> int = 2 "shift_left";
*)
    fun andb_ x y = Word.toInt (Word.andb (Word.fromInt x, Word.fromInt y));
    fun lshift_ x y = Word.toInt (Word.<< (Word.fromInt x, Word.fromInt y));
in 
    fun index (i, sz) = andb_ i (sz-1)

  (* find smallest power of 2 (>= 32) that is >= n *)
    fun roundUp n = 
	let fun f i = if (i >= n) then i else f (lshift_ i 1)
	in f 32 end
end;

  (* Create a new table; the int is a size hint and the exception
   * is to be raised by find.
   *)
    fun mkTable (hashVal, sameKey) (sizeHint, notFound) = HT{
            hashVal=hashVal,
	    sameKey=sameKey,
	    not_found = notFound,
	    table = ref (Array.array(roundUp sizeHint, NIL)),
	    n_items = ref 0
	  };

  (* conditionally grow a table *)
    fun growTable (HT{table, n_items, ...}) = let
	    val arr = !table
	    val sz = Array.length arr
	    in
	      if (!n_items >= sz)
		then let
		  val newSz = sz+sz
		  val newArr = Array.array (newSz, NIL)
		  fun copy NIL = ()
		    | copy (B(h, key, v, rest)) = let
			val indx = index (h, newSz)
			in
			  Array.update (newArr, indx,
			    B(h, key, v, Array.sub(newArr, indx)));
			  copy rest
			end
		  fun bucket n = (copy (Array.sub(arr, n)); bucket (n+1))
		  in
		    (bucket 0) handle _ => ();
		    table := newArr
		  end
		else ()
	    end (* growTable *);

  (* Insert an item.  If the key already has an item associated with it,
   * then the old item is discarded.
   *)
    fun insert (tbl as HT{hashVal, sameKey, table, n_items, ...}) (key, item) =
	let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = (
		Array.update(arr, indx, B(hash, key, item, Array.sub(arr, indx)));
		n_items := !n_items + 1;
		growTable tbl;
		NIL)
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then B(hash, key, item, r)
		else (case (look r)
		   of NIL => NIL
		    | rest => B(h, k, v, rest)
		  (* end case *))
	  in
	    case (look (Array.sub (arr, indx)))
	     of NIL => ()
	      | b => Array.update(arr, indx, b)
	  end;

  (* Insert an item if not there already; if it is there already, 
     then return the old data value and leave the table unmodified..
   *)
    fun peekInsert (tbl as HT{hashVal, sameKey, table, n_items, ...}) (key, item) =
	let val arr = !table
	    val sz = Array.length arr
	    val hash = hashVal key
	    val indx = index (hash, sz)
	    fun look NIL = 
		(Array.update(arr, indx, B(hash, key, item, 
					   Array.sub(arr, indx)));
		 n_items := !n_items + 1;
		 growTable tbl;
		 NONE)
	      | look (B(h, k, v, r)) = 
		if hash = h andalso sameKey(key, k) then SOME v
		else look r
	in
	    look (Array.sub (arr, indx))
	end;

  (* find an item, the table's exception is raised if the item doesn't exist *)
    fun find (HT{hashVal, sameKey, table, not_found, ...}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = raise not_found
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then v
		else look r
	  in
	    look (Array.sub (arr, indx))
	  end;

  (* look for an item, return NONE if the item doesn't exist *)
    fun peek (HT{hashVal, sameKey, table, ...}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = NONE
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then SOME v
		else look r
	  in
	    look (Array.sub (arr, indx))
	  end;

  (* Remove an item.  The table's exception is raised if
   * the item doesn't exist.
   *)
    fun remove (HT{hashVal, sameKey, not_found, table, n_items}) key = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = raise not_found
	    | look (B(h, k, v, r)) = if ((hash = h) andalso sameKey(key, k))
		then (v, r)
		else let val (item, r') = look r in (item, B(h, k, v, r')) end
	  val (item, bucket) = look (Array.sub (arr, indx))
	  in
	    Array.update (arr, indx, bucket);
	    n_items := !n_items - 1;
	    item
	  end (* remove *);

  (* Return the number of items in the table *)
   fun numItems (HT{n_items, ...}) = !n_items

  (* return a list of the items in the table *)
    fun listItems (HT{table = ref arr, n_items, ...}) = let
	  fun f (_, l, 0) = l
	    | f (~1, l, _) = l
	    | f (i, l, n) = let
		fun g (NIL, l, n) = f (i-1, l, n)
		  | g (B(_, k, v, r), l, n) = g(r, (k, v)::l, n-1)
		in
		  g (Array.sub(arr, i), l, n)
		end
	  in
	    f ((Array.length arr) - 1, [], !n_items)
	  end (* listItems *);

  (* Apply a function to the entries of the table *)
    fun apply f (HT{table, ...}) = let
	  fun appF NIL = ()
	    | appF (B(_, key, item, rest)) = (
		f (key, item);
		appF rest)
	  val arr = !table
	  val sz = Array.length arr
	  fun appToTbl i = if (i < sz)
		then (appF (Array.sub (arr, i)); appToTbl(i+1))
		else ()
	  in
	    appToTbl 0
	  end (* apply *);

  (* Map a table to a new table that has the same keys and exception *)
    fun map f (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  fun mapF NIL = NIL
	    | mapF (B(hash, key, item, rest)) =
		B(hash, key, f (key, item), mapF rest)
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = if (i < sz)
		then (
		  Array.update(newArr, i, mapF (Array.sub(arr, i)));
		  mapTbl (i+1))
		else ()
	  in
	    mapTbl 0;
	    HT{hashVal=hashVal,
	       sameKey=sameKey,
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* transform *);

  (* remove any hash table items that do not satisfy the given
   * predicate.
   *)
    fun filter pred (HT{table, n_items, not_found, ...}) = let
	  fun filterP NIL = NIL
	    | filterP (B(hash, key, item, rest)) = if (pred(key, item))
		then B(hash, key, item, filterP rest)
		else filterP rest
	  val arr = !table
	  val sz = Array.length arr
	  fun filterTbl i = if (i < sz)
		then (
		  Array.update (arr, i, filterP (Array.sub (arr, i)));
		  filterTbl (i+1))
		else ()
	  in
	    filterTbl 0
	  end (* filter *);

  (* Map a table to a new table that has the same keys, exception,
     hash function, and equality function *)

    fun transform f (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  fun mapF NIL = NIL
	    | mapF (B(hash, key, item, rest)) = B(hash, key, f item, mapF rest)
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = if (i < sz)
		then (
		  Array.update(newArr, i, mapF (Array.sub(arr, i)));
		  mapTbl (i+1))
		else ()
	  in
	    mapTbl 0;
	    HT{hashVal=hashVal, 
	       sameKey=sameKey, 
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* transform *);

  (* Create a copy of a hash table *)
    fun copy (HT{hashVal, sameKey, table, n_items, not_found}) = let
	  val arr = !table
	  val sz = Array.length arr
	  val newArr = Array.array (sz, NIL)
	  fun mapTbl i = (
		Array.update (newArr, i, Array.sub(arr, i));
		mapTbl (i+1))
	  in
	    (mapTbl 0) handle _ => ();
	    HT{hashVal=hashVal, 
	       sameKey=sameKey,
	       table = ref newArr, 
	       n_items = ref(!n_items), 
	       not_found = not_found}
	  end (* copy *);

  (* returns a list of the sizes of the various buckets.  This is to
   * allow users to gauge the quality of their hashing function.
   *)
    fun bucketSizes (HT{table = ref arr, ...}) = let
	  fun len (NIL, n) = n
	    | len (B(_, _, _, r), n) = len(r, n+1)
	  fun f (~1, l) = l
	    | f (i, l) = f (i-1, len (Array.sub (arr, i), 0) :: l)
	  in
	    f ((Array.length arr)-1, [])
	  end

(*
prim_val hash_param : int -> int -> 'a -> int = 3 "hash_univ_param";
*)
fun hash_param _ _ _ = 0;

fun hash x = hash_param 50 500 x;

fun mkPolyTable (sizeHint, notFound) = 
     mkTable (hash, op=) (sizeHint, notFound);

end
