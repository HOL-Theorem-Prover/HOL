(*============================================================================
 * $Id$
 *
 * Symbol tables.  Implementation is based on hash tables.
 *==========================================================================*)

structure Termtable :> Termtable =
struct
type term = Term.term

(*-------------------------------------------------------------------
 * From the SMLNJ library.  See COPYRIGHT.smlnj-lib
 *-------------------------------------------------------------------*)

local val prime = 8388593; (* largest prime less than 2^23 *)
      val ordof = Lib.ordof
in
fun hash_string str =
    let val l = size str
    in
      case l
        of 0 => 0
         | 1 => ordof (str,0)
         | 2 => ordof(str,0) + 128 * (ordof(str, 1))
         | 3 => ordof(str,0) + 128 * ((ordof(str, 1) + 128 * (ordof(str, 2))))
         | _ => let
            fun loop (0,n) = n
              | loop (i,n) =
                  let val i = i-1
                      val n' = ((128 * n) + ordof(str,i)) 
                  in loop (i, (n' - prime * (n' div prime)))
                  end
            in
              loop (l,0)
            end
    end;
end;          

local open Array Lib Term liteLib Psyntax
      type hash_key = (term list * term)
      val prime = 8388593; (* largest prime less than 2^23 *)
      fun hash_term t = 
	if is_var t then hash_string(fst(dest_var t))
	else if is_const t 
             then (hash_string(fst(dest_const t)) + 100021) mod prime
             else if is_comb t then (hash_term (rator t) * 67 
                                     + hash_term (rand t)) mod prime
	     else if is_abs t then (hash_term (bvar t) * 7 
                                    + hash_term (body t)) mod prime
	     else failwith "hash_term"
    fun hashVal (tl,t) =
       hash_term t + 
       foldr (fn (x,t) => 2 * hash_term x + t) 0 tl;
    val sameKey = (op =) : ((term list * term) * (term list * term)) -> bool
    datatype 'a bucket_t
      = NIL
      | B of (int * hash_key * 'a * 'a bucket_t)

    datatype 'a hash_table = HT of {
	not_found : exn,
	table : 'a bucket_t array ref,
	n_items : int ref
      }
    fun index (i, sz) = (i:int) mod sz;  (* Bits.andb(i, sz-1) *)
  (* find smallest power of 2 (>= 32) that is >= n *)
    fun roundUp n = let
	  fun f i = if (i >= n) then i else f (i * 2) (* (Bits.lshift (i,1)) *)
	  in
	    f 32
	  end

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
		    (bucket 0) handle Subscript => ();
		    table := newArr
		  end
		else ()
	    end (* growTable *)
in
   type 'a termtable = 'a hash_table;


  (* Create a new table; the int is a size hint and the exception
   * is to be raised by find.
   *)
    fun mk_termtable (sizeHint, notFound) = HT{
	    not_found = notFound,
	    table = ref (Array.array(roundUp sizeHint, NIL)),
	    n_items = ref 0
	  }


  (* Insert an item.  If the key already has an item associated with it,
   * then the old item is discarded.
   *)
    fun termtable_insert (tbl as HT{table, n_items, ...}) (key, item) = let
	  val arr = !table
	  val sz = Array.length arr
	  val hash = hashVal key
	  val indx = index (hash, sz)
	  fun look NIL = (
              Array.update(arr, indx, B(hash, key, item, Array.sub(arr,indx)));
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
	  end

  (* find an item, the table's exception is raised if the item doesn't exist *)
    fun termtable_find (HT{table, not_found, ...}) key = let
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
	  end

  (* return a list of the items in the table *)
    fun termtable_list (HT{table = ref arr, n_items, ...}) = let
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
	  end (* listItems *)

end (* local *)

end (* struct *)
