(* Hasht.sml *)

(* Hash tables *)

(* We do dynamic hashing, and we double the size of the table when
   buckets become too long, but without re-hashing the elements. *)

open Array;
infix 9 sub;

datatype ('a, 'b) bucketlist =
    Empty
  | Cons of 'a * int * 'b * ('a, 'b) bucketlist
;

type ('a, 'b) TCell =
  { max_len: int,                      (* max length of a bucket *)
    data: ('a, 'b) bucketlist array }  (* the buckets *)
;

type ('a, 'b) t = ('a, 'b) TCell ref;

fun forup f a b =
  let fun loop i = if i > b then () else (f i; loop (i+1))
  in loop a end
;

fun new initial_size =
  ref { max_len = 3, data = array(initial_size, Empty) }
;

fun clear h =
  let val {data, max_len} = !h in
    forup (fn i => update(data, i, Empty))
      0 (Array.length data - 1)
  end
;

fun resize h =
  let val {data, max_len} = !h
      val len = Array.length data
      val newlen = len+len+1
      val newdata = array(newlen, Empty)
      fun dispatch Empty = ()
        | dispatch (Cons(k, c, v, rest)) =
            let val () = dispatch rest
                val i = c mod newlen
            in update(newdata, i, Cons(k, c, v, newdata sub i)) end
  in
    forup (fn i => dispatch(data sub i)) 0 (len-1);
    h := { data = newdata, max_len = 2 * max_len};
    ()
  end
;

fun bucket_too_long n bucket =
  if n < 0 then true else
  case bucket of
      Empty => false
    | Cons(_, _, _, rest) => bucket_too_long (n-1) rest
;

prim_val hash_param : int -> int -> 'a -> int = 3 "hash_univ_param";

fun hash x = hash_param 50 500 x;

fun insert h key value =
  let val {data, max_len} = !h
      val code = hash_param 10 100 key
      fun insert_bucket Empty =
            Cons(key, code, value, Empty)
        | insert_bucket (Cons(k, c, v, next)) =
            if code = c andalso k = key then
              Cons(key, code, value, next)
            else Cons(k, c, v, insert_bucket next)
      val i = code mod (Array.length data)
      val bucket = insert_bucket (data sub i)
  in
    update(data, i, bucket);
    if bucket_too_long max_len bucket then resize h else ()
  end
;

fun remove h key =
  let val {data, max_len : int} = !h
      val code = hash_param 10 100 key
      fun remove_bucket Empty = Empty
        | remove_bucket (Cons(k, c, v, next)) =
            if code = c andalso k = key then
              next
            else Cons(k, c, v, remove_bucket next)
      val i = code mod (Array.length data)
  in update(data, i, remove_bucket (data sub i)) end
;

fun find h key =
  let val {data, max_len : int} = !h
      val code = (hash_param 10 100 key)
  in
  case data sub (code mod (Array.length data)) of
      Empty => raise Subscript
    | Cons(k1, c1, d1, rest1) =>
        if code = c1 andalso key = k1 then d1 else
        case rest1 of
          Empty => raise Subscript
        | Cons(k2, c2, d2, rest2) =>
            if code = c2 andalso key = k2 then d2 else
            case rest2 of
                Empty => raise Subscript
              | Cons(k3, c3, d3, rest3) =>
                if code = c3 andalso key = k3 then d3 else
                let fun find Empty = raise Subscript
                      | find (Cons(k, c, d, rest)) =
                          if code = c andalso key = k then d else find rest
                in find rest3 end
  end;

fun peek h key =
  let val {data, max_len : int} = !h
      val code = (hash_param 10 100 key)
  in
  case data sub (code mod (Array.length data)) of
      Empty => NONE
    | Cons(k1, c1, d1, rest1) =>
        if code = c1 andalso key = k1 then SOME d1 else
        case rest1 of
          Empty => NONE
        | Cons(k2, c2, d2, rest2) =>
            if code = c2 andalso key = k2 then SOME d2 else
            case rest2 of
                Empty => NONE
              | Cons(k3, c3, d3, rest3) =>
                if code = c3 andalso key = k3 then SOME d3 else
                let fun peek Empty = NONE
                      | peek (Cons(k, c, d, rest)) =
                          if code = c andalso key = k then SOME d 
			  else peek rest
                in peek rest3 end
  end;

fun apply f h =
  let val {data, max_len : int} = !h
      val len = Array.length data
  in
    forup (fn i =>
        let fun scan_bucket Empty = ()
              | scan_bucket (Cons(k, c, d, rest)) =
                  ( f k d : unit; scan_bucket rest )
        in scan_bucket (data sub i) end)
      0 (len - 1)
  end
;

fun fold f e h =
  let val {data, max_len : int} = !h
      fun fold_bucket (Empty, res) = res
	| fold_bucket (Cons(k, c, d, rest), res) = 
	  fold_bucket (rest, f k d res)
  in
      Array.foldl fold_bucket e data 
  end
;
