(* ===================================================================== *)
(* FILE          : lib.sml                                               *)
(* DESCRIPTION   : library of useful SML functions.                      *)
(* ===================================================================== *)


structure LiteLib :> LiteLib =
struct


(*---------------------------------------------------------------------
 *               Exceptions
 *--------------------------------------------------------------------*)

open Exception;

(*---------------------------------------------------------------------------
 * Fake for NJSML: it does not use Interrupt anyway so it won't ever 
 * get raised.
 *---------------------------------------------------------------------------*)
(* exception Interrupt;   *)

fun fail() = raise HOL_ERR{message="fail", 
			   origin_function="??",
			   origin_structure="??"};
fun failwith s = raise HOL_ERR{message=s, 
			   origin_function="failwith",
			   origin_structure="??"};

exception Subscript;
exception UNCHANGED;

fun exn_to_string (Exception.HOL_ERR{message,origin_function,...}) = 
    origin_function^" - "^message
  | exn_to_string (Fail s) = "Fail "^s
  | exn_to_string (Portable.Io _) = "Io error"
  | exn_to_string Subscript = "Subscript"
  | exn_to_string UNCHANGED = "UNCHANGED"
  | exn_to_string _ = "<not a HOL_ERR>";
fun STRUCT_ERR s (func,mesg) = 
    raise HOL_ERR{message=mesg, 
		  origin_function=func,
		  origin_structure=s};
fun STRUCT_WRAP s (func,exn) = 
    raise HOL_ERR{message=exn_to_string exn, 
		  origin_function=func,
		  origin_structure=s};


(*---------------------------------------------------------------------
 * delta's implemented by UNCHANGED exception
 *--------------------------------------------------------------------*)

  fun fun_to_qfun f a = 
      let val r = f a 
      in if a = r then raise UNCHANGED else r 
      end;

  fun qfun_to_fun f a = f a handle UNCHANGED => a;
      
  fun app2_qfun (f,g) (a1,a2) =
      let val r1 = f a1 
      in (r1,g a2) handle UNCHANGED => (r1,a2)
      end
      handle UNCHANGED => (a1,g a2);
      
  fun qmap f =
     let fun app [] = raise UNCHANGED
	   | app (h::t) = 
	     let val r1 = f h 
	     in r1::(app t handle UNCHANGED => t)
	     end
	     handle UNCHANGED => h::(app t)
     in app
     end;

(*---------------------------------------------------------------------
 * options
 *--------------------------------------------------------------------*)

fun the (SOME x) = x 
  | the _ = failwith "the: can't take \"the\" of NONE"

fun is_some (SOME x) = true
  | is_some NONE = false

fun is_none NONE = true
  | is_none _ = false;

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e

fun option_app f (SOME x) = SOME (f x)
  | option_app f NONE = NONE;

(*---------------------------------------------------------------------
 * Curry/Uncurry/Combinators
 *--------------------------------------------------------------------*)

fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y


fun A f x = f x
fun B f g x = f (g x)
fun C f x y = f y x
fun I x = x
fun K x y = x
fun S x y z = x z (y z)
fun W f x = f x x;;
infix 3 |>;
fun (x |> f) = f x;
infix thenf orelsef;
fun f thenf g = fn x => g(f x);
fun f orelsef g = (fn x => (f x) handle Interrupt => raise Interrupt 
                                      | _ => (g x));

(*---------------------------------------------------------------------
 * Curried versions of some functions
 * NOTE: ## is the same as Cambridge ML's infix #
 *--------------------------------------------------------------------*)

val append = Lib.append;

infix 3 ##
val op ## = (fn (f,g) => (fn (x,y) => (f x, g y)))

(*---------------------------------------------------------------------
 * Pair operations
 *--------------------------------------------------------------------*)

fun fst (x,_) = x
and snd (_,y) = y

(*---------------------------------------------------------------------
 * 
 *--------------------------------------------------------------------*)

fun can f x = (f x; true) handle Interrupt => raise Interrupt | _ => false

fun assert p x = 
   if (p x) 
   then x
   else failwith "assert: predicate not true"

fun for base top f =
   let fun For i = if (i>top) then [] else f i::For(i+1)
   in For base
   end;

fun for_se base top f =
   let fun For i = if (i>top) then () else (f i; For(i+1))
   in For base
   end;

(*---------------------------------------------------------------------
 * List functions
 *
 * We replace functions in List which return "Empty" or Subscript
 *
 * rotl/rotr
 *
 * We consider it an error to rotate an empty list,  although it is easier to 
 * just make that be an identity operation.
 *--------------------------------------------------------------------*)

open Lib;

fun hd (h::t) = h 
  | hd _ = failwith "hd";
fun tl (h::t) = t 
  | tl _ = failwith "tl";

fun tryfind f = 
   let fun F (h::t) = (f h handle Interrupt => raise Interrupt | _ => F t)
         | F [] = failwith "tryfind: all applications failed"
   in F
   end;

fun foldr f e L =
   let fun it [] = e
         | it (a::rst) = f (a,it rst)
   in it L 
   end;

fun el n l = Portable_List.nth (l,n-1) handle Subscript => failwith "el";

fun map2 f L1 L2 =
   let fun mp2 [] [] L = rev L
         | mp2 (a1::rst1) (a2::rst2) L = mp2 rst1 rst2 (f a1 a2::L)
         | mp2 _ _ _ = failwith "map2: different length lists"
   in mp2 L1 L2 []
   end;

fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L 
   end;

fun itlist2 f L1 L2 base_value =
   let fun it ([],[]) = base_value
         | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
         | it _ = failwith "itlist2: lists of different length"
   in  it (L1,L2)
   end;
fun all p l = itlist (fn h => fn a => a andalso p h) l true;;

fun all2 p l1 l2 = 
    itlist2 (fn h1 => fn h2 => fn a => a andalso p h1 h2) l1 l2 true;;

fun first p =
   let fun oneth (a::rst) = if (p a) then a else oneth rst
         | oneth [] = failwith "first: unsatisfied predicate"
   in oneth
   end;

fun split_after n alist = 
   if (n >= 0)
   then let fun spa 0 (L,R) = (rev L,R)
              | spa _ (_,[]) = failwith "split_after: index bigger than list length"
              | spa n (L,(a::rst)) = spa (n-1) (a::L, rst)
        in spa n ([],alist)
        end
   else failwith "split_after: negative index";

val chop_list = split_after;


fun rev_itlist f =
   let fun rev_it [] base = base
         | rev_it (a::rst) base = rev_it rst (f a base)
   in rev_it
   end;

fun foldl f e L =
   let fun rev_it [] e  = e
         | rev_it (a::rst) e = rev_it rst (f (a,e))
   in rev_it L e
   end;

fun rev_itlist2 f L1 L2 =
   let fun rev_it2 ([],[]) base = base
         | rev_it2 ((a::rst1),(b::rst2)) base = rev_it2 (rst1,rst2) 
                                                        (f a b base)
         | rev_it2 _ _ = failwith "rev_itlist2: lists of different length"
   in rev_it2 (L1,L2)
   end;

fun end_itlist f =
   let fun endit [] = failwith "end_itlist: list too short"
         | endit alist = 
            let val (base::ralist) = rev alist
            in itlist f (rev ralist) base
            end
   in endit
   end;

fun end_foldr f =
   let fun endit [] = failwith "end_foldr: list too short"
         | endit alist = 
            let val (base::ralist) = rev alist
            in foldr f base (rev ralist) 
            end
   in endit
   end;

fun gather p L = itlist (fn x => fn y => if (p x) then x::y else y) L []

val filter = gather;

fun partition p alist = 
   itlist (fn x => fn (L,R) => if (p x) then (x::L, R) else (L, x::R))
          alist ([],[]);

fun zip [] [] = []
  | zip (a::b) (c::d) = (a,c)::(zip b d)
  | zip _ _ = failwith "zip: different length lists"

fun unzip L = itlist (fn (x,y) => fn (l1,l2) => ((x::l1),(y::l2))) L ([],[]);

val combine = Lib.combine
val split = unzip

fun mapfilter f alist = 
   itlist (fn i => fn L => (f i::L) 
	   handle Interrupt => raise Interrupt 
		| _ => L) alist [];


fun front_n_back [] = failwith "front_n_back: empty list"
  | front_n_back L = 
       let val (last::rfront) = rev L
       in (rev rfront, last)
       end;

fun rotl (a::rst) = rst@[a]
  | rotl [] = failwith "rotl: empty list"

fun rotr lst = 
   let val (front,back) = front_n_back lst
   in (back::front)
   end 
   handle _ => failwith "rotr: empty list"


fun replicate (x,n) = 
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl n
   end

fun funpow n f x =
   let fun it (0,res) = res
         | it (n,res) = it (n-1, f res)
   in it(n,x)
   end;

(* A naive merge sort. *)
fun sort p = 
   let fun merge [] [] = []
         | merge a [] = a
         | merge [] a = a
         | merge (one as (a::rst1)) (two as (b::rst2)) = 
                if (p a b) 
                then (a::merge rst1 two)
                else (b::merge one rst2)
       fun pass [] = []
         | pass [a] = [a]
         | pass (a::b::rst) = merge a b::pass rst
       fun srt [] = []
         | srt [a] = a
         | srt L = srt (pass L)
   in
   srt o (map (fn x => [x]))
   end

val int_sort = sort (curry (op <= :int*int->bool));


fun upto (n,m) = 
   if (n > m) then [] else n::(upto (n+1,m));

fun repeat f pty = 
    (repeat f (f pty) 
     handle Interrupt => raise Interrupt 
	  | _ => pty);

(* ------------------------------------------------------------------------- 
 * Like partition, but with short-circuiting for special situation.          
 *
 * ------------------------------------------------------------------------- *)

fun qpartition p m =
  let fun qpartition l =
      if l = m then raise UNCHANGED else
	  case l of
	      [] => raise UNCHANGED
	    | (h::t) => 
		  if p h then
		      let val (yes,no) = qpartition t 
		      in (h::yes,no)
		      end
		  handle UNCHANGED => ([h],t)
		  else
		      let val (yes,no) = qpartition t 
		      in (yes,h::no) 
		      end
  in
      fn l => qpartition l
      handle UNCHANGED => ([],l)
  end;;


(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

fun splitlist dest x =
  let val (l,r) = dest x
      val (ls,res) = splitlist dest r
  in (l::ls,res)
  end 
handle Interrupt => raise Interrupt
     | _ => ([],x);;

fun rev_splitlist dest =
  let fun rsplist ls x =
    let val (l,r) = dest x
    in  rsplist (r::ls) l
    end
    handle Interrupt => raise Interrupt
	 | _ => (x,ls) 
  in fn x => rsplist [] x
  end;;

fun striplist dest =
  let fun strip x acc =
    let val (l,r) = dest x
    in strip l (strip r acc)
    end
    handle Interrupt => raise Interrupt
	 | _ => x::acc
  in fn x => strip x []
  end;;


(*---------------------------------------------------------------------
 * Associative list functions
 *--------------------------------------------------------------------*)

fun assoc item =
   let fun assc ((key,ob)::rst) = if (item = key) then ob else assc rst
         | assc [] = raise Subscript
   in assc
   end

fun rev_assoc item =
   let fun assc ((ob,key)::rst) = (assc rst handle Subscript => 
                                if (item = key) then ob else raise Subscript)
         | assc [] = raise Subscript
   in assc
   end

fun assoc1 item =
   let fun assc ((entry as (key,_))::rst) = 
             if (item = key) then SOME entry else assc rst
         | assc [] = NONE
    in assc
    end;

fun assoc2 item =
   let fun assc((entry as (_,key))::rst) =
            if (item = key) then SOME entry else assc rst
         | assc [] = NONE
   in assc
   end;

fun remove_assoc x =
    let fun remove [] = raise UNCHANGED
	  | remove ((h as (l,r))::t) = if (x = l) then t else (h::remove t)
    in fn l => (remove l handle UNCHANGED => l)
    end;
    
fun add_assoc (x as (l,r)) ll = x::(remove_assoc l ll);

infix 5 |-->
val (op |-->) = I

(*---------------------------------------------------------------------
 * Substitutions (Environments)
 *--------------------------------------------------------------------*)

infix 5 |->
fun a |-> b = (b,a);
fun redex (a ,b) = b;
fun residue (a ,b) = a;


(*---------------------------------------------------------------------
 * Sets implemented as lists, over equality types
 *--------------------------------------------------------------------*)

fun mem i =
   let fun it (a::rst) = (i=a) orelse it rst
         | it [] = false
   in it
   end;
    
fun mk_set [] = []
  | mk_set (a::rst) = if (mem a rst) then mk_set rst else a::mk_set rst;

fun union [] S = S
  | union S [] = S
  | union (a::rst) S2 = 
       if (mem a S2) 
       then (union rst S2)
       else union rst (a::S2);

(* Union of a family of sets *)
fun U set_o_sets = itlist union set_o_sets []

(* All the elements in the first set that are not also in the second set. *)
fun set_diff a b = gather (fn x => not (mem x b)) a
val subtract = set_diff

fun intersect [] _ = []
  | intersect _ [] = []
  | intersect S1 S2 = mk_set(gather (C mem S2) S1)

fun null_intersection _  [] = true
  | null_intersection [] _ = true
  | null_intersection (a::rst) S = 
        if (mem a S) 
        then false
        else (null_intersection rst S)

fun set_eq S1 S2 = (set_diff S1 S2 = []) andalso (set_diff S2 S1 = []);

fun insert x xs = if mem x xs then xs else x :: xs;

fun remove p l =
  case l of
    [] => failwith "remove"
  | (h::t) => if p(h) then (h,t) else
              let val (y,n) = remove p t in (y,h::n) end;;

(*---------------------------------------------------------------------
 * Sets implemented as lists, using given equality function
 *--------------------------------------------------------------------*)

fun op_mem eq i =
   let fun mem [] = false
         | mem (a::b) = eq (i,a) orelse mem b
   in mem
   end;

fun op_union eq =
   let val mem = op_mem eq
       fun un [] [] = []
         | un a []  = a
         | un [] a  = a
         | un (a::b) c = 
             if (mem a c) 
             then un b c
             else a::un b c
   in un
   end;

(* Union of a family of sets *)
fun op_U eq set_o_sets = itlist (op_union eq) set_o_sets [];

fun op_intersect eq a b = 
  let val mem = op_mem eq
      val in_b = C mem b
      fun mk_set [] = []
        | mk_set (a::rst) = if (mem a rst) then mk_set rst else a::mk_set rst
   in mk_set(gather in_b a)
   end;

fun op_insert eq x xs = if op_mem eq x xs then xs else x :: xs;

fun op_set_diff eq a b = 
   let val mem = C (op_mem eq) b
   in filter (not o mem) a
   end


(* ------------------------------------------------------------------------- *)
(* We have "lazy" objects to delay calculation and avoid recalculation.      *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b)Lazysum = Unrealized of (('a ->'b) * 'a) | Realized of ('b);;
type ('a,'b)lazy = ('a,'b)Lazysum ref;

(* fun lazy f x = ref(Unrealized(f,x));; *)
fun lazy f x = ref(Realized (f x));

fun eager y = ref(Realized(y));;

fun eval r =
  case !r of
    Realized(y) => y
  | Unrealized(f,x) => let val y = f(x) in (r := Realized(y); y) end;;

(*-------------------------------------------------------------------
 * String manipulation
 *-------------------------------------------------------------------*)

fun fresh_name s = 
   let val n = ref 0
   in   fn () => (n := !n + 1; s^(int_to_string (!n)))
   end;


fun quote s = "\""^s^"\"";

fun words2 sep string =
    snd (itlist (fn ch => fn (chs,tokl) => 
	           if (ch = sep) 
                   then if (null chs)
                        then ([],tokl)
		        else ([], (implode chs :: tokl))
	           else ((ch::chs), tokl))
                (sep::explode string)
                ([],[]));


fun string_variant slist =
   let fun pass str = if (mem str slist) then pass (str^"'") else str
   in pass 
   end

(*-------------------------------------------------------------------
 * Partial Orders
 *-------------------------------------------------------------------*)

datatype ordering = GREATER | LESS | EQUAL;

fun ord_of_lt lt (x,y) = 
    if lt(x, y) then LESS else if lt(y,x) then GREATER else EQUAL;

fun lt_of_ord ord (x,y) = (ord(x, y) = LESS);
    
fun list_ord order =
   let fun ordered (t1::rst1,t2::rst2) =
         (case (order (t1,t2)) of
	     EQUAL => ordered (rst1,rst2)
	   | x => x)
         | ordered ([],[]) = EQUAL
         | ordered ([],_)  = LESS
         | ordered (_,[])  = GREATER
   in ordered 
   end;


(*-------------------------------------------------------------------
 * From the SMLNJ library.  See COPYRIGHT.smlnj-lib
 *-------------------------------------------------------------------*)

local
val prime = 8388593; (* largest prime less than 2^23 *)
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



end (* struct *)
