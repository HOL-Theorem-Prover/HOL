(****************************************************************************)
(* FILE          : support.sml                                              *)
(* DESCRIPTION   : Miscellaneous supporting definitions for Boyer-Moore     *)
(*                 style prover in HOL.                                     *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 6th June 1991                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 2nd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreSupport =
struct

local

open HolKernel Parse basicHol90Lib Psyntax;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;


fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreSupport",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* forall : ('a -> bool) -> 'a list -> bool                                 *)
(*                                                                          *)
(* Returns true if and only if the predicate is true of all the elements in *)
(* the list.                                                                *)
(*--------------------------------------------------------------------------*)

fun forall p = not o (exists (not o p));

(*--------------------------------------------------------------------------*)
(* find : ('a -> bool) -> 'a list -> 'a                                     *)
(*                                                                          *)
(* Returns the first element of a list which satisfies a predicate.         *)
(*--------------------------------------------------------------------------*)

fun find p [] = failwith "find"
  | find p (x::xs) = if (p x) then x else find p xs;

(*--------------------------------------------------------------------------*)
(* last : 'a list -> 'a                                                     *)
(*                                                                          *)
(* last [x_1,...,x_n] ---> x_n                                              *)
(*--------------------------------------------------------------------------*)

fun last [] = failwith "last"
  | last [x] = x
  | last (_::xs) = last xs;

(*--------------------------------------------------------------------------*)
(* butlast : 'a list -> 'a list                                             *)
(*                                                                          *)
(* butlast [x_1,...,x_n-1,x_n] ---> [x1,...,x_n-1]                          *)
(*--------------------------------------------------------------------------*)

fun butlast [] = failwith "butlast"
  | butlast [_] = []
  | butlast (x::xs) = x::(butlast xs);

(*--------------------------------------------------------------------------*)
(* distinct : ''a list -> bool                                              *)
(*                                                                          *)
(* Checks whether the elements of a list are all distinct.                  *)
(*--------------------------------------------------------------------------*)

fun distinct [] = true
  | distinct (x::xs) = not (mem x xs) andalso distinct xs;

(*--------------------------------------------------------------------------*)
(* chop_list : int -> 'a list -> 'a list * 'a list                          *)
(*                                                                          *)
(* chop_list n [e_1,...,e_n,e_n+1,...,e_n+m] --->                           *)
(* ([e1,...,en],[e_n+1,...,e_n+m])                                          *)
(*--------------------------------------------------------------------------*)

fun chop_list n l =
   if (n <= 0)
   then ([],l)
   else case l
        of [] => failwith "chop_list"
         | x::xs => let val (m,l') = chop_list (n - 1) xs in (x::m,l') end;

(*--------------------------------------------------------------------------*)
(* number_list : 'a list -> ('a * int) list                                 *)
(*                                                                          *)
(* Numbers a list of elements,                                              *)
(* e.g. ["a","b","c"] ---> [("a",1),("b",2),("c",3)].                       *)
(*--------------------------------------------------------------------------*)

fun number_list l =
   let fun number_list' n [] = []
         | number_list' n (x::xs) =
          (x,n)::(number_list' (n + 1) xs)
   in  number_list' 1 l
   end;

(*--------------------------------------------------------------------------*)
(* insert_on_snd : ('a * int) -> ('a * int) list -> ('a * int) list         *)
(*                                                                          *)
(* Insert a numbered element into an ordered list,                          *)
(* e.g. insert_on_snd ("c",3) [("a",1),("b",2),("d",4)] --->                *)
(*      [("a",1),("b",2),("c",3),("d",4)]                                   *)
(*--------------------------------------------------------------------------*)

fun insert_on_snd (x,n) [] = [(x,n)]
  | insert_on_snd (x,n:int) (l as (xn as (_,n'))::xns) =
   if (n < n')
   then (x,n)::l
   else xn::(insert_on_snd (x,n) xns);

(*--------------------------------------------------------------------------*)
(* sort_on_snd : ('a * int) list -> ('a * int) list                         *)
(*                                                                          *)
(* Sort a list of pairs, of which the second component is an integer,       *)
(* e.g. sort_on_snd [("c",3),("d",4),("a",1),("b",2)] --->                  *)
(*      [("a",1), ("b",2), ("c",3), ("d",4)]                                *)
(*--------------------------------------------------------------------------*)

fun sort_on_snd [] = []
  | sort_on_snd (x::xs) = insert_on_snd x (sort_on_snd xs);

(*--------------------------------------------------------------------------*)
(* Discriminator functions for T (true) and F (false)                       *)
(*--------------------------------------------------------------------------*)

val is_T = let val T = (--`T`--) in fn tm => tm = T end
and is_F = let val F = (--`F`--) in fn tm => tm = F end;

(*--------------------------------------------------------------------------*)
(* conj_list : term -> term list                                            *)
(*                                                                          *)
(* Splits a conjunction into conjuncts. Only recursively splits the right   *)
(* conjunct.                                                                *)
(*--------------------------------------------------------------------------*)

fun conj_list tm =
   let val (tm1,tm2) = dest_conj tm
   in  tm1::(conj_list tm2)
   end
   handle HOL_ERR _ => [tm];

(*--------------------------------------------------------------------------*)
(* disj_list : term -> term list                                            *)
(*                                                                          *)
(* Splits a disjunction into disjuncts. Only recursively splits the right   *)
(* disjunct.                                                                *)
(*--------------------------------------------------------------------------*)

fun disj_list tm =
   let val (tm1,tm2) = dest_disj tm
   in  tm1::(disj_list tm2)
   end
   handle HOL_ERR _ => [tm];

(*--------------------------------------------------------------------------*)
(* find_bm_terms : (term -> bool) -> term -> term list                      *)
(*                                                                          *)
(* Function to find all subterms in a term that satisfy a given predicate   *)
(* p, breaking down terms as if they were Boyer-Moore logic expressions.    *)
(* In particular, the operator of a function application is only processed  *)
(* if it is of zero arity, i.e. there are no arguments.                     *)
(*--------------------------------------------------------------------------*)

fun find_bm_terms p tm =
   let fun accum tml p tm =
      let val tml' = if (p tm) then (tm::tml) else tml
      in  let val args = #2 (strip_comb tm)
          in  rev_itlist (fn tm => fn tml => accum tml p tm) args tml'
          end
          handle HOL_ERR _ => tml'
      end
   in  accum [] p tm
   end
   handle HOL_ERR _ => failwith "find_bm_terms";

(*--------------------------------------------------------------------------*)
(* ARGS_CONV : conv -> conv                                                 *)
(*                                                                          *)
(* Applies a conversion to every argument of an application of the form     *)
(* (--`f x1 ... xn`--).                                                     *)
(*--------------------------------------------------------------------------*)

fun ARGS_CONV conv tm =
   (RATOR_CONV (ARGS_CONV conv) THENC RAND_CONV conv) tm
   handle HOL_ERR _ => ALL_CONV tm;

end;

end; (* BoyerMooreSupport *)
