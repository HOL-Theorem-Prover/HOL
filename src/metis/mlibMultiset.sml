(* ========================================================================= *)
(* A MULTISET DATATYPE FOR ML                                                *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
List.app load ["Binarymap", "mlibUseful"];
*)

(*
*)
structure mlibMultiset :> mlibMultiset =
struct

structure M = Binarymap; local open Binarymap in end;

fun Mpurge m k = let val (m,_) = M.remove (m,k) in m end;

fun Mall p =
  let
    exception Cut
    fun f (x,y,()) = if p (x,y) then () else raise Cut
  in
    fn a => (M.foldl f () a; true) handle Cut => false
  end;

type 'a mset = ('a,int) M.dict;

fun empty ord : 'a mset = M.mkDict ord;

fun insert (_,0) a = a
  | insert (x,n) a =
  (case M.peek (a,x) of NONE => M.insert (a,x,n)
   | SOME n' =>
   let val n'' = n + n'
   in if n'' = 0 then Mpurge a x else M.insert (a,x,n'')
   end);

fun count m x = case M.peek (m,x) of SOME n => n | NONE => 0;

local fun un a b = M.foldl (fn (x : 'a,n : int,d) => insert (x,n) d) a b;
in fun union a b = if M.numItems a < M.numItems b then un b a else un a b;
end;

fun compl a : 'a mset = M.transform ~ a;

fun subtract a b = if M.numItems b = 0 then a else union a (compl b);

fun sign a =
  case (Mall (fn (_,n) => 0 <= n) a, Mall (fn (_,n) => n <= 0) a) of
    (true,true) => SOME EQUAL
  | (true,false) => SOME GREATER
  | (false,true) => SOME LESS
  | (false,false) => NONE;

fun compare (a,b) = sign (subtract a b);

fun subset a b =
  (case compare (a,b) of SOME LESS => true
   | SOME EQUAL => true
   | _ => false);

fun equal a b = (case compare (a,b) of SOME EQUAL => true | _ => false);

fun app f (a : 'a mset) = M.app f a;

fun foldl f x (a : 'a mset) = M.foldl f x a;

fun foldr f x (a : 'a mset) = M.foldr f x a;

(* "Unguarded type variables at the top level"
   prevents this function being implemented :-(
local
  exception foundit of 'a;
in
  fun find p m =
    (M.app (fn x => if p x then raise foundit x else ()) m; NONE)
    handle foundit x => SOME x;
end;
*)

local
  exception existing;
in
  fun exists p m =
    (M.app (fn x => if p x then raise existing else ()) m; false)
    handle existing => true;
end;

fun all p m = not (exists (not o p) m);

fun nonzero (a : 'a mset) = M.numItems a;

fun to_list (a : 'a mset) = M.listItems a;

local
  open mlibUseful;
in
  fun pp_mset pp_a =
    pp_map (map mlibUseful.|-> o to_list)
    (pp_bracket "M[" "]" (pp_sequence "," (mlibUseful.pp_maplet pp_a pp_int)));
end;

val map = M.map;

end
