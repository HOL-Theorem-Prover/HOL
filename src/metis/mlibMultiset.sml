(* ========================================================================= *)
(* A MULTISET DATATYPE FOR ML                                                *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

(*
List.app load ["Binarymap", "mlibUseful"];
*)

(*
*)
structure mlibMultiset :> mlibMultiset =
struct

structure M = Binarymap; local open Binarymap in end;

fun Mpurge m k = let val (m, _) = M.remove (m, k) in m end;

fun Mall p =
  let
    exception Cut
    fun f (x, y, ()) = if p (x, y) then () else raise Cut
  in
    fn a => (M.foldl f () a; true) handle Cut => false
  end;

type 'a mset = ('a, int) M.dict;

fun empty ord : 'a mset = M.mkDict ord;

fun insert (_, 0) a = a
  | insert (x, n) a =
  (case M.peek (a, x) of NONE => M.insert (a, x, n)
   | SOME n' =>
   let val n'' = n + n'
   in if n'' = 0 then Mpurge a x else M.insert (a, x, n'')
   end);

fun count m x = case M.peek (m, x) of SOME n => n | NONE => 0;

local fun un a b = M.foldl (fn (x : 'a, n : int, d) => insert (x, n) d) a b;
in fun union a b = if M.numItems a < M.numItems b then un b a else un a b;
end;

fun compl a : 'a mset = M.transform ~ a;

fun subtract a b = union a (compl b);

local
  fun sign a = (Mall (fn (_, n) => 0 <= n) a, Mall (fn (_, n) => n <= 0) a);
in
  fun compare (a, b) =
    (case sign (subtract a b) of (true, true) => SOME EQUAL
     | (true, false) => SOME GREATER
     | (false, true) => SOME LESS
     | (false, false) => NONE);
end;

fun subset a b =
  (case compare (a, b) of SOME LESS => true
   | SOME EQUAL => true
   | _ => false);

fun app f (a : 'a mset) = M.app f a;

fun to_list (a : 'a mset) = M.listItems a;

local
  open mlibUseful;
in
  fun pp_mset pp_a =
    pp_map (map mlibUseful.|-> o to_list)
    (pp_bracket ("M[", "]") (pp_sequence "," (mlibUseful.pp_maplet pp_a pp_int)));
end;

end
