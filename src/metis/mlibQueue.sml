(* ========================================================================= *)
(* A QUEUE DATATYPE FOR ML                                                   *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

structure mlibQueue :> mlibQueue =
struct

type 'a queue = 'a list * 'a list;

val empty : 'a queue = ([], []);

fun norm ([], ys as _ :: _) = (rev ys, [])
  | norm q = q;

fun add z (xs, ys) = norm (xs, z :: ys);

fun is_empty ([], _) = true
  | is_empty (_ :: _, _) = false;

fun hd ([], _) = raise Empty
  | hd (x :: _, _) = x;

fun tl ([], _) = raise Empty
  | tl (_ :: xs, ys) = norm (xs, ys);

val length = fn (xs, ys) => length xs + length ys;

fun from_list l = (rev l, []);

fun to_list (xs, ys) = xs @ rev ys;

local
  open mlibUseful;
in
  fun pp_queue pp_a =
    pp_map to_list (pp_bracket ("Q[", "]") (pp_sequence "," pp_a));
end;

end