structure RL_Lib = struct

fun die msg =
  (TextIO.output(TextIO.stdErr, msg);
   TextIO.output(TextIO.stdErr, "\n");
   OS.Process.exit OS.Process.failure)

(* TODO: move? or take from elsewhere? *)
local open boolLib in
fun goal_to_string((asl, w):goal) =
  "[" ^ (String.concatWith "," (List.map term_to_string asl)) ^ "] ?- " ^ (term_to_string w)
end
(* -- *)

(* TODO: move to Lib? *)
fun rotate_list [] = [] | rotate_list (x::xs) = xs @ [x]
fun unrotate_list ls = Lib.uncurry (Lib.C Lib.cons) (Lib.front_last ls)
(*
rotate_list [1,2,3]
unrotate_list [1,2,3]
unrotate_list (rotate_list [1,2,3])
unrotate_list (rotate_list [2])
*)
(* -- *)

end
