(* ========================================================================= *)
(* FILE          : mleCombinLibHp.sml                                        *)
(* DESCRIPTION   : Tools for term synthesis on combinator datatype           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinLibHp :> mleCombinLibHp =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory mleCombinLib

val ERR = mk_HOL_ERR "mleCombinLibHp"

(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

datatype pose = Left | Right

fun pose_compare (a,b) = case (a,b) of
    (Left,Right) => LESS
  | (Right,Left) => GREATER
  | _ => EQUAL

fun pose_to_string pose = case pose of 
    Left => "L"
  | Right => "R"

fun string_to_pose s = 
  if s = "L" then Left else if s = "R" then Right else 
    raise ERR "string_to_pose" ""

fun pos_to_string pos = String.concatWith " " (map pose_to_string pos)
fun string_to_pos s = 
  map string_to_pose (String.tokens Char.isSpace s)

val pos_compare = list_compare pose_compare

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

datatype combin = V1 | V2 | V3 | S | K | A of combin * combin 

fun combin_size combin = case combin of
    A (c1,c2) => 1 + combin_size c1 + combin_size c2
  | _ => 1

(* -------------------------------------------------------------------------
   Printing combinators
   ------------------------------------------------------------------------- *)

fun strip_A_aux c = case c of
    A (c1,c2) => c2 :: strip_A_aux c1
  | _ => [c]
fun strip_A c = rev (strip_A_aux c)

fun combin_to_string c = case c of 
    S => "S"
  | K => "K"
  | V1 => "V1"
  | V2 => "V2"
  | V3 => "V3"
  | A _ => "(" ^ String.concatWith " " (map combin_to_string (strip_A c)) ^ ")"

fun combin_compare (c1,c2) = case (c1,c2) of
    (A x, A y) => cpl_compare combin_compare combin_compare (x,y)
  | (_, A _) => LESS
  | (A _,_) => GREATER
  | _ => String.compare (combin_to_string c1, combin_to_string c2)

(* -------------------------------------------------------------------------
   Rewriting combinators
   ------------------------------------------------------------------------- *)

fun next_pos_aux l = case l of
    [] => raise ERR "next_pos" ""
  | Left :: m => Right :: m
  | Right :: m => next_pos_aux m

fun next_pos l = rev (next_pos_aux (rev l))

exception Break

fun hp_nf c = case c of
    A(A(A(S,x),y),z) => false
  | A(A(K,x),y) => false
  | A(c1,c2) => hp_nf c1 andalso hp_nf c2
  | _ => true

fun hp_norm n mainc =
  let
    val i = ref 0
    fun incra () = (incr i; if !i > n then raise Break else ())   
    fun hp_norm_aux n c = 
      case c of
        A(A(A(S,x),y),z) => (incra (); hp_norm_aux n (A(A(x,z),A(y,z))) )  
      | A(A(K,x),y) => (incra (); hp_norm_aux n x)
      | A(c1,c2) => A(hp_norm_aux n c1, hp_norm_aux n c2)  
      | x => x
    fun loop c =
      if hp_nf c then SOME c else loop (hp_norm_aux n c)
  in
    loop mainc handle Break => NONE
  end

(* -------------------------------------------------------------------------
   Generating combinators
   ------------------------------------------------------------------------- *)

fun cterm_to_hp cterm = 
  if term_eq cterm cS then S 
  else if term_eq cterm cK then K
  else if term_eq cterm v1 then V1
  else if term_eq cterm v2 then V2
  else if term_eq cterm v3 then V3
  else let val (a,b) = dest_cA cterm in A (cterm_to_hp a, cterm_to_hp b) end

fun hp_to_cterm c = case c of 
   S => cS | K => cK | V1 => v1 | V2 => v2 | V3 => v3 |
   A (c1,c2) => mk_cA (hp_to_cterm c1, hp_to_cterm c2)

(*
load "aiLib"; open aiLib;
load "mleCombinLib"; open mleCombinLib;
load "mleCombinLibHp"; open mleCombinLibHp;

fun add_varl c = (A(A(A(c,V1),V2),V3));
fun contains_sk c = case c of
    S => true
  | K => true
  | V1 => false
  | V2 => false
  | V3 => false
  | A (c1,c2) => contains_sk c1 orelse contains_sk c2;
fun compare_csize (a,b) = Int.compare (combin_size a, combin_size b);
fun smallest_csize l = hd (dict_sort compare_csize l);

fun find_newex n d =
  if dlength d >= 2200 then (d,n) else
  let 
    val c = cterm_to_hp (random_nf (random_int (1,20)))
    val cnorm = valOf (hp_norm 100 (add_varl c)) handle Option => K 
  in
    if contains_sk cnorm then find_newex (n+1) d 
    else if dmem cnorm d then
      let val oldc = dfind cnorm d in
        if compare_csize (c,oldc) = LESS 
        then find_newex (n+1) (dadd cnorm c d) 
        else find_newex (n+1) d
      end
    else 
      (print_endline (its (dlength d + 1)); 
       find_newex (n+1) (dadd cnorm c d))
  end;

val (dfull,ntry) = find_newex 0 (dempty combin_compare);

val il = map (combin_size o snd) (dlist dfull);
val statsl = dlist (count_dict (dempty Int.compare) 
  (map (fn x => (x + 1) div 2) il));
*)

end (* struct *)

