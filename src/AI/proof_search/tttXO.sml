(* ========================================================================== *)
(* FILE          : tttXO.sml                                                  *)
(* DESCRIPTION   : MCTS example                                        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttXO :> tttXO =
struct

open HolKernel Abbrev boolLib tttTools tttMCTS

val ERR = mk_HOL_ERR "tttXO"

(*
  ---------------------------------------------------------------------------
  tic-tac-toe: endcheck
  --------------------------------------------------------------------------- *)

val tic_startpos = (true,SOME [0,0,0,0,0,0,0,0,0])

val indexwin = 
  [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]]
(* [0,5,7],[2,3,7],[6,1,5],[8,1,3] *)

fun is_halfwin n board = 
  let 
    fun f i x = if x = n then SOME i else NONE
    val posn = List.mapPartial I (mapi f board)
  in
    exists (fn x => subset x posn) indexwin
  end

fun tic_is_win (player1, boardo) = 
  case boardo of
    NONE     => player1
  | SOME board => is_halfwin 1 board

fun tic_is_lose (player1, boardo) =
  case boardo of
    NONE       => not player1
  | SOME board => is_halfwin 2 board orelse all (fn x => x <> 0) board

fun tic_endcheck r =
  if tic_is_win r then Win else if tic_is_lose r then Lose else InProgress

(*
  ---------------------------------------------------------------------------
  tic-tac-toe: makes a move
  --------------------------------------------------------------------------- *)

fun tic_apply_move move pos =
  let 
    val (ps,moves) = split_string "." move 
    val movei = string_to_int moves
    val pn = string_to_int ps
    val (player, board) = (fst pos, valOf (snd pos))
  in 
    if List.nth (board, movei) <> 0 then (not player, NONE) else 
      let fun f i x = if i = movei then pn else x in 
        (not player, SOME (mapi f board))
      end
  end
  handle _ => raise ERR "tic_apply_move" ""

(*
  ---------------------------------------------------------------------------
  tic-tac-toe: evalpoli
  --------------------------------------------------------------------------- *)

val p1movel = map (fn x => "1." ^ int_to_string x) [0,1,2,3,4,5,6,7,8]
val p2movel = map (fn x => "2." ^ int_to_string x) [0,1,2,3,4,5,6,7,8]

fun tic_randplayer movel pid pos =
  let 
    val (eval,prepoli) = rand_evalpoli movel pos 
    val poli = combine (movel, prepoli)
  in
    (
    if tic_is_win pos then 1.0 else 
    if tic_is_lose pos then 0.0 else 
    eval, 
    wrap_poli pid poli
    )
  end

fun tic_build_evalpoli pid pos = case pos of
    (true,NONE)     => (1.0,[]) 
  | (false,NONE)    => (0.0,[]) 
  | (false, SOME l) => tic_randplayer p2movel pid pos
  | (true, SOME l)  => tic_randplayer p1movel pid pos

(*
  ---------------------------------------------------------------------------
  tic-tac-toe: user output
  --------------------------------------------------------------------------- *)

fun string_of_piecei l (i,a) =
  if a = 1 then " X " else if a = 2 then " O " else 
  let val r = approx 0 (List.nth (l,i) * 1000.0) in
    (if r < 10.0 then "0" else "") ^
    (if r < 100.0 then "0" else "") ^
    fst (split_string "." (Real.toString r))
  end
  handle Subscript => "   "

fun string_of_boardi l x = case x of [a,b,c,d,e,f,g,h,i] => 
  "\n  -----------\n" ^ 
  "  " ^ String.concatWith " " (map (string_of_piecei l) [a,b,c]) ^ "\n\n" ^ 
  "  " ^ String.concatWith " " (map (string_of_piecei l) [d,e,f]) ^ "\n\n" ^
  "  " ^ String.concatWith " " (map (string_of_piecei l) [g,h,i]) ^ "\n" ^
  "  " ^ "-----------"
  | _ => raise ERR "" ""

fun heatmap_of_node (node: int node) =
  case snd (#pos node) of
    NONE => "---"
  | SOME board => 
    string_of_boardi (map (snd o fst) (!(#value node))) (number_list 0 board)

end (* struct *)

(*
load "tttMCTS"; load "tic_tac_toe";
open tttMCTS; open tttTools;

val nsim = 1000000;

val tree = 
  mcts nsim tic_build_evalpoli tic_endcheck tic_apply_move tic_startpos;

val _ = update_value tree;
val nodel = principal_variation tree;
print_endline (String.concatWith "\n" (map heatmap_of_node nodel));
*)
