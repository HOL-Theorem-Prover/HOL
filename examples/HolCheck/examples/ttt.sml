

(********************************************************************************************************)
(* Tic-tac-toe or naughts-and-crosses                                                                   *)
(*                                                                                                      *)
(* State vars are m (A has just moved), ui_j (A has claimed grid square (i,j), vi_j (ditto for B)       *)
(*                                                                                                      *)
(* This example is mainly for testing algorithms on an interleaved transition system. It is also the    *)
(* simplest example (other than the mod8 counter toy example).                                          *)
(*                                                                                                      *)
(********************************************************************************************************)

(* usage example (start hol including the HolCheck/examples directory, using the -I command line option)

val _ = app load ["holCheckLib","ttt"];
(*val _ = set_trace "HolCheckDBGLZ" 0; val _ = set_trace "HolCheckDBG" 0;
val _ = set_trace "HolCheckPRF" 0; val _ = set_trace "HolCheckLZ" 1; *)
val ttt1 = ttt.makeTTT 1; (* n=1 gives more interesting results. Most props fail for n=3 and can't get traces *)
val ttt2 = holCheckLib.holCheck ttt1 handle ex => Raise ex;
val ttt3 = holCheckLib.prove_model ttt2;
val res = holCheckLib.get_results ttt3;

*)

structure ttt =

struct

local

open Globals HolKernel Parse
open Array2 ListPair bossLib simpLib Binarymap pairSyntax boolSyntax stringLib
open ctlTheory ctlSyntax commonTools holCheckLib

in

(* n is size of grid *)
fun makeTTT n =
  let
    val am = Array2.tabulate Array2.RowMajor (n,n,(fn (x,y) => "u"^Int.toString(x)^"_"^Int.toString(y)))
    val bm = Array2.tabulate Array2.RowMajor (n,n,(fn (x,y) => "v"^Int.toString(x)^"_"^Int.toString(y)))
    val am' = Array2.array(n,n,"")
    val bm' = Array2.array(n,n,"")
    val _ =  Array2.copy {src=({base=am,row=0,col=0,nrows=NONE,ncols=NONE}),dst=am',dst_row=0,dst_col=0}
    val _ = Array2.copy {src=({base=bm,row=0,col=0,nrows=NONE,ncols=NONE}),dst=bm',dst_row=0,dst_col=0}
    val _ = Array2.modify Array2.RowMajor (fn s => s^"'") am'
    val _ = Array2.modify Array2.RowMajor (fn s => s^"'") bm'
    val lam = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] am
    val lbm = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] bm
    val lam' = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] am'
    val lbm' = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] bm'

    (* Good variable order is V01 < v01' < v02 < v02' ...                        *)
    (* Function shuffle below used to create it                                  *)

    fun shuffle (l1,l2) =
     ListPair.foldr (fn(x1,x2,l) => x1 :: x2 :: l) [] (l1,l2);

    val bvm = ["m","m'"]@(shuffle(lam @ lbm, lam' @ lbm'));

    (* Finishing condition *)

    fun bwin pm pl =
    let
      val r = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.row(pm,x))) (List.tabulate (n, (fn x => x)))
      val c = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.column(pm,x))) (List.tabulate (n, (fn x => x)))
      val d1 = List.foldr (fn ((h1,h2),t) => if h1=h2 then h1::t else t) []
			  (ListPair.zip((List.foldr (fn (h,t) => h @ t) [] r),
					(List.foldr (fn (h,t) => h @ t) [] c)))
      val d2 = List.foldr (fn ((h1,h2),t) => if h1=h2 then h1::t else t) []
	  (ListPair.zip((List.foldr (fn (h,t) => h @ t) [] r),
			(List.rev(List.foldr (fn (h,t) => h @ t) [] c))))
      val aps = List.map (fn l => List.map (fn v => mk_bool_var v) l) (d1::d2::(r @ c))
      val wn = list_mk_disj (List.map list_mk_conj aps)
      val mv = if (pl=0) then (mk_neg(mk_bool_var "m")) else (mk_bool_var "m");
    in
      mk_conj(mv, wn)
    end;

    (* Note: fin is used only in making the moves. A draw is accounted for automatically because no moves are available *)
    val fin = mk_disj(bwin am 0,bwin bm 1);

    (* Initial state *)

    val I1 = list_mk_conj(List.map (fn v => if v="m" then (mk_bool_var v) else mk_neg(mk_bool_var v)) (lam @ lbm @ ["m"]))

    (* Function to create a relation to represent a move in which a 'o' or an 'x'    *)
    (* is placed at x which must have been unoccupied      		             *)
    fun make_move_trans (x) =
     let
     	val (_,unchanged) = List.partition (fn v => mem v [x]) (lam @ lbm);
     	val cp = if (String.compare(String.substring(x,0,1),"u")=EQUAL)
     			then (String.concat ["v", String.substring(x,1,String.size(x)-1)])
     			else (String.concat ["u", String.substring(x,1,String.size(x)-1)])
     in
     list_mk_conj
      ([mk_neg(mk_bool_var x),
        mk_neg(mk_bool_var cp),
        (if (mem x lam) then mk_bool_var "m" else mk_neg(mk_bool_var "m")),
        mk_neg(fin),
        mk_primed_bool_var x,
        (if (mem x lam) then mk_neg(mk_primed_bool_var "m") else mk_primed_bool_var "m")]
       @
       (List.map (fn v => mk_eq(mk_primed_bool_var v,mk_bool_var v)) unchanged))
     end;

    (* List of all possible moves *)
    val moves = lam @ lbm;

    (* Define transition relation as disjunction of all moves *)
    (*val R1 = list_mk_disj(List.map make_move_trans moves)*)
    val T1 = List.map (fn v => (v,(make_move_trans v))) moves;

    (* Properties for players A and B, as ctl formulae *)
    infixr 5 C_AND infixr 5 C_OR infixr 2 C_IMP infix C_IFF;
    val state = mk_state I1 T1
    fun ttt_AP s = C_AP state (mk_bool_var s)
    fun win pm pl =
    let
      val r = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.row(pm,x))) (List.tabulate (n, (fn x => x)))
      val c = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.column(pm,x))) (List.tabulate (n, (fn x => x)))
      val d1 = List.foldr (fn ((h1,h2),t) => if h1=h2 then h1::t else t) []
		(ListPair.zip((List.foldr (fn (h,t) => h @ t) [] r),(List.foldr (fn (h,t) => h @ t) [] c)))
      val d2 = List.foldr (fn ((h1,h2),t) => if h1=h2 then h1::t else t) []
		(ListPair.zip((List.foldr (fn (h,t) => h @ t) [] r),(List.rev(List.foldr (fn (h,t) => h @ t) [] c))))
      val aps = List.map (fn l => List.map (fn v => ttt_AP v) l) (d1::d2::(r @ c))
      val wn = list_C_OR (List.map list_C_AND aps)
      val mv = if (pl=0) then C_NOT(ttt_AP "m") else ttt_AP "m";
    in
       mv C_AND wn
    end;

    (* pl has a winning strategy if there exists a path from the current position such that either pl has already won,
       or, it is pl's move and there exists a path to a win, or, it is not pl's move but in all paths pl wins *)
    fun can_win pm pl =
    let
      val pl_won = win pm pl
      val pl_mv = if pl=0 then ttt_AP "m" else C_NOT(ttt_AP "m")
    in C_EG (pl_won C_OR ((pl_mv C_AND (C_EF pl_won)) C_OR ((C_NOT pl_mv) C_AND  (C_AF pl_won)))) end

    val isInit = list_C_AND (List.map (fn v => if v = "m" then ttt_AP "m" else C_NOT(ttt_AP v)) (lam @ lbm @ ["m"]))

    val A_win = win am 0; (* a win position for A *)

    val A_can_win = can_win am 0; (* A has a winning strategy *)

    val B_win = win bm 1; (* a win position for B *)

    val B_can_win = can_win bm 1 (* B has a winning strategy *)

    val fl =[("isInit",isInit),("A_win",A_win),("B_win",B_win),("A_canwin",A_can_win),("B_can_win",B_can_win)]
    (* this is for testing what holCheck does if supplied with both mu and CTL forumlas
     val fl' = [("muisInit",ctl2muTools.ctl2mu ((snd o hd) fl))]@fl@
	      [("muAcw",ctl2muTools.ctl2mu ((snd o last o butlast) fl))]*)
  in
    ((set_init I1) o (set_trans T1) o (set_flag_ric false) o (set_name "ttt") o (set_vord bvm)o (set_state state) o
    (set_props fl)) empty_model
  end

end
end




