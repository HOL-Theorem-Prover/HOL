(* NOTE: do manual init instead of loading holbddlib if loading large bdd's *)
(*List.app load ["Array2","ListPair","bossLib","simpLib","Binarymap","pairSyntax","boolSyntax","muLib"];*)

structure ttt =

struct

local

open Globals HolKernel Parse

open Array2;
open ListPair;
open bossLib;
open simpLib;
open Binarymap;
open pairSyntax;
open boolSyntax;
open stringLib
open ctlTheory;
open ctlSyntax;
open pairSyntax;
open ksTools;
open holCheckTools

in 

(* n is size of grid *)
fun makeTTT n =
  let	
    val am = Array2.tabulate Array2.RowMajor (n,n,(fn (x,y) => "u"^Int.toString(x)^"_"^Int.toString(y)));
    val bm = Array2.tabulate Array2.RowMajor (n,n,(fn (x,y) => "v"^Int.toString(x)^"_"^Int.toString(y)));
    val am' = Array2.array(n,n,"");
    val bm' = Array2.array(n,n,"");
    val _ =  Array2.copy {src=({base=am,row=0,col=0,nrows=NONE,ncols=NONE}),dst=am',dst_row=0,dst_col=0};
    val _ = Array2.copy {src=({base=bm,row=0,col=0,nrows=NONE,ncols=NONE}),dst=bm',dst_row=0,dst_col=0};
    val _ = Array2.modify Array2.RowMajor (fn s => s^"'") am';
    val _ = Array2.modify Array2.RowMajor (fn s => s^"'") bm';
    val lam = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] am;
    val lbm = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] bm;
    val lam' = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] am';
    val lbm' = Array2.fold Array2.RowMajor (fn (h,t) => t@[h]) [] bm';

    (* Good variable order is V01 < v01' < v02 < v02' ...                        *)
    (* Function shuffle below used to create it                                  *)

    fun shuffle (l1,l2) =
     ListPair.foldr (fn(x1,x2,l) => x1 :: x2 :: l) [] (l1,l2);

    val bvm = ["m","m'"]@(shuffle(lam @ lbm, lam' @ lbm'));

    (*val state  = pairSyntax.list_mk_pair (List.map mk_bool_var (lam @lbm @ ["m"]))*)

    (* Finishing condition *)
    
    fun bwin pm pl =
    let
      val r = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.row(pm,x))) (List.tabulate (n, (fn x => x)))
      val c = List.map (fn x => Vector.foldr (fn (h,t) => h::t) [] (Array2.column(pm,x))) (List.tabulate (n, (fn x => x)))
      val d1 = List.foldr (fn ((h1,h2),t) => if h1=h2 then h1::t else t) [] (ListPair.zip((List.foldr (fn (h,t) => h @ t) [] r),
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
    val state = ksTools.mk_state I1 T1
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
    in C_EG (pl_won C_OR
	      ((pl_mv C_AND (C_EF pl_won)) C_OR ((C_NOT pl_mv) C_AND  (C_AF pl_won))))
    end

    val isInit = list_C_AND (List.map (fn v => if v = "m" then ttt_AP "m" else C_NOT(ttt_AP v)) (lam @ lbm @ ["m"]))

    val A_win = win am 0; (* a win position for A *)

    val A_can_win = can_win am 0; (* A has a winning strategy *)

    val B_win = win bm 1; (* a win position for B *)

    val B_can_win = can_win bm 1; (* B has a winning strategy *)

  in
    ((I1,T1,false,SOME "ttt",SOME bvm,SOME state),[isInit,A_win,B_win,A_can_win,B_can_win])	
  end

end
end

(* usage example

app load ["bdd","holCheck","ttt"];
bdd.init 100000 10000;
val n = 1;
val tll = ttt.makeTTT n;  (* init the defs *)
val ((S0,T1,Ric,nm,vars,state),fl) = tll;
val dtb = PrimitiveBddRules.dest_term_bdd;
val _ = set_trace "metis" 0; val _ = set_trace "meson" 0; val _ = set_trace "notify type variable guesses" 0; 
val (res,ksd,ic) = holCheck.holCheck (fst tll) (snd tll) NONE NONE handle ex => Raise ex;

*)

(*
(* basic test formulae *)
val mf0 = ``mu "Q".. T``;
val mf1 = ``mu "Q".. (RV "Q")``;1
val mf2 = ``mu "Q".. (T \/ (RV "Q"))``;
val mf3 = ``mu "Q" .. (T \/ (RV "Q") \/ (RV "P"))``;
val mf4 = ``mu "Q" .. (<<"u0_0">> (T \/ (RV "Q")))``;
val mf5 = ``mu "Q" .. (<<"u0_0">> (T \/ (RV "Q" \/ RV "P")))``;
val mf6 = ``mu "Q" .. (T \/ (mu "P".. RV "P") \/ (RV "Q"))``;
val mf7 = ``mu "Q" .. (T \/ (mu "P".. RV "P" \/ RV "Q"))``;
val mf8 = ``mu "Q" .. (T \/ (mu "P".. RV "P" \/ T \/ RV "Q"))``;
val mf9 = ``mu "Q" .. (T \/ (mu "P".. RV "P" \/ T \/ RV "Q") \/ (RV "Q"))``;
val mf10 = ``nu "Q".. T``;
val mf11 = ``nu "Q".. (RV "Q")``;
val mf12 = ``nu "Q".. (T /\ (RV "Q"))``;
val mf13 = ``nu "Q" .. (T /\ (RV "Q") /\ (RV "P"))``;
val mf14 = ``nu "Q" .. (<<"u0_0">> (T /\ (RV "Q")))``;
val mf15 = ``nu "Q" .. (<<"u0_0">> (T /\ (RV "Q" \/ RV "P")))``;
val mf16 = ``nu "Q" .. (T /\ (nu "P".. RV "P") \/ (RV "Q"))``;
val mf17 = ``nu "Q" .. (T /\ (nu "P".. RV "P" \/ RV "Q"))``;
val mf18 = ``nu "Q" .. (T /\ (nu "P".. RV "P" \/ T \/ RV "Q"))``;
val mf19 = ``nu "Q" .. (T /\ (nu "P".. RV "P" \/ T \/ RV "Q") \/ (RV "Q"))``;
val mf20 = ``nu "Q" .. (T /\ (mu "P".. RV "P" \/ T \/ RV "Q") \/ (RV "Q"))``;
val mf21 = ``nu "Q" .. (T /\ (mu "P".. RV "P" \/ (T \/ T \/ T \/ T \/ T \/ T) \/ RV "Q") \/ (RV "Q"))``;
val mf22 = ``mu "Q1" .. (mu "Q2" .. (RV "Q1") \/ (RV "Q2") \/ TR)``;
val mf23 =  ``mu "Q" .. TR /\ ~(RV "P") /\ <<"u0_0">> (RV "Q")``;
val mf24 = ``AP "m" /\ AP "m"``;
val mf25 = ``~(T /\ F \/ AP "m") \/ AP "u0_0"``;
val mf26 = ``[["."]] T``;
val mf27 = ``RV "P"``;
val mf28 = ``mu "Q" .. T``;
val mf29 = ``mu "Q" .. AP "m" /\ T``;
val mf30 = ``mu "Q" .. AP "m" /\ T \/ F /\ <<"u0_0">> T``;
val mf31 = ``~TR``;
val mf32 = ``mu "Q" .. (RV "P")``;
val mf33 = ``mu "Q" .. (RV "Q")``;
val mf34 = ``mu "Q" .. (RV "P") /\ T``;
val mf35 = ``mu "Q" .. T /\ (RV "P")``;
val mf36 = ``RV "P" \/ T``;
val mf37 = ``~(RV "P")``;
val mf38 = ``mu "Q" .. (~(RV "P"))``;
val mf39 = ``<<"u0_0">> TR``;
val mf40 = ``<<"u0_0">> (RV "P")``;
val mf41 = ``mu "Q" .. (mu "Q'" .. TR)``;
val mf42 = ``mu "Q" .. (mu "Q'" .. (RV "P"))``;
val mf43 = ``mu "Q" .. (RV "Q")``;
val mf44 = ``mu "Q" .. (nu "P" .. (RV "Q") /\ (RV "P"))``;
val mf45 = ``mu "Q1" .. (mu "Q2" .. FL)``;
val mf46 = ``mu "Q1" .. (mu "Q2" .. (RV "Q1") \/ (RV "Q2") \/ TR)``;
*)


