(* ========================================================================= *)
(* FILE          : rlAimModel.sml                                            *)
(* DESCRIPTION   : Problems from the AIM conjecture                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlAimModel :> rlAimModel =
struct

open HolKernel Abbrev boolLib aiLib mlMatrix psMCTS

val ERR = mk_HOL_ERR "rlAimModel"

type table = int option vector vector
type table3 = int option vector vector vector 

(* -------------------------------------------------------------------------
   Given a table for * calculate a partial table for / \
   ------------------------------------------------------------------------- *)

fun mat_upd (v,m) =
  let val ((i,j),k) = v in mat_update m ((i,j),SOME k) end

fun mat_updl (vl,m) = foldl mat_upd m vl

fun empty_mat n = 
  let fun f i j = NONE in mat_tabulate f (n,n) end

fun mk_under_over mult = 
  let 
    val n = Vector.length mult
    val under = ref []
    val over = ref []
    fun f i j = 
    let val k = valOf (mat_sub mult i j) in
      under := ((i,k),j) :: !under;
      over := ((k,j),i) :: !over
    end
    handle Option => ()
  in
    mat_tabulate f (n,n);
    (mat_updl (!under,empty_mat n), mat_updl (!over,empty_mat n))
  end

fun f_multunderover (mult,under,over) = 
  let 
    fun fmult x y  = valOf (mat_sub mult x y)
    fun funder x y = valOf (mat_sub under x y)
    fun fover x y  = valOf (mat_sub over x y)
  in
    (fmult,funder,fover)
  end

(* -------------------------------------------------------------------------
   Calculate a truth table for lid rid b1 b2 s1 s2
   ------------------------------------------------------------------------- *)

fun mk_lid (mult,under,over) = 
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over) 
    val l = List.tabulate (Vector.length mult,I)
    fun f v0 = SOME (fmult 0 v0 = v0) handle Option => NONE 
  in
    map f l
  end

fun mk_rid (mult,under,over) = 
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over) 
    val l = List.tabulate (Vector.length mult,I)
    fun f v0 = SOME (fmult v0 0 = v0) handle Option => NONE 
  in
    map f l
  end

fun f_b1 (fmult,funder,fover) (v0,v1) =
  funder v0 (fmult v0 v1) = v1

fun f_b2 (fmult,funder,fover) (v0,v1) =
  fmult v0 (funder v0 v1) = v1

fun f_s1 (fmult,funder,fover) (v0,v1) =
  fover (fmult v0 v1) v1 = v0

fun f_s2 (fmult,funder,fover) (v0,v1) =
  fmult (fover v0 v1) v1 = v0

fun mk2_eq f2_ax (mult,under,over) = 
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over) 
    val l = List.tabulate (Vector.length mult,I)
    val l2 = cartesian_product l l
    fun f (v0,v1) = SOME (
      f2_ax (fmult,funder,fover) (v0,v1)
      ) handle Option => NONE 
  in
    map f l2
  end

fun mk_b1 (mult,under,over) = mk2_eq f_b1 (mult,under,over)
fun mk_b2 (mult,under,over) = mk2_eq f_b2 (mult,under,over)
fun mk_s1 (mult,under,over) = mk2_eq f_s1 (mult,under,over)
fun mk_s2 (mult,under,over) = mk2_eq f_s2 (mult,under,over)

fun is_partial_loop mult =
  let 
    val (under,over) = mk_under_over mult
    fun fbad x = (valOf x = false handle Option => false)
    val lid = mk_lid (mult,under,over)
    val rid = mk_rid (mult,under,over)
    val b1 = mk_b1 (mult,under,over)
    val b2 = mk_b2 (mult,under,over)
    val s1 = mk_s1 (mult,under,over)
    val s2 = mk_s2 (mult,under,over)
    val l = map (fn x => length (filter fbad x)) [lid,rid,b1,b2,s1,s2]
  in
    all (fn x => x = 0) l
  end

(* -------------------------------------------------------------------------
   Generate partial loops   
   ------------------------------------------------------------------------- *)

fun empty_partial_loop n =
  let fun f i j = NONE in mat_tabulate f (n,n) end

fun prev_ij n (i,j) = if j-1 < 0 then (i-1,n-1) else (i,j-1) 
fun next_ij n (i,j) = if j+1 > n-1 then (i+1,0) else (i,j+1)
  
fun updates_table n (i,j) m =
  List.tabulate (n, fn k => (mat_update m ((i,j), SOME k)))

fun some_partial_loop nmax n (i,j) =
  if i >= n orelse j >= n orelse j < 0 
    then raise ERR "some_partial_loop" "" else
  if i < 0 
    then [empty_partial_loop n] else
    let 
      val ml0 = some_partial_loop nmax n (prev_ij n (i,j))
      val ml1 = List.concat (map (updates_table n (i,j)) ml0)
      val ml2 = filter is_partial_loop ml1
      val ml3 = first_n nmax (shuffle ml2) 
    in
      print_endline (its i ^ "," ^ its j ^ ":" ^ its (length ml2)); 
      ml3
    end

(* -------------------------------------------------------------------------
   Given a table for * / \ infer T L R
   ------------------------------------------------------------------------- *)

fun mk_T (mult,under,over) =
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over) 
    fun f x0 x1 = SOME (funder x1 (fmult x0 x1)) handle Option => NONE
  in
    mat_tabulate f (n,n)
  end

fun mk_L (mult,under,over) =
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over)
    fun f x0 x1 x2 = SOME (
      funder (fmult x2 x1) (fmult x2 (fmult x1 x0)) 
      ) handle Option => NONE
  in
    mat3_tabulate f (n,n,n)
  end

fun mk_R (mult,under,over) =
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over)
    fun f x0 x1 x2 = SOME (
      fover (fmult (fmult x0 x1) x2) (fmult x1 x2) 
      ) handle Option => NONE
  in
    mat3_tabulate f (n,n,n)
  end

fun mk_a (mult,under,over) =
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over)
    fun f v0 v1 v2 = SOME (
      funder (fmult v0 (fmult v1 v2)) (fmult (fmult v0 v1) v2)
      ) handle Option => NONE
  in
    mat3_tabulate f (n,n,n)
  end

fun mk_K (mult,under,over) =
  let 
    val n = Vector.length mult
    val (fmult,funder,fover) = f_multunderover (mult,under,over)
    fun f v0 v1 = SOME (
      funder (fmult v1 v0) (fmult v0 v1)
      ) handle Option => NONE
  in
    mat_tabulate f (n,n)
  end


(* -------------------------------------------------------------------------
   Based on this calculate a truth table for TT TL TR LR LL RR.
   ------------------------------------------------------------------------- *)

datatype expr = 
  Ic of int | 
  Tc of expr * expr | Lc of expr * expr * expr | Rc of expr * expr * expr |  
  Ec of expr * expr

           
fun compare_expr (e1,e2) = case (e1,e2) of
    (Ic x1 , Ic x2) => Int.compare (x1,x2)
  | (Ic _ , _) => LESS
  | (_ , Ic _) => GREATER
  | (Tc x1 , Tc x2) => 
    list_compare compare_expr (list_of_pair x1, list_of_pair x2)
  | (Tc _, _) => LESS
  | (_, Tc _) => GREATER
  | (Lc x1 , Lc x2) => 
    list_compare compare_expr (list_of_triple x1, list_of_triple x2)
  | (Lc _ , _) => LESS
  | (_, Lc _) => GREATER
  | (Rc x1 , Rc x2) =>
    list_compare compare_expr (list_of_triple x1, list_of_triple x2)
  | (Rc _ , _) => LESS
  | (_, Rc _) => GREATER
  | (Ec x1 , Ec x2) =>
    list_compare compare_expr (list_of_pair x1, list_of_pair x2)


exception Block of expr;

fun reduce_one (T,L,R) expr = 
  let fun sub e = reduce_one (T,L,R) e in 
    case expr of
      Ic _ => raise ERR "reduce_expr" "Ic"
    | Tc (Ic a, Ic b) => (Ic (T a b) 
        handle Option => raise Block expr)
    | Tc (Ic a, eb)   => Tc (Ic a, sub eb)
    | Tc (ea, eb)     => Tc (sub ea, eb)
    | Lc (Ic a, Ic b, Ic c) => (Ic (L a b c) 
        handle Option => raise Block expr)
    | Lc (Ic a, Ic b, ec) => Lc (Ic a, Ic b, sub ec)
    | Lc (Ic a, eb, ec)   => Lc (Ic a, sub eb, ec)
    | Lc (ea, eb, ec)     => Lc (sub ea, eb, ec)
    | Rc (Ic a, Ic b, Ic c) => (Ic (R a b c) 
        handle Option => raise Block expr)
    | Rc (Ic a, Ic b, ec) => Rc (Ic a, Ic b, sub ec)
    | Rc (Ic a, eb, ec)   => Rc (Ic a, sub eb, ec)
    | Rc (ea, eb, ec)     => Rc (sub ea, eb, ec)
    | Ec (Ic a, Ic b) => Ec (Ic a, Ic b)
    | Ec (Ic a, eb)   => Ec (Ic a, sub eb)
    | Ec (ea, eb)     => Ec (sub ea, eb)
  end

fun reduce (T,L,R) expr = case expr of
    Ec (Ic a, Ic b) => (expr,NONE) | _ => 
  let val (b,newexpr) = 
    (true,reduce_one (T,L,R) expr) 
    handle Block eblock => (false,eblock) 
  in
    if b 
    then reduce (T,L,R) newexpr
    else (expr, SOME newexpr)
  end

fun is_trueeq e = case e of
    Ec (Ic a, Ic b) => a = b
  | _ => raise ERR "is_trueeq" ""
 
(* 

K 4 
a (1 2 3) : \ ( * 1 ( * 2 3)) ( * ( * 1 2) 3))
2 * 3 = 5
1 * 2 = 6
1 * 5 = 7
6 * 3 = 8
7 \ 8 = 9  7 * 9 = 8

K 9 4 : \ ( * 4 9) ( * 9 4))
4 * 9 = 10
9 * 4 = 11
10 \ 11 = 12   10 * 12 = 11




*)

fun norm_expr e = case e of 
    Ec (a,b) => 
    if compare_expr (a,b) = GREATER 
    then Ec (b,a)
    else e 
  | _ => raise ERR "norm_expr" "equality expected"

fun all_TLR_expr n =
  let 
    val l = List.tabulate (n,Ic)
    val l3 = map triple_of_list (cartesian_productl [l,l,l])
    val l4 = map quadruple_of_list (cartesian_productl [l,l,l,l])
    val l5 = map quintuple_of_list (cartesian_productl [l,l,l,l,l])
    fun f3 (v0,v1,v2) =
      [Ec (Tc(Tc(v0,v1),v2), Tc(Tc(v0,v2),v1))]
    fun f4 (v0,v1,v2,v3) =
      [Ec (Tc(Lc(v0,v1,v2),v3), Lc(Tc(v0,v3),v1,v2)),
       Ec (Tc(Rc(v0,v1,v2),v3), Rc(Tc(v0,v3),v1,v2))]
    fun f5 (v0,v1,v2,v3,v4) = 
      [Ec (Rc(Rc(v0,v1,v2),v3,v4), Rc(Rc(v0,v3,v4),v1,v2)),
       Ec (Lc(Lc(v0,v1,v2),v3,v4), Lc(Lc(v0,v3,v4),v1,v2)),
       Ec (Lc(Rc(v0,v1,v2),v3,v4), Rc(Lc(v0,v3,v4),v1,v2))]
  in
    mk_fast_set compare_expr (map norm_expr (List.concat (map f3 l3))) @  
    mk_fast_set compare_expr (map norm_expr (List.concat (map f4 l4))) @  
    mk_fast_set compare_expr (map norm_expr (List.concat (map f5 l5)))
  end

fun init_cgraph n =
  let
    fun T x y = valOf (NONE: int option)
    fun L x y z = valOf (NONE: int option)
    fun R x y z = valOf (NONE: int option)
    val l = all_TLR_expr n
    val l1 = map (reduce (T,L,R)) l 
    val l2 = map (fn (a,b) => (valOf b, a)) l1
    val d = dappendl l2 (dempty compare_expr)
  in
    d
  end



fun f_TLR (tT,tL,tR) = 
  let 
    fun fT x y = valOf (mat_sub tT x y) 
    fun fL x y z = valOf (mat3_sub tL x y z)
    fun fR x y z = valOf (mat3_sub tR x y z)
  in
    (fT,fL,fR)
  end  

(*
val ta = mk_a (newm,under,over)
val tK = mk_K (newm,under,over)
fun a x y z = valOf (mat3_sub ta x y z)
fun K x y = valOf (mat_sub tK x y)
val bcj = K (a 4 3 2) 1 <> 0 handle Option => true
*)


(* should be from newm *)
fun update_cgraph (newm,d) =
  let 
    val (under,over) = mk_under_over newm
    val tT = mk_T (newm,under,over)
    val tL = mk_L (newm,under,over)
    val tR = mk_R (newm,under,over)
    val l = List.tabulate (Vector.length newm, I)
    val l2 = cartesian_product l l
    val l3 = map triple_of_list (cartesian_productl [l,l,l])
    val (T,L,R) = f_TLR (tT,tL,tR)
    fun fT (x,y) = 
      if isSome (mat_sub tT x y) then SOME (Tc(Ic x,Ic y)) else NONE
    fun fL (x,y,z) = 
      if isSome (mat3_sub tL x y z) then SOME (Lc(Ic x,Ic y,Ic z)) else NONE
    fun fR (x,y,z) = 
      if isSome (mat3_sub tR x y z) then SOME (Rc(Ic x,Ic y,Ic z)) else NONE
    val avail1 = 
      List.mapPartial fT l2 @ List.mapPartial fL l3 @ List.mapPartial fR l3
    val avail2 = filter (fn x => dmem x d) avail1
    val el1 = List.concat (map (fn x => dfind x d) avail2)
    val el2 = map (reduce (T,L,R)) el1
    val (partiall, reducedl) = partition (isSome o snd) el2
    val el3 = mapfilter (fn (a,b) => (valOf b, a)) partiall;
    val d1 = foldl (uncurry drem) d avail2
    val d2 = dappendl el3 d1
  in
    (d2, all (is_trueeq o fst) reducedl)
  end

fun print_table m =
  let 
    fun xts x = pad 2 " " (if x = NONE then "x " else  its (valOf x))
    fun f v = String.concatWith " " (map xts (vector_to_list v)) 
  in
    print_endline "";
    print_endline (String.concatWith "\n" (map f (vector_to_list m)));
    print_endline ""
  end

(* -------------------------------------------------------------------------
   Verifies if the aim conjecture is true.
   ------------------------------------------------------------------------- *)

fun mk_aa1 (tK,ta) = 
  let 
    fun K x y = valOf (mat_sub tK x y) 
    fun a x y z = valOf (mat3_sub ta x y z)
    val l = List.tabulate (Vector.length tK,I)
    val l5 = map quintuple_of_list (cartesian_productl [l,l,l,l,l])
    fun f (v0,v1,v2,v3,v4) =
      SOME (a (a v4 v3 v2) v1 v0 = 0)
      handle Option => NONE 
  in
    map f l5
  end

fun mk_aK1 (tK,ta) = 
  let 
    fun K x y = valOf (mat_sub tK x y) 
    fun a x y z = valOf (mat3_sub ta x y z)
    val l = List.tabulate (Vector.length tK,I)
    val l4 = map quadruple_of_list (cartesian_productl [l,l,l,l])
    fun f (v0,v1,v2,v3) =
      SOME (a (K v3 v2) v1 v0 = 0)
      handle Option => NONE 
  in
    map f l4
  end

fun is_cjaim m =
  let
    val (under,over) = mk_under_over m
    val tK = mk_K (m,under,over)
    val ta = mk_a (m,under,over)
    fun fbad x = (valOf x = false handle Option => false)
    val aK1 = mk_aK1 (tK,ta)
    val aa1 = mk_aa1 (tK,ta)
  in
    all (fn x => null (filter fbad x)) [aK1,aa1]
  end

(* -------------------------------------------------------------------------
   Game specification
   ------------------------------------------------------------------------- *)

type board = table * (int * int) * (expr, expr list) Redblackmap.dict * bool
type move = int

fun status_of (_,(m,(i,j),_,b)) =
  (
  if i >= Vector.length m
  then (if b then Win else Lose)
  else (if b then Undecided else Lose)
  )

fun apply_move k (_,(m,(iold,jold),d,b)) =
  let 
    val n = Vector.length m 
    fun find_next (i,j) = 
      if isSome (mat_sub m i j) 
      then find_next (if j+1 > n-1 then (i+1,0) else (i,j+1))
      else (i,j)        
    val (i,j) = find_next (iold,jold)
    val newm = mat_update m ((i,j),SOME k)
    val newij = if j+1 > n-1 then (i+1,0) else (i,j+1)
    val (newd,newb) = update_cgraph (newm,d)
  in
    (true, (newm,newij,newd, newb andalso is_partial_loop newm))
  end

(* -------------------------------------------------------------------------
   Do MCTS simulations with rewarding 1 for a move that do not end up in
   a conflict.
   ------------------------------------------------------------------------- *)

(*
app load ["psMCTS","rlAimModel"];
open aiLib mlMatrix psMCTS rlAimModel;

val nsim = 1000;
val decay = 1.0;
val noiseb = true;
val boarddim = 16;
val movel = List.tabulate (boarddim,I);
fun fep _ = (1.0, map_assoc (fn _ => 1.0) movel)
val m = empty_partial_loop boarddim;
val d = init_cgraph boarddim;

(* 
fun mat_upd (v,m) =
  let val ((i,j),k) = v in mat_update m ((i,j),SOME k) end
fun mat_updl (vl,m) = foldl mat_upd m vl
val vl =
 [((2,3),5),((1,2),6),((1,5),7),((6,3),8),((7,9),8),
  ((4,9),10), ((9,4),11), ((10,12),11)]
val m' = mat_updl (vl,m);
   val (newd,newb) = update_cgraph (m',d); 
*)

val startsit = (true,(m,(0,0),d,true));
val starttree =
  starttree_of (nsim,decay,noiseb,status_of,apply_move,fep) startsit;
fun print_status status = 
   print_endline (
   case status of
   Win => "win" | Lose => "lose" | Undecided => "undecided")


fun f1 ((a,b),_) = its a ^ " " ^ rts (approx 4 b);
fun myloop tree =
  let 
    val exptree = mcts (nsim,decay,noiseb,status_of,apply_move,fep) tree
    val (distrib,cido) = select_bigstep exptree [0]
    val root = dfind [0] exptree
    val pol = #pol root
    val (_,(m,(i,j),_,_)) = #sit root
    val _ = print_table m
    val _ = print_status (status_of (#sit root))
    val _ = print_endline (its i ^ "," ^ its j ^ "\n")
  in
    case cido of
      NONE => m
    | SOME cid => 
      (
      print_endline (String.concatWith ", " (map f1 pol)); 
      print_distrib its distrib;
      print_endline (its (move_of_cid root cid));
      myloop (cut_tree exptree cid)
      )
  end   ;


val mresult = myloop starttree;
print_table mresult;
is_cjaim mresult;
   
*)
end (* struct *)



