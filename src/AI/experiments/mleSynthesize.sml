(* ========================================================================= *)
(* FILE          : mleSynthesize.sml                                         *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSynthesize :> mleSynthesize =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleLib mleArithData

val ERR = mk_HOL_ERR "mleSynthesize"
val version = 4

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int
fun string_of_board (a,b,c)= tts a ^ " " ^ tts b ^ " " ^ its c

fun board_compare ((a,b,c),(d,e,f)) =
  (cpl_compare Term.compare Term.compare) ((a,b),(d,e))

fun status_of (tm1,tm2,n) =
  let 
    val tm1a = list_mk_cA [tm1,cV1,cV2,cV3]
    val tm1o = lo_cnorm 100 [s_thm,k_thm] tm1a
  in
    if isSome tm1o andalso term_eq (valOf tm1o) tm2
      then Win
    else if n <= 0 
      then Lose
    else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
val movel = [cA,cS,cK]
val move_compare = Term.compare

fun apply_move move (tm1,tm2,n) = 
  let
    val res = list_mk_comb (move, List.tabulate (arity_of move, fn _ => cX))
    val sub = [{redex = cX, residue = res}]
  in
    (subst_occs [[1]] sub tm1, tm2, n-1)
  end

fun available_movel board = movel
fun string_of_move tm = tts tm

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  apply_move = apply_move,
  available_movel = available_movel,  
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = Term.compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val (l1,l2,l3) = split_triple boardl in
    export_terml (file ^ "_in") l1;
    export_terml (file ^ "_out") l2; 
    writel (file ^ "_timer") (map its l3)
  end

fun read_boardl file =
  let
    val l1 = import_terml (file ^ "_in")
    val l2 = import_terml (file ^ "_out")
    val l3 = map string_to_int (readl (file ^ "_timer"))
  in
    combine_triple (l1,l2,l3)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = HOLDIR ^ "/src/AI/experiments/target_combin"
val targetfile = targetdir ^ "/targetl-synt-" ^ its version
val stats_dir = HOLDIR ^ "/src/AI/experiments/stats_combin"
val stats_file = stats_dir ^ "/stats-synt-" ^ its version
fun stats_il header il = 
  let 
    fun f (a,b) = its a ^ "-" ^ its b
    val l = dlist (count_dict (dempty Int.compare) il) 
    val _ = mkDir_err stats_dir
    val s = header ^ "\n" ^ String.concatWith ", " (map f l) ^ "\n"
  in
    append_file stats_file s;
    print_endline s
  end

fun cgen_random n (a,b) =
  let 
    val size = random_int (a,b)
    val tml = List.tabulate (n, fn _ => 
      list_mk_cA [random_cterm size,cV1,cV2,cV3])
  in
    mk_fast_set Term.compare tml
  end 

fun cgen_exhaustive size = gen_term [cA,cS,cK] (2*size-1,alpha)

fun create_targetl tml =
  let
    fun f tm = 
      let val tmo =
        lo_cnorm 100 [s_thm,k_thm] (list_mk_cA [tm,cV1,cV2,cV3])
      in
        if not (isSome tmo) orelse 
           can (find_term (C tmem [cS,cK])) (valOf tmo)
        then NONE
        else tmo
      end
    val l1 = map_assoc f tml    
    val l2 = filter (fn x => isSome (snd x)) l1    
    val l3 = map_snd valOf l2
    val l4 = dregroup Term.compare (map swap l3)
    val l5 = map_snd (list_imin o map term_size) (dlist l4)
    val l6 = map (fn (a,b) => (cX,a,2 * b)) l5
  in
    stats_il "size_in" (map (cterm_size o #1) l6);
    stats_il "size_out" (map (cterm_size o #2) l6);
    stats_il "nstep" (map ((fn x => x div 2) o #3) l6);
    dict_sort (compare_third Int.compare) l6
  end

fun export_targetl targetl = 
  let val _ = mkDir_err targetdir in 
    write_boardl targetfile targetl
  end

fun import_targetd () =
  let 
    val l1 = read_boardl targetfile
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:'a -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
fun tob (tm1,tm2,_) = 
  [tag_heval (mk_cE (tm1,tm2)), tag_hpoli (mk_cE (tm1,tm2))]

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 40}]

val dim = 8
fun dim_head_poli n = [dim,n]

val tnnparam = map_assoc (dim_std (1,dim)) [cE,cX,cV1,cV2,cV3,cA,cS,cK] @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]


val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleSynthesize-combin-" ^ its version, exwindow = 40000,
   ncore = 30, ntarget = 200, nsim = 3200, decay = 1.0}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleSynthesize.extsearch" rlobj

(*
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
  val tml = cgen_exhaustive 10; length tml;
  val targetl = create_targetl tml; length targetl;
  val _ = export_targetl targetl;
val r = rl_start (rlobj,extsearch) (import_targetd ());
*)

end (* struct *)
