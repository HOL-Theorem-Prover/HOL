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
val version = 1

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
   Levels
   ------------------------------------------------------------------------- *)

val datadir = HOLDIR ^ "/src/AI/experiments/data_combin"
val datafile =  datadir ^ "/synt-" ^ its version
val stats_dir = HOLDIR ^ "/src/AI/experiments/stats_combin"
fun stats_il header il = 
  let 
    fun f (a,b) = its a ^ "-" ^ its b
    val l = dlist (count_dict (dempty Int.compare) il) 
    val _ = mkDir_err stats_dir
    val s = header ^ "\n" ^ String.concatWith ", " (map f l) ^ "\n"
  in
    append_file (stats_dir ^ "/synt-" ^ its version) s;
    print_endline s
  end

val witness_cache = ref (dempty Term.compare)

fun gen_board k cache =
  (
  print_endline (its (dlength cache));
  if dlength cache >= k then map snd (dlist cache) else
  let 
    val nstep = random_int (10,30)
    val tm = list_mk_cA [random_cterm nstep,cV1,cV2,cV3]
    val tmo = lo_cnorm 100 [s_thm,k_thm] tm
  in
    if not (isSome tmo) orelse 
       can (find_term (C tmem [cS,cK])) (valOf tmo)
      then gen_board k cache
    else if dmem (valOf tmo) cache then 
      let val (_,_,nstep') = dfind  (valOf tmo) cache in
        if 2*nstep < nstep' 
        then (witness_cache := dadd (valOf tmo) tm (!witness_cache);
             gen_board k (dadd (valOf tmo) (cX,valOf tmo,2*nstep) cache))
        else gen_board k cache
      end
    else (witness_cache := dadd (valOf tmo) tm (!witness_cache);
          gen_board k (dadd (valOf tmo) (cX,valOf tmo,2*nstep) cache)) 
  end
  )

fun create_levels n = 
  let 
    val _ = mkDir_err datadir 
    val l1 = gen_board n (dempty Term.compare)
    val l2 = dict_sort (compare_third Int.compare) l1
  in  
    write_boardl datafile l2;
    stats_il "size_in" (map (cterm_size o #1) l2);
    stats_il "size_out" (map (cterm_size o #2) l2);
    stats_il "nstep" (map ((fn x => x div 2) o #3) l2);
    l2
  end

fun div_equal n m =
  let val (q,r) = (n div m, n mod m) in
    List.tabulate (m, fn i => q + (if i < r then 1 else 0))
  end

fun level_targetl level = 
  let
    val n = 400
    val boardl1 = read_boardl datafile
    val boardl2 = first_n level (mk_batch n boardl1)
    val nl = div_equal n (length boardl2)
    val boardl3 = 
      List.concat (map (uncurry random_subset) (combine (nl,boardl2)))
  in
    stats_il "nstep_level" (map #3 boardl3);
    rev boardl3
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
  [{ncore = 1, verbose = true, learning_rate = 0.02,
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
   ncore = 4, level_threshold = 0.9, nsim = 1600, decay = 1.0}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  level_targetl = level_targetl,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleSynthesize.extsearch" rlobj

(*
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
(* val boardl = create_levels 400; *)
val r = rl_start (rlobj,extsearch) 1;
*)

(*
load "aiLib"; open aiLib;
load "mleLib"; open mleLib;
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
val boardl = create_levels 100;
val tm = list_mk_cA [list_mk_cA[cS,cK,cS],cV1,cV2,cV3];
val tmo = lo_cnorm 100 [s_thm,k_thm] tm;

val tml = map #2 boardl;
tmem tm tml;
val witness = dfind tm (!witness_cache);
*)


end (* struct *)
