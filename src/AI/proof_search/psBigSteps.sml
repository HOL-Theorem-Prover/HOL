(* ========================================================================= *)
(* FILE          : psBigSteps.sml                                            *)
(* DESCRIPTION   : Succession of non-backtrackable moves chosen after one    *)
(*                 MCTS call for each step                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure psBigSteps :> psBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS smlParallel mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "psBigSteps"

(* -------------------------------------------------------------------------
   Type for examples and distribution derived from a policy 
   ------------------------------------------------------------------------- *)

type 'a ex = ('a * real list * real list)
type 'b dis = ((('b * real) * id) * real) list

(* -------------------------------------------------------------------------
   Tree re-use
   ------------------------------------------------------------------------- *)

fun is_prefix l1 l2 = case (l1,l2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => a1 = a2 andalso is_prefix m1 m2 

fun is_suffix l1 l2 = is_prefix (rev l1) (rev l2)

fun rm_prefix l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => raise ERR "rm_prefix" "1"
  | (a1 :: m1, a2 :: m2) => 
    (if a1 = a2 then rm_prefix m1 m2 else raise ERR "rm_prefix" "2")

fun rm_suffix l1 l2 = rev (rm_prefix (rev l1) (rev l2))

fun cut_tree id tree = 
  let
    val l = filter (fn x => is_suffix id (fst x)) (dlist tree)
    fun change_node (x,{pol,board,sum,vis,status}) =
      (rm_suffix id x, 
        {pol=map_snd (rm_suffix id) pol,
         board=board,sum=sum,vis=vis,status=status})
  in
    dnew id_compare (map change_node l)
  end

(* -------------------------------------------------------------------------
   Big steps and example extraction
   ------------------------------------------------------------------------- *)

fun make_distrib tree =
  let
    val pol = #pol (dfind [] tree)
    val _ = if null pol then raise ERR "make_distrib" "pol" else ()
    fun f (_,cid) = #vis (dfind cid tree) handle NotFound => 0.0
    val dis = map_assoc f pol
    val tot = sum_real (map snd dis)
    val _ = if tot < 0.5 then raise ERR "make_distrib" "tot" else ()
  in
    (dis,tot)
  end

fun debug_ep_aux param dis root =
  let
    val mcts_param = #mcts_param param
    val gamespec = #gamespec mcts_param
    val old_eval = fst ((#guider mcts_param) (#board root))
    val new_eval = #sum root / #vis root
    val fm = #string_of_move gamespec
    fun g r = pad 6 "0" (rts (approx 4 r))
    fun f1 (((move,r),_),_) = fm move ^ " " ^ g r
    fun f2 (((move,_),_),r) = fm move ^ " " ^ g r
  in
    print_endline ("  Old Eval: " ^ g old_eval);
    print_endline ("  New Eval: " ^ g new_eval);
    print_endline ("  Old Policy: " ^ String.concatWith ", " (map f1 dis));
    print_endline ("  New Policy: " ^ String.concatWith ", " (map f2 dis))
  end

fun select_bigstep param tree =
  let
    val (d,_) = make_distrib tree
    val choice =
      if #temp_flag param 
      then select_in_distrib d 
      else best_in_distrib d
  in
    (snd choice, d)
  end

(* -------------------------------------------------------------------------
   Extracting root examples from bigsteps
   ------------------------------------------------------------------------- *)

fun complete_pol gamespec mrl =
  let
    val d = dnew (#move_compare gamespec) mrl
    fun f move = dfind move d handle NotFound => 0.0
  in
    map f (#movel gamespec)
  end

fun add_rootex gamespec tree exl =
  let
    val root = dfind [] tree
    val board  = #board root
    val (dis,tot) = make_distrib tree
    val eval = #sum root / #vis root
    val poli = map (fn (((move,_),_),r) => (move,r / tot)) dis
  in
    (board, [eval], complete_pol gamespec poli) :: exl
  end

(* -------------------------------------------------------------------------
   MCTS big steps. Ending the search when there is no move available.
   ------------------------------------------------------------------------- *)

type ('a,'b,'c) bigsteps_param =
  {
  verbose : bool,
  temp_flag : bool, 
  max_bigsteps : 'a -> int,
  mcts_param : ('a,'b) mcts_param,
  (* parallelization *)
  write_param : string -> 'c -> unit,
  read_param : string -> 'c,
  write_targetl : string -> 'a list -> unit,
  read_targetl : string -> 'a list,
  write_result : string -> bool * 'a ex list -> unit,
  read_result : string -> bool * 'a ex list
  }

fun debug_board param gamespec board = 
  if #verbose param
  then print_endline ((#string_of_board gamespec) board)
  else ()

fun debug_ep param dis root =
  if #verbose param then debug_ep_aux param dis root else ()

(* rootl and exl are reversed *)
fun loop_bigsteps (n,nmax) param (exl,rootl) tree =
  let
    val mcts_param = #mcts_param param
    val gamespec = #gamespec mcts_param
    val board = #board (dfind [] tree)
    val status = #status_of gamespec board
    val _ = debug_board param gamespec board
  in
    if status <> Undecided orelse n >= nmax 
      then (status = Win,exl,rootl) else
    let
      val newtree = mcts mcts_param tree
      val root = dfind [] newtree
      val (cid,dis) = select_bigstep param newtree
      val _ = debug_ep param dis root
      val cuttree = 
        if #noise_flag mcts_param
        then starttree_of mcts_param (#board (dfind cid newtree))
        else cut_tree cid newtree
      val newexl = add_rootex gamespec newtree exl
      val newrootl = root :: rootl
    in
      loop_bigsteps (n+1,nmax) param (newexl,newrootl) cuttree
    end
  end

fun run_bigsteps param target =
  let
    val tree = starttree_of (#mcts_param param) target
    val n = (#max_bigsteps param) target
  in
    loop_bigsteps (0,n) param ([],[]) tree
  end

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

(*
fun bts b = if b then "true" else "false"
fun stb s = if s = "true" then true
       else if s = "false" then false
       else raise ERR "stb" ""
*)

(*
fun flags_to_string (b1,b2,b3) = bts b1 ^ " " ^  bts b2 ^ " " ^ bts b3
fun string_to_flags s =
  triple_of_list (map stb (String.tokens Char.isSpace s))
*)

(*
fun write_param file (flags,dhtnn) =
  (writel (file ^ "_flags") [flags_to_string flags];
   write_dhtnn (file ^ "_dhtnn") dhtnn)

fun read_param file =
  ((string_to_flags o hd o readl) (file ^ "_flags"),
   read_dhtnn (file ^ "_dhtnn"))
*)

fun reflect_globals () = "()"

fun ext_bigsteps bigsteps_param param target = 
  let val (a,b,c) = run_bigsteps bigsteps_param target in (a,b) end

fun bigsteps_to_extspec name bigsteps_param =
  {
  self = name,
  reflect_globals = reflect_globals,
  function = (ext_bigsteps bigsteps_param : 'c -> 'a -> bool * 'a ex list),
  write_param = #write_param bigsteps_param,
  read_param = #read_param bigsteps_param,
  write_argl = #write_targetl bigsteps_param,
  read_argl = #read_targetl bigsteps_param,
  write_result = #write_result bigsteps_param,
  read_result = #read_result bigsteps_param
  }

fun para_bigsteps ncore bigsteps_param targetl =
  let 
    val (r,t) = add_time (parmap_queue_extern ncore extspec extparam) targetl
    val nwin = length (filter fst r)
  in
    print_endline ("Time: " ^ rts t);
    print_endline ("Wins: " ^ its nwin);
    r
  end

(* -------------------------------------------------------------------------
   Toy example (same as in psMCTS)
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;
load "mlTacticData"; open mlTacticData;
load "mlNeuralNetwork"; open mlNeuralNetwork;

val mcts_param : (toy_board,toy_move) mcts_param =
  {
  nsim = 16000, 
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_flag = false,
  noise_coeff = 0.25,
  noise_alpha = 0.2,
  gamespec = toy_gamespec,
  guider = uniform_guider toy_gamespec
  };

val ERR = mk_HOL_ERR "test";
fun bstatus_to_string b = if b then "win" else "lose"
fun string_to_bstatus s = assoc s [("win",true),("lose",false)]
  handle HOL_ERR _ => raise ERR "string_to_bstatus" ""

fun write_param (file: string) (param: unit) = ();
fun read_param (file: string) = ();

fun string_of_board (a,b) = its a ^ " " ^ its b
fun board_of_string s = 
  pair_of_list (map string_to_int (String.tokens Char.isSpace s))

fun string_of_ex (board,e,p) = 
  (string_of_board board ^ "," ^ reall_to_string e ^ "," ^ reall_to_string p)

fun write_result file (bstatus,exl) =
  (
  writel (file ^ "_bstatus") [bstatus_to_string bstatus];
  writel (file ^ "_exl") (map string_of_ex exl)
  )

fun ex_of_string s =
  let val (bds,es,ps) = triple_of_list (String.tokens (fn x => x = #",") s) in
    (board_of_string bds, string_to_reall es, string_to_reall ps)
  end

fun read_result file =
  let
    val bstatus = (string_to_bstatus o hd o readl) (file ^ "_bstatus")
    val exl = map ex_of_string (readl (file ^ "_exl"))
  in
    app remove_file [file ^ "_bstatus",file ^ "_exl"];
    (bstatus, exl)
  end

fun write_targetl file targetl =
  writel file (map string_of_board targetl)

fun read_targetl file = map board_of_string (readl file)

val bigsteps_param : 
  (toy_board,toy_move,unit) psBigSteps.bigsteps_param =
  {
  verbose = false,
  temp_flag = false, 
  max_bigsteps = (fn (a,b) => 2 * b),
  mcts_param = mcts_param,
  write_param = write_param,
  read_param = read_param,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  write_result = write_result,
  read_result = read_result
  };

val target = (0,10);
val _ = run_bigsteps bigsteps_param target;
val (winb,exl,rootl) = run_bigsteps bigsteps_param target;

val targetl = List.tabulate (15, fn x => (0,x+5));
val ncore = 4;
val extspec = 
val r = para_bigsteps ncore extspec param targetl

*)

end (* struct *)
