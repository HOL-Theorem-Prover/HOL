(* ========================================================================= *)
(* FILE          : mleResolution.sml                                         *)
(* DESCRIPTION   : Prover for propositional CNF                              *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleResolution :> mleResolution =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mlReinforce mleLib mleSetLib

val ERR = mk_HOL_ERR "mleResolution"

val max_steps_glob = 80
val max_vars_glob = 20

(* -------------------------------------------------------------------------
   Comparison function
   ------------------------------------------------------------------------- *)

type 'a set = ('a, unit) Redblackmap.dict
type lit = int * bool
type clause = lit list
val lit_compare = cpl_compare Int.compare bool_compare
val clause_compare = list_compare lit_compare 

(* -------------------------------------------------------------------------
   Subsumption
   ------------------------------------------------------------------------- *)

fun subsume c1 c2 = 
  let val d = dset lit_compare c2 in all (fn x => dmem x d) c1 end 

fun subsumel c1l c2 = exists (fn x => subsume x c2) c1l

fun inter_reduce cl = case cl of
    [] => []
  | c :: m => if subsumel m c then inter_reduce m else c :: inter_reduce m

(* -------------------------------------------------------------------------
   Resolution
   ------------------------------------------------------------------------- *)

fun resolve_aux b (c1,c2) = case (c1:clause,c2:clause) of
    ([],_) => if b then c2 else raise ERR "resolve_aux" "no match"
  | (_,[]) => if b then c1 else raise ERR "resolve_aux" "no match"
  | ((a1,b1) :: m1, (a2,b2) :: m2) =>
    if a1 < a2 then (a1,b1) :: resolve_aux b (m1,c2)
    else if a2 < a1 then (a2,b2) :: resolve_aux b (c1,m2) 
    else 
      if b1 = b2 then (a1,b1) :: resolve_aux b (m1,m2)
      else if b then raise ERR "resolve_aux" "multiple matches"
           else resolve_aux true (m1,m2)

fun resolve (c1:clause, c2:clause) = (resolve_aux false (c1,c2) : clause)
  
fun resolve_ctxt pb (c1,c2) = 
  let val c = resolve (c1,c2) in 
    if mem c pb orelse subsumel pb c 
    then raise ERR "resolve_ctxt" "" 
    else c
  end

fun exists_match pb l c = 
  exists (fn x => can (resolve_ctxt pb) (x,c)) l

(* -------------------------------------------------------------------------
   Brute force algorithm by iterative deepedning
   ------------------------------------------------------------------------- *)

fun resolve_cost pb ((c1,n1),(c2,n2)) =
  let val c = resolve (c1,c2) in
    if dmem c pb then raise ERR "resolve_cost" "" else (c, n1 + n2 + 1)
  end

fun resolve_brute (pb,l1,l2) =
  let val l = all_pairs l2 @ cartesian_product l1 l2 in
    mapfilter (resolve_cost pb) l
  end

fun brute_pb_aux (i,n) (pb,l1,l2) =
  if dmem [] pb then ("solved",i, SOME (dfind [] pb))
  else if null l2 then ("saturated", i, NONE)  
  else if i >= n then ("timeout", i, NONE)
  else
    let 
      val cl1 = dlist (dregroup clause_compare (resolve_brute (pb,l1,l2))) 
      val cl2 = map_snd list_imin cl1
    in
      brute_pb_aux (i+1,n) (daddl cl2 pb, l2 @ l1, cl2)
    end

fun brute_pb n (l: clause list) = 
  let val lcost = map_assoc (fn _ => 0) l in
    brute_pb_aux (0,n) (dnew clause_compare lcost, [], lcost)
  end

fun difficulty n l = case brute_pb n l of
    ("solved", _, SOME i) => (print_endline (its i); SOME i)
  | _ => NONE

(* -------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun eval_lit assign (lit,b) = 
  if b then Vector.sub (assign,lit) else not (Vector.sub (assign,lit))

fun eval_clause assign c = exists (eval_lit assign) c

fun eval_pb assign pb = all (eval_clause assign) pb

fun all_assign nvar =
  map Vector.fromList 
  (cartesian_productl (List.tabulate (nvar,fn _ => [false,true])))

fun is_sat pb = 
  let val nvar = list_imax (map fst (List.concat pb)) in
    exists (C eval_pb pb) (all_assign (nvar + 1))
  end

(* -------------------------------------------------------------------------
   Generation of a random problem for 3-SAT
   ------------------------------------------------------------------------- *)

fun random_lit nvar = 
  (random_int (0, nvar - 1), random_elem [true,false])

fun random_clause nlit nvar = 
  let 
    fun loop n d = 
      if n <= 0 then d else
      let val (i,b) = random_lit nvar in
        if dmem i d then loop (n-1) d else loop (n-1) (dadd i b d)
      end
  in
    dlist (loop nlit (dempty Int.compare))
  end

fun random_pb nclause nlit nvar =
  let 
    fun loop d =
      if dlength d >= nclause 
      then d 
      else loop (dadd (random_clause nlit nvar) () d)
  in
    dkeys (loop (dempty clause_compare))
  end

(*
val max_lit = 3;
val max_var = 8;
val max_clause = 40;
val c = random_clause max_lit max_var;
val pb = random_pb max_clause max_lit max_var;
val b = is_sat pb;
val r = brute_pb 32 pb;

val pbl = List.tabulate (100, fn _ => random_pb max_clause max_lit max_var);
val (pbl_sat, pbl_unsat) = partition is_sat pbl;
length pbl_unsat;

val pbl_result = map (brute_pb 32) pbl_unsat;
val pbl_solved = filter (fn x => #1 x = "solved") pbl_result;
length (filter (fn x => #1 x = "solved") pbl_result);
length (filter (fn x => #1 x = "saturated") pbl_result);
length (filter (fn x => #1 x = "timeout") pbl_result);

val diffl = map (valOf o #3) pbl_solved;
val diffd = count_dict (dempty Int.compare) diffl;
(dlist diffd);
*)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = clause list * clause list * int

fun mk_startboard cl = ([], cl, max_steps_glob)

fun triple_compare cmp1 cmp2 cmp3 ((a1,a2,a3),(b1,b2,b3)) = 
  cpl_compare (cpl_compare cmp1 cmp2) cmp3 (((a1,a2),a3),((b1,b2),b3))

fun set_compare cmp (d1,d2) = list_compare cmp (dkeys d1, dkeys d2)

val board_compare =
  triple_compare (list_compare clause_compare)
    (list_compare clause_compare) Int.compare

fun string_of_lit (i,b) = if b then its i else "~" ^ its i

fun string_of_clause c = 
  "(" ^ String.concatWith " " (map string_of_lit c) ^ ")"

fun string_of_clausel cl = 
  if null cl 
  then "empty clause list"
  else String.concatWith "\n" (map string_of_clause cl)

fun string_of_board (cl1,cl2,n) =
  String.concatWith "\n\n" 
  [string_of_clausel cl1, string_of_clausel cl2, its n]  
  
fun status_of (cl1,cl2,n) =
  if mem [] cl2 then Win 
  else if n <= 0 then Lose
  else Undecided

(* -------------------------------------------------------------------------
   Term representation of the board
   ------------------------------------------------------------------------- *)

fun mk_bvar i = mk_var ("V" ^ its i, bool)
fun bvar_of_term tm = string_to_int (tl_string (fst (dest_var tm)))

fun mk_lit (i,b) = (if b then I else mk_neg) (mk_bvar i)
fun lit_of_term tm = 
  if is_neg tm 
  then (bvar_of_term (dest_neg tm), false) 
  else (bvar_of_term tm, true)

fun term_of_clause c = list_mk_disj (map mk_lit c)
fun clause_of_term ctm = map lit_of_term (strip_disj ctm)

val empty_list_var = mk_var ("empty_list_var", bool)
fun term_of_clausel cl = 
  if null cl 
  then empty_list_var 
  else list_mk_conj (map term_of_clause cl)
fun clausel_of_term tm = 
  if term_eq empty_list_var tm 
  then []
  else map clause_of_term (strip_conj tm)

fun term_of_pb d = term_of_clausel (dkeys d)
fun pb_of_term tm = dset clause_compare (clausel_of_term tm)

val pair_cat = mk_var ("pair_cat", ``:bool -> bool -> bool``)

fun term_of_board (cl1,cl2,_) =
  list_mk_comb (pair_cat, [term_of_clausel cl1, term_of_clausel cl2])    

fun board_of_term tm = 
  let val (cl1,cl2) = pair_of_list (snd (strip_comb tm)) in
    (clausel_of_term cl1, clausel_of_term cl2)
  end

val operl_aux = List.tabulate (max_vars_glob, mk_bvar) @ 
  [empty_list_var, pair_cat, ``$~``,``$/\``,``$\/``]
val operl = mk_fast_set oper_compare (map_assoc arity_of operl_aux)
fun term_of_boardc (_:unit) b = term_of_board b

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val board = dset clause_compare [[(0,true),(1,false),(2,true)]];
val tm = term_of_board (board,NONE,0);
*)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Select | Delete
val movel = [Select, Delete]

fun string_of_move m = case m of Select => "select" | Delete => "delete" 
fun move_compare (a,b) = String.compare (string_of_move a, string_of_move b)

fun available_move (cl1,cl2,_) move = 
  if move = Delete then not (null cl2) else true

fun choose_clause_aux (cl1,cl2) = case cl2 of
    [] => raise ERR "choose_clause" "empty"
  | a :: m => (if not (subsumel cl1 a)
               then (a,m) 
               else choose_clause_aux (cl1, tl cl2))

fun choose_clause (cl1,cl2) = 
  SOME (choose_clause_aux (cl1,cl2)) handle HOL_ERR _ => NONE

fun apply_select (cl1,cl2,n) = 
  let val ro = choose_clause (cl1,cl2) in
    if not (isSome ro) then ([],[],~1) else 
    let
      val (c,cl2cont) = valOf ro
      val prodl = mapfilter (fn x => resolve_ctxt cl1 (c,x)) cl1
      val subl = filter (subsume c) cl1
      val subld = dset clause_compare subl
      val pb1 = filter (fn x => not (dmem x subld)) cl1  
      val pb2 = c :: pb1
    in
      (pb2, cl2cont @ prodl, n-1)
    end
  end
  

fun apply_move move (cl1,cl2,n) = case move of
    Select => apply_select (cl1,cl2,n-1)
  | Delete => (cl1,tl cl2,n-1)

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  board_compare = board_compare,
  string_of_board = string_of_board,
  movel = movel,
  move_compare = move_compare,
  string_of_move = string_of_move,
  status_of = status_of,
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   MCTS test with uniform player
   ------------------------------------------------------------------------- *)

fun mk_mcts_param nsim =
  {
  nsim = nsim, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false,
  noise_all = false, noise_gen = random_real
  }

fun string_of_status status = case status of
    Win => "win"
  | Lose => "lose"
  | Undecided => "undecided"

fun mcts_test nsim pb =
  let
    val mcts_obj =
      {mcts_param = mk_mcts_param nsim,
       game = game,
       player = random_player game}
    val tree = starttree_of mcts_obj (mk_startboard pb)
    val endtree = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;

val pbl_unsat  = List.tabulate (1000, fn _ => level_pb 4);
val pbl_result = map_assoc (brute_pb 15) pbl_unsat;
val pbl_solved = filter (fn x => #1 (snd x) = "solved") pbl_result;
val pbl1 = map (fn x => (fst x, valOf (#3 (snd x)))) pbl_solved;
map_snd length (dlist (dregroup Int.compare (map swap pbl1)));
val pbl2 = dict_sort compare_imin pbl1;

val (pb,diff) = List.nth (pbl2,100);
val pb' = inter_reduce pb;
val tm = term_of_board (mk_startboard pb');
val (win,endtree) = mcts_test 1000 pb';
dfind [0,0,0,0,0,0,0] endtree;
*)

(* -------------------------------------------------------------------------
   Initialization of the levels
   ------------------------------------------------------------------------- *)

fun level_pb level =
  let 
    val nvar = random_int (4,level)
    val nlit = 3
    val nclause = random_int (nvar * 2, nvar * 3)   
    fun loop () =
      let val pb = random_pb nclause nlit nvar in
        if is_sat pb then loop () else pb
      end
  in
    inter_reduce (mk_sameorder_set clause_compare (loop ()))
  end

fun level_targetl level =
  let val level_alt = 
    if level > max_vars_glob then max_vars_glob else level
  in
    map mk_startboard (List.tabulate (400, fn _=> level_pb level_alt))
  end

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val nl = map #3 boardl in
    export_terml (file ^ "_boardl") (map term_of_board boardl);
    writel (file ^ "_timel") (map its nl)
  end

fun read_boardl file =
  let 
    val boardl = map board_of_term (import_terml (file ^ "_boardl"))
    val nl = map string_to_int (readl (file ^ "_timel"))
    val (l1,l2) = split boardl
  in
    combine_triple (l1,l2,nl)
  end

fun write_target file target = write_boardl (file ^ "_target") [target]
fun read_target file = only_hd (read_boardl (file ^ "_target"))

fun write_exl file exl =
  let val (boardl,evall,polil) = split_triple exl in
    write_boardl file boardl;
    writel (file ^ "_eval") (map reall_to_string evall);
    writel (file ^ "_poli") (map reall_to_string polil)
  end
fun read_exl file =
  let
    val boardl = read_boardl file
    val evall = map string_to_reall (readl (file ^ "_eval"))
    val polil = map string_to_reall (readl (file ^ "_poli"))
  in
    combine_triple (boardl,evall,polil)
  end

fun write_splayer file (unib,dhtnn,noiseb,playerid,nsim) =
  (
  write_dhtnn (file ^ "_dhtnn") dhtnn;
  writel (file ^ "_flags") [String.concatWith " " (map bts [unib,noiseb])];
  writel (file ^ "_playerid") [playerid];
  writel (file ^ "_nsim") [its nsim]
  )
fun read_splayer file =
  let
    val dhtnn = read_dhtnn (file ^ "_dhtnn")
    val (unib,noiseb) =
      pair_of_list (map string_to_bool
        (String.tokens Char.isSpace (only_hd (readl (file ^ "_flags")))))
    val playerid = only_hd (readl (file ^ "_playerid"))
    val nsim = string_to_int (only_hd (readl (file ^ "_nsim")))
  in
    (unib,dhtnn,noiseb,playerid,nsim)
  end

val pre_extsearch =
  {
  write_target = write_target,
  read_target = read_target,
  write_exl = write_exl,
  read_exl = read_exl,
  write_splayer = write_splayer,
  read_splayer = read_splayer
  }

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

val schedule_base =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]
val dhtnn_param_base =
  {
  operl = operl, nlayer_oper = 2,
  nlayer_headeval = 2, nlayer_headpoli = 2,
  dimin = 8, dimpoli = length movel
  }
val player_base =
  {playerid = "base",
   dhtnn_param = dhtnn_param_base, schedule = schedule_base}

val pretobdict = dnew String.compare
  [("base", (term_of_board, term_of_boardc))]

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rl_param =
  {expname = "mleResolution-3", ex_window = 80000,
   ncore_search = 40, nsim = 16000, decay = 1.0}

val rlpreobj : (board,move,unit) rlpreobj =
  {
  rl_param = rl_param,
  max_bigsteps = (fn (_,_,n) => n+1),
  game = game,
  pre_extsearch = pre_extsearch,
  pretobdict = pretobdict,
  precomp_dhtnn = (fn _ => (fn _ => ())),
  dplayerl = [player_base],
  level_targetl = level_targetl
  }

val extsearch = mk_extsearch "mleResolution.extsearch" rlpreobj
val rlobj = mk_rlobj rlpreobj extsearch

(*
load "mleResolution"; open mleResolution;
load "mlReinforce"; open mlReinforce;
val _ = rl_start_sync rlobj 4;
*)

end (* struct *)
