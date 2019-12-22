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

load "aiLib"; open aiLib;

val ERR = mk_HOL_ERR "mleResolution"

(* -------------------------------------------------------------------------
   Comparison function
   ------------------------------------------------------------------------- *)

type clause = (int * bool) list
val lit_compare = cpl_compare Int.compare bool_compare
val clause_compare = list_compare lit_compare 

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
  
fun resolve_ctxt cd (c1,c2) = 
  let val c = resolve (c1,c2) in 
    if dmem c cd then raise ERR "resolve_ctxt" "" else r
  end

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
      if dlength d >= nlit then d else
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
   Exhaustive generation
   ------------------------------------------------------------------------- *)

(*
val all_clauses = cartesian_productl (List.tabulate (5,fn _ => [~1,0,1]));

fun subsume l1 l2 = 
  all (fn (a,b) => a = 0 orelse a = b) (combine (l1,l2))

fun all_subsumed l =
  filter (fn x => subsume l x andalso l <> x) all_clauses;

val ordered_clauses = 
  rev (topo_sort (list_compare Int.compare) (map_assoc all_subsumed 
  all_clauses))

val clausen_dict = dnew (list_compare Int.compare) (number_snd 0 ordered_clauses);
val nclause_dict = dnew Int.compare (map swap (dlist clausen_dict));

fun non_empty l = exists (fn x => x <> 0) l

fun remove_abs1 l = case l of
    [] => []
  | a :: m => if (a = 1 orelse a = ~1) then remove_abs1 m else l

fun leading_abs1 l = case l of
    [] => 0
  | a :: m => if (a = 1 orelse a = ~1) then 1 + leading_abs1 m else 0

fun union l1 l2 = 
  map (fn (a,b) => if (a = 1 orelse a = ~1) andalso (b = 1 orelse b = ~1)
                   then 1
                   else 0) (combine (l1,l2));

fun unionl ll = case ll of
    [] => raise ERR "unionl" ""
  | [l] => l
  | l :: m => union l (unionl m)

fun remove_zero l = case l of
    [] => []
  | a :: m => if a = 0 then remove_zero m else l

fun is_normal c = null (remove_zero (remove_abs1 c))

val clause1 = 
  let fun test x = non_empty x andalso is_normal x in
    map single (filter test all_clauses)
  end

fun add_exhaustive pb =
  let 
    val k = leading_abs1 (unionl pb)
    val ci = dfind (hd pb) clausen_dict
    fun is_normal x = 
      null (remove_zero (remove_abs1 (snd (part_n k x))))
    fun is_incr x = dfind x clausen_dict > ci
    fun is_subsumed x = exists (fn y => subsume y x) pb 
    fun test x = 
      non_empty x andalso is_normal x andalso is_incr x andalso
      not (is_subsumed x)
    val cl = filter test all_clauses
  in
    map (fn x => x :: pb) cl
  end

val clause2 = List.concat (map add_exhaustive clause1);
val clause3 = List.concat (map add_exhaustive clause2);
val clause4 = List.concat (map add_exhaustive clause3);
val clause5 = List.concat (time (map add_exhaustive) clause4);

fun convert_clause l = 
  let  
    val l1 = number_fst 0 l
    val l2 = filter (fn x => snd x <> 0) l1
    val l3 = map_snd (fn x => if x = 1 then true else false) l2
  in
    dnew Int.compare l3
  end

fun convert_pb ll = dset clause_compare (map convert_clause ll)



val pbl_solvablel =
  map (filter (not o is_sat)) [clause2,clause3,clause4,clause5];
map length pbl_solvablel;

val pbl_solvable = List.concat pbl_solvablel;

val pbl = map convert_pb pbl_solvable;
load "mleResolution"; open mleResolution;
val pbl_diff = map_assoc (difficulty 32) pbl;
val pbl_diff2 = map_snd valOf pbl_diff;
val d = dregroup Int.compare (map swap pbl_diff2);
dfind 1 d;
fun view pb = map dlist (dkeys pb);
val l = map view (dfind 1 d);
*)


(*
load "aiLib"; open aiLib;

(* backward *)
fun parents_of pivot c =
  let fun f i x = 
    if i = pivot then (1,~1) else
    if x <> 0 then random_elem [(0,x),(x,0),(x,x)] else (0,0)
  in
    split (mapi f c)
  end

fun backward_step c = 
  let val pivotl = map snd (filter (fn x => fst x = 0) (number_snd 0 c)) in
    if null pivotl then NONE else SOME (parents_of (random_elem pivotl) c)
  end

fun backward_step_pb pb = 
  let val l = shuffle pb in
    case backward_step (hd l) of
      NONE => NONE
    | SOME (a,b) => 
        SOME (mk_fast_set (list_compare Int.compare) (a :: b :: tl l))
  end

fun n_bstep_aux (i,n) pb =
  if i >= n then (pb,n) else
    (
    case backward_step_pb pb of
      NONE => (pb,i)
    | SOME newpb => n_bstep_aux (i+1,n) newpb
    )

fun n_bstep n = n_bstep_aux (0,n) [[0,0,0,0,0]]

val (pb,i) = n_bstep 15;

(* resolution *)
val ERR = mk_HOL_ERR "test";

fun resolve_one bo (a,b) = 
  if a <> 0 andalso a = ~b then 
    (if bo then raise ERR "resolve_one" "" else (0,true)) 
  else 
    (if a = 0 then (b,bo) else (a,bo))

fun resolve_aux bo l1 l2 = case (l1,l2) of
    ([],[]) => if bo then [] else raise ERR "resolve_aux" ""
  | (a1 :: m1, a2 :: m2) => 
    let val (a3,newbo) = resolve_one bo (a1,a2) in
      a3 :: resolve_aux newbo m1 m2
    end
  | _ => raise ERR "resolve_aux" ""

fun resolve l1 l2 = resolve_aux false l1 l2;




val pbl = map fst (List.tabulate (1000, fn _ => n_bstep (random_int (5,32))));
val pbil = map_assoc (difficulty 32) pbl;
val pbil2 = map_snd valOf pbil; 
val d = dregroup Int.compare (map swap pbil2);
map_snd length (dlist d);


*)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

val max_clauses = 20

type clause = (int, bool) Redblackmap.dict
val clause_compare = dict_compare lit_compare

type board = clause set * int option * int

fun mk_startboard pb = (pb, NONE, 40)

fun triple_compare cmp1 cmp2 cmp3 ((a1,a2,a3),(b1,b2,b3)) = 
  cpl_compare (cpl_compare cmp1 cmp2) cmp3 (((a1,a2),a3),((b1,b2),b3))

val board_compare =
  triple_compare 
    (set_compare clause_compare)
    (option_compare Int.compare)
    Int.compare

fun string_of_board _ = "board"

fun status_of (d,_,n) =
  if exists (fn x => dlength x = 0) (dkeys d) 
    then Win 
  else if n <= 0 orelse dlength d <= 0 orelse dlength d >= max_clauses orelse
          is_saturated d
    then Lose
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

fun term_of_clause c = list_mk_disj (map mk_lit (dlist c))
fun clause_of_term ctm = 
  dnew Int.compare (map lit_of_term (strip_disj ctm))

fun term_of_pb d = list_mk_conj (map term_of_clause (dkeys d))
fun pb_of_term tm = dset clause_compare (map clause_of_term (strip_conj tm))

val focus_cat = mk_var ("focus_cat", ``:bool -> bool -> bool``)
fun term_of_board (d,co,_) = case co of
    SOME ci => list_mk_comb (focus_cat, 
      [term_of_clause (lookup_clause d ci), term_of_pb d])
  | NONE => term_of_pb d
fun board_of_term tm = 
  let val (oper,argl) = strip_comb tm in
    if term_eq oper focus_cat 
    then 
      let 
        val (ctm,pbtm) = pair_of_list argl 
        val clause = clause_of_term ctm
        val pb = pb_of_term pbtm
        val pb' = dnew clause_compare (number_snd 0 (dkeys pb))
      in
        (pb, SOME (dfind clause pb'))
      end
    else (pb_of_term tm, NONE)
  end

val operl_aux = List.tabulate (5,mk_bvar) @ 
  [focus_cat, ``$~``,``$/\``,``$\/``]
val operl = mk_fast_set oper_compare (map_assoc arity_of operl_aux);
fun term_of_boardc (_:unit) b = term_of_board b

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val board = dset clause_compare
   [dnew Int.compare [(0,true),(1,false),(2,true)]];
val tm = term_of_board (board,NONE,0);
*)

(*
load "aiLib"; open aiLib;
val l = List.tabulate (100, fn x => random_elem [0,1]);
val n = sum_int l;
*)



fun eval_lit assign (i,b) = 
  if b then dfind i assign else not (dfind i assign)

fun eval_clause assign clause = 
  exists (eval_lit assign) (dlist clause)

fun eval_pb_assign assign pb = 
  all (eval_clause assign) (dkeys pb)

val all_assign = 
  map (dnew Int.compare)
  (cartesian_productl (List.tabulate (5,fn x => [(x,true),(x,false)])))

fun satisfiable_pb pb = 
  exists (C eval_pb_assign pb) all_assign

(* 
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val pb = random_pb 5 5;
val l = map dlist (dkeys pb);
val b = satisfiable_pb pb;
val r = brute_pb 5 pb;
*)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Select of int | Delete of int
fun is_select m = case m of Select _ => true | _ => false
fun is_delete m = case m of Delete _ => true | _ => false

fun string_of_move m = case m of
    Select c => "s" ^ its c
  | Delete c => "c" ^ its c

val movel = List.tabulate (max_clauses, Select) @ 
  List.tabulate (max_clauses, Delete)

fun move_compare (a,b) = String.compare (string_of_move a, string_of_move b)

fun available_move board move = 
  let 
    val d = #1 board
    val n = dlength d
    val cl = List.tabulate (n,I)
  in
    case #2 board of
      NONE => (case move of 
          Select c1 => n < max_clauses andalso exists_effecti d c1
        | Delete c => false)
    | SOME c1 => (case move of 
          Select c2 => has_effecti d (c1,c2) 
        | Delete c => false)
  end

fun apply_move move (d,c1o,n) = case move of
    Delete c => (drem (lookup_clause d c) d, NONE, n-1)  
  | Select c => (case c1o of
      NONE => (d, SOME c, n-1)
    | SOME c1 => (dadd (valOf (resolve_pairi d (c1,c))) () d, NONE, n-1))

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

fun mcts_test nsim pb =
  let
    val mcts_obj =
      {mcts_param = mk_mcts_param nsim,
       game = game,
       player = uniform_player game}
    val tree = starttree_of mcts_obj (mk_startboard pb)
    val endtree = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    if b then print_endline "Win" else print_endline "Lose"; 
    (b, endtree)
  end

(* -------------------------------------------------------------------------
   Big steps limit (redundant with status_of)
   ------------------------------------------------------------------------- *)

fun max_bigsteps (_,_,n) = n+1

(* -------------------------------------------------------------------------
   Initialization of the levels
   ------------------------------------------------------------------------- *)

val data_dir = HOLDIR ^ "/src/AI/experiments/data_resolution"

fun level_pb level =
  let 
    val nvar = random_int (4,level)
    val nlit = 3
    val nclause = random_int (nvar * 4, nvar * 5)   
    fun loop () =
      let val pb = random_pb nclause nlit nvar in
        if is_sat pb then loop () else pb
      end
  in
    loop ()
  end

fun level_targetl level =
  map (fn x => (x,NONE,40)) (List.tabulate (400, fn _=> level_pb level))

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val (_,_,l3) = split_triple boardl in
    export_terml (file ^ "_pboard") (map term_of_board boardl);
    writel (file ^ "_diff") (map its l3)
  end
fun read_boardl file =
  let
    val pboardl = map board_of_term (import_terml (file ^ "_pboard"))
    val diffl = map string_to_int (readl (file ^ "_diff"))
  in
    map (fn ((a,b),c) => (a,b,c)) (combine (pboardl,diffl))
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
  { expname = "mleResolution-1", ex_window = 40000,
    ncore_search = 40, nsim = 160, decay = 1.0}

val rlpreobj : (board,move,unit) rlpreobj =
  {
  rl_param = rl_param,
  max_bigsteps = max_bigsteps,
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
val _ = rl_start_sync rlobj 1;
*)

end (* struct *)
