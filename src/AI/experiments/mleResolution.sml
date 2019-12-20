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
type 'a set = ('a, unit) Redblackmap.dict

(* -------------------------------------------------------------------------
   Comparison function
   ------------------------------------------------------------------------- *)

val lit_compare = cpl_compare Int.compare bool_compare
fun dict_compare cmp (d1,d2) = list_compare cmp (dlist d1, dlist d2)
val clause_compare = dict_compare (cpl_compare Int.compare bool_compare)
fun set_compare cmp (d1,d2) = list_compare cmp (dkeys d1, dkeys d2)

fun lookup_clause d c = List.nth (dkeys d, c)
  handle Subscript => raise ERR "lookup_clause" ""

(* -------------------------------------------------------------------------
   Resolution
   ------------------------------------------------------------------------- *)

fun find_uniq test l = case l of
    [] => NONE
  | a :: m => 
    (if test a 
     then (if not (exists test m) then SOME a else NONE)
     else find_uniq test m)

fun find_match (d1,d2) =
  let fun test (i,b) = (dfind i d2 = not b handle NotFound => false) in
    Option.map fst (find_uniq test (dlist d1)) 
  end
        
fun is_match (d1,d2) = isSome (find_match (d1,d2))

fun resolve_at (d1,d2) i =
  daddl (dlist (drem i d1)) (drem i d2)

fun resolve_pair d (d1,d2) = case find_match (d1,d2) of
    SOME i => 
    let val clause = resolve_at (d1,d2) i in
      if dmem clause d then NONE else SOME clause
    end
  | NONE => NONE

fun resolve_pairi d (c1,c2)= 
  resolve_pair d (lookup_clause d c1, lookup_clause d c2)

fun has_effect d (d1,d2) = isSome (resolve_pair d (d1,d2))
fun exists_effect pb d =
  exists (fn x => has_effect pb (d,x)) (dkeys pb)

fun has_effecti d (c1,c2) =
  can (lookup_clause d) c1 andalso
  can (lookup_clause d) c2 andalso
  has_effect d (lookup_clause d c1, lookup_clause d c2)
fun exists_effecti d c =
  exists (fn x => has_effecti d (c,x)) (List.tabulate (dlength d, I))

fun is_saturated d = not (exists (exists_effect d) (dkeys d))

(* -------------------------------------------------------------------------
   Calculate difficulty
   ------------------------------------------------------------------------- *)

fun all_pairs l = case l of
    [] => []
  | [a] => []
  | a :: m => map (fn x => (a,x)) m @ all_pairs m

fun resolve_pair_cost pb ((d1,n1),(d2,n2)) = case find_match (d1,d2) of
    SOME i => 
    let val clause = resolve_at (d1,d2) i in
      if dmem clause pb then NONE else SOME (clause, n1 + n2 + 1)
    end
  | NONE => NONE

fun resolve_all (pb,sep) =
  let 
    val (l1,l2) = part_n sep (dlist pb)
    val ll = all_pairs l2 @ cartesian_product l1 l2 
  in
    List.mapPartial (resolve_pair_cost pb) ll
  end

val empty_clause = dempty Int.compare

fun brute_pb_aux (i,n) (pb,sep) =
  if dmem empty_clause pb
    then ("solved", dfind empty_clause pb) 
  else if i >= n 
    then ("timeout",i) 
  else
    let val clausel = resolve_all (pb,sep) in
      if null clausel then ("saturated", i+1) else
      brute_pb_aux (i+1,n) (daddl clausel pb, dlength pb)
    end

fun brute_pb n pb = 
  brute_pb_aux (0,n) (dmap (fn _ => 0) pb, 0)

fun difficulty maxdepth pb = case brute_pb maxdepth pb of
    ("solved", i) => SOME i
  | _ => NONE

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

(* -------------------------------------------------------------------------
   Generation
   ------------------------------------------------------------------------- *)

fun random_lit i = (i,random_elem [true,false])

fun random_clause maxlit = 
  let 
    fun f i = if random_int (0,1) = 0 then [random_lit i] else [] 
    val l = List.concat (List.tabulate (maxlit, f))
  in
    if null l 
    then random_clause maxlit
    else dnew Int.compare l
  end

fun random_pb nclause maxlit =
  let val dl = List.tabulate (nclause, fn _ => random_clause maxlit) in
    dset clause_compare dl
  end

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

fun max_bigsteps (_,_,n) = n

(* -------------------------------------------------------------------------
   Initialization of the levels
   ------------------------------------------------------------------------- *)

val data_dir = HOLDIR ^ "/src/AI/experiments/data_resolution"

fun bin_to_string bin = String.concatWith "," (map its bin)

(*
fun create_levels () =
  let
    val _ = print_endline ("Generating 100000 problems")
    val pbl = List.tabulate (100000, fn _ => random_pb 5 5)
    val _ = print_endline ("Removing satisfiables")
    val pbl_unsat = filter (not o satisfiable_pb) pbl
    val _ = print_endline ("  " ^ its (length pbl_unsat))
    val _ = print_endline ("Iterative deepening with depth 5")
    val rl = map_assoc (brute_pb 5) pbl_unsat
    val rl_solved = filter (fn x => #1 (snd x) = "solved") rl
    val rl_saturated = filter (fn x => #1 (snd x) = "saturated") rl
    val rl_timeout = filter (fn x => #1 (snd x) = "timeout") rl
    val rl_nontriv = filter (fn x => #2 (snd x) >= 1) rl_solved
    fun f (s,l) = print (s ^ " " ^ its (length l) ^ "  ")
    val _ = print "  "
    val _ = app f [("solved",rl_solved),("saturated",rl_saturated),
                   ("timeout",rl_timeout)]
    val _ = print_endline (its (length rl_nontriv) ^ " non-trivial")
    val pbl_diff = map difficulty rl_nontriv
    val pbl1 = dict_sort compare_imin (filter (fn x => snd x <= 20) pbl_diff)
    val _ = print_endline
      ("Exporting " ^ its (length pbl1) ^ " problems")
  in
    export_terml (data_dir ^ "/levels_term") (map (term_of_pb o fst) pbl1);
    writel (data_dir ^ "/levels_diff") (map (its o snd) pbl1)
  end
*)

fun random_solvable maxdepth maxdiff = 
  let 
    fun loop () =
      let val pb' = random_pb 5 5 in 
        if satisfiable_pb pb' then loop () else pb'
      end
    val pb = loop ()
  in
    case difficulty maxdepth pb of
      SOME i => if i > maxdiff 
                then random_solvable maxdepth maxdiff
                else (pb,i)
    | NONE => random_solvable maxdepth maxdiff
  end

fun equi_div n m =
  let 
    val l1 = List.tabulate (m, fn _ => n div m)
    val l2 = number_snd 0 l1
    val r = n mod m
    fun f (k,i) = if i < r then k + 1 else k
  in  
    map f l2
  end

fun mk_limitd n m =
  let val l = equi_div n m in
    dnew Int.compare (number_fst 1 l)
  end

fun collect_solvable_aux (rd,limitd) =
  if dlength limitd = 0 then rd else
  let val (pb,diff) = random_solvable 6 20 in
    if not (dmem diff limitd) then collect_solvable_aux (rd,limitd) else 
    let 
      val oldpbl = dfind diff rd handle NotFound => []
      val newpbl = pb :: oldpbl
      val newrd = dadd diff newpbl rd
      val limit = dfind diff limitd
      val newlimit = limit - 1
      val newlimitd = 
        if newlimit <= 0 
        then drem diff limitd 
        else dadd diff newlimit limitd 
    in
      collect_solvable_aux (newrd,newlimitd)
    end
  end

fun collect_solvable level = 
  collect_solvable_aux (dempty Int.compare, mk_limitd 400 level)   

fun level_targetl level =
  let 
    val level_alt = if level >= 10 then 10 else level
    val pbll = dlist (collect_solvable level_alt)
    fun f (diff,pbl) = map (fn pb => (pb, NONE, 4 * diff)) pbl
  in
    List.concat (map f (rev pbll))
  end

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
    ncore_search = 5, nsim = 160, decay = 1.0}

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
val l = time level_targetl 8;
length l;
val _ = rl_start_sync rlobj 1;
*)

end (* struct *)
