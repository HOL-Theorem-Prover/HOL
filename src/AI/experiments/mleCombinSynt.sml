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
  mlReinforce mleLib

val ERR = mk_HOL_ERR "mleSynthesize"
val version = 12

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = term * term * int
fun string_of_board (a,b,c)= tts a ^ " " ^ tts b ^ " " ^ its c

fun board_compare ((a,b,c),(d,e,f)) =
  (cpl_compare Term.compare Term.compare) ((a,b),(d,e))

val k_thm_bare = List.nth (eq_axl_bare,1)

fun status_of (tm1,tm2,n) =
  if not (can (find_term (fn x => term_eq x cX)) tm1) then
    let 
      val tm1a = list_mk_cA [tm1,v1,v2,v3]
      val tm1o = fast_lo_cnorm 100 eq_axl_bare tm1a
    in
      if isSome tm1o andalso term_eq (valOf tm1o) tm2 then Win else Lose
    end
  else if n <= 0 orelse can (find_term (fn x => is_match k_thm_bare x)) tm1
    then Lose else Undecided

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
val targetfile = targetdir ^ "/targetl-synt"
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

fun create_targetl tml =
  let
    val i = ref 0
    fun f tm = 
      let val tmo = fast_lo_cnorm 100 eq_axl_bare (list_mk_cA [tm,v1,v2,v3])
      in
        if not (isSome tmo) orelse 
           can (find_term (C tmem [cS,cK])) (valOf tmo)
        then NONE
        else (print_endline (its (!i)); incr i; tmo)
      end
    val l1 = map_assoc f tml    
    val l2 = filter (fn x => isSome (snd x)) l1    
    val l3 = map_snd valOf l2
    val l4 = dregroup Term.compare (map swap l3)
    val l5 = map_snd (list_imin o map term_size) (dlist l4)
    val l6 = map (fn (a,b) => (cX,a,2 * b)) l5
  in
    stats_il "size_in" (map (term_size o #1) l6);
    stats_il "size_out" (map (term_size o #2) l6);
    stats_il "nstep" (map ((fn x => x div 2) o #3) l6);
    dict_sort (compare_third Int.compare) l6
  end

fun create_policy_supervised tml =
  let
    val i = ref 0
    fun f tm = 
      let val tmo = fast_lo_cnorm 100 eq_axl_bare (list_mk_cA [tm,v1,v2,v3])
      in
        if not (isSome tmo) orelse 
           can (find_term (C tmem [cS,cK])) (valOf tmo)
        then NONE
        else (print_endline (its (!i)); incr i; tmo)
      end
    val l1 = map_assoc f tml    
    val l2 = filter (fn x => isSome (snd x)) l1    
    val l3 = map_snd valOf l2
    val d = dregroup Term.compare (map swap l3)
  in
    d
  end

fun export_targetl name targetl = 
  let val _ = mkDir_err targetdir in 
    write_boardl (targetfile ^ "-" ^ name) targetl
  end

fun import_targetl name = read_boardl (targetfile ^ "-" ^ name)
 
fun mk_targetd l1 =
  let 
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:bool -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)
fun tob (tm1,tm2,_) = 
  [tag_heval (mk_eq (tm1,tm2)), tag_hpoli (mk_eq (tm1,tm2))]

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val dim = 12
fun dim_head_poli n = [dim,n]
val equality = ``$= : 'a -> 'a -> bool``
val tnnparam = map_assoc (dim_std (1,dim)) [equality,cX,v1,v2,v3,cA,cS,cK] @ 
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleSynthesize-combin-" ^ its version, exwindow = 100000,
   ncore = 30, ntarget = 100, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleSynthesize.extsearch" rlobj

(*
load "mleSynthesize"; open mleSynthesize;
load "mlReinforce"; open mlReinforce;
load "aiLib"; open aiLib;
load "mleLib"; open mleLib;

val tml = cgen_synt 9; length tml;
val targetl1 = create_targetl tml; length targetl1;
fun cmp (b1,b2) = cpl_compare 
  (compare_third Int.compare) (#board_compare (#game rlobj)) 
  ((b1,b1),(b2,b2));
val targetl2 = dict_sort cmp targetl1;
val _ = export_targetl "sy9" targetl2;

val r = rl_start (rlobj,extsearch) (mk_targetd (import_targetl "sy9"));
(* todo output the number of theorem proven at least once *)
*)

(* -------------------------------------------------------------------------
   Transformation of problems to ATP goals
   ------------------------------------------------------------------------- *)

val vc = mk_var ("Vc",alpha)

fun goal_of_board_eq (_,tm2,n) =
  let val tm =
    mk_exists (vc, (list_mk_forall ([v1,v2,v3], 
      mk_eq (list_mk_cA [vc,v1,v2,v3],tm2))))
  in
    (eq_axl,tm)
  end

fun goal_of_board_rw (_,tm2,n) =
  let val tm =
    mk_exists (vc, (list_mk_forall ([v1,v2,v3], 
      mk_cRW (list_mk_cA [vc,v1,v2,v3],tm2))))
  in
    (rw_axl,tm)
  end

fun goal_of_board_ev (_,tm2,n) =
  let val tm =
    mk_exists (vc, (list_mk_forall ([v1,v2,v3], 
      list_mk_imp (map (fn x => mk_cEV (x,x)) [v1,v2,v3],
        mk_cEV (list_mk_cA [vc,v1,v2,v3],tm2)))))
  in
    (ev_axl,tm)
  end


(* -------------------------------------------------------------------------
   TPTP export
   ------------------------------------------------------------------------- *)

(*
load "mlReinforce"; open mlReinforce;
load "mleLib"; open mleLib;
load "aiLib"; open aiLib;
load "mleSynthesize"; open mleSynthesize;
load "hhExportFof"; open hhExportFof;

val tml = cgen_synt 10; length tml;
val targetl1 = create_targetl tml; length targetl;
fun cmp (b1,b2) = cpl_compare 
  (compare_third Int.compare) (#board_compare (#game rlobj)) 
  ((b1,b1),(b2,b2));
val targetl2 = dict_sort cmp targetl1;

val _ = export_targetl "sy10" targetl2;
val targetl3 = import_targetl "sy10";

val targetl4 = map (fn (a,b,x) => (a,b,((x div 2) + 1) div 2)) targetl3;
fun select y = filter (fn (_,_,x) => x <= y) targetl4;

fun export_goal dir (goal,n) =
  let 
    val tptp_dir = HOLDIR ^ "/src/AI/experiments/TPTP"
    val _ = mkDir_err tptp_dir
    val file = tptp_dir ^ "/" ^ dir ^ "/i/" ^ its n ^ ".p"
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir)
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/i")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/o")
  in 
    name_flag := false;
    type_flag := false;
    p_flag := false;
    fof_export_goal file goal
  end;

fun tptp_targetl size = 
  let 
    val prefix = "sy" ^ its size 
    val targetl = select size
    val goall_eq = map goal_of_board_eq targetl
    val goall_rw = map goal_of_board_rw targetl
    val goall_ev = map goal_of_board_ev targetl
  in
    app (export_goal (prefix ^ "-eq")) (number_snd 0 goall_eq);
    app (export_goal (prefix ^ "-rw")) (number_snd 0 goall_rw);
    app (export_goal (prefix ^ "-ev")) (number_snd 0 goall_ev)
  end;

app tptp_targetl (List.tabulate (10, fn x => x + 1));
*)

(* -------------------------------------------------------------------------
   Supervised learning for the policy.
   ------------------------------------------------------------------------- *)

(*
load "mleLib"; open mleLib;
load "aiLib"; open aiLib;
load "mleSynthesize"; open mleSynthesize;

val tml = cgen_synt 9; length tml;
val d = create_policy_supervised tml;

fun reduces l =
  let 
    val l1 = map_assoc term_size l
    val n = list_imin (map snd l1) 
  in
    map fst (filter (fn x => snd x = n) l1)
  end

val ll = map_snd reduces (dlist d);

val game = #game rlobj;

fun is_ground tm = not (can (find_term (fn x => term_eq x cX)) tm)

fun rename_cX maintm = 
  let
  fun loop i tm =
    if is_ground tm then tm else
      let val sub = [{redex = cX, residue = mk_var ("X" ^ its i,alpha)}] in    
        loop (i+1) (subst_occs [[1]] sub tm)
      end
  in
    loop 0 maintm
  end;

fun eq_of tm1 = mk_eq (rename_cX tm1,cX)
fun is_correct l ((tm1,_,_):board) = exists (is_match (eq_of tm1)) l;
fun one_ex l board = 
  let 
    val boardl = map (fn x => (#apply_move game) x board) (#movel game) 
    fun test x = is_correct l x
    fun f x = if test x then 1.0 else 0.0
  in
    ((board,map f boardl), filter test boardl)
  end;
fun all_ex l board =
  if #status_of game board <> psMCTS.Undecided then [] else 
    let val (ex,boardl) = one_ex l board in
      ex :: List.concat (map (all_ex l) boardl)
    end;

fun all_ex_fin (a,l) = all_ex l (cX,a,10000);
val exl = List.concat (map all_ex_fin ll);

val trainex = map (fn ((tm1,tm2,_),rl) => [(mk_eq (tm1,tm2),rl)]) exl;
write_tnnex "/home/thibault/test" trainex;

load "mleLib"; open mleLib;
load "aiLib"; open aiLib;
load "mleSynthesize"; open mleSynthesize;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val trainex = read_tnnex "/home/thibault/test";

val schedule = [{ncore = 1, verbose = true,
   learning_rate = 0.02, batch_size = 16, nepoch = 100}];
val dim = 12;
val equality = ``$= : 'a -> 'a -> bool``;
val tnnparam = map_assoc (dim_std (2,dim)) [cX,cA,cS,cK,v1,v2,v3] @ 
  [(equality,[2*dim,dim,3])];
val tnn = train_tnn schedule (random_tnn tnnparam) (part_pct 0.95 trainex);

*)


end (* struct *)
