(* ========================================================================= *)
(* FILE          : mleDiophSynt.sml                                          *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleDiophSynt :> mleDiophSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce arithmeticTheory numLib

(* 
load "aiLib"; open aiLib;
load "numLib"; open numLib;
val ERR = mk_HOL_ERR "mleDiophSynt";
val version = 1
*)
(*

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

val modulo = 16;

fun eval_f tm =
  if is_var tm then 
    let val i = string_to_int (tl_string (fst (dest_var tm))) in
      (fn l => List.nth (l,i))
    end
  else if is_numeral tm then 
    let val n = int_of_term tm in (fn l => n) end
  else
  let val (oper,argl) = strip_comb tm
    else if term_eq oper ``$+`` then 
      let val (f1,f2) = pair_of_list (map eval_f argl) in
        fn l => (f1 l + f2 l) mod modulo
      end
    else if term_eq oper ``$*`` then
      let val (f1,f2) = pair_of_list (map eval_f argl) in
        fn l => (f1 l * f2 l) mod modulo
      end
    else raise ERR "eval_f" (tts tm)
  end;

val numberl = List.tabulate (modulo,I);
val numbertml =  ``NUMERAL ZERO`` :: 
  tl (map (Parse.Term o (fn x => [QUOTE (its x)])) numberl);

fun has_solution bl diophf k =
  let
    val l1 = cartesian_productl 
      (map (fn b => if b then numberl else [0]) bl)
    val l2 = map (fn l => k :: l) l1
  in
    exists (fn l => diophf l = 0) l2
  end

fun dioph_set diophtm = 
  let 
    val vl = free_vars diophtm
    fun test x = tmem x vl
    val bl = map test varl 
    val diophf = eval_f diophtm 
  in 
    filter (has_solution bl diophf) numberl
  end



type board = term * term * int
fun string_of_board (a,b,c)= tts a ^ " " ^ tts b ^ " " ^ its c

fun board_compare ((a,b,c),(d,e,f)) =
  (cpl_compare Term.compare Term.compare) ((a,b),(d,e))

fun status_of (diophset,tm2,n) =
  if not (can (find_term (fn x => term_eq x cX)) tm1) then
    let 
      val tm1a = dioph_match diophset
    in
      if isSome tm1o andalso term_eq (valOf tm1o) tm2 then Win else Lose
    end
  else if n <= 0
    then Lose else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term
val movel = 
  numbertml @ [``$+``,``$*``,``k0:num``,``k0:num``,``k0:num``,``k0:num``,``k0:num``,
``k0:num``,``k0:num``,``k0:num``,
``v1:num``,``v1:num``,``v1:num``,``v1:num``,``v2:num``,``v2:num``,``v3:num``]

val movel = 
  numbertml @ [``$+``,``$*``,``k0:num``,``v1:num``,``v2:num``,``v3:num``]
(* todo forbid addition or multiplication of numbers *)

val movel = 
  numbertml @ [``$+``,``$*``,``k0:num``,``v1:num``,``v2:num``,``v3:num``]

val varfreq =
 [``k0:num``,``k0:num``,``k0:num``,``k0:num``,``k0:num``,
  ``k0:num``,``k0:num``,``k0:num``,
  ``v1:num``,``v1:num``,``v1:num``,``v1:num``,``v2:num``,``v2:num``,``v3:num``]

can't sum two sums or 
product two products.



val basetml = numbertml @ [``k0:num``,``v1:num``,``v2:num``,``v3:num``];

val basevl = [``x:num``,``y:num``,``z:num``];
val ll = cartesian_productl (List.tabulate (length basevl,fn _ => expl));


fun random_monomial () = 
  let 
    val expl = [random_int (0,4),random_int (0,4),random_int (0,4)]
    val l = combine (basevl,expl)
    fun f (v,n) = if n = 0 then ``1`` else 
      list_mk_mult (List.tabulate (n,fn _ => v))
  in
    list_mk_mult (random_elem numbertml :: map f l)
  end

fun random_polynomial () =
  let val n = random_int (1,5) in
    list_mk_plus (List.tabulate (n, fn _ => random_monomial ()))
  end

val polyl = List.tabulate (1000, fn _ => random_polynomial ());
length polyl;
val diophl1 = map_assoc dioph_set polyl;
val diophl2 = dlist (dregroup (list_compare Int.compare) (map swap diophl1));
length diophl2;

fun dterm_size tm = 
  if is_var tm orelse is_numeral tm then 1 else
  let val (oper,argl) = strip_comb tm in
    1 + sum_int (map dterm_size argl)
  end


fun gen_diophset n d =
  if dlength d >= n then d else
  let 
    val tm = random_polynomial () 
    val set = dioph_set tm
  in
    if dmem set d then 
      let val oldtm = dfind set d in
        if dterm_size tm < dterm_size oldtm 
        then gen_diophset n (dadd set tm d)
        else gen_diophset n d
      end
    else (print_endline (its ((dlength d) + 1)); 
          gen_diophset n (dadd set tm d))
  end


val d = gen_diophset 1000 (dempty (list_compare Int.compare));
load "mlTacticData"; open mlTacticData;

fun ilts il = String.concatWith " " (map its il);
val _ = writel  (HOLDIR ^ "/src/AI/experiments/diophgraph") (map (ilts o fst) (dlist d));
val _ = export_terml (HOLDIR ^ "/src/AI/experiments/diophlist")
  (map snd (dlist d));


val movel1 = 
  List.tabulate (16, fn i => mk_var ("n" ^ its i, alpha));
val movel2 = 
  [
   mk_var ("eplus",``:'a -> b -> num``),
   mk_var ("emult",``:'a -> num -> num``),
   mk_var ("mult",``:num -> num -> num``) 
  ]
val operl = [``k0:num``,``v1:num``,``v2:num``,``v3:num``] @ movel1 @ movel2;
val l0 = gen_term operl (5,``:num``); length l0;

fun contain_k0 tm = tmem ``k0:num`` (free_vars tm);
load "psTermGen"; open psTermGen;

val l1 = filter contain_k0 l0; length l1;

val tm = random_term movel (9,``:num``);
val il = dioph_set tm;

val move_compare = Term.compare

fun apply_move move tm1 = 
  let
    val res = list_mk_comb (move, List.tabulate (arity_of move, fn _ => cX))
    val sub = [{redex = cX, residue = res}]
  in
    subst_occs [[1]] sub tm1
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
  {expname = "mleDiophSynt-combin-" ^ its version, exwindow = 100000,
   ncore = 30, ntarget = 100, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {
  rlparam = rlparam,
  game = game,
  gameio = gameio,
  dplayer = dplayer
  }

val extsearch = mk_extsearch "mleDiophSynt.extsearch" rlobj

(*
load "mleDiophSynt"; open mleDiophSynt;
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
load "mleDiophSynt"; open mleDiophSynt;
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
load "mleDiophSynt"; open mleDiophSynt;

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
load "mleDiophSynt"; open mleDiophSynt;
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
*)

end (* struct *)
