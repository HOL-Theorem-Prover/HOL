(* ========================================================================= *)
(* FILE          : mleTacticToe.sml                                          *)
(* DESCRIPTION   : Tactical proof search as a game                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleTacticToe :> mleTacticToe =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlFeature mlNearestNeighbor
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mlReinforce mleLib

val ERR = mk_HOL_ERR "mleTacticToe"

val ttt_empty = mk_var ("ttt_empty", alpha)
val ttt_thm_concat = mk_var ("ttt_thm_concat", ``:'a -> 'a -> 'a``)

(* -------------------------------------------------------------------------
   Deleting theorems from the global simpsets
   ------------------------------------------------------------------------- *)

val delsimps = ["HD", "TL_DEF", "APPEND", "FLAT", "LENGTH", "MAP", 
"LIST_TO_SET_DEF", "FILTER", "EVERY_DEF", "EXISTS_DEF", "MAP2_DEF", 
"APPEND_NIL", "LENGTH_APPEND", "MAP_ID", "FLAT_APPEND", "EL_restricted", 
"EL_simp_restricted", "LIST_REL_def", "LIST_REL_NIL", "REVERSE_DEF", 
"REVERSE_REVERSE", "REVERSE_11", "MEM_REVERSE", "LENGTH_REVERSE", 
"REVERSE_EQ_NIL", "REVERSE_EQ_SING", "LAST_CONS", "FRONT_CONS", 
"LENGTH_FRONT_CONS", "FRONT_CONS_EQ_NIL", "LAST_APPEND_CONS", "TAKE_nil", 
"TAKE_cons", "DROP_nil", "DROP_cons", "TAKE_0", "TAKE_LENGTH_ID", 
"LENGTH_TAKE", "DROP_0", "TAKE_DROP", "LENGTH_DROP", "ALL_DISTINCT", 
"LIST_TO_SET_APPEND", "LIST_TO_SET_EQ_EMPTY", "FINITE_LIST_TO_SET", 
"LIST_TO_SET_REVERSE", "SET_TO_LIST_EMPTY", "SET_TO_LIST_SING", 
"ALL_DISTINCT_SET_TO_LIST", "isPREFIX", "isPREFIX_THM", "SNOC", "LENGTH_SNOC", 
"LAST_SNOC", "FRONT_SNOC", "SNOC_11", "LENGTH_GENLIST", "GENLIST_AUX_compute", 
"EL_GENLIST", "GENLIST_NUMERALS", "INFINITE_LIST_UNIV", "LENGTH_LUPDATE", 
"LIST_BIND_THM", "SINGL_LIST_APPLY_L", "SINGL_SINGL_APPLY", "dropWhile_def", 
"APPEND_11", "MAP2_NIL", "LENGTH_MAP2", "MAP_EQ_NIL", "MAP_EQ_SING", 
"LENGTH_NIL", "LENGTH_NIL_SYM", "ALL_DISTINCT_REVERSE", 
"ALL_DISTINCT_FLAT_REVERSE", "isPREFIX_NILR", "LUPDATE_NIL", "SHORTLEX_THM", 
"SHORTLEX_NIL2", "WF_SHORTLEX", "LLEX_THM", "LLEX_NIL2", "nub_set", 
"EVERY2_THM", "oHD_thm", "LIST_TO_SET", "LENGTH_MAP", "MEM_APPEND", "SING_HD", 
"APPEND_eq_NIL", "NULL_APPEND", "FILTER_F", "FILTER_T", "MEM", 
"LENGTH_ZIP_MIN", "LAST_MAP", "TAKE_EQ_NIL", "MEM_SET_TO_LIST", "MEM_SNOC", 
"LIST_REL_eq","CONS.1", "CONS_11.1", "CONS_11.2",
"CONS_ACYCLIC.1", "CONS_ACYCLIC.2","CONS_ACYCLIC.3", "CONS_ACYCLIC.4",
"EVERY_APPEND.1", "EVERY_SIMP.1","EXISTS_APPEND.1", "EXISTS_SIMP.1",
"FOLDL.1", "FOLDL.2", "FOLDL2_def.1","FOLDL2_def.2", "FOLDL2_def.3",
"FOLDL_ZIP_SAME.1", "FOLDR.1","FOLDR.2", "LENGTH_UNZIP.1","LENGTH_UNZIP.2", 
"LENGTH_ZIP.1","LENGTH_ZIP.2", "LUPDATE_LENGTH.1","MAP2.1", "MAP2.2", 
"MAP_APPEND.1","MAP_ZIP_SAME.1", "NOT_CONS_NIL.1",
"NOT_CONS_NIL.2", "NOT_EVERY.1","NOT_EXISTS.1", "NOT_NIL_CONS.1",
"NOT_NIL_CONS.2", "NULL_DEF.1","NULL_DEF.2", "SUM.1", "SUM.2",
"UNZIP.1", "UNZIP.2", "UNZIP_ZIP.1","ZIP.1", "ZIP.2", "ZIP_UNZIP.1",
"list_case_def.1", "list_case_def.2"];

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (goal list * goal list) * term * (int * int)

fun subset_goal gl1 gl2 =
  let val d = dset goal_compare gl2 in 
    all (fn x => dmem x d) gl1
  end

fun board_compare ((a,b,c),(e,f,g)) = 
  cpl_compare (
    cpl_compare (list_compare goal_compare) (list_compare goal_compare)) 
    (cpl_compare Term.compare (cpl_compare Int.compare Int.compare)) 
    ((a,(b,c)),(e,(f,g)))

fun string_of_goall gl =
  String.concatWith ", " (map string_of_goal gl)

fun string_of_board ((gl1,gl2),tactm,(n,m)) =
  string_of_goall gl1 ^ "\n" ^ string_of_goall gl2 ^ "\n" ^ 
  its n ^ " " ^ its m ^ " " ^ term_to_string tactm

fun mk_startboard a = (a,ttt_empty,(50,2))
fun dest_startboard (a,_,_) = a

fun status_of ((gl1,gl2),_,(n,_)) = 
  if subset_goal gl1 gl2
  then Win
  else if n <= 0 then Lose else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = term

val defl = (* filter (fn x => mem (fst x) ["ZIP_def","UNZIP"]) *)
  (DB.definitions "list");
val stacl = ["listLib.LIST_INDUCT_TAC", "STRIP_TAC"];
val tacl = [listLib.LIST_INDUCT_TAC, STRIP_TAC];
val stacthmll = ["fs", "simp", "METIS_TAC", "REWRITE_TAC", "ASM_REWRITE_TAC"];
val tacthmll = [fs, simp, METIS_TAC, REWRITE_TAC, ASM_REWRITE_TAC];
(*
val stacthmll = ["ASM_REWRITE_TAC"];
val tacthmll = [ASM_REWRITE_TAC];
*)
val end_move = mk_var ("end_move", alpha);
val thm_movel = map (fn x => mk_var ("thm_move_" ^ fst x, alpha)) defl
val tac_movel = map (fn x => mk_var ("tac_move_" ^ x, alpha)) stacl
val tacthml_movel = 
  map (fn x => mk_var ("tacthml_move_" ^ x, ``:'a -> 'a``)) stacthmll

val movel = (end_move :: thm_movel) @ tac_movel @ tacthml_movel

val thmd = dnew Term.compare (combine (thm_movel,map snd defl))
val tacd = dnew Term.compare (combine (tac_movel,tacl))
val tacthmld = dnew Term.compare (combine (tacthml_movel,tacthmll))

fun available_move (gl,tactm,(n,m)) move = 
  if term_eq tactm ttt_empty 
  then tmem move (tac_movel @ tacthml_movel)
  else 
    if m <= 0 
    then term_eq move end_move
    else tmem move (end_move :: thm_movel)  

fun apply_move_tactm move tactm = 
  let val res =
    if tmem move tacthml_movel then mk_comb (move, ttt_empty)
    else if tmem move tac_movel then move
    else if tmem move thm_movel 
      then list_mk_comb (ttt_thm_concat, [move,ttt_empty])
    else if term_eq move end_move then move
    else raise ERR "apply_move_tactm" ""
  in  
    subst_occs [[1]] [{redex = ttt_empty, residue = res}] tactm
  end

fun dfind_err x d = dfind x d 
  handle NotFound => raise ERR "dfind_err" (tts x)

fun tactic_of_tactm tactm = 
  if is_var tactm then dfind_err tactm tacd else
  let 
    val (a,b) = dest_comb tactm
    val tacthml = dfind_err a tacthmld 
    val thmvarl = strip_binop ttt_thm_concat b
    val thml = map (fn x => dfind_err x thmd) (butlast thmvarl)
  in
    tacthml thml
  end

fun losing_state gl = (([([],F)], gl), F, (~1,~1))

fun apply_move move ((gl1,gl2),tactm,(n,m)) =
  let val tactm1 = apply_move_tactm move tactm in  
    if can (find_term (fn x => term_eq x ttt_empty)) tactm1 
    then ((gl1,gl2),tactm1,(n,m-1))
    else
      let 
        val _ = if null gl1 then raise ERR "apply_move" "" else ()
        val d = dset goal_compare gl1
        fun is_loop x = dmem (hd gl1) (dset goal_compare x)
        (* val _ = print_endline (tts tactm1) *)
        val tac = tactic_of_tactm tactm1
        val glo = 
          SOME ( 
            smlRedirect.hide_out 
            (smlTimeout.timeout 0.1 (fst o tac)) (hd gl1))
          handle _ => NONE
      in
        if isSome glo andalso not (is_loop (valOf glo))
        then 
          let val newgl1= mk_sameorder_set goal_compare (valOf glo @ tl gl1) in
            ((newgl1,gl2), ttt_empty, (n-1,2))
          end
        else losing_state gl2
      end
  end

(*
fun feahash_of_thm thm = feahash_of_goal (dest_thm thm)
val thml2 = map_snd feahash_of_thm thml1 
val symweight = learn_tfidf thml2
val feavdict = dnew String.compare thml2;
fun pred_thml n goal =
  let
    val feag = feahash_of_goal goal
    val thml1 = thmknn (symweight,feavdict) n feag
    val thml2 = map (fn s => DB.fetch "list" s) thml1
  in
    thml2
  end
fun wrap_tac tac g =
  smlRedirect.hide_out 
    (smlTimeout.timeout 0.1 (fst o (tac (pred_thml 8 g)))) g;
val fs_pred = wrap_tac fs 
val simp_pred =  wrap_tac simp
val metis_pred = wrap_tac METIS_TAC
val rewrite_pred = wrap_tac REWRITE_TAC
val asm_rewrite_pred = wrap_tac ASM_REWRITE_TAC
val movel = 
  [("strip_tac", fst o STRIP_TAC),
   ("induct", fst o listLib.LIST_INDUCT_TAC),
   ("asm_rewrite_pred", asm_rewrite_pred),
   ("fs_pred", fs_pred),
   ("metis_pred", metis_pred),
   ("rewrite_pred", rewrite_pred),
   ("simp_pred", simp_pred)]
*)

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  board_compare = board_compare,
  string_of_board = string_of_board,
  movel = movel,
  move_compare = Term.compare,
  string_of_move = tts,
  status_of = status_of,
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   Term representations of the board
   ------------------------------------------------------------------------- *)

fun mk_fun_type tyl = case tyl of
    [] => raise ERR "mk_fun_type" ""
  | [ty] => ty
  | ty :: m => mk_type ("fun", [ty,mk_fun_type m]);

fun ttt_abs (ty1,ty2) = mk_var ("ttt_abs", mk_fun_type [ty1,ty2,ty1,ty2]);
fun ttt_comb (ty1,ty2) = 
  mk_var ("ttt_comb", mk_fun_type [mk_fun_type [ty1,ty2],ty1,ty2]);

fun repl_comb (a,b) =
  let 
    val ty1 = type_of b
    val ty2 = List.nth (snd (dest_type (type_of a)),1)
  in
    list_mk_comb (ttt_comb (ty1,ty2), [a,b])
  end

fun repl_abs (a,b) =
  list_mk_comb (ttt_abs (type_of a, type_of b), [a,b])


fun fofify tm = 
  if is_var tm orelse is_const tm then tm 
  else if is_comb tm then 
    let val (a,b) = dest_comb tm in 
      repl_comb (fofify a, fofify b)
    end
  else if is_abs tm then
    let val (a,b) = dest_abs tm in
      repl_abs (fofify a, fofify b)   
    end
  else raise ERR "replace_abscomb" ""

(*
val tm = concl arithmeticTheory.ADD_ASSOC; 
val tm' = fofify tm;
*)

fun nntm_of_goal g = fofify (list_mk_imp g)
 
val ttt_final_concat = mk_var ("ttt_final_concat",``: bool -> 'a -> bool``);
val ttt_goal_concat = mk_var ("ttt_goal_concat",``: bool -> bool -> bool``);

fun nntm_of_board ((gl1,gl2),tactm,_) = 
  if null gl2 
  then 
    list_mk_binop ttt_final_concat 
      [
      tactm, 
      list_mk_binop ttt_goal_concat (map nntm_of_goal gl1)
      ]
  else
    list_mk_binop ttt_final_concat 
      [
      tactm, 
      list_mk_binop ttt_goal_concat (map nntm_of_goal gl1),
      list_mk_binop ttt_goal_concat (map nntm_of_goal gl2)
      ]

(* -------------------------------------------------------------------------
   Test
   ------------------------------------------------------------------------- *)

fun mk_mcts_param nsim =
  {
  nsim = nsim, stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false,
  noise_all = false, noise_gen = random_real
  }

fun test_one nsim (s,_,g1,gl2) =
  let
    val mcts_obj =
      {mcts_param = mk_mcts_param nsim,
       game = game,
       player = uniform_player game}
    val tree = starttree_of mcts_obj (mk_startboard ([g1],gl2))
    val endtree = mcts mcts_obj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline ("\n" ^ s);
    print_endline (string_of_goal g1);
    print_endline (string_of_goall gl2);
    if b then print_endline "Win" else print_endline "Lose"; 
    b
  end

(*
load "mleTacticToe"; open mleTacticToe;
load "psMCTS"; open psMCTS;
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;
load "smlRedirect"; open smlRedirect;

val _ = BasicProvers.temp_delsimps delsimps;
val goall = map (dest_thm o snd) (DB.theorems "list");
val defl = map snd (DB.definitions "list");

fun metis g =
  let val (gl,_) = hide_out (smlTimeout.timeout 1.0 (METIS_TAC defl)) g in
    null gl
  end
  handle _ => false
;
val rl = map_assoc (fn x => (print "."; metis x)) goall;
length rl;
val rltrue = filter snd rl;
length rltrue;

load "holyHammer"; open holyHammer;
val hh = can (hh_pb [Eprover] (map (fn x => "listTheory." ^ fst x) 
(DB.definitions "list")));

val targetl2 = combine (targetl1, mapi test targetl1);
length targetl2;
val targetl3 = filter snd targetl2;
length targetl3;
*)

(* val _ = BasicProvers.temp_delsimps delsimps; *)




end (* struct *)
