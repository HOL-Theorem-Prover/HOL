(* ========================================================================= *)
(* FILE          : tacticToe.sml                                             *)
(* DESCRIPTION   : Automated theorem prover based on tactic selection        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tacticToe :> tacticToe =
struct

open HolKernel Abbrev boolLib aiLib
  smlLexer smlExecute smlRedirect smlInfix
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  psMinimize
  tttSetup tttLearn tttSearch

val ERR = mk_HOL_ERR "tacticToe"
val tactictoe_dir = HOLDIR ^ "/src/tactictoe"
fun debug s = debug_in_dir ttt_debugdir "tacticToe" s

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

fun set_timeout r = (ttt_search_time := r)

(* -------------------------------------------------------------------------
   Preselection of theorems
   ------------------------------------------------------------------------- *)

fun select_thmfea (symweight,thmfeadict) gfea =
  let
    val l0 = thmknn_wdep (symweight,thmfeadict) (!ttt_presel_radius) gfea
    val d = dset String.compare l0
    val l1 = filter (fn (k,v) => dmem k d) (dlist thmfeadict)
  in
    (symweight, dnew String.compare l1)
  end

(* -------------------------------------------------------------------------
   Preselection of tactics
   ------------------------------------------------------------------------- *)

fun select_tacfea tacdata goalf =
  let
    val tacfea = dlist (#tacfea tacdata)
    val tacsymweight = learn_tfidf tacfea
    val l0 =
      stacknn_preselect (tacsymweight,tacfea) (!ttt_presel_radius) goalf
    val l1 = add_stacdep (#tacdep tacdata) (!ttt_presel_radius) (map fst l0)
    fun f x = (x, dfind x (#tacfea tacdata))
    val l2 = map f l1
  in
    (tacsymweight, l2)
  end

(* -------------------------------------------------------------------------
   Main function
   ------------------------------------------------------------------------- *)

fun main_tactictoe (thmdata,tacdata) goal =
  let
    (* preselection *)
    val _ = print_endline "preselection"
    val goalf = feahash_of_goal goal
    val (thmsymweight,thmfeadict) = select_thmfea thmdata goalf
    val (tacsymweight,tacfea) = select_tacfea tacdata goalf
    (* caches *)
    val thm_cache = ref (dempty (cpl_compare goal_compare Int.compare))
    val tac_cache = ref (dempty goal_compare)
    (* predictors *)
    fun thmpred n g =
      dfind (g,n) (!thm_cache) handle NotFound =>
      let val r = thmknn (thmsymweight,thmfeadict) n (feahash_of_goal g) in
        thm_cache := dadd (g,n) r (!thm_cache); r
      end
    fun tacpred g =
      dfind g (!tac_cache) handle NotFound =>
      let
        val l = feahash_of_goal g
        val stacl = stacknn_uniq (tacsymweight,tacfea) (!ttt_presel_radius) l
      in
        tac_cache := dadd g stacl (!tac_cache); stacl
      end
    val _ = print_endline "search"
  in
    if !alt_search_flag 
    then alt_search thmpred tacpred goal 
    else search thmpred tacpred goal
  end

(* -------------------------------------------------------------------------
   Return values
   ------------------------------------------------------------------------- *)

fun read_status r = case r of
   ProofError     =>
   (print_endline "tactictoe: error";
    (NONE, FAIL_TAC "tactictoe: error"))
 | ProofSaturated =>
   (print_endline "tactictoe: saturated";
    (NONE, FAIL_TAC "tactictoe: saturated"))
 | ProofTimeOut   =>
   (print_endline "tactictoe: time out";
    (NONE, FAIL_TAC "tactictoe: time out"))
 | Proof s        =>
   (print_endline ("tactictoe found a proof:\n  " ^ s);
    (SOME s, tactic_of_sml s))

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val ttt_tacdata_cache = ref (dempty (list_compare String.compare))
fun clean_ttt_tacdata_cache () =
  ttt_tacdata_cache := dempty (list_compare String.compare)

val ttt_goaltac_cache = ref (dempty goal_compare)
fun clean_ttt_goaltac_cache () = ttt_goaltac_cache := dempty goal_compare

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun tactictoe_aux goal =
  if not (has_boolty_goal goal)
  then raise ERR "tactictoe" "a term is not of type bool"
  else
  let val (stac,tac) = dfind goal (!ttt_goaltac_cache) in
    print_endline ("goal already solved by:\n  " ^ stac); tac
  end
  handle NotFound =>
  let
    val _ = QUse.use infix_file
    val cthyl = current_theory () :: ancestry (current_theory ())
    val _ = init_metis ()
    val thmdata = create_thmdata ()
    val tacdata =
      dfind cthyl (!ttt_tacdata_cache) handle NotFound =>
      let val tacdata_aux = ttt_create_tacdata () in
        ttt_tacdata_cache := dadd cthyl tacdata_aux (!ttt_tacdata_cache);
        tacdata_aux
      end
    val proofstatus = main_tactictoe (thmdata,tacdata) goal
    val (staco,tac) = read_status proofstatus
    val _ = case staco of NONE => () | SOME stac =>
      ttt_goaltac_cache := dadd goal (stac,tac) (!ttt_goaltac_cache)
  in
    tac
  end

fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term =
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_aux goal) end

(* -------------------------------------------------------------------------
   Evaluation
   Warning : ttt_record should be run on all theories before evaluation
   ------------------------------------------------------------------------- *)

fun log_status tptpname r = case r of
   ProofError     => print_endline "  tactictoe: error"
 | ProofSaturated => print_endline "  tactictoe: saturated"
 | ProofTimeOut   => print_endline "  tactictoe: time out"
 | Proof s        =>
   (
   print_endline ("  tactictoe found a proof:\n  " ^ s);
   print_endline ("Proven: " ^ tptpname)
   )

fun ttt_eval (thmdata,tacdata) (thy,name) goal =
  let
    val tptpname = escape ("thm." ^ thy ^ "." ^ name)
    val _ = print_endline tptpname
    val _ = print_endline ("Theorem: " ^ tptpname)
    val _ = print_endline ("Goal: " ^ string_of_goal goal)
    val (status,t) = add_time (main_tactictoe (thmdata,tacdata)) goal
  in
    log_status tptpname status;
    print_endline ("  time: " ^ Real.toString t ^ "\n")
  end

(* -------------------------------------------------------------------------
   Usage:
     load "tttUnfold"; open tttUnfold; open tttSetup;
     ttt_ttteval_flag := true;
     ttt_ex_flag := true;
     ttt_search_time := 5.0;
     ttt_record_thy "ConseqConv";
   Results can be found in HOLDIR/src/tactictoe/eval/default.
  ------------------------------------------------------------------------- *)


end (* struct *)
