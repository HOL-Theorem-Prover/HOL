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
  tttSetup tttSearch

val ERR = mk_HOL_ERR "tacticToe"
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
  in
    search thmpred tacpred goal
  end

(* -------------------------------------------------------------------------
   Return values
   ------------------------------------------------------------------------- *)

fun status r = case r of
   ProofError     =>
   (print_endline "tactictoe: error"; FAIL_TAC "tactictoe: error")
 | ProofSaturated =>
   (print_endline "tactictoe: saturated"; FAIL_TAC "tactictoe: saturated")
 | ProofTimeOut   =>
   (print_endline "tactictoe: time out"; FAIL_TAC "tactictoe: time out")
 | Proof s        => (print_endline s; hide_out tactic_of_sml s)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val infix_file = HOLDIR ^ "/src/AI/sml_inspection/infix_file.sml"

fun tactictoe_aux goal = 
  let 
    val _ = hide_out QUse.use infix_file
    val _ = init_metis ()
    val thmdata = create_thmdata ()
    val tacdata = ttt_create_tacdata ()
  in
    status (hide_out (main_tactictoe (thmdata,tacdata)) goal)
  end
  
fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term = 
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_aux goal) end

(* -------------------------------------------------------------------------
   Evaluate TacticToe (to move to tttTest)
   ------------------------------------------------------------------------- *)
(*
fun debug_eval_status r =
  case r of
    ProofError     => debug "Error: debug_eval_status"
  | ProofSaturated => debug "Proof status: Saturated"
  | ProofTimeOut   => debug "Proof status: Time Out"
  | Proof s        => debug ("Proof found: " ^ s)

fun eval_tactictoe goal =
  (
  mkDir_err ttt_proof_dir;
  report_data ();
  init_tactictoe ();
  debug_eval_status (hide_out main_tactictoe goal)
  )
*)

end (* struct *)
