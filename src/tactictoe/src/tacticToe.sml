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

fun constant_space s = String.concatWith " " (partial_sml_lexer s)
fun prefix_absstac stac = [abstract_stac stac, SOME stac]

fun main_tactictoe (thmdata,tacdata) goal =
  let
    (* preselection *)
    val goalf = feahash_of_goal goal
    val _ = debug "preselection of theorems"
    val ((thmsymweight,thmfeadict),t1) =
      add_time (select_thmfea thmdata) goalf
    val _ = debug ("preselection of theorems time: " ^ rts_round 6 t1)
    val _ = debug "preselection of tactics"
    val ((tacsymweight,tacfea),t2) = add_time (select_tacfea tacdata) goalf
    val _ = debug ("preselection of tactics time: " ^ rts_round 6 t2)
    (* caches *)
    val thm_cache = ref (dempty (cpl_compare goal_compare Int.compare))
    val tac_cache = ref (dempty goal_compare)
    (* predictors *)
    fun sthmpred n g =
      dfind (g,n) (!thm_cache) handle NotFound =>
      let val r = thmknn (thmsymweight,thmfeadict) n (feahash_of_goal g) in
        thm_cache := dadd (g,n) r (!thm_cache); r
      end
    fun stacpred g =
      dfind g (!tac_cache) handle NotFound =>
      let
        val thmidl = sthmpred 16 g
        val l = feahash_of_goal g
        val metis_stac = constant_space
          ("metisTools.METIS_TAC [ " ^ thmlarg_placeholder ^ "]")
        val stacl1 = stacknn_uniq (tacsymweight,tacfea) (!ttt_presel_radius) l
        val stacl2 = 
          if not (!ttt_ortho_flag) 
          then List.mapPartial I (List.concat (map prefix_absstac stacl1))
          else stacl1
        val stacl3 = mk_sameorder_set String.compare (metis_stac :: stacl2)
        val istacl = map (inst_stac thmidl) stacl3
      in
        tac_cache := dadd g istacl (!tac_cache); istacl
      end
    val _ = debug "search"
  in
    search stacpred goal
  end

(* -------------------------------------------------------------------------
   Return values
   ------------------------------------------------------------------------- *)

fun read_status r = case r of
   ProofSaturated =>
   (print_endline "saturated"; (NONE, FAIL_TAC "tactictoe: saturated"))
 | ProofTimeout   =>
   (print_endline "timeout"; (NONE, FAIL_TAC "tactictoe: timeout"))
 | Proof s        =>
   (print_endline ("  " ^ s); (SOME s, hidef tactic_of_sml s))

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val ttt_tacdata_cache = ref (dempty (list_compare String.compare))
fun clean_ttt_tacdata_cache () =
  ttt_tacdata_cache := dempty (list_compare String.compare)

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun tactictoe_aux goal =
  if not (has_boolty_goal goal)
  then raise ERR "tactictoe" "type bool expected"
  else
  let
    val _ = hidef QUse.use infix_file
    val cthyl = current_theory () :: ancestry (current_theory ())
    val thmdata = hidef create_thmdata ()
    val tacdata =
      dfind cthyl (!ttt_tacdata_cache) handle NotFound =>
      let val tacdata_aux = ttt_create_tacdata () in
        ttt_tacdata_cache := dadd cthyl tacdata_aux (!ttt_tacdata_cache);
        tacdata_aux
      end
    val proofstatus = hidef (main_tactictoe (thmdata,tacdata)) goal
    val (staco,tac) = read_status proofstatus
  in
    tac
  end

fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term =
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_aux goal) end

(* -------------------------------------------------------------------------
   Evaluation function called by tttUnfold.run_evalscript_thy
   ------------------------------------------------------------------------- *)

fun log_status r = case r of
   ProofSaturated => print_endline "tactictoe: saturated"
 | ProofTimeout   => print_endline "tactictoe: timeout"
 | Proof s        => print_endline ("tactictoe: proven\n  " ^ s)

fun ttt_eval (thmdata,tacdata) goal =
  let
    val b = !hide_flag
    val _ = hide_flag := false
    val _ = print_endline ("ttt_eval: " ^ string_of_goal goal)
    val (status,t) = add_time (main_tactictoe (thmdata,tacdata)) goal
  in
    log_status status;
    print_endline ("ttt_eval time: " ^ rts_round 6 t ^ "\n");
    hide_flag := b
  end

end (* struct *)
