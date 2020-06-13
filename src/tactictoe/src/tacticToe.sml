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

fun select_thmfea (symweight,thmfea) gfea =
  let
    val l0 = thmknn_wdep (symweight,thmfea) (!ttt_presel_radius) gfea
    val d = dset String.compare l0
    val l1 = filter (fn (k,v) => dmem k d) thmfea
  in
    (symweight, l1)
  end

(* -------------------------------------------------------------------------
   Preselection of tactics
   ------------------------------------------------------------------------- *)

fun select_tacfea tacdata gfea =
  let
    val calls = #calls tacdata
    val callfea = map_assoc #fea calls
    val symweight = learn_tfidf callfea
    val sel1 = callknn (symweight,callfea) (!ttt_presel_radius) gfea
    val sel2 = add_calldep (#calldep tacdata) (!ttt_presel_radius) sel1
    val tacfea = map (fn x => (#ortho x, #fea x)) sel2
  in
    (symweight,tacfea)
  end

(* -------------------------------------------------------------------------
   Main function
   ------------------------------------------------------------------------- *)

fun main_tactictoe (thmdata,tacdata) goal =
  let
    val _ = hidef QUse.use infix_file
    (* preselection *)
    val goalf = fea_of_goal true goal
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
    fun thmpred n g =
      dfind (g,n) (!thm_cache) handle NotFound =>
      let val r = thmknn (thmsymweight,thmfeadict) n (fea_of_goal true g) in
        thm_cache := dadd (g,n) r (!thm_cache); r
      end
    fun tacpred g =
      dfind g (!tac_cache) handle NotFound =>
      if !thml_explo_flag then
        let
          val thmidl = thmpred (2 * !ttt_thmlarg_radius) g
          val (thmidl1,thmidl2) = part_n (!ttt_thmlarg_radius) thmidl
          val thmls2 = thmls_of_thmidl thmidl
          val l = fea_of_goal true g
          val metis_stac = "metisTools.METIS_TAC " ^ thmlarg_placeholder
          val stacl1 = tacknn (tacsymweight,tacfea) (!ttt_presel_radius) l
          val stacl2 = mk_sameorder_set String.compare (metis_stac :: stacl1)
          val oistacl = inst_stacl (thmidl1,g) stacl2 
          fun f (stac,istac) = 
            if not (is_thmlarg_stac stac)
            then (SOME istac, NONE)
            else (SOME istac, Option.map fst (inst_stac (thmls2,g) stac))
          val (stacl3,stacl4) = split (map f oistacl)
          val istacl = List.mapPartial I (interleave 2 stacl3 stacl4)
        in
          tac_cache := dadd g istacl (!tac_cache); istacl
        end
      else
        let
          val thmidl = thmpred (!ttt_thmlarg_radius) g
          val l = fea_of_goal true g
          val metis_stac = "metisTools.METIS_TAC " ^ thmlarg_placeholder
          val stacl1 = tacknn (tacsymweight,tacfea) (!ttt_presel_radius) l
          val stacl2 = mk_sameorder_set String.compare (metis_stac :: stacl1)
          val istacl = map snd (inst_stacl (thmidl,g) stacl2)     
        in
          tac_cache := dadd g istacl (!tac_cache); istacl
        end
    val _ = debug "search"
  in
    search tacpred goal
  end

(* -------------------------------------------------------------------------
   Return values
   ------------------------------------------------------------------------- *)

fun read_status status = case status of
   ProofSaturated =>
   (print_endline "saturated"; (NONE, FAIL_TAC "tactictoe: saturated"))
 | ProofTimeout   =>
   (print_endline "timeout"; (NONE, FAIL_TAC "tactictoe: timeout"))
 | Proof s        =>
   (print_endline ("  " ^ s); 
    (SOME s, hidef (tactic_of_sml (!ttt_search_time)) s))

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
    val cthyl = current_theory () :: ancestry (current_theory ())
    val thmdata = hidef create_thmdata ()
    val tacdata =
      dfind cthyl (!ttt_tacdata_cache) handle NotFound =>
      let val tacdata_aux = create_tacdata () in
        ttt_tacdata_cache := dadd cthyl tacdata_aux (!ttt_tacdata_cache);
        tacdata_aux
      end
    val (proofstatus,_) = hidef (main_tactictoe (thmdata,tacdata)) goal
    val (staco,tac) = read_status proofstatus
  in
    tac
  end

fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term =
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_aux goal) end


end (* struct *)
