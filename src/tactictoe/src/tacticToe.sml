(* ========================================================================= *)
(* FILE          : tacticToe.sml                                             *)
(* DESCRIPTION   : Automated theorem prover based on tactic selection        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tacticToe :> tacticToe =
struct

open HolKernel Abbrev boolLib aiLib
  smlLexer smlParser smlExecute smlRedirect smlInfix
  mlFeature mlThmData mlTacticData mlNearestNeighbor mlTreeNeuralNetwork
  psMinimize
  tttSetup tttLearn tttSearch

val ERR = mk_HOL_ERR "tacticToe"


(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

fun set_timeout r = (ttt_search_time := r)
val warning = ref true
fun disable_warnings () = warning := false
fun enable_warnings () = warning := true
fun warning_msg s = if !warning then print_endline ("warning: " ^ s) else ()

(* -------------------------------------------------------------------------
   Preparsing theorems and tactics
   ------------------------------------------------------------------------- *)

fun thml_of_thmidl thmidl = thml_of_sml (map dbfetch_of_thmid thmidl)

fun parse_thml thmidl = case thml_of_thmidl thmidl of
    NONE => 
    if is_singleton thmidl 
    then (warning_msg (singleton_of_list thmidl ^ "failed to parse"); [])
    else
      let val (l1,l2) = part_n (length thmidl div 2) thmidl in
        (parse_thml l1 @ parse_thml l2)
      end
  | SOME rl => combine (thmidl,rl)

fun parse_tacl stacl = case ttacl_of_sml 1.0 stacl of
    NONE => 
    if is_singleton stacl 
    then (warning_msg (singleton_of_list stacl ^ "failed to parse"); [])
    else
      let val (l1,l2) = part_n (length stacl div 2) stacl in
        (parse_tacl l1 @ parse_tacl l2)
      end
  | SOME rl => combine (stacl,rl)

(* -------------------------------------------------------------------------
   Preselection of theorems and tactics
   ------------------------------------------------------------------------- *)

fun select_thmfea (symweight,thmfea) gfea =
  let
    val l0 = thmknn_wdep (symweight,thmfea) (!ttt_presel_radius) gfea
    val d = dset String.compare l0
    val l1 = filter (fn (k,v) => dmem k d) thmfea
  in
    (symweight, l1)
  end

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

fun main_tactictoe (thmdata,tacdata) tnno goal =
  let
    val _ = hidef QUse.use infix_file
    (* preselection *)
    val goalf = fea_of_goal true goal
    val (thmsymweight,thmfea) = select_thmfea thmdata goalf
    val (tacsymweight,tacfea) = select_tacfea tacdata goalf
    (* parsing *)
    val metis_stac = "metisTools.METIS_TAC " ^ thmlarg_placeholder
    val metis_flag = is_tactic "metisTools.METIS_TAC []"
    val thm_parse_dict = dnew String.compare (parse_thml (map fst thmfea))
    val tac_parse_dict = 
       dnew String.compare (parse_tacl (
         (if metis_flag then [metis_stac] else []) @ map fst tacfea))
    fun lookup_thmidl thmidl = map (fn x => dfind x thm_parse_dict) thmidl 
      handle NotFound => 
        raise ERR "lookup_thmidl" (String.concatWith " " thmidl)
    fun lookup_stac stac = dfind stac tac_parse_dict
      handle NotFound => raise ERR "lookup_stac" stac
    val lookup = (lookup_thmidl, lookup_stac)
    val thmfea_filtered = filter (fn x => dmem (fst x) thm_parse_dict) thmfea 
    val tacfea_filtered = filter (fn x => dmem (fst x) tac_parse_dict) tacfea  
    (* predictors *)
    val thm_cache = ref (dempty (cpl_compare goal_compare Int.compare))
    val tac_cache = ref (dempty goal_compare)
    fun thmpred n g =
      dfind (g,n) (!thm_cache) handle NotFound =>
      let 
        val gfea = fea_of_goal true g
        val thmidl = thmknn (thmsymweight,thmfea_filtered) n gfea
      in
        thm_cache := dadd (g,n) thmidl (!thm_cache); thmidl
      end
    fun tacpred g =
      dfind g (!tac_cache) handle NotFound =>
      let
        val gfea = fea_of_goal true g
        val stacl1 = tacknn (tacsymweight,tacfea_filtered) 
          (!ttt_presel_radius) gfea
        val stacl2 =
          if metis_flag
          then mk_sameorder_set String.compare (metis_stac :: stacl1)
          else stacl1
      in
        tac_cache := dadd g stacl2 (!tac_cache); stacl2
      end
    fun tacpred' g = 
      let 
        val thmidl = thmpred (!ttt_thmlarg_radius) g 
        val stacl = tacpred g
      in
        map_assoc (fn _ => thmidl) stacl
      end
  in
    search (tacpred',lookup,tnno) goal
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
    val (proofstatus,_) = hidef
      (main_tactictoe (thmdata,tacdata) (NONE,NONE)) goal
    val (staco,tac) = read_status proofstatus
  in
    tac
  end

fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term =
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_aux goal) end


end (* struct *)
