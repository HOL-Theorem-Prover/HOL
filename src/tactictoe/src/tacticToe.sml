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
  tttSetup tttToken tttLearn tttSearch

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

fun preparse_thmidl thmidl = case thml_of_thmidl thmidl of
    NONE => 
    if is_singleton thmidl 
    then (warning_msg (singleton_of_list thmidl ^ "failed to parse"); [])
    else
      let val (l1,l2) = part_n (length thmidl div 2) thmidl in
        (preparse_thmidl l1 @ preparse_thmidl l2)
      end
  | SOME rl => combine (thmidl,rl)

fun preparse_stac stacl = case pretacl_of_sml 1.0 stacl of
    NONE => 
    if is_singleton stacl 
    then (warning_msg (singleton_of_list stacl ^ "failed to parse"); [])
    else
      let val (l1,l2) = part_n (length stacl div 2) stacl in
        (preparse_stac l1 @ preparse_stac l2)
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

fun main_tactictoe (thmdata,tacdata) (vnno,pnno) goal =
  let
    val _ = hidef QUse.use infix_file
    (* preselection *)
    val _ = print_endline "preselection"
    val goalf = fea_of_goal true goal
    val (thmsymweight,thmfea) = select_thmfea thmdata goalf
    val (tacsymweight,tacfea) = select_tacfea tacdata goalf
    (* parsing *)
    val _ = print_endline "parsing"
    val metis_stac = "metisTools.METIS_TAC " ^ thmlarg_placeholder
    val metis_flag = is_tactic "metisTools.METIS_TAC []"
    val thm_parse_dict = dnew String.compare (preparse_thmidl (map fst thmfea))
    val tac_parse_dict = 
       dnew String.compare (preparse_stac (
         (if metis_flag then [metis_stac] else []) @ map fst tacfea))
    fun parse_thmidl thmidl = map (fn x => dfind x thm_parse_dict) thmidl 
      handle NotFound => 
        raise ERR "parse_thmidl" (String.concatWith " " thmidl)
    fun parse_stac stac = dfind stac tac_parse_dict
      handle NotFound => raise ERR "parse_stac" stac
    val thmfea_filtered = filter (fn x => dmem (fst x) thm_parse_dict) thmfea 
    val tacfea_filtered = filter (fn x => dmem (fst x) tac_parse_dict) tacfea  
    val parsetoken = 
      {parse_stac = parse_stac,
       parse_thmidl = parse_thmidl,
       parse_sterm = fn x => [QUOTE x]}
    (* predictors *)
    val stacl_filtered = metis_stac :: (map fst tacfea_filtered)
    val atyd = dnew String.compare (map_assoc extract_atyl stacl_filtered)
    val thm_cache = ref (dempty goal_compare)
    val tac_cache = ref (dempty goal_compare)
    fun predthml g =
      dfind g (!thm_cache) handle NotFound =>
      let 
        val gfea = fea_of_goal true g
        val thmidl = thmknn (thmsymweight,thmfea_filtered) 
          (!ttt_thmlarg_radius) gfea
      in
        thm_cache := dadd g thmidl (!thm_cache); thmidl
      end
    fun predarg aty g = 
      if aty = Athml 
      then [Sthml (predthml g)] 
      else raise ERR "predarg" "no predictor for this argument type"
    fun predtac g =
      dfind g (!tac_cache) handle NotFound =>
      let
        val gfea = fea_of_goal true g
        val stacl1 = tacknn (tacsymweight,tacfea_filtered) 
          (!ttt_presel_radius) gfea
        val stacl2 =
          if metis_flag
          then mk_sameorder_set String.compare (metis_stac :: stacl1)
          else stacl1
        val stacl3 = map_assoc (fn x => dfind x atyd) stacl2
      in
        tac_cache := dadd g stacl3 (!tac_cache); stacl3
      end
    (* parameter record *)
    val _ = print_endline "search"
    val searchobj = 
      {predtac = predtac, predarg = predarg,
       parsetoken = parsetoken,
       vnno = vnno, pnno = pnno}
  in
    search searchobj goal
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
