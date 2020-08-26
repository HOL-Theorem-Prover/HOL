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

(* -------------------------------------------------------------------------
   Preparsing theorems and tactics
   ------------------------------------------------------------------------- *)

fun thml_of_thmidl thmidl = thml_of_sml (map dbfetch_of_thmid thmidl)

fun preparse_thmidl thmidl = case thml_of_thmidl thmidl of
    NONE =>
    if is_singleton thmidl
    then (print_endline ("Could not parse: " ^ singleton_of_list thmidl); [])
    else
      let val (l1,l2) = part_n (length thmidl div 2) thmidl in
        (preparse_thmidl l1 @ preparse_thmidl l2)
      end
  | SOME rl => combine (thmidl,rl)

fun preparse_stacl stacl = case pretacl_of_sml 1.0 stacl of
    NONE =>
    if is_singleton stacl
    then (print_endline ("Could not parse: " ^ singleton_of_list stacl); [])
    else
      let val (l1,l2) = part_n (length stacl div 2) stacl in
        (preparse_stacl l1 @ preparse_stacl l2)
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

fun build_searchobj (thmdata,tacdata) (vnno,pnno) goal =
  let
    val narg_explo = 1
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
       dnew String.compare (preparse_stacl (
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
          (narg_explo * (!ttt_thmlarg_radius)) gfea
      in
        thm_cache := dadd g thmidl (!thm_cache); thmidl
      end
    fun predarg stac aty g = case aty of
        Athml =>
        let val thml = predthml g in
          if stac = metis_stac
          then map Sthml (mk_batch_full (!ttt_thmlarg_radius) thml)
          else map Sthml (mk_batch_full 1 thml)
        end
      | Aterm => map Sterm (pred_svar 8 g)
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
  in
    {predtac = predtac, predarg = predarg,
     parsetoken = parsetoken,
     vnno = vnno, pnno = pnno}
  end

fun main_tactictoe (thmdata,tacdata) (vnno,pnno) goal =
  let 
    val searchobj = build_searchobj (thmdata,tacdata) (vnno,pnno) goal 
    val _ = print_endline "search"
  in
    search searchobj goal
  end

(* -------------------------------------------------------------------------
   Alternative main function (without recorded data)
   ------------------------------------------------------------------------- *)

val ministacl =
  [
  "metisTools.METIS_TAC " ^ thmlarg_placeholder,
  "BasicProvers.Induct_on " ^ termarg_placeholder,
  "simpLib.FULL_SIMP_TAC ( BasicProvers.srw_ss ( ) ) " ^ thmlarg_placeholder,
  "simpLib.SIMP_TAC ( BasicProvers.srw_ss ( ) ) " ^ thmlarg_placeholder,
  "Rewrite.ASM_REWRITE_TAC " ^ thmlarg_placeholder,
  "Rewrite.REWRITE_TAC " ^ thmlarg_placeholder
  ]

fun main_tactictoe_mini thmdata (vnno,pnno) goal =
  let
    val narg_explo = 8
    val mem = !ttt_policy_coeff
    val _ = ttt_policy_coeff := 0.9999
    (* trying to load basic modules *)
    val _ = hidef (map (can load))
      ["metisTools","BasicProvers","simpLib","Rewrite"]
    (* preselection *)
    val _ = print_endline "preselection"
    val goalf = fea_of_goal true goal
    val (thmsymweight,thmfea) = select_thmfea thmdata goalf
    (* parsing *)
    val _ = print_endline "parsing"
    val thm_parse_dict = dnew String.compare (preparse_thmidl (map fst thmfea))
    val tac_parse_dict = dnew String.compare (preparse_stacl ministacl)
    fun parse_thmidl thmidl = map (fn x => dfind x thm_parse_dict) thmidl
      handle NotFound =>
        raise ERR "parse_thmidl" (String.concatWith " " thmidl)
    fun parse_stac stac = dfind stac tac_parse_dict
      handle NotFound => raise ERR "parse_stac" stac
    val parsetoken =
      {parse_stac = parse_stac,
       parse_thmidl = parse_thmidl,
       parse_sterm = fn x => [QUOTE x]}
    val thmfea_filtered = filter (fn x => dmem (fst x) thm_parse_dict) thmfea
    val stacl_filtered = dkeys tac_parse_dict
    (* predictors *)
    val atyd = dnew String.compare (map_assoc extract_atyl stacl_filtered)
    val thm_cache = ref (dempty goal_compare)
    val tac_cache = ref (dempty goal_compare)
    fun predthml g =
      dfind g (!thm_cache) handle NotFound =>
      let
        val gfea = fea_of_goal true g
        val thmidl = thmknn (thmsymweight,thmfea_filtered)
          (narg_explo * (!ttt_thmlarg_radius)) gfea
      in
        thm_cache := dadd g thmidl (!thm_cache); thmidl
      end
    fun predarg _ aty g = case aty of
        Athml => map Sthml (mk_batch_full (!ttt_thmlarg_radius) (predthml g))
      | Aterm => map Sterm (pred_svar narg_explo g)
    fun predtac g = map_assoc (fn x => dfind x atyd) stacl_filtered
    (* search parameters *)
    val _ = print_endline "search"
    val searchobj =
      {predtac = predtac, predarg = predarg,
       parsetoken = parsetoken,
       vnno = vnno, pnno = pnno}
    val r = search searchobj goal
    val _ = ttt_policy_coeff := mem
  in
    r
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

(* -------------------------------------------------------------------------
   Interface (without recorded data)
   ------------------------------------------------------------------------- *)

fun tactictoe_mini_aux goal =
  if not (has_boolty_goal goal)
  then raise ERR "tactictoe" "type bool expected"
  else
  let
    val cthyl = current_theory () :: ancestry (current_theory ())
    val thmdata = hidef create_thmdata ()
    val (proofstatus,_) = hidef (main_tactictoe_mini thmdata (NONE,NONE)) goal
    val (staco,tac) = read_status proofstatus
  in
    tac
  end

fun ttt_mini goal = (tactictoe_mini_aux goal) goal

fun tactictoe_mini term =
  let val goal = ([],term) in TAC_PROOF (goal, tactictoe_mini_aux goal) end


end (* struct *)
