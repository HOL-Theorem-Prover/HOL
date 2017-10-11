(* ========================================================================== *)
(* FILE          : tacticToe.sml                                              *)
(* DESCRIPTION   : Automated theorem prover based on tactic selection         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tacticToe :> tacticToe =
struct

open HolKernel boolLib Abbrev
hhsSearch hhsTools hhsLexer hhsExec hhsFeature hhsPredict hhsData hhsInfix
hhsFeature hhsMetis hhsLearn hhsMinimize hhsSetup

val ERR = mk_HOL_ERR "tacticToe"

fun set_timeout r = hhs_search_time := Time.fromReal r

(* ----------------------------------------------------------------------
   Evaluating holyhammer
   ---------------------------------------------------------------------- *)

fun hh_eval goal =
  let val (staco,t) = add_time (!hh_stac_glob) goal in
    debug_proof ("hh_eval");
    debug_proof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_proof ("Proof status: Time Out")
    | SOME stac => debug_proof ("Proof found: " ^ stac)
  end

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict tacticl =
  let 
    val (_,goodl) = 
      partition (fn x => mem x (!hhs_badstacl) orelse is_pattern_stac x) 
      tacticl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (debug ("Warning: bad tactic: " ^ x ^ "\n");
                   hhs_badstacl := x :: (!hhs_badstacl);
                   raise ERR "" "")
    val l = combine (goodl, tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl
    val rdict = dnew String.compare l
  in
    rdict
  end

(* ----------------------------------------------------------------------
   Initialize TacticToe. Reading feature vectors from disk.
   ---------------------------------------------------------------------- *)

fun import_ancestry () =
  let
    val thyl    = ancestry (current_theory ())
    val stacfea = debug_t "import_feavl" import_feavl thyl
    val _ = debug (int_to_string (length stacfea));
    val _ = debug_t "init_mdict" init_mdict ()
    val _ = debug (int_to_string (dlength (!mdict_glob)))
    val _ = debug_t "import_astar" import_astar thyl
    val _ = debug (int_to_string (dlength (!hhs_astar)))
  in
    init_stacfea_ddict stacfea
  end

(* remember in which theory was the last call of tactictoe *)
val previous_theory = ref ""

fun init_tactictoe () =
  let 
    val cthy = current_theory ()
    val thyl = ancestry cthy
  in
    if !previous_theory <> cthy
    then 
      let 
        val _ = debug_t ("init_tactictoe " ^ cthy) import_ancestry ()
        val ns = int_to_string (dlength (!hhs_stacfea))
        val ms = int_to_string (dlength (!mdict_glob))
      in  
        hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
        debug (ns ^ " tactic feature vectors");
        debug (ns ^ " theorem feature vectors");
        print_endline ("Loading " ^ ns ^ " tactic feature vectors");
        print_endline ("Loading " ^ ms ^ " theorem feature vectors");
        previous_theory := cthy
      end
    else ()
  end

(* ----------------------------------------------------------------------
   Preselection of theorems and tactics
   ---------------------------------------------------------------------- *)

(* includes itself *)
fun descendant_of_feav_aux rlist rdict ddict (feav as ((stac,_,_,gl),_)) =
  (
  rlist := feav :: (!rlist);
  if dmem feav rdict
    then debug ("Warning: descendant_of_feav: " ^ stac)
    else 
      let 
        val new_rdict = dadd feav () rdict
        fun f g = 
          let val feavl = dfind g ddict handle _ => [] in  
            app (descendant_of_feav_aux rlist new_rdict ddict) feavl
          end
      in
        app f gl
      end
  )
     
fun descendant_of_feav ddict feav =
  let val rlist = ref [] in
    descendant_of_feav_aux rlist (dempty feav_compare) ddict feav;
    !rlist
  end

fun select_thmfeav goalfea =
  if !hhs_metis_flag 
  then
    let 
      val _ = debug "theorem selection"
      val _ = debug_t "update_mdict" update_mdict (current_theory ())
      val thmfeav = dlist (!mdict_glob)
      val thmsymweight = learn_tfidf thmfeav
      val thmfeavdep = 
        debug_t "dependency_of_thm"
        (mapfilter (fn (a,b) => (a,b,dependency_of_thm a))) thmfeav
      (* Some theorems might disappear so map is not enough here
         Orthogonalization and dependencies are slightly contradictory *)
      val thml = thmknn_ext (!hhs_maxselect_pred) thmfeavdep goalfea
      val pdict = dnew String.compare (map (fn x => (x,())) thml) 
      val feav0 = filter (fn (x,_,_) => dmem x pdict) thmfeavdep
      val feav1 = map (fn (a,b,c) => (a,b)) feav0
    in
      (thmsymweight,feav1)
    end
  else (dempty Int.compare, [])
  
fun select_desc l =
   let
     val l1 = List.concat (map (descendant_of_feav (!hhs_ddict)) l)
     val l2 = mk_sameorder_set feav_compare l1
   in
     first_n (!hhs_maxselect_pred) l2
   end

fun select_stacfeav goalfea =
  let 
    val stacfeav_org = dlist (!hhs_stacfea)
    (* computing tfidf *)
    val stacsymweight = debug_t "learn_tfidf" learn_tfidf stacfeav_org
    (* selecting neighbors *)
    val l0 = debug_t "stacknn_ext" 
      (stacknn_ext (!hhs_maxselect_pred) stacfeav_org) goalfea
    (* selecting descendants *)
    val l1 = debug_t "select_desc" select_desc l0
    (* parsing selected tactics *)
    val tacdict = debug_t "mk_tacdict" mk_tacdict (map (#1 o fst) l1)
    (* filtering readable tactics or that contains a pattern to
       be instantiated *)
    val stacfeav = filter (fn ((stac,_,_,_),_) => 
      is_pattern_stac stac orelse dmem stac tacdict) l1  
  in
    (stacsymweight, stacfeav, tacdict)
  end

fun select_astarfeav stacfeav =
  if !hhs_astar_flag
  then
    let
      val l = map (fea_of_gl o #4 o fst) stacfeav
      val astarfeav_org = map (fn (a,b) => (b,a)) (dlist (!hhs_astar))
      (* computing tfidf *)
      val astarsymweight = debug_t "learn_tfidf" learn_tfidf astarfeav_org
      (* selecting neighbors *)
      val astarfeav_aux = 
        List.concat (map (preastarknn astarsymweight (!hhs_astar_radius * 2)
        astarfeav_org) l)
      val astarfeav = 
        mk_fast_set (cpl_compare bool_compare (list_compare Int.compare)) 
          astarfeav_aux
    in
      (astarsymweight, astarfeav)
    end
  else (dempty Int.compare, [])

fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    val (astarsymweight, astarfeav) = 
      debug_t "select_astarfeav" select_astarfeav stacfeav
    (* fast predictors *)
    fun stacpredictor g =
      stacknn stacsymweight (!hhs_maxselect_pred) stacfeav (fea_of_goal g)
    fun thmpredictor g = 
      map fst (thmknn thmsymweight (!hhs_metis_npred) thmfeav (fea_of_goal g))
    fun astarpredictor gl =
      if !hhs_astar_flag 
      then astarknn astarsymweight (!hhs_astar_radius) astarfeav (fea_of_gl gl)
      else 0.0
  in
    debug_t "Search" 
      (imperative_search thmpredictor stacpredictor astarpredictor tacdict) goal
  end

fun tactic_of_status r = case r of
   ProofError     => 
   (print_endline "tactictoe: error"; FAIL_TAC "tactictoe: error")
 | ProofSaturated => 
   (print_endline "tactictoe: saturated"; FAIL_TAC "tactictoe: saturated")
 | ProofTimeOut   => 
   (print_endline "tactictoe: time out"; FAIL_TAC "tactictoe: time out")
 | Proof s        => 
   (print_endline s; hide_out tactic_of_sml s)

fun debug_eval_status r = 
  case r of
    ProofError     => debug_proof "Error: print_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

(* integer_words return errors hopefully no other *)
fun eval_tactictoe name goal =
  if !hhs_eval_flag 
    andalso not (mem (current_theory ())
              ["integer_word","word_simp","wordSem","labProps",
               "data_to_word_memoryProof","word_to_stackProof"])
    andalso one_in_n ()
    andalso 
      not (!hhs_noprove_flag andalso String.isPrefix "tactictoe_prove_" name)
  then
    if !hh_only_flag 
    then hh_eval goal handle _ => debug_proof "Error: print_eval_status" 
    else debug_eval_status (hide_out main_tactictoe goal)
  else ()

fun tactictoe goal =
  let
    val _ = init_tactictoe ()
    val _ = hide_out set_isearch ()
    val r = hide_out main_tactictoe goal
  in
    tactic_of_status r
  end

fun tt_tac goal = (tactictoe goal) goal

(*
val l1 = ["gcd","seq","poly","llist","set_relation"];
val l2 = map (fn x => x ^ "Theory") l1;
app load l2;
load "hhsTools";
open hhsTools;
val l3 = map (length o DB.thms) l1;
sum_int l3;
*)
 
(* ----------------------------------------------------------------------
   Predicting only the next tactic based on some distance measure.
   ---------------------------------------------------------------------- *)

fun string_stac stac g gl =
  let val stac0 = pretty_stac stac g gl in
    comestic_stac stac0
  end

val next_tac_glob = ref []
val next_tac_number = ref 5
fun next n = List.nth (!next_tac_glob,n)

fun save_stac tac stac g gl =
  (
  next_tac_glob := !next_tac_glob @ [tac];
  print_endline (hide_out (string_stac stac g) gl)
  )

fun try_tac tacdict memdict n goal stacl =
   if n <= 0 then () else
   case stacl of
    [] => print_endline "no more tactics"
  | stac :: m => 
    let 
      fun p0 s = print_endline s
      fun p s = (print_endline ("  " ^ s))
      val tac = dfind stac tacdict
      val ro = SOME (hide_out (hhsTimeout.timeOut 1.0 tac) goal)
               handle _ => NONE   
    in
      case ro of 
        NONE => (print "."; try_tac tacdict memdict n goal m)
      | SOME (gl,_) =>
        let val lbl = (stac,goal,gl) in
          if dmem gl memdict
          then (print "."; try_tac tacdict memdict n goal m)
          else 
            (
            if gl = []
            then (p0 ""; save_stac tac stac goal gl; p "solved")
            else 
              (
              if mem goal gl 
                then 
                  (print "."; try_tac tacdict (dadd gl lbl memdict) n goal m)
                else (p0 "";
                      save_stac tac stac goal gl;
                      app (p o string_of_goal) gl;
                      try_tac tacdict (dadd gl lbl memdict) (n-1) goal m)
              )
            )
        end
    end
    
fun next_tac goal =    
  let  
    val _ = hide_out set_isearch ()
    val _ = init_tactictoe ()
    val _ = next_tac_glob := []
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight,stacfeav,tacdict) = hide_out select_stacfeav goalfea
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!hhs_maxselect_pred) stacfeav (fea_of_goal g)
    val stacl = map (#1 o fst) (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict (!next_tac_number) goal stacl
  end



end (* struct *)
