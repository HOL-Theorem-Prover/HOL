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

val hh_eval_ref = ref 0

fun hh_eval goal =
  let 
    val _ = debug_t "update_mdict" update_mdict (current_theory ());
    fun f (a,(_,b)) = (a,b)
    val thmfeav = map f (dlist (!hhs_mdict))
    val thmsymweight = learn_tfidf thmfeav
    val thmfeavdep = 
      debug_t "dependency_of_thm"
        (mapfilter (fn (a,b) => (a,b,dependency_of_thm a))) thmfeav
    val _ = incr hh_eval_ref
    val index = !hh_eval_ref + hash_string (current_theory ())
    fun hammer goal = 
      (!hh_stac_glob) index thmfeavdep (!hhs_hhhammer_time) goal
    val _ = debug ("hh_eval " ^ int_to_string index)
    val _ = debug_proof ("hh_eval " ^ int_to_string index)
    val (staco,t) = add_time hammer goal 
      handle _ => (debug ("Error: hammer " ^ int_to_string index); (NONE,0.0))
  in
    debug_proof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_proof ("Proof status: Time Out")
    | SOME stac => 
      let val b = app_tac 2.0 (tactic_of_sml stac) goal in
        if isSome b then debug_proof ("Reconstructed: Yes") else ();
        debug_proof ("Proof found: " ^ stac)
      end
  end

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict stacl =
  let 
    (* val _ = app debug stacl *)
    val (_,goodl) = 
      partition (fn x => mem x (!hhs_badstacl) orelse is_absarg_stac x) stacl
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
    val _ = debug_t "import_mdict" import_mdict ()
    val _ = debug (int_to_string (dlength (!hhs_mdict)))
    val _ = debug_t "import_mc" import_mc thyl
    val _ = debug (int_to_string (dlength (!hhs_mcdict)))
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
        val ms = int_to_string (dlength (!hhs_mdict))
      in  
        hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
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

fun create_thmfeav feavdep goalfea =
  let 
    val thml = thmknn_ext hhs_predict_dir (!hhs_maxselect_pred) feavdep goalfea
    val pdict = dnew String.compare (map (fn x => (x,())) thml) 
    val feav0 = filter (fn (x,_,_) => dmem x pdict) feavdep
    val feav1 = map (fn (a,b,c) => (a,b)) feav0
  in
    feav1
  end

fun select_thmfeav goalfea =
  if !hhs_metishammer_flag orelse !hhs_hhhammer_flag
  then
    let 
      val _ = debug "theorem selection"
      val _ = debug_t "update_mdict" update_mdict (current_theory ());
      fun f (a,(_,b)) = (a,b)
      val thmfeav = map f (dlist (!hhs_mdict))
      val thmsymweight = learn_tfidf thmfeav
      val thmfeavdep = 
        debug_t "dependency_of_thm"
        (mapfilter (fn (a,b) => (a,b,dependency_of_thm a))) thmfeav
      fun is_ortho a = fst (dfind a (!hhs_mdict))
      val thmfeavdeportho = 
        if !hhs_thmortho_flag 
        then 
          let val l0 = filter (is_ortho o #1) thmfeavdep in
            map (fn (a,b,c) => (a,b,filter is_ortho c)) l0
          end
        else []
    in
      (thmsymweight, 
       create_thmfeav thmfeavdep goalfea,
         if !hhs_thmortho_flag 
         then create_thmfeav thmfeavdeportho goalfea else [],
       thmfeavdep)
    end
  else (dempty Int.compare, [], [], [])
  
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
      (stacknn_ext hhs_predict_dir (!hhs_maxselect_pred) stacfeav_org) goalfea
    (* selecting descendants *)
    val l1 = debug_t "select_desc" select_desc l0
    (* parsing selected tactics *)
    val tacdict = debug_t "mk_tacdict" mk_tacdict (map (#1 o fst) l1)
    (* filtering readable tactics or that contains an argument to
       be instantiated *)
    val stacfeav = filter (fn ((stac,_,_,_),_) => 
      is_absarg_stac stac orelse dmem stac tacdict) l1  
  in
    (stacsymweight, stacfeav, tacdict)
  end

fun select_mcfeav stacfeav =
  if !hhs_mc_flag andalso !hhs_mcrecord_flag then
    let
      fun f ((_,_,g,_),_) = (hash_goal g, ())
      val goal_dict = dnew Int.compare (map f stacfeav)    
      val mcfeav0 = map (fn (a,b) => (b,a)) (dlist (!hhs_mcdict))
      fun select ((b,n),nl) = dmem n goal_dict
      val mcfeav1 = filter select mcfeav0
      val mcsymweight = debug_t "mcsymweight" learn_tfidf mcfeav0
    in
      (mcsymweight, mcfeav1)
    end
  else (dempty Int.compare, [])
  
fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav, orthothmfeav,thmfeavdep) = 
      select_thmfeav goalfea
    val (mcsymweight, mcfeav) = debug_t "select_mcfeav" select_mcfeav stacfeav      
    (* fast predictors *)
    fun stacpredictor g =
      stacknn stacsymweight (!hhs_maxselect_pred) stacfeav (fea_of_goal g)
    fun thmpredictor ob n g = 
      let val herefeav = if ob then orthothmfeav else thmfeav in
        map fst (thmknn thmsymweight n herefeav (fea_of_goal g))
      end
    fun mcpredictor gl =
      mcknn mcsymweight (!hhs_mc_radius) mcfeav (fea_of_goallist gl)
    fun hammer pid goal = 
      (!hh_stac_glob) pid thmfeavdep (!hhs_hhhammer_time) goal
  in
    debug_t "Search" 
      (imperative_search
         thmpredictor stacpredictor mcpredictor hammer tacdict) goal
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
    ProofError     => debug "Error: print_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

(* integer_words return errors hopefully no other *)
fun eval_tactictoe name goal =
  if
    !test_eval_hook name andalso
    !hhs_eval_flag andalso 
    one_in_n () andalso 
    not (!hhs_noprove_flag andalso String.isPrefix "tactictoe_prove_" name)
  then
    if !hh_only_flag 
    then hh_eval goal handle _ => debug "Error: hh_eval" 
    else debug_eval_status (main_tactictoe goal)
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
andalso 
    not (mem (current_theory ())
     ["word_simp","wordSem","labProps",          "data_to_word_memoryProof","word_to_stackProof"])
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
