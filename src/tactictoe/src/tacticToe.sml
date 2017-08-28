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
hhsRedirect hhsFeature hhsTacticgen hhsLearn hhsMinimize

val ERR = mk_HOL_ERR "tacticToe"

val init_error_file = tactictoe_dir ^ "/code/init_error"
val main_error_file = tactictoe_dir ^ "/code/main_error"
val hide_error_file = tactictoe_dir ^ "/code/hide_error"


(* ----------------------------------------------------------------------
   Local references
   ---------------------------------------------------------------------- *)

val timeout = ref 5.0
fun set_timeout r = timeout := r

val max_select_pred = ref 0
val hhs_metis_npred = ref 0
val hhs_previous_theory = ref ""
val small_eval_flag = ref false

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict tacticl =
  let 
    val (_,goodl) = partition (fn x => mem x (!hhs_badstacl)) tacticl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (debug ("Warning: bad tactic: " ^ x ^ "\n");
                   hhs_badstacl := x :: (!hhs_badstacl);
                   raise ERR "mk_tacdict" "")
    val l = combine (goodl, tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl
    val rdict = Redblackmap.fromList String.compare l
  in
    rdict
  end

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

val mdict_glob = ref (dempty String.compare)

fun add_thy_mdict thy =
  let
    fun f (name,thm) =
      mdict_glob := dadd (thy ^ "Theory." ^ name) 
        (fea_of_goal (dest_thm thm)) (!mdict_glob)
  in
    app f (DB.thms thy)
  end

fun init_prev () =
  let
    val thyl = ancestry (current_theory ())
    val succratel = debug_t "Reading success rates" import_succrate thyl
    val _ = succ_cthy_dict := dempty String.compare
    val _ = succ_glob_dict := dnew String.compare succratel
    val _ = debug ("  success rates: " ^ 
                   int_to_string (dlength (!succ_glob_dict)))
    val stacfea = debug_t "Reading feature vectors" import_feavl thyl
    val _ = mdict_glob := dempty String.compare
    val _ = debug ("  feature vectors: " ^ int_to_string (length stacfea));
    val _ = if !hhs_metis_flag then app add_thy_mdict thyl else ()
    val _ = debug ("Reading theorems: " ^ int_to_string (dlength (!mdict_glob)))
  in
    hide init_error_file QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
    hhs_badstacl := [];
    init_stacfea_ddict stacfea
  end

(* ----------------------------------------------------------------------
   Parameters
   ---------------------------------------------------------------------- *)

val hhs_eval_flag = ref true

fun set_parameters () =
  (
  (* predicting *)
  max_select_pred := 500;
  (* searching *)
  hhs_cache_flag := true;
  hhs_search_time := Time.fromReal (!timeout);
  hhs_tactic_time := 0.02;
  hhs_astar_flag := false;
  hhs_timedepth_flag := false; 
  (* learning *)
  hhs_ortho_flag := false;
  hhs_selflearn_flag := false;
  hhs_succrate_flag := false;
  (* tactic generation *)
  hhs_mutate_flag := false;
  hhs_metis_flag := (false andalso 
                     exec_sml "metis_test" "metisTools.METIS_TAC []");
  hhs_metis_npred := 8;
  (* result *)
  hhs_minimize_flag := false;
  hhs_prettify_flag := false
  )

(* ----------------------------------------------------------------------
   Theorems dependencies
   ---------------------------------------------------------------------- *)

val did_cache = ref (dempty (cpl_compare String.compare Int.compare))

fun load_did_cache thy =
  let
    val thml = DB.thms thy
    fun f (name,thm) = 
      let 
        val fullname = thy ^ "Theory." ^ name
        val n = (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
      in
        did_cache := dadd (thy,n) fullname (!did_cache)
      end
  in
    app f thml  
  end 

fun thm_of_did (did as (thy,n)) =
  (
  dfind did (!did_cache) 
  handle _ => (load_did_cache thy; dfind did (!did_cache))
  )
  handle _ => raise ERR "thm_of_did" "Not found"

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun depl_of s =
  let 
    val thm = thm_of_string s
    val dl = (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
    val l = mapfilter thm_of_did dl
  in
    l
  end

(* ----------------------------------------------------------------------
   Main function
   ---------------------------------------------------------------------- *)

fun init_tactictoe () =
  let 
    val cthy = current_theory ()
    val thyl = ancestry cthy
  in
    if !hhs_previous_theory <> cthy
    then 
      let 
        val _ = debug_t ("init_tactictoe " ^ cthy) init_prev ()
        val ns = int_to_string (dlength (!hhs_stacfea))
      in  
        debug (ns ^ " feature vectors");
        print_endline ("Loading " ^ ns ^ " feature vectors");
        hhs_previous_theory := cthy
      end
    else ();
    debug "set_parameters";
    set_parameters ()
  end

(* includes itself *)
fun descendant_of_feav_aux rlist rdict ddict (feav as ((stac,_,_,gl),_)) =
  (
  rlist := feav :: (!rlist);
  if dmem feav rdict
    then debug ("warning: descendant_of_feav: " ^ stac)
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

fun string_of_feav ((stac,_,g,gl),_) = 
  stac ^ "\n  " ^ 
  string_of_goal g ^ "\n  " ^ 
  String.concatWith "," (map string_of_goal gl)

fun select_thmfeav goalfea =
  if !hhs_metis_flag 
  then
    let 
      val _ = debug "theorem selection"
      val _ = add_thy_mdict (current_theory ()) 
      val thmfeav = dlist (!mdict_glob)
      val thmsymweight = learn_tfidf thmfeav  
      val thmfeavdep = mapfilter (fn (a,b) => (a, b, depl_of a)) thmfeav
      val thml = thmknn_ext (!max_select_pred) thmfeavdep goalfea
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
     first_n (!max_select_pred) l2
   end

fun select_stacfeav goalfea =
  let 
    val stacfeav_org = dlist (!hhs_stacfea)
    (* computing tfidf *)
    val stacsymweight = debug_t "learn_tfidf" learn_tfidf stacfeav_org
    (* selecting neighbors *)
    val l0 = debug_t "stacknn_ext" 
      (stacknn_ext (!max_select_pred) stacfeav_org) goalfea
    (* selecting descendants *)
    val l1 = debug_t "select_desc" select_desc l0
    (* parsing selected tactics *)
    val tacdict = debug_t "mk_tacdict" mk_tacdict (map (#1 o fst) l1)
    (* filtering readable tactics *)
    val stacfeav = filter (fn ((stac,_,_,_),_) => dmem stac tacdict) l1
  in
    (stacsymweight, stacfeav, tacdict)
  end
      
fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    (* fast predictors *)
    fun stacpredictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    fun thmpredictor g = 
      map fst (thmknn thmsymweight (!hhs_metis_npred) thmfeav (fea_of_goal g))
  in
    debug_t "Search" 
       (imperative_search thmpredictor stacpredictor tacdict (!hhs_ddict)) 
       goal
  end

fun print_proof_status r = case r of
   ProofError     => print_endline "Proof status: Error\n"
 | ProofSaturated => print_endline "Proof status: Saturated\n"
 | ProofTimeOut   => print_endline "Proof status: Time Out\n"
 | Proof s        => print_endline s

fun debug_eval_status r = 
  case r of
    ProofError     => debug_proof "Error: print_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

(* integer_words return errors hopefully no other *)
fun eval_tactictoe goal =
  if !hhs_eval_flag andalso 
    not (
      mem (current_theory ())
      ["integer_word","word_simp","wordSem","labProps",
       "data_to_word_memoryProof","word_to_stackProof"]
        )
  then
    let
      val _ = init_tactictoe ()
      val r = hhsRedirect.hide main_error_file main_tactictoe goal 
    in
      debug_eval_status r
    end
  else ()
 
fun tactictoe goal =
  let
    val _ = init_tactictoe ()
    val r = hhsRedirect.hide main_error_file main_tactictoe goal 
  in
    print_proof_status r
  end

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

fun try_tac tacdict memdict n goal stacl = 
   if n <= 0 then () else
   case stacl of
    [] => ()
  | stac :: m => 
    let 
      fun p s = (print_endline ("  " ^ s))
      val tac = dfind stac tacdict
      val ro = (SOME (add_time (hhsTimeout.timeOut 1.0 tac) goal)) 
        handle _ => NONE   
    in
      case ro of 
        NONE => (try_tac tacdict memdict (n-1) goal m)
      | SOME ((gl,_),t) =>
        let 
          val lbl = (stac,t,goal,gl)
        in
          if dmem gl memdict
          then (try_tac tacdict memdict (n-1) goal m)
          else 
            (
            if gl = []
            then (print_endline stac; p "SOLVED")
            else 
              (
              if mem goal gl 
                then () 
                else (print_endline stac; app (p o string_of_goal) gl);
              try_tac tacdict (dadd gl lbl memdict) (n-1) goal m
              )
            )
        end
    end
    
fun next_tac n goal =    
  let  
    val _ = init_tactictoe ()
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    val stacl = map (#1 o fst) (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict n goal stacl
  end


end (* struct *)
