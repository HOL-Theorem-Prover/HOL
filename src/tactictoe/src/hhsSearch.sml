(* ========================================================================== *)
(* FILE          : tacticToe.sml                                              *)
(* DESCRIPTION   : A* search algorithm for TacticToe.                         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsSearch :> hhsSearch =
struct

open HolKernel boolLib Abbrev hhsTools hhsTimeout hhsFeature hhsPredict
hhsExec hhsLexer hhsPrettify hhsTacticgen hhsData

val ERR = mk_HOL_ERR "hhsSearch"

(* --------------------------------------------------------------------------
   Exceptions
   -------------------------------------------------------------------------- *)

exception SearchTimeOut
exception NoNextTac

(* -------------------------------------------------------------------------
   Globals
   -------------------------------------------------------------------------- *)

fun empty_predictor (g:goal) = []
val proofdict = ref (dempty Int.compare)
val finproofdict = ref (dempty Int.compare)
val tacdict_glob = ref (dempty String.compare)
val distdict_glob = ref (dempty goal_compare)
val thmpredictor_glob = ref (fn g => [])
val stacpredictor_glob = ref empty_predictor
val glob_timer = ref NONE
val hhs_minimize_flag = ref true
val succ_cthy_dict = ref (dempty String.compare)
val succ_glob_dict = ref (dempty String.compare)

(* --------------------------------------------------------------------------
   Cache
   -------------------------------------------------------------------------- *)

fun stacgoal_compare ((stac1,goal1),(stac2,goal2)) =
  case String.compare (stac1,stac2) of
    EQUAL => goal_compare (goal1,goal2)
  | x     => x

val goalpred_cache = ref (dempty goal_compare)
val stacgoal_cache = ref (dempty stacgoal_compare)

(* --------------------------------------------------------------------------
   Options
   -------------------------------------------------------------------------- *)

val hhs_search_time = ref (Time.fromReal 0.0)
val hhs_tactic_time = ref 0.0
val hhs_cache_flag  = ref false
val hhs_metis_time = ref 0.0
val hhs_succrate_flag = ref false
val hhs_astar_flag = ref false
val hhs_timedepth_flag = ref false
val hhs_selflearn_flag = ref false

(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val stac_counter = ref 0

fun string_of_predentry ((stac,_,_,_),score) =
      "(" ^ stac ^ "," ^ Real.toString score ^ ")"

fun string_of_pred pred =
  "[" ^ String.concatWith "," (map string_of_predentry pred) ^ "]"

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

val metis_chat = ref 0
val meson_chat = ref 0

(* --------------------------------------------------------------------------
   Checking time taken by the predictions
   -------------------------------------------------------------------------- *)

val predict_time = ref 0.0
val thmpredict_time = ref 0.0
val infstep_time = ref 0.0
val node_create_time = ref 0.0
val node_find_time = ref 0.0
val total_time = ref 0.0

fun save_time time_ref f x =
  let
    val rt = Timer.startRealTimer ()
    val r = f x
    val time = Timer.checkRealTimer rt
  in
    time_ref := (!time_ref) + (Time.toReal time);
    r
  end

val predict_timer = save_time predict_time
val thmpredict_timer = save_time thmpredict_time
val infstep_timer = save_time infstep_time
fun node_create_timer f x = save_time node_create_time f x
val node_find_timer = save_time node_find_time
fun total_timer f x = save_time total_time f x

(* ----------------------------------------------------------------------
   A*-heurisitic
   ---------------------------------------------------------------------- *)

fun list_min l = case l of 
    [] => raise ERR "list_min" ""
  | [a] => a
  | a :: m => Real.min (a,list_min m)

fun astar memdict g =
  let 
    val newdict = dadd g () memdict
    val l = dfind g (!distdict_glob)
    fun f ((_,t,_,gl),_) = 
      if exists (fn x => dmem x newdict) gl (* prevent loops *)
      then 1000000.0
      else 
        (if !hhs_timedepth_flag then t else 1.0) + 
        sum_real (map (astar newdict) gl)
  in
    list_min (map f l)
  end  

fun estimate_distance (depth,timedepth) (g,pred) =
  let
    val width_coeff = ref 0.0 
    fun f (lbl as (stac,t,g1,gl1),_) =
      let
        val cost = (!width_coeff) + 
          (if !hhs_timedepth_flag then timedepth else Real.fromInt depth)
        val heuristic = 
          if g1 = g 
            then 0.0
          else if !hhs_astar_flag 
            then astar (dempty goal_compare) g1 
            else 1.0
        val _ = width_coeff := (!width_coeff) +
                (if !hhs_timedepth_flag then (!hhs_tactic_time) else 1.0)
        val final_score =
          if !hhs_succrate_flag
          then
            let 
              val (succ,try) = dfind stac (!succ_glob_dict)
              (* starting value of 10 over 1 *)
              val inv_succrate = 
                Real.fromInt (10 + try) / Real.fromInt (succ + 1)
            in
              inv_succrate * (cost + heuristic)
            end
          else cost + heuristic
      in
        (lbl,final_score)
      end
  in
    (g, map f pred)
  end
  
(* --------------------------------------------------------------------------
   Node creation and deletion done by these functions
   -------------------------------------------------------------------------- *)

val max_depth_mem = ref 0
val pid_counter = ref 0

fun next_pid () =
  let
    val r = !pid_counter
    val _ = pid_counter := !pid_counter + 1
  in
    r
  end

fun root_create goal pred =
  let
    val selfid = next_pid ()
    val selfrec =
      {
      selfid   = selfid,
      parid    = NONE,
      parstac  = NONE,
      pargn    = NONE,
      parg     = NONE,
      goalarr  = Array.fromList [goal],
      predarr  = Array.fromList [pred],
      pending  = ref [0],
      proofl   = ref [],
      children = ref [],
      pardict  = dempty goal_compare,
      trydict  = ref (dempty (list_compare goal_compare)),
      depth = 0,
      timedepth = 0.0
      }
  in
    debug "root_create";
    debug ("  goals: " ^
          String.concatWith "," (map string_of_goal [goal]));
    (*
    debug ("  predictions: " ^
          String.concatWith "," (map (string_of_pred o (first_n 2)) [pred]));
    *)
    proofdict := dadd selfid selfrec (!proofdict)
  end

fun root_create_wrap g =
  let
    (* Predictions *)
    val pred = (!stacpredictor_glob) g
    val (_,pred1) = 
      (add_metis tacdict_glob thmpredictor_glob o 
       add_mutate tacdict_glob o 
       estimate_distance (0,0.0)) 
       (g,pred)
  in
    root_create g pred1
  end

fun node_create tactime parid parstac pargn parg goallist 
    predlist pending pardict =
  let
    val pardepth = #depth (dfind parid (!proofdict))
    val partimedepth = #timedepth (dfind parid (!proofdict))
    val _ = if pardepth + 1 > !max_depth_mem
            then max_depth_mem := pardepth + 1
            else ()
    val selfid = next_pid ()
    val selfrec =
    {
      selfid   = selfid,
      parid    = SOME parid,
      parstac  = SOME parstac,
      pargn    = SOME pargn,
      parg     = SOME parg,
      goalarr  = Array.fromList goallist,
      predarr  = Array.fromList predlist,
      pending  = ref pending,
      proofl   = ref [],
      children = ref [],
      pardict  = pardict,
      trydict  = ref (dempty (list_compare goal_compare)),
      depth    = pardepth + 1,
      timedepth = partimedepth + tactime
    }
  in
    debug ("node_create " ^ int_to_string selfid ^
           " child of " ^ int_to_string parid ^
           " by " ^ parstac ^
           " in " ^ Real.toString (#timedepth selfrec) ^ " sec");
    debug ("  goals: " ^ String.concatWith "," (map string_of_goal goallist));
    debug ("  predictions: " ^
       String.concatWith "," (map (string_of_pred o (first_n 2)) predlist));
    proofdict := dadd selfid selfrec (!proofdict);
    selfid
  end

fun node_delete pid =
  (
  debug ("node_delete " ^ int_to_string pid);
  proofdict := drem pid (!proofdict)
  )

fun node_save pid =
  (
  debug ("node_save " ^ int_to_string pid);
  let val prec = dfind pid (!proofdict) in
    finproofdict := dadd pid prec (!finproofdict)
  end
  )

(* --------------------------------------------------------------------------
   Application of a tactic.
   -------------------------------------------------------------------------- *)

exception OtherError

fun count_try stac = 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1,try1 + 1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2,try2 + 1) (!succ_glob_dict)
  end
  
fun count_succ stac = 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1 + 1,try1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2 + 1,try2) (!succ_glob_dict)
  end
 
fun apply_stac bmetis pardict trydict_unref stac g =
  let
    val _ = count_try stac (* doesn't work with metis *)
    val tactic_time = if bmetis then !hhs_metis_time else !hhs_tactic_time
    val _ = stac_counter := !stac_counter + 1
    val _ = debug ("  " ^ int_to_string (!stac_counter) ^ " " ^ stac)
    val tac = dfind stac (!tacdict_glob) 
      handle _ => 
        (debug ("SNH: apply_stac:" ^ stac); raise ERR "apply_stac" stac)
    val gl =
      if !hhs_cache_flag then
        if dmem (stac,g) (!stacgoal_cache)
        then
          case dfind (stac,g) (!stacgoal_cache) of
            NONE => raise OtherError
          | SOME cache_gl => cache_gl
        else
          let val r = fst (timeOut tactic_time (TC_OFF tac) g) in
            stacgoal_cache := dadd (stac,g) (SOME r) (!stacgoal_cache);
            r
          end
      else fst (timeOut tactic_time (TC_OFF tac) g)
  in
    if mem g gl orelse exists (fn x => dmem x pardict) gl
      then (debug ("  tacloop"); NONE)
    else if dmem gl trydict_unref
      then (debug ("  tacparallel"); NONE)
    else (debug ("  tacsuccess"); SOME gl)
  end
  handle TacTimeOut =>
     (
     if !hhs_cache_flag
     then stacgoal_cache := dadd (stac,g) NONE (!stacgoal_cache)
     else ();
     debug ("  tactimeout"); NONE
     )
       | OtherError => NONE
       | _ => (debug "apply_stac: other error"; NONE)

fun apply_next_stac bmetis pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
      handle _ => raise ERR "apply_next_stac" "empty pending"
    val goal = Array.sub (#goalarr prec, gn)
    val pred = Array.sub (#predarr prec, gn)
    val trydict_unref = !(#trydict prec)
    val pardict = (#pardict prec)
    val ((stac,_,_,_),_) = hd pred
      handle _ => raise ERR "apply_next_stac" "empty pred"
  in
    infstep_timer (apply_stac bmetis pardict trydict_unref stac) goal
  end

(* ----------------------------------------------------------------------
   Searching for the next tactic to be applied
   ---------------------------------------------------------------------- *)

fun node_find () =
  let
    val l0 = Redblackmap.listItems (!proofdict)
    fun give_score (pid,prec) =
      let
        val gn = hd (! (#pending prec))
          handle _ => raise ERR "find_next_tac" (int_to_string pid)
        val pred = Array.sub (#predarr prec, gn)
      in
        if null pred
        then NONE
        else SOME (pid, snd (hd pred))
      end
    fun compare_score ((_,r1),(_,r2)) = Real.compare (r1,r2)
    val l1 = List.mapPartial give_score l0
    val l2 = dict_sort compare_score l1
  in
    if null l2
    then (debug "nonexttac"; raise NoNextTac)
    else
      let
        val (pid,score) = hd l2
        val bmetis = score < 0.0
        val prec = dfind pid (!proofdict)
        val gn = hd (! (#pending prec))
        val goal = Array.sub (#goalarr prec, gn)
        val ((stac,_,_,_),_) = hd (Array.sub (#predarr prec, gn))
      in
        debug (
          "node_find " ^ int_to_string pid ^ " " ^ 
          stac ^ " " ^ Real.toString score);
        (bmetis,pid)
      end
  end

(* ---------------------------------------------------------------------------
   Closing proofs
   -------------------------------------------------------------------------- *)

fun children_of pid =
  let val prec = dfind pid (!proofdict) in
    ! (#children prec)
  end

fun descendant_of pid =
  let val cidl = children_of pid in
    cidl @ List.concat (map descendant_of cidl)
  end

fun close_descendant pid = app node_delete (descendant_of pid)

exception ProofFound

fun close_proof cid pid =
  let
    val crec = dfind cid (!proofdict)
    val prec = dfind pid (!proofdict)
    val {pargn = gn, parstac = stac,...} = crec
    val {proofl,pending,parid,children,trydict,...} = prec
  in
    if !pending <> [] then () else raise ERR "close_proof" (int_to_string pid);
    if valOf gn = hd (!pending) then () else raise ERR "close_proof" "";
    proofl  := (valOf gn, valOf stac, cid) :: !proofl;
    node_save cid; (* saves the child that gave the proof *)
    close_descendant pid; (* close all children *)
    children := [];
    trydict := dempty (list_compare goal_compare);
    pending := tl (!pending);
    if !pending = []
    then
      if parid = NONE
      (* special case when it's root *)
      then (node_save pid; node_delete pid; raise ProofFound)
      else close_proof pid (valOf parid)
    else ()
  end

(* ----------------------------------------------------------------------
   Creating new nodes
   ---------------------------------------------------------------------- *)

fun node_create_gl tactime gl pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val ((stac,_,_,_),_) = hd (Array.sub (#predarr prec, gn))
    val parchildren = #children prec
    val depth = #depth prec + 1
    val timedepth = #timedepth prec + tactime
    (* Warning: cache have wrong estimates *)
    fun add_pred g =
      if !hhs_cache_flag
      then
        (g, dfind g (!goalpred_cache)) handle _ =>
        let
          val r = (!stacpredictor_glob) g
        in
          goalpred_cache := dadd g r (!goalpred_cache);
          (g,r)
        end
      else (g, (!stacpredictor_glob) g)
    val predlist0 =
      map (add_metis tacdict_glob thmpredictor_glob o 
           add_mutate tacdict_glob o
           (estimate_distance (depth,timedepth)) o 
           add_pred) 
      gl
    val predlist1 = map snd predlist0
    (* Ordering the goals: hardest first. 
       Warning: METIS cancels the ordering of the goals *)
    val pending0 = number_list 0 predlist1
    val pending1 = map (fn (gn,pred) => (gn, (snd o hd) pred)) pending0
    fun compare_score ((_,r1),(_,r2)) = Real.compare (r2,r1)
    val pending = map fst (dict_sort compare_score pending1)
    (* Updating the list of parent *)
    val new_pardict = dadd goal () (#pardict prec)
    (* New node *)
    val selfid = 
      node_create tactime pid stac gn goal gl predlist1 pending new_pardict
  in
    parchildren := selfid :: (!parchildren);
    selfid
  end

(* fake a node when a proof is found but no search is performed on this node *)
fun node_create_empty tactime pid =
  let
    val prec = dfind pid (!proofdict)
    val gn   = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val ((stac,_,_,_),_) = hd (Array.sub (#predarr prec, gn))
    val parchildren = #children prec
    val selfid = node_create tactime pid stac gn goal [] [] [] 
                   (dempty goal_compare)
  in
    parchildren := selfid :: (!parchildren);
    selfid
  end

(* ---------------------------------------------------------------------------
   Main search function. Modifies proofdict.
   -------------------------------------------------------------------------- *)

fun init_search thmpredictor stacpredictor tacdict distdict g =
  let
    val _ = stacgoal_cache := dempty stacgoal_compare
    val _ = goalpred_cache := dempty goal_compare
    val _ = predict_time := 0.0
    val _ = thmpredict_time := 0.0
    val _ = infstep_time := 0.0
    val _ = node_find_time := 0.0
    val _ = node_create_time := 0.0
    val _ = total_time := 0.0
    val _ = glob_timer   := SOME (Timer.startRealTimer ())
    val _ = pid_counter  := 0
    val _ = stac_counter := 0
    val _ = max_depth_mem := 0
    val _ = proofdict    := dempty Int.compare
    val _ = finproofdict := dempty Int.compare
    val _ = stacpredictor_glob := predict_timer stacpredictor
    val _ = thmpredictor_glob := thmpredict_timer thmpredictor
    val _ = tacdict_glob := tacdict
    val _ = distdict_glob := distdict
  in
    ()
  end

fun get_next_pred pid =
  let
    val prec = dfind pid (!proofdict)
    val gn   = hd (! (#pending prec))
    val pred = Array.sub (#predarr prec, gn)
  in
    Array.update (#predarr prec, gn, tl pred)
    handle _ => raise ERR "init_none" ""
  end

fun search_step () =
  let
    val (bmetis,pid) = node_find_timer node_find ()
    val prec = dfind pid (!proofdict)
    val trydict = #trydict prec
    val (glo,tactime) = add_time (apply_next_stac bmetis) pid
  in
    case glo of
      NONE    => get_next_pred pid
    | SOME gl =>
      if gl = []
      then
        let val cid = node_create_timer (node_create_empty tactime) pid in
          close_proof cid pid
        end
      else
        (
        trydict := dadd gl () (!trydict);
        ignore (node_create_timer (node_create_gl tactime gl) pid)
        )
  end

datatype proof_status_t = 
  ProofError | ProofSaturated | ProofTimeOut | Proof of string

fun search_loop () =
  (
  if Timer.checkRealTimer (valOf (!glob_timer)) > (!hhs_search_time)
    then ProofTimeOut
  else if dmem 0 (!finproofdict) then Proof ""
  else (search_step (); search_loop ())
  )
  handle NoNextTac => ProofSaturated
       | ProofFound => Proof ""

fun proofl_of pid =
  let
    val prec = dfind pid (!finproofdict)
               handle _ => raise ERR "string_of_proof" "node not found"
    fun compare_gn ((gn1,_,_),(gn2,_,_)) = Int.compare (gn1,gn2)
    val proofl = !(#proofl prec)
    val new_proofl = dict_sort compare_gn proofl
    fun f (gn,stac,cid) = 
      let 
        val g = Array.sub (#goalarr prec, gn)
        val contl = proofl_of cid
        val tac = Tactic (stac,g)
      in
        if null contl then tac
        else if List.length contl = 1 then Then (tac, hd contl)
        else Thenl (tac, contl)
      end
  in
    map f new_proofl
  end

fun end_search () =
  (
  debug_proof ("Statistics");
  debug_proof ("  infstep : " ^ int_to_string (!stac_counter));
  debug_proof ("  nodes   : " ^ int_to_string (!pid_counter));
  debug_proof ("  maxdepth: " ^ int_to_string (!max_depth_mem));
  debug_proof ("Time: " ^ Real.toString (!total_time));
  debug_proof ("  inferstep time: " ^ Real.toString (!infstep_time));
  debug_proof ("  node_find time: " ^ Real.toString (!node_find_time));
  debug_proof ("  node_crea time: " ^ Real.toString (!node_create_time));
  debug_proof ("    pred time: " ^ Real.toString (!predict_time));
  debug_proof ("    thmpred time: " ^ Real.toString (!thmpredict_time));
  proofdict    := dempty Int.compare;
  finproofdict := dempty Int.compare;
  tacdict_glob := dempty String.compare;
  stacgoal_cache := dempty stacgoal_compare;
  goalpred_cache := dempty goal_compare
  )
 
(* ---------------------------------------------------------------------------
   Recording successful tactics from its search.
   -------------------------------------------------------------------------- *)

fun selflearn proof = case proof of 
    Tactic (stac,g) => 
      (
      let 
        val _ = count_succ stac
        val ((gl,_),t) = add_time (tactic_of_sml stac) g
        val lbl = (stac,t,g,gl) 
      in
        save_lbl lbl
      end
      handle _ => debug ("  " ^ stac)
      )
  | Then (p1,p2) => (selflearn p1; selflearn p2)
  | Thenl (p,pl) => (selflearn p; app selflearn pl)


fun imperative_search thmpredictor stacpredictor tacdict distdict g =
  (
  init_search thmpredictor stacpredictor tacdict distdict g;
  total_timer (node_create_timer root_create_wrap) g;
  let 
    val r = total_timer search_loop ()
    val _ = debug ("End search loop")
    val sproof_status = case r of
      Proof _  =>
       (if dmem 0 (!finproofdict) then
          let 
            val proofl = proofl_of 0
            val proof = 
              if length proofl <> 1 
              then (debug "SNH: imperative_search1"; 
                    raise ERR "imperative_search" "")
              else 
                (
                debug "Starting selflearn";
                if !hhs_selflearn_flag then selflearn (hd proofl) else ();
                debug "End selflearn";
                debug "Starting minimization";
                if !hhs_minimize_flag 
                then 
                  (prettify_proof o minimize_proof o minimize_tac) (hd proofl)
                else prettify_proof (hd proofl)
                )
            val sproof = 
              (
              debug "End minimization";
              debug "Starting reconstruction";
              safe_hhs_reconstruct g proof
              )
          in
            debug "End reconstruction";
            Proof sproof
          end
       else (debug "SNH: imperative_search2"; raise ERR "imperative_search" "")
       )
     | _ => r
  in
    end_search ();
    sproof_status
  end
  )

end (* struct *)
