(* ========================================================================== *)
(* FILE          : hhsSearch.sml                                              *)
(* DESCRIPTION   : Search algorithm for TacticToe.                            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsSearch :> hhsSearch =
struct

open HolKernel boolLib Abbrev hhsTools hhsTimeout hhsFeature hhsPredict
hhsExec hhsLexer hhsMinimize hhsMetis hhsData hhsLearn hhsSetup

val ERR = mk_HOL_ERR "hhsSearch"

(* --------------------------------------------------------------------------
   Exceptions
   -------------------------------------------------------------------------- *)

exception SearchTimeOut
exception NoNextTac

(* -------------------------------------------------------------------------
   Search references
   -------------------------------------------------------------------------- *)

fun empty_predictor (g:goal) = []
val proofdict = ref (dempty Int.compare)
val finproofdict = ref (dempty Int.compare)
val tacdict_glob = ref (dempty String.compare)
val minstepdict_glob = ref (dempty goal_compare)
val thmpredictor_glob = ref (fn g => [])
val stacpredictor_glob = ref empty_predictor
val glob_timer = ref NONE

(*
val goaldepth_dict = ref (dempty goal_compare)
val update_goaldepth (goal,depth) =
  goaldepth_dict := dadd goal depth (!goaldepth_dict)
*)

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
   Debugging
   -------------------------------------------------------------------------- *)

val stac_counter = ref 0

fun string_of_predentry ((stac,_,_,_),score) =
  "(" ^ stac ^ "," ^ Real.toString score ^ ")"

fun string_of_pred pred =
  "[" ^ String.concatWith "," (map string_of_predentry pred) ^ "]"

val stacpred_time = ref 0.0
val predict_time = ref 0.0
val thmpredict_time = ref 0.0
val infstep_time = ref 0.0
val node_create_time = ref 0.0
val node_find_time = ref 0.0
val astar_time = ref 0.0
val tot_time = ref 0.0

val stacpred_timer = total_time stacpred_time
val predict_timer = total_time predict_time
val thmpredict_timer = total_time thmpredict_time
val infstep_timer = total_time infstep_time
fun node_create_timer f x = total_time node_create_time f x
val node_find_timer = total_time node_find_time
val astar_timer = total_time astar_time
fun total_timer f x = total_time tot_time f x

fun reset_timers () =
  (
  stacpred_time := 0.0;
  predict_time := 0.0;
  thmpredict_time := 0.0;
  infstep_time := 0.0;
  node_create_time := 0.0;
  node_find_time := 0.0;
  astar_time := 0.0;
  tot_time := 0.0
  )
  
(* --------------------------------------------------------------------------
   A*-heurisitic
   -------------------------------------------------------------------------- *)

fun minstep_cache g = dfind g (!minstepdict_glob) 
  handle _ => (debug "Error: minstep"; NONE)

fun firstPartial_n n l = 
  if n <= 0 then [] else
  case l of
    [] => [] 
  | NONE :: m => firstPartial_n n m
  | SOME d :: m => d :: firstPartial_n (n-1) m

fun average_real l = 
  if null l
  then (debug "Error: average_real"; 0.0)
  else sum_real l / (Real.fromInt (length l))

fun astar n g pred =
  let 
    val l0 = map (minstep_cache o #3 o fst) pred
    val l1 = firstPartial_n n l0
  in
    average_real l1
  end

fun estimate_distance (depth,timedepth) (g,pred) =
  let
    val width_coeff = ref 0.0 
    val global_heuristic =
      if !hhs_astar_flag
      then astar_timer (astar (!hhs_astar_radius) g) pred 
      else 0.0
       
    fun f (lbl as (stac,t,g1,gl1),_) =
      let
        val cost = (!width_coeff) + 
          (if !hhs_timedepth_flag then timedepth else Real.fromInt depth)
        val heuristic = 
          if !hhs_astar_flag then 
            if g = g1
            then (valOf (minstep_cache g) handle _ => global_heuristic)
            else global_heuristic
          else 0.0
        val _ = width_coeff := (!width_coeff) +
                (if !hhs_timedepth_flag 
                 then !hhs_tactic_time 
                 else !hhs_width_coeff)
        val final_score = inv_succrate stac * (cost + heuristic)
      in
        (lbl,final_score)
      end
  in
    (g, map f pred)
  end
  
(* --------------------------------------------------------------------------
   Node creation and deletion
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
      predarrn = Array.fromList (map length [pred]),
      width    = ref 0,
      pending  = ref [0],
      proofl   = ref [],
      children = ref [],
      pardict  = dempty goal_compare,
      trydict  = ref (dempty (list_compare goal_compare)),
      depth = 0,
      timedepth = 0.0
      }
  in
    debug_search "Root";
    debug_search ("  goal: " ^
          String.concatWith "," (map string_of_goal [goal]));
    debug_search ("  pred: \n  " ^
       String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) [pred]));
    proofdict := dadd selfid selfrec (!proofdict)
  end

fun root_create_wrap g =
  let
    (* Predictions *)
    val pred = (!stacpredictor_glob) g
    val (_,pred1) = 
      (
      add_accept tacdict_glob o
      add_metis tacdict_glob thmpredictor_glob o 
      stacpred_timer (addpred_stac tacdict_glob thmpredictor_glob) o
      estimate_distance (0,0.0)
      ) 
        (g,pred)
  in
    root_create g pred1
  end

fun node_create tactime parid parstac pargn parg goallist 
    predlist pending pardict =
  let
    val pardepth = #depth (dfind parid (!proofdict))
    val partimedepth = #timedepth (dfind parid (!proofdict))
    (* for stats *)
    val _ = if pardepth + 1 > !max_depth_mem
            then max_depth_mem := pardepth + 1
            else ()
    val selfid = next_pid ()
    (*
    fun f g = update_goaldepth (g,pardepth + 1)
    val _ = app f goallist
    *)
    val selfrec =
    {
      selfid   = selfid,
      parid    = SOME parid,
      parstac  = SOME parstac,
      pargn    = SOME pargn,
      parg     = SOME parg,
      goalarr  = Array.fromList goallist,
      predarr  = Array.fromList predlist,
      predarrn = Array.fromList (map length predlist),
      width    = ref 0,
      pending  = ref pending,
      proofl   = ref [],
      children = ref [],
      pardict  = pardict,
      trydict  = ref (dempty (list_compare goal_compare)),
      depth    = pardepth + 1,
      timedepth = partimedepth + tactime
    }
  in
    debug_search 
       ("Node " ^ int_to_string selfid ^ " " ^ int_to_string parid ^ " " ^
        Real.toString (#timedepth selfrec));
    debug_search 
       ("  goals: " ^ String.concatWith "," (map string_of_goal goallist));
    debug_search ("  predictions: " ^
       String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) predlist));
    proofdict := dadd selfid selfrec (!proofdict);
    selfid
  end

fun node_delete pid =
  (
  debug_search ("node_delete " ^ int_to_string pid);
  proofdict := drem pid (!proofdict)
  )

fun node_save pid =
  (
  debug_search ("node_save " ^ int_to_string pid);
  let val prec = dfind pid (!proofdict) in
    finproofdict := dadd pid prec (!finproofdict)
  end
  )

(* --------------------------------------------------------------------------
   Application of a tactic.
   -------------------------------------------------------------------------- *)

fun update_cache k v =
  if !hhs_cache_flag 
  then stacgoal_cache := dadd k v (!stacgoal_cache) 
  else ()

fun apply_stac pardict trydict_unref stac g =
  let
    val tim = dfind stac (!stactime_dict) handle _ => (!hhs_tactic_time)
    val _ = count_try stac
    val _ = stac_counter := !stac_counter + 1
    val tac = dfind stac (!tacdict_glob) 
              handle _ => (debug ("SNH: apply_stac:" ^ stac); 
                           raise ERR "apply_stac" stac)
    val glo = dfind (stac,g) (!stacgoal_cache) 
              handle _ => app_tac tim tac g
    val new_glo =
      case glo of
        NONE => NONE
      | SOME gl =>
      (
      if mem g gl orelse exists (fn x => dmem x pardict) gl then NONE
      else if dmem gl trydict_unref then NONE
      else SOME gl
      )
  in
    update_cache (stac,g) new_glo;
    new_glo
  end

fun apply_next_stac pid =
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
    infstep_timer (apply_stac pardict trydict_unref stac) goal
  end

(* ----------------------------------------------------------------------
   Searching for a node (goal list) to explore.      
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
    then (debug_search "nonexttac"; raise NoNextTac)
    else
      let
        val (pid,score) = hd l2
        val prec = dfind pid (!proofdict)
        val _ = incr (#width prec)
        val gn = hd (! (#pending prec))
        val goal = Array.sub (#goalarr prec, gn)
        val ((stac,_,_,_),_) = hd (Array.sub (#predarr prec, gn))
      in
        debug_search ("Find " ^ int_to_string pid ^ " " ^ Real.toString score ^
          "\n  " ^ stac);
        pid
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

(* --------------------------------------------------------------------------
   Creating new nodes
   -------------------------------------------------------------------------- *)

fun node_create_gl tactime gl pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val prev_predl = Array.sub (#predarr prec, gn)
    val prev_predn = Array.sub (#predarrn prec, gn)
    val ((stac,_,_,_),_) = hd prev_predl
    val parchildren = #children prec
    val depth = #depth prec + 1
    val timedepth = #timedepth prec + tactime
    
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
      
    val width = prev_predn - (length prev_predl)

    val predlist0 =
      map (
          add_accept tacdict_glob o
          add_metis tacdict_glob thmpredictor_glob o 
          stacpred_timer (addpred_stac tacdict_glob thmpredictor_glob) o
          estimate_distance (depth + width,timedepth) o 
          add_pred
          ) 
      gl
    val predlist1 = map snd predlist0
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
   Search function. Modifies the proof state.
   -------------------------------------------------------------------------- *)

fun init_search thmpredictor stacpredictor tacdict minstepdict g =
  (
  (* global time-out *)
  glob_timer := SOME (Timer.startRealTimer ());
  (* theorems for ACCEPT_TAC *)
  init_thml_glob (); 
  (* flexible tactic time-out *)
  stactime_dict := dempty String.compare;
  (* caching *)
  stacgoal_cache := dempty stacgoal_compare;
  goalpred_cache := dempty goal_compare;
  (* proof states *)
  pid_counter := 0;
  proofdict    := dempty Int.compare;
  finproofdict := dempty Int.compare;
  (* easier access to values *)
  stacpredictor_glob := predict_timer stacpredictor;
  thmpredictor_glob := thmpredict_timer thmpredictor;
  tacdict_glob := tacdict;
  minstepdict_glob := minstepdict;
  (* statistics *)
  reset_timers ();
  stac_counter := 0;
  max_depth_mem := 0
  )

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
    val pid = node_find_timer node_find ()
    val prec = dfind pid (!proofdict)
    val trydict = #trydict prec
    val (glo,tactime) = add_time apply_next_stac pid
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
  debug_proof ("Time: " ^ Real.toString (!tot_time));
  debug_proof ("  inferstep time: " ^ Real.toString (!infstep_time));
  debug_proof ("  node_find time: " ^ Real.toString (!node_find_time));
  debug_proof ("  node_crea time: " ^ Real.toString (!node_create_time));
  debug_proof ("    pred time: " ^ Real.toString (!predict_time));
  debug_proof ("    thmpred time: " ^ Real.toString (!thmpredict_time));
  debug_proof ("    astar time: " ^ Real.toString (!astar_time));
  debug_proof ("    stacpred time: " ^ Real.toString (!stacpred_time));
  proofdict    := dempty Int.compare;
  finproofdict := dempty Int.compare;
  tacdict_glob := dempty String.compare;
  stacgoal_cache := dempty stacgoal_compare;
  goalpred_cache := dempty goal_compare
  )

(* ---------------------------------------------------------------------------
   Self learning
   -------------------------------------------------------------------------- *)

fun selflearn_aux proof = case proof of 
    Tactic (stac,g) => 
      (
      let 
        val _ = count_succ stac
        val ((gl,_),t) = add_time (tactic_of_sml stac) g
        val lbl = (stac,t,g,gl) 
      in
        save_lbl [] lbl (* to be updated *)
      end
      handle _ => debug_search ("Error: selflearn: " ^ stac)
      )
  | Then (p1,p2) => (selflearn_aux p1; selflearn_aux p2)
  | Thenl (p,pl) => (selflearn_aux p; app selflearn_aux pl)

fun selflearn proof =
  if !hhs_selflearn_flag 
  then debug_t "selflearn" selflearn_aux proof
  else ()

fun debug_err s = (debug s; raise ERR "" "")

(* ---------------------------------------------------------------------------
   Main
   -------------------------------------------------------------------------- *)

fun imperative_search thmpredictor stacpredictor tacdict minstepdict goal =
  (
  init_search thmpredictor stacpredictor tacdict minstepdict goal;
  total_timer (node_create_timer root_create_wrap) goal;
  let
    val r = total_timer search_loop ()
    val _ = debug_search "End search loop"
    val sproof_status = case r of
      Proof _  =>
      (
      if dmem 0 (!finproofdict) then
        let 
          val proofl = proofl_of 0 handle _ => debug_err "SNH0"
          val proof = 
            if length proofl <> 1 
            then debug_err "SNH1"
            else (selflearn (hd proofl); minimize (hd proofl))
          val sproof = debug_t "reconstruct" reconstruct goal proof
        in
          Proof sproof
        end
      else debug_err "SNH2"
      )
    | _ => r
  in
    end_search ();
    sproof_status
  end
  )

end (* struct *)
