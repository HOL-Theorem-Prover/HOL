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
val last_stac = ref ""
fun debug_err s = (debug ("Error: " ^ s); raise ERR "standard" "error")

(* --------------------------------------------------------------------------
   Exceptions
   -------------------------------------------------------------------------- *)

exception SearchTimeOut
exception NoNextTac

(* -------------------------------------------------------------------------
   Search references
   -------------------------------------------------------------------------- *)

val notactivedict = ref (dempty Int.compare)
fun is_notactive x = dmem x (!notactivedict)
fun deactivate x = notactivedict := dadd x () (!notactivedict)

val proofdict = ref (dempty Int.compare)
val finproofdict = ref (dempty Int.compare)

val thmpredictor_glob = ref (fn g => [])
val stacpredictor_glob = ref (fn g => [])
val mcpredictor_glob = ref (fn gl => 0.0)

val tacdict_glob = ref (dempty String.compare)

val glob_timer = ref NONE

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
val mc_time = ref 0.0
val tot_time = ref 0.0

val stacpred_timer = total_time stacpred_time
val predict_timer = total_time predict_time
val thmpredict_timer = total_time thmpredict_time
val infstep_timer = total_time infstep_time
fun node_create_timer f x = total_time node_create_time f x
val node_find_timer = total_time node_find_time
val mc_timer = total_time mc_time
fun total_timer f x = total_time tot_time f x

fun reset_timers () =
  (
  stacpred_time := 0.0;
  predict_time := 0.0;
  thmpredict_time := 0.0;
  infstep_time := 0.0;
  node_create_time := 0.0;
  node_find_time := 0.0;
  mc_time := 0.0;
  tot_time := 0.0
  )
  
(* --------------------------------------------------------------------------
   Basic diagonalized cost function.
   -------------------------------------------------------------------------- *)  
  
fun estimate_distance (depth,heuristic) (g,pred) =
  let
    val width_coeff = ref 0.0  
    fun f (lbl as (stac,t,g1,gl1),_) =
      let
        val cost = (!width_coeff) + Real.fromInt depth
        val _ = width_coeff := (!width_coeff) + !hhs_width_coeff
        val final_score = cost + heuristic
      in
        (lbl,final_score)
      end
  in
    (g, map f pred)
  end
  
(* --------------------------------------------------------------------------
   Monte Carlo Tree Search
   -------------------------------------------------------------------------- *)

fun init_eval pripol pid =
  let
    val _ = debug_search "mcts evaluation"
    val prec = dfind pid (!proofdict)
    val {visit,pending,goalarr,prioreval,cureval,priorpolicy,...} = prec
    val eval =
      if !hhs_mcnoeval_flag 
        then 0.0
      else if !hhs_mctriveval_flag
        then 1.0
      else if not (null (!pending)) 
        then (!mcpredictor_glob) (Array.sub (#goalarr prec, hd (!pending)))
      else 1.0 (* 100 percent *)
  in
    priorpolicy := pripol;
    visit := 1.0;
    prioreval := eval;
    cureval := [eval] 
  end

fun backup_loop eval cid =
  let
    val crec = dfind cid (!proofdict)
    val {parid,visit,cureval,...} = crec
  in 
    cureval := eval :: !cureval;
    visit := !visit + 1.0;
    if parid = NONE then () else backup_loop eval (valOf parid)
  end

fun backup cid =
  let 
    val _ = debug_search "mcts backpropagation"
    val crec = dfind cid (!proofdict)
    val {parid,prioreval,...} = crec
  in 
    if parid = NONE then () else backup_loop (!prioreval) (valOf parid)
  end

fun backup_fail cid =
  let 
    val _ = debug_search "mcts backpropagation fail"
    val crec = dfind cid (!proofdict)
    val {parid,...} = crec
  in 
    if parid = NONE then () else backup_loop 0.0 (valOf parid)
  end


(* --------------------------------------------------------------------------
   Pattern predictions
   -------------------------------------------------------------------------- *)

fun install_stac tacdict stac =
  let 
    val tac = hhsTimeout.timeOut (!hhs_tactic_time) tactic_of_sml stac 
      handle e => (debug ("Warning: install_stac: " ^ stac); raise e)
  in
    tacdict := dadd stac tac (!tacdict)
  end
  
fun addpred_stac tacdict thmpredictor (g,pred) =
  if !hhs_thmlarg_flag orelse !hhs_termarg_flag then
    let 
      (* 20 approximately corresponds to maximal width *)
      val (al,bl) = part_n 20 pred 
      val bl' = filter (not o is_absarg_stac o #1 o fst) bl
      (* number of prediction is not flexible in thmpredictor *)
      val thmls = 
        String.concatWith " , " (map dbfetch_of_string (!thmpredictor_glob g))
      fun inst_entry (lbl as (stac,a1,b1,c1),score) =
        if is_absarg_stac stac
        then 
          let 
            val _ = debug_search ("instantiating: " ^ stac)
            val new_stac = inst_stac thmls g stac 
          in
            debug_search ("to: " ^ new_stac);
            install_stac tacdict_glob new_stac;
            SOME ((new_stac,a1,b1,c1),score)
          end
          handle _ => (debug "Warning: addpred_stac"; NONE)
        else SOME (lbl,score)
    in
      (g, List.mapPartial inst_entry al @ bl')
    end
  else (g, pred)   
  
  
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
    fun init_empty _ = ref []
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
      (* compute cost function *)
      predarrn = Array.fromList (map length [pred]),
      width    = ref 0,
      depth = 0,
      timedepth = 0.0,
      (* proof saved for reconstruction + children *)
      pending  = ref [0],
      children = ref [],
      (* proof saved for reconstruction + children *)  
      proofl   = ref [],
      childrena = Array.fromList (map init_empty [goal]),
      (* preventing loop and parallel steps *)
      pardict  = dempty goal_compare,
      trydict  = ref (dempty (list_compare goal_compare)),
      (* monte carlo *)
      priorpolicy = ref 0.0,
      visit = ref 0.0,
      prioreval = ref 0.0, 
      cureval = ref [] 
      }
  in
    debug_search "Root";
    debug_search ("  goal: " ^
          String.concatWith "," (map string_of_goal [goal]));
    debug_search ("  pred: \n  " ^
       String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) [pred]));
    proofdict := dadd selfid selfrec (!proofdict);
    if !hhs_mc_flag then init_eval 0.0 selfid else ()
  end

fun root_create_wrap g =
  let
    (* Predictions *)
    val pred = (!stacpredictor_glob) g
    val cost = 0
    val (_,pred1) = 
      (
      add_accept tacdict_glob o
      add_metis tacdict_glob thmpredictor_glob o 
      stacpred_timer (addpred_stac tacdict_glob thmpredictor_glob) o
      estimate_distance (cost,0.0)
      ) 
        (g,pred)
  in
    root_create g pred1
  end

fun node_create pripol tactime parid parstac pargn parg goallist 
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
    fun init_empty _ = ref []
    val selfrec =
    {
      selfid   = selfid,
      parid    = SOME parid,
      parstac  = SOME parstac,
      pargn    = SOME pargn,
      parg     = SOME parg,
      goalarr  = Array.fromList goallist,
      predarr  = Array.fromList predlist,
      (* compute cost function *)
      predarrn = Array.fromList (map length predlist),
      width    = ref 0,
      depth    = pardepth + 1,
      timedepth = partimedepth + tactime,
      (* goal considered *)
      pending  = ref pending,
      children = ref [],
      (* proof saved for reconstruction + children *)
      proofl = ref [],
      childrena = Array.fromList (map init_empty goallist),
      (* preventing loop and parallel steps *)
      pardict  = pardict,
      trydict  = ref (dempty (list_compare goal_compare)),
      (* monte carlo: dummy values changed by init_eval *)
      priorpolicy = ref 0.0,
      visit = ref 0.0,
      prioreval = ref 0.0,
      cureval = ref []   
    }
  in
    debug_search 
       ("Node " ^ int_to_string selfid ^ " " ^ int_to_string parid ^ " " ^
        Real.toString (! (#priorpolicy selfrec)));
    debug_search 
       ("  goals: " ^ String.concatWith "," (map string_of_goal goallist));
    debug_search ("  predictions: " ^
       String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) predlist));
    proofdict := dadd selfid selfrec (!proofdict);
    if !hhs_mc_flag then init_eval pripol selfid else ();
    selfid
  end

fun node_delete pid =
  (debug_search ("node_delete " ^ int_to_string pid); deactivate pid)

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
    val _ = last_stac := stac
    val tim = dfind stac (!stactime_dict) handle _ => (!hhs_tactic_time)
    val _ = stac_counter := !stac_counter + 1
    val istac =
      if (!hhs_thmlarg_flag orelse !hhs_termarg_flag) andalso
         is_absarg_stac stac 
      then
        let
          val thml   = (!thmpredictor_glob) g
          val thmls  = String.concatWith " , " (map dbfetch_of_string thml)
          val rstac = inst_stac thmls g stac
        in
          install_stac tacdict_glob rstac;
          rstac
        end  
      else stac
    val tac = dfind stac (!tacdict_glob) 
      handle _ => debug_err ("apply_stac: " ^ stac)
    val glo = dfind (stac,g) (!stacgoal_cache) handle _ => app_tac tim tac g
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
      handle _ => debug_err "apply_next_stac: empty pending"
    val goal = Array.sub (#goalarr prec, gn)
    val pred = Array.sub (#predarr prec, gn)
    val trydict_unref = !(#trydict prec)
    val pardict = (#pardict prec)
    val ((stac,_,_,_),_) = hd pred 
      handle _ => debug_err "apply_next_stac: empty pred"
  in
    infstep_timer (apply_stac pardict trydict_unref stac) goal
  end

(* ----------------------------------------------------------------------
   Searching for a node (goal list) to explore.      
   ---------------------------------------------------------------------- *)

fun has_empty_pred pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (!(#pending prec))
    val pred = Array.sub (#predarr prec, gn)
      handle _ => debug_err ("find_next_tac: " ^ int_to_string pid)
  in
    if null pred then (deactivate pid; true) else false
  end

fun standard_node_find l0 =
  let
    val _ = debug_search "standard_node_find"
    fun give_score (pid,prec) =
      let
        val gn = hd (!(#pending prec)) handle _ => debug_err "m4"
        val pred = Array.sub (#predarr prec, gn)
        val sc = snd (hd pred) handle _ => debug_err "m3"
      in
        (pid, sc)
      end
    val l1 = map give_score l0
    val l2 = dict_sort compare_rmin l1
    val (pid,score) = hd l2 handle _ => debug_err "m0"
    val prec = dfind pid (!proofdict)
    val _ = incr (#width prec)
    val gn = hd (!(#pending prec)) handle _ => debug_err "m1"
    val ((stac,_,_,_),_) = 
      hd (Array.sub (#predarr prec, gn)) handle _ => debug_err "m2"
  in
    debug_search ("Find " ^ int_to_string pid ^ " " ^ Real.toString score ^
      "\n  " ^ stac);
    pid
  end

fun mc_node_find pid =
  let
    val prec = dfind pid (!proofdict) 
    val {children,visit,...} = prec
    val pvisit = !(#visit prec)
    val pdenom = Math.sqrt pvisit
    (* try new tactic on the node itself *)
    val n = length (!children) 
    val self_pripol = 1.0 / Math.pow (2.0, Real.fromInt n)
    val self_curpol = 1.0 / pdenom
    val self_selsc = (pid, (!hhs_mc_coeff) * (self_pripol / self_curpol))
    (* or explore deeper existing paritial proofs *)
    fun f cid = 
      let 
        val crec = dfind cid (!proofdict)
        val pripol = !(#priorpolicy crec)
        val meaneval = average_real (!(#cureval crec))
        val visit = !(#visit crec)
        val curpol = (visit + 1.0) / pdenom
      in
        (cid, meaneval + (!hhs_mc_coeff) * (pripol / curpol))
      end
    (* sort and select node with best selection score *)
    val l0 = self_selsc :: List.map f (!children)
    val l1 = dict_sort compare_rmax l0
    val (selid,_) = hd l1
  in
    if pid = selid then (pid,self_pripol) else mc_node_find selid
  end

fun try_mc_find () =
  if Timer.checkRealTimer (valOf (!glob_timer)) > (!hhs_search_time) 
  then (debug_search "timeout"; raise SearchTimeOut)
  else 
    let val (pid,pripol) = mc_node_find 0 in
      if is_notactive pid
      then (backup_fail pid; try_mc_find ())
      else (pid,pripol)
    end

fun node_find () = 
  let
    val _ = debug_search "node_find"
    val l0 = filter (fn x => not (is_notactive (fst x))) (dlist (!proofdict))
    val l1 = filter (fn x => not (has_empty_pred (fst x))) l0
    val _ = if null l1 then (debug_search "nonexttac"; raise NoNextTac) else ()
  in
    if !hhs_mc_flag then try_mc_find () else (standard_node_find l1, 0.0)
  end

(* ---------------------------------------------------------------------------
   Closing proofs
   -------------------------------------------------------------------------- *)

fun children_of pid =
  let val prec = dfind pid (!proofdict) in !(#children prec) end

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
    val {proofl,pending,parid,children,visit,trydict,priorpolicy,...} = prec
  in
    (* checking some assertions *)
    if !pending <> [] then () else debug_err "close_proof: pending";
    if valOf gn = hd (!pending) then () else debug_err "close_proof";
    (* remember which child gave the proof of which goal *)
    proofl := (valOf gn, valOf stac, cid) :: !proofl;
    (* saves the child that gave the proof *)
    node_save cid; 
    (* close all current  children *)
    close_descendant pid; 
    (* switching to next pending goal, erasing previous statistics *)
    children := [];
    trydict := dempty (list_compare goal_compare);
    pending := tl (!pending);
    if !hhs_mc_flag then init_eval (!priorpolicy) pid else ();
    (* check if the goal was solved and recursively close *)
    if null (!pending)
    then
      if parid = NONE
      (* special case when it's root *)
      then (debug_search "proof"; 
            node_save pid; node_delete pid; raise ProofFound)
      else close_proof pid (valOf parid)
    else ()
  end

(* --------------------------------------------------------------------------
   Creating new nodes
   -------------------------------------------------------------------------- *)

fun node_create_gl pripol tactime gl pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val prev_predl = Array.sub (#predarr prec, gn)
    val prev_predn = Array.sub (#predarrn prec, gn)
    val ((stac,_,_,_),_) = hd prev_predl
    val parchildren = #children prec
    val parchildrensave = Array.sub (#childrena prec,gn)
    val depth = #depth prec + 1
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
    val cost = depth + width
    val predlist0 =
      map (
          add_accept tacdict_glob o
          add_metis tacdict_glob thmpredictor_glob o 
          stacpred_timer (addpred_stac tacdict_glob thmpredictor_glob) o
          estimate_distance (cost,0.0) o 
          add_pred
          ) 
      gl  
    val predlist1 = map snd predlist0
    val pending0 = number_list 0 predlist1
    val pending1 = map (fn (gn,pred) => (gn, (snd o hd) pred)) pending0
    val pending = map fst (dict_sort compare_rmax pending1)
    (* Updating the list of parent *)
    val new_pardict = dadd goal () (#pardict prec)
    (* New node *)
    val selfid = 
      node_create pripol 
        tactime pid stac gn goal gl predlist1 pending new_pardict
  in
    parchildren := selfid :: (!parchildren);
    parchildrensave := selfid :: (!parchildrensave);
    selfid
  end

(* fake a node when a proof is found but no search is performed on this node *)
fun node_create_empty pripol tactime pid =
  let
    val prec = dfind pid (!proofdict)
    val gn   = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val ((stac,_,_,_),_) = hd (Array.sub (#predarr prec, gn))
    val parchildren = #children prec
    val parchildrensave = Array.sub (#childrena prec,gn)
    val selfid = node_create pripol tactime pid stac gn goal [] [] [] 
                   (dempty goal_compare)
  in
    parchildren := selfid :: (!parchildren);
    parchildrensave := selfid :: (!parchildrensave);
    selfid
  end

(* ---------------------------------------------------------------------------
   Search function. Modifies the proof state.
   -------------------------------------------------------------------------- *)

fun init_search thmpredictor stacpredictor mcpredictor tacdict g =
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
  notactivedict := dempty Int.compare;
  proofdict    := dempty Int.compare;
  finproofdict := dempty Int.compare;
  (* easier access to values *)
  stacpredictor_glob := predict_timer stacpredictor;
  thmpredictor_glob := thmpredict_timer thmpredictor;
  mcpredictor_glob := mc_timer mcpredictor;
  tacdict_glob := tacdict;
  (* statistics *)
  reset_timers ();
  stac_counter := 0;
  max_depth_mem := 0
  )

fun get_next_pred pid =
  let
    val _ = debug_search "get_next_pred"
    val prec = dfind pid (!proofdict)
  in
    if null (!(#pending prec)) then () else
      let
        val gn   = hd (!(#pending prec))
        val pred = Array.sub (#predarr prec, gn)
      in
        if null pred orelse null (tl pred)  
          then deactivate pid
          else Array.update (#predarr prec, gn, tl pred)
      end
  end

fun search_step () =
  let
    val (pid,pripol) = node_find_timer node_find ()
    val prec = dfind pid (!proofdict)
    val trydict = #trydict prec
    val (glo,tactime) = add_time apply_next_stac pid
    fun f0 () = 
      (
      if !hhs_mc_flag then backup_fail pid else ();
      get_next_pred pid
      )
    fun f1 gl =
      if gl = []
      then
        let val cid = 
          node_create_timer (node_create_empty pripol tactime) pid 
        in
          if !hhs_mc_flag then backup cid else ();
          close_proof cid pid (* change pid to next goal *)
        end
      else
        (
        trydict := dadd gl () (!trydict);
        let val cid = 
          node_create_timer (node_create_gl pripol tactime gl) pid
        in
          if !hhs_mc_flag then backup cid else ();
          get_next_pred pid
        end
        )
  in
    case glo of
      NONE    => f0 ()
    | SOME gl => f1 gl
  end

datatype proof_status_t = 
  ProofError | ProofSaturated | ProofTimeOut | Proof of string

fun search_loop () =
  (
  if Timer.checkRealTimer (valOf (!glob_timer)) > (!hhs_search_time)
    then ProofTimeOut
  else if dmem 0 (!finproofdict) then Proof ""
  else (search_step (); debug_search "search step"; search_loop ())
  )
  handle NoNextTac => ProofSaturated
       | SearchTimeOut => ProofTimeOut
       | ProofFound => Proof ""
       | e => raise e

fun proofl_of pid =
  let
    val prec = dfind pid (!finproofdict) handle _ => debug_err "proofl_of"
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
  debug_proof ("    mc time: " ^ Real.toString (!mc_time));   
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

(* From positives tactics and update hhs_stac, hhs_stac_cthy *)
fun selflearn_aux proof = case proof of 
    Tactic (stac,g) =>
      (
      let
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

(* From positives and negative goals, rely on proofdict
   and update hhs_mcdict, hhs_mcdict_cthy *)
   
fun learngoal_loop pid =
  let 
    val prec = dfind pid (!proofdict) 
    val {proofl,childrena,goalarr,...} = prec
    val i = ref 0
    val totn = ref 0
  in
    while !i < Array.length goalarr do
      let 
        val g  = Array.sub (goalarr,!i)
        val fea = fea_of_goal g
        val cl = !(Array.sub (childrena,!i))
        val b  = mem (!i) (map #1 (!proofl))
        val n  = 1 + sum_int (map learngoal_loop cl)
      in
        hhs_mcdict := dadd fea (b,n) (!hhs_mcdict);
        hhs_mcdict_cthy := dadd fea (b,n) (!hhs_mcdict_cthy);
        totn := !totn + n;
        incr i
      end
    ;
    !totn  
  end

fun learngoal () = 
  (
  debug ("proofdict: " ^ int_to_string (dlength (!proofdict)));
  ignore (learngoal_loop 0);
  print_endline (int_to_string (dlength (!hhs_mcdict_cthy)));
  debug ("mcdict_cthy: " ^ int_to_string (dlength (!hhs_mcdict_cthy)))
  )

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
    val _ = if !hhs_mcrecord_flag then learngoal () else ()
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
    end_search (); (* erase all references *)
    sproof_status
  end
  )

end (* struct *)
