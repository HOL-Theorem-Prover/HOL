(* ========================================================================= *)
(* FILE          : tttSearch.sml                                             *)
(* DESCRIPTION   : Search algorithm for TacticToe.                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttSearch :> tttSearch =
struct

open HolKernel Abbrev boolLib aiLib
  smlTimeout smlLexer smlExecute
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  psMinimize
  tttSetup tttLearn

val ERR = mk_HOL_ERR "tttSearch"
fun debug s = debug_in_dir ttt_debugdir "tttSearch" s
fun debug_err s = (debug ("Error: " ^ s); raise ERR s "")

(* -------------------------------------------------------------------------
   Exceptions
   ------------------------------------------------------------------------- *)

exception SearchTimeout
exception SearchSaturated

(* -------------------------------------------------------------------------
   Tell if a node is active or not
   ------------------------------------------------------------------------- *)

val notactivedict = ref (dempty Int.compare)
fun is_notactive x = dmem x (!notactivedict)
fun is_active x = not (is_notactive x)

fun deactivate x =
  (
  debug ("deactivate " ^ int_to_string x);
  notactivedict := dadd x () (!notactivedict)
  )

(* -------------------------------------------------------------------------
   Search references
   ------------------------------------------------------------------------- *)

val glob_timer = ref NONE
val proofdict = ref (dempty Int.compare)

(* global values to prevent many arguments in functions *)
val thmpredictor_glob = ref (fn _ => (fn _ => []))
val tacpredictor_glob = ref (fn _ => [])

(* -------------------------------------------------------------------------
   Caching tactic applications on goals
   ------------------------------------------------------------------------- *)

val stacgoal_cache = ref (dempty (cpl_compare String.compare goal_compare))

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

val stac_counter = ref 0
fun string_of_pred pred = "[" ^ String.concatWith "," pred ^ "]"

val tactime = ref 0.0
val thmtime = ref 0.0

val tactimer = total_time tactime
val thmtimer = total_time thmtime

val inst_time = ref 0.0
val terminst_time = ref 0.0
val infstep_time = ref 0.0
val node_create_time = ref 0.0
val node_find_time = ref 0.0

val inst_timer = total_time inst_time
val infstep_timer = total_time infstep_time
fun node_create_timer f x = total_time node_create_time f x
val node_find_timer = total_time node_find_time

val tot_time = ref 0.0
fun total_timer f x = total_time tot_time f x

fun reset_timers () =
  (
  tactime := 0.0;
  thmtime := 0.0;
  inst_time := 0.0;
  infstep_time := 0.0;
  node_create_time := 0.0;
  node_find_time := 0.0;
  tot_time := 0.0
  )

(* -------------------------------------------------------------------------
   Special tactics
   ------------------------------------------------------------------------- *)

val metis_spec = "tactictoe_metis"
fun add_metis pred = metis_spec :: pred

(* -------------------------------------------------------------------------
   MCTS: Priors
   ------------------------------------------------------------------------- *)

fun array_to_list a =
  let fun f (a,l) = a :: l in rev (Array.foldl f [] a) end

fun init_eval pripol pid =
  let
    val _ = debug "mcts evaluation"
    val prec = dfind pid (!proofdict)
    val {visit,pending,goalarr,prioreval,cureval,priorpolicy,...} = prec
    val eval = 1.0
  in
    priorpolicy := pripol;
    visit := 1.0;
    prioreval := eval;
    cureval := [eval]
  end

(* -------------------------------------------------------------------------
   MCTS: Backup (works marginally).
   Prior eval is constant equal to 1.0
   ------------------------------------------------------------------------- *)

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
    val _ = debug "mcts backpropagation"
    val crec = dfind cid (!proofdict)
    val {parid,prioreval,...} = crec
  in
    if parid = NONE then () else backup_loop (!prioreval) (valOf parid)
  end

fun backup_fail cid =
  let
    val _ = debug "backup fail"
    val crec = dfind cid (!proofdict)
    val {parid,...} = crec
  in
    if parid = NONE then () else backup_loop 0.0 (valOf parid)
  end

fun backup_success cid =
  let
    val _ = debug "backup success"
    val crec = dfind cid (!proofdict)
    val {parid,...} = crec
  in
    if parid = NONE then () else backup_loop 1.0 (valOf parid)
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
      depth = 0,
      (* *)
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
    debug "Root";
    debug ("  goal: " ^
      String.concatWith "," (map string_of_goal [goal]));
    debug ("  pred: \n  " ^
      String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) [pred]));
    proofdict := dadd selfid selfrec (!proofdict);
    init_eval 0.0 selfid
  end

fun root_create_wrap g =
  root_create g ((add_metis o !tacpredictor_glob) g)

fun node_create pripol tactime parid parstac pargn parg goallist
    predlist pending pardict =
  let
    val selfid = next_pid ()
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
      depth    = #depth (dfind parid (!proofdict)) + 1,
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
    val cdepth = #depth selfrec
  in
    if cdepth > !max_depth_mem then max_depth_mem := cdepth else ();
    debug
       ("Node " ^ int_to_string selfid ^ " " ^ int_to_string parid ^ " " ^
        Real.toString (! (#priorpolicy selfrec)));
    debug
       ("  goals: " ^ String.concatWith "," (map string_of_goal goallist));
    debug ("  predictions: " ^
       String.concatWith ",\n  " (map (string_of_pred o (first_n 2)) predlist));
    proofdict := dadd selfid selfrec (!proofdict);
    init_eval pripol selfid;
    selfid
  end

fun node_delete pid =
  (debug ("node_delete " ^ int_to_string pid); deactivate pid)

(* -------------------------------------------------------------------------
   Change the name of the tactic that has been applied
   ------------------------------------------------------------------------- *)

fun update_curstac newstac pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (!(#pending prec))
    val pred = Array.sub (#predarr prec, gn)
    val newpred = newstac :: tl pred
  in
    Array.update (#predarr prec, gn, newpred)
  end
  handle Interrupt => raise Interrupt | _ =>
    debug_err ("update_curstac :" ^ newstac)


(* -------------------------------------------------------------------------
   Caches
   ------------------------------------------------------------------------- *)

val thml_dict = ref (dempty (cpl_compare goal_compare Int.compare))
val inst_dict = ref (dempty (cpl_compare String.compare goal_compare))
val tac_dict = ref (dempty String.compare)

fun cache_thmpred n g =
  dfind (g,n) (!thml_dict) handle NotFound =>
  let val sl = (!thmpredictor_glob) n g in
    thml_dict := dadd (g,n) sl (!thml_dict);
    sl
  end

fun cache_thminst stac g =
  dfind (stac,g) (!inst_dict) handle NotFound =>
  let
    val _ = debug ("instantiating: " ^ stac)
    val thmidl = cache_thmpred (!ttt_thmlarg_radius) g
    val newstac = inst_stac thmidl stac
    val newtac = tactic_of_sml newstac
      handle Interrupt => raise Interrupt | _ =>
        debug_err ("stac_to_tac: " ^ newstac)
    val r = (newstac, newtac, !ttt_tactic_time)
  in
    debug ("to: " ^ newstac);
    inst_dict := dadd (stac,g) r (!inst_dict);
    r
  end

fun cache_metisinst stac g =
  dfind (stac,g) (!inst_dict) handle NotFound =>
  let
    val thmidl = cache_thmpred (!ttt_metis_radius) g
    val newstac = mk_metis_call thmidl
    val newtac = tactic_of_sml newstac
      handle Interrupt => raise Interrupt | _ =>
        debug_err ("stac_to_tac: " ^ newstac)
  in
    inst_dict := dadd (stac,g) (newstac,newtac,!ttt_metis_time) (!inst_dict);
    debug ("to: " ^ newstac);
    (newstac,newtac,!ttt_metis_time)
  end

fun cache_stac stac =
  dfind stac (!tac_dict) handle NotFound =>
  let val tac = tactic_of_sml stac in
    tac_dict := dadd stac tac (!tac_dict);
    tac
  end

(* -------------------------------------------------------------------------
   Transforming code into a tactic. Doing necessary predictions.
   ------------------------------------------------------------------------- *)

fun stac_to_tac stac g =
  (
  if is_thmlarg_stac stac
    then cache_thminst stac g
  else if stac = metis_spec
    then cache_metisinst stac g
  else (stac, cache_stac stac, !ttt_tactic_time)
  )
  handle Interrupt => raise Interrupt | _ =>
    (debug ("stac_to_tac: " ^ stac);
     ("Tactical.NO_TAC", NO_TAC, !ttt_tactic_time))

(* -------------------------------------------------------------------------
   Application of a tactic.
   ------------------------------------------------------------------------- *)

fun glob_productive pardict trydict g glo =
  case glo of
    NONE => NONE
  | SOME gl =>
    (
    if op_mem goal_eq g gl orelse exists (fn x => dmem x pardict) gl orelse
       dmem gl trydict
    then NONE
    else SOME gl
    )

fun apply_stac pid pardict trydict stac g =
  let
    val _ = stac_counter := !stac_counter + 1
    (* instantiation of theorems and reading *)
    val (newstac,newtac,tim) = stac_to_tac stac g
    val _ = update_curstac newstac pid
    (* execution *)
    val glo = dfind (newstac,g) (!stacgoal_cache)
       handle NotFound => timeout_tactic tim newtac g
    (* testing for loops *)
    val newglo = glob_productive pardict trydict g glo
  in
    stacgoal_cache := dadd (newstac,g) glo (!stacgoal_cache);
    newglo
  end

fun apply_next_stac pid =
  let
    val _ = debug "apply_next_stac"
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
      handle Interrupt => raise Interrupt | _ =>
      debug_err "apply_next_stac: empty pending"
    val g = Array.sub (#goalarr prec, gn)
    val pred = Array.sub (#predarr prec, gn)
    val trydict = !(#trydict prec)
    val pardict = (#pardict prec)
    val stac = hd pred
      handle Interrupt => raise Interrupt | _ =>
      debug_err "apply_next_stac: empty pred"
  in
    infstep_timer (apply_stac pid pardict trydict stac) g
  end

(* ----------------------------------------------------------------------
   Searching for a node (goal list) to explore.
   ---------------------------------------------------------------------- *)

fun has_empty_pred pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (!(#pending prec))
    val pred = Array.sub (#predarr prec, gn)
      handle Interrupt => raise Interrupt | _ =>
      debug_err ("find_next_tac: " ^ int_to_string pid)
  in
    if null pred then (deactivate pid; true) else false
  end

fun mc_node_find pid =
  if Timer.checkRealTimer (valOf (!glob_timer)) >
     Time.fromReal (!ttt_search_time)
  then (debug "Warning: mc_node_find: loop"; raise SearchTimeout)
  else
    let
      val prec = dfind pid (!proofdict)
      val {children,visit,...} = prec
      val pvisit = !(#visit prec)
      val pdenom = Math.sqrt pvisit
      (* try new tactic on the node itself *)
      val n = length (!children)
      val self_pripol =
        Math.pow (1.0 - !ttt_policy_coeff, Real.fromInt n) * !ttt_policy_coeff
      val self_curpol = 1.0 / pdenom
      val self_selsc = (pid, 2.0 * self_pripol / self_curpol)
      (* or explore deeper existing partial proofs *)
      fun f cid =
        let
          val crec = dfind cid (!proofdict)
          val pripol = !(#priorpolicy crec)
          val meaneval = average_real (!(#cureval crec))
          val visit = !(#visit crec)
          val curpol = (visit + 1.0) / pdenom
        in
          (cid, meaneval + 2.0 * (pripol / curpol))
        end
      (* sort and select node with best selection score *)
      val l0 = self_selsc :: List.map f (!children)
      val l1 = dict_sort compare_rmax l0
      val (selid,_) = hd l1
    in
      if pid = selid then (pid,self_pripol) else mc_node_find selid
    end

fun try_mc_find () =
  if Timer.checkRealTimer (valOf (!glob_timer)) >
     Time.fromReal (!ttt_search_time)
  then (debug "Warning: try_mc_find"; raise SearchTimeout)
  else
    let
      val _ = debug "mc_node_find"
      val (pid,pripol) = mc_node_find 0
    in
      if is_notactive pid
      then (backup_fail pid; try_mc_find ())
      else (debug ("Find " ^ int_to_string pid); (pid,pripol))
    end

(* ---------------------------------------------------------------------------
   Closing proofs (should not need that with a proper search mechanism)
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
    (* close all current  children *)
    close_descendant pid;
    (* switching to next pending goal, erasing previous statistics *)
    children := [];
    trydict := dempty (list_compare goal_compare);
    pending := tl (!pending);
    (* check if the goal was solved and recursively close *)
    if null (!pending)
    then
      if parid = NONE (* root *)
      then (debug "proof found"; node_delete pid; raise ProofFound)
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
    val stac = hd prev_predl
    val parchildren = #children prec
    val parchildrensave = Array.sub (#childrena prec,gn)
    val depth = #depth prec + 1
    val predlist = map (add_metis o !tacpredictor_glob) gl
    val pending = rev (map fst (number_list 0 predlist))
    (* Updating list of parents *)
    val new_pardict = dadd goal () (#pardict prec)
    (* New node *)
    val selfid =
      node_create pripol
        tactime pid stac gn goal gl predlist pending new_pardict
  in
    parchildren := selfid :: (!parchildren);
    parchildrensave := selfid :: (!parchildrensave);
    selfid
  end

(* fake a node when a proof is found but no search is performed on this node *)
fun node_create_empty staco tactime pid =
  let
    val prec = dfind pid (!proofdict)
    val gn   = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val pred = Array.sub (#predarr prec, gn)
    val stac =
      case staco of
        NONE => hd pred
      | SOME s => s
    val parchildren = #children prec
    val parchildrensave = Array.sub (#childrena prec,gn)
    val selfid = node_create 0.0 tactime pid stac gn goal [] [] []
                   (dempty goal_compare)
  in
    parchildren := selfid :: (!parchildren);
    parchildrensave := selfid :: (!parchildrensave);
    selfid
  end

(* pid should be active and the goal should match *)
fun close_proof_wrap staco tactime pid =
  let val cid = node_create_timer (node_create_empty staco tactime) pid in
    backup cid;
    close_proof cid pid
  end

(* ---------------------------------------------------------------------------
   Search function. Modifies the proof state.
   -------------------------------------------------------------------------- *)

fun init_search thmpred tacpred g =
  (
  (* global time-out *)
  glob_timer := SOME (Timer.startRealTimer ());
  (* caching *)
  stacgoal_cache := dempty (cpl_compare String.compare goal_compare);
  thml_dict := dempty (cpl_compare goal_compare Int.compare);
  inst_dict := dempty (cpl_compare String.compare goal_compare);
  tac_dict := dempty String.compare;
  (* proof states *)
  pid_counter := 0;
  notactivedict := dempty Int.compare;
  proofdict := dempty Int.compare;
  (* easier access to values *)
  tacpredictor_glob := tactimer tacpred;
  thmpredictor_glob := thmtimer thmpred;
  (* statistics *)
  reset_timers ();
  stac_counter := 0;
  max_depth_mem := 0
  )

fun get_next_pred pid =
  let
    val _ = debug "get_next_pred"
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

fun node_find () =
  let
    val _ = debug "node_find"
    val l0 = filter (fn x => is_active (fst x)) (dlist (!proofdict))
    (* deactivate node with empty predictions (no possible actions) *)
    val l1 = filter (fn x => not (has_empty_pred (fst x))) l0
    val _ =
      if null l1 then
      (debug "SearchSaturated"; raise SearchSaturated)
      else ()
  in
    try_mc_find ()
  end


fun search_step () =
  let
    val (pid,pripol) = node_find_timer node_find ()
    val prec = dfind pid (!proofdict)
    val trydict = #trydict prec
    val (glo,tactime) = add_time apply_next_stac pid
    fun f0 () = (backup_fail pid; get_next_pred pid)
    fun f1 gl =
      if null gl
      then
        (backup_success pid;
         close_proof_wrap NONE tactime pid)
      else
        (
        trydict := dadd gl () (!trydict);
        let val cid =
          node_create_timer (node_create_gl pripol tactime gl) pid
        in
          backup cid; get_next_pred pid
        end
        )
  in
    case glo of
      NONE    => f0 ()
    | SOME gl => f1 gl
  end

datatype proof_status =
  ProofError | ProofSaturated | ProofTimeOut | Proof of string

fun search_loop () =
  (
  if Timer.checkRealTimer (valOf (!glob_timer)) >
     Time.fromReal (!ttt_search_time)
  then ProofTimeOut
  else (search_step (); debug "search step"; search_loop ())
  )
  handle SearchSaturated => (debug "proof: saturated"; ProofSaturated)
       | SearchTimeout => (debug "proof: timeout"; ProofTimeOut)
       | ProofFound => (debug "proof: found"; Proof "")
       | e => raise e

fun proofl_of pid =
  let
    val prec = dfind pid (!proofdict)
      handle NotFound => debug_err "proofl_of"
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
  debug ("Statistics");
  debug ("  infstep : " ^ int_to_string (!stac_counter));
  debug ("  nodes   : " ^ int_to_string (!pid_counter));
  debug ("  maxdepth: " ^ int_to_string (!max_depth_mem));
  debug ("Time: " ^ Real.toString (!tot_time));
  debug ("  inferstep: " ^ Real.toString (!infstep_time));
  debug ("  node_find: " ^ Real.toString (!node_find_time));
  debug ("  node_crea: " ^ Real.toString (!node_create_time));
  debug ("  thminst  : " ^ Real.toString (!inst_time));
  debug ("  tacpred  : " ^ Real.toString (!tactime));
  debug ("  thmpred  : " ^ Real.toString (!thmtime));
  proofdict      := dempty Int.compare;
  tac_dict       := dempty String.compare;
  inst_dict      := dempty (cpl_compare String.compare goal_compare);
  stacgoal_cache := dempty (cpl_compare String.compare goal_compare)
  )

(* -------------------------------------------------------------------------
   Main
   ------------------------------------------------------------------------- *)

fun search thmpred tacpred goal =
  (
  init_search thmpred tacpred goal;
  total_timer (node_create_timer root_create_wrap) goal;
  let
    val r = total_timer search_loop ()
    val _ = debug "End search loop"
    val proof_status = case r of
      Proof _  =>
      let
        val proofl = proofl_of 0
          handle Interrupt => raise Interrupt | _ => debug_err "SNH0"
        val proof0 = hd proofl handle Empty => debug_err "SNH1"
        val proof1 = minimize_proof proof0
        val sproof = reconstruct goal proof1
      in
        Proof sproof
      end
    | _ => r
  in
    end_search ();
    proof_status
  end
  )

end (* struct *)
