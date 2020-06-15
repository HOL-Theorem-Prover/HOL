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
  mlFeature mlThmData mlTacticData mlNearestNeighbor mlTreeNeuralNetwork
  psMinimize
  tttSetup tttLearn

val ERR = mk_HOL_ERR "tttSearch"

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type id = (int * int) list (* reverse of natural order *)

fun string_of_id id =
  let
    fun f (gn,sn) = "g" ^ its gn ^ "t" ^ its sn
    val sl = map f (rev id)
  in
    String.concatWith " " sl
  end

val id_compare = list_compare (cpl_compare Int.compare Int.compare)

datatype stacstatus =
  StacProved |
  StacSaturated |
  StacUndecided of goal list |
  StacFail | StacLoop | StacPara |
  StacFresh

datatype goalstatus = GoalProved | GoalSaturated | GoalUndecided
datatype nodestatus = NodeProved | NodeSaturated | NodeUndecided
datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
datatype proofstatus = Proof of string | ProofSaturated | ProofTimeout

fun string_of_searchstatus x = case x of
    SearchProved => "SearchProved"
  | SearchSaturated => "SearchSaturated"
  | SearchTimeout => "SearchTimeOut"

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

type stac_record =
  {stac : string, svis : real, ssum : real, stacstatus : stacstatus}

type goal_record =
  {
  goal : goal, gvis : real, gsum  : real, goalstatus : goalstatus,
  stacv : stac_record vector,
  siblingd : (goal list, unit) Redblackmap.dict
  }

type node =
  {
  nvis : real, nsum : real, nodestatus : nodestatus,
  goalv : goal_record vector,
  parentd : (goal, unit) Redblackmap.dict
  }

type tree = (id,node) Redblackmap.dict

(* -------------------------------------------------------------------------
   Backing up status
   ------------------------------------------------------------------------- *)

fun is_staclose x = case x of
    StacSaturated => true
  | StacFail => true
  | StacLoop => true
  | StacPara => true
  | _ => false
fun is_stacwin x = case x of StacProved => true | _ => false
fun is_stacundec x = case x of StacUndecided _ => true | _ => false
fun dest_stacundec x = case x of
    StacUndecided gl => gl
  | _ => raise ERR "dest_stacundec" ""
fun is_goalwin x = (x = GoalProved)
fun is_goallose x = (x = GoalSaturated)

fun backstatus_stacv stacv =
  let val v = Vector.map #stacstatus stacv in
    if Vector.exists is_stacwin v then GoalProved
    else if Vector.all is_staclose v then GoalSaturated
    else GoalUndecided
  end

fun backstatus_goalv goalv =
  let val v = Vector.map #goalstatus goalv in
    if Vector.all is_goalwin v then NodeProved
    else if Vector.exists is_goallose v then NodeSaturated
    else NodeUndecided
  end

fun backstatus_node node = case #nodestatus node of
    NodeUndecided => StacUndecided
      (vector_to_list (Vector.map #goal (#goalv node)))
  | NodeProved => StacProved
  | NodeSaturated => StacSaturated

(* -------------------------------------------------------------------------
   Node creation and backup
   ------------------------------------------------------------------------- *)

fun stac_create stac =
  {stac = stac, svis = 0.0, ssum = 0.0, stacstatus = StacFresh}

fun goal_create tacpred g =
  let val stacv = Vector.fromList (map stac_create (tacpred g)) in
    {
    goal = g, gvis = 0.0, gsum = 0.0,
    goalstatus = backstatus_stacv stacv,
    stacv = stacv,
    siblingd = dempty (list_compare goal_compare)
    }
  end

fun node_update tree (reward,stacstatus) (id,(gn,stacn)) =
  let
    val {nvis,nsum,goalv,parentd,...} = dfind id tree
    val {goal,gvis,gsum,stacv,siblingd,...} = Vector.sub (goalv,gn)
    val {stac,svis,ssum,...} = Vector.sub (stacv,stacn)
    (* update stacv *)
    val newstacrec =
      {stac = stac,
       svis = svis + 1.0, ssum = ssum + reward,
       stacstatus = stacstatus}
    val newstacv = Vector.update (stacv,stacn,newstacrec)
    (* update goalv *)
    val newgoalrec =
      {
      goal = goal,
      gvis = gvis + 1.0, gsum = gsum + reward,
      goalstatus = backstatus_stacv newstacv,
      stacv = newstacv,
      siblingd =
        if is_stacundec stacstatus (* in theory only needed in leafs *)
        then dadd (dest_stacundec stacstatus) () siblingd
        else siblingd
      }
    val newgoalv = Vector.update (goalv,gn,newgoalrec)
    (* update node *)
    val newnode =
      {
      nvis = nvis + 1.0, nsum = nsum + reward,
      nodestatus = backstatus_goalv newgoalv,
      goalv = newgoalv,
      parentd = parentd
      }
  in
    (dadd id newnode tree, backstatus_node newnode)
  end

fun node_backup (tree:tree) (reward,stacstatus) (id,(gn,stacn)) =
  let val (newtree,newstacstatus) =
    node_update tree (reward,stacstatus) (id,(gn,stacn))
  in
    if null id then newtree else
      node_backup newtree (reward,newstacstatus) (tl id, hd id)
  end

fun string_of_goall gl = String.concatWith "," (map string_of_goal gl)

fun node_create_backup (tree,tacpred) (reward,gl) (pid,(gn,stacn)) =
  let
    val node = dfind pid tree
    val pgoalv = #goalv node
    val pgoalrec = Vector.sub (pgoalv,gn)
    val pstacrec = Vector.sub (#stacv pgoalrec,stacn)
    val pgoal = #goal pgoalrec
    val pstac = #stac pstacrec
    val cgoalv = Vector.fromList (map (goal_create tacpred) gl)
    val cid = (gn,stacn) :: pid
    val node =
      {
      nvis = 1.0, nsum = reward,
      nodestatus = backstatus_goalv cgoalv,
      goalv = cgoalv,
      parentd = dadd pgoal () (#parentd node)
      }
    val newtree = dadd cid node tree
  in
    debugf "node: " string_of_id cid;
    debugf "goal: " string_of_goal pgoal;
    debug ("tactic: " ^ pstac);
    debugf "goals: " string_of_goall gl;
    debug ("\n");
    node_backup newtree (reward, backstatus_node node) (pid,(gn,stacn))
  end

fun starttree_of (tacpred,tnno) goal =
  let
    val goalv = Vector.fromList [goal_create tacpred goal]
    val root =
      {
      nvis = 1.0, 
      nsum = 0.0,
      nodestatus = backstatus_goalv goalv,
      goalv = goalv,
      parentd = dempty goal_compare
      }
  in
    debugf "root: " string_of_goal goal;
    dadd [] root (dempty id_compare)
  end

(* ----------------------------------------------------------------------
   Searching for a node to explore
   ---------------------------------------------------------------------- *)

fun puct gvis ((sum,vis),polv) =
  let
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt gvis) / (vis + 1.0)
  in
    exploitation + (!ttt_explo_coeff) * exploration
  end

fun expo_polv_aux ci (c:real) l = case l of
    [] => []
  | a :: m => (a,c) :: expo_polv_aux ci (ci * c) m
fun expo_polv ci l = expo_polv_aux ci ci l


fun first_goalundec goalv =
  let
    fun test (_,x) = (#goalstatus x = GoalUndecided)
    val goalvo = Vector.findi test goalv
  in
    if isSome goalvo then valOf goalvo else raise ERR "first_goalundec" "sat"
  end

fun first_stacfresh stacv =
  let
    fun test (_,x) = case #stacstatus x of StacFresh => true | _ => false
    val stacvo = Vector.findi test stacv
  in
    stacvo
  end

fun mcts_select tree pid =
  let
    val {goalv,...} = dfind pid tree
    val (gn,{goal,gvis,stacv,...}) = first_goalundec goalv
    val stacundecl = filter (is_stacundec o #stacstatus o snd)
      (number_fst 0 (vector_to_list stacv))
    fun add_puct ((stacn,{ssum,svis,...}),polv) =
      (stacn, puct gvis ((ssum,svis),polv))
    (* select node with best puct *)
    val fresho = first_stacfresh stacv
    val l0 = stacundecl @ (if isSome fresho then [valOf fresho] else [])
    val _ = if null l0 then raise ERR "mcts_select" "sat" else ()
    val l1 = map add_puct (expo_polv (!ttt_policy_coeff) l0)
    val l2 = dict_sort compare_rmax l1
    val (stacbestn,_) = hd l2
  in
    if isSome fresho andalso stacbestn = fst (valOf fresho)
    then pid
    else mcts_select tree ((gn,stacbestn) :: pid)
  end

(* -------------------------------------------------------------------------
   Application of a string tactic
   ------------------------------------------------------------------------- *)

fun status_of_stac parentd goalrec glo = case glo of
    NONE => StacFail
  | SOME gl =>
    (
    if null gl then StacProved else
    if op_mem goal_eq (#goal goalrec) gl orelse
       exists (fn x => dmem x parentd) gl
       then StacLoop
    else if dmem gl (#siblingd goalrec) then StacPara
    else StacUndecided gl
    )

fun is_metis_stac s = hd (partial_sml_lexer s) = "metisTools.METIS_TAC"

fun apply_stac parentd goalrec stac =
  let
    val tim = if is_metis_stac stac then 0.1 else 0.04
    val glo = app_stac tim stac (#goal goalrec)
  in
    status_of_stac parentd goalrec glo
  end

fun reward_of tnno stacstatus = case stacstatus of
    StacFail => 0.0
  | StacLoop => 0.0
  | StacPara => 0.0
  | StacProved => 1.0
  | StacUndecided gl => 
    (
    if isSome tnno then
      let 
        val tnn = valOf tnno
        val nntm = mask_unknown_inferdim tnn (nntm_of_gl gl) 
      in
        singleton_of_list (snd (singleton_of_list (infer_tnn tnn [nntm])))
      end
    else 1.0
    )
  | _ => raise ERR "reward_of" "unexpected"

fun string_of_stacstatus x = case x of
    StacFail => "StacFail"
  | StacLoop => "StacLoop"
  | StacPara => "StacPara"
  | StacProved => "StacProved"
  | StacUndecided gl => "StacUndecided"
  | _ => raise ERR "string_of_stacstatus" "unexpected"


fun apply_stac_pid (tree,(tacpred,tnno)) pid =
  let
    val node = dfind pid tree
    val (gn,goalundec) = first_goalundec (#goalv node)
    val (stacn,stacfresh) = valOf (first_stacfresh (#stacv goalundec))
    val pidx = (pid,(gn,stacn))
    val cid = (gn,stacn) :: pid
    val stacstatus =
      apply_stac (#parentd node) goalundec (#stac stacfresh)
    val reward = reward_of tnno stacstatus
    fun msg (a,b,c) =
      "node: " ^ string_of_id a ^ "\n" ^
      "tactic: " ^ #stac b ^ "\n" ^
      "status: " ^ string_of_stacstatus c ^ "\n"
  in
    case stacstatus of
      StacUndecided gl =>
      node_create_backup (tree,tacpred) (reward,gl) pidx
    | _ => (debugf "" msg (cid,stacfresh,stacstatus);
      node_backup tree (reward,stacstatus) pidx)
  end

(* -------------------------------------------------------------------------
   Main search function
   ------------------------------------------------------------------------- *)

fun search_loop (tacpred,tnno) starttree =
  let
    val timer = Timer.startRealTimer ()
    fun loop pred tree =
      if Timer.checkRealTimer timer > Time.fromReal (!ttt_search_time)
        then (SearchTimeout,tree)
      else if #nodestatus (dfind [] tree) = NodeSaturated
        then (SearchSaturated,tree)
      else if #nodestatus (dfind [] tree) = NodeProved
        then (SearchProved,tree)
      else
        let
          val pid = mcts_select tree []
          val newtree = apply_stac_pid (tree,pred) pid
        in
          loop pred newtree
        end
  in
    loop (tacpred,tnno) starttree
  end

fun extract_proofl tree id =
  let
    val node = dfind id tree
    val _ = if #nodestatus node = NodeProved then ()
      else raise ERR "extract_proof" (string_of_id id)
    fun f (gn,goalrec) =
      let
        val stacv = #stacv goalrec
        fun teststac (_,x) = is_stacwin (#stacstatus x)
        val (stacn,stacrec) = valOf (Vector.findi teststac stacv)
        val ptac = Tactic (#stac stacrec, #goal goalrec)
        val cid = (gn,stacn) :: id
      in
        if dmem cid tree
        then Thenl (ptac, extract_proofl tree cid)
        else ptac
      end
  in
    vector_to_list (Vector.mapi f (#goalv node))
  end

fun reconstruct_proofstatus (searchstatus,tree) g =
   case searchstatus of
    SearchSaturated => ProofSaturated
  | SearchTimeout => ProofTimeout
  | SearchProved =>
    let
      val _ = debug "extraction"
      fun f tree = singleton_of_list (extract_proofl tree [])
      val (proof1,t1) = add_time f tree
      val _ = debug ("extraction time: " ^ rts_round 6 t1)
      val _ = debug "minimization"
      val (proof2,t2) = add_time minimize_proof proof1
      val _ = print_endline ("minimization time: " ^ rts_round 6 t2)
      val _ = debug "reconstruction"
      val (sproof,t3) = add_time (reconstruct g) proof2
      val _ = print_endline ("reconstruction time: " ^ rts_round 6 t3)
    in
      Proof sproof
    end

fun search (tacpred,tnno) g =
  let
    val starttree = starttree_of (tacpred,tnno) g
    val ((searchstatus,tree),t) = add_time 
      (search_loop (tacpred,tnno)) starttree
    val _ = print_endline ("search time: " ^ rts_round 6 t)
  in
    (reconstruct_proofstatus (searchstatus,tree) g, tree)
  end

end (* struct *)
