(* ========================================================================= *)
(* FILE          : tttSearch.sml                                             *)
(* DESCRIPTION   : Proof search algorithm for TacticToe.                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttSearch :> tttSearch =
struct

open HolKernel Abbrev boolLib aiLib
  smlTimeout smlLexer smlExecute
  mlFeature mlThmData mlTacticData mlNearestNeighbor mlTreeNeuralNetwork
  psMinimize
  tttSetup tttToken tttLearn

val ERR = mk_HOL_ERR "tttSearch"
val predtac_time = ref 0.0
val reward_time = ref 0.0
val reorder_time = ref 0.0
val dict_time = ref 0.0

(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

datatype sstatus = StacProved | StacSaturated | StacUndecided | StacFresh
datatype gstatus = GoalProved | GoalSaturated | GoalUndecided
datatype nstatus = NodeProved | NodeSaturated | NodeUndecided
datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
datatype proofstatus = Proof of string | ProofSaturated | ProofTimeout

fun string_of_sstatus x = case x of
    StacProved => "SearchProved"
  | StacSaturated => "SearchSaturated"
  | StacUndecided => "SearchTimeOut"
  | StacFresh => "StacFresh"

fun string_of_searchstatus x = case x of
    SearchProved => "SearchProved"
  | SearchSaturated => "SearchSaturated"
  | SearchTimeout => "SearchTimeOut"

fun is_stacwin x = (x = StacProved)
fun is_staclose x = (x = StacSaturated)
fun is_goalwin x = (x = GoalProved)
fun is_goallose x = (x = GoalSaturated)

fun backstatus_arg sstatusl =
  if exists is_stacwin sstatusl then StacProved
  else if all is_staclose sstatusl then StacSaturated
  else StacUndecided

fun backstatus_stacv stacv =
  let val v = Vector.map (fn x => #sstatus (dfind [] x)) stacv in
    if Vector.exists is_stacwin v then GoalProved
    else if Vector.all is_staclose v then GoalSaturated
    else GoalUndecided
  end

fun backstatus_goalv goalv =
  let val v = Vector.map #gstatus goalv in
    if Vector.all is_goalwin v then NodeProved
    else if Vector.exists is_goallose v then NodeSaturated
    else NodeUndecided
  end

fun backreward_goalv (gn,reward) goalv =
  let fun f (i,r) = if gn = i then reward else #gsum r / #gvis r in
    Vector.foldl (op *) 1.0 (Vector.mapi f goalv)
  end

fun backreward_allgoalv goalv =
  let fun f r = #gsum r / #gvis r in
    Vector.foldl (op *) 1.0 (Vector.map f goalv)
  end

fun backstatus_node node = case #nstatus node of
    NodeUndecided => StacUndecided
  | NodeProved => StacProved
  | NodeSaturated => StacSaturated

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

type id = (int * int * int list) list (* reverse of natural order *)
val id_compare = list_compare
  (triple_compare Int.compare Int.compare (list_compare Int.compare))
fun string_of_id id =
  let
    fun f (gn,sn,anl) = "g" ^ its gn ^ "t" ^ its sn ^ "a" ^
      (String.concatWith "|" (rev (map its anl)))
    val sl = map f (rev id)
  in
    String.concatWith " " sl
  end

type stac_record =
  {token : token, atyl : aty list,
   svis : real, ssum : real, sstatus : sstatus}

type argtree = (int list, stac_record) Redblackmap.dict
type goal_record =
  {goal : goal, gvis : real, gsum  : real, gstatus : gstatus,
   stacv : argtree vector,
   siblingd : (goal list, unit) Redblackmap.dict}

type node =
  {nvis : real, nsum : real, nstatus : nstatus,
   goalv : goal_record vector,
   parentd : (goal, unit) Redblackmap.dict}
type tree = (id,node) Redblackmap.dict

type searchobj =
  {predtac : goal -> (string * aty list) list,
   predarg : string -> aty -> goal -> token list,
   parsetoken : parsetoken,
   vnno: tnn option, pnno: tnn option}

(* -------------------------------------------------------------------------
   First part: Node selection
   ------------------------------------------------------------------------- *)

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

fun before_stacfresh accessf acc i =
  if not (can accessf i) then rev acc else
  let
    val stacrec = accessf i
    val sstatus = #sstatus stacrec
  in
    case sstatus of
      StacFresh => rev ((i,stacrec) :: acc)
    | StacUndecided => before_stacfresh accessf ((i,stacrec) :: acc) (i+1)
    | _ => before_stacfresh accessf acc (i+1)
  end

fun select_stacrecl stacrecl pvis =
  let
    fun add_puct ((sn,{ssum,svis,...}),polv) =
      (sn, puct pvis ((ssum,svis),polv))
    val l0 = expo_polv (!ttt_policy_coeff) stacrecl
    val _ = if null l0 then raise ERR "select_stacrecl" "unexpected" else ()
    val l1 = map add_puct l0
    val l2 = dict_sort compare_rmax l1
  in
    fst (hd l2)
  end

fun select_accessf accessf pvis =
  let val stacrecl = before_stacfresh accessf [] 0 in
    select_stacrecl stacrecl pvis
  end

(* -------------------------------------------------------------------------
   Select leaf in argument tree
   ------------------------------------------------------------------------- *)

fun access_child argtree anl i = dfind (i :: anl) argtree

fun select_arg argtree anl =
  let
    val pnode = dfind anl argtree
    val pvis = #svis pnode
  in
    if #sstatus pnode = StacFresh then NONE else
    SOME (select_accessf (access_child argtree anl) pvis)
  end
  handle HOL_ERR _ =>
    raise ERR "select_arg" (String.concatWith "|" (map its (rev anl)))

fun select_argl argtree anl =
  if null (#atyl (dfind anl argtree)) then anl else
  case select_arg argtree anl of
    NONE => anl
  | SOME an => select_argl argtree (an :: anl)

(* -------------------------------------------------------------------------
   Select leaf in proof tree
   ------------------------------------------------------------------------- *)

fun string_of_goalv gv =
  let val gl = vector_to_list (Vector.map #goal gv) in
    String.concatWith "," (map string_of_goal gl)
  end

fun select_goalundec goalv =
  let
    val goall = number_fst 0 (vector_to_list goalv)
    fun test (_,x) = (#gstatus x = GoalUndecided)
    val gl = filter test goall
    fun f (_,x) = #gvis x (* uniform *)
  in
    if null gl then
      raise ERR "select_goalundec"
        ("no undecided goals : " ^ string_of_goalv goalv)
    else fst (hd (dict_sort compare_rmin (map_assoc f gl)))
  end

fun select_node tree pid =
  let
    val {goalv,...} = dfind pid tree
    val (gn,{goal,gvis,stacv,...}) = select_goalundec goalv
    fun access_toprec i = dfind [] (Vector.sub (stacv,i))
    val sn = select_accessf access_toprec gvis handle HOL_ERR _ =>
      raise ERR "select_node" (string_of_id pid ^ " " ^ its gn)
    val argtree = Vector.sub (stacv,sn)
    val stac = dest_stac (#token (dfind [] argtree))
    val anl = select_argl argtree []
  in
    if #sstatus (dfind anl argtree) = StacFresh
    then ((pid,(gn,sn,anl)),(goal,stac,argtree))
    else select_node tree ((gn,sn,anl) :: pid)
  end

(* -------------------------------------------------------------------------
   Second part: Node expansion
   ------------------------------------------------------------------------- *)

(*  Policy re-ordering using policy network
fun reorder_stacl g pnn stacl =
  let
    fun f x = mask_unknown_policy pnn (nntm_of_gstactm (g,x))
    val l = map_assoc (infer_tnn_basic pnn o f o #stactm) stacl
  in
    map fst (dict_sort compare_rmax l)
  end

fun reorder_stacv g pnn stacv =
  let
    val stacl = vector_to_list stacv
    val (stacl1,stacl2) = part_n 20 stacl
  in
    Vector.fromList (reorder_stacl g pnn stacl1 @ stacl2)
  end
*)

(* -------------------------------------------------------------------------
   Expand argument tree and select first prediction
   ------------------------------------------------------------------------- *)

fun arg_create atyl arg =
  {token = arg, atyl = atyl, svis = 0.0, ssum = 0.0, sstatus = StacFresh}

fun expand_argtree searchobj (goal,stac) (argtree,anl) =
  let val atyl = #atyl (dfind anl argtree) in
    if null atyl then (argtree,anl,StacFresh) else
    let val argl1 = #predarg searchobj stac (hd atyl) goal in
      if null argl1 then (argtree,anl,StacSaturated) else
      let
        val argl2 = map (arg_create (tl atyl)) argl1
        fun f i x = (i :: anl, x)
        val newargtree = daddl (mapi f argl2) argtree
      in
        expand_argtree searchobj (goal,stac) (newargtree, 0 :: anl)
      end
    end
  end

(* -------------------------------------------------------------------------
   Application of a tactic
   ------------------------------------------------------------------------- *)

fun status_of_stac parentd goalrec glo = case glo of
    NONE => StacSaturated
  | SOME [] => StacProved
  | SOME gl =>
   (if op_mem goal_eq (#goal goalrec) gl orelse
       exists (fn x => dmem x parentd) gl orelse
       dmem gl (#siblingd goalrec) orelse
       exists (fn x => term_eq (snd x) F) gl
    then StacSaturated
    else StacUndecided)

fun is_metis_stac token = case token of
    Stac s => s = "metisTools.METIS_TAC " ^ thmlarg_placeholder
  | _ => false

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

val stac_cache = ref (
  dempty (cpl_compare goal_compare (list_compare compare_token)))
fun clean_stac_cache () = stac_cache :=
  dempty (cpl_compare goal_compare (list_compare compare_token))

fun apply_tac parsetoken tokenl goal =
  dfind (goal,tokenl) (!stac_cache) handle NotFound =>
  let
    val tim = if is_metis_stac (hd tokenl)
              then !ttt_metis_time
              else !ttt_tactic_time
    fun f g =
      let val tac = build_tac parsetoken tokenl in
        SOME (fst (TC_OFF tac g))
      end
    val glo = timeout tim f goal
      handle Interrupt => raise Interrupt | _ => NONE
  in
    stac_cache := dadd (goal,tokenl) glo (!stac_cache); glo
  end

fun reward_of vnno (sstatus,glo) = case sstatus of
    StacSaturated => 0.0
  | StacProved => 1.0
  | StacUndecided =>
    (
    (* to be changed to the product of the value *)
    if isSome vnno then
      let
        val vnn = valOf vnno
        val nntm = mask_unknown_value vnn (nntm_of_gl (valOf glo))
      in
        infer_tnn_basic vnn nntm
      end
    else 1.0 (* now ignored *)
    )
  | StacFresh => raise ERR "reward_of" "unexpected"

fun collect_tokenl acc (argtree,anl) =
  let val token = #token (dfind anl argtree) in
    if null anl
    then token :: acc
    else collect_tokenl (token :: acc) (argtree, tl anl)
  end

fun apply_stac (tree,searchobj) argtree (pid,(gn,sn,anl)) =
  let
    val node = dfind pid tree
    val parentd = #parentd node
    val goalrec = Vector.sub (#goalv node, gn)
    val siblingd = #siblingd goalrec
    val tokenl = collect_tokenl [] (argtree,anl)
    val _ = debugf "stac: " (dest_stac o hd) tokenl
    val glo = apply_tac (#parsetoken searchobj) tokenl (#goal goalrec)
    val sstatus = status_of_stac parentd goalrec glo
    val glo' = if sstatus = StacUndecided then glo else NONE
    val reward = total_time reward_time
      (reward_of (#vnno searchobj)) (sstatus,glo')
  in
    (glo',sstatus,reward)
  end

(* -------------------------------------------------------------------------
   Create a new node (if tactic application was successful)
   ------------------------------------------------------------------------- *)

fun argtree_create (stac,atyl) =
  let val stacrec = {token = Stac stac, atyl = atyl,
    svis = 0.0, ssum = 0.0, sstatus = StacFresh}
  in
    dnew (list_compare Int.compare) [([],stacrec)]
  end

fun goal_create searchobj goal =
  let val stacv = Vector.fromList
    (map argtree_create (#predtac searchobj goal))
    (* total_time reorder_time (reorder_stacv goal (valOf pnno)) stacv *)
  in
    {
    goal = goal,
    gvis = 1.0, gsum = 0.9 (* or tnn *), gstatus = backstatus_stacv stacv ,
    stacv = stacv,
    siblingd = dempty (list_compare goal_compare)
    }
  end

fun string_of_goall gl = String.concatWith "," (map string_of_goal gl)
fun debug_node gl = (debugf "goals: " string_of_goall gl; debug ("\n"))

fun node_create (tree,searchobj) gl (pid,(gn,sn,anl)) =
  let
    val node = dfind pid tree
    val pgoal = #goal (Vector.sub (#goalv node,gn))
    val cgoalv = Vector.fromList (map (goal_create searchobj) gl)
    val cid = (gn,sn,anl) :: pid
    val node =
      {
      nvis = 1.0, nsum = backreward_allgoalv cgoalv, 
      nstatus = backstatus_goalv cgoalv,
      goalv = cgoalv,
      parentd = dadd pgoal () (#parentd node)
      }
    val newtree = dadd cid node tree
  in
    debug_node gl;
    newtree
  end

(* -------------------------------------------------------------------------
   Third part: Node backup
   ------------------------------------------------------------------------- *)

fun children_statusl argtree anl acc i =
  if dmem (i :: anl) argtree
  then children_statusl argtree anl
    (#sstatus (dfind (i :: anl) argtree) :: acc) (i+1)
  else rev acc

fun backup_argtree (argtree,anl) (sstatus,reward) =
  let
    val {token,atyl,svis,ssum,...} = dfind anl argtree
    val newargnode =
      {token = token, atyl = atyl,
       svis = svis + 1.0, ssum = ssum + reward, sstatus = sstatus}
    val newargtree = dadd anl newargnode argtree
  in
    if null anl then newargtree else
    let
      val cstatusl = children_statusl newargtree (tl anl) [] 0
      val pstatus = backstatus_arg cstatusl
    in
      backup_argtree (newargtree, tl anl) (pstatus,reward)
    end
  end

fun node_update tree (argtreeo,glo) (sstatus,reward) (id,(gn,sn,anl)) =
  let
    val {nvis,nsum,goalv,parentd,...} = dfind id tree
    val {goal,gvis,gsum,stacv,siblingd,...} = Vector.sub (goalv,gn)
    val argtree = Vector.sub (stacv,sn)
    (* update argtree *)
    val argtree1 = if isSome argtreeo then (valOf argtreeo) else argtree
    val argtree2 = backup_argtree (argtree1,anl) (sstatus,reward)
    (* update stacv *)
    val newstacv = Vector.update (stacv,sn,argtree2)
    (* update goalv *)
    val newgoalrec =
      {
      goal = goal,
      gvis = gvis + 1.0, gsum = gsum + reward,
      gstatus = backstatus_stacv newstacv,
      stacv = newstacv,
      siblingd = if isSome glo then dadd (valOf glo) () siblingd else siblingd
      }
    val newgoalv = Vector.update (goalv,gn,newgoalrec)
    (* update node *)
    val newnode =
      {
      nvis = nvis + 1.0, nsum = nsum + backreward_goalv (gn,reward) newgoalv,
      nstatus = backstatus_goalv newgoalv,
      goalv = newgoalv,
      parentd = parentd
      }
  in
    (dadd id newnode tree, backstatus_node newnode)
  end

fun node_backup tree (argtreeo,glo) (sstatus,reward) (id,(gn,sn,anl)) =
  let val (newtree,newsstatus) =
    node_update tree (argtreeo,glo) (sstatus,reward) (id,(gn,sn,anl))
  in
    if null id
    then newtree
    else node_backup newtree (NONE,NONE) (newsstatus,reward) (tl id, hd id)
  end

(* -------------------------------------------------------------------------
   Search loop: selection, expansion and backup
   ------------------------------------------------------------------------- *)

fun search_loop startsearchobj starttree =
  let
    val timer = Timer.startRealTimer ()
    fun loop searchobj tree =
      if Timer.checkRealTimer timer > Time.fromReal (!ttt_search_time)
        then (SearchTimeout,tree)
      else if #nstatus (dfind [] tree) = NodeSaturated
        then (SearchSaturated,tree)
      else if #nstatus (dfind [] tree) = NodeProved
        then (SearchProved,tree)
      else
        let
          val _ = debug "selection"
          val ((pid,(gn,sn,anl)),(goal,stac,argtree)) =
            select_node tree []
          val _ = debug "argument expansion"
          val (newargtree,newanl,argstatus) =
            expand_argtree searchobj (goal,stac) (argtree,anl)
          val pidx = (pid,(gn,sn,newanl))
          val _ = debugf "application: " string_of_id ((gn,sn,newanl) :: pid)
          val (glo,sstatus,reward) =
            if argstatus = StacFresh
            then apply_stac (tree,searchobj) newargtree pidx
            else (debug "no argument predicted";
                  (NONE, StacSaturated, reward_of NONE (StacSaturated,NONE)))
          val _ = debug "node expansion"
          val exptree =
            if sstatus = StacUndecided
            then node_create (tree,searchobj) (valOf glo) pidx
            else tree
          val _ = debug "backup"
          val backuptree =
            node_backup exptree (SOME newargtree, glo) (sstatus,reward) pidx
        in
          loop searchobj backuptree
        end
  in
    loop startsearchobj starttree
  end

(* -------------------------------------------------------------------------
   Proof reconstruction
   ------------------------------------------------------------------------- *)

fun proofpath_argtree argtree anl =
  let
    val node = dfind anl argtree
    val atyl = #atyl node
    fun f i =
      if not (dmem (i :: anl) argtree)
        then raise ERR "proofpath_argtree" "unexpected"
      else if is_stacwin (#sstatus (dfind (i :: anl) argtree))
        then i
      else f (i + 1)
  in
    if null atyl then anl else proofpath_argtree argtree (f 0 :: anl)
  end

fun extract_proofl tree id =
  let
    val node = dfind id tree
    fun f (gn,goalrec) =
      let
        val stacv = #stacv goalrec
        fun test (_,x) = is_stacwin (#sstatus (dfind [] x))
        val (sn,argtree) = valOf (Vector.findi test stacv)
           handle Option => raise ERR "extract_proof" "unexpected"
        val anl = proofpath_argtree argtree []
        val tokenl = collect_tokenl [] (argtree,anl)
        val istac = build_stac tokenl
        val ptac = Tactic (istac, #goal goalrec)
        val _ = debugf "goal: " string_of_goal (#goal goalrec)
        val _ = debug ("stac: " ^ istac);
        val cid = (gn,sn,anl) :: id
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

(* -------------------------------------------------------------------------
   Proof search top-level function
   ------------------------------------------------------------------------- *)

fun starttree_of searchobj goal =
  let
    val goalv = Vector.fromList [goal_create searchobj goal]
    val root =
     {nvis = 1.0, nsum = 0.0, nstatus = backstatus_goalv goalv,
      goalv = goalv,
      parentd = dempty goal_compare}
  in
    debugf "root: " string_of_goal goal;
    dadd [] root (dempty id_compare)
  end

fun time_searchobj predtac_time {predtac,predarg,parsetoken,vnno,pnno} =
  {
  predtac = total_time predtac_time predtac,
  predarg = predarg, parsetoken = parsetoken, vnno = vnno, pnno = pnno
  }

fun search searchobj g =
  let
    val _ = clean_stac_cache ()
    val _ = (predtac_time := 0.0; reward_time := 0.0; reorder_time := 0.0)
    val starttree = starttree_of searchobj g
    val ((searchstatus,tree),t) = add_time
      (search_loop (time_searchobj predtac_time searchobj)) starttree
    val _ = clean_stac_cache ()
    val _ = print_endline ("search time: " ^ rts_round 6 t)
  in
    (reconstruct_proofstatus (searchstatus,tree) g, tree)
  end

end (* struct *)
