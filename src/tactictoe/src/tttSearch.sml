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
  tttSetup tttToken tttLearn tttTrain

val ERR = mk_HOL_ERR "tttSearch"

(* -------------------------------------------------------------------------
   Timers
   ------------------------------------------------------------------------- *)

val select_time = ref 0.0
val exparg_time = ref 0.0
val apply_time = ref 0.0
val create_time = ref 0.0
val backup_time = ref 0.0
val recons_time = ref 0.0
val metis_time = ref 0.0
val other_time = ref 0.0

fun reset_timer x = x := 0.0
fun clean_timers () = app reset_timer 
  [select_time, exparg_time, apply_time, create_time, 
   backup_time, recons_time, metis_time, other_time]

fun print_timers () = 
  app print_endline 
  ["select: " ^ rts_round 6 (!select_time),
   "exparg: " ^ rts_round 6 (!exparg_time),
   "apply: " ^ rts_round 6 (!apply_time),
   "create: " ^ rts_round 6 (!create_time),
   "backup: " ^ rts_round 6 (!backup_time),
   "recons: " ^ rts_round 6 (!recons_time),
   "metis: " ^ rts_round 6 (!metis_time),
   "other: " ^ rts_round 6 (!other_time)]

(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

datatype sstatus = StacProved | StacSaturated | StacUndecided | StacFresh
datatype gstatus = GoalProved | GoalSaturated | GoalUndecided
datatype nstatus = NodeProved | NodeSaturated | NodeUndecided
datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
datatype proofstatus = Proof of string | ProofSaturated | ProofTimeout

fun string_of_sstatus x = case x of
    StacProved => "StacProved"
  | StacSaturated => "StacSaturated"
  | StacUndecided => "StacUndecided"
  | StacFresh => "StacFresh"

fun string_of_searchstatus x = case x of
    SearchProved => "SearchProved"
  | SearchSaturated => "SearchSaturated"
  | SearchTimeout => "SearchTimeout"

fun is_stacwin x = (x = StacProved)
fun is_staclose x = (x = StacSaturated)
fun is_goalwin x = (x = GoalProved)
fun is_goallose x = (x = GoalSaturated)

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
   svis : real, ssum : real, spol : real,
   sstatus : sstatus}

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
   vnno: tnn option, pnno: tnn option, anno: tnn option}

(* -------------------------------------------------------------------------
   Backing up utilities
   ------------------------------------------------------------------------- *)

fun backstatus_arg sstatusl =
  if exists is_stacwin sstatusl then StacProved
  else if all is_staclose sstatusl then StacSaturated
  else StacUndecided

fun backstatus_stacv (stacv : argtree vector) =
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
  let fun f (i,r) = 
    if #gstatus r = GoalProved then 1.0
    else if #gstatus r = GoalSaturated then 0.0
    else if gn = i then reward 
    else #gsum r / #gvis r 
  in
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
   Re-evaluation of nearest neighbor choices
   by tree neural networks
   ------------------------------------------------------------------------- *)

(* value *)

(* called only when tactic applications either closes the goal or fails *)
fun reward_of_sstatus sstatus = case sstatus of
    StacSaturated => (sstatus,0.0)
  | StacProved => (sstatus,1.0)
  | _ => raise ERR "reward_of_sstatus" "unexpected"

fun eval_goal vnn g =
  let
    val tm1 = nntm_of_stateval g
    val tm2 = mask_unknown_val vnn tm1
  in
    infer_tnn_basic vnn tm2
  end

val default_reward = 1.0

fun reward_of_goal vnno g =
  if not (isSome vnno) then default_reward else eval_goal (valOf vnno) g

(* policy *)
fun eval_stac pnn g stac =
  let
    val tm1 = nntm_of_statepol (g,stac)
    val tm2 = mask_unknown_pol pnn tm1
  in
    infer_tnn_basic pnn tm2
  end

fun reorder_stacl g pnn stacl =
  let
    val (stacl1,stacl2) = part_n 16 stacl
    fun f x = eval_stac pnn g (fst x)
    val stacl1e = map_assoc f stacl1
    val stacl1o = map fst (dict_sort compare_rmax stacl1e)
  in
    stacl1o @ stacl2
  end

fun reorder_pol g pnno stacl =
  if not (isSome pnno) then stacl else reorder_stacl g (valOf pnno) stacl

(* argument *)
fun eval_argl ann g stac argl =
  let fun f x = mask_unknown_arg ann (nntm_of_statearg ((g,stac),x)) in
    map (singleton_of_list o snd) (infer_tnn ann (map f argl))
  end

fun reorder_arg anno g stac argl =
  if not (isSome anno) then argl else
  let
    val rl = eval_argl (valOf anno) g stac argl
    val argle = combine (argl,rl)
  in
    map fst (dict_sort compare_rmax argle)
  end

(* -------------------------------------------------------------------------
   First part: Node selection
   ------------------------------------------------------------------------- *)

fun puct gvis ((sum,vis),polv) =
  let
    val exploitation = sum / vis
    val exploration  = (polv * Math.sqrt gvis) / vis
  in
    exploitation + (!ttt_explo_coeff) * exploration
  end

fun expo_polv_aux ci (c:real) l = case l of
    [] => []
  | a :: m => (a,c) :: expo_polv_aux ci (ci * c) m
fun expo_polv ci l = expo_polv_aux ci 1.0 l

fun norm_polv l = 
  let val sum = sum_real (map snd l) in
    if sum > epsilon 
    then map_snd (fn x => x / sum) l
    else l
  end

fun before_stacfresh_aux accessf acc i =
  if not (can accessf i) then rev acc else
  let
    val stacrec = accessf i
    val sstatus = #sstatus stacrec
  in
    case sstatus of
      StacFresh => rev ((i,stacrec) :: acc)
    | StacUndecided => before_stacfresh_aux accessf ((i,stacrec) :: acc) (i+1)
    | _ => before_stacfresh_aux accessf acc (i+1)
  end

fun before_stacfresh accessf = before_stacfresh_aux accessf [] 0
  
fun before_stacfresh_all_aux accessf acc i =
  if not (can accessf i) then rev acc else
  let
    val stacrec = accessf i
    val sstatus = #sstatus stacrec
  in
    case sstatus of
      StacFresh => rev ((i,stacrec) :: acc)
    | _ => before_stacfresh_all_aux accessf ((i,stacrec) :: acc) (i+1)
  end

fun before_stacfresh_all accessf = before_stacfresh_all_aux accessf [] 0

fun select_stacrecl stacrecl pvis =
  let
    val l0 = norm_polv (expo_polv (!ttt_policy_coeff) stacrecl)
    val _ = if null l0 then raise ERR "select_stacrecl" "unexpected" else ()
    fun add_puct ((sn,{ssum,svis,...}),polv) =
      (sn, puct pvis ((ssum,svis),polv))
    val l1 = map add_puct l0
    val l2 = dict_sort compare_rmax l1
  in
    fst (hd l2)
  end

fun select_accessf accessf pvis =
  select_stacrecl (before_stacfresh accessf) pvis

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

(* -------------------------------------------------------------------------
   Expand argument tree and select first prediction
   ------------------------------------------------------------------------- *)

fun arg_create atyl arg =
  {token = arg, atyl = atyl, svis = 1.0, ssum = 0.0, spol = 0.0, 
   sstatus = StacFresh}

fun expand_argtree searchobj (goal,stac) (argtree,anl) =
  let val atyl = #atyl (dfind anl argtree) in
    if null atyl then (argtree,anl,StacFresh) else
    let val argl1 = #predarg searchobj stac (hd atyl) goal in
      if null argl1 then (argtree,anl,StacSaturated) else
      let
        val argl2p = if length argl1 <= 1 then argl1
          else reorder_arg (#anno searchobj) goal stac argl1
        val argl2 = map (arg_create (tl atyl)) argl2p
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

val nocut_flag = ref false

fun status_of_stac parentd goalrec glo = case glo of
    NONE => StacSaturated
  | SOME [] => StacProved
  | SOME gl =>
   (if op_mem goal_eq (#goal goalrec) gl orelse
       exists (fn x => dmem x parentd) gl orelse
       dmem gl (#siblingd goalrec) orelse
       exists (fn x => term_eq (snd x) F) gl orelse
       (!nocut_flag andalso 
        exists (fn x => term_eq (snd x) (snd (#goal goalrec))) gl)
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
    val tim = if is_metis_stac (hd tokenl) andalso !ttt_metis_flag
              then !ttt_metis_time
              else !ttt_tactic_time
    fun f g =
      let val tac = build_tac parsetoken tokenl in
        SOME (fst (TC_OFF tac g))
      end
    val timer = 
      if is_metis_stac (hd tokenl) 
      then total_time metis_time
      else total_time other_time
    val glo = timer (timeout tim f) goal
      handle Interrupt => raise Interrupt | _ => NONE
  in
    stac_cache := dadd (goal,tokenl) glo (!stac_cache); glo
  end

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
  in
    (glo',sstatus)
  end

(* -------------------------------------------------------------------------
   Create a new node (if tactic application was successful)
   ------------------------------------------------------------------------- *)

fun argtree_create (stac,atyl) =
  let val stacrec = {token = Stac stac, atyl = atyl,
    svis = 1.0, ssum = 0.0, spol = 0.0, sstatus = StacFresh}
  in
    dnew (list_compare Int.compare) [([],stacrec)]
  end

fun goal_create searchobj goal =
  let
    val stacl1 = #predtac searchobj goal
    val stacl2 = reorder_pol goal (#pnno searchobj) stacl1
    val stacv = Vector.fromList (map argtree_create stacl2)
  in
    {
    goal = goal,
    gvis = 1.0, gsum = reward_of_goal (#vnno searchobj) goal,
    gstatus = backstatus_stacv stacv,
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
    val status = backstatus_goalv cgoalv
    val reward = backreward_allgoalv cgoalv
    val node =
      {
      nvis = 1.0, nsum = reward, nstatus = status,
      goalv = cgoalv,
      parentd = dadd pgoal () (#parentd node)
      }
    val newtree = dadd cid node tree
  in
    debug_node gl;
    (newtree,reward)
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
    val {token,atyl,svis,ssum,spol,...} = dfind anl argtree
    val newargnode =
      {token = token, atyl = atyl,
       svis = svis + 1.0, ssum = ssum + reward, 
       spol = if reward > spol then reward else spol,
       sstatus = sstatus}
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
    val newreward = backreward_goalv (gn,reward) newgoalv
    val newnode =
      {
      nvis = nvis + 1.0, nsum = nsum + newreward,
      nstatus = backstatus_goalv newgoalv,
      goalv = newgoalv,
      parentd = parentd
      }
  in
    (dadd id newnode tree, backstatus_node newnode, newreward)
  end

fun node_backup tree (argtreeo,glo) (sstatus,reward) (id,(gn,sn,anl)) =
  let val (newtree,newsstatus,newreward) =
    node_update tree (argtreeo,glo) (sstatus,reward) (id,(gn,sn,anl))
  in
    if null id then newtree else 
    node_backup newtree (NONE,NONE) (newsstatus,newreward) (tl id, hd id)
  end

(* -------------------------------------------------------------------------
   Search loop: selection, expansion and backup
   ------------------------------------------------------------------------- *)

val snap_flag = ref false
val snap_tree = ref NONE
val snap_n = ref 10

fun search_loop startsearchobj nlimito starttree =
  let
    val nlimitb = isSome nlimito
    val timer = Timer.startRealTimer ()
    fun loop n searchobj tree =
      if isSome nlimito andalso n >= valOf nlimito
        then (print_endline ("loops: " ^ its n); (SearchTimeout,tree))
      else if not (isSome nlimito) andalso
        Timer.checkRealTimer timer > Time.fromReal (!ttt_search_time)
        then (print_endline ("loops: " ^ its n); (SearchTimeout,tree))
      else if #nstatus (dfind [] tree) = NodeSaturated
        then (print_endline ("loops: " ^ its n); (SearchSaturated,tree))
      else if #nstatus (dfind [] tree) = NodeProved
        then (print_endline ("loops: " ^ its n); (SearchProved,tree))
      else
        let
          val _ = if !snap_flag andalso dlength tree = !snap_n
                  then snap_tree := SOME tree
                  else ()
          val _ = debug "selection"
          val ((pid,(gn,sn,anl)),(goal,stac,argtree)) = total_time select_time 
              (select_node tree) []
          val _ = debug "argument expansion"
          val (newargtree,newanl,argstatus) = total_time exparg_time
            (expand_argtree searchobj (goal,stac)) (argtree,anl)
          val pidx = (pid,(gn,sn,newanl))
          val _ = debugf "application: " string_of_id ((gn,sn,newanl) :: pid)
          val (glo,sstatus) =
            if argstatus = StacFresh
            then total_time apply_time 
              (apply_stac (tree,searchobj) newargtree) pidx
            else (debug "no argument predicted"; (NONE, StacSaturated))
          val _ = debug "node expansion"
          val (exptree,(status,reward)) =
            if sstatus = StacUndecided
            then 
               let val(temptree,tempreward) = total_time create_time
                 (node_create (tree,searchobj) (valOf glo)) pidx
               in
                 (temptree,(sstatus,tempreward))
               end
            else (tree, reward_of_sstatus sstatus)
          val _ = debug "backup"
          val backuptree = total_time backup_time
            (node_backup exptree (SOME newargtree, glo) (status,reward)) 
            pidx
        in
          loop (n+1) searchobj backuptree
        end
  in
    loop 0 startsearchobj starttree
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
   Initializing the search tree
   ------------------------------------------------------------------------- *)

fun starttree_of_goal searchobj goal =
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

fun goal_create_stacv searchobj (goal,stacv) =
  {
  goal = goal,
  gvis = 1.0, gsum = 0.0,
  gstatus = backstatus_stacv stacv ,
  stacv = stacv,
  siblingd = dempty (list_compare goal_compare)
  }

fun argtree_add_tokenl (tree,id) (tokenl,atyl) =
  if null tokenl then tree else
  let val node =
    {token = hd tokenl, atyl = atyl, 
     svis = 1.0, ssum = 0.0, spol = 0.0, sstatus = StacFresh}
  in
    argtree_add_tokenl (dadd (0 :: id) node tree, 0 :: id)
    (tl tokenl, tl atyl)
  end

fun starttree_of_gstacarg searchobj (goal,stac,tokenl) =
  let
    val atyl = extract_atyl stac
    val argtree1 = argtree_create (stac,atyl)
    val argtree2 = argtree_add_tokenl (argtree1,[]) (tokenl,atyl)
    val stacv = Vector.fromList [argtree2]
    val goalv = Vector.fromList [goal_create_stacv searchobj (goal,stacv)]
    val root =
      {nvis = 1.0, nsum = 0.0,
       nstatus = backstatus_goalv goalv,
       goalv = goalv,
       parentd = dempty goal_compare}
  in
    debugf "root: " string_of_goal goal;
    dadd [] root (dempty id_compare)
  end

(* -------------------------------------------------------------------------
   Proof search top-level function
   ------------------------------------------------------------------------- *)

fun search searchobj g =
  let
    val _ = clean_stac_cache ()
    val _ = clean_timers ()
    val starttree = starttree_of_goal searchobj g
    val ((searchstatus,tree),t) = add_time
      (search_loop searchobj NONE) starttree
    val _ = clean_stac_cache ()
    val _ = print_endline ("nodes: " ^ its (dlength tree));
    val _ = print_endline ("search: " ^ rts_round 6 t)
    val r = total_time recons_time
      (reconstruct_proofstatus (searchstatus,tree)) g
    val _ = print_timers ()
  in
    (r, tree)
  end


end (* struct *)
