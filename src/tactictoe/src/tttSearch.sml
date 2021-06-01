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
   Global parameters
   ------------------------------------------------------------------------- *)

val default_reward = 0.0
val conttop_flag = ref false
val contmid_flag = ref false
val nocut_flag = ref false

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
   "backup: " ^ rts_round 6 (!backup_time),
   "recons: " ^ rts_round 6 (!recons_time),
   "metis: " ^ rts_round 6 (!metis_time),
   "other: " ^ rts_round 6 (!other_time)]

(* -------------------------------------------------------------------------
   Status
   ------------------------------------------------------------------------- *)

datatype status = Proved | Saturated | Undecided
datatype searchstatus = 
  SearchProved | SearchSaturated | SearchTimeout
datatype proofstatus = 
  Proof of string | ProofSaturated | ProofTimeout

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

datatype gtoken = 
  Token of token | Goal of (goal * (goal list, unit) Redblackmap.dict)

type searchrecord =
  {nvis : real, nsum : real, nstatus : status,
   parentd : (goal, unit) Redblackmap.dict}

type stacrecord =
  {gtoken : gtoken, atyl : aty list,
   svis : real, ssum : real, spol : real, sstatus : status}

datatype searchtree = SearchNode of searchrecord * stactree vector

and stactree = 
   StacLeaf of stacrecord * searchtree option
 | StacNode of stacrecord * (stactree vector * stactree list) option

fun dest_searchtree tree = case tree of SearchNode x => x

fun get_stacrecord stactree = case stactree of
   StacLeaf (r,_) => r
 | StacNode (r,_) => r

(* -------------------------------------------------------------------------
   Search parameters
   ------------------------------------------------------------------------- *)

type searchobj =
  {predtac : goal -> (string * aty list) list,
   predarg : string -> aty -> goal -> token list,
   parsetoken : parsetoken,
   vnno: tnn option, pnno: tnn option, anno: tnn option}

(* -------------------------------------------------------------------------
   Backing up utilities
   ------------------------------------------------------------------------- *)

fun is_proved x = (x = Proved)
fun is_saturated x = (x = Saturated)



(* -------------------------------------------------------------------------
   Re-evaluation of nearest neighbor choices
   by tree neural networks
   ------------------------------------------------------------------------- *)

(* value *)

(* called only when tactic applications either closes the goal or fails *)


fun eval_goal vnn g =
  let
    val tm1 = nntm_of_stateval g
    val tm2 = mask_unknown_val vnn tm1
  in
    infer_tnn_basic vnn tm2
  end

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

(* reorder_pol goal (#pnno searchobj) stacl1 *)

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

(*  reorder_arg (#anno searchobj) goal stac argl1 *)

(* -------------------------------------------------------------------------
   Node expansion
   ------------------------------------------------------------------------- *)

fun status_of_stac parentd (goal,siblingd) glo = case glo of
    NONE => StacSaturated
  | SOME [] => StacProved
  | SOME gl =>
   (if op_mem goal_eq goal gl orelse
       exists (fn x => dmem x parentd) gl orelse
       dmem gl siblingd orelse
       exists (fn x => term_eq (snd x) F) gl orelse
       (!nocut_flag andalso 
        exists (fn x => term_eq (snd x) (snd goal)) gl)
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

fun apply_stac searchobj noderec gtokenl = case gtokenl of
    Goal (goal,siblingd) :: tokenl =>
  let
    val glo = apply_tac (#parsetoken searchobj) (map dest_token tokenl) goal
    val sstatus = status_of_stac (#parentd noderec) (goal,siblingd) glo
    val glo' = if sstatus = Undecided then glo else NONE
  in
    (glo',sstatus)
  end
  | _ => raise ERR "apply_stac" ""

(* -------------------------------------------------------------------------
   Node creation
   ------------------------------------------------------------------------- *)

fun create_predtac searchobj svo = case svo of 
    NONE => SOME (Vector.fromList [], #predtac searchobj goal)
  | SOME _ => svo 

fun create_predarg searchobj tokenl aty svo = case svo of 
    NONE => case rev tokenl of  
      Goal goal :: Token (Stac stac) :: m =>
        SOME (Vector.fromList [], #predarg searchobj stac aty goal)
      | _ => raise ERR "create_predarg" "match"
  | SOME _ => svo

fun create_stacnode x = 
   if is_token (#gtoken x) andalso null (#atyl x)
   then StacLeaf (x,NONE)
   else StacNode (x,NONE)





fun create_searchleaf searchobj gl =
  let
    val pgoal = #goal (Vector.sub (#goalv node,gn))
    val cgoalv = Vector.fromList (map (goal_create searchobj) gl)
    val cid = (gn,sn,anl) :: pid
    val status = backstatus_goalv cgoalv
    val reward = backreward_allgoalv cgoalv
    val node =

    val newtree = dadd cid node tree
  in
    debug_node gl; (newtree,reward)
  end

(* -------------------------------------------------------------------------
   Node backup and update
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
   Node selection
   ------------------------------------------------------------------------- *)

fun reward_of_status status = case status of
    Saturated => 0.0
  | Proved => 1.0
  | _ => raise ERR "reward_of_sstatus" "unexpected"

fun puct gvis {ssum,svis,spol,...} =
  ssum / svis + (!ttt_explo_coeff) * (spol * Math.sqrt gvis) / svis

fun select_goaltree gtreev =
  let
    val _ = if Vector.length gtreev = 0
      then raise ERR "select_goaltree" "" else ()
    fun score x = #svis (get_stacrecord x)
    val i = vector_mini score gtreev
  in
    (i, Vector.sub (gtreev, i))
  end

fun policy_coeff n =
  (1 - !ttt_policy_coeff) * Math.pow (!ttt_policy_coeff, Real.fromInt n)

datatype selectres = 
  Sel of int | SelNone | SelFresh of sc 

fun select_stactree pvis (sv,sl) =
  if Vector.length sv = 0 then 
    (if null sl then SelNone 
     else SelFresh (hd sl, policy_coeff (Vector.length sv))) 
  else
  let
    fun score x = puct pvis (get_stacrecord x)
    val (i,sc) = vector_max score sv
  in
    if null sl then Sel i else
    let  
      val freshpol = policy_coeff (Vector.length sv)
      val freshsc = !ttt_explo_coeff * (freshpol * Math.sqrt pvis)
    in
      if freshsc > sc then Sel (hd sl, freshpol) else Sel i
    end
  end

fun hderr x = hd x handle Empty => raise ERR "hderr" ""
fun tlerr x = tl x handle Empty => raise ERR "tlerr" ""

fun atyl_of searchobj pr token = case token of 
    Stac stac => dfind stac (#atyd searchobj)
  | _ => tlerr (#atyl pr)

fun create_stactree searchobj pr token spol = create_stacnode
  {gtoken = Token token, atyl = atyl_of searchobj pr token, 
   svis = 1.0, ssum = 0.0, spol = spol, sstatus = Undecided}

fun backreward_stactree reward = reward

fun backstatus_stactree sv =
  let val v = Vector.map (fn (r,_) => #sstatus r) sv in
    if Vector.exists is_proved v then Proved
    else if Vector.all is_saturated v then Saturated
    else Undecided
  end

fun backup_stactree stree si (su,reward) = case stree of
     StacNode ({gtoken,atyl,svis,ssum,spol,sstatus}, SOME (sv,sl)) => 
     let 
       val newsv = Vector.update (sv,si,su) 
       val newreward = backreward_stactree reward
       val newstatus = backstatus_stactree newsv
     in 
       (StacNode
         {gtoken = gtoken, atyl = atyl,
          svis = svis + 1.0, ssum = ssum + newreward, spol = spol,
          sstatus = newstatus},
        newreward)
     end
   | _ => raise ERR "backup_stactree" ""
   

fun select_stacleaf searchobj backupl gtokenl stree = case stree of
    StacNode (r,svo) => 
    let 
      val newsvo = case #gtoken r of 
          Goal _ => create_predtac searchobj svo
        | Token _ => create_predarg searchobj (hderr (#atyl r)) svo
      val newstree = StacNode (r,newsvo)
    in
      case select_stactree (#svis r) (valOf newsvo) of
        SelNone => (stree, rev (#gtoken r :: gtokenl), backupl)
      | Sel si => 
        let 
          val cstree = Vector.sub (fst (valOf newsvo), si) 
          val newgtokenl = #gtoken r :: tokenl
          val backupf = backup_stactree newstree si
          val newbackupl = backupf :: backupl
        in
          select_stacfleaf searchobj newbackupl newgtokenl cstree
        end
      | SelFresh (token,spol) => 
        let 
          val cstree = create_stactree searchobj r token spol 
          val (sv,sl) = valOf newsvo
          val newnewsvo = SOME (Vector.concat [sv,cstree], tl sl)
          val newnewstree = StacNode (r,newnewsvo)
          val newgtokenl = #gtoken r :: tokenl
          val backupf = backup_stactree newnewstree (Vector.length sv)
          val newbackupl = backupf :: backupl
        in
          select_stacfleaf searchobj newbackupl newgtokenl cstree
        end
  | StacLeaf (r,_) => (stree, rev (#gtoken r :: gtokenl), backupl)

fun backstatus_searchtree gtreev =
  let val v = Vector.map (#sstatus o fst) gtreev in
    if Vector.all is_proved v then Proved
    else if Vector.exists is_saturated v then Saturated
    else Undecided
  end

fun backreward_searchtree (gi,reward) gtreev =
  let fun f (i,(r,_)) = 
    if #sstatus r = Proved then 1.0
    else if #sstatus r = Saturated then 0.0
    else if gi = i then reward 
    else #ssum r / #svis r 
  in
    Vector.foldl (op *) 1.0 (Vector.mapi f goalv)
  end

fun backup_searchtree tree gi reward gu =
  let 
    val ({nvis,nsum,nstatus,parentd},gtreev) = dest_searchtree tree
    val newgtreev = Vector.update (gtreev,gi,gu)
    val newstatus = backstatus_searchtree newgtreev
    val newreward = backreward_searchtree (gi,reward) newgtreev
  in
    SearchNode 
      ({nvis = nvis + 1.0, nsum = nsum + newreward, nstatus = newstatus,
        parentd = parentd}, newgtreev)
  end

fun createreward_searchtree gtreev =
  let fun f gtree = case gtree of
      StacNode (r,_) => #gsum r / #gvis r 
    | _ => raise ERR "createreward_searchtree" ""
  in
    Vector.foldl (op *) 1.0 (Vector.map f gtreev)
  end

val empty_siblind = dempty (list_compare goal_compare)

fun create_searchtree searchobj parentd gl = 
  let 
    val vnno = #vnno searchobj 
    fun create_gtree g = 
      StacNode (
      {token = Goal (g, empty_siblingd), atyl = [], 
       svis = 1.0, ssum = reward_of_goal vnno g, 
       spol = 0.0, sstatus = Undecided}
      , NONE)
    val gtreev = Vector.fromList (map create_gtree gl) 
    val reward = createreward_searchtree gtreev
  in
    (SOME (SearchNode ({nvis = 1.0, nsum = reward, nstatus = Undecided, 
                parentd = parentd} , gtreev)), reward)
  end
  
fun goal_of_gtokenl gtokenl = case gtokenl of
    Goal (g,_) :: m => g
  | _ => raise ERR "goal_of_tokenl" ""


fun update_stacrec (status,reward) {gtoken,atyl,svis,ssum,spol,sstatus} =
  {gtoken = gtoken, atyl = atyl,
   svis = svis + 1.0, ssum = ssum + reward, spol = spol,
   sstatus = status}

fun backupleaf_wstatus stacleaf status (cuo,reward) = 
  let     
    val newstacleaf = case stacleaf of
        StacNode (r,svo) => StacNode (update_stacrec (status,reward) r,svo)
      | StacLeaf (r,_) => StacLeaf (update_stacrec (status,reward) r,cuo)
  in
    (newstacleaf,reward)
  end

fun backupleaf stacleaf (cuo,reward) =
  let     
    val cu = valOf cuo handle Option => raise ERR "backupleaf" ""
    val status = (#nstatus o fst o dest_searchtree) cu
  in
    backupleaf_wstatus stacleaf status (cuo,reward)
  end

fun endselect status bfl bfroot sleaf = 
  let
    val ctreeo = case sleaf of StacNode _ => NONE
      | Stactree (_,co) => co
    val reward = reward_of_status status
    val be = (backupleaf_wstatus sleaf status, bfl, bfroot) 
  in
    ((ctreeo,reward), be :: backupl)
  end

fun select_searchleaf searchobj backupl tree =
  let 
    val (nr,gtreev) = dest_searchtree tree
    val (gi,gtree) = select_goaltree gtreev    
    val bfroot = backup_searchtree tree gi
    val (sleaf,gtokenl,bfl) = select_stacleaf searchobj [] gtree
  in
    case sleaf of
      StacNode _ => endselect Saturated bfl bfroot sleaf
    | StacLeaf (sr,SOME ctree) => 
      if #sstatus sr <> Undecided andalso not (!contmid_flag) then 
        endselect (#status sr) bfl bfroot sleaf
      else 
      let val be = (backupleaf sleaf,bfl,bfroot) in
        select_searchleaf searchobj (be :: backupl) ctree
      end         
    | StacLeaf (sr,NONE) => 
      if #sstatus sr <> Undecided then 
        endselect (#status sr) bfl bfroot sleaf
      else 
      let val (glo,status) = total_time apply_time 
        (apply_stac searchobj nr) gtokenl 
      in
        case glo of 
           NONE => endselect status bfl bfroot sleaf
         | SOME gl =>
        let 
          val newparentd = dadd (goal_of_gtokenl gtokenl) (#parentd nr)
          val _ = debug "creation"
          val (newctree,reward) = total_time create_time 
            (create_searchtree newparentd) gl
          val be = (backupleaf sleaf, bfl, bfroot)
        in
          ((SOME newctree, reward), be :: backupl)
        end
     end
  end

(* -------------------------------------------------------------------------
   Rebuild the tree using the stored backup functions
   ------------------------------------------------------------------------- *)

fun backuploop_stactree (bleaf,bnodel,broot) x =
  let fun f l x = case l of
      [] =>  x
    | backupf :: m => f m (backupf x)
  in
    broot (f bnodel (bleaf x))
  end

fun backuploop_searchtree backupl x =
  case backupl of
    [] => x
  | a :: m => backuploop_searchtree m (backuploop_stactree a x)
  
fun backupfull backupl x =
  let val (ctreeo,reward) = backuploop_searchtree backupl x in
    valOf ctreeo
  end


(* -------------------------------------------------------------------------
   Search loop: selection, expansion and backup
   ------------------------------------------------------------------------- *)

fun get_searchstatus tree =
  let val nstatus = #nstatus (dfind [] tree) in
    if nstatus = NodeSaturated then SearchSaturated
    else if nstatus = NodeProved then SearchProved
    else SearchTimeout
  end

fun stop_search (timer,nlimito) n tree =
  let val nstatus = (#nstatus o fst o dest_searchtree) tree in 
    (isSome nlimito andalso n >= valOf nlimito) orelse
    (not (isSome nlimito) andalso 
       Timer.checkRealTimer timer > Time.fromReal (!ttt_search_time)) orelse
    (not (!conttop_flag) andalso nstatus <> Undecided)
  end

fun search_loop startsearchobj nlimito starttree = 
  let
    val timer = Timer.startRealTimer ()
    fun loop n searchobj tree =
      if stop_search (timer,nlimito) n tree
      then (print_endline ("loops: " ^ its n); (get_searchstatus tree,tree))
      else
        let
          val _ = debug "selection"
          val ((ctreeo, reward), backupl) = total_time select_time 
            select_searchleaf searchobj [] tree
          val _ = debug "backup"
          val backuptree = total_time backup_time 
            (backupfull backupl) (ctreeo, reward)
        in
          loop (n+1) searchobj backuptree
        end
  in
    loop 0 startsearchobj starttree
  end

(* -------------------------------------------------------------------------
   Proof reconstruction
   ------------------------------------------------------------------------- *)

fun extract_proofl tree  = case tree of
  




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

fun search searchobj g =
  let
    val _ = (clean_stac_cache (); clean_timers ())
    val starttree = create_searchtree searchobj (dempty goal_compare) [goal]
    val ((searchstatus,tree),t) = add_time
      (search_loop searchobj NONE) starttree
    val _ = clean_stac_cache ()
    val _ = print_endline ("nodes: " ^ "1");
    val _ = print_endline ("search: " ^ rts_round 6 t)
    val r = total_time recons_time
      (reconstruct_proofstatus (searchstatus,tree)) g
    val _ = print_timers ()
  in
    (r, tree)
  end


end (* struct *)
