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
  psMinimize tttSetup tttToken tttLearn tttTrain

val ERR = mk_HOL_ERR "tttSearch"
fun hderr x = hd x handle Empty => raise ERR "hderr" ""
fun tlerr x = tl x handle Empty => raise ERR "tlerr" ""

(* -------------------------------------------------------------------------
   Global parameters
   ------------------------------------------------------------------------- *)

val default_reward = 0.0
val conttop_flag = ref false
val contmid_flag = ref false
val nocut_flag = ref false
val looplimit = ref NONE

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
fun is_proved x = (x = Proved)
fun is_saturated x = (x = Saturated)

datatype searchstatus = 
  SearchProved | SearchSaturated | SearchTimeout
datatype proofstatus = 
  Proof of string | ProofSaturated | ProofTimeout

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

datatype gtoken = 
  Token of token | Goal of (goal * (goal list, unit) Redblackmap.dict)
fun is_token gtoken = case gtoken of Token _ => true | _ => false
fun is_goal gtoken = case gtoken of Goal _ => true | _ => false
fun dest_token gtoken =
  case gtoken of Token x => x | _ => raise ERR "dest_token" ""
fun dest_goal gtoken =
  case gtoken of Goal (x,_) => x | _ => raise ERR "dest_goal" ""

type searchrecord =
  {nvis : real, nsum : real, nstatus : status,
   parentd : (goal, unit) Redblackmap.dict}

type stacrecord =
  {gtoken : gtoken, atyl : aty list,
   svis : real, ssum : real, spol : real, sstatus : status}

datatype searchtree = SearchNode of searchrecord * stactree vector

and stactree = 
   StacLeaf of stacrecord * searchtree option
 | StacNode of stacrecord * (stactree vector * token list) option

fun dest_searchtree tree = case tree of SearchNode x => x

fun get_stacrecord stactree = case stactree of
   StacLeaf (r,_) => r
 | StacNode (r,_) => r

(* -------------------------------------------------------------------------
   Search parameters
   ------------------------------------------------------------------------- *)

type searchobj =
  {predtac : goal -> token list,
   predarg : string -> aty -> goal -> token list,
   atyd : (string, aty list) Redblackmap.dict,
   parsetoken : parsetoken,
   vnno: tnn option, pnno: tnn option, anno: tnn option}

(* -------------------------------------------------------------------------
   Re-evaluation of nearest neighbor choices
   by tree neural networks
   ------------------------------------------------------------------------- *)

(* value *)
fun eval_goal vnn g =
  let
    val tm1 = nntm_of_stateval g
    val tm2 = mask_unknown_val vnn tm1
  in
    infer_tnn_basic vnn tm2
  end

fun reward_of_goal vnno g =
  if not (isSome vnno) then default_reward else eval_goal (valOf vnno) g

(*
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
*)

(* -------------------------------------------------------------------------
   Node expansion
   ------------------------------------------------------------------------- *)

fun status_of_stac parentd (goal,siblingd) glo = case glo of
    NONE => Saturated
  | SOME [] => Proved
  | SOME gl =>
   (if op_mem goal_eq goal gl orelse
       exists (fn x => dmem x parentd) gl orelse
       dmem gl siblingd orelse
       exists (fn x => term_eq (snd x) F) gl orelse
       (!nocut_flag andalso 
        exists (fn x => term_eq (snd x) (snd goal)) gl)
    then Saturated
    else Undecided)

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

fun apply_stac obj noderec gtokenl = case gtokenl of
    Goal (goal,siblingd) :: tokenl =>
  let
    val glo = apply_tac (#parsetoken obj) (map dest_token tokenl) goal
    val sstatus = status_of_stac (#parentd noderec) (goal,siblingd) glo
    val glo' = if sstatus = Undecided then glo else NONE
  in
    (glo',sstatus)
  end
  | _ => raise ERR "apply_stac" ""

(* -------------------------------------------------------------------------
   Node creation
   ------------------------------------------------------------------------- *)

(* predictions *)
fun create_predtac obj svo goal = case svo of 
    NONE => SOME (Vector.fromList [], #predtac obj goal)
  | SOME _ => svo 

fun create_predarg obj tokenl aty svo = case svo of 
    NONE => (case tokenl of  
      Goal (goal,_) :: Token (Stac stac) :: m =>
        SOME (Vector.fromList [], #predarg obj stac aty goal)
      | _ => raise ERR "create_predarg" "")
  | SOME _ => svo

(* stactree *)
fun wrap_stacrecord x = 
   if is_token (#gtoken x) andalso null (#atyl x)
   then StacLeaf (x,NONE)
   else StacNode (x,NONE)

fun atyl_of obj pr token = case token of 
    Stac stac => dfind stac (#atyd obj)
  | _ => tlerr (#atyl pr)

fun create_stactree obj pr token spol = wrap_stacrecord
  {gtoken = Token token, atyl = atyl_of obj pr token, 
   svis = 1.0, ssum = 0.0, spol = spol, sstatus = Undecided}

(* searchtree *)
fun createreward_searchtree gtreev =
  let fun f gtree = case gtree of
      StacNode (r,_) => #ssum r / #svis r 
    | _ => raise ERR "createreward_searchtree" ""
  in
    Vector.foldl (op *) 1.0 (Vector.map f gtreev)
  end

val empty_siblingd = dempty (list_compare goal_compare)

fun create_searchtree obj parentd gl = 
  let 
    val vnno = #vnno obj 
    fun create_gtree g = StacNode (
      {gtoken = Goal (g, empty_siblingd), atyl = [], 
       svis = 1.0, ssum = reward_of_goal vnno g, 
       spol = 0.0, sstatus = Undecided}
      , NONE)
    val gtreev = Vector.fromList (map create_gtree gl) 
    val reward = createreward_searchtree gtreev
  in
    (SearchNode ({nvis = 1.0, nsum = reward, nstatus = Undecided, 
                  parentd = parentd} , gtreev), reward)
  end

(* -------------------------------------------------------------------------
   Node backup
   ------------------------------------------------------------------------- *)

fun reward_of_status status = case status of
    Saturated => 0.0
  | Proved => 1.0
  | _ => raise ERR "reward_of_sstatus" "unexpected"

(* stactree *)
fun backstatus_stactree (sv,sl) =
  let val v = Vector.map (fn x => #sstatus (get_stacrecord x)) sv in
    if Vector.exists is_proved v then Proved
    else if null sl andalso Vector.all is_saturated v then Saturated
    else Undecided
  end

fun back_stactree stree si (su,reward) = case stree of
     StacNode ({gtoken,atyl,svis,ssum,spol,sstatus}, SOME (sv,sl)) => 
     let 
       val newsv = Vector.update (sv,si,su)
       val newstatus = backstatus_stactree (newsv,sl)
     in 
       (StacNode
         ({gtoken = gtoken, atyl = atyl,
          svis = svis + 1.0, ssum = ssum + reward, spol = spol,
          sstatus = newstatus}, SOME (newsv,sl)),
        reward)
     end
   | _ => raise ERR "back_stactree" ""

(* searchtree root *)
fun backstatus_root gtreev =
  let val v = Vector.map (#sstatus o get_stacrecord) gtreev in
    if Vector.all is_proved v then Proved
    else if Vector.exists is_saturated v then Saturated
    else Undecided
  end

fun backreward_root (gi,reward) gtreev =
  let fun f (i,gtree) = 
    let val r = get_stacrecord gtree in
      if #sstatus r = Proved then 1.0
      else if #sstatus r = Saturated then 0.0
      else if gi = i then reward 
      else #ssum r / #svis r
    end
  in
    Vector.foldl (op *) 1.0 (Vector.mapi f gtreev)
  end

fun back_root tree gi (gu,reward) =
  let 
    val ({nvis,nsum,nstatus,parentd},gtreev) = dest_searchtree tree
    val newgtreev = Vector.update (gtreev,gi,gu)
    val newstatus = backstatus_root newgtreev
    val newreward = backreward_root (gi,reward) newgtreev
  in
    (SOME (SearchNode 
      ({nvis = nvis + 1.0, nsum = nsum + newreward, nstatus = newstatus,
        parentd = parentd}, newgtreev)), newreward)
  end

fun update_stacrec (status,reward) {gtoken,atyl,svis,ssum,spol,sstatus} =
  {gtoken = gtoken, atyl = atyl,
   svis = svis + 1.0, ssum = ssum + reward, spol = spol,
   sstatus = status}

(* stactree leaf *)
fun backleaf_wstatus stacleaf status (cuo,reward) = 
  let     
    val newstacleaf = case stacleaf of
        StacNode (r,svo) => StacNode (update_stacrec (status,reward) r,svo)
      | StacLeaf (r,_) => StacLeaf (update_stacrec (status,reward) r,cuo)
  in
    (newstacleaf,reward)
  end

fun backleaf stacleaf (cuo,reward) =
  let     
    val cu = valOf cuo handle Option => raise ERR "backleaf" ""
    val status = (#nstatus o fst o dest_searchtree) cu
  in
    backleaf_wstatus stacleaf status (cuo,reward)
  end

(* -------------------------------------------------------------------------
   Node selection
   ------------------------------------------------------------------------- *)

fun puct gvis {ssum,svis,spol,...} =
  ssum / svis + (!ttt_explo_coeff) * (spol * Math.sqrt gvis) / svis

fun policy_coeff n =
  (1.0 - !ttt_policy_coeff) * Math.pow (!ttt_policy_coeff, Real.fromInt n)

(* stactree *)
datatype selectres = 
  Sel of int | SelNone | SelFresh of (token * real)

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
      if freshsc > sc then SelFresh (hd sl, freshpol) else Sel i
    end
  end

fun select_stacleaf obj backl gtokenl stree = case stree of
    StacNode (r,svo) => 
    let 
      val newsvo = case #gtoken r of 
          Goal (goal,_) => create_predtac obj svo goal 
        | Token _ => create_predarg obj (rev (#gtoken r :: gtokenl)) 
            (hderr (#atyl r)) svo
      val newstree = StacNode (r,newsvo)
      val newgtokenl = #gtoken r :: gtokenl
    in
      case select_stactree (#svis r) (valOf newsvo) of
        SelNone => (stree, rev newgtokenl, backl)
      | Sel si =>
        let 
          val cstree = Vector.sub (fst (valOf newsvo), si)
          val backf = back_stactree newstree si
          val newbackl = backf :: backl
        in
          select_stacleaf obj newbackl newgtokenl cstree
        end
      | SelFresh (token,spol) => 
        let 
          val cstree = create_stactree obj r token spol 
          val (sv,sl) = valOf newsvo
            handle Option => raise ERR "select_stacleaf" ""
          val newnewsvo = 
            SOME (Vector.concat [sv,Vector.fromList [cstree]], tl sl)
          val newnewstree = StacNode (r,newnewsvo)
          val backf = back_stactree newnewstree (Vector.length sv)
          val newbackl = backf :: backl
        in
          select_stacleaf obj newbackl newgtokenl cstree
        end
    end
  | StacLeaf (r,_) => (stree, rev (#gtoken r :: gtokenl), backl)

(* search tree *)
fun select_goaltree gtreev =
  let
    val _ = if Vector.length gtreev = 0
      then raise ERR "select_goaltree" "" else ()
    fun score x = #svis (get_stacrecord x)
    val i = vector_mini score gtreev
  in
    (i, Vector.sub (gtreev, i))
  end

fun endselect status (backl,bfroot,bfl) sleaf = 
  let
    val ctreeo = case sleaf of StacNode _ => NONE | StacLeaf (_,co) => co
    val reward = reward_of_status status
    val be = (backleaf_wstatus sleaf status, bfl, bfroot) 
  in
    ((ctreeo,reward), be :: backl)
  end

fun select_searchleaf obj backl tree =
  let 
    val (nr,gtreev) = dest_searchtree tree
    val (gi,gtree) = select_goaltree gtreev    
    val bfroot = back_root tree gi
    val (sleaf,gtokenl,bfl) = select_stacleaf obj [] [] gtree
    val bbb = (backl,bfroot,bfl)
  in
    case sleaf of
      StacNode _ => endselect Saturated bbb sleaf
    | StacLeaf (sr,SOME ctree) => 
      if #sstatus sr <> Undecided andalso not (!contmid_flag) then 
        endselect (#sstatus sr) bbb sleaf
      else 
      let val be = (backleaf sleaf, bfl, bfroot) in
        select_searchleaf obj (be :: backl) ctree
      end         
    | StacLeaf (sr,NONE) => 
      if #sstatus sr <> Undecided then 
        endselect (#sstatus sr) bbb sleaf 
      else 
      let val (glo,status) = total_time apply_time 
        (apply_stac obj nr) gtokenl 
      in
        case glo of 
           NONE => endselect status bbb sleaf
         | SOME gl =>
        let 
          fun goal_of_gtokenl gtokenl = case gtokenl of
            Goal (g,_) :: m => g
          | _ => raise ERR "goal_of_tokenl" ""
          val newparentd = dadd (goal_of_gtokenl gtokenl) () (#parentd nr)
          val _ = debug "creation"
          val (newctree,reward) = total_time create_time 
            (create_searchtree obj newparentd) gl
          val be = (backleaf sleaf, bfl, bfroot)
        in
          ((SOME newctree, reward), be :: backl)
        end
     end
  end

(* -------------------------------------------------------------------------
   Rebuild the tree using the stored back functions
   ------------------------------------------------------------------------- *)

fun backloop_stactree (bleaf,bnodel,broot) x =
  let fun f l x = case l of
      [] =>  x
    | backf :: m => f m (backf x)
  in
    broot (f bnodel (bleaf x))
  end

fun backloop_searchtree backl x =
  case backl of
    [] => x
  | a :: m => backloop_searchtree m (backloop_stactree a x)
  
fun backfull backl x =
  let val (ctreeo,reward) = backloop_searchtree backl x in
    valOf ctreeo
  end

(* -------------------------------------------------------------------------
   Search loop: selection, expansion and back
   ------------------------------------------------------------------------- *)

fun get_searchstatus tree =
  let val nstatus = (#nstatus o fst o dest_searchtree) tree in
    if nstatus = Saturated then SearchSaturated
    else if nstatus = Proved then SearchProved
    else SearchTimeout
  end

fun stop_search (timer,nlimito) n tree =
  let val nstatus = (#nstatus o fst o dest_searchtree) tree in 
    (isSome nlimito andalso n >= valOf nlimito) orelse
    (not (isSome nlimito) andalso 
       Timer.checkRealTimer timer > Time.fromReal (!ttt_search_time)) orelse
    (not (!conttop_flag) andalso nstatus <> Undecided)
  end

fun search_loop (obj : searchobj) nlimito starttree = 
  let
    val timer = Timer.startRealTimer ()
    fun loop n tree =
      if stop_search (timer,nlimito) n tree
      then (print_endline ("loops: " ^ its n); (get_searchstatus tree,tree))
      else
        let
          val _ = debug "selection"
          val ((ctreeo,reward),backl) = total_time select_time 
            (select_searchleaf obj []) tree
          val _ = debug "backup"
          val backtree = total_time backup_time 
            (backfull backl) (ctreeo,reward)
        in
          loop (n+1) backtree
        end
  in
    loop 0 starttree
  end

(* -------------------------------------------------------------------------
   Proof reconstruction
   ------------------------------------------------------------------------- *)

fun proof_stactree gtokenl stactree = case stactree of
    StacLeaf (r,ctreeo) => (rev (#gtoken r :: gtokenl), ctreeo)  
  | StacNode (r,svo) =>
    let 
      val (sv,_) = valOf svo 
        handle Option => raise ERR "proof_stactree" ""
      fun f x = is_proved (#sstatus (get_stacrecord x))
      val cstree = valOf (Vector.find f sv) 
        handle Option => raise ERR "proof_stactree" ""
    in
      proof_stactree (#gtoken r :: gtokenl) cstree
    end

fun proofl_searchtree tree =
  let
    val (_,gtreev) = dest_searchtree tree
    fun f gtree =
      let
        val (gtokenl,ctreeo) = proof_stactree [] gtree 
        val tokenl = map dest_token (tl gtokenl)
          handle Empty => raise ERR "proof_searchtree" ""
        val istac = build_stac tokenl
        val goal = dest_goal (hd gtokenl)
        val ptac = Tactic (istac, goal)
        val _ = debugf "goal: " string_of_goal goal
        val _ = debug ("stac: " ^ istac);
      in
        case ctreeo of 
          NONE => ptac 
        | SOME ctree => Thenl (ptac, proofl_searchtree ctree)
      end
  in
    vector_to_list (Vector.map f gtreev)
  end

fun reconstruct_proofstatus (searchstatus,tree) goal =
   case searchstatus of
    SearchSaturated => ProofSaturated
  | SearchTimeout => ProofTimeout
  | SearchProved =>
    let
      val _ = debug "extraction"
      fun f tree = singleton_of_list (proofl_searchtree tree)
      val (proof1,t1) = add_time f tree
      val _ = debug ("extraction time: " ^ rts_round 6 t1)
      val _ = debug "minimization"
      val (proof2,t2) = add_time minimize_proof proof1
      val _ = print_endline ("minimization time: " ^ rts_round 6 t2)
      val _ = debug "reconstruction"
      val (sproof,t3) = add_time (reconstruct goal) proof2
      val _ = print_endline ("reconstruction time: " ^ rts_round 6 t3)
    in
      Proof sproof
    end

(* -------------------------------------------------------------------------
   Proof search top-level function
   ------------------------------------------------------------------------- *)

fun search (obj : searchobj) goal =
  let
    val _ = (clean_stac_cache (); clean_timers ())
    val (starttree,_) = create_searchtree obj (dempty goal_compare) [goal]
    val ((searchstatus,endtree),t) = add_time 
      (search_loop obj (!looplimit)) starttree
    val _ = clean_stac_cache ()
    val _ = print_endline ("nodes: " ^ "1");
    val _ = print_endline ("search: " ^ rts_round 6 t)
    val r = total_time recons_time
      (reconstruct_proofstatus (searchstatus,endtree)) goal
    val _ = print_timers ()
  in
    (r,endtree)
  end


end (* struct *)
