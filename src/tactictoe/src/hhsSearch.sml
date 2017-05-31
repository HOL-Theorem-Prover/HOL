structure hhsSearch :> hhsSearch =
struct

(* ----------------------------------------------------------------------
   Warning:
   a call to metis is recognized because its score is greater than 1.
   ---------------------------------------------------------------------- *)

open HolKernel boolLib Abbrev hhsTools hhsLog hhsTimeout hhsFeature hhsPredict
hhsExec hhsLexer

val ERR = mk_HOL_ERR "hhsSearch"

(*---------------------------------------------------------------------------
   Removing comments
 ----------------------------------------------------------------------------*)

fun rm_comment_aux isq par acc charl = 
  if isq then
    case charl of
      []                  => rev acc
    | #"\\" :: #"\\" :: m => rm_comment_aux true 0 (#"\\" :: #"\\" :: acc) m
    | #"\\" :: #"\"" :: m => rm_comment_aux true 0 (#"\"" :: #"\\" :: acc) m
    | #"\"" :: m          => rm_comment_aux false 0 (#"\"" :: acc) m     
    | a :: m              => rm_comment_aux true 0 (a :: acc) m     
  else if par > 0 then
    (
    case charl of
      []                => rev acc
    | #"(" :: #"*" :: m => rm_comment_aux false (par + 1) acc m
    | #"*" :: #")" :: m => rm_comment_aux false (par - 1) acc m     
    | a :: m            => rm_comment_aux false par acc m     
    )
  else if par = 0 then
    (
    case charl of
      []                => rev acc
    | #"\"" :: m        => rm_comment_aux true 0 (#"\"" :: acc) m
    | #"(" :: #"*" :: m => rm_comment_aux false 1 acc m
    | #"*" :: #")" :: m => raise ERR "rm_comment" "negative_par" 
    | a :: m            => rm_comment_aux false 0 (a :: acc) m     
    )
  else raise ERR "rm_comment_aux" (implode (rev acc) ^ " : " ^ implode charl)

fun rm_comment s = implode (rm_comment_aux false 0 [] (explode s))


(* ----------------------------------------------------------------------
   Exceptions
   ---------------------------------------------------------------------- *)

exception SearchTimeOut
exception NoNextTac

(* ----------------------------------------------------------------------
   Globals
   ---------------------------------------------------------------------- *)

fun empty_predictor (g:goal) = []
val proofdict = ref (dempty Int.compare)
val finproofdict = ref (dempty Int.compare)
val tacdict_glob = ref (dempty String.compare)
val thm_predictor_glob = ref (fn g => [])
val predictor_glob = ref empty_predictor
val symweight_glob = ref (dempty String.compare)
val nfstfea_glob = ref 0
val glob_timer = ref NONE
val minimize_flag = ref true

(* ----------------------------------------------------------------------
   Cache
   ---------------------------------------------------------------------- *)

fun stacgoal_compare ((stac1,goal1),(stac2,goal2)) =
  case String.compare (stac1,stac2) of
    EQUAL => goal_compare (goal1,goal2)
  | x     => x

val goalpred_cache = ref (dempty goal_compare)
val stacgoal_cache = ref (dempty stacgoal_compare)

(* ----------------------------------------------------------------------
   Options
   ---------------------------------------------------------------------- *)

val hhs_search_time = ref (Time.fromReal 0.0)
val hhs_noscore = ref false

val hhs_tactic_time = ref 0.0
val hhs_cache_flag  = ref false
val hhs_metis_flag  = ref false
val hhs_metis_time = ref 0.0

val hhs_debug_flag = ref false
val hhs_depthpen_flag = ref false
val hhs_depthpen = ref 0.8
val hhs_widthpen_flag = ref false
val hhs_widthpen = ref 0.9


(* ----------------------------------------------------------------------
   Debugging
   ---------------------------------------------------------------------- *)

val stac_counter = ref 0

fun debug s =
  if !hhs_debug_flag
  then
    (
    append_file (hhs_log_dir ^ "/debug") (s ^ "\n");
    print (s ^ "\n")
    )
  else ()

fun string_of_predentry (stac,score) =
      "(" ^ stac ^ "," ^ Real.toString score ^ ")"

fun string_of_pred pred =
  "[" ^ String.concatWith "," (map string_of_predentry pred) ^ "]"

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

val metis_chat = ref 0
val meson_chat = ref 0

(* ----------------------------------------------------------------------
   Checking time taken by the predictions
   ---------------------------------------------------------------------- *)

val predict_time = ref 0.0
val thm_predict_time = ref 0.0
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
val thm_predict_timer = save_time thm_predict_time
val infstep_timer = save_time infstep_time
fun node_create_timer f x = save_time node_create_time f x
val node_find_timer = save_time node_find_time
fun total_timer f x = save_time total_time f x

(* ----------------------------------------------------------------------
    Node creation and deletion done by these functions
   ---------------------------------------------------------------------- *)

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
      (* trydict  = ref (dempty compare_goal_list) *)
      pending  = ref [0],
      proofl   = ref [],
      children = ref [],
      pardict  = dempty goal_compare,
      trydict  = ref (dempty (list_compare goal_compare)),
      depth = 0
      }
  in
    debug "root_create";
    debug ("  goals: " ^
          String.concatWith "," (map string_of_goal [goal]));
    debug ("  predictions: " ^
          String.concatWith "," (map string_of_pred [pred]));
    proofdict := dadd selfid selfrec (!proofdict)
  end

fun node_create parid parstac pargn parg goallist predlist pending pardict =
  let
    val pardepth = #depth (dfind parid (!proofdict))
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
      depth    = pardepth + 1
    }
  in
    debug ("node_create " ^ int_to_string selfid ^
           " child of " ^ int_to_string parid ^
           " by " ^ parstac);
    debug ("  goals: " ^
          String.concatWith "," (map string_of_goal goallist));
    debug ("  predictions: " ^
          String.concatWith "," (map string_of_pred predlist));
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

(* ----------------------------------------------------------------------
   Application of a tactic
   ---------------------------------------------------------------------- *)
exception TacTimeOutAgain

fun apply_stac bmetis pardict trydict_unref stac g =
  let
    val tactic_time = if bmetis then !hhs_metis_time else !hhs_tactic_time
    val _ = stac_counter := !stac_counter + 1
    (* val _ = debug ("  " ^ int_to_string (!stac_counter) ^ " tactic") *)
    (* val _ = debug ("  " ^ stac) *)
    val tac = dfind stac (!tacdict_glob) handle _ => raise ERR "apply_stac" stac
    val gl =
      if !hhs_cache_flag then
        if dmem (stac,g) (!stacgoal_cache)
        then
          case dfind (stac,g) (!stacgoal_cache) of
            NONE => raise TacTimeOutAgain
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
       | TacTimeOutAgain => NONE

fun apply_next_stac bmetis pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
      handle _ => raise ERR "apply_next_stac" "empty pending"
    val goal = Array.sub (#goalarr prec, gn)
    val pred = Array.sub (#predarr prec, gn)
    val trydict_unref = !(#trydict prec)
    val pardict = (#pardict prec)
    val (stac,_) = hd pred
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
    fun compare_score ((_,r1),(_,r2)) = Real.compare (r2,r1)
    val l1 = List.mapPartial give_score l0
    val l2 = dict_sort compare_score l1
  in
    if null l2
    then (debug "nonexttac"; raise NoNextTac)
    else
      let
        val (pid,score) = hd l2
        val bmetis = score > 1.01
        val prec = dfind pid (!proofdict)
        val gn = hd (! (#pending prec))
        val goal = Array.sub (#goalarr prec, gn)
        val (stac,_) = hd (Array.sub (#predarr prec, gn))
      in
        debug ("node_find " ^ int_to_string pid ^
               " with " ^ Real.toString score ^
               " for " ^ stac ^
               " on " ^ string_of_goal goal);
        (bmetis,pid)
      end
  end

(* ----------------------------------------------------------------------
   Closing proofs
   ---------------------------------------------------------------------- *)

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
   Three different cases. Either a proof, a failure or a list of goals.
   ---------------------------------------------------------------------- *)

(* Give a value of 1.1 to Metis so that it is processed first *)

exception METIS_PRED

fun add_metis_pred (g,pred) =
  if !hhs_metis_flag
  then
    let
      val thmpred = thm_predict_timer (!thm_predictor_glob) g
      val stac = "metisTools.METIS_TAC [ " ^
                 String.concatWith " , " thmpred ^ " ]"
      val tac = valid_tactic_of_sml stac handle _ => raise METIS_PRED
    in
      tacdict_glob := dadd stac tac (!tacdict_glob);
      (g, (stac,1.1) :: pred)
    end
    handle METIS_PRED => (g,pred)
  else (g,pred)

fun norm_pred depth_coeff (g,pred) =
  let
    val norm =
      if !hhs_noscore
      then 1.0
      else knn_self_distance (!nfstfea_glob) (!symweight_glob) (fea_of_goal g)
    val width_coeff = ref 1.0
    fun f (stac,score) =
      let
        val new_score =
          if !hhs_noscore
          then (!width_coeff) * depth_coeff * 1.0
          else (!width_coeff) * depth_coeff * (score / norm)
        val _ =
          if !hhs_widthpen_flag
          then width_coeff := (!width_coeff) * (!hhs_widthpen)
          else ()
      in
        (stac, new_score)
      end
  in
    (g, map f pred)
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

fun node_create_gl gl pid =
  let
    val prec = dfind pid (!proofdict)
    val gn = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val (stac,_) = hd (Array.sub (#predarr prec, gn))
    val parchildren = #children prec
   (* Normalization of the predictions scores *)
    val depth = #depth prec + 1;
    val depth_coeff =
      if !hhs_depthpen_flag
      then Math.pow (!hhs_depthpen, Real.fromInt depth)
      else 1.0
    fun add_pred g =
      if !hhs_cache_flag
      then
        (g, dfind g (!goalpred_cache)) handle _ =>
        let
          val r = predict_timer (!predictor_glob) g
        in
          goalpred_cache := dadd g r (!goalpred_cache);
          (g,r)
        end
      else (g, predict_timer (!predictor_glob) g)
    val predlist0 =
      map (add_metis_pred o (norm_pred depth_coeff) o add_pred) gl
    val predlist1 = map snd predlist0
    (* Ordering the goals: hardest first *)
    val pending0 = number_list 0 predlist1
    val pending1 = map (fn (gn,pred) => (gn, (snd o hd) pred)) pending0
    fun compare_score ((_,r1),(_,r2)) = Real.compare (r1,r2)
    val pending = map fst (dict_sort compare_score pending1)

    (* Updating the list of parent *)
    val new_pardict = dadd goal () (#pardict prec)

    (* New node *)
    val selfid = node_create pid stac gn goal gl predlist1 pending new_pardict
  in
    parchildren := selfid :: (!parchildren);
    selfid
  end

(* fake a node when a proof is found but no search is performed on this node *)
fun node_create_empty pid =
  let
    val prec = dfind pid (!proofdict)
    val gn   = hd (! (#pending prec))
    val goal = Array.sub (#goalarr prec, gn)
    val (stac,_) = hd (Array.sub (#predarr prec, gn))
    val parchildren = #children prec
    val selfid = node_create pid stac gn goal [] [] [] (dempty goal_compare)
  in
    parchildren := selfid :: (!parchildren);
    selfid
  end

(* ----------------------------------------------------------------------
   Main search function. Modifies proofdict.
   ---------------------------------------------------------------------- *)

fun init_search thm_predictor predictor nfstfea symweight tacdict g =
  let
    val _ = (meson_chat := !mesonLib.chatting;
             mesonLib.chatting := 0)
    val _ = (metis_chat := !mlibUseful.trace_level;
             mlibUseful.trace_level := 0)
    val _ = stacgoal_cache := dempty stacgoal_compare
    val _ = goalpred_cache := dempty goal_compare
    val _ = if !hhs_debug_flag
            then hhs_print ("Goal: " ^ string_of_goal g)
            else ()
    val _ = debug ("\nStarting proof of: " ^ string_of_goal g)
    val _ = predict_time := 0.0
    val _ = thm_predict_time := 0.0
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
    val _ = predictor_glob := predictor
    val _ = thm_predictor_glob := thm_predictor
    val _ = nfstfea_glob := nfstfea
    val _ = symweight_glob := symweight
    val _ = tacdict_glob := tacdict
  in
    ()
  end

fun root_create_wrap g =
  let
    (* Predictions *)
    val pred = predict_timer (!predictor_glob) g
    val (_,pred1) = (add_metis_pred o (norm_pred 1.0)) (g,pred)
  in
    root_create g pred1
  end

fun search_step () =
  let
    val (bmetis,pid) = node_find_timer node_find ()
    val prec = dfind pid (!proofdict)
    val trydict = #trydict prec
    val glo = apply_next_stac bmetis pid
  in
    case glo of
      NONE    => get_next_pred pid
    | SOME gl =>
      if gl = []
      then
        let val cid = node_create_timer node_create_empty pid in
          close_proof cid pid
        end
      else
        (
        trydict := dadd gl () (!trydict);
        ignore (node_create_timer (node_create_gl gl) pid)
        )
  end

fun search_loop () =
  (
  if Timer.checkRealTimer (valOf (!glob_timer)) > (!hhs_search_time)
    then print "  time out\n"
  else if dmem 0 (!finproofdict) then ()
  else
    (search_step (); search_loop ())
  )
  handle NoNextTac => print "  saturated\n"
       | ProofFound => ()

val pstep_counter = ref 0

fun unquote s =
  if String.size s >= 2
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unquote" ""

fun add_quote_aux sl = case sl of
    [] =>  ""
  | [a] => a
  | "(" :: "Parse.Type" :: "[" :: "HOLPP.QUOTE" :: "(" :: s :: ")" :: 
    "]" :: ")" :: m => 
    "``" ^ (rm_blank o rm_comment o unquote) s ^ "``" ^ " " ^ add_quote_aux m
  | "(" :: "Parse.Term" :: "[" :: "HOLPP.QUOTE" :: "(" :: s :: ")" :: 
    "]" :: ")" :: m => 
    "``" ^ (rm_blank o rm_comment o unquote) s ^ "``" ^ " " ^ add_quote_aux m
  | "[" :: "HOLPP.QUOTE" :: "(" :: s :: ")" :: "]" :: m =>
    "`" ^ (rm_blank o rm_comment o unquote) s ^ "`" ^ " " ^ add_quote_aux m
  | "[" :: "HOLPP.QUOTE"  :: s :: "]" :: m =>
    "`" ^ (rm_blank o rm_comment o unquote) s ^ "`" ^ " " ^ add_quote_aux m
  | a :: m => a ^ " " ^ add_quote_aux m

fun add_quote stac = add_quote_aux (hhs_lex stac)

fun rm_fetch_aux sl = case sl of
    [] =>  ""
  | [a] => a
  | "(" :: "DB.fetch" :: thy :: b :: ")" :: m =>
    (
    if thy = current_theory () 
    then String.concatWith " " ["(","DB.fetch",thy,b,")",rm_fetch_aux m]
    else unquote thy ^ "Theory." ^ unquote b ^ " " ^ rm_fetch_aux m
    )
  | a :: m => a ^ " " ^ rm_fetch_aux m

fun rm_fetch stac = rm_fetch_aux (hhs_lex stac)
 
fun minspace_sl sl = case sl of
    [] =>  ""
  | [a] => a
  | a :: b :: m =>
    (
    if mem a ["[","("] orelse mem b ["]",")",",",";"] 
      then a ^ minspace_sl (b :: m)
      else a ^ " " ^ minspace_sl (b :: m)
    )

fun rm_prefix stac =
  let
    val sl = hhs_lex stac
    fun rm_one_prefix s =
      let
        val l = String.tokens (fn x => x = #".") s
        val s' = last l
      in
        if List.length l = 1 orelse not (is_pointer_eq s s') then s else s'
      end
  in
    map rm_one_prefix sl
  end

fun prettify1_stac stac = 
  (minspace_sl o rm_prefix o rm_fetch o add_quote) stac
fun prettify2_stac stac =
  (minspace_sl o hhs_lex o rm_fetch o add_quote) stac

datatype Proof = 
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

(*
    fun is_single_token s = List.length (hhs_lex s) = 1
    fun par s = if is_single_token s
                then prettify_stac s
                else "(" ^ prettify_stac s ^ ")"
*)
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

fun exact_effect stac1 stac2 g =
  let 
    val gl1 = SOME (fst (valid_tactic_of_sml stac1 g)) handle _ => NONE
    val gl2 = SOME (fst (valid_tactic_of_sml stac2 g)) handle _ => NONE
  in
    gl1 <> NONE andalso gl2 <> NONE andalso gl1 = gl2 
  end

fun is_proof stac g =
  let 
    val tim = 1.0
    val gl1 = SOME (fst (timeOut tim (valid_tactic_of_sml stac) g)) 
              handle _ => NONE
  in
    gl1 = SOME []
  end

fun is_effect stac g gl =
  let 
    val tim = Real.max (!hhs_tactic_time, !hhs_metis_time)
    val gl1 = SOME (fst (timeOut tim (valid_tactic_of_sml stac) g)) 
              handle _ => NONE
  in
    gl1 = SOME gl
  end



fun string_of_proof proof = case proof of
    Tactic (s,_) => s
  | Then (p1,p2) => string_of_proof p1 ^ " THEN " ^ string_of_proof p2
  | Thenl (p,pl) => 
    let 
      val sl = map string_of_proof pl
      val set = mk_fast_set String.compare sl
    in
      if length set = 1 
      then string_of_proof p ^ " THEN " ^ hd set
      else string_of_proof p ^ " THENL " ^ "[" ^ String.concatWith ", " sl ^ "]"
    end 
fun safe_string_of_proof proof = case proof of
    Tactic (s,_) => "(" ^ s ^ ")"
  | Then (p1,p2) => 
    safe_string_of_proof p1 ^ " THEN " ^ safe_string_of_proof p2
  | Thenl (p,pl) =>     
    let 
      val sl = map safe_string_of_proof pl
      val set = mk_fast_set String.compare sl
    in
      if length set = 1 
      then safe_string_of_proof p ^ " THEN " ^ "(" ^ hd set ^ ")"
      else safe_string_of_proof p ^ " THENL " ^ 
        "[" ^ String.concatWith ", " sl ^ "]"
    end

fun parse_list acc l opar obra olet ocur sl = case sl of
    "{" :: m => parse_list ("{" :: acc) l opar obra olet (ocur + 1) m
  | "}" :: m => parse_list ("}" :: acc) l opar obra olet (ocur - 1) m
  | "let" :: m => parse_list ("let" :: acc) l opar obra (olet + 1) ocur m
  | "end" :: m => parse_list ("end" :: acc) l opar obra (olet - 1) ocur m
  | "(" :: m => parse_list ("(" :: acc) l (opar + 1) obra olet ocur m
  | ")" :: m => parse_list (")" :: acc) l (opar - 1) obra olet ocur m 
  | "[" :: m => parse_list ("[" :: acc) l opar (obra + 1) olet ocur m
  | "]" :: m => 
     if obra <= 1 andalso opar = 0 andalso olet = 0 andalso ocur = 0
     then (rev (rev acc :: l), m)
     else parse_list ("]" :: acc) l opar (obra - 1) olet ocur m 
  | "," :: m => 
     if obra <= 1 andalso opar = 0 andalso olet = 0 andalso ocur = 0
     then parse_list [] (rev acc :: l) opar obra olet ocur m
     else parse_list ("," :: acc) l opar obra olet ocur m
  | a :: m => parse_list (a :: acc) l opar obra olet ocur m
  | []     => raise ERR "parse_list" ""
  
fun parse_list_full sl = case sl of
    "[" :: m => 
    let val (eleml,nextl) = parse_list [] [] 0 1 0 0 m in
      (map (String.concatWith " ") eleml, nextl)
    end
  | _ => raise ERR "parse_list_full" ""
   
fun decompose sl = case sl of
    [] => []
  | "[" :: m => 
    let val (eleml,nextl) = parse_list_full sl in
      (true, ([],eleml)) :: decompose nextl
    end
  | a :: m => (false, ([],[a])) :: decompose m
  
fun list_to_string sl = "[ " ^ String.concatWith " , " sl ^ " ]"
  
fun group_to_string l =
  let fun to_string (b,(l1',l2')) =  
    if b then list_to_string (l1' @ l2') else hd l2'
  in
    String.concatWith " " (map to_string l)
  end
  
fun minimize_stac g gl pl l = case l of
    [] => group_to_string pl
  | (false,a) :: m => minimize_stac g gl (pl @ [(false,a)]) m
  | (true,(l1,l2)) :: m => 
    if null l2 
    then minimize_stac g gl (pl @ [(true,(l1,l2))]) m
    else 
      let val new_stac = group_to_string  (pl @ [(true, (l1, tl l2))] @ m) in
        if is_effect new_stac g gl 
        then minimize_stac g gl pl ((true, (l1, tl l2)) :: m)
        else minimize_stac g gl pl ((true, (l1 @ [hd l2], tl l2)) :: m)
      end   
        
fun minimize_stac_full stac g =
  let val gl = fst (valid_tactic_of_sml stac g) 
    handle _ => raise ERR "minimize" stac
  in
    minimize_stac g gl [] (decompose (hhs_lex stac))
  end       
       
fun minimize_tac proof = case proof of 
    Tactic (s,g) => Tactic (minimize_stac_full s g,g)   
  | Then (p1,p2) => Then (minimize_tac p1, minimize_tac p2)
  | Thenl (p,pl) => Thenl (minimize_tac p, map minimize_tac pl)
 
fun minimize_proof proof = case proof of
    Tactic _ => proof
  | Then (Tactic (_,g),p2) => 
    let val s = safe_string_of_proof p2 in
      if is_proof s g then p2 else proof
    end
  | Then (p1,p2) => Then (minimize_proof p1, minimize_proof p2)
  | Thenl (p,pl) => Thenl (minimize_proof p, map minimize_proof pl)
 
fun prettify_proof proof = case proof of
    Tactic (s,g) =>
    let 
      val s1 = prettify1_stac s
      val s2 = prettify2_stac s
    in
      if exact_effect s s1 g then Tactic (s1,g)
      else if exact_effect s s2 g then Tactic (s2,g)
      else Tactic (s,g)
    end
  | Then (p1,p2) => Then (prettify_proof p1, prettify_proof p2)
  | Thenl (p,pl) => Thenl (prettify_proof p, map prettify_proof pl)

fun hhs_reconstruct g proof =
  let
    val sproof = string_of_proof proof
    val tac    = valid_tactic_of_sml sproof
                 handle _ => raise ERR "hhs_reconstruct" sproof
  in
    (
    ignore (Tactical.TAC_PROOF (g,tac));
    print (sproof ^ "\n");
    if !hhs_debug_flag then hhs_print (sproof ^ "\n") else ()
    )
    handle _ => raise ERR "hhs_reconstruct" sproof
  end
  
fun safe_hhs_reconstruct g proof =
  hhs_reconstruct g proof handle _ => 
  (
  let
    val sproof = safe_string_of_proof proof
    val tac    = valid_tactic_of_sml sproof
                 handle _ => raise ERR "safe_hhs_reconstruct" sproof
  in
    (
    ignore (Tactical.TAC_PROOF (g,tac));
    print (sproof ^ "\n");
    if !hhs_debug_flag then hhs_print (sproof ^ "\n") else ()
    )
    handle _ => raise ERR "safe_hhs_reconstruct" sproof
  end  
  )

fun end_search () =
  (
  if !hhs_debug_flag then
  (
  hhs_print ("Statistics");
  hhs_print ("  infstep : " ^ int_to_string (!stac_counter));
  hhs_print ("  nodes   : " ^ int_to_string (!pid_counter));
  hhs_print ("  maxdepth: " ^ int_to_string (!max_depth_mem));
  hhs_print ("Time: " ^ Real.toString (!total_time));
  hhs_print ("  inferstep time: " ^ Real.toString (!infstep_time));
  hhs_print ("  node_find time: " ^ Real.toString (!node_find_time));
  hhs_print ("  node_crea time: " ^ Real.toString (!node_create_time));
  hhs_print ("    predictio time: " ^ Real.toString (!predict_time));
  hhs_print ("    thm predictio time: " ^ Real.toString (!thm_predict_time))
  )
  else ();
  mesonLib.chatting := !meson_chat;
  mlibUseful.trace_level := !metis_chat;
  predict_time := 0.0;
  thm_predict_time := 0.0;
  infstep_time := 0.0;
  node_find_time := 0.0;
  node_create_time := 0.0;
  total_time := 0.0;
  proofdict    := dempty Int.compare;
  finproofdict := dempty Int.compare;
  pid_counter := 0;
  stac_counter := 0;
  tacdict_glob := dempty String.compare;
  predictor_glob := empty_predictor;
  thm_predictor_glob := (fn g => []);
  symweight_glob := dempty String.compare;
  stacgoal_cache := dempty stacgoal_compare;
  goalpred_cache := dempty goal_compare
  )

fun imperative_search thm_predictor predictor nfstfea symweight tacdict g =
  (
  init_search thm_predictor predictor nfstfea symweight tacdict g;
  total_timer (node_create_timer root_create_wrap) g;
  total_timer search_loop ();
  if dmem 0 (!finproofdict) then 
    let 
      val proofl = proofl_of 0
      val proof = 
        if length proofl <> 1 
        then raise ERR "imperative_search" "" 
        else 
          if !minimize_flag 
          then (prettify_proof o minimize_proof o minimize_tac) (hd proofl)
          else prettify_proof (hd proofl)
    in
      safe_hhs_reconstruct g proof
    end
  else ();
  end_search ()
  )

end (* struct *)
