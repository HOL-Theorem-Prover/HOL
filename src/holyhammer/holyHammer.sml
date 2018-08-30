(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, predicted theorems to        *)
(*                 the holyHammer framework. The lemmas                  *)
(*                 found by the provers help Metis to reconstruct the    *)
(*                 proof.                                                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread 
  tttTools tttExec tttFeature tttPredict tttSetup
  hhWriter hhReconstruct hhTranslate hhTptp 

val ERR = mk_HOL_ERR "holyHammer"

(*----------------------------------------------------------------------------
   Settings
  ----------------------------------------------------------------------------*)

val timeout_glob = ref 5
fun set_timeout n = timeout_glob := n

(*----------------------------------------------------------------------------
  ATPs
  ----------------------------------------------------------------------------*)

datatype prover = Eprover | Z3 | Vampire
fun name_of atp = case atp of
    Eprover => "eprover"
  | Z3 => "z3"
  | Vampire => "vampire"

fun npremises_of atp = case atp of
    Eprover => 128
  | Z3 => 32
  | Vampire => 96

val all_atps = ref [Eprover,Z3,Vampire] 
(* atps called by holyhammer if their binary exists *)

(*----------------------------------------------------------------------------
   Directories
 -----------------------------------------------------------------------------*)

fun pathl sl = case sl of 
    []  => raise ERR "pathl" "empty"
  | [a] => a
  | a :: m => OS.Path.concat (a, pathl m)

val hh_dir         = pathl [HOLDIR,"src","holyhammer"];
val hh_eval_dir    = pathl [hh_dir,"eval"];
val provbin_dir    = pathl [hh_dir,"provers"];
fun provdir_of atp = pathl [provbin_dir, name_of atp ^ "_files"]
val parallel_dir   = pathl [provbin_dir,"eprover_parallel"];

fun out_of atp     = pathl [provdir_of atp,"out"]
fun status_of atp  = pathl [provdir_of atp,"status"]
fun out_dir dir    = pathl [dir,"out"]
fun status_dir dir = pathl [dir,"status"]

(*----------------------------------------------------------------------------
  Messages for evaluation. 
  Should not be used in parallel threads.
  ----------------------------------------------------------------------------*)

val hh_eval_flag = ref false
val thy_ref = ref "scratch"

fun hh_log_eval s = 
  if !hh_eval_flag 
  then append_endline (hh_eval_dir ^ "/" ^ !thy_ref) s 
  else ()

fun hh_logt_eval s f x =
  let
    val _ = hh_log_eval s
    val (r,t) = add_time f x
    val _ = hh_log_eval (s ^ " " ^ Real.toString t)
  in
    r
  end

(*----------------------------------------------------------------------------
   Building a database of theorems and cached their features.
   Makes subsequent call of holyhammer in the same theory faster. 
   Should not be used in parallel threads.
  ----------------------------------------------------------------------------*)

val hh_goalfea_cache = ref (dempty goal_compare)

fun clean_goalfea_cache () = hh_goalfea_cache := dempty goal_compare

fun fea_of_goal_cached g = 
  dfind g (!hh_goalfea_cache) handle NotFound =>
  let val fea = fea_of_goal g in
    hh_goalfea_cache := dadd g fea (!hh_goalfea_cache);
    fea
  end

fun add_fea dict (name,thm) =
  let val g = dest_thm thm in
    if not (dmem g (!dict)) andalso uptodate_thm thm
    then dict := dadd g (name, fea_of_goal_cached g) (!dict)
    else ()
  end

fun insert_thyfeav initdict thyl =
  let
    val dict = ref initdict
    fun f_thy thy =
      let fun f (name,thm) =
        add_fea dict ((thy ^ "Theory." ^ name), thm)
      in
        app f (DB.thms thy)
      end
  in
    app f_thy thyl;
    !dict
  end

fun insert_namespace thmdict =
  let
    val dict = ref thmdict
    fun f (x,y) = (namespace_tag ^ "Theory." ^ x, y)
    val l1 = hide_out namespace_thms ()
    val l2 = map f l1
  in
    app (add_fea dict) l2;
    (!dict)
  end

fun create_symweight_feav thmdict =
  let
    val l = dlist thmdict
    val feav = map snd l
    val symweight = learn_tfidf feav
    fun f (g,(name,fea)) = (name,(g,fea))
    val revdict = dnew String.compare (map f l)
  in
    (symweight,feav,revdict)
  end

fun update_thmdata () =
  let
    val thyl = current_theory () :: ancestry (current_theory ())
    val dict0 = insert_thyfeav (dempty goal_compare) thyl
    val dict1 = insert_namespace dict0
    val is = int_to_string (dlength dict1)
  in
    print_endline ("Loading " ^ is ^ " theorems ");
    create_symweight_feav dict1
  end

(*----------------------------------------------------------------------------
   Reading a theorem from its string representation
 -----------------------------------------------------------------------------*)

fun in_namespace s = fst (split_string "Theory." s) = namespace_tag

fun thm_of_name s =
  let val (a,b) = split_string "Theory." s in 
    (s, DB.fetch a b)
  end

fun thml_of_namel sl = 
  let
    val (ns1,namel) = partition in_namespace sl
    fun f s = case thm_of_sml (snd (split_string "Theory." s)) of
        SOME (_,thm) => SOME (s,thm)
      | NONE => NONE
    val ns2  = hide_out (List.mapPartial f) ns1
    val thml = map thm_of_name namel
  in
    ns2 @ thml
  end

(*----------------------------------------------------------------------------
   Run function in parallel and terminate as soon as one returned a
   positive result in parallel_result.
 -----------------------------------------------------------------------------*)

val (parallel_result : string list option ref) = ref NONE

fun close_thread thread =
  if Thread.isActive thread
  then (Thread.interrupt thread;
        if Thread.isActive thread then Thread.kill thread else ())
  else ()
   
fun parallel_call t fl =
  let
    val _ = parallel_result := NONE
    fun rec_fork f = Thread.fork (fn () => f (), [])
    val threadl = map rec_fork fl
    val rt = Timer.startRealTimer ()
    fun loop () =
      (
      OS.Process.sleep (Time.fromReal 0.2);
      if isSome (!parallel_result) orelse 
         not (exists Thread.isActive threadl) orelse
         Timer.checkRealTimer rt  > Time.fromReal t
      then (app close_thread threadl; !parallel_result)
      else loop ()
      )
  in
    loop ()
  end

(*----------------------------------------------------------------------------
   Launch an ATP
  ----------------------------------------------------------------------------*)

val atp_ref = ref ""

fun launch_atp_mute dir atp t =
  let 
    val cmd = "sh " ^ name_of atp ^ ".sh " ^ int_to_string t ^ " " ^ 
      dir ^ " > /dev/null 2> /dev/null"
    val _ = cmd_in_dir provbin_dir cmd   
    val r = get_lemmas (dir ^ "/status", dir ^ "/out")
  in
    r
  end

fun launch_atp dir atp t =
  let 
    val cmd = "sh " ^ name_of atp ^ ".sh " ^ int_to_string t ^ " " ^ 
      dir ^ " > /dev/null 2> /dev/null"
    val _ = cmd_in_dir provbin_dir cmd   
    val r = get_lemmas (status_of atp, out_of atp)
  in
    if isSome r 
    then 
      (
      atp_ref := name_of atp;
      print_endline ("Proof found by " ^ name_of atp ^ ":");
      print_endline ("  " ^ mk_metis_call (valOf r));
      parallel_result := r 
      )
    else ();
    r
  end

(*----------------------------------------------------------------------------
  HolyHammer
  ----------------------------------------------------------------------------*)  

val notfalse = EQT_ELIM (last (CONJ_LIST 3 NOT_CLAUSES))

val extra_premises = 
  [("truth", TRUTH), ("notfalse", notfalse),
   ("bool_cases_ax", BOOL_CASES_AX), ("eq_ext", EQ_EXT)]

fun translate_write_atp premises cj atp =
  let     
    val new_premises = first_n (npremises_of atp) premises
    val thml = extra_premises @ thml_of_namel new_premises           
    val pb = hh_logt_eval "translate_pb" (translate_pb true thml) cj
    val (axl,new_cj) = name_pb pb
  in
    write_tptp (provdir_of atp) axl new_cj
  end

fun exists_atp atp = 
  exists_file (pathl [provbin_dir, name_of atp])

fun exists_atp_err atp = 
  let val b = exists_file (pathl [provbin_dir, name_of atp]) in
    if not b then print_endline ("No binary for " ^ name_of atp) else ();
    b
  end

val hh_goaltac_cache = ref (dempty goal_compare)

fun hh_pb wanted_atpl premises goal =
  let
    val _ = mkDir_err ttt_code_dir
    val atpl = filter exists_atp_err wanted_atpl
    val cj = list_mk_imp goal
    val _  = app (translate_write_atp premises cj) atpl
    val t1 = !timeout_glob
    val t2 = Real.fromInt t1 + 2.0
    val olemmas = 
      parallel_call t2
        (map 
           (fn x => (fn () => ignore (launch_atp (provdir_of x) x t1)))
           atpl)
  in
    case olemmas of
      NONE => 
        (
        hh_log_eval "Proof status: failure";
        raise ERR "holyhammer" "ATPs could not find a proof"
        )
    | SOME lemmas => 
      let 
        val _ = hh_log_eval "Proof status: success"
        val (stac,tac) = hh_reconstruct lemmas goal 
      in
        print_endline "Minimized proof:";
        print_endline ("  " ^ stac);
        hh_log_eval "Proof reconstructed";
        hh_log_eval stac;
        hh_goaltac_cache := dadd goal (stac,tac) (!hh_goaltac_cache);
        tac
      end
  end

fun clean_goaltac_cache () = hh_goaltac_cache := dempty goal_compare

fun hh_goal goal =
  let val (stac,tac) = dfind goal (!hh_goaltac_cache) in
    print_endline ("Goal already solved by " ^ stac);
    tac
  end
  handle NotFound =>
    let
      val _ = mkDir_err ttt_code_dir
      val atpl = filter exists_atp (!all_atps)
      val (symweight,feav,revdict) = update_thmdata ()
      val n = list_imax (map npremises_of atpl)
      val premises = thmknn_wdep (symweight,feav,revdict) n (fea_of_goal goal)
    in
      hh_pb atpl premises goal
    end

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), [])

fun holyhammer term = hh_goal ([],term)

fun hh goal = (hh_goal goal) goal

fun metis_auto t n goal = 
  let
    val _ = mkDir_err ttt_code_dir
    val (symweight,feav,revdict) = update_thmdata ()
    val premises = thmknn_wdep (symweight,feav,revdict) n (fea_of_goal goal)
    val thml = map snd (thml_of_namel premises)
    val stac = mk_metis_call premises
    val tac = hide_out tactic_of_sml stac
  in
    case hide_out (app_tac t tac) goal of
      SOME _ => 
      let
        val t1 = !minimization_timeout
        val newstac = hide_out (tttMinimize.minimize_stac t1 stac goal) []
      in
        SOME newstac
      end
    | NONE   => NONE    
  end
 
(*----------------------------------------------------------------------------
   Multiple instances of the "eprover" function can be called in parallel.
   Include mk_thm only because of type constraints.
 -----------------------------------------------------------------------------*)

fun translate_write_parallelsafe dir thml0 cj =
  let
    val thml = extra_premises @ thml0       
    val pb = translate_pb false thml cj
    val (axl,new_cj) = name_pb pb
  in
    write_tptp dir axl new_cj
  end

fun eprover t dir terml cj =
  let
    val terml1 = number_list 0 terml
    val terml2 = map (fn (i,x) => ("noTheory." ^ int_to_string i, x)) terml1
    val d = dnew String.compare terml2
    val thml = map (fn (s,x) => (s, mk_thm ([],x))) terml2 
    val _  = translate_write_parallelsafe dir thml cj 
  in
    case launch_atp_mute dir Eprover t of
      SOME l => SOME (map (fn x => dfind x d) l)
    | NONE   => NONE
  end

(*----------------------------------------------------------------------------
   Asynchronous calls to holyhammer in tactictoe.
 -----------------------------------------------------------------------------*)

fun hh_stac pids (symweight,feav,revdict) t goal =
  let
    val cj = list_mk_imp goal
    val premises = 
      thmknn_wdep (symweight,feav,revdict) 128 (fea_of_goal goal)
    val provdir = pathl [provbin_dir,pids]
    val thml = extra_premises @ thml_of_namel premises
    val pb = translate_pb false thml cj
    val (axl,new_cj) = name_pb pb
    val _ = write_tptp provdir axl new_cj
    val olemmas = launch_atp_mute provdir Eprover t
    val _ = (clean_dir provdir; rmDir_err provdir)
  in
    Option.map mk_metis_call olemmas
  end

(*----------------------------------------------------------------------------
  Evaluation
  ----------------------------------------------------------------------------*)  

fun hh_eval_thm atpl bsound (s,thm) =
  let
    val _ = (mkDir_err hh_eval_dir; print_endline s)
    val _ = hh_log_eval ("\nTheorem: " ^ s)
    val goal = if bsound then ([],F) else dest_thm thm
    val (b,premises) = depl_of_thm thm
  in
    if not b 
    then hh_log_eval "broken dependencies" 
    else 
      let val (_,t) = add_time (can (hh_pb atpl premises)) goal in
        hh_log_eval ("Time: " ^ Real.toString t)
      end
  end

fun hh_eval_thy atpl bsound thy = 
  (
  hh_eval_flag := true; 
  thy_ref := thy; 
  mkDir_err hh_eval_dir;
  erase_file (hh_eval_dir ^ "/" ^ thy);
  app (hh_eval_thm atpl bsound) (DB.theorems thy);
  hh_eval_flag := false
  )

(*---------------------------------------------------------------------------
   Export to TT format. Used in the previous holyhammer version.
 ----------------------------------------------------------------------------*)

fun pred_filter pred thy ((name,_),_) =
  let val thypred = map snd (filter (fn x => fst x = thy) pred) in
    mem name thypred
  end

fun export_problem dir premises cj =
  let
    val premises' = map (split_string "Theory.") premises
    (* val _ = print_endline (String.concatWith " " (first_n 10 premises)) *)
    val nsthml1 = filter in_namespace premises
    fun f s = case thm_of_sml (snd (split_string "Theory." s)) of
        SOME (_,thm) => SOME (s,thm)
      | NONE => NONE
    val nsthml2 = hide_out (List.mapPartial f) nsthml1
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct
  in
    clean_dir dir;
    write_problem dir (pred_filter premises') nsthml2 thyl cj;
    write_thydep (dir ^ "/thydep.dep") thyl
  end

fun export_theories dir thyl =
  (
  clean_dir dir;
  write_thyl dir (fn thy => (fn thma => true)) thyl;
  write_thydep (dir ^ "/thydep.dep") thyl
  )

(*----------------------------------------------------------------------------
  load "holyHammer";
  open holyHammer;
  hh_eval_thy [Eprover] false "list"; 
  ----------------------------------------------------------------------------*)  

end
