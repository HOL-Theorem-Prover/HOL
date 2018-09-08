(* ========================================================================== *)
(* FILE          : tttSyntEval.sml                                            *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSyntEval :> tttSyntEval =
struct

open HolKernel boolLib Abbrev tttTools tttSynt tttPredict 
  tttExec tttTermData

val ERR = mk_HOL_ERR "tttSyntEval"

type idict_t = (int * (term * (string, term) Redblackmap.dict)) 

val provers_dir = HOLDIR ^ "/src/holyhammer/provers"

(* --------------------------------------------------------------------------
   Globals
   -------------------------------------------------------------------------- *)

val nb_premises = ref 128

(* --------------------------------------------------------------------------
   Features of term
   -------------------------------------------------------------------------- *)

val fea_cache = ref (dempty Term.compare)

fun fea_of_term_cached tm = 
  dfind tm (!fea_cache) handle NotFound =>
  let val fea = tttFeature.fea_of_goal ([],tm) in
    fea_cache := dadd tm fea (!fea_cache);
    fea
  end
  
fun assoc_fea tml = map (fn x => (x, fea_of_term_cached x)) tml

(* --------------------------------------------------------------------------
   Initialization
   -------------------------------------------------------------------------- *)

datatype role = Axiom | Theorem | Conjecture

val id_compare = list_compare Int.compare

fun init_dicts_thm (order_dict,term_dict,role_dict) nthy role (name,thm) =
  let 
    val nthm = depnumber_of_thm thm
    val thml = CONJUNCTS (SPEC_ALL thm)
    val nthml = number_list 0 thml
    fun insert_thm (nconj,x) =
      let 
        val tm = (concl o GEN_ALL o DISCH_ALL) x
        val id = [nthy,nthm,nconj]
      in
        if dmem tm (!term_dict) then () else
        (
        order_dict := dadd id tm (!order_dict);
        term_dict  := dadd tm id (!term_dict);
        role_dict  := dadd tm role (!role_dict)
        )
      end
  in
    app insert_thm nthml
  end

fun init_dicts_thy state (nthy,thy) =
  let fun f role (name,thm) = init_dicts_thm state nthy role (name,thm) in
    app (f Theorem) (DB.theorems thy);
    app (f Axiom) (DB.axioms thy @ DB.definitions thy)
  end

fun init_dicts n =
  let
    val _ = clean_dir (!ttt_synt_dir)
    val order_dict = ref (dempty id_compare)
    val term_dict  = ref (dempty Term.compare)
    val role_dict  = ref (dempty Term.compare)
    val thyl0 = first_n n (sort_thyl (ancestry (current_theory ())))
    val thyl1 = number_list 0 thyl0
    val state = (order_dict,term_dict,role_dict)
  in
    app (init_dicts_thy state) thyl1;
    (!order_dict, !term_dict, !role_dict)
  end

(* --------------------------------------------------------------------------
   Inserting conjectures in dictionnaries
   -------------------------------------------------------------------------- *)

fun after_id_aux odict n id =
  if dmem (id @ [n]) odict
  then after_id_aux odict (n + 1) id  
  else id @ [n]

fun after_id order_dict id = after_id_aux order_dict 0 id 

fun insert_cj (order_dict,term_dict,role_dict) (tm,lemmas) =  
  if dmem tm (!term_dict) then () else
  let 
    val idl         = map (fn x => dfind x (!term_dict)) lemmas
    val lastid      = last (dict_sort id_compare idl)
    val id          = after_id (!order_dict) lastid
  in
    order_dict := dadd id tm (!order_dict);
    term_dict  := dadd tm id (!term_dict);
    role_dict  := dadd tm Conjecture (!role_dict)
  end

fun insert_cjl (odict,tdict,rdict) cjlp = 
  let 
    val _ = msg_synt cjlp "to be inserted in the dicts"
    val state as (order_dict, term_dict, role_dict) = (ref odict, ref tdict, ref rdict)
  in
    app (insert_cj state) cjlp;
    (!order_dict, !term_dict, !role_dict)
  end

(* --------------------------------------------------------------------------
   Reading the result of launch_eprover_parallel
   -------------------------------------------------------------------------- *) 

fun read_result pid_idict_list pid_result_list =
  let 
    val pid_result_dict = dnew Int.compare pid_result_list
    fun read_result_one (pid,(cj,idict)) = case dfind pid pid_result_dict of
      SOME l => (pid, (cj, SOME (map (fn x => dfind x idict) l)))
    | NONE   => (pid, (cj, NONE))
  in
    map read_result_one pid_idict_list
  end

fun roleterm_to_string rdict tm = 
  (
  case dfind tm rdict of
    Conjecture => "Conjecture"
  | Theorem    => "Theorem"
  | Axiom      => "Axiom"
  ) 
  ^ ": " ^ term_to_string tm

fun write_result rdict file l = 
  let
    val _ = log_synt ("writing result in " ^ file)
    fun f (pid,(cj,ro)) = 
      "Pid: " ^ int_to_string pid ^ "\n" ^
      "Target: " ^ term_to_string cj ^ "\n" ^
      (
      case ro of
        SOME l => 
        "Proof:\n  " ^ String.concatWith "\n  "
         (map (roleterm_to_string rdict) l) ^ "\n"
      | NONE => "Failure\n"
      )
  in
    writel file (map f l)
  end

fun is_nontrivial x = case x of
    SOME [] => false
  | NONE    => false
  | _        => true

(* --------------------------------------------------------------------------
   Proving conjectures
   -------------------------------------------------------------------------- *) 

fun prove_predict (symweight,tmfea) cj =
  (tmknn (!nb_premises) (symweight,tmfea) (fea_of_term_cached cj), cj)

fun prove_write pdir transf exportf tml cjl =
  let
    val tmfea = time_synt "generating features" assoc_fea tml
    val symweight = learn_tfidf tmfea
    val pbl = time_synt "predict" (map (prove_predict (symweight,tmfea))) cjl
    val _ = time_synt "translate" (map transf) tml
  in
    time_synt "export" (mapi (exportf pdir)) pbl
  end

fun prove_result rdict pl0 = 
  let 
    val pl1 = filter (isSome o snd o snd) pl0;
    val _ = msg_synt pl1 "proven conjectures";
    val pl2 = filter (is_nontrivial o snd o snd) pl0;
    val _ = msg_synt pl2 "nontrivial conjectures";
    val _ = write_result rdict (!ttt_synt_dir ^ "/prove_nontrivial") pl2
  in
    map (fn (a,b) => (a, valOf b)) (map snd pl2)
  end
 
fun prove_main rdict pdir ncores timelimit 
    transf exportf launchf tml cjl =
  let
    val _ = cleanDir_rec pdir
    val _ = msg_synt tml "terms to select from"
    val pid_idict_list = prove_write pdir transf exportf tml cjl 
    val pidl = map fst pid_idict_list
    val _    = msg_synt pidl "proving tasks"
    val pid_result_list = time_synt "launchf" 
      (launchf pdir ncores pidl) timelimit
    val pl0 = read_result pid_idict_list pid_result_list
  in
    prove_result rdict pl0
  end

(* --------------------------------------------------------------------------
   Evaluating conjectures
   -------------------------------------------------------------------------- *) 

fun eval_predict (odict,tdict,rdict) tm =
  let
    val tml0 = dkeys tdict
    val tmid = dfind tm tdict
    fun is_older x = id_compare (dfind x tdict,tmid) = LESS
    val tml1 = filter is_older tml0
    val tmfea = assoc_fea tml1
    val symweight = learn_tfidf tmfea
    val predl = tmknn (!nb_premises) (symweight,tmfea) (fea_of_term_cached tm)
    val cjl = filter (fn x => dfind x rdict = Conjecture) predl
  in
    SOME (predl,tm)
  end

fun eval_write pdir dicts transf exportf tml =
  let
    val pbl = time_synt "predict" (List.mapPartial (eval_predict dicts)) tml
    val _ = time_synt "translate" (map transf) tml (* update the cache *)
  in
    time_synt "export" (mapi (exportf pdir)) pbl
  end

fun eval_result rdict el0 =
  let
    val el1 = filter (isSome o snd o snd) el0
    val _ = msg_synt el1 "proven theorems"
    val el2 = filter (is_nontrivial o snd o snd) el0
    val _ = msg_synt el2 "nontrivial theorems"
    val _   = write_result rdict (!ttt_synt_dir ^ "/" ^ "eval_nontrivial") el0
    fun is_conjecture x = dfind x rdict = Conjecture
    fun f (i,(a,b)) = (i,(a, filter is_conjecture (valOf b)))
    val el3 = map f el2
    val el4 = filter (not o null o snd o snd) el3
    val _ = msg_synt el4 "theorems proven using at least one conjecture"
  in
    (map snd el4, map (fst o snd) el1)
  end

fun write_usefulcj el =
  let
    val ecjl0 = List.concat (map snd el)
    val ecjl1 = 
      dict_sort compare_imax (dlist (count_dict (dempty Term.compare) ecjl0))
    fun string_of_ecjl (tm,n) = 
      int_to_string n ^ "\n" ^ term_to_string tm ^ "\n"
  in
    writel (!ttt_synt_dir ^ "/useful_conjectures") (map string_of_ecjl ecjl1)
  end

fun eval_main pdir ncores timelimit (odict,tdict,rdict) 
    transf exportf launchf =
  let
    val _ = cleanDir_rec pdir
    val tml0 = dkeys tdict
    val tml1 = filter (fn x => dfind x rdict = Theorem) tml0  
    val _ = msg_synt tml1 "theorems to be proven"
    val pid_idict_list = 
      eval_write pdir (odict,tdict,rdict) transf exportf tml1
    val pidl = map fst pid_idict_list
    val pid_result_list = time_synt "launchf" 
      (launchf pdir ncores pidl) timelimit
    val el0 = read_result pid_idict_list pid_result_list
    val (el1, proven) = eval_result rdict el0
    val rate = approx 2 (int_div (length proven) (length tml1) * 100.0)
    val _ = log_synt (Real.toString rate ^ " success rate")
    val provendict = count_dict (dempty Term.compare) proven
    val unproven = filter (fn x => not (dmem x provendict)) tml1
  in
    write_usefulcj el1; (el1, proven, unproven)
  end

end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;

(* Fixed parameters *)
val provers_dir = HOLDIR ^ "/src/holyhammer/provers"
val pdir_eval = provers_dir ^ "/parallel_eval";
val pdir_prove = provers_dir ^ "/parallel_prove";
val pdir_baseline = provers_dir ^ "/parallel_baseline";
val exportf  = export_pb;
val launchf  = eprover_parallel;
val transf   = hhTranslate.cached_translate;

(* Parameters *)
val _ = show_types := true;
  (* conjecturing *)
val _ = conjecture_limit := 100000;
val _ = patsub_flag := false;
val _ = concept_flag := false;
val _ = concept_threshold := 4;
val ncj_max  = 1000;
  (* proving *)
val nthy_max = 2; 
val _ = nb_premises := 128;
val ncores    = 3;
val timelimit = 5;
  (* output *)
val run_id = "baseline";
val _ = ttt_synt_dir := tactictoe_dir ^ "/log_synt/" ^ run_id;
val _ = mkDir_err (tactictoe_dir ^ "/log_synt");

(* Initialization *)
val dicts_org as (odict_org, tdict_org, rdict_org)  = init_dicts nthy_max;
val tmlorg = dkeys tdict_org;

(* Baseline *)
val (eluseful, proven, unproven) = 
  eval_main pdir_eval ncores timelimit dicts_org transf exportf launchf;
val _ = export_tml (!ttt_synt_dir ^ "/proven_thms") proven;
val _ = export_tml (!ttt_synt_dir ^ "/unproven_thms") unproven;


(* Generating conjectures *)
val cjl0 = conjecture tmlorg;

val cjl1 = first_n ncj_max cjl0;

(* Proving conjectures *)
val pl = prove_main rdict_org pdir_prove 
  ncores timelimit exportf launchf tmlorg cjl1;

(* Updating the dictionnaries *)
val dicts_new as (odict_new, tdict_new, rdict_new) = insert_cjl dicts_org pl;

(* Evaluate conjectures *)
val el = eval_main pdir_eval ncores timelimit dicts_new exportf launchf;

Debug 
val tm = concl pred_setTheory.UNION_DEF;
val cj = subst [{redex = ``$\/``,residue = ``$/\``}] tm;
val d = trans_write_tmlcj 0 ([tm],cj);
val e = launch_eprover_parallel 1 [0] 5;

load "hhTranslate";
open hhTranslate tttTools;
val tml = map (concl o DISCH_ALL o GEN_ALL o snd) (DB.thms "list");
val tml' = first_n 100 tml;
val ntml' = number_list 0 tml';
val (r,t) = add_time (parallel_translate 3) tml';
val (r',t') = add_time (map translate) ntml';



2) Increase the matching possibility from patterns.
   Think of including subterms match.

1) Increase the coverage using generalization techniques.
   Do statistics from the point of view of patterns.
2) Only allow N conjectures per theorems.
   Try most frequent subsitutions first. Then when applicable 
   the ratio of conjecture / Theorem should guide the choice of the 
   substitution and theorems.

   
2) Try to prove theorems without conjectures.
   Do the re-ordering on the theorems proven.
3) Think about how to implement the feedback loop. 
   (features and machine learning)
4) Issue: too many proving tasks?

5) Add conceptualization.

6) Authorizes in the creation only things that come from the past

*)

