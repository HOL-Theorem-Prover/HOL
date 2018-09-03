(* ========================================================================== *)
(* FILE          : tttSyntEval.sml                                            *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSyntEval :> tttSyntEval =
struct

open HolKernel boolLib Abbrev tttTools tttSynt tttPredict tttExec

val ERR = mk_HOL_ERR "tttSyntEval"

type idict_t = (int * (term * (string, term) Redblackmap.dict)) 

val parallel_dir = HOLDIR ^ "/src/holyhammer/provers/parallel"

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
    val _ = clean_dir ttt_synt_dir
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

fun write_result file l = 
  let 
    val _ = log_synt ("writing result in " ^ file)
    fun f (pid,(cj,ro)) = 
      "Pid: " ^ int_to_string pid ^ "\n" ^
      "Target: " ^ term_to_string cj ^ "\n" ^
      (
      case ro of
        SOME l => 
        "Proof:\n  " ^ String.concatWith "\n  " (map term_to_string l) ^ "\n"
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
  (tmknn 16 (symweight,tmfea) (fea_of_term_cached cj), cj)

fun prove_write exportf tml cjl =
  let
    val _ = log_synt "generating features"
    val tmfea = assoc_fea tml
    val symweight = learn_tfidf tmfea
    val _ = log_synt "predict"
    val tmlcjl = map (prove_predict (symweight,tmfea)) cjl
    val _ = log_synt "export"
    fun f i x =
      (  
      log_synt_file "log_prove_write" 
        ((int_to_string i) ^ " " ^ term_to_string (snd x));
      exportf i x
      ) 
  in
    mapi f tmlcjl
  end

fun prove_result pl0 = 
  let 
    val pl1 = filter (isSome o snd) pl0;
    val _ = msg_synt pl1 "proven conjectures";
    val pl2 = filter (is_nontrivial o snd) pl0;
    val _ = msg_synt pl2 "nontrivial conjectures";
  in
    map (fn (a,b) => (a, valOf b)) pl2
  end
 
fun prove_main ncores timelimit exportf launchf tml cjl =
  let
    val _ = cleanDir_rec parallel_dir
    val _ = msg_synt tml "terms to select from"
    val pid_idict_list = prove_write exportf tml cjl 
    val pidl = map fst pid_idict_list
    val _    = msg_synt pidl "proving tasks"
    val pid_result_list = launchf ncores pidl timelimit
    val pl0 = read_result pid_idict_list pid_result_list
    val _ = write_result (ttt_synt_dir ^ "/proofs_prove") pl0
  in
    prove_result (map snd pl0)
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
    val predl = tmknn 16 (symweight,tmfea) (fea_of_term_cached tm)
    val cjl = filter (fn x => dfind x rdict = Conjecture) predl
  in
    if null cjl then NONE else SOME (predl,tm)
  end

fun eval_write dicts exportf tml =
  let
    val _   = log_synt "predict"
    val pbl = List.mapPartial (eval_predict dicts) tml
    val _   = log_synt "export"
    fun f i x =
      (  
      log_synt_file "log_eval_write" 
        ((int_to_string i) ^ " " ^ term_to_string (snd x));
      exportf i x
      )
  in
    mapi exportf pbl
  end

fun eval_result rdict el0 =
  let
    val el1 = filter (isSome o snd) el0
    val _ = msg_synt el1 "proven theorems"
    val el2 = filter (is_nontrivial o snd) el0
    val _ = msg_synt el2 "nontrivial theorems"
    fun is_conjecture x = dfind x rdict = Conjecture
    fun f (a,b) = (a, filter is_conjecture (valOf b))
    val el3 = map f el2
    val _ = msg_synt el3 "theorems proven using at least one conjecture"
  in
    el3
  end

fun write_usefulcj el =
  let
    val ecjl0 = List.concat (map snd el)
    val ecjl1 = dict_sort compare_imax (dlist (count_dict (dempty Term.compare) ecjl0))
    fun string_of_ecjl (tm,n) = int_to_string n ^ "\n" ^ term_to_string tm ^ "\n"
  in
    writel (ttt_synt_dir ^ "/useful_conjectures") (map string_of_ecjl ecjl1)
  end

fun eval_main ncores timelimit (odict,tdict,rdict) exportf launchf =
  let
    val _ = cleanDir_rec parallel_dir
    val tml0 = dkeys tdict
    val tml1 = filter (fn x => dfind x rdict = Theorem) tml0  
    val _ = msg_synt tml1 "theorems to be proven"
    val pid_idict_list = eval_write (odict,tdict,rdict) exportf tml1
    val pidl = map fst pid_idict_list
    val _ = msg_synt pidl "theorems with conjectures as predictions"
    val pid_result_list = launchf ncores pidl timelimit
    val el0 = read_result pid_idict_list pid_result_list
    val _   = write_result (ttt_synt_dir ^ "/" ^ "proofs_eval") el0
    val el1 = eval_result rdict (map snd el0)
  in
    write_usefulcj el1; el1
  end

(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *) 

fun string_of_tml tml =
  ("  " ^ String.concatWith "\n  " (map term_to_string tml) ^ "\n")

fun string_of_subst sub = 
  let fun f (a,b) = "(" ^ term_to_string a ^ ", " ^ term_to_string b ^ ")" in
    "[" ^ String.concatWith ", " (map f sub) ^ "]"
  end

fun write_subdict subdict =
  let
    val _ = 
     log_synt ("writing subdict " ^ (int_to_string (dlength subdict)))
    val l = dlist subdict
    fun f (sub, (cjl,score)) = String.concatWith "\n" 
      [
      "Substitution:",
      string_of_subst sub,
      "  Score: " ^ Real.toString score,
      "  Conjectures:",
      string_of_tml cjl
      ]
  in
    writel (ttt_synt_dir ^ "/subdict") (map f l)
  end
       
fun write_origindict origindict = 
  let
    val _ = 
      log_synt ("writing origindict " ^ (int_to_string (dlength origindict)))
    val l = dlist origindict
    fun g (sub,tm) = String.concatWith "\n  "
      [
      "  Substitution:",
      string_of_subst sub,
      "From: ",
      term_to_string tm
      ] 
    fun f (cj,subtml) = String.concatWith "\n" 
       (["Conjecture:",
        term_to_string cj] @
        map g subtml)  
  in
    writel (ttt_synt_dir ^ "/origindict") (map f l)
  end

end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;

(* Parameters *)
val ncores = 40; val timelimit = 5;
val nthy = 1000; val ncj = 100000;
val exportf = trans_write_tmlcj;
val launchf = launch_eprover_parallel;
val _ = freq_limit := 4;

(* Initialization *)
val dicts_org as (odict_org, tdict_org, rdict_org)  = init_dicts nthy;
val tmlorg = dkeys tdict_org;

(* Generating conjectures *)
val (cjl0, subdict, origindict) = gen_cjl tmlorg;
val _ = write_subdict subdict;
val _ = write_origindict origindict;
val cjl1 = first_n ncj cjl0;

(* Proving conjectures *)
val pl = prove_main ncores timelimit exportf launchf tmlorg cjl1;

(* Updating the dictionnaries *)
val dicts_new as (odict_new, tdict_new, rdict_new) = insert_cjl dicts_org pl;

(* Evaluate conjectures *)
val el = eval_main ncores timelimit dicts_new exportf launchf;

(* Todo 
+ make separate directories for parallel calls.
+ make a simple function for testing eprover translation on some input.
*)

(* Debug 
val tm = concl pred_setTheory.UNION_DEF;
val cj = subst [{redex = ``$\/``,residue = ``$/\``}] tm;
val d = trans_write_tmlcj 0 ([tm],cj);
val e = launch_eprover_parallel 1 [0] 5;
*)
*)

