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
   Initialization. Remove duplicated theorems and keep the oldest one.
   -------------------------------------------------------------------------- *)

datatype role = Axiom | Theorem

val id_compare = list_compare Int.compare
val name_dict = ref (dempty (Term.compare))


fun init_dicts_thm (order_dict,term_dict,role_dict) (nthy,thy) role (name,thm) =
  let 
    val nthm = depnumber_of_thm thm
    val thml = CONJUNCTS (SPEC_ALL thm)
    val nthml = number_list 0 thml
    fun insert_thm (nconj,x) =
      let 
        val tm = (concl o GEN_ALL o DISCH_ALL) x
        val id = [nthy,nthm,nconj]
        val newname = String.concatWith "." 
          (thy :: name :: (map int_to_string id))
      in
        if dmem tm (!term_dict) then () else
        (
        name_dict  := dadd tm newname (!name_dict);
        order_dict := dadd id tm (!order_dict);
        term_dict  := dadd tm id (!term_dict);
        role_dict  := dadd tm role (!role_dict)
        )
      end
  in
    app insert_thm nthml
  end

fun init_dicts_thy state (nthy,thy) =
  let fun f role (name,thm) = init_dicts_thm state 
    (nthy,thy) role (name,thm) in
    app (f Theorem) (DB.theorems thy);
    app (f Axiom) (DB.axioms thy @ DB.definitions thy)
  end

fun init_dicts () =
  let
    val _ = rmDir_rec (!ttt_synt_dir)
    val _ = mkDir_err (!ttt_synt_dir)
    val order_dict = ref (dempty id_compare)
    val term_dict  = ref (dempty Term.compare)
    val role_dict  = ref (dempty Term.compare)
    val thyl0 = sort_thyl (ancestry (current_theory ()))
    val thyl1 = number_list 0 thyl0
    val state = (order_dict,term_dict,role_dict)
  in
    app (init_dicts_thy state) thyl1;
    (!order_dict, !term_dict, !role_dict)
  end

(* --------------------------------------------------------------------------
   Analysis of the results
   -------------------------------------------------------------------------- *) 

fun write_result file l = 
  let
    val _ = log_synt ("writing result in " ^ file)
    fun f (is_cj,(cj,ro)) = 
      let fun role tm = if is_cj tm
        then "Conjecture: " ^ term_to_string tm
        else "Theorem: " ^ 
             (dfind tm (!name_dict) handle NotFound => "Error") ^ " " ^
             term_to_string tm
      in
        "Target: " ^ term_to_string cj ^ "\n" ^
        (
        case ro of
          SOME l => 
          "Proof:\n  " ^ String.concatWith "\n  "
           (map role l) ^ "\n"
        | NONE => "Failure\n"
        )
      end
  in
    writel file (map f l)
  end

fun write_result_cj file l = 
  let
    val _ = log_synt ("writing result in " ^ file)
    fun f (cj,ro) = 
      "Conjecture: " ^ term_to_string cj ^ "\n" ^ (
      case ro of
        SOME l => "Proof:\n  " ^ String.concatWith "\n  "
                  (map term_to_string l) ^ "\n"
      | NONE => "Failure\n")
  in
    writel file (map f l)
  end

fun is_nontrivial x = case x of
    SOME [] => false
  | NONE    => false
  | _        => true

(* --------------------------------------------------------------------------
   Problem preparation and postprocessing
   -------------------------------------------------------------------------- *) 

fun find_oldertml tdict tm =
  let
    val tml0 = dkeys tdict
    val tmid = dfind tm tdict
    fun is_older x = id_compare (dfind x tdict,tmid) = LESS
  in
    filter is_older tml0
  end

fun prepredict tml tm =
  let val tmfea = assoc_fea tml in (learn_tfidf tmfea, tmfea) end

fun read_result pid_idict_list pid_result_list =
  let 
    val pid_result_dict = dnew Int.compare pid_result_list
    fun read_result_one (pid,(cj,idict)) = case dfind pid pid_result_dict of
      SOME l => (pid, (cj, SOME (map (fn x => dfind x idict) l)))
    | NONE   => (pid, (cj, NONE))
    val l = map read_result_one pid_idict_list
    fun cmp (a,b) = Int.compare (fst a, fst b)
  in
    map snd (dict_sort cmp l)
  end

fun prove_pbl pdir ncores tim exportf launchf pbl =
  let 
    val _ = cleanDir_rec pdir
    val pid_idict_list = time_synt "export" 
      (mapi (exportf pdir)) pbl
    val pidl = map fst pid_idict_list
    val _  = msg_synt pidl "proving tasks"
    val pid_result_list = time_synt "launchf" 
      (launchf pdir ncores pidl) tim
  in
    read_result pid_idict_list pid_result_list
  end

(* --------------------------------------------------------------------------
   Proving problem.
   -------------------------------------------------------------------------- *) 

fun create_cjl pdir ncores tim conjf exportf launchf tdict tm =
  let 
    val name = dfind tm (!name_dict) handle NotFound => "Error"
    val dir  = (!ttt_synt_dir) ^ "/proofs_cj"
    val _    = mkDir_err dir
    val file = dir ^ "/" ^ name
    val _ = log_synt (term_to_string tm)
    val tml = find_oldertml tdict tm
    val (symweight,tmfea) = prepredict tml tm
    val predl = tmknn 64 (symweight,tmfea) (fea_of_term_cached tm)
    val cjl   = conjf 30000 (tm :: tml)
    val (cjsymweight,cjtmfea) = prepredict cjl tm
    val cjl640  = tmknn 640 (cjsymweight,cjtmfea) (fea_of_term_cached tm)
    fun mk_pb x = (tmknn 64 (symweight,tmfea) (fea_of_term_cached x), x)
    val pbl   = time_synt "predict" (parmap ncores mk_pb) cjl640
    val cjpl0 = prove_pbl pdir ncores tim exportf launchf pbl
    val _     = write_result_cj file cjpl0
    val cjpl1 = filter (is_nontrivial o snd) cjpl0 
    val _     = msg_synt cjpl1 "non trivial conjectures"
    val cjpl2 = map fst (first_n 64 cjpl1)
    fun is_cj x = mem x cjpl2 andalso not (mem x predl)
  in
    (is_cj,(predl @ cjpl2, tm))
  end

fun one_in_n n start l = case l of
    [] => []
  | a :: m => if start mod n = 0 
              then a :: one_in_n n (start + 1) m
              else one_in_n n (start + 1) m

fun success_rate l1 l2 =
  let val rate = approx 2 (int_div (length l1) (length l2) * 100.0) in
    log_synt (Real.toString rate ^ " success rate")
  end

(* --------------------------------------------------------------------------
   Re-proving theorems using conjectures
   -------------------------------------------------------------------------- *) 

fun reprove nfreq conjf exportf launchf pdir ncores tim (odict,tdict,rdict) =
  let
    val tml0 = filter (fn x => dfind x rdict = Theorem) (dkeys tdict)
    (* add filter for already proven theorem *)
    val tml1 = one_in_n nfreq 0 tml0
    val _ = msg_synt tml1 "theorems to be re-proven"
    val pbl = map (create_cjl pdir ncores tim conjf exportf launchf tdict) tml1
    val (l1,l2) =  split pbl
    (* proving theorems *)
    val result0 = prove_pbl pdir ncores tim exportf launchf l2
    val result1 = combine (l1,result0)
    val _       = write_result (!ttt_synt_dir ^ "/proofs") result1
    (* success rate *)
    val (proven,unproven) = partition (isSome o snd) result0
    val _ = success_rate proven tml1
    val _ = export_tml (!ttt_synt_dir ^ "/proven_thms") 
      (map fst proven)
    val _ = export_tml (!ttt_synt_dir ^ "/unproven_thms") 
      (map fst unproven)    
  in
    map fst proven
  end


end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;

(* Fixed parameters *)
val provers_dir = HOLDIR ^ "/src/holyhammer/provers"
val pdir_eval = provers_dir ^ "/parallel_eval";
val exportf  = export_pb;
val launchf  = eprover_parallel;
val transf   = hhTranslate.cached_translate;
val conjf = tttSynt.conjecture
(* Parameters *)
val _ = show_types := true;
(* proving *)
val ncores = 40;
val tim = 1;
val nfreq = 10;
(* output *)
val run_id = "onein10";
val _ = ttt_synt_dir := tactictoe_dir ^ "/log_synt/" ^ run_id;

(* Initialization *)
val dicts = init_dicts ();

(* Re-proving theorems *)
val proven = reprove nfreq conjf exportf launchf pdir_eval ncores tim dicts;

(* *)
val baseline_file = tactictoe_dir ^ "/log_synt/baseline/proven_thms";
val baselineproven  = import_tml baseline_file;
val l = list_diff proven baselineproven;

(* todo *)
1) check for variable permutations.
2) include the conjecture in the list of terms conjectures are created from.

*)

