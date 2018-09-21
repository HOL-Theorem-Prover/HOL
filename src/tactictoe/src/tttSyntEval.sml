(* ========================================================================== *)
(* FILE          : tttSyntEval.sml                                            *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSyntEval :> tttSyntEval =
struct

open HolKernel boolLib Abbrev tttTools tttSynt tttPredict 
  tttExec tttTermData tttFeature

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

fun prepredict tml =
  let val tmfea = assoc_fea tml in (learn_tfidf tmfea, tmfea) end

fun assoc_syntfea tml = 
  map (fn x => (x, syntfea_of_term x)) tml

fun synt_prepredict tml =
  let val tmfea = assoc_syntfea tml in (learn_tfidf tmfea, tmfea) end

fun is_interesting tm = 
  let val tm' = snd (strip_forall tm) in
    term_size tm' < 20 andalso null (find_terms is_abs tm')  
  end

(* --------------------------------------------------------------------------
   Metis prover. Should call metis from the future as
   tactictoe is in the build sequence.
   -------------------------------------------------------------------------- *) 

fun mprove tmax premises tm =
  let
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = (valOf (!tttExec.metis_tac_glob)) thml
    val r = tttExec.app_tac tmax tac (mk_goal tm)
  in
    r = SOME []
  end

fun is_trivial tmax tm = mprove tmax [] tm

fun time_mprove tmax premises tm =
  let
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = (valOf (!tttExec.metis_tac_glob)) thml
    val (r,t) = add_time (tttExec.app_tac tmax tac) (mk_goal tm)
  in
    if r = SOME [] then SOME t else NONE
  end

fun minimize_aux t l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if mprove t (l1 @ m) tm
    then minimize_aux t l1 m tm
    else minimize_aux t (a :: l1) m tm
    
fun miniprove t tml tm = 
  if mprove t tml tm 
  then SOME (minimize_aux t [] tml tm)
  else NONE

(* --------------------------------------------------------------------------
   Initialization. Remove duplicated theorems and keep the oldest one.
   -------------------------------------------------------------------------- *)

datatype role = Axiom | Theorem

val id_compare = list_compare Int.compare
val name_dict = ref (dempty (Term.compare))

fun init_dicts_thm term_dict (nthy,thy) role (name,thm) =
  let 
    val nthm = depnumber_of_thm thm
    val thml = CONJUNCTS (SPEC_ALL thm)
    val nthml = number_list 0 thml
    fun insert_thm (nconj,x) =
      let 
        val tm_aux = (concl o SPEC_ALL o DISCH_ALL) x
        val tm = rename_bvarl (fn _ => "") 
          (list_mk_forall (free_vars_lr tm_aux, tm_aux))
        val id = [nthy,nthm,nconj]
        val newname = String.concatWith "." 
          (thy :: name :: (map int_to_string id))
      in
        if dmem tm (!term_dict) orelse not (is_interesting tm) then () else
        (
        name_dict  := dadd tm newname (!name_dict);
        term_dict  := dadd tm (id,role) (!term_dict)
        )
      end
  in
    app insert_thm nthml
  end

fun init_dicts_thy term_dict (nthy,thy) =
  let fun f role (name,thm) = init_dicts_thm term_dict
    (nthy,thy) role (name,thm) in
    app (f Theorem) (DB.theorems thy);
    app (f Axiom) (DB.axioms thy @ DB.definitions thy)
  end

fun init_dicts () =
  let
    val _ = rmDir_rec (!ttt_synt_dir)
    val _ = mkDir_err (!ttt_synt_dir)
    val _ = name_dict := dempty Term.compare
    val term_dict  = ref (dempty Term.compare)
    val thyl0 = sort_thyl (ancestry (current_theory ()))
  in
    app (init_dicts_thy term_dict) (number_list 0 thyl0);
    !term_dict
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

fun get_accl tdict target =
  let
    val tml0 = dkeys tdict
    val targetid = fst (dfind target tdict)
    fun is_older x = id_compare (fst (dfind x tdict),targetid) = LESS
  in
    filter is_older tml0
  end

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

val timeout_big = 0.1
val timeout = 0.02

fun usefulness t minil target (cj,t1) =
  case time_mprove t (cj :: minil) target of
    SOME t2 => SOME (cj,(t1,t2))
  | NONE   => NONE

fun provable t minil cj = 
  case time_mprove t minil cj of
    SOME t1 => SOME (cj,t1)
  | NONE   => NONE

fun is_useful torg (cj,(t1,t2)) = t1+t2 < torg

fun optimize torg minil target =
  let
    val sreal = Real.toString o approx 5
    val feas = mk_fast_set Int.compare 
      (List.concat (map syntfea_of_term (target :: minil)))
    fun filterf n accl = 
      tmknn n (synt_prepredict accl) feas
    fun filterf n accl = first_n n (shuffle accl)
    val cjl0 = cjenum 20 100 filterf minil target   
    val _   = msg_synt cjl0 "conjectures"
    val cjl1 = first_n 1000 cjl0
    val cjl2 = filter (not o (is_trivial 0.01)) cjl1
    val _ = msg_synt cjl2 "non-trivial conjectures"
    val cjl3 = List.mapPartial (provable timeout minil) cjl2
    val _ = msg_synt cjl3 "provable conjectures"
    val cjl4 = List.mapPartial (usefulness timeout minil target) cjl3
    val cjl4' = filter (is_useful torg) cjl4
    val _ = msg_synt cjl4' "useful conjectures"
    fun cmp ((x,(a,b)),(y,(c,d))) = Real.compare (a+b,c+d)
    val cjl5 = dict_sort cmp cjl4
    val _ = case cjl5 of 
      (cj,(t1,t2)) :: m => 
      (
      log_synt ("Most useful conjecture: " ^ term_to_string cj);
      if t1+t2 < torg 
      then log_synt ("Improvement: " ^ sreal (torg - (t1+t2)))
      else ()
      ;
      log_synt ("Times: " ^ String.concatWith " " (map sreal [t1+t2,t1,t2]))
      )
      | [] => ()
  in
    ()
  end

fun create_cjl_first tdict target =
  let
    val name = dfind target (!name_dict) handle NotFound => "Error"
    val _ = log_synt (name ^ ": " ^ term_to_string target)
    val accl = get_accl tdict target
    val targetfea = fea_of_term_cached target
    val predl = tmknn 16 (prepredict accl) targetfea
  in
    case miniprove timeout_big predl target of
      SOME minil =>
      (
      log_synt ("Proof: " ^ String.concatWith "\n" (map term_to_string minil));
      if null minil then log_synt "Trivial" else
        (
        case time_mprove timeout minil target of      
          SOME torg => 
          (log_synt ("Time: " ^ Real.toString torg);
           optimize torg minil target)
        | NONE      => log_synt "No reconstruction in 0.02 seconds"
        )
      )
    | NONE => log_synt "Unknown in 0.1 seconds"
  end

(*
fun create_cjl pdir ncores tim conjf exportf launchf tdict target =
  let 
    val name = dfind target (!name_dict) handle NotFound => "Error"
    val dir  = (!ttt_synt_dir) ^ "/proofs_cj"
    val _    = mkDir_err dir
    val file = dir ^ "/" ^ name
    val _ = log_synt (name ^ ": " ^ term_to_string target)
    val tml = get_accl (dkeys tdict) target
    val (symweight,tmfea) = prepredict tml target
    val predl = tmknn 32 (symweight,tmfea) (fea_of_term_cached tm)
    (* targeted conjecturing *)
    fun filterf n tml = 
      let val (symweight,tmfea) = prepredict tml tm in
        tmknn 16 (symweight,tmfea) (fea_of_term_cached target)
      end
    val cjl = cjenum 40 filterf predl target
    val (cjsymweight,cjtmfea) = prepredict cjl tm
    val cjl160  = tmknn 160 (cjsymweight,cjtmfea) (fea_of_term_cached tm)
    fun mk_pb x = (tmknn 16 (symweight,tmfea) (fea_of_term_cached x), x)
    val pbl   = time_synt "predict" (parmap ncores mk_pb) cjl160
    val cjpl0 = prove_pbl pdir ncores tim exportf launchf pbl
    val _     = write_result_cj file cjpl0
    val cjpl1 = filter (is_nontrivial o snd) cjpl0 
    val _     = msg_synt cjpl1 "non trivial conjectures"
    val cjpl2 = map fst (first_n 64 cjpl1)
    fun is_cj x = mem x cjpl2 andalso not (mem x predl)
  in
    (is_cj,(predl @ cjpl2, tm))
  end
*)

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

fun targeted_conjectures nfreq tdict =
  let
    val tml0 = filter (fn x => snd (dfind x tdict) = Theorem) (dkeys tdict)
    val tml1 = one_in_n nfreq 0 tml0
    val _ = msg_synt tml1 "theorems to be re-proven"
    val _ = log_synt "creating conjectures"
  in
    app (ignore o create_cjl_first tdict) tml1
  end

val i = ref 0

fun string_of_aimterm sep x = 
  if is_var x then fst (dest_var x)
          else if is_comb x then 
            let val (a,bl) = strip_comb x in
              "(" ^ String.concatWith sep (map (string_of_aimterm sep) (a :: bl)) ^ ")"
            end
          else raise ERR "string_of_aimterm" ""


fun cj_target tml target =
  let
    val dir = tactictoe_dir ^ "/aimtermknn" 
    val file = dir ^ "/" ^ string_of_aimterm "_" target
    val dtest = count_dict (dempty Term.compare) tml
    val _ = (incr i; 
      log_synt (int_to_string (!i) ^ " " ^ term_to_string target)) 
    val predl = tmknn 16 (synt_prepredict tml) 
      (syntfea_of_term target)
    val feas = mk_fast_set Int.compare 
      (List.concat (map syntfea_of_term (target :: predl)))
    fun filterf n x = tmknn n (synt_prepredict x) feas
    val l0 = aimcj 20 100 filterf predl target
    val l1 = filter (fn x => not (dmem x dtest)) l0
    val l2 = map (string_of_aimterm " ") l1 
  in
    msg_synt l2 "conjectures";
    writel file l2
  end

(*
fun reprove nfreq conjf exportf launchf pdir ncores tim (odict,tdict,rdict) =
  let
    val tml0 = filter (fn x => dfind x rdict = Theorem) (dkeys tdict)
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
*)

end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;
tttExec.update_metis_tac ();

(* Initialization *)
val run_id = "bruteforce";
val _ = ttt_synt_dir := tactictoe_dir ^ "/log_synt/" ^ run_id;
val nfreq = 10;
val tdict = init_dicts ();

(* Conjecturing *)
val _ = mlibUseful.trace_level := 0;
val _ = targeted_conjectures nfreq tdict;

(* Fixed parameters *)
val provers_dir = HOLDIR ^ "/src/holyhammer/provers"
val pdir_eval   = provers_dir ^ "/parallel_eval";
val exportf     = export_pb;
val launchf     = eprover_parallel;
val transf      = hhTranslate.cached_translate;
val conjf       = tttSynt.conjecture
(* Parameters *)
val _ = show_types := true;
(* proving *)
val ncores = 40;
val tim = 1;

(* output *)
thibault@grid02:/shared/mptp/deepmath/mizar40$ less statements
thibault@grid02:/shared/mptp/deepmath/mizar40$ 
thibault@grid02:/shared/mptp/deepmath/mizar40$ wc -l statements

Cache creates out of memory problems.

(* Re-proving theorems *)
val proven = reprove nfreq conjf exportf launchf pdir_eval ncores tim dicts;

(* *)
val baseline_file = tactictoe_dir ^ "/log_synt/baseline/proven_thms";
val baselineproven  = import_tml baseline_file;
val l = list_diff proven baselineproven;


load "tttSyntEval"; open tttTools tttSyntEval;
show_types := true;
val dicts = init_dicts ();
val tml = dkeys (#2 dicts);
fun is_vc x = is_var x orelse is_const x;
val vcl = List.concat (map (find_terms is_vc) tml); 
val vcset = mk_fast_set Term.compare vcl;
fun tml_of_d d = List.concat (map snd (dlist d))
init_gen_size vcset;
val size2 = tml_of_d (gen_size 2);



load "tacticToe"; open tacticToe;
val l0 = dlist (!ttt_tacfea);
fun is_metis s = String.isPrefix "METIS_TAC" (drop_sig s); 
val l1 = filter (is_metis o #1 o fst) l0;

metisTools.limit :=  {infs = SOME 1, time = NONE};
mlibUseful.trace_level := 0;

fun app_err x = SOME (METIS_TAC (first_n 10 (map snd (DB.thms "arithmetic"))) x) handle HOL_ERR _ => NONE;



load "tttSyntEval"; 
open tttPredict tttTools tttSynt tttSyntEval tttExec;
val i = ``:'a``;
val i2 = ``:'a -> 'a -> 'a``;
val i3 = ``:'a -> 'a -> 'a -> 'a``;
val l = readl "hol4terms";
val tml = mk_fast_set Term.compare (map hol4term_of_sml l);
val _ = app (cj_target tml) (one_in_n 40 0 tml);

load "holyHammer";
open holyHammer;
val ax1 = ``~(SUC x = 0)``;
val ax2 = ``~(x = 0) ==> ?y. (SUC y = x)``;
val ax3 = ``(SUC x = SUC y) ==> (x = y)``;
val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``x * 0 = 0``;
val ax7 = ``x * (SUC y) = (x * y) + x``;
val ax8 = concl numTheory.INDUCTION;
val bl = map (can holyhammer) [ax1,ax2,ax3,ax4,ax5,ax6,ax7];

time_mprove 0.1 [ax1,ax2] ``~(SUC 0 = 0)``;

TODO:
1) generate conjectures. 
2) generate induction predicates.
3) prove them using Eprover in parallel for 1sec.



*)

