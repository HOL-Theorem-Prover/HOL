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

fun feai_of_term x = tttFeature.fea_of_goal ([],x)

(* --------------------------------------------------------------------------
   Initialization
   -------------------------------------------------------------------------- *)

datatype role = Axiom | Theorem | Conjecture

val id_compare = list_compare Int.compare

val dict_glob :
  (int list, (term * int list) * role) Redblackmap.dict ref
  = ref (dempty id_compare)

val revtm_glob : 
  (term, int list * (string * thm) * role) Redblackmap.dict ref 
  = ref (dempty Term.compare)

fun id_of_term tm   = #1 (dfind tm (!revtm_glob))
fun thm_of_term tm  = #2 (dfind tm (!revtm_glob))
fun role_of_term tm = #3 (dfind tm (!revtm_glob))
  
fun term_of_id id = (fst o fst) (dfind id (!dict_glob))

fun update_dict thydict thy =
  let fun f role (name,thm) =
    let 
      val nthy = dfind thy thydict
      val nthm = depnumber_of_thm thm
      val thml = CONJUNCTS (SPEC_ALL thm)
      val nthml = number_list 0 thml
      fun update_aux (nconj,thm') =
        let 
          val tm' = (concl o GEN_ALL o DISCH_ALL) thm'
          val k = [nthy,nthm,nconj]
          val v = ((tm', feai_of_term tm'),role)
        in
          if dmem tm' (!revtm_glob) then () else
          (
          revtm_glob := dadd tm' (k,(name,thm),role) (!revtm_glob);
          dict_glob := dadd k v (!dict_glob)
          )
        end
    in
      app update_aux nthml
    end
  in
    app (f Theorem) (DB.theorems thy);
    app (f Axiom) (DB.axioms thy @ DB.definitions thy)
  end
 
val cji = ref 1

fun insert_cj (cj,lemmas) =  
  if dmem cj (!revtm_glob) then () else
  let 
    val idl         = map id_of_term lemmas
    val lastid      = last (dict_sort id_compare idl)
    val k           = lastid @ [!cji]
    val _           = incr cji
    val role        = Conjecture
    val v           = ((cj,feai_of_term cj),role)
    val fake_name   = ("",TRUTH)
  in
    revtm_glob := dadd cj (k,fake_name,role) (!revtm_glob);
    dict_glob := dadd k v (!dict_glob)
  end

fun init_n_thy n =
  let
    val _ = dict_glob := dempty id_compare
    val _ = revtm_glob := dempty Term.compare
    val thyl = first_n n (sort_thyl (ancestry (current_theory ())))
    val thyl1 = map (fn (a,b) => (b,a)) (number_list 0 thyl)
    val thydict = dnew String.compare thyl1
  in
    app (update_dict thydict) thyl
  end


(* --------------------------------------------------------------------------
   Translating the result of launch_eprover_parallel back into terms
   using the dictionnary list.
   -------------------------------------------------------------------------- *) 

fun read_result dl rl =
  let 
    val rld = dnew Int.compare rl
    fun read_result_one (pid,(cj,d)) = case dfind pid rld of
      SOME l => (cj, SOME (map (fn x => dfind x d) l))
    | NONE   => (cj, NONE)
  in
    map read_result_one dl
  end

(* --------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *) 

fun is_conjecture tm = role_of_term tm = Conjecture

fun is_nontrivial x = case x of
    SOME [] => false
  | NONE    => false
  | _        => true

(* --------------------------------------------------------------------------
   Proving conjectures
   -------------------------------------------------------------------------- *) 

fun predict_cj (symweight,tmfea) cj =
  (tmknn 16 (symweight,tmfea) (feai_of_term cj) , cj)

val parallel_dir = HOLDIR ^ "/src/holyhammer/provers/parallel"

fun pred_trans_write_cjl (symweight,tmfea) exportf cjl =
  let 
    val _ = mkDir_err parallel_dir
    val _ = print_endline "start predict"
    val tmlcjl = map (predict_cj (symweight,tmfea)) cjl
    val _ = print_endline "start export"
  in
    mapi exportf tmlcjl
  end

(* --------------------------------------------------------------------------
   Evaluating conjectures
   -------------------------------------------------------------------------- *) 

fun msg l s = print_endline (int_to_string (length l) ^ " " ^ s)

fun eval_predict l0 (tmid,((topcj,fea),role)) =
  let
    fun is_older (x,_) = id_compare (x,tmid) = LESS
    val l1 = filter is_older l0
    val tmfea = map (fst o snd) l1
    val symweight = learn_tfidf tmfea
    val predl = tmknn 16 (symweight,tmfea) fea
    val icjl = filter (fn x => role_of_term x = Conjecture) predl
  in
    if null icjl 
    then NONE
    else SOME (predl,topcj)
  end

fun eval_pred_trans_write exportf cjlp =
  let 
    val _ = app insert_cj cjlp
    val l0 = dlist (!dict_glob)
    fun role_theorem (_,((_,_),role)) = role = Theorem
    val l1 = filter role_theorem l0
    val _ = print_endline "start predict"
    val tmlcjl = List.mapPartial (eval_predict l0) l1
    val _ = print_endline "start export"
  in
    mapi exportf tmlcjl
  end

end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;

(* Initialization *)
val ncores = 3;
val timelimit = 2;
val _ = init_n_thy 5;
val norg = dlength (!dict_glob);
val _ = print_endline (int_to_string norg ^ " theorems");
val tmfea_org = map (fst o snd) (dlist (!dict_glob));
val symweight_org = learn_tfidf tmfea_org;
fun msg l s = print_endline (int_to_string (length l) ^ " " ^ s);

(* Generating conjectures *)
val cjl0 = gen_cjl tmfea_org;
val cjl1 = first_n 10 cjl0;
val _ = msg cjl0 "generated conjectures";

(* Proving conjectures *)
val p_dl = 
  pred_trans_write_cjl (symweight_org,tmfea_org) trans_write_tmlcj cjl1;
val p_rl = launch_eprover_parallel ncores (map fst p_dl) 2;
val p_rlfinal = read_result p_dl p_rl;
val p_rlproven = filter (isSome o snd) p_rlfinal;
val _ = msg p_rlproven "proven conjectures";
val p_rlnontrivial = filter (is_nontrivial o snd) p_rlfinal;
val _ = msg p_rlnontrivial "nontrivial conjectures";
val cjlp = map (fn (a,b) => (a, valOf b)) rlnontrivial;

(* Evaluate conjectures *)
val e_dl = eval_pred_trans_write trans_write_tmlcj cjlp;
val _ = msg e_dl "theorems with predicted conjectures"
val e_rl = launch_eprover_parallel ncores (map fst e_dl) 2;
val e_rlfinal = read_result e_dl e_rl;
val e_rlnontrivial = filter (is_nontrivial o snd) e_rlfinal;
val _ = msg e_rlnontrivial "nontrivial theorems";
val cjle = 
  map (fn (a,b) => (a, filter is_conjecture (valOf b))) e_rlnontrivial;
val cjle' = filter (not o null o snd) cjle;
val _ = msg cjle' "theorems with a proof containing at least one conjecture";


(* Summary *)

val tl0 = dlist (!dict_glob);
fun role_theorem (_,((_,_),role)) = role = Theorem;
fun role_axiom (_,((_,_),role)) = role = Axiom;
val tl1 = filter role_theorem tl0;
val tl2 = filter role_axiom tl0;

val _ = 
  (
  msg tl2 "axioms";
  msg tl1 "theorems";
  msg cjl0 "generated conjectures";
  msg cjl1 "selected conjectures";
  msg p_rlproven "proven conjectures";
  msg p_rlnontrivial "nontrivial conjectures";
  msg e_dl "theorems with predicted conjectures";
  msg e_rlnontrivial "nontrivial theorems";
  msg cjle' "theorems with a proof containing at least one conjecture"
  );

*)

(*
fun reprove t (tmid,((tm,fea),role)) =
  if role <> Theorem then true else
  let
    val l0 = dlist (!dict_glob)
    fun is_older (x,_) = id_compare (x,tmid) = LESS
    val l1 = filter is_older l0
    val tmfea = map (fst o snd) l1
    val symweight = learn_tfidf tmfea
    val tml = tmknn 16 (symweight,tmfea) fea
  in
    mprove t tml tm
  end
*)
