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

fun feai_of_term x = tttFeature.fea_of_goal ([],x)

(* --------------------------------------------------------------------------
   Global dictionaries.
   -------------------------------------------------------------------------- *)

datatype role = Axiom | Theorem | Reproven | Conjecture

val id_compare = 
  (cpl_compare Int.compare (cpl_compare Int.compare Int.compare))

val dict_glob :
  (int * (int * int), (term * int list) * role) Redblackmap.dict ref
  = ref (dempty id_compare)

val (revtm_glob : (term, (int * (int * int)) * (string * thm) * role) 
  Redblackmap.dict ref) =
  ref (dempty Term.compare)

fun id_of_term tm   = #1 (dfind tm (!revtm_glob))
fun thm_of_term tm  = #2 (dfind tm (!revtm_glob))
fun role_of_term tm = #3 (dfind tm (!revtm_glob))
  
fun term_of_id id = (fst o fst) (dfind id (!dict_glob))

(* todo: split conjunctions *)

fun update_dict thydict thy =
  let fun f role (name,thm) =
    let 
      val tm = (concl o GEN_ALL o DISCH_ALL) thm
      val k = (dfind thy thydict,(depnumber_of_thm thm,0))
      val v = ((tm,feai_of_term tm),role)
    in
      if dmem tm (!revtm_glob) then () else
      (
      revtm_glob := dadd tm (k,(name,thm),role) (!revtm_glob);
      dict_glob := dadd k v (!dict_glob)
      )
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
    val (i1,(i2,_)) = last (dict_sort id_compare idl)
    val k           = (i1,(i2,(!cji)))
    val _           = incr cji
    val role        = Conjecture
    val v           = ((cj,feai_of_term cj),role)
    val fake_name   = ("",TRUTH)
  in
    revtm_glob := dadd cj (k,fake_name,role) (!revtm_glob);
    dict_glob := dadd k v (!dict_glob)
  end

(* --------------------------------------------------------------------------
   Proving conjectures
   todo parallelize proving
   -------------------------------------------------------------------------- *) 

fun mprove premises tm =
  let
    val goal = ([], tm)
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = METIS_TAC thml
  in
    case app_tac 0.1 tac goal of
      SOME [] => true 
    | _ => false
  end

fun minimize_aux l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if mprove (l1 @ m) tm 
    then minimize_aux l1 m tm
    else minimize_aux (a :: l1) m tm
    
fun miniprove tml tm = 
  let
    fun cmp (a,b) = id_compare (id_of_term a, id_of_term b)
    val tml' = dict_sort cmp tml 
  in
    if mprove tml' tm 
    then SOME (minimize_aux [] tml' tm)
    else NONE
  end

fun prove_cj (symweight_org,tmfea_org) cj =
  let 
    val tml = tmknn 16 (symweight_org,tmfea_org) (feai_of_term cj)
    val ro = miniprove tml cj
  in
    case ro of
      SOME []     => NONE (* trivial *)
    | NONE        => NONE
    | SOME lemmas => SOME (cj,lemmas)
  end

(* --------------------------------------------------------------------------
   Evaluating conjectures
   -------------------------------------------------------------------------- *) 

datatype usage = Irrelevant | Predicted | Useful of term list

fun reprove (tmid,((tm,fea),role)) =
  if role <> Theorem then () else
  let
    val l0 = dlist (!dict_glob)
    fun is_older (x,_) = id_compare (x,tmid) = LESS
    val l1 = filter is_older l0
    val tmfea = map (fst o snd) l1
    val symweight = learn_tfidf tmfea
    val tml = tmknn 16 (symweight,tmfea) fea
  in
    if mprove tml tm
    then dict_glob := dadd tmid ((tm,fea),Reproven) (!dict_glob)
    else ()
  end

fun eval (tmid,((tm,fea),role)) =
  if role <> Theorem then NONE else
  let
    val l0 = dlist (!dict_glob)
    fun is_older (x,_) = id_compare (x,tmid) = LESS
    val l1 = filter is_older l0
    val tmfea = map (fst o snd) l1
    val symweight = learn_tfidf tmfea
    val tml = tmknn 16 (symweight,tmfea) fea 
    val cjl = filter (fn x => role_of_term x = Conjecture) tml
    val r =
      if null cjl then (Irrelevant, tm) else
      if not (mprove tml tm) then (Predicted, tm) else
      let 
        val mintml1 = minimize_aux [] tml tm 
        val mintml2 = filter (fn x => role_of_term x = Conjecture) mintml1
      in
        (Useful mintml2, tm)
      end
  in
    SOME r
  end

fun eval_cjl cjl =
  let 
    val rl = ref []
    val _ = app insert_cj cjl
    val lo = par_map 3 eval (dlist (!dict_glob))
  in
    List.mapPartial I lo
  end

fun init_n_thy n =
  let
    val thyl = first_n n (sort_thyl (ancestry (current_theory ())))
    val thyl1 = map (fn (a,b) => (b,a)) (number_list 0 thyl)
    val thydict = dnew String.compare thyl1
  in
    app (update_dict thydict) thyl
  end

fun is_useful x = case x of
    Useful [] => false
  | Useful _  => true  
  | _ => false  

fun is_predicted x = case x of
    Predicted => true
  | _ => false  


end (* struct *)

(*
load "tttSyntEval";
open tttPredict tttTools tttSynt tttSyntEval;
mlibUseful.trace_level := 0;
(* Initialization *)
init_n_thy 20;
dlength (!dict_glob);
(* app reprove (dlist (!dict_glob)); *)

(* Generating conjectures *)
val tmfea_org = map (fst o snd) (dlist (!dict_glob));
val symweight_org = learn_tfidf tmfea_org;
val cjl0 = gen_cjl tmfea_org;

(* Proving conjectures *)
val cjl1 = first_n 1000 cjl0;
val cjlp' = par_map 3 (prove_cj (symweight_org,tmfea_org)) cjl1
val cjlp = List.mapPartial I cjlp';
length cjl0; length cjl1; length cjlp;

(* Evaluate conjectures *)
val rl = eval_cjl cjlp;
val rl0 = filter (is_predicted o fst) rl;
val rl1 = filter (is_useful o fst) rl;
length rl0; length rl1;
*)
