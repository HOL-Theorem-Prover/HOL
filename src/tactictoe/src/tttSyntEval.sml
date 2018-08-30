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

(* --------------------------------------------------------------------------
   Proving
   -------------------------------------------------------------------------- *) 

fun prove prover t (symweight_org,tmfea_org) (pids,cj) =
  let val tml = tmknn 16 (symweight_org,tmfea_org) (feai_of_term cj) in
    (cj, prover pids t tml cj)
  end

fun filter_nontrivial (a,b) = case b of
    SOME [] => NONE
  | NONE => NONE
  | _    => SOME (a,valOf b)

(* --------------------------------------------------------------------------
   Evaluating conjectures
   -------------------------------------------------------------------------- *) 

datatype usage = Irrelevant | Predicted of term list | Useful of term list

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

fun eval t prover l0 (pids,(tmid,((tm,fea),role))) =
  if role <> Theorem then NONE else
  let
    fun is_older (x,_) = id_compare (x,tmid) = LESS
    val l1 = filter is_older l0
    val tmfea = map (fst o snd) l1
    val symweight = learn_tfidf tmfea
    val tml = tmknn 16 (symweight,tmfea) fea 
    val cjl = filter (fn x => role_of_term x = Conjecture) tml
    val r =
      if null cjl then (Irrelevant, tm) else
      case prove prover t (symweight,tmfea) (pids,tm) of
        (_,NONE) => (Predicted cjl, tm)
      | (_,SOME l) => 
      let val mintml = filter (fn x => role_of_term x = Conjecture) l in
        (Useful mintml, tm)
      end
  in
    SOME r
  end

fun parallel_eval prover ncores t cjl =
  let 
    val rl = ref []
    val _ = app insert_cj cjl
    val l0 = dlist (!dict_glob)
    val lo = parmap_dir ncores (eval t prover l0) (dlist (!dict_glob))
  in
    List.mapPartial I lo
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

fun is_useful x = case x of
    Useful [] => false
  | Useful _  => true  
  | _ => false  

fun is_predicted x = case x of
    Predicted _ => true
  | _ => false  

end (* struct *)

(*
load "tttSyntEval"; load "holyHammer";
open tttPredict tttTools tttSynt tttSyntEval holyHammer;

(* Initialization *)
val ncores = 32;
val timelimit = 5;
val _ = init_n_thy 1000;
val norg = dlength (!dict_glob);
val _ = print_endline (int_to_string norg ^ " theorems");

(* Generating conjectures *)
val tmfea_org = map (fst o snd) (dlist (!dict_glob))
val symweight_org = learn_tfidf tmfea_org
val cjl0 = gen_cjl tmfea_org
val cjl1 = first_n 1000000 cjl0;
val _ = print_endline (int_to_string (length cjl0) ^ " generated conjectures");

(* Proving conjectures *)
val cjlp0 = 
  parmap_dir ncores (prove eprover timelimit (symweight_org,tmfea_org)) cjl1;
val cjlp1 = List.mapPartial filter_nontrivial cjlp0;
val _ = print_endline (int_to_string (length cjlp1) ^ " proven conjectures");

(* Evaluate conjectures *)
val rl = parallel_eval eprover ncores timelimit cjlp1;
val rl0 = filter (is_predicted o fst) rl;
val rl1 = filter (is_useful o fst) rl;

(* Summary *)
val _ = 
  (
  print_endline (int_to_string norg ^ " theorems");
  print_endline (int_to_string (length cjl0) ^ " generated conjectures");
  print_endline (int_to_string (length cjlp1) ^ " proven conjectures");
  print_endline (int_to_string (length rl0) ^ " predicted conjectures");
  print_endline (int_to_string (length rl1) ^ " useful conjectures")
  );
*)
