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

val ncores = 32

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
   Proving conjectures
   todo parallelize proving
   -------------------------------------------------------------------------- *) 

fun mprove t premises tm =
  let
    val goal = ([], tm)
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = METIS_TAC thml
  in
    can tac goal
  end

fun minimize_aux t l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if mprove t (l1 @ m) tm 
    then minimize_aux t l1 m tm
    else minimize_aux t (a :: l1) m tm
    
fun miniprove t tml tm = 
  let
    fun cmp (a,b) = id_compare (id_of_term a, id_of_term b)
    val tml' = dict_sort cmp tml 
  in
    if mprove t tml' tm 
    then SOME (minimize_aux t [] tml' tm)
    else NONE
  end

fun prove_cj t (symweight_org,tmfea_org) cj =
  let 
    val tml = tmknn 16 (symweight_org,tmfea_org) (feai_of_term cj)
    val ro = miniprove t tml cj
  in
    case ro of
      SOME []     => NONE (* trivial *)
    | NONE        => NONE
    | SOME lemmas => SOME (cj,lemmas)
  end

(* --------------------------------------------------------------------------
   Evaluating conjectures
   -------------------------------------------------------------------------- *) 

datatype usage = Irrelevant | Predicted of term list | Useful of term list

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

fun eval t (tmid,((tm,fea),role)) =
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
      if not (mprove t tml tm) then (Predicted cjl, tm) else
      let 
        val mintml1 = minimize_aux t [] tml tm 
        val mintml2 = filter (fn x => role_of_term x = Conjecture) mintml1
      in
        (Useful mintml2, tm)
      end
  in
    SOME r
  end

fun eval_cjl t cjl =
  let 
    val rl = ref []
    val _ = app insert_cj cjl
    val lo = par_map ncores (eval t) (dlist (!dict_glob))
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

fun all_in_one ncores tim cjlimit =
  let 
    val _ = mlibUseful.trace_level := 0
    val _ = init_n_thy 1000
    val _ = par_app ncores (reprove tim) (dlist (!dict_glob))
    val tmfea_org = map (fst o snd) (dlist (!dict_glob))
    val symweight_org = learn_tfidf tmfea_org
    val cjl0 = gen_cjl tmfea_org
    val cjl1 = first_n cjlimit cjl0;
    val cjlp0 = par_map ncores (prove_cj tim (symweight_org,tmfea_org)) cjl1
    val cjlp1 = List.mapPartial I cjlp0
    val rl = eval_cjl 0.1 cjlp1
    val rl1 = filter (is_useful o fst) rl
  in
    rl1
  end  

fun batch_n n l =
  let val (l1,l2) = part_n n l in
     if null l2 then [l1] else l1 :: batch_n n l2
  end

end (* struct *)

(*
load "tttSyntEval";
open tttPredict tttTools tttSynt tttSyntEval;
mlibUseful.trace_level := 0;
limit := {infs = NONE, time = SOME 0.1};

(* Initialization *)
val ncores = 32;
val _ = init_n_thy 1000; print "end";
val _ = print_endline (int_to_string (dlength (!dict_glob)) ^ " theorems")

(* Generating conjectures *)
val tmfea_org = map (fst o snd) (dlist (!dict_glob))
val symweight_org = learn_tfidf tmfea_org
val cjl0 = gen_cjl tmfea_org
val _ = print_endline (int_to_string (length cjl0) ^ " generated conjectures")

(* Proving conjectures *)
val cjlp' = par_map ncores (prove_cj 0.2 (symweight_org,tmfea_org)) cjl0;
val cjlp = List.mapPartial I cjlp';
val _ = print_endline (int_to_string (length cjlp) ^ " proven conjectures")

(* Evaluate conjectures *)
val rl = eval_cjl 0.2 cjlp;
val rl0 = filter (is_predicted o fst) rl;
val rl1 = filter (is_useful o fst) rl;
val _ = print_endline (int_to_string (length rl1) ^ " useful conjectures");

(* Summary *)
val _ = 
  (
  print_endline (int_to_string (dlength (!dict_glob)) ^ " theorems");
  print_endline (int_to_string (length cjl0) ^ " generated conjectures");
  print_endline (int_to_string (length cjlp) ^ " proven conjectures");
  print_endline (int_to_string (length rl1) ^ " useful conjectures")
  );
*)


(* test 
load "tttSyntEval";
open tttPredict tttTools tttSynt tttSyntEval tttFeature;
mlibUseful.trace_level := 0;
limit := {infs = NONE, time = SOME 0.1};

fun f () = METIS_TAC (map snd (DB.thms "arithmetic")) ([],``1+1=2``);

val l0 = List.tabulate (100, fn _ => ());
val (l1,t) = add_time (map f) l0;
val (l1,t) = add_time (par_map 3 f) l0;

*)

(* 
val _ = par_app ncores (reprove 0.1) (dlist (!dict_glob))
val reprovenl = filter (fn x => snd (snd x) = Reproven) (dlist (!dict_glob))
val _ = print_endline (int_to_string (length reprovenl) ^ " reproven theorems")
*)
(*
fun f () = METIS_TAC (map snd (DB.thms "arithmetic")) ([],``1+1=2``);
*)
