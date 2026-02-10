Theory elim_lambda
Ancestors
  pair option relation prim_rec arithmetic list sorting hol_to_acl2
Libs
  HOL_to_ACL2 Elim_Lambda

(* unlambda_conjuncts should not alter MAP definition *)

val map_def = unlambda_conjuncts listTheory.MAP;

(* Various examples with quantifiers at depth *)

val skolem    = unlambda_conjuncts SKOLEM_THM;
val num_ind   = unlambda_conjuncts numTheory.INDUCTION;
val list_ind  = unlambda_conjuncts listTheory.list_induction;
val tc        = unlambda_conjuncts relationTheory.TC_DEF;
val rtc_ind   = unlambda_conjuncts relationTheory.RTC_ind;
val pforall_thm  = unlambda_conjuncts pairTheory.PFORALL_THM;
val pair_cases   = unlambda_conjuncts pairTheory.pair_CASES;
val pair_case_eq = unlambda_conjuncts pairTheory.pair_case_eq;
val prim_rec_thm = unlambda_conjuncts prim_recTheory.PRIM_REC_THM;
val qsort_def    = unlambda_conjuncts sortingTheory.QSORT_DEF;

(* Definitions with case expressions *)

Definition fact_case_def:
  fact n = case n of 0 => 1 | _ => n * fact (n-1)
End

Definition len_case_def:
  len list = case list of [] => 0 | _::t => 1 + len t
End

val fact_case_def = unlambda_conjuncts fact_case_def;
val len_case_def  = unlambda_conjuncts len_case_def;

(*---------------------------------------------------------------------------*)
(* Prepare for making defhols                                                *)
(*---------------------------------------------------------------------------*)

fun process_thm name (th,defs,shrunk) =
    (th, defs @ [mk_named_thm name shrunk])

fun process_def (th,defs,shrunk) = (th, defs @ [shrunk])

val list =
  [process_def map_def,
   process_thm "SKOLEM_THM" skolem,
   process_thm "INDUCTION" num_ind,
   process_thm "list_induction" list_ind,
   process_def tc,
   process_thm "RTC_ind" rtc_ind,
   process_thm "PFORALL_THM" pforall_thm,
   process_thm "pair_CASES" pair_cases,
   process_thm "pair_case_eq" pair_case_eq,
   process_thm "PRIM_REC_THM" prim_rec_thm,
   process_def qsort_def,
   process_def fact_case_def,
   process_def len_case_def];

val _ = print_defhols_to_file "elim_lambda.defhol" (List.concat (map snd list));
