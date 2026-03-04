Theory elim_lambda
Ancestors
  pair option relation prim_rec arithmetic list sorting hol_to_acl2
Libs
  HOL_to_ACL2 Elim_Lambda Conv

(* Replace variable RTC' with P because ACL2 doesn't like primes on vars *)
val RTC_ind' =
    CONV_RULE (RENAME_VARS_CONV ["R", "P"]) relationTheory.RTC_ind;

(* Push  quantifier scope inwards *)

val PRIM_REC_THM' = SRULE [FORALL_AND_THM] prim_recTheory.PRIM_REC_THM;

(*---------------------------------------------------------------------------*)
(* MAP definition shouldn't be altered since there's no buried lambda in it. *)
(*---------------------------------------------------------------------------*)

val map_def = def_bundle listTheory.MAP;

(* Various examples with quantifiers at depth *)

val skolem   = goal_bundle "SKOLEM_THM" (concl SKOLEM_THM);
val num_ind  = thm_bundle "num_ind" numTheory.INDUCTION;
val list_ind = thm_bundle "list_ind" listTheory.list_induction;
val tc_def   = def_bundle relationTheory.TC_DEF;
val rtc_ind  = thm_bundle "rtc_ind" RTC_ind';
val pforall_thm  = thm_bundle "pforall_thm" pairTheory.PFORALL_THM;
val pair_cases   = thm_bundle "pair_cases" pairTheory.pair_CASES;
val pair_case_eq = thm_bundle "pair_case_eq" pairTheory.pair_case_eq;
val prim_rec_thm = thm_bundle "prim_rec_thm" PRIM_REC_THM';
val qsort_def    = def_bundle sortingTheory.QSORT_DEF;

(* Definitions with case expressions *)

Definition fact_case_def:
  fact n = case n of 0 => 1 | _ => n * fact (n-1)
End

Definition len_case_def:
  len list = case list of [] => 0 | _::t => 1 + len t
End

val fact_case_def = def_bundle fact_case_def;
val len_case_def  = def_bundle len_case_def;

(* Definition with nested recursive type *)

Datatype:
  tree = Node 'a (tree list)
End

(*---------------------------------------------------------------------------*)
(* Deeply nested lambda terms and quantifiers in the type characterization   *)
(* theorem. This example also has a lot of auto-generated names that are     *)
(* normalized into ACL2-suitable (and human-readable) form.                  *)
(*---------------------------------------------------------------------------*)

val tree_ty_def = definition "tree_TY_DEF";

val tree_ty_def' = C EQ_MP tree_ty_def
    (ALPHA (concl tree_ty_def)
     “∃rep :α tree -> α recspace.
        TYPE_DEFINITION
         (λx. ∀f g.
                   (∀a2.
                      (∃a0 a1.
                         a2 =
                         (λa0 a1.
                              ind_type$CONSTR 0 a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0 a1 ∧
                         g a1) ⇒
                      f a2) ∧
                   (∀a3.
                      a3 = ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a3 =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ f a0 ∧
                         g a1) ⇒
                      g a3) ⇒
                   f x) rep”);


val tree_ty_bundle = thm_bundle "tree_ty_def" tree_ty_def';

val tree_ind = thm_bundle "tree_induction" (fetch "-" "tree_induction");

Definition occurs_def:
  occurs (Node x ts) a <=> (x = a) ∨ EXISTS (\t. occurs t a) ts
End

val occurs_def_bundle = def_bundle occurs_def;

val bundles =
  [map_def, skolem, num_ind, list_ind, tc_def, rtc_ind,
   pforall_thm, pair_cases, pair_case_eq, prim_rec_thm,
   qsort_def, fact_case_def, len_case_def, tree_ty_bundle, tree_ind,
   occurs_def_bundle];

val _ = print_bundles_to_file "elim_lambda.defhol" bundles;
