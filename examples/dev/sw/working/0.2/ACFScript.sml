
open HolKernel Parse boolLib bossLib pairLib pairSyntax pairTheory PairRules;

(*---------------------------------------------------------------------------------*)

val _ = new_theory "ACF";

(*---------------------------------------------------------------------------*)
(* Convert HOL programs to combinator-based pseudo-ASTs                      *)
(* Term programs is translated to equivalent A-Combinator Forms (ACF)        *)
(*---------------------------------------------------------------------------*)

val sc_def =
  Define
   `sc (f1:'a->'b) (f2:'b->'c) = \x. f2(f1 x)`;

val cj_def =
 Define
   `cj f1 f2 f3 = \x. if f1 x then f2 x else f3 x`;

val tr_def =
 TotalDefn.DefineSchema
   `tr (x:'a) = if f1 x then x else tr (f2 x)`;

val tr_ind = fetch "-" "tr_ind";

(*---------------------------------------------------------------------------*)
(* HOL programs is converted to sc, tr and cj structures                     *)
(*---------------------------------------------------------------------------*)

val tr_INTRO = store_thm
("tr_INTRO",
 ``!f f1 f2.
     (!x:'a. f x = if f1(x) then x else f(f2 x))
     ==> (?R. WF R /\ (!x. ~f1 x ==> R (f2 x) x))
     ==> (f:'a->'a = tr f1 f2)``,

  REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN 
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN 
  HO_MATCH_MP_TAC tr_ind THEN 
  GEN_TAC THEN STRIP_TAC THEN 
  IMP_RES_TAC (DISCH_ALL tr_def) THEN 
  POP_ASSUM (fn th => ONCE_REWRITE_TAC[th]) THEN 
  METIS_TAC[]
 );

val rec_INTRO = store_thm
("rec_INTRO",
 ``!f f1 f2 f3.
     (!x:'a. f x = if f1(x) then f2(x) else f(f3 x))
     ==> (?R. WF R /\ (!x. ~f1 x ==> R (f3 x) x))
     ==> (f:'a->'b = sc (tr f1 f3) f2)``,

  REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN 
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN 
  GEN_TAC THEN
  IMP_RES_TAC  relationTheory.WF_INDUCTION_THM THEN
  POP_ASSUM (MATCH_MP_TAC o SIMP_RULE std_ss [] o
          Q.SPEC `\x. f x = sc (tr f1 f3) f2 x`) THEN
  REPEAT STRIP_TAC THEN
  Cases_on `f1 x` THENL [ 
    METIS_TAC [sc_def, DISCH_ALL tr_def],
  
    IMP_RES_TAC (DISCH_ALL tr_def) THEN
    METIS_TAC [sc_def]
  ]
 );


(*---------------------------------------------------------------------------------*)

val _ = export_theory();
