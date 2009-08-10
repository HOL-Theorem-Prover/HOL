structure quantHeuristicsScript =
struct


open HolKernel Parse boolLib Drule BasicProvers
     pairTheory listTheory optionTheory;

val _ = new_theory "quantHeuristics";

(*
quietdec := false;
*)


(*Basic theorems*)

val CONJ_NOT_OR_THM = store_thm ("CONJ_NOT_OR_THM",
``!A B. A /\ B = ~(~A \/ ~B)``,
REWRITE_TAC[DE_MORGAN_THM])


val EXISTS_NOT_FORALL_THM = store_thm ("EXISTS_NOT_FORALL_THM",
``!P. ((?x. P x) = (~(!x. ~(P x))))``,
PROVE_TAC[])


val EXISTS_UNIQUE_INSTANTIATE_THM = store_thm ("EXISTS_UNIQUE_INSTANTIATE_THM",
``!P i. (!v. ~(v = i) ==> ~(P v)) ==> ((?!v. P v) = P i)``,PROVE_TAC[]);


val MOVE_EXISTS_IMP_THM = store_thm ("MOVE_EXISTS_IMP_THM",
``(?x. ((!y. (~(P x y)) ==> R y) ==> Q x)) =
         (((!y. (~(!x. P x y)) ==> R y)) ==> ?x. Q x)``,
         PROVE_TAC[]);


val UNWIND_EXISTS_THM = store_thm ("UNWIND_EXISTS_THM",
 ``!a P. (?x. P x) = ((!x. ~(x = a) ==> ~(P x)) ==> P a)``,
 PROVE_TAC[]);



val LEFT_IMP_AND_INTRO = store_thm ("LEFT_IMP_AND_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((x /\ t1) ==> (x /\ t2))``,
 PROVE_TAC[]);

val RIGHT_IMP_AND_INTRO = store_thm ("RIGHT_IMP_AND_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((t1 /\ x) ==> (t2 /\ x))``,
 PROVE_TAC[]);


val LEFT_IMP_OR_INTRO = store_thm ("LEFT_IMP_OR_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((x \/ t1) ==> (x \/ t2))``,
 PROVE_TAC[]);

val RIGHT_IMP_OR_INTRO = store_thm ("RIGHT_IMP_OR_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((t1 \/ x) ==> (t2 \/ x))``,
 PROVE_TAC[]);




(* Theorems for the specialised logics *)

val PAIR_EQ_EXPAND = store_thm ("PAIR_EQ_EXPAND",
``(((x:'a,y:'b) = X) = ((x = FST X) /\ (y = SND X))) /\
  ((X = (x,y)) = ((FST X = x) /\ (SND X = y)))``,
SingleStep.Cases_on `X` THEN
REWRITE_TAC[pairTheory.PAIR_EQ]);


val PAIR_EQ_SIMPLE_EXPAND = store_thm ("PAIR_EQ_SIMPLE_EXPAND",
``(((x:'a,y:'b) = (x, y')) = (y = y')) /\
  (((y:'b,x:'a) = (y', x)) = (y = y')) /\
  (((FST X, y) = X) = (y = SND X)) /\
  (((x, SND X) = X) = (x = FST X)) /\
  ((X = (FST X, y)) = (SND X = y)) /\
  ((X = (x, SND X)) = (FST X = x))``,
SingleStep.Cases_on `X` THEN
ASM_REWRITE_TAC[pairTheory.PAIR_EQ]);


val IS_SOME_EQ_NOT_NONE = store_thm ("IS_SOME_EQ_NOT_NONE",
``!x. IS_SOME x = ~(x = NONE)``,
REWRITE_TAC[GSYM optionTheory.NOT_IS_SOME_EQ_NONE]);


val _ = export_theory();


end
