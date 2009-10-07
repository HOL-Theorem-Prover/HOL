structure ConseqConvScript =
struct

open HolKernel Parse boolLib Drule;

val _ = new_theory "ConseqConv";


val ty_forall_eq_thm = store_thm ("ty_forall_eq_thm",
   ``(!:'a:'k. (P [:'a:] = Q [:'a:])) ==> ((!:'a. P [:'a:]) = (!:'a. Q [:'a:]))``,
     STRIP_TAC THEN ASM_REWRITE_TAC[]);

val ty_exists_eq_thm = store_thm ("ty_exists_eq_thm",
   ``(!:'a:'k. (P [:'a:] = Q [:'a:])) ==> ((?:'a. P [:'a:]) = (?:'a. Q [:'a:]))``,
     STRIP_TAC THEN ASM_REWRITE_TAC[]);

val forall_eq_thm = store_thm ("forall_eq_thm",
   ``(!s:'a. (P s = Q s)) ==> ((!s. P s) = (!s. Q s))``,
     STRIP_TAC THEN ASM_REWRITE_TAC[]);

val exists_eq_thm = store_thm ("exists_eq_thm",
   ``(!s:'a. (P s = Q s)) ==> ((?s. P s) = (?s. Q s))``,
     STRIP_TAC THEN ASM_REWRITE_TAC[]);


val true_imp = store_thm ("true_imp", ``!t. t ==> T``, REWRITE_TAC[]);
val false_imp = store_thm ("false_imp", ``!t. F ==> t``, REWRITE_TAC[]);


val NOT_CLAUSES_THML = CONJUNCTS NOT_CLAUSES
val NOT_CLAUSES_X = save_thm ("NOT_CLAUSES_X", el 1 NOT_CLAUSES_THML)
val NOT_CLAUSES_T = save_thm ("NOT_CLAUSES_T", el 2 NOT_CLAUSES_THML)
val NOT_CLAUSES_F = save_thm ("NOT_CLAUSES_F", el 3 NOT_CLAUSES_THML)



val IMP_CONG_conj_strengthen = store_thm ("IMP_CONG_conj_strengthen",
``!x x' y y'.
  ((y ==> (x' ==> x)) /\ (x' ==> (y' ==> y))) ==>
  ((x' /\ y') ==> (x /\ y))``,
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);

val IMP_CONG_conj_weaken = store_thm("IMP_CONG_conj_weaken",
``!x x' y y'.
  ((y ==> (x ==> x')) /\ (x' ==> (y ==> y'))) ==>
  ((x /\ y) ==> (x' /\ y'))``,
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);


val AND_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] AND_CLAUSES))

val AND_CLAUSES_TX = save_thm ("AND_CLAUSES_TX", el 1 AND_CLAUSES_THML)
val AND_CLAUSES_XT = save_thm ("AND_CLAUSES_XT", el 2 AND_CLAUSES_THML)
val AND_CLAUSES_FX = save_thm ("AND_CLAUSES_FX", el 3 AND_CLAUSES_THML)
val AND_CLAUSES_XF = save_thm ("AND_CLAUSES_XF", el 4 AND_CLAUSES_THML)
val AND_CLAUSES_XX = save_thm ("AND_CLAUSES_XX", el 5 AND_CLAUSES_THML)


val IMP_CONG_disj_strengthen = store_thm ("IMP_CONG_disj_strengthen",
``!x x' y y'.
  ((~y ==> (x' ==> x)) /\ (~x' ==> (y' ==> y))) ==>
  ((x' \/ y') ==> (x \/ y))``,
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);


val IMP_CONG_disj_weaken = store_thm ("IMP_CONG_disj_weaken",
``!x x' y y'.
  ((~y ==> (x ==> x')) /\ (~x' ==> (y ==> y'))) ==>
  ((x \/ y) ==> (x' \/ y'))``,
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);


val OR_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] OR_CLAUSES))

val OR_CLAUSES_TX = save_thm ("OR_CLAUSES_TX", el 1 OR_CLAUSES_THML)
val OR_CLAUSES_XT = save_thm ("OR_CLAUSES_XT", el 2 OR_CLAUSES_THML)
val OR_CLAUSES_FX = save_thm ("OR_CLAUSES_FX", el 3 OR_CLAUSES_THML)
val OR_CLAUSES_XF = save_thm ("OR_CLAUSES_XF", el 4 OR_CLAUSES_THML)
val OR_CLAUSES_XX = save_thm ("OR_CLAUSES_XX", el 5 OR_CLAUSES_THML)




val IMP_CONG_imp_strengthen = store_thm ("IMP_CONG_imp_strengthen",
``!x x' y y'.
  ((x ==> (y' ==> y)) /\ (~y' ==> (x ==> x'))) ==>
  ((x' ==> y') ==> (x ==> y))``,
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);

val IMP_CONG_imp_weaken = store_thm ("IMP_CONG_imp_weaken",
``!x x' y y'.
  ((x ==> (y ==> y')) /\ (~y' ==> (x' ==> x))) ==>
  ((x ==> y) ==> (x' ==> y'))``,
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);


val IMP_CONG_simple_imp_strengthen = store_thm ("IMP_CONG_simple_imp_strengthen",
``!x x' y y'.
  ((x ==> x') /\ (x' ==> (y' ==> y))) ==>
  ((x' ==> y') ==> (x ==> y))``,
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);

val IMP_CONG_simple_imp_weaken = store_thm ("IMP_CONG_simple_imp_weaken",
``!x x' y y'.
  ((x' ==> x) /\ (x' ==> (y ==> y'))) ==>
  ((x ==> y) ==> (x' ==> y'))``,
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]);


val IMP_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] IMP_CLAUSES))

val IMP_CLAUSES_TX = save_thm ("IMP_CLAUSES_TX", el 1 IMP_CLAUSES_THML)
val IMP_CLAUSES_XT = save_thm ("IMP_CLAUSES_XT", el 2 IMP_CLAUSES_THML)
val IMP_CLAUSES_FX = save_thm ("IMP_CLAUSES_FX", el 3 IMP_CLAUSES_THML)
val IMP_CLAUSES_XX = save_thm ("IMP_CLAUSES_XX", el 4 IMP_CLAUSES_THML)
val IMP_CLAUSES_XF = save_thm ("IMP_CLAUSES_XF", el 5 IMP_CLAUSES_THML)



val _ = export_theory();

end (* boolScript *)
