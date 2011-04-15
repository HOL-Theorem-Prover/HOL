open HolKernel boolLib bossLib Parse ntermTheory nomsetTheory listTheory
     ramanaLib ntermLib

val _ = new_theory "apply_pi"

val apply_pi_q = `
  (apply_pi pi (Nom a) = Nom (perm_of pi a)) ∧
  (apply_pi pi (Sus p v) = Sus (pi ++ p) v) ∧
  (apply_pi pi (Tie a t) = Tie (perm_of pi a) (apply_pi pi t)) ∧
  (apply_pi pi (nPair t1 t2) = nPair (apply_pi pi t1) (apply_pi pi t2)) ∧
  (apply_pi pi (nConst c) = nConst c)`

val def_suffix = !Defn.def_suffix;
val _ = Defn.def_suffix := "_def_with_choice";
val apply_pi_def_with_choice = Define apply_pi_q;
val _ = Defn.def_suffix := def_suffix;
val apply_pi_def = RWstore_thm("apply_pi_def",apply_pi_q,SIMP_TAC (psrw_ss()) [apply_pi_def_with_choice]);

val _ = set_fixity "·" (Infixr 700)
val _ = overload_on("·",``apply_pi``)

val apply_pi_is_perm = Q.store_thm(
"apply_pi_is_perm",
`is_perm apply_pi`,
SRW_TAC [][is_perm_def] THENL [
  Induct_on `x` THEN ASM_SIMP_TAC (psrw_ss()) [],
  Induct_on `x` THEN ASM_SIMP_TAC (psrw_ss()) [is_perm_decompose],
  SRW_TAC [][FUN_EQ_THM] THEN
  Induct_on `x` THEN SRW_TAC [][] THEN
  ASM_SIMP_TAC (psrw_ss()) [app_permeq_monotone]
])

val apply_pi_nil = RWsave_thm("apply_pi_nil",MATCH_MP is_perm_nil apply_pi_is_perm)
val apply_pi_decompose = save_thm("apply_pi_decompose",MATCH_MP is_perm_decompose apply_pi_is_perm)
val apply_pi_inverse = RWsave_thm("apply_pi_inverse",MATCH_MP is_perm_inverse apply_pi_is_perm)
val apply_pi_id = RWsave_thm("apply_pi_id",MATCH_MP is_perm_id apply_pi_is_perm)
val apply_pi_injective = save_thm("apply_pi_injective",MATCH_MP is_perm_injective apply_pi_is_perm)
val apply_pi_eq_perms = RWsave_thm("apply_pi_eq_perms", is_perm_def |> Q.ISPEC
`apply_pi` |> C EQ_MP apply_pi_is_perm |> funpow 2 CONJUNCT2 |> SIMP_RULE
(bool_ss) [FUN_EQ_THM] |>SPEC_ALL|>UNDISCH|>SPEC_ALL|>DISCH_ALL)
val _ = export_permweakening "apply_pi_eq_perms"
val apply_pi_eql = save_thm("apply_pi_eql",MATCH_MP is_perm_eql apply_pi_is_perm);
val apply_pi_eqr = store_thm("apply_pi_eqr",
``(t1 = apply_pi pi t2) ⇔ (apply_pi (REVERSE pi) t1 = t2)``,
METIS_TAC [apply_pi_inverse]);

val nvars_apply_pi = RWstore_thm(
"nvars_apply_pi",
`∀t. nvars (apply_pi pi t) = nvars t`,
Induct THEN SRW_TAC [][])

val _ = export_theory ()
