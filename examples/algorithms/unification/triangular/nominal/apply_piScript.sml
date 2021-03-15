open HolKernel boolLib bossLib Parse ntermTheory nomsetTheory listTheory
     ramanaLib ntermLib

val _ = new_theory "apply_pi"

val raw_apply_pi_q = `
  (raw_apply_pi pi (Nom a) = Nom (lswapstr pi a)) ∧
  (raw_apply_pi pi (Sus p v) = Sus (pi ++ p) v) ∧
  (raw_apply_pi pi (Tie a t) = Tie (lswapstr pi a) (raw_apply_pi pi t)) ∧
  (raw_apply_pi pi (nPair t1 t2) =
     nPair (raw_apply_pi pi t1) (raw_apply_pi pi t2)) ∧
  (raw_apply_pi pi (nConst c) = nConst c)`

val def_suffix = !Defn.def_suffix;
val _ = Defn.def_suffix := "_def_with_choice";
val raw_apply_pi_def_with_choice = Define raw_apply_pi_q;
val _ = Defn.def_suffix := def_suffix;
val raw_apply_pi_def = Q.store_thm(
  "raw_apply_pi_def",
  raw_apply_pi_q,
  SIMP_TAC (psrw_ss()) [raw_apply_pi_def_with_choice]);


val _ = overload_on ("nterm_pmact", ``mk_pmact raw_apply_pi``)
val _ = overload_on ("apply_pi", ``pmact nterm_pmact``)

val _ = set_fixity "·" (Infixr 700)
val _ = overload_on("·",``apply_pi``)

val apply_pi_raw = Q.store_thm(
  "apply_pi_raw",
  `apply_pi = raw_apply_pi`,
  SRW_TAC [][GSYM pmact_bijections, is_pmact_def] THENL [
    Induct_on `x` THEN ASM_SIMP_TAC (psrw_ss()) [raw_apply_pi_def],
    Induct_on `x` THEN
    ASM_SIMP_TAC (psrw_ss()) [pmact_decompose, raw_apply_pi_def],
    SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Induct_on `x` THEN
    SRW_TAC [][raw_apply_pi_def] THEN
    ASM_SIMP_TAC (psrw_ss()) [app_permeq_monotone]
  ])

val apply_pi_thm = RWsave_thm(
  "apply_pi_thm",
  ONCE_REWRITE_RULE [GSYM apply_pi_raw] raw_apply_pi_def);

fun nterm_inst q th = th |> INST_TYPE [alpha |-> ``:'a nterm``]
                         |> Q.INST [q |-> `nterm_pmact`]
val nterm_spec = Q.ISPEC `nterm_pmact`

val apply_pi_decompose =
    save_thm("apply_pi_decompose",nterm_spec pmact_decompose)
val apply_pi_inverse =
    save_thm("apply_pi_inverse",nterm_inst `f` pmact_inverse);
val apply_pi_id = save_thm("apply_pi_id",nterm_spec pmact_id)
val apply_pi_injective =
    save_thm("apply_pi_injective",nterm_inst `pm` pmact_injective);
val apply_pi_eql = save_thm("apply_pi_eql",nterm_inst `pm` pmact_eql);
val apply_pi_eqr = store_thm("apply_pi_eqr",
``(t1 = apply_pi pi t2) ⇔ (apply_pi (REVERSE pi) t1 = t2)``,
METIS_TAC [apply_pi_inverse]);

val nvars_apply_pi = RWstore_thm(
"nvars_apply_pi",
`∀t. nvars (apply_pi pi t) = nvars t`,
Induct THEN SRW_TAC [][])

val _ = export_theory ()
