open preamble MiniMLTheory MiniMLTerminationTheory;
open typeSoundTheory bigSmallEquivTheory determTheory untypedSafetyTheory;

val _ = new_theory "bigBigEquiv"

val pmatch_pmatch' = Q.prove (
`(!envc p v env. (pmatch envc p v env ≠ Match_type_error) ⇒
   (pmatch envc p v env = pmatch' p v env)) ∧
 (!envc ps vs env. (pmatch_list envc ps vs env ≠ Match_type_error) ⇒
   (pmatch_list envc ps vs env = pmatch_list' ps vs env))`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [pmatch_def, pmatch'_def] >|
[Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     Cases_on `lookup n' envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `pmatch envc p v env` >>
     fs [] >>
     Cases_on `pmatch' p v env` >>
     fs []]);

val evaluate_to_evaluate' = Q.prove (
`(!envc env e r. evaluate envc env e r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate' env e r) ∧
 (!envc env es r. evaluate_list envc env es r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate_list' env es r) ∧
 (!envc env v p r. evaluate_match envc env v p r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate_match' env v p r)`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate'_cases] >>
fs [] >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val evaluate'_to_evaluate = Q.prove (
`(!env e r. evaluate' env e r ⇒
   !envc. ¬evaluate envc env e (Rerr Rtype_error) ⇒ evaluate envc env e r) ∧
 (!env es r. evaluate_list' env es r ⇒
   !envc. ¬evaluate_list envc env es (Rerr Rtype_error) ⇒
   evaluate_list envc env es r) ∧
 (!env v p r. evaluate_match' env v p r ⇒
   !envc. ¬evaluate_match envc env v p (Rerr Rtype_error) ⇒
   evaluate_match envc env v p r)`,
HO_MATCH_MP_TAC evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val type_no_error = Q.prove (
`!tenvC tenv e t envC env r.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_e tenvC tenv e t
  ⇒
  ¬evaluate envC env e (Rerr Rtype_error)`,
rw [GSYM small_big_exp_equiv] >>
metis_tac [untyped_safety_exp, small_exp_determ, exp_type_soundness]);

val evaluate_evaluate'_thm = Q.store_thm ("evaluate_evaluate'_thm",
`!tenvC envC tenv e t cenv env r.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_e tenvC tenv e t
  ⇒
  (evaluate' env e r = evaluate envC env e r)`,
metis_tac [type_no_error, evaluate'_to_evaluate, evaluate_to_evaluate']);

val _ = export_theory ()
