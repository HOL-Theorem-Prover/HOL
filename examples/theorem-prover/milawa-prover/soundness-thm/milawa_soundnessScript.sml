
open HolKernel Parse boolLib bossLib; val _ = new_theory "milawa_soundness";

(* open prog_armTheory prog_ppcTheory prog_x86Theory; *)

open helperLib set_sepTheory progTheory;
open lisp_correctnessTheory milawa_proofpTheory lisp_semanticsTheory;

val R_exec_T_11 = prove(
  ``!x y. R_exec x y ==> !z. SND y /\ R_exec x z ==> (y = z)``,
  HO_MATCH_MP_TAC R_exec_ind \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [R_exec_cases]
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC R_ev_T_11
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC   \\ FULL_SIMP_TAC std_ss []);

val milawa_soundness_thm = save_thm("milawa_soundness_thm",let
  val th1 = milawa_main_soundness
  val th = jitawa_correctness_thm
  val assum = fst (dest_imp (concl th1))
  val pc = find_term (can (match_term ``zPC xxx``)) (concl th |> rand)
  val th = Q.INST [`input`|->`STRCAT MILAWA_CORE_TEXT rest`] th
  val th = SPEC_BOOL_FRAME_RULE th assum
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zERROR_MESSAGE ex \/
        let output = compute_output cmds in
          cond (EVERY line_ok output) * ~zS * ^pc * zLISP_OUTPUT
            (IO_STREAMS "" (output_to_string output ++ "SUCCESS\n"),T)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,LET_DEF] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC SEP_IMP_DISJ \\ SIMP_TAC std_ss [SEP_IMP_REFL]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC th1 \\ IMP_RES_TAC R_exec_T_11
    \\ FULL_SIMP_TAC std_ss [LET_DEF])
  val th = MP th lemma
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [] |> REWRITE_RULE [SPEC_MOVE_COND]
  val assum2 = fst (dest_imp (concl th))
  val goal = mk_imp(assum,assum2)
  val lemma = prove(goal,SIMP_TAC std_ss [R_exec_TERMINATES_def] \\ METIS_TAC [th1])
  val th = DISCH_ALL (MP th (UNDISCH lemma))
  val th = REWRITE_RULE [GSYM SPEC_MOVE_COND] th
  in th end);

val _ = export_theory();
