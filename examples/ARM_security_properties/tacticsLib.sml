structure tacticsLib :> tacticsLib =
struct

open HolKernel boolLib bossLib;

val UNDISCH_MATCH_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (MP_TAC th)));
val UNDISCH_ALL_TAC = (REPEAT (UNDISCH_MATCH_TAC ``X``));
val SPEC_ASSUM_TAC = fn (MATCH, SLIST) => (REPEAT (PAT_ASSUM MATCH (fn th => ASSUME_TAC (SPECL SLIST th))));
val SPEC_AND_KEEP_ASSUM_TAC = fn (MATCH, SLIST) => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th THEN ASSUME_TAC (SPECL SLIST th)));
val THROW_AWAY_TAC = fn MATCH => (REPEAT (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th)));
val THROW_ONE_AWAY_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th));
val THROW_AWAY_IMPLICATIONS_TAC = (REPEAT (WEAKEN_TAC is_imp));
val ASSERT_ASSUM_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th));
val PROTECTED_RW_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (RW_TAC (srw_ss()) [] THEN ASSUME_TAC th)));
val PROTECTED_OR_RW_TAC = fn RWLIST => (PAT_ASSUM ``X \/ Y`` (fn th => (RW_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (RW_TAC (srw_ss()) RWLIST);
val PROTECTED_OR_SIMP_TAC = fn RWLIST => (PAT_ASSUM ``X \/ Y`` (fn th => (FULL_SIMP_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (FULL_SIMP_TAC (srw_ss()) RWLIST);
val CONJ_ASSUM_TAC = (REPEAT (PAT_ASSUM ``A /\ B`` (fn th => ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th))));
val FORCE_REWRITE_TAC = (fn thm =>
                             let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val COMB (ab, c) = dest_term trm
                                 val COMB (a, b) = dest_term ab
                             in SUBGOAL_THEN c (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end);
val FORCE_REV_REWRITE_TAC = (fn thm =>
                             let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val COMB (ab, c) = dest_term trm
                                 val COMB (a, b) = dest_term ab
                             in SUBGOAL_THEN b (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end);


val ASSUME_SPECL_TAC =
fn l => fn thm => ASSUME_TAC (SPECL l thm);

val ASSUME_SIMP_TAC =
fn l => fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) l thm);

val IMP_RES_SIMP_TAC =
fn l => fn thm => IMP_RES_TAC (SIMP_RULE (srw_ss()) l thm);


val ASSUME_SPEC_TAC =
fn l => fn thm => ASSUME_TAC (SPEC l thm);


val ASSUME_SPECL_SIMP_TAC =
fn l => fn sthms => fn thm => ASSUME_TAC (SPECL l (SIMP_RULE (srw_ss()) sthms thm));

val IMP_RES_SPEC_TAC =
fn l => fn thm => IMP_RES_TAC (SPEC l thm);

val IMP_RES_SPECL_TAC =
fn l => fn thm => IMP_RES_TAC (SPECL l thm);

val MP_SPEC_TAC =
fn l => fn thm => MP_TAC (SPEC l thm);

val MP_SPECL_TAC =
fn l => fn thm => MP_TAC (SPECL l thm);

val ASSUME_SPECL_INST_TAC =
 fn sl => fn tl => fn thm =>
	     ASSUME_TAC (SPECL sl (INST_TYPE tl thm))


val ASSUME_SPECL_GEN_REWRITE_TAC =
 fn (l , thm, simps) => ASSUME_TAC (SPECL
					l (GEN_ALL (REWRITE_RULE simps thm)));

end
