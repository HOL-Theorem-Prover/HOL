
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open listTheory;
open arithmeticTheory;
open impTheory;
val ect = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "imp2";


val _ = temp_type_abbrev("vname",``:string``);

Datatype:
    com = Assign vname imp$aexp
        | If imp$bexp (com list) (com list)
        | While imp$bexp (com list)
End

val com_size_def = fetch "-" "com_size_def";

Definition cval_def:
    (cval 0 _ _ = NONE) /\
    (cval (t:num) (Assign v a) s = SOME ((v =+ aval a s) s)) /\
    (cval t (If b cs1 cs2) s = pval t (if bval b s then cs1 else cs2) s) /\
    (cval t (While b cs) s = if bval b s then pval (t-1) (cs ++ [(While b cs)]) s else SOME s) /\

    (pval 0 _ _ = NONE) /\
    (pval (t:num) [] s = SOME s) /\
    (pval t (c::cs) s = case cval t c s of
        | NONE => NONE
        | SOME s' => pval t cs s')
Termination
    WF_REL_TAC `inv_image (measure I LEX measure I) (\r. case r of
        | INR (t, cs, _) => (t, com1_size cs)
        | INL (t, c, _) => (t, com_size c))` >>
    rw[]
End

Definition imp2imp2_def:
    (imp2imp2 (SKIP:imp$com) = []) /\
    (imp2imp2 (Assign v a) = [((Assign v a):com)]) /\
    (imp2imp2 (Seq c1 c2) = (imp2imp2 c1) ++ (imp2imp2 c2)) /\
    (imp2imp2 (If b c1 c2) = [(If b (imp2imp2 c1) (imp2imp2 c2))]) /\
    (imp2imp2 (While b c) = [(While b (imp2imp2 c))])
End

Definition p2imp_def:
    (p2imp [] = SKIP) /\
    (p2imp (x::xs) = Seq (imp2imp x) (p2imp xs)) /\
    (imp2imp ((Assign v a):com) = ((Assign v a):imp$com)) /\
    (imp2imp (If b c1s c2s) = (If b (p2imp c1s) (p2imp c2s))) /\
    (imp2imp (While b cs) = (While b (p2imp cs)))
Termination
    WF_REL_TAC `inv_image (measure I) (\r. case r of
        | INR c => com_size c
        | INL cs => com1_size cs)`
End
(* wow terminationa actually worked...I thought it had to be stricly decreasing but I don't think this is *)


Theorem com_lt:
    !c h t. MEM c t ==> com_size c < com1_size (h::t)
Proof
    rw[] >>
    simp[com_size_def] >>
    Induct_on `t` >>
    rw[] >>
    simp[com_size_def] >>
    fs[]
QED

Theorem com_ineq:
    !c cs. MEM c cs ==> com_size c <= com1_size cs
Proof
    rw[] >>
    simp[LESS_OR_EQ] >>
    Cases_on `cs` >>
    fs[MEM]
        >- simp[com_size_def]
        >- simp[com_lt]
QED


(* Theorem pval_NONE[simp]:
    pval 0 cs s = NONE
Proof
    rw[cval_def]
QED *)

Theorem cval_mono:
    (!t1 c s t2. t1 <= t2 /\ cval t1 c s <> NONE ==> cval t1 c s = cval t2 c s) /\
    (!t1 cs s t2. t1 <= t2 /\ pval t1 cs s <> NONE ==> pval t1 cs s = pval t2 cs s)
Proof
    ho_match_mp_tac cval_ind >>
    rw[] >>
    Cases_on `t2`
        >- fs[cval_def]
        >- fs[cval_def]
        >- fs[]
        >- simp[cval_def]
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            gvs[cval_def]
        )
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            gvs[cval_def]
        )
        >- fs[]
        >- (Cases_on `bval b s` >>
            fs[]
                >- (simp[cval_def] >>
                    first_x_assum $ qspec_then `n` assume_tac >>
                    gvs[cval_def]
                )
                >- simp[cval_def]
        )
        >- simp[]
        >- fs[cval_def]
        >- fs[]
        >- simp[cval_def]
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            Cases_on `cval (SUC v26) c s`
                >- gvs[cval_def] (* got lazy trying to do granularly but seems straight forward *)
                >- (gvs[] >>
                    last_x_assum $ qspec_then `SUC n` assume_tac >>
                    Cases_on `cval (SUC n) c s` (* why do I have to do this to force rewrite *)
                        >- fs[]
                        >- (gvs[] >>
                            Cases_on `pval (SUC v26) cs x`
                                >- gvs[cval_def]
                                >- gvs[]
                        )
                )
        )
QED

Theorem pval_concat:
    ! t l1 l2 s. pval t (l1 ++ l2) s = OPTION_BIND (pval t l1 s) (pval t l2)
Proof
    Cases_on `t`
        >- simp[cval_def]
        >- (Induct_on `l1`
            >- simp[cval_def]
            >- (simp[cval_def] >>
                rpt strip_tac >>
                Cases_on `cval (SUC n) h s`
                    >- simp[]
                    >- fs[cval_def]
            )
        )
QED

(* is an equality theorem more useful than an inequality theorem??? *)
Theorem seq_none:
    cval (Seq c c') s t <> NONE ==> cval c s t <> NONE
Proof
    rw[] >>
    fs[impTheory.cval_def] >>
    Cases_on `cval c s t` >>
    fs[]
QED

Theorem equiv_exists:
    !c s t. ?t'. OPTION_MAP FST (cval c s t) = pval t' (imp2imp2 c) s
Proof
    recInduct impTheory.cval_ind >>
    rw[]
        >- (simp[impTheory.cval_def] >>
            simp[imp2imp2_def] >>
            qexists `SUC k` >>
            simp[cval_def]
        )
        >- (simp[impTheory.cval_def] >>
            simp[imp2imp2_def] >>
            qexists `SUC k` >>
            simp[cval_def]
        )
        >- (simp[impTheory.cval_def] >>
            simp[imp2imp2_def] >>
            simp[pval_concat] >>
            Cases_on `cval c1 s t`
                >- (fs[] >>
                    qexists `0` >>
                    simp[cval_def]
                )
                >- (Cases_on `x` >>
                    simp[] >>
                    Cases_on `cval c2 q r`
                        >- (fs[] >>
                            qexists `0` >>
                            simp[cval_def]
                        )
                        >- (Cases_on `x` >>
                            simp[] >>
                            gvs[] >>
                            (* pick a t bigger than both t'' and t' and apply the monotonicity lemma ...do cases on order*)
                            Cases_on `t' <= t''`
                                >- (qspecl_then [`t''`, `imp2imp2 c2`, `q`, `SUC t''`] assume_tac (cj 2 cval_mono) >>
                                    qspecl_then [`t'`, `imp2imp2 c1`, `s`, `SUC t''`] assume_tac (cj 2 cval_mono) >>
                                    gvs[] >>
                                    Cases_on `pval t'' (imp2imp2 c2) q` >>
                                    Cases_on `pval t' (imp2imp2 c1) s` >>
                                    fs[] >>
                                    qexists `SUC t''` >>
                                    qexists `q` >>
                                    simp[]
                                )
                                >- (fs[NOT_LESS_EQUAL] >>
                                    qspecl_then [`t''`, `imp2imp2 c2`, `q`, `SUC t'`] assume_tac (cj 2 cval_mono) >>
                                    qspecl_then [`t'`, `imp2imp2 c1`, `s`, `SUC t'`] assume_tac (cj 2 cval_mono) >>
                                    gvs[] >>
                                    Cases_on `pval t'' (imp2imp2 c2) q` >>
                                    Cases_on `pval t' (imp2imp2 c1) s` >>
                                    fs[] >>
                                    qexists `SUC t'` >>
                                    qexists `q` >>
                                    simp[]
                                )
                        )
                )
        )
        >- (simp[impTheory.cval_def] >>
            simp[imp2imp2_def] >>
            Cases_on `t'`
                >- (qexists `0` >> simp[cval_def])
                >- (qexists `SUC n` >>
                    simp[cval_def] >>
                    Cases_on `pval (SUC n) (imp2imp2 c1) s` >>
                    simp[]
                )
        )
        >- (simp[impTheory.cval_def] >>
            simp[imp2imp2_def] >>
            Cases_on `t'`
                >- (qexists `0` >> simp[cval_def])
                >- (qexists `SUC n` >>
                    simp[cval_def] >>
                    Cases_on `pval (SUC n) (imp2imp2 c2) s` >>
                    simp[]
                )
        )
        >- (Cases_on `bval b s` >>
            Cases_on `t`
                >- (simp[Once impTheory.cval_def] >>
                    qexists `0` >>
                    simp[cval_def]
                )
                >- (fs[] >>
                    simp[Once impTheory.cval_def] >>
                    simp[imp2imp2_def] >>
                    qexists `SUC t'` >>
                    simp[cval_def] >>
                    Cases_on `pval t' (imp2imp2 c ⧺ [While b (imp2imp2 c)]) s` >>
                    simp[]
                )
                >- (simp[Once impTheory.cval_def] >>
                    qexists `SUC k` >>
                    simp[imp2imp2_def] >>
                    simp[cval_def]
                )
                >- (simp[Once impTheory.cval_def] >>
                    qexists `SUC k` >>
                    simp[imp2imp2_def] >>
                    simp[cval_def]
                )
        )
QED

Theorem conc_lemma:
    !s t. OPTION_MAP FST (imp$cval (p2imp (cs ++ ds)) s t) = OPTION_MAP FST (imp$cval (Seq (p2imp cs) (p2imp ds)) s t)
Proof
    Induct_on `cs` (* I wonder if it would be better to induct on ds??? *)
        >- (simp[p2imp_def] >>
            simp[impTheory.cval_def]
        )
        >- (strip_tac >>
            simp[p2imp_def] >>
            simp[impTheory.cval_def] >>
            rpt strip_tac >>
            Cases_on `cval (imp2imp h) s t`
                >- simp[]
                >- (simp[] >>
                    Cases_on `x` >>
                    simp[] >>
                    Cases_on `cval (p2imp cs) q r`
                        >- (simp[] >>
                            simp[impTheory.cval_def]
                        )
                        >- (simp[] >>
                            Cases_on `x` >>
                            simp[] >>
                            simp[impTheory.cval_def]
                        )
                )
        )
QED

Theorem equiv_exists2:
    (!t1 c s. cval t1 c s <> NONE ==> ?t2. cval t1 c s =  OPTION_MAP FST (cval (imp2imp c) s t2)) /\
    (!t1 cs s. pval t1 cs s <> NONE ==> ?t2. pval t1 cs s = OPTION_MAP FST (cval (p2imp cs) s t2))
Proof
    ho_match_mp_tac cval_ind >>
    rw[]
        >- fs[cval_def]
        >- (simp[p2imp_def] >>
            qexists `SUC v8` >>
            simp[cval_def, impTheory.cval_def]
        )
        >- (simp[cval_def] >>
            simp[p2imp_def] >>
            simp[impTheory.cval_def] >>
            fs[cval_def] >>
            rfs[]
        )
        >- (simp[cval_def] >>
            simp[p2imp_def] >>
            simp[impTheory.cval_def] >>
            fs[cval_def] >>
            rfs[]
        )
        (* try and simplify and apply conc_lemma before doing case split so don't have to repeat so much work *)
        >- (fs[cval_def] >>
            last_x_assum mp_tac >>
            rewrite_tac[conc_lemma] >>
            simp[p2imp_def] >>
            simp[Once impTheory.cval_def] >>
            simp[Once impTheory.cval_def] >>
            Cases_on `bval b s` >>
            Cases_on `pval v10 (cs ⧺ [While b cs]) s`
                >- fs[]
                >- (rw[] >>
                    fs[CaseEq"option"] >>
                    Cases_on `v` >>
                    fs[] >>
                    fs[CaseEq"option"] >>
                    Cases_on `v` >> (* why does v show up again *)
                    fs[] >>
                    qexists `SUC t2` >>
                    qexists `z` >>
                    simp[] >>
                    simp[Once impTheory.cval_def] >>
                    simp[Once impTheory.cval_def] >>
                    fs[Once impTheory.cval_def]
                )
                >- simp[Once impTheory.cval_def] (* not entirely sure why this simp solves the subgoal *)
                >- simp[Once impTheory.cval_def] (* similarly *)
        )
        >- fs[cval_def]
        >- (simp[p2imp_def] >>
            qexists `t2` >>
            simp[impTheory.cval_def] >>
            simp[cval_def]
        )
        >- (simp[cval_def] >>
            Cases_on `cval (SUC v26) c s`
                >- gvs[cval_def] (* contradiction in assumptions *)
                >- (simp[CaseEq"option"] >>
                    simp[p2imp_def] >>
                    simp[impTheory.cval_def] >>
                    fs[cval_def] >>
                    Cases_on `z` >>
                    fs[] >>
                    qspecl_then [`(imp2imp c)`, `s`, `t2'`, `q`, `r`] assume_tac arb_resc >>
                    rfs[] >>
                    pop_assum $ qspec_then `t2` assume_tac >>
                    fs[] >>
                    qexists `t'` >>
                    simp[]
                )
        )
QED

val _ = export_theory();
