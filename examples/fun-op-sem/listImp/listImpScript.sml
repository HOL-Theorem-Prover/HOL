
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open listTheory arithmeticTheory optionTheory;
open impTheory;

val _ = new_theory "listImp";

Type vname[local] = ``:string``;

Datatype:
  com = Assign vname imp$aexp
    | If imp$bexp (com list) (com list)
    | While imp$bexp (com list)
End

val com_size_def = fetch "-" "com_size_def";

Definition pval_def:
  (cval (0:num) _ _ = NONE) /\
  (cval t (Assign v a) s = SOME ((v =+ aval a s) s)) /\
  (cval t (If b cs1 cs2) s = pval t (if bval b s then cs1 else cs2) s) /\
  (cval t (While b cs) s =
    if bval b s then pval (t-1) (cs ++ [(While b cs)]) s
    else SOME s) /\
  (pval (0:num) _ _ = NONE) /\
  (pval t [] s = SOME s) /\
  (pval t (c::cs) s = case cval t c s of
    | NONE => NONE
    | SOME s' => pval t cs s')
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I) (\r. case r of
    | INR (t, cs, _) => (t, com1_size cs)
    | INL (t, c, _) => (t, com_size c))` >>
  rw[]
End

Definition imp_to_listImp_def[simp]:
  (imp_to_listImp (SKIP:imp$com) = []) /\
  (imp_to_listImp (Assign v a) = [(Assign v a):com]) /\
  (imp_to_listImp (Seq c1 c2) = imp_to_listImp c1 ++ imp_to_listImp c2) /\
  (imp_to_listImp (If b c1 c2) =
    [If b (imp_to_listImp c1) (imp_to_listImp c2)]) /\
  (imp_to_listImp (While b c) = [While b (imp_to_listImp c)])
End

Definition listImp_to_imp_def[simp]:
  (prog_to_imp [] = SKIP) /\
  (prog_to_imp (x::xs) = Seq (com_to_imp x) (prog_to_imp xs)) /\
  (com_to_imp ((Assign v a):com) = (Assign v a):imp$com) /\
  (com_to_imp (If b c1s c2s) = If b (prog_to_imp c1s) (prog_to_imp c2s)) /\
  (com_to_imp (While b cs) = While b (prog_to_imp cs))
Termination
  WF_REL_TAC `inv_image (measure I) (\r. case r of
    | INR c => com_size c
    | INL cs => com1_size cs)`
End

Theorem pval_none[simp]:
    pval 0 cs s = NONE /\ cval 0 c s = NONE
Proof
    rw[pval_def]
QED

Theorem com_lt:
  !c h t. MEM c t ==> com_size c < com1_size (h::t)
Proof
  rw[] >>
  simp[com_size_def] >>
  Induct_on `t` >>
  rw[] >>
  fs[com_size_def]
QED

Theorem com_leq:
  !c cs. MEM c cs ==> com_size c <= com1_size cs
Proof
  rw[] >>
  simp[LESS_OR_EQ] >>
  Cases_on `cs` >>
  fs[MEM] >>
  simp[com_size_def, com_lt]
QED

Theorem pval_pos:
  (!t c s r. cval t c s = SOME r ==> ?k. t = SUC k) /\
  (!t cs s r. pval t cs s = SOME r ==> ?k. t = SUC k)
Proof
  ho_match_mp_tac pval_ind >>
  rw[]
QED

Theorem pval_mono:
  (!t1 c s t2.
    t1 <= t2 /\ cval t1 c s <> NONE ==> cval t1 c s = cval t2 c s) /\
  (!t1 cs s t2.
    t1 <= t2 /\ pval t1 cs s <> NONE ==> pval t1 cs s = pval t2 cs s)
Proof
  ho_match_mp_tac pval_ind >>
  rw[] >>
  Cases_on `t2` >>
  gvs[pval_def]
    >- (Cases_on `bval b s` >> fs[])
    >- (fs[CaseEq"option"] >>
        Cases_on `cval (SUC v26) c s` >>
        fs[] >>
        rpt $ last_x_assum $ qspec_then `SUC n` assume_tac >>
        qexists `x` >>
        rfs[]
    )
QED

Theorem pval_concat:
  ! t l1 l2 s. pval t (l1 ++ l2) s = OPTION_BIND (pval t l1 s) (pval t l2)
Proof
  Cases_on `t` >>
  simp[pval_def] >>
  Induct_on `l1` >>
  simp[pval_def] >>
  rpt strip_tac >>
  Cases_on `cval (SUC n) h s` >>
  fs[pval_def]
QED

Theorem equiv_exists:
  !c s t. ?t'. OPTION_MAP FST (cval c s t) = pval t' (imp_to_listImp c) s
Proof
  rpt strip_tac >>
  Cases_on `cval c s t`
    >- (qexists `0` >> simp[pval_def])
    >- (pop_assum mp_tac >>
        qid_spec_tac `x` >> qid_spec_tac `t` >>
        qid_spec_tac `s` >> qid_spec_tac `c` >>
        recInduct cval_ind >>
        rw[] >>~-
        ([`While _ _`],
          Cases_on `bval b s` >>
          Cases_on `t`
            >- fs[Once cval_def]
            >- (qpat_x_assum `cval _ _ _ = _` mp_tac >>
                simp[Once cval_def] >>
                disch_then assume_tac >>
                fs[] >>
                qexists `SUC t'` >>
                fs[pval_def, CaseEq"option"] >>
                disj2_tac >>
                qexists `FST x` >>
                simp[]
            ) >>
            fs[Once cval_def] >>
            qexists `SUC k` >>
            gvs[pval_def]
        ) >>
        simp[cval_def] >>~-
        ([`Seq _ _`],
          fs[cval_def, CaseEq"option"] >>
          simp[pval_concat] >>
          Cases_on `v` >>
          fs[] >>
          qspecl_then
            [`t'`, `imp_to_listImp c2`, `q`, `t' + t''`]
            assume_tac (cj 2 pval_mono) >>
          qspecl_then
            [`t''`, `imp_to_listImp c1`, `s`, `t' + t''`]
            assume_tac (cj 2 pval_mono) >>
          last_x_assum $ assume_tac o GSYM >>
          last_x_assum $ assume_tac o GSYM >>
          qexists `t' + t''` >>
          qexists `q` >>
          fs[]
        ) >>~-
        ([`If _ _ _`],
          gvs[cval_def] >>
          qpat_x_assum `SOME _ = pval _ _ _` $ assume_tac o GSYM >>
          drule (cj 2 pval_pos) >>
          rw[] >>
          qexists `SUC k` >>
          simp[pval_def]
        ) >>
        qexists `SUC t` >>
        gvs[cval_def, pval_def]
    )
QED

Theorem conc_lemma:
  !s t.
    cval (prog_to_imp (cs ++ ds)) s t =
    cval (Seq (prog_to_imp cs) (prog_to_imp ds)) s t
Proof
  Induct_on `cs` >>
  rpt strip_tac >>
  simp[cval_def] >>
  Cases_on `cval (com_to_imp h) s t` >>
  simp[] >>
  Cases_on `x` >>
  simp[cval_def]
QED

Theorem equiv_exists2:
  (!t1 c s.
    cval t1 c s <> NONE ==>
    ?t2. cval t1 c s =  OPTION_MAP FST (cval (com_to_imp c) s t2)) /\
  (!t1 cs s.
    pval t1 cs s <> NONE ==>
    ?t2. pval t1 cs s = OPTION_MAP FST (cval (prog_to_imp cs) s t2))
Proof
  ho_match_mp_tac pval_ind >>
  rw[] >>
  fs[pval_def] >>~-
  ([`While _ _`],
    gvs[conc_lemma] >>
    Cases_on `bval b s` >>
    Cases_on `pval v10 (cs ⧺ [While b cs]) s` >>
    fs[Once cval_def, CaseEq"option"] >>
    Cases_on `v` >>
    gvs[] >>
    qexists `SUC t2` >>
    qexists `z` >>
    simp[Once cval_def]
  ) >>
  fs[cval_def] >>~-
  ([`if _ then _ else _`],
    gvs[pval_def] >>
    qexists `t2` >>
    simp[]
  ) >>
  Cases_on `cval (SUC v26) c s` >>
  gvs[pval_def] >>
  Cases_on `z` >>
  drule arb_resc >>
  disch_then $ qspec_then `t2'` assume_tac >>
  fs[] >>
  qexists `t'` >>
  simp[]
QED

val _ = export_theory();
