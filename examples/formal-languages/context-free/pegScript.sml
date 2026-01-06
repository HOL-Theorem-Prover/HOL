Theory peg
Ancestors
  grammar finite_map location list rich_list
Libs
  boolSimps

(* Based on
     Koprowski and Binzstok, "TRX: A Formally Verified Parser Interpreter".
     LMCS vol 7, no. 2. 2011.
     DOI: 10.2168/LMCS-7(2:18)2011
*)

Datatype:
  pegsym =
    empty 'c
  | any  ('a # locs -> 'c)
  | tok ('a -> bool) ('a # locs -> 'c)
  | nt ('b inf) ('c -> 'c)
  | seq pegsym pegsym ('c  -> 'c -> 'c)
  | choice pegsym pegsym ('c + 'c -> 'c)
  | rpt pegsym ('c list -> 'c)
  | not pegsym 'c
  | error 'e
End

Datatype:
  peg = <| start : ('a,'b,'c,'e) pegsym ;
           anyEOF : 'e ;
           tokFALSE : 'e ; tokEOF : 'e;
           notFAIL : 'e;
           rules : 'b inf |-> ('a,'b,'c,'e) pegsym |>
End

Datatype:
  pegresult = Success 'a 'c ((locs # 'e) option)
            | Failure locs 'e
End
Definition isSuccess_def[simp]:
  isSuccess (Success _ _ _) = T ∧
  isSuccess (Failure _ _) = F
End
Definition isFailure_def[simp]:
  isFailure (Success _ _ _) = F ∧
  isFailure (Failure _ _) = T
End

Definition resultmap_def[simp]:
  resultmap f (Success a c eo) = Success a (f c) eo ∧
  resultmap f (Failure fl fe) = Failure fl fe
End
Theorem resultmap_EQ_Success :
  resultmap f r = Success a x eo ⇔ ∃x0. r = Success a x0 eo ∧ x = f x0
Proof
  Cases_on ‘r’ >> simp[] >> metis_tac[]
QED

Theorem resultmap_EQ_Failure[simp]:
  (resultmap f r = Failure fl fe ⇔ r = Failure fl fe) ∧
  (Failure fl fe = resultmap f r ⇔ r = Failure fl fe)
Proof
  Cases_on ‘r’ >> simp[] >> metis_tac[]
QED

Theorem resultmap_I[simp]:
  resultmap I r = r
Proof
  Cases_on ‘r’ >> simp[]
QED

Definition MAXerr_def:
  MAXerr (fl1, fe1) (fl2, fe2) =
  if locsle fl1 fl2 then (fl2, fe2) else (fl1,fe1)
End

Definition optmax_def:
  optmax f NONE NONE = NONE ∧
  optmax f NONE (SOME x) = SOME x ∧
  optmax f (SOME x) NONE = SOME x ∧
  optmax f (SOME x) (SOME y) = SOME (f x y)
End

Theorem result_cases[local] = TypeBase.nchotomy_of “:(α,β,γ) pegresult”

Overload EOF[local] = “Locs EOFpt EOFpt”
Definition sloc_def:
  sloc [] = EOF ∧
  sloc (h::t) = SND h
End

Theorem sloc_thm[simp]:
  sloc [] = EOF ∧
  sloc ((c,l) :: t) = l
Proof
  simp[sloc_def]
QED


(* Option type should be replaced with sum type (loc. for NONE *)
Inductive peg_eval:
[~empty:]
  (∀s c. peg_eval G (s, empty c) (Success s c NONE))
[~nt:]
  (∀n s f res.
       n ∈ FDOM G.rules ∧ peg_eval G (s, G.rules ' n) res ⇒
       peg_eval G (s, nt n f) (resultmap f res))
[~any_success:]
  (∀h t f. peg_eval G (h::t, any f) (Success t (f h) NONE))
[~any_failure:]
  (∀f. peg_eval G ([], any f) (Failure EOF G.anyEOF))
[~tok_success:]
  (∀e t P f.
     P (FST e) ⇒ peg_eval G (e::t, tok P f) (Success t (f e) NONE))
[~tok_failureF:]
  (∀h t P f.
     ¬P (FST h) ⇒
     peg_eval G (h::t, tok P f) (Failure (SND h) G.tokFALSE))
[~tok_failureEOF:]
  (∀P f. peg_eval G ([], tok P f) (Failure EOF G.tokEOF))
[~not_success:]
  (∀e s c fr.
     peg_eval G (s, e) fr ∧ isFailure fr ⇒
     peg_eval G (s, not e c) (Success s c NONE))
[~not_failure:]
  (∀e s r c.
     peg_eval G (s, e) r ∧ isSuccess r ⇒
     peg_eval G (s, not e c) (Failure (sloc s) G.notFAIL))
[~seq_fail1:]
  (∀e1 e2 s f fl fe.
     peg_eval G (s, e1) (Failure fl fe) ⇒
     peg_eval G (s, seq e1 e2 f) (Failure fl fe))
[~seq_fail2:]
  (∀e1 e2 f s0 eo s1 c1 fl fe.
     peg_eval G (s0, e1) (Success s1 c1 eo) ∧
     peg_eval G (s1, e2) (Failure fl fe) ⇒
     peg_eval G (s0, seq e1 e2 f) (Failure fl fe))
[~seq_success:]
  (∀e1 e2 s0 s1 s2 c1 c2 f eo1 eo2.
     peg_eval G (s0, e1) (Success s1 c1 eo1) ∧
     peg_eval G (s1, e2) (Success s2 c2 eo2) ⇒
     peg_eval G (s0, seq e1 e2 f) (Success s2 (f c1 c2) eo2))
[~choice_fail:]
  (∀e1 e2 s f fl1 fe1 fl2 fe2.
     peg_eval G (s, e1) (Failure fl1 fe1) ∧
     peg_eval G (s, e2) (Failure fl2 fe2) ⇒
     peg_eval G (s, choice e1 e2 f)
              (UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))))
[~choice_success1:]
  (∀e1 e2 s0 f s r eo.
     peg_eval G (s0, e1) (Success s r eo) ⇒
     peg_eval G (s0, choice e1 e2 f) (Success s (f (INL r)) eo))
[~choice_success2:]
  (∀e1 e2 s0 s r eo f fl fe.
     peg_eval G (s0, e1) (Failure fl fe) ∧
     peg_eval G (s0, e2) (Success s r eo) ⇒
     peg_eval G (s0, choice e1 e2 f)
              (Success s (f (INR r)) (optmax MAXerr (SOME (fl,fe)) eo)))
[~error:]
  (∀e s. peg_eval G (s, error e) (Failure (sloc s) e))
[~rpt:]
  (∀e f s s1 list err.
     peg_eval_list G (s, e) (s1,list,err) ⇒
     peg_eval G (s, rpt e f) (Success s1 (f list) (SOME err)))
[~list_nil:]
  (∀e s fl fe. peg_eval G (s, e) (Failure fl fe) ⇒
               peg_eval_list G (s, e) (s,[],(fl,fe)))
[~list_cons:]
  (∀e eo0 eo s0 s1 s2 c cs.
     peg_eval G (s0, e) (Success s1 c eo0) ∧
     peg_eval_list G (s1, e) (s2,cs,eo) ⇒
     peg_eval_list G (s0, e) (s2,c::cs,eo))
End

val fprod = HO_REWR_CONV pairTheory.FORALL_PROD
Theorem peg_eval_strongind' =
  peg_eval_strongind
    |> Q.SPECL [`G`, `\es0 r. P1 (FST es0) (SND es0) r`,
                ‘\es0 sr. P2 (FST es0) (SND es0) (FST sr)
                             (FST $ SND sr)
                             (SND $ SND sr)’]
    |> SIMP_RULE (srw_ss()) []
    |> UNDISCH |> CONJ_PAIR
    |> (SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD] ##
        CONV_RULE (fprod THENC
                   LAST_FORALL_CONV (fprod THENC LAST_FORALL_CONV fprod)))
    |> uncurry CONJ
    |> SIMP_RULE (srw_ss()) []
    |> DISCH_ALL;

Theorem UNCURRY_Failure_EQ_Success[simp]:
  UNCURRY Failure fle ≠ Success s r eo
Proof
  Cases_on ‘fle’ >> simp[]
QED

Theorem IS_PREFIX_MEM:
  l1 ≼ l2 ∧ MEM e l1 ⇒ MEM e l2
Proof
  simp[IS_PREFIX_APPEND, PULL_EXISTS]
QED

Theorem peg_eval_suffix0[local]:
  (∀s0 e sr.
     peg_eval G (s0,e) sr ⇒
     (∀s r eo.
       sr = Success s r eo ⇒ IS_SUFFIX s0 s) ∧
     (∀fl fe. sr = Failure fl fe ∧ fl ≠ EOF ⇒ MEM fl (MAP SND s0))) ∧
  ∀s0 e s rl err.
    peg_eval_list G (s0,e) (s,rl,err) ⇒ IS_SUFFIX s0 s
Proof
  HO_MATCH_MP_TAC peg_eval_strongind' THEN
  SRW_TAC [][IS_SUFFIX_compute, IS_PREFIX_APPEND3, IS_PREFIX_REFL] THEN
  gvs[resultmap_EQ_Success] >~
  [‘UNCURRY Failure (MAXerr (fl1,_) (fl2,_))’]
  >- (Cases_on ‘locsle fl1 fl2’ >> gvs[MAXerr_def]) >~
  [‘isSuccess sr’, ‘MEM (sloc s0) (MAP SND s0)’]
  >- (Cases_on ‘s0’ >> gvs[sloc_def]) >~
  [‘sloc s0 ≠ EOF’, ‘MEM (sloc s0) (MAP SND s0)’]
  >- (Cases_on ‘s0’ >> gvs[sloc_def]) >~
  [‘MEM fl (MAP SND s0)’, ‘REVERSE s1 ≼ REVERSE s0’]
  >- (gvs[MEM_MAP] >>
      metis_tac[IS_PREFIX_MEM, MEM_REVERSE]) >>
  metis_tac [IS_PREFIX_TRANS]
QED

(* Theorem 3.1 *)
Theorem peg_eval_suffix =
  peg_eval_suffix0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [GSYM CONJ_ASSOC]

(* Theorem 3.2 *)
Theorem peg_deterministic:
  (∀s0 e sr. peg_eval G (s0,e) sr ⇒
               ∀sr'. peg_eval G (s0,e) sr' ⇔ sr' = sr) ∧
  ∀s0 e s rl err.
    peg_eval_list G (s0,e) (s,rl,err) ⇒
    ∀srl'. peg_eval_list G (s0,e) srl' ⇔ srl' = (s,rl,err)
Proof
  HO_MATCH_MP_TAC peg_eval_strongind' THEN SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [peg_eval_cases] THEN SRW_TAC [][] THEN
  csimp[] >>
  TRY (Q.MATCH_ASSUM_RENAME_TAC ‘isSuccess result’ >>
       Cases_on ‘result’ >> fs[]) THEN
  TRY (Q.MATCH_ASSUM_RENAME_TAC ‘isFailure result’ >>
       Cases_on ‘result’ >> fs[])
QED

(* Lemma 3.3 *)
Theorem peg_badrpt:
  peg_eval G (s0,e) (Success s0 r eo) ⇒ ∀r. ¬peg_eval G (s0, rpt e f) r
Proof
  strip_tac >> simp[Once peg_eval_cases] >>
  rpt strip_tac >> dxrule_then assume_tac $ cj 2 peg_deterministic  >>
  drule peg_eval_list_cons >> simp[]
QED

Inductive peg0:
  (∀c. peg0 G (empty c)) ∧

  (* any *)
  (∀f. peggt0 G (any f)) ∧
  (∀f. pegfail G (any f)) ∧

  (* tok *)
  (∀t f. peggt0 G (tok t f)) ∧
  (∀t f. pegfail G (tok t f)) ∧

  (* rpt *)
  (∀e f. pegfail G e ⇒ peg0 G (rpt e f)) ∧
  (∀e f. peggt0 G e ⇒ peggt0 G (rpt e f)) ∧

  (* nt rules *)
  (∀n f. n ∈ FDOM G.rules ∧ peg0 G (G.rules ' n) ⇒
         peg0 G (nt n f)) ∧
  (∀n f. n ∈ FDOM G.rules ∧ peggt0 G (G.rules ' n) ⇒
         peggt0 G (nt n f)) ∧
  (∀n f. n ∈ FDOM G.rules ∧ pegfail G (G.rules ' n) ⇒
         pegfail G (nt n f)) ∧

  (* seq rules *)
  (∀e1 e2 f. pegfail G e1 ∨ (peg0 G e1 ∧ pegfail G e2) ∨
             (peggt0 G e1 ∧ pegfail G e2) ⇒
             pegfail G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∧ (peg0 G e2 ∨ peggt0 G e2) ∨
             (peg0 G e1 ∨ peggt0 G e1) ∧ peggt0 G e2 ⇒
             peggt0 G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peg0 G e1 ∧ peg0 G e2 ⇒ peg0 G (seq e1 e2 f)) ∧

  (* choice rules *)
  (∀e1 e2 f. peg0 G e1 ∨ (pegfail G e1 ∧ peg0 G e2) ⇒
             peg0 G (choice e1 e2 f)) ∧
  (∀e1 e2 f. pegfail G e1 ∧ pegfail G e2 ⇒ pegfail G (choice e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∨ (pegfail G e1 ∧ peggt0 G e2) ⇒
             peggt0 G (choice e1 e2 f)) ∧

  (* not *)
  (∀e c. pegfail G e ⇒ peg0 G (not e c)) ∧
  (∀e c. peg0 G e ∨ peggt0 G e ⇒ pegfail G (not e c)) ∧

  (* error *)
  (∀e. pegfail G (error e))
End

Theorem peg0_error[simp]:
  ¬peg0 G (error e)
Proof
  simp[Once peg0_cases]
QED

Theorem peg_eval_suffix':
  peg_eval G (s0,e) (Success s c eo) ⇒
  s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0
Proof
  strip_tac >>
  drule_then strip_assume_tac (cj 1 peg_eval_suffix) >>
  Cases_on `s0 = s` >> gvs[] >>
  gvs[IS_SUFFIX_compute] >>
  imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >>
  strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]
QED

Theorem peg_eval_list_suffix':
  peg_eval_list G (s0, e) (s,rl,err) ⇒
  s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0
Proof
  strip_tac >>
  drule_then strip_assume_tac (cj 3 peg_eval_suffix) >>
  Cases_on `s0 = s` >> gvs[] >>
  fs[IS_SUFFIX_compute] >> imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >> strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]
QED

fun rule_match th = FIRST (List.mapPartial (total MATCH_MP_TAC)
                           (th |> SPEC_ALL |> CONJUNCTS))

Theorem FORALL_result:
  (∀r. P r) ⇔ (∀a c eo. P (Success a c eo)) ∧ (∀fl fe. P (Failure fl fe))
Proof
  rw[EQ_IMP_THM] >> Cases_on ‘r’ >> simp[]
QED

Theorem EXISTS_result:
  (∃r. P r) ⇔ (∃a c eo. P (Success a c eo)) ∨ (∃fl fe. P (Failure fl fe))
Proof
  rw[EQ_IMP_THM] >- (Cases_on ‘r’ >> metis_tac[]) >> metis_tac[]
QED

Theorem lemma4_1a0[local]:
  (∀s0 e r.
     peg_eval G (s0, e) r ⇒
     (∀c eo. r = Success s0 c eo ⇒ peg0 G e) ∧
     (isFailure r ⇒ pegfail G e) ∧
     (∀s c eo. r = Success s c eo ∧ LENGTH s < LENGTH s0 ⇒ peggt0 G e)) ∧
  (∀s0 e s rl err.
     peg_eval_list G (s0,e) (s,rl,err) ⇒
     (s0 = s ⇒ pegfail G e) ∧
     (LENGTH s < LENGTH s0 ⇒ peggt0 G e))
Proof
  ho_match_mp_tac peg_eval_strongind' >>
  simp[peg0_rules, FORALL_result, pairTheory.FORALL_PROD] >>
  rpt conj_tac
  >- (rpt strip_tac >> imp_res_tac peg_eval_suffix' >> gvs[peg0_rules])
  >- (rpt strip_tac >> rule_match peg0_rules >>
      imp_res_tac peg_eval_suffix' >> gvs[])
  >- (rpt strip_tac >> rule_match peg0_rules >> gvs[] >>
      imp_res_tac peg_eval_suffix' >> rgs[]) >>
  rpt strip_tac
  >- (first_x_assum match_mp_tac >> rw[] >>
      imp_res_tac peg_eval_suffix >> fs[IS_SUFFIX_compute] >>
      imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
      imp_res_tac IS_PREFIX_ANTISYM >> fs[]) >>
  imp_res_tac peg_eval_suffix' >- gvs[] >>
  imp_res_tac peg_eval_list_suffix' >> gvs[]
QED

Theorem lemma4_1a = lemma4_1a0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]

Inductive wfpeg:
  (∀n f. n ∈ FDOM G.rules ∧ wfpeg G (G.rules ' n) ⇒ wfpeg G (nt n f))
[~_empty[simp]:]
  (∀c. wfpeg G (empty c))
[~_any[simp]:]
  (∀f. wfpeg G (any f))
[~tok[simp]:]
  (∀t f. wfpeg G (tok t f))
[~_error[simp]:]
  (∀e. wfpeg G (error e)) ∧
  (∀e c. wfpeg G e ⇒ wfpeg G (not e c)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ (peg0 G e1 ⇒ wfpeg G e2) ⇒
             wfpeg G (seq e1 e2 f)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ wfpeg G e2 ⇒ wfpeg G (choice e1 e2 f)) ∧
  (∀e f. wfpeg G e ∧ ¬peg0 G e ⇒ wfpeg G (rpt e f))
End

Definition subexprs_def[simp]:
  (subexprs (any f1) = { any f1 }) ∧
  (subexprs (empty c) = { empty c }) ∧
  (subexprs (tok t f2) = { tok t f2 }) ∧
  (subexprs (error e) = { error e }) ∧
  (subexprs (nt s f) = { nt s f }) ∧
  (subexprs (not e c) = not e c INSERT subexprs e) ∧
  (subexprs (seq e1 e2 f3) = seq e1 e2 f3 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (choice e1 e2 f4) =
    choice e1 e2 f4 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (rpt e f5) = rpt e f5 INSERT subexprs e)
End

Theorem subexprs_included[simp]: e ∈ subexprs e
Proof Induct_on `e` >> srw_tac[][subexprs_def]
QED

Definition Gexprs_def:
  Gexprs G = BIGUNION (IMAGE subexprs (G.start INSERT FRANGE G.rules))
End

Theorem start_IN_Gexprs[simp]:
  G.start ∈ Gexprs G
Proof
  simp[Gexprs_def, subexprs_included]
QED

Definition wfG_def:  wfG G ⇔ ∀e. e ∈ Gexprs G ⇒ wfpeg G e
End

Theorem IN_subexprs_TRANS:
  ∀a b c. a ∈ subexprs b ∧ b ∈ subexprs c ⇒ a ∈ subexprs c
Proof
  Induct_on `c` >> simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem Gexprs_subexprs:
  e ∈ Gexprs G ⇒ subexprs e ⊆ Gexprs G
Proof
  simp_tac (srw_ss() ++ DNF_ss) [Gexprs_def, pred_setTheory.SUBSET_DEF] >>
  strip_tac >> metis_tac [IN_subexprs_TRANS]
QED

Theorem IN_Gexprs_E:
  (not e c ∈ Gexprs G ⇒ e ∈ Gexprs G) ∧
  (seq e1 e2 f ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
  (choice e1 e2 f2 ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
  (rpt e f3 ∈ Gexprs G ⇒ e ∈ Gexprs G)
Proof
  rpt strip_tac >> imp_res_tac Gexprs_subexprs >> fs[] >>
  metis_tac [pred_setTheory.SUBSET_DEF, subexprs_included]
QED

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy

Theorem reducing_peg_eval_makes_list[local]:
  (∀s. LENGTH s < n ⇒ ∃r. peg_eval G (s, e) r) ∧ ¬peg0 G e ∧ LENGTH s0 < n ⇒
  ∃s' rl err. peg_eval_list G (s0,e) (s',rl,err)
Proof
  strip_tac >> completeInduct_on `LENGTH s0` >> rw[] >>
  full_simp_tac (srw_ss() ++ DNF_ss ++ ARITH_ss) [] >>
  ‘(∃fl fe. peg_eval G (s0,e) (Failure fl fe)) ∨
   ∃s1 c eo. peg_eval G (s0,e) (Success s1 c eo)’
    by metis_tac [result_cases]
  >- metis_tac [peg_eval_list_nil] >>
  `s0 ≠ s1` by metis_tac [lemma4_1a] >>
  `LENGTH s1 < LENGTH s0` by metis_tac [peg_eval_suffix'] >>
  irule_at Any peg_eval_list_cons >> first_x_assum $ irule_at Any >>
  metis_tac []
QED

Theorem peg_eval_total:
  wfG G ⇒ ∀s e. e ∈ Gexprs G ⇒ ∃r. peg_eval G (s,e) r
Proof
  simp[wfG_def] >> strip_tac >> gen_tac >>
  completeInduct_on ‘LENGTH s’ >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> rpt strip_tac >>
  ‘wfpeg G e’ by metis_tac[] >>
  Q.UNDISCH_THEN ‘e ∈ Gexprs G’ mp_tac >>
  pop_assum mp_tac >> qid_spec_tac ‘e’ >>
  Induct_on ‘wfpeg’ >> rw[]
  >- ((* nt *)
      qsuff_tac ‘G.rules ' n ∈ Gexprs G’
      >- (strip_tac >>
          first_x_assum $ drule_then
                        $ qx_choose_then ‘result’ strip_assume_tac >>
          metis_tac [peg_eval_nt]) >>
      asm_simp_tac (srw_ss() ++ DNF_ss) [Gexprs_def, FRANGE_DEF] >>
      metis_tac [subexprs_included])
  >- (* empty *) metis_tac [peg_eval_empty]
  >- (* any *) metis_tac [peg_eval_any_success, peg_eval_any_failure,list_CASES]
  >- (* tok *) metis_tac [peg_eval_tok_success, peg_eval_tok_failureF,
                          peg_eval_tok_failureEOF, list_CASES]
  >- (* error *) metis_tac[peg_eval_error]
  >- (* not *) metis_tac [peg_eval_not_success, result_cases, IN_Gexprs_E,
                          isFailure_def, isSuccess_def, peg_eval_not_failure]
  >- ((* seq *) rename [‘seq e1 e2 f ∈ Gexprs G’] >>
      ‘e1 ∈ Gexprs G’ by imp_res_tac IN_Gexprs_E >>
      ‘(∃fl fe. peg_eval G (s,e1) (Failure fl fe))  ∨
       ∃s' c eo. peg_eval G (s,e1) (Success s' c eo)’
        by metis_tac[result_cases]
      >- metis_tac [peg_eval_rules, isFailure_def, isSuccess_def] >>
      Cases_on ‘s' = s’
      >- (‘peg0 G e1’ by metis_tac [lemma4_1a] >>
          ‘e2 ∈ Gexprs G’ by imp_res_tac IN_Gexprs_E >>
          metis_tac [peg_eval_rules, result_cases, isSuccess_def,
                     isFailure_def]) >>
      ‘LENGTH s' < LENGTH s’ by metis_tac [peg_eval_suffix'] >>
      ‘∃r'. peg_eval G (s',e2) r'’ by metis_tac [IN_Gexprs_E] >>
      metis_tac [result_cases, peg_eval_rules, isFailure_def, isSuccess_def])
  >- (* choice *)
    (drule_then strip_assume_tac (cj 3 IN_Gexprs_E) >> fs[] >>
     metis_tac [peg_eval_rules, result_cases, isSuccess_def, isFailure_def]) >>
  (* rpt *) imp_res_tac IN_Gexprs_E >>
  ‘(∃fl fe. peg_eval G (s, e) (Failure fl fe)) ∨
   ∃s' c eo. peg_eval G (s,e) (Success s' c eo)’
    by metis_tac [result_cases]
  >- (‘peg_eval_list G (s,e) (s,[],fl,fe)’ by metis_tac [peg_eval_list_nil] >>
      metis_tac [peg_eval_rpt]) >>
  ‘s' ≠ s’ by metis_tac [lemma4_1a] >>
  ‘LENGTH s' < LENGTH s’ by metis_tac [peg_eval_suffix'] >>
  metis_tac [peg_eval_rules, reducing_peg_eval_makes_list]
QED

(* derived and useful PEG forms *)
Definition pegf_def:  pegf sym f = seq sym (empty ARB) (λl1 l2. f l1)
End

Definition ignoreL_def:
  ignoreL s1 s2 = seq s1 s2 (λa b. b)
End
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "ignoreL",
                          tok = "~>"}

Definition ignoreR_def:
  ignoreR s1 s2 = seq s1 s2 (λa b. a)
End
val _ = set_mapped_fixity{fixity = Infixl 500, term_name = "ignoreR",
                          tok = "<~"}

Definition choicel_def:
  (choicel [] = not (empty ARB) ARB) ∧
  (choicel (h::t) = choice h (choicel t) (λs. sum_CASE s I I))
End

Definition checkAhead_def:
  checkAhead P s = not (not (tok P ARB) ARB) ARB ~> s
End

Theorem peg_eval_seq_SOME:
  peg_eval G (i0, seq s1 s2 f) (Success i r eo) ⇔
    ∃i1 r1 r2 eo1.
      peg_eval G (i0, s1) (Success i1 r1 eo1) ∧
      peg_eval G (i1, s2) (Success i r2 eo) ∧ r = f r1 r2
Proof simp[Once peg_eval_cases] >> metis_tac[]
QED

Theorem peg_eval_seq_NONE:
  peg_eval G (i0, seq s1 s2 f) (Failure fl fe) ⇔
  peg_eval G (i0, s1) (Failure fl fe) ∨
  ∃i r eo. peg_eval G (i0,s1) (Success i r eo) ∧
           peg_eval G (i,s2) (Failure fl fe)
Proof
  simp[Once peg_eval_cases] >> metis_tac[]
QED

Theorem peg_eval_tok_NONE =
  “peg_eval G (i, tok P f) (Failure fl fe)”
    |> SIMP_CONV (srw_ss()) [Once peg_eval_cases]

Theorem peg_eval_tok_SOME:
  peg_eval G (i0, tok P f) (Success i r eo) ⇔
  ∃h l. P h ∧ i0 = (h,l)::i ∧ r = f (h,l) ∧ eo = NONE
Proof simp[Once peg_eval_cases, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem peg_eval_empty[simp,allow_rebind]:
  peg_eval G (i, empty r) x ⇔ x = Success i r NONE
Proof simp[Once peg_eval_cases]
QED

Theorem peg_eval_NT_SOME:
  peg_eval G (i0,nt N f) (Success i r eo) ⇔
  ∃r0. r = f r0 ∧ N ∈ FDOM G.rules ∧
       peg_eval G (i0,G.rules ' N) (Success i r0 eo)
Proof simp[Once peg_eval_cases, resultmap_EQ_Success, PULL_EXISTS]
QED

Theorem peg_eval_choice:
  ∀x.
     peg_eval G (i0, choice s1 s2 f) x ⇔
      (∃sr. peg_eval G (i0, s1) sr ∧ isSuccess sr ∧
            x = resultmap (f o INL) sr) ∨
      (∃i r eo fl fe.
         peg_eval G (i0, s1) (Failure fl fe) ∧
         peg_eval G (i0, s2) (Success i r eo) ∧
         x = Success i (f $ INR r) (optmax MAXerr (SOME (fl,fe)) eo)) ∨
      ∃fl1 fe1 fl2 fe2.
        peg_eval G (i0, s1) (Failure fl1 fe1) ∧
        peg_eval G (i0, s2) (Failure fl2 fe2) ∧
        x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))
Proof
  simp[Once peg_eval_cases, SimpLHS] >> simp[EXISTS_result, FORALL_result] >>
  metis_tac[]
QED

Theorem peg_eval_choicel_NIL[simp]:
  peg_eval G (i0, choicel []) x = (x = Failure (sloc i0) G.notFAIL)
Proof
  simp[choicel_def, Once peg_eval_cases]
QED

Theorem peg_eval_choicel_CONS:
  ∀x. peg_eval G (i0, choicel (h::t)) x ⇔
        ∃y.
          peg_eval G (i0, h) y ∧
          case y of
            Success i r eo => x = Success i r eo
          | Failure fl1 fe1 =>
              ∃z. peg_eval G (i0, choicel t) z ∧
                  case z of
                    Success i r eo =>
                      x = Success i r (optmax MAXerr (SOME(fl1,fe1)) eo)
                  | Failure fl2 fe2 =>
                      x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))
Proof
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  dsimp[FORALL_result, EXISTS_result] >>
  metis_tac[]
QED

Theorem peg_eval_rpt[allow_rebind]:
  peg_eval G (i0, rpt s f) x ⇔
    ∃i l err. peg_eval_list G (i0,s) (i,l,err) ∧ x = Success i (f l) (SOME err)
Proof simp[Once peg_eval_cases, SimpLHS] >> metis_tac[]
QED

Theorem peg_eval_list:
   peg_eval_list G (i0, e) (i, r, err) ⇔
     (∃fl fe. peg_eval G (i0, e) (Failure fl fe) ∧ i = i0 ∧ r = [] ∧
             err = (fl,fe)) ∨
     (∃i1 rh rt eo0.
        peg_eval G (i0, e) (Success i1 rh eo0) ∧
        peg_eval_list G (i1, e) (i, rt, err) ∧ r = rh::rt)
Proof
  simp[Once peg_eval_cases, SimpLHS] >> metis_tac[]
QED

Theorem pegfail_empty[simp]:
  pegfail G (empty r) = F
Proof simp[Once peg0_cases]
QED

Theorem peg0_empty[simp]:
  peg0 G (empty r) = T
Proof simp[Once peg0_cases]
QED

Theorem peg0_not[simp]:
  peg0 G (not s r) ⇔ pegfail G s
Proof simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_choice[simp]:
  peg0 G (choice s1 s2 f) ⇔ peg0 G s1 ∨ pegfail G s1 ∧ peg0 G s2
Proof
  simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_choicel[simp]:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

Theorem peg0_seq[simp]:
  peg0 G (seq s1 s2 f) ⇔ peg0 G s1 ∧ peg0 G s2
Proof simp[Once peg0_cases, SimpLHS]
QED

Theorem peg0_tok[simp]:
  peg0 G (tok P f) = F
Proof
  simp[Once peg0_cases]
QED

Theorem peg0_pegf[simp]:
  peg0 G (pegf s f) = peg0 G s
Proof
  simp[pegf_def]
QED

