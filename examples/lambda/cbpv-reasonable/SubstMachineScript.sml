Theory SubstMachine
Ancestors arithmetic option num list CBPV_Mutual_Recursive Program

(* --------------------------------
         Substitution Machine
   -------------------------------- *)

Type state = ``:Pro list # Pro list``;

Definition tc:
  tc c C =
    case c of
      [] => C
    | _  => c::C
End

Theorem tc_not_empty:
  x ≠ [] ⇒ tc x C = x::C
Proof
  rw[tc] >> Cases_on ‘x’ >> rw[]
QED

Theorem tc_empty[simp]:
  tc [] C = C
Proof
  rw[tc]
QED

Theorem tc_size:
  SUM (MAP sizeT P) + SUM (MAP sizeP Ps) ≤ SUM (MAP sizeP (tc P Ps))
Proof
   Cases_on ‘P’ >> rw[tc_not_empty] >> rw[sizeP]
QED

Theorem tc_size_empty:
  SUM (MAP sizeP (tc [] Ps)) = SUM (MAP sizeT []) + SUM (MAP sizeP Ps)
Proof
  rw[sizeP]
QED

Theorem tc_size_not_empty:
  P ≠ [] ⇒ SUM (MAP sizeP (tc P Ps)) = SUM (MAP sizeT P) + SUM (MAP sizeP Ps) + 1
Proof
  Cases_on ‘P’ >> rw[tc_not_empty] >> rw[sizeP, sizeT]
QED

Inductive subst_step:
[~thunk:]
  (∀P M P' K T.
  jumpThunk 0 [] P = SOME (M, P') ⇒
  subst_step ((thunkT::P)::T, K) (tc P' T, (thunkT::M++[endThunkT])::K))
[~var:]
  (∀n P T V.
    subst_step (((varT n)::P)::T, V) (tc P T, [varT n]::V))
[~force:]
  (∀P V K T.
  jumpThunk 0 [] V = SOME (M, V') ⇒
  subst_step ((forceT::P)::T, (thunkT::V)::K) (tc (M++P) T, K))
[~lam:]
  (∀P P' M T V.
    jumpTarget 0 [] P = SOME (M,P') ⇒
    subst_step ((lamT::P)::T, V) (tc P' T,(lamT::M++[endLamT])::V))
[~app:]
  (∀P Q M T V.
    subst_step ((appT::P)::T, Q::(lamT::M++[endLamT])::V) (substP M 0 Q::tc P T,V))
[~ret:]
  (∀P P' M T V.
    jumpRet 0 [] P = SOME (M,P') ⇒
    subst_step ((retT::P)::T, V) (tc P' T,(retT::M++[endRetT])::V))
[~seq:]
  (∀P P' M R T V.
    jumpSeq 0 [] P = SOME (M, P') ⇒
    subst_step ((seqT::P)::T, (retT::R++[endRetT])::V) (substP M 0 R::tc P' T,V))
[~pseq:]
  (∀P P' M1 M2 N T V.
    jumpPseq 0 [] P = SOME (N, P') ⇒
    subst_step ((pseqT::P)::T, (retT::M2++[endRetT])::(retT::M1++[endRetT])::V) (substP (substP N 0 M1) 1 M2::tc P' T,V))
[~letin:]
  (∀P M P' V T Vs.
    jumpLetin 0 [] P = SOME (M, P') ⇒
    subst_step ((letinT::P)::T, V::Vs) (substP M 0 V::tc P' T,Vs))
End

(* Rewrite rules for subst machine *)

Definition subst_machine[nocompute]:
  subst_machine s = some s'. subst_step s s'
End

Theorem subst_machine_var[simp,compute]:
  ∀n P T V.
    subst_machine (((varT n)::P)::T, V) = SOME (tc P T, [varT n]::V)
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_thunk[simp,compute]:
  ∀P M P' K T.
    subst_machine ((thunkT::P)::T, K) =
      case (jumpThunk 0 [] P) of
        | SOME (M, P') => SOME (tc P' T, (thunkT::M++[endThunkT])::K)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_force[simp,compute]:
  ∀T P V K M V'.
    subst_machine ((forceT::P)::T, (thunkT::V)::K) =
      case (jumpThunk 0 [] V) of
        | SOME (M, V') => SOME ((tc (M++P) T), K)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >> fs[Once subst_step_cases] >>
  gs[]
QED

Theorem subst_machine_lam[simp,compute]:
  ∀P P' Q T V.
    subst_machine ((lamT::P)::T,V) =
      case jumpTarget 0 [] P of
        | SOME (Q,P') => SOME (tc P' T,(lamT::Q++[endLamT])::V)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_app:
  ∀P Q R T V.
    subst_machine ((appT::P)::T, Q::(lamT::R++[endLamT])::V) = SOME (substP R 0 Q::tc P T,V)
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> fs[Once subst_step_cases]
QED

Theorem subst_machine_app2[simp,compute]:
  ∀P Q R T V.
    subst_machine ((appT::P)::T, Q::(lamT::R)::V) =
      if R ≠ [] ∧ LAST R = endLamT then SOME (substP (FRONT R) 0 Q::tc P T,V) else NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> fs[Once subst_step_cases]
  >- simp[rich_listTheory.FRONT_APPEND]
  >- metis_tac[APPEND_FRONT_LAST]
  >> rw[] >> gs[]
QED

Theorem subst_machine_ret[simp,compute]:
  ∀P P' Q T V.
    subst_machine ((retT::P)::T,V) =
      case jumpRet 0 [] P of
        | SOME (Q,P') => SOME (tc P' T,(retT::Q++[endRetT])::V)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_seq[simp,compute]:
  ∀P P' M R T V.
    subst_machine ((seqT::P)::T, (retT::R++[endRetT])::V) =
      case jumpSeq 0 [] P of
        | SOME (M, P') => SOME (substP M 0 R::tc P' T,V)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_pseq[simp,compute]:
  ∀P P' N M1 M2 T V.
    subst_machine ((pseqT::P)::T, (retT::M2++[endRetT])::(retT::M1++[endRetT])::V) =
      case jumpPseq 0 [] P of
        | SOME (N, P') => SOME (substP (substP N 0 M1) 1 M2::tc P' T,V)
        | NONE => NONE
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

Theorem subst_machine_letin[simp,compute]:
  ∀P P' M V T V.
    jumpLetin 0 [] P = SOME (M, P') ⇒
    subst_machine ((letinT::P)::T, V::Vs) = SOME (substP M 0 V::tc P' T,Vs)
Proof
  rw[subst_machine] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[] >> rpt BasicProvers.TOP_CASE_TAC >>
  fs[Once subst_step_cases] >> gs[]
QED

(* run machine *)

Definition init:
  init s = ([compileComp s], [])
End

Definition run_machine:
  run_machine = WHILE (IS_SOME o subst_machine) (THE o subst_machine)
End

Definition run_n_steps:
  run_n_steps 0 state = SOME state ∧
  run_n_steps (SUC n) state = OPTION_BIND (subst_machine state) (run_n_steps n)
End

(* lemmas *)

Theorem tc_compileVal:
  ∀s c C. tc (compileVal s++c) C = (compileVal s++c)::C
Proof
  Induct_on `s` >> rw[tc, Once compileVal_def]
QED

Theorem tc_compileComp:
  ∀s c C. tc (compileComp s++c) C = (compileComp s++c)::C
Proof
  Induct_on `s` >> rw[tc, Once compileVal_def]
  >- (Cases_on `compileVal v ⧺ [forceT] ⧺ c` >> rw[] >> gs[])
  >- (Cases_on `compileComp s ⧺ compileVal v ⧺ [appT] ⧺ c` >> rw[] >> gs[])
  >- (Cases_on `compileComp s ⧺ [seqT] ++ compileComp s' ⧺ [endSeqT] ⧺ c` >> rw[] >> gs[])
  >- (Cases_on `compileVal v ++ [letinT] ++ compileComp s ++ [endLetinT] ++ c` >> rw[] >> gs[])
  >> Cases_on `compileComp s' ⧺ compileComp s ⧺ [pseqT] ⧺
           compileComp s'' ⧺ [endPseqT] ⧺ c` >> rw[] >> gs[]
QED

Theorem tc_compileCompSingle:
  ∀s C. tc (compileComp s) C = (compileComp s)::C
Proof
  Induct_on `s` >> rw[tc, Once compileVal_def]
  >- (Cases_on `compileVal v ⧺ [forceT]` >> rw[] >> gs[])
  >- (Cases_on `compileComp s ⧺ compileVal v ⧺ [appT]` >> rw[] >> gs[])
  >- (Cases_on `compileComp s ⧺ [seqT] ++ compileComp s' ⧺ [endSeqT]` >> rw[] >> gs[])
  >- (Cases_on `compileVal v ++ [letinT] ++ compileComp s ++ [endLetinT]` >> rw[] >> gs[])
  >> Cases_on `compileComp s' ⧺ compileComp s ⧺ [pseqT] ⧺
              compileComp s'' ⧺ [endPseqT]` >> rw[] >> gs[]
QED


(* --------------------------------
              Time Cost
   -------------------------------- *)

Theorem subst_step_compileVal:
  ∀v c0 C V. subst_step ((compileVal v ++ c0)::C, V) (tc c0 C, compileVal v::V)
Proof
  Induct_on `v` >> rw[compileVal_def, Once subst_step_cases] >>
  metis_tac[jumpThunk_correct, APPEND_ASSOC, APPEND]
QED

Theorem subst_big_step_correct':
  ∀k s t c0 C V.
    timeBS k s t ⇒
    ∃n.
      NRC subst_step n ((compileComp s++c0)::C, V) (tc c0 C,(compileComp t)::V)
Proof
  Induct_on `timeBS` >> rw[] >> rw[compileVal_def]
  (* lam *)
  >- (qexists_tac `1`  >> rw[Once subst_step_cases] >>
      metis_tac[jumpTarget_correct, APPEND_ASSOC, APPEND])
  (* ret *)
  >- (qexists_tac `1`  >> rw[Once subst_step_cases] >>
      metis_tac[jumpRet_correct, APPEND_ASSOC, APPEND])
  (* app *)
  >- (last_x_assum (qspecl_then [`compileVal v ⧺ [appT] ⧺ c0`, `C`, `V`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `n+(2+n')` >> irule NRC_ADD_I >>
      qexists_tac `(tc (compileVal v ⧺ [appT] ⧺ c0) C,compileComp (lam m')::V)` >> rw[] >>
      `NRC subst_step (2 + n')
          (tc (compileVal v ⧺ ([appT] ⧺ c0)) C,compileComp (lam m')::V)
          (tc c0 C,compileComp t::V)` suffices_by simp[] >>
      irule NRC_ADD_I >> rw[tc_compileVal] >>
      qexists_tac `(compileComp (substComp m' 0 v)::tc c0 C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
          ((compileVal v ⧺ [appT] ⧺ c0)::C,compileComp (lam m')::V)
          (compileComp (substComp m' 0 v)::tc c0 C,V)` suffices_by rw[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(tc ([appT] ⧺ c0) C, compileVal v::compileComp (lam m')::V)` >> rw[]
          (* V *)
          >- metis_tac[subst_step_compileVal, APPEND, APPEND_ASSOC]
          (* appT *)
          >> rw[tc, compileVal_def, Once subst_step_cases] >>
          metis_tac[substP_correct])
      >> `tc [] (tc c0 C) = tc c0 C` by rw[tc] >> gs[])
  (* seq *)
  >- (rename [`substComp s' 0 v`] >>
      last_x_assum (qspecl_then [`[seqT] ++ compileComp s' ⧺ [endSeqT] ⧺ c0`, `C`, `V`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `n+(1+n')` >> irule NRC_ADD_I >>
      qexists_tac `(tc (seqT::(compileComp s' ⧺ [endSeqT] ⧺ c0)) C, compileComp (ret v)::V)` >>
      rw[] >>
      `NRC subst_step (1 + n')
        (tc (seqT::(compileComp s' ⧺ [endSeqT] ⧺ c0)) C,
          compileComp (ret v)::V) (tc c0 C,compileComp t::V)`
        suffices_by simp[] >>
      irule NRC_ADD_I >>
      qexists_tac `(compileComp (substComp s' 0 v)::tc c0 C,V)` >> rw[]
      >- (rw[Once tc] >> rw[Once subst_step_cases, compileVal_def] >>
          qexistsl_tac [`c0`, `compileComp s'`] >> rw[]
          >- metis_tac[GSYM substP_correct]
          >> metis_tac[jumpSeq_correct, APPEND_ASSOC, APPEND])
      >> `tc [] (tc c0 C) = tc c0 C` by rw[tc] >> gs[])
  (* pseq *)
  >- (last_x_assum (qspecl_then [‘compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’, ‘C’, ‘V’] ASSUME_TAC) >>
      last_x_assum (qspecl_then [‘[pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’, ‘C’, ‘compileComp (ret v1) :: V’] ASSUME_TAC)  >>
      first_x_assum (qspecl_then [‘[]’, ‘tc c0 C’, ‘V’] ASSUME_TAC) >> fs[] >>
      qexists_tac `n' + n'' + (1+n''')` >> irule NRC_ADD_I >>
      qexists_tac `tc (pseqT::(compileComp n ⧺ [endPseqT] ⧺ c0)) C,
      compileComp (ret v2)::compileComp (ret v1)::V` >>
      rw[]
      >- (irule NRC_ADD_I >>
          qexists_tac ‘(compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0)::C,
                       compileComp (ret v1)::V’ >>
          rw[] >> fs[Once tc] >>
          Cases_on ‘compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’ >>
          gvs[])
      >> ` NRC subst_step (1 + n'³')
           (tc (pseqT::(compileComp n ⧺ [endPseqT] ⧺ c0)) C,
            compileComp (ret v2)::compileComp (ret v1)::V)
           (tc c0 C,compileComp t::V)`
        suffices_by simp[] >>
      irule NRC_ADD_I >>
      qexists_tac `(compileComp (substComp (substComp n 0 v1) 1 v2)::tc c0 C,V)` >>
      rw[] >> rw[Once tc] >> rw[Once subst_step_cases, compileVal_def] >>
      qexistsl_tac [‘c0’, ‘compileComp n’] >> rw[]
      >- metis_tac[GSYM substP_correct]
      >> metis_tac[jumpPseq_correct, APPEND_ASSOC, APPEND])
  (* letin *)
  >- (last_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `1+1+n` >> irule NRC_ADD_I >>
      qexists_tac `((compileComp (substComp m 0 v)):: tc c0 C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
            ((compileVal v ⧺ [letinT] ⧺ compileComp m ⧺ [endLetinT] ⧺ c0)::C,V)
            (compileComp (substComp m 0 v)::tc c0 C,V)` suffices_by simp[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(tc ([letinT] ⧺ compileComp m ⧺ [endLetinT] ⧺ c0) C,compileVal v::V)` >>
          rw[]
          >- metis_tac[subst_step_compileVal, APPEND_ASSOC, APPEND]
          >> rw[tc] >> rw[Once subst_step_cases] >>
          qexistsl_tac [`compileComp m`, `c0`] >> rw[]
          >- metis_tac[substP_correct]
          >- (Cases_on `c0` >> rw[tc])
          >> metis_tac[jumpLetin_correct, APPEND_ASSOC, APPEND])
      >> fs[tc])
  (* thunk+force *)
  >- (last_x_assum (qspecl_then [`c0`, `C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `1+1+n` >> irule NRC_ADD_I >>
      qexists_tac `(tc (compileComp s ++ c0) C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
            ((thunkT::(compileComp s ⧺ [endThunkT] ⧺ [forceT] ⧺ c0))::C,V)
            (tc (compileComp s ++ c0) C,V)` suffices_by simp[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(([forceT] ⧺ c0)::C,(thunkT::compileComp s ⧺ [endThunkT])::V)` >>
          rw[]
          >- (rw[Once subst_step_cases] >> qexists_tac `forceT::c0` >>
              rw[tc] >> metis_tac[jumpThunk_correct, APPEND_ASSOC, APPEND])
          >> rw[Once subst_step_cases] >>
          qexistsl_tac [`compileComp s`, `[]`] >> rw[]
          >> metis_tac[jumpThunk_correct, APPEND, APPEND_ASSOC])
      >> Cases_on ‘compileComp s ++ c0’ >> fs[compile_not_empty] >> rw[tc_not_empty])
QED

Theorem subst_big_step_correct:
  ∀k s t.
    timeBS k s t ⇒
    ∃n. NRC subst_step n (init s) ([],[compileComp t])
Proof
  rw[init] >>
  `∃n. NRC subst_step n ((compileComp s ⧺ [])::[],[])
             (tc [] [],compileComp t::[])`
    by metis_tac[subst_big_step_correct'] >>
  qexists_tac `n` >> rw[] >>
  fs[tc]
QED

Theorem subst_big_step_correct_n':
  ∀k s t c0 C V.
    timeBS k s t ⇒
    ∃n.
      NRC subst_step n ((compileComp s++c0)::C,V) (tc c0 C,(compileComp t)::V) ∧
      n ≤ 3 * k + 1
Proof
  Induct_on `timeBS` >> rw[] >> rw[compileVal_def]
  (* lam *)
  >- (qexists_tac `1`  >> rw[Once subst_step_cases] >>
      metis_tac[jumpTarget_correct, APPEND_ASSOC, APPEND])
  (* ret *)
  >- (qexists_tac `1`  >> rw[Once subst_step_cases] >>
      metis_tac[jumpRet_correct, APPEND_ASSOC, APPEND])
  (* app *)
  >- (last_x_assum (qspecl_then [`compileVal v ⧺ [appT] ⧺ c0`, `C`, `V`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `n+(2+n')` >> rw[] >> irule NRC_ADD_I >>
      qexists_tac `(tc (compileVal v ⧺ [appT] ⧺ c0) C,compileComp (lam m')::V)` >> rw[] >>
      `NRC subst_step (2 + n')
          (tc (compileVal v ⧺ ([appT] ⧺ c0)) C,compileComp (lam m')::V)
          (tc c0 C,compileComp t::V)` suffices_by simp[] >>
      irule NRC_ADD_I >> rw[tc_compileVal] >>
      qexists_tac `(compileComp (substComp m' 0 v)::tc c0 C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
          ((compileVal v ⧺ [appT] ⧺ c0)::C,compileComp (lam m')::V)
          (compileComp (substComp m' 0 v)::tc c0 C,V)` suffices_by rw[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(tc ([appT] ⧺ c0) C, compileVal v::compileComp (lam m')::V)` >> rw[]
          (* V *)
          >- metis_tac[subst_step_compileVal, APPEND, APPEND_ASSOC]
          (* appT *)
          >> rw[tc, compileVal_def, Once subst_step_cases] >>
          metis_tac[substP_correct])
      >> `tc [] (tc c0 C) = tc c0 C` by rw[tc] >> gs[])
  (* seq *)
  >- (rename [`substComp s' 0 v`] >>
      last_x_assum (qspecl_then [`[seqT] ++ compileComp s' ⧺ [endSeqT] ⧺ c0`, `C`, `V`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `n+(1+n')` >> rw[] >> irule NRC_ADD_I >>
      qexists_tac `(tc (seqT::(compileComp s' ⧺ [endSeqT] ⧺ c0)) C, compileComp (ret v)::V)` >>
      rw[] >>
      `NRC subst_step (1 + n')
        (tc (seqT::(compileComp s' ⧺ [endSeqT] ⧺ c0)) C,
          compileComp (ret v)::V) (tc c0 C,compileComp t::V)`
        suffices_by simp[] >>
      irule NRC_ADD_I >>
      qexists_tac `(compileComp (substComp s' 0 v)::tc c0 C,V)` >> rw[]
      >- (rw[Once tc] >> rw[Once subst_step_cases, compileVal_def] >>
          qexistsl_tac [`c0`, `compileComp s'`] >> rw[]
          >- metis_tac[GSYM substP_correct]
          >> metis_tac[jumpSeq_correct, APPEND_ASSOC, APPEND])
      >> `tc [] (tc c0 C) = tc c0 C` by rw[tc] >> gs[])
  (* pseq *)
  >- (last_x_assum (qspecl_then [‘compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’, ‘C’, ‘V’] ASSUME_TAC) >>
      last_x_assum (qspecl_then [‘[pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’, ‘C’, ‘compileComp (ret v1) :: V’] ASSUME_TAC)  >>
      first_x_assum (qspecl_then [‘[]’, ‘tc c0 C’, ‘V’] ASSUME_TAC) >> fs[] >>
      qexists_tac ‘n' + n'' + (1+n''')’ >> reverse(conj_tac)
      >- rw[]
      >> irule NRC_ADD_I >>
      qexists_tac `tc (pseqT::(compileComp n ⧺ [endPseqT] ⧺ c0)) C,
      compileComp (ret v2)::compileComp (ret v1)::V` >>
      rw[]
      >- (irule NRC_ADD_I >>
          qexists_tac ‘(compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0)::C,
                       compileComp (ret v1)::V’ >>
          rw[] >> fs[Once tc] >>
          Cases_on ‘compileComp s' ⧺ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ c0’ >>
          gvs[])
      >> ` NRC subst_step (1 + n'³')
           (tc (pseqT::(compileComp n ⧺ [endPseqT] ⧺ c0)) C,
            compileComp (ret v2)::compileComp (ret v1)::V)
           (tc c0 C,compileComp t::V)`
        suffices_by simp[] >>
      irule NRC_ADD_I >>
      qexists_tac `(compileComp (substComp (substComp n 0 v1) 1 v2)::tc c0 C,V)` >>
      rw[] >> rw[Once tc] >> rw[Once subst_step_cases, compileVal_def] >>
      qexistsl_tac [‘c0’, ‘compileComp n’] >> rw[]
      >- metis_tac[GSYM substP_correct]
      >> metis_tac[jumpPseq_correct, APPEND_ASSOC, APPEND])
  (* letin *)
  >- (last_x_assum (qspecl_then [`[]`, `tc c0 C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `1+1+n` >> reverse(strip_tac) >- rw[] >> irule NRC_ADD_I >>
      qexists_tac `((compileComp (substComp m 0 v)):: tc c0 C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
            ((compileVal v ⧺ [letinT] ⧺ compileComp m ⧺ [endLetinT] ⧺ c0)::C,V)
            (compileComp (substComp m 0 v)::tc c0 C,V)` suffices_by simp[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(tc ([letinT] ⧺ compileComp m ⧺ [endLetinT] ⧺ c0) C,compileVal v::V)` >>
          rw[]
          >- metis_tac[subst_step_compileVal, APPEND_ASSOC, APPEND]
          >> rw[tc] >> rw[Once subst_step_cases] >>
          qexistsl_tac [`compileComp m`, `c0`] >> rw[]
          >- metis_tac[substP_correct]
          >- (Cases_on `c0` >> rw[tc])
          >> metis_tac[jumpLetin_correct, APPEND_ASSOC, APPEND])
      >> fs[tc])
  (* thunk+force *)
  >- (last_x_assum (qspecl_then [`c0`, `C`, `V`] ASSUME_TAC) >> fs[] >>
      qexists_tac `1+1+n` >> reverse(strip_tac) >- rw[] >> irule NRC_ADD_I >>
      qexists_tac `(tc(compileComp s ++ c0) C,V)` >> rw[]
      >- (`NRC subst_step (1+1)
            ((thunkT::(compileComp s ⧺ [endThunkT] ⧺ [forceT] ⧺ c0))::C,V)
            (tc(compileComp s ++ c0) C,V)` suffices_by simp[] >>
          irule NRC_ADD_I >> rw[NRC_1] >>
          qexists_tac `(([forceT] ⧺ c0)::C,(thunkT::compileComp s ⧺ [endThunkT])::V)` >>
          rw[]
          >- (rw[Once subst_step_cases] >> qexists_tac `forceT::c0` >>
              rw[tc] >> metis_tac[jumpThunk_correct, APPEND_ASSOC, APPEND])
          >> rw[Once subst_step_cases] >>
          qexistsl_tac [`compileComp s`, `[]`] >> rw[] >>
          metis_tac[jumpThunk_correct, APPEND, APPEND_ASSOC])
      >> Cases_on ‘compileComp s ++ c0’ >> fs[compile_not_empty] >> rw[tc_not_empty])
QED

Theorem subst_big_step_correct_n:
  ∀k s t.
    timeBS k s t ⇒
    ∃n.
      NRC subst_step n (init s) ([],[compileComp t]) ∧
      n ≤ 3 * k + 1
Proof
  rw[init] >>
  `∃n. NRC subst_step n ((compileComp s ⧺ [])::[],[])
             (tc [] [],compileComp t::[]) ∧ n ≤ 3*k+1`
    by metis_tac[subst_big_step_correct_n'] >>
  qexists_tac `n` >> rw[] >>
  fs[tc]
QED


(* --------------------------
   Preliminaries for Space Cost
   --------------------------*)

(* reduce while keeping track of the maximum size of terms *)
Inductive redWithMaxSize:
[~R:]
  (∀size step (m: num) s. m = size s ⇒ redWithMaxSize size step m s s)
[~C:]
  (∀size step (s: 'a) (s': 'a) (t: 'a) (m: num) (m':num).
    step s s' ∧
    redWithMaxSize size step m' s' t ∧
    m = MAX (size s) m' ⇒
    redWithMaxSize size step m s t)
End

Theorem redWithMaxSize_ge:
  ∀size step s t m.
    redWithMaxSize size step m s t ⇒
    size s ≤ m ∧ size t ≤ m
Proof
  Induct_on `redWithMaxSize` >> rw[]
QED

Theorem redWithMaxSize_trans:
  ∀size step s t u m1 m2 m3.
    redWithMaxSize size step m1 s t ⇒
    redWithMaxSize size step m2 t u ⇒
    MAX m1 m2 = m3 ⇒
    redWithMaxSize size step m3 s u
Proof
  Induct_on `redWithMaxSize` >> rw[]
  >- (qpat_x_assum `redWithMaxSize _ _ _ _ _` mp_tac >>
      rw[Once redWithMaxSize_cases]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once redWithMaxSize_cases] >>
      drule redWithMaxSize_ge >> rw[] >>
      rw[Once MAX_DEF] >> fs[NOT_LESS] >> rw[]
      >- (rw[Once MAX_DEF] >>
          goal_assum drule >> goal_assum drule >>
          rw[MAX_DEF])
      >> metis_tac[MAX_DEF])
  >> rw[Once redWithMaxSize_cases] >>
  drule redWithMaxSize_ge >> rw[] >>
  `size s' ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  `size t ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  first_x_assum drule >> rw[] >>
  pop_assum mp_tac >> rw[Once redWithMaxSize_cases]
  >- (pop_assum mp_tac >> rw[Once MAX_DEF] >>
      fs[NOT_LESS] >>
      drule_all LESS_EQUAL_ANTISYM >>
      qpat_x_assum `size s' ≤ m2` (fn _ => all_tac) >>
      qpat_x_assum `m2 ≤ size s'` (fn _ => all_tac) >>
      rw[] >>
      `∃s'' m'.
        step s s'' ∧ redWithMaxSize size step m' s'' s' ∧
        MAX (MAX (size s) (size s')) (size s') = MAX (size s) m'` suffices_by simp[] >>
      qexistsl_tac [`s'`, `size s'`] >> rw[]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once MAX_DEF])
  >> `∃s' m'.
        step s s' ∧ redWithMaxSize size step m' s' u ∧
        MAX (MAX (size s) m1') m2 = MAX (size s) m'` suffices_by simp[] >>
  qexistsl_tac [`s'`, `MAX m1' m2`] >> rw[]
  >- (rw[Once redWithMaxSize_cases] >> metis_tac[])
  >> `MAX (MAX (size s) m1') m2 = MAX (size s) (MAX m1' m2)` suffices_by simp[] >>
  rw[MAX_ASSOC]
QED

Definition redWithMaxSizeS:
  redWithMaxSizeS =
    redWithMaxSize (λ(T', V'). (SUM (MAP sizeP T') + SUM (MAP sizeP V'))) subst_step
End

(* Helper Lemmas *)

Theorem size_le_sizeT:
  (∀v. sizeVal v ≤ SUM (MAP sizeT (compileVal v))) ∧
  ∀c. sizeComp c ≤ SUM (MAP sizeT (compileComp c))
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >>
  rw[sizeVal_def, compileVal_def, sizeT, SUM_APPEND]
QED

Theorem size_le_m_comp:
  (∀s m. sizeVal s ≤ m ⇒ 1 + SUM (MAP sizeT (compileVal s)) ≤ 2*m) ∧
    ∀s m. sizeComp s ≤ m ⇒ 1 + SUM (MAP sizeT (compileComp s)) ≤ 2*m
Proof
  rw[]
  >- (qspec_then ‘s’ assume_tac $ cj 1 sizeP_size >> intLib.COOPER_TAC) >>
  qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >> intLib.COOPER_TAC
QED

Theorem size_le_3m_comp:
  (∀s m. sizeVal s ≤ m ⇒ 1 + SUM (MAP sizeT (compileVal s)) ≤ 3*m) ∧
    ∀s m. sizeComp s ≤ m ⇒ 1 + SUM (MAP sizeT (compileComp s)) ≤ 3*m
Proof
  rw[]
  >- (qspec_then ‘s’ assume_tac $ cj 1 sizeP_size >> intLib.COOPER_TAC) >>
  qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >> intLib.COOPER_TAC
QED


(* --------------------------------
              Space Cost
   -------------------------------- *)


Theorem subst_big_step_correctSpace':
  ∀s t k P T V.
    spaceBS k s t ⇒
    ∃m.
      redWithMaxSizeS m ((compileComp s++P)::T,V) (tc P T,(compileComp t)::V) ∧
      k + SUM (MAP sizeP (tc P T)) + SUM (MAP sizeP V) ≤ m ∧
      m ≤ 9*k + SUM (MAP sizeP (tc P T)) + SUM (MAP sizeP V)
Proof
  simp[redWithMaxSizeS] >>
  Induct_on `spaceBS` >> rw[] (* 6 *)
  (* lam *)
  >- (rw[Once redWithMaxSize_cases, PULL_EXISTS] >>
      rw[compileVal_def] >>
      rw[Once subst_step_cases, PULL_EXISTS] >>
      rw[jumpTarget_correct_conc] >>
      irule_at (Pos hd) redWithMaxSize_R >> rw[]
      >- (rw[sizeP] >> disj2_tac >> rw[Once sizeVal_def] >> rw[SUM_APPEND] >>
          qspec_then ‘s’ assume_tac (cj 2 sizeP_size') >> intLib.COOPER_TAC)
      >- (rw[sizeP, sizeT, SUM_APPEND, sizeVal_def] >> rw[tc] >>
          Cases_on ‘P’ >> rw[]
          >- (qspec_then ‘s’ assume_tac (cj 2 sizeP_size) >> intLib.COOPER_TAC)
          >> rw[sizeP] >> qspec_then ‘s’ assume_tac (cj 2 sizeP_size) >> intLib.COOPER_TAC)
      >> rw[sizeP, sizeT, SUM_APPEND, sizeVal_def] >>
      qspec_then ‘s’ assume_tac (cj 2 sizeP_size) >> intLib.COOPER_TAC)
  (* ret *)
  >- (rw[Once redWithMaxSize_cases, PULL_EXISTS] >>
      rw[compileVal_def] >>
      rw[Once subst_step_cases, PULL_EXISTS] >>
      rw[jumpRet_correct_conc] >>
      irule_at (Pos hd) redWithMaxSize_R >> rw[]
      >- (rw[sizeP] >> disj2_tac >> rw[Once sizeVal_def] >> rw[SUM_APPEND] >>
          qspec_then ‘s’ assume_tac (cj 1 sizeP_size') >> intLib.COOPER_TAC)
      >- (rw[sizeP, sizeT, SUM_APPEND, sizeVal_def] >> rw[tc] >>
          Cases_on ‘P’ >> rw[]
          >- (qspec_then ‘s’ assume_tac (cj 1 sizeP_size) >> intLib.COOPER_TAC)
          >> rw[sizeP] >> qspec_then ‘s’ assume_tac (cj 1 sizeP_size) >> intLib.COOPER_TAC)
      >> rw[sizeP, sizeT, SUM_APPEND, sizeVal_def] >>
      qspec_then ‘s’ assume_tac (cj 1 sizeP_size) >> intLib.COOPER_TAC)
  (* App *)
  >- (rw[compileVal_def] >>
      last_x_assum (qspecl_then [‘compileVal v ⧺ [appT] ⧺ P’, ‘T'’, ‘V’] strip_assume_tac) >>
      gs[APPEND_ASSOC] >> rename [‘m1 ≤ 9*k1 + _’] >>
      irule_at (Pos hd) redWithMaxSize_trans >> first_x_assum $ irule_at $ Pos hd >>
      gs[tc_not_empty] >> rw[compileVal_def] >> irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      irule_at (Pos hd) subst_step_compileVal >> rw[Once tc] >>
      irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >> rw[Once subst_step_cases, PULL_EXISTS] >>
      rw[substP_correct] >>
      first_x_assum (qspecl_then [‘[]’, ‘tc P T'’, ‘V’] strip_assume_tac) >> gs[] >>
      rename [‘m2 ≤ 9 * k2 + (_ + SUM (MAP sizeP (tc P T')))’] >>
      first_x_assum $ irule_at $ Pos hd >> rw[sizeP] (* 5 *)
      >- (gs[sizeP, sizeT, SUM_APPEND] >> Cases_on ‘k1 + (sizeVal v + 1) < k2’ >> rw[MAX_DEF] >>
          disj1_tac >> Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >> gs[] >>
          qspec_then ‘v’ assume_tac $ cj 1 size_le_sizeT >> intLib.COOPER_TAC)
      >- (gs[sizeP, sizeT, SUM_APPEND] >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspec_then ‘v’ assume_tac $ cj 1 sizeP_size >> rw[] >> intLib.COOPER_TAC)
      >- (gs[sizeP, sizeT, SUM_APPEND] >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspecl_then [‘k1’, ‘s’, ‘lam s'’] assume_tac spaceBS_ge >> gs[sizeVal_def] >>
          qspecl_then [‘s'’, ‘k1’] assume_tac $ cj 2 size_le_m_comp >> gs[] >>
          qspecl_then [‘v’, ‘sizeVal v’] assume_tac $ cj 1 size_le_m_comp >> gs[])
      >- (gs[sizeP, sizeT, SUM_APPEND] >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspecl_then [‘k1’, ‘s’, ‘lam s'’] assume_tac spaceBS_ge >> gs[sizeVal_def] >>
          qspecl_then [‘s'’, ‘k1’] assume_tac $ cj 2 size_le_m_comp >> gs[] >>
          qspecl_then [‘v’, ‘sizeVal v’] assume_tac $ cj 1 size_le_m_comp >> gs[])
      >> gs[sizeP, sizeT, SUM_APPEND] >>
      Cases_on ‘P = []’ >> gs[tc_size_not_empty, tc_size_empty] >>
      gs[] (* 2 *) >> rw[MAX_DEF])
     (* Seq *)
  >- (gs[compileVal_def] >>
      last_x_assum (qspecl_then [‘ [seqT] ⧺ compileComp n ⧺ [endSeqT] ⧺ P’, ‘T'’, ‘V’] mp_tac) >>
      rw[Once tc] >> gs[APPEND_ASSOC] >> rename [‘m1 ≤ 9*k1 + _’] >>
      irule_at (Pos hd) redWithMaxSize_trans >> first_x_assum $ irule_at $ Pos hd >>
      rw[] >> irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >>
      rw[subst_step_cases] >>
      first_x_assum (qspecl_then [‘[]’, ‘tc P T'’, ‘V’] strip_assume_tac) >> gs[] >>
      gs[GSYM substP_correct] >> gs[Once tc] >> gs[Once tc] >>
      rw[jumpSeq_correct_conc] >>
      rename [‘m2 ≤ 9 * k2 + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))’] >>
      qexists_tac ‘m2’ >> gs[sizeP, sizeT, SUM_APPEND] >> rw[] (* 4 *)
      >- (rw[MAX_DEF] >> disj1_tac >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >> gs[] >> (* 2 *)
          qspec_then ‘n’ assume_tac $ cj 2 size_le_sizeT >> intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 4 *) >>
          qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >> rw[] >> intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspecl_then [‘k1’, ‘s’, ‘ret v’] assume_tac spaceBS_ge >> gs[sizeVal_def] >>
          qspecl_then [‘v’, ‘sizeVal v’] assume_tac $ cj 1 size_le_3m_comp >> gs[] >>
          qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >> rw[])
      >>  Cases_on ‘P = []’ >> gs[tc_size_not_empty, tc_size_empty] >>
      gs[] (* 2 *) >> rw[MAX_DEF])
    (* Pseq *)
  >- (gs[compileVal_def] >>
      last_x_assum (qspecl_then [‘compileComp s' ++ [pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ P’,
                                 ‘T'’, ‘V’] mp_tac) >>
      rw[] >>
      irule_at (Pos hd) redWithMaxSize_trans >> first_x_assum $ irule_at $ Pos hd >>
      fs[tc_not_empty] >>
      last_x_assum (qspecl_then [‘[pseqT] ⧺ compileComp n ⧺ [endPseqT] ⧺ P’,
                                 ‘T'’, ‘compileComp (ret v1) :: V’] mp_tac) >>
      rw[] >> fs[tc_not_empty] >> irule_at (Pos hd) redWithMaxSize_trans >>
      fs[compileVal_def] >> first_x_assum $ irule_at $ Pos hd >>
      rw[] >> irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >>
      rw[subst_step_cases] >>
      first_x_assum (qspecl_then [‘[]’, ‘tc P T'’, ‘V’] strip_assume_tac) >> gs[] >>
      gs[GSYM substP_correct] >>
      rw[jumpPseq_correct_conc] >> rw[PULL_EXISTS] >>
      qexists_tac ‘m''’ >> gs[sizeP, sizeT, SUM_APPEND] >> rw[] (* 5 *)
      >- (rw[MAX_DEF] (* 3 *)
          >- (disj2_tac >> disj1_tac >>  Cases_on ‘P = []’ >>
              rw[tc_size_not_empty, tc_size_empty] >> gs[] >> rw[] (* 2 *)
              >> qspec_then ‘n’ assume_tac $ cj 2 size_le_sizeT >>
              qspec_then ‘v1’ assume_tac $ cj 1 size_le_sizeT >>
              intLib.COOPER_TAC)
          >- (disj2_tac >> disj1_tac >>  Cases_on ‘P = []’ >>
              rw[tc_size_not_empty, tc_size_empty] >> gs[] >> rw[] (* 2 *)
              >> qspec_then ‘n’ assume_tac $ cj 2 size_le_sizeT >>
              qspec_then ‘v1’ assume_tac $ cj 1 size_le_sizeT >>
              intLib.COOPER_TAC)
          >> disj1_tac >> Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] >> rw[] (* 2 *)
          >> qspec_then ‘n’ assume_tac $ cj 2 size_le_sizeT >>
          qspec_then ‘s'’ assume_tac $ cj 2 size_le_sizeT >>
          intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 10 *) >>
          qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >>
          qspec_then ‘s'’ assume_tac $ cj 2 sizeP_size >>
          rw[] >> intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 10 *) >>
          qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >>
          qspec_then ‘v1’ assume_tac $ cj 1 sizeP_size >>
          rw[] >> intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 10 *) >>
          qspecl_then [‘k'’, ‘s'’, ‘ret v2’] assume_tac spaceBS_ge >> gs[sizeVal_def] >>
          qspecl_then [‘v2’, ‘k'’] assume_tac $ cj 1 size_le_3m_comp >> gs[] >>
          qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >>
          qspec_then ‘v1’ assume_tac $ cj 1 sizeP_size >> rw[] >> intLib.COOPER_TAC) >>
      fs[tc] >>  Cases_on ‘P’ >> rw[tc_size_not_empty, tc_size_empty] >>
      gvs[] (* 2 *) >> rw[MAX_DEF] >>
      qspec_then ‘n’ assume_tac $ cj 2 sizeP_size >>
      qspec_then ‘v1’ assume_tac $ cj 1 sizeP_size >>
      rw[] >> intLib.COOPER_TAC)
     (* Letin *)
  >- (gs[compileVal_def] >>
      first_x_assum (qspecl_then [‘[]’, ‘tc P T'’, ‘V’] strip_assume_tac) >> gs[] >>
      rename [‘m1 ≤ 9*k1 + _’] >>
      irule_at (Pos hd) redWithMaxSize_trans >> first_x_assum $ irule_at $ Any >>
      irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >> PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      irule_at (Pos hd) subst_step_compileVal >> rw[Once tc] >>
      irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >> rw[Once subst_step_cases, PULL_EXISTS] >>
      rw[jumpLetin_correct_conc] >> rw[GSYM substP_correct] >>
      irule_at (Pos hd) $ cj 1 redWithMaxSize_rules >>
      gs[sizeP, sizeT, SUM_APPEND] >> rw[] (* 5 *)
      >- (rw[MAX_DEF] >> disj1_tac >> disj1_tac >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >> gs[] >> (* 2 *)
          qspec_then ‘m’ assume_tac $ cj 2 size_le_sizeT >>
          qspec_then ‘v’ assume_tac $ cj 1 size_le_sizeT >>
          intLib.COOPER_TAC)
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspecl_then [‘v’, ‘sizeVal v’] assume_tac $ cj 1 size_le_3m_comp >> gs[] >>
          qspec_then ‘m’ assume_tac $ cj 2 sizeP_size >> rw[])
      >- (Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *) >>
          qspecl_then [‘v’, ‘sizeVal v’] assume_tac $ cj 1 size_le_3m_comp >> gs[] >>
          qspec_then ‘m’ assume_tac $ cj 2 sizeP_size >> rw[])
      >- (rw[substP_correct] >>
          qspecl_then [‘k1’, ‘substComp m 0 v’, ‘t’] assume_tac spaceBS_ge >>
          gs[sizeVal_def] >> rw[] >>
          qspecl_then [‘substComp m 0 v’, ‘k1’] assume_tac $ cj 2 size_le_3m_comp >> gs[] >>
          Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >>
          gs[] (* 2 *) >> rw[MAX_DEF] (* 2 *)) >>
      rw[MAX_DEF] >> disj1_tac >>
      Cases_on ‘P = []’ >> rw[tc_size_not_empty, tc_size_empty] >> gs[]) >>
  (* Force *)
  gs[compileVal_def] >>
  first_x_assum (qspecl_then [‘P’, ‘T'’, ‘V’] strip_assume_tac) >> gs[] >>
  irule_at (Pos hd) redWithMaxSize_trans >>
  first_x_assum $ irule_at $ Any >> (* Use assumption to remove the later steps *)
  irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >> (* Thunk Step *)
  rw[Once subst_step_cases, PULL_EXISTS] >>
  qspecl_then [‘s’, ‘forceT::P’] assume_tac $ cj 2 jumpThunk_correct_conc >>
  ‘compileComp s ++ [endThunkT] ++ forceT::P = compileComp s ++ [endThunkT; forceT] ++ P’
    by rw[] >> gs[] >> rw[Once tc] >>
  rename [‘m1 ≤ 9*k1 + _’] >>
  irule_at (Pos hd) $ cj 2 redWithMaxSize_rules >> (* Force Step *)
  rw[Once subst_step_cases, PULL_EXISTS] >>
  qspecl_then [‘s’, ‘[]’] assume_tac $ cj 2 jumpThunk_correct_conc >> gs[] >>
  ‘compileComp s++P ≠ []’
    by (Cases_on ‘compileComp s ++ P’ >> fs[compile_not_empty] >> rw[tc_not_empty]) >>
  rw[tc_not_empty] >>
  irule_at (Pos hd) $ cj 1 redWithMaxSize_rules >> (* Reflexive Step *)
  rw[Once subst_step_cases, PULL_EXISTS] >>
  rw[] >> gs[sizeP, sizeT, SUM_APPEND] >> rw[]
  (* 5 *)
  >- (rw[MAX_DEF] >> qspec_then ‘s’ assume_tac $ cj 2 size_le_sizeT >>
      ntac 2 disj1_tac >> Cases_on ‘P = []’ >> rw[tc_not_empty, tc_empty] >> gs[] >>
      rw[sizeP])
  >- (rw[MAX_DEF] >> (* 2 *) qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >>
      Cases_on ‘P = []’ >> rw[tc_not_empty, tc_empty] >> gs[] >>
      rw[sizeP])
  >- (rw[MAX_DEF] >> (* 2 *) qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >>
      Cases_on ‘P = []’ >> rw[tc_not_empty, tc_empty] >> gs[] >>
      rw[sizeP])
  >- (rw[MAX_DEF] >> (* 2 *) qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >>
      Cases_on ‘P = []’ >> rw[tc_not_empty, tc_empty] >> gs[] >>
      rw[sizeP])
  >> rw[MAX_DEF]
QED

Theorem subst_big_step_correctSpace:
  ∀k s t.
    spaceBS k s t ⇒
    ∃m.
      redWithMaxSizeS m (init s) ([],[compileComp t]) ∧
      k ≤ m ∧
      m ≤ 9 * k
Proof
  rw[init] >>
  qspecl_then [‘s’, ‘t’, ‘k’, ‘[]’, ‘[]’, ‘[]’] assume_tac subst_big_step_correctSpace' >>
  gs[] >> qexists_tac `m` >> rw[]
QED
