open HolKernel Parse boolLib bossLib

open boolSimps

open pegTheory locationTheory

open rich_listTheory;

val _ = new_theory "pegexec"

Datatype:
  kont =
    ksym (('atok,'bnt,'cvalue,'err) pegsym) kont kont
  | appf1 ('cvalue -> 'cvalue) kont
  | appf2 ('cvalue -> 'cvalue -> 'cvalue) kont
  | dropErr kont
  | addErr locs 'err kont
  | cmpErrs kont
  | returnTo (('atok # locs) list) ('cvalue option list) kont
  | poplist ('cvalue list -> 'cvalue) kont
  | listsym (('atok,'bnt,'cvalue,'err) pegsym)
            ('cvalue list -> 'cvalue)
            kont
  | done
  | failed
End

val poplist_aux_def = Define`
  poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t ∧
  poplist_aux acc (NONE::t) = (acc,t) ∧
  poplist_aux acc [] = (acc,[]) (* should never happen *)
`;

val poplistval_def = Define`
  poplistval f l = let (values,rest) = poplist_aux [] l
                   in
                     SOME(f values) :: rest
`;

Datatype:
  evalcase = EV (('atok,'bnt,'cvalue,'err) pegsym)
                (('atok # locs) list)
                ('cvalue option list)
                ((locs # 'err) list)
                (('atok,'bnt,'cvalue,'err) kont)
                (('atok,'bnt,'cvalue,'err) kont)
           | AP (('atok,'bnt,'cvalue,'err) kont)
                (('atok # locs) list)
                ('cvalue option list)
                ((locs # 'err) list)
           | Result ((('atok # locs) list, 'cvalue, 'err) pegresult)
           | Looped
End

Definition coreloop_def[nocompute]:
  coreloop G =
   OWHILE (λs. case s of Result _ => F
                       | _ => T)
          (λs. case s of
                   EV (empty v) i r errs k fk => AP k i (SOME v::r) errs
                 | EV (any tf) i r errs k fk =>
                   (case i of
                        [] => AP fk i r ((sloc i, G.anyEOF)::errs)
                      | h::t => AP k t (SOME (tf h) :: r) errs)
                 | EV (tok P tf2) i r errs k fk =>
                   (case i of
                        [] => AP fk i r ((sloc i, G.tokEOF)::errs)
                      | h::t => if P (FST h) then
                                  AP k t (SOME (tf2 h)::r) errs
                                else AP fk i r ((sloc i, G.tokFALSE)::errs))
                 | EV (nt n tf3) i r errs k fk =>
                   if n ∈ FDOM G.rules then
                     EV (G.rules ' n) i r errs (appf1 tf3 k) fk
                   else
                     Looped
                 | EV (seq e1 e2 f) i r errs k fk =>
                     EV e1 i r errs
                        (ksym e2 (appf2 f k) (returnTo i r fk))
                        fk
                 | EV (choice e1 e2 cf) i r errs k fk =>
                     EV e1 i r errs
                        (appf1 (cf o INL) k)
                        (returnTo i r
                         (ksym e2
                          (dropErr (appf1 (cf o INR) k))
                          (cmpErrs fk)))
                 | EV (rpt e lf) i r errs k fk =>
                     EV e i (NONE::r) errs (listsym e lf k) (poplist lf k)
                 | EV (not e v) i r errs k fk =>
                     EV e i r errs
                        (returnTo i r (addErr (sloc i) G.notFAIL fk))
                        (returnTo i (SOME v::r) (dropErr k))
                 | EV (error err) i r errs k fk =>
                     AP fk i r ((sloc i, err) :: errs)
                 | AP done i [] _ => Looped
                 | AP done i (NONE :: t) _ => Looped
                 | AP done i (SOME rv :: _) _ => Result (Success i rv)
                 | AP failed i r [] => Looped
                 | AP failed i r ((l,e)::_) => Result (Failure l e)
                 | AP (dropErr _) i r [] => Looped
                 | AP (dropErr k) i r (_ :: t) => AP k i r t
                 | AP (addErr l e k) i r errs => AP k i r ((l,e)::errs)
                 | AP (cmpErrs k) i r [] => Looped
                 | AP (cmpErrs k) i r [_] => Looped
                 | AP (cmpErrs k) i r ((l2,er2)::(l1,er1)::rest) =>
                     AP k i r ((if locsle l1 l2 then (l2,er2) else (l1,er1)) ::
                               rest)
                 | AP (ksym e k fk) i r errs => EV e i r errs k fk
                 | AP (appf1 f1 k) i (SOME v :: r) errs =>
                     AP k i (SOME (f1 v) :: r) errs
                 | AP (appf1 _ _) _ _ _ => Looped
                 | AP (appf2 f2 k) i (SOME v1 :: SOME v2 :: r) errs =>
                     AP k i (SOME (f2 v2 v1) :: r) errs
                 | AP (appf2 _ _) _ _ _ => Looped
                 | AP (returnTo i r k) i' r' errs => AP k i r errs
                 | AP (listsym e f k) i r errs =>
                     EV e i r errs (listsym e f k) (poplist f k)
                 | AP (poplist f k) i r [] => Looped
                 | AP (poplist f k) i r (_ :: errs) =>
                     AP k i (poplistval f r) errs
                 | Result r => Result r
                 | Looped => Looped)
End

Definition peg_exec_def[nocompute]:
  peg_exec (G:('atok,'bnt,'cvalue,'err)peg) e i r errs k fk =
    case coreloop G (EV e i r errs k fk) of
        SOME r => r
      | NONE => Looped
End

Definition applykont_def[nocompute]:
  applykont G k i r errs =
  case coreloop G (AP k i r errs) of
    SOME r => r
  | NONE => Looped
End

Theorem coreloop_result[simp]:
  coreloop G (Result x) = SOME (Result x)
Proof
  simp[coreloop_def, Once whileTheory.OWHILE_THM]
QED

Theorem coreloop_Looped[simp]:
  coreloop G Looped = NONE
Proof
  simp[coreloop_def, whileTheory.OWHILE_EQ_NONE] >> Induct >>
  simp[arithmeticTheory.FUNPOW]
QED

fun inst_thm def (qs,ths) =
    def |> SIMP_RULE (srw_ss()) [Once whileTheory.OWHILE_THM, coreloop_def]
        |> SPEC_ALL
        |> Q.INST qs
        |> SIMP_RULE (srw_ss()) []
        |> SIMP_RULE bool_ss (GSYM peg_exec_def :: GSYM coreloop_def ::
                              GSYM applykont_def :: coreloop_result ::
                              optionTheory.option_case_def :: ths)

val peg_exec_thm = inst_thm peg_exec_def

val option_case_COND = prove(
  ``option_CASE (if P then Q else R) n s =
    if P then option_CASE Q n s else option_CASE R n s``,
  SRW_TAC [][]);

val better_peg_execs =
    map peg_exec_thm [([`e` |-> `empty v`], []),
                      ([`e` |-> `tok P f`, `i` |-> `[]`], []),
                      ([`e` |-> `tok P f`, `i` |-> `x::xs`],
                       [Once COND_RAND, option_case_COND]),
                      ([`e` |-> `any f`, `i` |-> `[]`], []),
                      ([`e` |-> `any f`, `i` |-> `x::xs`], []),
                      ([`e` |-> `seq e1 e2 sf`], []),
                      ([`e` |-> `choice e1 e2 cf`], []),
                      ([`e` |-> `not e v`], []),
                      ([`e` |-> `rpt e lf`], []),
                      ([‘e’ |-> ‘error err’], [])]

val better_apply =
    map (SIMP_RULE (srw_ss()) [] o inst_thm applykont_def)
        [([`k` |-> `ksym e k fk`], []),
         ([`k` |-> `appf1 f k`, `r` |-> `SOME v::r`], []),
         ([`k` |-> `appf2 f k`, `r` |-> `SOME v1::SOME v2::r`], []),
         ([`k` |-> `returnTo i' r' k`], []),
         ([‘k’ |-> ‘addErr l e k’], []),
         ([‘k’ |-> ‘dropErr k’, ‘errs’ |-> ‘[]’], []),
         ([‘k’ |-> ‘dropErr k’, ‘errs’ |-> ‘e::errs’], []),
         ([‘k’ |-> ‘cmpErrs k’, ‘errs’ |-> ‘(l1,er1)::(l2,er2)::errs’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘[]’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘NONE::rs’], []),
         ([`k` |-> `done`, ‘r’ |-> ‘SOME rv::rs’], []),
         ([`k` |-> `failed`, ‘errs’ |-> ‘[]’], []),
         ([`k` |-> `failed`, ‘errs’ |-> ‘(l,e)::errs’], []),
         ([`k` |-> `poplist f k`, ‘errs’ |-> ‘[]’], []),
         ([`k` |-> `poplist f k`, ‘errs’ |-> ‘le::errs’], []),
         ([`k` |-> `listsym e f k`], [])]

Theorem peg_nt_thm =
  peg_exec_thm ([`e` |-> `nt n nfn`], [Once COND_RAND, option_case_COND])
  |> SIMP_RULE (srw_ss()) []

Theorem peg_exec_thm = LIST_CONJ better_peg_execs

Theorem applykont_thm = LIST_CONJ better_apply

val _ = computeLib.add_persistent_funs ["peg_exec_thm", "applykont_thm"]

val _ = app (fn s => ignore (remove_ovl_mapping s {Thy = "pegexec", Name = s}))
            ["AP", "EV"]

Theorem exec_correct0[local]:
  (∀i e r.
     peg_eval G (i,e) r ⇒
     (∀j v k fk stk errs.
        r = Success j v ⇒
        peg_exec G e i stk errs k fk = applykont G k j (SOME v :: stk) errs) ∧
     (∀k fk stk errs l err.
        r = Failure l err ⇒
        peg_exec G e i stk errs k fk = applykont G fk i stk ((l,err)::errs))) ∧
  (∀i e j vlist.
     peg_eval_list G (i,e) (j,vlist) ⇒
     ∀f k stk errs vs.
       peg_exec G e i (MAP SOME vs ++ (NONE::stk))
                errs
                (listsym e f k)
                (poplist f k) =
       applykont G k j (SOME (f (REVERSE vs ++ vlist)) :: stk) errs)
Proof
  ho_match_mp_tac peg_eval_strongind' >>
  simp[peg_exec_thm, peg_nt_thm, applykont_thm, FORALL_result, AllCaseEqs()] >>
  rpt conj_tac
  >- ((* locsle comparison *) rw[])
  >- ((* rpt - no elements succeed *)
      map_every qx_gen_tac [`e`, `f`, `i`, `j`, `vlist`] >> strip_tac >>
      map_every qx_gen_tac [`k`, `stk`, ‘errs’] >>
      first_x_assum (qspecl_then [`f`, `k`, `stk`, ‘errs’, `[]`] mp_tac) >>
      simp[])
  >- ((* poplistval works *)
      rpt strip_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rpt (pop_assum (K ALL_TAC)) >>
      simp[poplistval_def] >>
      qmatch_abbrev_tac `
        (λ(values,rest). SOME (f values)::rest)
        (poplist_aux [] (MAP SOME vs ++ [NONE] ++ stk)) =
        SOME (f (REVERSE vs))::stk` >>
      qsuff_tac `∀a. poplist_aux a (MAP SOME vs ++ [NONE] ++ stk) =
                     (REVERSE vs ++ a, stk)` >- simp[] >>
      Induct_on `vs` >> simp[poplist_aux_def])
  >- ((* rpt - some elements succeed *)
      map_every qx_gen_tac [`e`, `i0`, `i1`, `j`, `v`, `vs`] >> strip_tac >>
      map_every qx_gen_tac [`f`, `k`, `stk`, ‘errs’, `vs'`] >>
      first_x_assum (qspecl_then [`f`, `k`, `stk`, ‘errs’, `v::vs'`] mp_tac) >>
      simp[] >>
      simp_tac bool_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND])
QED

Theorem exec_correct =
  exec_correct0 |> SIMP_RULE (srw_ss() ++ DNF_ss) []

Theorem pegexec_succeeds =
  exec_correct
    |> CONJUNCTS |> hd |> SPEC_ALL
    |> Q.INST [`k` |-> `done`, `fk` |-> `failed`, `stk` |-> `[]`,
               ‘errs’ |-> ‘[]’]
    |> SIMP_RULE (srw_ss()) [applykont_thm]

Theorem pegexec_fails =
  exec_correct |> CONJUNCTS |> tl |> hd |> SPEC_ALL
               |> Q.INST [`k` |-> `done`, `fk` |-> `failed`,
                          `stk` |-> `[]`, ‘errs’ |-> ‘[]’]
               |> SIMP_RULE (srw_ss()) [applykont_thm]

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy
val list_CASES = listTheory.list_CASES

Theorem pegexec:
  peg_eval G (s,e) r ⇒ peg_exec G e s [] [] done failed = Result r
Proof
  strip_tac >>
  Cases_on ‘r’ >> (drule pegexec_succeeds ORELSE drule pegexec_fails) >>
  simp[]
QED

Theorem peg_eval_executed:
  wfG G ∧ e ∈ Gexprs G ⇒
    (peg_eval G (s,e) r ⇔ peg_exec G e s [] [] done failed = Result r)
Proof
  strip_tac >> eq_tac >- simp[pegexec] >>
  strip_tac >>
  `∃r'. peg_eval G (s,e) r'` by metis_tac[peg_eval_total] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >> first_x_assum (assume_tac o MATCH_MP pegexec) >> fs[]
QED

Definition destResult_def[simp]: destResult (Result r) = r
End

Definition pegparse_def:
  pegparse G s =
    if wfG G then
      case destResult (peg_exec G G.start s [] [] done failed) of
        Success s v => SOME (s,v)
      | _ => NONE
    else NONE
End

Theorem pegparse_eq_SOME:
  pegparse G s = SOME (s', v) ⇔
  wfG G ∧ peg_eval G (s,G.start) (Success s' v)
Proof
  Tactical.REVERSE (Cases_on `wfG G`) >- simp[pegparse_def] >>
  `∃r. peg_eval G (s,G.start) r`
    by metis_tac [peg_eval_total, start_IN_Gexprs] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >>
  reverse (Cases_on ‘r’)
  >- (rw[pegparse_def] >> drule pegexec_fails >> simp[]) >>
  rw[pegparse_def] >> drule pegexec_succeeds >> simp[] >> metis_tac[]
QED

Theorem pegparse_eq_NONE:
  pegparse G s = NONE ⇔ ¬wfG G ∨ ∃l e. peg_eval G (s,G.start) (Failure l e)
Proof
  Cases_on `wfG G` >> simp[pegparse_def] >>
  `∃r. peg_eval G (s,G.start) r`
    by metis_tac [peg_eval_total, start_IN_Gexprs] >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >> reverse (Cases_on ‘r’) >> simp[]
  >- (drule pegexec_fails >> simp[]) >>
  drule pegexec_succeeds >> simp[]
QED

Theorem peg_exec_total:
  wfG G ==> ∃r. peg_exec G G.start i [] [] done failed = Result r
Proof
  strip_tac >>
  `∃pr. peg_eval G (i, G.start) pr` by simp[peg_eval_total, start_IN_Gexprs] >>
  pop_assum mp_tac >> simp[peg_eval_executed, start_IN_Gexprs]
QED

(*
   |- wfG G ⇒
      ∃r.
        coreloop G (pegexec$EV G.start i [] done failed) = SOME (Result r)
*)
Theorem coreloop_total =
  peg_exec_total |> SIMP_RULE (srw_ss()) [peg_exec_def, AllCaseEqs()]

val _ = export_theory()
