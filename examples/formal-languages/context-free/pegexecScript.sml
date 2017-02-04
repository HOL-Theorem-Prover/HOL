open HolKernel Parse boolLib bossLib

open boolSimps lcsymtacs

open pegTheory locationTheory

open rich_listTheory;

val _ = new_theory "pegexec"

val _ = Hol_datatype`
  kont =
    ksym of ('atok,'bnt,'cvalue) pegsym => kont => kont
  | appf1 of ('cvalue -> 'cvalue) => kont
  | appf2 of ('cvalue -> 'cvalue -> 'cvalue) => kont
  | returnTo of ('atok # locs) list => ('cvalue # locs) option list => kont
  | poplist of ('cvalue list -> 'cvalue) => kont
  | listsym of ('atok,'bnt,'cvalue) pegsym =>
               ('cvalue  list -> 'cvalue ) =>
               kont
  | done
  | failed
`

val poplist_aux_def = Define`
  poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t ∧
  poplist_aux acc (NONE::t) = (acc,t) ∧
  poplist_aux acc [] = (acc,[]) (* should never happen *)
`;

val app_list_locs_def = Define`
  app_list_locs f l = (f (MAP FST l), merge_list_locs (REVERSE(MAP SND l)))`;


val poplistval_def = Define`
  poplistval f l = 
    let (values,rest) = poplist_aux [] l in
      SOME(app_list_locs f values) :: rest `;



val _ = Hol_datatype `
  evalcase = EV of ('atok,'bnt,'cvalue) pegsym =>
                   ('atok # locs) list => ('cvalue #locs) option list =>
                   ('atok,'bnt,'cvalue) kont =>
                   ('atok,'bnt,'cvalue) kont
           | AP of ('atok,'bnt,'cvalue) kont =>
                   ('atok # locs) list => ('cvalue # locs) option list
           | Result of (('atok # locs)  list # 'cvalue) option # locs
           | Looped
`;
val coreloop_def = zDefine`
  coreloop G =
   OWHILE (λs. case s of Result _ => F
                       | _ => T)
          (λs. case s of
                   EV (empty v) i r k fk => AP k i (SOME (v, unknown_loc)::r)
                 | EV (any tf) i r k fk =>
                   (case i of
                        [] => AP fk i r
                      | (h, l)::t => AP k t (SOME (tf h, l) :: r))
                 | EV (tok P tf2) i r k fk =>
                   (case i of
                        [] => AP fk i r
                      | (h, l)::t => if P h then AP k t (SOME (tf2 h, l)::r)
                                else AP fk i r)
                 | EV (nt n tf3) i r k fk =>
                   if n ∈ FDOM G.rules then
                     EV (G.rules ' n) i r (appf1 tf3 k) fk
                   else
                     Result (NONE, unknown_loc)
                 | EV (seq e1 e2 f) i r k fk =>
                     EV e1 i r
                        (ksym e2 (appf2 f k) (returnTo i r fk))
                        fk
                 | EV (choice e1 e2 cf) i r k fk =>
                     EV e1 i r
                        (appf1 (cf o INL) k)
                        (returnTo i r (ksym e2 (appf1 (cf o INR) k) fk))
                 | EV (rpt e lf) i r k fk =>
                     EV e i (NONE::r) (listsym e lf k) (poplist lf k)
                 | EV (not e v) i r k fk =>
                     EV e i r (returnTo i r fk) (returnTo i (SOME (v,unknown_loc)::r) k)
                 | AP done i r => Result(case r of
                                             [] => (NONE, unknown_loc)
                                           | NONE::t => (NONE, unknown_loc)
                                           | SOME (rv, l)::t => (SOME(i, rv),l))
                 | AP failed i r => Result (NONE, unknown_loc)
                 | AP (ksym e k fk) i r => EV e i r k fk
                 | AP (appf1 f1 k) i (SOME (v,l) :: r) => 
                     AP k i (SOME (f1 v,l) :: r)
                 | AP (appf1 _ _) _ _ => Looped
                 | AP (appf2 f2 k) i (SOME (v1, l1) :: SOME (v2, l2) :: r) =>
                     AP k i (SOME (f2 v2 v1, merge_locs l2 l1) :: r)
                 | AP (appf2 _ _) _ _ => Looped
                 | AP (returnTo i r k) i' r' => AP k i r
                 | AP (listsym e f k) i r =>
                     EV e i r (listsym e f k) (poplist f k)
                 | AP (poplist f k) i r => AP k i (poplistval f r)
                 | Result r => Result r
                 | Looped => Looped)
`;


val peg_exec_def = zDefine`
  peg_exec (G:('atok,'bnt,'cvalue)peg) e i r k fk =
    case coreloop G (EV e i r k fk) of
        SOME r => r
      | NONE => Looped
`

val applykont_def = zDefine`
  applykont G k i r = case coreloop G (AP k i r) of
                          SOME r => r
                        | NONE => Looped
`

val coreloop_result = store_thm(
  "coreloop_result",
  ``coreloop G (Result x) = SOME (Result x)``,
  simp[coreloop_def, Once whileTheory.OWHILE_THM]);

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
                  ([`e` |-> `tok P f`, `i` |-> `(x,l)::xs`],
                   [Once COND_RAND, option_case_COND]),
                  ([`e` |-> `any f`, `i` |-> `[]`], []),
                  ([`e` |-> `any f`, `i` |-> `(x,l)::xs`], []),
                  ([`e` |-> `seq e1 e2 sf`], []),
                  ([`e` |-> `choice e1 e2 cf`], []),
                  ([`e` |-> `not e v`], []),
                  ([`e` |-> `rpt e lf`], [])]

val better_apply =
    map (inst_thm applykont_def)
        [([`k` |-> `ksym e k fk`], []),
         ([`k` |-> `appf1 f k`, `r` |-> `SOME (v,l)::r`], []),
         ([`k` |-> `appf2 f k`, `r` |-> `SOME (v1,l1)::SOME (v2,l2)::r`], []),
         ([`k` |-> `returnTo i' r' k`], []),
         ([`k` |-> `done`], []),
         ([`k` |-> `failed`], []),
         ([`k` |-> `poplist f k`], []),
         ([`k` |-> `listsym e f k`], [])]

val peg_nt_thm = save_thm(
  "peg_nt_thm",
  peg_exec_thm ([`e` |-> `nt n nfn`], [Once COND_RAND, option_case_COND]))

val peg_exec_thm = save_thm("peg_exec_thm", LIST_CONJ better_peg_execs);

val applykont_thm = save_thm("applykont_thm", LIST_CONJ better_apply);

val _ = computeLib.add_persistent_funs ["peg_exec_thm", "applykont_thm"]

val _ = app (fn s => ignore (remove_ovl_mapping s {Thy = "pegexec", Name = s}))
            ["AP", "EV"]

val exec_correct0 = prove(
  ``(∀i e r l l'. peg_eval G (i,e) (r,l,l') ⇒
             (∀j v k fk stk.
                r = SOME(j,v) ⇒
                peg_exec G e i stk k fk = applykont G k j (SOME (v, l, l') :: stk)) ∧
             (∀k fk stk.
                r = NONE ⇒ peg_exec G e i stk k fk = applykont G fk i stk)) ∧
    (∀i e j vlist l l'.
      peg_eval_list G (i,e) (j,vlist,l,l') ⇒
      ∀f k stk vs.
          peg_exec G e i (APPEND (MAP SOME vs) (NONE::stk))
                     (listsym e f k)
                     (poplist f k) =
          applykont G k j (SOME (f (APPEND (REVERSE (MAP FST vs)) vlist), 
                           merge_list_locs ( (MAP SND vs))) :: stk))``,
  ho_match_mp_tac peg_eval_strongind' >>
  simp[peg_exec_thm, peg_nt_thm, applykont_thm] >>
  rpt conj_tac
  >- cheat 
  >- ((* rpt - no elements succeed *)
      map_every qx_gen_tac [`e`, `f`, `i`, `j`, `vlist`, `l`, `l'`] >> 
      strip_tac >>
      map_every qx_gen_tac [`k`, `stk`] >>
      first_x_assum (qspecl_then [`f`, `k`, `stk`, `[]`] mp_tac) >>
      simp[merge_list_locs_def] >>
      cheat 
      )
  >- ((* poplistval works *)
      rpt strip_tac >> rpt AP_TERM_TAC >> rpt (pop_assum (K ALL_TAC)) >>
      simp[poplistval_def, app_list_locs_def,MAP_REVERSE] >>
(*      qmatch_abbrev_tac `
        (λ(values,rest). SOME (app_list_locs f values)::rest)
        (poplist_aux [] (MAP SOME vs ++ [NONE] ++ stk)) =
        SOME (f (REVERSE (MAP FST vs), i, e'))::stk` >> *)
      qsuff_tac `∀a. poplist_aux a (MAP SOME vs ++ [NONE] ++ stk) =
                     (REVERSE vs ++ a, stk)`
                     >- simp[MAP_REVERSE] 
      >- (Induct_on `vs` >> simp[poplist_aux_def]))
  >- ((* rpt - some elements succeed *)
      map_every qx_gen_tac [`e`,`i0`,`i1`,`l1`,`l2`,`j`,`l3`,`l4`,`v`,`s`] >> 
      strip_tac >>
      map_every qx_gen_tac [`f`, `k`, `stk`, `vs'`] >>
      first_x_assum (qspecl_then [`f`, `k`, `stk`, `(v, l1, l2)::vs'`] mp_tac) >>
      simp[] >>
      simp_tac bool_ss [GSYM
          listTheory.APPEND_ASSOC,listTheory.APPEND,merge_locs_def] >>
      cheat
      ))

val exec_correct = save_thm(
  "exec_correct",
  exec_correct0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [])

val pegexec_succeeds = save_thm(
  "pegexec_succeeds",
  exec_correct |> CONJUNCTS |> hd |> SPEC_ALL
               |> Q.INST [`k` |-> `done`, `fk` |-> `failed`, `stk` |-> `[]`]
               |> SIMP_RULE (srw_ss()) [applykont_thm])

val pegexec_fails = save_thm(
  "pegexec_fails",
  exec_correct |> CONJUNCTS |> tl |> hd |> SPEC_ALL
               |> Q.INST [`k` |-> `done`, `fk` |-> `failed`, `stk` |-> `[]`]
               |> SIMP_RULE (srw_ss()) [applykont_thm])

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy
val list_CASES = listTheory.list_CASES

val pegexec = store_thm(
  "pegexec",
  ``peg_eval G (s,e) (r,l) ⇒ ?l'. peg_exec G e s [] done failed = Result (r,l')``,
   metis_tac [option_CASES, pair_CASES, pegexec_fails, pegexec_succeeds]);

val peg_eval_executed = store_thm(
  "peg_eval_executed",
  ``wfG G ∧ e ∈ Gexprs G ⇒
    (peg_eval G (s,e) (r,l) ⇔ ?l'. peg_exec G e s [] done failed = Result (r,l'))``,
  strip_tac >> eq_tac
  >- (
    `r = NONE ∨ ∃s' v. r = SOME (s',v)`
        by metis_tac[option_CASES, pair_CASES] >>
      simp[pegexec_fails, pegexec_succeeds] >> metis_tac[pegexec]) >>
  strip_tac >>
  `∃r' l''. peg_eval G (s,e) (r',l'')` by metis_tac[peg_eval_total] >>
  Cases_on `l''` >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  first_x_assum (assume_tac o MATCH_MP pegexec) >> fs[] >>
  fs[] >>
  cheat );

val destResult_def = Define`destResult (Result r) = r`
val _ = export_rewrites ["destResult_def"]

val pegparse_def = Define`
  pegparse G s =
    if wfG G then destResult (peg_exec G G.start s [] done failed)
    else (NONE, unknown_loc) `;

val pegparse_eq_SOME = store_thm(
  "pegparse_eq_SOME",
  ``pegparse G s = (SOME (s',v),l) ⇔ wfG G ∧ peg_eval G (s,G.start) (SOME(s',v), l)``,
  Tactical.REVERSE (Cases_on `wfG G`) >- simp[pegparse_def] >>
  `∃r. peg_eval G (s,G.start) r`
    by metis_tac [peg_eval_total, start_IN_Gexprs] >>
  Cases_on`r` >> Cases_on`r'` >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >>
  `q = NONE ∨ ∃s2 v2. q = SOME (s2,v2)` by metis_tac [option_CASES, pair_CASES]
  >- rw[pegparse_def, pegexec_fails] >>
  rw[pegparse_def] >> first_x_assum (assume_tac o MATCH_MP pegexec_succeeds) >>
  simp[] >> metis_tac[]);

val pegparse_eq_NONE = store_thm(
  "pegparse_eq_NONE",
  ``pegparse G s = (NONE,unknown_loc) ⇔ ? l. ¬wfG G ∨ peg_eval G (s,G.start) (NONE,l)``,
  Cases_on `wfG G` >> simp[pegparse_def] >>
  `∃r. peg_eval G (s,G.start) r`
    by metis_tac [peg_eval_total, start_IN_Gexprs] >>
  Cases_on`r` >> Cases_on`r'` >>
  first_assum (assume_tac o MATCH_MP (CONJUNCT1 peg_deterministic)) >>
  simp[] >>
  `q = NONE ∨ ∃s2 v2. q = SOME (s2,v2)` by metis_tac [option_CASES, pair_CASES]
  >- rw[pegexec_fails] >>
  rw[] >> first_x_assum (assume_tac o MATCH_MP pegexec_succeeds) >>
  simp[]);

val peg_exec_total = store_thm(
  "peg_exec_total",
  ``wfG G ==> ∃r l. peg_exec G G.start i [] done failed = Result (r, l)``,
  strip_tac >>
  `∃pr l. peg_eval G (i, G.start) (pr,l)` by simp[peg_eval_total, start_IN_Gexprs] >>
  pop_assum mp_tac >> 
  simp[peg_eval_executed, start_IN_Gexprs] >> rw[] >> rw[]);

val option_case_EQ = prove(
  ``option_CASE x n s = v ⇔ x = NONE ∧ n = v ∨ ∃v0. x = SOME v0 ∧ v = s v0``,
  Cases_on `x` >> simp[] >> metis_tac[]);

(*
   |- wfG G ⇒
      ∃r.
        coreloop G (pegexec$EV G.start i [] done failed) = SOME (Result r)
*)
val coreloop_total = save_thm(
  "coreloop_total",
  peg_exec_total |> SIMP_RULE (srw_ss()) [peg_exec_def, option_case_EQ])


val _ = export_theory()
