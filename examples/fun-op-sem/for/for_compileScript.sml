open HolKernel Parse boolLib bossLib BasicProvers;

val _ = new_theory "for_compile";

(*

This file proves correctness of a compiler for the FOR language
defined in forScript.sml. The compiler targets a simple assembly-like
language. We prove that the compiler preserves the top-level
observable semantics.

The compiler consists of three phasees:
 - the first phase simplifies For loops and removes Dec
 - the second phase compiles expressions into very simple assignments
 - the third phase maps the FOR language into assmembly code

*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open forTheory listTheory arithmeticTheory;

val _ = temp_tight_equality ();


(* === PHASE 1 : simplifies For loops and removes Dec === *)

val Loop_def = Define `
  Loop t = For (Num 1) (Num 1) t`;

val phase1_def = Define `
  (phase1 (Exp e) = Exp e) /\
  (phase1 (Dec x t) = Seq (Exp (Assign x (Num 0))) (phase1 t)) /\
  (phase1 (Break) = Break) /\
  (phase1 (Seq t1 t2) = Seq (phase1 t1) (phase1 t2)) /\
  (phase1 (If e t1 t2) = If e (phase1 t1) (phase1 t2)) /\
  (phase1 (For e1 e2 t) = Loop (If e1 (Seq (phase1 t) (Exp e2)) Break))`;

(* Verification of phase 1 *)

val sem_e_break = store_thm("sem_e_break[simp]",
  ``!b1 s. ~(sem_e s b1 = (Rbreak,r)) /\ ~(sem_e s b1 = (Rtimeout,r))``,
  Induct \\ rpt strip_tac
  \\ fs [sem_e_def]
  \\ every_case_tac \\ fs [] \\ rfs []);

val phase1_correct = store_thm("phase1_correct",
  ``!s t. sem_t s (phase1 t) = sem_t s t``,
  once_rewrite_tac [EQ_SYM_EQ]
  \\ recInduct sem_t_ind
  \\ rw [phase1_def,Loop_def]
  \\ simp [sem_t_def_with_stop,sem_e_def]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ simp [sem_t_def_with_stop])
  \\ fs [STOP_def]);

val phase1_pres = store_thm("phase1_pres",
  ``!t. semantics (phase1 t) = semantics t``,
  fs [semantics_def,phase1_correct]);

(* End of phase 1 verification -- 18 lines *)

(* the rest is old redundant stuff *)

val sem_t_Dec = store_thm("sem_t_Dec",
  ``sem_t s (Dec v t) =
    sem_t s (Seq (Exp (Assign v (Num 0))) t)``,
  fs [sem_t_def,sem_e_def]);

val sem_t_pull_if = prove(
  ``sem_t s1 (if b then t1 else t2) =
    (if b then sem_t s1 t1 else sem_t s1 t2)``,
  SRW_TAC [] []);

val sem_t_eval = save_thm("sem_t_eval",
  (EVAL THENC REWRITE_CONV [sem_t_pull_if] THENC EVAL)
    ``sem_t s (If b (Exp (Num 0)) Break)``);

val sem_t_Loop = save_thm("sem_t_Loop",
  ``sem_t s (Loop t)``
  |> (SIMP_CONV (srw_ss()) [Once sem_t_def,sem_e_def,Loop_def] THENC
      REWRITE_CONV [GSYM Loop_def]));

val sem_t_For_swap_body = prove(
  ``(!s. sem_t s t1 = sem_t s t2) ==>
    (sem_t s (For b1 b2 t1) = sem_t s (For b1 b2 t2))``,
  STRIP_TAC
  \\ completeInduct_on `s.clock`
  \\ rw [sem_t_def_with_stop,sem_e_def,Once sem_t_Loop]
  \\ every_case_tac \\ fs [PULL_FORALL,STOP_def]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ fs [dec_clock_def]
  \\ imp_res_tac sem_e_clock
  \\ imp_res_tac sem_t_clock
  \\ decide_tac);

val sem_t_For = store_thm("sem_t_For",
  ``!s b1 b2 t. sem_t s (For b1 b2 t) =
                sem_t s (Loop (If b1 (Seq t (Exp b2)) Break))``,
  REPEAT STRIP_TAC
  \\ completeInduct_on `s.clock`
  \\ rw [sem_t_def_with_stop,sem_e_def,Once sem_t_Loop]
  \\ Cases_on `sem_e s b1` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ SRW_TAC [] [sem_t_def_with_stop]
  \\ Cases_on `sem_t r t` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `sem_e r' b2` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ SRW_TAC [] []
  \\ fs [sem_e_break]
  \\ fs [PULL_FORALL,STOP_def]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ fs [dec_clock_def]
  \\ imp_res_tac sem_e_clock
  \\ imp_res_tac sem_t_clock
  \\ decide_tac);


(* === PHASE 2 : compiles expressions into very simple assignments === *)

val comp_exp_def = Define `
  (comp_exp (Var v) s = Exp (Assign s (Var v))) /\
  (comp_exp (Num i) s = Exp (Assign s (Num i))) /\
  (comp_exp (Assign v e) s =
     (Seq (comp_exp e s) (Exp (Assign v (Var s))))) /\
  (comp_exp (Add x y) s =
     (Seq (comp_exp x s)
     (Seq (comp_exp y (s++"'"))
          (Exp (Assign s (Add (Var s) (Var (s++"'"))))))))`;

val flatten_t_def = Define `
  (flatten_t (Exp e) n = comp_exp e n) /\
  (flatten_t (Dec x t) n = t) /\
  (flatten_t (Break) n = Break) /\
  (flatten_t (Seq t1 t2) n = Seq (flatten_t t1 n) (flatten_t t2 n)) /\
  (flatten_t (For e1 e2 t) n = For e1 e2 (flatten_t t n)) /\
  (flatten_t (If e t1 t2) n =
     Seq (comp_exp e n) (If (Var n) (flatten_t t1 n) (flatten_t t2 n)))`;

val MAX_def = Define `MAX n m = if n < m then m else n:num`

val exp_max_def = Define `
  (exp_max (Var v) = LENGTH v) /\
  (exp_max (Add x y) = MAX (exp_max x) (exp_max y)) /\
  (exp_max (Assign v e) = MAX (LENGTH v) (exp_max e)) /\
  (exp_max _ = 0)`;

val t_max_def = Define `
  (t_max (Exp e) = exp_max e) /\
  (t_max (Dec x t) = MAX (LENGTH x) (t_max t)) /\
  (t_max (Break) = 0) /\
  (t_max (Seq t1 t2) = MAX (t_max t1) (t_max t2)) /\
  (t_max (For e1 e2 t) = MAX (exp_max e1) (MAX (exp_max e2) (t_max t))) /\
  (t_max (If e t1 t2) = MAX (exp_max e) (MAX (t_max t1) (t_max t2)))`;

val phase2_def = Define `
  phase2 t = flatten_t t ("temp" ++ REPLICATE (t_max t - 3) #"'")`;

(* Verification of phase 2 *)

val possible_var_name_def = Define `
  possible_var_name v s = !n. ~(v ++ REPLICATE n #"'" IN FDOM s)`;

val possible_var_name_IMP_SUBMAP = prove(
  ``possible_var_name n s.store /\ s.store SUBMAP t.store ==>
    s.store SUBMAP t.store |+ (n,i)``,
  fs [FLOOKUP_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
  \\ fs [possible_var_name_def] \\ REPEAT STRIP_TAC
  \\ SRW_TAC [] [] \\ fs []
  \\ METIS_TAC [APPEND_NIL,rich_listTheory.REPLICATE]);

val MAX_LESS = prove(
  ``MAX n m < k <=> n < k /\ m < k``,
  SRW_TAC [] [MAX_def] \\ DECIDE_TAC);

val sem_e_possible_var_name = prove(
  ``!e s i r.
      (sem_e s e = (Rval i,r)) /\ exp_max e < STRLEN k ==>
      possible_var_name k s.store ==>
      possible_var_name k r.store``,
  Induct \\ fs [sem_e_def] \\ REPEAT STRIP_TAC \\ every_case_tac \\ fs []
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPEC `r'`)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
    \\ fs [exp_max_def,MAX_LESS])
  \\ SRW_TAC [] [] \\ fs [exp_max_def,MAX_LESS]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s'`) \\ fs []
  \\ fs [store_var_def,possible_var_name_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ fs [] \\ DECIDE_TAC);

val r_cases_eq = prove_case_eq_thm {
  case_def = forTheory.r_case_def,
  nchotomy = forTheory.r_nchotomy
};

val pair_cases_eq = Q.prove(
  ‘(pair_CASE p f = v) ⇔ ∃q r. p = (q,r) ∧ v = f q r’,
  Cases_on `p` >> simp[] >> metis_tac[]);

val bool_cases_eq = Q.prove(
  ‘(if p then q else r) = v ⇔ p /\ q = v ∨ ¬p ∧ r = v’,
  Cases_on `p` >> simp[]);

val option_cases_eq = Q.prove(
  ‘(option_CASE opt n s = v) ⇔
     opt = NONE ∧ n = v ∨ ∃sv. opt = SOME sv ∧ s sv = v’,
  Cases_on ‘opt’ >> simp[]);

val store_var_clock = Q.store_thm(
  "store_var_clock[simp]",
  ‘(store_var v n s).clock = s.clock’,
  simp[store_var_def]);

local val fs = fsrw_tac[] in
val comp_exp_correct = prove(
  ``!e s t n res s1.
      sem_e s e = (res,s1) /\ res <> Rfail /\
      possible_var_name n s.store /\
      s.store SUBMAP t.store /\ (t.clock = s.clock) /\
      exp_max e < LENGTH n ==>
      ?t1. (sem_t t (comp_exp e n) = (res,t1)) /\
           s1.store SUBMAP t1.store /\ (t1.clock = s1.clock) /\
           (!v. (res = Rval v) ==> FLOOKUP t1.store n = SOME v) /\
           possible_var_name n s1.store /\
           (!k v. possible_var_name k s.store /\
                  exp_max e < LENGTH k /\ LENGTH k < LENGTH n /\
                  FLOOKUP t.store k = SOME v ==>
                  FLOOKUP t1.store k = SOME v)``,
  Induct
  >- (rpt gen_tac >> rename [‘Var vnm’] >>
      simp[sem_e_def, comp_exp_def, sem_t_def, option_cases_eq] >> csimp[] >>
      rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      imp_res_tac FLOOKUP_SUBMAP >> simp[store_var_def] >>
      imp_res_tac possible_var_name_IMP_SUBMAP >>
      simp[FLOOKUP_DEF, FAPPLY_FUPDATE_THM] >> rw[])
  >- (rpt gen_tac >> rename [‘Num n’] >>
      simp[sem_e_def, comp_exp_def, sem_t_def] >> rw[] >>
      simp[store_var_def] >>
      imp_res_tac possible_var_name_IMP_SUBMAP >>
      simp[FLOOKUP_DEF, FAPPLY_FUPDATE_THM] >> rw[])
  >- (rpt gen_tac >> rename [‘Add e1 e2’] >>
      simp[sem_e_def, SimpL “$==>”, pair_cases_eq, r_cases_eq] >>
      rpt strip_tac >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      fs[exp_max_def, MAX_LESS] >>
      dsimp[sem_t_def, comp_exp_def, pair_cases_eq, r_cases_eq] >>
      rename [‘sem_e s1 e1 = (Rval n1, s2)’, ‘sem_e s2 e2 = (Rval n2, s3)’] >>
      first_x_assum
        (fn th =>
            mp_then.mp_then (mp_then.Pos hd) mp_tac th
                            (ASSUME “sem_e s1 e1 = (Rval n1, s2)”)) >>
      simp[] >>
      rpt (disch_then (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac))>>
      disch_then (qx_choose_then ‘t1’ strip_assume_tac) >> simp[] >>
      rename1 ‘possible_var_name n s2.store’ >>
      ‘possible_var_name (STRCAT n "'") s2.store’
        by (fs[possible_var_name_def] >> rpt strip_tac >>
            rename [‘STRCAT (STRCAT nm "'") (REPLICATE c #"'")’] >>
            first_x_assum (qspec_then ‘SUC c’ mp_tac) >>
            simp[] >>
            full_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
      pop_assum mp_tac >>
      first_x_assum (disch_then o mp_then.mp_then mp_then.Any mp_tac) >>
      simp[] >>
      rpt (disch_then (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac))>>
      disch_then (qx_choose_then ‘t2’ strip_assume_tac) >> simp[] >>
      simp[sem_e_def, pair_cases_eq, r_cases_eq, option_cases_eq] >>
      dsimp[] >> rw[]
      >- (simp[store_var_def] >>
          irule possible_var_name_IMP_SUBMAP >> simp[] >>
          metis_tac[sem_e_possible_var_name])
      >- simp[store_var_def, FLOOKUP_DEF]
      >- metis_tac[sem_e_possible_var_name]
      >- (simp[store_var_def] >>
          rename [‘FLOOKUP (t2.store |+ (n, _)) k = SOME _’] >>
          ‘k ≠ n’ by (strip_tac >> fs[]) >>
          simp[FLOOKUP_UPDATE] >> first_x_assum irule >> simp[] >>
          metis_tac[sem_e_possible_var_name]))
  >- (rpt gen_tac >> rename [‘Assign v e’] >>
      simp[sem_e_def, SimpL “$==>”, pair_cases_eq, r_cases_eq] >>
      rw[] >> fs[sem_e_break, exp_max_def, MAX_LESS] >>
      dsimp[comp_exp_def, sem_t_def, pair_cases_eq, r_cases_eq] >>
      simp[sem_e_def, pair_cases_eq, r_cases_eq, option_cases_eq] >>
      first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
      simp[] >>
      disch_then (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
      disch_then (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
      simp[] >> strip_tac >> simp[store_var_def] >> rw[] >>
      fs[SUBMAP_DEF, FAPPLY_FUPDATE_THM, FLOOKUP_DEF] >> rw[] >> fs[] >>
      fs[possible_var_name_def] >> rpt strip_tac >>
      BasicProvers.VAR_EQ_TAC >>
      full_simp_tac (srw_ss() ++ ARITH_ss) []))
end

val phase2_subset_def = Define `
  (phase2_subset (Dec v t) = F) /\
  (phase2_subset (Exp e) = T) /\
  (phase2_subset Break = T) /\
  (phase2_subset (Seq t1 t2) = (phase2_subset t1 /\ phase2_subset t2)) /\
  (phase2_subset (If e t1 t2) = (phase2_subset t1 /\ phase2_subset t2)) /\
  (phase2_subset (For e1 e2 t) = ((e1 = Num 1) /\ (e2 = Num 1) /\
     phase2_subset t))`

val sem_t_possible_var_name = prove(
  ``!s e i r.
      (sem_t s e = (i,r)) /\ t_max e < STRLEN k /\ i <> Rfail ==>
      possible_var_name k s.store ==>
      possible_var_name k r.store``,
  HO_MATCH_MP_TAC sem_t_ind \\ REVERSE (REPEAT STRIP_TAC)
  THEN1
   (NTAC 4 (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [sem_t_def]
    \\ fs [t_max_def,MAX_LESS]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `sem_e s e1` \\ fs []
    \\ Cases_on `q` \\ fs [sem_e_break]
    \\ Cases_on `i' = 0` \\ fs []
    \\ SRW_TAC [] [] \\ fs [t_max_def,MAX_LESS]
    THEN1 (METIS_TAC [sem_e_possible_var_name])
    \\ Cases_on `sem_t r' e` \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    THEN1 (METIS_TAC [sem_e_possible_var_name])
    THEN1 (METIS_TAC [sem_e_possible_var_name])
    \\ Cases_on `sem_e r'' e2` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ Cases_on `r'''.clock = 0` \\ fs[]
    \\ METIS_TAC [sem_e_possible_var_name])
  \\ fs [sem_t_def,t_max_def,MAX_LESS]
  THEN1
   (Cases_on `sem_e s e` \\ fs [] \\ Cases_on `q` \\ fs [sem_e_break]
    \\ Cases_on `i' = 0` \\ fs []
    \\ METIS_TAC [sem_e_possible_var_name])
  THEN1 (Cases_on `sem_t s e` \\ fs [] \\ Cases_on `q` \\ fs [sem_e_break])
  THEN1 (SRW_TAC [] [])
  THEN1
   (fs [store_var_def]
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [possible_var_name_def]
    \\ CCONTR_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [] \\ DECIDE_TAC)
  THEN1
   (Cases_on `i` \\ fs [sem_e_break]
    \\ IMP_RES_TAC sem_e_possible_var_name))
  |> Q.SPECL [`s`,`e`,`Rval i`,`r`]
  |> SIMP_RULE (srw_ss()) [];

val IMP_IMP = METIS_PROVE [] ``b /\ (b1 ==> b2) ==> ((b ==> b1) ==> b2)``

val flatten_t_correct = prove(
  ``!s e t n res s1.
      sem_t s e = (res,s1) /\ res <> Rfail /\ phase2_subset e /\
      possible_var_name n s.store /\
      s.store SUBMAP t.store /\ (t.clock = s.clock) /\
      t_max e < LENGTH n ==>
      ?t1. (sem_t t (flatten_t e n) = (res,t1)) /\
           s1.store SUBMAP t1.store /\ (t1.clock = s1.clock) /\
           possible_var_name n s1.store /\
           (!k v. possible_var_name k s.store /\
                  t_max e < LENGTH k /\ LENGTH k < LENGTH n /\
                  FLOOKUP t.store k = SOME v ==>
                  FLOOKUP t1.store k = SOME v)``,
  HO_MATCH_MP_TAC sem_t_ind \\ REPEAT STRIP_TAC \\ fs [phase2_subset_def]
  THEN1 (* Exp *)
   (fs [flatten_t_def,sem_t_def,t_max_def]
    \\ MP_TAC (SPEC_ALL comp_exp_correct)
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs [])
  THEN1 (* Break *)
   (fs [sem_t_def,flatten_t_def] \\ SRW_TAC [] [])
  THEN1 (* Seq *)
   (fs [sem_t_def,flatten_t_def] \\ SRW_TAC [] []
    \\ fs [t_max_def,MAX_LESS]
    \\ Cases_on `sem_t s e` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t`,`n`])
    \\ `q <> Rfail` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1:state`,`n`])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
    \\ IMP_RES_TAC sem_t_possible_var_name)
  THEN1 (* If *)
   (fs [sem_t_def,flatten_t_def]
    \\ Cases_on `sem_e s e` \\ fs []
    \\ `q <> Rfail` by (REPEAT STRIP_TAC \\ fs [])
    \\ MP_TAC (Q.SPECL [`e`,`s`] comp_exp_correct) \\ fs []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t`,`n`])
    \\ fs [MAX_LESS,t_max_def] \\ REPEAT STRIP_TAC \\ fs [sem_e_def]
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ TRY (SRW_TAC [] [] \\ NO_TAC)
    \\ Q.MATCH_ASSUM_RENAME_TAC `FLOOKUP t3.store n = SOME i`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t3:state`,`n`]) \\ fs []
    \\ Cases_on `i = 0` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
    \\ IMP_RES_TAC sem_e_possible_var_name)
  THEN1 (* For *)
   (ASM_SIMP_TAC (srw_ss()) [sem_t_def_with_stop,flatten_t_def,sem_e_def]
    \\ fs [sem_e_def,t_max_def] \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `sem_t s (For (Num 1) (Num 1) e) = (res,s1)` MP_TAC
    \\ ONCE_REWRITE_TAC [sem_t_def] \\ fs [sem_e_def]
    \\ REPEAT STRIP_TAC \\ Cases_on `sem_t s e` \\ fs []
    \\ `q <> Rfail` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t`,`n`])
    \\ fs [MAX_LESS,t_max_def] \\ REPEAT STRIP_TAC \\ fs [sem_e_def]
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ TRY (SRW_TAC [] [] \\ NO_TAC)
    \\ Cases_on `r.clock = 0` \\ fs [] THEN1 (SRW_TAC [] [])
    \\ fs [STOP_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`n`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [dec_clock_def]) \\ REPEAT STRIP_TAC \\ fs []
    \\ fs [flatten_t_def] \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
    \\ IMP_RES_TAC sem_t_possible_var_name));

val phase2_correct = flatten_t_correct
  |> Q.SPECL [`s`,`t`,`s`,`"temp" ++ REPLICATE (t_max t - 3) #"'"`]
  |> DISCH ``s.store = FEMPTY``
  |> SIMP_RULE (srw_ss()) [GSYM phase2_def,Once possible_var_name_def,
       rich_listTheory.LENGTH_REPLICATE,DECIDE ``n < 4 + (n - 3:num)``,
       PULL_FORALL] |> GEN_ALL;

val pair_eq = prove(
  ``(x = (y1,y2)) <=> (FST x = y1) /\ (SND x = y2)``,
  Cases_on `x` \\ fs [] \\ METIS_TAC []);

val phase2_correct_FST = prove(
  ``phase2_subset t ==>
    (FST (sem_t (s_with_clock c) t) = Rfail) \/
    (FST (sem_t (s_with_clock c) (phase2 t)) =
     FST (sem_t (s_with_clock c) t))``,
  REPEAT STRIP_TAC \\ CCONTR_TAC \\ fs []
  \\ MP_TAC (phase2_correct
      |> Q.SPECL [`t`,`s_with_clock c`]
      |> SIMP_RULE std_ss [pair_eq])
  \\ fs [s_with_clock_def]);

val lemma = prove(
  ``((if b then x1 else x2) <> x2) <=> (x1 <> x2) /\ b``,
  Cases_on `b` \\ fs [])

(* We prove that phase 2 preserves semantics if the source semantics
   does not Crash (implied by successful type check) and if the syntax
   of the compiler program fits with phase2_subset (i.e. syntax
   produced by phase1) *)

val phase2_pres = store_thm("phase2_pres",
  ``!t. semantics t <> Crash /\ phase2_subset t ==>
        semantics (phase2 t) = semantics t``,
  REPEAT STRIP_TAC \\ fs [semantics_thm]
  \\ REVERSE (SRW_TAC [] []) \\ fs [lemma] \\ fs [pair_eq]
  \\ REPEAT (FIRST_X_ASSUM (MP_TAC o Q.SPEC `c:num`))
  \\ REPEAT STRIP_TAC \\ fs []
  \\ MP_TAC phase2_correct_FST \\ fs []);


(* === PHASE 3 : maps the FOR language into assmembly code === *)

(* We define the tagert assembly language *)

val _ = Datatype `
reg = Reg string`

val _ = Datatype `
instr =
    Add reg reg reg
  | Int reg int
  | Jmp num
  | JmpIf reg num`;

val _ = Datatype `
state_a = <| store : state; pc : num; instrs : instr list |>`;

val do_jump_def = Define `
do_jump s n =
  if n > s.pc then
    (Rval 0, s with pc := n)
  else if s.store.clock = 0 then
    (Rtimeout, s)
  else
    let st' = s.store with clock := s.store.clock - 1 in
      (Rval 0, s with <| store := st'; pc := n |>)`;

val inc_pc_def = Define `
inc_pc s = s with pc := s.pc + 1`;

val sem_e_clock = prove(
  ``!e x st' st. (sem_e st e = (x,st')) ==> (st'.clock = st.clock)``,
  Induct \\ fs [sem_e_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs [store_var_def] \\ METIS_TAC []) |> GSYM;

val sem_a_def = tDefine "sem_a" `
sem_a s =
  if s.pc < LENGTH s.instrs then
    case EL s.pc s.instrs of
       | Int (Reg r) i =>
           let (r,st) = sem_e s.store (Assign r (Num i)) in
           let s' = s with store := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Add (Reg r) (Reg r1) (Reg r2) =>
           let (r,st) = sem_e s.store (Assign r (Add (Var r1) (Var r2))) in
           let s' = s with store := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Jmp n' =>
           (case do_jump s n' of
               | (Rval _, s') => sem_a s'
               | r => r)
       | JmpIf (Reg r) n' =>
           let (r,st) = sem_e s.store (Var r) in
           let s' = s with store := st in
             case r of
                | Rval n =>
                    if n <> 0 then
                      sem_a (inc_pc s')
                    else
                      (case do_jump s' n' of
                          | (Rval _, s') => sem_a s'
                          | r => r)
                | _ => (r, s')
  else if s.pc = LENGTH s.instrs then
    (Rval 0, s)
  else
    (Rfail, s)`
  (WF_REL_TAC `inv_image (measure I LEX measure I)
       (\s. (s.store.clock,LENGTH s.instrs - s.pc))`
   \\ fs [inc_pc_def,do_jump_def,LET_DEF]
   \\ REPEAT STRIP_TAC
   \\ every_case_tac \\ fs []
   \\ SRW_TAC [] [] \\ fs []
   \\ IMP_RES_TAC sem_e_clock
   \\ DECIDE_TAC);

val a_state_def = Define `
  a_state code clock =
    <| store := s_with_clock clock; pc := 0; instrs := code |>`;

val asm_semantics_def = Define `
  asm_semantics code =
    if (?c s. sem_a (a_state code c) = (Rval 0,s)) then Terminate
    else if (!c. ?s. sem_a (a_state code c) = (Rtimeout,s)) then Diverge
    else Crash`;

(* Definition of phase3 *)

val phase3_def = Define `
  (phase3 n b (Dec v t) = []) /\
  (phase3 n b (Exp e) =
     case e of
     | Assign v (Var x) =>
         if x = v then [] else [Int (Reg v) 0; Add (Reg v) (Reg x) (Reg v)]
     | Assign v (Add (Var v1) (Var v2)) => [Add (Reg v) (Reg v1) (Reg v2)]
     | Assign v (Num i) => [Int (Reg v) i]
     | _ => []) /\
  (phase3 n b Break = [Jmp b]) /\
  (phase3 n b (Seq t1 t2) =
     let c1 = phase3 n b t1 in
     let c2 = phase3 (n + LENGTH c1) b t2 in
       c1 ++ c2) /\
  (phase3 n b (If e t1 t2) =
     let c1 = phase3 (n + 1) b t1 in
     let c2 = phase3 (n + 2 + LENGTH c1) b t2 in
       [JmpIf (case e of Var v => Reg v | _ => Reg "")
          (n + 2 + LENGTH c1)] ++ c1 ++
       [Jmp (n + 2 + LENGTH c1 + LENGTH c2)] ++ c2) /\
  (phase3 n b (For e1 e2 t) =
     let c1 = phase3 n 0 t in
     let c2 = phase3 n (n + 1 + LENGTH c1) t in
       c2 ++ [Jmp n])`

(* Verification of phase3 *)

val LENGTH_phase3 = prove(
  ``!t n b. LENGTH (phase3 n b t) = LENGTH (phase3 0 0 t)``,
  Induct \\ fs [phase3_def,LET_DEF]);

val phase3_subset_def = Define `
  (phase3_subset (Dec v t) = F) /\
  (phase3_subset (Exp e) <=>
     (?v x. e = Assign v (Var x)) \/
     (?v i. e = Assign v (Num i)) \/
     (?v x y. e = Assign v (Add (Var x) (Var y)))) /\
  (phase3_subset Break = T) /\
  (phase3_subset (Seq t1 t2) = (phase3_subset t1 /\ phase3_subset t2)) /\
  (phase3_subset (If e t1 t2) <=>
     (?w. e = Var w) /\ phase3_subset t1 /\ phase3_subset t2) /\
  (phase3_subset (For e1 e2 t) = ((e1 = Num 1) /\ (e2 = Num 1) /\ phase3_subset t))`

val instr_lookup_lemma = prove(
  ``(x.pc = LENGTH xs) /\ (x.instrs = xs ++ [y] ++ ys) ==>
    x.pc < LENGTH x.instrs /\ (EL x.pc x.instrs = y)``,
  fs [DECIDE ``n < n + 1 + m:num``,rich_listTheory.EL_LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

val EL_LENGTH_APPEND_LEMMA =
  rich_listTheory.EL_LENGTH_APPEND
  |> Q.SPECL [`[y] ++ ys`,`xs1++xs2`]
  |> SIMP_RULE (srw_ss()) []

val EL_LEMMA = prove(
  ``(LENGTH (xs1 ++ xs2 ++ xs3) = n) ==>
    (EL n (xs1 ++ xs2 ++ xs3 ++ [y] ++ ys1 ++ ys2) = y)``,
  Q.SPEC_TAC (`(xs1 ++ xs2 ++ xs3)`,`zs`) \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

val state_rel_def = Define `
  state_rel s x = (x.store = s)`;

local val rw = srw_tac[] val fs = fsrw_tac[] val rfs = rev_full_simp_tac(srw_ss()) in
val phase3_lemma = prove(
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ phase3_subset t /\
      state_rel s1 x /\
      (x.pc = LENGTH xs) /\
      (x.instrs = xs ++ phase3 (LENGTH xs) b t ++ ys) /\
      res <> Rfail /\
      (res = Rbreak ==> LENGTH (xs ++ phase3 (LENGTH xs) b t) <= b) ==>
      ?x'.
        (sem_a x = sem_a x') /\
        state_rel s2 x' /\ OMIT (
        (x'.instrs = x.instrs) /\
        (case res of
         | Rfail => T
         | Rbreak => (x'.pc = b)
         | Rtimeout => (sem_a x' = (Rtimeout,x'))
         | Rval v => (x'.pc = LENGTH (xs ++ phase3 (LENGTH xs) b t))))``,
  REWRITE_TAC [state_rel_def,OMIT_def]
  \\ HO_MATCH_MP_TAC sem_t_ind \\ REPEAT STRIP_TAC \\ fs [phase3_subset_def]
  THEN1 (* Exp 1 *)
   (fs [phase3_def,sem_t_def] \\ rfs []
    \\ Cases_on `v = x'` \\ fs [] THEN1
     (fs [sem_e_def]
      \\ Cases_on `FLOOKUP s1.store x'` \\ fs [] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `x` \\ fs [store_var_def,state_component_equality]
      \\ fs [FLOOKUP_DEF,fmap_EXT,FAPPLY_FUPDATE_THM]
      \\ SRW_TAC [] [] \\ fs [EXTENSION] \\ METIS_TAC [])
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ Cases_on `FLOOKUP x.store.store x'` \\ fs [] \\ SRW_TAC [] []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ fs [inc_pc_def,DECIDE ``n + 1 < n + 2 + m:num``]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
           rich_listTheory.EL_LENGTH_APPEND
           |> Q.SPECL [`y::ys`,`xs ++ [x]`]
           |> SIMP_RULE (srw_ss()) []
           |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC]]
    \\ fs [sem_e_def,store_var_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,LET_DEF]
    \\ Q.EXISTS_TAC `(x with
         <|store :=
            x.store with store := x.store.store |+ (v,x'');
           pc := LENGTH xs + 1 + 1|>)`
    \\ fs [GSYM ADD_ASSOC])
  THEN1 (* Exp 2 *)
   (fs [phase3_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with store := store_var v i x.store))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 2 *)
   (fs [phase3_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ every_case_tac \\ fs [] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with store := store_var v (i'' + i') x.store))`
    \\ fs [inc_pc_def])
  THEN1 (* Break *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [phase3_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ imp_res_tac instr_lookup_lemma \\ fs [LET_DEF]
    \\ fs [do_jump_def]
    \\ `b > LENGTH xs` by DECIDE_TAC \\ fs []
    \\ Q.EXISTS_TAC `x with pc := b`
    \\ fs [] \\ fs [state_component_equality])
  THEN1 (* Seq *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [phase3_def,LET_DEF]
    \\ Cases_on `sem_t x.store t` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `phase3 (LENGTH xs + LENGTH (phase3 (LENGTH (xs:instr list)) b t)) b t'
          ++ ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (Cases_on `q` \\ fs [] \\ SRW_TAC [] [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.store = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x2`,`xs ++ phase3 (LENGTH xs) b t`,
         `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x3.store = s2`
    \\ Q.EXISTS_TAC `x3` \\ fs []
    \\ fs [ADD_ASSOC])
  THEN1 (* If *)
   (fs [phase3_def,sem_t_def]
    \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ rfs [] \\ POP_ASSUM (K ALL_TAC)
    \\ REVERSE (Cases_on `sem_e s1 (Var w)`) \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ SRW_TAC [] [] \\ fs [sem_e_break]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `gg = (LENGTH xs + 2 + LENGTH (phase3 0 0 t1) +
          LENGTH (phase3 0 0 t2))`
    THEN1 (* false case *)
     (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(inc_pc (x with store := r))`,
         `xs ++ [JmpIf (Reg w) (LENGTH (xs:instr list) + 2 + LENGTH (phase3 0 0 t1))]`,
         `[Jmp gg] ++ phase3 (LENGTH (xs:instr list) + 2 + LENGTH (phase3 0 0 t1))
            b t2 ++ ys`,`b`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (fs [inc_pc_def] \\ REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `x2.store = s2`
      \\ REVERSE (Cases_on `res`) \\ fs []
      \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
      \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
      \\ `LENGTH xs + 1 + LENGTH (phase3 0 0 t1) <
          LENGTH xs + 1 + LENGTH (phase3 (LENGTH xs + 1) b t1) + 1 +
          LENGTH (phase3 (LENGTH xs + 2 + LENGTH (phase3 0 0 t1)) b t2) +
          LENGTH ys /\
          (EL (LENGTH xs + 1 + LENGTH (phase3 0 0 t1))
           (xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (phase3 0 0 t1))] ++
            phase3 (LENGTH xs + 1) b t1 ++ [Jmp gg] ++
            phase3 (LENGTH xs + 2 + LENGTH (phase3 0 0 t1)) b t2 ++ ys) =
           Jmp gg)` by
      (ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
       \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
       \\ MATCH_MP_TAC EL_LEMMA
       \\ fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs [])
      \\ fs [do_jump_def]
      \\ UNABBREV_ALL_TAC
      \\ SRW_TAC [] []
      \\ TRY (`F` by DECIDE_TAC)
      \\ Q.EXISTS_TAC `(x2 with pc :=
           LENGTH xs + 2 + LENGTH (phase3 0 0 t1) + LENGTH (phase3 0 0 t2))`
      \\ fs [AC ADD_COMM ADD_ASSOC,ADD1] \\ DECIDE_TAC)
    (* true case *)
    \\ fs [do_jump_def,DECIDE ``n + 2 + m > n:num``]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [
         `(x with <|store := r; pc := LENGTH (xs:instr list) +
            2 + LENGTH (phase3 0 0 t1)|>)`,
         `xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (phase3 0 0 t1))] ++
          phase3 (LENGTH xs + 1) b t1 ++ [Jmp gg]`, `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``]
      \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.store = s2`
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `x2` \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``,ADD1]
    \\ Cases_on `res` \\ fs [])
  THEN1 (* For *)
   (fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `sem_t x.store (For (Num 1) (Num 1) t) = (res,s2)` MP_TAC
    \\ SIMP_TAC (srw_ss()) [sem_t_def_with_stop,sem_e_def]
    \\ SIMP_TAC std_ss [STOP_def]
    \\ Cases_on `sem_t x.store t` \\ fs [phase3_def,LET_DEF]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `[Jmp (LENGTH (xs:instr list))] ++ ys`,`(LENGTH (xs:instr list) + 1 +
             LENGTH (phase3 (LENGTH (xs:instr list)) 0 t))`]) \\ fs []
    \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.store = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ `x2.pc < LENGTH x2.instrs` by
      (fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs [] \\ DECIDE_TAC) \\ fs []
    \\ `(EL (LENGTH xs + LENGTH (phase3 0 0 t)) (xs ++
         phase3 (LENGTH xs) (LENGTH xs + 1 + LENGTH (phase3 0 0 t)) t ++
         [Jmp (LENGTH xs)] ++ ys) = Jmp (LENGTH xs))` by
     (`LENGTH (phase3 0 0 t) =
       LENGTH (phase3 (LENGTH (xs:instr list))
         (LENGTH (xs:instr list) + 1 + LENGTH (phase3 0 0 t)) t)` by
           (fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs [])
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
      \\ fs [EL_LENGTH_APPEND_LEMMA])
    \\ fs [do_jump_def,DECIDE ``~(n > n + k:num)``,LET_DEF]
    \\ Cases_on `x2.store.clock = 0` \\ fs [] THEN1
     (SRW_TAC [] [] \\ fs []
      \\ Q.EXISTS_TAC `x2` \\ fs []
      \\ SIMP_TAC std_ss [EQ_SYM_EQ] \\ fs []
      \\ ONCE_REWRITE_TAC [sem_a_def]
      \\ fs [do_jump_def,DECIDE ``~(n > n + k:num)``,LET_DEF])
    \\ Q.PAT_ASSUM `!x. bb` MP_TAC
    \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [dec_clock_def]
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.PAT_ASSUM `xxx <= b` MP_TAC
    \\ ONCE_REWRITE_TAC [LENGTH_phase3] \\ fs []))
end

val _ = save_thm("phase3_lemma",
  phase3_lemma |> REWRITE_RULE [state_rel_def]);

val phase3_thm = phase3_lemma
  |> REWRITE_RULE [state_rel_def,OMIT_def];

val phase3_correct = store_thm("phase3_correct",
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ phase3_subset t /\
      (x.store = s1) /\
      (x.pc = 0) /\
      (x.instrs = phase3 0 0 t) /\
      res <> Rfail /\ res <> Rbreak ==>
      ?res' x'.
        (sem_a x = (res', x')) /\
        (x'.store = s2) /\
        (case res of
         | Rval v => (res' = Rval 0)
         | _ => (res' = res))``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL phase3_thm
       |> Q.INST [`xs`|->`[]`,`ys`|->`[]`,`b`|->`0`])
  \\ fs [phase3_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `res` \\ fs [rich_listTheory.EL_LENGTH_APPEND]
  \\ SIMP_TAC std_ss [Once sem_a_def]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

(* We prove that phase3 preserves semantics if the source does not
   crash and if the syntax fits within the subset defined by
   phase3_subset. *)

val phase3_pres = store_thm("phase3_pres",
  ``!t. semantics t <> Crash /\ phase3_subset t ==>
        asm_semantics (phase3 0 0 t) = semantics t``,
  REPEAT STRIP_TAC \\ fs [semantics_thm]
  \\ REVERSE (SRW_TAC [] [])
  THEN1 METIS_TAC []
  THEN1
   (fs [asm_semantics_def]
    \\ REVERSE (sg `!c. ?s. sem_a (a_state (phase3 0 0 t) c) = (Rtimeout,s)`)
    THEN1 (fs [] \\ SRW_TAC [] []
           \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `c`) \\ fs [])
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `c`)
    \\ MP_TAC (Q.SPECL [`s_with_clock c`,`t`] phase3_correct) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPEC `a_state (phase3 0 0 t) c`)
    \\ fs [a_state_def] \\ REPEAT STRIP_TAC \\ fs [])
  \\ fs [asm_semantics_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b ==> ((if b then x else y) = x)``)
  \\ Q.EXISTS_TAC `c`
  \\ MP_TAC (Q.SPECL [`s_with_clock c`,`t`] phase3_correct) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `a_state (phase3 0 0 t) c`)
  \\ fs [a_state_def] \\ REPEAT STRIP_TAC \\ fs []);


(* === The end-to-end compiler === *)

val compile_def = Define `
  compile t = phase3 0 0 (phase2 (phase1 t))`;

(* Verification of the compile function *)

val phase2_subset_phase1 = prove(
  ``!t. phase2_subset (phase1 t)``,
  Induct \\ fs [phase1_def,phase2_subset_def,Loop_def]);

val phase3_subset_comp_exp = prove(
  ``!e n. phase3_subset (comp_exp e n)``,
  Induct \\ fs [phase3_subset_def,comp_exp_def]);

val phase3_subset_flatten_t = prove(
  ``!t n. phase2_subset t ==> phase3_subset (flatten_t t n)``,
  Induct \\ fs [phase2_subset_def,flatten_t_def,phase3_subset_def]
  \\ fs [phase3_subset_comp_exp]);

val phase3_subset_phase2_phase1 = prove(
  ``!t. phase3_subset (phase2 (phase1 t))``,
  fs [phase2_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC phase3_subset_flatten_t
  \\ fs [phase2_subset_phase1]);

(* The compile function produces code that has observable behaviour
   that is identical to the source program, if the course program does
   not Crash. *)

val compile_pres = store_thm("compile_pres",
  ``!t. semantics t <> Crash ==>
        (asm_semantics (compile t) = semantics t)``,
  fs [compile_def]
  \\ ONCE_REWRITE_TAC [GSYM phase1_pres]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC phase2_pres
  \\ fs [phase2_subset_phase1]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ MATCH_MP_TAC phase3_pres
  \\ fs [phase2_pres,phase2_subset_phase1,phase3_subset_phase2_phase1]);

(* The simple type checker (defined in forScript.sml) ensures that the
   source program cannot Crash. This leads to a cleaner top-level
   correctness theorem for compile. *)

val syntax_ok_def = Define `
  syntax_ok t = type_t F {} t`;

val compile_correct = store_thm("compile_correct",
  ``!t. syntax_ok t ==>
        (asm_semantics (compile t) = semantics t)``,
  METIS_TAC [type_soundness,syntax_ok_def,compile_pres]);

val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* Start re-verification of phase1 in relational big step semantics *)

val sem_e_reln_not = Q.prove(
  `∀s e res. sem_e_reln s e res ⇒ FST res ≠ Rbreak ∧ FST res ≠ Rtimeout`,
  ho_match_mp_tac sem_e_reln_ind>>rw[])

val semttac = simp[Once simple_sem_t_reln_cases,is_rval_def]
val semetac = simp[Once sem_e_reln_cases]
val sdtac = simp[Once simple_sem_t_div_cases]

val phase1_correct_reln = store_thm("phase1_correct_reln",
``∀s t res. simple_sem_t_reln s t res ⇒ simple_sem_t_reln s (phase1 t) res``,
  ho_match_mp_tac simple_sem_t_reln_strongind>>fs[phase1_def]>>rw[]>>
  TRY(semttac>>metis_tac[])
  >- metis_tac[simple_sem_t_reln_cases,sem_e_reln_cases]>>
  simp[Loop_def]>>semttac>>
  ntac 8 semetac>>
  metis_tac[simple_sem_t_reln_cases,is_rval_def,sem_e_reln_not,FST,sem_e_reln_cases,Loop_def])

val phase1_correct_div_lemma = Q.prove (
`∀s t'. (∃t. phase1 t = t' ∧ simple_sem_t_div s t) ⇒ simple_sem_t_div s t'`,
  ho_match_mp_tac simple_sem_t_div_coind>>rw[]>>
  Cases_on`t`>>fs[phase1_def,Loop_def,PULL_EXISTS]>>
  pop_assum mp_tac>> sdtac>>rw[]
  >- metis_tac[simple_sem_t_div_cases,sem_e_reln_cases,simple_sem_t_reln_cases,is_rval_def]>>
  TRY(metis_tac[phase1_correct_reln])
  >-
    (semetac>>DISJ1_TAC>>
    qexists_tac`If e0 (Seq t' (Exp e)) Break`>>fs[phase1_def]>>
    metis_tac[simple_sem_t_div_cases])
  >>
    semetac>>DISJ2_TAC>>
    ntac 2 semetac>>
    qexists_tac`n3`>>qexists_tac`s3`>>qexists_tac`For e0 e t'`>>
    CONJ_TAC>- metis_tac[phase1_correct_reln,simple_sem_t_reln_cases]>>
    fs[phase1_def,Loop_def])

val phase1_correct_div = store_thm("phase1_correct_div",
``∀s t. simple_sem_t_div s t ⇒ simple_sem_t_div s (phase1 t)``,
  metis_tac[phase1_correct_div_lemma])

Theorem phase1_pres_rel:
  ∀t. rel_semantics t ≠ Crash ⇒ rel_semantics (phase1 t) = rel_semantics t
Proof
  strip_tac>>fs[rel_semantics_def]>>
  metis_tac[phase1_correct_reln,simple_sem_t_reln_not_div,phase1_correct_div]
QED

(* End verification for relational semantics -- 43 lines *)

(* We now re-verify phase1 in the relational Pretty Big Step semantics (for terminating programs) *)

val pb_sem_t_reln_Exp = ``pb_sem_t_reln s1' (Trm (Exp e)) r3'``
  |> SIMP_CONV (srw_ss()) [Once pb_sem_t_reln_cases,abort_def];

val sem_e_reln_Num = store_thm("sem_e_reln_Num[simp]",
  ``sem_e_reln s (Num n) r1 <=> r1 = (Rval n,s)``,
  fs [Once sem_e_reln_cases]);

val pb_sem_t_reln_Forn2 = ``pb_sem_t_reln s (Forn 2 r3 n1 n1 t) (Ter r)``
  |> SIMP_CONV (srw_ss()) [Once pb_sem_t_reln_cases,abort_def];

val pb_sem_t_reln_Forn3 = ``pb_sem_t_reln s (Forn 3 r3 n1 n1 t) (Ter r)``
  |> SIMP_CONV (srw_ss()) [Once pb_sem_t_reln_cases,abort_def];

local
    val rw = srw_tac[] val fs = fsrw_tac[]
    val bp_step_tac = simp [Once pb_sem_t_reln_cases] \\ fs [];
    val bp_size_step_tac = simp [Once pb_sem_t_size_reln_cases] \\ fs [];
in
val pb_sem_t_reln_IMP_phase1 = Q.store_thm("pb_sem_t_reln_IMP_phase1",
  `!s t r.
     pb_sem_t_reln s (Trm t) (Ter r) ⇒
     pb_sem_t_reln s (Trm (phase1 t)) (Ter r)`,
  simp [Once pb_sem_t_size_reln_equiv,PULL_EXISTS]
  \\ completeInduct_on `n` \\ fs [PULL_FORALL]
  \\ Cases_on `t` \\ fs [phase1_def]
  \\ TRY (rw [] \\ fs [pb_sem_t_size_reln_equiv]
          \\ qexists_tac `n` \\ fs [] \\ NO_TAC)
  THEN1 (* Dec case *)
   (bp_size_step_tac \\ fs [] \\ rw []
    \\ fs [AND_IMP_INTRO] \\ res_tac \\ fs []
    \\ ntac 2 (bp_step_tac \\ fs [] \\ rw [])
    \\ rpt (fs [Once sem_e_reln_cases,is_rval_def]))
  THEN1 (* Seq case *)
   (bp_size_step_tac \\ fs [] \\ rw []
    \\ fs [AND_IMP_INTRO] \\ res_tac \\ fs []
    \\ fs [DECIDE ``0 < h' + 1n /\ h' < h + (h' + 1n)``]
    \\ bp_step_tac \\ rw [] \\ metis_tac [])
  THEN1 (* If case *)
   (bp_size_step_tac \\ fs [] \\ rw []
    \\ fs [AND_IMP_INTRO] \\ res_tac \\ fs []
    \\ bp_step_tac \\ rw [] \\ metis_tac [])
  (* the rest is For case *)
  \\ ntac 2 bp_size_step_tac \\ fs [] \\ rw []
  THEN1 (* For stops *)
   (rw [Loop_def]
    \\ ntac 4 (bp_step_tac \\ fs [] \\ rw [sem_e_reln_Num])
    \\ fs [pb_sem_t_reln_Forn2] \\ metis_tac [])
  THEN1 (* For runs the body *)
   (ntac 2 (pop_assum mp_tac)
    \\ bp_size_step_tac \\ fs [] \\ rw [Loop_def]
    \\ `!x. sem_e_reln s e0 x <=> (x = (Rval n',s'))` by
            metis_tac [sem_e_reln_determ]
    THEN1 (* Break in body *)
     (ntac 4 (bp_step_tac \\ fs [] \\ rw [sem_e_reln_Num])
      \\ qexists_tac `(Ter (Rbreak,s''))`
      \\ fs [abort_def,is_rval_def,pb_sem_t_reln_Forn2]
      \\ metis_tac [DECIDE ``n<n+1+1:num``])
    THEN1 (* For continues *)
     (ntac 4 (bp_step_tac \\ fs [] \\ rw [sem_e_reln_Num,is_rval_def])
      \\ fs [pb_sem_t_reln_Exp] \\ disj1_tac
      \\ qexists_tac `Ter r2` \\ fs [] \\ rw []
      THEN1
       (fs [AND_IMP_INTRO] \\ res_tac
        \\ metis_tac [DECIDE ``h' < h' + (h + 1 + 1) + 1n``])
      \\ fs [abort_def,is_rval_def,pb_sem_t_reln_Forn2]
      \\ imp_res_tac sem_e_reln_not \\ fs[pb_sem_t_reln_Forn3]
      \\ qpat_x_assum `pb_sem_t_size_reln h s'' _ (Ter r)` mp_tac
      \\ bp_size_step_tac \\ fs [] \\ reverse (rw [Loop_def])
      THEN1 (rpt disj2_tac \\ Cases_on `r` \\ fs [abort_def])
      \\ disj1_tac
      \\ fs [AND_IMP_INTRO] \\ res_tac
      \\ rpt (pop_assum mp_tac \\ match_mp_tac IMP_IMP \\ conj_tac THEN1 decide_tac)
      \\ rw [] \\ fs [phase1_def,Loop_def])
    \\ ntac 4 (bp_step_tac \\ fs [] \\ rw [sem_e_reln_Num])
    \\ disj1_tac \\ rename [‘abort T (Ter result)’] >> qexists_tac `Ter result`
    \\ Cases_on `result` \\ fs [is_rval_def,abort_def,pb_sem_t_reln_Forn2]
    \\ metis_tac [DECIDE ``n<n+1n+1``])
  THEN1 (* For eval of exp fails *)
   (rename [‘abort F (Ter result)’] >> Cases_on `result` \\
    fs [abort_def,Loop_def]
    \\ ntac 3 (bp_step_tac \\ fs [] \\ rw [sem_e_reln_Num])
    \\ disj1_tac >>
    rename [‘sem_e_reln s0 e0 (r,s)’] >>
    qexists_tac `Ter (r,s)` \\ fs []
    \\ fs [pb_sem_t_reln_Forn2,abort_def]
    \\ imp_res_tac sem_e_reln_not\\ fs []));
end

(* End verification in Pretty-Big-Step -- 81 lines
   Note: this verification does not cover divergence preservation. *)

(* for presentation purposes: *)

val phase1_abbrev = store_thm("phase1_abbrev",
  ``(phase1 (For g e t) = Loop (If g (Seq (phase1 t) (Exp e)) Break))/\
    (phase1 (Dec x t) = Seq (Exp (Assign x (Num 0))) (phase1 t))``,
  fs [phase1_def]);

val _ = export_theory ();
