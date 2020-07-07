open HolKernel Parse boolLib bossLib;

val _ = new_theory "for_nd_compile";

(*

This file proves correctness of a compiler for the FOR language
defined in for_ndScript.sml and for_nd_semScript.sml. The compiler
targets a simple assembly-like language. We prove that the compiler
preserves the top-level observable semantics.

The compiler consists of three phasees:
 - the first phase simplifies For loops and removes Dec
 - the second phase compiles expressions into very simple assignments
 - the third phase maps the FOR language into assmembly code

*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open for_ndTheory for_nd_semTheory listTheory arithmeticTheory;

val _ = temp_tight_equality ();

val ect = BasicProvers.EVERY_CASE_TAC;

val IMP_IMP = METIS_PROVE [] ``b /\ (b1 ==> b2) ==> ((b ==> b1) ==> b2)``


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

val sem_e_break = prove(
  ``!b1 s. ~(sem_e s b1 = (Rbreak,r)) /\ ~(sem_e s b1 = (Rtimeout,r))``,
  Induct \\ REPEAT STRIP_TAC
  \\ fs [sem_e_def,permute_pair_def,LET_DEF,oracle_get_def,
         unpermute_pair_def,getchar_def]
  \\ ect \\ fs [] \\ rfs [] \\ ect \\ fs [] \\ rfs []);

val sem_t_For_swap_body = prove(
  ``(!s. sem_t s t1 = sem_t s t2) ==>
    (sem_t s (For b1 b2 t1) = sem_t s (For b1 b2 t2))``,
  STRIP_TAC
  \\ completeInduct_on `s.clock`
  \\ rw [sem_t_def_with_stop,sem_e_def,Once sem_t_Loop]
  \\ ect \\ fs [PULL_FORALL,STOP_def]
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

val phase1_correct = store_thm("phase1_correct",
  ``!t s. sem_t s (phase1 t) = sem_t s t``,
  Induct \\ fs [phase1_def,sem_t_def_with_stop,GSYM sem_t_For,GSYM sem_t_Dec]
  \\ REPEAT STRIP_TAC \\ ect \\ fs [STOP_def]
  \\ MATCH_MP_TAC sem_t_For_swap_body \\ fs []);

val phase1_pres = store_thm("phase1_pres",
  ``!t. semantics (phase1 t) = semantics t``,
  REPEAT STRIP_TAC \\ fs [FUN_EQ_THM] \\ Cases_on `x'`
  \\ fs [semantics_def,phase1_correct]);


(* === PHASE 2 : compiles expressions into very simple assignments === *)

val comp_exp_def = Define `
  (comp_exp (Var v) s = Exp (Assign s (Var v))) /\
  (comp_exp (Num i) s = Exp (Assign s (Num i))) /\
  (comp_exp (Assign v e) s =
     (Seq (comp_exp e s) (Exp (Assign v (Var s))))) /\
  (comp_exp Getchar s = Exp (Assign s Getchar)) /\
  (comp_exp (Putchar x) s =
     Seq (comp_exp x s) (Exp (Putchar (Var s)))) /\
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
  (exp_max (Putchar e) = exp_max e) /\
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

val store_var_def = Define `
  store_var v x s = s with store := s.store |+ (v,x)`;

val sem_e_def = sem_e_def |> REWRITE_RULE [GSYM store_var_def]

val r_cases_eq = prove_case_eq_thm {
  case_def = for_nd_semTheory.r_case_def,
  nchotomy = for_nd_semTheory.r_nchotomy
};

val pair_cases_eq = Q.prove(
  ‘(pair_CASE p f = v) ⇔ ∃q r. p = (q,r) ∧ v = f q r’,
  Cases_on `p` >> simp[] >> metis_tac[]);
val rveq = rpt BasicProvers.VAR_EQ_TAC

val sem_e_possible_var_name = prove(
  ``!e s i r.
      (sem_e s e = (Rval i,r)) /\ exp_max e < STRLEN k ==>
      possible_var_name k s.store ==>
      possible_var_name k r.store``,
  Induct \\ fs [sem_e_def] \\ REPEAT STRIP_TAC \\ ect \\ fs []
  THEN1
   (fs [permute_pair_def]
    \\ Cases_on `oracle_get s.non_det_o` \\ fs [LET_DEF]
    \\ rename [‘oracle_get s.non_det_o = (b,bo)’]
    \\ Cases_on `b` >> fs [] (* 2 subgoals *)
    \\ fs[r_cases_eq, pair_cases_eq, unpermute_pair_def, exp_max_def,
          MAX_LESS] >> rveq >>
    rpt (first_x_assum
           (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac)) >>
    simp[])
  \\ SRW_TAC [] [] \\ fs [exp_max_def,MAX_LESS,getchar_def]
  \\ ect \\ fs [LET_DEF] \\ SRW_TAC [] [store_var_def] >>
  first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
  simp[] >>
  simp[possible_var_name_def] >>
  rpt strip_tac >> SRW_TAC [] [] >>
  fs []);

val comp_exp_correct = store_thm(
  "comp_exp_correct",
  “!e s t n res s1.
      sem_e s e = (res,s1) /\ res <> Rfail /\
      possible_var_name n s.store /\
      s.store SUBMAP t.store /\ (t.clock = s.clock) /\
      (s.non_det_o = K F) /\
      (FILTER ISL s.io_trace = FILTER ISL t.io_trace) /\
      (s.input = t.input) /\
      exp_max e < LENGTH n ==>
      ?t1. (sem_t t (comp_exp e n) = (res,t1)) /\
           s1.store SUBMAP t1.store /\ (t1.clock = s1.clock) /\
           (s1.non_det_o = K F) /\
           (FILTER ISL s1.io_trace = FILTER ISL t1.io_trace) /\
           (s1.input = t1.input) /\
           (!v. (res = Rval v) ==> FLOOKUP t1.store n = SOME v) /\
           possible_var_name n s1.store /\
           (!k v. possible_var_name k s.store /\
                  exp_max e < LENGTH k /\ LENGTH k < LENGTH n /\
                  FLOOKUP t.store k = SOME v ==>
                  FLOOKUP t1.store k = SOME v)”,
  Induct \\ fs [sem_e_def,comp_exp_def,sem_t_def,store_var_def]
  \\ REPEAT STRIP_TAC
  THEN1
   (Cases_on `FLOOKUP s'.store s` \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC FLOOKUP_SUBMAP \\ fs []
    \\ IMP_RES_TAC possible_var_name_IMP_SUBMAP \\ fs []
    \\ fs [FLOOKUP_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [])
  \\ TRY (IMP_RES_TAC possible_var_name_IMP_SUBMAP \\ fs []
          \\ fs [FLOOKUP_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
          \\ SRW_TAC [] [] \\ fs [] \\ NO_TAC)
  THEN1
   (fs [permute_pair_def,oracle_get_def,LET_DEF,unpermute_pair_def]
    \\ `(s with non_det_o := K F) = s` by
          (fs [state_component_equality]) \\ fs [] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `sem_e (s with io_trace := s.io_trace ++ [INR F]) e` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ Cases_on `sem_e r e'` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ fs [exp_max_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s with io_trace := s.io_trace ++ [INR F]`,`t`,`n`])
    \\ `exp_max e < STRLEN n /\
        exp_max e' < STRLEN n /\
        exp_max e' < STRLEN (STRCAT n "'")` by
            (fs [MAX_LESS]  \\ DECIDE_TAC)
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs [FILTER_APPEND_DISTRIB] \\ rfs []
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`STRCAT n "'"`])
    \\ `possible_var_name (STRCAT n "'") r.store` by
     (fs [possible_var_name_def]
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n'`)
      \\ FULL_SIMP_TAC std_ss [rich_listTheory.REPLICATE,
           APPEND,GSYM APPEND_ASSOC])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.store SUBMAP t2.store`
    \\ `FLOOKUP t2.store n = SOME i` by (FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [sem_e_def,AC integerTheory.INT_ADD_ASSOC integerTheory.INT_ADD_COMM, FILTER_APPEND_DISTRIB]
    \\ `possible_var_name n r'.store` by
          IMP_RES_TAC sem_e_possible_var_name
    \\ REPEAT STRIP_TAC
    \\ TRY (MATCH_MP_TAC possible_var_name_IMP_SUBMAP \\ fs [] \\ NO_TAC)
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ Cases_on `k = n` \\ fs []
    \\ `v = t1.store ' k` by (SRW_TAC [] [] \\ METIS_TAC [MAX_LESS])
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [MAX_LESS] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC sem_e_possible_var_name
    \\ fs [Q.prove (`!y. (s with io_trace := y).store = s.store`, rw [state_component_equality])]
    \\ decide_tac)
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s'`)
    \\ Cases_on `sem_e s' e` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ SRW_TAC [] [] \\ fs [exp_max_def,MAX_LESS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t`,`n`])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ REPEAT STRIP_TAC
    \\ fs [SUBMAP_DEF,FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
    \\ REPEAT STRIP_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ fs [possible_var_name_def]
    \\ REPEAT STRIP_TAC
    \\ SRW_TAC [] [] \\ fs [] \\ DECIDE_TAC)
  THEN1
   (fs [] \\ Cases_on `getchar t.input` \\ fs [LET_DEF]
    \\ SRW_TAC [] [] \\ fs []
    \\ IMP_RES_TAC possible_var_name_IMP_SUBMAP \\ fs []
    \\ fs [FLOOKUP_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [] \\ fs [FILTER_APPEND_DISTRIB])
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
    \\ Cases_on `sem_e s e` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ SRW_TAC [] [] \\ fs [exp_max_def,MAX_LESS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t`,`n`])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ REPEAT STRIP_TAC
    \\ fs [SUBMAP_DEF,FAPPLY_FUPDATE_THM,FLOOKUP_DEF, FILTER_APPEND_DISTRIB]));

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

val flatten_t_correct = prove(
  ``!s e t n res s1.
      sem_t s e = (res,s1) /\ res <> Rfail /\ phase2_subset e /\
      possible_var_name n s.store /\
      s.store SUBMAP t.store /\ (t.clock = s.clock) /\
      (s.non_det_o = K F) /\
      (FILTER ISL s.io_trace = FILTER ISL t.io_trace) /\
      (s.input = t.input) /\
      t_max e < LENGTH n ==>
      ?t1. (sem_t t (flatten_t e n) = (res,t1)) /\
           s1.store SUBMAP t1.store /\ (t1.clock = s1.clock) /\
           (s1.non_det_o = K F) /\
           (FILTER ISL s1.io_trace = FILTER ISL t1.io_trace) /\
           (s1.input = t1.input) /\
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
    \\ Cases_on `i = 0` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1:state`,`n`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [] \\ REPEAT STRIP_TAC
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
  |> Q.SPECL [`s`,`t`,`s3`,`"temp" ++ REPLICATE (t_max t - 3) #"'"`]
  |> DISCH ``s.store = FEMPTY``
  |> DISCH ``s1.store = FEMPTY``
  |> SIMP_RULE (srw_ss()) [GSYM phase2_def,Once possible_var_name_def,
       rich_listTheory.LENGTH_REPLICATE,DECIDE ``n < 4 + (n - 3:num)``,
       PULL_FORALL] |> GEN_ALL;

val pair_eq = prove(
  ``(x = (y1,y2)) <=> (FST x = y1) /\ (SND x = y2)``,
  Cases_on `x` \\ fs [] \\ METIS_TAC []);

val s_with_clock_def = Define `
  s_with_clock c input = <| store := FEMPTY; clock := c;
                            input := input ; io_trace := [];
                            non_det_o := K F |>`;

val lemma = prove(
  ``((if b then x1 else x2) <> x2) <=> (x1 <> x2) /\ b``,
  Cases_on `b` \\ fs [])

(* We prove that phase 2 preserves semantics: any behaviour that the
   generated code has must also be behaviour of the input program, if
   the source semantics does not contain Crash (implied by successful
   type check) and if the syntax of the compiler program fits with
   phase2_subset (i.e. syntax produced by phase1) *)

val phase2_pres = store_thm("phase2_pres",
  ``!t input. ~(Crash IN semantics t input) /\ phase2_subset t ==>
              semantics (phase2 t) input SUBSET semantics t input``,
  REPEAT STRIP_TAC \\ fs [semantics_def,IN_DEF,SUBSET_DEF]
  \\ Cases \\ fs [semantics_def]
  \\ TRY
   (SRW_TAC [] []
    \\ MP_TAC (phase2_correct |> Q.SPECL [`t`,`init_st c nd input`,
         `s_with_clock c input`,`s_with_clock c input`]) \\ fs []
    \\ Cases_on `sem_t (s_with_clock c input) t` \\ fs []
    \\ fs [AND_IMP_INTRO]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [s_with_clock_def,init_st_def] \\ METIS_TAC [])
    \\ TRY (fs [s_with_clock_def,init_st_def] \\ METIS_TAC [])
    \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`c`,`K F`] \\ fs []
    \\ fs [s_with_clock_def,init_st_def]
    \\ SRW_TAC [] [] \\ NO_TAC)
  \\ REPEAT STRIP_TAC
  \\ fs [semantics_def] \\ Q.EXISTS_TAC `K F` \\ fs [] \\ REPEAT STRIP_TAC
  THEN1
   (POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (MP_TAC o Q.SPEC `c`) \\ REPEAT STRIP_TAC
    \\ MP_TAC (phase2_correct |> Q.SPECL [`t`,`init_st c nd input`,
         `s_with_clock c input`,`s_with_clock c input`]) \\ fs []
    \\ Cases_on `sem_t (s_with_clock c input) t` \\ fs []
    \\ fs [AND_IMP_INTRO]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [s_with_clock_def,init_st_def] \\ METIS_TAC [])
    \\ STRIP_TAC \\ fs [s_with_clock_def,init_st_def])
  \\ `!c. FILTER ISL (SND (sem_t (init_st c (K F) input) t)).io_trace =
          FILTER ISL (SND (sem_t (init_st c nd input) (phase2 t))).io_trace` by (
      rw []
      \\ first_x_assum (MP_TAC o Q.SPEC `c`) \\ REPEAT STRIP_TAC
      \\ MP_TAC (phase2_correct |> Q.SPECL [`t`,`init_st c nd input`,
           `s_with_clock c input`,`s_with_clock c input`]) \\ fs []
      \\ Cases_on `sem_t (s_with_clock c input) t` \\ fs []
      \\ fs [AND_IMP_INTRO]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (fs [s_with_clock_def,init_st_def] \\ METIS_TAC [])
      \\ STRIP_TAC \\ fs [s_with_clock_def,init_st_def])
  \\ rw []);


(* === PHASE 3 : maps the FOR language into assmembly code === *)

(* We define the tagert deterministic assembly language *)

val _ = Datatype `
reg = Reg string`

val _ = Datatype `
instr =
    Add reg reg reg
  | Mov reg reg
  | Int reg int
  | Read reg
  | Write reg
  | Jmp num
  | JmpIf reg num`;

val _ = Datatype `
state_a = <| state : state; pc : num; instrs : instr list |>`;

val do_jump_def = Define `
do_jump s n =
  if n > s.pc then
    (Rval 0, s with pc := n)
  else if s.state.clock = 0 then
    (Rtimeout, s)
  else
    let st' = s.state with clock := s.state.clock - 1 in
      (Rval 0, s with <| state := st'; pc := n |>)`;

val inc_pc_def = Define `
inc_pc s = s with pc := s.pc + 1`;

val sem_a_def = tDefine "sem_a" `
sem_a s =
  if s.pc < LENGTH s.instrs then
    case EL s.pc s.instrs of
       | Int (Reg r) i =>
           let (r,st) = sem_e s.state (Assign r (Num i)) in
           let s' = s with state := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Add (Reg r) (Reg r1) (Reg r2) =>
           let (r,st) = sem_e s.state (Assign r (Add (Var r1) (Var r2))) in
           let s' = s with state := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Mov (Reg r) (Reg r1) =>
           let (r,st) = sem_e s.state (Assign r (Var r1)) in
           let s' = s with state := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Read (Reg r) =>
           let (r,st) = sem_e s.state (Assign r Getchar) in
           let s' = s with state := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Write (Reg r) =>
           let (r,st) = sem_e s.state (Putchar (Var r)) in
           let s' = s with state := st in
             (case r of
                | Rval _ => sem_a (inc_pc s')
                | _ => (r, s'))
       | Jmp n' =>
           (case do_jump s n' of
               | (Rval _, s') => sem_a s'
               | r => r)
       | JmpIf (Reg r) n' =>
           let (r,st) = sem_e s.state (Var r) in
           let s' = s with state := st in
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
       (\s. (s.state.clock,LENGTH s.instrs - s.pc))`
   \\ fs [inc_pc_def,do_jump_def,LET_DEF]
   \\ REPEAT STRIP_TAC
   \\ ect \\ fs []
   \\ SRW_TAC [] [] \\ fs []
   \\ IMP_RES_TAC sem_e_clock
   \\ IMP_RES_TAC (GSYM sem_e_clock)
   \\ TRY DECIDE_TAC);

val a_state_def = Define `
  a_state code clock input =
    <| state := s_with_clock clock input; pc := 0; instrs := code |>`;

val asm_semantics_def = Define `
(asm_semantics code input (Terminate io_trace) =
  (* Terminate when there is a clock and some non-determinism oracle
     that gives a value result *)
  ?c i s.
    sem_a (a_state code c input) = (Rval i, s) /\
    FILTER ISL s.state.io_trace = io_trace) /\
(asm_semantics code input Crash =
  (* Crash when there is a clock that gives a non-value, non-timeout
     result *)
  ?c r s.
    sem_a (a_state code c input) = (r, s) /\
    (r = Rbreak \/ r = Rfail)) /\
(asm_semantics code input (Diverge io_trace) <=>
  (!c. ?s. sem_a (a_state code c input) = (Rtimeout, s)) ∧
    lprefix_lub {fromList (FILTER ISL (SND (sem_a (a_state code c input))).state.io_trace) | c | T} io_trace)`;

(* Definition of phase3 *)

val phase3_aux_def = Define `
  (phase3_aux n (Dec v t) b = []) /\
  (phase3_aux n (Exp e) b =
     case e of
     | Assign v (Var x) =>
         if x = v then [] else [Mov (Reg v) (Reg x)]
     | Assign v (Add (Var v1) (Var v2)) => [Add (Reg v) (Reg v1) (Reg v2)]
     | Assign v (Num i) => [Int (Reg v) i]
     | Assign v Getchar => [Read (Reg v)]
     | Putchar (Var v) => [Write (Reg v)]
     | _ => []) /\
  (phase3_aux n Break b = [Jmp b]) /\
  (phase3_aux n (Seq t1 t2) b =
     let c1 = phase3_aux n t1 b in
     let c2 = phase3_aux (n + LENGTH c1) t2 b in
       c1 ++ c2) /\
  (phase3_aux n (If e t1 t2) b =
     let c1 = phase3_aux (n + 1) t1 b in
     let c2 = phase3_aux (n + 2 + LENGTH c1) t2 b in
       [JmpIf (case e of Var v => Reg v | _ => Reg "")
          (n + 2 + LENGTH c1)] ++ c1 ++
       [Jmp (n + 2 + LENGTH c1 + LENGTH c2)] ++ c2) /\
  (phase3_aux n (For e1 e2 t) b =
     let c1 = phase3_aux n t 0 in
     let c2 = phase3_aux n t (n + 1 + LENGTH c1) in
       c2 ++ [Jmp n])`

val phase3_def = Define `
  phase3 t = phase3_aux 0 t 0`;

(* Verification of phase3 *)

val LENGTH_phase3_aux = prove(
  ``!t n b. LENGTH (phase3_aux n t b) = LENGTH (phase3_aux 0 t 0)``,
  Induct \\ fs [phase3_aux_def,LET_DEF]);

val phase3_subset_def = Define `
  (phase3_subset (Dec v t) = F) /\
  (phase3_subset (Exp e) <=>
     (?v. e = Assign v (Getchar)) \/
     (?v. e = Putchar (Var v)) \/
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
  state_rel s x = (x.state = s)`;

local val fs = fsrw_tac[] val rfs = rev_full_simp_tac(srw_ss()) in
val phase3_aux_thm = store_thm("phase3_aux_thm",
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ phase3_subset t /\
      state_rel s1 x /\
      (x.pc = LENGTH xs) /\
      (x.instrs = xs ++ phase3_aux (LENGTH xs) t b ++ ys) /\
      res <> Rfail /\
      (res = Rbreak ==> (LENGTH (xs ++ phase3_aux (LENGTH xs) t b) <= b)) ==>
      ?x'.
        (sem_a x = sem_a x') /\
        state_rel s2 x' /\
        (x'.instrs = x.instrs) /\
        (case res of
         | Rfail => T
         | Rbreak => (x'.pc = b)
         | Rtimeout => (sem_a x' = (Rtimeout,x'))
         | Rval v => (x'.pc = LENGTH (xs ++ phase3_aux (LENGTH xs) t b)))``,
  REWRITE_TAC [state_rel_def]
  \\ HO_MATCH_MP_TAC sem_t_ind \\ REPEAT STRIP_TAC \\ fs [phase3_subset_def]
  THEN1 (* Exp 1 *)
   (fs [phase3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def,LET_DEF] \\ SRW_TAC [] []
    \\ Cases_on `getchar x.state.input` \\ fs []
    \\ fs [sem_e_def,LET_DEF] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc
       (x with
        state :=
          store_var v q
            (x.state with
             <|io_trace := x.state.io_trace ++ [INL (Itag q)];
               input := r|>)))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 2 *)
   (fs [phase3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def,LET_DEF]
    \\ Cases_on `FLOOKUP s1.store v` \\ fs []
    \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc
       (x with
        state :=
          x.state with io_trace := x.state.io_trace ++ [INL (Otag x')]))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 3 *)
   (fs [phase3_aux_def,sem_t_def] \\ rfs []
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
    \\ fs [sem_e_def,LET_DEF]
    \\ Cases_on `FLOOKUP s1.store x'` \\ fs []
    \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with state := store_var v x'' x.state))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 4 *)
   (fs [phase3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with state := store_var v i x.state))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 5 *)
   (fs [phase3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ ect \\ fs [] \\ SRW_TAC [] []
    \\ fs [permute_pair_def,oracle_get_def,LET_DEF]
    \\ Cases_on `x.state.non_det_o 0` \\ fs [sem_e_def]
    \\ Cases_on `FLOOKUP x.state.store y` \\ fs []
    \\ Cases_on `FLOOKUP x.state.store x'` \\ fs [unpermute_pair_def]
    \\ Q.EXISTS_TAC `(inc_pc (x with state := store_var v i r))` \\ fs []
    \\ SRW_TAC [] [inc_pc_def])
  THEN1 (* Break *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [phase3_aux_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ imp_res_tac instr_lookup_lemma \\ fs [LET_DEF]
    \\ fs [do_jump_def]
    \\ `b > LENGTH xs` by DECIDE_TAC \\ fs []
    \\ Q.EXISTS_TAC `x with pc := b`
    \\ fs [] \\ fs [state_component_equality])
  THEN1 (* Seq *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [phase3_aux_def,LET_DEF]
    \\ Cases_on `sem_t x.state t` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `phase3_aux (LENGTH xs + LENGTH (phase3_aux (LENGTH (xs:instr list)) t b)) t' b
          ++ ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (Cases_on `q` \\ fs [] \\ SRW_TAC [] [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x2`,`xs ++ phase3_aux (LENGTH xs) t b`,
         `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x3.state = s2`
    \\ Q.EXISTS_TAC `x3` \\ fs []
    \\ fs [ADD_ASSOC])
  THEN1 (* If *)
   (Q.MATCH_ASSUM_RENAME_TAC `sem_t s1 (If e t1 t2) = (res,s2)`
    \\ fs [phase3_aux_def,sem_t_def]
    \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ rfs [] \\ POP_ASSUM (K ALL_TAC)
    \\ REVERSE (Cases_on `sem_e s1 (Var w)`) \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ SRW_TAC [] [] \\ fs [sem_e_break]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `gg = (LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0) +
          LENGTH (phase3_aux 0 t2 0))`
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    THEN1 (* false case *)
     (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(inc_pc (x with state := r))`,
         `xs ++ [JmpIf (Reg w) (LENGTH (xs:instr list) + 2 +
                   LENGTH (phase3_aux 0 t1 0))]`,
         `[Jmp gg] ++ phase3_aux (LENGTH (xs:instr list) + 2 +
                   LENGTH (phase3_aux 0 t1 0))
            t2 b ++ ys`,`b`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (fs [inc_pc_def] \\ REPEAT STRIP_TAC \\ fs []
             \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
             \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = s2`
      \\ REVERSE (Cases_on `res`) \\ fs []
      \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
      \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
      \\ `LENGTH xs + 1 + LENGTH (phase3_aux 0 t1 0) <
          LENGTH xs + 1 + LENGTH (phase3_aux (LENGTH xs + 1) t1 b) + 1 +
          LENGTH (phase3_aux (LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0)) t2 b) +
          LENGTH ys /\
          (EL (LENGTH xs + 1 + LENGTH (phase3_aux 0 t1 0))
           (xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0))] ++
            phase3_aux (LENGTH xs + 1) t1 b ++ [Jmp gg] ++
            phase3_aux (LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0)) t2 b ++ ys) =
           Jmp gg)` by
      (ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
       \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
       \\ MATCH_MP_TAC EL_LEMMA
       \\ fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs [])
      \\ fs [do_jump_def]
      \\ UNABBREV_ALL_TAC
      \\ SRW_TAC [] []
      \\ TRY (`F` by DECIDE_TAC)
      \\ Q.EXISTS_TAC `(x2 with pc :=
           LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0) + LENGTH (phase3_aux 0 t2 0))`
      \\ fs [AC ADD_COMM ADD_ASSOC,ADD1] \\ DECIDE_TAC)
    (* true case *)
    \\ fs [do_jump_def,DECIDE ``n + 2 + m > n:num``]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [
         `(x with <|state := r; pc := LENGTH (xs:instr list) +
            2 + LENGTH (phase3_aux 0 t1 0)|>)`,
         `xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (phase3_aux 0 t1 0))] ++
          phase3_aux (LENGTH xs + 1) t1 b ++ [Jmp gg]`, `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``]
      \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = s2`
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `x2` \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``,ADD1]
    \\ Cases_on `res` \\ fs [])
  THEN1 (* For *)
   (fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `sem_t x.state (For (Num 1) (Num 1) t) = (res,s2)` MP_TAC
    \\ SIMP_TAC (srw_ss()) [sem_t_def_with_stop,sem_e_def]
    \\ SIMP_TAC std_ss [STOP_def]
    \\ Cases_on `sem_t x.state t` \\ fs [phase3_aux_def,LET_DEF]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `[Jmp (LENGTH (xs:instr list))] ++ ys`,`(LENGTH (xs:instr list) + 1 +
             LENGTH (phase3_aux (LENGTH (xs:instr list)) t 0))`]) \\ fs []
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ `x2.pc < LENGTH x2.instrs` by
      (fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs [] \\ DECIDE_TAC) \\ fs []
    \\ `(EL (LENGTH xs + LENGTH (phase3_aux 0 t 0)) (xs ++
         phase3_aux (LENGTH xs) t (LENGTH xs + 1 + LENGTH (phase3_aux 0 t 0)) ++
         [Jmp (LENGTH xs)] ++ ys) = Jmp (LENGTH xs))` by
     (`LENGTH (phase3_aux 0 t 0) =
       LENGTH (phase3_aux (LENGTH (xs:instr list)) t
         (LENGTH (xs:instr list) + 1 + LENGTH (phase3_aux 0 t 0)))` by
           (fs [] \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs [])
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
      \\ fs [EL_LENGTH_APPEND_LEMMA])
    \\ fs [do_jump_def,DECIDE ``~(n > n + k:num)``,LET_DEF]
    \\ Cases_on `x2.state.clock = 0` \\ fs [] THEN1
     (SRW_TAC [] [] \\ fs []
      \\ Q.EXISTS_TAC `x2` \\ fs []
      \\ SIMP_TAC std_ss [EQ_SYM_EQ] \\ fs []
      \\ ONCE_REWRITE_TAC [sem_a_def]
      \\ fs [do_jump_def,DECIDE ``~(n > n + k:num)``,LET_DEF])
    \\ Q.PAT_ASSUM `!x. bb` MP_TAC
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [dec_clock_def]
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.PAT_ASSUM `xxx <= b` MP_TAC
    \\ ONCE_REWRITE_TAC [LENGTH_phase3_aux] \\ fs []))
  |> REWRITE_RULE [state_rel_def];
end

val phase3_correct = store_thm("phase3_correct",
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ phase3_subset t /\
      (x.state = s1) /\
      (x.pc = 0) /\
      (x.instrs = phase3 t) /\
      res <> Rfail /\ res <> Rbreak ==>
      ?res' x'.
        (sem_a x = (res', x')) /\
        (x'.state = s2) /\
        (case res of
         | Rval v => (res' = Rval 0)
         | _ => (res' = res))``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL phase3_aux_thm
       |> Q.INST [`xs`|->`[]`,`ys`|->`[]`,`b`|->`0`])
  \\ fs [phase3_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `res` \\ fs [rich_listTheory.EL_LENGTH_APPEND]
  \\ SIMP_TAC std_ss [Once sem_a_def]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

(* We prove that phase3 preserves semantics if the source does not
   contain Crash and if the syntax fits within the subset defined by
   phase3_subset. *)

val EVERY_IMP_FILTER = prove(
  ``!xs. EVERY P xs ==> FILTER P xs = xs``,
  Induct \\ fs []);

val phase3_pres = store_thm("phase3_pres",
  ``!t input. ~(Crash IN semantics t input) /\ phase3_subset t ==>
              asm_semantics (phase3 t) input SUBSET semantics t input``,
  REPEAT STRIP_TAC \\ fs [semantics_def,IN_DEF,SUBSET_DEF]
  \\ Cases \\ fs [semantics_def,asm_semantics_def]
  \\ TRY
   (SRW_TAC [] []
    \\ MP_TAC (phase3_correct |> Q.SPECL [`s_with_clock c input`,`t`])
    \\ Cases_on `sem_t (s_with_clock c input) t` \\ fs []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `(a_state (phase3 t) c input)`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [a_state_def,init_st_def]
           \\ fs [s_with_clock_def] \\ METIS_TAC [])
    \\ TRY (fs [a_state_def,s_with_clock_def,init_st_def] \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] []
    \\ fs [semantics_def]
    \\ fs [s_with_clock_def,init_st_def,a_state_def]
    \\ Q.LIST_EXISTS_TAC [`c`,`K F`] \\ fs []
    \\ match_mp_tac EVERY_IMP_FILTER
    \\ fs [] \\ NO_TAC)
  \\ REPEAT STRIP_TAC
  \\ fs [semantics_def] \\ Q.EXISTS_TAC `K F` \\ fs [] \\ REPEAT STRIP_TAC
  THEN1
   (POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (MP_TAC o Q.SPEC `c`) \\ REPEAT STRIP_TAC
    \\ MP_TAC (phase3_correct |> Q.SPECL [`s_with_clock c input`,`t`])
    \\ Cases_on `sem_t (s_with_clock c input) t` \\ fs []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `(a_state (phase3 t) c input)`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [a_state_def,init_st_def]
           \\ fs [s_with_clock_def] \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] []
    \\ fs [s_with_clock_def,init_st_def,a_state_def])
  \\ RES_TAC
  \\ sg `!c. FILTER ISL (SND (sem_t (init_st c (K F) input) t)).io_trace =
          FILTER ISL (SND (sem_a (a_state (phase3 t) c
              input))).state.io_trace` \\ fs []
  \\ rw [] \\ first_x_assum (qspec_then `c` mp_tac) \\ rw []
  \\ qspecl_then [`(init_st c (K F) input)`,`t`] mp_tac phase3_correct
  \\ Cases_on `sem_t (init_st c (K F) input) t` \\ fs []
  \\ rw []
  \\ pop_assum (qspec_then `(a_state (phase3 t) c input)` mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (fs [a_state_def,s_with_clock_def,init_st_def]
    \\ fs [METIS_PROVE [] ``~b\/c <=> (b==>c)``] \\ res_tac \\ fs [])
  \\ Cases_on `q` \\ fs []);


(* === The end-to-end compiler === *)

val compile_def = Define `
  compile t = phase3 (phase2 (phase1 t))`;

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

(* Any observable behaviour of the compiled code is also observable
   behaviour of the source code, if Crash is not an observable
   behaviour of the course program. *)

val compile_pres = store_thm("compile_pres",
  ``!t input. ~(Crash IN semantics t input) ==>
        asm_semantics (compile t) input SUBSET semantics t input``,
  fs [compile_def]
  \\ ONCE_REWRITE_TAC [GSYM phase1_pres]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SUBSET_TRANS
  \\ Q.EXISTS_TAC `semantics (phase2 (phase1 t)) input`
  \\ REPEAT STRIP_TAC
  THEN1
   (MATCH_MP_TAC phase3_pres
    \\ fs [phase3_subset_phase2_phase1]
    \\ IMP_RES_TAC phase2_pres
    \\ fs [phase2_subset_phase1,SUBSET_DEF]
    \\ METIS_TAC [])
  \\ MATCH_MP_TAC phase2_pres \\ fs [phase2_subset_phase1]);

(* The simple type checker (defined in for_nd_semScript.sml) ensures
   that the source program cannot Crash. This leads to a cleaner
   top-level correctness theorem for compile. *)

val syntax_ok_def = Define `
  syntax_ok t = type_t F {} t`;

val compile_correct = store_thm("compile_correct",
  ``!t inp. syntax_ok t ==>
            asm_semantics (compile t) inp SUBSET semantics t inp``,
  rpt strip_tac \\ match_mp_tac compile_pres \\ fs [syntax_ok_def]
  \\ imp_res_tac type_soundness
  \\ fs [semantics_def,IN_DEF,for_nd_semTheory.semantics_with_nd_def]);

val _ = export_theory ();
