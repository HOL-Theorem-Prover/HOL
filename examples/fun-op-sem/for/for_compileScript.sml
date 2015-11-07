open HolKernel Parse boolLib bossLib;

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
open lcsymtacs forTheory listTheory arithmeticTheory;

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
  \\ fs [sem_e_def] \\ ect
  \\ fs [] \\ rfs []);

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
  fs [semantics_def,phase1_correct]);


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
  Induct \\ fs [sem_e_def] \\ REPEAT STRIP_TAC \\ ect \\ fs []
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPEC `r'`)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
    \\ fs [exp_max_def,MAX_LESS])
  \\ SRW_TAC [] [] \\ fs [exp_max_def,MAX_LESS]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s'`) \\ fs []
  \\ fs [store_var_def,possible_var_name_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ fs [] \\ DECIDE_TAC);

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
   (Cases_on `sem_e s e` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ Cases_on `sem_e r e'` \\ Cases_on `q` \\ fs [sem_e_break]
    \\ fs [exp_max_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s`,`t`,`n`])
    \\ `exp_max e < STRLEN n /\
        exp_max e' < STRLEN n /\
        exp_max e' < STRLEN (STRCAT n "'")` by
            (fs [MAX_LESS]  \\ DECIDE_TAC)
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`STRCAT n "'"`])
    \\ `possible_var_name (STRCAT n "'") r.store` by ALL_TAC THEN1
     (fs [possible_var_name_def]
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n'`)
      \\ FULL_SIMP_TAC std_ss [rich_listTheory.REPLICATE,
           APPEND,GSYM APPEND_ASSOC])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.store SUBMAP t2.store`
    \\ `FLOOKUP t2.store n = SOME i` by (FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ fs [] \\ SRW_TAC [] []
    \\ `possible_var_name n r'.store` by
          IMP_RES_TAC sem_e_possible_var_name
    THEN1 (MATCH_MP_TAC possible_var_name_IMP_SUBMAP \\ fs [])
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ Cases_on `k = n` \\ fs []
    \\ `v = t1.store ' k` by (SRW_TAC [] [] \\ METIS_TAC [MAX_LESS])
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [MAX_LESS]
    \\ REVERSE (REPEAT STRIP_TAC) THEN1 DECIDE_TAC
    \\ IMP_RES_TAC sem_e_possible_var_name)
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
    \\ SRW_TAC [] [] \\ fs [] \\ DECIDE_TAC));

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
  \\ ect \\ SRW_TAC [] [] \\ fs [store_var_def] \\ METIS_TAC []) |> GSYM;

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
   \\ ect \\ fs []
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
    \\ ect \\ fs [] \\ SRW_TAC [] []
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
           Jmp gg)` by ALL_TAC THEN1
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
    \\ REVERSE (`!c. ?s. sem_a (a_state (phase3 0 0 t) c) = (Rtimeout,s)` by ALL_TAC)
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
(* We now re-verify phase1 in the relational big step semantics *)

val simple_sem_t_reln_Dec = Q.prove(
  `simple_sem_t_reln s (Exp (Assign v (Num 0))) (Rval 0,s with store := s.store |+ (v,0))`,
  simp[Once simple_sem_t_reln_cases]>>
  ntac 2 (simp[Once sem_e_reln_cases]))

val sem_e_reln_not_break = Q.prove(
  `∀s e res. sem_e_reln s e res ⇒
  FST res ≠ Rbreak`,
  ho_match_mp_tac sem_e_reln_ind>>rw[])

val semttac = simp[Once simple_sem_t_reln_cases,is_rval_def]
val semetac = simp[Once sem_e_reln_cases]

val simple_sem_t_reln_Loop1 = Q.prove(
  `∀s t res.
  simple_sem_t_reln s t res ⇒
  ∀e1 e2 t'.
  t = (For e1 e2 t') ⇒
  simple_sem_t_reln s (Loop (If e1 (Seq t' (Exp e2)) Break)) res`,
  ho_match_mp_tac simple_sem_t_reln_strongind>>fs[Loop_def]>>rw[]>>
  semttac>>simp[is_rval_def]
  >-
    (ntac 2 DISJ2_TAC>>
    semttac>>
    simp[Once sem_e_reln_cases,Once simple_sem_t_reln_cases])
  >-
    (ntac 8 semetac>>
    ntac 4 DISJ2_TAC>>
    semttac>>
    imp_res_tac sem_e_reln_not_break>>
    fs[])
  >-
    (ntac 8 semetac>>simp[is_rval_def]>>
    DISJ1_TAC>>
    qexists_tac`s''`>>qexists_tac`n3`>>
    semttac>>simp[is_rval_def]>>DISJ2_TAC>>
    qexists_tac`s'`>>qexists_tac`n1`>>
    semetac>>
    semttac>>
    metis_tac[simple_sem_t_reln_cases])
  >-
    (ntac 4 semetac>>DISJ2_TAC>>
    semttac>>DISJ2_TAC>>DISJ1_TAC>>
    semttac>>
    metis_tac[simple_sem_t_reln_cases])
  >-
    (ntac 8 semetac>>
    ntac 4 DISJ2_TAC>>
    imp_res_tac sem_e_reln_not_break>>fs[]>>
    metis_tac[simple_sem_t_reln_cases])
  >>
    ntac 8 semetac>>
    ntac 4 DISJ2_TAC>>
    metis_tac[simple_sem_t_reln_cases])

val sem_e_reln_num = Q.prove(
`sem_e_reln s (Num 1) (Rval n1,s') ⇔
 s' = s ∧ n1 = 1`,
 simp[Once sem_e_reln_cases]>>
 metis_tac[])

val simple_sem_t_reln_Loop2 = Q.prove(
  `∀s t res.
  simple_sem_t_reln s t res ⇒
  ∀e1 e2 t'.
  t = (Loop (If e1 (Seq t' (Exp e2)) Break)) ⇒
  simple_sem_t_reln s (For e1 e2 t') res`,
  ho_match_mp_tac simple_sem_t_reln_strongind>>fs[Loop_def]>>rw[]>>
  semttac>>simp[is_rval_def]>>fs[sem_e_reln_num]
  >-
    (fs[Once sem_e_reln_cases]>>metis_tac[is_rval_def])
  >-
    (ntac 2 DISJ2_TAC>>DISJ1_TAC>>
    qpat_assum`simple_sem_t_reln s' B C` mp_tac>>
    semttac>>rw[] >- fs[Once simple_sem_t_reln_cases]>>
    pop_assum mp_tac>>
    semttac>>rw[]>>
    pop_assum mp_tac>>
    semttac>>rw[]>>
    metis_tac[])
  >-
    (pop_assum mp_tac>>semttac>>rw[]
    >-
      fs[Once simple_sem_t_reln_cases]
    >-
      (pop_assum mp_tac>>semttac>>rw[]
      >-
        (pop_assum mp_tac>>semttac>>rw[]>>
        imp_res_tac sem_e_reln_not_break>>fs[])
      >-
        metis_tac[])
    >-
      (imp_res_tac sem_e_reln_not_break>>fs[]))
  >-
    (qpat_assum`simple_sem_t_reln A B C` mp_tac>>
    semttac>>rw[]
    >-
      fs[Once simple_sem_t_reln_cases]
    >>
      (fs[Once sem_e_reln_cases]>>
      metis_tac[is_rval_def]))
  >-
    (qpat_assum`simple_sem_t_reln A B C` mp_tac>>
    semttac>>rw[]>>fs[]
    >-
      fs[Once simple_sem_t_reln_cases]
    >-
      (pop_assum mp_tac>>semttac>>rw[]
      >-
        (pop_assum mp_tac>>semttac>>rw[]>>
        metis_tac[])
      >-
        metis_tac[])))

val simple_sem_t_reln_Loop = Q.prove(
`simple_sem_t_reln s (Loop (If e1 (Seq t (Exp e2)) Break)) res ⇔
 simple_sem_t_reln s (For e1 e2 t) res`,
 metis_tac[simple_sem_t_reln_Loop1,simple_sem_t_reln_Loop2])

val phase1_correct_reln = store_thm("phase1_correct_reln",
``∀s t res.
 simple_sem_t_reln s t res ⇒
 simple_sem_t_reln s (phase1 t) res``,
 ho_match_mp_tac simple_sem_t_reln_strongind>>fs[phase1_def]>>rw[]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_Dec,simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >- metis_tac[simple_sem_t_reln_cases]
 >>
   (fs[simple_sem_t_reln_Loop]>>
   simp[Once simple_sem_t_reln_cases]>>
   metis_tac[]))

val sdtac = simp[Once simple_sem_t_div_cases]

val phase1_correct_div = Q.prove (
`∀s t'.
  (∃t. t' = phase1 t ∧ simple_sem_t_div s t) ⇒
  simple_sem_t_div s t'`,
  ho_match_mp_tac simple_sem_t_div_coind>>rw[]>>
  Cases_on`t`>>fs[phase1_def,Loop_def]
  >-
    (DISJ2_TAC>>semttac>>
    semetac>>semetac>>
    qexists_tac`0`>>
    qexists_tac`s with store:=s.store|+(s',0)`>>fs[is_rval_def]>>
    pop_assum mp_tac >>sdtac>>
    metis_tac[])
  >-(pop_assum mp_tac >> sdtac)
  >-(pop_assum mp_tac >> sdtac)
  >-(pop_assum mp_tac >> sdtac >>rw[]
    >-
      metis_tac[]
    >-
      (DISJ2_TAC>>
      imp_res_tac phase1_correct_reln>>
      metis_tac[]))
  >-
    (pop_assum mp_tac>>sdtac>>rw[]>>metis_tac[])
  >>
    pop_assum mp_tac>>sdtac>>rw[]
    >-
      (semetac>>DISJ1_TAC>>
      qexists_tac`If e0 (Seq t' (Exp e)) Break`>>fs[phase1_def]>>
      sdtac>>DISJ2_TAC>>
      sdtac>>
      metis_tac[])
   >>
     semetac>>DISJ2_TAC>>
     ntac 2 semetac>>
     qexists_tac`n3`>>qexists_tac`s3`>>CONJ_TAC
     >-
       (imp_res_tac phase1_correct_reln>>
       metis_tac[simple_sem_t_reln_cases])
     >>
       qexists_tac`For e0 e t'`>>fs[phase1_def,Loop_def])

val phase1_correct_div = store_thm("phase1_correct_div",
``∀s t.
  simple_sem_t_div s t ⇒
  simple_sem_t_div s (phase1 t)``,
  metis_tac[phase1_correct_div])

val phase1_pres_rel = Q.store_thm("phase1_pres_rel",`
  ∀t.
  rel_semantics t ≠ Crash ⇒
  rel_semantics (phase1 t) = rel_semantics t`,
  strip_tac>>fs[rel_semantics_def,EQ_SYM_EQ]>>
  metis_tac[phase1_correct_reln,simple_sem_t_reln_not_div,phase1_correct_div])

val _ = export_theory ();
