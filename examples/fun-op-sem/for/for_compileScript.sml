open HolKernel Parse boolLib bossLib;

val _ = new_theory "for_compile";

(*

This file proves correctness of a compiler for the FOR language
defined in forScript.sml. The compiler targets a simple assembly-like
language. We prove that the compiler preserves the top-level
observable semantics.

The compiler consists of three passes:
 - the first pass simplifies For loops and removes Dec
 - the second pass compiles expressions into very simple assignments
 - the third pass maps the FOR language into assmembly code

*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open lcsymtacs forTheory listTheory arithmeticTheory;

val _ = temp_tight_equality ();

val ect = BasicProvers.EVERY_CASE_TAC;

val IMP_IMP = METIS_PROVE [] ``b /\ (b1 ==> b2) ==> ((b ==> b1) ==> b2)``


(* === PASS 1 : simplifies For loops and removes Dec === *)

val Loop_def = Define `
  Loop t = For (Num 1) (Num 1) t`;

val pass1_def = Define `
  (pass1 (Exp e) = Exp e) /\
  (pass1 (Dec x t) = Seq (Exp (Assign x (Num 0))) (pass1 t)) /\
  (pass1 (Break) = Break) /\
  (pass1 (Seq t1 t2) = Seq (pass1 t1) (pass1 t2)) /\
  (pass1 (If e t1 t2) = If e (pass1 t1) (pass1 t2)) /\
  (pass1 (For e1 e2 t) = Loop (If e1 (Seq (pass1 t) (Exp e2)) Break))`;

(* Verification of pass 1 *)

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

val pass1_correct = store_thm("pass1_correct",
  ``!t s. sem_t s (pass1 t) = sem_t s t``,
  Induct \\ fs [pass1_def,sem_t_def_with_stop,GSYM sem_t_For,GSYM sem_t_Dec]
  \\ REPEAT STRIP_TAC \\ ect \\ fs [STOP_def]
  \\ MATCH_MP_TAC sem_t_For_swap_body \\ fs []);

val pass1_pres = store_thm("pass1_pres",
  ``!t. semantics (pass1 t) = semantics t``,
  fs [semantics_def,pass1_correct]);


(* === PASS 2 : compiles expressions into very simple assignments === *)

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

val pass2_def = Define `
  pass2 t = flatten_t t ("temp" ++ REPLICATE (t_max t - 3) #"'")`;

(* Verification of pass 2 *)

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

val pass2_subset_def = Define `
  (pass2_subset (Dec v t) = F) /\
  (pass2_subset (Exp e) = T) /\
  (pass2_subset Break = T) /\
  (pass2_subset (Seq t1 t2) = (pass2_subset t1 /\ pass2_subset t2)) /\
  (pass2_subset (If e t1 t2) = (pass2_subset t1 /\ pass2_subset t2)) /\
  (pass2_subset (For e1 e2 t) = ((e1 = Num 1) /\ (e2 = Num 1) /\
     pass2_subset t))`

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
      sem_t s e = (res,s1) /\ res <> Rfail /\ pass2_subset e /\
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
  HO_MATCH_MP_TAC sem_t_ind \\ REPEAT STRIP_TAC \\ fs [pass2_subset_def]
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

val pass2_correct = flatten_t_correct
  |> Q.SPECL [`s`,`t`,`s`,`"temp" ++ REPLICATE (t_max t - 3) #"'"`]
  |> DISCH ``s.store = FEMPTY``
  |> SIMP_RULE (srw_ss()) [GSYM pass2_def,Once possible_var_name_def,
       rich_listTheory.LENGTH_REPLICATE,DECIDE ``n < 4 + (n - 3:num)``,
       PULL_FORALL] |> GEN_ALL;

val pair_eq = prove(
  ``(x = (y1,y2)) <=> (FST x = y1) /\ (SND x = y2)``,
  Cases_on `x` \\ fs [] \\ METIS_TAC []);

val pass2_correct_FST = prove(
  ``pass2_subset t ==>
    (FST (sem_t (s_with_clock c) t) = Rfail) \/
    (FST (sem_t (s_with_clock c) (pass2 t)) =
     FST (sem_t (s_with_clock c) t))``,
  REPEAT STRIP_TAC \\ CCONTR_TAC \\ fs []
  \\ MP_TAC (pass2_correct
      |> Q.SPECL [`t`,`s_with_clock c`]
      |> SIMP_RULE std_ss [pair_eq])
  \\ fs [s_with_clock_def]);

val lemma = prove(
  ``((if b then x1 else x2) <> x2) <=> (x1 <> x2) /\ b``,
  Cases_on `b` \\ fs [])

(* We prove that pass 2 preserves semantics if the source semantics
   does not Crash (implied by successful type check) and if the syntax
   of the compiler program fits with pass2_subset (i.e. syntax
   produced by pass1) *)

val pass2_pres = store_thm("pass2_pres",
  ``!t. semantics t <> Crash /\ pass2_subset t ==>
        semantics (pass2 t) = semantics t``,
  REPEAT STRIP_TAC \\ fs [semantics_thm]
  \\ REVERSE (SRW_TAC [] []) \\ fs [lemma] \\ fs [pair_eq]
  \\ REPEAT (FIRST_X_ASSUM (MP_TAC o Q.SPEC `c:num`))
  \\ REPEAT STRIP_TAC \\ fs []
  \\ MP_TAC pass2_correct_FST \\ fs []);


(* === PASS 3 : maps the FOR language into assmembly code === *)

(* We define the tagert assembly language *)

val _ = Datatype `
reg = Reg string`

val _ = Datatype `
instr =
    Add reg reg reg
  | Int reg int
  | Jmp num
  | JmpIf reg num
  | Halt`;

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

val sem_e_clock = prove(
  ``!e x st' st. (sem_e st e = (x,st')) ==> (st'.clock = st.clock)``,
  Induct \\ fs [sem_e_def] \\ REPEAT STRIP_TAC
  \\ ect \\ SRW_TAC [] [] \\ fs [store_var_def] \\ METIS_TAC []) |> GSYM;

val sem_a_def = tDefine "sem_a" `
sem_a s =
  if s.pc < LENGTH s.instrs then
    case EL s.pc s.instrs of
       | Halt => (Rval 0, s)
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
  else
    (Rfail, s)`
  (WF_REL_TAC `inv_image (measure I LEX measure I)
       (\s. (s.state.clock,LENGTH s.instrs - s.pc))`
   \\ fs [inc_pc_def,do_jump_def,LET_DEF]
   \\ REPEAT STRIP_TAC
   \\ ect \\ fs []
   \\ SRW_TAC [] [] \\ fs []
   \\ IMP_RES_TAC sem_e_clock
   \\ DECIDE_TAC);

val a_state_def = Define `
  a_state code clock =
    <| state := s_with_clock clock; pc := 0; instrs := code |>`;

val asm_semantics_def = Define `
  asm_semantics code =
    if (?c s. sem_a (a_state code c) = (Rval 0,s)) then Terminate
    else if (!c. ?s. sem_a (a_state code c) = (Rtimeout,s)) then Diverge
    else Crash`;

(* Definition of pass3 *)

val pass3_aux_def = Define `
  (pass3_aux n (Dec v t) b = []) /\
  (pass3_aux n (Exp e) b =
     case e of
     | Assign v (Var x) =>
         if x = v then [] else [Int (Reg v) 0; Add (Reg v) (Reg x) (Reg v)]
     | Assign v (Add (Var v1) (Var v2)) => [Add (Reg v) (Reg v1) (Reg v2)]
     | Assign v (Num i) => [Int (Reg v) i]
     | _ => []) /\
  (pass3_aux n Break b = [Jmp b]) /\
  (pass3_aux n (Seq t1 t2) b =
     let c1 = pass3_aux n t1 b in
     let c2 = pass3_aux (n + LENGTH c1) t2 b in
       c1 ++ c2) /\
  (pass3_aux n (If e t1 t2) b =
     let c1 = pass3_aux (n + 1) t1 b in
     let c2 = pass3_aux (n + 2 + LENGTH c1) t2 b in
       [JmpIf (case e of Var v => Reg v | _ => Reg "")
          (n + 2 + LENGTH c1)] ++ c1 ++
       [Jmp (n + 2 + LENGTH c1 + LENGTH c2)] ++ c2) /\
  (pass3_aux n (For e1 e2 t) b =
     let c1 = pass3_aux n t 0 in
     let c2 = pass3_aux n t (n + 1 + LENGTH c1) in
       c2 ++ [Jmp n])`

val pass3_def = Define `
  pass3 t = pass3_aux 0 t 0 ++ [Halt]`;

(* Verification of pass3 *)

val LENGTH_pass3_aux = prove(
  ``!t n b. LENGTH (pass3_aux n t b) = LENGTH (pass3_aux 0 t 0)``,
  Induct \\ fs [pass3_aux_def,LET_DEF]);

val pass3_subset_def = Define `
  (pass3_subset (Dec v t) = F) /\
  (pass3_subset (Exp e) <=>
     (?v x. e = Assign v (Var x)) \/
     (?v i. e = Assign v (Num i)) \/
     (?v x y. e = Assign v (Add (Var x) (Var y)))) /\
  (pass3_subset Break = T) /\
  (pass3_subset (Seq t1 t2) = (pass3_subset t1 /\ pass3_subset t2)) /\
  (pass3_subset (If e t1 t2) <=>
     (?w. e = Var w) /\ pass3_subset t1 /\ pass3_subset t2) /\
  (pass3_subset (For e1 e2 t) = ((e1 = Num 1) /\ (e2 = Num 1) /\ pass3_subset t))`

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

val pass3_aux_thm = store_thm("pass3_aux_thm",
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ pass3_subset t /\
      state_rel s1 x /\
      (x.pc = LENGTH xs) /\
      (x.instrs = xs ++ pass3_aux (LENGTH xs) t b ++ ys) /\
      res <> Rfail /\
      (res = Rbreak ==> OMIT (LENGTH (xs ++ pass3_aux (LENGTH xs) t b) <= b)) ==>
      ?x'.
        (sem_a x = sem_a x') /\
        state_rel s2 x' /\ OMIT (
        (x'.instrs = x.instrs) /\
        (case res of
         | Rfail => T
         | Rbreak => (x'.pc = b)
         | Rtimeout => (sem_a x' = (Rtimeout,x'))
         | Rval v => (x'.pc = LENGTH (xs ++ pass3_aux (LENGTH xs) t b))))``,
  REWRITE_TAC [state_rel_def,OMIT_def]
  \\ HO_MATCH_MP_TAC sem_t_ind \\ REPEAT STRIP_TAC \\ fs [pass3_subset_def]
  THEN1 (* Exp 1 *)
   (fs [pass3_aux_def,sem_t_def] \\ rfs []
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
    \\ Cases_on `FLOOKUP x.state.store x'` \\ fs [] \\ SRW_TAC [] []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ fs [inc_pc_def,DECIDE ``n + 1 < n + 2 + m:num``]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
           rich_listTheory.EL_LENGTH_APPEND
           |> Q.SPECL [`y::ys`,`xs ++ [x]`]
           |> SIMP_RULE (srw_ss()) []
           |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC]]
    \\ fs [sem_e_def,store_var_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,LET_DEF]
    \\ Q.EXISTS_TAC `(x with
         <|state :=
            x.state with store := x.state.store |+ (v,x'');
           pc := LENGTH xs + 1 + 1|>)`
    \\ fs [GSYM ADD_ASSOC])
  THEN1 (* Exp 2 *)
   (fs [pass3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with state := store_var v i x.state))`
    \\ fs [inc_pc_def])
  THEN1 (* Exp 2 *)
   (fs [pass3_aux_def,sem_t_def] \\ rfs []
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])
    \\ fs [LET_DEF,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [sem_e_def] \\ SRW_TAC [] []
    \\ ect \\ fs [] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `(inc_pc (x with state := store_var v (i'' + i') x.state))`
    \\ fs [inc_pc_def])
  THEN1 (* Break *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [pass3_aux_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ imp_res_tac instr_lookup_lemma \\ fs [LET_DEF]
    \\ fs [do_jump_def]
    \\ `b > LENGTH xs` by DECIDE_TAC \\ fs []
    \\ Q.EXISTS_TAC `x with pc := b`
    \\ fs [] \\ fs [state_component_equality])
  THEN1 (* Seq *)
   (fs [sem_t_def] \\ SRW_TAC [] [] \\ fs [pass3_aux_def,LET_DEF]
    \\ Cases_on `sem_t x.state t` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `pass3_aux (LENGTH xs + LENGTH (pass3_aux (LENGTH (xs:instr list)) t b)) t' b
          ++ ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (Cases_on `q` \\ fs [] \\ SRW_TAC [] [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x2`,`xs ++ pass3_aux (LENGTH xs) t b`,
         `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x3.state = s2`
    \\ Q.EXISTS_TAC `x3` \\ fs []
    \\ fs [ADD_ASSOC])
  THEN1 (* If *)
   (fs [pass3_aux_def,sem_t_def]
    \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac (instr_lookup_lemma |> REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ rfs [] \\ POP_ASSUM (K ALL_TAC)
    \\ REVERSE (Cases_on `sem_e s1 (Var w)`) \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ SRW_TAC [] [] \\ fs [sem_e_break]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `gg = (LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0) +
          LENGTH (pass3_aux 0 t2 0))`
    THEN1 (* false case *)
     (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(inc_pc (x with state := r))`,
         `xs ++ [JmpIf (Reg w) (LENGTH (xs:instr list) + 2 + LENGTH (pass3_aux 0 t1 0))]`,
         `[Jmp gg] ++ pass3_aux (LENGTH (xs:instr list) + 2 + LENGTH (pass3_aux 0 t1 0))
            t2 b ++ ys`,`b`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (fs [inc_pc_def] \\ REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = s2`
      \\ REVERSE (Cases_on `res`) \\ fs []
      \\ TRY (Q.EXISTS_TAC `x2` \\ fs [] \\ NO_TAC)
      \\ SIMP_TAC std_ss [Once sem_a_def] \\ fs [LET_DEF]
      \\ `LENGTH xs + 1 + LENGTH (pass3_aux 0 t1 0) <
          LENGTH xs + 1 + LENGTH (pass3_aux (LENGTH xs + 1) t1 b) + 1 +
          LENGTH (pass3_aux (LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0)) t2 b) +
          LENGTH ys /\
          (EL (LENGTH xs + 1 + LENGTH (pass3_aux 0 t1 0))
           (xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0))] ++
            pass3_aux (LENGTH xs + 1) t1 b ++ [Jmp gg] ++
            pass3_aux (LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0)) t2 b ++ ys) =
           Jmp gg)` by ALL_TAC THEN1
      (ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
       \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC
       \\ MATCH_MP_TAC EL_LEMMA
       \\ fs [] \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs [])
      \\ fs [do_jump_def]
      \\ UNABBREV_ALL_TAC
      \\ SRW_TAC [] []
      \\ TRY (`F` by DECIDE_TAC)
      \\ Q.EXISTS_TAC `(x2 with pc :=
           LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0) + LENGTH (pass3_aux 0 t2 0))`
      \\ fs [AC ADD_COMM ADD_ASSOC,ADD1] \\ DECIDE_TAC)
    (* true case *)
    \\ fs [do_jump_def,DECIDE ``n + 2 + m > n:num``]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [
         `(x with <|state := r; pc := LENGTH (xs:instr list) +
            2 + LENGTH (pass3_aux 0 t1 0)|>)`,
         `xs ++ [JmpIf (Reg w) (LENGTH xs + 2 + LENGTH (pass3_aux 0 t1 0))] ++
          pass3_aux (LENGTH xs + 1) t1 b ++ [Jmp gg]`, `ys`,`b`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``]
      \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = s2`
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `x2` \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC,DECIDE ``1+(1+n) = 2 + n:num``,ADD1]
    \\ Cases_on `res` \\ fs [])
  THEN1 (* For *)
   (fs [sem_e_def] \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `sem_t x.state (For (Num 1) (Num 1) t) = (res,s2)` MP_TAC
    \\ SIMP_TAC (srw_ss()) [sem_t_def_with_stop,sem_e_def]
    \\ SIMP_TAC std_ss [STOP_def]
    \\ Cases_on `sem_t x.state t` \\ fs [pass3_aux_def,LET_DEF]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`xs`,
         `[Jmp (LENGTH (xs:instr list))] ++ ys`,`(LENGTH (xs:instr list) + 1 +
             LENGTH (pass3_aux (LENGTH (xs:instr list)) t 0))`]) \\ fs []
    \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `x2.state = r`
    \\ REVERSE (Cases_on `q`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Q.EXISTS_TAC `x2` \\ fs [AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
    \\ SIMP_TAC std_ss [Once sem_a_def]
    \\ `x2.pc < LENGTH x2.instrs` by
      (fs [] \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs [] \\ DECIDE_TAC) \\ fs []
    \\ `(EL (LENGTH xs + LENGTH (pass3_aux 0 t 0)) (xs ++
         pass3_aux (LENGTH xs) t (LENGTH xs + 1 + LENGTH (pass3_aux 0 t 0)) ++
         [Jmp (LENGTH xs)] ++ ys) = Jmp (LENGTH xs))` by
     (`LENGTH (pass3_aux 0 t 0) =
       LENGTH (pass3_aux (LENGTH (xs:instr list)) t
         (LENGTH (xs:instr list) + 1 + LENGTH (pass3_aux 0 t 0)))` by
           (fs [] \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs [])
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
    \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [dec_clock_def]
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.PAT_ASSUM `xxx <= b` MP_TAC
    \\ ONCE_REWRITE_TAC [LENGTH_pass3_aux] \\ fs []))
  |> REWRITE_RULE [state_rel_def,OMIT_def];

val pass3_correct = store_thm("pass3_correct",
  ``!s1 t res s2 x xs ys b.
      (sem_t s1 t = (res,s2)) /\ pass3_subset t /\
      (x.state = s1) /\
      (x.pc = 0) /\
      (x.instrs = pass3 t) /\
      res <> Rfail /\ res <> Rbreak ==>
      ?res' x'.
        (sem_a x = (res', x')) /\
        (x'.state = s2) /\
        (case res of
         | Rval v => (res' = Rval 0)
         | _ => (res' = res))``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL pass3_aux_thm
       |> Q.INST [`xs`|->`[]`,`ys`|->`[Halt]`,`b`|->`0`])
  \\ fs [pass3_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `res` \\ fs [rich_listTheory.EL_LENGTH_APPEND]
  \\ SIMP_TAC std_ss [Once sem_a_def]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

(* We prove that pass3 preserves semantics if the source does not
   crash and if the syntax fits within the subset defined by
   pass3_subset. *)

val pass3_pres = store_thm("pass3_pres",
  ``!t. semantics t <> Crash /\ pass3_subset t ==>
        asm_semantics (pass3 t) = semantics t``,
  REPEAT STRIP_TAC \\ fs [semantics_thm]
  \\ REVERSE (SRW_TAC [] [])
  THEN1 METIS_TAC []
  THEN1
   (fs [asm_semantics_def]
    \\ REVERSE (`!c. ?s. sem_a (a_state (pass3 t) c) = (Rtimeout,s)` by ALL_TAC)
    THEN1 (fs [] \\ SRW_TAC [] []
           \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `c`) \\ fs [])
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `c`)
    \\ MP_TAC (Q.SPECL [`s_with_clock c`,`t`] pass3_correct) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPEC `a_state (pass3 t) c`)
    \\ fs [a_state_def] \\ REPEAT STRIP_TAC \\ fs [])
  \\ fs [asm_semantics_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b ==> ((if b then x else y) = x)``)
  \\ Q.EXISTS_TAC `c`
  \\ MP_TAC (Q.SPECL [`s_with_clock c`,`t`] pass3_correct) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `a_state (pass3 t) c`)
  \\ fs [a_state_def] \\ REPEAT STRIP_TAC \\ fs []);


(* === The end-to-end compiler === *)

val compile_def = Define `
  compile t = pass3 (pass2 (pass1 t))`;

(* Verification of the compile function *)

val pass2_subset_pass1 = prove(
  ``!t. pass2_subset (pass1 t)``,
  Induct \\ fs [pass1_def,pass2_subset_def,Loop_def]);

val pass3_subset_comp_exp = prove(
  ``!e n. pass3_subset (comp_exp e n)``,
  Induct \\ fs [pass3_subset_def,comp_exp_def]);

val pass3_subset_flatten_t = prove(
  ``!t n. pass2_subset t ==> pass3_subset (flatten_t t n)``,
  Induct \\ fs [pass2_subset_def,flatten_t_def,pass3_subset_def]
  \\ fs [pass3_subset_comp_exp]);

val pass3_subset_pass2_pass1 = prove(
  ``!t. pass3_subset (pass2 (pass1 t))``,
  fs [pass2_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC pass3_subset_flatten_t
  \\ fs [pass2_subset_pass1]);

(* The compile function produces code that has observable behaviour
   that is identical to the source program, if the course program does
   not Crash. *)

val compile_pres = store_thm("compile_pres",
  ``!t. semantics t <> Crash ==>
        (asm_semantics (compile t) = semantics t)``,
  fs [compile_def]
  \\ ONCE_REWRITE_TAC [GSYM pass1_pres]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC pass2_pres
  \\ fs [pass2_subset_pass1]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ MATCH_MP_TAC pass3_pres
  \\ fs [pass2_pres,pass2_subset_pass1,pass3_subset_pass2_pass1]);

(* The simple type checker (defined in forScript.sml) ensures that the
   source program cannot Crash. This leads to a cleaner top-level
   correctness theorem for compile. *)

val syntax_ok_def = Define `
  syntax_ok t = type_t F {} t`;

val compile_correct = store_thm("compile_correct",
  ``!t. syntax_ok t ==>
        (asm_semantics (compile t) = semantics t)``,
  METIS_TAC [type_soundness,syntax_ok_def,compile_pres]);

val _ = export_theory ();
