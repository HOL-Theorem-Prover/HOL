
open HolKernel boolLib bossLib Parse;
open wordsTheory pred_setTheory pairTheory;

open x86_coretypesTheory x86_astTheory x86_seq_monadTheory;

val _ = new_theory "x86_icache";


(* instruction cache definitions *)

val X86_ICACHE_def = Define `
  X86_ICACHE ((r,e,s,m,i):x86_state) ((r2,e2,s2,m2,i2):x86_state) =
    ?insert delete.
      (r = r2) /\ (e = e2) /\ (s = s2) /\ (m = m2) /\
      (i2 = \addr. if addr IN insert then m addr else
                   if addr IN delete then NONE else i addr)`;

val X86_ACCURATE_def = Define `
  X86_ACCURATE a ((r,e,s,m,i):x86_state) = (i a = NONE) \/ (i a = m a)`;

val icache_def = Define `
  icache (insert,delete) m i addr =
    if addr IN insert then m addr else if addr IN delete then NONE else i addr`;

val X86_ICACHE_UPDATE_def = Define `
  X86_ICACHE_UPDATE x ((r1,e1,s1,m1,i1):x86_state) = (r1,e1,s1,m1,icache x m1 i1)`;


(* theorems *)

val X86_ICACHE_REFL = store_thm("X86_ICACHE_REFL",
  ``!s. X86_ICACHE s s``,
  STRIP_TAC THEN `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  THEN ASM_SIMP_TAC std_ss [X86_ICACHE_def]
  THEN Q.EXISTS_TAC `{}` THEN Q.EXISTS_TAC `{}`
  THEN ASM_SIMP_TAC std_ss [NOT_IN_EMPTY,FUN_EQ_THM]);

val X86_ICACHE_TRANS = store_thm("X86_ICACHE_TRANS",
  ``!s t u. X86_ICACHE s t /\ X86_ICACHE t u ==> X86_ICACHE s u``,
  REPEAT STRIP_TAC
  THEN `?r1 e1 t1 m1 i1. s = (r1,e1,t1,m1,i1)` by METIS_TAC [PAIR]
  THEN `?r2 e2 t2 m2 i2. t = (r2,e2,t2,m2,i2)` by METIS_TAC [PAIR]
  THEN `?r3 e3 t3 m3 i3. u = (r3,e3,t3,m3,i3)` by METIS_TAC [PAIR]
  THEN FULL_SIMP_TAC std_ss [X86_ICACHE_def,FUN_EQ_THM]
  THEN REPEAT (POP_ASSUM (K ALL_TAC))
  THEN Q.EXISTS_TAC `insert' UNION (insert DIFF delete')`
  THEN Q.EXISTS_TAC `delete UNION delete'`
  THEN SIMP_TAC std_ss [IN_DIFF,IN_INSERT,IN_UNION] THEN METIS_TAC []);

val X86_ICACHE_THM = store_thm("X86_ICACHE_THM",
  ``X86_ICACHE (r,e,s,m,i) (r2,e2,s2,m2,i2) =
    ?update.
      (r2,e2,s2,m2,i2) = (r,e,s,m,icache update m i)``,
  SIMP_TAC std_ss [EXISTS_PROD,X86_ICACHE_def,icache_def,FUN_EQ_THM]
  THEN METIS_TAC []);

val XREAD_CLAUSES = store_thm("XREAD_CLAUSES",
  ``!s. (XREAD_REG r (XWRITE_REG r2 w s) = if r2 = r then w else XREAD_REG r s) /\
        (XREAD_REG r (XWRITE_EIP e s) = XREAD_REG r s) /\
        (XREAD_REG r (XWRITE_EFLAG f b s) = XREAD_REG r s) /\
        (XREAD_REG r (XCLEAR_ICACHE s) = XREAD_REG r s) /\
        (XREAD_REG r (X86_ICACHE_UPDATE u s) = XREAD_REG r s) /\
        (XREAD_REG r (XWRITE_MEM2 a x s) = XREAD_REG r s) /\
        (XREAD_EIP (XWRITE_REG r2 w s) = XREAD_EIP s) /\
        (XREAD_EIP (XWRITE_EIP e s) = e) /\
        (XREAD_EIP (XWRITE_EFLAG f b s) = XREAD_EIP s) /\
        (XREAD_EIP (XCLEAR_ICACHE s) = XREAD_EIP s) /\
        (XREAD_EIP (X86_ICACHE_UPDATE u s) = XREAD_EIP s) /\
        (XREAD_EIP (XWRITE_MEM2 a x s) = XREAD_EIP s) /\
        (XREAD_EFLAG i (XWRITE_REG r2 w s) = XREAD_EFLAG i s) /\
        (XREAD_EFLAG i (XWRITE_EIP e s) = XREAD_EFLAG i s) /\
        (XREAD_EFLAG i (XWRITE_EFLAG f b s) = if f = i then b else XREAD_EFLAG i s) /\
        (XREAD_EFLAG i (XCLEAR_ICACHE s) = XREAD_EFLAG i s) /\
        (XREAD_EFLAG i (X86_ICACHE_UPDATE u s) = XREAD_EFLAG i s) /\
        (XREAD_EFLAG i (XWRITE_MEM2 a x s) = XREAD_EFLAG i s) /\
        (XREAD_MEM2 a (XWRITE_REG r2 w s) = XREAD_MEM2 a s) /\
        (XREAD_MEM2 a (XWRITE_EIP e s) = XREAD_MEM2 a s) /\
        (XREAD_MEM2 a (XWRITE_EFLAG f b s) = XREAD_MEM2 a s) /\
        (XREAD_MEM2 a (XCLEAR_ICACHE s) = XREAD_MEM2 a s) /\
        (XREAD_MEM2 a (X86_ICACHE_UPDATE u s) = XREAD_MEM2 a s) /\
        (XREAD_MEM2 a (XWRITE_MEM2 c x s) = if a = c then x else XREAD_MEM2 a s)``,
  STRIP_TAC THEN `?r2 e2 s2 m2 i2. s = (r2,e2,s2,m2,i2)` by METIS_TAC [pairTheory.PAIR]
  THEN Cases_on `u`
  THEN ASM_SIMP_TAC std_ss [XREAD_REG_def,XREAD_EIP_def,
         XREAD_EFLAG_def, XWRITE_REG_def, XWRITE_MEM2_def, XREAD_MEM2_def,
         combinTheory.APPLY_UPDATE_THM, XWRITE_EIP_def,CAN_XREAD_MEM,
         XWRITE_EFLAG_def,XCLEAR_ICACHE_def,CAN_XWRITE_MEM,X86_ICACHE_UPDATE_def]
  THEN Cases_on `c = a` THEN ASM_SIMP_TAC std_ss []);


val _ = export_theory ();
