
open HolKernel boolLib bossLib Parse;
open wordsTheory pred_setTheory pairTheory;

open x64_coretypesTheory x64_astTheory x64_seq_monadTheory;

val _ = new_theory "x64_icache";


(* instruction cache definitions *)

val X64_ICACHE_def = Define `
  X64_ICACHE ((r,e,s,m,i):x64_state) ((r2,e2,s2,m2,i2):x64_state) =
    ?insert delete.
      (r = r2) /\ (e = e2) /\ (s = s2) /\ (m = m2) /\
      (i2 = \addr. if addr IN insert then m addr else
                   if addr IN delete then NONE else i addr)`;

val X64_ACCURATE_def = Define `
  X64_ACCURATE a ((r,e,s,m,i):x64_state) = (i a = NONE) \/ (i a = m a)`;

val icache_def = Define `
  icache (insert,delete) m i addr =
    if addr IN insert then m addr else if addr IN delete then NONE else i addr`;

val X64_ICACHE_UPDATE_def = Define `
  X64_ICACHE_UPDATE x ((r1,e1,s1,m1,i1):x64_state) = (r1,e1,s1,m1,icache x m1 i1)`;


(* theorems *)

val X64_ICACHE_REFL = store_thm("X64_ICACHE_REFL",
  ``!s. X64_ICACHE s s``,
  STRIP_TAC THEN `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  THEN ASM_SIMP_TAC std_ss [X64_ICACHE_def]
  THEN Q.EXISTS_TAC `{}` THEN Q.EXISTS_TAC `{}`
  THEN ASM_SIMP_TAC std_ss [NOT_IN_EMPTY,FUN_EQ_THM]);

val X64_ICACHE_TRANS = store_thm("X64_ICACHE_TRANS",
  ``!s t u. X64_ICACHE s t /\ X64_ICACHE t u ==> X64_ICACHE s u``,
  REPEAT STRIP_TAC
  THEN `?r1 e1 t1 m1 i1. s = (r1,e1,t1,m1,i1)` by METIS_TAC [PAIR]
  THEN `?r2 e2 t2 m2 i2. t = (r2,e2,t2,m2,i2)` by METIS_TAC [PAIR]
  THEN `?r3 e3 t3 m3 i3. u = (r3,e3,t3,m3,i3)` by METIS_TAC [PAIR]
  THEN FULL_SIMP_TAC std_ss [X64_ICACHE_def,FUN_EQ_THM]
  THEN REPEAT (POP_ASSUM (K ALL_TAC))
  THEN Q.EXISTS_TAC `insert' UNION (insert DIFF delete')`
  THEN Q.EXISTS_TAC `delete UNION delete'`
  THEN SIMP_TAC std_ss [IN_DIFF,IN_INSERT,IN_UNION] THEN METIS_TAC []);

val X64_ICACHE_THM = store_thm("X64_ICACHE_THM",
  ``X64_ICACHE (r,e,s,m,i) (r2,e2,s2,m2,i2) =
    ?update.
      (r2,e2,s2,m2,i2) = (r,e,s,m,icache update m i)``,
  SIMP_TAC std_ss [EXISTS_PROD,X64_ICACHE_def,icache_def,FUN_EQ_THM]
  THEN METIS_TAC []);

val ZREAD_CLAUSES = store_thm("ZREAD_CLAUSES",
  ``!s. (ZREAD_REG r (ZWRITE_REG r2 w s) = if r2 = r then w else ZREAD_REG r s) /\
        (ZREAD_REG r (ZWRITE_RIP e s) = ZREAD_REG r s) /\
        (ZREAD_REG r (ZWRITE_EFLAG f b s) = ZREAD_REG r s) /\
        (ZREAD_REG r (ZCLEAR_ICACHE s) = ZREAD_REG r s) /\
        (ZREAD_REG r (X64_ICACHE_UPDATE u s) = ZREAD_REG r s) /\
        (ZREAD_REG r (ZWRITE_MEM2 a x s) = ZREAD_REG r s) /\
        (ZREAD_RIP (ZWRITE_REG r2 w s) = ZREAD_RIP s) /\
        (ZREAD_RIP (ZWRITE_RIP e s) = e) /\
        (ZREAD_RIP (ZWRITE_EFLAG f b s) = ZREAD_RIP s) /\
        (ZREAD_RIP (ZCLEAR_ICACHE s) = ZREAD_RIP s) /\
        (ZREAD_RIP (X64_ICACHE_UPDATE u s) = ZREAD_RIP s) /\
        (ZREAD_RIP (ZWRITE_MEM2 a x s) = ZREAD_RIP s) /\
        (ZREAD_EFLAG i (ZWRITE_REG r2 w s) = ZREAD_EFLAG i s) /\
        (ZREAD_EFLAG i (ZWRITE_RIP e s) = ZREAD_EFLAG i s) /\
        (ZREAD_EFLAG i (ZWRITE_EFLAG f b s) = if f = i then b else ZREAD_EFLAG i s) /\
        (ZREAD_EFLAG i (ZCLEAR_ICACHE s) = ZREAD_EFLAG i s) /\
        (ZREAD_EFLAG i (X64_ICACHE_UPDATE u s) = ZREAD_EFLAG i s) /\
        (ZREAD_EFLAG i (ZWRITE_MEM2 a x s) = ZREAD_EFLAG i s) /\
        (ZREAD_MEM2 a (ZWRITE_REG r2 w s) = ZREAD_MEM2 a s) /\
        (ZREAD_MEM2 a (ZWRITE_RIP e s) = ZREAD_MEM2 a s) /\
        (ZREAD_MEM2 a (ZWRITE_EFLAG f b s) = ZREAD_MEM2 a s) /\
        (ZREAD_MEM2 a (ZCLEAR_ICACHE s) = ZREAD_MEM2 a s) /\
        (ZREAD_MEM2 a (X64_ICACHE_UPDATE u s) = ZREAD_MEM2 a s) /\
        (ZREAD_MEM2 a (ZWRITE_MEM2 c x s) = if a = c then x else ZREAD_MEM2 a s)``,
  STRIP_TAC THEN `?r2 e2 s2 m2 i2. s = (r2,e2,s2,m2,i2)` by METIS_TAC [pairTheory.PAIR]
  THEN Cases_on `u`
  THEN ASM_SIMP_TAC std_ss [ZREAD_REG_def,ZREAD_RIP_def,
         ZREAD_EFLAG_def, ZWRITE_REG_def, ZWRITE_MEM2_def, ZREAD_MEM2_def,
         combinTheory.APPLY_UPDATE_THM, ZWRITE_RIP_def,CAN_ZREAD_MEM,
         ZWRITE_EFLAG_def,ZCLEAR_ICACHE_def,CAN_ZWRITE_MEM,X64_ICACHE_UPDATE_def]
  THEN Cases_on `c = a` THEN ASM_SIMP_TAC std_ss []);


val _ = export_theory ();
