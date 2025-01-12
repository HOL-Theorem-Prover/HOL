
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory fcpTheory;

open set_sepTheory progTheory x64_Theory x64_seq_monadTheory x64_icacheTheory;
open x64_astTheory x64_coretypesTheory x64_Lib x64_encodeLib;
open temporalTheory;

val _ = new_theory "prog_x64";
val _ = ParseExtras.temp_loose_equality()

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val T64 = ``18446744073709551616:num``

(* ----------------------------------------------------------------------------- *)
(* The x64 set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  x64_el =  zReg of Zreg => word64
          | zStatus of Zeflags => bool option
          | zRIP of word64
          | zMem of word64 => ((word8 # x64_permission set) option) => bool `;

val x64_el_11 = DB.fetch "-" "x64_el_11";
val x64_el_distinct = DB.fetch "-" "x64_el_distinct";

val _ = Parse.type_abbrev("x64_set",``:x64_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from x64-state tuple to x64_set                                    *)
(* ----------------------------------------------------------------------------- *)

val x64_2set'_def = Define `
  x64_2set' (rs,st,ep,ms) (r,e,s,m,i) =
    IMAGE (\a. zReg a (r a)) rs UNION
    IMAGE (\a. zStatus a (s a)) st UNION
    (if ep then {zRIP e} else {}) UNION
    IMAGE (\a. zMem a (m a) (X64_ACCURATE a (r,e,s,m,i))) ms`;

val x64_2set_def   = Define `x64_2set s = x64_2set' (UNIV,UNIV,T,UNIV) s`;
val x64_2set''_def = Define `x64_2set'' x s = x64_2set s DIFF x64_2set' x s`;

(* theorems *)

val x64_2set'_SUBSET_x64_2set = prove(
  ``!y s. x64_2set' y s SUBSET x64_2set s``,
  STRIP_TAC \\ STRIP_TAC
  \\ `?rs st ep ms. y = (rs,st,ep,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SUBSET_DEF,x64_2set'_def,x64_2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_x64_2set = prove(
  ``!x s. SPLIT (x64_2set s) (x64_2set' x s, x64_2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,x64_2set''_def]
  \\ `x64_2set' x s SUBSET x64_2set s` by METIS_TAC [x64_2set'_SUBSET_x64_2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``;

val SUBSET_x64_2set = prove(
  ``!u s. u SUBSET x64_2set s = ?y. u = x64_2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [x64_2set'_SUBSET_x64_2set]
  \\ Q.EXISTS_TAC `({ a | a | ?x. zReg a x IN u },{ a | a | ?x. zStatus a x IN u },
                    (?x. zRIP x IN u),
                    { a | a | ?x y. zMem a x y IN u })`
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [x64_2set'_def,x64_2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [x64_el_11,x64_el_distinct]
  \\ FULL_SIMP_TAC std_ss [PUSH_IN_INTO_IF,NOT_IN_EMPTY,IN_INSERT]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [x64_el_11,x64_el_distinct]
  \\ METIS_TAC []);

val SPLIT_x64_2set_EXISTS = prove(
  ``!s u v. SPLIT (x64_2set s) (u,v) = ?y. (u = x64_2set' y s) /\ (v = x64_2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_x64_2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,x64_2set'_def,x64_2set''_def]
  \\ `u SUBSET (x64_2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_x64_2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val X64_GET_MEMORY_def = Define `X64_GET_MEMORY (r,e,t,m,i) = m`;

val IN_x64_2set = prove(``
  (!r x s. zReg r x IN (x64_2set s) = (x = ZREAD_REG r s)) /\
  (!r x s. zReg r x IN (x64_2set' (rs,st,e,ms) s) = (x = ZREAD_REG r s) /\ r IN rs) /\
  (!r x s. zReg r x IN (x64_2set'' (rs,st,e,ms) s) = (x = ZREAD_REG r s) /\ ~(r IN rs)) /\
  (!a x s. zStatus a x IN (x64_2set s) = (x = ZREAD_EFLAG a s)) /\
  (!a x s. zStatus a x IN (x64_2set' (rs,st,e,ms) s) = (x = ZREAD_EFLAG a s) /\ a IN st) /\
  (!a x s. zStatus a x IN (x64_2set'' (rs,st,e,ms) s) = (x = ZREAD_EFLAG a s) /\ ~(a IN st)) /\
  (!x s. zRIP x IN (x64_2set s) = (x = ZREAD_RIP s)) /\
  (!x s. zRIP x IN (x64_2set' (rs,st,e,ms) s) = (x = ZREAD_RIP s) /\ e) /\
  (!x s. zRIP x IN (x64_2set'' (rs,st,e,ms) s) = (x = ZREAD_RIP s) /\ ~e) /\
  (!p x y s. zMem p x y IN (x64_2set s) = (X64_GET_MEMORY s p = x) /\ (y = X64_ACCURATE p s)) /\
  (!p x y s. zMem p x y IN (x64_2set' (rs,st,e,ms) s) = (X64_GET_MEMORY s p = x) /\ (y = X64_ACCURATE p s) /\ p IN ms) /\
  (!p x y s. zMem p x y IN (x64_2set'' (rs,st,e,ms) s) = (X64_GET_MEMORY s p = x) /\ (y = X64_ACCURATE p s) /\ ~(p IN ms))``,
  REPEAT STRIP_TAC
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR] \\ ASM_SIMP_TAC std_ss []
  \\ SRW_TAC [] [x64_2set'_def,x64_2set''_def,x64_2set_def,IN_UNION,
       IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF,ZREAD_REG_def,
       ZREAD_RIP_def,ZREAD_EFLAG_def,X64_GET_MEMORY_def]
  \\ METIS_TAC []);

val x64_2set''_11 = prove(
  ``!y y2 s s2. (x64_2set'' y2 s2 = x64_2set'' y s) ==> (y = y2)``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?rs st ep m st. y = (rs,st,ep,m)` by METIS_TAC [PAIR]
  \\ `?rs2 st2 ep2 m2. y2 = (rs2,st2,ep2,m2)` by METIS_TAC [PAIR]
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ `?r2 e2 t2 m2 i2. s2 = (r2,e2,t2,m2,i2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ,EXTENSION, Excl "lift_disj_eq"]
  THEN1 (Q.PAT_X_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.SPEC `zReg xi yi`)
    \\ FULL_SIMP_TAC std_ss [IN_x64_2set] \\ METIS_TAC [])
  THEN1 (Q.PAT_X_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.SPEC `zStatus xi yi`)
    \\ FULL_SIMP_TAC std_ss [IN_x64_2set] \\ METIS_TAC [])
  THEN1 (Q.PAT_X_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `ei` o Q.SPEC `zRIP ei`)
    \\ FULL_SIMP_TAC std_ss [IN_x64_2set] \\ METIS_TAC [])
  THEN (Q.PAT_X_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.GEN `zi` o Q.SPEC `zMem xi yi zi`)
    \\ FULL_SIMP_TAC std_ss [IN_x64_2set] \\ METIS_TAC []));

val DELETE_x64_2set = prove(``
  (!a. (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE zReg a (r a) =
       (x64_2set' (rs DELETE a,st,ei,ms) (r,e,s,m,i))) /\
  (!c. (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE zStatus c (s c) =
       (x64_2set' (rs,st DELETE c,ei,ms) (r,e,s,m,i))) /\
  (!c. (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE zRIP e =
       (x64_2set' (rs,st,F,ms) (r,e,s,m,i))) /\
  (!b. (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE
         zMem b (m b) (X64_ACCURATE b (r,e,s,m,i)) =
       (x64_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i)))``,
  REPEAT STRIP_TAC
  \\ SRW_TAC [] [x64_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
       EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF,
       ZREAD_REG_def,ZREAD_MEM_def,ZREAD_EFLAG_def,ZREAD_RIP_def]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_x64_2set = prove(``
  (x64_2set' (rs,st,e,ms) s = {}) = (rs = {}) /\ (ms = {}) /\ (st = {}) /\ ~e``,
  REPEAT STRIP_TAC
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR] \\ ASM_SIMP_TAC std_ss []
  \\ SRW_TAC [] [x64_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
       EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ SIMP_TAC std_ss [x64_el_distinct,x64_el_11] \\ METIS_TAC [PAIR,FST]);


(* ----------------------------------------------------------------------------- *)
(* Defining the X64_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val zR1_def = Define `zR1 a x = SEP_EQ {zReg a x}`;
val zM1_def = Define `zM1 a x b = SEP_EQ {zMem a x b}`;
val zS1_def = Define `zS1 a x = SEP_EQ {zStatus a x}`;
val zPC_def = Define `zPC x = SEP_EQ {zRIP x}`;

val zS_def = Define `
  zS (x0,x1,x2,x3,x4,x5) =
    zS1 Z_CF x0 * zS1 Z_PF x1 * zS1 Z_AF x2 *
    zS1 Z_ZF x3 * zS1 Z_SF x4 * zS1 Z_OF x5`;

val X64_INSTR_PERM_def = Define `
  X64_INSTR_PERM b = {Zread;Zexecute} UNION (if b then {Zwrite} else {})`;

val X64_INSTR_def    = Define `
  (X64_INSTR (a,([])) = {}) /\
  (X64_INSTR (a,((c:word8)::cs)) =
     zMem a (SOME (c,X64_INSTR_PERM T)) T INSERT X64_INSTR (a+1w,(cs)))`;

val X64_STACK_FULL_def = Define `
  X64_STACK_FULL ((r,e,s,m,i):x64_state) = (r zGhost_stack_top = r RSP)`;

val X64_MODEL_def = Define `
  X64_MODEL = (x64_2set, X64_NEXT_REL, X64_INSTR, X64_ICACHE, X64_STACK_FULL)`;

val zCODE_def = Define `zCODE = CODE_POOL X64_INSTR`;

val zM_def = Define `
  zM a (w:word32) =
    ~zM1 a        (SOME ((7 >< 0) (w      ),{Zread;Zwrite;Zexecute})) *
    ~zM1 (a + 1w) (SOME ((7 >< 0) (w >>  8),{Zread;Zwrite;Zexecute})) *
    ~zM1 (a + 2w) (SOME ((7 >< 0) (w >> 16),{Zread;Zwrite;Zexecute})) *
    ~zM1 (a + 3w) (SOME ((7 >< 0) (w >> 24),{Zread;Zwrite;Zexecute})) `;

val zM64_def = Define `
  zM64 a (w:word64) =
    zM a ((31 >< 0) w) * zM (a + 4w) ((63 >< 32) w)`;

val zR_def = Define `
  (zR 0w = zR1 RAX) /\
  (zR 1w = zR1 RCX) /\
  (zR 2w = zR1 RDX) /\
  (zR 3w = zR1 RBX) /\
  (zR 4w = zR1 RSP) /\
  (zR 5w = zR1 RBP) /\
  (zR 6w = zR1 RSI) /\
  (zR 7w = zR1 RDI) /\
  (zR 8w = zR1 zR8) /\
  (zR 9w = zR1 zR9) /\
  (zR 10w = zR1 zR10) /\
  (zR 11w = zR1 zR11) /\
  (zR 12w = zR1 zR12) /\
  (zR 13w = zR1 zR13) /\
  (zR 14w = zR1 zR14) /\
  (zR (15w:word4) = zR1 zR15)`;


(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_x64_2set]
  ``p (x64_2set' y s) ==> (?u v. SPLIT (x64_2set s) (u,v) /\ p u /\ (\v. v = x64_2set'' y s) v)``;

val CODE_POOL_EMPTY = prove(
  ``CODE_POOL m EMPTY = emp``,
  FULL_SIMP_TAC std_ss [Once FUN_EQ_THM,emp_def,CODE_POOL_def]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val X64_SPEC_SEMANTICS = store_thm("X64_SPEC_SEMANTICS",
  ``SPEC X64_MODEL p {} q =
    !y s t1 seq.
      p (x64_2set' y t1) /\ X64_ICACHE t1 s /\ rel_sequence X64_NEXT_REL seq s /\
      ~(X64_STACK_FULL s) ==>
      ?k t2. q (x64_2set' y t2) /\ X64_ICACHE t2 (seq k) /\
             (x64_2set'' y t1 = x64_2set'' y t2) \/ X64_STACK_FULL (seq k)``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_thm,X64_MODEL_def,STAR_def,
    SEP_REFINE_def,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC bool_ss [SPLIT_x64_2set_EXISTS]
    \\ NTAC 4 (POP_ASSUM MP_TAC) \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!y.bbb` (MP_TAC o Q.SPECL [`y`,`state`,`s`,`seq`])
    \\ FULL_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
    \\ Q.EXISTS_TAC `k` \\ DISJ1_TAC \\ Q.EXISTS_TAC `t2`
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  THEN1
   (IMP_RES_TAC lemma \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ FULL_SIMP_TAC bool_ss [SPLIT_x64_2set_EXISTS]
    \\ IMP_RES_TAC x64_2set''_11
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
    \\ Q.PAT_X_ASSUM `!y.bbb` (MP_TAC o Q.SPECL [`s`,`\x. x = (x64_2set'' y t1)`,
          `t1`,`seq`,`y`]) \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1 (METIS_TAC [])
    \\ Q.LIST_EXISTS_TAC [`i`,`s''`]
    \\ IMP_RES_TAC x64_2set''_11
    \\ FULL_SIMP_TAC std_ss []));

val X64_SPEC_1_SEMANTICS = store_thm("X64_SPEC_1_SEMANTICS",
  ``SPEC_1 X64_MODEL p {} q SEP_F =
    !y s t1 seq.
      p (x64_2set' y t1) /\ X64_ICACHE t1 s /\ rel_sequence X64_NEXT_REL seq s /\
      ~(X64_STACK_FULL s) ==>
      ?k t2. q (x64_2set' y t2) /\ X64_ICACHE t2 (seq (k + 1)) /\
             (x64_2set'' y t1 = x64_2set'' y t2) \/ X64_STACK_FULL (seq k)``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_thm,X64_MODEL_def,
    SEP_REFINE_def,PULL_EXISTS,SPEC_1_def,TEMPORAL_def,T_IMPLIES_def,
    T_OR_F_def,NEXT_def,EVENTUALLY_def,NOW_def,SEP_F_def,LET_DEF,
    CODE_POOL_EMPTY,SEP_CLAUSES] \\ SIMP_TAC std_ss [STAR_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC bool_ss [SPLIT_x64_2set_EXISTS] \\ SRW_TAC [] []
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!y.bbb` (MP_TAC o Q.SPECL [`y`,`state`,`s`,`seq`])
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `X64_STACK_FULL state` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC std_ss [rel_sequence_def] \\ METIS_TAC [])
    \\ `state = seq 0` by FULL_SIMP_TAC std_ss [rel_sequence_def]
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ METIS_TAC [])
  \\ IMP_RES_TAC lemma \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_x64_2set_EXISTS]
  \\ IMP_RES_TAC x64_2set''_11
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  THEN1 (METIS_TAC [])
  \\ SRW_TAC [] []
  \\ Q.PAT_X_ASSUM `!y.bbb` (MP_TAC o Q.SPECL [`s`,`seq`,`\s. s = x64_2set'' y t1`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 METIS_TAC [rel_sequence_def]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC []
  THEN1 METIS_TAC []
  \\ IMP_RES_TAC x64_2set''_11
  \\ Q.LIST_EXISTS_TAC [`k`,`s'`] \\ FULL_SIMP_TAC std_ss [])

(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC X64_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_x64_2set = store_thm("STAR_x64_2set",
  ``((zR1 a x * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (x = r a) /\ a IN rs /\ p (x64_2set' (rs DELETE a,st,ei,ms) (r,e,s,m,i))) /\
    ((zS1 c z * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (z = s c) /\ c IN st /\ p (x64_2set' (rs,st DELETE c,ei,ms) (r,e,s,m,i))) /\
    ((zPC q * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (q = e) /\ ei /\ p (x64_2set' (rs,st,F,ms) (r,e,s,m,i))) /\
    ((zM1 b y w * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (y = m b) /\ (w = X64_ACCURATE b (r,e,s,m,i)) /\ b IN ms /\ p (x64_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i))) /\
    ((~(zM1 b y) * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (y = m b) /\ b IN ms /\ p (x64_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i))) /\
    ((cond g * p) (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      g /\ p (x64_2set' (rs,st,ei,ms) (r,e,s,m,i)))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ SIMP_TAC std_ss [zR1_def,zS1_def,zM1_def,EQ_STAR,INSERT_SUBSET,cond_STAR,zPC_def,ZREAD_RIP_def,
       EMPTY_SUBSET,IN_x64_2set,ZREAD_REG_def,ZREAD_EFLAG_def,ZREAD_MEM_def,GSYM DELETE_DEF,
       X64_GET_MEMORY_def]
  THEN1 METIS_TAC [DELETE_x64_2set]
  THEN1 METIS_TAC [DELETE_x64_2set]
  THEN1 METIS_TAC [DELETE_x64_2set]
  \\ Cases_on `y = m b` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `w = X64_ACCURATE b (r,e,s,m,i)`
  \\ ASM_SIMP_TAC std_ss [DELETE_x64_2set,AC CONJ_ASSOC CONJ_COMM]);

val CODE_POOL_x64_2set_AUZ_LEMMA = prove(
  ``!x y z. ~(z IN y) ==> ((x = z INSERT y) = z IN x /\ (x DELETE z = y))``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DELETE] \\ METIS_TAC []);

val address_list_def = Define `
  (address_list a 0 = {}) /\
  (address_list a (SUC n) = a INSERT address_list (a+1w) n)`;

val x64_pool_def = Define `
  (x64_pool (r,s,e,m,i) p ([]) = T) /\
  (x64_pool (r,s,e,m,i) p ((c::cs)) =
     (SOME (c:word8,X64_INSTR_PERM T) = m p) /\ X64_ACCURATE p (r,s,e,m,i) /\
     x64_pool (r,s,e,m,i) (p+1w) (cs))`;

val LEMMA1 = prove(
  ``!p q cs y b. zMem p y b IN X64_INSTR (q,(cs)) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs`
  \\ ASM_SIMP_TAC std_ss [X64_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x64_el_11,n2w_11]
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val LEMMA2 = prove(
  ``!p q cs. p IN address_list q (LENGTH cs) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs`
  \\ ASM_SIMP_TAC std_ss [X64_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x64_el_11,n2w_11]
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val CODE_POOL_x64_2set_LEMMA = prove(
  ``!cs p ms.
      LENGTH cs < 5000 ==>
      (zCODE {(p,(cs))} (x64_2set' (rs,st,ei,ms) (r,s,e,m,i)) =
       (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\
       x64_pool (r,s,e,m,i) p (cs))``,
  Induct
  \\ FULL_SIMP_TAC bool_ss [INSERT_SUBSET,GSYM DELETE_DEF,
      LENGTH,x64_pool_def, EMPTY_SUBSET,zCODE_def,
      IN_DELETE, IMAGE_INSERT, CODE_POOL_def, IMAGE_EMPTY,
      ZREAD_MEM_def, address_list_def, BIGUNION_INSERT, BIGUNION_EMPTY,
      UNION_EMPTY, X64_INSTR_def, IN_x64_2set, EMPTY_x64_2set]
  THEN1 METIS_TAC []
  \\ REPEAT STRIP_TAC
  \\ `LENGTH cs < 5000` by DECIDE_TAC
  \\ Cases_on `zMem p (SOME (h,X64_INSTR_PERM T)) T IN X64_INSTR (p + 1w,(cs))`
  THEN1 (IMP_RES_TAC LEMMA1
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < ^T64` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ Cases_on `p IN address_list (p + 1w) (LENGTH cs)`
  THEN1 (IMP_RES_TAC LEMMA2
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < ^T64` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ ASM_SIMP_TAC bool_ss [CODE_POOL_x64_2set_AUZ_LEMMA,GSYM CONJ_ASSOC,IN_x64_2set,ZREAD_MEM_def]
  \\ Cases_on `SOME (h,X64_INSTR_PERM T) = m p` \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_x64_2set,X64_GET_MEMORY_def]
  \\ Cases_on `X64_ACCURATE p (r,s,e,m,i)` \\ ASM_SIMP_TAC std_ss []
  \\ `zMem p (m p) T = zMem p (m p) (X64_ACCURATE p (r,s,e,m,i))` by
       FULL_SIMP_TAC std_ss [x64_el_11]
  \\ ONCE_ASM_REWRITE_TAC [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_x64_2set,X64_GET_MEMORY_def]
  \\ Cases_on `p IN ms` \\ ASM_REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ FULL_SIMP_TAC bool_ss []);

val CODE_POOL_x64_2set = store_thm("CODE_POOL_x64_2set",
  ``!cs p ms.
      zCODE {(p,(cs))} (x64_2set' (rs,st,ei,ms) (r,s,e,m,i)) =
      if LENGTH cs < 5000 then
        (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\
        x64_pool (r,s,e,m,i) p (cs)
      else zCODE {(p,(cs))} (x64_2set' (rs,st,ei,ms) (r,s,e,m,i))``,
  METIS_TAC [CODE_POOL_x64_2set_LEMMA]);

val icache_revert_def = Define `
  icache_revert (m1:x64_memory,i1:x64_memory) (m2:x64_memory,i2:x64_memory) a =
    if m1 a = m2 a then i1 a else i2 a`;

val X64_ACCURATE_UPDATE = store_thm("X64_ACCURATE_UPDATE",
  ``(X64_ACCURATE a ((xr =+ yr) r,e,s,m,i) = X64_ACCURATE a (r,e,s,m,i)) /\
    (X64_ACCURATE a (r,xe,s,m,i) = X64_ACCURATE a (r,e,s,m,i)) /\
    (X64_ACCURATE a (r,e,(xs =+ ys) s,m,i) = X64_ACCURATE a (r,e,s,m,i)) /\
    (~(xm = a) ==> (X64_ACCURATE a (r,e,s,(xm =+ ym) m,i) = X64_ACCURATE a (r,e,s,m,i))) /\
    (~(a = b) ==>
       (X64_ACCURATE a (r,e,s,m,icache_revert (m,i) ((b =+ w) m2,i2)) =
        X64_ACCURATE a (r,e,s,m,icache_revert (m,i) (m2,i2))))``,
  SIMP_TAC std_ss [X64_ACCURATE_def,APPLY_UPDATE_THM,icache_revert_def]);

val icache_revert_ID = store_thm("icache_revert_ID",
  ``!m i y. icache_revert (m,i) (m,y) = i``,
  SIMP_TAC std_ss [FUN_EQ_THM,icache_revert_def]);

val icache_revert_update = prove(
  ``b IN ms ==>
    (x64_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) ((b =+ w) m2,j)) =
     x64_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) (m2,j)))``,
  SIMP_TAC std_ss [EXTENSION] \\ STRIP_TAC \\ Cases
  \\ SIMP_TAC std_ss [IN_x64_2set,ZREAD_REG_def,ZREAD_EFLAG_def,APPLY_UPDATE_THM,
       ZREAD_RIP_def,X64_GET_MEMORY_def,X64_ACCURATE_def,
       icache_revert_def] \\ METIS_TAC []);

val UPDATE_x64_2set'' = store_thm("UPDATE_x64_2set''",
  ``(!a x. a IN rs ==>
      (x64_2set'' (rs,st,ei,ms) ((a =+ x) r,e,s,m,i) = x64_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x. a IN st ==>
      (x64_2set'' (rs,st,ei,ms) (r,e,(a =+ x) s,m,i) = x64_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x y.
      ((x64_2set'' (rs,st,T,ms) (r,x,s,m,i) = x64_2set'' (rs,st,T,ms) (r,y,s,m,i)) = T)) /\
    (!a x. a IN ms ==>
      (x64_2set'' (rs,st,ei,ms) (r,e,s,(a =+ x) m,i) = x64_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x. a IN ms ==>
      (x64_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) ((a =+ w) m2,j)) =
       x64_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) (m2,j))))``,
  SIMP_TAC std_ss [x64_2set_def,x64_2set''_def,x64_2set'_def,EXTENSION,IN_UNION,
       IN_INSERT,NOT_IN_EMPTY,IN_IMAGE,IN_DIFF,IN_UNIV,ZREAD_REG_def,ZREAD_MEM_def,
       ZREAD_EFLAG_def,APPLY_UPDATE_THM,ZREAD_RIP_def,icache_revert_update]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [X64_ACCURATE_UPDATE]
  \\ METIS_TAC [X64_ACCURATE_UPDATE]);

val SPEC_1_CODE = prove(
  ``!x p c q.
      SPEC_1 x (CODE_POOL (FST (SND (SND x))) c * p) {}
               (CODE_POOL (FST (SND (SND x))) c * q) SEP_F <=>
      SPEC_1 x p c q SEP_F``,
  FULL_SIMP_TAC std_ss [SPEC_1_def,FORALL_PROD,TEMPORAL_def,T_IMPLIES_def,
    EVENTUALLY_def,T_OR_F_def,NOW_def,NEXT_def,LET_DEF,CODE_POOL_EMPTY,
    SEP_CLAUSES,AC STAR_ASSOC STAR_COMM]);

val X64_SPEC_CODE = save_thm("X64_SPEC_CODE",
  RW [GSYM X64_MODEL_def,GSYM zCODE_def]
  (SIMP_RULE std_ss [X64_MODEL_def] (Q.ISPEC `X64_MODEL` SPEC_CODE)));

val X64_SPEC_1_CODE = save_thm("X64_SPEC_1_CODE",
  RW [GSYM X64_MODEL_def,GSYM zCODE_def]
  (SIMP_RULE std_ss [X64_MODEL_def] (Q.ISPEC `X64_MODEL` SPEC_1_CODE)));

val IMP_X64_SPEC_LEMMA = prove(
  ``!p q.
      (!y s t1.
         p (x64_2set' y t1) /\ X64_ICACHE t1 s ==>
         ?v t2.
           p (x64_2set' y s) /\
           (X64_NEXT s = SOME v) /\ q (x64_2set' y t2) /\ X64_ICACHE t2 v /\
           (x64_2set'' y t1 = x64_2set'' y t2)) ==>
      SPEC_1 X64_MODEL p {} q SEP_F``,
  REWRITE_TAC [X64_SPEC_1_SEMANTICS] \\ REPEAT STRIP_TAC
  \\ `p (x64_2set' y s)` by METIS_TAC []
  \\ `X64_NEXT_REL (seq 0) (seq (SUC 0))` by
   (`?x. X64_NEXT_REL (seq 0) x` by
      (RES_TAC \\ Q.EXISTS_TAC `v'`
       \\ ASM_SIMP_TAC std_ss [X64_NEXT_REL_def]
       \\ Q.EXISTS_TAC `seq 0` \\ ASM_SIMP_TAC std_ss []
       \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,X64_ICACHE_REFL])
    \\ METIS_TAC [rel_sequence_def])
  \\ FULL_SIMP_TAC std_ss [X64_NEXT_REL_def]
  \\ `seq 0 = s` by FULL_SIMP_TAC std_ss [rel_sequence_def]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `0`
  \\ Q.PAT_X_ASSUM `!y s t1. bbb` (MP_TAC o
       RW [GSYM AND_IMP_INTRO] o Q.SPECL [`y`,`u`,`t1`])
  \\ IMP_RES_TAC X64_ICACHE_TRANS
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ METIS_TAC []);

val X64_ICACHE_EXTRACT_def = Define `
  X64_ICACHE_EXTRACT ((r1,e1,s1,m1,i1):x64_state) = i1`;

val X64_ICACHE_THM2 = prove(
  ``!s t. X64_ICACHE s t = ?z. t = X64_ICACHE_UPDATE z s``,
  REPEAT STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. s = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ `?r2 e2 s2 m2 i2. t = (r2,e2,s2,m2,i2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X64_ICACHE_UPDATE_def,X64_ICACHE_THM]);

val X64_ICACHE_X64_ACCURATE = prove(
  ``X64_ICACHE (r1,e1,s1,m1,i1) (r1,e1,s1,m1,i2) =
    !a. X64_ACCURATE a (r1,e1,s1,m1,i2) \/ (i1 a = i2 a)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [X64_ACCURATE_def,X64_ICACHE_def,FUN_EQ_THM]
         \\ Cases_on `a IN insert` \\ ASM_SIMP_TAC std_ss []
         \\ Cases_on `a IN delete` \\ ASM_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [X64_ICACHE_def,FUN_EQ_THM]
  \\ Q.EXISTS_TAC `{ a | X64_ACCURATE a (r1,e1,s1,m1,i2) /\ ~(i2 a = NONE) }`
  \\ Q.EXISTS_TAC `{ a | X64_ACCURATE a (r1,e1,s1,m1,i2) /\ (i2 a = NONE) }`
  \\ SIMP_TAC std_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `addr`)
  \\ Cases_on `X64_ACCURATE addr (r1,e1,s1,m1,i2)`
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [X64_ACCURATE_def] \\ METIS_TAC []);

val X64_ICACHE_icache_revert = prove(
  ``X64_ICACHE (r1,e1,s1,m1,i1) (r1,e1,s1,m1,i2) ==>
    X64_ICACHE (r2,e2,s2,m2,icache_revert (m1,i1) (m2,i2)) (r2,e2,s2,m2,i2)``,
  SIMP_TAC std_ss [X64_ICACHE_X64_ACCURATE] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `a`)
  \\ FULL_SIMP_TAC std_ss [X64_ACCURATE_def,icache_revert_def]
  \\ Cases_on `m1 a = m2 a` \\ ASM_SIMP_TAC std_ss []);

val X64_ICACHE_REVERT_def = Define `
  X64_ICACHE_REVERT (r2,e2,s2,m2,i2) (r1,e1,s1,m1,i1) =
    (r2,e2,s2,m2,icache_revert (m1,i1) (m2,i2))`;

val X64_ICACHE_X64_ICACHE_REVERT = store_thm("X64_ICACHE_X64_ICACHE_REVERT",
  ``!s t u. X64_ICACHE s t /\ (X64_ICACHE_EXTRACT t = X64_ICACHE_EXTRACT u) ==>
            X64_ICACHE (X64_ICACHE_REVERT u s) u``,
  NTAC 3 STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. s = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ `?r2 e2 s2 m2 i2. t = (r2,e2,s2,m2,i2)` by METIS_TAC [PAIR]
  \\ `?r3 e3 s3 m3 i3. u = (r3,e3,s3,m3,i3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X64_ICACHE_REVERT_def,X64_ICACHE_EXTRACT_def]
  \\ REPEAT STRIP_TAC
  \\ `(r1,e1,s1,m1) = (r2,e2,s2,m2)` by FULL_SIMP_TAC std_ss [X64_ICACHE_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [X64_ICACHE_icache_revert]);

val X64_ICACHE_EXTRACT_CLAUSES = store_thm("X64_ICACHE_EXTRACT_CLAUSES",
  ``!s r w f fv xs.
      (X64_ICACHE_EXTRACT (ZWRITE_RIP w s) = X64_ICACHE_EXTRACT s) /\
      (X64_ICACHE_EXTRACT (ZWRITE_REG r w s) = X64_ICACHE_EXTRACT s) /\
      (X64_ICACHE_EXTRACT (ZWRITE_EFLAG f fv s) = X64_ICACHE_EXTRACT s)``,
  REPEAT STRIP_TAC
  THEN `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  THEN ASM_SIMP_TAC std_ss [X64_ICACHE_EXTRACT_def,ZWRITE_RIP_def,
          ZWRITE_REG_def,ZWRITE_EFLAG_def]);

val X64_ACCURATE_CLAUSES = store_thm("X64_ACCURATE_CLAUSES",
  ``(X64_ACCURATE a ((r =+ w) x,e,s,m,i) = X64_ACCURATE a (x,e,s,m,i)) /\
    (X64_ACCURATE a (x,e,(f =+ fv) s,m,i) = X64_ACCURATE a (x,e,s,m,i)) /\
    (~(b = a) ==> (X64_ACCURATE a (x,e,s,(b =+ v) m,i) = X64_ACCURATE a (x,e,s,m,i)))``,
  SIMP_TAC std_ss [X64_ACCURATE_def,APPLY_UPDATE_THM]);

val X64_ACCURATE_IMP = store_thm("X64_ACCURATE_IMP",
  ``X64_ACCURATE a (r,e2,t,m,i) ==>
    X64_ACCURATE a (r,e1,t,m,icache_revert (m,i) (m,icache x m i)) /\
    X64_ACCURATE a (r,e1,t,m,icache x m i) /\
    X64_ACCURATE a (r,e1,t,m,i)``,
  Cases_on `x` THEN SIMP_TAC std_ss [X64_ACCURATE_def,icache_revert_def,icache_def]
  THEN METIS_TAC []);

val ZREAD_INSTR_IMP = store_thm("ZREAD_INSTR_IMP",
  ``!x r e t i m a w p.
      (m a = SOME (w,X64_INSTR_PERM p)) /\ X64_ACCURATE a (r,e,t,m,i) ==>
      (ZREAD_INSTR a (r,e,t,m,icache x m i) = SOME w)``,
  Cases THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [X64_ACCURATE_def,icache_def,ZREAD_INSTR_def]
  THEN Cases_on `a IN q` \\ ASM_SIMP_TAC std_ss []
  THEN Cases_on `a IN r` \\ ASM_SIMP_TAC (srw_ss()) []
  THEN Cases_on `p` \\ ASM_SIMP_TAC (srw_ss()) [X64_INSTR_PERM_def]);

val X64_ICACHE_REVERT_EMPTY = prove(
  ``(X64_ICACHE_EXTRACT v = X64_ICACHE_EMPTY) ==>
    X64_ICACHE (X64_ICACHE_REVERT v (r,e,t,m,i)) v``,
  REPEAT STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. v = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X64_ICACHE_REVERT_def,X64_ICACHE_EXTRACT_def]
  \\ FULL_SIMP_TAC std_ss [X64_ICACHE_def]
  \\ Q.EXISTS_TAC `{}` \\ Q.EXISTS_TAC `UNIV`
  \\ SIMP_TAC std_ss [NOT_IN_EMPTY,IN_UNIV,X64_ICACHE_EMPTY_def]);

val IMP_X64_SPEC_LEMMA2 = prove(
  ``!p q.
      (!rs st ei es ms x r e t m i.
         p (x64_2set' (rs,st,ei,ms) (r,e,t,m,i)) ==>
         ?v.
           (X64_NEXT (X64_ICACHE_UPDATE x (r,e,t,m,i)) = SOME v) /\
           ((X64_ICACHE_EXTRACT v = X64_ICACHE_EMPTY) \/
            (X64_ICACHE_EXTRACT (X64_ICACHE_UPDATE x (r,e,t,m,i)) = X64_ICACHE_EXTRACT v)) /\
           p (x64_2set' (rs,st,ei,ms) (X64_ICACHE_UPDATE x (r,e,t,m,i))) /\
           q (x64_2set' (rs,st,ei,ms) (X64_ICACHE_REVERT v (r,e,t,m,i))) /\
           (x64_2set'' (rs,st,ei,ms) (r,e,t,m,i) =
            x64_2set'' (rs,st,ei,ms) (X64_ICACHE_REVERT v (r,e,t,m,i)))) ==>
      SPEC_1 X64_MODEL p {} q SEP_F``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_X64_SPEC_LEMMA
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC X64_ICACHE_THM2
  \\ ASM_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. t1 = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!rs.bb` (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`rs`,`st`,`ei`,`ms`,`z`,`r`,`e`,`t`,`m`,`i`])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(X64_ICACHE_REVERT v (r,e,t,m,i))`
  \\ FULL_SIMP_TAC std_ss []
  THEN1 (METIS_TAC [X64_ICACHE_REVERT_EMPTY])
  \\ MATCH_MP_TAC X64_ICACHE_X64_ICACHE_REVERT
  \\ Q.EXISTS_TAC `(X64_ICACHE_UPDATE z (r,e,t,m,i))` \\ ASM_SIMP_TAC std_ss []);

val SPEC_1_SEP_F_IMP_SPEC = store_thm("SPEC_1_SEP_F_IMP_SPEC",
  ``SPEC_1 model pre code post SEP_F ==> SPEC model pre code post``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC SPEC_1_IMP_SPEC
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]);

val IMP_X64_SPEC = save_thm("IMP_X64_SPEC",
  (SPECL [``p * CODE_POOL X64_INSTR {(rip,c)}``,
          ``q * CODE_POOL X64_INSTR {(rip,c)}``]) IMP_X64_SPEC_LEMMA2
   |> UNDISCH |> MATCH_MP SPEC_1_IMP_SPEC |> RW [SEP_CLAUSES]
   |> RW [X64_SPEC_CODE,GSYM zCODE_def]
   |> RW1 [STAR_COMM]
   |> DISCH_ALL
   |> RW [X64_SPEC_CODE,GSYM zCODE_def]);

val IMP_X64_SPEC_1 = save_thm("IMP_X64_SPEC_1",
  (RW1 [STAR_COMM] o RW [X64_SPEC_1_CODE,GSYM zCODE_def] o
   SPECL [``CODE_POOL X64_INSTR {(rip,c)} * p``,
          ``CODE_POOL X64_INSTR {(rip,c)} * q``]) IMP_X64_SPEC_LEMMA2);

val zS_HIDE = store_thm("zS_HIDE",
  ``~zS = ~zS1 Z_CF * ~zS1 Z_PF * ~zS1 Z_AF * ~zS1 Z_ZF * ~zS1 Z_SF * ~zS1 Z_OF``,
  SIMP_TAC std_ss [SEP_HIDE_def,zS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [zS_def,PAIR]);


(* ----------------------------------------------------------------------------- *)
(* Byte-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val zDATA_PERM_def = Define `
  zDATA_PERM exec = if exec then {Zread;Zwrite;Zexecute} else {Zread;Zwrite}`;

val zBYTE_MEMORY_ANY_SET_def = Define `
  zBYTE_MEMORY_ANY_SET df f exec c =
    { zMem a (SOME (f a, zDATA_PERM exec)) (c a) | a | a IN df }`;

val zBYTE_MEMORY_ANY_C_def = Define `
  zBYTE_MEMORY_ANY_C exec df f c = SEP_EQ (zBYTE_MEMORY_ANY_SET df f exec c)`;

val zBYTE_MEMORY_ANY_def = Define `
  zBYTE_MEMORY_ANY exec df f =
    SEP_EXISTS c. SEP_EQ (zBYTE_MEMORY_ANY_SET df f exec c)`;

val zBYTE_MEMORY_def = Define `zBYTE_MEMORY = zBYTE_MEMORY_ANY T`;
val zBYTE_MEMORY_Z_def = Define `zBYTE_MEMORY_Z = zBYTE_MEMORY_ANY T`;

val IN_zDATA_PERM = store_thm("IN_zDATA_PERM",
  ``(Zread IN zDATA_PERM exec) /\
    (Zwrite IN zDATA_PERM exec) /\
    (Zexecute IN zDATA_PERM exec = exec)``,
  Cases_on `exec` \\ SRW_TAC [] [zDATA_PERM_def,IN_INSERT,NOT_IN_EMPTY]);

val IN_zBYTE_MEMORY_ANY_SET = prove(
  ``a IN df ==>
    (zBYTE_MEMORY_ANY_SET df g exec c =
     (zMem a (SOME (g a, zDATA_PERM exec))) (c a) INSERT
     zBYTE_MEMORY_ANY_SET (df DELETE a) g exec c)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,zBYTE_MEMORY_ANY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_zBYTE_MEMORY_ANY_SET = prove(
  ``zBYTE_MEMORY_ANY_SET (df DELETE a) ((a =+ w) g) exec ((a =+ b) c) =
    zBYTE_MEMORY_ANY_SET (df DELETE a) g exec c``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,zBYTE_MEMORY_ANY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val zBYTE_MEMORY_ANY_C_INSERT = prove(
  ``a IN df ==>
    (zBYTE_MEMORY_ANY_C e df ((a =+ w) g) ((a =+ b) c) =
     zM1 a (SOME (w,zDATA_PERM e)) b * zBYTE_MEMORY_ANY_C e (df DELETE a) g c)``,
  SIMP_TAC std_ss [zM1_def,zBYTE_MEMORY_ANY_C_def,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_zBYTE_MEMORY_ANY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_zBYTE_MEMORY_ANY_SET,APPLY_UPDATE_THM]
  \\ sg `~(zMem a (SOME (w,zDATA_PERM e)) b IN zBYTE_MEMORY_ANY_SET (df DELETE a) g e c)`
  \\ SIMP_TAC std_ss [zBYTE_MEMORY_ANY_SET_def,GSPECIFICATION,IN_DELETE,x64_el_11]
  \\ FULL_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_SET_def,EXTENSION,GSPECIFICATION,IN_DELETE,IN_INSERT]
  \\ METIS_TAC []);

val zBYTE_MEMORY_ANY_INSERT = store_thm("zBYTE_MEMORY_ANY_INSERT",
  ``a IN df ==>
    (zBYTE_MEMORY_ANY e df ((a =+ w) g) =
     ~zM1 a (SOME (w,zDATA_PERM e)) * zBYTE_MEMORY_ANY e (df DELETE a) g)``,
  SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,GSYM zBYTE_MEMORY_ANY_C_def]
    \\ `(y = (a =+ y a) y)` by SIMP_TAC std_ss [APPLY_UPDATE_THM,FUN_EQ_THM]
    \\ Q.PAT_X_ASSUM `zBYTE_MEMORY_ANY_C e df ((a =+ w) g) y x` MP_TAC
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ ASM_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_C_INSERT]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [],
    FULL_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,GSYM zBYTE_MEMORY_ANY_C_def]
    \\ FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `(a =+ y') y`
    \\ ASM_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_C_INSERT]]);

val zBYTE_MEMORY_ANY_INSERT_SET =
  SIMP_RULE std_ss [IN_INSERT,DELETE_INSERT,APPLY_UPDATE_ID]
  (Q.INST [`df`|->`a INSERT df`,`w`|->`g a`] zBYTE_MEMORY_ANY_INSERT);

val zBYTE_MEMORY_ANY_INTRO = store_thm("zBYTE_MEMORY_ANY_INTRO",
  ``SPEC m (~zM1 a (SOME (v,zDATA_PERM e)) * P) c
           (~zM1 a (SOME (w,zDATA_PERM e)) * Q) ==>
    a IN df ==>
    SPEC m (zBYTE_MEMORY_ANY e df ((a =+ v) f) * P) c
           (zBYTE_MEMORY_ANY e df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [zBYTE_MEMORY_ANY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Word-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val zMEMORY_DOMAIN_def = Define `
  zMEMORY_DOMAIN df = BIGUNION { {b;b+1w;b+2w;b+3w} | (b && 3w = 0w) /\ b:word64 IN df }`;

val zMEMORY_FUNC_def = Define `
  zMEMORY_FUNC (f:word64->word32) a =
    let w = f (a - (a && 3w)) in
      if a && 3w = 0w then (7 >< 0) (w) else
      if a && 3w = 1w then (7 >< 0) (w >> 8) else
      if a && 3w = 2w then (7 >< 0) (w >> 16) else
      if a && 3w = 3w then (7 >< 0) (w >> 24) else 0w:word8`;

val zMEMORY_def = Define `
  zMEMORY df f = zBYTE_MEMORY (zMEMORY_DOMAIN df) (zMEMORY_FUNC f)`;

val zBYTE_MEMORY_ANY_SET_EQ = prove(
  ``zBYTE_MEMORY_ANY_SET df f exec c =
     {zMem d (SOME (f d,zDATA_PERM exec)) (c d) | d IN df}``,
  METIS_TAC [zBYTE_MEMORY_ANY_SET_def]);

val aligned_4_ADD_AND_3 = prove(
  ``!x. (x && 0x3w = 0x0w) ==>
        (x + 0x0w && 0x3w = 0x0w) /\
        (x + 0x1w && 0x3w = 0x1w) /\
        (x + 0x2w && 0x3w = 0x2w) /\
        (x + 0x3w && 0x3w = 0x3w:word64)``,
  blastLib.BBLAST_TAC);

val not_aligned = prove(
  ``!x. (x && 0x3w = 0x0w) ==>
        ~((x + 1w) && 0x3w = 0x0w) /\
        ~((x + 2w) && 0x3w = 0x0w) /\
        ~((x + 3w) && 0x3w = 0x0w:word64)``,
  blastLib.BBLAST_TAC);

val aligned_ADD_SELF = prove(
  ``!x. ((x + 4w) && 0x3w = 0x0w) = (x && 0x3w = 0x0w:word64)``,
  blastLib.BBLAST_TAC);

val aligned_cases = prove(
  ``!w. (w && 3w = 0w) \/ (w && 3w = 1w) \/ (w && 3w = 2w) \/ (w && 3w = 3w:word64)``,
  blastLib.BBLAST_TAC);

val zMEMORY_INSERT = store_thm("zMEMORY_INSERT",
  ``a IN df /\ (a && 3w = 0w) ==>
    (zMEMORY df ((a =+ w) f) = zM a w * zMEMORY (df DELETE a) f)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [zMEMORY_def,zBYTE_MEMORY_def,zM_def,GSYM STAR_ASSOC]
  \\ `zMEMORY_DOMAIN df = a INSERT (a+1w) INSERT (a+2w) INSERT
      (a+3w) INSERT zMEMORY_DOMAIN (df DELETE a)` by
   (FULL_SIMP_TAC std_ss [zMEMORY_DOMAIN_def]
    \\ `{{b; b + 1w; b + 2w; b + 3w} | (b && 3w = 0w) /\ b IN df} =
        {a; a + 1w; a + 2w; a + 3w} INSERT
        {{b; b + 1w; b + 2w; b + 3w} | (b && 3w = 0w) /\ b IN df DELETE a}` by
      (SIMP_TAC std_ss [EXTENSION,IN_INSERT,
         IN_BIGUNION,GSPECIFICATION,NOT_IN_EMPTY,IN_DELETE]
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
       \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
       \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [BIGUNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY])
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [zBYTE_MEMORY_ANY_INSERT_SET,DELETE_INSERT,
       WORD_EQ_ADD_CANCEL,n2w_11]
  \\ SIMP_TAC std_ss [zMEMORY_FUNC_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [aligned_4_ADD_AND_3]
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB,WORD_SUB_RZERO]
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,zDATA_PERM_def]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(q1 = q2) ==> ((p * q1) = (STAR p q2))``)
  \\ `~(a IN zMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+1w IN zMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+2w IN zMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+3w IN zMEMORY_DOMAIN (df DELETE a))` by
   (SIMP_TAC std_ss [zMEMORY_DOMAIN_def,GSPECIFICATION,IN_BIGUNION,
        IN_DELETE,EXTENSION,IN_INSERT,NOT_IN_EMPTY]
    \\ IMP_RES_TAC not_aligned
    \\ SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
    \\ REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_EQ_SUB,word_arith_lemma4]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,WORD_EQ_ADD_CANCEL]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,aligned_ADD_SELF,
         word_arith_lemma3,WORD_ADD_0])
  \\ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x z = f y z)``)
  \\ SIMP_TAC std_ss [zBYTE_MEMORY_ANY_SET_EQ,EXTENSION,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [x64_el_11]
  \\ SIMP_TAC std_ss [zMEMORY_FUNC_def,LET_DEF]
  \\ STRIP_ASSUME_TAC (Q.SPEC `d` aligned_cases)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,WORD_SUB_RZERO,n2w_11]
  \\ SIMP_TAC std_ss [WORD_EQ_SUB_LADD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val zM_LEMMA = prove(
  ``!w a f. (a && 3w = 0w) ==> (zM a w = zMEMORY {a} ((a =+ w) f))``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [IN_INSERT] (Q.INST [`df`|->`{a}`] zMEMORY_INSERT))
  \\ ASM_SIMP_TAC std_ss []
  \\ `({a} DELETE a) = {}` by
    SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE,NOT_IN_EMPTY]
  \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE (sg `zMEMORY {} f = emp`)
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [zMEMORY_def,zBYTE_MEMORY_def,zBYTE_MEMORY_ANY_def,zBYTE_MEMORY_ANY_SET_def]
  \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ SIMP_TAC std_ss [emp_def]
  \\ SIMP_TAC std_ss [SEP_EXISTS_THM,zMEMORY_DOMAIN_def,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [IN_BIGUNION,GSPECIFICATION,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY]);

val zM_THM = store_thm("zM_THM",
  ``!a w f. (a && 3w = 0w) ==> (zMEMORY {a} ((a =+ w) f) = zM a w) /\
                               (zMEMORY {a} (\x. w) = zM a w)``,
  SIMP_TAC std_ss [GSYM zM_LEMMA,GSYM (RW [APPLY_UPDATE_ID]
    (Q.SPECL [`(f:word64->word32) a`,`a`,`f`] zM_LEMMA))]);

val zMEMORY_INTRO = store_thm("zMEMORY_INTRO",
  ``SPEC m (zM a v * P) c (zM a w * Q) ==>
    (a && 3w = 0w) /\ a IN df ==>
    SPEC m (zMEMORY df ((a =+ v) f) * P) c (zMEMORY df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [zMEMORY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Word-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val zMEMORY64_DOMAIN_def = Define `
  zMEMORY64_DOMAIN df = BIGUNION
    { {b;b+1w;b+2w;b+3w;b+4w;b+5w;b+6w;b+7w} |
      (b && 7w = 0w) /\ b:word64 IN df }`;

val zMEMORY64_FUNC_def = Define `
  zMEMORY64_FUNC (f:word64->word64) a =
    let w = f (a - (a && 7w)) in
      if a && 7w = 0w then (7 >< 0) (w) else
      if a && 7w = 1w then (7 >< 0) (w >> 8) else
      if a && 7w = 2w then (7 >< 0) (w >> 16) else
      if a && 7w = 3w then (7 >< 0) (w >> 24) else
      if a && 7w = 4w then (7 >< 0) (w >> 32) else
      if a && 7w = 5w then (7 >< 0) (w >> 40) else
      if a && 7w = 6w then (7 >< 0) (w >> 48) else
      if a && 7w = 7w then (7 >< 0) (w >> 56) else 0w:word8`;

val zMEMORY64_def = Define `
  zMEMORY64 df f = zBYTE_MEMORY (zMEMORY64_DOMAIN df) (zMEMORY64_FUNC f)`;

val zBYTE_MEMORY_ANY_SET_EQ = prove(
  ``zBYTE_MEMORY_ANY_SET df f exec c =
     {zMem d (SOME (f d,zDATA_PERM exec)) (c d) | d IN df}``,
  METIS_TAC [zBYTE_MEMORY_ANY_SET_def]);

val aligned_8_ADD_AND_7 = prove(
  ``!x. (x && 0x7w = 0x0w) ==>
        (x + 0x0w && 0x7w = 0x0w) /\
        (x + 0x1w && 0x7w = 0x1w) /\
        (x + 0x2w && 0x7w = 0x2w) /\
        (x + 0x3w && 0x7w = 0x3w) /\
        (x + 0x4w && 0x7w = 0x4w) /\
        (x + 0x5w && 0x7w = 0x5w) /\
        (x + 0x6w && 0x7w = 0x6w) /\
        (x + 0x7w && 0x7w = 0x7w:word64)``,
  blastLib.BBLAST_TAC);

val not_aligned = prove(
  ``!x. (x && 0x7w = 0x0w) ==>
        ~((x + 1w) && 0x7w = 0x0w) /\
        ~((x + 2w) && 0x7w = 0x0w) /\
        ~((x + 3w) && 0x7w = 0x0w) /\
        ~((x + 4w) && 0x7w = 0x0w) /\
        ~((x + 5w) && 0x7w = 0x0w) /\
        ~((x + 6w) && 0x7w = 0x0w) /\
        ~((x + 7w) && 0x7w = 0x0w:word64)``,
  blastLib.BBLAST_TAC);

val aligned_ADD_SELF = prove(
  ``!x. ((x + 8w) && 0x7w = 0x0w) = (x && 0x7w = 0x0w:word64)``,
  blastLib.BBLAST_TAC);

val aligned_cases = prove(
  ``!w:word64.
      (w && 7w = 0w) \/ (w && 7w = 1w) \/ (w && 7w = 2w) \/ (w && 7w = 3w) \/
      (w && 7w = 4w) \/ (w && 7w = 5w) \/ (w && 7w = 6w) \/ (w && 7w = 7w)``,
  blastLib.BBLAST_TAC);

val word_lemma = prove(
  ``!w. ((7 >< 0) (((31 >< 0):word64->word32) w) = ((7 >< 0) w):word8) /\
        ((7 >< 0) (((31 >< 0):word64->word32) w >> 8) = ((7 >< 0) (w >> 8)):word8) /\
        ((7 >< 0) (((31 >< 0):word64->word32) w >> 16) = ((7 >< 0) (w >> 16)):word8) /\
        ((7 >< 0) (((31 >< 0):word64->word32) w >> 24) = ((7 >< 0) (w >> 24)):word8) /\
        ((7 >< 0) (((63 >< 32):word64->word32) w) = ((7 >< 0) (w >> 32)):word8) /\
        ((7 >< 0) (((63 >< 32):word64->word32) w >> 8) = ((7 >< 0) (w >> 40)):word8) /\
        ((7 >< 0) (((63 >< 32):word64->word32) w >> 16) = ((7 >< 0) (w >> 48)):word8) /\
        ((7 >< 0) (((63 >< 32):word64->word32) w >> 24) = ((7 >< 0) (w >> 56)):word8)``,
  blastLib.BBLAST_TAC);

val zMEMORY64_INSERT = store_thm("zMEMORY64_INSERT",
  ``a IN df /\ (a && 7w = 0w) ==>
    (zMEMORY64 df ((a =+ w) f) = zM64 a w * zMEMORY64 (df DELETE a) f)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [zMEMORY64_def,zBYTE_MEMORY_def,zM64_def,GSYM STAR_ASSOC,zM_def]
  \\ FULL_SIMP_TAC std_ss [word_lemma]
  \\ `zMEMORY64_DOMAIN df =
        a INSERT (a+1w) INSERT (a+2w) INSERT (a+3w) INSERT
        (a+4w) INSERT (a+5w) INSERT (a+6w) INSERT (a+7w) INSERT
        zMEMORY64_DOMAIN (df DELETE a)` by
   (FULL_SIMP_TAC std_ss [zMEMORY64_DOMAIN_def]
    \\ `{{b; b + 1w; b + 2w; b + 3w; b+4w; b+5w; b+6w; b+7w} | (b && 7w = 0w) /\ b IN df} =
        {a; a + 1w; a + 2w; a + 3w; a+4w; a+5w; a+6w; a+7w} INSERT
        {{b; b + 1w; b + 2w; b + 3w; b+4w; b+5w; b+6w; b+7w} | (b && 7w = 0w) /\ b IN df DELETE a}` by
      (SIMP_TAC std_ss [EXTENSION,IN_INSERT,
         IN_BIGUNION,GSPECIFICATION,NOT_IN_EMPTY,IN_DELETE]
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
       \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
       \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [BIGUNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY])
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [zBYTE_MEMORY_ANY_INSERT_SET,DELETE_INSERT,
       WORD_EQ_ADD_CANCEL,n2w_11]
  \\ SIMP_TAC std_ss [zMEMORY64_FUNC_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [aligned_8_ADD_AND_7]
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB,WORD_SUB_RZERO]
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,zDATA_PERM_def]
  \\ SIMP_TAC std_ss [STAR_ASSOC,word_arith_lemma1]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(q1 = q2) ==> ((p * q1) = (STAR p q2))``)
  \\ `~(a IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+1w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+2w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+3w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+4w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+5w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+6w IN zMEMORY64_DOMAIN (df DELETE a)) /\
      ~(a+7w IN zMEMORY64_DOMAIN (df DELETE a))` by
   (SIMP_TAC std_ss [zMEMORY64_DOMAIN_def,GSPECIFICATION,IN_BIGUNION,
        IN_DELETE,EXTENSION,IN_INSERT,NOT_IN_EMPTY]
    \\ IMP_RES_TAC not_aligned
    \\ SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
    \\ REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_EQ_SUB,word_arith_lemma4]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,WORD_EQ_ADD_CANCEL]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,aligned_ADD_SELF,
         word_arith_lemma3,WORD_ADD_0])
  \\ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [zBYTE_MEMORY_ANY_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x z = f y z)``)
  \\ SIMP_TAC std_ss [zBYTE_MEMORY_ANY_SET_EQ,EXTENSION,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [x64_el_11]
  \\ SIMP_TAC std_ss [zMEMORY64_FUNC_def,LET_DEF]
  \\ STRIP_ASSUME_TAC (Q.SPEC `d` aligned_cases)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,WORD_SUB_RZERO,n2w_11]
  \\ SIMP_TAC std_ss [WORD_EQ_SUB_LADD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val zM64_LEMMA = prove(
  ``!w a f. (a && 7w = 0w) ==> (zM64 a w = zMEMORY64 {a} ((a =+ w) f))``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [IN_INSERT] (Q.INST [`df`|->`{a}`] zMEMORY64_INSERT))
  \\ ASM_SIMP_TAC std_ss []
  \\ `({a} DELETE a) = {}` by
    SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE,NOT_IN_EMPTY]
  \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE (sg `zMEMORY64 {} f = emp`)
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [zMEMORY64_def,zBYTE_MEMORY_def,zBYTE_MEMORY_ANY_def,zBYTE_MEMORY_ANY_SET_def]
  \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ SIMP_TAC std_ss [emp_def]
  \\ SIMP_TAC std_ss [SEP_EXISTS_THM,zMEMORY64_DOMAIN_def,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [IN_BIGUNION,GSPECIFICATION,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY]);

val zM64_THM = store_thm("zM64_THM",
  ``!a w f. (a && 7w = 0w) ==> (zMEMORY64 {a} ((a =+ w) f) = zM64 a w) /\
                               (zMEMORY64 {a} (\x. w) = zM64 a w)``,
  SIMP_TAC std_ss [GSYM zM64_LEMMA,GSYM (RW [APPLY_UPDATE_ID]
    (Q.SPECL [`(f:word64->word64) a`,`a`,`f`] zM64_LEMMA))]);

val zMEMORY64_INTRO = store_thm("zMEMORY64_INTRO",
  ``SPEC m (zM64 a v * P) c (zM64 a w * Q) ==>
    (a && 7w = 0w) /\ a IN df ==>
    SPEC m (zMEMORY64 df ((a =+ v) f) * P) c (zMEMORY64 df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [zMEMORY64_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Conversions between code and data                                             *)
(* ----------------------------------------------------------------------------- *)

val zCODE_SET_def = Define `zCODE_SET df f = { (a,[f a]) | a IN df }`;

val zCODE_IMP_BYTE_MEMORY = store_thm("zCODE_IMP_BYTE_MEMORY",
  ``!df f. SEP_IMP (zCODE (zCODE_SET df f)) (zBYTE_MEMORY_Z df f)``,
  SIMP_TAC std_ss [SEP_IMP_def,zCODE_def,CODE_POOL_def,SEP_EQ_def,
    zBYTE_MEMORY_Z_def,zBYTE_MEMORY_ANY_def,SEP_EXISTS,zBYTE_MEMORY_ANY_SET_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `\x.T`
  \\ SIMP_TAC std_ss [zDATA_PERM_def,zCODE_SET_def,EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,EXTENSION,IN_BIGUNION]
  \\ ONCE_REWRITE_TAC [IN_IMAGE]
  \\ `X64_INSTR_PERM T = {Zread; Zwrite; Zexecute}` by
       (SIMP_TAC std_ss [X64_INSTR_PERM_def,EXTENSION,IN_INSERT,
          NOT_IN_EMPTY,IN_UNION] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (NTAC 2 (FULL_SIMP_TAC std_ss [X64_INSTR_def,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY])
    \\ Q.EXISTS_TAC `a` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `X64_INSTR (a,[f a])`
  \\ ASM_SIMP_TAC std_ss [X64_INSTR_def,IN_INSERT,X64_INSTR_PERM_def]
  \\ Q.EXISTS_TAC `(a,[f a])`
  \\ ASM_SIMP_TAC std_ss [X64_INSTR_def,IN_INSERT,X64_INSTR_PERM_def]
  \\ ASM_SIMP_TAC std_ss [GSPECIFICATION]);

Theorem x64_2set_ICACHE_EMPTY[local]:
  (x64_2set' (rs,st,ei,ms) (r,e2,t,m,(\a. if a IN ms then NONE else i a)) =
   x64_2set' (rs,st,ei,ms) (r,e2,t,m,X64_ICACHE_EMPTY)) /\
  (x64_2set'' (rs,st,ei,ms) (r,e2,t,m,(\a. if a IN ms then NONE else i a)) =
   x64_2set'' (rs,st,ei,ms) (r,e2,t,m,i))
Proof
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [EXTENSION] \\ Cases
  \\ SIMP_TAC std_ss [
      IN_x64_2set,ZREAD_REG_def,ZREAD_EFLAG_def,Excl "lift_imp_disj",
         ZREAD_RIP_def,X64_GET_MEMORY_def,X64_ACCURATE_def,X64_ICACHE_EMPTY_def]
  \\ SRW_TAC [][Excl "lift_imp_disj"]
QED

val IMP_X64_SPEC_LEMMA3 = prove(
  ``!p q.
      (!rs st ei es ms x r e t m i.
         p (x64_2set' (rs,st,ei,ms) (r,e,t,m,i)) ==>
         ?v.
           (X64_NEXT (r,e,t,m,icache x m i) = SOME v) /\
           (X64_ICACHE_EXTRACT v = X64_ICACHE_EMPTY) /\
           p (x64_2set' (rs,st,ei,ms) (r,e,t,m,icache x m i)) /\
           q (x64_2set' (rs,st,ei,ms) ((\(r,e,t,m,i). (r,e,t,m,X64_ICACHE_EMPTY)) v)) /\
           (x64_2set'' (rs,st,ei,ms) (r,e,t,m,i) =
            x64_2set'' (rs,st,ei,ms) ((\(r,e,t,m,i2). (r,e,t,m,i)) v))) ==>
      SPEC_1 X64_MODEL p {} q SEP_F``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_X64_SPEC_LEMMA
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC X64_ICACHE_THM2
  \\ ASM_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. t1 = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!rs.bb` (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`rs`,`st`,`ei`,`ms`,`z`,`r`,`e`,`t`,`m`,`i`])
  \\ ASM_SIMP_TAC std_ss [X64_ICACHE_UPDATE_def]
  \\ `?r e t m i. v = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(r',e',t',m',(\addr. if addr IN ms then NONE else i addr))`
  \\ ASM_SIMP_TAC std_ss [x64_2set_ICACHE_EMPTY]
  \\ SIMP_TAC std_ss [X64_ICACHE_EMPTY_def,X64_ICACHE_def,FUN_EQ_THM]
  \\ FULL_SIMP_TAC std_ss [X64_ICACHE_EXTRACT_def]
  \\ Q.EXISTS_TAC `{}` \\ Q.EXISTS_TAC `UNIV` \\ SRW_TAC [] [] \\ EVAL_TAC);

val IMP_X64_SPEC2 = save_thm("IMP_X64_SPEC2",
  SPECL [``p * CODE_POOL X64_INSTR c``,
         ``q * CODE_POOL X64_INSTR c``] IMP_X64_SPEC_LEMMA3
  |> UNDISCH_ALL
  |> MATCH_MP SPEC_1_SEP_F_IMP_SPEC
  |> RW1 [STAR_COMM]
  |> DISCH_ALL
  |> RW [X64_SPEC_CODE,GSYM zCODE_def]);

val cpuid_thm = let
  val th = x64_step "0FA2" (* cpuid *)
  val th = Q.INST [`s`|->`X64_ICACHE_UPDATE x (r,e,t,m,i)`] th
  val th = RW [ZREAD_CLAUSES] th
  val th = RW [ZREAD_REG_def,X64_ICACHE_UPDATE_def,
               ZWRITE_RIP_def,ZCLEAR_ICACHE_def] th
  in th end

val zBYTE_MEMORY_Z_x64_2set = prove(
  ``!df ms.
      (zBYTE_MEMORY_Z df f * p) (x64_2set' (rs,st,ei,ms) (r,e,t,m,i)) =
      p (x64_2set' (rs,st,ei,ms DIFF df) (r,e,t,m,i)) /\ df SUBSET ms /\
      !a. a IN df ==> (m a = SOME (f a, {Zread;Zwrite;Zexecute}))``,
  HO_MATCH_MP_TAC WORD_SET_INDUCT \\ REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [zBYTE_MEMORY_Z_def,zBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [NOT_IN_EMPTY]
    \\ `!c. zBYTE_MEMORY_ANY_SET {} f T c = {}` by
      SIMP_TAC std_ss [zBYTE_MEMORY_ANY_SET_def,NOT_IN_EMPTY,EXTENSION,GSPECIFICATION]
    \\ ASM_SIMP_TAC std_ss [GSYM emp_def,SEP_EQ_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [DIFF_EMPTY,EMPTY_SUBSET],
    FULL_SIMP_TAC std_ss [zBYTE_MEMORY_Z_def]
    \\ SIMP_TAC std_ss [DIFF_INSERT,zBYTE_MEMORY_ANY_INSERT_SET]
    \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC,STAR_x64_2set,DELETE_NON_ELEMENT]
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,GSYM DELETE_NON_ELEMENT]
    \\ ASM_SIMP_TAC std_ss [zDATA_PERM_def,INSERT_SUBSET,SUBSET_DELETE]
    \\ METIS_TAC []]);

val zCODE_SET_INSERT = store_thm("zCODE_SET_INSERT",
  ``~(e IN df) ==>
    (zCODE (zCODE_SET (e INSERT df) f) =
     zM1 e (SOME (f e, {Zread; Zwrite; Zexecute})) T * zCODE (zCODE_SET df f))``,
  SIMP_TAC std_ss [zCODE_def,zCODE_SET_def,zM1_def,EQ_STAR,FUN_EQ_THM] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [CODE_POOL_def,INSERT_SUBSET,EMPTY_SUBSET]
  \\ `~((e,[f e]) IN {(a,[f a]) | a IN df}) /\
      ({(a,[f a]) | a IN e INSERT df} = (e,[f e]) INSERT {(a,[f a]) | a IN df})` by
        (SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ SIMP_TAC std_ss [X64_INSTR_def,INSERT_UNION_EQ,UNION_EMPTY]
  \\ `X64_INSTR_PERM T = {Zread; Zwrite; Zexecute}` by
        (SIMP_TAC std_ss [X64_INSTR_PERM_def,EXTENSION,IN_INSERT,
          IN_UNION,NOT_IN_EMPTY] \\ REPEAT STRIP_TAC \\ EQ_TAC
         \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [DIFF_INSERT,DIFF_EMPTY]
  \\ Q.ABBREV_TAC `a1 = zMem e (SOME (f e,{Zread; Zwrite; Zexecute})) T`
  \\ Q.ABBREV_TAC `a2 = BIGUNION (IMAGE X64_INSTR {(a,[f a]) | a IN df})`
  \\ `~(a1 IN a2)` suffices_by
  (STRIP_TAC THEN SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE] \\ METIS_TAC [])
  \\ Q.UNABBREV_TAC `a1` \\ Q.UNABBREV_TAC `a2`
  \\ ASM_SIMP_TAC std_ss [IN_IMAGE,IN_BIGUNION]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``e \/ b = ~e ==> b``,GSPECIFICATION]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [X64_INSTR_def,IN_INSERT,NOT_IN_EMPTY,x64_el_11]);

val zCODE_SET_x64_2set = prove(
  ``!df ms.
      (zCODE (zCODE_SET df f) * p) (x64_2set' (rs,st,ei,ms) (r,e,t,m,i)) =
      p (x64_2set' (rs,st,ei,ms DIFF df) (r,e,t,m,i)) /\ df SUBSET ms /\
      !a. a IN df ==> (m a = SOME (f a, {Zread;Zwrite;Zexecute})) /\
                      X64_ACCURATE a (r,e,t,m,i)``,
  HO_MATCH_MP_TAC WORD_SET_INDUCT \\ REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [zCODE_SET_def,zCODE_def,SEP_CLAUSES]
    \\ `{(a,[f a]) | a IN {}} = {}` by
      SIMP_TAC std_ss [NOT_IN_EMPTY,EXTENSION,GSPECIFICATION]
    \\ ASM_SIMP_TAC std_ss [CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY]
    \\ SIMP_TAC std_ss [GSYM emp_def,SEP_CLAUSES,DIFF_EMPTY,EMPTY_SUBSET]
    \\ SIMP_TAC std_ss [NOT_IN_EMPTY],
    ASM_SIMP_TAC std_ss [GSYM STAR_ASSOC,zCODE_SET_INSERT]
    \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC,STAR_x64_2set,DELETE_NON_ELEMENT]
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,GSYM DELETE_NON_ELEMENT]
    \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,SUBSET_DELETE,DIFF_INSERT]
    \\ METIS_TAC []]);

val X64_SPEC_CPUID = store_thm("X64_SPEC_CPUID",
  ``SPEC X64_MODEL
      (zR1 RAX rax * zR1 RBX rbx * zR1 RCX rcx * zR1 RDX rdx *
       zPC rip * zBYTE_MEMORY_Z df f * cond (rax = 0w))
      {(rip,[0x0Fw;0xA2w])}
      (zR1 RAX ARB * zR1 RBX ARB * zR1 RCX ARB * zR1 RDX ARB *
       zPC (rip+2w) * zCODE (zCODE_SET df f))``,
  FULL_SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_X64_SPEC2 \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [X64_ICACHE_UPDATE_def]
  \\ EXISTS_TAC (cpuid_thm |> concl |> dest_imp |> snd |> rand |> rand)
  \\ STRIP_TAC THENL [MATCH_MP_TAC cpuid_thm,ALL_TAC]
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x64_2set, IN_DELETE, APPLY_UPDATE_THM, x64_decoderTheory.Zreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Zeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES,X64_ICACHE_UPDATE_def,ZREAD_RIP_def,
         X64_ICACHE_REVERT_def,zM_def,WORD_EQ_ADD_CANCEL,x64_address_lemma,
         zCODE_SET_x64_2set,zBYTE_MEMORY_Z_x64_2set]
  \\ ONCE_REWRITE_TAC [CODE_POOL_x64_2set]
  \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
  \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,X64_ICACHE_EXTRACT_def]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x64_2set, IN_DELETE, APPLY_UPDATE_THM, x64_decoderTheory.Zreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Zeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,x64_pool_def,X64_ACCURATE_CLAUSES,
         zCODE_SET_x64_2set,zBYTE_MEMORY_Z_x64_2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN1
   (REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ MATCH_MP_TAC ZREAD_INSTR_IMP \\ Q.EXISTS_TAC `T`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC X64_ACCURATE_IMP
  \\ ASM_SIMP_TAC std_ss [IN_INSERT]
  THEN1 EVAL_TAC
  \\ SIMP_TAC std_ss [ZWRITE_REG_def,ZCLEAR_ICACHE_def,ZWRITE_RIP_def,
       X64_ICACHE_REVERT_def,icache_revert_ID]
  \\ SIMP_TAC std_ss [ZWRITE_REG_def,ZCLEAR_ICACHE_def,ZWRITE_RIP_def,X64_ICACHE_REVERT_def]
  \\ ASM_SIMP_TAC (srw_ss()) [STAR_x64_2set,APPLY_UPDATE_THM,zCODE_SET_x64_2set]
  \\ SIMP_TAC std_ss [X64_ACCURATE_def,X64_ICACHE_EMPTY_def,X64_ICACHE_EXTRACT_def]
  \\ ONCE_REWRITE_TAC [CODE_POOL_x64_2set]
  \\ ASM_SIMP_TAC std_ss [LENGTH,x64_pool_def,X64_ACCURATE_def]
  \\ FULL_SIMP_TAC std_ss [icache_revert_def,X64_ACCURATE_def]
  \\ ASM_SIMP_TAC std_ss [UPDATE_x64_2set'']
  \\ ASM_SIMP_TAC std_ss [EVAL ``address_list rip 2``]
  \\ ASM_SIMP_TAC std_ss [SET_EQ_SUBSET,INSERT_SUBSET,EMPTY_SUBSET]);

val SPLIT_CODE_SEQ = prove(
  ``SPEC X64_MODEL p ((a,x::xs) INSERT s) q =
    SPEC X64_MODEL p ((a+1w,xs) INSERT (a,[x]) INSERT s) q``,
  SIMP_TAC std_ss [progTheory.SPEC_def,X64_MODEL_def]
  \\ sg `CODE_POOL X64_INSTR ((a + 0x1w,xs) INSERT (a,[x]) INSERT s) =
      CODE_POOL X64_INSTR ((a,x::xs) INSERT s)`
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [progTheory.CODE_POOL_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> ((\s. s = x) = (\s. s = y))``)
  \\ SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ SIMP_TAC std_ss [EXTENSION,IN_BIGUNION]
  \\ SIMP_TAC std_ss [X64_INSTR_def]
  \\ SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []);

val X64_SPEC_EXLPODE_CODE_LEMMA = store_thm("X64_SPEC_EXLPODE_CODE_LEMMA",
  ``!s. SPEC X64_MODEL p ((a,xs) INSERT s) q =
        SPEC X64_MODEL p ({ (a + n2w n, [EL n xs]) | n | n < LENGTH xs } UNION s) q``,
  Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`xs`,`xs`) \\ REVERSE Induct THEN1
   (ASM_SIMP_TAC std_ss [SPLIT_CODE_SEQ] \\ REPEAT STRIP_TAC
    \\ sg `{(a + n2w n,[EL n (h::xs)]) | n | n < LENGTH (h::xs)} =
        {(a + 0x1w + n2w n,[EL n xs]) | n | n < LENGTH xs} UNION {(a,[h])}`
    \\ ASM_SIMP_TAC std_ss [INSERT_UNION_EQ,UNION_EMPTY,GSYM UNION_ASSOC]
    \\ SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
      Cases_on `n` \\ ASM_SIMP_TAC std_ss [EL,HD,WORD_ADD_0,TL,CONS_11]
      \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,LENGTH]
      \\ SIMP_TAC std_ss [DECIDE ``1+n = SUC n``] \\ METIS_TAC [],
      Q.EXISTS_TAC `SUC n`
      \\ SIMP_TAC std_ss [EL,GSYM word_add_n2w,RW1 [ADD_COMM] ADD1]
      \\ ASM_SIMP_TAC std_ss [TL,WORD_ADD_ASSOC,LENGTH] \\ DECIDE_TAC,
      Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,EL,LENGTH,HD]])
  \\ REPEAT STRIP_TAC
  \\ `{(a + n2w n,[EL n ([]:word8 list)]) | n | n < LENGTH ([]:word8 list)} = {}` by
    ASM_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,LENGTH]
  \\ ASM_SIMP_TAC std_ss [UNION_EMPTY]
  \\ SIMP_TAC std_ss [progTheory.SPEC_def,X64_MODEL_def]
  \\ sg `CODE_POOL X64_INSTR ((a,[]) INSERT s) =
      CODE_POOL X64_INSTR (s)`
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [progTheory.CODE_POOL_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> ((\s. s = x) = (\s. s = y))``)
  \\ POP_ASSUM (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [UNION_EMPTY,IMAGE_INSERT,X64_INSTR_def,BIGUNION_INSERT]);

val X64_SPEC_EXLPODE_CODE = save_thm("X64_SPEC_EXLPODE_CODE",
  RW [UNION_EMPTY] (Q.SPEC `{}` X64_SPEC_EXLPODE_CODE_LEMMA));

val CODE_POOL_INSERT_INSERT = store_thm("CODE_POOL_INSERT_INSERT",
  ``CODE_POOL X64_INSTR ((a1,xs) INSERT (a1 + n2w (LENGTH xs),ys) INSERT s) =
    CODE_POOL X64_INSTR ((a1,xs ++ ys) INSERT s)``,
  SIMP_TAC std_ss [CODE_POOL_def,IMAGE_INSERT] \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> !s. (s = x) = (s = y)``)
  \\ SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ `!xs a ys. X64_INSTR (a,xs ++ ys) =
             X64_INSTR (a,xs) UNION X64_INSTR (a + n2w (LENGTH xs),ys)` suffices_by
  (STRIP_TAC THEN ASM_SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM])
  \\ Induct
  \\ ASM_SIMP_TAC std_ss [APPEND,X64_INSTR_def,UNION_EMPTY,LENGTH,WORD_ADD_0]
  \\ SIMP_TAC std_ss [RW1[ADD_COMM]ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [INSERT_UNION_EQ]);

val SPEC_X64_MERGE_CODE = store_thm("SPEC_X64_MERGE_CODE",
  ``SPEC X64_MODEL p ((a1,xs) INSERT (a2,ys) INSERT s) q ==>
    (a2 = a1 + n2w (LENGTH xs)) ==>
    SPEC X64_MODEL p ((a1,xs++ys) INSERT s) q``,
  Q.SPEC_TAC (`a2`,`a2`) \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SPEC_def,X64_MODEL_def]
  \\ REVERSE (sg `CODE_POOL X64_INSTR
       ((a1,xs) INSERT (a1 + n2w (LENGTH xs),ys) INSERT s) =
       CODE_POOL X64_INSTR ((a1,xs ++ ys) INSERT s)`)
  \\ FULL_SIMP_TAC std_ss [CODE_POOL_INSERT_INSERT]);

val SPEC_X64_MERGE_CODE_REV = store_thm("SPEC_X64_MERGE_CODE_REV",
  ``SPEC X64_MODEL p ((a1,xs++ys) INSERT s) q ==>
    (a2 = a1 + n2w (LENGTH xs)) ==>
    SPEC X64_MODEL p ((a1,xs) INSERT (a2,ys) INSERT s) q``,
  Q.SPEC_TAC (`a2`,`a2`) \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SPEC_def,X64_MODEL_def]
  \\ REVERSE (sg `CODE_POOL X64_INSTR
       ((a1,xs) INSERT (a1 + n2w (LENGTH xs),ys) INSERT s) =
       CODE_POOL X64_INSTR ((a1,xs ++ ys) INSERT s)`)
  \\ FULL_SIMP_TAC std_ss [CODE_POOL_INSERT_INSERT]);


(* ----------------------------------------------------------------------------- *)
(* Improved code assertion                                                       *)
(* ----------------------------------------------------------------------------- *)

val zCODE_HEAP_AUX_def = Define `
  zCODE_HEAP_AUX safe a xs =
    SEP_EXISTS df f.
      cond ((SEP_ARRAY (\a x. one (a,x)) 1w a xs) (fun2set (f,df))) *
      if safe then zCODE (zCODE_SET df f) else zBYTE_MEMORY_Z df f`;

val zCODE_HEAP_def = Define `
  zCODE_HEAP safe a xs n =
    SEP_EXISTS ys.
      cond (LENGTH xs + LENGTH ys = n) * zCODE_HEAP_AUX safe a (xs ++ ys)`;

(* snoc *)

val PULL_FORALL = METIS_PROVE [] ``(b ==> !x. P x) = (!x. b ==> P x)``

val zCODE_HEAP_SNOC = store_thm("zCODE_HEAP_SNOC",
  ``(!df f.
      SPEC X64_MODEL
        (p * zBYTE_MEMORY_Z df f * cond (a + n2w (LENGTH xs) IN df)) c
        (q * zBYTE_MEMORY_Z df ((a + n2w (LENGTH xs) =+ x) f))) ==>
    SPEC X64_MODEL
      (p * zCODE_HEAP F a xs n * cond (LENGTH xs < n)) c
      (q * zCODE_HEAP F a (SNOC x xs) n)``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss) [zCODE_HEAP_def,
       zCODE_HEAP_AUX_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++helperLib.sep_cond_ss) [GSYM SPEC_PRE_EXISTS,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `ys` THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ `F` by DECIDE_TAC)
  \\ MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `q * zBYTE_MEMORY_Z df ((a + n2w (LENGTH xs) =+ x) f)`
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [SPEC_MOVE_COND] \\ Q.PAT_X_ASSUM `!x.bb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,SEP_ARRAY_def]
    \\ FULL_SIMP_TAC std_ss [word_mul_n2w] \\ helperLib.SEP_R_TAC)
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`t`,`df`,`((a + n2w (LENGTH xs) =+ x) f)`]
  \\ FULL_SIMP_TAC (srw_ss()) [cond_STAR,ADD_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,SEP_ARRAY_def]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w] \\ helperLib.SEP_WRITE_TAC);

val list_lemma = prove(
  ``!xs n. n < LENGTH xs ==> ?ys1 y ys2. (xs = ys1 ++ y::ys2) /\ (LENGTH ys1 = n)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,APPEND]
  \\ RES_TAC \\ Q.EXISTS_TAC `h::ys1`
  \\ FULL_SIMP_TAC (srw_ss()) [APPEND]);

val zCODE_HEAP_UPDATE = store_thm("zCODE_HEAP_UPDATE",
  ``(!df f.
      SPEC X64_MODEL
        (p * zBYTE_MEMORY_Z df f * cond (a + n2w k IN df)) c
        (q * zBYTE_MEMORY_Z df ((a + n2w k =+ x) f))) ==>
    SPEC X64_MODEL
      (p * zCODE_HEAP F a xs n * cond (k < LENGTH xs)) c
      (q * zCODE_HEAP F a (LUPDATE x k xs) n)``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss) [zCODE_HEAP_def,
       zCODE_HEAP_AUX_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++helperLib.sep_cond_ss) [GSYM SPEC_PRE_EXISTS,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `q * zBYTE_MEMORY_Z df ((a + n2w k =+ x) f)`
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [SPEC_MOVE_COND] \\ Q.PAT_X_ASSUM `!x.bb` MATCH_MP_TAC
    \\ IMP_RES_TAC list_lemma
    \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,SEP_ARRAY_def,word_mul_n2w]
    \\ helperLib.SEP_R_TAC)
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`ys`,`df`,`((a + n2w k =+ x) f)`]
  \\ FULL_SIMP_TAC (srw_ss()) [cond_STAR,ADD_CLAUSES,LENGTH_LUPDATE]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC list_lemma
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,SEP_ARRAY_def,word_mul_n2w,
       LENGTH_LUPDATE,STAR_ASSOC,LENGTH_APPEND,LENGTH]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH]
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_APPEND,SEP_ARRAY_def,word_mul_n2w,
       LENGTH_LUPDATE,STAR_ASSOC,LENGTH_APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w] \\ helperLib.SEP_WRITE_TAC);


(* safe vs unsafe *)

val zCODE_HEAP_UNSAFE = store_thm("zCODE_HEAP_UNSAFE",
  ``SPEC X64_MODEL (zCODE_HEAP T a xs n) {} (zCODE_HEAP F a xs n)``,
  MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `zCODE_HEAP T a xs n` \\ FULL_SIMP_TAC std_ss [SPEC_REFL]
  \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss) [zCODE_HEAP_def,
       zCODE_HEAP_AUX_def,SEP_CLAUSES]
  \\ MATCH_MP_TAC SEP_IMP_EXISTS_EXISTS \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ MATCH_MP_TAC SEP_IMP_EXISTS_EXISTS \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ MATCH_MP_TAC SEP_IMP_EXISTS_EXISTS \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_STAR]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
    (zCODE_IMP_BYTE_MEMORY |> SIMP_RULE std_ss [SEP_IMP_def]));

val zCODE_HEAP_SAFE = store_thm("zCODE_HEAP_SAFE",
  ``SPEC X64_MODEL
     (zR 0w r0 * zR 1w r1 * zR 2w r2 * zR 3w r3 * zPC rip *
      zCODE_HEAP F a xs n * cond (r0 = 0x0w))
     {(rip,[0xFw; 0xA2w])}
     (~zR 0w * ~zR 1w * ~zR 2w * ~zR 3w * zPC (rip + 0x2w) *
      zCODE_HEAP T a xs n)``,
  MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `(zR 0x0w ARB * zR 0x1w ARB * zR 0x2w ARB * zR 0x3w ARB *
                    zPC (rip + 0x2w) * zCODE_HEAP T a xs n)`
  \\ REVERSE STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [zCODE_HEAP_def,zCODE_HEAP_AUX_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++helperLib.sep_cond_ss) [GSYM SPEC_PRE_EXISTS,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `(zR 0x0w ARB * zR 0x1w ARB * zR 0x2w ARB * zR 0x3w ARB *
                    zPC (rip+2w) * zCODE (zCODE_SET df f))`
  \\ REVERSE STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ SIMP_TAC (std_ss++helperLib.sep_cond_ss) [cond_STAR] \\ METIS_TAC [])
  \\ IMP_RES_TAC (X64_SPEC_CPUID |> REWRITE_RULE [GSYM zR_def,SPEC_MOVE_COND] |> GEN_ALL)
  \\ FULL_SIMP_TAC (std_ss++helperLib.star_ss) [] \\ METIS_TAC []);


(* exec safe *)

val SPEC_X64_RUN_CODE_HEAP_AUX = prove(
  ``SPEC X64_MODEL p {(a,xs)} q ==>
    SPEC X64_MODEL (p * zCODE_HEAP_AUX T a xs) {} (q * zCODE_HEAP_AUX T a xs)``,
  FULL_SIMP_TAC std_ss [zCODE_HEAP_AUX_def,SEP_CLAUSES,X64_SPEC_EXLPODE_CODE]
  \\ SIMP_TAC (std_ss++helperLib.sep_cond_ss) [GSYM SPEC_PRE_EXISTS,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `(q * zCODE (zCODE_SET df f))`
  \\ REVERSE STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`df`,`f`] \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES])
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ FULL_SIMP_TAC std_ss [X64_SPEC_CODE]
  \\ FULL_SIMP_TAC std_ss [zCODE_SET_def]
  \\ sg `{(a + n2w n,[EL n xs]) | n | n < LENGTH xs} = {(a,[f a]) | a IN df}`
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ Q.SPEC_TAC (`df`,`df`) \\ Q.SPEC_TAC (`a`,`a`)
  \\ Induct_on `xs`
  THEN1 FULL_SIMP_TAC (srw_ss()) [SEP_ARRAY_def,emp_def,fun2set_def,EXTENSION]
  \\ FULL_SIMP_TAC std_ss [SEP_ARRAY_def,one_STAR]
  \\ SIMP_TAC std_ss [Once fun2set_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ `fun2set (f,df) DELETE (a,f a) = fun2set (f,df DELETE a)` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION,fun2set_def] \\ METIS_TAC [PAIR_EQ])
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ `{(a + n2w n,[EL n (f a::xs)]) | n | n < SUC (LENGTH xs)} =
      (a,[f a]) INSERT {(a + 0x1w + n2w n,[EL n xs]) | n | n < LENGTH xs}` suffices_by
  (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `n` THEN1 FULL_SIMP_TAC (srw_ss()) []
    \\ DISJ2_TAC \\ FULL_SIMP_TAC std_ss [EL,TL,CONS_11]
    \\ FULL_SIMP_TAC std_ss [ADD1,word_arith_lemma1]
    \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `x`)
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `(?n. (x = (a + n2w n + 0x1w,[EL n xs])) /\ n < LENGTH xs)` by METIS_TAC []
  \\ Q.EXISTS_TAC `n+1` \\ FULL_SIMP_TAC (srw_ss()) [word_arith_lemma1]
  \\ ASM_SIMP_TAC std_ss [GSYM ADD1,EL,TL]);

val SPEC_X64_RUN_CODE_HEAP = store_thm("SPEC_X64_RUN_CODE_HEAP",
  ``SPEC X64_MODEL p {(a,xs)} q ==>
    SPEC X64_MODEL (p * zCODE_HEAP T a xs n) {} (q * zCODE_HEAP T a xs n)``,
  FULL_SIMP_TAC std_ss [zCODE_HEAP_def,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss) [SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `(q * zCODE_HEAP_AUX T a (xs ++ ys))` \\ REVERSE STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] \\ METIS_TAC [])
  \\ MATCH_MP_TAC SPEC_X64_RUN_CODE_HEAP_AUX
  \\ MATCH_MP_TAC (SPEC_X64_MERGE_CODE |> RW [AND_IMP_INTRO] |> GEN_ALL)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (SPEC_SUBSET_CODE |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])
  \\ Q.EXISTS_TAC `{(a,xs)}` \\ FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]);


(* ----------------------------------------------------------------------------- *)
(* Simplifications of w2w (w2w x + w2w y) and similar                            *)
(* ----------------------------------------------------------------------------- *)

val LOAD64 = store_thm("LOAD64",
  ``(w2w (((63 >< 32) w):word32) << 32 || w2w (((31 >< 0) w):word32) = w:word64) /\
    (w2w (((31 >< 0) w):word32) || w2w (((63 >< 32) w):word32) << 32 = w:word64)``,
  blastLib.BBLAST_TAC);

val WORD_BITS_BITS_ZERO = store_thm("WORD_BITS_BITS_ZERO",
  ``!w k. (k -- 0) ((k -- 0) w) = (k -- 0) w``,
  SIMP_TAC std_ss [word_bits_def,fcpTheory.CART_EQ,fcpTheory.FCP_BETA]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [fcpTheory.FCP_BETA]);

val WORD_BITS_NOT_BITS_ZERO = store_thm("WORD_BITS_NOT_BITS_ZERO",
  ``!w k. (k -- 0) (~((k -- 0) w)) = (k -- 0) (~w)``,
  SIMP_TAC std_ss [word_bits_def,fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_1comp_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [fcpTheory.FCP_BETA]);

val WORD_w2w_n2w_OVER_BITWISE = store_thm("WORD_w2w_n2w_OVER_BITWISE",
  ``!w n. n < dimword (:'b) \/ dimindex (:'a) <= dimindex (:'b) ==>
          (w2w w && n2w n = w2w ((w:'b word) && n2w n) :'a word) /\
          (n2w n && w2w w = w2w (n2w n && (w:'b word)) :'a word) /\
          (w2w w ?? n2w n = w2w ((w:'b word) ?? n2w n) :'a word) /\
          (n2w n ?? w2w w = w2w (n2w n ?? (w:'b word)) :'a word) /\
          (w2w w || n2w n = w2w ((w:'b word) || n2w n) :'a word) /\
          (n2w n || w2w w = w2w (n2w n || (w:'b word)) :'a word)``,
  NTAC 3 STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ `(n2w n):'a word = w2w ((n2w (n MOD dimword (:'b))):'b word)` by
          ASM_SIMP_TAC std_ss [w2w_def,w2n_n2w]
    \\ ASM_SIMP_TAC std_ss [WORD_w2w_OVER_BITWISE])
  \\ SIMP_TAC std_ss [CART_EQ,w2w,word_and_def,FCP_BETA,word_or_def,word_xor_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `i < dimindex(:'b)`
  \\ ASM_SIMP_TAC std_ss [FCP_BETA,AC CONJ_COMM CONJ_ASSOC,word_index]
  \\ `F` by DECIDE_TAC);

val w2w_OVER_ARITH = store_thm("w2w_OVER_ARITH",
  ``!v w.
      dimindex (:'b) <= dimindex (:'a) /\ dimindex (:'b) <= dimindex (:'c) ==>
      (w2w (w2w v + (w2w w) :'c word) = w2w (v + w:'a word) :'b word) /\
      (w2w (w2w v - (w2w w) :'c word) = w2w (v - w:'a word) :'b word) /\
      (w2w (w2w v * (w2w w) :'c word) = w2w (v * w:'a word) :'b word)``,
  Cases \\ Cases
  \\ ASM_SIMP_TAC std_ss [w2w_def,w2n_n2w,word_add_n2w,
       word_mul_n2w, word_sub_def,n2w_11,word_2comp_n2w]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [dimword_def]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS,EXP_ADD]
  \\ FULL_SIMP_TAC std_ss [MOD_MULT_MOD,ZERO_LT_EXP]
  \\ ONCE_REWRITE_TAC [GSYM (SIMP_RULE std_ss [ZERO_LT_EXP]
                              (Q.SPEC `2**k` MOD_PLUS))]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ FULL_SIMP_TAC std_ss [EXP_ADD]
  \\ FULL_SIMP_TAC std_ss [GSYM dimword_def]
  \\ MP_TAC (Q.SPECL [`dimword(:'b)`,`2**p'`,`n' MOD (2 ** p' * dimword (:'b))`]
             MOD_COMPLEMENT)
  \\ `0:num < 2**p'` by ASM_SIMP_TAC std_ss [ZERO_LT_EXP]
  \\ ASM_SIMP_TAC std_ss [ZERO_LT_dimword,MOD_LESS,ZERO_LESS_MULT]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [RW1[MULT_COMM]th])
  \\ ASM_SIMP_TAC std_ss [MOD_MULT_MOD,ZERO_LT_dimword]
  \\ MP_TAC (Q.SPECL [`dimword(:'b)`,`2**p`,`n'`] MOD_COMPLEMENT)
  \\ `0:num < 2**p` by ASM_SIMP_TAC std_ss [ZERO_LT_EXP]
  \\ ASM_SIMP_TAC std_ss [ZERO_LT_dimword,MOD_LESS,ZERO_LESS_MULT]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (fn th => MP_TAC (RW1[MULT_COMM]th))
  \\ ASM_SIMP_TAC std_ss []);

val w2w_OVER_ARITH_n2w_LEMMA1 = w2w_OVER_ARITH
    |> Q.SPECL [`n2w n`,`w`]
    |> DISCH ``n < dimword (:'a)``
    |> SIMP_RULE std_ss [w2w_def,w2n_n2w]
    |> SIMP_RULE std_ss [GSYM w2w_def,AND_IMP_INTRO]
    |> UNDISCH

val w2w_OVER_ARITH_n2w_LEMMA2 = w2w_OVER_ARITH
    |> Q.SPECL [`w`,`n2w n`]
    |> DISCH ``n < dimword (:'a)``
    |> SIMP_RULE std_ss [w2w_def,w2n_n2w]
    |> SIMP_RULE std_ss [GSYM w2w_def,AND_IMP_INTRO]
    |> UNDISCH

val w2w_OVER_ARITH_n2w = CONJ w2w_OVER_ARITH_n2w_LEMMA1 w2w_OVER_ARITH_n2w_LEMMA2
    |> DISCH_ALL
    |> RW [GSYM CONJ_ASSOC]

val _ = save_thm("w2w_OVER_ARITH_n2w",w2w_OVER_ARITH_n2w);

val ALIGNED64 = store_thm("ALIGNED64",
  ``!w n. ((0x0w = w && 0x3w) = (w && 0x3w = 0w)) /\
          ((0x3w && w = 0w) = (w && 0x3w = 0w)) /\
          ((4w + w && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w + 4w && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w - 4w && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w + n2w (8 * n) && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w + n2w (4 * n) && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w - n2w (8 * n) && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((w - n2w (4 * n) && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((n2w (8 * n) + w && 0x3w = 0w) = (w && 0x3w = 0w:word64)) /\
          ((n2w (4 * n) + w && 0x3w = 0w) = (w && 0x3w = 0w:word64))``,
  NTAC 2 STRIP_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
  \\ Q.SPEC_TAC (`(n2w n):word64`,`v`) \\ blastLib.BBLAST_TAC);

val SIGN_EXTEND_IGNORE = store_thm("SIGN_EXTEND_IGNORE",
  ``SIGN_EXTEND 8 64 (w2n imm8) MOD 256 = w2n (imm8:word8)``,
  Cases_on `imm8` \\ SRW_TAC [] [SIGN_EXTEND_def,LET_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ IMP_RES_TAC MOD_MULT
  \\ ASM_REWRITE_TAC [GSYM (EVAL ``72057594037927935 * 256``)]);


(* ----------------------------------------------------------------------------- *)
(* SPEC_1 introduction                                                           *)
(* ----------------------------------------------------------------------------- *)

local
  val lemma =
    SPEC_IMP_SPEC_1 |> Q.GEN `model`
    |> ISPEC ``X64_MODEL``
    |> SIMP_RULE std_ss [X64_MODEL_def,LET_DEF]
    |> RW [GSYM X64_MODEL_def]
    |> Q.INST [`pre`|->`zPC pc1 * p`,`post`|->`zPC pc2 * q`]
    |> RW [AND_IMP_INTRO] |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO]
  val goal = lemma |> concl |> dest_imp |> fst
  val lemma2 = prove(
    ``pc1 <> pc2:word64 ==> ^goal``,
    FULL_SIMP_TAC std_ss [SEP_REFINE_def,x64_2set_def,PULL_EXISTS,
      GSYM STAR_ASSOC,FORALL_PROD,STAR_x64_2set,X64_ICACHE_def]
    \\ SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,n2w_11]);
in
  val X64_SPEC_IMP_SPEC_1 = save_thm("X64_SPEC_IMP_SPEC_1",
    MATCH_MP lemma (lemma2 |> UNDISCH) |> DISCH_ALL
    |> RW [AND_IMP_INTRO] |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO]
    |> RW1 [STAR_COMM]);
end;

val _ = export_theory();
