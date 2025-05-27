
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory;

open set_sepTheory progTheory x86_Theory x86_seq_monadTheory x86_icacheTheory;

val _ = new_theory "prog_x86";
val _ = ParseExtras.temp_loose_equality()

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The x86 set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  x86_el =  xReg of Xreg => word32
          | xStatus of Xeflags => bool option
          | xEIP of word32
          | xMem of word32 => ((word8 # x86_permission set) option) => bool `;

val x86_el_11 = DB.fetch "-" "x86_el_11";
val x86_el_distinct = DB.fetch "-" "x86_el_distinct";

val _ = Parse.type_abbrev("x86_set",``:x86_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from x86-state tuple to x86_set                                    *)
(* ----------------------------------------------------------------------------- *)

val x86_2set'_def = Define `
  x86_2set' (rs,st,ep,ms) (r,e,s,m,i) =
    IMAGE (\a. xReg a (r a)) rs UNION
    IMAGE (\a. xStatus a (s a)) st UNION
    (if ep then {xEIP e} else {}) UNION
    IMAGE (\a. xMem a (m a) (X86_ACCURATE a (r,e,s,m,i))) ms`;

val x86_2set_def   = Define `x86_2set s = x86_2set' (UNIV,UNIV,T,UNIV) s`;
val x86_2set''_def = Define `x86_2set'' x s = x86_2set s DIFF x86_2set' x s`;

(* theorems *)

val x86_2set'_SUBSET_x86_2set = prove(
  ``!y s. x86_2set' y s SUBSET x86_2set s``,
  STRIP_TAC \\ STRIP_TAC
  \\ `?rs st ep ms. y = (rs,st,ep,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SUBSET_DEF,x86_2set'_def,x86_2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_x86_2set = prove(
  ``!x s. SPLIT (x86_2set s) (x86_2set' x s, x86_2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,x86_2set''_def]
  \\ `x86_2set' x s SUBSET x86_2set s` by METIS_TAC [x86_2set'_SUBSET_x86_2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``;

val SUBSET_x86_2set = prove(
  ``!u s. u SUBSET x86_2set s = ?y. u = x86_2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [x86_2set'_SUBSET_x86_2set]
  \\ Q.EXISTS_TAC `({ a | a| ?x. xReg a x IN u },{ a | a| ?x. xStatus a x IN u },
                    (?x. xEIP x IN u),{ a | a| ?x y. xMem a x y IN u })`
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [x86_2set'_def,x86_2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [x86_el_11,x86_el_distinct]
  \\ FULL_SIMP_TAC std_ss [PUSH_IN_INTO_IF,NOT_IN_EMPTY,IN_INSERT]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [x86_el_11,x86_el_distinct]
  \\ METIS_TAC []);

val SPLIT_x86_2set_EXISTS = prove(
  ``!s u v. SPLIT (x86_2set s) (u,v) = ?y. (u = x86_2set' y s) /\ (v = x86_2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_x86_2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,x86_2set'_def,x86_2set''_def]
  \\ `u SUBSET (x86_2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_x86_2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val X86_GET_MEMORY_def = Define `X86_GET_MEMORY (r,e,t,m,i) = m`;

val IN_x86_2set = prove(``
  (!r x s. xReg r x IN (x86_2set s) = (x = XREAD_REG r s)) /\
  (!r x s. xReg r x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_REG r s) /\ r IN rs) /\
  (!r x s. xReg r x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_REG r s) /\ ~(r IN rs)) /\
  (!a x s. xStatus a x IN (x86_2set s) = (x = XREAD_EFLAG a s)) /\
  (!a x s. xStatus a x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_EFLAG a s) /\ a IN st) /\
  (!a x s. xStatus a x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_EFLAG a s) /\ ~(a IN st)) /\
  (!x s. xEIP x IN (x86_2set s) = (x = XREAD_EIP s)) /\
  (!x s. xEIP x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_EIP s) /\ e) /\
  (!x s. xEIP x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_EIP s) /\ ~e) /\
  (!p x y s. xMem p x y IN (x86_2set s) = (X86_GET_MEMORY s p = x) /\ (y = X86_ACCURATE p s)) /\
  (!p x y s. xMem p x y IN (x86_2set' (rs,st,e,ms) s) = (X86_GET_MEMORY s p = x) /\ (y = X86_ACCURATE p s) /\ p IN ms) /\
  (!p x y s. xMem p x y IN (x86_2set'' (rs,st,e,ms) s) = (X86_GET_MEMORY s p = x) /\ (y = X86_ACCURATE p s) /\ ~(p IN ms))``,
  REPEAT STRIP_TAC
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR] \\ ASM_SIMP_TAC std_ss []
  \\ SRW_TAC [] [x86_2set'_def,x86_2set''_def,x86_2set_def,IN_UNION,
       IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF,XREAD_REG_def,
       XREAD_EIP_def,XREAD_EFLAG_def,X86_GET_MEMORY_def]
  \\ METIS_TAC []);

val x86_2set''_11 = prove(
  ``!y y2 s s2. (x86_2set'' y2 s2 = x86_2set'' y s) ==> (y = y2)``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?rs st ep m st. y = (rs,st,ep,m)` by METIS_TAC [PAIR]
  \\ `?rs2 st2 ep2 m2. y2 = (rs2,st2,ep2,m2)` by METIS_TAC [PAIR]
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ `?r2 e2 t2 m2 i2. s2 = (r2,e2,t2,m2,i2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ,EXTENSION,Excl "lift_disj_eq"]
  THEN1
   (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.SPEC `xReg xi yi`)
    \\ FULL_SIMP_TAC std_ss [IN_x86_2set] \\ METIS_TAC [])
  THEN1
   (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.SPEC `xStatus xi yi`)
    \\ FULL_SIMP_TAC std_ss [IN_x86_2set] \\ METIS_TAC [])
  THEN1
   (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `ei` o Q.SPEC `xEIP ei`)
    \\ FULL_SIMP_TAC std_ss [IN_x86_2set] \\ METIS_TAC [])
  THEN
   (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.GEN `xi` o Q.GEN `yi` o Q.GEN `zi` o Q.SPEC `xMem xi yi zi`)
    \\ FULL_SIMP_TAC std_ss [IN_x86_2set] \\ METIS_TAC []));

val DELETE_x86_2set = prove(``
  (!a. (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE xReg a (r a) =
       (x86_2set' (rs DELETE a,st,ei,ms) (r,e,s,m,i))) /\
  (!c. (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE xStatus c (s c) =
       (x86_2set' (rs,st DELETE c,ei,ms) (r,e,s,m,i))) /\
  (!c. (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE xEIP e =
       (x86_2set' (rs,st,F,ms) (r,e,s,m,i))) /\
  (!b. (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) DELETE xMem b (m b) (X86_ACCURATE b (r,e,s,m,i)) =
       (x86_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i)))``,
  REPEAT STRIP_TAC
  \\ SRW_TAC [] [x86_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
       EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF,
       XREAD_REG_def,XREAD_MEM_def,XREAD_EFLAG_def,XREAD_EIP_def]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_x86_2set = prove(``
  (x86_2set' (rs,st,e,ms) s = {}) = (rs = {}) /\ (ms = {}) /\ (st = {}) /\ ~e``,
  REPEAT STRIP_TAC
  \\ `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR] \\ ASM_SIMP_TAC std_ss []
  \\ SRW_TAC [] [x86_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
       EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ SIMP_TAC std_ss [x86_el_distinct,x86_el_11] \\ METIS_TAC [PAIR,FST]);


(* ----------------------------------------------------------------------------- *)
(* Defining the X86_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val xR_def = Define `xR a x = SEP_EQ {xReg a x}`;
val xM1_def = Define `xM1 a x b = SEP_EQ {xMem a x b}`;
val xS1_def = Define `xS1 a x = SEP_EQ {xStatus a x}`;
val xPC_def = Define `xPC x = SEP_EQ {xEIP x}`;

val xS_def = Define `
  xS (x0,x1,x2,x3,x4,x5) =
    xS1 X_CF x0 * xS1 X_PF x1 * xS1 X_AF x2 *
    xS1 X_ZF x3 * xS1 X_SF x4 * xS1 X_OF x5`;

val X86_INSTR_PERM_def = Define `
  X86_INSTR_PERM b = {Xread;Xexecute} UNION (if b then {Xwrite} else {})`;

val X86_INSTR_def    = Define `
  (X86_INSTR (a,([],b)) = {}) /\
  (X86_INSTR (a,((c:word8)::cs,b)) =
     xMem a (SOME (c,X86_INSTR_PERM b)) T INSERT X86_INSTR (a+1w,(cs,b)))`;

val X86_MODEL_def = Define `
  X86_MODEL = (x86_2set, X86_NEXT_REL, X86_INSTR, X86_ICACHE,
               (K F):x86_state->bool)`;

val xCODE_def = Define `xCODE = CODE_POOL X86_INSTR`;

val xM_def = Define `
  xM a (w:word32) =
    ~xM1 a        (SOME ((7 >< 0) w,{Xread;Xwrite})) *
    ~xM1 (a + 1w) (SOME ((7 >< 0) (w >> 8),{Xread;Xwrite})) *
    ~xM1 (a + 2w) (SOME ((7 >< 0) (w >> 16),{Xread;Xwrite})) *
    ~xM1 (a + 3w) (SOME ((7 >< 0) (w >> 24),{Xread;Xwrite}))`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_x86_2set]
  ``p (x86_2set' y s) ==> (?u v. SPLIT (x86_2set s) (u,v) /\ p u /\ (\v. v = x86_2set'' y s) v)``;

val X86_SPEC_SEMANTICS = store_thm("X86_SPEC_SEMANTICS",
  ``SPEC X86_MODEL p {} q =
    !y s t1 seq.
      p (x86_2set' y t1) /\ X86_ICACHE t1 s /\ rel_sequence X86_NEXT_REL seq s ==>
      ?k t2. q (x86_2set' y t2) /\ X86_ICACHE t2 (seq k) /\ (x86_2set'' y t1 = x86_2set'' y t2)``,
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,X86_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC bool_ss [SPLIT_x86_2set_EXISTS]
    \\ NTAC 3 (POP_ASSUM MP_TAC) \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ Q.EXISTS_TAC `k` \\ Q.EXISTS_TAC `t2`
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [],
    FULL_SIMP_TAC std_ss [METIS_PROVE [] ``((?x. P x) ==> b) = !x. P x ==> b``,
                          METIS_PROVE [] ``(b /\ (?x. P x)) = ?x. b /\ P x``]
    \\ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
    \\ IMP_RES_TAC lemma \\ RES_TAC
    \\ FULL_SIMP_TAC bool_ss [SPLIT_x86_2set_EXISTS]
    \\ IMP_RES_TAC x86_2set''_11 \\ METIS_TAC []]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC X86_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_x86_2set = store_thm("STAR_x86_2set",
  ``((xR a x * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (x = r a) /\ a IN rs /\ p (x86_2set' (rs DELETE a,st,ei,ms) (r,e,s,m,i))) /\
    ((xS1 c z * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (z = s c) /\ c IN st /\ p (x86_2set' (rs,st DELETE c,ei,ms) (r,e,s,m,i))) /\
    ((xPC q * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (q = e) /\ ei /\ p (x86_2set' (rs,st,F,ms) (r,e,s,m,i))) /\
    ((xM1 b y w * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (y = m b) /\ (w = X86_ACCURATE b (r,e,s,m,i)) /\ b IN ms /\ p (x86_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i))) /\
    ((~(xM1 b y) * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      (y = m b) /\ b IN ms /\ p (x86_2set' (rs,st,ei,ms DELETE b) (r,e,s,m,i))) /\
    ((cond g * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)) =
      g /\ p (x86_2set' (rs,st,ei,ms) (r,e,s,m,i)))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ SIMP_TAC std_ss [xR_def,xS1_def,xM1_def,EQ_STAR,INSERT_SUBSET,cond_STAR,xPC_def,XREAD_EIP_def,
       EMPTY_SUBSET,IN_x86_2set,XREAD_REG_def,XREAD_EFLAG_def,XREAD_MEM_def,GSYM DELETE_DEF,X86_GET_MEMORY_def]
  THEN1 METIS_TAC [DELETE_x86_2set]
  THEN1 METIS_TAC [DELETE_x86_2set]
  THEN1 METIS_TAC [DELETE_x86_2set]
  \\ Cases_on `y = m b` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `w = X86_ACCURATE b (r,e,s,m,i)`
  \\ ASM_SIMP_TAC std_ss [DELETE_x86_2set,AC CONJ_ASSOC CONJ_COMM]);

val CODE_POOL_x86_2set_AUX_LEMMA = prove(
  ``!x y z. ~(z IN y) ==> ((x = z INSERT y) = z IN x /\ (x DELETE z = y))``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DELETE] \\ METIS_TAC []);

val address_list_def = Define `
  (address_list a 0 = {}) /\
  (address_list a (SUC n) = a INSERT address_list (a+1w) n)`;

val x86_pool_def = Define `
  (x86_pool (r,s,e,m,i) p ([],d) = T) /\
  (x86_pool (r,s,e,m,i) p ((c::cs),d) =
     (SOME (c:word8,X86_INSTR_PERM d) = m p) /\ X86_ACCURATE p (r,s,e,m,i) /\
     x86_pool (r,s,e,m,i) (p+1w) (cs,d))`;

val LEMMA1 = prove(
  ``!p q cs y b. xMem p y b IN X86_INSTR (q,(cs,d)) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs`
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x86_el_11,n2w_11]
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val LEMMA2 = prove(
  ``!p q cs. p IN address_list q (LENGTH cs) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs`
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x86_el_11,n2w_11]
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val CODE_POOL_x86_2set_LEMMA = prove(
  ``!cs p ms.
      LENGTH cs < 5000 ==>
      (xCODE {(p,(cs,d))} (x86_2set' (rs,st,ei,ms) (r,s,e,m,i)) =
       (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\
       x86_pool (r,s,e,m,i) p (cs,d))``,
  Induct
  \\ FULL_SIMP_TAC bool_ss [INSERT_SUBSET,GSYM DELETE_DEF,
      LENGTH,x86_pool_def, EMPTY_SUBSET,xCODE_def,
      IN_DELETE, IMAGE_INSERT, CODE_POOL_def, IMAGE_EMPTY,
      XREAD_MEM_def, address_list_def, BIGUNION_INSERT, BIGUNION_EMPTY,
      UNION_EMPTY, X86_INSTR_def, IN_x86_2set, EMPTY_x86_2set]
  THEN1 METIS_TAC []
  \\ REPEAT STRIP_TAC
  \\ `LENGTH cs < 5000` by DECIDE_TAC
  \\ Cases_on `xMem p (SOME (h,X86_INSTR_PERM d)) T IN X86_INSTR (p + 1w,(cs,d))`
  THEN1 (IMP_RES_TAC LEMMA1
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ Cases_on `p IN address_list (p + 1w) (LENGTH cs)`
  THEN1 (IMP_RES_TAC LEMMA2
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ ASM_SIMP_TAC bool_ss [CODE_POOL_x86_2set_AUX_LEMMA,GSYM CONJ_ASSOC,IN_x86_2set,XREAD_MEM_def]
  \\ Cases_on `SOME (h,X86_INSTR_PERM d) = m p` \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_x86_2set,X86_GET_MEMORY_def]
  \\ Cases_on `X86_ACCURATE p (r,s,e,m,i)` \\ ASM_SIMP_TAC std_ss []
  \\ `xMem p (m p) T = xMem p (m p) (X86_ACCURATE p (r,s,e,m,i))` by
       FULL_SIMP_TAC std_ss [x86_el_11]
  \\ ONCE_ASM_REWRITE_TAC [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_x86_2set,X86_GET_MEMORY_def]
  \\ Cases_on `p IN ms` \\ ASM_REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ FULL_SIMP_TAC bool_ss []);

val CODE_POOL_x86_2set = store_thm("CODE_POOL_x86_2set",
  ``!cs p ms.
      xCODE {(p,(cs,d))} (x86_2set' (rs,st,ei,ms) (r,s,e,m,i)) =
      if LENGTH cs < 5000 then
        (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\
        x86_pool (r,s,e,m,i) p (cs,d)
      else xCODE {(p,(cs,d))} (x86_2set' (rs,st,ei,ms) (r,s,e,m,i))``,
  METIS_TAC [CODE_POOL_x86_2set_LEMMA]);

val icache_revert_def = Define `
  icache_revert (m1:x86_memory,i1:x86_memory) (m2:x86_memory,i2:x86_memory) a =
    if m1 a = m2 a then i1 a else i2 a`;

val X86_ACCURATE_UPDATE = store_thm("X86_ACCURATE_UPDATE",
  ``(X86_ACCURATE a ((xr =+ yr) r,e,s,m,i) = X86_ACCURATE a (r,e,s,m,i)) /\
    (X86_ACCURATE a (r,xe,s,m,i) = X86_ACCURATE a (r,e,s,m,i)) /\
    (X86_ACCURATE a (r,e,(xs =+ ys) s,m,i) = X86_ACCURATE a (r,e,s,m,i)) /\
    (~(xm = a) ==> (X86_ACCURATE a (r,e,s,(xm =+ ym) m,i) = X86_ACCURATE a (r,e,s,m,i))) /\
    (~(a = b) ==>
       (X86_ACCURATE a (r,e,s,m,icache_revert (m,i) ((b =+ w) m2,i2)) =
        X86_ACCURATE a (r,e,s,m,icache_revert (m,i) (m2,i2))))``,
  SIMP_TAC std_ss [X86_ACCURATE_def,APPLY_UPDATE_THM,icache_revert_def]);

val icache_revert_ID = store_thm("icache_revert_ID",
  ``!m i y. icache_revert (m,i) (m,y) = i``,
  SIMP_TAC std_ss [FUN_EQ_THM,icache_revert_def]);

val icache_revert_update = prove(
  ``b IN ms ==>
    (x86_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) ((b =+ w) m2,j)) =
     x86_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) (m2,j)))``,
  SIMP_TAC std_ss [EXTENSION] \\ STRIP_TAC \\ Cases
  \\ SIMP_TAC std_ss [IN_x86_2set,XREAD_REG_def,XREAD_EFLAG_def,APPLY_UPDATE_THM,
       XREAD_EIP_def,X86_GET_MEMORY_def,X86_ACCURATE_def,icache_revert_def]
  \\ METIS_TAC []);

val UPDATE_x86_2set'' = store_thm("UPDATE_x86_2set''",
  ``(!a x. a IN rs ==>
      (x86_2set'' (rs,st,ei,ms) ((a =+ x) r,e,s,m,i) = x86_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x. a IN st ==>
      (x86_2set'' (rs,st,ei,ms) (r,e,(a =+ x) s,m,i) = x86_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x y.
      ((x86_2set'' (rs,st,T,ms) (r,x,s,m,i) = x86_2set'' (rs,st,T,ms) (r,y,s,m,i)) = T)) /\
    (!a x. a IN ms ==>
      (x86_2set'' (rs,st,ei,ms) (r,e,s,(a =+ x) m,i) = x86_2set'' (rs,st,ei,ms) (r,e,s,m,i))) /\
    (!a x. a IN ms ==>
      (x86_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) ((a =+ w) m2,j)) =
       x86_2set'' (rs,st,ei,ms) (r,x,t,m, icache_revert (m,i) (m2,j))))``,
  SIMP_TAC std_ss [x86_2set_def,x86_2set''_def,x86_2set'_def,EXTENSION,IN_UNION,
       IN_INSERT,NOT_IN_EMPTY,IN_IMAGE,IN_DIFF,IN_UNIV,XREAD_REG_def,XREAD_MEM_def,
       XREAD_EFLAG_def,APPLY_UPDATE_THM,XREAD_EIP_def,icache_revert_update]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [X86_ACCURATE_UPDATE]
  \\ METIS_TAC [X86_ACCURATE_UPDATE]);

val X86_SPEC_CODE = save_thm("X86_SPEC_CODE",
  RW [GSYM X86_MODEL_def,GSYM xCODE_def]
  (SIMP_RULE std_ss [X86_MODEL_def] (Q.ISPEC `X86_MODEL` SPEC_CODE)));

val IMP_X86_SPEC_LEMMA = prove(
  ``!p q.
      (!y s t1.
         p (x86_2set' y t1) /\ X86_ICACHE t1 s ==>
         ?v t2.
           p (x86_2set' y s) /\
           (X86_NEXT s = SOME v) /\ q (x86_2set' y t2) /\ X86_ICACHE t2 v /\
           (x86_2set'' y t1 = x86_2set'' y t2)) ==>
      SPEC X86_MODEL p {} q``,
  REWRITE_TAC [X86_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC
  \\ `p (x86_2set' y s)` by METIS_TAC []
  \\ `X86_NEXT_REL (seq 0) (seq (SUC 0))` by
   (`?x. X86_NEXT_REL (seq 0) x` by
      (RES_TAC \\ Q.EXISTS_TAC `v'`
       \\ ASM_SIMP_TAC std_ss [X86_NEXT_REL_def]
       \\ Q.EXISTS_TAC `seq 0` \\ ASM_SIMP_TAC std_ss []
       \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,X86_ICACHE_REFL])
    \\ METIS_TAC [rel_sequence_def])
  \\ FULL_SIMP_TAC std_ss [X86_NEXT_REL_def]
  \\ `seq 0 = s` by FULL_SIMP_TAC std_ss [rel_sequence_def]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `1`
  \\ `X86_ICACHE t1 u` by IMP_RES_TAC X86_ICACHE_TRANS
  \\ Q.PAT_ASSUM `!y s t1. bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o
       RW [GSYM AND_IMP_INTRO] o Q.SPECL [`y`,`u`,`t1`])
  \\ Q.EXISTS_TAC `t2`
  \\ FULL_SIMP_TAC std_ss [optionTheory.SOME_11] \\ METIS_TAC []);

val X86_ICACHE_EXTRACT_def = Define `
  X86_ICACHE_EXTRACT ((r1,e1,s1,m1,i1):x86_state) = i1`;

val X86_ICACHE_THM2 = prove(
  ``!s t. X86_ICACHE s t = ?z. t = X86_ICACHE_UPDATE z s``,
  REPEAT STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. s = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ `?r2 e2 s2 m2 i2. t = (r2,e2,s2,m2,i2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X86_ICACHE_UPDATE_def,X86_ICACHE_THM]);

val X86_ICACHE_X86_ACCURATE = prove(
  ``X86_ICACHE (r1,e1,s1,m1,i1) (r1,e1,s1,m1,i2) =
    !a. X86_ACCURATE a (r1,e1,s1,m1,i2) \/ (i1 a = i2 a)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [X86_ACCURATE_def,X86_ICACHE_def,FUN_EQ_THM]
         \\ Cases_on `a IN insert` \\ ASM_SIMP_TAC std_ss []
         \\ Cases_on `a IN delete` \\ ASM_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [X86_ICACHE_def,FUN_EQ_THM]
  \\ Q.EXISTS_TAC `{ a | X86_ACCURATE a (r1,e1,s1,m1,i2) /\ ~(i2 a = NONE) }`
  \\ Q.EXISTS_TAC `{ a | X86_ACCURATE a (r1,e1,s1,m1,i2) /\ (i2 a = NONE) }`
  \\ SIMP_TAC std_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `addr`)
  \\ Cases_on `X86_ACCURATE addr (r1,e1,s1,m1,i2)`
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [X86_ACCURATE_def] \\ METIS_TAC []);

val X86_ICACHE_icache_revert = prove(
  ``X86_ICACHE (r1,e1,s1,m1,i1) (r1,e1,s1,m1,i2) ==>
    X86_ICACHE (r2,e2,s2,m2,icache_revert (m1,i1) (m2,i2)) (r2,e2,s2,m2,i2)``,
  SIMP_TAC std_ss [X86_ICACHE_X86_ACCURATE] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `a`)
  \\ FULL_SIMP_TAC std_ss [X86_ACCURATE_def,icache_revert_def]
  \\ Cases_on `m1 a = m2 a` \\ ASM_SIMP_TAC std_ss []);

val X86_ICACHE_REVERT_def = Define `
  X86_ICACHE_REVERT (r2,e2,s2,m2,i2) (r1,e1,s1,m1,i1) =
    (r2,e2,s2,m2,icache_revert (m1,i1) (m2,i2))`;

val X86_ICACHE_X86_ICACHE_REVERT = store_thm("X86_ICACHE_X86_ICACHE_REVERT",
  ``!s t u. X86_ICACHE s t /\ (X86_ICACHE_EXTRACT t = X86_ICACHE_EXTRACT u) ==>
            X86_ICACHE (X86_ICACHE_REVERT u s) u``,
  NTAC 3 STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. s = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ `?r2 e2 s2 m2 i2. t = (r2,e2,s2,m2,i2)` by METIS_TAC [PAIR]
  \\ `?r3 e3 s3 m3 i3. u = (r3,e3,s3,m3,i3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X86_ICACHE_REVERT_def,X86_ICACHE_EXTRACT_def]
  \\ REPEAT STRIP_TAC
  \\ `(r1,e1,s1,m1) = (r2,e2,s2,m2)` by FULL_SIMP_TAC std_ss [X86_ICACHE_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [X86_ICACHE_icache_revert]);

val X86_ICACHE_EXTRACT_CLAUSES = store_thm("X86_ICACHE_EXTRACT_CLAUSES",
  ``!s r w f fv.
      (X86_ICACHE_EXTRACT (XWRITE_EIP w s) = X86_ICACHE_EXTRACT s) /\
      (X86_ICACHE_EXTRACT (XWRITE_REG r w s) = X86_ICACHE_EXTRACT s) /\
      (X86_ICACHE_EXTRACT (XWRITE_EFLAG f fv s) = X86_ICACHE_EXTRACT s)``,
  REPEAT STRIP_TAC
  THEN `?r e t m i. s = (r,e,t,m,i)` by METIS_TAC [PAIR]
  THEN ASM_SIMP_TAC std_ss [X86_ICACHE_EXTRACT_def,XWRITE_EIP_def,
          XWRITE_REG_def,XWRITE_EFLAG_def]);

val X86_ACCURATE_CLAUSES = store_thm("X86_ACCURATE_CLAUSES",
  ``(X86_ACCURATE a ((r =+ w) x,e,s,m,i) = X86_ACCURATE a (x,e,s,m,i)) /\
    (X86_ACCURATE a (x,e,(f =+ fv) s,m,i) = X86_ACCURATE a (x,e,s,m,i)) /\
    (~(b = a) ==> (X86_ACCURATE a (x,e,s,(b =+ v) m,i) = X86_ACCURATE a (x,e,s,m,i)))``,
  SIMP_TAC std_ss [X86_ACCURATE_def,APPLY_UPDATE_THM]);

val X86_ACCURATE_IMP = store_thm("X86_ACCURATE_IMP",
  ``X86_ACCURATE a (r,e2,t,m,i) ==>
    X86_ACCURATE a (r,e1,t,m,icache_revert (m,i) (m,icache x m i)) /\
    X86_ACCURATE a (r,e1,t,m,icache x m i) /\
    X86_ACCURATE a (r,e1,t,m,i)``,
  Cases_on `x` THEN SIMP_TAC std_ss [X86_ACCURATE_def,icache_revert_def,icache_def]
  THEN METIS_TAC []);

val XREAD_INSTR_IMP = store_thm("XREAD_INSTR_IMP",
  ``!x r e t i m a w p.
      (m a = SOME (w,X86_INSTR_PERM p)) /\ X86_ACCURATE a (r,e,t,m,i) ==>
      (XREAD_INSTR a (r,e,t,m,icache x m i) = SOME w)``,
  Cases THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [X86_ACCURATE_def,icache_def,XREAD_INSTR_def]
  THEN Cases_on `a IN q` \\ ASM_SIMP_TAC std_ss []
  THEN Cases_on `a IN r` \\ ASM_SIMP_TAC (srw_ss()) []
  THEN Cases_on `p` \\ ASM_SIMP_TAC (srw_ss()) [X86_INSTR_PERM_def]);

val X86_ICACHE_REVERT_EMPTY = prove(
  ``(X86_ICACHE_EXTRACT v = X86_ICACHE_EMPTY) ==>
    X86_ICACHE (X86_ICACHE_REVERT v (r,e,t,m,i)) v``,
  REPEAT STRIP_TAC
  \\ `?r1 e1 s1 m1 i1. v = (r1,e1,s1,m1,i1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [X86_ICACHE_REVERT_def,X86_ICACHE_EXTRACT_def]
  \\ FULL_SIMP_TAC std_ss [X86_ICACHE_def]
  \\ Q.EXISTS_TAC `{}` \\ Q.EXISTS_TAC `UNIV`
  \\ SIMP_TAC std_ss [NOT_IN_EMPTY,IN_UNIV,X86_ICACHE_EMPTY_def]);

val IMP_X86_SPEC_LEMMA2 = prove(
  ``!p q.
      (!rs st ei ms x r e t m i.
         p (x86_2set' (rs,st,ei,ms) (r,e,t,m,i)) ==>
         ?v.
           (X86_NEXT (X86_ICACHE_UPDATE x (r,e,t,m,i)) = SOME v) /\
           ((X86_ICACHE_EXTRACT v = X86_ICACHE_EMPTY) \/
            (X86_ICACHE_EXTRACT (X86_ICACHE_UPDATE x (r,e,t,m,i)) = X86_ICACHE_EXTRACT v)) /\
           p (x86_2set' (rs,st,ei,ms) (X86_ICACHE_UPDATE x (r,e,t,m,i))) /\
           q (x86_2set' (rs,st,ei,ms) (X86_ICACHE_REVERT v (r,e,t,m,i))) /\
           (x86_2set'' (rs,st,ei,ms) (r,e,t,m,i) =
            x86_2set'' (rs,st,ei,ms) (X86_ICACHE_REVERT v (r,e,t,m,i)))) ==>
      SPEC X86_MODEL p {} q``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_X86_SPEC_LEMMA
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC X86_ICACHE_THM2
  \\ ASM_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. t1 = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!rs.bb` (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`rs`,`st`,`ei`,`ms`,`z`,`r`,`e`,`t`,`m`,`i`])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(X86_ICACHE_REVERT v (r,e,t,m,i))`
  \\ FULL_SIMP_TAC std_ss []
  THEN1 (METIS_TAC [X86_ICACHE_REVERT_EMPTY])
  \\ MATCH_MP_TAC X86_ICACHE_X86_ICACHE_REVERT
  \\ Q.EXISTS_TAC `(X86_ICACHE_UPDATE z (r,e,t,m,i))` \\ ASM_SIMP_TAC std_ss []);

val IMP_X86_SPEC = save_thm("IMP_X86_SPEC",
  (RW1 [STAR_COMM] o RW [X86_SPEC_CODE,GSYM xCODE_def] o
   SPECL [``CODE_POOL X86_INSTR {(eip,c)} * p``,
          ``CODE_POOL X86_INSTR {(eip,c)} * q``]) IMP_X86_SPEC_LEMMA2);

val xS_HIDE = store_thm("xS_HIDE",
  ``~xS = ~xS1 X_CF * ~xS1 X_PF * ~xS1 X_AF * ~xS1 X_ZF * ~xS1 X_SF * ~xS1 X_OF``,
  SIMP_TAC std_ss [SEP_HIDE_def,xS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [xS_def,PAIR]);


(* ----------------------------------------------------------------------------- *)
(* Byte-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val xDATA_PERM_def = Define `
  xDATA_PERM exec = if exec then {Xread;Xwrite;Xexecute} else {Xread;Xwrite}`;

val xBYTE_MEMORY_ANY_SET_def = Define `
  xBYTE_MEMORY_ANY_SET df f exec c =
    { xMem a (SOME (f a, xDATA_PERM exec)) (c a) | a | a IN df }`;

val xBYTE_MEMORY_ANY_C_def = Define `
  xBYTE_MEMORY_ANY_C exec df f c = SEP_EQ (xBYTE_MEMORY_ANY_SET df f exec c)`;

val xBYTE_MEMORY_ANY_def = Define `
  xBYTE_MEMORY_ANY exec df f =
    SEP_EXISTS c. SEP_EQ (xBYTE_MEMORY_ANY_SET df f exec c)`;

val xBYTE_MEMORY_def = Define `xBYTE_MEMORY = xBYTE_MEMORY_ANY F`;
val xBYTE_MEMORY_X_def = Define `xBYTE_MEMORY_X = xBYTE_MEMORY_ANY T`;

val IN_xDATA_PERM = store_thm("IN_xDATA_PERM",
  ``(Xread IN xDATA_PERM exec) /\
    (Xwrite IN xDATA_PERM exec) /\
    (Xexecute IN xDATA_PERM exec = exec)``,
  Cases_on `exec` \\ SRW_TAC [] [xDATA_PERM_def,IN_INSERT,NOT_IN_EMPTY]);

val IN_xBYTE_MEMORY_ANY_SET = prove(
  ``a IN df ==>
    (xBYTE_MEMORY_ANY_SET df g exec c =
     (xMem a (SOME (g a, xDATA_PERM exec))) (c a) INSERT
     xBYTE_MEMORY_ANY_SET (df DELETE a) g exec c)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,xBYTE_MEMORY_ANY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_xBYTE_MEMORY_ANY_SET = prove(
  ``xBYTE_MEMORY_ANY_SET (df DELETE a) ((a =+ w) g) exec ((a =+ b) c) =
    xBYTE_MEMORY_ANY_SET (df DELETE a) g exec c``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,xBYTE_MEMORY_ANY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val xBYTE_MEMORY_ANY_C_INSERT = prove(
  ``a IN df ==>
    (xBYTE_MEMORY_ANY_C e df ((a =+ w) g) ((a =+ b) c) =
     xM1 a (SOME (w,xDATA_PERM e)) b * xBYTE_MEMORY_ANY_C e (df DELETE a) g c)``,
  SIMP_TAC std_ss [xM1_def,xBYTE_MEMORY_ANY_C_def,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_xBYTE_MEMORY_ANY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_xBYTE_MEMORY_ANY_SET,APPLY_UPDATE_THM]
  \\ sg `~(xMem a (SOME (w,xDATA_PERM e)) b IN xBYTE_MEMORY_ANY_SET (df DELETE a) g e c)`
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_ANY_SET_def,GSPECIFICATION,IN_DELETE,x86_el_11]
  \\ FULL_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_SET_def,EXTENSION,GSPECIFICATION,IN_DELETE,IN_INSERT]
  \\ METIS_TAC []);

val xBYTE_MEMORY_ANY_INSERT = store_thm("xBYTE_MEMORY_ANY_INSERT",
  ``a IN df ==>
    (xBYTE_MEMORY_ANY e df ((a =+ w) g) =
     ~xM1 a (SOME (w,xDATA_PERM e)) * xBYTE_MEMORY_ANY e (df DELETE a) g)``,
  SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,GSYM xBYTE_MEMORY_ANY_C_def]
    \\ `(y = (a =+ y a) y)` by SIMP_TAC std_ss [APPLY_UPDATE_THM,FUN_EQ_THM]
    \\ Q.PAT_ASSUM `xBYTE_MEMORY_ANY_C e df ((a =+ w) g) y x` MP_TAC
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ ASM_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_C_INSERT]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [],
    FULL_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,GSYM xBYTE_MEMORY_ANY_C_def]
    \\ FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `(a =+ y') y`
    \\ ASM_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_C_INSERT]]);

val xBYTE_MEMORY_ANY_INSERT_SET =
  SIMP_RULE std_ss [IN_INSERT,DELETE_INSERT,APPLY_UPDATE_ID]
  (Q.INST [`df`|->`a INSERT df`,`w`|->`g a`] xBYTE_MEMORY_ANY_INSERT);

val xBYTE_MEMORY_ANY_INTRO = store_thm("xBYTE_MEMORY_ANY_INTRO",
  ``SPEC m (~xM1 a (SOME (v,xDATA_PERM e)) * P) c
           (~xM1 a (SOME (w,xDATA_PERM e)) * Q) ==>
    a IN df ==>
    SPEC m (xBYTE_MEMORY_ANY e df ((a =+ v) f) * P) c
           (xBYTE_MEMORY_ANY e df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_ANY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Word-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val xMEMORY_DOMAIN_def = Define `
  xMEMORY_DOMAIN df = BIGUNION { {b;b+1w;b+2w;b+3w} | ALIGNED b /\ b IN df }`;

val xMEMORY_FUNC_def = Define `
  xMEMORY_FUNC (f:word32->word32) a =
    let w = f (ADDR32 (ADDR30 a)) in
      if a && 3w = 0w then (7 >< 0) (w) else
      if a && 3w = 1w then (7 >< 0) (w >> 8) else
      if a && 3w = 2w then (7 >< 0) (w >> 16) else
      if a && 3w = 3w then (7 >< 0) (w >> 24) else 0w:word8`;

val xMEMORY_def = Define `
  xMEMORY df f = xBYTE_MEMORY (xMEMORY_DOMAIN df) (xMEMORY_FUNC f)`;

val xM_LEMMA = prove(
  ``!w a f. ALIGNED a ==> (xM a w = xMEMORY {a} ((a =+ w) f))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [xM_def,xMEMORY_def,xBYTE_MEMORY_def]
  \\ REPEAT STRIP_TAC
  \\ `xMEMORY_DOMAIN {a} = {a;a+1w;a+2w;a+3w}` by
   (SIMP_TAC std_ss [xMEMORY_DOMAIN_def,IN_INSERT,NOT_IN_EMPTY]
    \\ `{{b; b + 1w; b + 2w; b + 3w} | ALIGNED b /\ (b = a)} =
        {{a; a + 1w; a + 2w; a + 3w}}` by
     (SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_BIGUNION,IN_INSERT,NOT_IN_EMPTY]
      \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [BIGUNION_INSERT,BIGUNION_EMPTY,UNION_EMPTY])
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++SIZES_ss) [xBYTE_MEMORY_ANY_INSERT_SET,DELETE_INSERT,
       WORD_EQ_ADD_CANCEL,n2w_11,EMPTY_DELETE,STAR_ASSOC,xDATA_PERM_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [xMEMORY_FUNC_def,LET_DEF,ALIGNED_add_3_and_3,
       ALIGNED_add_2_and_3,ALIGNED_add_1_and_3,n2w_11,APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ALIGNED_INTRO]
  \\ IMP_RES_TAC (RW [ALIGNED_INTRO] EXISTS_ADDR30)
  \\ FULL_SIMP_TAC std_ss [ADDR30_ADDR32]
  \\ sg `!f. xBYTE_MEMORY_ANY F {} (xMEMORY_FUNC f) = emp`
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,WORD_ADD_0]
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_ANY_def,SEP_EXISTS,SEP_EQ_def]
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_ANY_SET_def,NOT_IN_EMPTY,EXTENSION,GSPECIFICATION,emp_def]);

val xM_THM = store_thm("xM_THM",
  ``!a w f. ALIGNED a ==> (xMEMORY {a} ((a =+ w) f) = xM a w) /\
                          (xMEMORY {a} (\x. w) = xM a w)``,
  SIMP_TAC std_ss [GSYM xM_LEMMA,GSYM (RW [APPLY_UPDATE_ID]
    (Q.SPECL [`(f:word32->word32) a`,`a`,`f`] xM_LEMMA))]);

val xBYTE_MEMORY_ANY_SET_EQ = prove(
  ``xBYTE_MEMORY_ANY_SET df f exec c =
     {xMem d (SOME (f d,xDATA_PERM exec)) (c d) | d IN df}``,
  METIS_TAC [xBYTE_MEMORY_ANY_SET_def]);

val xMEMORY_INSERT = prove(
  ``a IN df /\ ALIGNED a ==>
    (xMEMORY df ((a =+ w) f) = xM a w * xMEMORY (df DELETE a) f)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [xMEMORY_def,xBYTE_MEMORY_def,xM_def,GSYM STAR_ASSOC]
  \\ `xMEMORY_DOMAIN df = a INSERT (a+1w) INSERT (a+2w) INSERT
      (a+3w) INSERT xMEMORY_DOMAIN (df DELETE a)` by
   (FULL_SIMP_TAC std_ss [xMEMORY_DOMAIN_def]
    \\ `{{b; b + 1w; b + 2w; b + 3w} | ALIGNED b /\ b IN df} =
        {a; a + 1w; a + 2w; a + 3w} INSERT
        {{b; b + 1w; b + 2w; b + 3w} | ALIGNED b /\ b IN df DELETE a}` by
      (SIMP_TAC std_ss [EXTENSION,IN_INSERT,
         IN_BIGUNION,GSPECIFICATION,NOT_IN_EMPTY,IN_DELETE]
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
       \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
       \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [BIGUNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY])
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [xBYTE_MEMORY_ANY_INSERT_SET,DELETE_INSERT,
       WORD_EQ_ADD_CANCEL,n2w_11]
  \\ SIMP_TAC std_ss [xMEMORY_FUNC_def,LET_DEF]
  \\ IMP_RES_TAC (GSYM (RW [ALIGNED_INTRO] ADDR32_ADDR30))
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ SIMP_TAC std_ss [ADDR30_ADDR32]
  \\ IMP_RES_TAC ((RW [ALIGNED_INTRO] ADDR32_ADDR30))
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ALIGNED_add_1_and_3,ALIGNED_add_2_and_3,
       ALIGNED_add_3_and_3,n2w_11]
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,xDATA_PERM_def]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(q1 = q2) ==> ((p * q1) = (STAR p q2))``)
  \\ `~(a IN xMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+1w IN xMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+2w IN xMEMORY_DOMAIN (df DELETE a)) /\
      ~(a+3w IN xMEMORY_DOMAIN (df DELETE a))` by
   (SIMP_TAC std_ss [xMEMORY_DOMAIN_def,GSPECIFICATION,IN_BIGUNION,
        IN_DELETE,EXTENSION,IN_INSERT,NOT_IN_EMPTY]
    \\ IMP_RES_TAC NOT_ALIGNED
    \\ SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
    \\ REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_EQ_SUB,word_arith_lemma4]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,ALIGNED_CLAUSES,WORD_EQ_ADD_CANCEL]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,ALIGNED_CLAUSES,
         word_arith_lemma3,WORD_ADD_0])
  \\ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
  \\ FULL_SIMP_TAC std_ss [xBYTE_MEMORY_ANY_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x z = f y z)``)
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_ANY_SET_EQ,EXTENSION,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [x86_el_11]
  \\ SIMP_TAC std_ss [xMEMORY_FUNC_def,LET_DEF]
  \\ `?q. (d = ADDR32 q + 0w) \/ (d = ADDR32 q + 1w) \/
          (d = ADDR32 q + 2w) \/ (d = ADDR32 q + 3w)` by METIS_TAC [EXISTS_ADDR32]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_ADD_0,RW [ALIGNED_def] ALIGNED_ADDR32,
       ALIGNED_add_1_and_3,ALIGNED_add_2_and_3,ALIGNED_add_3_and_3,
       ALIGNED_ADDR32,n2w_11]
  \\ SIMP_TAC std_ss [ADDR30_ADDR32,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val xMEMORY_INTRO = store_thm("xMEMORY_INTRO",
  ``SPEC m (xM a v * P) c (xM a w * Q) ==>
    ALIGNED a /\ a IN df ==>
    SPEC m (xMEMORY df ((a =+ v) f) * P) c (xMEMORY df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [xMEMORY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Conversions between code and data                                             *)
(* ----------------------------------------------------------------------------- *)

val xCODE_SET_def = Define `xCODE_SET df f = { (a,[f a],T) | a IN df }`;

val xCODE_IMP_BYTE_MEMORY = store_thm("xCODE_IMP_BYTE_MEMORY",
  ``!df f. SEP_IMP (xCODE (xCODE_SET df f)) (xBYTE_MEMORY_X df f)``,
  SIMP_TAC std_ss [SEP_IMP_def,xCODE_def,CODE_POOL_def,SEP_EQ_def,
    xBYTE_MEMORY_X_def,xBYTE_MEMORY_ANY_def,SEP_EXISTS,xBYTE_MEMORY_ANY_SET_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `\x.T`
  \\ SIMP_TAC std_ss [xDATA_PERM_def,xCODE_SET_def,EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,EXTENSION,IN_BIGUNION]
  \\ ONCE_REWRITE_TAC [IN_IMAGE]
  \\ `X86_INSTR_PERM T = {Xread; Xwrite; Xexecute}` by
       (SIMP_TAC std_ss [X86_INSTR_PERM_def,EXTENSION,IN_INSERT,
          NOT_IN_EMPTY,IN_UNION] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (NTAC 2 (FULL_SIMP_TAC std_ss [X86_INSTR_def,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY])
    \\ Q.EXISTS_TAC `a` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `X86_INSTR (a,[f a],T)`
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,IN_INSERT,X86_INSTR_PERM_def]
  \\ Q.EXISTS_TAC `(a,[f a],T)`
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,IN_INSERT,X86_INSTR_PERM_def]
  \\ ASM_SIMP_TAC std_ss [GSPECIFICATION]);

Theorem x86_2set_ICACHE_EMPTY[local]:
  (x86_2set' (rs,st,ei,ms) (r,e2,t,m,(\a. if a IN ms then NONE else i a)) =
   x86_2set' (rs,st,ei,ms) (r,e2,t,m,X86_ICACHE_EMPTY)) /\
  (x86_2set'' (rs,st,ei,ms) (r,e2,t,m,(\a. if a IN ms then NONE else i a)) =
   x86_2set'' (rs,st,ei,ms) (r,e2,t,m,i))
Proof
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [EXTENSION] \\ Cases
  \\ SIMP_TAC std_ss [
      IN_x86_2set,XREAD_REG_def,XREAD_EFLAG_def,Excl "lift_disj_eq",
      Excl "lift_imp_disj",
      XREAD_EIP_def,X86_GET_MEMORY_def,X86_ACCURATE_def,X86_ICACHE_EMPTY_def
    ]
  \\ SRW_TAC [][Excl "lift_disj_eq", Excl "lift_imp_disj"]
QED

val IMP_X86_SPEC_LEMMA3 = prove(
  ``!p q.
      (!rs st ei ms x r e t m i.
         p (x86_2set' (rs,st,ei,ms) (r,e,t,m,i)) ==>
         ?e2.
           (X86_NEXT (r,e,t,m,icache x m i) = SOME (r,e2,t,m,X86_ICACHE_EMPTY)) /\
           p (x86_2set' (rs,st,ei,ms) (r,e,t,m,icache x m i)) /\
           q (x86_2set' (rs,st,ei,ms) (r,e2,t,m,X86_ICACHE_EMPTY)) /\
           (x86_2set'' (rs,st,ei,ms) (r,e,t,m,i) =
            x86_2set'' (rs,st,ei,ms) (r,e2,t,m,i))) ==>
      SPEC X86_MODEL p {} q``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_X86_SPEC_LEMMA
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC X86_ICACHE_THM2
  \\ ASM_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e t m i. t1 = (r,e,t,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!rs.bb` (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`rs`,`st`,`ei`,`ms`,`z`,`r`,`e`,`t`,`m`,`i`])
  \\ ASM_SIMP_TAC std_ss [X86_ICACHE_UPDATE_def]
  \\ Q.EXISTS_TAC `(r,e2,t,m,(\addr. if addr IN ms then NONE else i addr))`
  \\ ASM_SIMP_TAC std_ss [x86_2set_ICACHE_EMPTY]
  \\ SIMP_TAC std_ss [X86_ICACHE_EMPTY_def,X86_ICACHE_def,FUN_EQ_THM]
  \\ Q.EXISTS_TAC `{}` \\ Q.EXISTS_TAC `UNIV` \\ SRW_TAC [] []);

val IMP_X86_SPEC2 = save_thm("IMP_X86_SPEC2",
  (RW1 [STAR_COMM] o RW [X86_SPEC_CODE,GSYM xCODE_def] o
   SPECL [``CODE_POOL X86_INSTR c * p``,
          ``CODE_POOL X86_INSTR c * q``]) IMP_X86_SPEC_LEMMA3);


open x86_astTheory;
open x86_coretypesTheory;
open x86_Lib x86_encodeLib;

val jmp_esi = let
  val th = x86_step (x86_encode "jmp esi")
  val th = Q.INST [`s`|->`X86_ICACHE_UPDATE x (r,e,t,m,i)`] th
  val th = RW [XREAD_CLAUSES] th
  val th = RW [XREAD_REG_def,X86_ICACHE_UPDATE_def,XWRITE_EIP_def,XCLEAR_ICACHE_def] th
  in th end

val WORD_FINITE = store_thm("WORD_FINITE",
  ``!s:'a word set. FINITE s``,
  STRIP_TAC
  \\ MATCH_MP_TAC ((ONCE_REWRITE_RULE [CONJ_COMM] o
    REWRITE_RULE [AND_IMP_INTRO] o GEN_ALL o DISCH_ALL o SPEC_ALL o
    UNDISCH_ALL o SPEC_ALL) SUBSET_FINITE)
  \\ Q.EXISTS_TAC `UNIV`
  \\ ASM_SIMP_TAC std_ss [SUBSET_UNIV]
  \\ MATCH_MP_TAC ((ONCE_REWRITE_RULE [CONJ_COMM] o
    REWRITE_RULE [AND_IMP_INTRO] o GEN_ALL o DISCH_ALL o SPEC_ALL o
    UNDISCH_ALL o SPEC_ALL) SUBSET_FINITE)
  \\ Q.EXISTS_TAC `{ n2w n | n < dimword(:'a) }`
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [SUBSET_DEF,IN_UNIV,GSPECIFICATION]
    \\ Cases_word \\ Q.EXISTS_TAC `n` \\ ASM_SIMP_TAC std_ss [])
  \\ Q.SPEC_TAC (`dimword (:'a)`,`k`)
  \\ Induct \\ sg `{n2w n | n < 0} = {}`
  \\ ASM_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,FINITE_EMPTY]
  \\ sg `{n2w n | n < SUC k} = n2w k INSERT {n2w n | n < k}`
  \\ ASM_SIMP_TAC std_ss [FINITE_INSERT]
  \\ ASM_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INSERT]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DECIDE ``n < SUC k = n < k \/ (n = k)``]
  \\ METIS_TAC []);

val WORD_SET_INDUCT = save_thm("WORD_SET_INDUCT",
  REWRITE_RULE [WORD_FINITE]
  (INST_TYPE [``:'a``|->``:'a word``] FINITE_INDUCT));

val xBYTE_MEMORY_X_x86_2set = prove(
  ``!df ms.
      (xBYTE_MEMORY_X df f * p) (x86_2set' (rs,st,ei,ms) (r,e,t,m,i)) =
      p (x86_2set' (rs,st,ei,ms DIFF df) (r,e,t,m,i)) /\ df SUBSET ms /\
      !a. a IN df ==> (m a = SOME (f a, {Xread;Xwrite;Xexecute}))``,
  HO_MATCH_MP_TAC WORD_SET_INDUCT \\ REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [xBYTE_MEMORY_X_def,xBYTE_MEMORY_ANY_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [NOT_IN_EMPTY]
    \\ `!c. xBYTE_MEMORY_ANY_SET {} f T c = {}` by
      SIMP_TAC std_ss [xBYTE_MEMORY_ANY_SET_def,NOT_IN_EMPTY,EXTENSION,GSPECIFICATION]
    \\ ASM_SIMP_TAC std_ss [GSYM emp_def,SEP_EQ_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [DIFF_EMPTY,EMPTY_SUBSET],
    FULL_SIMP_TAC std_ss [xBYTE_MEMORY_X_def]
    \\ SIMP_TAC std_ss [DIFF_INSERT,xBYTE_MEMORY_ANY_INSERT_SET]
    \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC,STAR_x86_2set,DELETE_NON_ELEMENT]
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,GSYM DELETE_NON_ELEMENT]
    \\ ASM_SIMP_TAC std_ss [xDATA_PERM_def,INSERT_SUBSET,SUBSET_DELETE]
    \\ METIS_TAC []]);

val xCODE_SET_INSERT = store_thm("xCODE_SET_INSERT",
  ``~(e IN df) ==>
    (xCODE (xCODE_SET (e INSERT df) f) =
     xM1 e (SOME (f e, {Xread; Xwrite; Xexecute})) T * xCODE (xCODE_SET df f))``,
  SIMP_TAC std_ss [xCODE_def,xCODE_SET_def,xM1_def,EQ_STAR,FUN_EQ_THM] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [CODE_POOL_def,INSERT_SUBSET,EMPTY_SUBSET]
  \\ `~((e,[f e],T) IN {(a,[f a],T) | a IN df}) /\
      ({(a,[f a],T) | a IN e INSERT df} = (e,[f e],T) INSERT {(a,[f a],T) | a IN df})` by
        (SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ SIMP_TAC std_ss [X86_INSTR_def,INSERT_UNION_EQ,UNION_EMPTY]
  \\ `X86_INSTR_PERM T = {Xread; Xwrite; Xexecute}` by
        (SIMP_TAC std_ss [X86_INSTR_PERM_def,EXTENSION,IN_INSERT,
          IN_UNION,NOT_IN_EMPTY] \\ REPEAT STRIP_TAC \\ EQ_TAC
         \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [DIFF_INSERT,DIFF_EMPTY]
  \\ Q.ABBREV_TAC `a1 = xMem e (SOME (f e,{Xread; Xwrite; Xexecute})) T`
  \\ Q.ABBREV_TAC `a2 = BIGUNION (IMAGE X86_INSTR {(a,[f a],T) | a IN df})`
  \\ `~(a1 IN a2)` suffices_by
  (STRIP_TAC THEN SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE] \\ METIS_TAC [])
  \\ Q.UNABBREV_TAC `a1` \\ Q.UNABBREV_TAC `a2`
  \\ ASM_SIMP_TAC std_ss [IN_IMAGE,IN_BIGUNION]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``e \/ b = ~e ==> b``,GSPECIFICATION]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [X86_INSTR_def,IN_INSERT,NOT_IN_EMPTY,x86_el_11]);

val xCODE_SET_x86_2set = prove(
  ``!df ms.
      (xCODE (xCODE_SET df f) * p) (x86_2set' (rs,st,ei,ms) (r,e,t,m,i)) =
      p (x86_2set' (rs,st,ei,ms DIFF df) (r,e,t,m,i)) /\ df SUBSET ms /\
      !a. a IN df ==> (m a = SOME (f a, {Xread;Xwrite;Xexecute})) /\
                      X86_ACCURATE a (r,e,t,m,i)``,
  HO_MATCH_MP_TAC WORD_SET_INDUCT \\ REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [xCODE_SET_def,xCODE_def,SEP_CLAUSES]
    \\ `{(a,[f a],T) | a IN {}} = {}` by
      SIMP_TAC std_ss [NOT_IN_EMPTY,EXTENSION,GSPECIFICATION]
    \\ ASM_SIMP_TAC std_ss [CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY]
    \\ SIMP_TAC std_ss [GSYM emp_def,SEP_CLAUSES,DIFF_EMPTY,EMPTY_SUBSET]
    \\ SIMP_TAC std_ss [NOT_IN_EMPTY],
    ASM_SIMP_TAC std_ss [GSYM STAR_ASSOC,xCODE_SET_INSERT]
    \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC,STAR_x86_2set,DELETE_NON_ELEMENT]
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,GSYM DELETE_NON_ELEMENT]
    \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,SUBSET_DELETE,DIFF_INSERT]
    \\ METIS_TAC []]);

val xCODE_INTRO = store_thm("xCODE_INTRO",
  ``SPEC X86_MODEL
      (xR ESI esi * xPC eip * xBYTE_MEMORY_X df f)
      {(eip,[0xFFw;0xE6w],T)}
      (xR ESI esi * xPC esi * xCODE (xCODE_SET df f))``,
  MATCH_MP_TAC IMP_X86_SPEC2 \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r ESI`
  \\ STRIP_TAC THENL [MATCH_MP_TAC jmp_esi,ALL_TAC]
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES,X86_ICACHE_UPDATE_def,XREAD_EIP_def,
         X86_ICACHE_REVERT_def,xM_def,WORD_EQ_ADD_CANCEL,x86_address_lemma,
         xCODE_SET_x86_2set,xBYTE_MEMORY_X_x86_2set]
  \\ ONCE_REWRITE_TAC [CODE_POOL_x86_2set]
  \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
  \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,X86_ICACHE_EXTRACT_def]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,x86_pool_def,X86_ACCURATE_CLAUSES,
         xCODE_SET_x86_2set,xBYTE_MEMORY_X_x86_2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]  THEN1
   (REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ MATCH_MP_TAC XREAD_INSTR_IMP \\ Q.EXISTS_TAC `T`
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [UPDATE_x86_2set'',IN_INSERT]
  \\ STRIP_TAC \\ IMP_RES_TAC X86_ACCURATE_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
  \\ SIMP_TAC std_ss [X86_ACCURATE_def,X86_ICACHE_EMPTY_def]);

val SPLIT_CODE_SEQ = prove(
  ``SPEC X86_MODEL p ((a,x::xs,T) INSERT s) q =
    SPEC X86_MODEL p ((a+1w,xs,T) INSERT (a,[x],T) INSERT s) q``,
  SIMP_TAC std_ss [progTheory.SPEC_def,X86_MODEL_def]
  \\ sg `CODE_POOL X86_INSTR ((a + 0x1w,xs,T) INSERT (a,[x],T) INSERT s) =
      CODE_POOL X86_INSTR ((a,x::xs,T) INSERT s)`
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [progTheory.CODE_POOL_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> ((\s. s = x) = (\s. s = y))``)
  \\ SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ SIMP_TAC std_ss [EXTENSION,IN_BIGUNION]
  \\ SIMP_TAC std_ss [X86_INSTR_def]
  \\ SIMP_TAC std_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []);

val X86_SPEC_EXLPODE_CODE_LEMMA = prove(
  ``!s. SPEC X86_MODEL p ((a,xs,T) INSERT s) q =
        SPEC X86_MODEL p ({ (a + n2w n, [EL n xs], T) | n| n < LENGTH xs } UNION s) q``,
  Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`xs`,`xs`) \\ REVERSE Induct THEN1
   (ASM_SIMP_TAC std_ss [SPLIT_CODE_SEQ] \\ REPEAT STRIP_TAC
    \\ sg `{(a + n2w n,[EL n (h::xs)],T) | n | n < LENGTH (h::xs)} =
        {(a + 0x1w + n2w n,[EL n xs],T) | n | n < LENGTH xs} UNION {(a,[h],T)}`
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
  \\ `{(a + n2w n,[EL n ([]:word8 list)],T) | n| n < LENGTH ([]:word8 list)} = {}` by
    ASM_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,LENGTH]
  \\ ASM_SIMP_TAC std_ss [UNION_EMPTY]
  \\ SIMP_TAC std_ss [progTheory.SPEC_def,X86_MODEL_def]
  \\ sg `CODE_POOL X86_INSTR ((a,[],T) INSERT s) =
      CODE_POOL X86_INSTR (s)`
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [progTheory.CODE_POOL_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> ((\s. s = x) = (\s. s = y))``)
  \\ POP_ASSUM (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [UNION_EMPTY,IMAGE_INSERT,X86_INSTR_def,BIGUNION_INSERT]);

val X86_SPEC_EXLPODE_CODE = save_thm("X86_SPEC_EXLPODE_CODE",
  RW [UNION_EMPTY] (Q.SPEC `{}` X86_SPEC_EXLPODE_CODE_LEMMA));

(* Stack --- sp points at top of stack, stack grows towards smaller addresses *)

val xSTACK_def = Define `
  xSTACK bp xs = xR EBP bp * xR ESP (bp - n2w (4 * LENGTH xs)) *
                 SEP_ARRAY xM (-4w) bp xs * cond (ALIGNED bp)`;

val STAR6 = prove(
  ``p1 * p2 * p3 * p4 * p5 * p6 = (p1 * p2 * p5) * (STAR p3 p4 * p6)``,
  SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);

val xSTACK_INTRO_EBX = store_thm("xSTACK_INTRO_EBX",
  ``(ALIGNED ebp ==>
     SPEC X86_MODEL (q1 * xR EBP ebp * xM (ebp - n2w n) x) c
                    (q2 * xR EBP ebp * xM (ebp - n2w n) y)) ==>
    !xs ys.
      (4 * LENGTH xs = n) ==>
      SPEC X86_MODEL (q1 * xSTACK ebp (xs ++ [x] ++ ys))
                   c (q2 * xSTACK ebp (xs ++ [y] ++ ys))``,
  SIMP_TAC std_ss [xSTACK_def,SEP_ARRAY_APPEND,GSYM WORD_NEG_RMUL,STAR_ASSOC,
    RW1 [MULT_COMM] word_mul_n2w,GSYM word_sub_def,SEP_ARRAY_def,SEP_CLAUSES,
    LENGTH,LENGTH_APPEND,SPEC_MOVE_COND] \\ ONCE_REWRITE_TAC [STAR6]
  \\ METIS_TAC [SPEC_FRAME]);

val _ = export_theory();
