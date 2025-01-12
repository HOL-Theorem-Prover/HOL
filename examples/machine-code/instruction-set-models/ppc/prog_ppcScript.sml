
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory;

open set_sepTheory progTheory ppc_Theory ppc_seq_monadTheory;

val _ = new_theory "prog_ppc";
val _ = ParseExtras.temp_loose_equality()

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The PowerPC set                                                               *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  ppc_el =  pReg of ppc_reg => word32
          | pMem of word32 => word8 option
          | pStatus of ppc_bit => bool option`;

val ppc_el_11 = DB.fetch "-" "ppc_el_11";
val ppc_el_distinct = DB.fetch "-" "ppc_el_distinct";

val _ = Parse.type_abbrev("ppc_set",``:ppc_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from PPC-state tuple to ppc_set                                    *)
(* ----------------------------------------------------------------------------- *)

val ppc2set'_def = Define `
  ppc2set' (rs,ms,st) s =
    IMAGE (\a. pReg a (PREAD_R a s)) rs UNION
    IMAGE (\a. pMem a (PREAD_M a s)) ms UNION
    IMAGE (\a. pStatus a (PREAD_S a s)) st`;

val ppc2set_def   = Define `ppc2set s = ppc2set' (UNIV,UNIV,UNIV) s`;
val ppc2set''_def = Define `ppc2set'' x s = ppc2set s DIFF ppc2set' x s`;

(* theorems *)

val ppc2set'_SUBSET_ppc2set = prove(
  ``!y s. ppc2set' y s SUBSET ppc2set s``,
  Cases_on `y` \\ Cases_on `r`
  \\ SIMP_TAC std_ss [SUBSET_DEF,ppc2set'_def,ppc2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_ppc2set = prove(
  ``!x s. SPLIT (ppc2set s) (ppc2set' x s, ppc2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,ppc2set''_def]
  \\ `ppc2set' x s SUBSET ppc2set s` by METIS_TAC [ppc2set'_SUBSET_ppc2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val SUBSET_ppc2set = prove(
  ``!u s. u SUBSET ppc2set s = ?y. u = ppc2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [ppc2set'_SUBSET_ppc2set]
  \\ Q.EXISTS_TAC `({ a |a| ?x. pReg a x IN u },
       { a |a| ?x. pMem a x IN u },{ a |a| ?x. pStatus a x IN u })`
  \\ FULL_SIMP_TAC std_ss [ppc2set'_def,ppc2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_X_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC) \\ FULL_SIMP_TAC std_ss [ppc_el_11,ppc_el_distinct]);

val SPLIT_ppc2set_EXISTS = prove(
  ``!s u v. SPLIT (ppc2set s) (u,v) = ?y. (u = ppc2set' y s) /\ (v = ppc2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_ppc2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,ppc2set'_def,ppc2set''_def]
  \\ `u SUBSET (ppc2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_ppc2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``;

val IN_ppc2set = prove(``
  (!r x s. pReg r x IN (ppc2set s) = (x = PREAD_R r s)) /\
  (!r x s. pReg r x IN (ppc2set' (rs,ms,st) s) = (x = PREAD_R r s) /\ r IN rs) /\
  (!r x s. pReg r x IN (ppc2set'' (rs,ms,st) s) = (x = PREAD_R r s) /\ ~(r IN rs)) /\
  (!p x s. pMem p x IN (ppc2set s) = (x = PREAD_M p s)) /\
  (!p x s. pMem p x IN (ppc2set' (rs,ms,st) s) = (x = PREAD_M p s) /\ p IN ms) /\
  (!p x s. pMem p x IN (ppc2set'' (rs,ms,st) s) = (x = PREAD_M p s) /\ ~(p IN ms)) /\
  (!a x s. pStatus a x IN (ppc2set s) = (x = PREAD_S a s)) /\
  (!a x s. pStatus a x IN (ppc2set' (rs,ms,st) s) = (x = PREAD_S a s) /\ a IN st) /\
  (!a x s. pStatus a x IN (ppc2set'' (rs,ms,st) s) = (x = PREAD_S a s) /\ ~(a IN st))``,
  SRW_TAC [] [ppc2set'_def,ppc2set''_def,ppc2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val ppc2set''_11 = prove(
  ``!y y' s s'. (ppc2set'' y' s' = ppc2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st. y = (r,m,st)` by METIS_TAC [PAIR]
  \\ `?r' m' st'. y' = (r',m',st')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ, Excl "lift_disj_eq"] THENL [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. pReg a x IN ppc2set'' y s) = (?x. pReg a x IN ppc2set'' y' s'))`,
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. pMem a x IN ppc2set'' y s) = (?x. pMem a x IN ppc2set'' y' s'))`,
    `?a. ~(a IN st = a IN st')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. pStatus a x IN ppc2set'' y s) = (?x. pStatus a x IN ppc2set'' y' s'))`]
  \\ REPEAT (FULL_SIMP_TAC bool_ss [IN_ppc2set] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `ppc2set'' _ _  = ppc2set'' _ _` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [IN_ppc2set] \\ METIS_TAC []);

val DELETE_ppc2set = prove(``
  (!a s. (ppc2set' (rs,ms,st) (r,s,m)) DELETE pReg a (r a) =
         (ppc2set' (rs DELETE a,ms,st) (r,s,m))) /\
  (!b s. (ppc2set' (rs,ms,st) (r,s,m)) DELETE pMem b (m b) =
         (ppc2set' (rs,ms DELETE b,st) (r,s,m))) /\
  (!c s. (ppc2set' (rs,ms,st) (r,s,m)) DELETE pStatus c (s c) =
         (ppc2set' (rs,ms,st DELETE c) (r,s,m)))``,
  SRW_TAC [] [ppc2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF,
    PREAD_R_def,PREAD_M_def,PREAD_S_def]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_ppc2set = prove(``
  (ppc2set' (rs,ms,st) s = {}) = (rs = {}) /\ (ms = {}) /\ (st = {})``,
  SRW_TAC [] [ppc2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Defining the PPC_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val pR1_def = Define `pR1 a x = SEP_EQ {pReg a x}`;
val pM1_def = Define `pM1 a x = SEP_EQ {pMem a x}`;
val pS1_def = Define `pS1 a x = SEP_EQ {pStatus a x}`;

val pR_def   = Define `pR a x = pR1 (PPC_IR a) x`;
val pPC_def  = Define `pPC x  = pR1 (PPC_PC) x * cond (ALIGNED x)`;
val pLR_def  = Define `pLR x  = pR1 (PPC_LR) x`;
val pCTR_def = Define `pCTR x = pR1 (PPC_CTR) x`;

val pS_def = Define `
  pS (x0,x1,x2,x3,c) =
    pS1 (PPC_CR0 0w) x0 * pS1 (PPC_CR0 1w) x1 *
    pS1 (PPC_CR0 2w) x2 * pS1 (PPC_CR0 3w) x3 * pS1 PPC_CARRY c`;

val PPC_NEXT_REL_def = Define `PPC_NEXT_REL s s' = (PPC_NEXT s = SOME s')`;

val PPC_INSTR_def    = Define `PPC_INSTR (a,w:word32) =
  { pMem a      (SOME ((31 >< 24) w)) ;
    pMem (a+1w) (SOME ((23 >< 16) w)) ;
    pMem (a+2w) (SOME ((15 ><  8) w)) ;
    pMem (a+3w) (SOME (( 7 ><  0) w)) }`;

val PPC_MODEL_def = Define `
  PPC_MODEL = (ppc2set, PPC_NEXT_REL, PPC_INSTR, (\x y. (x = (y:ppc_state))),
               (K F):ppc_state -> bool)`;

val pLINK_REGISTER_def = Define `pLINK_REGISTER x  = pLR x * cond (ALIGNED x)`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_ppc2set]
  ``p (ppc2set' y s) ==> (?u v. SPLIT (ppc2set s) (u,v) /\ p u /\ (\v. v = ppc2set'' y s) v)``;

val PPC_SPEC_SEMANTICS = store_thm("PPC_SPEC_SEMANTICS",
  ``SPEC PPC_MODEL p {} q =
    !y s seq. p (ppc2set' y s) /\ rel_sequence PPC_NEXT_REL seq s ==>
              ?k. q (ppc2set' y (seq k)) /\ (ppc2set'' y s = ppc2set'' y (seq k))``,
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,PPC_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_ppc2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = ppc2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_ppc2set_EXISTS]
  \\ IMP_RES_TAC ppc2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC PPC_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_ppc2set = store_thm("STAR_ppc2set",
  ``((pR1 a x * p) (ppc2set' (rs,ms,st) (r,s,m)) =
      (x = r a) /\ a IN rs /\ p (ppc2set' (rs DELETE a,ms,st) (r,s,m))) /\
    ((pM1 b y * p) (ppc2set' (rs,ms,st) (r,s,m)) =
      (y = m b) /\ b IN ms /\ p (ppc2set' (rs,ms DELETE b,st) (r,s,m))) /\
    ((pS1 c z * p) (ppc2set' (rs,ms,st) (r,s,m)) =
      (z = s c) /\ c IN st /\ p (ppc2set' (rs,ms,st DELETE c) (r,s,m))) /\
    ((cond g * p) (ppc2set' (rs,ms,st) (r,s,m)) =
      g /\ p (ppc2set' (rs,ms,st) (r,s,m)))``,
  SIMP_TAC std_ss [pR1_def,pS1_def,pM1_def,EQ_STAR,INSERT_SUBSET,cond_STAR,
    EMPTY_SUBSET,IN_ppc2set,PREAD_R_def,PREAD_S_def,PREAD_M_def,GSYM DELETE_DEF]
  \\ METIS_TAC [DELETE_ppc2set]);

val CODE_POOL_ppc2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) = (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_ppc2set = store_thm("CODE_POOL_ppc2set",
  ``CODE_POOL PPC_INSTR {(p,w)} (ppc2set' (rs,ms,st) (r,s,m)) =
      ({p;p+1w;p+2w;p+3w} = ms) /\ (rs = {}) /\ (st = {}) /\
      (SOME ((31 >< 24) (w:word32)) = m p) /\
      (SOME ((23 >< 16) (w:word32)) = m (p+1w)) /\
      (SOME ((15 ><  8) (w:word32)) = m (p+2w)) /\
      (SOME (( 7 ><  0) (w:word32)) = m (p+3w))``,
  SIMP_TAC bool_ss [INSERT_SUBSET,GSYM DELETE_DEF, CODE_POOL_ppc2set_LEMMA,
    EMPTY_SUBSET, IN_DELETE, IMAGE_INSERT, CODE_POOL_def, IMAGE_EMPTY,PREAD_M_def,
    BIGUNION_INSERT, BIGUNION_EMPTY, UNION_EMPTY, PPC_INSTR_def,IN_ppc2set]
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_ppc2set]
  \\ Cases_on `SOME (( 7 ><  0) (w:word32)) = m (p + 3w)` \\ ASM_REWRITE_TAC []
  \\ Cases_on `SOME ((15 ><  8) (w:word32)) = m (p + 2w)` \\ ASM_REWRITE_TAC []
  \\ Cases_on `SOME ((23 >< 16) (w:word32)) = m (p + 1w)` \\ ASM_REWRITE_TAC []
  \\ Cases_on `SOME ((31 >< 24) (w:word32)) = m (p     )` \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC std_ss [DIFF_INSERT,DELETE_ppc2set,DIFF_EMPTY,EMPTY_ppc2set]
  \\ METIS_TAC []);

val UPDATE_ppc2set'' = store_thm("UPDATE_ppc2set''",
  ``(!a x. a IN rs ==>
      (ppc2set'' (rs,ms,st) ((a =+ x) r,s,m) = ppc2set'' (rs,ms,st) (r,s,m))) /\
    (!a x. a IN ms ==>
      (ppc2set'' (rs,ms,st) (r,s,(a =+ x) m) = ppc2set'' (rs,ms,st) (r,s,m))) /\
    (!a x. a IN st ==>
      (ppc2set'' (rs,ms,st) (r,(a =+ x) s,m) = ppc2set'' (rs,ms,st) (r,s,m)))``,
  SIMP_TAC std_ss [ppc2set_def,ppc2set''_def,ppc2set'_def,EXTENSION,IN_UNION,
    IN_IMAGE,IN_DIFF,IN_UNIV,PREAD_R_def,PREAD_M_def,PREAD_S_def,APPLY_UPDATE_THM]
  \\ METIS_TAC [ppc_el_distinct,ppc_el_11]);

val PPC_SPEC_CODE = RW [GSYM PPC_MODEL_def]
  (SIMP_RULE std_ss [PPC_MODEL_def] (Q.ISPEC `PPC_MODEL` SPEC_CODE));

val IMP_PPC_SPEC_LEMMA = prove(
  ``!p q.
      (!rs ms st pr pm ps. ?s'.
        (p (ppc2set' (rs,ms,st) (pr,ps,pm)) ==>
        (PPC_NEXT (pr,ps,pm) = SOME s') /\ q (ppc2set' (rs,ms,st) s') /\
        (ppc2set'' (rs,ms,st) (pr,ps,pm) = ppc2set'' (rs,ms,st) s'))) ==>
      SPEC PPC_MODEL p {} q``,
  REWRITE_TAC [PPC_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,PPC_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC [optionTheory.SOME_11,PAIR]);

val IMP_PPC_SPEC = save_thm("IMP_PPC_SPEC",
  (RW1 [STAR_COMM] o RW [PPC_SPEC_CODE] o
   SPECL [``CODE_POOL PPC_INSTR {(p,c)} * p'``,
          ``CODE_POOL PPC_INSTR {(p,c)} * q'``]) IMP_PPC_SPEC_LEMMA);

val pS_HIDE = store_thm("pS_HIDE",
  ``~pS = ~pS1 (PPC_CR0 0w) * ~pS1 (PPC_CR0 1w) * ~pS1 (PPC_CR0 2w) *
          ~pS1 (PPC_CR0 3w) * ~pS1 PPC_CARRY``,
  SIMP_TAC std_ss [SEP_HIDE_def,pS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [pS_def,PAIR]);


(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates                                                    *)
(* ----------------------------------------------------------------------------- *)

val pMEMORY_WORD_def = Define `
  pMEMORY_WORD (a:word32) (w:word32) =
    { pMem a      (SOME ((7 >< 0) (w >> 24))) ;
      pMem (a+1w) (SOME ((7 >< 0) (w >> 16))) ;
      pMem (a+2w) (SOME ((7 >< 0) (w >> 8))) ;
      pMem (a+3w) (SOME ((7 >< 0) w)) }`;

val pMEMORY_SET_def = Define `
  pMEMORY_SET df f = BIGUNION { pMEMORY_WORD a (f a) | a | a IN df /\ ALIGNED a  }`;

val pMEMORY_def = Define `pMEMORY df f = SEP_EQ (pMEMORY_SET df f)`;

val pMEMORY_SET_SING = prove(
  ``!a f. ALIGNED a ==> (pMEMORY_SET {a} f = pMEMORY_WORD a (f a))``,
  ASM_SIMP_TAC std_ss [GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,APPLY_UPDATE_THM,
    EXTENSION,pMEMORY_SET_def,IN_BIGUNION] \\ METIS_TAC [IN_INSERT]);

val pMEMORY_ARITH_LEMMA = prove(
  ``!a:word32. ~(a = a + 1w) /\ ~(a = a + 2w) /\ ~(a = a + 3w) /\
               ~(a + 1w = a + 2w) /\ ~(a + 1w = a + 3w) /\ ~(a + 2w = a + 3w)``,
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
    RW [WORD_ADD_0] (Q.SPECL [`x`,`0w`] WORD_EQ_ADD_LCANCEL)]);

val pMEMORY_LEMMA = prove(
  ``!a f w.
      ALIGNED a ==>
      (pMEMORY {a} ((a =+ w) f) =
       pM1 a (SOME ((7 >< 0) (w >> 24))) * pM1 (a + 1w) (SOME ((7 >< 0) (w >> 16))) *
       pM1 (a + 2w) (SOME ((7 >< 0) (w >> 8))) * pM1 (a + 3w) (SOME ((7 >< 0) w)))``,
  SIMP_TAC std_ss [pMEMORY_def,pMEMORY_SET_SING] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [pM1_def,EQ_STAR,GSYM STAR_ASSOC,APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [SEP_EQ_def]
  \\ STRIP_TAC \\ Cases_on `x = pMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [pMEMORY_WORD_def,INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY,GSYM DELETE_DEF,EMPTY_SUBSET,IN_DELETE,ppc_el_11,EXTENSION]
  THEN1 METIS_TAC [pMEMORY_ARITH_LEMMA,ppc_el_11,ppc_el_distinct]
  \\ SIMP_TAC std_ss [pMEMORY_ARITH_LEMMA]
  \\ Cases_on `pMem a (SOME ((7 >< 0) (w >> 24))) IN x` THEN1 METIS_TAC []
  \\ Cases_on `pMem (a + 1w) (SOME ((7 >< 0) (w >> 16))) IN x` THEN1 METIS_TAC []
  \\ Cases_on `pMem (a + 2w) (SOME ((7 >< 0) (w >> 8))) IN x` THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss []);

val pMEMORY_INSERT = prove(
  ``!s. ALIGNED a /\ ~(a IN s) ==>
        (pMEMORY {a} ((a =+ w) g) * pMEMORY s f = pMEMORY (a INSERT s) ((a =+ w) f))``,
  STRIP_TAC
  \\ SIMP_TAC bool_ss [FUN_EQ_THM,cond_STAR,pMEMORY_def,pMEMORY_SET_SING,APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [STAR_def,SEP_EQ_def,SPLIT_def]
  \\ REPEAT STRIP_TAC
  \\ `DISJOINT (pMEMORY_WORD a w) (pMEMORY_SET s f)` by
   (SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,
                     pMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REWRITE_TAC [GSYM IMP_DISJ_THM] \\ REPEAT STRIP_TAC
    \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!x. b` (K ALL_TAC)
    \\ `~(a = a')` by METIS_TAC []
    \\ NTAC 2 (FULL_SIMP_TAC bool_ss [pMEMORY_WORD_def,IN_INSERT,
         NOT_IN_EMPTY,ppc_el_11,WORD_EQ_ADD_RCANCEL])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma5,word_arith_lemma4]
    \\ METIS_TAC [NOT_ALIGNED])
  \\ `pMEMORY_WORD a w UNION pMEMORY_SET s f =
      pMEMORY_SET (a INSERT s) ((a =+ w) f)` by
   (SIMP_TAC std_ss [IN_UNION,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_INSERT,
                     pMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `pMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM],
      Q.EXISTS_TAC `s'` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a'` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM],
      `~(a = a')` by METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
      \\ METIS_TAC []])
  \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);

val pMEMORY_INTRO = store_thm("pMEMORY_INTRO",
  ``SPEC PPC_MODEL
     (pM1 a (SOME ((7 >< 0) (v >> 24))) * pM1 (a + 1w) (SOME ((7 >< 0) (v >> 16))) *
      pM1 (a + 2w) (SOME ((7 >< 0) (v >> 8))) * pM1 (a + 3w) (SOME ((7 >< 0) v)) * P) c
     (pM1 a (SOME ((7 >< 0) (w >> 24))) * pM1 (a + 1w) (SOME ((7 >< 0) (w >> 16))) *
      pM1 (a + 2w) (SOME ((7 >< 0) (w >> 8))) * pM1 (a + 3w) (SOME ((7 >< 0) w)) * Q) ==>
    ALIGNED a /\ a IN df ==>
    SPEC PPC_MODEL (pMEMORY df ((a =+ v) f) * P) c (pMEMORY df ((a =+ w) f) * Q)``,
  REPEAT STRIP_TAC
  \\ (IMP_RES_TAC o GEN_ALL o REWRITE_RULE [AND_IMP_INTRO] o
     SIMP_RULE std_ss [INSERT_DELETE,IN_DELETE] o
     DISCH ``a:word32 IN df`` o Q.SPEC `df DELETE a` o GSYM) pMEMORY_INSERT
  \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC bool_ss [pMEMORY_LEMMA]
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ REWRITE_TAC [STAR_ASSOC]
  \\ MATCH_MP_TAC SPEC_FRAME
  \\ FULL_SIMP_TAC bool_ss [AC STAR_COMM STAR_ASSOC]);

(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates (byte addressed memory)                            *)
(* ----------------------------------------------------------------------------- *)

val pBYTE_MEMORY_SET_def = Define `
  pBYTE_MEMORY_SET df f = { pMem a (SOME (f a)) | a | a IN df }`;

val pBYTE_MEMORY_def = Define `pBYTE_MEMORY df f = SEP_EQ (pBYTE_MEMORY_SET df f)`;

val IN_pBYTE_MEMORY_SET = prove(
  ``a IN df ==>
    (pBYTE_MEMORY_SET df g =
     (pMem a (SOME (g a))) INSERT pBYTE_MEMORY_SET (df DELETE a) g)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,pBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_pBYTE_MEMORY_SET = prove(
  ``pBYTE_MEMORY_SET (df DELETE a) ((a =+ w) g) =
    pBYTE_MEMORY_SET (df DELETE a) g``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,pBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val pBYTE_MEMORY_INSERT = store_thm("pBYTE_MEMORY_INSERT",
  ``a IN df ==>
    (pBYTE_MEMORY df ((a =+ w) g) =
    pM1 a (SOME w) * pBYTE_MEMORY (df DELETE a) g)``,
  SIMP_TAC std_ss [pBYTE_MEMORY_def,pM1_def,pMEMORY_def,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_pBYTE_MEMORY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_pBYTE_MEMORY_SET,APPLY_UPDATE_THM]
  \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_DELETE]
  \\ `~(pMem a (SOME w) IN pBYTE_MEMORY_SET (df DELETE a) g)` suffices_by METIS_TAC []
  \\ SIMP_TAC std_ss [pBYTE_MEMORY_SET_def,GSPECIFICATION,IN_DELETE,ppc_el_11]);

val pBYTE_MEMORY_INTRO = store_thm("pBYTE_MEMORY_INTRO",
  ``SPEC m (pM1 a (SOME v) * P) c (pM1 a (SOME w) * Q) ==>
    a IN df ==>
    SPEC m (pBYTE_MEMORY df ((a =+ v) f) * P) c (pBYTE_MEMORY df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [pBYTE_MEMORY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


val _ = export_theory();
