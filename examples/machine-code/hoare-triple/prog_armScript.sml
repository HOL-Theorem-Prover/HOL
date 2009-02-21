
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open set_sepTheory progTheory armTheory arm_auxTheory systemTheory;
open listTheory pairTheory combinTheory addressTheory;

val _ = new_theory "prog_arm";


infix \\ 
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The ARM set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  arm_el =  aReg of word4 => word32
          | aMem of word30 => word32  
          | aStatus of arm_bit => bool
          | aUndef of bool`;

val arm_el_11 = DB.fetch "-" "arm_el_11";
val arm_el_distinct = DB.fetch "-" "arm_el_distinct";

val _ = Parse.type_abbrev("arm_set",``:arm_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from ARM-state record to arm_set                                   *)
(* ----------------------------------------------------------------------------- *)

val arm2set'_def = Define `
  arm2set' (rs,ms,st,ud) (s:unit arm_sys_state) =
    IMAGE (\a. aReg a (ARM_READ_REG a s)) rs UNION
    IMAGE (\a. aMem a (ARM_READ_MEM a s)) ms UNION
    IMAGE (\a. aStatus a (ARM_READ_STATUS a s)) st UNION
    if ud then { aUndef (ARM_READ_UNDEF s) } else {}`;

val arm2set_def   = Define `arm2set s = arm2set' (UNIV,UNIV,UNIV,T) s`;
val arm2set''_def = Define `arm2set'' x s = arm2set s DIFF arm2set' x s`;

(* theorems *)

val arm2set'_SUBSET_arm2set = prove(
  ``!y s. arm2set' y s SUBSET arm2set s``, 
  Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'`
  \\ SIMP_TAC std_ss [SUBSET_DEF,arm2set'_def,arm2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_arm2set = prove(
  ``!x s. SPLIT (arm2set s) (arm2set' x s, arm2set'' x s)``,
  REPEAT STRIP_TAC 
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,arm2set''_def]
  \\ `arm2set' x s SUBSET arm2set s` by METIS_TAC [arm2set'_SUBSET_arm2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``;

val SUBSET_arm2set = prove(
  ``!u s. u SUBSET arm2set s = ?y. u = arm2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [arm2set'_SUBSET_arm2set]
  \\ Q.EXISTS_TAC `({ a |a| ?x. aReg a x IN u },
       { a |a| ?x. aMem a x IN u },{ a |a| ?x. aStatus a x IN u },
       (?y. aUndef y IN u))`
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,arm2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV,PUSH_IN_INTO_IF]  
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC) \\ FULL_SIMP_TAC std_ss [arm_el_11,arm_el_distinct]);

val SPLIT_arm2set_EXISTS = prove(
  ``!s u v. SPLIT (arm2set s) (u,v) = ?y. (u = arm2set' y s) /\ (v = arm2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_arm2set] 
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,arm2set'_def,arm2set''_def]
  \\ `u SUBSET (arm2set s)` by 
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_arm2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]  
  \\ METIS_TAC []);

val IN_arm2set = prove(``
  (!r x s. aReg r x IN (arm2set s) = (x = ARM_READ_REG r s)) /\
  (!r x s. aReg r x IN (arm2set' (rs,ms,st,ud) s) = (x = ARM_READ_REG r s) /\ r IN rs) /\
  (!r x s. aReg r x IN (arm2set'' (rs,ms,st,ud) s) = (x = ARM_READ_REG r s) /\ ~(r IN rs)) /\
  (!p x s. aMem p x IN (arm2set s) = (x = ARM_READ_MEM p s)) /\
  (!p x s. aMem p x IN (arm2set' (rs,ms,st,ud) s) = (x = ARM_READ_MEM p s) /\ p IN ms) /\
  (!p x s. aMem p x IN (arm2set'' (rs,ms,st,ud) s) = (x = ARM_READ_MEM p s) /\ ~(p IN ms)) /\
  (!a x s. aStatus a x IN (arm2set s) = (x = ARM_READ_STATUS a s)) /\
  (!a x s. aStatus a x IN (arm2set' (rs,ms,st,ud) s) = (x = ARM_READ_STATUS a s) /\ a IN st) /\
  (!a x s. aStatus a x IN (arm2set'' (rs,ms,st,ud) s) = (x = ARM_READ_STATUS a s) /\ ~(a IN st)) /\
  (!x s. aUndef x IN (arm2set s) = (x = ARM_READ_UNDEF s)) /\
  (!x s. aUndef x IN (arm2set' (rs,ms,st,ud) s) = (x = ARM_READ_UNDEF s) /\ ud) /\
  (!x s. aUndef x IN (arm2set'' (rs,ms,st,ud) s) = (x = ARM_READ_UNDEF s) /\ ~ud)``,
  SRW_TAC [] [arm2set'_def,arm2set''_def,arm2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val arm2set''_11 = prove(
  ``!y y' s s'. (arm2set'' y' s' = arm2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st ud. y = (r,m,st,ud)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud'. y' = (r',m',st',ud')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] THENL [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. aReg a x IN arm2set'' y s) = (?x. aReg a x IN arm2set'' y' s'))` by ALL_TAC,
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. aMem a x IN arm2set'' y s) = (?x. aMem a x IN arm2set'' y' s'))` by ALL_TAC,
    `?a. ~(a IN st = a IN st')` by METIS_TAC [EXTENSION]
    \\ `~((?x. aStatus a x IN arm2set'' y s) = (?x. aStatus a x IN arm2set'' y' s'))` by ALL_TAC,
    `~((?x. aUndef x IN arm2set'' y s) = (?x. aUndef x IN arm2set'' y' s'))` by ALL_TAC]
  \\ REPEAT (FULL_SIMP_TAC bool_ss [IN_arm2set] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (K ALL_TAC)     
  \\ FULL_SIMP_TAC bool_ss [IN_arm2set] \\ METIS_TAC []);

val DELETE_arm2set = prove(``
  (!a s. (arm2set' (rs,ms,st,ud) s) DELETE aReg a (ARM_READ_REG a s) =
         (arm2set' (rs DELETE a,ms,st,ud) s)) /\ 
  (!b s. (arm2set' (rs,ms,st,ud) s) DELETE aMem b (ARM_READ_MEM b s) =
         (arm2set' (rs,ms DELETE b,st,ud) s)) /\ 
  (!c s. (arm2set' (rs,ms,st,ud) s) DELETE aStatus c (ARM_READ_STATUS c s) =
         (arm2set' (rs,ms,st DELETE c,ud) s)) /\ 
  (!s. (arm2set' (rs,ms,st,ud) s) DELETE aUndef (ARM_READ_UNDEF s) =
       (arm2set' (rs,ms,st,F) s))``,
  SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_arm2set = prove(``
  (arm2set' (rs,ms,st,ud) s = {}) = (rs = {}) /\ (ms = {}) /\ (st = {}) /\ ~ud``,
  Cases_on `ud`
  \\ SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ METIS_TAC []);
    

(* ----------------------------------------------------------------------------- *)
(* Defining the ARM_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val aR_def = Define `aR a x = SEP_EQ {aReg a x}`;
val aM_def = Define `aM a x = SEP_EQ {aMem a x}`;
val aS1_def = Define `aS1 a x = SEP_EQ {aStatus a x}`;
val aU1_def = Define `aU1 x = SEP_EQ {aUndef x}`;

val aPC_def = Define `aPC x = aR 15w x * aU1 F * cond (ALIGNED x)`;

val aS_def = Define `aS (n,z,c,v) = aS1 sN n * aS1 sZ z * aS1 sC c * aS1 sV v`;

val ARM_NEXT_REL_def = Define `ARM_NEXT_REL s s' = (NEXT_ARM_MMU NO_CP (s:unit arm_sys_state) = s')`;

val ARM_INSTR_def = Define `ARM_INSTR (a:word32,c:word32) = { aMem (ADDR30 a) c }`;

val ARM_MODEL_def = Define `ARM_MODEL = (arm2set, ARM_NEXT_REL, ARM_INSTR)`;

val aLR_def = Define `aLR x = aR 14w x * cond (ALIGNED x)`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_arm2set]
  ``p (arm2set' y s) ==> (?u v. SPLIT (arm2set s) (u,v) /\ p u /\ (\v. v = arm2set'' y s) v)``;

val ARM_SPEC_SEMANTICS = store_thm("ARM_SPEC_SEMANTICS",
  ``SPEC ARM_MODEL p {} q =
    !y s seq. p (arm2set' y s) /\ rel_sequence ARM_NEXT_REL seq s ==>
              ?k. q (arm2set' y (seq k)) /\ (arm2set'' y s = arm2set'' y (seq k))``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_def,ARM_MODEL_def,STAR_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_arm2set_EXISTS] \\ METIS_TAC [])    
  \\ Q.PAT_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o 
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = arm2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_arm2set_EXISTS]
  \\ IMP_RES_TAC arm2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC ARM_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_arm2set = store_thm("STAR_arm2set",
  ``((aR a x * p) (arm2set' (rs,ms,st,ud) s) =
      (x = ARM_READ_REG a s) /\ a IN rs /\ p (arm2set' (rs DELETE a,ms,st,ud) s)) /\ 
    ((aM b y * p) (arm2set' (rs,ms,st,ud) s) =
      (y = ARM_READ_MEM b s) /\ b IN ms /\ p (arm2set' (rs,ms DELETE b,st,ud) s)) /\ 
    ((aS1 c z * p) (arm2set' (rs,ms,st,ud) s) =
      (z = ARM_READ_STATUS c s) /\ c IN st /\ p (arm2set' (rs,ms,st DELETE c,ud) s)) /\ 
    ((aU1 q * p) (arm2set' (rs,ms,st,ud) s) =
      (q = ARM_READ_UNDEF s) /\ ud /\ p (arm2set' (rs,ms,st,F) s)) /\ 
    ((cond g * p) (arm2set' (rs,ms,st,ud) s) =
      g /\ p (arm2set' (rs,ms,st,ud) s))``,
  SIMP_TAC std_ss [aR_def,aS1_def,aM_def,EQ_STAR,INSERT_SUBSET,cond_STAR,aU1_def,
    EMPTY_SUBSET,IN_arm2set,GSYM DELETE_DEF]
  \\ Cases_on `x = ARM_READ_REG a s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `y = ARM_READ_MEM b s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `z = ARM_READ_STATUS c s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `q = ARM_READ_UNDEF s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC]);  

val CODE_POOL_arm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) = (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_arm2set = store_thm("CODE_POOL_arm2set",
  ``CODE_POOL ARM_INSTR {(p,c)} (arm2set' (rs,ms,st,ud) s) =
      ({ADDR30 p} = ms) /\ (rs = {}) /\ (st = {}) /\ ~ud /\ (ARM_READ_MEM (ADDR30 p) s = c)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,ARM_INSTR_def,CODE_POOL_arm2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_arm2set]
  \\ Cases_on `c = ARM_READ_MEM (ADDR30 p) s` 
  \\ ASM_SIMP_TAC std_ss [DELETE_arm2set,EMPTY_arm2set]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC]);

val UPDATE_arm2set'' = store_thm("UPDATE_arm2set''",
  ``(!a x. a IN rs ==> (arm2set'' (rs,ms,st,ud) (ARM_WRITE_REG a x s) = arm2set'' (rs,ms,st,ud) s)) /\
    (!a x. a IN ms ==> (arm2set'' (rs,ms,st,ud) (ARM_WRITE_MEM a x s) = arm2set'' (rs,ms,st,ud) s)) /\
    (!b. (arm2set'' (rs,ms,st,T) (ARM_WRITE_UNDEF b s) = arm2set'' (rs,ms,st,T) s)) /\
    (!x. sN IN st /\ sZ IN st /\ sC IN st /\ sV IN st ==> 
      (arm2set'' (rs,ms,st,ud) (ARM_WRITE_STATUS x s) = arm2set'' (rs,ms,st,ud) s))``,
  SIMP_TAC std_ss [arm2set_def,arm2set''_def,arm2set'_def,EXTENSION,IN_UNION,
    IN_IMAGE,IN_DIFF,IN_UNIV,NOT_IN_EMPTY,IN_INSERT,ARM_READ_WRITE,PUSH_IN_INTO_IF]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC std_ss [arm_el_distinct,arm_el_11] \\ METIS_TAC []);

val FORMAT_ALIGNED = store_thm("FORMAT_ALIGNED",
  ``ALIGNED a ==> (FORMAT UnsignedWord ((1 >< 0) a) x = x)``,
  REWRITE_TAC [ALIGNED_def] THEN STRIP_TAC THEN IMP_RES_TAC EXISTS_ADDR30
  THEN ASM_SIMP_TAC bool_ss [ADDR32_eq_0] THEN SRW_TAC [] [armTheory.FORMAT_def]);

val ARM_SPEC_CODE = (RW [GSYM ARM_MODEL_def] o SIMP_RULE std_ss [ARM_MODEL_def] o prove)
  (``SPEC ARM_MODEL (CODE_POOL (SND (SND ARM_MODEL)) c * p) {} (CODE_POOL (SND (SND ARM_MODEL)) c * q) =
    SPEC ARM_MODEL p c q``,
  REWRITE_TAC [SPEC_CODE]);

val IMP_ARM_SPEC_LEMMA = prove(
  ``!p q. 
      (!rs ms st ud s. ?s'.  
        (p (arm2set' (rs,ms,st,ud) s) ==> 
        (NEXT_ARM_MMU NO_CP s = s') /\ q (arm2set' (rs,ms,st,ud) s') /\ 
        (arm2set'' (rs,ms,st,ud) s = arm2set'' (rs,ms,st,ud) s'))) ==>
      SPEC ARM_MODEL p {} q``,
  REWRITE_TAC [ARM_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,ARM_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC [PAIR]);

val IMP_ARM_SPEC = save_thm("IMP_ARM_SPEC", 
  (RW1 [STAR_COMM] o RW [ARM_SPEC_CODE] o
   SPECL [``CODE_POOL ARM_INSTR {(p,c)} * p'``,
          ``CODE_POOL ARM_INSTR {(p,c)} * q'``]) IMP_ARM_SPEC_LEMMA);

val aS_HIDE = store_thm("aS_HIDE",
  ``~aS = ~aS1 sN * ~aS1 sZ * ~aS1 sC * ~aS1 sV``,
  SIMP_TAC std_ss [SEP_HIDE_def,aS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [aS_def,PAIR]);


(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates -- word-sized entities                             *)
(* ----------------------------------------------------------------------------- *)

val aMEMORY_SET_def = Define `
  aMEMORY_SET df f = { aMem (ADDR30 a) (f a) | a | a IN df /\ ALIGNED a }`;

val aMEMORY_def = Define `aMEMORY df f = SEP_EQ (aMEMORY_SET df f)`;

val ADDR30_11 = prove(
  ``!a a'. ALIGNED a /\ ALIGNED a' /\ (ADDR30 a = ADDR30 a') ==> (a = a')``,
  METIS_TAC [EXISTS_ADDR30,ALIGNED_def,ADDR30_ADDR32]);

val aMEMORY_INSERT = store_thm("aMEMORY_INSERT",
  ``!s. ALIGNED a /\ ~(a IN s) ==>
        (aM (ADDR30 a) w * aMEMORY s f = aMEMORY (a INSERT s) ((a =+ w) f))``,
  SIMP_TAC bool_ss [FUN_EQ_THM,cond_STAR,aMEMORY_def,APPLY_UPDATE_THM,aM_def]  
  \\ SIMP_TAC std_ss [STAR_def,SEP_EQ_def,SPLIT_def]
  \\ REPEAT STRIP_TAC
  \\ `DISJOINT {aMem (ADDR30 a) w} (aMEMORY_SET s f)` by 
   (SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,
      aMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION,IN_INSERT,arm_el_11]   
    \\ STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `~(a = a')` by METIS_TAC []
    \\ METIS_TAC [ADDR30_11,ADDR30_def])
  \\ `{aMem (ADDR30 a) w} UNION aMEMORY_SET s f =
      aMEMORY_SET (a INSERT s) ((a =+ w) f)` by 
   (SIMP_TAC std_ss [IN_UNION,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_INSERT,
                     aMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ METIS_TAC [APPLY_UPDATE_THM])
  \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);
    
val aMEMORY_INTRO = store_thm("aMEMORY_INTRO",
  ``SPEC ARM_MODEL (aM (ADDR30 a) v * P) c (aM (ADDR30 a) w * Q) ==>
    ALIGNED a /\ a IN df ==>
    SPEC ARM_MODEL (aMEMORY df ((a =+ v) f) * P) c (aMEMORY df ((a =+ w) f) * Q)``,
  REPEAT STRIP_TAC
  \\ (IMP_RES_TAC o GEN_ALL o REWRITE_RULE [AND_IMP_INTRO] o 
     SIMP_RULE std_ss [INSERT_DELETE,IN_DELETE] o
     DISCH ``a:word32 IN df`` o Q.SPEC `df DELETE a` o GSYM) aMEMORY_INSERT
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ REWRITE_TAC [STAR_ASSOC]
  \\ MATCH_MP_TAC SPEC_FRAME
  \\ FULL_SIMP_TAC bool_ss [AC STAR_COMM STAR_ASSOC]);


(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates -- byte-sized entities                             *)
(* ----------------------------------------------------------------------------- *)

val BYTE_MEMORY_MAP_def = Define `
  (BYTE_MEMORY_MAP (f:word32->word8) x):word32 = 
    (SET_BYTE 0w (f (ADDR32 (ADDR30 x) + 0w)) o
     SET_BYTE 1w (f (ADDR32 (ADDR30 x) + 1w)) o
     SET_BYTE 2w (f (ADDR32 (ADDR30 x) + 2w)) o
     SET_BYTE 3w (f (ADDR32 (ADDR30 x) + 3w))) 0w`;


val aBYTE_MEMORY_def = Define `
  aBYTE_MEMORY (df:word32 set) (f:word32->word8) = 
    aMEMORY { ADDR32 (ADDR30 x) | x IN df } (BYTE_MEMORY_MAP f)`;

val SET_BYTE_EQ = prove(
  ``!x y z w. SET_BYTE x y (SET_BYTE x z w) = SET_BYTE x y w``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [fcpTheory.CART_EQ]
  \\ SIMP_TAC std_ss [word_modify_def,n2w_11,fcpTheory.FCP_BETA,SET_BYTE_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `i < 8`
  THEN1 (`~(8 <= i) /\ ~(16 <= i) /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `i < 16`
  THEN1 (`8 <= i /\ ~(16 <= i) /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `i < 24`
  THEN1 (`8 <= i /\ 16 <= i /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ `8 <= i /\ 16 <= i /\ 24 <= i` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC []);

val SET_BYTE_NEQ = prove(
  ``!x y z w. ~(x = y) ==> (SET_BYTE x z (SET_BYTE y q w) = SET_BYTE y q (SET_BYTE x z w))``,
  Cases_word \\ Cases_word \\ SIMP_TAC std_ss [SET_BYTE_def]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ REWRITE_TAC [fcpTheory.CART_EQ]
  \\ SIMP_TAC std_ss [word_modify_def,n2w_11,fcpTheory.FCP_BETA,SET_BYTE_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `i < 8`
  THEN1 (`~(8 <= i) /\ ~(16 <= i) /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Cases_on `i < 16`
  THEN1 (`8 <= i /\ ~(16 <= i) /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Cases_on `i < 24`
  THEN1 (`8 <= i /\ 16 <= i /\ ~(24 <= i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ `8 <= i /\ 16 <= i /\ 24 <= i` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC []);

val GET_BYTE_SET_BYTE_EQ = prove(
  ``!x y w. GET_BYTE x (SET_BYTE x y w) = y``,
  REVERSE (SRW_TAC [] [fcpTheory.CART_EQ]
  \\ `i < dimindex (:32)` by (SRW_TAC [] [] \\ DECIDE_TAC)
  \\ `i + 8 < dimindex (:32)` by (SRW_TAC [] [] \\ DECIDE_TAC)
  \\ `i + 16 < dimindex (:32)` by (SRW_TAC [] [] \\ DECIDE_TAC)
  \\ `i + 24 < dimindex (:32)` by (SRW_TAC [] [] \\ DECIDE_TAC)
  \\ `i + 16 < 24 /\ i + 8 < 16` by DECIDE_TAC
  \\ Cases_on `x = 0w` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `x = 1w` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `x = 2w` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `x = 3w` \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (REPEAT (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`x`,`x`) \\ Cases
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ REPEAT STRIP_TAC \\ `F` by DECIDE_TAC)
  \\ (SRW_TAC [] [GET_BYTE_def,word_extract_def,w2w,word_bits_def]
    \\ ASM_SIMP_TAC std_ss [fcpTheory.FCP_BETA]
    \\ SIMP_TAC (std_ss++SIZES_ss) [SET_BYTE_def,n2w_11]
    \\ ASM_SIMP_TAC std_ss [word_modify_def,fcpTheory.FCP_BETA]
    \\ REPEAT STRIP_TAC \\ REPEAT EQ_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
    \\ REPEAT (`F` by DECIDE_TAC) \\ REPEAT DECIDE_TAC));

val WORD2_CASES = prove(
  ``!x:word2. (x = 0w) \/ (x = 1w) \/ (x = 2w) \/ (x = 3w)``,
  Cases \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC);

val GET_BYTE_SET_BYTE_NEQ = prove(
  ``!x y w. ~(x = y) ==> (GET_BYTE x (SET_BYTE y z w) = GET_BYTE x w)``,
  STRIP_TAC \\ STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `x` WORD2_CASES)
  \\ STRIP_ASSUME_TAC (Q.SPEC `y` WORD2_CASES)
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [] \\ REPEAT STRIP_TAC
  \\ (SRW_TAC [] [GET_BYTE_def,SET_BYTE_def]  
    \\ SRW_TAC [] [fcpTheory.CART_EQ]
    \\ SRW_TAC [] [GET_BYTE_def,word_extract_def,w2w,word_bits_def]
    \\ `i + 8 < 16 /\ i + 16 < 24 /\ i + 24 < 32 /\ i + 16 < 32 /\ i + 8 < 32 /\ i < 32` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [fcpTheory.FCP_BETA,word_modify_def]
    \\ REPEAT STRIP_TAC \\ REPEAT EQ_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
    \\ REPEAT (`F` by DECIDE_TAC) \\ REPEAT DECIDE_TAC));

val GET_BYTE_SET_BYTE = prove(
  ``!x y w. GET_BYTE x (SET_BYTE y z w) = if x = y then z else GET_BYTE x w``,
  METIS_TAC [GET_BYTE_SET_BYTE_EQ,GET_BYTE_SET_BYTE_NEQ]);

val aBYTE_MEMORY_INTRO_LEMMA = prove(
  ``SPEC ARM_MODEL (P * aM (ADDR30 (ADDR32 (ADDR30 a))) (BYTE_MEMORY_MAP f a)) c 
                   (Q (FORMAT UnsignedByte ((1 >< 0) a) (BYTE_MEMORY_MAP f a)) * 
                        aM (ADDR30 (ADDR32 (ADDR30 a))) (SET_BYTE ((1 >< 0) a) w (BYTE_MEMORY_MAP f a))) ==>
    a IN df ==>
    SPEC ARM_MODEL (P * aBYTE_MEMORY df f) c 
                   (Q (w2w (f a)) * aBYTE_MEMORY df ((a =+ w) f))``,
  ONCE_REWRITE_TAC [STAR_COMM] \\ REPEAT STRIP_TAC  
  \\ IMP_RES_TAC aMEMORY_INTRO
  \\ REPEAT (Q.PAT_ASSUM `!x.b` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [ALIGNED_ADDR32,aBYTE_MEMORY_def]
  \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPEC `{ADDR32 (ADDR30 x) | x IN df}`)
  \\ `ADDR32 (ADDR30 a) IN {ADDR32 (ADDR30 x) | x IN df}` by 
    (FULL_SIMP_TAC std_ss [GSPECIFICATION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPEC `BYTE_MEMORY_MAP f`)
  \\ `(ADDR32 (ADDR30 a) =+ BYTE_MEMORY_MAP f a) (BYTE_MEMORY_MAP f) = BYTE_MEMORY_MAP f` by 
   (SIMP_TAC std_ss [FUN_EQ_THM,BYTE_MEMORY_MAP_def,APPLY_UPDATE_THM]
    \\ STRIP_TAC \\ Cases_on `x = ADDR32 (ADDR30 a)` 
    \\ ASM_SIMP_TAC std_ss [ADDR30_ADDR32])
  \\ `w2w (f a) = FORMAT UnsignedByte ((1 >< 0) a) (BYTE_MEMORY_MAP f a)` by
   (SRW_TAC [] [FORMAT_def,BYTE_MEMORY_MAP_def] 
    \\ STRIP_ASSUME_TAC (Q.SPEC `a` EXISTS_ADDR32)
    \\ ASM_SIMP_TAC std_ss [ADDR30_ADDR32,lower_ADDR32_ADD,
           EVAL ``((1 >< 0) (0w:word32)):word2``, EVAL ``((1 >< 0) (1w:word32)):word2``,
           EVAL ``((1 >< 0) (2w:word32)):word2``, EVAL ``((1 >< 0) (3w:word32)):word2``]    
    \\ SIMP_TAC (std_ss++SIZES_ss) [GET_BYTE_SET_BYTE,n2w_11]    
    \\ REWRITE_TAC [WORD_ADD_0])
  \\ REVERSE (`!y. aMEMORY y ((ADDR32 (ADDR30 a) =+ SET_BYTE ((1 >< 0) a) w (BYTE_MEMORY_MAP f a))
                   (BYTE_MEMORY_MAP f)) = aMEMORY y (BYTE_MEMORY_MAP ((a =+ w) f))` by ALL_TAC)
  THEN1 FULL_SIMP_TAC std_ss []
  \\ `!b. ALIGNED b ==> (((ADDR32 (ADDR30 a) =+ SET_BYTE ((1 >< 0) a) w (BYTE_MEMORY_MAP f a))
                   (BYTE_MEMORY_MAP f) b = BYTE_MEMORY_MAP ((a =+ w) f) b))` by ALL_TAC THENL [    
    REPEAT STRIP_TAC \\ IMP_RES_TAC (RW [ALIGNED_INTRO] EXISTS_ADDR30)
    \\ ASM_SIMP_TAC std_ss [BYTE_MEMORY_MAP_def,ADDR30_ADDR32,APPLY_UPDATE_THM,ADDR32_11]
    \\ REVERSE (Cases_on `y = ADDR30 a` \\ ASM_SIMP_TAC std_ss []) THENL [
      STRIP_ASSUME_TAC (Q.SPEC `a` EXISTS_ADDR32)
      \\ FULL_SIMP_TAC std_ss [ADDR30_ADDR32,ADDR32_NEQ_ADDR32,ADDR32_11],      
      STRIP_ASSUME_TAC (Q.SPEC `a` EXISTS_ADDR32)
      \\ FULL_SIMP_TAC std_ss [ADDR30_ADDR32,ADDR32_NEQ_ADDR32,ADDR32_11,lower_ADDR32_ADD,
           EVAL ``((1 >< 0) (0w:word32)):word2``, EVAL ``((1 >< 0) (1w:word32)):word2``,
           EVAL ``((1 >< 0) (2w:word32)):word2``, EVAL ``((1 >< 0) (3w:word32)):word2``]
      \\ METIS_TAC [SET_BYTE_EQ,SET_BYTE_NEQ,
           EVAL ``~(0w = 1w:word2) /\ ~(0w = 2w:word2) /\ ~(0w = 3w:word2) /\ 
                  ~(1w = 2w:word2) /\ ~(1w = 3w:word2) /\ ~(2w = 3w:word2)``]],
    SIMP_TAC std_ss [aMEMORY_def] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (SEQ_EQ x = SEQ_EQ y)``)
    \\ REWRITE_TAC [aMEMORY_SET_def]
    \\ SIMP_TAC std_ss [EXTENSION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `a'`
    \\ RES_TAC \\ ASM_SIMP_TAC std_ss []]);

val aBYTE_MEMORY_INTRO = save_thm("aBYTE_MEMORY_INTRO",
  RW [ADDR30_ADDR32] aBYTE_MEMORY_INTRO_LEMMA);

val SET_BYTE_BYTE_MEMORY_MAP = prove(
  ``!f a. SET_BYTE ((1 >< 0) a) (f a) (BYTE_MEMORY_MAP f a) = BYTE_MEMORY_MAP f a``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `a` EXISTS_ADDR32)
  \\ ASM_SIMP_TAC std_ss [BYTE_MEMORY_MAP_def,lower_ADDR32_ADD,ADDR30_ADDR32,
           EVAL ``((1 >< 0) (0w:word32)):word2``, EVAL ``((1 >< 0) (1w:word32)):word2``,
           EVAL ``((1 >< 0) (2w:word32)):word2``, EVAL ``((1 >< 0) (3w:word32)):word2``]   
  \\ METIS_TAC [SET_BYTE_EQ,SET_BYTE_NEQ,
           EVAL ``~(0w = 1w:word2) /\ ~(0w = 2w:word2) /\ ~(0w = 3w:word2) /\ 
                  ~(1w = 2w:word2) /\ ~(1w = 3w:word2) /\ ~(2w = 3w:word2)``]);

val lemma = prove(``!a f. (a =+ f a) f = f``,SIMP_TAC std_ss [APPLY_UPDATE_THM,FUN_EQ_THM]);

val aBYTE_MEMORY_INTRO2 = save_thm("aBYTE_MEMORY_INTRO2",
  RW [lemma,SET_BYTE_BYTE_MEMORY_MAP] (Q.INST [`w`|->`f a`] aBYTE_MEMORY_INTRO));

val EXTRACT_BYTE = store_thm("EXTRACT_BYTE",  
  ``!w:word32. (7 >< 0) w = (w2w w):word8``,
  Cases \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_def,word_extract_def,word_bits_n2w]
  \\ SIMP_TAC (std_ss++SIZES_ss) [bitTheory.BITS_THM,w2n_n2w,n2w_11]
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``256 * 16777216``),MOD_MULT_MOD,
       EVAL ``0 < 256``, EVAL ``0 < 16777216``,MOD_MOD]);


val _ = export_theory();
