
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory;
open finite_mapTheory;

open set_sepTheory progTheory;
open armTheory arm_coretypesTheory arm_stepTheory armLib;

val _ = new_theory "prog_arm";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The ARM set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  arm_el =  aReg of word4 => word32
          | aMem of word32 => word8
          | aStatus of arm_bit => bool
          | aCPSR_Reg of word32
          | aUndef of bool`;

val arm_el_11 = DB.fetch "-" "arm_el_11";
val arm_el_distinct = DB.fetch "-" "arm_el_distinct";

val _ = Parse.type_abbrev("arm_set",``:arm_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from ARM-state record to arm_set                                   *)
(* ----------------------------------------------------------------------------- *)

Definition ARM_OK_def:
  ARM_OK state <=>
    (ARM_ARCH state = ARMv6) /\ (ARM_EXTENSIONS state = {}) /\
    (ARM_UNALIGNED_SUPPORT state) /\ (ARM_READ_EVENT_REGISTER state) /\
    ~(ARM_READ_INTERRUPT_WAIT state) /\ ~(ARM_READ_SCTLR sctlrV state) /\
    (ARM_READ_SCTLR sctlrA state) /\ ~(ARM_READ_SCTLR sctlrU state) /\
    (ARM_READ_IT state = 0w) /\ ~(ARM_READ_STATUS psrJ state) /\
    ~(ARM_READ_STATUS psrT state) /\ ~(ARM_READ_STATUS psrE state) /\
    (ARM_MODE state = 16w)
End

val ARM_READ_UNDEF_def = Define `ARM_READ_UNDEF s = ~(ARM_OK s)`;

val ARM_READ_MASKED_CPSR_def = Define `
  ARM_READ_MASKED_CPSR s = (26 '' 0) (encode_psr (ARM_READ_CPSR s))`;

val arm2set'_def = Define `
  arm2set' (rs,ms,st,cp,ud) (s:arm_state) =
    IMAGE (\a. aReg a (ARM_READ_REG a s)) rs UNION
    IMAGE (\a. aMem a (ARM_READ_MEM a s)) ms UNION
    IMAGE (\a. aStatus a (ARM_READ_STATUS a s)) st UNION
    (if cp then { aCPSR_Reg (ARM_READ_MASKED_CPSR s) } else {}) UNION
    (if ud then { aUndef (ARM_READ_UNDEF s) } else {})`;

val arm2set_def   = Define `arm2set s = arm2set' (UNIV,UNIV,UNIV,T,T) s`;
val arm2set''_def = Define `arm2set'' x s = arm2set s DIFF arm2set' x s`;

(* theorems *)

val arm2set'_SUBSET_arm2set = prove(
  ``!y s. arm2set' y s SUBSET arm2set s``,
  Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
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
  ``!g x y z. x IN (if g then y else z) <=> if g then x IN y else x IN z``;

val SUBSET_arm2set = prove(
  ``!u s. u SUBSET arm2set s <=> ?y. u = arm2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [arm2set'_SUBSET_arm2set]
  \\ Q.EXISTS_TAC `({ a | a| ?x. aReg a x IN u },
       { a | a| ?x. aMem a x IN u },{ a | a| ?x. aStatus a x IN u },
       (?y. aCPSR_Reg y IN u),(?y. aUndef y IN u))`
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,arm2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV,PUSH_IN_INTO_IF]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_X_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC) \\ FULL_SIMP_TAC std_ss [arm_el_11,arm_el_distinct]);

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
  (!r x s. aReg r x IN (arm2set s) ⇔ (x = ARM_READ_REG r s)) /\
  (!r x s. aReg r x IN (arm2set' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_REG r s) /\ r IN rs) /\
  (!r x s. aReg r x IN (arm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_REG r s) /\ ~(r IN rs)) /\
  (!p x s. aMem p x IN (arm2set s) ⇔ (x = ARM_READ_MEM p s)) /\
  (!p x s. aMem p x IN (arm2set' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_MEM p s) /\ p IN ms) /\
  (!p x s. aMem p x IN (arm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_MEM p s) /\ ~(p IN ms)) /\
  (!a x s. aStatus a x IN (arm2set s) ⇔ (x = ARM_READ_STATUS a s)) /\
  (!a x s. aStatus a x IN (arm2set' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_STATUS a s) /\ a IN st) /\
  (!a x s. aStatus a x IN (arm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_STATUS a s) /\ ~(a IN st)) /\
  (!x s. aCPSR_Reg x IN (arm2set s) ⇔ (x = ARM_READ_MASKED_CPSR s)) /\
  (!x s. aCPSR_Reg x IN (arm2set' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_MASKED_CPSR s) /\ cp) /\
  (!x s. aCPSR_Reg x IN (arm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_MASKED_CPSR s) /\ ~cp) /\
  (!x s. aUndef x IN (arm2set s) ⇔ (x = ARM_READ_UNDEF s)) /\
  (!x s. aUndef x IN (arm2set' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_UNDEF s) /\ ud) /\
  (!x s. aUndef x IN (arm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = ARM_READ_UNDEF s) /\ ~ud)``,
  SRW_TAC [] [arm2set'_def,arm2set''_def,arm2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

Theorem arm2set''_11[local]:
  !y y' s s'. (arm2set'' y' s' = arm2set'' y s) ==> (y = y')
Proof
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st cp ud. y = (r,m,st,cp,ud)` by METIS_TAC [PAIR]
  \\ `?r' m' st' cp' ud'. y' = (r',m',st',cp',ud')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ, Excl "lift_disj_eq"] THENL [
    `?a. ~(a IN r ⇔ a IN r')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aReg a x IN arm2set'' y s) = (?x. aReg a x IN arm2set'' y' s'))`,
    `?a. ~(a IN m ⇔ a IN m')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aMem a x IN arm2set'' y s) = (?x. aMem a x IN arm2set'' y' s'))`,
    `?a. ~(a IN st ⇔ a IN st')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aStatus a x IN arm2set'' y s) = (?x. aStatus a x IN arm2set'' y' s'))`,
    sg `~((?x. aCPSR_Reg x IN arm2set'' y s) = (?x. aCPSR_Reg x IN arm2set'' y' s'))`,
    sg `~((?x. aUndef x IN arm2set'' y s) = (?x. aUndef x IN arm2set'' y' s'))`]
  \\ REPEAT (FULL_SIMP_TAC bool_ss [IN_arm2set] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `arm2set'' _ _ = arm2set'' _ _` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [IN_arm2set] \\ METIS_TAC []
QED

val DELETE_arm2set = prove(``
  (!a s. (arm2set' (rs,ms,st,cp,ud) s) DELETE aReg a (ARM_READ_REG a s) =
         (arm2set' (rs DELETE a,ms,st,cp,ud) s)) /\
  (!b s. (arm2set' (rs,ms,st,cp,ud) s) DELETE aMem b (ARM_READ_MEM b s) =
         (arm2set' (rs,ms DELETE b,st,cp,ud) s)) /\
  (!c s. (arm2set' (rs,ms,st,cp,ud) s) DELETE aStatus c (ARM_READ_STATUS c s) =
         (arm2set' (rs,ms,st DELETE c,cp,ud) s)) /\
  (!s. (arm2set' (rs,ms,st,cp,ud) s) DELETE aCPSR_Reg (ARM_READ_MASKED_CPSR s) =
       (arm2set' (rs,ms,st,F,ud) s)) /\
  (!s. (arm2set' (rs,ms,st,cp,ud) s) DELETE aUndef (ARM_READ_UNDEF s) =
       (arm2set' (rs,ms,st,cp,F) s))``,
  SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_arm2set = prove(``
  (arm2set' (rs,ms,st,cp,ud) s = {}) ⇔ (rs = {}) /\ (ms = {}) /\ (st = {}) /\ ~cp /\ ~ud``,
  Cases_on `ud`
  \\ SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ METIS_TAC []);

val ARM_READ_MASKED_CPSR_THM =
 (SIMP_CONV std_ss [ARM_READ_MASKED_CPSR_def,encode_psr_def,word_slice_def] THENC
  ONCE_REWRITE_CONV [METIS_PROVE [] ``p /\ q ⇔ p /\ (p ==> q)``] THENC
  SIMP_CONV (std_ss++SIZES_ss) [
    fcpTheory.FCP_BETA,DECIDE “(i<=31⇔i<32:num)/\(i<=26⇔i<27)”] THENC
  ONCE_REWRITE_CONV [GSYM (METIS_PROVE [] ``p /\ q ⇔ p /\ (p ==> q)``)] THENC
  SIMP_CONV std_ss [DECIDE ``i<27 /\ i<32 ⇔ i<27``])
    ``ARM_READ_MASKED_CPSR s``


(* ----------------------------------------------------------------------------- *)
(* Defining the ARM_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val aR_def = Define `aR a x = SEP_EQ {aReg a x}`;
val aM1_def = Define `aM1 a x = SEP_EQ {aMem a x}`;
val aS1_def = Define `aS1 a x = SEP_EQ {aStatus a x}`;
val aU1_def = Define `aU1 x = SEP_EQ {aUndef x}`;
val aCPSR_def = Define `aCPSR x = SEP_EQ {aCPSR_Reg x}`;

val aLR_def = Define `aLR lr = cond (ALIGNED lr) * aR 14w lr`;

val aM_def = Define `
  aM a (w:word32) =
    aM1 a        ((7 >< 0) w) *
    aM1 (a + 1w) ((7 >< 0) (w >> 8)) *
    aM1 (a + 2w) ((7 >< 0) (w >> 16)) *
    aM1 (a + 3w) ((7 >< 0) (w >> 24))`;

val aPC_def = Define `aPC x = aR 15w x * aU1 F * cond (ALIGNED x)`;

val aS_def = Define `aS (n,z,c,v) = aS1 psrN n * aS1 psrZ z * aS1 psrC c * aS1 psrV v`;

val ARM_NEXT_REL_def = Define `ARM_NEXT_REL s s' = (ARM_NEXT NoInterrupt s = SOME s')`;

val ARM_INSTR_def    = Define `ARM_INSTR (a,w:word32) =
  { aMem (a+3w) ((31 >< 24) w) ;
    aMem (a+2w) ((23 >< 16) w) ;
    aMem (a+1w) ((15 ><  8) w) ;
    aMem (a+0w) (( 7 ><  0) w) }`;

val ARM_MODEL_def = Define `
  ARM_MODEL = (arm2set, ARM_NEXT_REL, ARM_INSTR, (\x y. x = (y:arm_state)),
               (K F):arm_state -> bool)`;

val aST_LIST_def = Define `
  (aST_LIST a [] = emp) /\
  (aST_LIST a (x::xs) = aM a x * aST_LIST (a-4w) xs)`;

val aST_def = Define `aST a xs = aR 13w a * aST_LIST a xs * cond (ALIGNED a)`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_arm2set]
  ``p (arm2set' y s) ==> (?u v. SPLIT (arm2set s) (u,v) /\ p u /\ (\v. v = arm2set'' y s) v)``;

val ARM_SPEC_SEMANTICS = store_thm("ARM_SPEC_SEMANTICS",
  ``SPEC ARM_MODEL p {} q =
    !y s seq. p (arm2set' y s) /\ rel_sequence ARM_NEXT_REL seq s ==>
              ?k. q (arm2set' y (seq k)) /\ (arm2set'' y s = arm2set'' y (seq k))``,
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,ARM_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_arm2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = arm2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_arm2set_EXISTS]
  \\ IMP_RES_TAC arm2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC ARM_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

Theorem STAR_arm2set:
    ((aR a x * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      (x = ARM_READ_REG a s) /\ a IN rs /\ p (arm2set' (rs DELETE a,ms,st,cp,ud) s)) /\
    ((aM1 b y * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      (y = ARM_READ_MEM b s) /\ b IN ms /\ p (arm2set' (rs,ms DELETE b,st,cp,ud) s)) /\
    ((aS1 c z * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      (z = ARM_READ_STATUS c s) /\ c IN st /\ p (arm2set' (rs,ms,st DELETE c,cp,ud) s)) /\
    ((aCPSR t * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      (t = ARM_READ_MASKED_CPSR s) /\ cp /\ p (arm2set' (rs,ms,st,F,ud) s)) /\
    ((aU1 q * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      (q = ARM_READ_UNDEF s) /\ ud /\ p (arm2set' (rs,ms,st,cp,F) s)) /\
    ((cond g * p) (arm2set' (rs,ms,st,cp,ud) s) ⇔
      g /\ p (arm2set' (rs,ms,st,cp,ud) s))
Proof
  SIMP_TAC std_ss [aR_def,aS1_def,aM1_def,EQ_STAR,INSERT_SUBSET,cond_STAR,aU1_def,
    aCPSR_def,EMPTY_SUBSET,IN_arm2set,GSYM DELETE_DEF]
  \\ Cases_on `x = ARM_READ_REG a s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `y = ARM_READ_MEM b s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `z = ARM_READ_STATUS c s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `t = ARM_READ_MASKED_CPSR s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ Cases_on `q = ARM_READ_UNDEF s` \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC]
QED

val CODE_POOL_arm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) ⇔ (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_arm2set_2 = prove(
  ``CODE_POOL ARM_INSTR {(p,c);(q,d)} (arm2set' (rs,ms,st,cp,ud) s) ⇔
      ({p+3w;p+2w;p+1w;p;q+3w;q+2w;q+1w;q} = ms) /\ (rs = {}) /\ (st = {}) /\ ~cp /\ ~ud /\
      (ARM_READ_MEM (p + 0w) s = ( 7 ><  0) c) /\
      (ARM_READ_MEM (p + 1w) s = (15 ><  8) c) /\
      (ARM_READ_MEM (p + 2w) s = (23 >< 16) c) /\
      (ARM_READ_MEM (p + 3w) s = (31 >< 24) c) /\
      (ARM_READ_MEM (q + 0w) s = ( 7 ><  0) d) /\
      (ARM_READ_MEM (q + 1w) s = (15 ><  8) d) /\
      (ARM_READ_MEM (q + 2w) s = (23 >< 16) d) /\
      (ARM_READ_MEM (q + 3w) s = (31 >< 24) d)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,ARM_INSTR_def,CODE_POOL_arm2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_arm2set,INSERT_UNION_EQ]
  \\ Cases_on `(31 >< 24) c = ARM_READ_MEM (p + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) c = ARM_READ_MEM (p + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) c = ARM_READ_MEM (p + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) c = ARM_READ_MEM (p + 0w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(31 >< 24) d = ARM_READ_MEM (q + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) d = ARM_READ_MEM (q + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) d = ARM_READ_MEM (q + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) d = ARM_READ_MEM (q + 0w) s` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [DELETE_arm2set,EMPTY_arm2set,DIFF_INSERT]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,DIFF_EMPTY,EMPTY_arm2set]);

val CODE_POOL_arm2set_1 = prove(
  ``CODE_POOL ARM_INSTR {(p,c)} (arm2set' (rs,ms,st,cp,ud) s) ⇔
      ({p+3w;p+2w;p+1w;p} = ms) /\ (rs = {}) /\ (st = {}) /\ ~cp /\ ~ud /\
      (ARM_READ_MEM (p + 0w) s = ( 7 ><  0) c) /\
      (ARM_READ_MEM (p + 1w) s = (15 ><  8) c) /\
      (ARM_READ_MEM (p + 2w) s = (23 >< 16) c) /\
      (ARM_READ_MEM (p + 3w) s = (31 >< 24) c)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,ARM_INSTR_def,CODE_POOL_arm2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_arm2set]
  \\ Cases_on `(31 >< 24) c = ARM_READ_MEM (p + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) c = ARM_READ_MEM (p + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) c = ARM_READ_MEM (p + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) c = ARM_READ_MEM (p + 0w) s` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [DELETE_arm2set,EMPTY_arm2set,DIFF_INSERT]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,DIFF_EMPTY,EMPTY_arm2set]);

val CODE_POOL_arm2set = save_thm("CODE_POOL_arm2set",
  CONJ CODE_POOL_arm2set_1 CODE_POOL_arm2set_2);

val ARM_WRITE_STS_def = Define `
  ARM_WRITE_STS a x s = if a IN {psrN;psrZ;psrC;psrV;psrQ} then ARM_WRITE_STATUS a x s else s`;

val ARM_WRITE_STS_INTRO = store_thm("ARM_WRITE_STS_INTRO",
  ``(ARM_WRITE_STATUS psrN x s = ARM_WRITE_STS psrN x s) /\
    (ARM_WRITE_STATUS psrZ x s = ARM_WRITE_STS psrZ x s) /\
    (ARM_WRITE_STATUS psrC x s = ARM_WRITE_STS psrC x s) /\
    (ARM_WRITE_STATUS psrV x s = ARM_WRITE_STS psrV x s) /\
    (ARM_WRITE_STATUS psrQ x s = ARM_WRITE_STS psrQ x s)``,
  SIMP_TAC std_ss [ARM_WRITE_STS_def,IN_INSERT]);

val UNDEF_OF_UPDATES = prove(
  ``(!a x. ARM_READ_UNDEF (ARM_WRITE_REG a x s) = ARM_READ_UNDEF s) /\
    (!a x. ARM_READ_UNDEF (ARM_WRITE_MEM a x s) = ARM_READ_UNDEF s) /\
    (!a x. ARM_READ_UNDEF (ARM_WRITE_STS a x s) = ARM_READ_UNDEF s) /\
    (!a x. ARM_READ_UNDEF (ARM_WRITE_MEM_WRITE a x s) = ARM_READ_UNDEF s) /\
    (!a. ARM_READ_UNDEF (ARM_WRITE_MEM_READ a s) = ARM_READ_UNDEF s) /\
    (!a x y. ARM_READ_UNDEF (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = ARM_READ_UNDEF s)``,
  SIMP_TAC std_ss [ARM_READ_UNDEF_def,ARM_OK_def] \\ REPEAT STRIP_TAC
  \\ EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC);

val MASKED_CPSR_OF_UPDATES = prove(
  ``(!a x. ARM_READ_MASKED_CPSR (ARM_WRITE_STS a x s) = ARM_READ_MASKED_CPSR s) /\
    (!a x. ARM_READ_MASKED_CPSR (ARM_WRITE_REG a x s) = ARM_READ_MASKED_CPSR s) /\
    (!a x. ARM_READ_MASKED_CPSR (ARM_WRITE_MEM a x s) = ARM_READ_MASKED_CPSR s) /\
    (!a x. ARM_READ_MASKED_CPSR (ARM_WRITE_MEM_WRITE a x s) = ARM_READ_MASKED_CPSR s) /\
    (!a. ARM_READ_MASKED_CPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_MASKED_CPSR s) /\
    (!a x y. ARM_READ_MASKED_CPSR (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = ARM_READ_MASKED_CPSR s)``,
  SIMP_TAC std_ss [ARM_READ_MASKED_CPSR_THM,ARM_OK_def] \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [ARM_WRITE_STS_def]
    \\ Cases_on `a IN {psrN; psrZ; psrC; psrV; psrQ}` \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
    \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,NOT_IN_EMPTY] \\ EVAL_TAC)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC \\ EVAL_TAC);

val ARM_READ_WRITE = LIST_CONJ [REG_OF_UPDATES,MEM_OF_UPDATES,MASKED_CPSR_OF_UPDATES,
                                UNDEF_OF_UPDATES,CPSR_COMPONENTS_OF_UPDATES]
val _ = save_thm("ARM_READ_WRITE",ARM_READ_WRITE);

val ARM_OK_WRITE_GE = prove(
  ``ARM_OK (ARM_WRITE_GE w4 s) = ARM_OK s``,
  SIMP_TAC std_ss [ARM_OK_def] \\ EVAL_TAC);

(*
val UPDATE_arm2set''_GE = prove(
  ``(!w4. arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_GE w4 s) = arm2set'' (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [arm2set_def,arm2set''_def,arm2set'_def,REG_OF_UPDATES,
    MEM_OF_UPDATES,ARM_READ_WRITE,ARM_READ_UNDEF_def,ARM_OK_WRITE_GE]
*)

val UPDATE_arm2set'' = store_thm("UPDATE_arm2set''",
  ``(!a x. a IN rs ==> (arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_REG a x s) = arm2set'' (rs,ms,st,cp,ud) s)) /\
    (!a x. a IN ms ==> (arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_MEM a x s) = arm2set'' (rs,ms,st,cp,ud) s)) /\
    (!b x. b IN st ==> (arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_STS b x s) = arm2set'' (rs,ms,st,cp,ud) s)) /\
    (!a x. arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_MEM_WRITE a x s) = arm2set'' (rs,ms,st,cp,ud) s) /\
    (!a. arm2set'' (rs,ms,st,cp,ud) (ARM_WRITE_MEM_READ a s) = arm2set'' (rs,ms,st,cp,ud) s) /\
    (!x y. arm2set'' (rs,ms,st,cp,ud) (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
           arm2set'' (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [arm2set_def,arm2set''_def,arm2set'_def,EXTENSION,IN_UNION,
    IN_IMAGE,IN_DIFF,IN_UNIV,NOT_IN_EMPTY,IN_INSERT,ARM_READ_WRITE,PUSH_IN_INTO_IF]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `xx = yy` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC std_ss [arm_el_distinct,arm_el_11]
  \\ IMP_RES_TAC (METIS_PROVE [] ``x IN s /\ ~(y IN s) ==> ~(x = y:'a)``)
  \\ ASM_SIMP_TAC std_ss [ARM_READ_WRITE,UNDEF_OF_UPDATES]
  \\ SIMP_TAC std_ss [ARM_WRITE_STS_def] \\ TRY (Cases_on `b IN {psrN; psrZ; psrC; psrV; psrQ}`)
  \\ FULL_SIMP_TAC std_ss [ARM_READ_WRITE,UNDEF_OF_UPDATES]
  \\ METIS_TAC []);

val ARM_SPEC_CODE =
  SPEC_CODE |> ISPEC ``ARM_MODEL``
  |> SIMP_RULE std_ss [ARM_MODEL_def]
  |> RW [GSYM ARM_MODEL_def];

val IMP_ARM_SPEC_LEMMA = prove(
  ``!p q.
      (!rs ms st cp ud s. ?s'.
        (p (arm2set' (rs,ms,st,cp,ud) s) ==>
        (ARM_NEXT NoInterrupt s = SOME s') /\ q (arm2set' (rs,ms,st,cp,ud) s') /\
        (arm2set'' (rs,ms,st,cp,ud) s = arm2set'' (rs,ms,st,cp,ud) s'))) ==>
      SPEC ARM_MODEL p {} q``,
  SIMP_TAC std_ss [RIGHT_EXISTS_IMP_THM] \\ REWRITE_TAC [ARM_SPEC_SEMANTICS]
  \\ SIMP_TAC std_ss [FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,ARM_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC [PAIR,optionTheory.SOME_11]);

val IMP_ARM_SPEC = save_thm("IMP_ARM_SPEC",
  (RW1 [STAR_COMM] o RW [ARM_SPEC_CODE] o
   SPECL [``CODE_POOL ARM_INSTR c * p'``,
          ``CODE_POOL ARM_INSTR c * q'``]) IMP_ARM_SPEC_LEMMA);

val aS_HIDE = store_thm("aS_HIDE",
  ``~aS = ~aS1 psrN * ~aS1 psrZ * ~aS1 psrC * ~aS1 psrV``,
  SIMP_TAC std_ss [SEP_HIDE_def,aS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [aS_def,PAIR]);

val _ = wordsLib.guess_lengths();
val BYTES_TO_WORD_LEMMA = store_thm("BYTES_TO_WORD_LEMMA",
  ``!w. (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w``,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] []);

val aM_INTRO_LEMMA1 = prove(
  ``!a x0 x1 x2 x3 p.
     (p * aM1 a x0 * aM1 (a + 1w) x1 * aM1 (a + 2w) x2 * aM1 (a + 3w) x3 =
      p * aM a (bytes2word [x0;x1;x2;x3]))``,
 SRW_TAC [wordsLib.WORD_EXTRACT_ss] [bit_listTheory.bytes2word_def,aM_def,STAR_ASSOC]);

val aM_INTRO_LEMMA2 = prove(
  ``!a x0 x1 x2 x3 p.
     (p * aM1 a x3 * aM1 (a - 1w) x2 * aM1 (a - 2w) x1 * aM1 (a - 3w) x0 =
     p * aM (a - 3w) (bytes2word [x0; x1; x2; x3]))``,
  SIMP_TAC std_ss [GSYM aM_INTRO_LEMMA1,word_arith_lemma3,WORD_ADD_0,
     AC STAR_ASSOC STAR_COMM]);

val aM_INTRO = save_thm("aM_INTRO",
  GEN_ALL (CONJ (Q.SPEC `a` aM_INTRO_LEMMA1)
                (Q.SPEC `a` aM_INTRO_LEMMA2)));


(* ----------------------------------------------------------------------------- *)
(* Byte-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val aBYTE_MEMORY_SET_def = Define `
  aBYTE_MEMORY_SET df f = { aMem a (f a) | a | a IN df }`;

val aBYTE_MEMORY_def = Define `aBYTE_MEMORY df f = SEP_EQ (aBYTE_MEMORY_SET df f)`;

val IN_aBYTE_MEMORY_SET = prove(
  ``a IN df ==>
    (aBYTE_MEMORY_SET df g = (aMem a (g a)) INSERT aBYTE_MEMORY_SET (df DELETE a) g)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,aBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_aBYTE_MEMORY_SET = prove(
  ``aBYTE_MEMORY_SET (df DELETE a) ((a =+ w) g) =
    aBYTE_MEMORY_SET (df DELETE a) g``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,aBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val aBYTE_MEMORY_INSERT = store_thm("aBYTE_MEMORY_INSERT",
  ``a IN df ==>
    (aBYTE_MEMORY df ((a =+ w) g) = aM1 a w * aBYTE_MEMORY (df DELETE a) g)``,
  SIMP_TAC std_ss [aBYTE_MEMORY_def,aM1_def,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_aBYTE_MEMORY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_aBYTE_MEMORY_SET,APPLY_UPDATE_THM]
  \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_DELETE]
  \\ `~(aMem a w IN aBYTE_MEMORY_SET (df DELETE a) g)` suffices_by METIS_TAC []
  \\ SIMP_TAC std_ss [aBYTE_MEMORY_SET_def,GSPECIFICATION,IN_DELETE,arm_el_11]);

val aBYTE_MEMORY_INTRO = store_thm("aBYTE_MEMORY_INTRO",
  ``SPEC m (aM1 a v * P) c (aM1 a w * Q) ==>
    a IN df ==>
    SPEC m (aBYTE_MEMORY df ((a =+ v) f) * P) c (aBYTE_MEMORY df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [aBYTE_MEMORY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);


(* ----------------------------------------------------------------------------- *)
(* Memory assertion based on finite maps                                         *)
(* ----------------------------------------------------------------------------- *)

val aMEM_def = Define `aMEM m = aBYTE_MEMORY (FDOM m) (\x. m ' x)`;

(*
val _ = wordsLib.guess_lengths();
val READ32_def = Define `
  READ32 a (m:word32 |-> word8) =
    (m ' (a + 3w) @@ m ' (a + 2w) @@ m ' (a + 1w) @@ m ' (a)):word32`;

val WRITE32_def = Define `
  WRITE32 (a:word32) (w:word32) m =
    m |+ (a + 0w, (( 7 ><  0) w):word8)
      |+ (a + 1w, ((15 ><  8) w):word8)
      |+ (a + 2w, ((23 >< 16) w):word8)
      |+ (a + 3w, ((31 >< 24) w):word8)`;

val WRITE32_THM = store_thm("WRITE32_THM",
  ``!a w.
     (((a + 3w =+ (31 >< 24) w)
       ((a + 2w =+ (23 >< 16) w)
        ((a + 1w =+ (15 >< 8) w)
         ((a =+ (7 >< 0) w) (\x. m ' x))))) =
      (\x. WRITE32 a w m ' x)) /\
     (((a =+ (7 >< 0) w)
       ((a + 0x1w =+ (15 >< 8) w)
        ((a + 0x2w =+ (23 >< 16) w)
         ((a + 0x3w =+ (31 >< 24) w) (\x. m ' x))))) =
       (\x. WRITE32 a w m ' x))``,
  SIMP_TAC std_ss [WRITE32_def,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_LCANCEL,
       RW [WORD_ADD_0] (Q.SPECL [`w`,`0w`] WORD_EQ_ADD_LCANCEL),
       RW [WORD_ADD_0] (Q.SPECL [`w`,`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]);
*)

val aMEM_WRITE_BYTE = store_thm("aMEM_WRITE_BYTE",
  ``!a:word32 w:word8. ((a =+ w) (\x. m ' x) = (\x. (m |+ (a,w)) ' x))``,
  SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM,FUN_EQ_THM] \\ SRW_TAC [] []);


(* ----------------------------------------------------------------------------- *)
(* Word-sized data memory                                                        *)
(* ----------------------------------------------------------------------------- *)

val aMEMORY_WORD_def = Define `
  aMEMORY_WORD (a:word32) (w:word32) =
    { aMem a      (((7 >< 0) (w))) ;
      aMem (a+1w) (((7 >< 0) (w >> 8))) ;
      aMem (a+2w) (((7 >< 0) (w >> 16))) ;
      aMem (a+3w) (((7 >< 0) (w >> 24))) }`;

val aMEMORY_SET_def = Define `
  aMEMORY_SET df f = BIGUNION { aMEMORY_WORD a (f a) | a | a IN df /\ ALIGNED a  }`;

val aMEMORY_def = Define `aMEMORY df f = SEP_EQ (aMEMORY_SET df f)`;

val aMEMORY_SET_SING = prove(
  ``!a f. ALIGNED a ==> (aMEMORY_SET {a} f = aMEMORY_WORD a (f a))``,
  ASM_SIMP_TAC std_ss [GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,APPLY_UPDATE_THM,
    EXTENSION,aMEMORY_SET_def,IN_BIGUNION] \\ METIS_TAC [IN_INSERT]);

val aMEMORY_ARITH_LEMMA = prove(
  ``!a:word32. ~(a = a + 1w) /\ ~(a = a + 2w) /\ ~(a = a + 3w) /\
               ~(a + 1w = a + 2w) /\ ~(a + 1w = a + 3w) /\ ~(a + 2w = a + 3w)``,
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
    RW [WORD_ADD_0] (Q.SPECL [`x`,`0w`] WORD_EQ_ADD_LCANCEL)]);

val aM_THM = store_thm("aM_THM",
  ``!a f w. ALIGNED a ==> (aMEMORY {a} ((a =+ w) f) = aM a w)``,
  SIMP_TAC std_ss [aMEMORY_def,aMEMORY_SET_SING,aM_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [aM1_def,EQ_STAR,GSYM STAR_ASSOC,APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [SEP_EQ_def]
  \\ STRIP_TAC \\ Cases_on `x = aMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [aMEMORY_WORD_def,INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY,
                           GSYM DELETE_DEF,EMPTY_SUBSET,IN_DELETE,arm_el_11,EXTENSION]
  THEN1 METIS_TAC [aMEMORY_ARITH_LEMMA,arm_el_11,arm_el_distinct]
  \\ SIMP_TAC std_ss [aMEMORY_ARITH_LEMMA]
  \\ Cases_on `aMem (a + 3w) (((7 >< 0) (w >> 24))) IN x` THEN1 METIS_TAC []
  \\ Cases_on `aMem (a + 2w) (((7 >< 0) (w >> 16))) IN x` THEN1 METIS_TAC []
  \\ Cases_on `aMem (a + 1w) (((7 >< 0) (w >> 8))) IN x` THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss []);

val aMEMORY_INSERT_LEMMA = prove(
  ``!s. ALIGNED a /\ ~(a IN s) ==>
        (aMEMORY {a} ((a =+ w) g) * aMEMORY s f = aMEMORY (a INSERT s) ((a =+ w) f))``,
  STRIP_TAC
  \\ SIMP_TAC bool_ss [FUN_EQ_THM,cond_STAR,aMEMORY_def,aMEMORY_SET_SING,APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [STAR_def,SEP_EQ_def,SPLIT_def]
  \\ REPEAT STRIP_TAC
  \\ `DISJOINT (aMEMORY_WORD a w) (aMEMORY_SET s f)` by
   (SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,
                     aMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REWRITE_TAC [GSYM IMP_DISJ_THM] \\ REPEAT STRIP_TAC
    \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!x. b` (K ALL_TAC)
    \\ `~(a = a')` by METIS_TAC []
    \\ NTAC 2 (FULL_SIMP_TAC bool_ss [aMEMORY_WORD_def,IN_INSERT,
         NOT_IN_EMPTY,arm_el_11,WORD_EQ_ADD_RCANCEL])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma5,word_arith_lemma4]
    \\ METIS_TAC [NOT_ALIGNED])
  \\ `aMEMORY_WORD a w UNION aMEMORY_SET s f =
      aMEMORY_SET (a INSERT s) ((a =+ w) f)` by
   (SIMP_TAC std_ss [IN_UNION,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_INSERT,
                     aMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `aMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM],
      Q.EXISTS_TAC `s'` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a'` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM],
      `~(a = a')` by METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
      \\ METIS_TAC []])
  \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);

val aMEMORY_INSERT = save_thm("aMEMORY_INSERT",
  SIMP_RULE std_ss [aM_THM] aMEMORY_INSERT_LEMMA);

val aMEMORY_INTRO = store_thm("aMEMORY_INTRO",
  ``SPEC ARM_MODEL (aM a v * P) c (aM a w * Q) ==>
    ALIGNED a /\ a IN df ==>
    SPEC ARM_MODEL (aMEMORY df ((a =+ v) f) * P) c (aMEMORY df ((a =+ w) f) * Q)``,
  REPEAT STRIP_TAC
  \\ (IMP_RES_TAC o GEN_ALL o REWRITE_RULE [AND_IMP_INTRO] o
     SIMP_RULE std_ss [INSERT_DELETE,IN_DELETE] o
     DISCH ``a:word32 IN df`` o Q.SPEC `df DELETE a` o GSYM) aMEMORY_INSERT_LEMMA
  \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC bool_ss [aM_THM]
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ REWRITE_TAC [STAR_ASSOC]
  \\ MATCH_MP_TAC SPEC_FRAME
  \\ FULL_SIMP_TAC bool_ss [AC STAR_COMM STAR_ASSOC]);


(* ----------------------------------------------------------------------------- *)
(* Extra                                                                         *)
(* ----------------------------------------------------------------------------- *)

val aligned4_thm = store_thm("aligned4_thm",
  ``!a. aligned (a,4) = ALIGNED a``,
  Cases \\ ASM_SIMP_TAC std_ss [arm_coretypesTheory.aligned_def,
      arm_coretypesTheory.align_def,w2n_n2w,ALIGNED_n2w,n2w_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ (STRIP_ASSUME_TAC o Q.SPEC `n` o GSYM o
      RW1 [arithmeticTheory.MULT_COMM] o MATCH_MP arithmeticTheory.DIVISION) (DECIDE ``0 < 4:num``)
  \\ Cases_on `n MOD 4 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ `(4 * (n DIV 4)) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val aligned2_thm = store_thm("aligned2_thm",
  ``!a:word32. aligned (a,2) = (a && 1w = 0w)``,
  Cases \\ ASM_SIMP_TAC std_ss [arm_coretypesTheory.aligned_def,
      arm_coretypesTheory.align_def,w2n_n2w,n2w_and_1,n2w_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ (STRIP_ASSUME_TAC o Q.SPEC `n` o GSYM o
      RW1 [arithmeticTheory.MULT_COMM] o MATCH_MP arithmeticTheory.DIVISION) (DECIDE ``0 < 2:num``)
  \\ Cases_on `n MOD 2 = 0` \\ FULL_SIMP_TAC std_ss []
  \\ `(2 * (n DIV 2)) < 4294967296` by DECIDE_TAC
  \\ `0 < 2:num` by DECIDE_TAC
  \\ `n MOD 2 < 2` by METIS_TAC [arithmeticTheory.MOD_LESS]
  \\ `n MOD 2 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

val ADD_WITH_CARRY_SUB_n2w = save_thm("ADD_WITH_CARRY_SUB_n2w",
  ((RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
    (ONCE_REWRITE_CONV [GSYM WORD_NOT_NOT] THENC
     ONCE_REWRITE_CONV [word_1comp_n2w] THENC
     SIMP_CONV (std_ss++wordsLib.SIZES_ss) []) THENC
   REWRITE_CONV [ADD_WITH_CARRY_SUB])
      ``add_with_carry (x:word32,n2w n,T)``);

val UPDATE_FCP = prove(
  ``!k b f. (k :+ b) ((FCP i. f i):'a word) = (FCP i. if i = k then b else f i):'a word``,
  SIMP_TAC std_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA]
  \\ ONCE_REWRITE_TAC [fcpTheory.FCP_APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA] \\ METIS_TAC []);

val ARM_READ_MASKED_CPSR_INTRO = store_thm("ARM_READ_MASKED_CPSR_INTRO",
  ``encode_psr (ARM_READ_CPSR s) =
     (31 :+ ARM_READ_STATUS psrN s)
    ((30 :+ ARM_READ_STATUS psrZ s)
    ((29 :+ ARM_READ_STATUS psrC s)
    ((28 :+ ARM_READ_STATUS psrV s)
    ((27 :+ ARM_READ_STATUS psrQ s) (ARM_READ_MASKED_CPSR s)))))``,
  SIMP_TAC std_ss [ARM_READ_CPSR_def,ARM_READ_MASKED_CPSR_THM,UPDATE_FCP,encode_psr_def]
  \\ SIMP_TAC std_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA]
  \\ SIMP_TAC std_ss [ARM_READ_STATUS_def,ARM_READ_CPSR_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = 31` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i = 30` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i = 29` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i = 28` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i = 27` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i < 27` \\ ASM_SIMP_TAC std_ss []
  \\ `F` by DECIDE_TAC);

val FCP_UPDATE_WORD_AND = store_thm("FCP_UPDATE_WORD_AND",
  ``((j :+ b) w) && v = (j :+ v ' j /\ b) (w && ((j :+ F) v))``,
  SIMP_TAC std_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_and_def]
  \\ ONCE_REWRITE_TAC [fcpTheory.FCP_APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [fcpTheory.FCP_BETA]
  \\ ONCE_REWRITE_TAC [fcpTheory.FCP_APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [fcpTheory.FCP_BETA] \\ METIS_TAC []);


(* Stack --- sp points at top of stack, stack grows towards smaller addresses *)

val SEP_HIDE_ARRAY_def = Define `
  SEP_HIDE_ARRAY p i a n = SEP_EXISTS xs. SEP_ARRAY p i a xs * cond (LENGTH xs = n)`;

val aSTACK_def = Define `
  aSTACK bp n xs =
    SEP_ARRAY aM 4w bp xs * cond (ALIGNED bp) *
    SEP_HIDE_ARRAY aM (-4w) (bp - 4w) n`;

val SEP_HIDE_ARRAY_SUC = prove(
  ``SEP_HIDE_ARRAY aM w a (SUC n) = ~aM a * SEP_HIDE_ARRAY aM w (a + w) n``,
  SIMP_TAC std_ss [SEP_HIDE_ARRAY_def,SEP_CLAUSES,FUN_EQ_THM,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,cond_STAR,SEP_ARRAY_def]
    \\ Q.EXISTS_TAC `t` \\ FULL_SIMP_TAC std_ss [word_sub_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ Q.EXISTS_TAC `h` \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [SEP_HIDE_def,SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
  \\ Q.EXISTS_TAC `x'::xs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,SEP_ARRAY_def,cond_STAR,STAR_ASSOC]);

val SEP_EXISTS_aSTACK = store_thm("SEP_EXISTS_aSTACK",
  ``((SEP_EXISTS x. p x * q) = (SEP_EXISTS x. p x) * q) /\
    ((SEP_EXISTS x. q * p x) = q * (SEP_EXISTS x. p x)) /\
    ((SEP_EXISTS x. aSTACK a n (x::xs)) = aSTACK (a + 4w) (n + 1) xs)``,
  SIMP_TAC std_ss [SEP_CLAUSES,aSTACK_def,GSYM ADD1,ALIGNED,
      SEP_HIDE_ARRAY_SUC,SEP_ARRAY_def,WORD_ADD_SUB]
  THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_HIDE_def,STAR_ASSOC,GSYM word_sub_def]
  THEN SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);


(* ----------------------------------------------------------------------------- *)
(* Reading/writing chunks of memory                                              *)
(* ----------------------------------------------------------------------------- *)

val READ8_def = Define `
  READ8 a (m:word32 -> word8) = m a`;

val WRITE8_def = Define `
  WRITE8 (a:word32) (w:word8) m = (a =+ w:word8) m`;

val _ = wordsLib.guess_lengths();
val READ32_def = zDefine `
  READ32 a (m:word32 -> word8) =
    (m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m (a)):word32`;

val WRITE32_def = zDefine `
  WRITE32 (a:word32) (w:word32) m =
    ((a + 0w =+ (w2w w):word8)
    ((a + 1w =+ (w2w (w >>> 8)):word8)
    ((a + 2w =+ (w2w (w >>> 16)):word8)
    ((a + 3w =+ (w2w (w >>> 24)):word8) m))))`;

val WRITE32_blast_lemma = blastLib.BBLAST_PROVE
  ``((( 7 ><  0) (w:word32)) = (w2w w):word8) /\
    (((15 ><  8) (w:word32)) = (w2w (w >>> 8)):word8) /\
    (((23 >< 16) (w:word32)) = (w2w (w >>> 16)):word8) /\
    (((31 >< 24) (w:word32)) = (w2w (w >>> 24)):word8)``

val WRITE32_THM = store_thm("WRITE32_THM",
  ``!a w.
     (((a      =+ (( 7 ><  0) w):word8)
      ((a + 1w =+ ((15 ><  8) w):word8)
      ((a + 2w =+ ((23 >< 16) w):word8)
      ((a + 3w =+ ((31 >< 24) w):word8) m)))) = WRITE32 a w m) /\
     (((a + 3w =+ ((31 >< 24) w):word8)
      ((a + 2w =+ ((23 >< 16) w):word8)
      ((a + 1w =+ ((15 ><  8) w):word8)
      ((a      =+ (( 7 ><  0) w):word8) m)))) = WRITE32 a w m)``,
  SIMP_TAC std_ss [GSYM WRITE32_blast_lemma,WRITE32_def,APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_LCANCEL,
       RW [WORD_ADD_0] (Q.SPECL [`w`,`0w`] WORD_EQ_ADD_LCANCEL),
       RW [WORD_ADD_0] (Q.SPECL [`w`,`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]);


val _ = export_theory();
