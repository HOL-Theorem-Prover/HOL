
open HolKernel boolLib bossLib Parse;
open pred_setTheory wordsTheory wordsLib arithmeticTheory;
open set_sepTheory progTheory lpc_devicesTheory;
open listTheory pairTheory combinTheory addressTheory;

val _ = new_theory "lpc_prog";


infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The LPC set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  lpc_el =  tReg of word4 => word32
          | tStatus of arm_bit => bool
          | tRom of word32 => word8 option
          | tRam of word32 => word8 option
          | tTime of num
          | tUart0 of (word8 list # num # word8 list # num)
          | tUndef of bool`;

val lpc_el_11 = DB.fetch "-" "lpc_el_11";
val lpc_el_distinct = DB.fetch "-" "lpc_el_distinct";

val _ = Parse.type_abbrev("lpc_set",``:lpc_el set``);


(* ----------------------------------------------------------------------------- *)
(* State reader functions                                                        *)
(* ----------------------------------------------------------------------------- *)

val ty = (type_of o snd o dest_comb) ``LPC_NEXT s1 s2``
val _ = Parse.type_abbrev("lpc_state",ty);

val LPC_READ_REG_def = Define `
  LPC_READ_REG a ((s,p):lpc_state) = ARM_READ_REG a s`;

val LPC_READ_STATUS_def = Define `
  LPC_READ_STATUS a ((s,p):lpc_state) = ARM_READ_STATUS a s`;

val LPC_READ_TIME_def = Define `
  LPC_READ_TIME ((s,(time,rom,ram,p)):lpc_state) = time`;

val LPC_READ_ROM_def = Define `
  LPC_READ_ROM a ((s,(time,rom,ram,p)):lpc_state) = rom a`;

val LPC_READ_RAM_def = Define `
  LPC_READ_RAM a ((s,(time,rom,ram,p)):lpc_state) = ram a`;

val LPC_READ_UART0_def = Define `
  LPC_READ_UART0 ((s,(time,rom,ram,uart0,p)):lpc_state) = UART0_READ uart0`;

val ARM_OK_def = Define `
  ARM_OK state =
    (ARM_ARCH state = ARMv4) /\ (ARM_EXTENSIONS state = {}) /\
    (ARM_UNALIGNED_SUPPORT state) /\ (ARM_READ_EVENT_REGISTER state) /\
    ~(ARM_READ_INTERRUPT_WAIT state) /\ ~(ARM_READ_SCTLR sctlrV state) /\
    (ARM_READ_SCTLR sctlrA state) /\ ~(ARM_READ_SCTLR sctlrU state) /\
    (ARM_READ_IT state = 0w) /\ ~(ARM_READ_STATUS psrJ state) /\
    ~(ARM_READ_STATUS psrT state) /\ ~(ARM_READ_STATUS psrE state) /\
    (ARM_MODE state = 16w)`;

val LPC_READ_UNDEF_def = Define `
  LPC_READ_UNDEF ((s,p):lpc_state) = ~ARM_OK s /\ ~PERIPHERALS_OK p`;


(* ----------------------------------------------------------------------------- *)
(* Converting from lpc_state to lpc_set                                          *)
(* ----------------------------------------------------------------------------- *)

val lpc2set'_def = Define `
  lpc2set' (rs,st:arm_bit set,is,ms,tt:unit set,ua:unit set,ud:unit set) (s:lpc_state) =
    IMAGE (\a. tReg a (LPC_READ_REG a s)) rs UNION
    IMAGE (\a. tStatus a (LPC_READ_STATUS a s)) st UNION
    IMAGE (\a. tRom a (LPC_READ_ROM a s)) is UNION
    IMAGE (\a. tRam a (LPC_READ_RAM a s)) ms UNION
    IMAGE (\a. tTime (LPC_READ_TIME s)) tt UNION
    IMAGE (\a. tUart0 (LPC_READ_UART0 s)) ua UNION
    IMAGE (\a. tUndef (LPC_READ_UNDEF s)) ud`;

val lpc2set_def   = Define `lpc2set s = lpc2set' (UNIV,UNIV,UNIV,UNIV,UNIV,UNIV,UNIV) s`;
val lpc2set''_def = Define `lpc2set'' x s = lpc2set s DIFF lpc2set' x s`;

(* theorems *)

val lpc2set'_SUBSET_lpc2set = prove(
  ``!y s. lpc2set' y s SUBSET lpc2set s``,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ SIMP_TAC std_ss [SUBSET_DEF,lpc2set'_def,lpc2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_lpc2set = prove(
  ``!x s. SPLIT (lpc2set s) (lpc2set' x s, lpc2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,lpc2set''_def]
  \\ `lpc2set' x s SUBSET lpc2set s` by METIS_TAC [lpc2set'_SUBSET_lpc2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val SUBSET_lpc2set = prove(
  ``!u s. u SUBSET lpc2set s = ?y. u = lpc2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [lpc2set'_SUBSET_lpc2set]
  \\ Q.EXISTS_TAC `(
       { a |a| ?x. tReg a x IN u },
       { a |a| ?x. tStatus a x IN u },
       { a |a| ?x. tRom a x IN u },
       { a |a| ?x. tRam a x IN u },
       { a |a| ?x. tTime x IN u },
       { a |a| ?x. tUart0 x IN u },
       { a |a| ?x. tUndef x IN u })`
  \\ FULL_SIMP_TAC std_ss [lpc2set'_def,lpc2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` IMP_RES_TAC \\ FULL_SIMP_TAC std_ss [lpc_el_11,lpc_el_distinct]);

val SPLIT_lpc2set_EXISTS = prove(
  ``!s u v. SPLIT (lpc2set s) (u,v) = ?y. (u = lpc2set' y s) /\ (v = lpc2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_lpc2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,lpc2set'_def,lpc2set''_def]
  \\ `u SUBSET (lpc2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_lpc2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val IN_lpc2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a x s. tReg a x IN (lpc2set s) = (x = LPC_READ_REG a s)) /\
  (!a x s. tReg a x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_REG a s) /\ a IN rs) /\
  (!a x s. tReg a x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_REG a s) /\ ~(a IN rs)) /\
  (!a x s. tStatus a x IN (lpc2set s) = (x = LPC_READ_STATUS a s)) /\
  (!a x s. tStatus a x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_STATUS a s) /\ a IN st) /\
  (!a x s. tStatus a x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_STATUS a s) /\ ~(a IN st)) /\
  (!a x s. tRom a x IN (lpc2set s) = (x = LPC_READ_ROM a s)) /\
  (!a x s. tRom a x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_ROM a s) /\ a IN is) /\
  (!a x s. tRom a x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_ROM a s) /\ ~(a IN is)) /\
  (!a x s. tRam a x IN (lpc2set s) = (x = LPC_READ_RAM a s)) /\
  (!a x s. tRam a x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_RAM a s) /\ a IN ms) /\
  (!a x s. tRam a x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_RAM a s) /\ ~(a IN ms)) /\
  (!a x s. tTime x IN (lpc2set s) = (x = LPC_READ_TIME s)) /\
  (!a x s. tTime x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_TIME s) /\ a IN tt) /\
  (!a x s. tTime x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_TIME s) /\ ~(a IN tt)) /\
  (!a x s. tUart0 x IN (lpc2set s) = (x = LPC_READ_UART0 s)) /\
  (!a x s. tUart0 x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_UART0 s) /\ a IN ua) /\
  (!a x s. tUart0 x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_UART0 s) /\ ~(a IN ua)) /\
  (!a x s. tUndef x IN (lpc2set s) = (x = LPC_READ_UNDEF s)) /\
  (!a x s. tUndef x IN (lpc2set' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_UNDEF s) /\ a IN ud) /\
  (!a x s. tUndef x IN (lpc2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = LPC_READ_UNDEF s) /\ ~(a IN ud))``,
  SRW_TAC [] [lpc2set'_def,lpc2set''_def,lpc2set_def,IN_UNION,IN_DIFF,oneTheory.one]
  \\ METIS_TAC []);

val SET_NOT_EQ = prove(
  ``!x y. ~(x = y:'a set) = ?a. ~(a IN x = a IN y)``,
   FULL_SIMP_TAC std_ss [EXTENSION])

val lpc2set''_11 = prove(
  ``!y y' s s'. (lpc2set'' y' s' = lpc2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC
  \\ `?rs st is ms tt ua ud. y = (rs,st,is,ms,tt,ua,ud)` by METIS_TAC [PAIR]
  \\ `?rs2 st2 is2 ms2 tt2 ua2 ud2. y' = (rs2,st2,is2,ms2,tt2,ua2,ud2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (`~((?y. tReg x y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tReg x y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tStatus x y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tStatus x y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tRom x y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tRom x y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tRam x y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tRam x y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tTime y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tTime y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tUart0 y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tUart0 y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tUndef y IN lpc2set'' (rs,st,is,ms,tt,ua,ud) s) =
            (?y. tUndef y IN lpc2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] THEN1 METIS_TAC []));

val DELETE_lpc2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tReg a (LPC_READ_REG a s) =
         (lpc2set' (rs DELETE a,st,is,ms,tt,ua,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tStatus a (LPC_READ_STATUS a s) =
         (lpc2set' (rs,st DELETE a,is,ms,tt,ua,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tRom a (LPC_READ_ROM a s) =
         (lpc2set' (rs,st,is DELETE a,ms,tt,ua,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tRam a (LPC_READ_RAM a s) =
         (lpc2set' (rs,st,is,ms DELETE a,tt,ua,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tTime (LPC_READ_TIME s) =
         (lpc2set' (rs,st,is,ms,tt DELETE a,ua,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tUart0 (LPC_READ_UART0 s) =
         (lpc2set' (rs,st,is,ms,tt,ua DELETE a,ud) s)) /\
  (!a s. (lpc2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tUndef (LPC_READ_UNDEF s) =
         (lpc2set' (rs,st,is,ms,tt,ua,ud DELETE a) s))``,
  SRW_TAC [] [lpc2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,oneTheory.one]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_lpc2set = prove(``
  (lpc2set' (rs,st,is,ms,tt,ua,ud) s = {}) =
  (rs = {}) /\ (st = {}) /\ (is = {}) /\ (ms = {}) /\ (tt = {}) /\ (ua = {}) /\ (ud = {})``,
  SRW_TAC [] [lpc2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,EXISTS_OR_THM]
  \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Defining the LPC_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val tR_def = Define `tR a x = SEP_EQ {tReg a x}`;
val tM_def = Define `tM a x = SEP_EQ {tRam a x}`;
val tS_def = Define `tS a x = SEP_EQ {tStatus a x}`;
val tU_def = Define `tU x = SEP_EQ {tUndef x}`;
val tT_def = Define `tT x = SEP_EQ {tTime x}`;
val tUART0_def = Define `tUART0 x = SEP_EQ {tUart0 x}`;

val tPC_def = Define `tPC x = tR 15w x * tU F * cond (ALIGNED x)`;

val LPC_ROM_def = Define `LPC_ROM (a,w:word32) =
  { tRom (a+3w) (SOME ((31 >< 24) w)) ;
    tRom (a+2w) (SOME ((23 >< 16) w)) ;
    tRom (a+1w) (SOME ((15 ><  8) w)) ;
    tRom (a+0w) (SOME (( 7 ><  0) w)) }`;

val LPC_MODEL_def = Define `
  LPC_MODEL = (lpc2set, LPC_NEXT, LPC_ROM, (\x y. (x:lpc_state) = y))`;


(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_lpc2set]
  ``p (lpc2set' y s) ==> (?u v. SPLIT (lpc2set s) (u,v) /\ p u /\ (\v. v = lpc2set'' y s) v)``;

val LPC_SPEC_SEMANTICS = store_thm("LPC_SPEC_SEMANTICS",
  ``SPEC LPC_MODEL p {} q =
    !y s seq. p (lpc2set' y s) /\ rel_sequence LPC_NEXT seq s ==>
              ?k. q (lpc2set' y (seq k)) /\ (lpc2set'' y s = lpc2set'' y (seq k))``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_def,LPC_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_lpc2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = lpc2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_lpc2set_EXISTS]
  \\ IMP_RES_TAC lpc2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC LPC_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val SEP_EQ_STAR_LEMMA = prove(
  ``!p s t. (SEP_EQ t * p) s <=> t SUBSET s /\ (t SUBSET s ==> p (s DIFF t))``,
  METIS_TAC [EQ_STAR]);

val FLIP_CONJ = prove(``!b c. b /\ (b ==> c) = b /\ c``,METIS_TAC []);

val EXPAND_STAR =
  GEN_ALL o (SIMP_CONV std_ss [tR_def,tM_def,tS_def,tU_def,tT_def,tUART0_def,
    SEP_EQ_STAR_LEMMA,INSERT_SUBSET,IN_lpc2set,DELETE_lpc2set,
    DIFF_INSERT,DIFF_EMPTY,EMPTY_SUBSET] THENC SIMP_CONV std_ss [FLIP_CONJ]
   THENC REWRITE_CONV [GSYM CONJ_ASSOC])

val STAR_lpc2set = save_thm("STAR_lpc2set",LIST_CONJ (map EXPAND_STAR
  [``(tR a x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tM a x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tS a x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tU x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tT x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tUART0 x * p) (lpc2set' (rs,st,is,ms,tt,ua,ud) s)``]));

val CODE_POOL_lpc2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) = (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_lpc2set = store_thm("CODE_POOL_lpc2set",
  ``CODE_POOL LPC_ROM {(p,c)} (lpc2set' (rs,st,is,ms,tt,ua,ud) s) =
      ({p+3w;p+2w;p+1w;p} = is) /\ (rs = {}) /\ (st = {}) /\ (ms = {}) /\ (tt = {}) /\ (ua = {}) /\ (ud = {}) /\
      (LPC_READ_ROM (p + 0w) s = SOME (( 7 ><  0) c)) /\
      (LPC_READ_ROM (p + 1w) s = SOME ((15 ><  8) c)) /\
      (LPC_READ_ROM (p + 2w) s = SOME ((23 >< 16) c)) /\
      (LPC_READ_ROM (p + 3w) s = SOME ((31 >< 24) c))``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,LPC_ROM_def,CODE_POOL_lpc2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_lpc2set]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [DELETE_lpc2set,EMPTY_lpc2set,DIFF_INSERT,WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [GSYM AND_IMP_INTRO,DELETE_lpc2set,EMPTY_lpc2set,DIFF_EMPTY]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [DELETE_lpc2set,EMPTY_lpc2set]);

val LPC_SPEC_CODE = (RW [GSYM LPC_MODEL_def] o SIMP_RULE std_ss [LPC_MODEL_def] o prove)
  (``SPEC LPC_MODEL (CODE_POOL (FST (SND (SND LPC_MODEL))) c * p) {}
                    (CODE_POOL (FST (SND (SND LPC_MODEL))) c * q) =
    SPEC LPC_MODEL p c q``,
  REWRITE_TAC [SPEC_CODE]);

val IMP_LPC_SPEC_LEMMA = prove(
  ``!p q.
      (!s s2 y.
        p (lpc2set' y s) ==>
        (?s1. LPC_NEXT s s1) /\
        (LPC_NEXT s s2 ==> q (lpc2set' y s2) /\ (lpc2set'' y s = lpc2set'' y s2))) ==>
      SPEC LPC_MODEL p {} q``,
  REWRITE_TAC [LPC_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC []);

val IMP_LPC_SPEC = save_thm("IMP_LPC_SPEC",
  (RW1 [STAR_COMM] o RW [LPC_SPEC_CODE] o
   SPECL [``CODE_POOL LPC_ROM {(p,c)} * p1``,
          ``CODE_POOL LPC_ROM {(p,c)} * q1``]) IMP_LPC_SPEC_LEMMA);

val lpc2set''_thm = store_thm("lpc2set''_thm",
  ``(lpc2set'' (rs,st,is,ms,tt,ua,ud) s1 = lpc2set'' (rs,st,is,ms,tt,ua,ud) s2) =
    (!a. ~(a IN rs) ==> (LPC_READ_REG a s1 = LPC_READ_REG a s2)) /\
    (!a. ~(a IN st) ==> (LPC_READ_STATUS a s1 = LPC_READ_STATUS a s2)) /\
    (!a. ~(a IN is) ==> (LPC_READ_ROM a s1 = LPC_READ_ROM a s2)) /\
    (!a. ~(a IN ms) ==> (LPC_READ_RAM a s1 = LPC_READ_RAM a s2)) /\
    (!a. ~(a IN tt) ==> (LPC_READ_TIME s1 = LPC_READ_TIME s2)) /\
    (!a. ~(a IN ua) ==> (LPC_READ_UART0 s1 = LPC_READ_UART0 s2)) /\
    (!a. ~(a IN ud) ==> (LPC_READ_UNDEF s1 = LPC_READ_UNDEF s2))``,
  SIMP_TAC std_ss [oneTheory.one]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (Cases \\ ASM_SIMP_TAC std_ss [IN_lpc2set] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tReg a (LPC_READ_REG a s1)`)
         \\ METIS_TAC [IN_lpc2set])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tStatus a (LPC_READ_STATUS a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tRom a (LPC_READ_ROM a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tRam a (LPC_READ_RAM a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tTime (LPC_READ_TIME s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tUart0 (LPC_READ_UART0 s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tUndef (LPC_READ_UNDEF s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_lpc2set,oneTheory.one] \\ METIS_TAC []));


val _ = export_theory();
