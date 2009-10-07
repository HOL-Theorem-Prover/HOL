
open HolKernel boolLib bossLib Parse;
open pred_setTheory wordsTheory wordsLib arithmeticTheory;
open set_sepTheory progTheory toy_systemTheory;
open listTheory pairTheory combinTheory addressTheory;

val _ = new_theory "prog_toy";


infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The TOY set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  toy_el =  tReg of word4 => word32
          | tStatus of bool
          | tInstr of word32 => instruction
          | tRam of word32 => word32 option
          | tTime of num
          | tUart0 of (word8 list # num # word8 list # num)
          | tUndef of bool`;

val toy_el_11 = DB.fetch "-" "toy_el_11";
val toy_el_distinct = DB.fetch "-" "toy_el_distinct";

val _ = Parse.type_abbrev("toy_set",``:toy_el set``);


(* ----------------------------------------------------------------------------- *)
(* State reader functions                                                        *)
(* ----------------------------------------------------------------------------- *)

val ty = (type_of o snd o dest_comb) ``TOY_NEXT s1 s2``
val _ = Parse.type_abbrev("toy_state",ty);

val TOY_READ_REG_def = Define `
  TOY_READ_REG a (((r,b,c),p):toy_state) = r a`;

val TOY_READ_STATUS_def = Define `
  TOY_READ_STATUS (((r,b,c),p):toy_state) = b`;

val TOY_READ_INSTR_def = Define `
  TOY_READ_INSTR a (((r,b,c),p):toy_state) = c a`;

val TOY_READ_TIME_def = Define `
  TOY_READ_TIME (((r,b,c),(time,rom,ram,p)):toy_state) = time`;

val TOY_READ_RAM_def = Define `
  TOY_READ_RAM a (((r,b,c),(time,rom,ram,p)):toy_state) = ram a`;

val TOY_READ_UART0_def = Define `
  TOY_READ_UART0 (((r,b,c),(time,rom,ram,uart0,p)):toy_state) = UART0_READ uart0`;

val TOY_READ_UNDEF_def = Define `
  TOY_READ_UNDEF (((r,b,c),p):toy_state) = 
    ~PERIPHERALS_OK p`;


(* ----------------------------------------------------------------------------- *)
(* Converting from toy_state to toy_set                                          *)
(* ----------------------------------------------------------------------------- *)

val toy2set'_def = Define `
  toy2set' (rs,st:unit set,is,ms,tt:unit set,ua:unit set,ud:unit set) (s:toy_state) =
    IMAGE (\a. tReg a (TOY_READ_REG a s)) rs UNION
    IMAGE (\a. tStatus (TOY_READ_STATUS s)) st UNION
    IMAGE (\a. tInstr a (TOY_READ_INSTR a s)) is UNION
    IMAGE (\a. tRam a (TOY_READ_RAM a s)) ms UNION
    IMAGE (\a. tTime (TOY_READ_TIME s)) tt UNION
    IMAGE (\a. tUart0 (TOY_READ_UART0 s)) ua UNION
    IMAGE (\a. tUndef (TOY_READ_UNDEF s)) ud`;

val toy2set_def   = Define `toy2set s = toy2set' (UNIV,UNIV,UNIV,UNIV,UNIV,UNIV,UNIV) s`;
val toy2set''_def = Define `toy2set'' x s = toy2set s DIFF toy2set' x s`;

(* theorems *)

val toy2set'_SUBSET_toy2set = prove(
  ``!y s. toy2set' y s SUBSET toy2set s``,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ SIMP_TAC std_ss [SUBSET_DEF,toy2set'_def,toy2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_toy2set = prove(
  ``!x s. SPLIT (toy2set s) (toy2set' x s, toy2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,toy2set''_def]
  \\ `toy2set' x s SUBSET toy2set s` by METIS_TAC [toy2set'_SUBSET_toy2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val SUBSET_toy2set = prove(
  ``!u s. u SUBSET toy2set s = ?y. u = toy2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [toy2set'_SUBSET_toy2set]
  \\ Q.EXISTS_TAC `(
       { a |a| ?x. tReg a x IN u },
       { a |a| ?x. tStatus x IN u },
       { a |a| ?x. tInstr a x IN u },
       { a |a| ?x. tRam a x IN u },
       { a |a| ?x. tTime x IN u },
       { a |a| ?x. tUart0 x IN u },
       { a |a| ?x. tUndef x IN u })`
  \\ FULL_SIMP_TAC std_ss [toy2set'_def,toy2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` IMP_RES_TAC \\ FULL_SIMP_TAC std_ss [toy_el_11,toy_el_distinct]);

val SPLIT_toy2set_EXISTS = prove(
  ``!s u v. SPLIT (toy2set s) (u,v) = ?y. (u = toy2set' y s) /\ (v = toy2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_toy2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,toy2set'_def,toy2set''_def]
  \\ `u SUBSET (toy2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_toy2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);

val IN_toy2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a x s. tReg a x IN (toy2set s) = (x = TOY_READ_REG a s)) /\
  (!a x s. tReg a x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_REG a s) /\ a IN rs) /\
  (!a x s. tReg a x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_REG a s) /\ ~(a IN rs)) /\ 
  (!a x s. tStatus x IN (toy2set s) = (x = TOY_READ_STATUS s)) /\
  (!a x s. tStatus x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_STATUS s) /\ a IN st) /\
  (!a x s. tStatus x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_STATUS s) /\ ~(a IN st)) /\ 
  (!a x s. tInstr a x IN (toy2set s) = (x = TOY_READ_INSTR a s)) /\
  (!a x s. tInstr a x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_INSTR a s) /\ a IN is) /\
  (!a x s. tInstr a x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_INSTR a s) /\ ~(a IN is)) /\ 
  (!a x s. tRam a x IN (toy2set s) = (x = TOY_READ_RAM a s)) /\
  (!a x s. tRam a x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_RAM a s) /\ a IN ms) /\
  (!a x s. tRam a x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_RAM a s) /\ ~(a IN ms)) /\ 
  (!a x s. tTime x IN (toy2set s) = (x = TOY_READ_TIME s)) /\
  (!a x s. tTime x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_TIME s) /\ a IN tt) /\
  (!a x s. tTime x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_TIME s) /\ ~(a IN tt)) /\ 
  (!a x s. tUart0 x IN (toy2set s) = (x = TOY_READ_UART0 s)) /\
  (!a x s. tUart0 x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_UART0 s) /\ a IN ua) /\
  (!a x s. tUart0 x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_UART0 s) /\ ~(a IN ua)) /\ 
  (!a x s. tUndef x IN (toy2set s) = (x = TOY_READ_UNDEF s)) /\
  (!a x s. tUndef x IN (toy2set' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_UNDEF s) /\ a IN ud) /\
  (!a x s. tUndef x IN (toy2set'' (rs,st,is,ms,tt,ua,ud) s) = (x = TOY_READ_UNDEF s) /\ ~(a IN ud))``,
  SRW_TAC [] [toy2set'_def,toy2set''_def,toy2set_def,IN_UNION,IN_DIFF,oneTheory.one] 
  \\ METIS_TAC []);

val SET_NOT_EQ = prove(
  ``!x y. ~(x = y:'a set) = ?a. ~(a IN x = a IN y)``,
   FULL_SIMP_TAC std_ss [EXTENSION])

val toy2set''_11 = prove(
  ``!y y' s s'. (toy2set'' y' s' = toy2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC
  \\ `?rs st is ms tt ua ud. y = (rs,st,is,ms,tt,ua,ud)` by METIS_TAC [PAIR]
  \\ `?rs2 st2 is2 ms2 tt2 ua2 ud2. y' = (rs2,st2,is2,ms2,tt2,ua2,ud2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (`~((?y. tReg x y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tReg x y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_toy2set] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tStatus y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tStatus y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tInstr x y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tInstr x y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tRam x y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tRam x y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tTime y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tTime y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tUart0 y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tUart0 y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tUndef y IN toy2set'' (rs,st,is,ms,tt,ua,ud) s) = 
            (?y. tUndef y IN toy2set'' (rs2,st2,is2,ms2,tt2,ua2,ud2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] THEN1 METIS_TAC []));

val DELETE_toy2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tReg a (TOY_READ_REG a s) =
         (toy2set' (rs DELETE a,st,is,ms,tt,ua,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tStatus (TOY_READ_STATUS s) =
         (toy2set' (rs,st DELETE a,is,ms,tt,ua,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tInstr a (TOY_READ_INSTR a s) =
         (toy2set' (rs,st,is DELETE a,ms,tt,ua,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tRam a (TOY_READ_RAM a s) =
         (toy2set' (rs,st,is,ms DELETE a,tt,ua,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tTime (TOY_READ_TIME s) =
         (toy2set' (rs,st,is,ms,tt DELETE a,ua,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tUart0 (TOY_READ_UART0 s) =
         (toy2set' (rs,st,is,ms,tt,ua DELETE a,ud) s)) /\ 
  (!a s. (toy2set' (rs,st,is,ms,tt,ua,ud) s) DELETE tUndef (TOY_READ_UNDEF s) =
         (toy2set' (rs,st,is,ms,tt,ua,ud DELETE a) s))``,
  SRW_TAC [] [toy2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,oneTheory.one]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_toy2set = prove(``
  (toy2set' (rs,st,is,ms,tt,ua,ud) s = {}) = 
  (rs = {}) /\ (st = {}) /\ (is = {}) /\ (ms = {}) /\ (tt = {}) /\ (ua = {}) /\ (ud = {})``,
  SRW_TAC [] [toy2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,EXISTS_OR_THM]
  \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Defining the TOY_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val tR_def = Define `tR a x = SEP_EQ {tReg a x}`;
val tM_def = Define `tM a x = SEP_EQ {tRam a x}`;
val tS_def = Define `tS x = SEP_EQ {tStatus x}`;
val tU_def = Define `tU x = SEP_EQ {tUndef x}`;
val tT_def = Define `tT x = SEP_EQ {tTime x}`;
val tUART0_def = Define `tUART0 x = SEP_EQ {tUart0 x}`;

val tPC_def = Define `tPC x = tR 15w x * tU F`;

val TOY_INSTR_def = Define `TOY_INSTR (a,c) = { tInstr a c }`;

val TOY_MODEL_def = Define `
  TOY_MODEL = (toy2set, TOY_NEXT, TOY_INSTR, (\x y. (x:toy_state) = y))`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_toy2set]
  ``p (toy2set' y s) ==> (?u v. SPLIT (toy2set s) (u,v) /\ p u /\ (\v. v = toy2set'' y s) v)``;

val TOY_SPEC_SEMANTICS = store_thm("TOY_SPEC_SEMANTICS",
  ``SPEC TOY_MODEL p {} q =
    !y s seq. p (toy2set' y s) /\ rel_sequence TOY_NEXT seq s ==>
              ?k. q (toy2set' y (seq k)) /\ (toy2set'' y s = toy2set'' y (seq k))``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_def,TOY_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_toy2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = toy2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_toy2set_EXISTS]
  \\ IMP_RES_TAC toy2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC TOY_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val SEP_EQ_STAR_LEMMA = prove(
  ``!p s t. (SEP_EQ t * p) s <=> t SUBSET s /\ (t SUBSET s ==> p (s DIFF t))``,  
  METIS_TAC [EQ_STAR]);

val FLIP_CONJ = prove(``!b c. b /\ (b ==> c) = b /\ c``,METIS_TAC []);

val EXPAND_STAR =  
  GEN_ALL o (SIMP_CONV std_ss [tR_def,tM_def,tS_def,tU_def,tT_def,tUART0_def,
    SEP_EQ_STAR_LEMMA,INSERT_SUBSET,IN_toy2set,DELETE_toy2set,
    DIFF_INSERT,DIFF_EMPTY,EMPTY_SUBSET] THENC SIMP_CONV std_ss [FLIP_CONJ]
   THENC REWRITE_CONV [GSYM CONJ_ASSOC])

val STAR_toy2set = save_thm("STAR_toy2set",LIST_CONJ (map EXPAND_STAR 
  [``(tR a x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tM a x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tS x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tU x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tT x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``,
   ``(tUART0 x * p) (toy2set' (rs,st,is,ms,tt,ua,ud) s)``]));

val CODE_POOL_toy2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) = (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_toy2set = store_thm("CODE_POOL_toy2set",
  ``(CODE_POOL TOY_INSTR {(p,c)}) (toy2set' (rs,st,is,ms,tt,ua,ud) s) =
      ({p} = is) /\ (rs = {}) /\ (st = {}) /\ (ms = {}) /\ (tt = {}) /\ (ua = {}) /\ (ud = {}) /\
      (TOY_READ_INSTR p s = c)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,TOY_INSTR_def,CODE_POOL_toy2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_toy2set]
  \\ Cases_on `c = TOY_READ_INSTR p s`
  \\ ASM_SIMP_TAC std_ss [DELETE_toy2set,EMPTY_toy2set]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC]);

val TOY_SPEC_CODE = (RW [GSYM TOY_MODEL_def] o SIMP_RULE std_ss [TOY_MODEL_def] o prove)
  (``SPEC TOY_MODEL (CODE_POOL (FST (SND (SND TOY_MODEL))) c * p) {}
                    (CODE_POOL (FST (SND (SND TOY_MODEL))) c * q) =
    SPEC TOY_MODEL p c q``,
  REWRITE_TAC [SPEC_CODE]);

val IMP_TOY_SPEC_LEMMA = prove(
  ``!p q.
      (!s s2 y.
        p (toy2set' y s) ==>
        (?s1. TOY_NEXT s s1) /\
        (TOY_NEXT s s2 ==> q (toy2set' y s2) /\ (toy2set'' y s = toy2set'' y s2))) ==>
      SPEC TOY_MODEL p {} q``,
  REWRITE_TAC [TOY_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC []);

val IMP_TOY_SPEC = save_thm("IMP_TOY_SPEC",
  (RW1 [STAR_COMM] o RW [TOY_SPEC_CODE] o
   SPECL [``CODE_POOL TOY_INSTR {(p,c)} * p1``,
          ``CODE_POOL TOY_INSTR {(p,c)} * q1``]) IMP_TOY_SPEC_LEMMA);

val toy2set''_thm = store_thm("toy2set''_thm",
  ``(toy2set'' (rs,st,is,ms,tt,ua,ud) s1 = toy2set'' (rs,st,is,ms,tt,ua,ud) s2) =
    (!a. ~(a IN rs) ==> (TOY_READ_REG a s1 = TOY_READ_REG a s2)) /\
    (!a. ~(a IN st) ==> (TOY_READ_STATUS s1 = TOY_READ_STATUS s2)) /\
    (!a. ~(a IN is) ==> (TOY_READ_INSTR a s1 = TOY_READ_INSTR a s2)) /\
    (!a. ~(a IN ms) ==> (TOY_READ_RAM a s1 = TOY_READ_RAM a s2)) /\
    (!a. ~(a IN tt) ==> (TOY_READ_TIME s1 = TOY_READ_TIME s2)) /\
    (!a. ~(a IN ua) ==> (TOY_READ_UART0 s1 = TOY_READ_UART0 s2)) /\
    (!a. ~(a IN ud) ==> (TOY_READ_UNDEF s1 = TOY_READ_UNDEF s2))``,
  SIMP_TAC std_ss [oneTheory.one]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (Cases \\ ASM_SIMP_TAC std_ss [IN_toy2set] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tReg a (TOY_READ_REG a s1)`)
         \\ METIS_TAC [IN_toy2set])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tStatus (TOY_READ_STATUS s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tInstr a (TOY_READ_INSTR a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tRam a (TOY_READ_RAM a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tTime (TOY_READ_TIME s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tUart0 (TOY_READ_UART0 s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tUndef (TOY_READ_UNDEF s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_toy2set,oneTheory.one] \\ METIS_TAC []));

    
val _ = export_theory();
