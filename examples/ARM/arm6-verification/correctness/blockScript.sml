(* ========================================================================= *)
(* FILE          : blockScript.sml                                           *)
(* DESCRIPTION   : A collection of lemmas used to verify the Block Data      *)
(*                 Transfer (ldm, stm) instruction class                     *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2003 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "wordsTheory", "wordsLib", "armLib",
            "iclass_compLib", "io_onestepTheory", "my_listTheory", "armTheory",
            "coreTheory", "lemmasTheory", "interruptsTheory"];
*)

open HolKernel boolLib bossLib;
open Q arithmeticTheory whileTheory rich_listTheory;
open bitTheory sum_numTheory wordsLib wordsTheory;
open armLib iclass_compLib io_onestepTheory my_listTheory;
open armTheory coreTheory lemmasTheory interruptsTheory;

val _ = new_theory "block";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val WL = ``dimindex (:'a)``;

val tt = set_trace "types";

(* ------------------------------------------------------------------------- *)

val GEN_REG_LIST_def = Define`
  GEN_REG_LIST wl n = (MAP SND o FILTER FST) (GENLIST (\b. (BIT b n,b)) wl)`;

val MASK_BIT_def = Define`
  MASK_BIT (list:bool ** 'a) mask =
    CLEARBIT ((LEASTBIT (list && mask)) MOD ^WL) mask`;

val MASKN_def = Define `MASKN n list = FUNPOW (MASK_BIT list) n Tw`;

val REG_WRITE_RP_def = Define`
  REG_WRITE_RP n reg mode list data =
    REG_WRITE reg mode (RP ldm list (MASKN n list)) data`;

val REG_WRITEN_def = Define`
  (REG_WRITEN 0 reg mode list i = reg) /\
  (REG_WRITEN (SUC n) reg mode list i =
     REG_WRITE_RP n (REG_WRITEN n reg mode list i) mode list
       (PROJ_DATA (i n)))`;

(* ------------------------------------------------------------------------- *)

val BITV_THM2 = prove(
  `!n. BITV n = \b. SBIT (BIT b n) 0`,
  REWRITE_TAC [FUN_EQ_THM] \\ SIMP_TAC std_ss [BITV_THM]);

val CLEARBIT_THM = prove(
  `!a w:bool ** 'a.  a < ^WL ==> ~((CLEARBIT a w) %% a)`,
  RW_TAC fcp_ss [CLEARBIT_def,word_modify_def]);

val CLEARBIT_THM2 = prove(
  `!a b w:bool ** 'a. ~(a = b) /\ (a < ^WL) ==>
      ((CLEARBIT b w) %% a = w %% a)`,
  RW_TAC fcp_ss [CLEARBIT_def,word_modify_def]);

val GEN_REG_LIST_ZERO = prove(
  `!n. GEN_REG_LIST 0 n = []`,
  SIMP_TAC list_ss [GENLIST,FILTER,MAP,GEN_REG_LIST_def]);

val GEN_REG_LIST_THM = prove(
  `!wl n. GEN_REG_LIST (SUC wl) n =
         if BIT wl n then SNOC wl (GEN_REG_LIST wl n)
                     else GEN_REG_LIST wl n`,
  RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC]);

val LENGTH_GEN_REG_LIST = prove(
  `!wl n. LENGTH (GEN_REG_LIST wl n) = SUM wl (BITV n)`,
  Induct >> REWRITE_TAC [GEN_REG_LIST_ZERO,LENGTH,SUM_def]
    \\ RW_TAC arith_ss [SUM_def,GEN_REG_LIST_THM,BITV_THM2,SBIT_def,
         LENGTH_SNOC,ADD1]);

(* ------------------------------------------------------------------------- *)

val BIT_w2n = prove(
  `!i w:bool ** 'a. i < ^WL ==> (BIT i (w2n w) = w %% i)`,
  STRIP_TAC \\ Cases \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss)
         [w2n_n2w,dimword_def,BIT_def,MIN_DEF,BITS_COMP_THM2,GSYM BITS_ZERO3]
    \\ ASM_SIMP_TAC fcp_ss [BIT_def,n2w_def]);

val MASKN_ZERO = store_thm("MASKN_ZERO",
  `!ireg. MASKN 0 list = Tw`,
  REWRITE_TAC [MASKN_def,FUNPOW]);

val MASKN_SUC = prove(
  `!n list. MASKN (SUC n) list = MASK_BIT list (MASKN n list)`,
  REWRITE_TAC [MASKN_def,FUNPOW_SUC]);

val lem = (SPEC `p` o SIMP_RULE bool_ss [] o INST [`P` |->
  `\b. (list && (MASKN
     (SUM p (\b. (if BIT b ireg then 1 else 0))) list)) %% b`]) LEAST_THM;

val MASKN_THM = prove(
  `!p list:bool ** 'a.
     (!x. p <= x /\ x < ^WL ==>
       (MASKN (SUM p (BITV (w2n list))) list) %% x) /\
     (!x. x < p /\ p <= ^WL ==>
       ~((list && (MASKN (SUM p (BITV (w2n list))) list)) %% x))`,
  REWRITE_TAC [BITV_THM2]
    \\ Induct
    >> SIMP_TAC bool_ss [prim_recTheory.NOT_LESS_0,SUM_def,MASKN_def,
         FUNPOW,word_T]
    \\ STRIP_TAC
    \\ POP_ASSUM (SPEC_THEN `list` (STRIP_ASSUME_TAC o
         SIMP_RULE arith_ss [SBIT_def]))
    \\ RW_TAC arith_ss [SUM_def,SBIT_def,GSYM ADD1,BIT_w2n]
    \\ REWRITE_TAC [MASKN_SUC,MASK_BIT_def,LEASTBIT_def]
    << [
      `(list && (MASKN
         (SUM p (\b. (if BIT b (w2n list) then 1 else 0))) list)) %% p`
        by ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_and_def]
        \\ IMP_RES_TAC lem
        \\ ASM_SIMP_TAC arith_ss [CLEARBIT_THM2],
      `(list && (MASKN
         (SUM p (\b. (if BIT b (w2n list) then 1 else 0))) list)) %% p`
        by ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_and_def]
        \\ IMP_RES_TAC lem
        \\ Cases_on `x < p`
        >> FULL_SIMP_TAC (fcp_ss++ARITH_ss) [CLEARBIT_THM2,word_and_def]
        \\ `x = p` by DECIDE_TAC
        \\ FULL_SIMP_TAC (fcp_ss++ARITH_ss) [CLEARBIT_THM,word_and_def],
      Cases_on `x < p` >> ASM_SIMP_TAC arith_ss []
        \\ `x = p` by DECIDE_TAC
        \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_and_def]]);

(* ------------------------------------------------------------------------- *)

val SUM_BITS = prove(
  `!p n. SUM (SUC p) (BITV n) =
           if BIT p n then
             SUC (SUM p (BITV n))
           else
             SUM p (BITV n)`,
  RW_TAC arith_ss [SUM_def,BITV_THM2,SBIT_def]);

val SUM_BITS2 = prove(
  `!p n. BIT p n ==> (SUM (SUC p) (BITV n) = SUC (SUM p (BITV n)))`,
  RW_TAC bool_ss [SUM_BITS]);

val SUM_BITS3 = prove(
  `!p n. BIT p n ==>
      (!q. q < p ==> ~(SUM (SUC q) (BITV n) = SUM (SUC p) (BITV n)))`,
  REPEAT STRIP_TAC
    \\ `~(BITV n p = 0)`
    by ASM_SIMP_TAC arith_ss [GSYM BIT_def,NOT_BITS,BITV_def]
    \\ IMP_RES_TAC ((GEN_ALL o REWRITE_RULE [GSYM LESS_EQ] o
         SPEC `SUC m`) SUM_MONO)
    \\ DECIDE_TAC);

val EL_GEN_REG_LIST = prove(
  `!x wl n. x < LENGTH (GEN_REG_LIST wl n) ==>
     (EL x (GEN_REG_LIST wl n) = $LEAST (\p. SUM (SUC p) (BITV n) = SUC x))`,
  Induct_on `wl`
    >> REWRITE_TAC [prim_recTheory.NOT_LESS_0,GEN_REG_LIST_ZERO,LENGTH]
    \\ RW_TAC arith_ss [GEN_REG_LIST_THM,LENGTH_SNOC]
    \\ Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    >> ASM_SIMP_TAC bool_ss [EL_SNOC]
    \\ `x = LENGTH (GEN_REG_LIST wl n)` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC]
    \\ ASM_SIMP_TAC bool_ss [LENGTH_GEN_REG_LIST,GSYM SUM_BITS2]
    \\ IMP_RES_TAC SUM_BITS3
    \\ IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `wl` o INST [`P` |->
         `\x. SUM (SUC x) (BITV n) = SUM (SUC wl) (BITV n)`]) LEAST_THM)
    \\ ASM_REWRITE_TAC []);

val EXISTS_SUM_BITS = prove(
  `!x wl n. x < LENGTH (GEN_REG_LIST wl n) ==>
     ?p. p < wl /\ (x = SUM p (BITV n))`,
  Induct_on `wl`
    >> REWRITE_TAC [prim_recTheory.NOT_LESS_0,GEN_REG_LIST_ZERO,LENGTH]
    \\ RW_TAC arith_ss [GEN_REG_LIST_THM,LENGTH_SNOC]
    << [
       Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
         << [
           PAT_ASSUM `!x n. P` IMP_RES_TAC
             \\ `p < SUC wl` by DECIDE_TAC \\ PROVE_TAC [],
           `x = LENGTH (GEN_REG_LIST wl n)` by DECIDE_TAC
             \\ FULL_SIMP_TAC bool_ss [LENGTH_GEN_REG_LIST]
             \\ EXISTS_TAC `wl` \\ SIMP_TAC arith_ss []
         ],
       PAT_ASSUM `!x n. P` IMP_RES_TAC
         \\ `p < SUC wl` by DECIDE_TAC \\ PROVE_TAC []]);

val SUM_LT = prove(
  `!p list:bool ** 'a.
     SUM p (BITV (w2n list)) < SUM ^WL (BITV (w2n list)) ==>
     ?y. p <= y /\ y < ^WL /\
        ((list && (MASKN (SUM p (BITV (w2n list))) list)) %% y) /\
     (!q. q < y ==>
       ~((list && (MASKN (SUM p (BITV (w2n list))) list)) %% q))`,
  REPEAT STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o
         (MATCH_MP ((GEN_ALL o snd o EQ_IMP_RULE o SPEC_ALL) SUM_LESS)))
    \\ RULE_ASSUM_TAC (SIMP_RULE arith_ss
         [BITV_THM,SBIT_def,METIS_PROVE [DECIDE ``~(1 = 0)``]
          ``!a. ((if a then 1 else 0) = 0) = ~a``])
    \\ RULE_ASSUM_TAC (REWRITE_RULE [(SIMP_RULE std_ss [] o
            SPEC `\y. p <= y /\ y < m /\ BIT y n`) LEAST_EXISTS])
    \\ ABBREV_TAC `z = LEAST y. p <= y /\ y < ^WL /\ BIT y (w2n list)`
    \\ POP_ASSUM (K ALL_TAC) \\ EXISTS_TAC `z`
    \\ RW_TAC arith_ss []
    >> (ASM_SIMP_TAC fcp_ss [MASKN_THM,word_and_def] \\ PROVE_TAC [BIT_w2n])
    \\ PAT_ASSUM `!n. P` (IMP_RES_TAC o SPEC `q`)
    \\ FULL_SIMP_TAC arith_ss []
    >> (`q < p /\ p <= ^WL` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [MASKN_THM])
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_and_def]
    \\ `q < ^WL` by DECIDE_TAC \\ PROVE_TAC [BIT_w2n]);

val lem3a = prove(
  `!y p list:bool ** 'a. p <= y /\ y < ^WL /\
    (list && (MASKN (SUM p (BITV (w2n list))) list)) %% y /\
    (!q. q < y ==>
           ~((list && (MASKN (SUM p (BITV (w2n list))) list)) %% q)) ==>
    (p <= y /\ y < ^WL /\ list %% y /\ (!q. q < y ==> ~(p <= q /\ list %% q)))`,
  RW_TAC bool_ss []
    >> PAT_ASSUM `y < ^WL` (fn th => FULL_SIMP_TAC fcp_ss [word_and_def,th])
    \\ SPOSE_NOT_THEN STRIP_ASSUME_TAC
    \\ PAT_ASSUM `!q. P` (SPEC_THEN `q` IMP_RES_TAC)
    \\ `q < ^WL` by DECIDE_TAC
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC (fcp_ss++ARITH_ss) [word_and_def,th]
         \\ ASSUME_TAC th)
    \\ PROVE_TAC [MASKN_THM]);

val SPEC_SUM_EQUAL2 =
  (GEN_ALL o SIMP_RULE std_ss [BITV_def,GSYM NOT_BIT] o
    SPECL [`p`,`y`,`BITV (w2n list)`]) SUM_EQUAL;

val SPEC_SUM_EQUAL3 = PROVE [SUM_EQUAL]
  ``!m n f. m <= n /\ (!q. m <= q /\ q < n ==> (f q = 0)) ==>
       (SUM m f = SUM n f)``;

val SPEC_SUM_EQUAL4 =
  (GEN_ALL o SIMP_RULE std_ss [BITV_def,GSYM NOT_BIT] o
   SPECL [`p`,`y`,`BITV (w2n list)`]) SPEC_SUM_EQUAL3;

val lem3b = prove(
  `!y p list:bool ** 'a.
   (p <= y /\ y < ^WL /\ list %% y /\
       (!q. q < y ==> ~(p <= q /\ list %% q))) ==>
   ((SUM (SUC y) (BITV (w2n list)) = SUC (SUM p (BITV (w2n list)))) /\
    (!q. q < y ==>
       ~(SUM (SUC q) (BITV (w2n list)) = SUC (SUM p (BITV (w2n list))))))`,
  RW_TAC arith_ss [SUM_def,BITV_THM,SBIT_def,GSYM ADD1,BIT_w2n]
    \\ RULE_ASSUM_TAC (REWRITE_RULE [DECIDE
         ``!a b c. (a ==> ~b \/ c) = (b /\ a ==> c)``])
    << [
      Cases_on `p = y` >> PROVE_TAC []
        \\ `p < y /\ !q. q < y ==> q < ^WL` by DECIDE_TAC
        \\ PROVE_TAC [SPEC_SUM_EQUAL2,BIT_w2n],
      RW_TAC arith_ss [GSYM ADD1,SPEC_SUM_EQUAL2]
        << [
          Cases_on `~(q <= p)` >> PROVE_TAC []
            \\ FULL_SIMP_TAC arith_ss []
            \\ Cases_on `q < p`
            >> (EXISTS_TAC `q` \\ ASM_SIMP_TAC arith_ss [BIT_w2n])
            \\ `p <= q` by DECIDE_TAC \\ PROVE_TAC [],
          Cases_on `~(p < q)` >> PROVE_TAC []
            \\ FULL_SIMP_TAC arith_ss []
            \\ `p <= q` by DECIDE_TAC
            \\ PROVE_TAC [],
          `SUM p (BITV (w2n list)) = SUM y (BITV (w2n list))`
            by (MATCH_MP_TAC SPEC_SUM_EQUAL4 \\
                  ASM_SIMP_TAC arith_ss [BIT_w2n])
            \\ ASM_SIMP_TAC arith_ss []
            \\ `SUC (SUM y (BITV (w2n list))) = SUM (SUC y) (BITV (w2n list))`
            by FULL_SIMP_TAC arith_ss
                 [BITV_def,SBIT_def,SUM_def,ADD1,GSYM BIT_def,BIT_w2n]
            \\ POP_ASSUM SUBST1_TAC
            \\ `q <= y` by DECIDE_TAC
            \\ METIS_TAC [(GEN_ALL o SIMP_RULE arith_ss
                 [BITV_def,GSYM NOT_BIT] o
                 SPECL [`q`,`y`,`BITV (w2n list)`]) SUM_MONO,
                 DECIDE ``a < b ==> ~(a = b:num)``,BIT_w2n]]]);

val lem3 = GEN_ALL (IMP_TRANS (SPEC_ALL lem3a) (SPEC_ALL lem3b));

val IN_LDM_STM =
  SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss) [] ``ic IN {ldm; stm}``;

val INST_16 =
  SIMP_RULE (bool_ss++SIZES_ss) [] o Thm.INST_TYPE [alpha |-> ``:16``];

val REGISTER_LIST_LEM = prove(
  `!ic x list:word16.
    (ic IN {ldm; stm}) /\
    x < LENGTH (GEN_REG_LIST 16 (w2n list)) ==>
    (n2w (EL x (GEN_REG_LIST 16 (w2n list))) = RP ic list (MASKN x list))`,
  RW_TAC bool_ss [EL_GEN_REG_LIST]
    \\ IMP_RES_TAC EXISTS_SUM_BITS
    \\ FULL_SIMP_TAC bool_ss [GSYM IN_LDM_STM,RP_def,LEASTBIT_def,
         LENGTH_GEN_REG_LIST]
    \\ IMP_RES_TAC (INST_16 SUM_LT)
    \\ IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `y` o
         INST [`P` |-> `\b. (list:word16 && (MASKN
           (SUM p (BITV (w2n list))) list)) %% b`]) LEAST_THM)
    \\ IMP_RES_TAC (INST_16 lem3)
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `y` o
         INST [`P` |-> `\p'. SUM (SUC p') (BITV n) =
           SUC (SUM p (BITV n))`]) LEAST_THM)
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD]);

(* ------------------------------------------------------------------------- *)

val MUST_BE_EQUAL = DECIDE ``!x y. x < SUC y /\ ~(x < y) ==> (x = y)``;

val EL_GEN_REG_LIST_LT_WL = prove(
  `!wl x n. x < LENGTH (GEN_REG_LIST wl n) ==> (EL x (GEN_REG_LIST wl n) < wl)`,
  Induct >> SIMP_TAC list_ss [GEN_REG_LIST_ZERO]
    \\ RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC,LENGTH_SNOC]
    \\ FULL_SIMP_TAC arith_ss [(GSYM o SIMP_RULE std_ss []) GEN_REG_LIST_def,
         EL_SNOC,(GSYM o CONJUNCT1) EL,prim_recTheory.LESS_SUC]
    \\ Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    >> ASM_SIMP_TAC arith_ss [EL_SNOC,prim_recTheory.LESS_SUC]
    \\ IMP_RES_TAC MUST_BE_EQUAL
    \\ ASM_SIMP_TAC arith_ss [EL_LENGTH_SNOC]);

(* ------------------------------------------------------------------------- *)

val EL_FILTER = prove(
  `!f g h j k l.
    (!x. x < LENGTH k ==>
           (f (EL x k) = g (EL x l)) /\
           (h (EL x k) = j (EL x l))) /\
    (LENGTH k = LENGTH l) ==>
    (!x. x < LENGTH (FILTER f k) ==>
       (h (EL x (FILTER f k)) = j (EL x (FILTER g l))))`,
  Induct_on `k` \\ Induct_on `l` \\ RW_TAC list_ss []
    >> (Cases_on `x` \\ ASM_SIMP_TAC list_ss [EL_CONS,prim_recTheory.PRE] \\
          METIS_TAC [EL,HD,TL,LESS_MONO_EQ,prim_recTheory.LESS_0])
    \\ METIS_TAC [EL,HD,TL,LESS_MONO_EQ,prim_recTheory.LESS_0]);

val LENGTH_FILTER = prove(
  `!f g k l. (!x. x < LENGTH k ==> (f (EL x k) = g (EL x l))) /\
    (LENGTH k = LENGTH l) ==>
    (LENGTH (FILTER f k) = LENGTH (FILTER g l))`,
  Induct_on `k` \\ Induct_on `l` \\ RW_TAC list_ss []
    \\ METIS_TAC [EL,HD,TL,LESS_MONO_EQ,prim_recTheory.LESS_0]);

val REGISTER_LIST_GEN_REG_LIST = prove(
  `!list. GEN_REG_LIST 16 (w2n list) = MAP w2n (REGISTER_LIST list)`,
  STRIP_TAC \\ MATCH_MP_TAC LIST_EQ \\ REWRITE_TAC [REGISTER_LIST_def]
    \\ Q.ABBREV_TAC `sz = 16`
    \\ SIMP_TAC list_ss [GEN_REG_LIST_def,REGISTER_LIST_def]
    \\ `LENGTH (FILTER FST (GENLIST (\b. (BIT b (w2n list),b)) sz)) =
        LENGTH (FILTER FST (GENLIST (\i. (list %% i,(n2w i):word4)) sz))`
    by (MATCH_MP_TAC LENGTH_FILTER \\
          SIMP_TAC std_ss [LENGTH_GENLIST,EL_GENLIST,INST_16 BIT_w2n, Abbr`sz`])
    \\ RW_TAC list_ss [EL_MAP]
    \\ `!z:bool # word4. w2n (SND z) = (w2n o SND) z`
    by SIMP_TAC std_ss []
    \\ POP_ASSUM (fn th => REWRITE_TAC [th]) \\ POP_ASSUM MP_TAC
    \\ CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) \\ MATCH_MP_TAC EL_FILTER
    \\ SIMP_TAC (list_ss++SIZES_ss)
         [EL_GENLIST,LENGTH_GENLIST,w2n_n2w,BIT_w2n]
    \\ SIMP_TAC (list_ss ++ SIZES_ss) [Abbr`sz`, BIT_w2n]);

val EL_GEN_REG_LIST_EQUAL = prove(
  `!wl x y n.
      x < LENGTH (GEN_REG_LIST wl n) /\
      y < LENGTH (GEN_REG_LIST wl n) ==>
     ((EL x (GEN_REG_LIST wl n) = EL y (GEN_REG_LIST wl n)) = (x = y))`,
  Induct >> SIMP_TAC list_ss [GEN_REG_LIST_ZERO]
    \\ RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC,LENGTH_SNOC]
    \\ FULL_SIMP_TAC arith_ss [(GSYM o SIMP_RULE std_ss []) GEN_REG_LIST_def,
         EL_SNOC,(GSYM o CONJUNCT1) EL]
    \\ Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    \\ Cases_on `y < LENGTH (GEN_REG_LIST wl n)`
    \\ ASM_SIMP_TAC arith_ss [EL_SNOC]
    \\ IMP_RES_TAC EL_GEN_REG_LIST_LT_WL
    \\ IMP_RES_TAC MUST_BE_EQUAL
    \\ ASM_SIMP_TAC arith_ss [EL_LENGTH_SNOC]);

val RP_NOT_EQUAL_ZERO = prove(
  `!x list. 0 < x /\
      x < LENGTH (GEN_REG_LIST 16 (w2n list)) ==>
     ~(RP stm list (MASKN x list) = RP stm list (MASKN 0 list))`,
  SIMP_TAC (arith_ss++SIZES_ss) [GSYM REGISTER_LIST_LEM,EL_GEN_REG_LIST_LT_WL,
    EL_GEN_REG_LIST_EQUAL,IN_LDM_STM,n2w_11]);

val RP_NOT_EQUAL_ZERO = save_thm("RP_NOT_EQUAL_ZERO",
  (REWRITE_RULE [MASKN_ZERO,LENGTH_MAP,REGISTER_LIST_GEN_REG_LIST])
   RP_NOT_EQUAL_ZERO);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!ic x list. ic IN {ldm; stm} /\ x < LENGTH (REGISTER_LIST list) ==>
         (EL x (REGISTER_LIST list) = RP ic list (MASKN x list))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC ((SIMP_RULE std_ss
         [LENGTH_MAP,REGISTER_LIST_GEN_REG_LIST] o GSYM) REGISTER_LIST_LEM)
    \\ IMP_RES_TAC (Thm.INST_TYPE
         [alpha |-> ``:word4``, beta |-> ``:num``] EL_MAP)
    \\ POP_ASSUM (SPEC_THEN `w2n` ASSUME_TAC)
    \\ ASM_SIMP_TAC std_ss [n2w_w2n]);

val RP_LT_16 = store_thm("RP_LT_16",
  `!x ic list mask. w2n (RP ic list mask) < 16`,
  PROVE_TAC [(SIMP_RULE (std_ss++SIZES_ss) [] o
    Thm.INST_TYPE [alpha |-> ``:4``]) w2n_lt]);

val LENGTH_TL_GENLIST = prove(
  `!n f. LENGTH (TL (GENLIST f (n + 1))) = n`,
  METIS_TAC [LENGTH_GENLIST,LENGTH_TL,
    DECIDE ``!n. 0 < n + 1 /\ (n + 1 - 1 = n)``]);

val SPEC_FOLDL_SNOC = (GEN_ALL o GSYM o SIMP_RULE std_ss [] o
  ISPECL [`(\(reg':reg) (rp:word4,rd:word32). REG_WRITE reg' mode rp rd)`,
          `reg:reg`,`(r:word4,a:word32)`])
  FOLDL_SNOC;

val PROJ_DATA_EL = store_thm("PROJ_DATA_EL",
  `!x n i. SUC x <= n ==>
     (PROJ_DATA (ADVANCE 1 i x) =
        EL x (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1))))`,
  RW_TAC arith_ss [GSYM EL,EL_GENLIST,ADVANCE_def,ADD1]);

val REGISTER_LIST_LDM_THM = store_thm("REGISTER_LIST_LDM_THM",
  `!n x list reg mode inp.
     x <= LENGTH (REGISTER_LIST list) /\
     LENGTH (REGISTER_LIST list) <= n ==>
     (LDM_LIST reg mode (FIRSTN x (FST (ADDR_MODE4 P U base list)))
               (FIRSTN x (TL (GENLIST (\s. PROJ_DATA (inp s)) (n + 1)))) =
      REG_WRITEN x reg mode list (ADVANCE 1 inp))`,
  Induct_on `x` \\ REPEAT STRIP_TAC
    >> SIMP_TAC list_ss [FIRSTN,LDM_LIST_def,REG_WRITEN_def]
    \\ `x <= LENGTH (REGISTER_LIST list)` by DECIDE_TAC
    \\ PAT_ASSUM `!n list reg mode inp. P` (IMP_RES_TAC o GSYM)
    \\ ASM_SIMP_TAC arith_ss [REG_WRITEN_def,ADDR_MODE4_def,REG_WRITE_RP_def,
         (REWRITE_RULE [IN_LDM_STM] o GSYM) REGISTER_LIST_THM]
    \\ `SUC x <= n` by DECIDE_TAC
    \\ IMP_RES_TAC PROJ_DATA_EL \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (ISPEC_THEN `inp` SUBST1_TAC)
    \\ `LENGTH (REGISTER_LIST list) <=
        LENGTH (TL (GENLIST (\s. PROJ_DATA (inp s)) (n + 1)))`
    by ASM_SIMP_TAC arith_ss [LENGTH_TL_GENLIST]
    \\ `EL x (TL (GENLIST (\s. PROJ_DATA (inp s)) (n + 1))) =
          EL x (FIRSTN (LENGTH (REGISTER_LIST list))
            (TL (GENLIST (\s. PROJ_DATA (inp s)) (n + 1))))`
    by ASM_SIMP_TAC arith_ss [GSYM EL_FIRSTN]
    \\ ASM_SIMP_TAC list_ss [LENGTH_TL_GENLIST,PROJ_DATA_EL,
         GSYM listTheory.EL_ZIP,SPEC_FOLDL_SNOC,LENGTH_FIRSTN,SNOC_EL_FIRSTN,
         LENGTH_ZIP,LDM_LIST_def,ZIP_FIRSTN_LEQ]);

val FST_ADDR_MODE4 = save_thm("FST_ADDR_MODE4",
  (GEN_ALL o SIMP_CONV std_ss [ADDR_MODE4_def])
  ``FST (ADDR_MODE4 P U base n)``);

val SND_ADDR_MODE4 = save_thm("SND_ADDR_MODE4",
  SIMP_CONV std_ss [ADDR_MODE4_def] ``SND (ADDR_MODE4 P U base n)``);

val LENGTH_ADDR_MODE4 = save_thm("LENGTH_ADDR_MODE4",
  (GEN_ALL o REWRITE_CONV [FST_ADDR_MODE4])
  ``LENGTH (FST (ADDR_MODE4 P U base n))``);

val REGISTER_LIST_STM_THM = save_thm("REGISTER_LIST_STM_THM",
  (GSYM o REWRITE_RULE [IN_LDM_STM,GSYM FST_ADDR_MODE4] o
   SPEC `stm`) REGISTER_LIST_THM);

val LENGTH_ADDRESS_LIST =
  (GEN_ALL o REWRITE_CONV [LENGTH_GENLIST,ADDRESS_LIST_def])
  ``LENGTH (ADDRESS_LIST base n)``;

val FST_HD_FST_ADDR_MODE4 = store_thm("FST_HD_FST_ADDR_MODE4",
  `!P U base n. 0 < LENGTH (REGISTER_LIST n) ==>
     (HD (FST (ADDR_MODE4 P U base n)) = RP stm n Tw)`,
  METIS_TAC [FST_ADDR_MODE4,(GSYM o CONJUNCT1) EL,MASKN_ZERO,
    LENGTH_ADDRESS_LIST,REGISTER_LIST_THM,IN_LDM_STM]);

(* ------------------------------------------------------------------------- *)

val lift_gen_reg_list =
  (GEN_ALL o SIMP_RULE arith_ss
    [(GEN_ALL o SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w] o
        ISPECL [`v:word4`,`15w:word4`]) w2n_11,
    EL_MAP,LENGTH_MAP,REGISTER_LIST_GEN_REG_LIST] o
  ISPECL [`15`,`w2n (list:word16)`]);

val GEN_REG_LIST_NOT_LAST = prove(
  `!x n y. y < LENGTH (GEN_REG_LIST (SUC x) n) - 1 ==>
             ~(EL y (GEN_REG_LIST (SUC x) n) = x)`,
  RW_TAC arith_ss [LENGTH_SNOC,GEN_REG_LIST_THM,EL_SNOC]
    >> (IMP_RES_TAC EL_GEN_REG_LIST_LT_WL \\ ASM_SIMP_TAC arith_ss [])
    \\ `y < LENGTH (GEN_REG_LIST x n)` by DECIDE_TAC
    \\ IMP_RES_TAC EL_GEN_REG_LIST_LT_WL
    \\ ASM_SIMP_TAC arith_ss []);

val REGISTER_LIST_NOT_LAST = lift_gen_reg_list GEN_REG_LIST_NOT_LAST;

val RP_NOT_15 = store_thm("RP_NOT_15",
  `!ic y n. ic IN {ldm; stm} /\ y < LENGTH (REGISTER_LIST n) - 1 ==>
            ~(RP ic n (MASKN y n) = 15w)`,
  SIMP_TAC arith_ss [REGISTER_LIST_NOT_LAST,EL_MAP,n2w_w2n,
      (GSYM o SIMP_RULE std_ss [LENGTH_MAP,REGISTER_LIST_GEN_REG_LIST])
       REGISTER_LIST_LEM]);

val lem = DECIDE ``!x. 0 < x ==> (x - 1 < x) /\ (x = SUC (x - 1))``;

val GEN_RP_LAST = prove(
  `!x n. 0 < LENGTH (GEN_REG_LIST (SUC x) n) ==>
     ((EL (LENGTH (GEN_REG_LIST (SUC x) n) - 1) (GEN_REG_LIST (SUC x) n) = x) =
      BIT x n)`,
  RW_TAC arith_ss [LENGTH_SNOC,GEN_REG_LIST_THM,EL_SNOC,EL_LENGTH_SNOC]
    \\ PROVE_TAC [lem,prim_recTheory.LESS_NOT_EQ,EL_GEN_REG_LIST_LT_WL]);

val lift_gen_reg_list =
  (SIMP_RULE (std_ss++SIZES_ss) [BIT_w2n] o lift_gen_reg_list);

val REGISTER_LIST_LAST = lift_gen_reg_list GEN_RP_LAST;

val RP_LAST_15 = store_thm("RP_LAST_15",
  `!list. 0 < LENGTH (REGISTER_LIST list) ==>
     ((RP ldm list (MASKN (LENGTH (REGISTER_LIST list) - 1) list) = 15w) =
      list %% 15)`,
  SIMP_TAC arith_ss [IN_LDM_STM,GSYM REGISTER_LIST_THM,REGISTER_LIST_LAST]);

val REG_WRITEN_COMMUTES = store_thm("REG_WRITEN_COMMUTES",
  `!n ireg reg m1 m2 i.
        n < LENGTH (REGISTER_LIST ireg) ==>
          (REG_WRITEN n (REG_WRITE reg m1 15w d) m2 ireg i =
           REG_WRITE (REG_WRITEN n reg m2 ireg i) m1 15w d)`,
  Induct \\ RW_TAC bool_ss [REG_WRITEN_def,TO_WRITE_READ6,REG_WRITE_RP_def]
    \\ ASM_SIMP_TAC arith_ss [REG_WRITE_RP_def,RP_LT_16,RP_NOT_15,IN_LDM_STM,
         REG_WRITE_WRITE_PC]);

val LENGTH_GEN_REG_LIST_NOT_ZERO = prove(
  `!wl ireg. BIT wl ireg ==> 0 < LENGTH (GEN_REG_LIST (SUC wl) ireg)`,
  RW_TAC arith_ss [LENGTH_GEN_REG_LIST,SUM_def,BITV_THM,SBIT_def]);

val LENGTH_REGISTER_LIST_NOT_ZERO =
  lift_gen_reg_list LENGTH_GEN_REG_LIST_NOT_ZERO;

(* --- *)

val writen_pc_tac = REPEAT STRIP_TAC
  \\ IMP_RES_TAC LENGTH_REGISTER_LIST_NOT_ZERO
  \\ IMP_RES_TAC lem \\ POP_ASSUM SUBST1_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
  \\ ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,
       REG_WRITEN_COMMUTES,TO_WRITE_READ6,REG_WRITE_WRITE,REG_READ_WRITE];

val REG_WRITE_WRITEN_PC = store_thm("REG_WRITE_WRITEN_PC",
  `!list reg mode i. list %% 15 ==>
      (REG_WRITEN (LENGTH (REGISTER_LIST list))
         (REG_WRITE reg usr 15w d) mode list i =
       REG_WRITEN (LENGTH (REGISTER_LIST list)) reg mode list i)`,
  writen_pc_tac);

val REG_WRITEN_WRITE_PC = store_thm("REG_WRITEN_WRITE_PC",
  `!list reg mode i. list %% 15 ==>
      (REG_WRITE (REG_WRITEN
         (LENGTH (REGISTER_LIST list)) reg mode list i) usr 15w
            (PROJ_DATA (i (LENGTH (REGISTER_LIST list) - 1))) =
       REG_WRITEN (LENGTH (REGISTER_LIST list)) reg mode list i)`,
  writen_pc_tac);

val REG_WRITEN_WRITE_PC2 = store_thm("REG_WRITEN_WRITE_PC2",
  `!list reg mode i. list %% 15 ==>
      (REG_WRITE (REG_WRITEN
         (LENGTH (REGISTER_LIST list) - 1) reg mode list i) usr 15w
            (PROJ_DATA (i (LENGTH (REGISTER_LIST list) - 1))) =
       REG_WRITEN (LENGTH (REGISTER_LIST list)) reg mode list i)`,
  writen_pc_tac);

val REG_READ_WRITEN_PC = store_thm("REG_READ_WRITEN_PC",
  `!list reg mode i. list %% 15 ==>
      (REG_READ6 (REG_WRITEN
         (LENGTH (REGISTER_LIST list)) reg mode list i) usr 15w =
      (PROJ_DATA (i (LENGTH (REGISTER_LIST list) - 1))))`,
  writen_pc_tac);

val REG_WRITEN_COMMUTE_PC = store_thm("REG_WRITEN_COMMUTE_PC",
  `!list reg mode i.  ~(list %% 15) /\ 0 < LENGTH (REGISTER_LIST list) ==>
      (REG_WRITEN (LENGTH (REGISTER_LIST list))
         (REG_WRITE reg usr 15w d) mode list i =
       REG_WRITE (REG_WRITEN
         (LENGTH (REGISTER_LIST list)) reg mode list i) usr 15w d)`,
  writen_pc_tac \\ ASM_SIMP_TAC arith_ss [REG_WRITE_WRITE_PC]);

val REG_READ_WRITEN_PC2 = store_thm("REG_READ_WRITEN_PC2",
  `!list reg mode i. x < LENGTH (REGISTER_LIST list) ==>
      (REG_READ6 (REG_WRITEN x reg mode list i) usr 15w =
       REG_READ6 reg usr 15w)`,
  REPEAT STRIP_TAC \\ Induct_on `x`
    \\ REWRITE_TAC [REG_WRITEN_def]
    \\ STRIP_TAC \\ IMP_RES_TAC prim_recTheory.SUC_LESS
    \\ ASM_SIMP_TAC arith_ss [IN_LDM_STM,REG_WRITE_RP_def,RP_NOT_15,
         REG_READ_WRITE_PC]);

(* ------------------------------------------------------------------------- *)

val LENGTH_REGISTER_LIST = save_thm("LENGTH_REGISTER_LIST",
  (GEN_ALL o REWRITE_RULE [LENGTH_MAP,REGISTER_LIST_GEN_REG_LIST] o
   SPECL [`16`,`w2n (list:word16)`]) LENGTH_GEN_REG_LIST);

val REGISTER_LIST_LENGTH = GSYM LENGTH_REGISTER_LIST;

val PENCZ1 = prove(
   `!list:word16 x. x < LENGTH (GEN_REG_LIST 16 (w2n list)) ==>
       ~(list && (MASKN x list) = 0w)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_SUM_BITS
    \\ POP_ASSUM SUBST_ALL_TAC
    \\ FULL_SIMP_TAC bool_ss [LENGTH_GEN_REG_LIST]
    \\ IMP_RES_TAC (INST_16 SUM_LT)
    \\ PAT_ASSUM `list && (MASKN (SUM p (BITV (w2n list))) list) = 0w`
         SUBST_ALL_TAC
    \\ PROVE_TAC [INST_16 word_0]);

val PENCZ1 = REWRITE_RULE [LENGTH_GEN_REG_LIST,REGISTER_LIST_LENGTH] PENCZ1;

val PENCZ2 = prove(
  `!list. list && (MASKN (LENGTH (REGISTER_LIST list)) list) = 0w`,
  SIMP_TAC (arith_ss++SIZES_ss) [GSYM WORD_EQ,word_bit_def,word_0,
    LENGTH_REGISTER_LIST,MASKN_THM]);

val PENCZ_THM = store_thm("PENCZ_THM",
  `!ic. ic IN {ldm; stm} ==>
         (!list x. x < LENGTH (REGISTER_LIST list) ==>
            ~PENCZ ic list (MASKN x list)) /\
         !list. PENCZ ic list (MASKN (LENGTH (REGISTER_LIST list)) list)`,
  RW_TAC bool_ss [IN_LDM_STM,PENCZ_def,PENCZ2,PENCZ1]);

val PENCZ_THM2 = store_thm("PENCZ_THM2",
  `!list. (list = 0w) = (LENGTH (REGISTER_LIST list) = 0)`,
  Cases \\ SIMP_TAC bool_ss
         [LENGTH_REGISTER_LIST,BITV_def,GSYM SUM_ZERO,BITS_COMP_THM2,w2n_n2w,
          MOD_DIMINDEX,GSYM WORD_EQ,word_bit_n2w,BIT_def,BITS_ZERO2,dimindex_16]
    \\ SIMP_TAC arith_ss [MIN_DEF,NOT_BITS2]);

val PENCZ_THM3 = store_thm("PENCZ_THM3",
  `!list mask. (list = 0w) /\ ic IN {ldm; stm} ==> PENCZ ic list mask`,
  SIMP_TAC std_ss [PENCZ_def,WORD_AND_CLAUSES,IN_LDM_STM]);

(* ------------------------------------------------------------------------- *)

val ADD_THREE_ONE = prove(
  `!a. 3w + a + 1w = a + 4w`,
  SIMP_TAC arith_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,word_add_n2w]);

val NOT_ADD = prove(
  `!a b. ~a + b = b - (a + 1w)`,
  REWRITE_TAC [WORD_NOT,GSYM WORD_ADD_SUB_SYM,WORD_SUB_PLUS,
    WORD_LCANCEL_SUB,WORD_SUB]);

val NOT_ADD_1 = prove(
  `!a b. ~a + b + 1w = b - a`,
  REWRITE_TAC [WORD_NOT,GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,WORD_SUB]);

val FIRST_ADDRESS = store_thm("FIRST_ADDRESS",
  `!ireg ic base c borrow2 mul.
    1 <= LENGTH (REGISTER_LIST ((15 >< 0) ireg)) /\ ic IN {ldm; stm} ==>
    (FIRST_ADDRESS (ireg %% 24) (ireg %% 23) base
      (WB_ADDRESS (ireg %% 23) base (LENGTH (REGISTER_LIST ((15 >< 0) ireg)))) =
     SND (ALU6 ic t3 ireg borrow2 mul F
      (OFFSET ic t3 ireg ((15 >< 0) ireg)) base c))`,
  RW_TAC std_ss [FIRST_ADDRESS_def,WB_ADDRESS_def,ALU6_def,OFFSET_def,
        ALUOUT_ADD_CARRY,ALUOUT_ADD,ALUOUT_ALU_logic,UP_DOWN_def,
        REGISTER_LIST_LENGTH,IN_LDM_STM,ADD_THREE_ONE,NOT_ADD,NOT_ADD_1,
        word_mul_n2w,WORD_EQ_ADD_LCANCEL,WORD_ADD_SUB_SYM,WORD_SUB_SUB]
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_SUB_ADD,
        EVAL ``3w + 1w:word32``]);

val WB_ADDRESS = store_thm("WB_ADDRESS",
  `!ireg ic base c borrow2 mul. ic IN {ldm; stm} ==>
    (WB_ADDRESS (ireg %% 23) base (LENGTH (REGISTER_LIST ((15 >< 0) ireg))) =
     SND (ALU6 ic t4 ireg borrow2 mul F
       (OFFSET ic t4 ireg ((15 >< 0) ireg)) base c))`,
  RW_TAC std_ss [FIRST_ADDRESS_def,WB_ADDRESS_def,ALU6_def,OFFSET_def,
        ALUOUT_ADD_CARRY,ALUOUT_ADD,ALUOUT_ALU_logic,UP_DOWN_def,
        REGISTER_LIST_LENGTH,IN_LDM_STM,ADD_THREE_ONE,NOT_ADD,NOT_ADD_1,
        word_mul_n2w,WORD_EQ_ADD_LCANCEL,WORD_ADD_SUB_SYM,WORD_SUB_SUB,
        PENCZ_THM2,WORD_ADD_0,WORD_SUB_RZERO]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,WORD_EQ_ADD_LCANCEL]
    \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,EVAL ``1w + 3w:word32``,WORD_SUB_ADD2]);

val WB_ADDRESS_ZERO = save_thm("WB_ADDRESS_ZERO",
  (GEN_ALL o
   SIMP_RULE bool_ss [(GEN_ALL o snd o EQ_IMP_RULE o SPEC_ALL) PENCZ_THM2] o
   DISCH `LENGTH (REGISTER_LIST ((15 >< 0) ireg)) = 0` o
   GSYM o SPEC_ALL) WB_ADDRESS);

(* ------------------------------------------------------------------------- *)

val MASKN_SUC = store_thm("MASKN_SUC",
  `!n ic list. ((ic = ldm) \/ (ic = stm)) ==>
       (CLEARBIT (w2n (RP ic list (MASKN n list))) (MASKN n list) =
        MASKN (SUC n) list)`,
  SIMP_TAC (arith_ss++SIZES_ss) [MASKN_SUC,MASK_BIT_def,RP_def,w2n_n2w]);

val LDM_LIST_EMPTY = store_thm("LDM_LIST_EMPTY",
  `!reg mode. LDM_LIST reg mode [] [] = reg`,
  SIMP_TAC list_ss [LDM_LIST_def]);

val WORD_BITS_150_ZERO = store_thm("WORD_BITS_150_ZERO",
  `(!i:word32. (((15 >< 0) i = 0w:word16) ==> ~(i %% 15))) /\
    !i:word32. (i %% 15 = ((15 >< 0) i):word16 %% 15)`,
  STRIP_TAC \\ REWRITE_TAC [GSYM WORD_EQ]
    \\ RW_TAC (fcp_ss++ARITH_ss++SIZES_ss) [word_bit_def,word_0,
         word_extract_def,word_bits_def,w2w]);

(* ------------------------------------------------------------------------- *)

val IS_ABORT_ZERO = prove(
  `(?s. s < 1 /\ IS_ABORT i (s + 1)) = IS_ABORT i 1`,
  EQ_TAC \\ REPEAT STRIP_TAC
    >> (`s = 0` by DECIDE_TAC \\ FULL_SIMP_TAC arith_ss [])
    \\ EXISTS_TAC `0` \\ ASM_SIMP_TAC arith_ss []);

val LEAST_ABORT_ZERO = prove(
  `!w i. 0 < w /\ IS_ABORT i 1 ==>
      ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = 0)`,
  RW_TAC arith_ss [LEAST_DEF,Once WHILE]);

val LEAST_ABORT_ZERO_ISA = store_thm("LEAST_ABORT_ZERO_ISA",
  `!i. IS_ABORT i 1 ==> ((LEAST s. IS_ABORT i (s + 1)) = 0)`,
  RW_TAC arith_ss [LEAST_DEF,Ntimes WHILE 2]);

val lem = prove(
  `(!m. m < n ==> ~(m < w /\ IS_ABORT i (m + 1))) /\
                    n < w /\ IS_ABORT i (n + 1) ==>
          (n = LEAST s. IS_ABORT i (s + 1))`,
  RW_TAC std_ss []
    \\ `!m. m < n ==> m < w` by METIS_TAC [LESS_TRANS]
    \\ FULL_SIMP_TAC std_ss [(BETA_RULE o
         INST [`P` |-> `\s. IS_ABORT i (s + 1)`]) LEAST_THM]);

val LEAST_ABORT_ISA = store_thm("LEAST_ABORT_ISA",
  `(?s. s < w /\ IS_ABORT i (s + 1)) ==>
    ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = (LEAST s. IS_ABORT i (s + 1)))`,
  RW_TAC std_ss []
    \\ IMP_RES_TAC ((GEN_ALL o BETA_RULE o
         SPECL [`\l. l = LEAST s. IS_ABORT i (s + 1)`,
                `\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM)
    \\ METIS_TAC [lem]);

val LEAST_ABORT_LT2 = store_thm("LEAST_ABORT_LT2",
  `(?s. s < w /\ IS_ABORT i (s + 1)) ==> (LEAST s. IS_ABORT i (s + 1)) < w`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC (GSYM LEAST_ABORT_ISA)
    \\ POP_ASSUM SUBST1_TAC
    \\ METIS_TAC [lem,(GEN_ALL o SIMP_RULE bool_ss [] o
         BETA_RULE o SPECL [`\l. l < w`,
           `\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM]);

(* ------------------------------------------------------------------------- *)

val NEW_ABORT_SUC = prove(
  `!x. (?s. s < x + 1 /\ IS_ABORT i (s + 1)) \/ IS_ABORT i (x + 2) =
        ?s. s < x + 2 /\ IS_ABORT i (s + 1)`,
  STRIP_TAC \\ EQ_TAC \\ RW_TAC arith_ss []
    >> METIS_TAC [DECIDE ``!s x. s < x + 1 ==> s < x + 2``]
    >> (EXISTS_TAC `x + 1` \\ ASM_SIMP_TAC arith_ss [])
    \\ Cases_on `s = x + 1` >> FULL_SIMP_TAC arith_ss []
    \\ DISJ1_TAC \\ EXISTS_TAC `s`
    \\ ASM_SIMP_TAC arith_ss []);

val lem = prove(
  `!w x i. SUC x <= w - 1 /\ (!s. s < x + 1 ==>
        ~IS_ABORT i (s + 1)) /\ s < x + 2 /\ IS_ABORT i (s + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n = x + 1))`,
  RW_TAC std_ss [] \\ Cases_on `n < x + 1`
    >> PAT_ASSUM `!s. s < w ==> ~IS_ABORT i (s + 1)`
         (SPEC_THEN `n` IMP_RES_TAC)
    \\ Tactical.REVERSE (Cases_on `x + 1 < n`) >> DECIDE_TAC
    \\ `s < n /\ s < w` by DECIDE_TAC
    \\ PAT_ASSUM `!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)`
         (SPEC_THEN `s` IMP_RES_TAC));

val NEW_LEAST_ABORT_SUC = prove(
  `!x w i s. SUC x <= w - 1 /\
       (!s. s < x + 1 ==> ~IS_ABORT i (s + 1)) /\
            s < x + 2 /\ IS_ABORT i (s + 1) ==>
              ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = x + 1)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC lem
    \\ `s < w` by DECIDE_TAC
    \\ IMP_RES_TAC ((GEN_ALL o
         REWRITE_RULE [DECIDE ``!a b c. a /\ b ==> c = (a ==> b ==> c)``,
                       DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
         BETA_RULE o SPECL [`\l. l = x + 1`,`\s. s < w /\ IS_ABORT i (s + 1)`])
         LEAST_ELIM));

val NEW_LEAST_ABORT_ZERO = prove(
  `!w i. 0 < w /\ (?s. s < 1 /\ IS_ABORT i (s + 1)) ==>
     ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = 0)`,
   REPEAT STRIP_TAC \\ `s = 0 ` by DECIDE_TAC
     \\ FULL_SIMP_TAC arith_ss [LEAST_DEF,Once WHILE]);

val lem = prove(
  `!w x i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n < w))`,
  RW_TAC arith_ss []);

val NEW_LEAST_ABORT_LT = prove(
  `!x w i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) < w)`,
  METIS_TAC [lem,DECIDE ``x < w - 1 ==> x < w``,
    (GEN_ALL o REWRITE_RULE [DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
     BETA_RULE o SPECL [`\l. l < w`,`\s. s < w /\ IS_ABORT i (s + 1)`])
    LEAST_ELIM]);

val NEW_LEAST_ABORT_LT2 = prove(
  `!x w i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) - 1 < w)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC NEW_LEAST_ABORT_LT \\ DECIDE_TAC);

val lem = prove(
  `!w x i. 1 < w /\ x < w /\ IS_ABORT i (x + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n - 1 < w))`,
  RW_TAC arith_ss []);

val NEW_LEAST_ABORT_LT3 = prove(
  `!x w i. 1 < w /\ x < w /\ IS_ABORT i (x + 1) ==>
      ((LEAST s. s < w /\ IS_ABORT i (s + 1)) - 1 < w)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC lem
    \\ METIS_TAC [(GEN_ALL o
         REWRITE_RULE [DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
         BETA_RULE o SPECL [`\l. l - 1 < w`,`\s. s < w /\ IS_ABORT i (s + 1)`])
         LEAST_ELIM]);

(* ------------------------------------------------------------------------- *)

val MULT_ADD_FOUR = prove(
  `!a x. a + n2w x * 4w + 4w = a + n2w (x + 1) * 4w`,
  REWRITE_TAC [RIGHT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC,MULT_LEFT_1,
    word_add_n2w,word_mul_n2w]);

fun SIMP_ASSUM a = (SIMP_RULE (stdi_ss++ARITH_ss)
  [COND_PAIR,MASKN_SUC,PENCZ_THM3,IN_LDM_STM] o DISCH a);

val REG_WRITEN_SUC = save_thm("REG_WRITEN_SUC",
  (GEN_ALL o SIMP_RULE arith_ss [ADD1,ADVANCE_def] o
   INST [`i` |-> `ADVANCE 1 i`] o SPEC_ALL o
   REWRITE_RULE [REG_WRITE_RP_def] o GSYM o CONJUNCT2) REG_WRITEN_def);

val lem = prove(
  `!b. ~((if b then tm else tn) = t3)`, PROVE_TAC [iseq_distinct]);

val NEXT_CORE_LDM_TN1 = (GEN_ALL o
   SIMP_ASSUM `~((15 >< 0) ireg = 0w:word16)` o
   GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites
   [MULT_ADD_FOUR,ALUOUT_ALU_logic,LSL_ZERO,lem] o LDM_ITER_CONV)
   ``NEXT_ARM6 (ARM6 (DP (REG_WRITEN y reg
         (if ireg %% 22 /\ ~(ireg %% 15) then usr else
            DECODE_MODE ((4 >< 0) (CPSR_READ psr))) ((15 >< 0) ireg) din)
         psr (base + n2w (x + 1) * 4w) din2 alua alub dout)
      (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F ldm tn
         T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
         aregn2 T T F sctrlreg psrfb oareg (MASKN (x + 2) ((15 >< 0) ireg))
         (RP ldm ((15 >< 0) ireg) (MASKN (x + 1) ((15 >< 0) ireg)))
         (RP ldm ((15 >< 0) ireg) (MASKN x ((15 >< 0) ireg)))
         mul mul2 borrow2 mshift)) (NRESET,ABORT,NFQ,NIQ,DATA,CPA,CPB)``;

val LDM_PENCZ_THM =
  (GEN_ALL o SIMP_RULE std_ss [] o
   DISCH `LENGTH (REGISTER_LIST list) = x` o
   SPEC `list` o CONJUNCT2 o SIMP_RULE stdi_ss [IN_LDM_STM] o
   SPEC `ldm`) PENCZ_THM;

val LDM_PENCZ_LEM = prove(
  `!list x. SUC x <= LENGTH (REGISTER_LIST list) - 1 ==>
       (PENCZ ldm list (MASKN (x + 2) list) =
        (x + 1 = LENGTH (REGISTER_LIST list) - 1))`,
  RW_TAC std_ss [GSYM ADD1]
    \\ Cases_on `SUC x  = LENGTH (REGISTER_LIST list) - 1`
    >> (`LENGTH (REGISTER_LIST list) = x + 2` by DECIDE_TAC \\
          ASM_SIMP_TAC arith_ss [LDM_PENCZ_THM])
    \\ ASM_SIMP_TAC arith_ss [PENCZ_THM,IN_LDM_STM]);

val NEXT_CORE_LDM_TN_X = store_thm("NEXT_CORE_LDM_TN_X",
   `!x w reg ireg alub alua din dout i.
      (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
      0 < w ==>
      x <= w - 1 ==>
      (!t. t < SUC (SUC w) ==> ~IS_RESET i t) ==>
      ?ointstart' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt'
       aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(aregn' IN {0w; 1w; 2w; 5w}) /\
        ((aregn' = 7w) ==> ~((CPSR_READ psr) %% 6)) /\
        ((aregn' = 6w) ==> ~((CPSR_READ psr) %% 7)) /\
       (FUNPOW (SNEXT NEXT_ARM6) x <|state := ARM6
           (DP reg psr (if w = 1 then din else base + 1w * 4w)
             (PROJ_DATA (i 1)) alua alub dout)
           (CTRL pipea T pipeb T ireg T ointstart F F T F ldm
             (if w = 1 then tm else tn) (~(w = 1)) F F onfq ooonfq oniq oooniq
             pipeaabt pipebabt pipebabt (IS_ABORT i 1) aregn2 (~(w = 1)) T F
             sctrlreg psrfb oareg (MASKN 2 ((15 >< 0) ireg))
             (RP ldm ((15 >< 0) ireg) (MASKN 1 ((15 >< 0) ireg)))
             (RP ldm ((15 >< 0) ireg) Tw) mul mul2 borrow2 mshift);
           inp := ADVANCE 2 i|> =
        (let dataabt2 = ?s. (s < x + 1) /\ IS_ABORT i (s + 1) in
         let y = if dataabt2 then LEAST s. (s < w) /\ IS_ABORT i (s + 1) else x
         and nbs = if ireg %% 22 /\ ~(ireg %% 15) then usr
                   else DECODE_MODE ((4 >< 0) (CPSR_READ psr)) in
         <| state := ARM6
           (DP (REG_WRITEN y reg nbs ((15 >< 0) ireg) (ADVANCE 1 i))
             psr (if (x = w - 1) /\ ~(w = 1) then
                    REG_READ6 (REG_WRITEN (y - 1) reg nbs ((15 >< 0) ireg)
                      (ADVANCE 1 i)) usr 15w
                   else if w = 1 then din else base + n2w (SUC x) * 4w)
             (PROJ_DATA (i (x + 1)))
             (if x = 0 then alua else REG_READ6 reg nbs ((19 >< 16) ireg))
             (if x = 0 then alub else PROJ_DATA (i x))
             (if x = 0 then dout else PROJ_DATA (i x)))
           (CTRL pipea T pipeb T ireg T ointstart' F F (x = 0) F ldm
             (if x = w - 1 then tm else tn) (~(x = w - 1)) F F onfq' ooonfq'
              oniq' oooniq' pipeaabt' pipebabt' pipebabt' dataabt2
              (if x = 0 then aregn2 else
                 if ointstart' then (if dataabt2 then 4w else aregn') else 2w)
              (~(x = w - 1)) T F sctrlreg
              (if x = 0 then psrfb else SPSR_READ psr nbs)
              (if x = 0 then oareg else oareg')
              (MASKN (SUC (SUC x)) ((15 >< 0) ireg))
              (RP ldm ((15 >< 0) ireg) (MASKN (SUC x) ((15 >< 0) ireg)))
              (RP ldm ((15 >< 0) ireg) (MASKN x ((15 >< 0) ireg)))
              mul' mul2' borrow2' mshift'); inp := ADVANCE x (ADVANCE 2 i)|>))`,
  Induct
    >> (RW_TAC arith_ss [FUNPOW,REG_WRITEN_def,MASKN_ZERO,ADVANCE_ZERO,
            IS_ABORT_ZERO,LEAST_ABORT_ZERO] \\
          FULL_SIMP_TAC arith_ss [interrupt_exists])
    \\ REPEAT STRIP_TAC
    \\ `1 < w /\ x <= w - 1` by DECIDE_TAC
    \\ PAT_ASSUM `!w reg ireg alub alua din dout i. X` IMP_RES_TAC
    \\ POP_ASSUM (SPECL_THEN [`reg`,`dout`,`din`,`alub`,`alua`]
         STRIP_ASSUME_TAC)
    \\ FULL_SIMP_TAC arith_ss [FUNPOW_SUC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ `~((15 >< 0) ireg = 0w:word16)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    \\ `~IS_RESET i (x + 2)` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [SNEXT,NEXT_CORE_LDM_TN1,
           PROJ_DATA_def,state_arm6_11,dp_11,ctrl_11,ADD1,NEW_ABORT_SUC,
           ADVANCE_def,GSYM ADVANCE_COMP,LDM_PENCZ_LEM,
           DECIDE ``!a b. (~a \/ b) = (a ==> b)``,
           NEW_LEAST_ABORT_ZERO,CONJUNCT1 REG_WRITEN_def]
    \\ SIMP_TAC (bool_ss++boolSimps.CONJ_ss) [REG_WRITEN_SUC]
    \\ ONCE_REWRITE_TAC [DECIDE ``a /\ b /\ c /\ d /\ e /\ f /\ g =
                                   (a /\ b /\ c /\ g) /\ (d /\ e /\ f)``]
    \\ CONV_TAC EXISTS_AND_CONV
    \\ CONJ_TAC
    << [
      ASM_SIMP_TAC std_ss [NEW_ABORT_SUC,
             DECIDE ``a \/ b \/ c \/ d \/ e = (b \/ a) \/ c \/ d \/ e``]
        \\ RW_TAC (arith_ss++SIZES_ss) [AREGN1_def,n2w_11,
             pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY]
        \\ EXISTS_TAC `3w` \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11],
      CONJ_TAC
        << [
           RW_TAC std_ss [ADD1]
             \\ FULL_SIMP_TAC arith_ss [DECIDE ``!a b. (~a \/ b) = (a ==> b)``]
             \\ TRY (METIS_TAC [DECIDE ``!s. s < x + 1 ==> s < x + 2``,
                  NEW_LEAST_ABORT_SUC]),
           CONJ_TAC
             >> RW_TAC arith_ss [NEW_LEAST_ABORT_LT,NEW_LEAST_ABORT_LT2,
                  NEW_LEAST_ABORT_LT3,REG_READ_WRITEN_PC2]
             \\ RW_TAC arith_ss [RP_NOT_15,IN_LDM_STM] \\ METIS_TAC []]]);

val NEXT_CORE_LDM_TN_W1 = save_thm("NEXT_CORE_LDM_TN_W1",
  (GEN_ALL o SIMP_RULE std_ss [] o
    DISCH `Abbrev (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) /\
           Abbrev (nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr)))` o
    SIMP_RULE arith_ss [WORD_MULT_CLAUSES,GSYM ADVANCE_COMP,WORD_ADD_0,
      DECIDE ``!x. 0 < x ==> (SUC (x - 1) = x)``,
      DECIDE ``!w. 0 < w ==> (w <= 1 = (w = 1))``] o
   INST [`w` |-> `LENGTH (REGISTER_LIST ((15 >< 0) ireg))`] o
   SPEC_ALL o SPECL [`w - 1`,`w`]) NEXT_CORE_LDM_TN_X);

(* ------------------------------------------------------------------------- *)

val NEXT_CORE_STM_TN1 = (GEN_ALL o SIMP_RULE (stdi_ss++ARITH_ss) [COND_PAIR] o
   GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites [MULT_ADD_FOUR] o
   STM_ITER_CONV)
   ``NEXT_ARM6 (ARM6
       (DP reg psr (base + n2w (SUC x) * 4w) din alua alub dout)
       (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
          T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
          aregn2 T T T sctrlreg psrfb oareg
          (MASKN (SUC (SUC x)) ((15 >< 0) ireg))
          (RP stm ((15 >< 0) ireg) (MASKN (SUC x) ((15 >< 0) ireg)))
          (RP stm ((15 >< 0) ireg) (MASKN x ((15 >< 0) ireg)))
          mul mul2 borrow2 mshift)) (NRESET,ABORT,NFQ,NIQ,DATA,CPA,CPB)``;

val NEXT_CORE_STM_TN_X = store_thm("NEXT_CORE_STM_TN_X",
   `!x w y reg ireg alub alua dout i.
      (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
      1 < w ==>
      x <= w - 2 ==>
      (!t. t < SUC w ==> ~IS_RESET i t) ==>
      ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt'
       dataabt2' aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(aregn' IN {0w; 1w; 2w; 5w}) /\
        ((aregn' = 7w) ==> ~((CPSR_READ psr) %% 6)) /\
        ((aregn' = 6w) ==> ~((CPSR_READ psr) %% 7)) /\
       (FUNPOW (SNEXT NEXT_ARM6) x <|state :=
          ARM6 (DP reg psr (base + 1w * 4w) din alua alub dout)
           (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
              T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
              aregn2 T T T sctrlreg psrfb oareg (MASKN 2 ((15 >< 0) ireg))
              (RP stm ((15 >< 0) (ireg)) (MASKN 1 ((15 >< 0) ireg)))
              (RP stm ((15 >< 0) (ireg)) Tw) mul mul2 borrow2 mshift);
          inp := ADVANCE 2 i|> =
       (let nbs = if ireg %% 22 then usr else
                    DECODE_MODE ((4 >< 0) (CPSR_READ psr)) in
        <|state := ARM6 (DP reg psr (base + n2w (SUC x) * 4w)
            (if x = 0 then din else ireg) alua alub
            (if x = 0 then dout else
               REG_READ6 reg nbs
                 (RP stm ((15 >< 0) ireg) (MASKN x ((15 >< 0) ireg)))))
          (CTRL pipea T pipeb T ireg T ointstart' F F obaselatch' F stm tn
            T F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' pipebabt'
            dataabt2' (if x = 0 then aregn2 else
              if ointstart' then aregn' else 2w) T T T sctrlreg
           (if x = 0 then psrfb else SPSR_READ psr nbs)
           (if x = 0 then oareg else oareg')
           (MASKN (SUC (SUC x)) ((15 >< 0) ireg))
           (RP stm ((15 >< 0) ireg) (MASKN (SUC x) ((15 >< 0) ireg)))
           (RP stm ((15 >< 0) ireg) (MASKN x ((15 >< 0) ireg)))
           mul' mul2' borrow2' mshift'); inp := ADVANCE x (ADVANCE 2 i)|>))`,
  Induct
    >> (RW_TAC arith_ss [FUNPOW,MASKN_ZERO,GSYM ADVANCE_COMP] \\
          METIS_TAC [interrupt_exists])
    \\ REPEAT STRIP_TAC
    \\ `x <= w - 2` by DECIDE_TAC
    \\ PAT_ASSUM `!w y reg ireg alub alua dout i. X` IMP_RES_TAC
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    \\ FULL_SIMP_TAC std_ss [FUNPOW_SUC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ `SUC (SUC x) < LENGTH (REGISTER_LIST ((15 >< 0) ireg))` by DECIDE_TAC
    \\ `~((15 >< 0) ireg = 0w:word16)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    \\ ABBREV_TAC `nbs = if ireg %% 22 then usr else
                   DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ `~IS_RESET i (x + 2)` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [SNEXT,NEXT_CORE_STM_TN1,
         GSYM ADVANCE_COMP,ADVANCE_def,IN_LDM_STM,PENCZ_THM,
         DECIDE ``!x. x + 3 = SUC x + 2``]
    \\ RW_TAC (arith_ss++SIZES_ss) [MASK_def,MASKN_SUC,ADVANCE_def,AREGN1_def,
         pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,n2w_11]
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss) [ADD1,n2w_11]
    \\ EXISTS_TAC `3w` \\ SIMP_TAC (arith_ss++SIZES_ss) [n2w_11]);

val NEXT_CORE_STM_TN_W2 =
  (GEN_ALL o SIMP_RULE arith_ss [] o
   INST [`w` |-> `LENGTH (REGISTER_LIST ((15 >< 0) ireg))`] o
   SPEC_ALL o SPECL [`w - 2`,`w`]) NEXT_CORE_STM_TN_X;

val SUC_SUC_SUB2 =
  DECIDE ``!x. 1 < x ==> (1 + (x - 2) + 2 = x + 1) /\ (2 + (x - 2 + 0) = x)``;

val SUC_SUC_SUB2b = DECIDE ``!x. 1 < x ==> (SUC (SUC (x - 2)) = x)``;

val NEXT_CORE_STM_TN_W1 = prove(
   `!w y reg ireg alub alua.
      (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
      1 < w ==>
      (!t. t < SUC w ==> ~IS_RESET i t) ==>
      ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt'
       dataabt2' aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(aregn' IN {0w; 1w; 2w; 5w}) /\
        ((aregn' = 7w) ==> ~((CPSR_READ psr) %% 6)) /\
        ((aregn' = 6w) ==> ~((CPSR_READ psr) %% 7)) /\
       (FUNPOW (SNEXT NEXT_ARM6) (w - 1) <|state := ARM6
          (DP reg psr (base + 1w * 4w) din alua alub dout)
          (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
            T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
            aregn2 T T T sctrlreg psrfb oareg (MASKN 2 ((15 >< 0) ireg))
            (RP stm ((15 >< 0) (ireg)) (MASKN 1 ((15 >< 0) ireg)))
            (RP stm ((15 >< 0) (ireg)) Tw) mul mul2 borrow2 mshift);
         inp := ADVANCE 2 i|> =
       (let nbs = if ireg %% 22 then usr else
                    DECODE_MODE ((4 >< 0) (CPSR_READ psr)) in
        <|state := ARM6 (DP reg psr (REG_READ6 reg usr 15w) pipeb alua alub
            (REG_READ6 reg nbs
               (RP stm ((15 >< 0) ireg) (MASKN (w - 1) ((15 >< 0) ireg)))))
          (CTRL pipea T pipea T pipeb T ointstart' T T obaselatch' T
            (if ointstart' then swi_ex else DECODE_INST pipeb) t3
            F F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipeaabt' pipebabt'
            dataabt2' (if ointstart' then aregn' else 2w) T T F sctrlreg
            (SPSR_READ psr nbs) oareg'
            (MASK (if ointstart' then swi_ex else DECODE_INST pipeb) t3 ARB ARB)
            (RP stm ((15 >< 0) ireg) (MASKN w ((15 >< 0) ireg)))
            (RP stm ((15 >< 0) ireg) (MASKN (w - 1) ((15 >< 0) ireg)))
            mul' mul2' borrow2' mshift'); inp := ADVANCE (w + 1) i|>))`,
  REPEAT STRIP_TAC
    \\ `~((15 >< 0) ireg = 0w:word16)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    \\ PAT_ASSUM `w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))` SUBST_ALL_TAC
    \\ IMP_RES_TAC NEXT_CORE_STM_TN_W2
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    \\ ASM_SIMP_TAC std_ss [FUNPOW_SUC,
         DECIDE ``!x. 1 < x ==> (x - 1 = SUC (x - 2))``]
    \\ POP_ASSUM (K ALL_TAC)
    \\ `~IS_RESET i (LENGTH (REGISTER_LIST ((15 >< 0) ireg)))`
    by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [SNEXT,NEXT_CORE_STM_TN1,
         SUC_SUC_SUB2,GSYM ADVANCE_COMP,ADVANCE_def]
    \\ ASM_SIMP_TAC stdi_ss [MASK_def,PENCZ_THM,SUC_SUC_SUB2b]
    \\ ABBREV_TAC `nbs = if ireg %% 22 then usr else
                   DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ POP_ASSUM (K ALL_TAC)
    \\ RW_TAC (arith_ss++SIZES_ss) [MASK_def,PENCZ_THM,ADVANCE_def,AREGN1_def,
         pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,n2w_11]
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss) [ADD1,n2w_11]
    \\ EXISTS_TAC `3w` \\ SIMP_TAC (arith_ss++SIZES_ss) [n2w_11]);

val NEXT_CORE_STM_TN_W1 = save_thm("NEXT_CORE_STM_TN_W1",
  (GEN_ALL o SIMP_RULE bool_ss [] o
   DISCH `Abbrev (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) /\
          Abbrev (nbs = DECODE_MODE ((4 >< 0) cpsr)) /\
          Abbrev (cpsr = CPSR_READ psr)` o SPEC_ALL o
   SIMP_RULE std_ss [WORD_ADD_0,WORD_MULT_CLAUSES]) NEXT_CORE_STM_TN_W1);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
