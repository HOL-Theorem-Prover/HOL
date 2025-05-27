(* ========================================================================= *)
(* FILE          : arm_evalScript.sml                                        *)
(* DESCRIPTION   : Various theorems about the ISA and instruction encoding   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2007                                                 *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "rich_listTheory", "wordsLib", "armLib",
            "updateTheory", "instructionTheory", "systemTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q rich_listTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open combinTheory updateTheory armTheory systemTheory instructionTheory;

val _ = new_theory "arm_eval";
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val fcp_ss   = armLib.fcp_ss;
val SIZES_ss = wordsLib.SIZES_ss;

val _ = wordsLib.guess_lengths();

(* ------------------------------------------------------------------------- *)

val REG_READ6_def = Define`
  REG_READ6 reg mode n =
    if n = 15w then
      FETCH_PC reg
    else
      REG_READ reg mode n`;

val REG_WRITEL_def = Define`
  (REG_WRITEL r m [] = r) /\
  (REG_WRITEL r m ((n,d)::l) = REG_WRITE (REG_WRITEL r m l) m n d)`;

(* ------------------------------------------------------------------------- *)

val STATE_ARM_MMU_NEXT = store_thm("STATE_ARM_MMU_NEXT",
  `!t a b c. (STATE_ARM_MMU ops t a = b) /\ (NEXT_ARM_MMU ops b = c) ==>
             (STATE_ARM_MMU ops (t + 1) a = c)`,
  RW_TAC bool_ss [STATE_ARM_MMU_def,GSYM arithmeticTheory.ADD1]);

(* ------------------------------------------------------------------------- *)

val register2num_lt_neq = store_thm("register2num_lt_neq",
  `!x y. register2num x < register2num y ==> ~(x = y)`,
  METIS_TAC [prim_recTheory.LESS_NOT_EQ, register2num_11]);

val psr2num_lt_neq = store_thm("psr2num_lt_neq",
  `!x y. psr2num x < psr2num y ==> ~(x = y)`,
  METIS_TAC [prim_recTheory.LESS_NOT_EQ, psr2num_11]);

val REGISTER_RANGES =
  (SIMP_RULE (std_ss++SIZES_ss) [] o Thm.INST_TYPE [alpha |-> ``:4``]) w2n_lt;

val mode_reg2num_15 = (GEN_ALL o
  SIMP_RULE (arith_ss++SIZES_ss) [w2n_n2w] o
  SPECL [`m`,`15w`]) mode_reg2num_def;

val mode_reg2num_lt = store_thm("mode_reg2num_lt",
  `!w m w. mode_reg2num m w < 31`,
  ASSUME_TAC REGISTER_RANGES
    \\ RW_TAC std_ss [mode_reg2num_def,USER_def,DECIDE ``n < 16 ==> n < 31``]
    \\ Cases_on `m`
    \\ FULL_SIMP_TAC arith_ss [mode_distinct,mode_case_def,
         DECIDE ``a < 16 /\ b < 16 ==> (a + b < 31)``,
         DECIDE ``a < 16 /\ ~(a = 15) ==> (a + 16 < 31)``]);

val not_reg_eq_lem = prove(`!v w. ~(v = w) ==> ~(w2n v = w2n w)`,
  REPEAT Cases \\ SIMP_TAC std_ss [w2n_n2w,n2w_11]);

val not_reg_eq = store_thm("not_reg_eq",
  `!v w m1 m2. ~(v = w) ==> ~(mode_reg2num m1 v = mode_reg2num m2 w)`,
  NTAC 4 STRIP_TAC
    \\ `w2n v < 16 /\ w2n w < 16` by REWRITE_TAC [REGISTER_RANGES]
    \\ Cases_on `m1` \\ Cases_on `m2`
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [USER_def,mode_reg2num_def,not_reg_eq_lem]
    \\ COND_CASES_TAC \\ ASM_SIMP_TAC arith_ss [not_reg_eq_lem]
    \\ COND_CASES_TAC \\ ASM_SIMP_TAC arith_ss [not_reg_eq_lem]);

val not_pc = (GEN_ALL o REWRITE_RULE [mode_reg2num_15] o
  SPECL [`v`,`15w`]) not_reg_eq;

val r15 = SYM (List.nth (CONJUNCTS num2register_thm, 15))
val READ_TO_READ6 = store_thm("READ_TO_READ6",
  `!r m n d. (REG_READ (REG_WRITE r usr 15w (d - 8w)) m n =
              REG_READ6 (REG_WRITE r usr 15w d) m n)`,
  RW_TAC (std_ss++SIZES_ss) [REG_READ_def,REG_READ6_def,FETCH_PC_def,
         REG_WRITE_def,UPDATE_def,WORD_SUB_ADD,mode_reg2num_15]
  \\ PROVE_TAC [r15,num2register_11,mode_reg2num_lt,not_pc,DECIDE ``15 < 31``]);

val TO_WRITE_READ6 = store_thm("TO_WRITE_READ6",
  `(!r. FETCH_PC r = REG_READ6 r usr 15w) /\
   (!r. INC_PC r = REG_WRITE r usr 15w (REG_READ6 r usr 15w + 4w)) /\
   (!r m d. REG_WRITE r m 15w d = REG_WRITE r usr 15w d) /\
   (!r m. REG_READ6 r m 15w = REG_READ6 r usr 15w)`,
  RW_TAC std_ss [INC_PC_def,REG_READ6_def,REG_WRITE_def,REG_READ_def,
    FETCH_PC_def,mode_reg2num_15]);

val REG_WRITE_WRITE = store_thm("REG_WRITE_WRITE",
  `!r m n d1 d2. REG_WRITE (REG_WRITE r m n d1) m n d2 = REG_WRITE r m n d2`,
  RW_TAC bool_ss [REG_WRITE_def,UPDATE_EQ]);

val REG_WRITE_WRITE_COMM = store_thm("REG_WRITE_WRITE_COMM",
  `!r m n1 n2 d1 d2.
     ~(n1 = n2) ==>
      (REG_WRITE (REG_WRITE r m n1 d1) m n2 d2 =
       REG_WRITE (REG_WRITE r m n2 d2) m n1 d1)`,
  RW_TAC std_ss [REG_WRITE_def,UPDATE_COMMUTES,not_reg_eq,
    mode_reg2num_lt,num2register_11]);

val REG_WRITE_WRITE_PC = store_thm("REG_WRITE_WRITE_PC",
  `!r m1 m2 n d p.
     REG_WRITE (REG_WRITE r m1 15w p) m2 n d =
       if n = 15w then
         REG_WRITE r usr 15w d
       else
         REG_WRITE (REG_WRITE r m2 n d) usr 15w p`,
  RW_TAC std_ss [TO_WRITE_READ6,REG_WRITE_WRITE]
    \\ ASM_SIMP_TAC std_ss [REG_WRITE_def,UPDATE_COMMUTES,not_pc,
         mode_reg2num_15,mode_reg2num_lt,num2register_11]);

val REG_READ_WRITE_THM = prove(
  `(!r m n1 n2 d. REG_READ6 (REG_WRITE r m n1 d) m n2 =
      if n1 = n2 then d else REG_READ6 r m n2) /\
    !r m n d. (REG_WRITE r m n (REG_READ6 r m n) = r)`,
  RW_TAC std_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,
    UPDATE_APPLY_IMP_ID,mode_reg2num_15] \\ SIMP_TAC std_ss [UPDATE_def]
    \\ PROVE_TAC [r15,not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
         DECIDE ``15 < 31``]);

val REG_READ_WRITE_PC_THM =
  let val thm = (SPEC_ALL o CONJUNCT1) REG_READ_WRITE_THM in
    CONJ
      ((SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n2` |-> `15w`]) thm)
      ((SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n1` |-> `15w`]) thm)
  end;

val REG_READ_WRITE_NEQ = store_thm("REG_READ_WRITE_NEQ",
  `!r m1 m2 n1 n2 d. ~(n1 = n2) ==>
      (REG_READ6 (REG_WRITE r m1 n1 d) m2 n2 = REG_READ6 r m2 n2)`,
  RW_TAC std_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,
    UPDATE_APPLY_IMP_ID,mode_reg2num_15] \\ SIMP_TAC std_ss [UPDATE_def]
    \\ PROVE_TAC [r15,not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
         DECIDE ``15 < 31``]);

val REG_READ_READ6 = store_thm("REG_READ_READ6",
  `!r m n. ~(n = 15w) ==> (REG_READ6 r m n = REG_READ r m n)`,
  SIMP_TAC bool_ss [REG_READ6_def]);

val REG_READ_WRITE_PC =
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o INST [`n2` |-> `n`] o
   DISCH `~(n2 = 15w)` o CONJUNCT2) REG_READ_WRITE_PC_THM;

val REG_READ_INC_PC = store_thm("REG_READ_INC_PC",
  `!r m n. ~(n = 15w) ==> (REG_READ (INC_PC r) m n = REG_READ r m n)`,
  SIMP_TAC bool_ss [TO_WRITE_READ6,REG_READ_WRITE_PC]);

val REG_WRITE_INC_PC = store_thm("REG_WRITE_INC_PC",
  `!r m n. ~(n = 15w) ==>
      (REG_WRITE (INC_PC r) m n d = INC_PC (REG_WRITE r m n d))`,
  SIMP_TAC bool_ss [TO_WRITE_READ6,REG_READ_WRITE_NEQ,REG_WRITE_WRITE_PC]);

val REG_READ_WRITE = save_thm("REG_READ_WRITE",
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o
   DISCH `~(n = 15w)` o SPEC_ALL o CONJUNCT2) REG_READ_WRITE_THM);

val REG_WRITE_READ =
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o
   DISCH `~(n2 = 15w)` o SPEC_ALL o CONJUNCT1) REG_READ_WRITE_THM;

val INC_PC = save_thm("INC_PC",
  (SIMP_RULE std_ss [REG_READ6_def,FETCH_PC_def] o
   hd o tl o CONJUNCTS) TO_WRITE_READ6);

val REG_WRITEL = store_thm("REG_WRITEL",
  `!r m l. REG_WRITEL r m l = FOLDR (\h r. REG_WRITE r m (FST h) (SND h)) r l`,
  Induct_on `l` \\ TRY (Cases_on `h`) \\ ASM_SIMP_TAC list_ss [REG_WRITEL_def]);

val REG_WRITE_WRITEL = store_thm("REG_WRITE_WRITEL",
  `!r m n d. REG_WRITE r m n d = REG_WRITEL r m [(n,d)]`,
  SIMP_TAC std_ss [REG_WRITEL_def]);

val REG_WRITEL_WRITEL = store_thm("REG_WRITEL_WRITEL",
  `!r m l1 l2. REG_WRITEL (REG_WRITEL r m l1) m l2 = REG_WRITEL r m (l2 ++ l1)`,
  SIMP_TAC std_ss [REG_WRITEL,rich_listTheory.FOLDR_APPEND]);

val REG_WRITE_WRITE_THM = store_thm("REG_WRITE_WRITE_THM",
  `!m n r m e d. x <=+ y ==>
      (REG_WRITE (REG_WRITE r m x e) m y d =
         if x = y then
           REG_WRITE r m y d
         else
           REG_WRITE (REG_WRITE r m y d) m x e)`,
  RW_TAC std_ss [WORD_LOWER_OR_EQ,WORD_LO,REG_WRITE_WRITE]
    \\ METIS_TAC [REG_WRITE_def,not_reg_eq,UPDATE_COMMUTES,
         mode_reg2num_lt,num2register_11]);

val REG_READ_WRITEL = store_thm("REG_READ_WRITEL",
  `(!r m n. REG_READ (REG_WRITEL r m []) m n = REG_READ r m n) /\
   (!r m n a b l. ~(n = 15w) ==>
      (REG_READ (REG_WRITEL r m ((a,b)::l)) m n =
       if a = n then b else REG_READ (REG_WRITEL r m l) m n))`,
  RW_TAC std_ss [REG_WRITEL_def,REG_WRITE_READ]);

val mode_reg2num_15 = (GEN_ALL o SIMP_RULE (arith_ss++SIZES_ss) [w2n_n2w] o
  SPECL [`m`,`15w`]) mode_reg2num_def;

val lem = (SIMP_RULE std_ss[REG_READ_WRITE_PC_THM,
  TO_WRITE_READ6,WORD_ADD_SUB] o SPECL [`r`,`m`,`15w`,`d + 8w`]) READ_TO_READ6;

val lem2 = prove(
  `!r m m2 n d. ~(n = 15w) ==>
     (REG_READ (REG_WRITE r m n d) m2 15w = REG_READ r m2 15w)`,
  RW_TAC std_ss [REG_READ_def,REG_WRITE_def,UPDATE_def,
         mode_reg2num_lt,num2register_11]
    \\ PROVE_TAC [r15,mode_reg2num_lt,armTheory.num2register_11,
                  mode_reg2num_15,not_reg_eq]);

val REG_READ_WRITEL_PC = store_thm("REG_READ_WRITEL_PC",
  `!r m m2 a b l. REG_READ (REG_WRITEL r m ((a,b)::l)) m2 15w =
       if a = 15w then b + 8w else REG_READ (REG_WRITEL r m l) m2 15w`,
  RW_TAC std_ss [REG_WRITEL_def,TO_WRITE_READ6,lem,lem2]);

val REG_READ_WRITEL_PC2 = store_thm("REG_READ_WRITEL_PC2",
  `!r m a b l. (REG_WRITEL r m ((a,b)::l)) r15 =
       if a = 15w then b else (REG_WRITEL r m l) r15`,
  RW_TAC std_ss [REG_WRITEL_def,REG_WRITE_def,UPDATE_def,
         mode_reg2num_lt,num2register_11]
    \\ PROVE_TAC [r15,mode_reg2num_lt,armTheory.num2register_11,
                  mode_reg2num_15,not_reg_eq]);

(* ------------------------------------------------------------------------- *)

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

fun Cases_on_nzcv tm =
  FULL_STRUCT_CASES_TAC (SPEC tm (armLib.tupleCases
  ``(n,z,c,v):bool#bool#bool#bool``));

val SET_NZCV_IDEM = store_thm("SET_NZCV_IDEM",
  `!a b c. SET_NZCV a (SET_NZCV b c) = SET_NZCV a c`,
  REPEAT STRIP_TAC \\ Cases_on_nzcv `a` \\ Cases_on_nzcv `b`
    \\ RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,word_modify_def]);

val DECODE_NZCV_SET_NZCV = store_thm("DECODE_NZCV_SET_NZCV",
   `(!a b c d n. (SET_NZCV (a,b,c,d) n) ' 31 = a) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) ' 30 = b) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) ' 29 = c) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) ' 28 = d)`,
  RW_TAC (fcp_ss++SIZES_ss) [SET_NZCV_def,word_modify_def]);

val DECODE_IFMODE_SET_NZCV = store_thm("DECODE_IFMODE_SET_NZCV",
   `(!a n. (27 -- 8) (SET_NZCV a n) = (27 -- 8) n) /\
    (!a n. (SET_NZCV a n) ' 7 = n ' 7) /\
    (!a n. (SET_NZCV a n) ' 6 = n ' 6) /\
    (!a n. (SET_NZCV a n) ' 5 = n ' 5) /\
    (!a n. (4 >< 0) (SET_NZCV a n) = (4 >< 0) n)`,
  RW_TAC bool_ss [] \\ Cases_on_nzcv `a`
    \\ SIMP_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,word_modify_def,word_extract_def,word_bits_def]);

val DECODE_IFMODE_SET_IFMODE = store_thm("DECODE_IFMODE_SET_IFMODE",
   `(!i f m n. (SET_IFMODE i f m n) ' 7 = i) /\
    (!i f m n. (SET_IFMODE i f m n) ' 6 = f) /\
    (!i f m n. (4 >< 0) (SET_IFMODE i f m n) = mode_num m)`,
   RW_TAC (fcp_ss++ARITH_ss++SIZES_ss) [SET_IFMODE_def,word_modify_def,
     word_extract_def,word_bits_def,w2w]);

val SET_IFMODE_IDEM = store_thm("SET_IFMODE_IDEM",
  `!a b c d e f g. SET_IFMODE a b c (SET_IFMODE d e f g) = SET_IFMODE a b c g`,
  SIMP_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
    [SET_IFMODE_def,word_modify_def]);

val SET_IFMODE_NZCV_SWP = store_thm("SET_IFMODE_NZCV_SWP",
  `!a b c d e. SET_IFMODE a b c (SET_NZCV d e) =
               SET_NZCV d (SET_IFMODE a b c e)`,
  REPEAT STRIP_TAC \\ Cases_on_nzcv `d`
    \\ RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,SET_IFMODE_def,word_modify_def]
    \\ Cases_on `i < 5` \\ ASM_SIMP_TAC arith_ss []
    \\ Cases_on `i < 28` \\ ASM_SIMP_TAC arith_ss []);

val DECODE_NZCV_SET_IFMODE = store_thm("DECODE_NZCV_SET_IFMODE",
  `(!i f m n. (SET_IFMODE i f m n) ' 31 = n ' 31) /\
   (!i f m n. (SET_IFMODE i f m n) ' 30 = n ' 30) /\
   (!i f m n. (SET_IFMODE i f m n) ' 29 = n ' 29) /\
   (!i f m n. (SET_IFMODE i f m n) ' 28 = n ' 28) /\
   (!i f m n. (27 -- 8) (SET_IFMODE i f m n) = (27 -- 8) n) /\
   (!i f m n. (SET_IFMODE i f m n) ' 5 = n ' 5)`,
  RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
    [SET_IFMODE_def,word_modify_def,word_bits_def]);

val SET_NZCV_ID = store_thm("SET_NZCV_ID",
  `!a. SET_NZCV (a ' 31,a ' 30,a ' 29,a ' 28) a = a`,
  SRW_TAC [fcpLib.FCP_ss,SIZES_ss] [SET_NZCV_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM]);

(* ------------------------------------------------------------------------- *)

val SPSR_READ_THM = store_thm("SPSR_READ_THM",
  `!psr mode cpsr.
     (CPSR_READ psr = cpsr) ==>
     ((if USER mode then cpsr else SPSR_READ psr mode) = SPSR_READ psr mode)`,
  RW_TAC bool_ss [CPSR_READ_def,SPSR_READ_def,mode2psr_def,USER_def]
    \\ REWRITE_TAC [mode_case_def]);

val SPSR_READ_THM2 = store_thm("SPSR_READ_THM2",
  `!psr mode cpsr.  USER mode ==> (SPSR_READ psr mode = CPSR_READ psr)`,
  METIS_TAC [SPSR_READ_THM]);

val CPSR_WRITE_READ = store_thm("CPSR_WRITE_READ",
  `(!psr m x. CPSR_READ (SPSR_WRITE psr m x) = CPSR_READ psr) /\
   (!psr x. CPSR_READ (CPSR_WRITE psr x) = x)`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,UPDATE_def,
         USER_def,mode2psr_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC bool_ss [mode_case_def,psr_distinct]);

val CPSR_READ_WRITE = store_thm("CPSR_READ_WRITE",
  `(!psr. CPSR_WRITE psr (CPSR_READ psr) = psr) /\
   (!psr mode. USER mode ==> (CPSR_WRITE psr (SPSR_READ psr mode) = psr))`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,
         UPDATE_APPLY_IMP_ID,USER_def,mode2psr_def]
    \\ REWRITE_TAC [mode_case_def,APPLY_UPDATE_ID]);

val CPSR_WRITE_WRITE = store_thm("CPSR_WRITE_WRITE",
  `!psr a b. CPSR_WRITE (CPSR_WRITE psr a) b = CPSR_WRITE psr b`,
  SIMP_TAC bool_ss [CPSR_WRITE_def,UPDATE_EQ]);

val USER_usr = save_thm("USER_usr",
  simpLib.SIMP_PROVE bool_ss [USER_def] ``USER usr``);

val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y =
               CPSR_WRITE (SPSR_WRITE psr m y) x`,
  RW_TAC bool_ss [SPSR_WRITE_def,CPSR_WRITE_def,USER_def,mode2psr_def]
    \\ Cases_on `m`
    \\ FULL_SIMP_TAC bool_ss [mode_distinct,mode_case_def,psr_distinct,
         UPDATE_COMMUTES]);

val SPSR_READ_WRITE = store_thm("SPSR_READ_WRITE",
  `!psr m. SPSR_WRITE psr m (SPSR_READ psr m) = psr`,
  RW_TAC std_ss [SPSR_READ_def,SPSR_WRITE_def,mode2psr_def]
    \\ Cases_on `m` \\ SIMP_TAC (srw_ss()) [UPDATE_APPLY_IMP_ID]);

val SPSR_WRITE_THM = store_thm("SPSR_WRITE_THM",
  `!psr m x. USER m ==> (SPSR_WRITE psr m x = psr)`,
  SIMP_TAC std_ss [SPSR_WRITE_def]);

val SPSR_WRITE_WRITE = store_thm("SPSR_WRITE_WRITE",
  `!psr m x y. SPSR_WRITE (SPSR_WRITE psr m x) m y = SPSR_WRITE psr m y`,
  RW_TAC std_ss [SPSR_WRITE_def,UPDATE_EQ]);

val SPSR_WRITE_READ = store_thm("SPSR_WRITE_READ",
  `!psr m x. ~USER m ==> (SPSR_READ (SPSR_WRITE psr m x) m = x) /\
                         (SPSR_READ (CPSR_WRITE psr x) m = SPSR_READ psr m)`,
  RW_TAC std_ss [SPSR_WRITE_def,CPSR_WRITE_def,SPSR_READ_def,UPDATE_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC (srw_ss()) [USER_def,mode2psr_def]);

(* ------------------------------------------------------------------------- *)

val word_ss = armLib.fcp_ss ++ wordsLib.SIZES_ss ++ ARITH_ss;

val lem = prove(
  `!w:word32 i. i < 5 ==> (((4 >< 0) w) ' i = w ' i)`,
  RW_TAC word_ss [word_extract_def,word_bits_def,w2w]);

val w2n_mod = prove(
  `!a:'a word b. (a = n2w b) = (w2n a = b MOD dimword (:'a))`,
  Cases \\ REWRITE_TAC [n2w_11,w2n_n2w]);

val PSR_CONS = store_thm("PSR_CONS",
   `!w:word32. w =
       let m = DECODE_MODE ((4 >< 0) w) in
         if m = safe then
           SET_NZCV (w ' 31, w ' 30, w ' 29, w ' 28) ((27 -- 0) w)
         else
           SET_NZCV (w ' 31, w ' 30, w ' 29, w ' 28)
             (SET_IFMODE (w ' 7) (w ' 6) m (0xFFFFF20w && w))`,
  RW_TAC word_ss [SET_IFMODE_def,SET_NZCV_def,word_modify_def,n2w_def]
    \\ RW_TAC word_ss [word_bits_def]
    THENL [
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/ (i < 28)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC arith_ss [],
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/
       (7 < i /\ i < 28) \/ (i = 7) \/ (i = 6) \/ (i = 5) \/ (i < 5)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC (word_ss++ARITH_ss) [word_and_def]
        THENL [
          FULL_SIMP_TAC std_ss [LESS_THM]
            \\ FULL_SIMP_TAC arith_ss [] \\ EVAL_TAC,
          EVAL_TAC,
          `~(mode_num m = 0w)`
            by (Cases_on `m` \\ RW_TAC std_ss [mode_num_def] \\ EVAL_TAC)
            \\ POP_ASSUM MP_TAC \\ UNABBREV_TAC `m`
            \\ `w ' i = (((4 >< 0) w):word5) ' i` by METIS_TAC [lem]
            \\ ASM_REWRITE_TAC [] \\ ABBREV_TAC `x = ((4 >< 0) w):word5`
            \\ Cases_on `(x = 16w) \/ (x = 17w) \/ (x = 18w) \/ (x = 19w) \/
                         (x = 23w) \/ (x = 27w) \/ (x = 31w)`
            \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC
                 [fcpLib.FCP_ss,wordsLib.SIZES_ss,ARITH_ss,boolSimps.LET_ss]
                 [DECODE_MODE_def,mode_num_def]
            \\ POP_ASSUM MP_TAC
            \\ FULL_SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [w2n_mod]]]);

val word_modify_PSR = save_thm("word_modify_PSR",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``word_modify f (SET_NZCV (n,z,c,v) x)``);

val word_modify_PSR2 = save_thm("word_modify_PSR2",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``word_modify f (SET_NZCV (n,z,c,v) (SET_IFMODE imask fmask m x))``);

val CPSR_WRITE_n2w = save_thm("CPSR_WRITE_n2w", GEN_ALL
  ((PURE_ONCE_REWRITE_CONV [PSR_CONS] THENC PURE_REWRITE_CONV [CPSR_WRITE_def])
   ``CPSR_WRITE psr (n2w n)``));

val SPSR_WRITE_n2w = save_thm("SPSR_WRITE_n2w", GEN_ALL
  ((PURE_ONCE_REWRITE_CONV [PSR_CONS] THENC PURE_REWRITE_CONV [SPSR_WRITE_def])
   ``SPSR_WRITE psr mode (n2w n)``));

(* ------------------------------------------------------------------------- *)

val decode_opcode_def = Define`
  decode_opcode i =
    case i of
      AND cond s Rd Rn Op2 => 0w:word4
    | EOR cond s Rd Rn Op2 => 1w
    | SUB cond s Rd Rn Op2 => 2w
    | RSB cond s Rd Rn Op2 => 3w
    | ADD cond s Rd Rn Op2 => 4w
    | ADC cond s Rd Rn Op2 => 5w
    | SBC cond s Rd Rn Op2 => 6w
    | RSC cond s Rd Rn Op2 => 7w
    | TST cond Rn Op2      => 8w
    | TEQ cond Rn Op2      => 9w
    | CMP cond Rn Op2      => 10w
    | CMN cond Rn Op2      => 11w
    | ORR cond s Rd Rn Op2 => 12w
    | MOV cond s Rd Op2    => 13w
    | BIC cond s Rd Rn Op2 => 14w
    | MVN cond s Rd Op2    => 15w
    | _ => ARB`;

val DECODE_PSRD_def = Define`
  (DECODE_PSRD CPSR_c = (F,F,T)) /\ (DECODE_PSRD CPSR_f = (F,T,F)) /\
  (DECODE_PSRD CPSR_a = (F,T,T)) /\ (DECODE_PSRD SPSR_c = (T,F,T)) /\
  (DECODE_PSRD SPSR_f = (T,T,F)) /\ (DECODE_PSRD SPSR_a = (T,T,T))`;

val IS_DP_IMMEDIATE_def = Define`
  (IS_DP_IMMEDIATE (Dp_immediate rot i) = T) /\
  (IS_DP_IMMEDIATE (Dp_shift_immediate sh imm) = F) /\
  (IS_DP_IMMEDIATE (Dp_shift_register sh reg) = F)`;

val IS_DTH_IMMEDIATE_def = Define`
  (IS_DTH_IMMEDIATE (Dth_immediate i) = T) /\
  (IS_DTH_IMMEDIATE (Dth_register r) = F)`;

val IS_DT_SHIFT_IMMEDIATE_def = Define`
  (IS_DT_SHIFT_IMMEDIATE (Dt_immediate i) = F) /\
  (IS_DT_SHIFT_IMMEDIATE (Dt_shift_immediate sh imm) = T)`;

val IS_MSR_IMMEDIATE_def = Define`
  (IS_MSR_IMMEDIATE (Msr_immediate rot i) = T) /\
  (IS_MSR_IMMEDIATE (Msr_register r) = F)`;

fun Cases_on_nzcv tm = FULL_STRUCT_CASES_TAC (SPEC tm (armLib.tupleCases
  ``(n,z,c,v):bool#bool#bool#bool``));

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (:'a) ==> (((n2w n):bool ** 'a) ' i = BIT i n)``;

val fcp_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss;

val condition_encode_lem = prove(
  `!cond i. i < 28 ==> ~(condition_encode cond ' i)`,
  SIMP_TAC (arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss)
    [condition_encode_def,word_index,w2w,word_lsl_def]);

fun b_of_b t = (GEN_ALL o SIMP_RULE std_ss [BITS_THM] o
  SPECL [`6`,`0`,`x`,t]) BIT_OF_BITS_THM2;

val shift_encode_lem = prove(
  `!r. (!i. 6 < i /\ i < 32 ==> ~(shift_encode r ' i)) /\
       ~(shift_encode r ' 4)`,
  Cases \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss)
    [shift_encode_def,word_index,w2w,word_or_def,
     b_of_b `32`, b_of_b `64`, b_of_b `96`] \\ EVAL_TAC);

val extract_out_of_range = prove(
  `!w:'a word i h.
      (h + 1 - l < i) /\ i < dimindex(:'b) ==> ~((((h >< l) w):'b word) ' i)`,
  SRW_TAC [ARITH_ss,fcpLib.FCP_ss] [word_extract_def,word_bits_def,w2w]
    \\ Cases_on `i < dimindex (:'a)` \\ SRW_TAC [ARITH_ss,fcpLib.FCP_ss] []);

val INDEX_RAND =
 (GEN_ALL o SIMP_RULE bool_ss [] o ISPEC `\x:word32. x ' i`) COND_RAND;

val BIT_NUMERAL = CONJ (SPECL [`0`,`NUMERAL n`] BIT_def)
                       (SPECL [`NUMERAL b`,`NUMERAL n`] BIT_def);

val BITS_NUMERAL = (GEN_ALL o SPECL [`h`,`l`,`NUMERAL n`]) BITS_def;

val BITS_NUMERAL_ss = let open numeral_bitTheory numeralTheory in rewrites
  [BITS_NUMERAL, BITS_ZERO2, NUMERAL_DIV_2EXP, NUMERAL_iDIV2,
   NUMERAL_SFUNPOW_iDIV2, NUMERAL_SFUNPOW_iDUB, NUMERAL_SFUNPOW_FDUB,
   FDUB_iDIV2, FDUB_iDUB, FDUB_FDUB, iDUB_removal,
   numeral_suc, numeral_imod_2exp, MOD_2EXP, NORM_0]
end;

val word_frags = [fcpLib.FCP_ss,wordsLib.SIZES_ss,BITS_NUMERAL_ss,
  rewrites [SIMP_RULE std_ss [] DECODE_ARM_THM, INDEX_RAND,BIT_def,
    shift_encode_lem,word_or_def,word_index,w2w,word_lsl_def,
    condition_encode_lem,instruction_encode_def]];

(* ......................................................................... *)

val decode_enc_br = store_thm("decode_enc_br",
  `(!cond offset. DECODE_ARM (enc (instruction$B cond offset)) = br) /\
   (!cond offset. DECODE_ARM (enc (instruction$BL cond offset)) = br)`,
  SRW_TAC word_frags []);

val decode_enc_swi = store_thm("decode_enc_swi",
  `!cond. DECODE_ARM (enc (instruction$SWI cond)) = swi_ex`,
  SRW_TAC word_frags []);

val decode_enc_data_proc_ = prove(
  `!cond op s rd rn Op2. ~(op ' 3) \/ (op ' 2) ==>
      (DECODE_ARM (data_proc_encode cond op s rn rd Op2) = data_proc)`,
  Cases_on `Op2`
    \\ SRW_TAC word_frags [data_proc_encode_def,addr_mode1_encode_def]);

val decode_enc_data_proc__ = prove(
  `!cond op s rd rn Op2.
      (DECODE_ARM (data_proc_encode cond op T rd 0w Op2) = data_proc)`,
  Cases_on `Op2`
    \\ SRW_TAC word_frags [data_proc_encode_def,addr_mode1_encode_def]);

val decode_enc_data_proc = prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn Op2. DECODE_ARM (enc (f cond s rd rn Op2)) = data_proc)`,
  SRW_TAC [] [instruction_encode_def]
    \\ SRW_TAC [fcpLib.FCP_ss,wordsLib.SIZES_ss,BITS_NUMERAL_ss]
               [BIT_def,word_index,decode_enc_data_proc_]);

val decode_enc_data_proc2 = prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn Op2. DECODE_ARM (enc (f cond rn Op2)) = data_proc)`,
   SRW_TAC [] [instruction_encode_def] \\ SRW_TAC [] [decode_enc_data_proc__]);

val decode_enc_data_proc3 = prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd Op2. DECODE_ARM (enc (f cond s rd Op2)) = data_proc)`,
  SRW_TAC [] [instruction_encode_def]
    \\ SRW_TAC [fcpLib.FCP_ss,wordsLib.SIZES_ss,BITS_NUMERAL_ss]
               [BIT_def,word_index,decode_enc_data_proc_]);

val decode_enc_mla_mul = store_thm("decode_enc_mla_mul",
  `(!cond s rd rm rs.
      DECODE_ARM (enc (instruction$MUL cond s rd rm rs)) = mla_mul) /\
   (!cond s rd rm rs rn.
      DECODE_ARM (enc (instruction$MLA cond s rd rm rs rn)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_ARM (enc (instruction$UMULL cond s rdlo rdhi rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_ARM (enc (instruction$UMLAL cond s rdlo rdhi rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_ARM (enc (instruction$SMULL cond s rdlo rdhi rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_ARM (enc (instruction$SMLAL cond s rdlo rdhi rm rs)) = mla_mul)`,
  SRW_TAC word_frags []);

val decode_enc_ldr_str = store_thm("decode_enc_ldr_str",
  `(!cond b opt rd rn offset.
      DECODE_ARM (enc (instruction$LDR cond b opt rd rn offset)) = ldr_str) /\
   (!cond b opt rd rn offset.
      DECODE_ARM (enc (instruction$STR cond b opt rd rn offset)) = ldr_str)`,
  REPEAT STRIP_TAC \\ Cases_on `offset` \\ TRY (Cases_on `s`)
    \\ SRW_TAC word_frags [addr_mode2_encode_def,options_encode_def,
         shift_encode_def,word_modify_def]);

val decode_enc_ldrh_strh = store_thm("decode_enc_ldrh_strh",
  `(!cond s h opt rd rn offset.
      DECODE_ARM (enc (instruction$LDRH cond s h opt rd rn offset)) =
      ldrh_strh) /\
   (!cond opt rd rn offset.
      DECODE_ARM (enc (instruction$STRH cond opt rd rn offset)) = ldrh_strh)`,
  REPEAT STRIP_TAC \\ Cases_on `offset`
    \\ SRW_TAC word_frags [addr_mode3_encode_def,options_encode2_def,
         word_modify_def,extract_out_of_range]
    \\ METIS_TAC []);

val decode_enc_ldm_stm = store_thm("decode_enc_ldm_stm",
  `(!cond s opt rn list.
      DECODE_ARM (enc (instruction$LDM cond s opt rn list)) = ldm_stm) /\
   (!cond s opt rn list.
      DECODE_ARM (enc (instruction$STM cond s opt rn list)) = ldm_stm)`,
  SRW_TAC word_frags [options_encode_def,word_modify_def]);

val decode_enc_swp = store_thm("decode_enc_swp",
  `!cond b rd rm rn. DECODE_ARM (enc (instruction$SWP cond b rd rm rn)) = swp`,
  SRW_TAC word_frags []);

val decode_enc_mrs = store_thm("decode_enc_mrs",
  `!cond r rd. DECODE_ARM (enc (instruction$MRS cond r rd)) = mrs`,
  SRW_TAC word_frags []);

val decode_enc_msr = store_thm("decode_enc_msr",
  `!cond psrd op.  DECODE_ARM (enc (instruction$MSR cond psrd op)) = msr`,
  REPEAT STRIP_TAC \\ Cases_on `psrd` \\ Cases_on `op`
    \\ SRW_TAC word_frags [msr_psr_encode_def,msr_mode_encode_def]);

val decode_enc_coproc = store_thm("decode_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      DECODE_ARM (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
      cdp_und) /\
   (!cond. DECODE_ARM (enc (instruction$UND cond)) = cdp_und) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_ARM (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) =
      mrc) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_ARM (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) = mcr) /\
   (!cond n opt cpn crd rn offset.
      DECODE_ARM (enc (instruction$STC cond n opt cpn crd rn offset)) =
      ldc_stc) /\
   (!cond n opt cpn crd rn offset.
      DECODE_ARM (enc (instruction$LDC cond n opt cpn crd rn offset)) =
      ldc_stc)`,
  SRW_TAC word_frags [options_encode_def,word_modify_def]);

val decode_cp_enc_coproc = store_thm("decode_cp_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      DECODE_CP (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
      cdp_und) /\
   (!cond. DECODE_CP (enc (instruction$UND cond)) = cdp_und) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_CP (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) = mrc) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_CP (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) = mcr) /\
   (!cond n opt cpn crd rn offset.
      DECODE_CP (enc (instruction$STC cond n opt cpn crd rn offset)) =
      ldc_stc) /\
   (!cond n opt cpn crd rn offset.
      DECODE_CP (enc (instruction$LDC cond n opt cpn crd rn offset)) =
      ldc_stc)`,
  SRW_TAC word_frags [DECODE_CP_def,options_encode_def,word_modify_def]);

val decode_27_enc_coproc = store_thm("decode_27_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      enc (instruction$CDP cond cpn cop1 crd crn crm cop2) ' 27) /\
   (!cond. enc (instruction$UND cond) ' 27 = F) /\
   (!cond cpn cop1 rd crn crm cop2.
      enc (instruction$MRC cond cpn cop1 rd crn crm cop2) ' 27) /\
   (!cond cpn cop1 rd crn crm cop2.
      enc (instruction$MCR cond cpn cop1 rd crn crm cop2) ' 27) /\
   (!cond n opt cpn crd rn offset.
      enc (instruction$STC cond n opt cpn crd rn offset) ' 27) /\
   (!cond n opt cpn crd rn offset.
      enc (instruction$LDC cond n opt cpn crd rn offset) ' 27)`,
  SRW_TAC word_frags [options_encode_def,word_modify_def]);

(* ......................................................................... *)

val word_frags =
  [ARITH_ss,fcpLib.FCP_ss,wordsLib.SIZES_ss,BITS_NUMERAL_ss,
   rewrites [INDEX_RAND,word_or_def,word_index,w2w,word_lsl_def,
     word_bits_def,word_extract_def,condition_encode_lem,
     instruction_encode_def,shift_encode_lem,BIT_NUMERAL,BIT_ZERO]];

val decode_br_enc = store_thm("decode_br_enc",
  `(!cond offset.
      DECODE_BRANCH (enc (instruction$B cond offset)) = (F, offset)) /\
   (!cond offset.
      DECODE_BRANCH (enc (instruction$BL cond offset)) = (T, offset))`,
  SRW_TAC word_frags [DECODE_BRANCH_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,
         (SYM o EVAL) ``11 * 2 ** 24``,(SYM o EVAL) ``10 * 2 ** 24``]);

val shift_immediate_enc_lem = prove(
  `(!i r. (w2w:word32->word8)
    ((11 -- 7) (w2w (i:word5) << 7 || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8)
    ((11 -- 7) (w2w (i:word5) << 7 || 32w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8)
    ((11 -- 7) (w2w (i:word5) << 7 || 64w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8)
    ((11 -- 7) (w2w (i:word5) << 7 || 96w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word2) ((6 -- 5) (i << 7 || w2w (r:word4))) = 0w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5) (i << 7 || 32w || w2w (r:word4))) = 1w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5) (i << 7 || 64w || w2w (r:word4))) = 2w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5) (i << 7 || 96w || w2w (r:word4))) = 3w) /\
   (!i r. (w2w:word32->word4) ((3 -- 0) (i << 7 || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0) (i << 7 || 32w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0) (i << 7 || 64w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0) (i << 7 || 96w || w2w (r:word4))) = r)`,
  SRW_TAC word_frags [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []);

val shift_immediate_enc_lem2 = prove(
  `(!i r. (w2w:word32->word8) ((11 -- 7)
      (33554432w || w2w (i:word5) << 7 || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8) ((11 -- 7)
      (33554432w || w2w (i:word5) << 7 || 32w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8) ((11 -- 7)
      (33554432w || w2w (i:word5) << 7 || 64w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word8) ((11 -- 7)
      (33554432w || w2w (i:word5) << 7 || 96w || w2w (r:word4))) = w2w i) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (33554432w || i << 7 || w2w (r:word4))) = 0w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (33554432w || i << 7 || 32w || w2w (r:word4))) = 1w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (33554432w || i << 7 || 64w || w2w (r:word4))) = 2w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (33554432w || i << 7 || 96w || w2w (r:word4))) = 3w) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (33554432w || i << 7 || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (33554432w || i << 7 || 32w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (33554432w || i << 7 || 64w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (33554432w || i << 7 || 96w || w2w (r:word4))) = r)`,
  SRW_TAC word_frags [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []);

val shift_register_enc_lem = prove(
  `(!i r. (w2w:word32->word4) ((11 -- 8)
      (16w || w2w (i:word4) << 8 || w2w (r:word4))) = i) /\
   (!i r. (w2w:word32->word4) ((11 -- 8)
      (16w || w2w (i:word4) << 8 || 32w || w2w (r:word4))) = i) /\
   (!i r. (w2w:word32->word4) ((11 -- 8)
      (16w || w2w (i:word4) << 8 || 64w || w2w (r:word4))) = i) /\
   (!i r. (w2w:word32->word4) ((11 -- 8)
      (16w || w2w (i:word4) << 8 || 96w || w2w (r:word4))) = i) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (16w || i << 8 || w2w (r:word4))) = 0w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (16w || i << 8 || 32w || w2w (r:word4))) = 1w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (16w || i << 8 || 64w || w2w (r:word4))) = 2w) /\
   (!i r. (w2w:word32->word2) ((6 -- 5)
      (16w || i << 8 || 96w || w2w (r:word4))) = 3w) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (16w || i << 8 || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (16w || i << 8 || 32w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (16w || i << 8 || 64w || w2w (r:word4))) = r) /\
   (!i r. (w2w:word32->word4) ((3 -- 0)
      (16w || i << 8 || 96w || w2w (r:word4))) = r)`,
  SRW_TAC word_frags [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []);

val immediate_enc = store_thm("immediate_enc",
  `(!c r i. IMMEDIATE c ((11 >< 0) (addr_mode1_encode (Dp_immediate r i))) =
      arm$ROR (w2w i) (2w * w2w r) c) /\
    !c r i. IMMEDIATE c ((11 >< 0) (msr_mode_encode (Msr_immediate r i))) =
      arm$ROR (w2w i) (2w * w2w r) c`,
  SRW_TAC (boolSimps.LET_ss::word_frags)
         [IMMEDIATE_def,addr_mode1_encode_def,msr_mode_encode_def]
    \\ (MATCH_MP_TAC (METIS_PROVE [] ``!a b c d x. (a = b) /\ (c = d) ==>
         (ROR a c x = ROR b d x)``)
    \\ STRIP_TAC THENL [ALL_TAC,
         MATCH_MP_TAC (PROVE [] ``!a b. (a = b) ==> (2w:word8 * a = 2w * b)``)]
    \\ SRW_TAC word_frags [WORD_EQ]
    THENL [Cases_on `i' < 12` \\ SRW_TAC word_frags []
        \\ Cases_on `i' < 8` \\ SRW_TAC word_frags [],
      Cases_on `i' < 4` \\ SRW_TAC word_frags []]
    \\ POP_ASSUM_LIST (ASSUME_TAC o hd)
    \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []));

val immediate_enc2 = store_thm("immediate_enc2",
  `!i. (11 >< 0) (addr_mode2_encode (Dt_immediate i)) = i`,
  SRW_TAC word_frags [addr_mode2_encode_def,w2w]
    \\ Cases_on `i' < 12` \\ SRW_TAC word_frags []);

val immediate_enc3 = store_thm("immediate_enc3",
  `(!i. (11 >< 8) (addr_mode3_encode (Dth_immediate i)) = (7 >< 4) i) /\
     !i. (3 >< 0) (addr_mode3_encode (Dth_immediate i)) = (3 >< 0) i`,
  SRW_TAC word_frags [addr_mode3_encode_def,w2w]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val register_enc3 = store_thm("register_enc3",
  `!i. (3 >< 0) (addr_mode3_encode (Dth_register r)) = r`,
  SRW_TAC word_frags [addr_mode3_encode_def,w2w]);

val lem = simpLib.SIMP_PROVE (std_ss++WORD_BIT_EQ_ss) []
  ``~(i = 0w:word5) ==> ~((4 >< 0) i = 0w:word8)``;

val lem2 = simpLib.SIMP_PROVE (std_ss++WORD_ARITH_ss++WORD_ARITH_EQ_ss) []
  ``-1w = 3w:word2``;

val shift_immediate_enc = store_thm("shift_immediate_enc",
  `!reg m c sh i. SHIFT_IMMEDIATE reg m c
      ((11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i))) =
      if i = 0w then
        case sh of
          LSL Rm => arm$LSL (REG_READ reg m Rm) 0w c
        | LSR Rm => arm$LSR (REG_READ reg m Rm) 32w c
        | ASR Rm => arm$ASR (REG_READ reg m Rm) 32w c
        | ROR Rm => word_rrx(c, REG_READ reg m Rm)
      else
        case sh of
          LSL Rm => arm$LSL (REG_READ reg m Rm) (w2w i) c
        | LSR Rm => arm$LSR (REG_READ reg m Rm) (w2w i) c
        | ASR Rm => arm$ASR (REG_READ reg m Rm) (w2w i) c
        | ROR Rm => arm$ROR (REG_READ reg m Rm) (w2w i) c`,
  REPEAT STRIP_TAC \\ Cases_on `sh` \\ Cases_on `i = 0w` \\ IMP_RES_TAC lem
    \\ SRW_TAC [boolSimps.LET_ss, WORD_EXTRACT_ss]
         [SHIFT_IMMEDIATE_def,SHIFT_IMMEDIATE2_def,addr_mode1_encode_def,
          shift_encode_def,shift_immediate_enc_lem,lem2]);

val shift_immediate_enc2 = store_thm("shift_immediate_enc2",
  `!reg m c sh i. SHIFT_IMMEDIATE reg m c
      ((11 >< 0) (addr_mode2_encode (Dt_shift_immediate sh i))) =
      if i = 0w then
        case sh of
          LSL Rm => arm$LSL (REG_READ reg m Rm) 0w c
        | LSR Rm => arm$LSR (REG_READ reg m Rm) 32w c
        | ASR Rm => arm$ASR (REG_READ reg m Rm) 32w c
        | ROR Rm => word_rrx(c, REG_READ reg m Rm)
      else
        case sh of
          LSL Rm => arm$LSL (REG_READ reg m Rm) (w2w i) c
        | LSR Rm => arm$LSR (REG_READ reg m Rm) (w2w i) c
        | ASR Rm => arm$ASR (REG_READ reg m Rm) (w2w i) c
        | ROR Rm => arm$ROR (REG_READ reg m Rm) (w2w i) c`,
  REPEAT STRIP_TAC \\ Cases_on `sh` \\ Cases_on `i = 0w` \\ IMP_RES_TAC lem
    \\ SRW_TAC [boolSimps.LET_ss, WORD_EXTRACT_ss]
        [SHIFT_IMMEDIATE_def,SHIFT_IMMEDIATE2_def,addr_mode2_encode_def,
         shift_encode_def,shift_immediate_enc_lem2,lem2]);

val shift_register_enc = store_thm("shift_register_enc",
  `!reg m c sh r. SHIFT_REGISTER reg m c
      ((11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))) =
      let rs = (7 >< 0) (REG_READ reg m r) in
        case sh of
          LSL Rm => arm$LSL (REG_READ (INC_PC reg) m Rm) rs c
        | LSR Rm => arm$LSR (REG_READ (INC_PC reg) m Rm) rs c
        | ASR Rm => arm$ASR (REG_READ (INC_PC reg) m Rm) rs c
        | ROR Rm => arm$ROR (REG_READ (INC_PC reg) m Rm) rs c`,
  REPEAT STRIP_TAC \\ Cases_on `sh`
    \\ SRW_TAC [boolSimps.LET_ss, WORD_EXTRACT_ss]
        [SHIFT_REGISTER_def,SHIFT_REGISTER2_def,addr_mode1_encode_def,
         shift_encode_def,shift_register_enc_lem,lem2]);

val shift_register_enc2 = store_thm("shift_register_enc2",
  `!r. (3 >< 0) ((11 >< 0) (msr_mode_encode (Msr_register r))) = r`,
  SRW_TAC (boolSimps.LET_ss::word_frags) [msr_mode_encode_def]);

val shift_immediate_shift_register = store_thm("shift_immediate_shift_register",
  `(!reg m c sh r.
     (11 >< 0) (addr_mode1_encode (Dp_shift_register sh r)) ' 4) /\
   (!reg m c sh i.
     ~((11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i)) ' 4))`,
  NTAC 6 STRIP_TAC \\ Cases_on `sh`
    \\ SRW_TAC word_frags [addr_mode1_encode_def]);

val decode_data_proc_enc_ = prove(
  `!cond op s rd rn Op2.
      DECODE_DATAP (data_proc_encode cond op s rn rd Op2) =
        (IS_DP_IMMEDIATE Op2,op,s,rn,rd,(11 >< 0) (addr_mode1_encode Op2))`,
  Cases_on `Op2`
    \\ SRW_TAC word_frags [IS_DP_IMMEDIATE_def,DECODE_DATAP_def,
         addr_mode1_encode_def,data_proc_encode_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,(SYM o EVAL) ``256 * 2 ** 12``]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_data_proc_enc = prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn Op2.
      DECODE_DATAP (enc (f cond s rd rn Op2)) =
      (IS_DP_IMMEDIATE Op2,decode_opcode (f cond s rd rn Op2),
       s,rn,rd,(11 >< 0) (addr_mode1_encode Op2)))`,
  SRW_TAC [] [instruction_encode_def,decode_opcode_def]
    \\ SRW_TAC [] [decode_data_proc_enc_]);

val decode_data_proc_enc2 = prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn Op2.
      DECODE_DATAP (enc (f cond rn Op2)) =
      (IS_DP_IMMEDIATE Op2,decode_opcode (f cond rn Op2),
       T,rn,0w,(11 >< 0) (addr_mode1_encode Op2)))`,
  SRW_TAC [] [instruction_encode_def,decode_opcode_def]
    \\ SRW_TAC [] [decode_data_proc_enc_]);

val decode_data_proc_enc3 = prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd Op2.
      DECODE_DATAP (enc (f cond s rd Op2)) =
      (IS_DP_IMMEDIATE Op2,decode_opcode (f cond s rd Op2),
       s,0w,rd,(11 >< 0) (addr_mode1_encode Op2)))`,
  SRW_TAC [] [instruction_encode_def,decode_opcode_def]
    \\ SRW_TAC [] [decode_data_proc_enc_]);

val decode_mla_mul_enc = store_thm("decode_mla_mul_enc",
  `(!cond s rd rm rs.
      DECODE_MLA_MUL (enc (instruction$MUL cond s rd rm rs)) =
      (F,F,F,s,rd,0w,rs,rm)) /\
   (!cond s rd rm rs rn.
      DECODE_MLA_MUL (enc (instruction$MLA cond s rd rm rs rn)) =
      (F,F,T,s,rd,rn,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$UMULL cond s rdlo rdhi rm rs)) =
      (T,F,F,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$UMLAL cond s rdlo rdhi rm rs)) =
      (T,F,T,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$SMULL cond s rdlo rdhi rm rs)) =
      (T,T,F,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$SMLAL cond s rdlo rdhi rm rs)) =
      (T,T,T,s,rdhi,rdlo,rs,rm))`,
  REPEAT STRIP_TAC \\ SRW_TAC word_frags [DECODE_MLA_MUL_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_ldr_str_enc = Count.apply store_thm("decode_ldr_str_enc",
  `(!cond b opt rd rn offset.
      DECODE_LDR_STR (enc (instruction$LDR cond b opt rd rn offset)) =
      (IS_DT_SHIFT_IMMEDIATE offset, opt.Pre, opt.Up, b, opt.Wb,
       T, rn, rd, (11 >< 0) (addr_mode2_encode offset))) /\
   (!cond b opt rd rn offset.
      DECODE_LDR_STR (enc (instruction$STR cond b opt rd rn offset)) =
      (IS_DT_SHIFT_IMMEDIATE offset, opt.Pre, opt.Up, b, opt.Wb,
       F, rn, rd, (11 >< 0) (addr_mode2_encode offset)))`,
  REPEAT STRIP_TAC \\ Cases_on `offset` \\ TRY (Cases_on `sh`)
    \\ SRW_TAC word_frags [DECODE_LDR_STR_def,IS_DT_SHIFT_IMMEDIATE_def,
         addr_mode2_encode_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_ldrh_strh_enc = Count.apply store_thm("decode_ldrh_strh_enc",
  `(!cond s h opt rd rn offset.
      DECODE_LDRH_STRH (enc (instruction$LDRH cond s h opt rd rn offset)) =
      let x = addr_mode3_encode offset in
        (opt.Pre, opt.Up, IS_DTH_IMMEDIATE offset, opt.Wb, T,
         rn, rd, (11 >< 8) x, s, h \/ (~h /\ ~s), (3 >< 0) x)) /\
   (!cond opt rd rn offset.
      DECODE_LDRH_STRH (enc (instruction$STRH cond opt rd rn offset)) =
      let x = addr_mode3_encode offset in
        (opt.Pre, opt.Up, IS_DTH_IMMEDIATE offset, opt.Wb, F,
         rn, rd, (11 >< 8) x, F, T, (3 >< 0) x))`,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ Cases_on `offset`
    \\ SRW_TAC word_frags [DECODE_LDRH_STRH_def,IS_DTH_IMMEDIATE_def,
         addr_mode3_encode_def,options_encode2_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_ldm_stm_enc = store_thm("decode_ldm_stm_enc",
  `(!cond s opt rn l.
      DECODE_LDM_STM (enc (instruction$LDM cond s opt rn l)) =
      (opt.Pre, opt.Up, s, opt.Wb, T, rn, l)) /\
   (!cond s opt rn l.
      DECODE_LDM_STM (enc (instruction$STM cond s opt rn l)) =
      (opt.Pre, opt.Up, s, opt.Wb, F, rn, l))`,
  SRW_TAC word_frags [DECODE_LDM_STM_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_swp_enc = store_thm("decode_swp_enc",
  `!cond b rd rm rn.
      DECODE_SWP (enc (instruction$SWP cond b rd rm rn)) = (b,rn,rd,rm)`,
  SRW_TAC word_frags [DECODE_SWP_def] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []);

val decode_mrs_enc = store_thm("decode_mrs_enc",
  `!cond r rd. DECODE_MRS (enc (instruction$MRS cond r rd)) = (r, rd)`,
  SRW_TAC word_frags [DECODE_MRS_def]
    \\ ASM_SIMP_TAC (bool_ss++ARITH_ss) [BIT_SHIFT_THM3,
         (SYM o EVAL) ``271 * 2 ** 16``,(SYM o EVAL) ``335 * 2 ** 16``]);

val decode_msr_enc = store_thm("decode_msr_enc",
  `!cond psrd Op2.
      DECODE_MSR (enc (instruction$MSR cond psrd Op2)) =
        let (r,bit19,bit16) = DECODE_PSRD psrd
        and opnd = (11 >< 0) (msr_mode_encode Op2) in
          (IS_MSR_IMMEDIATE Op2,r,bit19,bit16,(3 >< 0) opnd,opnd)`,
  REPEAT STRIP_TAC \\ Cases_on `Op2` \\ Cases_on `psrd`
    \\ SRW_TAC (boolSimps.LET_ss::word_frags) [DECODE_MSR_def,DECODE_PSRD_def,
         IS_MSR_IMMEDIATE_def,msr_psr_encode_def,msr_mode_encode_def]
    \\ ASM_SIMP_TAC (bool_ss++ARITH_ss) [BIT_SHIFT_THM3,
         (SYM o EVAL) ``4623 * 2 ** 12``, (SYM o EVAL) ``1168 * 2 ** 12``,
         (SYM o EVAL) ``1152 * 2 ** 12``, (SYM o EVAL) ``1040 * 2 ** 12``,
         (SYM o EVAL) ``144 * 2 ** 12``, (SYM o EVAL) ``128 * 2 ** 12``,
         (SYM o EVAL) ``16 * 2 ** 12``]);

val decode_mrc_mcr_rd_enc = store_thm("decode_mrc_mcr_rd_enc",
  `(!cond cpn cop1 rd crn crm cop2.
      (15 >< 12) (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) = rd) /\
   !cond cpn cop1 rd crn crm cop2.
      (15 >< 12) (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) = rd`,
  SRW_TAC word_frags [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ SRW_TAC word_frags []);

val decode_ldc_stc_enc = store_thm("decode_ldc_stc_enc",
  `(!cond n opt cpn crd rn offset.
      DECODE_LDC_STC (enc (instruction$LDC cond n opt cpn crd rn offset)) =
      (opt.Pre, opt.Up, n, opt.Wb, T, rn, crd, cpn, offset)) /\
   (!cond n opt cpn crd rn offset.
      DECODE_LDC_STC (enc (instruction$STC cond n opt cpn crd rn offset)) =
      (opt.Pre, opt.Up, n, opt.Wb, F, rn, crd, cpn, offset))`,
  SRW_TAC word_frags [DECODE_LDC_STC_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_ldc_stc_20_enc = store_thm("decode_ldc_stc_20_enc",
  `(!cond n opt cpn crd rn offset.
      enc (instruction$LDC cond n opt cpn crd rn offset) ' 20) /\
    !cond n opt cpn crd rn offset.
      ~(enc (instruction$STC cond n opt cpn crd rn offset) ' 20)`,
  SRW_TAC word_frags [DECODE_LDC_STC_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_cdp_enc = store_thm("decode_cdp_enc",
  `(!cond cpn cop1 crd crn crm cop2.
      DECODE_CDP (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
        (cop1,crn,crd,cpn,cop2,crm)) /\
    !cond cpn cop1 crd crn crm cop2.
      DECODE_CPN (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) = cpn`,
  SRW_TAC word_frags [DECODE_CDP_def,DECODE_CPN_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

val decode_mrc_mcr_enc = store_thm("decode_mrc_mcr_enc",
  `(!cond cpn cop1 rd crn crm cop2.
      DECODE_MRC_MCR (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) =
        (cop1,crn,rd,cpn,cop2,crm)) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_CPN (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) = cpn) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_MRC_MCR (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) =
        (cop1,crn,rd,cpn,cop2,crm)) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_CPN (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) = cpn)`,
  SRW_TAC word_frags [DECODE_MRC_MCR_def,DECODE_CPN_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ SRW_TAC word_frags []);

(* ......................................................................... *)

val BITS_ZERO5 = prove(
  `!h l n.  n < 2 ** l ==> (BITS h l n = 0)`,
  SRW_TAC [] [BITS_THM,LESS_DIV_EQ_ZERO,ZERO_LT_TWOEXP]);

val BITS_w2n_ZERO = prove(
  `!w: bool ** 'a. dimindex (:'a) <= l ==> (BITS h l (w2n w) = 0)`,
  METIS_TAC [dimword_def,TWOEXP_MONO2,LESS_LESS_EQ_TRANS,BITS_ZERO5,w2n_lt]);

val WORD_BITS_LSL = prove(
  `!h l n w:bool ** 'a.
      n <= h /\ n <= l /\ l <= h /\ h < dimindex (:'a) ==>
      ((h -- l) (w << n) = ((h - n) -- (l - n)) w)`,
  SRW_TAC [fcpLib.FCP_ss] [WORD_EQ,word_lsl_def,word_bits_def]
    \\ Cases_on `i + l < dimindex (:'a)`
    \\ FULL_SIMP_TAC (arith_ss++fcpLib.FCP_ss) [NOT_LESS_EQUAL,NOT_LESS]);

val condition_code_lem = prove(
  `!cond. condition_encode cond ' 28 = cond IN {NE;CC;PL;VC;LS;LT;LE;NV}`,
  Cases \\ RW_TAC (std_ss++wordsLib.SIZES_ss++
     pred_setSimps.PRED_SET_ss++BITS_NUMERAL_ss)
   [BIT_def,condition2num_thm,word_rol_def,word_ror_n2w,word_lsl_n2w,
    w2w_n2w,word_index,condition_encode_def]);

val condition_code_lem2 = prove(
  `!cond. ~(condition_encode cond ' 28) = cond IN {EQ;CS;MI;VS;HI;GE;GT;AL}`,
  Cases \\ SRW_TAC [] [condition_code_lem]);

val condition_code_lem =
  SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] condition_code_lem;

val condition_code_lem2 =
  SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] condition_code_lem2;

val condition_code_lem3 = prove(
  `!cond. num2condition (w2n ((31 -- 29) (condition_encode cond))) =
      case cond of
        EQ => EQ | NE => EQ | CS => CS | CC => CS
      | MI => MI | PL => MI | VS => VS | VC => VS
      | HI => HI | LS => HI | GE => GE | LT => GE
      | GT => GT | LE => GT | AL => AL | NV => AL`,
  Cases \\ SRW_TAC [boolSimps.LET_ss]
    [condition_encode_def,condition2num_thm,num2condition_thm,word_bits_n2w,
     word_rol_def,word_ror_n2w,word_lsl_n2w,w2w_n2w,w2n_n2w]
    \\ EVAL_TAC );

val word_ss = srw_ss()++fcpLib.FCP_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss++
  rewrites [word_or_def,word_index,w2w,word_lsl_def,word_bits_def,
    shift_encode_lem,BIT_def];

val pass_frags =
 [ARITH_ss,wordsLib.SIZES_ss,BITS_NUMERAL_ss,boolSimps.LET_ss,
  rewrites [CONDITION_PASSED_def,CONDITION_PASSED2_def,
    GSYM WORD_BITS_OVER_BITWISE,WORD_OR_CLAUSES,BITS_w2n_ZERO,WORD_BITS_LSL,
    word_bits_n2w,w2w_def,instruction_encode_def,condition_code_lem3]];

val condition_addr_mode1 = prove(
  `(!op2. (31 -- 29) (addr_mode1_encode op2) = 0w) /\
    !op2. ~((addr_mode1_encode op2) ' 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2` \\ TRY (Cases_on `s`)
    \\ SRW_TAC [WORD_BIT_EQ_ss] [addr_mode1_encode_def,shift_encode_def]);

val condition_addr_mode2 = prove(
  `(!op2. (31 -- 29) (addr_mode2_encode op2) = 0w) /\
    !op2. ~((addr_mode2_encode op2) ' 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2` \\ TRY (Cases_on `s`)
    \\ SRW_TAC [WORD_BIT_EQ_ss] [addr_mode2_encode_def,shift_encode_def]);

val condition_addr_mode3 = prove(
  `(!op2. (31 -- 29) (addr_mode3_encode op2) = 0w) /\
    !op2. ~((addr_mode3_encode op2) ' 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2`
    \\ SRW_TAC [WORD_BIT_EQ_ss] [addr_mode3_encode_def]);

val condition_msr_mode = prove(
  `(!op2. (31 -- 29) (msr_mode_encode op2) = 0w) /\
    !op2. ~((msr_mode_encode op2) ' 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2`
    \\ SRW_TAC [WORD_BIT_EQ_ss] [msr_mode_encode_def]);

val condition_msr_psr = prove(
  `(!psrd. (31 -- 29) (msr_psr_encode psrd) = 0w) /\
    !psrd. ~((msr_psr_encode psrd) ' 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `psrd`
    \\ SRW_TAC [WORD_BIT_EQ_ss] [msr_psr_encode_def]);

val condition_options = prove(
  `(!x opt. (31 -- 29) (options_encode x opt) = 0w) /\
    !x opt. ~((options_encode x opt) ' 28)`,
  NTAC 2 STRIP_TAC
    \\ SRW_TAC [WORD_BIT_EQ_ss] [options_encode_def,word_modify_def]);

val condition_options2 = prove(
  `(!x opt. (31 -- 29) (options_encode2 x opt) = 0w) /\
    !x opt. ~((options_encode2 x opt) ' 28)`,
  NTAC 2 STRIP_TAC
    \\ SRW_TAC [WORD_BIT_EQ_ss] [options_encode2_def,word_modify_def]);

val PASS_TAC = REPEAT STRIP_TAC \\ Cases_on_nzcv `flgs`
  \\ SRW_TAC pass_frags [condition_addr_mode1,condition_addr_mode2,
       condition_addr_mode3,condition_msr_mode,condition_msr_psr,
       condition_options,condition_options2,data_proc_encode_def]
  \\ FULL_SIMP_TAC word_ss [BITS_w2n_ZERO,condition_addr_mode1,
       condition_addr_mode2,condition_addr_mode3,condition_msr_mode,
       condition_msr_psr,condition_options,condition_options2]
  \\ RULE_ASSUM_TAC (REWRITE_RULE [condition_code_lem2])
  \\ FULL_SIMP_TAC (srw_ss()) [condition_code_lem];

(* ......................................................................... *)

val cond_pass_enc_br = store_thm("cond_pass_enc_br",
  `(!cond flgs offset.
      CONDITION_PASSED flgs (enc (instruction$B cond offset)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond flgs offset.
      CONDITION_PASSED flgs (enc (instruction$BL cond offset)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_swi = store_thm("cond_pass_enc_swi",
  `!cond flgs. CONDITION_PASSED flgs (enc (instruction$SWI cond)) =
               CONDITION_PASSED2 flgs cond`,
  PASS_TAC);

val cond_pass_enc_data_proc_ = prove(
  `!cond op s rd rn op2.
      CONDITION_PASSED flgs (data_proc_encode cond op s rd rn op2) =
      CONDITION_PASSED2 flgs cond`,
  PASS_TAC);

val cond_pass_enc_data_proc = prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn op2.
      CONDITION_PASSED flgs (enc (f cond s rd rn op2)) =
      CONDITION_PASSED2 flgs cond)`,
  SRW_TAC [] [instruction_encode_def] \\ SRW_TAC [] [cond_pass_enc_data_proc_]);

val cond_pass_enc_data_proc2 = prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn op2.
      CONDITION_PASSED flgs (enc (f cond rn op2)) =
      CONDITION_PASSED2 flgs cond)`,
  SRW_TAC [] [instruction_encode_def] \\ SRW_TAC [] [cond_pass_enc_data_proc_]);

val cond_pass_enc_data_proc3 = prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd op2.
      CONDITION_PASSED flgs (enc (f cond s rd op2)) =
      CONDITION_PASSED2 flgs cond)`,
  SRW_TAC [] [instruction_encode_def] \\ SRW_TAC [] [cond_pass_enc_data_proc_]);

val cond_pass_enc_mla_mul = store_thm("cond_pass_enc_mla_mul",
  `(!cond s rd rm rs.
      CONDITION_PASSED flgs (enc (instruction$MUL cond s rd rm rs)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s rd rm rs rn.
      CONDITION_PASSED flgs (enc (instruction$MLA cond s rd rm rs rn)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$UMULL cond s rdlo rdhi rm rs)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$UMLAL cond s rdlo rdhi rm rs)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$SMULL cond s rdlo rdhi rm rs)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$SMLAL cond s rdlo rdhi rm rs)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_ldr_str = store_thm("cond_pass_enc_ldr_str",
  `(!cond b opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$LDR cond b opt rd rn offset)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond b opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$STR cond b opt rd rn offset)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_ldrh_strh = store_thm("cond_pass_enc_ldrh_strh",
  `(!cond s h opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$LDRH cond s h opt rd rn offset)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$STRH cond opt rd rn offset)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_ldm_stm = store_thm("cond_pass_enc_ldm_stm",
  `(!cond s opt rn list.
      CONDITION_PASSED flgs (enc (instruction$LDM cond s opt rn list)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond s opt rn list.
      CONDITION_PASSED flgs (enc (instruction$STM cond s opt rn list)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_swp = store_thm("cond_pass_enc_swp",
  `!cond b rd rm rn.
      CONDITION_PASSED flgs (enc (instruction$SWP cond b rd rm rn)) =
      CONDITION_PASSED2 flgs cond`,
  PASS_TAC);

val cond_pass_enc_mrs = store_thm("cond_pass_enc_mrs",
  `!cond r rd.
      CONDITION_PASSED flgs (enc (instruction$MRS cond r rd)) =
      CONDITION_PASSED2 flgs cond`,
  PASS_TAC);

val cond_pass_enc_msr = store_thm("cond_pass_enc_msr",
  `!cond psrd op.
      CONDITION_PASSED flgs (enc (instruction$MSR cond psrd op)) =
      CONDITION_PASSED2 flgs cond`,
  PASS_TAC);

val cond_pass_enc_coproc = store_thm("cond_pass_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond. CONDITION_PASSED flgs (enc (instruction$UND cond)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond cpn cop1 rd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond cpn cop1 rd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond n opt cpn crd rn offset.
      CONDITION_PASSED flgs
        (enc (instruction$STC cond n opt cpn crd rn offset)) =
      CONDITION_PASSED2 flgs cond) /\
   (!cond n opt cpn crd rn offset.
      CONDITION_PASSED flgs
        (enc (instruction$LDC cond n opt cpn crd rn offset)) =
      CONDITION_PASSED2 flgs cond)`,
  PASS_TAC);

(* ......................................................................... *)

val condition_encode = save_thm("condition_encode",
   LIST_CONJ (map (fn x => EVAL ``condition_encode ^x``)
    ((snd o strip_comb o snd o dest_comb o concl) datatype_condition)));

(* ......................................................................... *)

fun MAP_SPEC t l = LIST_CONJ (map (fn x =>
  SIMP_RULE (srw_ss()++pred_setSimps.PRED_SET_ss)
    [decode_opcode_def] (SPEC x t)) l);

val opc1 =
 [`instruction$AND`, `instruction$EOR`, `instruction$SUB`, `instruction$RSB`,
  `instruction$ADD`, `instruction$ADC`, `instruction$SBC`, `instruction$RSC`,
  `instruction$ORR`, `instruction$BIC`];

val opc2 =
 [`instruction$TST`, `instruction$TEQ`, `instruction$CMP`, `instruction$CMN`];

val opc3 = [`instruction$MOV`, `instruction$MVN`];

val cond_pass_enc_data_proc = save_thm("cond_pass_enc_data_proc",
  MAP_SPEC cond_pass_enc_data_proc opc1);

val cond_pass_enc_data_proc2 = save_thm("cond_pass_enc_data_proc2",
  MAP_SPEC cond_pass_enc_data_proc2 opc2);

val cond_pass_enc_data_proc3 = save_thm("cond_pass_enc_data_proc3",
  MAP_SPEC cond_pass_enc_data_proc3 opc3);

val decode_data_proc_enc = save_thm("decode_data_proc_enc",
  MAP_SPEC decode_data_proc_enc opc1);

val decode_data_proc_enc2 = save_thm("decode_data_proc_enc2",
  MAP_SPEC decode_data_proc_enc2 opc2);

val decode_data_proc_enc3 = save_thm("decode_data_proc_enc3",
  MAP_SPEC decode_data_proc_enc3 opc3);

val decode_enc_data_proc = save_thm("decode_enc_data_proc",
  MAP_SPEC decode_enc_data_proc opc1);

val decode_enc_data_proc2 = save_thm("decode_enc_data_proc2",
  MAP_SPEC decode_enc_data_proc2 opc2);

val decode_enc_data_proc3 = save_thm("decode_enc_data_proc3",
  MAP_SPEC decode_enc_data_proc3 opc3);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
