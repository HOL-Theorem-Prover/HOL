(* ========================================================================= *)
(* FILE          : arm_evalScript.sml                                        *)
(* DESCRIPTION   : Various theorems about the ISA and instruction encoding   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005-2006                                                 *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "rich_listTheory", "wordsLib", "armLib",
            "bsubstTheory", "instructionTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q rich_listTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open bsubstTheory armTheory instructionTheory;

val _ = new_theory "arm_eval";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val fcp_ss   = armLib.fcp_ss;
val SIZES_ss = wordsLib.SIZES_ss;

val tt = set_trace "types";

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

val Sa_def = Define `Sa = $:-`;
val Sb_def = Define `Sb = $:-`;

(* ------------------------------------------------------------------------- *)

val STATE_ARMe_NEXT = store_thm("STATE_ARMe_NEXT",
  `!t a b c. (STATE_ARMe t a = b) /\ (NEXT_ARMe b = c) ==>
             (STATE_ARMe (t + 1) a = c)`,
  RW_TAC bool_ss [STATE_ARMe_def,GSYM arithmeticTheory.ADD1]);

val SUBST_EQ2 = store_thm("SUBST_EQ2",
  `!m a v. (m a = v) ==> ((a :- v) m = m)`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ RW_TAC std_ss [SUBST_def]);

val SUBST_EQ3 = prove(
  `!m a. (a :- m a) m = m`,
  STRIP_TAC \\ SIMP_TAC bool_ss [FUN_EQ_THM,SUBST_def]);

val Sab_EQ = store_thm("Sab_EQ",
  `(Sb a e (Sa a d m) = Sa a e m) /\
   (Sb a e (Sb a d m) = Sb a e m) /\
   (Sa a e (Sa a d m) = Sa a e m)`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_EQ]);

val SUBST_EVAL = store_thm("SUBST_EVAL",
  `!a w b. (a :- w) m b = if a = b then w else m b`,
  RW_TAC std_ss [SUBST_def]);

(* --- *)

val Sa_RULE_WORD = store_thm("Sa_RULE_WORD",
  `!m a b d e. Sa a e (Sa b d m) =
     if a <+ b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES]);

val Sb_RULE_WORD = store_thm("Sb_RULE_WORD",
  `!m a b d e. Sa a e (Sb b d m) =
     if a <+ b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES]);

val SUBST_COMMUTES4 = store_thm("SUBST_COMMUTES4",
  `!m a b d e. register2num a < register2num b ==>
     ((a :- e) ((b :- d) m) = (b :- d) ((a :- e) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    \\ RW_TAC bool_ss [SUBST_def]
    \\ FULL_SIMP_TAC bool_ss [register2num_11]);

val Sa_RULE4 = store_thm("Sa_RULE4",
  `!m a b d e. Sa a e (Sa b d m) =
     if register2num a < register2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES4]);

val Sb_RULE4 = store_thm("Sb_RULE4",
  `!m a b d e. Sa a e (Sb b d m) =
     if register2num a < register2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES4]);

(* --- *)

val SUBST_COMMUTES_PSR = store_thm("SUBST_COMMUTES_PSR",
  `!m a b d e. psrs2num b < psrs2num a ==>
     ((a :- e) ((b :- d) m) = (b :- d) ((a :- e) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    \\ RW_TAC bool_ss [SUBST_def]
    \\ FULL_SIMP_TAC bool_ss [psrs2num_11]);

val Sa_RULE_PSR = store_thm("Sa_RULE_PSR",
  `!m a b d e. Sa a e (Sa b d m) =
     if psrs2num a < psrs2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES_PSR]);

val Sb_RULE_PSR = store_thm("Sb_RULE_PSR",
  `!m a b d e. Sa a e (Sb b d m) =
     if psrs2num a < psrs2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES_PSR]);

(* ------------------------------------------------------------------------- *)

val tm1 = `!a b x y m. (a ::-> y) ((b ::-> x) m) =
     let lx = LENGTH x and ly = LENGTH y in
        if a <=+ b then
          if w2n b - w2n a <= ly then
            if ly - (w2n b - w2n a) < lx then
              (a ::-> y ++ BUTFIRSTN (ly - (w2n b - w2n a)) x) m
            else
              (a ::-> y) m
          else
            (a ::-< y) ((b ::-> x) m)
        else (* b <+ a *)
          if w2n a - w2n b < lx then
            (b ::-> JOIN (w2n a - w2n b) x y) m
          else
            (b ::-> x) ((a ::-> y) m)`

val tm2 = `!a b x y m. (a ::-> y) ((b ::-< x) m) =
     let lx = LENGTH x and ly = LENGTH y in
        if a <=+ b then
          if w2n b - w2n a <= ly then
            if ly - (w2n b - w2n a) < lx then
              (a ::-> y ++ BUTFIRSTN (ly - (w2n b - w2n a)) x) m
            else
              (a ::-> y) m
          else
            (a ::-< y) ((b ::-< x) m)
        else (* b <+ a *)
          if w2n a - w2n b < lx then
            (b ::-> JOIN (w2n a - w2n b) x y) m
          else
            (b ::-> x) ((a ::-> y) m)`

val BSa_RULE = store_thm("BSa_RULE", tm1,
  METIS_TAC [BSa_def,BSb_def,BSUBST_BSUBST]);

val BSb_RULE = store_thm("BSb_RULE", tm2,
  METIS_TAC [BSa_def,BSb_def,BSUBST_BSUBST]);

(* ------------------------------------------------------------------------- *)

val REGISTER_RANGES =
  (SIMP_RULE (std_ss++SIZES_ss) [] o Thm.INST_TYPE [alpha |-> ``:i4``]) w2n_lt;

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
  REPEAT Cases_word \\ SIMP_TAC std_ss [w2n_n2w,n2w_11]);

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

val READ_TO_READ6 = store_thm("READ_TO_READ6",
  `!r m n d. (REG_READ (REG_WRITE r usr 15w (d - 8w)) m n =
              REG_READ6 (REG_WRITE r usr 15w d) m n)`,
  RW_TAC (std_ss++SIZES_ss) [REG_READ_def,REG_READ6_def,FETCH_PC_def,
         REG_WRITE_def,SUBST_def,WORD_SUB_ADD,mode_reg2num_15,r15]
    \\ PROVE_TAC [num2register_11,mode_reg2num_lt,not_pc,DECIDE ``15 < 31``]);

val TO_WRITE_READ6 = store_thm("TO_WRITE_READ6",
  `(!r. FETCH_PC r = REG_READ6 r usr 15w) /\
   (!r. INC_PC r = REG_WRITE r usr 15w (REG_READ6 r usr 15w + 4w)) /\
   (!r m d. REG_WRITE r m 15w d = REG_WRITE r usr 15w d) /\
   (!r m. REG_READ6 r m 15w = REG_READ6 r usr 15w)`,
  RW_TAC std_ss [INC_PC_def,REG_READ6_def,REG_WRITE_def,REG_READ_def,
    FETCH_PC_def,mode_reg2num_15,r15]);

val REG_WRITE_WRITE = store_thm("REG_WRITE_WRITE",
  `!r m n d1 d2. REG_WRITE (REG_WRITE r m n d1) m n d2 = REG_WRITE r m n d2`,
  RW_TAC bool_ss [REG_WRITE_def,SUBST_EQ]);

val REG_WRITE_WRITE_COMM = store_thm("REG_WRITE_WRITE_COMM",
  `!r m n1 n2 d1 d2.
     ~(n1 = n2) ==>
      (REG_WRITE (REG_WRITE r m n1 d1) m n2 d2 =
       REG_WRITE (REG_WRITE r m n2 d2) m n1 d1)`,
  RW_TAC std_ss [REG_WRITE_def,SUBST_NE_COMMUTES,not_reg_eq,
    mode_reg2num_lt,num2register_11]);

val REG_WRITE_WRITE_PC = store_thm("REG_WRITE_WRITE_PC",
  `!r m1 m2 n d p.
     REG_WRITE (REG_WRITE r m1 15w p) m2 n d =
       if n = 15w then
         REG_WRITE r usr 15w d
       else
         REG_WRITE (REG_WRITE r m2 n d) usr 15w p`,
  RW_TAC std_ss [TO_WRITE_READ6,REG_WRITE_WRITE]
    \\ ASM_SIMP_TAC std_ss [REG_WRITE_def,SUBST_NE_COMMUTES,not_pc,
         mode_reg2num_15,mode_reg2num_lt,num2register_11]);

val REG_READ_WRITE_THM = prove(
  `(!r m n1 n2 d. REG_READ6 (REG_WRITE r m n1 d) m n2 =
      if n1 = n2 then d else REG_READ6 r m n2) /\
    !r m n d. (REG_WRITE r m n (REG_READ6 r m n) = r)`,
  RW_TAC std_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,
    SUBST_EQ3,mode_reg2num_15,r15] \\ SIMP_TAC std_ss [SUBST_def]
    \\ PROVE_TAC [not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
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
    SUBST_EQ3,mode_reg2num_15,r15] \\ SIMP_TAC std_ss [SUBST_def]
    \\ PROVE_TAC [not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
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
    \\ METIS_TAC [REG_WRITE_def,not_reg_eq,SUBST_NE_COMMUTES,
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
  RW_TAC std_ss [REG_READ_def,REG_WRITE_def,SUBST_def,
         r15,mode_reg2num_lt,num2register_11]
    \\ METIS_TAC [mode_reg2num_15,not_reg_eq]);

val REG_READ_WRITEL_PC = store_thm("REG_READ_WRITEL_PC",
  `!r m m2 a b l. REG_READ (REG_WRITEL r m ((a,b)::l)) m2 15w =
       if a = 15w then b + 8w else REG_READ (REG_WRITEL r m l) m2 15w`,
  RW_TAC std_ss [REG_WRITEL_def,TO_WRITE_READ6,lem,lem2]);

val REG_READ_WRITEL_PC2 = store_thm("REG_READ_WRITEL_PC2",
  `!r m a b l. (REG_WRITEL r m ((a,b)::l)) r15 =
       if a = 15w then b else (REG_WRITEL r m l) r15`,
  RW_TAC std_ss [REG_WRITEL_def,REG_WRITE_def,SUBST_def,
         r15,mode_reg2num_lt,num2register_11]
    \\ METIS_TAC [mode_reg2num_15,not_reg_eq]);

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
   `(!a b c d n. (SET_NZCV (a,b,c,d) n) %% 31 = a) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 30 = b) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 29 = c) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 28 = d)`,
  RW_TAC (fcp_ss++SIZES_ss) [SET_NZCV_def,word_modify_def]);

val DECODE_IFMODE_SET_NZCV = store_thm("DECODE_IFMODE_SET_NZCV",
   `(!a n. (27 -- 8) (SET_NZCV a n) = (27 -- 8) n) /\
    (!a n. (SET_NZCV a n) %% 7 = n %% 7) /\
    (!a n. (SET_NZCV a n) %% 6 = n %% 6) /\
    (!a n. (SET_NZCV a n) %% 5 = n %% 5) /\
    (!a n. (4 >< 0) (SET_NZCV a n) = (4 >< 0) n)`,
  RW_TAC bool_ss [] \\ Cases_on_nzcv `a`
    \\ SIMP_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,word_modify_def,word_extract_def,word_bits_def]);

val DECODE_IFMODE_SET_IFMODE = store_thm("DECODE_IFMODE_SET_IFMODE",
   `(!i f m n. (SET_IFMODE i f m n) %% 7 = i) /\
    (!i f m n. (SET_IFMODE i f m n) %% 6 = f) /\
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
  `(!i f m n. (SET_IFMODE i f m n) %% 31 = n %% 31) /\
   (!i f m n. (SET_IFMODE i f m n) %% 30 = n %% 30) /\
   (!i f m n. (SET_IFMODE i f m n) %% 29 = n %% 29) /\
   (!i f m n. (SET_IFMODE i f m n) %% 28 = n %% 28) /\
   (!i f m n. (27 -- 8) (SET_IFMODE i f m n) = (27 -- 8) n) /\
   (!i f m n. (SET_IFMODE i f m n) %% 5 = n %% 5)`,
  RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
    [SET_IFMODE_def,word_modify_def,word_bits_def]);

val SET_NZCV_ID = store_thm("SET_NZCV_ID",
  `!a. SET_NZCV (a %% 31,a %% 30,a %% 29,a %% 28) a = a`,
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
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,SUBST_def,
         USER_def,mode2psr_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC bool_ss [mode_case_def,psrs_distinct]);

val CPSR_READ_WRITE = store_thm("CPSR_READ_WRITE",
  `(!psr. CPSR_WRITE psr (CPSR_READ psr) = psr) /\
   (!psr mode. USER mode ==> (CPSR_WRITE psr (SPSR_READ psr mode) = psr))`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SUBST_EQ3,
         USER_def,mode2psr_def]
    \\ REWRITE_TAC [mode_case_def,SUBST_EQ3]);

val CPSR_WRITE_WRITE = store_thm("CPSR_WRITE_WRITE",
  `!psr a b. CPSR_WRITE (CPSR_WRITE psr a) b = CPSR_WRITE psr b`,
  SIMP_TAC bool_ss [CPSR_WRITE_def,SUBST_EQ]);

val USER_usr = save_thm("USER_usr",
  simpLib.SIMP_PROVE bool_ss [USER_def] ``USER usr``);

val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y =
               CPSR_WRITE (SPSR_WRITE psr m y) x`,
  RW_TAC bool_ss [SPSR_WRITE_def,CPSR_WRITE_def,USER_def,mode2psr_def]
    \\ Cases_on `m`
    \\ FULL_SIMP_TAC bool_ss [mode_distinct,mode_case_def,psrs_distinct,
         SUBST_NE_COMMUTES]);

val SPSR_READ_WRITE = store_thm("SPSR_READ_WRITE",
  `!psr m. SPSR_WRITE psr m (SPSR_READ psr m) = psr`,
  RW_TAC std_ss [SPSR_READ_def,SPSR_WRITE_def,mode2psr_def]
    \\ Cases_on `m`
    \\ SIMP_TAC (srw_ss()) [SUBST_EQ3]);

val SPSR_WRITE_THM = store_thm("SPSR_WRITE_THM",
  `!psr m x. USER m ==> (SPSR_WRITE psr m x = psr)`,
  SIMP_TAC std_ss [SPSR_WRITE_def]);

val SPSR_WRITE_WRITE = store_thm("SPSR_WRITE_WRITE",
  `!psr m x y. SPSR_WRITE (SPSR_WRITE psr m x) m y = SPSR_WRITE psr m y`,
  RW_TAC std_ss [SPSR_WRITE_def,SUBST_EQ]);

val SPSR_WRITE_READ = store_thm("SPSR_WRITE_READ",
  `!psr m x. ~USER m ==> (SPSR_READ (SPSR_WRITE psr m x) m = x) /\
                         (SPSR_READ (CPSR_WRITE psr x) m = SPSR_READ psr m)`,
  RW_TAC std_ss [SPSR_WRITE_def,CPSR_WRITE_def,SPSR_READ_def,SUBST_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC (srw_ss()) [USER_def,mode2psr_def]);

(* ------------------------------------------------------------------------- *)

val word_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++
  rewrites [n2w_def,word_extract_def,word_bits_n2w,w2w,
    BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
    DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def];

val REDUCE_RULE = numLib.REDUCE_RULE;

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val MOD_DIMINDEX_32 = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
   Thm.INST_TYPE [alpha |-> ``:i32``]) MOD_DIMINDEX;

val DECODE_INST = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_bit,
    word_bits_n2w,word_bit_n2w,n2w_11,BITS_COMP_THM2,BITS_ZERO2,MOD_DIMINDEX_32,
    EVAL ``BITS 31 0 1``,EVAL ``BITS 31 0 2``,EVAL ``BITS 31 0 4``] o
  SPEC `n2w n`) DECODE_INST_def;

val DECODE_TAC = SIMP_TAC std_ss [DECODE_PSR_def,DECODE_BRANCH_def,
      DECODE_DATAP_def,DECODE_MRS_def,DECODE_MSR_def,DECODE_LDR_STR_def,
      DECODE_MLA_MUL_def,DECODE_LDM_STM_def,DECODE_SWP_def,DECODE_LDC_STC_def,
      SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,NZCV_def,DECODE_INST,
      REGISTER_LIST_def,SUC2NUM  rich_listTheory.GENLIST,rich_listTheory.SNOC,
      word_extract_def]
 \\ SIMP_TAC word_ss [];

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,i) = DIVMOD_2EXP 1 (DIV2 q0) in
     let (q2,f) = DIVMOD_2EXP 1 q1 in
     let (q3,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q2) in
     let (q4,C) = DIVMOD_2EXP 1 q3 in
     let (q5,Z) = DIVMOD_2EXP 1 q4 in
       ((ODD q5,Z=1,C=1,V=1),f = 1,i = 1,n2w m)`, DECODE_TAC);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH (n2w n) =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,n2w offset)`, DECODE_TAC);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP (n2w n) =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,n2w opcode,S = 1,n2w Rn,n2w Rd,n2w opnd2)`, DECODE_TAC);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS (n2w n) =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),n2w Rd)`, DECODE_TAC);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR (n2w n) =
     let (q0,opnd) = DIVMOD_2EXP 12 n in
     let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
     let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
     let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
       (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,
        n2w (MOD_2EXP 4 opnd),n2w opnd)`,
  DECODE_TAC \\ `4096 = 16 * 256` by numLib.ARITH_TAC
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC arith_ss [MOD_MULT_MOD]);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 12 n in
    let (q1,Rd) = DIVMOD_2EXP 4 q0 in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,L) = DIVMOD_2EXP 1 q2 in
    let (q4,W) = DIVMOD_2EXP 1 q3 in
    let (q5,B) = DIVMOD_2EXP 1 q4 in
    let (q6,U) = DIVMOD_2EXP 1 q5 in
    let (q7,P) = DIVMOD_2EXP 1 q6 in
      (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,n2w Rn,n2w Rd,n2w offset)`,
   DECODE_TAC);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,Rd) = DIVMOD_2EXP 4 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,A) = DIVMOD_2EXP 1 q4 in
    let (q6,Sgn) = DIVMOD_2EXP 1 q5 in
      (ODD q6,Sgn = 1,A = 1,S = 1,n2w Rd,n2w Rn,n2w Rs,n2w Rm)`, DECODE_TAC);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM (n2w n) =
    let (q0,list) = DIVMOD_2EXP 16 n in
    let (q1,Rn) = DIVMOD_2EXP 4 q0 in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,U) = DIVMOD_2EXP 1 q4 in
      (ODD q5, U = 1, S = 1, W = 1, L = 1,n2w Rn,n2w list)`, DECODE_TAC);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),n2w Rn,n2w Rd,n2w Rm)`, DECODE_TAC);

val DECODE_LDC_STC_THM = store_thm("DECODE_LDC_STC_THM",
  `!n. DECODE_LDC_STC (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 8 n in
    let (q1,Rn) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,U) = DIVMOD_2EXP 1 (DIV2 q3) in
      (ODD q4,U = 1,W = 1,L = 1,n2w Rn,n2w offset)`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

fun w2w_n2w_sizes a b = (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
  Thm.INST_TYPE [alpha |-> a, beta |-> b]) w2w_n2w;

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!reg mode C opnd2.
     SHIFT_IMMEDIATE reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let shift = MOD_2EXP 5 q1 in
       let rm = REG_READ reg mode (n2w Rm) in
         SHIFT_IMMEDIATE2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``) [``:i8``, ``:i4``, ``:i2``])
    \\ DECODE_TAC);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg mode C opnd2.
     SHIFT_REGISTER reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ reg mode (n2w Rs)))
       and rm = REG_READ (INC_PC reg) mode (n2w Rm) in
         SHIFT_REGISTER2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC [w2w_n2w_sizes ``:i32`` ``:i8``]
    \\ ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``)
          [``:i8``, ``:i4``, ``:i2``])
    \\ SIMP_TAC std_ss [SHIFT_REGISTER_def,word_extract_def,
         (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [n2w_w2n,BITS_THM,DIV_1,
            (GSYM o SIMP_RULE std_ss [] o SPEC `8`) MOD_2EXP_def] o
          SPECL [`7`,`0`,`w2n (a:word32)`] o
          Thm.INST_TYPE [alpha |-> ``:i32``]) word_bits_n2w]
    \\ SIMP_TAC word_ss []);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST (n2w n) =
       let (q0,b0) = DIVMOD_2EXP 1 n in
       let (q1,b1) = DIVMOD_2EXP 1 q0 in
       let (q2,b2) = DIVMOD_2EXP 1 q1 in
       let (q3,b3) = DIVMOD_2EXP 1 q2 in
       let (q4,b4) = DIVMOD_2EXP 1 q3 in
       let (q5,b5) = DIVMOD_2EXP 1 q4 in
       let (q6,b6) = DIVMOD_2EXP 1 q5 in
       let (q7,b7) = DIVMOD_2EXP 1 q6 in
       let (q8,b8) = DIVMOD_2EXP 1 q7 in
       let (q9,b9) = DIVMOD_2EXP 1 q8 in
       let (q10,b10) = DIVMOD_2EXP 1 q9 in
       let (q11,b11) = DIVMOD_2EXP 1 q10 in
       let (q12,b12) = DIVMOD_2EXP 1 q11 in
       let (q13,b13) = DIVMOD_2EXP 1 q12 in
       let (q14,b14) = DIVMOD_2EXP 1 q13 in
       MAP SND (FILTER FST
         [(b0 = 1,0w); (b1 = 1,1w); (b2 = 1,2w); (b3 = 1,3w);
          (b4 = 1,4w); (b5 = 1,5w); (b6 = 1,6w); (b7 = 1,7w);
          (b8 = 1,8w); (b9 = 1,9w); (b10 = 1,10w); (b11 = 1,11w);
          (b12 = 1,12w); (b13 = 1,13w); (b14 = 1,14w); (ODD q14,15w)])`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val DECODE_INST_THM = store_thm("DECODE_INST_THM",
  `!n. DECODE_INST (n2w n) =
        let (q0,r4) = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
        let (q1,r65) = DIVMOD_2EXP 2 q0 in
        let (q2,r7) = DIVMOD_2EXP 1 q1 in
        let (q3,r20) = DIVMOD_2EXP 1 (DIV_2EXP 12 q2) in
        let (q4,r21) = DIVMOD_2EXP 1 q3 in
        let (q5,r23) = DIVMOD_2EXP 1 (DIV2 q4) in
        let (q6,r24) = DIVMOD_2EXP 1 q5 in
        let (q7,r25) = DIVMOD_2EXP 1 q6 in
        let bits2726 = MOD_2EXP 2 q7 in
        let (bit25,bit24,bit23,bit21,bit20,bit7,bits65,bit4) =
             (r25 = 1,r24 = 1,r23 = 1,r21 = 1,r20 = 1,r7 = 1,r65,r4 = 1) in
          if bits2726 = 0 then
            if bit24 /\ ~bit23 /\ ~bit20 then
                if bit25 \/ ~bit4 then
                  mrs_msr
                else
                  if ~bit21 /\ (BITS 11 5 n = 4) then swp else cdp_und
            else
              if ~bit25 /\ bit4 then
                if ~bit7 then
                  reg_shift
                else
                  if ~bit24 /\ (bits65 = 0) then mla_mul else cdp_und
              else
                data_proc
          else
            if bits2726 = 1 then
              if bit25 /\ bit4 then
                cdp_und
              else
                if bit20 then ldr else str
            else
              if bits2726 = 2 then
                if bit25 then br else
                  if bit20 then ldm else stm
              else
                if bit25 then
                  if bit24 then swi_ex else
                    if bit4 then
                      if bit20 then mrc else mcr
                    else
                      cdp_und
                  else
                    if bit20 then ldc else stc`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val word_ss = armLib.fcp_ss ++ wordsLib.SIZES_ss ++ ARITH_ss;

val lem = prove(
  `!w:word32 i. i < 5 ==> (((4 >< 0) w) :word5 %% i = w %% i)`,
  RW_TAC word_ss [word_extract_def,word_bits_def,w2w]);

val PSR_CONS = store_thm("PSR_CONS",
   `!w:word32. w =
       let m = DECODE_MODE ((4 >< 0) w) in
         if m = safe then
           SET_NZCV (w %% 31, w %% 30, w %% 29, w %% 28) ((27 -- 0) w)
         else
           SET_NZCV (w %% 31, w %% 30, w %% 29, w %% 28)
             (SET_IFMODE (w %% 7) (w %% 6) m (0xFFFFF20w && w))`,
  RW_TAC word_ss [SET_IFMODE_def,SET_NZCV_def,word_modify_def,n2w_def]
    \\ RW_TAC word_ss [word_bits_def]
    << [
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/ (i < 28)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC arith_ss [],
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/
       (7 < i /\ i < 28) \/ (i = 7) \/ (i = 6) \/ (i = 5) \/ (i < 5)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC (word_ss++ARITH_ss) [word_and_def]
        << [
          FULL_SIMP_TAC std_ss [LESS_THM]
            \\ FULL_SIMP_TAC arith_ss [] \\ EVAL_TAC,
          EVAL_TAC,
          `~(mode_num m = 0w)`
            by (Cases_on `m` \\ RW_TAC std_ss [mode_num_def] \\ EVAL_TAC)
            \\ POP_ASSUM MP_TAC \\ UNABBREV_TAC `m`
            \\ RW_TAC (word_ss++ARITH_ss)
                 [DECODE_MODE_def,mode_num_def,n2w_def,lem]
            \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC word_ss []]]);

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
       AND cond s Rd Rn Op2 -> 0w:word4
    || EOR cond s Rd Rn Op2 -> 1w
    || SUB cond s Rd Rn Op2 -> 2w
    || RSB cond s Rd Rn Op2 -> 3w
    || ADD cond s Rd Rn Op2 -> 4w
    || ADC cond s Rd Rn Op2 -> 5w
    || SBC cond s Rd Rn Op2 -> 6w
    || RSC cond s Rd Rn Op2 -> 7w
    || TST cond Rn Op2      -> 8w
    || TEQ cond Rn Op2      -> 9w
    || CMP cond Rn Op2      -> 10w
    || CMN cond Rn Op2      -> 11w
    || ORR cond s Rd Rn Op2 -> 12w
    || MOV cond s Rd Op2    -> 13w
    || BIC cond s Rd Rn Op2 -> 14w
    || MVN cond s Rd Op2    -> 15w
    || _ -> ARB`;

val DECODE_PSRD_def = Define`
  (DECODE_PSRD CPSR_c = (F,F,T)) /\ (DECODE_PSRD CPSR_f = (F,T,F)) /\
  (DECODE_PSRD CPSR_a = (F,T,T)) /\ (DECODE_PSRD SPSR_c = (T,F,T)) /\
  (DECODE_PSRD SPSR_f = (T,T,F)) /\ (DECODE_PSRD SPSR_a = (T,T,T))`;

val CONDITION_PASSED3_def = Define`
  CONDITION_PASSED3 (N,Z,C,V) cond =
    case cond of
       EQ -> Z
    || NE -> ~Z
    || CS -> C
    || CC -> ~C
    || MI -> N
    || PL -> ~N
    || VS -> V
    || VC -> ~V
    || HI -> C /\ ~Z
    || LS -> ~C \/ Z
    || GE -> N = V
    || LT -> ~(N = V)
    || GT -> ~Z /\ (N = V)
    || LE -> Z \/ ~(N = V)
    || AL -> T
    || NV -> F`;

val _ = overload_on("enc", ``instruction_encode``);

fun Cases_on_nzcv tm = FULL_STRUCT_CASES_TAC (SPEC tm (armLib.tupleCases
  ``(n,z,c,v):bool#bool#bool#bool``));

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (:'a) ==> (((n2w n):bool ** 'a) %% i = BIT i n)``;

val fcp_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss;

val word2_bits = map (fn i => CONJ (EVAL ``BIT 0 ^i``) (EVAL ``BIT 1 ^i``))
  [``0``,``1``,``2``,``3``];

val BIT_NUMERAL = CONJ (SPECL [`0`,`NUMERAL n`] BIT_def)
                       (SPECL [`NUMERAL b`,`NUMERAL n`] BIT_def);

fun BIT_CASE_TAC t = POP_ASSUM (SPEC_THEN t
    (STRIP_ASSUME_TAC o SIMP_RULE fcp_ss [BIT_NUMERAL,BITS_THM]));

val decode_enc_lem = prove( 
  `(!w:word32. (((27 -- 26) w = 0w) = ~(w %% 27) /\ ~(w %% 26))) /\
   (!w:word32. (((27 -- 26) w = 1w) = ~(w %% 27) /\ (w %% 26))) /\
   (!w:word32. (((27 -- 26) w = 2w) = (w %% 27) /\ ~(w %% 26))) /\
   (!w:word32. (((27 -- 26) w = 3w) = (w %% 27) /\ (w %% 26)))`,
  REPEAT STRIP_TAC \\ Cases_on_word `w`
    \\ SIMP_TAC fcp_ss [word_bits_def,n2w_def,BIT_ZERO,
          DECIDE ``(i + 26 <= 27 /\ i + 26 <= 31) = (i = 0) \/ (i = 1)``]
    \\ (EQ_TAC \\ RW_TAC arith_ss []
    << [BIT_CASE_TAC `1`,BIT_CASE_TAC `0`, 
     STRIP_ASSUME_TAC (DECIDE ``(i = 0) \/ (i = 1) \/ (2 <= i)``)
       \\ FULL_SIMP_TAC fcp_ss word2_bits
       \\ IMP_RES_TAC TWOEXP_MONO2
       \\ FULL_SIMP_TAC bool_ss [EVAL ``2 ** 2``,BIT_def,BITS_THM,SUC_SUB]       \\ ASM_SIMP_TAC arith_ss [LESS_DIV_EQ_ZERO]]));

val decode_enc_lem2 = prove(
  `!w:word32. ((6 -- 5) w = 0w) = ~(w %% 6) /\ ~(w %% 5)`,
  REPEAT STRIP_TAC \\ Cases_on_word `w`
    \\ SIMP_TAC fcp_ss [word_bits_def,n2w_def,BIT_ZERO,
          DECIDE ``(i + 5 <= 6 /\ i + 5 <= 31) = (i = 0) \/ (i = 1)``]
    \\ EQ_TAC \\ RW_TAC arith_ss []
    << [BIT_CASE_TAC `1`,BIT_CASE_TAC `0`,
     STRIP_ASSUME_TAC (DECIDE ``(i = 0) \/ (i = 1) \/ (2 <= i)``)
       \\ FULL_SIMP_TAC fcp_ss word2_bits
       \\ IMP_RES_TAC TWOEXP_MONO2
       \\ FULL_SIMP_TAC bool_ss [EVAL ``2 ** 2``,BIT_def,BITS_THM,SUC_SUB]       \\ ASM_SIMP_TAC arith_ss [LESS_DIV_EQ_ZERO]]);

val decode_enc_lem3 = prove(
  `!w:word32. ((11 -- 5) w = 4w) =
     ~(w %% 11) /\ ~(w %% 10) /\ ~(w %% 9) /\ ~(w %% 8) /\
     (w %% 7)  /\ ~(w %% 6)  /\ ~(w %% 5)`,
  REPEAT STRIP_TAC \\ Cases_on_word `w`
    \\ SIMP_TAC std_ss [dimindex_32,word_bits_def,n2w_def,BIT_ZERO,
         DECIDE ``(i + 5 <= 11 /\ i + 5 <= 31) =
            (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3) \/
            (i = 4) \/ (i = 5) \/ (i = 6)``]
    \\ EQ_TAC \\ RW_TAC fcp_ss []
    << [BIT_CASE_TAC `6`,BIT_CASE_TAC `5`,BIT_CASE_TAC `4`,
        BIT_CASE_TAC `3`,BIT_CASE_TAC `2`,BIT_CASE_TAC `1`,
        BIT_CASE_TAC `0`,
     STRIP_ASSUME_TAC (DECIDE ``(i = 0) \/ (i = 1) \/ (i = 2) \/
          (i = 3) \/ (i = 4) \/ (i = 5) \/ (i = 6) \/ (7 <= i)``)
       \\ FULL_SIMP_TAC fcp_ss [BIT_NUMERAL,BITS_THM]
       \\ IMP_RES_TAC TWOEXP_MONO2
       \\ FULL_SIMP_TAC bool_ss [EVAL ``2 ** 7``,BIT_def,BITS_THM,SUC_SUB]
       \\ ASM_SIMP_TAC arith_ss [LESS_DIV_EQ_ZERO]]);

val condition_encode_lem = prove(
  `!cond i. i < 28 ==> ~(condition_encode cond %% i)`,
  SIMP_TAC (arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss)
    [condition_encode_def,word_index,w2w,word_lsl_def]);

fun b_of_b t = (GEN_ALL o SIMP_RULE std_ss [BITS_THM] o
  SPECL [`6`,`0`,`x`,t]) BIT_OF_BITS_THM2;

val shift_encode_lem = prove(
  `!r. (!i. 6 < i /\ i < 32 ==> ~(shift_encode r %% i)) /\
       ~(shift_encode r %% 4)`,
  Cases \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss)
    [shift_encode_def,word_index,w2w,word_or_def,
     b_of_b `32`, b_of_b `64`, b_of_b `96`] \\ EVAL_TAC);

val DECODE_INST =
  SIMP_RULE std_ss [decode_enc_lem,decode_enc_lem2,decode_enc_lem3]
    DECODE_INST_def;

val INDEX_RAND =
 (GEN_ALL o SIMP_RULE bool_ss [] o ISPEC `\x:word32. x %% i`) COND_RAND;

val BITS_NUMERAL = (GEN_ALL o SPECL [`h`,`l`,`NUMERAL n`]) BITS_def;

val BITS_NUMERAL_ss = rewrites
  [BITS_NUMERAL,BITS_ZERO2,numeralTheory.numeral_suc,numeralTheory.iDUB_removal,
   numeral_bitTheory.NUMERAL_DIV_2EXP,numeral_bitTheory.NUMERAL_MOD_2EXP,
   numeral_bitTheory.iMOD_2EXP,numeral_bitTheory.NUMERAL_DIV2,DIV2_def,NORM_0];

val word_ss = srw_ss()++fcpLib.FCP_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss++
  rewrites [INDEX_RAND,BIT_def,word_or_def,word_index,w2w,word_lsl_def,
    DECODE_INST,condition_encode_lem,instruction_encode_def,shift_encode_lem];

(* ......................................................................... *)

val decode_enc_br = store_thm("decode_enc_br",
  `(!cond offset. DECODE_INST (enc (instruction$B cond offset)) = br) /\
   (!cond offset. DECODE_INST (enc (instruction$BL cond offset)) = br)`,
  RW_TAC word_ss []);

val decode_enc_swi = store_thm("decode_enc_swi",
  `!cond. DECODE_INST (enc (instruction$SWI cond)) = swi_ex`,
  RW_TAC word_ss []);

val decode_enc_data_proc = Count.apply prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn r i.
      DECODE_INST (enc (f cond s rd rn (Dp_immediate r i))) = data_proc) /\
   (!cond s rd rn sh i.
      DECODE_INST (enc (f cond s rd rn (Dp_shift_immediate sh i))) =
        data_proc)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [addr_mode1_encode_def]);

val decode_enc_reg_shift = Count.apply prove(
  `!f cond s rd rn sh r.
       f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
    (DECODE_INST (enc (f cond s rd rn (Dp_shift_register sh r))) = reg_shift)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [addr_mode1_encode_def,shift_encode_def]);

val decode_enc_data_proc2 = prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn r i.
      DECODE_INST (enc (f cond rn (Dp_immediate r i))) = data_proc) /\
   (!cond rn sh i.
      DECODE_INST (enc (f cond rn (Dp_shift_immediate sh i))) = data_proc)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [addr_mode1_encode_def,shift_encode_def]);

val decode_enc_reg_shift2 = prove(
  `!f cond rn sh r.
       f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
    (DECODE_INST (enc (f cond rn (Dp_shift_register sh r))) = reg_shift)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [DECODE_INST,addr_mode1_encode_def,shift_encode_def]);

val decode_enc_data_proc3 = prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd r i.
      DECODE_INST (enc (f cond s rd (Dp_immediate r i))) = data_proc) /\
   (!cond s rd sh i.
      DECODE_INST (enc (f cond s rd (Dp_shift_immediate sh i))) = data_proc)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [addr_mode1_encode_def,shift_encode_def]);

val decode_enc_reg_shift3 = prove(
  `!f cond s rd sh r.
       f IN {instruction$MOV; instruction$MVN} ==>
    (DECODE_INST (enc (f cond s rd (Dp_shift_register sh r))) = reg_shift)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    \\ RW_TAC word_ss [addr_mode1_encode_def,shift_encode_def]);

val decode_enc_mla_mul = store_thm("decode_enc_mla_mul",
  `(!cond s rd rm rs.
      DECODE_INST (enc (instruction$MUL cond s rd rm rs)) = mla_mul) /\
   (!cond s rd rm rs rn.
      DECODE_INST (enc (instruction$MLA cond s rd rm rs rn)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_INST (enc (instruction$UMULL cond s rdhi rdlo rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_INST (enc (instruction$UMLAL cond s rdhi rdlo rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_INST (enc (instruction$SMULL cond s rdhi rdlo rm rs)) = mla_mul) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_INST (enc (instruction$SMLAL cond s rdhi rdlo rm rs)) = mla_mul)`,
  RW_TAC word_ss []);

val decode_enc_ldr_str = store_thm("decode_enc_ldr_str",
  `(!cond opt rd rn offset.
      DECODE_INST (enc (instruction$LDR cond opt rd rn offset)) = ldr) /\
   (!cond opt rd rn offset.
      DECODE_INST (enc (instruction$STR cond opt rd rn offset)) = str)`,
  REPEAT STRIP_TAC \\ Cases_on `offset` \\ TRY (Cases_on `s`)
    \\ RW_TAC word_ss [addr_mode2_encode_def,options_encode_def,
         shift_encode_def,word_modify_def]);

val decode_enc_ldm_stm = store_thm("decode_enc_ldm_stm",
  `(!cond opt rn list.
      DECODE_INST (enc (instruction$LDM cond opt rn list)) = ldm) /\
   (!cond opt rn list.
      DECODE_INST (enc (instruction$STM cond opt rn list)) = stm)`,
  RW_TAC word_ss [options_encode_def,word_modify_def]);

val decode_enc_swp = store_thm("decode_enc_swp",
  `!cond b rd rm rn. DECODE_INST (enc (instruction$SWP cond b rd rm rn)) = swp`,
  RW_TAC word_ss []);

val decode_enc_mrs = store_thm("decode_enc_mrs",
  `!cond r rd. (DECODE_INST (enc (instruction$MRS cond r rd)) = mrs_msr) /\
               ~(enc (instruction$MRS cond r rd) %% 21)`,
  RW_TAC word_ss []);

val decode_enc_msr = store_thm("decode_enc_msr",
  `!cond psrd op.
      (DECODE_INST (enc (instruction$MSR cond psrd op)) = mrs_msr) /\
      enc (instruction$MSR cond psrd op) %% 21`,
  REPEAT STRIP_TAC \\ Cases_on `psrd` \\ Cases_on `op`
    \\ RW_TAC word_ss [msr_psr_encode_def,msr_mode_encode_def]);

val decode_enc_coproc = store_thm("decode_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      DECODE_INST (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
      cdp_und) /\
   (!cond. DECODE_INST (enc (instruction$UND cond)) = cdp_und) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_INST (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) =
      mrc) /\
   (!cond cpn cop1 rd crn crm cop2.
      DECODE_INST (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) = mcr)`,
  RW_TAC word_ss []);

(* ......................................................................... *)

val word_ss =
  srw_ss()++ARITH_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss++
  rewrites [INDEX_RAND,word_or_def,word_index,w2w,word_lsl_def,
    word_bits_def,word_extract_def,condition_encode_lem,
    instruction_encode_def,shift_encode_lem,BIT_NUMERAL,BIT_ZERO];

val decode_br_enc = store_thm("decode_br_enc",
  `(!cond offset.
      DECODE_BRANCH (enc (instruction$B cond offset)) = (F, offset)) /\
   (!cond offset.
      DECODE_BRANCH (enc (instruction$BL cond offset)) = (T, offset))`,
  RW_TAC word_ss [DECODE_BRANCH_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,
         (SYM o EVAL) ``11 * 2 ** 24``,(SYM o EVAL) ``10 * 2 ** 24``]);

val shift_immediate_enc_lem = prove(
  `(!i r. w2w:word32->word8
    ((11 -- 7) (w2w (i:word5) << 7 !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8
    ((11 -- 7) (w2w (i:word5) << 7 !! 32w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8
    ((11 -- 7) (w2w (i:word5) << 7 !! 64w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8
    ((11 -- 7) (w2w (i:word5) << 7 !! 96w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word2 ((6 -- 5) (i << 7 !! w2w (r:word4))) = 0w) /\
   (!i r. w2w:word32->word2 ((6 -- 5) (i << 7 !! 32w !! w2w (r:word4))) = 1w) /\
   (!i r. w2w:word32->word2 ((6 -- 5) (i << 7 !! 64w !! w2w (r:word4))) = 2w) /\
   (!i r. w2w:word32->word2 ((6 -- 5) (i << 7 !! 96w !! w2w (r:word4))) = 3w) /\
   (!i r. w2w:word32->word4 ((3 -- 0) (i << 7 !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0) (i << 7 !! 32w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0) (i << 7 !! 64w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0) (i << 7 !! 96w !! w2w (r:word4))) = r)`,
  RW_TAC word_ss [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []);

val shift_immediate_enc_lem2 = prove(
  `(!i r. w2w:word32->word8 ((11 -- 7)
      (33554432w !! w2w (i:word5) << 7 !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8 ((11 -- 7)
      (33554432w !! w2w (i:word5) << 7 !! 32w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8 ((11 -- 7)
      (33554432w !! w2w (i:word5) << 7 !! 64w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word8 ((11 -- 7)
      (33554432w !! w2w (i:word5) << 7 !! 96w !! w2w (r:word4))) = w2w i) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (33554432w !! i << 7 !! w2w (r:word4))) = 0w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (33554432w !! i << 7 !! 32w !! w2w (r:word4))) = 1w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (33554432w !! i << 7 !! 64w !! w2w (r:word4))) = 2w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (33554432w !! i << 7 !! 96w !! w2w (r:word4))) = 3w) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (33554432w !! i << 7 !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (33554432w !! i << 7 !! 32w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (33554432w !! i << 7 !! 64w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (33554432w !! i << 7 !! 96w !! w2w (r:word4))) = r)`,
  RW_TAC word_ss [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []);

val shift_register_enc_lem = prove(
  `(!i r. w2w:word32->word4 ((11 -- 8)
      (16w !! w2w (i:word4) << 8 !! w2w (r:word4))) = i) /\
   (!i r. w2w:word32->word4 ((11 -- 8)
      (16w !! w2w (i:word4) << 8 !! 32w !! w2w (r:word4))) = i) /\
   (!i r. w2w:word32->word4 ((11 -- 8)
      (16w !! w2w (i:word4) << 8 !! 64w !! w2w (r:word4))) = i) /\
   (!i r. w2w:word32->word4 ((11 -- 8)
      (16w !! w2w (i:word4) << 8 !! 96w !! w2w (r:word4))) = i) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (16w !! i << 8 !! w2w (r:word4))) = 0w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (16w !! i << 8 !! 32w !! w2w (r:word4))) = 1w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (16w !! i << 8 !! 64w !! w2w (r:word4))) = 2w) /\
   (!i r. w2w:word32->word2 ((6 -- 5)
      (16w !! i << 8 !! 96w !! w2w (r:word4))) = 3w) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (16w !! i << 8 !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (16w !! i << 8 !! 32w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (16w !! i << 8 !! 64w !! w2w (r:word4))) = r) /\
   (!i r. w2w:word32->word4 ((3 -- 0)
      (16w !! i << 8 !! 96w !! w2w (r:word4))) = r)`,
  RW_TAC word_ss [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []);

val immediate_enc = store_thm("immediate_enc",
  `(!c r i. IMMEDIATE c ((11 >< 0) (addr_mode1_encode (Dp_immediate r i))) =
      arm$ROR (w2w i) (2w * w2w r) c) /\
    !c r i. IMMEDIATE c ((11 >< 0) (msr_mode_encode (Msr_immediate r i))) =
      arm$ROR (w2w i) (2w * w2w r) c`,
  RW_TAC (word_ss++boolSimps.LET_ss)
         [IMMEDIATE_def,addr_mode1_encode_def,msr_mode_encode_def]
    \\ (MATCH_MP_TAC (METIS_PROVE [] ``!a b c d x. (a = b) /\ (c = d) ==>
         (ROR a c x = ROR b d x)``)
    \\ STRIP_TAC << [ALL_TAC,
         MATCH_MP_TAC (PROVE [] ``!a b. (a = b) ==> (2w:word8 * a = 2w * b)``)]
    \\ RW_TAC word_ss [WORD_EQ]
    << [Cases_on `i' < 12` \\ ASM_SIMP_TAC word_ss []
        \\ Cases_on `i' < 8` \\ ASM_SIMP_TAC word_ss [],
      Cases_on `i' < 4` \\ ASM_SIMP_TAC word_ss []]
    \\ POP_ASSUM_LIST (ASSUME_TAC o hd)
    \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []));

val immediate_enc2 = store_thm("immediate_enc2",
  `!i. ((11 >< 0) (addr_mode2_encode (Dt_immediate i))):word12 = i`,
  RW_TAC word_ss [addr_mode2_encode_def,w2w]
    \\ Cases_on `i' < 12` \\ ASM_SIMP_TAC word_ss []);

val shift_immediate_enc = store_thm("shift_immediate_enc",
  `!reg m c sh i. SHIFT_IMMEDIATE reg m c
      ((11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i))) =
      if i = 0w then
        case sh of
           LSL Rm -> arm$LSL (REG_READ reg m Rm) 0w c
        || LSR Rm -> arm$LSR (REG_READ reg m Rm) 32w c
        || ASR Rm -> arm$ASR (REG_READ reg m Rm) 32w c
        || ROR Rm -> word_rrx(c, REG_READ reg m Rm)
      else
        case sh of
           LSL Rm -> arm$LSL (REG_READ reg m Rm) (w2w i) c
        || LSR Rm -> arm$LSR (REG_READ reg m Rm) (w2w i) c
        || ASR Rm -> arm$ASR (REG_READ reg m Rm) (w2w i) c
        || ROR Rm -> arm$ROR (REG_READ reg m Rm) (w2w i) c`,
  REPEAT STRIP_TAC \\ Cases_on `sh`
    \\ RW_TAC (srw_ss()++wordsLib.SIZES_ss++boolSimps.LET_ss)
        [SHIFT_IMMEDIATE_def,SHIFT_IMMEDIATE2_def,addr_mode1_encode_def,
         WORD_BITS_COMP_THM,shift_encode_def,w2w_w2w,word_extract_def,
         word_bits_w2w,shift_immediate_enc_lem,n2w_11]
    \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss)
        [EVAL ``w2w:word5->word8 0w``,word_0_n2w,w2n_w2w,GSYM w2n_11]);

val shift_immediate_enc2 = store_thm("shift_immediate_enc2",
  `!reg m c sh i. SHIFT_IMMEDIATE reg m c
      ((11 >< 0) (addr_mode2_encode (Dt_shift_immediate sh i))) =
      if i = 0w then
        case sh of
           LSL Rm -> arm$LSL (REG_READ reg m Rm) 0w c
        || LSR Rm -> arm$LSR (REG_READ reg m Rm) 32w c
        || ASR Rm -> arm$ASR (REG_READ reg m Rm) 32w c
        || ROR Rm -> word_rrx(c, REG_READ reg m Rm)
      else
        case sh of
           LSL Rm -> arm$LSL (REG_READ reg m Rm) (w2w i) c
        || LSR Rm -> arm$LSR (REG_READ reg m Rm) (w2w i) c
        || ASR Rm -> arm$ASR (REG_READ reg m Rm) (w2w i) c
        || ROR Rm -> arm$ROR (REG_READ reg m Rm) (w2w i) c`,
  REPEAT STRIP_TAC \\ Cases_on `sh`
    \\ RW_TAC (srw_ss()++wordsLib.SIZES_ss++boolSimps.LET_ss)
        [SHIFT_IMMEDIATE_def,SHIFT_IMMEDIATE2_def,addr_mode2_encode_def,
         WORD_BITS_COMP_THM,shift_encode_def,w2w_w2w,word_extract_def,
         word_bits_w2w,shift_immediate_enc_lem2,n2w_11]
    \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss)
        [EVAL ``w2w:word5->word8 0w``,word_0_n2w,w2n_w2w,GSYM w2n_11]);

val shift_register_enc = store_thm("shift_register_enc",
  `!reg m c sh r. SHIFT_REGISTER reg m c
      ((11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))) =
      let rs = (7 >< 0) (REG_READ reg m r) in
        case sh of
           LSL Rm -> arm$LSL (REG_READ (INC_PC reg) m Rm) rs c
        || LSR Rm -> arm$LSR (REG_READ (INC_PC reg) m Rm) rs c
        || ASR Rm -> arm$ASR (REG_READ (INC_PC reg) m Rm) rs c
        || ROR Rm -> arm$ROR (REG_READ (INC_PC reg) m Rm) rs c`,
  REPEAT STRIP_TAC \\ Cases_on `sh`
    \\ RW_TAC (srw_ss()++wordsLib.SIZES_ss++boolSimps.LET_ss)
        [SHIFT_REGISTER_def,SHIFT_REGISTER2_def,addr_mode1_encode_def,
         WORD_BITS_COMP_THM,shift_encode_def,w2w_w2w,word_extract_def,
         word_bits_w2w,shift_register_enc_lem,n2w_11]);

val shift_immediate_shift_register = store_thm("shift_immediate_shift_register",
  `(!reg m c sh r.
     ((11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))):word12 %% 4) /\
   (!reg m c sh i.
     ~(((11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i))):word12 %% 4))`,
  NTAC 6 STRIP_TAC \\ Cases_on `sh` \\ RW_TAC word_ss [addr_mode1_encode_def]);

val decode_data_proc_enc = Count.apply prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn r i.
      DECODE_DATAP (enc (f cond s rd rn (Dp_immediate r i))) =
      (T,decode_opcode (f cond s rd rn (Dp_immediate r i)),
       s,rn,rd,(11 >< 0) (addr_mode1_encode (Dp_immediate r i)))) /\
   (!cond s rd rn sh i.
      DECODE_DATAP (enc (f cond s rd rn (Dp_shift_immediate sh i))) =
      (F,decode_opcode (f cond s rd rn (Dp_shift_immediate sh i)),
       s,rn,rd,(11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i)))) /\
   (!cond s rd rn sh r.
      DECODE_DATAP (enc (f cond s rd rn (Dp_shift_register sh r))) =
      (F,decode_opcode (f cond s rd rn (Dp_shift_register sh r)),
       s,rn,rd,(11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))))`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [decode_opcode_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ RW_TAC word_ss [DECODE_DATAP_def,addr_mode1_encode_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,(SYM o EVAL) ``256 * 2 ** 12``]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_data_proc_enc2 = Count.apply prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn r i.
      DECODE_DATAP (enc (f cond rn (Dp_immediate r i))) =
      (T,decode_opcode (f cond rn (Dp_immediate r i)),
       T,rn,0w,(11 >< 0) (addr_mode1_encode (Dp_immediate r i)))) /\
   (!cond rn sh i.
      DECODE_DATAP (enc (f cond rn (Dp_shift_immediate sh i))) =
      (F,decode_opcode (f cond rn (Dp_shift_immediate sh i)),
       T,rn,0w,(11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i)))) /\
   (!cond rn sh r.
      DECODE_DATAP (enc (f cond rn (Dp_shift_register sh r))) =
      (F,decode_opcode (f cond rn (Dp_shift_register sh r)),
       T,rn,0w,(11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))))`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [decode_opcode_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ RW_TAC word_ss [DECODE_DATAP_def,addr_mode1_encode_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,(SYM o EVAL) ``256 * 2 ** 12``]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_data_proc_enc3 = Count.apply prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd r i.
      DECODE_DATAP (enc (f cond s rd (Dp_immediate r i))) =
      (T,decode_opcode (f cond s rd (Dp_immediate r i)),
       s,0w,rd,(11 >< 0) (addr_mode1_encode (Dp_immediate r i)))) /\
   (!cond s rd sh i.
      DECODE_DATAP (enc (f cond s rd (Dp_shift_immediate sh i))) =
      (F,decode_opcode (f cond s rd (Dp_shift_immediate sh i)),
       s,0w,rd,(11 >< 0) (addr_mode1_encode (Dp_shift_immediate sh i)))) /\
   (!cond s rd sh r.
      DECODE_DATAP (enc (f cond s rd (Dp_shift_register sh r))) =
      (F,decode_opcode (f cond s rd (Dp_shift_register sh r)),
       s,0w,rd,(11 >< 0) (addr_mode1_encode (Dp_shift_register sh r))))`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [decode_opcode_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ RW_TAC word_ss [DECODE_DATAP_def,addr_mode1_encode_def]
    \\ ASM_SIMP_TAC bool_ss [BIT_SHIFT_THM3,(SYM o EVAL) ``256 * 2 ** 12``]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_mla_mul_enc = store_thm("decode_mla_mul_enc",
  `(!cond s rd rm rs.
      DECODE_MLA_MUL (enc (instruction$MUL cond s rd rm rs)) =
      (F,F,F,s,rd,0w,rs,rm)) /\
   (!cond s rd rm rs rn.
      DECODE_MLA_MUL (enc (instruction$MLA cond s rd rm rs rn)) =
      (F,F,T,s,rd,rn,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$UMULL cond s rdhi rdlo rm rs)) =
      (T,F,F,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$UMLAL cond s rdhi rdlo rm rs)) =
      (T,F,T,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$SMULL cond s rdhi rdlo rm rs)) =
      (T,T,F,s,rdhi,rdlo,rs,rm)) /\
   (!cond s rdhi rdlo rm rs.
      DECODE_MLA_MUL (enc (instruction$SMLAL cond s rdhi rdlo rm rs)) =
      (T,T,T,s,rdhi,rdlo,rs,rm))`,
  REPEAT STRIP_TAC \\ RW_TAC word_ss [DECODE_MLA_MUL_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_ldr_str_enc = Count.apply store_thm("decode_ldr_str_enc",
  `(!cond opt rd rn i.
      DECODE_LDR_STR (enc (instruction$LDR cond opt rd rn (Dt_immediate i))) =
      (F, opt.Pre, opt.Up, opt.BSN, opt.Wb, T, rn, rd,
       (11 >< 0) (addr_mode2_encode (Dt_immediate i)))) /\
   (!cond opt rd rn sh i.
      DECODE_LDR_STR (enc (instruction$LDR cond opt rd rn
          (Dt_shift_immediate sh i))) =
      (T, opt.Pre, opt.Up, opt.BSN, opt.Wb, T, rn, rd,
        (11 >< 0) (addr_mode2_encode (Dt_shift_immediate sh i)))) /\
   (!cond opt rd rn i.
      DECODE_LDR_STR (enc (instruction$STR cond opt rd rn (Dt_immediate i))) =
      (F, opt.Pre, opt.Up, opt.BSN, opt.Wb, F, rn, rd,
       (11 >< 0) (addr_mode2_encode (Dt_immediate i)))) /\
   (!cond opt rd rn sh i.
      DECODE_LDR_STR (enc (instruction$STR cond opt rd rn
          (Dt_shift_immediate sh i))) =
      (T, opt.Pre, opt.Up, opt.BSN, opt.Wb, F, rn, rd,
        (11 >< 0) (addr_mode2_encode (Dt_shift_immediate sh i))))`,
  REPEAT STRIP_TAC \\ TRY (Cases_on `sh`)
    \\ RW_TAC word_ss [DECODE_LDR_STR_def,addr_mode2_encode_def,
         options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_ldm_stm_enc = store_thm("decode_ldm_stm_enc",
  `(!cond opt rn l.
      DECODE_LDM_STM (enc (instruction$LDM cond opt rn l)) =
      (opt.Pre, opt.Up, opt.BSN, opt.Wb, T, rn, l)) /\
   (!cond opt rn l.
      DECODE_LDM_STM (enc (instruction$STM cond opt rn l)) =
      (opt.Pre, opt.Up, opt.BSN, opt.Wb, F, rn, l))`,
  RW_TAC word_ss [DECODE_LDM_STM_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

val decode_swp_enc = store_thm("decode_swp_enc",
  `!cond b rd rm rn.
      DECODE_SWP (enc (instruction$SWP cond b rd rm rn)) = (b,rn,rd,rm)`,
  RW_TAC word_ss [DECODE_SWP_def] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []);

val decode_mrs_enc = store_thm("decode_mrs_enc",
  `!cond r rd. DECODE_MRS (enc (instruction$MRS cond r rd)) = (r, rd)`,
  RW_TAC word_ss [DECODE_MRS_def]
    \\ ASM_SIMP_TAC (bool_ss++ARITH_ss) [BIT_SHIFT_THM3,
         (SYM o EVAL) ``271 * 2 ** 16``,(SYM o EVAL) ``335 * 2 ** 16``]);

val decode_msr_enc = store_thm("decode_msr_enc",
  `(!cond psrd rot imm.
      DECODE_MSR (enc (instruction$MSR cond psrd (Msr_immediate rot imm))) =
        let (r,bit19,bit16) = DECODE_PSRD psrd
        and opnd = (11 >< 0) (msr_mode_encode (Msr_immediate rot imm)) in
          (T,r,bit19,bit16,(3 >< 0) opnd,opnd)) /\
    !cond psrd rm.
      DECODE_MSR (enc (instruction$MSR cond psrd (Msr_register rm))) =
        let (r,bit19,bit16) = DECODE_PSRD psrd
        and opnd = (11 >< 0) (msr_mode_encode (Msr_register rm)) in
          (F,r,bit19,bit16,rm,opnd)`,
  REPEAT STRIP_TAC \\ Cases_on `psrd`
    \\ RW_TAC (word_ss++boolSimps.LET_ss) [DECODE_MSR_def,DECODE_PSRD_def,
         msr_psr_encode_def,msr_mode_encode_def]
    \\ ASM_SIMP_TAC (bool_ss++ARITH_ss) [BIT_SHIFT_THM3,
         (SYM o EVAL) ``4623 * 2 ** 12``, (SYM o EVAL) ``1168 * 2 ** 12``,
         (SYM o EVAL) ``1152 * 2 ** 12``, (SYM o EVAL) ``1040 * 2 ** 12``,
         (SYM o EVAL) ``144 * 2 ** 12``, (SYM o EVAL) ``128 * 2 ** 12``,
         (SYM o EVAL) ``16 * 2 ** 12``]);

val decode_mrc_enc = store_thm("decode_mrc_enc",
  `!cond cpn cop1 rd crn crm cop2.
      (15 >< 12) (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) = rd`,
  RW_TAC word_ss [] \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ ASM_SIMP_TAC word_ss []);

val decode_ldc_stc_enc = store_thm("decode_ldc_stc_enc",
  `(!cond opt cpn crd rn offset.
      DECODE_LDC_STC (enc (instruction$LDC cond opt cpn crd rn offset)) =
      (opt.Pre, opt.Up, opt.Wb, T, rn, offset)) /\
   (!cond opt cpn crd rn offset.
      DECODE_LDC_STC (enc (instruction$STC cond opt cpn crd rn offset)) =
      (opt.Pre, opt.Up, opt.Wb, F, rn, offset))`,
  RW_TAC word_ss [DECODE_LDC_STC_def,options_encode_def,word_modify_def]
    \\ FULL_SIMP_TAC std_ss [LESS_THM] \\ ASM_SIMP_TAC word_ss []);

(* ......................................................................... *)

val BITS_ZERO5 = prove(
  `!h l n.  n < 2 ** l ==> (BITS h l n = 0)`,
  RW_TAC arith_ss [BITS_THM,LESS_DIV_EQ_ZERO,ZERO_LT_TWOEXP]);

val BITS_w2n_ZERO = prove(
  `!w: bool ** 'a. dimindex (:'a) <= l ==> (BITS h l (w2n w) = 0)`,
  METIS_TAC [dimword_def,TWOEXP_MONO2,LESS_LESS_EQ_TRANS,BITS_ZERO5,w2n_lt]);

val WORD_BITS_LSL = prove(
  `!h l n w:bool ** 'a.
      n <= h /\ n <= l /\ l <= h /\ h < dimindex (:'a) ==>
      ((h -- l) (w << n) = ((h - n) -- (l - n)) w)`,
  RW_TAC (arith_ss++fcpLib.FCP_ss) [WORD_EQ,word_lsl_def,word_bits_def]
    \\ Cases_on `i + l < dimindex (:'a)`
    \\ FULL_SIMP_TAC (arith_ss++fcpLib.FCP_ss) [NOT_LESS_EQUAL,NOT_LESS]);

val condition_code_lem = prove(
  `!cond. condition_encode cond %% 28 = cond IN {NE;CC;PL;VC;LS;LT;LE;NV}`,
  Cases \\ RW_TAC (std_ss++wordsLib.SIZES_ss++
     pred_setSimps.PRED_SET_ss++BITS_NUMERAL_ss)
   [BIT_def,condition2num_thm,word_rol_def,word_ror_n2w,word_lsl_n2w,
    w2w_n2w,word_index,condition_encode_def]);

val condition_code_lem2 = prove(
  `!cond. ~(condition_encode cond %% 28) = cond IN {EQ;CS;MI;VS;HI;GE;GT;AL}`,
  Cases \\ SIMP_TAC (srw_ss()++pred_setSimps.PRED_SET_ss) [condition_code_lem]);

val condition_code_lem =
  SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] condition_code_lem;

val condition_code_lem2 =
  SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] condition_code_lem2;

val condition_code_lem3 = prove(
  `!cond. num2condition (w2n ((31 -- 29) (condition_encode cond))) =
      case cond of
         EQ -> EQ || NE -> EQ || CS -> CS || CC -> CS
      || MI -> MI || PL -> MI || VS -> VS || VC -> VS
      || HI -> HI || LS -> HI || GE -> GE || LT -> GE
      || GT -> GT || LE -> GT || AL -> AL || NV -> AL`,
  Cases \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss++
       boolSimps.LET_ss++BITS_NUMERAL_ss)
    [condition_encode_def,condition2num_thm,num2condition_thm,word_bits_n2w,
     word_rol_def,word_ror_n2w,word_lsl_n2w,w2w_n2w,w2n_n2w]);

val word_ss = srw_ss()++fcpLib.FCP_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss++
  rewrites [word_or_def,word_index,w2w,word_lsl_def,word_bits_def,
    shift_encode_lem,BIT_def];

val pass_ss =
 (srw_ss()++ARITH_ss++wordsLib.SIZES_ss++BITS_NUMERAL_ss++boolSimps.LET_ss) ++
 rewrites [CONDITION_PASSED_def,CONDITION_PASSED2_def,CONDITION_PASSED3_def,
   GSYM WORD_BITS_OVER_BITWISE,WORD_OR_CLAUSES,BITS_w2n_ZERO,WORD_BITS_LSL,
   word_bits_n2w,w2w_def,instruction_encode_def,condition_code_lem3];

val condition_addr_mode1 = prove(
  `(!op2. (31 -- 29) (addr_mode1_encode op2) = 0w) /\
    !op2. ~((addr_mode1_encode op2) %% 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2` \\ TRY (Cases_on `s`)
    \\ RW_TAC pass_ss [addr_mode1_encode_def,shift_encode_def]
    \\ SIMP_TAC word_ss [BITS_w2n_ZERO]);

val condition_addr_mode2 = prove(
  `(!op2. (31 -- 29) (addr_mode2_encode op2) = 0w) /\
    !op2. ~((addr_mode2_encode op2) %% 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2` \\ TRY (Cases_on `s`)
    \\ RW_TAC pass_ss [addr_mode2_encode_def,shift_encode_def]
    \\ SIMP_TAC word_ss [BITS_w2n_ZERO]);

val condition_msr_mode = prove(
  `(!op2. (31 -- 29) (msr_mode_encode op2) = 0w) /\
    !op2. ~((msr_mode_encode op2) %% 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `op2`
    \\ RW_TAC pass_ss [msr_mode_encode_def]
    \\ SIMP_TAC word_ss [BITS_w2n_ZERO]);

val condition_msr_psr = prove(
  `(!psrd. (31 -- 29) (msr_psr_encode psrd) = 0w) /\
    !psrd. ~((msr_psr_encode psrd) %% 28)`,
  NTAC 2 STRIP_TAC \\ Cases_on `psrd`
    \\ RW_TAC pass_ss [msr_psr_encode_def]
    \\ SIMP_TAC word_ss []);

val condition_options = prove(
  `(!opt. (31 -- 29) (options_encode opt) = 0w) /\
    !opt. ~((options_encode opt) %% 28)`,
  NTAC 2 STRIP_TAC \\ RW_TAC pass_ss [options_encode_def,word_modify_def]
    \\ RW_TAC word_ss [] \\ Cases_on `i + 29 < 32`
    \\ RW_TAC (word_ss++ARITH_ss) []);

val PASS_TAC = REPEAT STRIP_TAC \\ Cases_on_nzcv `flgs`
  \\ RW_TAC pass_ss [condition_addr_mode1,condition_addr_mode2,
       condition_msr_mode,condition_msr_psr,condition_options]
  \\ FULL_SIMP_TAC word_ss [BITS_w2n_ZERO,condition_addr_mode1,
       condition_addr_mode2,condition_msr_mode,condition_msr_psr,
       condition_options]
  \\ RULE_ASSUM_TAC (REWRITE_RULE [condition_code_lem2])
  \\ FULL_SIMP_TAC (srw_ss()) [condition_code_lem];

(* ......................................................................... *)

val cond_pass_enc_br = store_thm("cond_pass_enc_br",
  `(!cond flgs offset.
      CONDITION_PASSED flgs (enc (instruction$B cond offset)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond flgs offset.
      CONDITION_PASSED flgs (enc (instruction$BL cond offset)) =
      CONDITION_PASSED3 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_swi = store_thm("cond_pass_enc_swi",
  `!cond flgs. CONDITION_PASSED flgs (enc (instruction$SWI cond)) =
               CONDITION_PASSED3 flgs cond`,
  PASS_TAC);

val cond_pass_enc_data_proc = prove(
  `!f. f IN {instruction$AND; instruction$EOR;
             instruction$SUB; instruction$RSB;
             instruction$ADD; instruction$ADC;
             instruction$SBC; instruction$RSC;
             instruction$ORR; instruction$BIC} ==>
   (!cond s rd rn op2.
      CONDITION_PASSED flgs (enc (f cond s rd rn op2)) =
      CONDITION_PASSED3 flgs cond)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] \\ PASS_TAC);

val cond_pass_enc_data_proc2 = prove(
  `!f. f IN {instruction$TST; instruction$TEQ;
             instruction$CMP; instruction$CMN} ==>
   (!cond rn op2.
      CONDITION_PASSED flgs (enc (f cond rn op2)) =
      CONDITION_PASSED3 flgs cond)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] \\ PASS_TAC);

val cond_pass_enc_data_proc3 = prove(
  `!f. f IN {instruction$MOV; instruction$MVN} ==>
   (!cond s rd op2.
      CONDITION_PASSED flgs (enc (f cond s rd op2)) =
      CONDITION_PASSED3 flgs cond)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] \\ PASS_TAC);

val cond_pass_enc_mla_mul = store_thm("cond_pass_enc_mla_mul",
  `(!cond s rd rm rs.
      CONDITION_PASSED flgs (enc (instruction$MUL cond s rd rm rs)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond s rd rm rs rn.
      CONDITION_PASSED flgs (enc (instruction$MLA cond s rd rm rs rn)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$UMULL cond s rdhi rdlo rm rs)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$UMLAL cond s rdhi rdlo rm rs)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$SMULL cond s rdhi rdlo rm rs)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond s rdhi rdlo rm rs.
      CONDITION_PASSED flgs (enc (instruction$SMLAL cond s rdhi rdlo rm rs)) =
      CONDITION_PASSED3 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_ldr_str = store_thm("cond_pass_enc_ldr_str",
  `(!cond opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$LDR cond opt rd rn offset)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond opt rd rn offset.
      CONDITION_PASSED flgs (enc (instruction$STR cond opt rd rn offset)) =
      CONDITION_PASSED3 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_ldm_stm = store_thm("cond_pass_enc_ldm_stm",
  `(!cond opt rn list.
      CONDITION_PASSED flgs (enc (instruction$LDM cond opt rn list)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond opt rn list.
      CONDITION_PASSED flgs (enc (instruction$STM cond opt rn list)) =
      CONDITION_PASSED3 flgs cond)`,
  PASS_TAC);

val cond_pass_enc_swp = store_thm("cond_pass_enc_swp",
  `!cond b rd rm rn.
      CONDITION_PASSED flgs (enc (instruction$SWP cond b rd rm rn)) =
      CONDITION_PASSED3 flgs cond`,
  PASS_TAC);

val cond_pass_enc_mrs = store_thm("cond_pass_enc_mrs",
  `!cond r rd.
      CONDITION_PASSED flgs (enc (instruction$MRS cond r rd)) =
      CONDITION_PASSED3 flgs cond`,
  PASS_TAC);

val cond_pass_enc_msr = store_thm("cond_pass_enc_msr",
  `!cond psrd op.
      CONDITION_PASSED flgs (enc (instruction$MSR cond psrd op)) =
      CONDITION_PASSED3 flgs cond`,
  PASS_TAC);

val cond_pass_enc_coproc = store_thm("cond_pass_enc_coproc",
  `(!cond cpn cop1 crd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$CDP cond cpn cop1 crd crn crm cop2)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond. CONDITION_PASSED flgs (enc (instruction$UND cond)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond cpn cop1 rd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$MRC cond cpn cop1 rd crn crm cop2)) =
      CONDITION_PASSED3 flgs cond) /\
   (!cond cpn cop1 rd crn crm cop2.
      CONDITION_PASSED flgs
        (enc (instruction$MCR cond cpn cop1 rd crn crm cop2)) =
      CONDITION_PASSED3 flgs cond)`,
  PASS_TAC);

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

val decode_enc_reg_shift = save_thm("decode_enc_reg_shift",
  MAP_SPEC decode_enc_reg_shift opc1);

val decode_enc_reg_shift2 = save_thm("decode_enc_reg_shift2",
  MAP_SPEC decode_enc_reg_shift2 opc2);

val decode_enc_reg_shift3 = save_thm("decode_enc_reg_shift3",
  MAP_SPEC decode_enc_reg_shift3 opc3);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();

(* ------------------------------------------------------------------------- *)

(*
val ABS_ARMe_def = Define`
  ABS_ARMe state  =
     ARM_EX (ARM state.registers state.psrs)
       (state.memory (ADDR30 (FETCH_PC state.registers)))
       (if state.undefined then undefined else software)`;

val ABS_STRMe_def = Define`
  ABS_STRMe a t =
    let s0 = STATE_ARMe t a and s1 = STATE_ARMe (SUC t) a in
      (if s1.undefined then SOME Undef else NONE, T,
       s1.memory (ADDR30 (FETCH_PC s1.registers)),
       SND (TRANSFERS s0.memory [] (OUT_ARM (ABS_ARMe s0))))`;

val trans = GEN_ALL o SIMP_CONV (srw_ss()) [SNOC,HD,TRANSFERS_def];
val TRANSFER_LDR = trans ``TRANSFERS mem [] [MemRead a]``;
val TRANSFER_STR = trans ``TRANSFERS mem [] [MemWrite b a d]``;
val TRANSFER_SWP = trans ``TRANSFERS mem [] [MemRead a; MemWrite b a2 d]``;
val alu_nchotomy = METIS_PROVE [pairTheory.ABS_PAIR_THM]
  ``!a. ?n z c v r. (a:(bool # bool # bool # bool) # word32) = ((n,z,c,v),r)``;

fun Cases_on_alu tm = SPEC_THEN tm FULL_STRUCT_CASES_TAC alu_nchotomy;

val DECODE_INST_LDM = store_thm("DECODE_INST_LDM",
  `!i. (DECODE_INST i = ldm) ==> i %% 20`,
  RW_TAC arith_ss [DECODE_INST_def]);

val DECODE_INST_STM = store_thm("DECODE_INST_STM",
  `!i. (DECODE_INST i = stm) ==> ~(i %% 20)`,
  RW_TAC arith_ss [DECODE_INST_def]);

val ARMe_CORRECT = Count.apply store_thm("ARMe_CORRECT",
  `!t a. ABS_ARMe (STATE_ARMe t a) =
         STATE_ARM t <| state := ABS_ARMe a; inp := ABS_STRMe a |>`,
  Induct \\ STRIP_TAC \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [STATE_ARM_def,STATE_ARMe_def,ABS_STRMe_def]
    \\ POP_ASSUM (SUBST1_TAC o SYM o SPEC `a`)
    \\ ABBREV_TAC `s = STATE_ARMe t a`
    \\ ABBREV_TAC `ns = NEXT_ARMe s` \\ POP_ASSUM MP_TAC
    \\ ABBREV_TAC `ireg = s.memory (ADDR30 (FETCH_PC s.registers))`
    \\ ABBREV_TAC `mode = DECODE_MODE ((4 >< 0) (CPSR_READ s.psrs))`
    \\ SIMP_TAC (srw_ss()++armLib.PBETA_ss++boolSimps.LET_ss)
         [IS_Reset_def,IS_Dabort_def,ABS_ARMe_def,OUT_ARM_def,DECODE_PSR_def,
          NEXT_ARMe_def,NEXT_ARM_def]
    \\ Cases_on `s.undefined`
    \\ ASM_SIMP_TAC (srw_ss()) [CONJUNCT1 TRANSFERS_def]
    << [
      SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
             [EXEC_INST_def,EXCEPTION_def]
        \\ STRIP_TAC \\ UNABBREV_TAC `ns`
        \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
             [PROJ_IF_FLAGS_def,interrupt2exceptions_def],
       Tactical.REVERSE
        (Cases_on `CONDITION_PASSED (NZCV (CPSR_READ s.psrs)) ireg`)
        \\ ASM_SIMP_TAC (srw_ss()) [CONJUNCT1 TRANSFERS_def]
        << [
          ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [EXEC_INST_def,DECODE_PSR_def]
            \\ STRIP_TAC \\ UNABBREV_TAC `ns`
            \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [PROJ_IF_FLAGS_def,interrupt2exceptions_def],
          Cases_on `DECODE_INST ireg`
            \\ MAP_EVERY IMP_RES_TAC [DECODE_INST_LDM,DECODE_INST_STM]
            \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
              [EXEC_INST_def,NEXT_ARM_def,EXCEPTION_def,PROJ_IF_FLAGS_def,
               IS_Reset_def,IS_Dabort_def,DECODE_PSR_def,
               TRANSFER_LDR,TRANSFER_STR,TRANSFER_SWP,
               LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def,
               LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def,
               SWP_def,DECODE_SWP_def,MLA_MUL_def,DECODE_MLA_MUL_def,
               MRS_def,DECODE_MRS_def,MSR_def,DECODE_MSR_def,
               DATA_PROCESSING_def,ADDR_MODE1_def,
               BRANCH_def,DECODE_BRANCH_def]
            \\ TRY (PAT_ABBREV_TAC `alu = ALU opc rn op2 c` \\
                    Cases_on_alu `alu`)
            \\ STRIP_TAC \\ UNABBREV_TAC `ns`
            \\ RW_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [PROJ_IF_FLAGS_def,DECODE_PSR_def,interrupt2exceptions_def]
            \\ FULL_SIMP_TAC (srw_ss()) []]]);
*)
