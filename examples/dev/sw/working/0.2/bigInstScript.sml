(*
quietdec := true;

app load ["arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "whileTheory", "finite_mapTheory", 
          "listTheory", "pred_setSimps", "pred_setTheory", "preARMTheory", "CFLTheory", "simplifier"];

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory whileTheory 
       listTheory pred_setSimps pred_setTheory finite_mapTheory preARMTheory CFLTheory simplifier;

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory whileTheory
       listTheory pred_setSimps pred_setTheory finite_mapTheory preARMTheory CFLTheory simplifier;

(*---------------------------------------------------------------------------------*)
(*   This theory is about stack-involved big instructions including:               *)
(*     1. push_list: push the values of a list of expression into the stack        *)
(*     2. pop_list:  pop the values of a list of expression from the stack         *)
(*     3. copy_list: copy the values of a list of expression to another list       *)
(*                   through the stack                                             *)
(*     4. sr_list:   save the values of a list of expression into the stack first, *)
(*                   then restore them later                                       *)
(*                                                                                 *)
(*     For each big instruction, a sanity theorem shows which expressions will keep*)
(*         their values unchanged; a functionality theorem shows that how the      *)
(*         values of affected expressions are changed.                             *)
(*                                                                                 *)
(*     An expression could be a register variable, a constant or a stack variable  *)
(*     since these instructions are mainly used by function calls (e.g. parameters *)
(*     passing), heap variables are not taken into account since they shouldn't be *)
(*     transferred through the stack                                               *)
(*---------------------------------------------------------------------------------*)

val _ = new_theory "bigInst";

(*---------------------------------------------------------------------------------*)
(*         Expressions                                                             *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype `
    CFL_EXP = isR of num            (* registers *)
         | isC of word32            (* constants *)
         | isV of num               (* stack variables *)
         | isM of num               (* memory locations *)
    `;

val reade_def = Define `
    (reade st (isR r) = read st (REG r)) /\
    (reade st (isC c) = c) /\
    (reade st (isV k) = read st (MEM (fp, NEG k))) /\
    (reade st (isM m) = (SND st) ' m)
  `;

val writee_def = Define `
    (writee st (isR r, v) = write st (REG r) v) /\
    (writee st (isC c, v) = st) /\
    (writee st (isV k, v) = write st (MEM (fp, NEG k)) v) /\
    (writee st (isM m, v) = (FST st, (SND st) |+ (m, v)))
  `;

val _ = overload_on ("''", ``reade``);
val _ = overload_on ("|#", ``writee``);
val _ = set_fixity "''"  (Infixl 500);   (* dstate apply *)
val _ = set_fixity "|#"  (Infixl 600);   (* dstate update *)


val addr_of_def = Define `
    (addr_of st (isM m) = m) /\
    (addr_of st (isV v) = w2n (read st FP) -  v)`; 

val eq_addr_def = Define `
    eq_addr st addr1 addr2 =
         (addr_of st addr1 = addr_of st addr2)`; 


val eq_exp_def = Define `
    (eq_exp st (isR r1) (isR r2) = (r1 = r2)) /\  
    (eq_exp st (isC c1) (isC c2) = (c1 = c2)) /\
    (eq_exp st (isV v1) (isV v2) = eq_addr st (isV v1) (isV v2)) /\
    (eq_exp st (isM m1) (isM m2) = eq_addr st (isM m1) (isM m2)) /\
    (eq_exp st (isM m) (isV v) = eq_addr st (isM m) (isV v)) /\
    (eq_exp st (isV v) (isM m) = eq_addr st (isV v) (isM m)) /\
    (eq_exp st (isR r) (isV v) = (r = fp)) /\
    (eq_exp st (isV v) (isR r) = (r = fp)) /\
    (eq_exp st _ _ = F)
    `;

val eq_exp_def = Define `
    (eq_exp st (isR r1) (isR r2) = (r1 = r2)) /\  
    (eq_exp st (isC c1) (isC c2) = (c1 = c2)) /\
    (eq_exp st (isV v1) (isV v2) = eq_addr st (isV v1) (isV v2)) /\
    (eq_exp st (isM m1) (isM m2) = eq_addr st (isM m1) (isM m2)) /\
    (eq_exp st (isM m) (isV v) = eq_addr st (isM m) (isV v)) /\
    (eq_exp st (isV v) (isM m) = eq_addr st (isV v) (isM m)) /\
    (eq_exp st _ _ = F)
    `;

val is_C_def = Define `
    (is_C (isC c) = T) /\
    (is_C _ = F)`;

val eq_exp_SYM = Q.store_thm (
    "eq_exp_SYM",
    `!st e1 e2. eq_exp st e1 e2 = eq_exp st e2 e1`,
    Cases_on `e1` THEN Cases_on `e2` THEN
    RW_TAC std_ss [eq_exp_def, eq_addr_def] THEN
    METIS_TAC []
   );

val NOT_EQ_isR_LEM = Q.store_thm (
    "NOT_EQ_isR_LEM",
    `!e r. ~(e = isR r) = (!st. ~(eq_exp st (isR r) e))`,
    Cases_on `e` THEN
    RW_TAC std_ss [eq_exp_def] THEN
    METIS_TAC []
   );

(*---------------------------------------------------------------------------------*)
(*      Different ways to restrict an expression                                   *)
(*---------------------------------------------------------------------------------*)
 
val valid_regs_def = Define `
    (valid_regs r = 
        ~(r=9) /\ ~(r=10) /\ ~(r=11) /\ ~(r=12) /\ ~(r=13) /\ ~(r=14) /\ ~(r=15) /\
       (index_of_reg (from_reg_index r) = r)) /\
    (valid_regs _ = T)`;

val valid_regs_lem = Q.store_thm (
    "valid_regs_lem",
    `!r. valid_regs r ==>
       ~(r=13) /\  ~(r=9) /\ ~(r=11) /\
       (index_of_reg (from_reg_index r) = r)`,
    RW_TAC arith_ss [valid_regs_def]
  );

val valid_exp_def = Define `
    (valid_exp (isR r) = valid_regs r) /\ 
    (valid_exp (isM m) = F) /\
    (valid_exp _ = T)`;

val valid_exp_1_def = Define `
    (valid_exp_1 (isR r) = ~(r = 13) /\ ~(r = 9) /\ (index_of_reg (from_reg_index r) = r)) /\ 
    (valid_exp_1 (isM m) = T) /\
    (valid_exp_1 _ = T)`;

val valid_exp_2_def = Define `
    (valid_exp_2 (isR r) = valid_regs r) /\ 
    (valid_exp_2 (isM m) = T) /\
    (valid_exp_2 _ = T)`;

val valid_exp_3_def = Define `
    (valid_exp_3 (isR r) = (index_of_reg (from_reg_index r) = r)) /\
    (valid_exp_3 (isM m) = F) /\
    (valid_exp_3 _ = T)`;

val valid_exp_thm = Q.store_thm (
    "valid_exp_thm",
    `!e. valid_exp e ==> valid_exp_1 e /\ valid_exp_2 e /\ valid_exp_3 e`,
    Cases_on `e` THEN RW_TAC std_ss [valid_exp_1_def, valid_exp_2_def, valid_exp_3_def, valid_exp_def, valid_regs_lem]
  );

val VALID_EXP_LEM = Q.store_thm (
    "VALID_EXP_LEM",
    `!l. EVERY valid_exp l ==> EVERY valid_exp_1 l /\ EVERY valid_exp_2 l /\ EVERY valid_exp_3 l`,
    Induct_on `l` THEN SIMP_TAC list_ss [] THEN
    RW_TAC std_ss [valid_exp_thm]
  );

(*---------------------------------------------------------------------------------*)
(*         Theorems about expressions                                              *)
(*---------------------------------------------------------------------------------*)

val READE_WRITEE = Q.store_thm (
    "READE_WRITEE",
    `!st e v. ~(is_C e) ==> (st |# (e,v) '' e = v)`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    Cases_on `e` THEN
    RW_TAC finmap_ss [is_C_def, reade_def, writee_def, read_thm, write_thm] THEN
    Cases_on `p` THEN Cases_on `r` THEN
    RW_TAC finmap_ss [read_thm, write_thm]
  );

val READE_WRITEE_THM = Q.store_thm (
    "READE_WRITEE_THM",
    `!st e v. ~(is_C e1) /\ valid_exp e1 ==> ((st |# (e1,v) '' e2 = if eq_exp st e1 e2 then v else st '' e2))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    Cases_on `e1` THEN Cases_on `e2` THEN
    RW_TAC std_ss [is_C_def, reade_def, writee_def, read_thm, write_thm, eq_exp_def, eq_addr_def] THEN
    FULL_SIMP_TAC finmap_ss [valid_exp_def, valid_regs_def, fp_def, addr_of_def, FP_def, read_thm]
  );

val READE_WRITEE_THM_2 = Q.store_thm (
    "READE_WRITEE_THM_2",
    `!st e v. ~(eq_exp st e1 e2) /\ ~(e1 = isR fp) ==> ((st |# (e1,v) '' e2 = st '' e2))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    Cases_on `e1` THEN Cases_on `e2` THEN
    RW_TAC std_ss [reade_def, writee_def, read_thm, write_thm, eq_exp_def, eq_addr_def] THEN
    FULL_SIMP_TAC finmap_ss [fp_def, addr_of_def, FP_def, read_thm]
  );

val WRITEE_EQ = Q.store_thm (
    "WRITEE_EQ",
    `!st e v1 v2. st |# (e,v1) |# (e,v2) = st |# (e,v2)`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    Cases_on `e` THEN
    RW_TAC finmap_ss [reade_def, writee_def, read_thm, write_thm]
  );

val WRITEE_COMMUTES = Q.store_thm (
    "WRITEE_COMMUTES",
    `!st e1 e2 v1 v2. ~(eq_exp st e1 e2) /\ valid_exp e1 /\ valid_exp e2
          ==> (st |# (e1,v1) |# (e2,v2) = st |# (e2,v2) |# (e1,v1))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    Cases_on `e1` THEN  Cases_on `e2` THEN
    RW_TAC finmap_ss [valid_exp_def, valid_regs_lem, eq_exp_def, eq_addr_def, addr_of_def, reade_def, writee_def, 
            read_thm, write_thm, FUPDATE_COMMUTES, FP_def, fp_def]
  );

(*---------------------------------------------------------------------------------*)
(*      Sufficient stack space is required                                         *)
(*      Indicated by the value of sp                                               *)
(*---------------------------------------------------------------------------------*)

val locate_ge_def = Define `
    locate_ge (x:word32) (k:num) =
      k <= w2n x`;

val w2n_sub_lem = Q.store_thm (
    "w2n_sub_lem",
    `w2n i <= w2n k ==>
      (w2n (k - i) = w2n k - w2n i)`,
    RW_TAC std_ss [word_sub_def, word_add_def, w2n_n2w, word_2comp_def] THEN 
    `0 < dimword (:'a)` by METIS_TAC [ZERO_LT_dimword] THEN
    RW_TAC std_ss [Once (GSYM MOD_PLUS)] THEN
    RW_TAC std_ss [Once MOD_PLUS] THEN
    RW_TAC arith_ss [SUB_LEFT_ADD] THENL [
      METIS_TAC [w2n_lt, LESS_EQ_ANTISYM],
      RW_TAC std_ss [LESS_EQ_ADD_SUB, ADD_MODULUS] THEN
      ASSUME_TAC (Q.SPEC `k` w2n_lt) THEN
      RW_TAC arith_ss [LESS_EQ_ADD]
    ]
  );

val locate_ge_lem_1 = Q.store_thm (
    "locate_ge_lem_1",
    `locate_ge (x:word32) (k:num) ==>
     (!i. w2n i <= k ==> 
        (w2n (x - i) = w2n x - w2n i))`,
     RW_TAC arith_ss [locate_ge_def, w2n_sub_lem] 
   );
      
val locate_ge_lem_2 = Q.store_thm (
    "locate_ge_lem_2",
    `locate_ge x k ==> 
      (!i j. ~(i = j) /\ w2n i <= k /\ w2n j <= k ==>
            ~(w2n (x - i) = w2n (x - j))) /\
      (!j. 1 <= w2n x ==> (w2n x - 1 + (j + 2) = w2n x + SUC j))`,
    RW_TAC arith_ss [] THEN
    IMP_RES_TAC locate_ge_lem_1 THEN
    RW_TAC arith_ss [] THEN 
    FULL_SIMP_TAC std_ss [locate_ge_def] THEN
    METIS_TAC [SUB_CANCEL, w2n_11, LESS_EQ_TRANS]
   );

val locate_ge_thm = Q.store_thm (
    "locate_ge_thm",
    `!x k. locate_ge x (SUC k) ==> 
           locate_ge x 1 /\ locate_ge x k`,
     RW_TAC arith_ss [locate_ge_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Data registers are restricted to R0-R8                                     *)
(*      Frames are separate                                                        *)
(*      The temporary use of the stack won't affect existing data in the frame     *)
(*---------------------------------------------------------------------------------*)
 
val in_range_def = Define `
    in_range (k:num) (ubound,lbound) = 
      k <= ubound /\ lbound < k`;

val addr_in_range_def = Define `
    (addr_in_range st (isM m) bound = in_range m bound) /\
    (addr_in_range st (isV k) bound = in_range (addr_of st (isV k)) bound) /\
    (addr_in_range st _ _ = F)`;

val ADDR_IN_RANGE_OUTSIDE = Q.store_thm (
    "ADDR_IN_RANGE_OUTSIDE",
   `!st e x i. ~addr_in_range st e (x, x - SUC i) /\ SUC i <= x ==>
           ~(eq_exp st e (isM (x - i)))`,
   Cases_on `e` THEN
   RW_TAC arith_ss [addr_in_range_def, in_range_def, eq_exp_def, eq_addr_def, addr_of_def]
   );

val ADDR_IN_RANGE_OUTSIDE_2 = Q.store_thm (
    "ADDR_IN_RANGE_OUTSIDE_2",
   `!st e i k. ~(addr_in_range st e (k + x, x)) /\ i < k ==>
           ~(eq_exp st e (isM (SUC i + x)))`,
   Cases_on `e` THEN
   RW_TAC arith_ss [addr_in_range_def, in_range_def, eq_exp_def, eq_addr_def, addr_of_def]
   );

val ADDR_IN_RANGE_INDUCT_1 = Q.store_thm (
    "ADDR_IN_RANGE_INDUCT_1",
    `!x k e. ~addr_in_range st e (x, x - SUC k) ==>
        ~addr_in_range st e (x, x - k)`,
    Cases_on `e` THEN RW_TAC std_ss [addr_in_range_def, eq_exp_def, addr_of_def, eq_addr_def] THENL [
       FULL_SIMP_TAC std_ss [in_range_def] THEN
         Q.ABBREV_TAC `y = w2n (read st FP)` THEN
         Cases_on `x = SUC k + (y - n)` THENL [
           FULL_SIMP_TAC std_ss [SUC_ONE_ADD] THEN
             RW_TAC arith_ss [],
           RW_TAC arith_ss []
         ],
       FULL_SIMP_TAC std_ss [in_range_def] THEN
       RW_TAC arith_ss []
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      Auxiliary Theorems                                                         *)
(*---------------------------------------------------------------------------------*)

val RUN_CFL_BLK_APPEND = Q.store_thm (
    "RUN_CFL_BLK_APPEND",
    `(!st. run_cfl (BLK []) st = st) /\
     (!st l1 l2. run_cfl (BLK (l1 ++ l2)) st = run_cfl (BLK l2) (run_cfl (BLK l1) st))`,
    SIMP_TAC std_ss [CFL_SEMANTICS_BLK] THEN
    Induct_on `l1` THEN
    RW_TAC list_ss [CFL_SEMANTICS_BLK]
  );

(*---------------------------------------------------------------------------------*)
(*      Store and load an individual data                                          *)
(*      Push and pop an individual data                                            *)
(*---------------------------------------------------------------------------------*)

val store_one_def = Define `
     (store_one (isR r) offset = 
          [MSTR (13,offset) (from_reg_index r)]) /\
     (store_one (isC c) offset = 
          [MMOV R9 (MC c);  MSTR (13,offset) R9]) /\
     (store_one (isV k) offset = 
          [MLDR R9 (fp, NEG k); MSTR (13,offset) R9])`;

val load_one_def = Define `
     (load_one (isR r) offset = 
          [MLDR (from_reg_index r) (13,offset)]) /\
     (load_one (isC c) offset = 
          []) /\
     (load_one (isV k) offset = 
          [MLDR R9 (13,offset);  MSTR (fp, NEG (12 + k)) R9])`;

val push_one_def = Define `
     (push_one (isR r) = 
          [MSTR (13,NEG 0) (from_reg_index r); MSUB R13 R13 (MC 1w)]) /\
     (push_one (isC c) = 
          [MMOV R9 (MC c);  MSTR (13,NEG 0) R9; MSUB R13 R13 (MC 1w)]) /\
     (push_one (isV k) = 
          [MLDR R9 (fp, NEG k);  MSTR (13,NEG 0) R9; MSUB R13 R13 (MC 1w)]) /\
     (push_one (isM m) = [MSUB R13 R13 (MC 1w)])
     `;

val pop_one_def = Define `
     (pop_one (isR r) = 
          [MLDR (from_reg_index r) (13,POS 1); MADD R13 R13 (MC 1w)]) /\
     (pop_one (isC c) = 
          [MADD R13 R13 (MC 1w)]) /\
     (pop_one (isV k) = 
          [MLDR R9 (13, POS 1); MSTR (fp,NEG k) R9; MADD R13 R13 (MC 1w)]) /\
     (pop_one (isM m) = [MADD R13 R13 (MC 1w)])
     `;

(*---------------------------------------------------------------------------------*)
(*      Properties about pushing / storing a single data                           *)
(*---------------------------------------------------------------------------------*)

val tac1 = (fn g => 
            ((CONV_TAC (DEPTH_CONV (
              REWRITE_CONV [Once mdecode_def] THENC
              SIMP_CONV finmap_ss [write_thm, read_thm, toMEM_def, toEXP_def, toREG_def, index_of_reg_def]))) THEN
              FULL_SIMP_TAC std_ss [word_0_n2w, GSYM WORD_SUB_PLUS])
             g);

val push_one_lem = Q.store_thm (
    "push_one_lem", 
    `!st e. valid_exp_3 e ==>
          ((run_cfl (BLK (push_one e)) st = st |# (isM (w2n (read st SP)), st '' e) |# (isR sp, st '' (isR sp) - 1w)) \/ 
           (?v. run_cfl (BLK (push_one e)) st = 
                   st |# (isM (w2n (read st SP)), st '' e) |# (isR 9, v) |# (isR sp, st '' (isR sp) - 1w)))
          `,
     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     RW_TAC finmap_ss [reade_def, writee_def, read_thm, write_thm, SP_def, sp_def] THEN
     Cases_on `e` THEN
     FULL_SIMP_TAC std_ss [valid_exp_3_def, push_one_def,CFL_SEMANTICS_BLK, reade_def, read_thm] THENL [
       NTAC 4 tac1,
       NTAC 6 tac1 THEN METIS_TAC [],
       NTAC 6 tac1 THEN METIS_TAC []
     ]
  );

(*---------------------------------------------------------------------------------*)
(*      Push a list of data into the stack                                         *)
(*---------------------------------------------------------------------------------*)

val push_list_def = Define `
    (push_list [] = []) /\
    (push_list (x::xs) = push_list xs ++ push_one x)`;

(*---------------------------------------------------------------------------------*)
(*      Lemmas about push_list                                                     *)
(*---------------------------------------------------------------------------------*)

val legal_push_exp_def = Define `
    legal_push_exp st e k = 
       ~(addr_in_range st e (w2n (read st SP), w2n (read st SP) - k)) /\ valid_exp_1 e`;

val PUSH_ONE_SANITY = Q.store_thm (
    "PUSH_ONE_SANITY",
    `!st h l. valid_exp_3 h /\ locate_ge (read st SP) (SUC (LENGTH l))
                ==>
              let st1 = run_cfl (BLK (push_one h)) st in
              locate_ge (read st1 SP) (LENGTH l)`,

     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC locate_ge_thm THEN
     IMP_RES_TAC locate_ge_lem_1 THEN
     IMP_RES_TAC push_one_lem THEN
     POP_ASSUM (ASSUME_TAC o Q.SPEC `(regs,mem)`) THEN
     RW_TAC std_ss [LET_THM] THEN
     FULL_SIMP_TAC finmap_ss [LET_THM, locate_ge_def, reade_def, writee_def, write_thm, read_thm, SP_def, sp_def] THEN
     `w2n (1w:word32) = 1` by WORDS_TAC THEN
     FULL_SIMP_TAC arith_ss []
   );


val PUSH_LIST_SP_FP = Q.store_thm (
    "PUSH_LIST_SP_FP",
    `!l st x. locate_ge (read st SP) (LENGTH l)
             ==> let st' = run_cfl (BLK (push_list l)) st in 
              (w2n (read st' SP) = w2n (read st SP) - LENGTH l) /\
              (w2n (read st' FP) = w2n (read st FP)) /\
              (w2n (read st' IP) = w2n (read st IP))`,

    Induct_on `l` THENL [
        RW_TAC list_ss [CFL_SEMANTICS_BLK, push_list_def],

        SIMP_TAC list_ss [RUN_CFL_BLK_APPEND, push_list_def] THEN
          REPEAT STRIP_TAC THEN
          IMP_RES_TAC locate_ge_thm THEN
          RES_TAC THEN
          `?regs mem. run_cfl (BLK (push_list l)) st = (regs,mem)` by METIS_TAC [ABS_PAIR_THM] THEN  
          FULL_SIMP_TAC std_ss [read_thm, SP_def, FP_def, IP_def, LET_THM] THEN
          `locate_ge ((regs ' 13):word32) 1` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
          `(w2n (1w:word32) <= 1) /\ (w2n (1w:word32) = 1)` by WORDS_TAC THEN
          IMP_RES_TAC locate_ge_lem_1 THEN
          NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
          Cases_on `h` THEN
          SIMP_TAC std_ss [push_one_def, CFL_SEMANTICS_BLK, read_thm] THENL [
            NTAC 6 tac1 THEN RW_TAC arith_ss [],
            NTAC 9 tac1 THEN RW_TAC arith_ss [],
            NTAC 9 tac1 THEN RW_TAC arith_ss [],
            NTAC 4 tac1 THEN RW_TAC arith_ss []
          ]
        ]
  );


val PUSH_LIST_EXP_INTACT = Q.store_thm (
    "PUSH_LIST_EXP_INTACT",
    `!l st x e. locate_ge (read st SP) (LENGTH l)
             ==> (eq_exp st e x = eq_exp (run_cfl (BLK (push_list l)) st) e x)`,
    RW_TAC std_ss [] THEN
    IMP_RES_TAC PUSH_LIST_SP_FP THEN
    Cases_on `e` THEN Cases_on `x` THEN
    FULL_SIMP_TAC std_ss [eq_exp_def, eq_addr_def, addr_of_def, LET_THM, valid_exp_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Main Theorems about push_list                                              *)
(*---------------------------------------------------------------------------------*)

val PUSH_LIST_SANITY = Q.store_thm (
    "PUSH_LIST_SANITY",
    `!l st x. EVERY valid_exp_3 l /\ locate_ge (read st SP) (LENGTH l)
             ==> !e. ~addr_in_range st e (w2n (read st SP),w2n (read st SP) - LENGTH l) /\ valid_exp_1 e ==>
                    ((run_cfl (BLK (push_list l)) st) '' e = st '' e)`,

    Induct_on `l` THENL [
        RW_TAC std_ss [CFL_SEMANTICS_BLK, push_list_def],
        RW_TAC list_ss [RUN_CFL_BLK_APPEND, push_list_def] THEN
          IMP_RES_TAC locate_ge_thm THEN
          IMP_RES_TAC ADDR_IN_RANGE_INDUCT_1 THEN
          RES_TAC THEN
          IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN POP_ASSUM (K ALL_TAC) THEN
          IMP_RES_TAC (Q.SPECL [`l`,`st`,`e`,`isM (w2n (read st SP) - LENGTH (l:CFL_EXP list))`] 
                        PUSH_LIST_EXP_INTACT) THEN
          NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN

          Q.ABBREV_TAC `st1 = run_cfl (BLK (push_list l)) st` THEN
          IMP_RES_TAC push_one_lem THEN
          POP_ASSUM (ASSUME_TAC o Q.SPEC `st1`) THEN
          RW_TAC std_ss [sp_def] THEN RW_TAC std_ss [] THEN
          `(!st. ~(eq_exp st (isR 9) e)) /\ (!st.~(eq_exp st (isR 13) e))` by 
                METIS_TAC [NOT_EQ_isR_LEM, valid_exp_1_def] THEN
          `~(eq_exp st1 (isM (w2n (read st SP) - LENGTH l)) e)` by 
                   METIS_TAC [locate_ge_def, ADDR_IN_RANGE_OUTSIDE, eq_exp_SYM] THEN
          `~(isR 9 = isR fp) /\ ~(isR 13 = isR fp) /\ ~(isM (w2n (read st SP) - LENGTH l) = isR fp)`
                by RW_TAC std_ss [fp_def] THEN
          RW_TAC std_ss [READE_WRITEE_THM_2]
       ]
  );

val PUSH_LIST_FUNCTIONALITY = Q.store_thm (
    "PUSH_LIST_FUNCTIONALITY",
    `!l st. EVERY valid_exp_3 l /\ locate_ge (read st SP) (LENGTH l)  ==> 
        !i. i < LENGTH l /\ legal_push_exp st (EL i l) (PRE (LENGTH l) - i) ==>
             ((run_cfl (BLK (push_list l)) st) '' (isM (w2n (read st SP) - PRE (LENGTH l) + i))  = st '' (EL i l))`,

    Induct_on `l` THENL [
        RW_TAC list_ss [],

        RW_TAC list_ss [RUN_CFL_BLK_APPEND, push_list_def] THEN
          IMP_RES_TAC locate_ge_thm THEN
          IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
          IMP_RES_TAC (Q.SPECL [`l`,`st`,`e`,`isM (w2n (read st SP) - LENGTH (l:CFL_EXP list))`] 
                PUSH_LIST_EXP_INTACT) THEN
          NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN

          Q.ABBREV_TAC `st1 = run_cfl (BLK (push_list l)) st` THEN
          IMP_RES_TAC push_one_lem THEN
          POP_ASSUM (ASSUME_TAC o Q.SPEC `st1`) THEN
          RW_TAC std_ss [sp_def] THEN RW_TAC std_ss [] THEN

          (fn g => (
           Cases_on `i` THENL [
             FULL_SIMP_TAC list_ss [] THEN
               `(!st1. ~(eq_exp st1 (isR 9) (isM (w2n (read st SP) - LENGTH l)))) /\ 
                 (!st1. ~(eq_exp st1 (isR 13) (isM (w2n (read st SP) - LENGTH l))))` by RW_TAC std_ss [eq_exp_def] THEN
               `~(isR 9 = isR fp) /\ ~(isR 13 = isR fp)` by RW_TAC std_ss [fp_def] THEN
               RW_TAC std_ss [READE_WRITEE_THM_2] THEN
               `~(is_C (isM (w2n (read st1 SP))))` by RW_TAC std_ss [is_C_def] THEN
               Q.UNABBREV_TAC `st1` THEN
               FULL_SIMP_TAC std_ss [legal_push_exp_def] THEN
               METIS_TAC [PUSH_LIST_SANITY, READE_WRITEE],

           FULL_SIMP_TAC list_ss [] THEN
               `(w2n (read st SP) - LENGTH l + SUC n = w2n (read st SP) - PRE (LENGTH l) + n) /\
                (LENGTH l - SUC n = PRE (LENGTH l) - n)` by 
                  (NTAC 7 (POP_ASSUM (K ALL_TAC)) THEN FULL_SIMP_TAC arith_ss [locate_ge_def]) THEN
               FULL_SIMP_TAC std_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
               `(!st1. ~(eq_exp st1 (isR 9) (isM (w2n (read st SP) - PRE (LENGTH l) + n)))) /\ 
                (!st1. ~(eq_exp st1 (isR 13) (isM (w2n (read st SP) - PRE (LENGTH l) + n))))` 
                     by RW_TAC std_ss [eq_exp_def] THEN
               `~(isR 9 = isR fp) /\ ~(isR 13 = isR fp)` by RW_TAC std_ss [fp_def] THEN
               RW_TAC std_ss [READE_WRITEE_THM_2] THEN
               NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN               

               `~(eq_exp st1 (isM (w2n (read st SP) - LENGTH l)) (isM (w2n (read st SP) - PRE (LENGTH l) + n)))` 
                 by FULL_SIMP_TAC arith_ss [eq_exp_def, eq_addr_def, addr_of_def, locate_ge_def] THEN
               `~(is_C (isM (w2n (read st1 SP) - LENGTH l)))` by RW_TAC std_ss [is_C_def] THEN
               RW_TAC std_ss [READE_WRITEE_THM_2] THEN
               METIS_TAC []
          ]) g)
     ]
  );

(*---------------------------------------------------------------------------------*)
(*      Properties about popping a single data                                     *)
(*---------------------------------------------------------------------------------*)

val pop_one_lem = Q.store_thm (
    "pop_one_lem", 
    `!st e. valid_exp e ==>
           (run_cfl (BLK (pop_one e)) st = 
                   st |# (e, st '' (isM (w2n (read st SP) + 1))) |# (isR sp, st '' (isR sp) + 1w)) \/
           ?v. run_cfl (BLK (pop_one e)) st = 
                   st |# (e, st '' (isM (w2n (read st SP) + 1))) |# (isR 9, v) |# (isR sp, st '' (isR sp) + 1w)
          `,
     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     RW_TAC finmap_ss [reade_def, writee_def, read_thm, write_thm, SP_def, sp_def] THEN
     Cases_on `e` THEN
     FULL_SIMP_TAC std_ss [valid_exp_def, valid_regs_lem, pop_one_def,CFL_SEMANTICS_BLK, 
             reade_def, read_thm, writee_def, write_thm] THENL [
       NTAC 4 tac1 THEN FULL_SIMP_TAC finmap_ss [valid_regs_lem] THEN
           METIS_TAC [DECIDE ``~(9 = 13)``, FUPDATE_COMMUTES, FUPDATE_REFL, valid_regs_lem],
       tac1 THEN METIS_TAC [DECIDE ``~(9 = 13)``, FUPDATE_COMMUTES, FUPDATE_REFL],
       NTAC 6 tac1 THEN RW_TAC std_ss [fp_def] THEN METIS_TAC []
     ]
  );

(*---------------------------------------------------------------------------------*)
(*      Pop from the stack a list of data                                          *)
(*---------------------------------------------------------------------------------*)

val pop_list_def = Define `
    (pop_list [] = []) /\
    (pop_list (x::xs) = pop_one x ++ pop_list xs)`;

(*---------------------------------------------------------------------------------*)
(*      When growing (to higher addresses), the stack shouldn't overflow           *)
(*      Indicated by the value of sp                                               *)
(*---------------------------------------------------------------------------------*)

val grow_lt_def = Define `
    grow_lt (x:word32) (k:num) = 
      w2n x + k < dimword (:i32)`;

val grow_lt_lem_1 = Q.store_thm (
    "grow_lt_lem_1",
    `grow_lt (x:word32) (k:num) ==>
      (w2n (x + n2w k) = w2n x + k)`,
    RW_TAC arith_ss [grow_lt_def, word_add_def, w2n_n2w]
   );

val grow_lt_thm = Q.store_thm (
    "grow_lt_thm",
    `grow_lt x (SUC k) ==>
       grow_lt x 1 /\ grow_lt x k`,
    RW_TAC arith_ss [grow_lt_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Lemmas about pop_list                                                      *)
(*---------------------------------------------------------------------------------*)

val legal_pop_exp_def = Define `
    legal_pop_exp st e l = 
       EVERY (\x. ~(eq_exp st e x)) l /\ ~(is_C e) /\ valid_exp e
       `;

val LEGAL_POP_EXP_NOT_FP_SP = Q.store_thm (
    "LEGAL_POP_EXP_NOT_FP_SP",
    `!e st k. legal_pop_exp st e k ==>
        ~(e = isR 9) /\ ~(e = isR 13)`,
    SIMP_TAC std_ss [legal_pop_exp_def] THEN
    Cases_on `e` THEN
    RW_TAC std_ss [valid_exp_def, valid_regs_def]
   );

val POP_ONE_SANITY = Q.store_thm (
    "POP_ONE_SANITY", 
    `!st e h l. valid_exp_2 e /\ valid_exp h /\ grow_lt (read st SP) (SUC (LENGTH l)) /\ 
              ~eq_exp st e h ==>
           let st1 = run_cfl (BLK (pop_one h)) st in  
              grow_lt (read st1 SP) (LENGTH l) /\ (st1 '' e = st '' e)
    `,
    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC grow_lt_thm THEN
    IMP_RES_TAC grow_lt_lem_1 THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [valid_exp_def, valid_regs_lem, pop_one_def,CFL_SEMANTICS_BLK, 
             read_thm, write_thm, SP_def, FP_def] THEN
    (fn g => (NTAC 3 tac1 THEN FULL_SIMP_TAC finmap_ss [LET_THM, read_thm, valid_regs_lem] THEN
         FULL_SIMP_TAC set_ss [FDOM_FUPDATE] THEN
         FULL_SIMP_TAC arith_ss [grow_lt_def] THEN
         Cases_on `e` THEN 
         IMP_RES_TAC valid_regs_lem THEN
         FULL_SIMP_TAC finmap_ss [eq_exp_def, valid_exp_2_def, eq_addr_def, addr_of_def, valid_exp_def, is_C_def, 
             reade_def, read_thm, addr_in_range_def, in_range_def, fp_def, FP_def] THEN
         FULL_SIMP_TAC arith_ss [valid_regs_lem]
         ) g)
  );

val POP_ONE_SANITY_2 = Q.store_thm (
    "POP_ONE_SANITY_2", 
    `!st h l. valid_exp_2 e /\ valid_exp h /\ grow_lt (read st SP) (SUC (LENGTH l)) ==>
           let st1 = run_cfl (BLK (pop_one h)) st in  
              grow_lt (read st1 SP) (LENGTH l)
    `,
    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC grow_lt_thm THEN
    IMP_RES_TAC grow_lt_lem_1 THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [valid_exp_def, valid_regs_lem, pop_one_def,CFL_SEMANTICS_BLK, 
             read_thm, write_thm, SP_def, FP_def] THEN
    (fn g => (NTAC 3 tac1 THEN FULL_SIMP_TAC finmap_ss [LET_THM, read_thm, valid_regs_lem] THEN
         FULL_SIMP_TAC set_ss [FDOM_FUPDATE] THEN
         FULL_SIMP_TAC arith_ss [grow_lt_def] THEN
         FULL_SIMP_TAC finmap_ss [eq_exp_def, eq_addr_def, addr_of_def, valid_exp_def, valid_exp_2_def, is_C_def, 
                       read_thm, addr_in_range_def, in_range_def, fp_def, FP_def] THEN
         FULL_SIMP_TAC arith_ss [valid_regs_lem]
         ) g)
  );

val POP_ONE_ADDR_IN_RANGE = Q.store_thm (
    "POP_ONE_ADDR_IN_RANGE", 
    `!st e h l. EVERY valid_exp l /\ valid_exp h /\ grow_lt (read st SP) (SUC (LENGTH l)) /\ 
              EVERY (\x. ~addr_in_range st x (w2n (read st SP) + SUC (LENGTH l), w2n (read st SP))) l ==>
           let st' = run_cfl (BLK (pop_one h)) st in  
              EVERY (\x. ~addr_in_range st' x (w2n (read st' SP) + LENGTH l, w2n (read st' SP))) l`,

    SIMP_TAC std_ss [FORALL_DSTATE, LET_THM] THEN
    REPEAT STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    RW_TAC std_ss [] THEN
    `?st'. run_cfl (BLK (pop_one h)) (regs,mem) = st'` by METIS_TAC [] THEN
    FULL_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN
    IMP_RES_TAC grow_lt_thm THEN
    IMP_RES_TAC grow_lt_lem_1 THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [valid_exp_def, valid_regs_lem, pop_one_def,CFL_SEMANTICS_BLK, 
             read_thm, write_thm, SP_def, FP_def] THEN
    (fn g => (NTAC 3 tac1 THEN FULL_SIMP_TAC finmap_ss [LET_THM, read_thm, valid_regs_lem] THEN
              (fn g => REWRITE_TAC [Once EQ_SYM_EQ] g) THEN
              Cases_on `x` THEN 
              IMP_RES_TAC valid_regs_lem THEN
              FULL_SIMP_TAC finmap_ss [addr_in_range_def, in_range_def, addr_of_def, 
                 valid_exp_def, is_C_def, addr_in_range_def, in_range_def, fp_def, FP_def, read_thm] THEN
              FULL_SIMP_TAC arith_ss [valid_regs_lem]
         ) g)
  );    

val POP_LIST_SP_FP = Q.store_thm (
    "POP_LIST_SP_FP",
    `!l st x. grow_lt (read st SP) (LENGTH l) /\ EVERY valid_exp l
             ==> let st' = run_cfl (BLK (pop_list l)) st in 
              (w2n (read st' SP) = w2n (read st SP) + LENGTH l) /\
              (w2n (read st' FP) = w2n (read st FP)) /\
              (w2n (read st' IP) = w2n (read st IP)) `,

    let val tac2 = FULL_SIMP_TAC finmap_ss [LET_THM,read_thm, SP_def, FP_def, IP_def, valid_regs_lem, grow_lt_lem_1] 
                             THEN FULL_SIMP_TAC arith_ss [grow_lt_def, valid_regs_def]
    in
    Induct_on `l` THENL [
        RW_TAC list_ss [CFL_SEMANTICS_BLK, pop_list_def],

          SIMP_TAC list_ss [RUN_CFL_BLK_APPEND, pop_list_def] THEN
          REPEAT STRIP_TAC THEN
          IMP_RES_TAC grow_lt_thm THEN
          `let st1 = run_cfl (BLK (pop_one h)) st in
               grow_lt (read st1 SP) (LENGTH l) /\ (w2n (read st1 SP) = SUC (w2n (read st SP))) /\ 
               (w2n (read st1 FP) = w2n (read st FP)) /\ (w2n (read st1 IP) = w2n (read st IP))` 
                   by SIMP_TAC std_ss [grow_lt_def] THENL [
            `?regs mem. st = (regs,mem)` by METIS_TAC [ABS_PAIR_THM] THEN
            Cases_on `h` THEN
            FULL_SIMP_TAC list_ss [valid_exp_def, pop_one_def, CFL_SEMANTICS_BLK, read_thm] THENL [
                NTAC 2 tac1 THEN tac2,
                tac1 THEN tac2,
                NTAC 3 tac1 THEN tac2
            ],
       FULL_SIMP_TAC arith_ss [LET_THM]
     ]
   ]
  end
  );

val POP_ONE_EXP_LEM_1 = Q.store_thm (
    "POP_ONE_EXP_LEM_1",
    `!h st i. grow_lt (read st SP) 1 /\ valid_exp h /\ ~(eq_exp st h (isM (SUC i + w2n (read st SP)))) ==>
       let st' = run_cfl (BLK (pop_one h)) st in
          (st '' (isM (SUC i + w2n (read st SP))) = st' '' (isM (i + w2n (read st' SP))))`,
    
    let val tac2 = FULL_SIMP_TAC finmap_ss [LET_THM,read_thm, SP_def, FP_def, valid_regs_lem, fp_def] THEN
                   RW_TAC arith_ss [SUC_ONE_ADD]
    in
    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC grow_lt_lem_1 THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC list_ss [eq_exp_def, eq_addr_def, addr_of_def, valid_exp_def, pop_one_def, CFL_SEMANTICS_BLK, 
           read_thm, reade_def, SP_def, FP_def] THENL [
       NTAC 2 tac1 THEN tac2,
       tac1 THEN tac2,
       NTAC 3 tac1 THEN tac2
   ]
    end
  );

val POP_LIST_EXP_INTACT = Q.store_thm (
    "POP_LIST_EXP_INTACT",
    `!l st x e. grow_lt (read st SP) (LENGTH l) /\ EVERY valid_exp l
             ==> (eq_exp st e x = eq_exp (run_cfl (BLK (pop_list l)) st) e x)`,
    RW_TAC std_ss [] THEN
    IMP_RES_TAC POP_LIST_SP_FP THEN
    Cases_on `e` THEN Cases_on `x` THEN
    FULL_SIMP_TAC std_ss [eq_exp_def, eq_addr_def, addr_of_def, LET_THM, valid_exp_def]
   );

val POP_ONE_EXP_INTACT = Q.store_thm (
    "POP_ONE_EXP_INTACT",
   `!l st e h. grow_lt (read st SP) 1 /\ valid_exp h /\ 
      EVERY (\x. ~eq_exp st e x) l ==> 
        EVERY (\x. ~eq_exp (run_cfl (BLK (pop_one h)) st) e x) l`,
    REPEAT STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    METIS_TAC [(SIMP_RULE list_ss [pop_list_def] o Q.SPECL [`[h]`,`st`]) POP_LIST_EXP_INTACT]
   );

(*---------------------------------------------------------------------------------*)
(*      The pop list should contain unique elements                                *)
(*---------------------------------------------------------------------------------*)

val unique_exp_list_def = Define `
    (unique_exp_list st (h::l) = EVERY (\x. ~eq_exp st h x) l /\ unique_exp_list st l) /\
    (unique_exp_list st [] = T)`;

val unique_exp_list_lem_1 = Q.store_thm (
    "unique_exp_list_lem_1",
    `!i h l. i < LENGTH l /\ EVERY (\x. ~eq_exp st h x) l ==> ~eq_exp st (EL i l) h`,
    Induct_on `l` THEN
    RW_TAC list_ss [] THEN
    Cases_on `i` THEN
    RW_TAC list_ss [] THEN 
    METIS_TAC [eq_exp_SYM]
  );

val unique_exp_list_lem_2 = Q.store_thm (
    "unique_exp_list_lem_2",   
    `unique_exp_list st l /\ EVERY valid_exp l /\ valid_exp h /\ grow_lt (read st SP) 1 ==> 
         unique_exp_list (run_cfl (BLK (pop_one h)) st) l`,
     Induct_on `l` THEN
     RW_TAC list_ss [unique_exp_list_def] THEN
     METIS_TAC [POP_ONE_EXP_INTACT]
   );

(*---------------------------------------------------------------------------------*)
(*      Main Theorems about pop_list                                               *)
(*---------------------------------------------------------------------------------*)

val POP_LIST_SANITY = Q.store_thm (
    "POP_LIST_SANITY",
    `!l st x. EVERY valid_exp l /\ grow_lt (read st SP) (LENGTH l)
             ==> !e. EVERY (\x. ~eq_exp st e x) l /\ valid_exp_2 e ==>                
                    ((run_cfl (BLK (pop_list l)) st) '' e = st '' e)`,

    Induct_on `l` THENL [
        RW_TAC std_ss [CFL_SEMANTICS_BLK, pop_list_def],

        RW_TAC list_ss [RUN_CFL_BLK_APPEND, pop_list_def] THEN
          IMP_RES_TAC POP_ONE_SANITY THEN
          Q.ABBREV_TAC `st' = run_cfl (BLK (pop_one h)) st` THEN
          FULL_SIMP_TAC std_ss [LET_THM] THEN
          IMP_RES_TAC grow_lt_thm THEN
          METIS_TAC [POP_ONE_EXP_INTACT]
     ]
  );


val POP_LIST_FUNCTIONALITY = Q.store_thm (
    "POP_LIST_FUNCTIONALITY",
    `!l st. EVERY valid_exp l /\ grow_lt (read st SP) (LENGTH l) /\
            unique_exp_list st l /\ EVERY (\x.~addr_in_range st x (w2n (read st SP) + LENGTH l, w2n (read st SP))) l 
             ==> !i. i < LENGTH l /\ ~(is_C (EL i l)) /\ valid_exp (EL i l) ==>
             ((run_cfl (BLK (pop_list l)) st) '' (EL i l)  = st '' (isM (w2n (read st SP) + SUC i)))`,

    Induct_on `l` THENL [
        RW_TAC list_ss [],

        RW_TAC list_ss [RUN_CFL_BLK_APPEND, pop_list_def, unique_exp_list_def] THEN
          IMP_RES_TAC grow_lt_thm THEN
          Cases_on `i` THENL [
         
            FULL_SIMP_TAC list_ss [] THEN
              `(run_cfl (BLK (pop_one h)) st) '' h = st '' isM (w2n (read st SP) + 1)` by ALL_TAC THENL [
                IMP_RES_TAC pop_one_lem THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `st`) THEN
                RW_TAC std_ss [] THEN 
                `(!st1. ~(eq_exp st1 (isR 9) h)) /\ (!st1. ~(eq_exp st1 (isR sp) h))` by (Cases_on `h` THEN 
                      FULL_SIMP_TAC std_ss [eq_exp_def, valid_exp_def, valid_regs_lem, sp_def]) THEN
                `~(isR 9 = isR fp) /\ ~(isR sp = isR fp)` by RW_TAC std_ss [fp_def, sp_def] THEN
                RW_TAC std_ss [READE_WRITEE_THM_2, READE_WRITEE],

              IMP_RES_TAC valid_exp_thm THEN
                IMP_RES_TAC POP_ONE_SANITY_2 THEN
                IMP_RES_TAC POP_ONE_EXP_INTACT THEN POP_ASSUM (K ALL_TAC) THEN
                FULL_SIMP_TAC std_ss [LET_THM] THEN
                `legal_pop_exp (run_cfl (BLK (pop_one h)) st) h l` by METIS_TAC [legal_pop_exp_def] THEN
                FULL_SIMP_TAC std_ss [legal_pop_exp_def] THEN
                METIS_TAC [POP_LIST_SANITY]
            ],
  
            FULL_SIMP_TAC list_ss [] THEN
                IMP_RES_TAC unique_exp_list_lem_1 THEN
                IMP_RES_TAC valid_exp_thm THEN
                IMP_RES_TAC POP_ONE_SANITY THEN
                IMP_RES_TAC unique_exp_list_lem_2 THEN
                IMP_RES_TAC (SIMP_RULE list_ss [] POP_ONE_ADDR_IN_RANGE) THEN
                `~eq_exp st h (isM (SUC (SUC n) + w2n (read st SP)))` by (IMP_RES_TAC ADDR_IN_RANGE_OUTSIDE_2 THEN
                     FULL_SIMP_TAC arith_ss []) THEN
                FULL_SIMP_TAC std_ss [LET_THM] THEN
                METIS_TAC [Q.SPECL [`h`,`st`,`SUC n`] (SIMP_RULE std_ss [LET_THM] POP_ONE_EXP_LEM_1)]
         ]
       ]
  );

(*---------------------------------------------------------------------------------*)
(*   Copy a list to another list                                                   *)
(*---------------------------------------------------------------------------------*)

val copy_list_def = Define `
    copy_list dstL srcL = push_list srcL ++ pop_list dstL`;

(*---------------------------------------------------------------------------------*)
(*   Lemmas about copy_list                                                        *)
(*---------------------------------------------------------------------------------*)

val LOCATE_GE_GROW_LT = Q.store_thm (
    "LOCATE_GE_GROW_LT",
    `locate_ge x k /\ (w2n x' = w2n x - k) ==> grow_lt x' k`,
    RW_TAC arith_ss [locate_ge_def, grow_lt_def, w2n_lt]
   );

val LEGAL_PUSH_EXP_DSTATE = Q.store_thm (
    "LEGAL_PUSH_EXP_DSTATE",
    `legal_pop_exp st e l /\ (w2n (read st FP) = w2n (read st' FP)) ==> 
         legal_pop_exp st' e l`,
    RW_TAC std_ss [legal_pop_exp_def] THEN
    Q.PAT_ASSUM `EVERY x y` MP_TAC THEN
    MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    RW_TAC std_ss [] THEN
    Cases_on `e` THEN Cases_on `x` THEN
    FULL_SIMP_TAC std_ss [eq_exp_def, eq_addr_def, addr_of_def] THEN
    METIS_TAC []
   );

val PUSH_LIST_ADDR_IN_RANGE = Q.store_thm (
    "PUSH_LIST_ADDR_IN_RANGE",
    `!st l1 l2. EVERY valid_exp l1 /\ locate_ge (read st SP) (LENGTH l1) /\
        EVERY (\x. ~addr_in_range st x (w2n (read st SP), w2n (read st SP) - LENGTH l1)) l2 ==>
       let st' = run_cfl (BLK (push_list l1)) st in
          EVERY (\x. ~addr_in_range st' x (w2n (read st' SP) + LENGTH l1, w2n (read st' SP))) l2`,

    RW_TAC std_ss [LET_THM] THEN
    IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
    RW_TAC std_ss [] THEN
    Q.PAT_ASSUM `EVERY x y` MP_TAC THEN
    MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    RW_TAC std_ss [] THEN
    Cases_on `x` THEN
    FULL_SIMP_TAC arith_ss [addr_in_range_def, in_range_def, addr_of_def, locate_ge_def]
   );

val UNIQUE_LIST_THM = Q.store_thm (
    "UNIEQUE_LIST_THM",
    `!st st'. (read st FP = read st' FP) /\ unique_exp_list st l ==>
            unique_exp_list st' l`,
    Induct_on `l` THEN
    RW_TAC std_ss [unique_exp_list_def] THENL [
      Q.PAT_ASSUM `EVERY x y` MP_TAC THEN
        MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
        RW_TAC std_ss [] THEN
        Cases_on `h` THEN Cases_on `x` THEN
        FULL_SIMP_TAC std_ss [eq_exp_def, eq_addr_def, addr_of_def] THEN
        METIS_TAC [],
      METIS_TAC []
   ]
  );


val  ADDR_IN_RANGE_LEGAL_EXP = Q.store_thm (
    "ADDR_IN_RANGE_LEGAL_EXP",
    `!st l. EVERY valid_exp l /\ EVERY ($~ o is_C) l /\ locate_ge (read st SP) (LENGTH l) /\
         EVERY (\x. ~addr_in_range st x (w2n (read st SP), w2n (read st SP) - LENGTH l)) l
       ==> !i. i < LENGTH l ==> legal_push_exp st (EL i l) (PRE (LENGTH l) - i)`,

    RW_TAC std_ss [legal_push_exp_def, EVERY_EL] THEN
    RES_TAC THEN REPEAT (Q.PAT_ASSUM `!n.x` (K ALL_TAC)) THEN
    Cases_on `EL i l` THEN
    FULL_SIMP_TAC std_ss [valid_exp_1_def, addr_in_range_def, in_range_def, addr_of_def, valid_exp_def, 
        valid_regs_lem, locate_ge_def] THEN
    Q.ABBREV_TAC `x = w2n (read st SP)` THEN Q.ABBREV_TAC `y = w2n (read st FP)` THEN
    FULL_SIMP_TAC std_ss [NOT_LESS, PRE_SUB1] THEN
    `(1 + i) <= LENGTH l` by RW_TAC arith_ss [] THEN
    RW_TAC std_ss [GSYM SUB_PLUS] THEN
    FULL_SIMP_TAC arith_ss [SUB_RIGHT_ADD]
   );

(*---------------------------------------------------------------------------------*)
(*   Main theorems about copy_list                                                 *)
(*---------------------------------------------------------------------------------*)

val COPY_LIST_SANITY = Q.store_thm (
    "COPY_LIST_SANITY",
    `!st dstL srcL. EVERY valid_exp dstL /\ EVERY valid_exp srcL /\ (LENGTH srcL = LENGTH dstL) /\
         locate_ge (read st SP) (LENGTH srcL)
             ==> !e. legal_push_exp st e (LENGTH dstL) /\ legal_pop_exp st e dstL ==>
                    ((run_cfl (BLK (copy_list dstL srcL)) st) '' e = st '' e)`,

    RW_TAC std_ss [copy_list_def, RUN_CFL_BLK_APPEND] THEN
    IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
    `grow_lt (read (run_cfl (BLK (push_list srcL)) st) SP) (LENGTH dstL)` by METIS_TAC [LOCATE_GE_GROW_LT] THEN
    IMP_RES_TAC (REWRITE_RULE [Once EQ_SYM_EQ] LEGAL_PUSH_EXP_DSTATE) THEN
    FULL_SIMP_TAC std_ss [legal_pop_exp_def, legal_push_exp_def] THEN
    IMP_RES_TAC valid_exp_thm THEN
    RW_TAC std_ss [POP_LIST_SANITY] THEN
    METIS_TAC [PUSH_LIST_SANITY, VALID_EXP_LEM]
  );

val COPY_LIST_FUNCTIONALITY = Q.store_thm (
    "COPY_LIST_FUNCTIONALITY",
    `!st dstL srcL. EVERY valid_exp srcL /\ EVERY ($~ o is_C) srcL /\ EVERY ($~ o is_C) dstL /\
                    EVERY valid_exp dstL /\ 
         locate_ge (read st SP) (LENGTH srcL) /\ unique_exp_list st dstL /\
            EVERY (\x. ~addr_in_range st x (w2n (read st SP), w2n (read st SP) - LENGTH srcL)) srcL /\
            EVERY (\x. ~addr_in_range st x (w2n (read st SP), w2n (read st SP) - LENGTH dstL)) dstL /\
            (LENGTH dstL = LENGTH srcL)
           ==> !i. i < LENGTH dstL ==>
           (run_cfl (BLK (copy_list dstL srcL)) st '' (EL i dstL) = st '' (EL i srcL))`,

    RW_TAC std_ss [copy_list_def, RUN_CFL_BLK_APPEND] THEN
    `let st' = run_cfl (BLK (push_list srcL)) st in EVERY (\x. ~addr_in_range st' x 
           (w2n (read st' SP) + LENGTH dstL, w2n (read st' SP))) dstL` by METIS_TAC [PUSH_LIST_ADDR_IN_RANGE] THEN
    POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [LET_THM]) THEN
    IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
    `read st FP = read (run_cfl (BLK (push_list srcL)) st) FP` by METIS_TAC [w2n_11] THEN
    IMP_RES_TAC UNIQUE_LIST_THM THEN
    `grow_lt (read (run_cfl (BLK (push_list srcL)) st) SP) (LENGTH dstL)` by METIS_TAC [LOCATE_GE_GROW_LT] THEN
    `~is_C (EL i dstL) /\ valid_exp (EL i dstL)` by (FULL_SIMP_TAC std_ss [EVERY_EL] THEN METIS_TAC []) THEN
    IMP_RES_TAC valid_exp_thm THEN
    RW_TAC std_ss [POP_LIST_FUNCTIONALITY] THEN
    NTAC 8 (POP_ASSUM (K ALL_TAC)) THEN

    `w2n (read st SP) - PRE (LENGTH srcL) + i = w2n (read st SP) - LENGTH srcL + SUC i` by 
               FULL_SIMP_TAC arith_ss [locate_ge_def, PRE_SUB1] THEN
    `~is_C (EL i srcL) /\ valid_exp (EL i srcL)` by (FULL_SIMP_TAC std_ss [EVERY_EL] THEN
           METIS_TAC []) THEN
    `legal_push_exp st (EL i srcL) (PRE (LENGTH srcL) - i)` by METIS_TAC [ADDR_IN_RANGE_LEGAL_EXP] THEN
    METIS_TAC [PUSH_LIST_FUNCTIONALITY, VALID_EXP_LEM]
  );

(*---------------------------------------------------------------------------------*)
(*   Save and restore a list                                                       *)
(*---------------------------------------------------------------------------------*)

val sr_list_def = Define `
    sr_list (dstL, l, srcL) = push_list srcL ++ l ++ pop_list dstL`;


(* Its properites are analogous to copy_list's *)

(*---------------------------------------------------------------------------------*)

val _ = export_theory();
