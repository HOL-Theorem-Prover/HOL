(*
quietdec := true;

app load ["arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "whileTheory", "finite_mapTheory",
          "listTheory", "pred_setSimps", "pred_setTheory", "preARMTheory", "CFLTheory", "bigInstTheory", 
          "simplifier", "HSLTheory"];

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory whileTheory
       listTheory pred_setSimps pred_setTheory finite_mapTheory preARMTheory CFLTheory bigInstTheory 
       simplifier HSLTheory;

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory whileTheory
       listTheory pred_setSimps pred_setTheory finite_mapTheory preARMTheory CFLTheory bigInstTheory 
       simplifier HSLTheory;

(*---------------------------------------------------------------------------------*)
(*   This theory is about an implementation of function calls                      *)
(*   The pre-call processing and post-call processing are fulfilled using          *)
(*      fixed routines that comply with ARM Function Call Standard                 *)
(*---------------------------------------------------------------------------------*)

val _ = new_theory "funCall";

(*---------------------------------------------------------------------------------*)
(*         Convert expressions                                                     *)
(*---------------------------------------------------------------------------------*)

val conv_exp_def = Define `
    (conv_exp (inR r) = isR (data_reg_index r)) /\
    (conv_exp (inC c) = isC c) /\
    (conv_exp (inE v) = isV (12 + v))`;

(*---------------------------------------------------------------------------------*)
(*         Compare an HSL state and CFL state                                      *)
(*---------------------------------------------------------------------------------*)

val same_content_def = Define `
    same_content ((rg,sk):TSTATE) (st:DSTATE) m =
      (!r. rg ' r = reade st (conv_exp (inR r))) /\
      (!i. i < m ==> (sk ' i = reade st (conv_exp (inE i))))
    `;

val same_content_thm = Q.store_thm (
    "same_content_htm",
    `!s st m. same_content s st m =
         !x. valid_TEXP x m ==> (tread s x = reade st (conv_exp x))`,

    SIMP_TAC std_ss [FORALL_TSTATE, FORALL_DSTATE] THEN
    RW_TAC std_ss [same_content_def] THEN
    EQ_TAC THEN
    RW_TAC std_ss [] THENL [
      Cases_on `x` THEN
        FULL_SIMP_TAC std_ss [tread_def, conv_exp_def, reade_def, read_thm, valid_TEXP_def, within_bound_def],
      POP_ASSUM (ASSUME_TAC o Q.SPEC `inR r`) THEN
        FULL_SIMP_TAC std_ss [tread_def, conv_exp_def, reade_def, read_thm, valid_TEXP_def, within_bound_def],
      Q.PAT_ASSUM `!x.k` (ASSUME_TAC o Q.SPEC `inE i`) THEN
        FULL_SIMP_TAC std_ss [tread_def, conv_exp_def, reade_def, read_thm, valid_TEXP_def, within_bound_def]
    ]
  );


val same_content_read = Q.store_thm (
    "same_content_read",
    `!s st m. same_content s st m /\ EVERY (\x.valid_TEXP x m) lst ==>
         (MAP (tread s) lst = MAP (reade st o conv_exp) lst)`,

    SIMP_TAC std_ss [FORALL_TSTATE, FORALL_DSTATE] THEN
    RW_TAC std_ss [same_content_def] THEN
    Induct_on `lst` THEN
    RW_TAC list_ss [] THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [tread_def, conv_exp_def, reade_def, read_thm, valid_TEXP_def, within_bound_def]
  );

(*---------------------------------------------------------------------------------*)
(*         Sufficient conditions to implement function calls correctly             *)
(*---------------------------------------------------------------------------------*)

val FC_OUTPUT_LEM = Q.store_thm (
    "FC_OUTPUT_LEM",
  `!s st m. valid_arg_list (caller_i, caller_o, callee_i, callee_o) /\
     WELL_FORMED (SC (SC pre body) post) /\ EVERY (\x.valid_TEXP x m) callee_o /\
     (!st. MAP (reade st o conv_exp) caller_i = MAP (reade (run_cfl pre st) o conv_exp) callee_i) /\
     (!s st. same_content s st m ==> same_content (transfer (empty_s,s) (callee_i,caller_i)) (run_cfl pre st) m) /\
     (!s st. same_content s st m ==> same_content (run_hsl S_hsl s) (run_cfl body st) m) /\
     (!st. MAP (reade st o conv_exp) callee_o = MAP (reade (run_cfl post st) o conv_exp) caller_o) /\
     same_content s st m
       ==> 
       (MAP (tread (run_hsl (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o)) s)) caller_o = 
        MAP (reade (run_cfl (SC (SC pre body) post) st) o conv_exp) caller_o)`,

   RW_TAC std_ss [valid_arg_list_def, run_hsl_def, WELL_FORMED_thm, SEMANTICS_OF_CFL] THEN 
   `(MAP (tread (transfer (s,s2) (caller_o,callee_o))) caller_o = MAP (tread s2) callee_o) /\
    (MAP (tread s) caller_i = MAP (tread s1) callee_i)` by (Q.UNABBREV_TAC `s1` THEN METIS_TAC [TRANSFER_THM]) THEN
   Q.UNABBREV_TAC `s2` THEN Q.UNABBREV_TAC `s1` THEN
   `MAP (tread (run_hsl S_hsl (transfer (empty_s,s) (callee_i,caller_i)))) callee_o = 
    MAP (reade (run_cfl body (run_cfl pre st)) o conv_exp) callee_o` by METIS_TAC [same_content_read] THEN
   FULL_SIMP_TAC std_ss []
  );

val MAP_LEM_1 = Q.store_thm (
    "MAP_LEM_1",
    `!x l f g. MEM x l /\ (MAP f l = MAP g l) ==> (f x = g x)`,
    Induct_on `l` THEN RW_TAC list_ss [] THEN
    METIS_TAC []
  );

val FC_SUFFICIENT_COND = Q.store_thm (
    "FC_SUFFICIENT_COND",

   `!s st m. valid_arg_list (caller_i, caller_o, callee_i, callee_o) /\
     WELL_FORMED (SC (SC pre body) post) /\ EVERY (\x.valid_TEXP x m) callee_o /\

     (!st. MAP (reade st o conv_exp) caller_i = MAP (reade (run_cfl pre st) o conv_exp) callee_i) /\
     (!s st. same_content s st m ==> same_content (transfer (empty_s,s) (callee_i,caller_i)) (run_cfl pre st) m) /\
     (!s st. same_content s st m ==> same_content (run_hsl S_hsl s) (run_cfl body st) m) /\
     (!st. MAP (reade st o conv_exp) callee_o = MAP (reade (run_cfl post st) o conv_exp) caller_o) /\

     (!x. ~(MEM x caller_o) /\ valid_TEXP x m ==> 
          (reade (run_cfl (SC (SC pre body) post) st) (conv_exp x) = reade st (conv_exp x)))
       ==> 
       same_content s st m ==>
       same_content (run_hsl (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o)) s)
                    (run_cfl (SC (SC pre body) post) st) m`,

    RW_TAC std_ss [] THEN
    IMP_RES_TAC FC_OUTPUT_LEM THEN
    NTAC 12 (POP_ASSUM (K ALL_TAC)) THEN
    Q.ABBREV_TAC `st1 = run_cfl (SC (SC pre body) post) st` THEN
    FULL_SIMP_TAC std_ss [same_content_thm] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `MEM x caller_o` THENL [
       Q.ABBREV_TAC `s1 = run_hsl (Fc (caller_i,callee_i) S_hsl (caller_o,callee_o)) s` THEN
           IMP_RES_TAC MAP_LEM_1 THEN
           FULL_SIMP_TAC std_ss [],

       FULL_SIMP_TAC std_ss [valid_arg_list_def, run_hsl_def, LET_THM] THEN
         METIS_TAC [TRANSFER_INTACT]
    ]
  );       

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing                                                        *)
(*---------------------------------------------------------------------------------*)

val saved_regs_list_def = Define `
    saved_regs_list = [isR 0; isR 1; isR 2; isR 3; isR 4; isR 5; isR 6; isR 7; isR 8; isR fp; isR ip; isR lr]`;

val mov_pointers_def = Define `
    mov_pointers =                               
      [MMOV R12 (MR R13);                      (* mov ip sp *)
       MSUB R11 R12 (MC 1w)]                   (* sub fp ip 1 *)
      `;

(* k = max (length caller_i, length caller_o) - length caller_i, n = #stack_variables *)

val pre_call_def = Define `
    pre_call (caller_i, callee_i) k n =
      (MSUB R13 R13 (MC (n2w k))) ::
      push_list (saved_regs_list ++ caller_i) ++
      [MADD R13 R13 (MC 12w)] ++
      mov_pointers ++
      pop_list callee_i
(*      [MSUB R13 R11 (MC (n2w (12 + n)))] *)
    `;

(*---------------------------------------------------------------------------------*)
(*      Theorems about pre-call processing                                         *)
(*---------------------------------------------------------------------------------*)

val MAP_LEM_2 = Q.store_thm (
    "MAP_LEM_2",
    `!l f g. (MAP f l = MAP g l) = (!i. i < LENGTH l ==> (f (EL i l) = g (EL i l)))`,
    Induct_on `l` THEN RW_TAC list_ss [] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Induct_on `i` THEN RW_TAC list_ss [],
      POP_ASSUM (ASSUME_TAC o Q.SPEC `0`) THEN
        FULL_SIMP_TAC list_ss [],
      Q.PAT_ASSUM `!i.k` (ASSUME_TAC o Q.SPEC `SUC i`) THEN
        FULL_SIMP_TAC list_ss []
    ]
  );

val MAP_LEM_3 = Q.store_thm (
    "MAP_LEM_3",
    `!l1 l2 f g. (!i. i < LENGTH l1 ==> (f (EL i l1) = g (EL i l2))) /\ 
       (LENGTH l1 = LENGTH l2) ==> (MAP f l1 = MAP g l2)`,
    Induct_on `l1` THEN Induct_on `l2` THEN
    RW_TAC list_ss [] THENL [
      Q.PAT_ASSUM `!i.k` (ASSUME_TAC o Q.SPEC `0`) THEN
        FULL_SIMP_TAC list_ss [],
      `(!i. i < LENGTH l1 ==> (f (EL i l1) = g (EL i l2)))` by (
         RW_TAC std_ss [] THEN
         Q.PAT_ASSUM `!i.k` (ASSUME_TAC o Q.SPEC `SUC i`) THEN
         FULL_SIMP_TAC list_ss []) THEN
        METIS_TAC []
    ]
  );

val valid_MEXP_def = Define `
    (valid_MEXP (isV i) bound = within_bound i (12 + bound)) /\
    (valid_MEXP (isR r) bound = valid_regs r) /\
    (valid_MEXP (isC c) bound = T) /\
    (valid_MEXP (isM m) bound = F)`;

val valid_MEXP_1_def = Define `
    (valid_MEXP_1 (isV i) bound = within_bound i (12 + bound)) /\
    (valid_MEXP_1 (isR r) bound = valid_exp_1 (isR r)) /\
    (valid_MEXP_1 (isC c) bound = T) /\
    (valid_MEXP_1 (isM m) bound = F)`;

val VALID_MEXP_1_exp_3 = Q.store_thm (
   "VALID_MEXP_1_exp_3",
   `!m l. EVERY (\x.valid_MEXP_1 x m) l ==>
      EVERY valid_exp_3 l`,
    GEN_TAC THEN MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    Cases_on `x` THEN RW_TAC std_ss [valid_MEXP_1_def, valid_exp_3_def, valid_exp_1_def]
  );

val VALID_TEXP_MEXP_1 = Q.store_thm (
   "VALID_TEXP_MEXP_1",
   `!l m. EVERY (\x.valid_TEXP x m) l ==>
      EVERY (\x. valid_MEXP_1 x m) (MAP conv_exp l)`,
   Induct_on `l` THEN
   SIMP_TAC list_ss [] THEN
   Cases_on `h` THEN RW_TAC arith_ss [conv_exp_def,valid_exp_def,valid_MEXP_1_def,valid_TEXP_def, within_bound_def] THEN
   Cases_on `T'` THEN RW_TAC std_ss [valid_exp_1_def, data_reg_index_def, valid_regs_def, 
       from_reg_index_thm, index_of_reg_def]
  );

val VALID_TEXP_MEXP = Q.store_thm (
   "VALID_TEXP_MEXP",
   `!l m. EVERY (\x.valid_TEXP x m) l ==>
      EVERY (\x. valid_MEXP x m) (MAP conv_exp l)`,
   Induct_on `l` THEN
   SIMP_TAC list_ss [] THEN
   Cases_on `h` THEN RW_TAC arith_ss [conv_exp_def,valid_exp_def,valid_MEXP_def,valid_TEXP_def, within_bound_def] THEN
   Cases_on `T'` THEN RW_TAC std_ss [valid_exp_1_def, data_reg_index_def, valid_regs_def, 
       from_reg_index_thm, index_of_reg_def]
  );

val VALID_MEXP_exp = Q.store_thm (
   "VALID_MEXP_exp",
   `!l m. EVERY (\x.valid_MEXP x m) l ==> EVERY valid_exp l`,
   Induct_on `l` THEN
   SIMP_TAC list_ss [] THEN
   Cases_on `h` THEN RW_TAC arith_ss [conv_exp_def,valid_exp_def,valid_MEXP_def, within_bound_def] THEN
   METIS_TAC []
  );


(*  standard frame structure 
      ip | saved pc |
      fp | saved lr |
         | saved sp |
         | saved fp |
         | ...      |
      sp |          |
*)

val standard_frame_def = Define `
   standard_frame st m = 
      (w2n (read st SP) <= w2n (read st FP) - (12 + m)) /\
      locate_ge (read st FP) (12 + m)`;

(*---------------------------------------------------------------------------------*)
(*      Push arguments                                                             *)
(*---------------------------------------------------------------------------------*)

val LEGAL_PUSH_EXP_LEM = Q.store_thm (
  "LEGAL_PUSH_EXP_LEM",
  `!st l m. standard_frame st m /\ EVERY (\x.valid_MEXP_1 x m) l
       ==> 
     (!i. i < LENGTH l ==> legal_push_exp st (EL i l) (PRE (LENGTH l) - i))`,

  RW_TAC std_ss [standard_frame_def, legal_push_exp_def] THEN
  FULL_SIMP_TAC std_ss [EVERY_EL] THEN RES_TAC THEN
  Cases_on `EL i l` THEN
  FULL_SIMP_TAC std_ss [conv_exp_def, addr_in_range_def, in_range_def, addr_of_def, valid_MEXP_1_def, 
            valid_exp_1_def, within_bound_def] THEN
  IMP_RES_TAC LOCATE_GE_GROW_LT THEN
  IMP_RES_TAC grow_lt_lem_1 THEN
  FULL_SIMP_TAC std_ss [locate_ge_def] THEN
  Q.ABBREV_TAC `x = read st SP` THEN
  Cases_on `w2n (read st FP) <= n + w2n (x:word32)` THEN
  RW_TAC std_ss [] THEN RW_TAC arith_ss []
  );

val tac1 = (fn g =>
            ((CONV_TAC (DEPTH_CONV (
              REWRITE_CONV [Once mdecode_def] THENC
              SIMP_CONV finmap_ss [write_thm, read_thm, toMEM_def, toEXP_def, toREG_def, index_of_reg_def]))) THEN
              FULL_SIMP_TAC std_ss [word_0_n2w, GSYM WORD_SUB_PLUS])
             g);


val PRE_CALL_PUSH_ARGUMENTS = Q.store_thm (
    "PRE_CALL_PUSH_ARGUMENTS",
    `!st l m k. locate_ge (read st SP) (k + LENGTH l) /\ 
          standard_frame st m /\ EVERY (\x.valid_MEXP_1 x m) l
       ==> 
    !i. i < LENGTH l ==>
     ((run_cfl (BLK ((MSUB R13 R13 (MC (n2w k))) :: push_list l)) st) '' 
        (isM (w2n (read st SP) - k - PRE (LENGTH l) + i)) = st '' (EL i l))`,
  
    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    RW_TAC std_ss [CFL_SEMANTICS_BLK] THEN
    tac1 THEN
    FULL_SIMP_TAC std_ss [read_thm, SP_def] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (13,regs ' 13 - n2w k),mem)` THEN
    `locate_ge (read st1 SP) (LENGTH l) /\ standard_frame st1 m /\ 
        (w2n (regs ' 13) - k = w2n (read st1 SP))` by ALL_TAC THENL [
       Q.UNABBREV_TAC `st1` THEN
         IMP_RES_TAC locate_ge_lem_1 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, locate_ge_def, SP_def, FP_def, standard_frame_def] THEN 
         `w2n ((n2w k):word32) = k` by (
            WORDS_TAC THEN `w2n (regs ' 13) < dimword (:i32)` by METIS_TAC [w2n_lt] THEN
            `k < dimword (:i32)` by RW_TAC arith_ss [] THEN POP_ASSUM MP_TAC THEN WORDS_TAC THEN RW_TAC arith_ss []) THEN
         Q.PAT_ASSUM `!i.k` (ASSUME_TAC o Q.SPEC `(n2w k):word32`) THEN
         FULL_SIMP_TAC arith_ss [],

    `legal_push_exp st1 (EL i l) (PRE (LENGTH l) - i)` by METIS_TAC [LEGAL_PUSH_EXP_LEM] THEN
    IMP_RES_TAC VALID_MEXP_1_exp_3 THEN
    IMP_RES_TAC PUSH_LIST_FUNCTIONALITY THEN
    FULL_SIMP_TAC std_ss [EVERY_EL] THEN RES_TAC THEN
    Q.UNABBREV_TAC `st1` THEN
    Cases_on `EL i l` THEN 
    FULL_SIMP_TAC finmap_ss [reade_def, read_thm, fp_def, valid_exp_3_def, valid_MEXP_1_def, valid_exp_1_def]
   ]
  );

val above_lem_1 = Q.store_thm (
  "above_lem_1",
  `!st n. i > w2n (read st SP)
       ==> ~addr_in_range st (isM i) (w2n (read st SP),w2n (read st SP) - n)`,
  RW_TAC arith_ss [addr_in_range_def, in_range_def, addr_of_def]
  );

val PRE_CALL_SANITY_1 = Q.store_thm (
    "PRE_CALL_SANITY_1",
    `!st l k m. locate_ge (read st SP) (k + LENGTH l) /\ EVERY (\x.valid_MEXP_1 x m) l
       ==> 
      let st' = run_cfl (BLK ((MSUB R13 R13 (MC (n2w k))) :: push_list l)) st in
        (!i. i > w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i))) /\
        (w2n (read st' SP) = w2n (read st SP) - (k + LENGTH l))`,
 
    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC std_ss [CFL_SEMANTICS_BLK] THEN
    tac1 THEN
    FULL_SIMP_TAC std_ss [LET_THM, read_thm, SP_def] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (13,regs ' 13 - n2w k),mem)` THEN
    `locate_ge (read st1 SP) (LENGTH l) /\ (w2n (regs ' 13) - k = w2n (read st1 SP))` by ALL_TAC THENL [
       Q.UNABBREV_TAC `st1` THEN
         IMP_RES_TAC locate_ge_lem_1 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, locate_ge_def, SP_def, FP_def] THEN 
         `w2n ((n2w k):word32) = k` by (
            WORDS_TAC THEN `w2n (regs ' 13) < dimword (:i32)` by METIS_TAC [w2n_lt] THEN
            `k < dimword (:i32)` by RW_TAC arith_ss [] THEN POP_ASSUM MP_TAC THEN WORDS_TAC THEN RW_TAC arith_ss []) THEN
         Q.PAT_ASSUM `!i.k` (ASSUME_TAC o Q.SPEC `(n2w k):word32`) THEN
         FULL_SIMP_TAC arith_ss [],

     RW_TAC std_ss [] THENL [
      `i > w2n (read st1 SP)` by RW_TAC arith_ss [] THEN
        IMP_RES_TAC above_lem_1 THEN
        POP_ASSUM (ASSUME_TAC o Q.SPEC `LENGTH (l:CFL_EXP list)`) THEN
        FULL_SIMP_TAC std_ss [] THEN
        `valid_exp_1 (isM i)` by RW_TAC std_ss [valid_exp_1_def] THEN
        IMP_RES_TAC VALID_MEXP_1_exp_3 THEN
        RW_TAC std_ss [PUSH_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
        FULL_SIMP_TAC arith_ss [SP_def, locate_ge_def]
      ]
    ]
  );


(*---------------------------------------------------------------------------------*)
(*      The callee pops arguments out                                              *)
(*---------------------------------------------------------------------------------*)

val LEGAL_POP_EXP_LEM = Q.store_thm (
  "LEGAL_POP_EXP_LEM",
  `!st l m. w2n (read st FP) <= w2n (read st SP) /\ EVERY (\x.valid_TEXP x m) l
       ==> 
     EVERY (\x.~addr_in_range st x (w2n (read st SP) + LENGTH (MAP conv_exp l), w2n (read st SP))) (MAP conv_exp l)`,

  REPEAT STRIP_TAC THEN
  IMP_RES_TAC VALID_EXP_LEM THEN
  FULL_SIMP_TAC list_ss [EVERY_EL, rich_listTheory.EL_MAP] THEN 
  RW_TAC std_ss [] THEN RES_TAC THEN
  Cases_on `EL n l` THEN
  FULL_SIMP_TAC std_ss [conv_exp_def, addr_in_range_def, in_range_def, addr_of_def, valid_exp_def, 
               valid_regs_lem, within_bound_def] THEN
  RW_TAC arith_ss []
  );

val UNIQUE_LIST_11 = Q.store_thm (
  "UNIQUE_LIST_11",
  `!l st. locate_ge (read st FP) (12 + m) /\ EVERY (\x. valid_TEXP x m) l /\ unique_list l ==>  
          unique_exp_list st (MAP conv_exp l)`,

  Induct_on `l` THEN RW_TAC list_ss [unique_exp_list_def, unique_list_def] THEN
    FULL_SIMP_TAC list_ss [EVERY_EL, rich_listTheory.EL_MAP] THEN
    RW_TAC std_ss [] THEN
    REPEAT (Q.PAT_ASSUM `!n.k` (ASSUME_TAC o Q.SPEC `n`)) THEN
    IMP_RES_TAC locate_ge_lem_1 THEN
    Cases_on `EL n l` THEN Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [locate_ge_def, conv_exp_def, eq_exp_def, eq_addr_def, addr_of_def, valid_TEXP_def] THENL [
      Cases_on `T''` THEN Cases_on `T'` THEN 
        FULL_SIMP_TAC std_ss [data_reg_index_def],
      METIS_TAC [],
      FULL_SIMP_TAC std_ss [within_bound_def] THEN RW_TAC arith_ss [] THEN STRIP_TAC THEN
        FULL_SIMP_TAC arith_ss []
    ]
  );

val grow_lt_lem_2 = Q.store_thm (
    "grow_lt_lem_2",
    `grow_lt (x:word32) (k:num) ==>
      !i. i <= k ==> (w2n (x + n2w i) = w2n x + i)`,
    RW_TAC arith_ss [grow_lt_def, word_add_def, w2n_n2w]
   );

val notC_LEM = Q.store_thm (
   "notC_LEM",
   `!l. EVERY notC l ==>
      EVERY ($~ o is_C) (MAP conv_exp l)`,
   Induct_on `l` THEN
   RW_TAC list_ss [] THEN
   Cases_on `h` THEN 
   FULL_SIMP_TAC std_ss [conv_exp_def, notC_def, is_C_def]
  );

val PRE_CALL_POP_ARGUMENTS = Q.store_thm (
    "PRE_CALL_POP_ARGUMENTS",
    `!st l m. grow_lt (read st SP) (12 + LENGTH l) /\ locate_ge (read st SP) (m + 1) /\ EVERY notC l /\
          unique_list l /\ EVERY (\x.valid_TEXP x m) l /\ (MAP conv_exp l = l')
       ==> 
    !i. i < LENGTH l' ==>
     ((run_cfl (BLK ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list l')) st) '' (EL i l') = 
           st '' (isM (12 + w2n (read st SP) + SUC i)))`,
  
    SIMP_TAC std_ss [FORALL_DSTATE, mov_pointers_def] THEN
    RW_TAC std_ss [APPEND, CFL_SEMANTICS_BLK] THEN
    NTAC 3 tac1 THEN
    FULL_SIMP_TAC std_ss [read_thm, SP_def] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (11,regs ' 13 + 12w - 1w) |+ (12,regs ' 13 + 12w) |+ (13,regs ' 13 + 12w),mem)` THEN

    `grow_lt (read st1 SP) (LENGTH (MAP conv_exp l)) /\ w2n (read st1 FP) <= w2n (read st1 SP) /\
     locate_ge (read st1 FP) (12 + m) /\ (w2n (regs ' 13) + 12 = w2n (read st1 SP))` by ALL_TAC THENL [
       Q.UNABBREV_TAC `st1` THEN
         IMP_RES_TAC locate_ge_lem_1 THEN
         IMP_RES_TAC grow_lt_lem_2 THEN
         `LENGTH (MAP conv_exp l) = LENGTH l` by METIS_TAC [LENGTH_MAP] THEN
         FULL_SIMP_TAC finmap_ss [read_thm, locate_ge_def, grow_lt_def, SP_def, FP_def] THEN 
         `12w - 1w = (11w:word32)` by WORDS_TAC THEN
         RW_TAC arith_ss [WORD_ADD_SUB_ASSOC],

    IMP_RES_TAC UNIQUE_LIST_11 THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN
      IMP_RES_TAC VALID_MEXP_exp THEN
      IMP_RES_TAC LEGAL_POP_EXP_LEM THEN
      `i < LENGTH l` by METIS_TAC [LENGTH_MAP] THEN
      IMP_RES_TAC notC_LEM THEN
      IMP_RES_TAC POP_LIST_FUNCTIONALITY THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
      FULL_SIMP_TAC arith_ss [EVERY_EL] THEN
      Q.UNABBREV_TAC `st1` THEN
      RW_TAC finmap_ss [reade_def, read_thm]
    ]
  );


val above_lem_2 = Q.store_thm (
    "above_lem_2",  
    `!i l st. EVERY (\x. valid_MEXP x m) l /\ i > w2n (read st FP)
       ==> EVERY (\x. ~eq_exp st (isM i) x) l`,

   RW_TAC std_ss [] THEN
   Q.PAT_ASSUM `EVERY k l` MP_TAC THEN
   MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
   Cases_on `x` THEN RW_TAC arith_ss [eq_exp_def, valid_MEXP_def, eq_addr_def, addr_of_def]
  );


val PRE_CALL_SANITY_2 = Q.store_thm (
    "PRE_CALL_SANITY_2",
    `!st. grow_lt (read st SP) (12 + LENGTH l) /\ EVERY (\x.valid_MEXP x m) l
       ==> 
      let st' = run_cfl (BLK ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list l)) st in
        !i. i > 12 + w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i)) /\
        (w2n (read st' SP) = w2n (read st SP) + 12 + (LENGTH l)) /\
        (w2n (read st' FP) = w2n (read st SP) + 11)`,

    SIMP_TAC std_ss [FORALL_DSTATE, mov_pointers_def] THEN
    SIMP_TAC std_ss [APPEND, CFL_SEMANTICS_BLK] THEN
    NTAC 3 tac1 THEN
    RW_TAC std_ss [read_thm, FP_def, SP_def, LET_THM] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (11,regs ' 13 + 12w - 1w) |+ (12,regs ' 13 + 12w) |+ (13,regs ' 13 + 12w),mem)` THEN

    `grow_lt (read st1 SP) (LENGTH l) /\ (w2n (regs ' 13) + 12 = w2n (read st1 SP)) /\
       (w2n (regs ' 13) + 11 = w2n (read st1 FP))` by (
       Q.UNABBREV_TAC `st1` THEN IMP_RES_TAC grow_lt_lem_2 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, grow_lt_def, SP_def, FP_def] THEN 
         `12w - 1w = (11w:word32)` by WORDS_TAC THEN
         RW_TAC arith_ss [WORD_ADD_SUB_ASSOC]) THEN
     
    IMP_RES_TAC VALID_MEXP_exp THENL [

      `i > w2n (read st1 FP)` by RW_TAC arith_ss [] THEN
        IMP_RES_TAC above_lem_2 THEN
        `valid_exp_2 (isM i)` by RW_TAC std_ss [valid_exp_2_def] THEN
        RW_TAC std_ss [POP_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] POP_LIST_SP_FP) THEN
        FULL_SIMP_TAC arith_ss [SP_def],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] POP_LIST_SP_FP) THEN
        FULL_SIMP_TAC arith_ss [FP_def]
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing lemmas                                                 *)
(*---------------------------------------------------------------------------------*)

val valid_MEXP_1_saved_regs = Q.store_thm (
    "valid_MEXP_1_saved_regs",
    `!m. EVERY (\x. valid_MEXP_1 x m) saved_regs_list`,
    RW_TAC list_ss [saved_regs_list_def, valid_MEXP_1_def] THEN
    RW_TAC std_ss [valid_exp_1_def, from_reg_index_thm, index_of_reg_def, fp_def, lr_def, ip_def]
  );

val PRE_CALL_PASS_ARGUMENTS_LEM_1 = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS_LEM_1", 
    `!st st' k l. 
       locate_ge (read st SP) (k + 13 + LENGTH l + m) /\ 
        (w2n (read st' SP) = w2n (read st SP) - (k + LENGTH (saved_regs_list ++ l))) ==> 
       grow_lt (read st' SP) (12 + LENGTH l) /\ locate_ge (read st' SP) (m + 1)`,
  
    RW_TAC list_ss [grow_lt_def, locate_ge_def, saved_regs_list_def] THENL [
      `w2n (read st SP) < dimword (:i32)` by METIS_TAC [w2n_lt] THEN
        RW_TAC arith_ss [],
      WORDS_TAC
    ]
  );

val PRE_CALL_PASS_ARGUMENTS_LEM_2 = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS_LEM_2", 
    `!x k m i j. locate_ge x (k + m) /\ 0 < m ==> 
         (j + (w2n x - (k + m)) + SUC i = w2n x - k - PRE m + (j + i))`,
    RW_TAC std_ss [locate_ge_def, PRE_SUB1, SUC_ONE_ADD] THEN
    Cases_on `m` THEN
    RW_TAC arith_ss [] 
  );

val EL_APPEND_3 = Q.store_thm (
    "EL_APPEND_3", 
    `!l1 l2 n. EL (LENGTH l1 + n) (l1 ++ l2) = EL n l2`,
    RW_TAC arith_ss [rich_listTheory.EL_APPEND2]
  );

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing accomplished the argument passing task                 *)
(*---------------------------------------------------------------------------------*)

val PRE_CALL_PASS_ARGUMENTS = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\ 
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\ 
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i) 
       ==> 
      !i. i < LENGTH caller_i ==> 
          ((run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::push_list (saved_regs_list ++ MAP conv_exp caller_i) ++ 
              ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i)))) st) '' 
           (EL i (MAP conv_exp callee_i)) = st '' (EL i (MAP conv_exp caller_i)))`,

      RW_TAC bool_ss [] THEN
      Q.ABBREV_TAC `l1 = [MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i)` THEN
      REWRITE_TAC [RUN_CFL_BLK_APPEND] THEN
      `EVERY (\x.valid_MEXP_1 x m1) (saved_regs_list ++ MAP conv_exp caller_i)` by 
         METIS_TAC [EVERY_APPEND, valid_MEXP_1_saved_regs, VALID_TEXP_MEXP_1] THEN
      Q.ABBREV_TAC `st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::
                      push_list (saved_regs_list ++ MAP conv_exp caller_i))) st` THEN
      `LENGTH (MAP conv_exp caller_i) = LENGTH caller_i` by METIS_TAC [LENGTH_MAP] THEN
      `locate_ge (read st SP) (k + LENGTH (saved_regs_list ++ MAP conv_exp caller_i))` by 
             FULL_SIMP_TAC list_ss [locate_ge_def, saved_regs_list_def] THEN
      `grow_lt (read st' SP) (12 + LENGTH callee_i) /\ locate_ge (read st' SP) (m2 + 1)` by
         (Q.UNABBREV_TAC `st'` THEN METIS_TAC [PRE_CALL_PASS_ARGUMENTS_LEM_1, 
           SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1]) THEN
      Q.UNABBREV_TAC `l1` THEN
      IMP_RES_TAC PRE_CALL_POP_ARGUMENTS THEN NTAC 31 (POP_ASSUM (K ALL_TAC)) THEN
      `i < LENGTH (MAP conv_exp callee_i)` by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN
      RW_TAC std_ss [] THEN NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN

      `LENGTH saved_regs_list = 12` by RW_TAC list_ss [saved_regs_list_def] THEN
      `0 < LENGTH (saved_regs_list ++ MAP conv_exp caller_i)` by RW_TAC list_ss [] THEN
      `12 + w2n (read st' SP) + SUC i = w2n (read st SP) - k - 
          PRE (LENGTH (saved_regs_list ++ MAP conv_exp caller_i)) + (12 + i)` by 
       (Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1, 
           PRE_CALL_PASS_ARGUMENTS_LEM_2]) THEN
      RW_TAC std_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
      Q.UNABBREV_TAC `st'` THEN
      `12 + i < LENGTH (saved_regs_list ++ MAP conv_exp caller_i)` by RW_TAC list_ss [] THEN
      IMP_RES_TAC PRE_CALL_PUSH_ARGUMENTS THEN
      RW_TAC list_ss [] THEN
      METIS_TAC [EL_APPEND_3, ADD_SYM]
  );

val PRE_CALL_PRE_CALL_THM = Q.store_thm (
    "PRE_CALL_PRE_CALL_THM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\ 
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\ 
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i) 
       ==> 
           (MAP (reade st o conv_exp) caller_i = 
            MAP (reade (run_cfl (BLK (pre_call (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) 
              o conv_exp) callee_i)`,

        RW_TAC std_ss [pre_call_def] THEN
        MATCH_MP_TAC MAP_LEM_3 THEN
        RW_TAC std_ss [] THEN
        `i < LENGTH (MAP conv_exp callee_i) /\ i < LENGTH (MAP conv_exp caller_i)` by METIS_TAC [LENGTH_MAP] THEN
        IMP_RES_TAC PRE_CALL_PASS_ARGUMENTS THEN NTAC 13 (POP_ASSUM (K ALL_TAC)) THEN
        METIS_TAC [rich_listTheory.EL_MAP, APPEND_ASSOC]
   );

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing accomplished the argument passing task                 *)
(*---------------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------------*)

val _ = export_theory();

