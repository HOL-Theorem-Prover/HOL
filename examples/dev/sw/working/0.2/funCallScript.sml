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
(*                                                                                 *)
(*   This implementation ensures that:                                             *)
(*     (1) the caller's frame and callee's frame locate in separate areas          *)
(*         in the memory.                                                          *)
(*     (2) the parameter/result passing and the body execution don't change        *)
(*         the values of stack variables in the caller's frame except those for    *)
(*         receiving results.                                                      *)
(*     (3) all register variables are pushed into memory before parameter passing  *)
(*         on function entry and then poped from memory before result passing on   *)
(*         function exit.                                                          *)
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
      (!r. rg ' (data_reg_index r) = reade st (conv_exp (inR r))) /\
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
   `!s st m1 m2. valid_arg_list (caller_i, caller_o, callee_i, callee_o) /\
     WELL_FORMED (SC (SC pre body) post) /\ EVERY (\x.valid_TEXP x m2) callee_o ==>
     let s1 = transfer (empty_s,s) (callee_i,caller_i) in
     let st1 = run_cfl pre st in
     let st2 = run_cfl body st1 in
     (MAP (reade st o conv_exp) caller_i = MAP (reade st1 o conv_exp) callee_i) /\
     same_content (run_hsl S_hsl s1) st2 m2 /\
     (MAP (reade st2 o conv_exp) callee_o = MAP (reade (run_cfl post st2) o conv_exp) caller_o)
       ==>
       (MAP (tread (run_hsl (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o) (m1,m2)) s)) caller_o =
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

val FC_SUFFICIENT_COND_LEM = Q.store_thm (
    "FC_SUFFICIENT_COND_LEM",

   `!s st m1 m2. valid_arg_list (caller_i, caller_o, callee_i, callee_o) /\
     WELL_FORMED (SC (SC pre body) post) /\ EVERY (\x.valid_TEXP x m2) callee_o /\
     same_content s st m1
      ==>
     let s1 = transfer (empty_s,s) (callee_i,caller_i) in
     let st1 = run_cfl pre st in
     let st2 = run_cfl body st1 in
     (MAP (reade st o conv_exp) caller_i = MAP (reade st1 o conv_exp) callee_i) /\
     same_content (run_hsl S_hsl s1) st2 m2 /\
     (MAP (reade st2 o conv_exp) callee_o = MAP (reade (run_cfl post st2) o conv_exp) caller_o) /\

     (!x. ~(MEM x caller_o) /\ valid_TEXP x m1 ==>
          (reade (run_cfl (SC (SC pre body) post) st) (conv_exp x) = reade st (conv_exp x)))
       ==>
       same_content (run_hsl (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o) (m1,m2)) s)
                    (run_cfl (SC (SC pre body) post) st) m1`,

    RW_TAC std_ss [] THEN
    Q.UNABBREV_TAC `s1` THEN Q.UNABBREV_TAC `st1` THEN Q.UNABBREV_TAC `st2` THEN
    IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] FC_OUTPUT_LEM) THEN
    Q.ABBREV_TAC `st1 = run_cfl (SC (SC pre body) post) st` THEN
    FULL_SIMP_TAC std_ss [same_content_thm] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `MEM x caller_o` THENL [
       Q.PAT_ASSUM `!m1.x` (ASSUME_TAC o Q.SPEC `m1`) THEN
           IMP_RES_TAC MAP_LEM_1 THEN
           FULL_SIMP_TAC std_ss [],

       FULL_SIMP_TAC std_ss [valid_arg_list_def, run_hsl_def, LET_THM] THEN
         METIS_TAC [TRANSFER_INTACT]
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing                                                        *)
(*---------------------------------------------------------------------------------*)

(* We save all registers instead of those modified by the callee for the sake of   *)
(* easier proof                                                                    *)

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
      pop_list callee_i ++
      [MSUB R13 R11 (MC (n2w (12 + n)))]
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

(*  A valid parameter (which is trasferred from the caller to the callee) can be a stack variable, a constant and a register variable *)
(*  A valid argument (which accepts the parameter), on the other hand, can only be either a stack variable or register variable *)

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

val VALID_MEXP_MEXP_1 = Q.store_thm (
   "VALID_MEXP_MEXP_1",
   `!m l. EVERY (\x.valid_MEXP x m) l ==>
           EVERY (\x.valid_MEXP_1 x m) l`,
    GEN_TAC THEN MATCH_MP_TAC listTheory.EVERY_MONOTONIC THEN
    Cases_on `x` THEN RW_TAC std_ss [valid_MEXP_1_def, valid_MEXP_def] THEN
    FULL_SIMP_TAC std_ss [valid_regs_def, valid_exp_1_def]
  );

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
      ip | saved lr |
      fp | saved sp |
         | saved fp |
         | saved r8 |
         | ...      |
         | saved r0 |
         | local V0 |  the first local(stack) variable
         | ...      |
         | local Vm |  the last local(stack) variable
      sp |          |  the first avaible empty slot
*)

val standard_frame_def = Define `
   standard_frame st m =
      (w2n (read st SP) <= w2n (read st FP) - (12 + m)) /\
      locate_ge (read st FP) (12 + m)`;

(*---------------------------------------------------------------------------------*)
(*    The caller pushes parameters into the stack                                  *)
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
            WORDS_TAC THEN `w2n (regs ' 13) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
            `k < dimword (:32)` by RW_TAC arith_ss [] THEN POP_ASSUM MP_TAC THEN WORDS_TAC THEN RW_TAC arith_ss []) THEN
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
            WORDS_TAC THEN `w2n (regs ' 13) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
            `k < dimword (:32)` by RW_TAC arith_ss [] THEN POP_ASSUM MP_TAC THEN WORDS_TAC THEN RW_TAC arith_ss []) THEN
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
(*      The callee pops the parameters out of the stack                            *)
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
        (!i. i > 12 + w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i))) /\
        (w2n (read st' SP) = w2n (read st SP) + 12 + (LENGTH l)) /\
        (w2n (read st' FP) = w2n (read st SP) + 11) /\
        (w2n (read st' IP) = w2n (read st' FP) + 1)`,

    SIMP_TAC std_ss [FORALL_DSTATE, mov_pointers_def] THEN
    SIMP_TAC std_ss [APPEND, CFL_SEMANTICS_BLK] THEN
    NTAC 3 tac1 THEN
    SIMP_TAC std_ss [read_thm, FP_def, SP_def, LET_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    Q.ABBREV_TAC `st1 = (regs |+ (11,regs ' 13 + 12w - 1w) |+ (12,regs ' 13 + 12w) |+ (13,regs ' 13 + 12w),mem)` THEN

    `grow_lt (read st1 SP) (LENGTH l) /\ (w2n (regs ' 13) + 12 = w2n (read st1 SP)) /\
       (w2n (regs ' 13) + 11 = w2n (read st1 FP)) /\ (w2n (read st1 IP) = w2n (read st1 FP) + 1)` by (
       Q.UNABBREV_TAC `st1` THEN IMP_RES_TAC grow_lt_lem_2 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, grow_lt_def, SP_def, FP_def, IP_def] THEN
         `12w - 1w = (11w:word32)` by WORDS_TAC THEN
         RW_TAC arith_ss [WORD_ADD_SUB_ASSOC]) THEN

    IMP_RES_TAC VALID_MEXP_exp THEN STRIP_TAC THENL [
      REPEAT STRIP_TAC THEN
        `i > w2n (read st1 FP)` by RW_TAC arith_ss [] THEN
        IMP_RES_TAC above_lem_2 THEN
        `valid_exp_2 (isM i)` by RW_TAC std_ss [valid_exp_2_def] THEN
        RW_TAC std_ss [POP_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] POP_LIST_SP_FP) THEN
        FULL_SIMP_TAC arith_ss [SP_def, FP_def, IP_def]
    ]
  );

val above_lem_3 = Q.store_thm (
    "above_lem_3",
    `!i l st. EVERY (\x. valid_TEXP x m) l /\ i > w2n (read st FP) - 12
       ==> EVERY (\x. ~eq_exp st (isM i) x) (MAP conv_exp l)`,

   Induct_on `l` THEN RW_TAC list_ss [] THEN
   Cases_on `h` THEN RW_TAC arith_ss [eq_exp_def, valid_MEXP_def, eq_addr_def, addr_of_def,
         conv_exp_def, within_bound_def]
  );

val PRE_CALL_SANITY_2' = Q.store_thm (
    "PRE_CALL_SANITY_2'",
    `!st. grow_lt (read st SP) (12 + LENGTH l) /\ EVERY (\x.valid_TEXP x m) l
       ==>
      let st' = run_cfl (BLK ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp l))) st in
        (!i. i > w2n (read st SP) - 1 ==> (st '' (isM i) = st' '' (isM i)))`,

    SIMP_TAC std_ss [FORALL_DSTATE, mov_pointers_def] THEN
    SIMP_TAC std_ss [APPEND, CFL_SEMANTICS_BLK] THEN
    NTAC 3 tac1 THEN
    RW_TAC std_ss [SP_def, LET_THM] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (11,regs ' 13 + 12w - 1w) |+ (12,regs ' 13 + 12w) |+ (13,regs ' 13 + 12w),mem)` THEN
    `grow_lt (read st1 SP) (LENGTH (MAP conv_exp l)) /\ (w2n (read st1 FP) = w2n (read (regs,mem) SP) + 11)`
       by (Q.UNABBREV_TAC `st1` THEN IMP_RES_TAC grow_lt_lem_2 THEN
        `12w - 1w = (11w:word32)` by WORDS_TAC THEN FULL_SIMP_TAC finmap_ss [read_thm, grow_lt_def, LENGTH_MAP,
              FP_def, SP_def] THEN RW_TAC arith_ss [WORD_ADD_SUB_ASSOC]) THEN

    `i > w2n (read st1 FP) - 12` by RW_TAC arith_ss [SP_def] THEN
        IMP_RES_TAC above_lem_3 THEN
        IMP_RES_TAC VALID_TEXP_MEXP THEN
        IMP_RES_TAC VALID_MEXP_exp THEN
        `valid_exp_2 (isM i)` by RW_TAC std_ss [valid_exp_2_def] THEN
        RW_TAC std_ss [POP_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def]
  );

(*---------------------------------------------------------------------------------*)
(*      Lemmas bout pre-call processing                                            *)
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
      `w2n (read st SP) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
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
(*   The pre-call processing passes the parameters.                                *)
(*   We need to keep track of how sp,fp and ip are changed.                        *)
(*   Note that r0-r8,fp,ip and lr are also pushed into the stack                   *)
(*---------------------------------------------------------------------------------*)

val tac3 =
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
      Q.UNABBREV_TAC `l1`
    ;


val PRE_CALL_SANITY_3 = Q.store_thm (
    "PRE_CALL_SANITY_3",
    ` locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
        let st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::push_list (saved_regs_list ++ MAP conv_exp caller_i) ++
              ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i)))) st in
          (!i. i > w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i))) /\
          (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
          (w2n (read st' IP) = w2n (read st' FP) + 1)`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SIMP_TAC std_ss [LET_THM] THEN
      tac3 THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN
      `grow_lt (read st' SP) (12 + LENGTH (MAP conv_exp callee_i))` by METIS_TAC [LENGTH_MAP] THEN
      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_2) THEN
      NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN RW_TAC std_ss [] THENL [

         REPEAT (Q.PAT_ASSUM `w2n x = y` (K ALL_TAC)) THEN
           `i > 12 + w2n (read st' SP)` by
             (`w2n (read st' SP) = w2n (read st SP) - (k + LENGTH (saved_regs_list ++ MAP conv_exp caller_i))` by
               (Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1]) THEN
             `LENGTH saved_regs_list = 12` by RW_TAC list_ss [saved_regs_list_def] THEN
             FULL_SIMP_TAC list_ss [locate_ge_def]) THEN
           RES_TAC THEN POP_ASSUM ((fn th => REWRITE_TAC [th]) o GSYM) THEN
           Q.UNABBREV_TAC `st'` THEN
           IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1),

         Q.UNABBREV_TAC `st'` THEN
           IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1) THEN
           RW_TAC std_ss [] THEN NTAC 11 (POP_ASSUM (K ALL_TAC)) THEN
           `LENGTH saved_regs_list = 12` by RW_TAC list_ss [saved_regs_list_def] THEN
           FULL_SIMP_TAC list_ss [locate_ge_def]
      ]
  );


val PRE_CALL_SAVED_REGS_LEM = Q.store_thm (
    "PRE_CALL_SAVED_REGS_LEM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
         let st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::push_list (saved_regs_list ++ MAP conv_exp caller_i) ++
              ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i)))) st in
       !i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SIMP_TAC std_ss [LET_THM] THEN
      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_3) THEN NTAC 40 (POP_ASSUM (K ALL_TAC)) THEN
      RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
      tac3 THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN
      `grow_lt (read st' SP) (12 + LENGTH (MAP conv_exp callee_i))` by METIS_TAC [LENGTH_MAP] THEN
      `w2n (read st SP) - (k + LENGTH caller_i) - 1 - 10 + i > w2n (read st' SP) - 1` by
             (`w2n (read st' SP) = w2n (read st SP) - (k + LENGTH (saved_regs_list ++ MAP conv_exp caller_i))` by
               (Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1]) THEN
             `LENGTH saved_regs_list = 12` by RW_TAC list_ss [saved_regs_list_def] THEN
             RW_TAC std_ss [LENGTH_APPEND] THEN NTAC 17 (POP_ASSUM (K ALL_TAC)) THEN
             FULL_SIMP_TAC arith_ss [locate_ge_def]
             ) THEN
      IMP_RES_TAC (GSYM (SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_2')) THEN
      RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN

      `LENGTH saved_regs_list = 12` by RW_TAC list_ss [saved_regs_list_def] THEN STRIP_TAC THEN
      `w2n (read st SP) - (k + LENGTH caller_i) - 1 - 10 + i =
           w2n (read st SP) - k - PRE (LENGTH (saved_regs_list ++ MAP conv_exp caller_i)) + i` by (
         NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 16 (POP_ASSUM (K ALL_TAC)) THEN
         RW_TAC std_ss [LENGTH_APPEND, LENGTH_MAP] THEN
         FULL_SIMP_TAC arith_ss [locate_ge_def, PRE_SUB1]) THEN
      RW_TAC std_ss [] THEN

      `i < LENGTH (saved_regs_list ++ MAP conv_exp caller_i)` by METIS_TAC
             [LENGTH_APPEND, LENGTH_MAP, LESS_IMP_LESS_ADD] THEN
      IMP_RES_TAC PRE_CALL_PUSH_ARGUMENTS THEN
      Q.UNABBREV_TAC `st'` THEN
      RW_TAC list_ss [rich_listTheory.EL_APPEND1]
  );

(*---------------------------------------------------------------------------------*)
(*      Pre-call processing accomplished the argument passing task                 *)
(*---------------------------------------------------------------------------------*)

val PRE_CALL_PASS_ARGUMENTS_LEM = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS_LEM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
      !i. i < LENGTH caller_i ==>
          ((run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::push_list (saved_regs_list ++ MAP conv_exp caller_i) ++
              ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i)))) st) ''
           (EL i (MAP conv_exp callee_i)) = st '' (EL i (MAP conv_exp caller_i)))`,

      RW_TAC bool_ss [] THEN
      tac3 THEN
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


(*---------------------------------------------------------------------------------*)
(*      Some Lemmas                                                                *)
(*---------------------------------------------------------------------------------*)

val MOD_LE = Q.store_thm (
    "MOD_LE",
    `!i n. 0 < n ==> i MOD n <= i`,
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC (Q.SPECL [`\j. j <= i`,`i`,`n`] MOD_ELIM) THEN
    FULL_SIMP_TAC arith_ss []
  );

val locate_ge_lem_3 = Q.store_thm (
    "locate_ge_lem_3",
    `!x k.locate_ge x k ==> !i. i <= k ==> (w2n (x - n2w i) = w2n x - i)`,
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC locate_ge_lem_1 THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `n2w i:word32`) THEN
    FULL_SIMP_TAC std_ss [locate_ge_def] THEN
    `w2n x < dimword (:32)` by RW_TAC arith_ss [w2n_lt] THEN
    `w2n (n2w i:word32) = i` by RW_TAC arith_ss [w2n_n2w] THEN
    METIS_TAC [MOD_LE, LESS_EQ_TRANS]
  );

val sub_sp_lem_1 = Q.store_thm (
    "sub_sp_lem_1",
    `!st m. locate_ge (read st FP) (12 + m) ==>
         let st1 = run_cfl (BLK [MSUB R13 R11 (MC (n2w (12 + m)))]) st in
       (!i. st1 '' isM i = st '' isM i) /\
      (w2n (read st1 FP) = w2n (read st FP)) /\
      (w2n (read st1 IP) = w2n (read st IP)) /\
      (w2n (read st1 SP) = w2n (read st FP) - (12 + m)) /\
      (!l. EVERY (\x.valid_TEXP x m) l ==> !i. i < LENGTH l ==>
          (st1 '' (EL i (MAP conv_exp l)) = st '' (EL i (MAP conv_exp l))))`,

   SIMP_TAC std_ss [FORALL_DSTATE, APPEND, CFL_SEMANTICS_BLK] THEN
   tac1 THEN
   RW_TAC finmap_ss [LET_THM, FP_def, IP_def, SP_def, read_thm, reade_def] THENL [
     IMP_RES_TAC locate_ge_lem_3 THEN RW_TAC arith_ss [],

     IMP_RES_TAC VALID_TEXP_MEXP THEN
     IMP_RES_TAC VALID_MEXP_exp THEN
     `i < LENGTH (MAP conv_exp l)` by METIS_TAC [LENGTH_MAP] THEN
     FULL_SIMP_TAC std_ss [EVERY_EL] THEN RES_TAC THEN
     Cases_on `EL i (MAP conv_exp l)` THEN
     FULL_SIMP_TAC finmap_ss [tread_def, conv_exp_def, reade_def, read_thm,
         valid_exp_def, valid_regs_lem, fp_def, within_bound_def]
  ]
 );

(*---------------------------------------------------------------------------------*)
(*      An optimization on the implementation of register saving                   *)
(*---------------------------------------------------------------------------------*)

val [FOLDL_NIL, FOLDL_CONS] = CONJUNCTS FOLDL;

val PUSH_TAC =
    CONV_TAC (DEPTH_CONV (REWRITE_CONV [Once mdecode_def, pushL_def])) THEN
    REWRITE_TAC [GSYM rich_listTheory.MAP_REVERSE, REVERSE_DEF, APPEND, MAP, LENGTH] THEN
    SIMP_TAC finmap_ss [read_thm] THEN
    CONV_TAC (DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
        THENC RATOR_CONV (RAND_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV
                THENC REWRITE_CONV [read_thm, write_thm, pair_case_def]
                THENC reduceLib.REDUCE_CONV)))) THEN
    SIMP_TAC finmap_ss [write_thm];

val tac4 = (fn g =>
            ((CONV_TAC (DEPTH_CONV (
              REWRITE_CONV [Once mdecode_def] THENC
              SIMP_CONV finmap_ss [write_thm, read_thm, toEXP_def, toMEM_def, toREG_def, index_of_reg_def]))))
             g);

val saved_regs_list_thm_1 = Q.store_thm (
    "saved_regs_list_thm_1",
    `!st. locate_ge (read st SP) 12 ==>
      (run_cfl (BLK (push_list (saved_regs_list))) st =
        run_cfl (BLK [MPUSH 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]]) st)`,

  SIMP_TAC std_ss [FORALL_DSTATE, saved_regs_list_def, push_list_def, push_one_def] THEN
  RW_TAC std_ss [APPEND, CFL_SEMANTICS_BLK, from_reg_index_thm, fp_def, ip_def, lr_def] THEN
  NTAC 25 tac4 THEN PUSH_TAC THEN
  `(1w + 1w = 2w:word32) /\ (2w + 1w = 3w:word32) /\ (3w + 1w = 4w:word32) /\ (4w + 1w = 5w:word32) /\
   (5w + 1w = 6w:word32) /\ (6w + 1w = 7w:word32) /\ (7w + 1w = 8w:word32) /\ (8w + 1w = 9w:word32) /\
   (9w + 1w = 10w:word32) /\ (10w + 1w = 11w:word32) /\ (11w + 1w = 12w:word32)` by WORDS_TAC THEN
  RW_TAC std_ss [GSYM WORD_SUB_PLUS, WORD_ADD_ASSOC] THEN
  IMP_RES_TAC locate_ge_lem_3 THEN
  FULL_SIMP_TAC arith_ss [SP_def, read_thm]
  );

val push_list_append = Q.store_thm (
    "push_list_append",
    `!l1 l2. push_list (l1 ++ l2) = push_list l2 ++ push_list l1`,
    Induct_on `l1` THEN RW_TAC list_ss [push_list_def]
   );

val saved_regs_list_thm_2 = Q.store_thm (
    "saved_regs_list_thm_2",
   `!st l m. locate_ge (read st SP) (k + 12 + LENGTH l) /\ EVERY (\x.valid_MEXP_1 x m) l ==>
     (run_cfl (BLK ((MSUB R13 R13 (MC (n2w k))) :: push_list (saved_regs_list ++ l))) st =
      run_cfl (BLK ((MSUB R13 R13 (MC (n2w k))) :: (APPEND (push_list l) [MPUSH 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]]))) st)`,

   RW_TAC std_ss [GSYM APPEND, push_list_append, RUN_CFL_BLK_APPEND] THEN
   `locate_ge (read st SP) (k + LENGTH l)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
   Q.ABBREV_TAC `st1 = run_cfl (BLK (MSUB R13 R13 (MC (n2w k))::push_list l)) st` THEN
   `w2n (read st1 SP) = w2n (read st SP) - (k + LENGTH l)` by (Q.UNABBREV_TAC `st1` THEN
       METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_1]) THEN
   `locate_ge (read st1 SP) 12`  by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
   RW_TAC std_ss [saved_regs_list_thm_1]
  );

val pre_call_2_def = Define `
    pre_call_2 (caller_i, callee_i) k n =
      (MSUB R13 R13 (MC (n2w k))) ::
      push_list caller_i ++
      [MPUSH 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++
      [MADD R13 R13 (MC 12w)] ++
      mov_pointers ++
      pop_list callee_i ++
      [MSUB R13 R11 (MC (n2w (12 + n)))]
    `;


val saved_regs_list_thm_3 = Q.store_thm (
    "saved_regs_list_thm_3",
   `!st l k m1 m2. locate_ge (read st SP) (k + 12 + LENGTH caller_i) /\ EVERY (\x.valid_TEXP x m1) caller_i ==>
     (run_cfl (BLK (pre_call (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st =
      run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st)`,

   RW_TAC std_ss [pre_call_def, pre_call_2_def] THEN
   IMP_RES_TAC VALID_TEXP_MEXP_1 THEN
   `MSUB R13 R13 (MC (n2w k)):: push_list (saved_regs_list ++ MAP conv_exp caller_i) ++ [MADD R13 R13 (MC 12w)] ++
     mov_pointers ++ pop_list (MAP conv_exp callee_i) ++ [MSUB R13 R11 (MC (n2w (12 + m2)))] =
     MSUB R13 R13 (MC (n2w k)):: push_list (saved_regs_list ++ MAP conv_exp caller_i) ++ ([MADD R13 R13 (MC 12w)] ++
     mov_pointers ++ pop_list (MAP conv_exp callee_i) ++ [MSUB R13 R11 (MC (n2w (12 + m2)))])` by RW_TAC list_ss [] THEN
   `MSUB R13 R13 (MC (n2w k))::push_list (MAP conv_exp caller_i) ++ [MPUSH 13 [0; 1; 2; 3; 4; 5; 6; 7; 8; fp; ip; lr]] ++
     [MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i) ++ [MSUB R13 R11 (MC (n2w (12 + m2)))] =
    MSUB R13 R13 (MC (n2w k))::(push_list (MAP conv_exp caller_i) ++ [MPUSH 13 [0; 1; 2; 3; 4; 5; 6; 7; 8; fp; ip; lr]])
     ++ ([MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i) ++ [MSUB R13 R11
       (MC (n2w (12 + m2)))])` by RW_TAC list_ss [] THEN
   RW_TAC bool_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
   `locate_ge (read st SP) (k + 12 + LENGTH (MAP conv_exp caller_i))` by METIS_TAC [LENGTH_MAP] THEN
   METIS_TAC [RUN_CFL_BLK_APPEND, saved_regs_list_thm_2]
  );

(*---------------------------------------------------------------------------------*)
(*      Main theorems about pre-call processing                                    *)
(*---------------------------------------------------------------------------------*)

val PRE_CALL_SANITY_THM = Q.store_thm (
    "PRE_CALL_SANITY_THM",
    ` locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
        let st' = run_cfl (BLK (pre_call (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st in
          (!i. i > w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i))) /\
          (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
          (w2n (read st' IP) = w2n (read st' FP) + 1) /\
          (w2n (read st' SP) = w2n (read st' FP) - (12 + m2))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SIMP_TAC std_ss [pre_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k)):: push_list (saved_regs_list ++ MAP conv_exp caller_i)
                     ++ [MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i))) st` THEN
      `(!i. i > w2n (read st SP) ==> (st '' isM i = st' '' isM i)) /\
          (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
          (w2n (read st' IP) = w2n (read st' FP) + 1)` by (
         Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_3, APPEND_ASSOC]) THEN
      `locate_ge (read st' FP) (12 + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      RW_TAC std_ss [LET_THM, SIMP_RULE std_ss [LET_THM] sub_sp_lem_1]
  );

val PRE_CALL_SAVED_REGS_THM = Q.store_thm (
    "PRE_CALL_SAVED_REGS_THM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
         let st' =  run_cfl (BLK (pre_call (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st in
       !i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SIMP_TAC std_ss [pre_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k)):: push_list (saved_regs_list ++ MAP conv_exp caller_i)
                     ++ [MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i))) st` THEN
      `!i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))` by (
         Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SAVED_REGS_LEM, APPEND_ASSOC]) THEN
       `(w2n (read st SP) - (k + LENGTH callee_i) - 1 = w2n (read st' FP))` by (
         Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_3, APPEND_ASSOC]) THEN
      `locate_ge (read st' FP) (12 + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      RW_TAC std_ss [LET_THM, SIMP_RULE std_ss [LET_THM] sub_sp_lem_1]
  );


val PRE_CALL_PASS_ARGUMENTS_THM = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS_THM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
      !i. i < LENGTH caller_i ==>
          ((run_cfl (BLK (pre_call (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) ''
           (EL i (MAP conv_exp callee_i)) = st '' (EL i (MAP conv_exp caller_i)))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SIMP_TAC std_ss [pre_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st' = run_cfl (BLK (MSUB R13 R13 (MC (n2w k)):: push_list (saved_regs_list ++ MAP conv_exp caller_i)
                     ++ [MADD R13 R13 (MC 12w)] ++ mov_pointers ++ pop_list (MAP conv_exp callee_i))) st` THEN
      `!i. i < LENGTH caller_i ==> (st' '' (EL i (MAP conv_exp callee_i)) = st '' (EL i (MAP conv_exp caller_i)))` by (
         Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_PASS_ARGUMENTS_LEM, APPEND_ASSOC]) THEN
       `(w2n (read st SP) - (k + LENGTH callee_i) - 1 = w2n (read st' FP))` by (
         Q.UNABBREV_TAC `st'` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_3, APPEND_ASSOC]) THEN
      `locate_ge (read st' FP) (12 + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      RW_TAC std_ss [LET_THM, SIMP_RULE std_ss [LET_THM] sub_sp_lem_1]
  );

(*---------------------------------------------------------------------------------*)
(*      Main theorems about pre-call processing                                    *)
(*      After the optimization on register saving                                  *)
(*---------------------------------------------------------------------------------*)

val PRE_CALL_SANITY_THM_2 = Q.store_thm (
    "PRE_CALL_SANITY_THM_2",
    ` locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
        let st' = run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st in
          (!i. i > w2n (read st SP) ==> (st '' (isM i) = st' '' (isM i))) /\
          (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
          (w2n (read st' IP) = w2n (read st' FP) + 1) /\
          (w2n (read st' SP) = w2n (read st' FP) - (12 + m2))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      `locate_ge (read st SP) (k + 12 + LENGTH caller_i)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      METIS_TAC [saved_regs_list_thm_3, PRE_CALL_SANITY_THM]
  );

val PRE_CALL_SAVED_REGS_THM_2 = Q.store_thm (
    "PRE_CALL_SAVED_REGS_THM_2",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
         let st' =  run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st in
       !i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      `locate_ge (read st SP) (k + 12 + LENGTH caller_i)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      METIS_TAC [saved_regs_list_thm_3, PRE_CALL_SAVED_REGS_THM]
  );

val PRE_CALL_PASS_ARGUMENTS_THM_2 = Q.store_thm (
    "PRE_CALL_PASS_ARGUMENTS_THM_2",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
      !i. i < LENGTH caller_i ==>
          ((run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) ''
           (EL i (MAP conv_exp callee_i)) = st '' (EL i (MAP conv_exp caller_i)))`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      `locate_ge (read st SP) (k + 12 + LENGTH caller_i)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      METIS_TAC [saved_regs_list_thm_3, PRE_CALL_PASS_ARGUMENTS_THM]
  );

(*---------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------------*)
(*      Post-call processing                                                       *)
(*---------------------------------------------------------------------------------*)

val post_call_def = Define `
    post_call (caller_o, callee_o) n =
      (MADD R13 R12 (MC (n2w (LENGTH callee_o)))) ::  (* add sp ip #callee_o *)
      push_list callee_o ++
      [MSUB R13 R11 (MC 11w)] ++                      (* sub sp fp 12 *)
      [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++
      pop_list caller_o ++
      [MSUB R13 R11 (MC (n2w (12 + n)))]
    `;

(*---------------------------------------------------------------------------------*)
(*      The callee pushed results into the stack                                   *)
(*---------------------------------------------------------------------------------*)

val LEGAL_PUSH_EXP_LEM_2 = Q.store_thm (
  "LEGAL_PUSH_EXP_LEM_2",
  `!st l m. w2n (read st FP) + LENGTH l < w2n (read st SP) /\ EVERY (\x.valid_MEXP x m) l
       ==>
     (!i. i < LENGTH l ==> legal_push_exp st (EL i l) (PRE (LENGTH l) - i))`,

  RW_TAC std_ss [legal_push_exp_def] THENL [
    FULL_SIMP_TAC std_ss [EVERY_EL] THEN RES_TAC THEN
      Cases_on `EL i l` THEN
      FULL_SIMP_TAC std_ss [conv_exp_def, addr_in_range_def, in_range_def, addr_of_def, valid_MEXP_def,
            valid_regs_lem, within_bound_def] THEN
      `w2n (read st FP) <= n + w2n (read st SP)` by RW_TAC arith_ss [] THEN
      RW_TAC std_ss [] THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
      Cases_on `w2n (read st SP) < PRE (LENGTH l) - i + (w2n (read st FP) - n)` THEN
      `PRE (LENGTH l) - i < LENGTH l /\ (w2n (read st FP) - n <= w2n (read st SP))` by RW_TAC arith_ss [] THEN
      RW_TAC arith_ss [LESS_MONO_ADD_EQ],

   IMP_RES_TAC VALID_MEXP_exp THEN
      METIS_TAC [EVERY_EL, valid_exp_thm]
   ]
  );


val POST_CALL_PUSH_RESULTS = Q.store_thm (
    "POST_CALL_PUSH_RESULTS",
    `!st l m k. grow_lt (read st IP) (LENGTH l) /\ EVERY (\x.valid_MEXP x m) l /\
       (w2n (read st IP) = w2n (read st FP) + 1) ==>
      !i. i < LENGTH l ==>
         ((run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH l))) :: push_list l)) st) ''
           (isM (w2n (read st FP) + 1 + SUC i)) = st '' (EL i l))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    RW_TAC std_ss [CFL_SEMANTICS_BLK] THEN
    tac1 THEN
    FULL_SIMP_TAC std_ss [read_thm, SP_def] THEN
    Q.ABBREV_TAC `st1 = (regs |+ (13,regs ' 12 + n2w (LENGTH l)),mem)` THEN
    `locate_ge (read st1 SP) (LENGTH l) /\ w2n (read st1 FP) + LENGTH l < w2n (read st1 SP) /\
        (w2n (read st1 SP) = w2n (read (regs,mem) IP) + LENGTH l)` by (Q.UNABBREV_TAC `st1` THEN
         IMP_RES_TAC grow_lt_lem_1 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, locate_ge_def, SP_def, FP_def, IP_def, grow_lt_def]) THEN

    `legal_push_exp st1 (EL i l) (PRE (LENGTH l) - i)` by METIS_TAC [LEGAL_PUSH_EXP_LEM_2] THEN
    IMP_RES_TAC VALID_MEXP_MEXP_1 THEN
    IMP_RES_TAC VALID_MEXP_1_exp_3 THEN
    IMP_RES_TAC PUSH_LIST_FUNCTIONALITY THEN
    `w2n (read st1 SP) - PRE (LENGTH l) + i = w2n (read (regs,mem) FP) + 1 + SUC i` by
          FULL_SIMP_TAC arith_ss [PRE_SUB1, locate_ge_def] THEN
    FULL_SIMP_TAC std_ss [EVERY_EL] THEN RES_TAC THEN
    Q.UNABBREV_TAC `st1` THEN
    Cases_on `EL i l` THEN
    FULL_SIMP_TAC finmap_ss [reade_def, read_thm, fp_def, valid_exp_3_def, valid_MEXP_1_def, valid_exp_1_def]
  );

val below_lem_1 = Q.store_thm (
  "below_lem_1",
  `!st n. i <= w2n (read st SP) - n
       ==> ~addr_in_range st (isM i) (w2n (read st SP),w2n (read st SP) - n)`,
  RW_TAC arith_ss [addr_in_range_def, in_range_def, addr_of_def]
  );

val POST_CALL_SANITY_1 = Q.store_thm (
    "POST_CALL_SANITY_1",
    `!st l m k. grow_lt (read st IP) (LENGTH l) /\ EVERY (\x.valid_MEXP x m) l /\
       (w2n (read st IP) = w2n (read st FP) + 1)
       ==>
      let st' = run_cfl (BLK ((MADD R13 R12 (MC (n2w (LENGTH l)))) :: push_list l)) st in
        (!i. (i > w2n (read st IP) + LENGTH l \/ i <= w2n (read st IP)) ==> (st '' (isM i) = st' '' (isM i))) /\
        (w2n (read st' IP) = w2n (read st IP)) /\ (w2n (read st' FP) = w2n (read st FP)) /\
        (w2n (read st' SP) = w2n (read st IP))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    SIMP_TAC std_ss [CFL_SEMANTICS_BLK] THEN
    tac1 THEN
    FULL_SIMP_TAC std_ss [read_thm, SP_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    Q.ABBREV_TAC `st1 = (regs |+ (13,regs ' 12 + n2w (LENGTH l)),mem)` THEN
    `locate_ge (read st1 SP) (LENGTH l) /\ w2n (read st1 FP) + LENGTH l < w2n (read st1 SP) /\
        (w2n (read st1 SP) = w2n (read (regs,mem) IP) + LENGTH l)` by (Q.UNABBREV_TAC `st1` THEN
         IMP_RES_TAC grow_lt_lem_1 THEN
         FULL_SIMP_TAC finmap_ss [read_thm, locate_ge_def, SP_def, FP_def, IP_def, grow_lt_def]) THEN
    RW_TAC std_ss [LET_THM] THENL [

      `i > w2n (read st1 SP)` by RW_TAC arith_ss [] THEN
        IMP_RES_TAC above_lem_1 THEN
        POP_ASSUM (ASSUME_TAC o Q.SPEC `LENGTH (l:CFL_EXP list)`) THEN
        FULL_SIMP_TAC std_ss [] THEN
        `valid_exp_1 (isM i)` by RW_TAC std_ss [valid_exp_1_def] THEN
        IMP_RES_TAC VALID_MEXP_MEXP_1 THEN
        IMP_RES_TAC VALID_MEXP_1_exp_3 THEN
        RW_TAC std_ss [PUSH_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def],

      `i <= w2n (read st1 SP) - LENGTH (l:CFL_EXP list)` by RW_TAC arith_ss [] THEN
        IMP_RES_TAC below_lem_1 THEN
        `valid_exp_1 (isM i)` by RW_TAC std_ss [valid_exp_1_def] THEN
        IMP_RES_TAC VALID_MEXP_MEXP_1 THEN
        IMP_RES_TAC VALID_MEXP_1_exp_3 THEN
        RW_TAC std_ss [PUSH_LIST_SANITY] THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [reade_def],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [IP_def, FP_def, read_thm],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [IP_def, FP_def, read_thm],

      IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] PUSH_LIST_SP_FP) THEN
        Q.UNABBREV_TAC `st1` THEN
        FULL_SIMP_TAC finmap_ss [SP_def, FP_def, read_thm]
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      Registers saved in the stack are restored                                  *)
(*---------------------------------------------------------------------------------*)

val POP_TAC =
    CONV_TAC (DEPTH_CONV (REWRITE_CONV [Once mdecode_def, popL_def])) THEN
    REWRITE_TAC [MAP, LENGTH] THEN
    SIMP_TAC finmap_ss [read_thm] THEN
    CONV_TAC (DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
        THENC RATOR_CONV (RAND_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV
                THENC REWRITE_CONV [read_thm, write_thm, pair_case_def]
                THENC reduceLib.REDUCE_CONV)))) THEN
    SIMP_TAC finmap_ss [write_thm];


val EVAL_POP_SAVED_REGS_LIST = Q.store_thm (
    "EVAL_POP_SAVED_REGS_LIST",

   `!regs mem. locate_ge (read (regs,mem) FP) 11 ==>
      (run_cfl (BLK ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]])) (regs,mem) =
     (regs |+ (0,mem ' (w2n (regs ' 11) - 10)) |+
     (1,mem ' (w2n (regs ' 11) - 9)) |+ (2,mem ' (w2n (regs ' 11) - 8)) |+
     (3,mem ' (w2n (regs ' 11) - 7)) |+ (4,mem ' (w2n (regs ' 11) - 6)) |+
     (5,mem ' (w2n (regs ' 11) - 5)) |+ (6,mem ' (w2n (regs ' 11) - 4)) |+
     (7,mem ' (w2n (regs ' 11) - 3)) |+ (8,mem ' (w2n (regs ' 11) - 2)) |+
     (11,mem ' (w2n (regs ' 11) - 1)) |+ (12,mem ' (w2n (regs ' 11))) |+
     (13,regs ' 11 + 1w) |+ (14,mem ' (w2n (regs ' 11) + 1)),mem))`,

  RW_TAC std_ss [APPEND, CFL_SEMANTICS_BLK, from_reg_index_thm, fp_def, ip_def, lr_def] THEN
  NTAC 2 tac4 THEN POP_TAC THEN
  IMP_RES_TAC locate_ge_lem_1 THEN
  `grow_lt (read (regs,mem) FP - 11w) 11` by (
     IMP_RES_TAC LOCATE_GE_GROW_LT THEN `w2n (11w:word32) = 11` by WORDS_TAC THEN
     FULL_SIMP_TAC std_ss [locate_ge_def]) THEN
  IMP_RES_TAC grow_lt_lem_2 THEN
  FULL_SIMP_TAC std_ss [FP_def, read_thm] THEN
  Q.ABBREV_TAC `x = regs ' 11 - 11w` THEN
  WORDS_TAC THEN Q.UNABBREV_TAC `x` THEN
  RW_TAC arith_ss [GSYM WORD_ADD_SUB_SYM, WORD_ADD_SUB_ASSOC] THEN
  `w2n (11w:word32) <= 11` by WORDS_TAC THEN
  RW_TAC std_ss [] THEN WORDS_TAC THEN
  FULL_SIMP_TAC arith_ss [locate_ge_def]
 );

val EVAL_POP_SAVED_REGS_LIST_2 = Q.store_thm (
    "EVAL_POP_SAVED_REGS_LIST_2",

   `!regs mem. locate_ge (read (regs,mem) FP) 11 ==>
      (run_cfl (BLK ([MSUB R13 R11 (MC 11w)] ++ pop_list saved_regs_list)) (regs,mem) =
     (regs |+ (0,mem ' (w2n (regs ' 11) - 10)) |+
     (1,mem ' (w2n (regs ' 11) - 9)) |+ (2,mem ' (w2n (regs ' 11) - 8)) |+
     (3,mem ' (w2n (regs ' 11) - 7)) |+ (4,mem ' (w2n (regs ' 11) - 6)) |+
     (5,mem ' (w2n (regs ' 11) - 5)) |+ (6,mem ' (w2n (regs ' 11) - 4)) |+
     (7,mem ' (w2n (regs ' 11) - 3)) |+ (8,mem ' (w2n (regs ' 11) - 2)) |+
     (11,mem ' (w2n (regs ' 11) - 1)) |+ (12,mem ' (w2n (regs ' 11))) |+
     (13,regs ' 11 + 1w) |+ (14,mem ' (w2n (regs ' 11) + 1)),mem))`,

  SIMP_TAC std_ss [FORALL_DSTATE, saved_regs_list_def, pop_list_def, pop_one_def] THEN
  RW_TAC std_ss [APPEND, CFL_SEMANTICS_BLK, from_reg_index_thm, fp_def, ip_def, lr_def] THEN
  NTAC 25 tac4 THEN
  RW_TAC std_ss [GSYM WORD_ADD_ASSOC] THEN

  IMP_RES_TAC locate_ge_lem_1 THEN
  `grow_lt (read (regs,mem) FP - 11w) 11` by (
     IMP_RES_TAC LOCATE_GE_GROW_LT THEN `w2n (11w:word32) = 11` by WORDS_TAC THEN
     FULL_SIMP_TAC std_ss [locate_ge_def]) THEN
  IMP_RES_TAC grow_lt_lem_2 THEN
  FULL_SIMP_TAC std_ss [FP_def, read_thm] THEN
  Q.ABBREV_TAC `x = regs ' 11 - 11w` THEN
  WORDS_TAC THEN Q.UNABBREV_TAC `x` THEN
  RW_TAC arith_ss [GSYM WORD_ADD_SUB_SYM, WORD_ADD_SUB_ASSOC] THEN
  `w2n (11w:word32) <= 11` by WORDS_TAC THEN
  RW_TAC std_ss [] THEN WORDS_TAC THEN
  FULL_SIMP_TAC arith_ss [locate_ge_def]
 );

val POP_SAVED_REGS_LIST_SANITY_1 = Q.store_thm (
    "POP_SAVED_REGS_LIST_SANITY_1",
   `!st. locate_ge (read st FP) 11 /\ grow_lt (read st FP) 1 ==>
      let st' = run_cfl (BLK ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]])) st in
        (!i. st' '' (isM i) = st '' (isM i)) /\
        (w2n (read st' IP) = w2n (st '' (isM (w2n (read st FP))))) /\
        (w2n (read st' FP) = w2n (st '' (isM (w2n (read st FP) - 1)))) /\
        (w2n (read st' SP) = w2n (read st FP) + 1) /\
        (w2n (read st' SP) = w2n (read st FP + 1w))`,

    SIMP_TAC std_ss [FORALL_DSTATE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    IMP_RES_TAC EVAL_POP_SAVED_REGS_LIST THEN
    IMP_RES_TAC grow_lt_lem_2 THEN
    FULL_SIMP_TAC std_ss [FP_def, read_thm] THEN
    RW_TAC finmap_ss [LET_THM, reade_def, read_thm, FP_def, IP_def, SP_def]
  );

(*---------------------------------------------------------------------------------*)
(*      The caller pops the results out of the stack                               *)
(*---------------------------------------------------------------------------------*)

val LEGAL_POP_EXP_LEM_2 = Q.store_thm (
  "LEGAL_POP_EXP_LEM_2",
  `!st l m. w2n (read st SP) + LENGTH (MAP conv_exp l) + (12 + m) <= w2n (read st FP) /\ EVERY (\x.valid_TEXP x m) l
       ==>
     EVERY (\x.~addr_in_range st x (w2n (read st SP) + LENGTH (MAP conv_exp l), w2n (read st SP))) (MAP conv_exp l)`,

  REPEAT STRIP_TAC THEN
  IMP_RES_TAC VALID_EXP_LEM THEN
  FULL_SIMP_TAC list_ss [EVERY_EL, rich_listTheory.EL_MAP] THEN
  RW_TAC std_ss [] THEN RES_TAC THEN
  Cases_on `EL n l` THEN
  FULL_SIMP_TAC std_ss [conv_exp_def, addr_in_range_def, in_range_def, addr_of_def, valid_exp_def, valid_TEXP_def,
               valid_regs_lem, within_bound_def] THEN
  RW_TAC arith_ss []
  );

val POST_CALL_POP_RESULTS = Q.store_thm (
    "POST_CALL_POP_RESULTS",
    `!st l m. locate_ge (read st FP + 1w) 12 /\
            w2n (read st FP) + 1 + LENGTH l + (12 + m) <= w2n (st '' (isM (w2n (read st FP) - 1))) /\
            EVERY notC l /\ unique_list l /\ EVERY (\x.valid_TEXP x m) l /\ (MAP conv_exp l = l')
       ==>
    !i. i < LENGTH l' ==>
     ((run_cfl (BLK ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++ pop_list l')) st) ''
          (EL i l') = st '' (isM ((w2n (read st FP) + 1) + SUC i)))`,

    RW_TAC std_ss [APPEND, Once RUN_CFL_BLK_APPEND] THEN
    Q.ABBREV_TAC `st1 = run_cfl (BLK (MSUB R13 R11 (MC 11w)::[MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]])) st` THEN
    `locate_ge (read st FP) 11 /\ grow_lt (read st FP) 1` by (
       `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
       `grow_lt (read st FP) 1` by FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def] THEN
       IMP_RES_TAC grow_lt_lem_1 THEN FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def]) THEN

    `(!i. st '' (isM i) = st1 '' (isM i)) /\ (w2n (st '' (isM (w2n (read st FP) - 1))) = w2n (read st1 FP)) /\
     (w2n (read st FP) + 1 = w2n (read st1 SP)) /\ (read st FP + 1w = read st1 SP)`
         by (Q.UNABBREV_TAC `st1` THEN
         METIS_TAC [rich_listTheory.CONS_APPEND, SIMP_RULE std_ss [LET_THM] POP_SAVED_REGS_LIST_SANITY_1, w2n_11]) THEN
    FULL_SIMP_TAC std_ss [] THEN NTAC 7 (POP_ASSUM (K ALL_TAC)) THEN

    `grow_lt (read st1 SP) (LENGTH (MAP conv_exp l)) /\ locate_ge (read st1 FP) (12 + m)` by (`w2n (read st1 FP)
            < dimword (:32)` by METIS_TAC [w2n_lt] THEN RW_TAC arith_ss [grow_lt_def, locate_ge_def, LENGTH_MAP]) THEN
    `w2n (read st1 SP) + LENGTH (MAP conv_exp l) + (12 + m) <= w2n (read st1 FP)` by METIS_TAC [LENGTH_MAP] THEN

    IMP_RES_TAC UNIQUE_LIST_11 THEN
    IMP_RES_TAC LEGAL_POP_EXP_LEM_2 THEN
    IMP_RES_TAC VALID_TEXP_MEXP THEN
    IMP_RES_TAC VALID_MEXP_exp THEN
    IMP_RES_TAC LEGAL_POP_EXP_LEM_2 THEN
    `i < LENGTH l` by METIS_TAC [LENGTH_MAP] THEN
    IMP_RES_TAC notC_LEM THEN
    IMP_RES_TAC POP_LIST_FUNCTIONALITY THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
    FULL_SIMP_TAC std_ss [EVERY_EL]
  );

val word_add_lem_1 = Q.store_thm (
    "word_add_lem_1",
    `!x y k. (w2n x = w2n y + k) ==> (x:word32 = y + n2w k)`,
       METIS_TAC [word_add_n2w, n2w_w2n]
    );

val POST_CALL_PASS_RESULTS_LEM = Q.store_thm (
    "POST_CALL_PASS_RESULTS_LEM",

    `!st l m1 m2 k. (w2n (read st IP) = w2n (read st FP) + 1) /\ locate_ge (read st IP) 12 /\
          w2n (read st IP) + LENGTH caller_o + (12 + m1) <= w2n (st '' isM (w2n (read st FP) - 1)) /\
          EVERY (\x. valid_TEXP x m2) callee_o /\
          EVERY notC caller_o /\ unique_list caller_o /\ EVERY (\x.valid_TEXP x m1) caller_o /\
         (LENGTH callee_o = LENGTH caller_o)
       ==>
      !i. i < LENGTH caller_o ==>
         ((run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o)))) :: push_list (MAP conv_exp callee_o)
             ++ ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++
            pop_list (MAP conv_exp caller_o)))) st) '' (EL i (MAP conv_exp caller_o)) =
          st '' (EL i (MAP conv_exp callee_o)))`,

      RW_TAC bool_ss [] THEN
      REWRITE_TAC [Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
             push_list (MAP conv_exp callee_o))) st` THEN
      `grow_lt (read st IP) (LENGTH (MAP conv_exp callee_o))` by (
        `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
           FULL_SIMP_TAC arith_ss [LENGTH_MAP, grow_lt_def]) THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN

      `locate_ge (read st1 FP + 1w) 12 /\ (w2n (read st1 FP) = w2n (read st FP)) /\
        w2n (read st1 FP) + 1 + LENGTH caller_o + (12 + m1) <= w2n (st1 '' (isM (w2n (read st1 FP) - 1)))` by (
           `w2n (read st FP) - 1 <= w2n (read st IP)` by RW_TAC arith_ss [] THEN
           `(w2n (read st1 IP) = w2n (read st IP)) /\ (w2n (read st1 FP) = w2n (read st FP)) /\
            (st1 '' (isM (w2n (read st FP) - 1)) = st '' (isM (w2n (read st FP) - 1)))` by
                (Q.UNABBREV_TAC `st1` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_1]) THEN
            IMP_RES_TAC word_add_lem_1 THEN METIS_TAC [w2n_11]) THEN

      IMP_RES_TAC POST_CALL_POP_RESULTS THEN NTAC 32 (POP_ASSUM (K ALL_TAC)) THEN
      `i < LENGTH (MAP conv_exp caller_o)` by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC std_ss [] THEN NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN
      Q.UNABBREV_TAC `st1` THEN
      METIS_TAC [POST_CALL_PUSH_RESULTS, LENGTH_MAP]
  );

(*---------------------------------------------------------------------------------*)
(*      Status after the caller restores pops results out                          *)
(*---------------------------------------------------------------------------------*)

val eq_exp_lem_1 = Q.store_thm (
    "eq_exp_lem_1",
   `!e l st m. ~(MEM e l) /\ valid_TEXP e m /\ locate_ge (read st FP) (12 + m) /\ EVERY (\x.valid_TEXP x m) l ==>
         EVERY (\x. ~eq_exp st (conv_exp e) x) (MAP conv_exp l)`,

    RW_TAC std_ss [EVERY_EL, LENGTH_MAP, rich_listTheory.EL_MAP, MEM_EL] THEN
    REPEAT (Q.PAT_ASSUM `!n.k` (ASSUME_TAC o Q.SPEC `n`)) THEN RW_TAC std_ss [] THEN
    Cases_on `EL n l` THEN  Cases_on `e` THEN
    FULL_SIMP_TAC std_ss [conv_exp_def, eq_exp_def, eq_addr_def, addr_of_def, valid_exp_def,
        valid_TEXP_def, within_bound_def, locate_ge_def] THENL [
      Cases_on `T''` THEN Cases_on `T'` THEN RW_TAC std_ss [data_reg_index_def],
      RW_TAC std_ss [],
      RES_TAC THEN STRIP_TAC THEN
      `n'' + 12 <= w2n (read st FP) /\ n' + 12 <= w2n (read st FP)` by RW_TAC arith_ss [] THEN
      FULL_SIMP_TAC arith_ss [SUB_CANCEL]
    ]
  );

val tac5 =
    Q.ABBREV_TAC `st1 = run_cfl (BLK (MSUB R13 R11 (MC 11w)::[MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]])) st` THEN
    `locate_ge (read st FP) 11 /\ grow_lt (read st FP) 1` by (
       `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
       `grow_lt (read st FP) 1` by FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def] THEN
       IMP_RES_TAC grow_lt_lem_1 THEN FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def]) THEN
    `(!i. st '' (isM i) = st1 '' (isM i)) /\ (w2n (st '' (isM (w2n (read st FP) - 1))) = w2n (read st1 FP)) /\
     (w2n (read st FP) + 1 = w2n (read st1 SP)) /\ (read st FP + 1w = read st1 SP)`
         by (Q.UNABBREV_TAC `st1` THEN
         METIS_TAC [rich_listTheory.CONS_APPEND, SIMP_RULE std_ss [LET_THM] POP_SAVED_REGS_LIST_SANITY_1, w2n_11]) THEN
    FULL_SIMP_TAC std_ss [] THEN
    `grow_lt (read st1 SP) (LENGTH (MAP conv_exp l)) /\ locate_ge (read st1 FP) (12 + m)` by (`w2n (read st1 FP)
        < dimword (:32)` by METIS_TAC [w2n_lt] THEN RW_TAC arith_ss [grow_lt_def, locate_ge_def, LENGTH_MAP]) THEN
    `w2n (read st1 SP) + LENGTH (MAP conv_exp l) + (12 + m) <= w2n (read st1 FP)` by METIS_TAC [LENGTH_MAP]
    ;

val VALID_TEXP_MEXP_SINGLE = Q.store_thm (
   "VALID_TEXP_MEXP_SINGLE",
   `!e m. valid_TEXP e m ==> valid_MEXP (conv_exp e) m`,
   Cases_on `e` THEN RW_TAC arith_ss [conv_exp_def,valid_exp_def,valid_MEXP_def,valid_TEXP_def, within_bound_def] THEN
   Cases_on `T'` THEN RW_TAC std_ss [valid_exp_1_def, data_reg_index_def, valid_regs_def,
       from_reg_index_thm, index_of_reg_def]
  );

val VALID_MEXP_exp_SINGLE = Q.store_thm (
   "VALID_MEXP_exp_SINGLE",
   `!e m. valid_MEXP e m ==> valid_exp e`,
   Cases_on `e` THEN RW_TAC arith_ss [conv_exp_def,valid_exp_def, valid_MEXP_def]
  );

val eval_saved_regs_list_lem = Q.store_thm (
   "eval_saved_regs_list_lem",
   `!x. locate_ge x 11 /\ (!i. i < 12 ==> (st '' isM (w2n (x:word32) - 10 + i) = st0 '' EL i saved_regs_list)) ==>
     (st '' isM (w2n x + 1) = st0 '' isR lr) /\ (st '' isM (w2n x) = st0 '' isR ip) /\
     (st '' isM (w2n x - 1) = st0 '' isR fp) /\ (st '' isM (w2n x - 2) = st0 '' isR 8) /\
     (st '' isM (w2n x - 3) = st0 '' isR 7) /\ (st '' isM (w2n x - 4) = st0 '' isR 6) /\
     (st '' isM (w2n x - 5) = st0 '' isR 5) /\ (st '' isM (w2n x - 6) = st0 '' isR 4) /\
     (st '' isM (w2n x - 7) = st0 '' isR 3) /\ (st '' isM (w2n x - 8) = st0 '' isR 2) /\
     (st '' isM (w2n x - 9) = st0 '' isR 1) /\ (st '' isM (w2n x - 10) = st0 '' isR 0)`,

   REPEAT GEN_TAC THEN STRIP_TAC THEN
   `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12 /\ 4 < 12 /\ 5 < 12 /\ 6 < 12 /\ 7 < 12 /\ 8 < 12 /\ 9 < 12 /\ 10 < 12 /\
      11 < 12` by RW_TAC arith_ss [] THEN
   RES_TAC THEN
   FULL_SIMP_TAC list_ss [saved_regs_list_def, locate_ge_def] THEN
   `~(w2n (x:word32) <= 10)` by RW_TAC arith_ss [] THEN
   FULL_SIMP_TAC arith_ss [SUB_RIGHT_ADD]
  );

val POST_CALL_SANITY_2 = Q.store_thm (
    "POST_CALL_SANITY_2",

    `!st0 st e l m.
      locate_ge (read st FP + 1w) 12 /\
      w2n (read st FP) + 1 + LENGTH l + (12 + m) <= w2n (st '' (isM (w2n (read st FP) - 1))) /\
      (!i. i < 12 ==> (st '' (isM (w2n (read st FP) - 10 + i)) = st0 '' (EL i saved_regs_list)))
       ==>
       let st' = run_cfl (BLK (([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]]))) st in
        (!i. st' '' isM i = st '' isM i) /\
        (w2n (read st' FP) = w2n (read st0 FP)) /\ (w2n (read st' IP) = w2n (read st0 IP)) /\
        (w2n (read st' SP) = w2n (read st FP) + 1)`,

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC std_ss [APPEND] THEN
    `locate_ge (read st FP) 11 /\ grow_lt (read st FP) 1` by (
       `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
       `grow_lt (read st FP) 1` by FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def] THEN
       IMP_RES_TAC grow_lt_lem_1 THEN FULL_SIMP_TAC arith_ss [locate_ge_def, grow_lt_def]) THEN
    FULL_SIMP_TAC std_ss [LET_THM, SIMP_RULE list_ss [LET_THM] POP_SAVED_REGS_LIST_SANITY_1] THEN
    Q.ABBREV_TAC `x = read st FP` THEN
    `(st '' isM (w2n x) = st0 '' isR ip) /\ (st '' isM (w2n x - 1) = st0 '' isR fp)` by
        METIS_TAC [eval_saved_regs_list_lem] THEN
    FULL_SIMP_TAC std_ss [reade_def, read_thm, FP_def, IP_def, fp_def, ip_def]
  );

val POST_CALL_SANITY_3 = Q.store_thm (
    "POST_CALL_SANITY_3",

    `!st0 st e l m.
      locate_ge (read st FP + 1w) 12 /\
      w2n (read st FP) + 1 + LENGTH l + (12 + m) <= w2n (st '' (isM (w2n (read st FP) - 1))) /\
      EVERY notC l /\ unique_list l /\ EVERY (\x.valid_TEXP x m) l /\ (MAP conv_exp l = l') /\
      (!i. i < 12 ==> (st '' (isM (w2n (read st FP) - 10 + i)) = st0 '' (EL i saved_regs_list)))
       ==>
       let st' = run_cfl (BLK (([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++ pop_list l'))) st in
        (!i. i > w2n (read st0 FP) - 12 ==> (st '' isM i = st' '' isM i)) /\
        (w2n (read st' FP) = w2n (read st0 FP)) /\ (w2n (read st' IP) = w2n (read st0 IP)) /\
        (w2n (read st' SP) = w2n (read st FP) + 1 + LENGTH l)`,

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC std_ss [APPEND, Once RUN_CFL_BLK_APPEND] THEN
    IMP_RES_TAC POST_CALL_SANITY_2 THEN
    IMP_RES_TAC VALID_TEXP_MEXP THEN IMP_RES_TAC VALID_MEXP_exp THEN
    tac5 THEN
    Q.PAT_ASSUM ` MAP conv_exp l = l'` (ASSUME_TAC o GSYM) THEN
    FULL_SIMP_TAC std_ss [LET_THM] THEN
    FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [LET_THM] POP_LIST_SP_FP, LENGTH_MAP] THEN
    STRIP_TAC THENL [
      NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN
        `valid_exp_2 (isM i)` by METIS_TAC [valid_exp_2_def] THEN
        `i > w2n (read st1 FP) - 12` by (Q.UNABBREV_TAC `st1` THEN METIS_TAC [rich_listTheory.CONS_APPEND]) THEN
        IMP_RES_TAC above_lem_3 THEN
        METIS_TAC [POP_LIST_SANITY, LENGTH_MAP],

      NTAC 8 (POP_ASSUM (K ALL_TAC)) THEN
        Q.UNABBREV_TAC `st1` THEN
        METIS_TAC [rich_listTheory.CONS_APPEND]
    ]
  );

val POST_CALL_SANITY_4 = Q.store_thm (
    "POST_CALL_SANITY_4",

    `!st0 st e l m.
      locate_ge (read st FP + 1w) 12 /\
      w2n (read st FP) + 1 + LENGTH l + (12 + m) <= w2n (st '' (isM (w2n (read st FP) - 1))) /\
      valid_TEXP e m /\ ~(MEM e l) /\
      EVERY notC l /\ unique_list l /\ EVERY (\x.valid_TEXP x m) l /\ (MAP conv_exp l = l') /\
      (!i. i < 12 ==> (st '' (isM (w2n (read st FP) - 10 + i)) = st0 '' (EL i saved_regs_list))) /\
      (!n. n < m ==> (st '' (isM (w2n (read st0 FP) - (12 + n)))  = st0 '' (isM (w2n (read st0 FP) - (12 + n)))))
       ==>
      ((run_cfl (BLK (([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++ pop_list l'))) st) ''
          (conv_exp e) =  st0 '' (conv_exp e))`,

    RW_TAC std_ss [APPEND, Once RUN_CFL_BLK_APPEND] THEN
    `w2n (read (run_cfl (BLK (MSUB R13 R11 (MC 11w)::[MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]])) st) FP) = w2n(read st0 FP)`
       by METIS_TAC [SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_2, rich_listTheory.CONS_APPEND] THEN
    IMP_RES_TAC VALID_TEXP_MEXP THEN IMP_RES_TAC VALID_MEXP_exp THEN
    IMP_RES_TAC VALID_TEXP_MEXP_SINGLE THEN IMP_RES_TAC VALID_MEXP_exp_SINGLE THEN
    IMP_RES_TAC valid_exp_thm THEN
    tac5 THEN
    IMP_RES_TAC eq_exp_lem_1 THEN
    RW_TAC std_ss [POP_LIST_SANITY] THEN NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
    Cases_on `e` THEN FULL_SIMP_TAC std_ss [conv_exp_def, valid_exp_def, valid_MEXP_def] THENL [

      NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (MP_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
        NTAC 2 (POP_ASSUM (MP_TAC)) THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (MP_TAC) THEN
        NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (MP_TAC) THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
        `?regs mem. st = (regs,mem)` by METIS_TAC [ABS_PAIR_THM] THEN
        RW_TAC std_ss [] THEN Q.UNABBREV_TAC `st1` THEN
        POP_ASSUM (ASSUME_TAC o GSYM) THEN
        RW_TAC std_ss [SIMP_RULE list_ss [] EVAL_POP_SAVED_REGS_LIST] THEN
        IMP_RES_TAC (GEN_ALL eval_saved_regs_list_lem) THEN
        NTAC 12 (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [reade_def, read_thm, FP_def] THEN
        NTAC 14 (POP_ASSUM (K ALL_TAC)) THEN
        Cases_on `T'` THEN FULL_SIMP_TAC finmap_ss [data_reg_index_def],

      RW_TAC std_ss [reade_def],

      FULL_SIMP_TAC arith_ss [within_bound_def] THEN
        `!st n. st '' (isV (n + 12)) = reade st (isM (w2n (read st FP) - (12 + n)))` by
          (SIMP_TAC std_ss [FORALL_DSTATE, read_thm, reade_def, fp_def, FP_def, ADD_SYM]) THEN
        FULL_SIMP_TAC std_ss [] THEN METIS_TAC [ADD_SYM]
   ]
 );

val POST_CALL_RESTORED_REGS_LEM = Q.store_thm (
    "POST_CALL_RESTORED_REGS_LEM",

    `!st l m1 m2 e. (w2n (read st IP) = w2n (read st FP) + 1) /\ locate_ge (read st IP) 12 /\
          w2n (read st IP) + LENGTH caller_o + (12 + m1) <= w2n (st '' isM (w2n (read st FP) - 1)) /\
         (!i. i < 12 ==> (st '' (isM (w2n (read st FP) - 10 + i)) = st0 '' (EL i saved_regs_list))) /\
         (!n. n < m1 ==> (st '' (isM (w2n (read st0 FP) - (12 + n))) = st0 '' (isM (w2n (read st0 FP) - (12 + n))))) /\
          w2n (read st0 FP) - (12 + m1) >= w2n (read st IP) + LENGTH callee_o /\
          valid_TEXP e m1 /\ ~(MEM e caller_o) /\
          EVERY (\x. valid_TEXP x m2) callee_o /\ EVERY notC caller_o /\ unique_list caller_o /\
          EVERY (\x.valid_TEXP x m1) caller_o /\ (LENGTH callee_o = LENGTH caller_o)
       ==>
         ((run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o)))) :: push_list (MAP conv_exp callee_o)
           ++ ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++ pop_list (MAP conv_exp caller_o))))
           st) '' (conv_exp e) = st0 '' (conv_exp e))`,

      RW_TAC bool_ss [] THEN
      REWRITE_TAC [Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
             push_list (MAP conv_exp callee_o))) st` THEN
      `grow_lt (read st IP) (LENGTH (MAP conv_exp callee_o))` by (
        `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
           FULL_SIMP_TAC arith_ss [LENGTH_MAP, grow_lt_def]) THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN

      `(!i. i < 12 ==> (w2n (read st FP) - 10 + i <= w2n (read st IP))) /\ (!n. w2n (read st FP) - (12 + n) <=
        w2n (read st IP)) /\ w2n (read st FP) - 1 <= w2n (read st IP)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      `(read st1 FP = read st FP) /\ (read st1 IP = read st IP) /\
       (st1 '' isM (w2n (read st1 FP) - 1) = st '' isM (w2n (read st FP) - 1)) /\
       (!i. i < 12 ==> (st1 '' (isM (w2n (read st1 FP) - 10 + i)) = st0 '' (EL i saved_regs_list)))`
         by (Q.UNABBREV_TAC `st1` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_1, w2n_11]) THEN

      `(!n. n < m1 ==> (st1 '' (isM (w2n (read st0 FP) - (12 + n))) = st0 '' (isM (w2n (read st0 FP) - (12 + n)))))` by (
          RW_TAC std_ss [] THEN
          `!a:num b c. a > b /\ b >= c ==> a > c` by RW_TAC arith_ss [] THEN
          `(!i. i > w2n (read st0 FP) - (12+m1) ==> (st1 '' isM i = st '' isM i))`  by (
          IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_1) THEN NTAC 9 (POP_ASSUM (K ALL_TAC)) THEN
          RW_TAC std_ss [] THEN Q.UNABBREV_TAC `st1` THEN METIS_TAC [LENGTH_MAP]) THEN
          RW_TAC arith_ss []) THEN

      IMP_RES_TAC word_add_lem_1 THEN
      NTAC 6 (POP_ASSUM MP_TAC) THEN NTAC 7 (POP_ASSUM (K ALL_TAC)) THEN
      NTAC 8 (POP_ASSUM MP_TAC) THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN
      METIS_TAC [POST_CALL_SANITY_4]
  );

val POST_CALL_SANITY_LEM = Q.store_thm (
    "POST_CALL_SANITY_LEM",

    `!st l m1 m2 e. (w2n (read st IP) = w2n (read st FP) + 1) /\ locate_ge (read st IP) 12 /\
          w2n (read st IP) + LENGTH caller_o + (12 + m1) <= w2n (st '' isM (w2n (read st FP) - 1)) /\
          w2n (read st0 FP) - 12 >= w2n (read st IP) + LENGTH caller_o /\
          (!i. i < 12 ==> (st '' (isM (w2n (read st FP) - 10 + i)) = st0 '' (EL i saved_regs_list))) /\
          EVERY (\x. valid_TEXP x m2) callee_o /\ EVERY notC caller_o /\ unique_list caller_o /\
          EVERY (\x.valid_TEXP x m1) caller_o /\ (LENGTH callee_o = LENGTH caller_o)
       ==>
      let st' = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::push_list (MAP conv_exp callee_o)
          ++ ([MSUB R13 R11 (MC 11w)] ++ [MPOP 13 [0;1;2;3;4;5;6;7;8;fp;ip;lr]] ++ pop_list (MAP conv_exp caller_o)))) st
      in
        (!i. i > w2n (read st0 FP) - 12 ==> (st '' isM i = st' '' isM i)) /\
        (w2n (read st' FP) = w2n (read st0 FP)) /\ (w2n (read st' IP) = w2n (read st0 IP)) /\
        (w2n (read st' SP) = w2n (read st FP) + 1 + LENGTH caller_o)`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
             push_list (MAP conv_exp callee_o))) st` THEN

      `grow_lt (read st IP) (LENGTH (MAP conv_exp callee_o))` by (
        `w2n (st '' isM (w2n (read st FP) - 1)) < dimword (:32)` by METIS_TAC [w2n_lt] THEN
           FULL_SIMP_TAC arith_ss [LENGTH_MAP, grow_lt_def]) THEN
      IMP_RES_TAC VALID_TEXP_MEXP THEN

      `(!i. i < 12 ==> (w2n (read st FP) - 10 + i <= w2n (read st IP))) /\ w2n (read st FP) - 1 <= w2n (read st IP) /\
         (!a:num b c. a > b /\ b >= c ==> a > c)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      `(read st1 FP = read st FP) /\ (read st1 IP = read st IP) /\
       (st1 '' isM (w2n (read st1 FP) - 1) = st '' isM (w2n (read st FP) - 1)) /\
       (!i. i < 12 ==> (st1 '' (isM (w2n (read st1 FP) - 10 + i)) = st0 '' (EL i saved_regs_list)))`
         by (Q.UNABBREV_TAC `st1` THEN METIS_TAC [SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_1, w2n_11]) THEN
      `(!i. i > w2n (read st0 FP) - 12 ==> (st1 '' isM i = st '' isM i))`  by (
          IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_1) THEN NTAC 9 (POP_ASSUM (K ALL_TAC)) THEN
          RW_TAC std_ss [] THEN Q.UNABBREV_TAC `st1` THEN METIS_TAC [LENGTH_MAP]) THEN

      IMP_RES_TAC word_add_lem_1 THEN
      `locate_ge (read st1 FP + 1w) 12 /\ w2n (read st1 FP) + 1 + LENGTH caller_o + (12 + m1) <=
         w2n (st1 '' isM (w2n (read st1 FP) - 1))` by METIS_TAC [] THEN
      NTAC 8 (POP_ASSUM MP_TAC) THEN NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN
      NTAC 5 (POP_ASSUM MP_TAC) THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN
      IMP_RES_TAC POST_CALL_SANITY_3 THEN NTAC 60 (POP_ASSUM (K ALL_TAC)) THEN
      FULL_SIMP_TAC std_ss [LET_THM]
  );

(*---------------------------------------------------------------------------------*)
(*      Main theorems about post-call processing                                   *)
(*---------------------------------------------------------------------------------*)

val valid_post_call_def = Define `
    valid_post_call (st0,st) (m1,m2) (callee_o,caller_o) =
     (w2n (read st IP) = w2n (read st FP) + 1) /\ locate_ge (read st IP) 12 /\
     w2n (read st IP) + LENGTH caller_o + (12 + m1) <= w2n (st '' isM (w2n (read st FP) - 1)) /\
     w2n (read st0 FP) - (12 + m1) >= w2n (read st IP) + LENGTH callee_o /\
     (!i. i < 12 ==> (st '' isM (w2n (read st FP) - 10 + i) = st0 '' EL i saved_regs_list)) /\
     EVERY (\x. valid_TEXP x m2) callee_o /\ EVERY notC caller_o /\ unique_list caller_o /\
     EVERY (\x. valid_TEXP x m1) caller_o /\ (LENGTH callee_o = LENGTH caller_o)`;


val POST_CALL_SANITY_THM = Q.store_thm (
    "POST_CALL_SANITY_THM",
    `!st st0 m1 m2 caller_o callee_o.
     valid_post_call (st0,st) (m1,m2) (callee_o,caller_o)
       ==>
        let st' = run_cfl (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1)) st in
     (!i. i > w2n (read st0 FP) - 12 ==> (st '' isM i = st' '' isM i)) /\
     (w2n (read st' FP) = w2n (read st0 FP)) /\ (w2n (read st' IP) = w2n (read st0 IP)) /\
     (w2n (read st' SP) = w2n (read st0 FP) - (12 + m1))`,

      REPEAT GEN_TAC THEN REWRITE_TAC [valid_post_call_def] THEN STRIP_TAC THEN
      `w2n (read st0 FP) - 12 >= w2n (read st IP) + LENGTH caller_o` by RW_TAC arith_ss [] THEN
      SIMP_TAC std_ss [post_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
         push_list (MAP conv_exp callee_o) ++ [MSUB R13 R11 (MC 11w)] ++
        [MPOP 13 [0; 1; 2; 3; 4; 5; 6; 7; 8; fp; ip; lr]] ++ pop_list (MAP conv_exp caller_o))) st` THEN

      ` (!i. i > w2n (read st0 FP) - 12 ==> (st '' isM i = st1 '' isM i)) /\
        (w2n (read st1 FP) = w2n (read st0 FP)) /\ (w2n (read st1 IP) = w2n (read st0 IP)) /\
        (w2n (read st1 SP) = w2n (read st FP) + 1 + LENGTH caller_o)` by
        (Q.UNABBREV_TAC `st1` THEN METIS_TAC [SIMP_RULE bool_ss [LET_THM, APPEND_ASSOC] POST_CALL_SANITY_LEM]) THEN

      `locate_ge (read st1 FP) (12 + m1)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      RW_TAC std_ss [LET_THM, SIMP_RULE std_ss [LET_THM] sub_sp_lem_1]
  );

val POST_CALL_PASS_RESULTS_THM = Q.store_thm (
    "POST_CALL_PASS_RESULTS_THM",

    `!st m1 m2 caller_o callee_o.
       valid_post_call (st0,st) (m1,m2) (callee_o,caller_o)
       ==>
        !i. i < LENGTH caller_o ==>
        (run_cfl (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1)) st ''
        EL i (MAP conv_exp caller_o) = st '' EL i (MAP conv_exp callee_o))`,

      REPEAT GEN_TAC THEN REWRITE_TAC [valid_post_call_def] THEN STRIP_TAC THEN
      `w2n (read st0 FP) - 12 >= w2n (read st IP) + LENGTH caller_o` by RW_TAC arith_ss [] THEN
      SIMP_TAC std_ss [post_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
         push_list (MAP conv_exp callee_o) ++ [MSUB R13 R11 (MC 11w)] ++
        [MPOP 13 [0; 1; 2; 3; 4; 5; 6; 7; 8; fp; ip; lr]] ++ pop_list (MAP conv_exp caller_o))) st` THEN

      RW_TAC std_ss [] THEN
      `st1 '' EL i (MAP conv_exp caller_o) = st '' EL i (MAP conv_exp callee_o)` by
        (ASSUME_TAC (SPEC_ALL POST_CALL_PASS_RESULTS_LEM) THEN
           Q.UNABBREV_TAC `st1` THEN FULL_SIMP_TAC list_ss [LET_THM]) THEN
      `w2n (read st1 FP) = w2n (read st0 FP)` by
         (Q.UNABBREV_TAC `st1` THEN METIS_TAC [SIMP_RULE bool_ss [LET_THM, APPEND_ASSOC] POST_CALL_SANITY_LEM]) THEN

      `locate_ge (read st1 FP) (12 + m1)` by FULL_SIMP_TAC arith_ss [locate_ge_def] THEN
      RW_TAC std_ss [LET_THM, SIMP_RULE std_ss [LET_THM] sub_sp_lem_1]
  );

val POST_CALL_RESTORED_REGS_THM = Q.store_thm (
    "POST_CALL_RESTORED_REGS_THM",

    `!st m1 m2 caller_o callee_o.
     valid_post_call (st0,st) (m1,m2) (callee_o,caller_o) /\
     (!n. n < m1 ==> (st '' isM (w2n (read st0 FP) - (12 + n)) = st0 '' isM (w2n (read st0 FP) - (12 + n)))) /\
     ~MEM e caller_o /\ valid_TEXP e m1
       ==>
        (run_cfl (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1)) st ''
        (conv_exp e) = st0 '' (conv_exp e))`,

      REPEAT GEN_TAC THEN REWRITE_TAC [valid_post_call_def] THEN STRIP_TAC THEN
      SIMP_TAC std_ss [post_call_def, Once RUN_CFL_BLK_APPEND] THEN
      Q.ABBREV_TAC `st1 = run_cfl (BLK (MADD R13 R12 (MC (n2w (LENGTH (MAP conv_exp callee_o))))::
         push_list (MAP conv_exp callee_o) ++ [MSUB R13 R11 (MC 11w)] ++
        [MPOP 13 [0; 1; 2; 3; 4; 5; 6; 7; 8; fp; ip; lr]] ++ pop_list (MAP conv_exp caller_o))) st` THEN

      `st0 '' (conv_exp e) = st1 '' (conv_exp e)` by (
         `w2n (read st0 FP) >= m1 + (LENGTH callee_o + (w2n (read st IP) + 12))` by RW_TAC arith_ss [] THEN
         ASSUME_TAC (SPEC_ALL POST_CALL_RESTORED_REGS_LEM) THEN
           Q.UNABBREV_TAC `st1` THEN FULL_SIMP_TAC list_ss [LET_THM]) THEN

      `?regs mem. st1 = (regs,mem)` by METIS_TAC [ABS_PAIR_THM] THEN
      RW_TAC std_ss [CFL_SEMANTICS_BLK] THEN tac1 THEN
      Cases_on `e` THEN
      FULL_SIMP_TAC finmap_ss [valid_TEXP_def, conv_exp_def, reade_def, read_thm, fp_def] THEN
      Cases_on `T'` THEN FULL_SIMP_TAC std_ss [data_reg_index_def]
  );

(*---------------------------------------------------------------------------------*)
(*      Lemmas for proving main theorems about function calls                      *)
(*---------------------------------------------------------------------------------*)

val same_fp_ip_sp_def = Define `
    same_fp_ip_sp st1 st0 =
     (w2n (read st1 FP) = w2n (read st0 FP)) /\
     (w2n (read st1 IP) = w2n (read st0 IP)) /\
     (w2n (read st1 SP) = w2n (read st0 SP))`;

val status_intact_def = Define `
    status_intact st1 st0 =
        same_fp_ip_sp st1 st0 /\
        (!i. i > w2n (read st0 FP) - 12 ==> (st1 '' isM i = st0 '' isM i))`;

val PRE_CALL_FP_IP_IN_MEM = Q.store_thm (
    "PRE_CALL_FP_IP_IN_MEM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
         let st' =  run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st in
          (st' '' (isM (w2n (read st' FP) - 10 + 10)) = read st IP) /\
          (st' '' (isM (w2n (read st' FP) - 10 + 9)) = read st FP)`,

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      IMP_RES_TAC PRE_CALL_SAVED_REGS_THM_2 THEN NTAC 13 (POP_ASSUM (K ALL_TAC)) THEN
      FULL_SIMP_TAC std_ss [LET_THM] THEN
      RW_TAC list_ss [saved_regs_list_def, reade_def, IP_def, FP_def, ip_def, fp_def]
  );

val fun_call_lem_1 = Q.store_thm (
    "fun_call_lem_1",
    `!k j st st' st2. locate_ge (read st SP) (k + 13 + j + m2) /\ standard_frame st m1 /\
     (w2n (read st2 FP) = w2n (read st' FP)) /\
     (w2n (read st SP) - (k + j) - 1 = w2n (read st' FP)) ==>
     (!i. i < 12 ==> w2n (read st' FP) - 10 + i > w2n (read st2 FP) - 12) /\
     (w2n (read st' FP) - 10 + 9 = w2n (read st' FP) - 1)`,
    RW_TAC arith_ss [locate_ge_def, standard_frame_def]
  );

val fun_call_lem_2 = Q.store_thm (
    "fun_call_lem_2",
   `!x y. locate_ge x (MAX n1 n2 + 13 + m2) /\
     (MAX n1 n2 - n1 = k) /\ (w2n x - (k + n1) - 1 = y) ==>
         12 + m2 <= y /\ y + n2 < w2n x`,
   RW_TAC arith_ss [locate_ge_def, MAX_DEF]
  );

val fun_call_lem_3 = Q.store_thm (
    "fun_call_lem_3",
    `!k n1 n2 st st' st2.
     standard_frame st m1 /\
     (w2n (read st2 FP) = w2n (read st' FP)) /\ (w2n (read st2 IP) = w2n (read st' FP) + 1) /\
     locate_ge (read st SP) (MAX n1 n2 + 13 + m2) /\
     (MAX n1 n2 - n1 = k) /\
     (w2n (read st SP) - (k + n1) - 1 = w2n (read st' FP))
       ==>
    (w2n (read st2 IP) = w2n (read st2 FP) + 1) /\ locate_ge (read st2 IP) 12 /\
     w2n (read st2 IP) + n2 + (12 + m1) <= w2n (read st FP) /\
     w2n (read st FP) - (12 + m1) >= w2n (read st2 IP) + n2 /\
     (!i. i > w2n (read st FP) - 12 ==> i > w2n (read st SP) /\ i > w2n (read st' FP) - 12)`,

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    IMP_RES_TAC fun_call_lem_2 THEN
    NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN NTAC 2 STRIP_TAC THEN
    FULL_SIMP_TAC arith_ss [locate_ge_def, standard_frame_def]
  );

val VALID_BEFORE_POST_CALL = Q.store_thm (
    "VALID_BEFORE_POST_CALL",
   `!st m1 m2 caller_i callee_i caller_o callee_o.
         locate_ge (read st SP) (MAX (LENGTH caller_i) (LENGTH caller_o) + 13 + m2) /\
         (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
         (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i) = k) /\
         (st' = run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) /\
         status_intact (run_cfl S_body st') st' /\
         VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) /\ WELL_FORMED S_body
     ==>
         valid_post_call (st, run_cfl S_body st') (m1,m2) (callee_o,caller_o)`,

   REPEAT GEN_TAC THEN STRIP_TAC THEN
   `standard_frame st m1` by FULL_SIMP_TAC arith_ss [standard_frame_def, locate_ge_def] THEN
   FULL_SIMP_TAC std_ss [LET_THM, CFL_SEMANTICS_SC, WELL_FORMED_thm] THEN
   Q.PAT_ASSUM `st' = kk` (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
   `locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def, MAX_DEF] THEN

   `!i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SAVED_REGS_THM_2]) THEN
   `(st' '' isM (w2n (read st' FP) - 10 + 10) = read st IP) /\ (st' '' isM (w2n (read st' FP) - 10 + 9) = read st FP)`
       by (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_FP_IP_IN_MEM]) THEN
   `(!i. i > w2n (read st SP) ==> (st' '' (isM i) = st '' (isM i))) /\
    (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
    (w2n (read st' IP) = w2n (read st' FP) + 1) /\ (w2n (read st' SP) = w2n (read st' FP) - (12 + m2))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_THM_2]) THEN

   Q.PAT_ASSUM `run_cfl x y = k` (K ALL_TAC) THEN
   Q.ABBREV_TAC `st2 = run_cfl S_body st'` THEN
   Q.ABBREV_TAC `st3 = run_cfl (BLK (post_call (MAP conv_exp caller_o,MAP conv_exp callee_o) m1)) st2` THEN
   Q.PAT_ASSUM `w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [status_intact_def, same_fp_ip_sp_def] THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN NTAC 2 STRIP_TAC THEN

   `!i. i < 12 ==> w2n (read st' FP) - 10 + i > w2n (read st2 FP) - 12` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1] THEN
   `st2 '' isM (w2n (read st2 FP) - 1) = read st FP` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1, DECIDE ``9 < 12``] THEN
   `!i.  i < 12 ==> (st2 '' isM (w2n (read st2 FP) - 10 + i) = st '' EL i saved_regs_list)` by METIS_TAC [] THEN

    `(w2n (read st SP) - (k + LENGTH caller_i) - 1 = w2n (read st' FP)) /\
      (MAX (LENGTH callee_i) (LENGTH caller_o) - LENGTH callee_i = k)` by METIS_TAC [VALID_FC_1_def] THEN
    IMP_RES_TAC (Q.SPECL [`k`, `LENGTH (caller_i:TEXP list)`, `LENGTH (caller_o:TEXP list)`, `st`, `st'`, `st2`] fun_call_lem_3) THEN
    NTAC 78 (POP_ASSUM (K ALL_TAC)) THEN
    FULL_SIMP_TAC bool_ss [valid_post_call_def, VALID_FC_1_def] THEN
    METIS_TAC []
  );

(*---------------------------------------------------------------------------------*)
(*      Main theorems about pre-call processing and post-call processing           *)
(*  The pre-call processing and post-call processing do accomplish parameter       *)
(*  passing and result passing repsectively                                        *)
(*---------------------------------------------------------------------------------*)

val PRE_CALL_PRE_CALL_THM = Q.store_thm (
    "PRE_CALL_PRE_CALL_THM",
    `!st l m1 m2 k. locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2) /\ standard_frame st m1 /\
          EVERY notC callee_i /\ unique_list callee_i /\ EVERY (\x.valid_TEXP x m2) callee_i /\
          EVERY (\x. valid_TEXP x m1) caller_i /\ (LENGTH callee_i = LENGTH caller_i)
       ==>
           (MAP (reade st o conv_exp) caller_i =
            MAP (reade (run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st)
              o conv_exp) callee_i)`,

        RW_TAC std_ss [] THEN
        MATCH_MP_TAC MAP_LEM_3 THEN RW_TAC std_ss [] THEN
        METIS_TAC [SIMP_RULE std_ss [rich_listTheory.EL_MAP] PRE_CALL_PASS_ARGUMENTS_THM_2]
   );


val POST_CALL_PRE_CALL_THM = Q.store_thm (
    "POST_CALL_PRE_CALL_THM",
    `!st m1 m2 caller_o callee_o.
         valid_post_call (st0,st) (m1,m2) (callee_o,caller_o) ==>
           (MAP (reade st o conv_exp) callee_o =
            MAP (reade (run_cfl (BLK (post_call (MAP conv_exp caller_o,MAP conv_exp callee_o) m1)) st)
              o conv_exp) caller_o)`,

        RW_TAC std_ss [] THEN
        `LENGTH caller_o = LENGTH callee_o` by FULL_SIMP_TAC std_ss [valid_post_call_def] THEN
        MATCH_MP_TAC MAP_LEM_3 THEN RW_TAC std_ss [] THEN
        METIS_TAC [rich_listTheory.EL_MAP, POST_CALL_PASS_RESULTS_THM]
   );

(*---------------------------------------------------------------------------------*)
(*      Main theorems about function calls                                         *)
(*  The values fp,ip and sp are recovered after the function call;                 *)
(*  the caller's frame will not be altered unneccessarily (i.e. only those for     *)
(*  receiving results from the callee will be changed). This guarantees the        *)
(*  separation of the caller's frame (activation record) and the callee's frame    *)
(*---------------------------------------------------------------------------------*)

val FUN_CALL_SANITY_THM = Q.store_thm (
    "FUN_CALL_SANITY_THM",
   `!st m1 m2 caller_i callee_i caller_o callee_o.
         locate_ge (read st SP) (MAX (LENGTH caller_i) (LENGTH caller_o) + 13 + m2) /\
         standard_frame st m1 /\ (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
         (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i) = k) /\
         (st' = run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) /\
         status_intact (run_cfl S_body st') st' /\
         VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) /\ WELL_FORMED S_body
     ==>
      let st1 = run_cfl (SC (SC (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) S_body)
             (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1))) st in
           status_intact st1 st`,

   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [LET_THM, CFL_SEMANTICS_SC, WELL_FORMED_thm] THEN
   Q.PAT_ASSUM `st' = kk` (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
   `locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def, MAX_DEF] THEN

   `!i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SAVED_REGS_THM_2]) THEN
   `(st' '' isM (w2n (read st' FP) - 10 + 10) = read st IP) /\ (st' '' isM (w2n (read st' FP) - 10 + 9) = read st FP)`
       by (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_FP_IP_IN_MEM]) THEN
   `(!i. i > w2n (read st SP) ==> (st' '' (isM i) = st '' (isM i))) /\
    (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
    (w2n (read st' IP) = w2n (read st' FP) + 1) /\ (w2n (read st' SP) = w2n (read st' FP) - (12 + m2))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_THM_2]) THEN

   Q.PAT_ASSUM `run_cfl x y = k` (K ALL_TAC) THEN
   Q.ABBREV_TAC `st2 = run_cfl S_body st'` THEN
   Q.ABBREV_TAC `st3 = run_cfl (BLK (post_call (MAP conv_exp caller_o,MAP conv_exp callee_o) m1)) st2` THEN
   Q.PAT_ASSUM `w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [status_intact_def, same_fp_ip_sp_def] THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN NTAC 2 STRIP_TAC THEN

   `!i. i < 12 ==> w2n (read st' FP) - 10 + i > w2n (read st2 FP) - 12` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1] THEN
   `st2 '' isM (w2n (read st2 FP) - 1) = read st FP` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1, DECIDE ``9 < 12``] THEN
   `!i.  i < 12 ==> (st2 '' isM (w2n (read st2 FP) - 10 + i) = st '' EL i saved_regs_list)` by METIS_TAC [] THEN

    `(w2n (read st SP) - (k + LENGTH caller_i) - 1 = w2n (read st' FP)) /\
      (MAX (LENGTH callee_i) (LENGTH caller_o) - LENGTH callee_i = k)` by METIS_TAC [VALID_FC_1_def] THEN
    IMP_RES_TAC (Q.SPECL [`k`, `LENGTH (caller_i:TEXP list)`, `LENGTH (caller_o:TEXP list)`, `st`, `st'`, `st2`] fun_call_lem_3) THEN
    NTAC 78 (POP_ASSUM (K ALL_TAC)) THEN
    `valid_post_call (st,st2) (m1,m2) (callee_o,caller_o)` by (
        FULL_SIMP_TAC bool_ss [valid_post_call_def, VALID_FC_1_def] THEN METIS_TAC []) THEN
    Q.UNABBREV_TAC `st3` THEN
    METIS_TAC [SIMP_RULE std_ss [LET_THM] POST_CALL_SANITY_THM]
  );

val FUN_CALL_VALUE_RESTORING = Q.store_thm (
    "FUN_CALL_VALUE_RESTORING",

   `!st m1 m2 caller_i callee_i caller_o callee_o.
         locate_ge (read st SP) (MAX (LENGTH caller_i) (LENGTH caller_o) + 13 + m2) /\
         standard_frame st m1 /\ (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
         (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i) = k) /\
         (st' = run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) /\
         status_intact (run_cfl S_body st') st' /\
         ~MEM e caller_o /\ valid_TEXP e m1 /\
         VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) /\ WELL_FORMED S_body
     ==>
      let st1 = run_cfl (SC (SC (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) S_body)
             (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1))) st in
           st1 '' (conv_exp e) = st '' (conv_exp e)`,

   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [LET_THM, CFL_SEMANTICS_SC, WELL_FORMED_thm] THEN
   Q.PAT_ASSUM `st' = kk` (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
   `locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2)` by FULL_SIMP_TAC arith_ss [locate_ge_def, MAX_DEF] THEN

   `!i. i < 12 ==> (st' '' (isM (w2n (read st' FP) - 10 + i)) = st '' (EL i saved_regs_list))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SAVED_REGS_THM_2]) THEN
   `(st' '' isM (w2n (read st' FP) - 10 + 9) = read st FP)` by (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_FP_IP_IN_MEM]) THEN

   `(!i. i > w2n (read st SP) ==> (st' '' (isM i) = st '' (isM i))) /\
    (w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1) /\
    (w2n (read st' IP) = w2n (read st' FP) + 1) /\ (w2n (read st' SP) = w2n (read st' FP) - (12 + m2))` by
       (METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_THM_2]) THEN

   `!n. n < m1 ==> w2n (read st FP) - (12 + n) > w2n (read st SP) /\ w2n (read st FP) - (12 + n) > w2n (read st' FP) - 12` by
       (ASM_REWRITE_TAC [] THEN NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN
       FULL_SIMP_TAC arith_ss [standard_frame_def, locate_ge_def])  THEN

    Q.PAT_ASSUM `run_cfl x y = k` (K ALL_TAC) THEN
    Q.ABBREV_TAC `st2 = run_cfl S_body st'` THEN
   `!n. n < m1 ==> (st2 '' isM (w2n (read st FP) - (12 + n)) = st '' isM (w2n (read st FP) - (12 + n)))` by
       METIS_TAC [VALID_FC_1_def, SIMP_RULE std_ss [LET_THM] PRE_CALL_SANITY_THM_2, status_intact_def] THEN
    POP_ASSUM MP_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN

   Q.ABBREV_TAC `st3 = run_cfl (BLK (post_call (MAP conv_exp caller_o,MAP conv_exp callee_o) m1)) st2` THEN
   Q.PAT_ASSUM `w2n (read st' FP) = w2n (read st SP) - (k + LENGTH callee_i) - 1` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [status_intact_def, same_fp_ip_sp_def] THEN

   `!i. i < 12 ==> w2n (read st' FP) - 10 + i > w2n (read st2 FP) - 12` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1] THEN
   `st2 '' isM (w2n (read st2 FP) - 1) = read st FP` by METIS_TAC [VALID_FC_1_def, fun_call_lem_1, DECIDE ``9 < 12``] THEN
   `!i.  i < 12 ==> (st2 '' isM (w2n (read st2 FP) - 10 + i) = st '' EL i saved_regs_list)` by METIS_TAC [] THEN

    `(w2n (read st SP) - (k + LENGTH caller_i) - 1 = w2n (read st' FP)) /\
      (MAX (LENGTH callee_i) (LENGTH caller_o) - LENGTH callee_i = k)` by METIS_TAC [VALID_FC_1_def] THEN
    IMP_RES_TAC (Q.SPECL [`k`, `LENGTH (caller_i:TEXP list)`, `LENGTH (caller_o:TEXP list)`, `st`, `st'`, `st2`] fun_call_lem_3) THEN
    NTAC 104 (POP_ASSUM (K ALL_TAC)) THEN
    `valid_post_call (st,st2) (m1,m2) (callee_o,caller_o)` by (
        FULL_SIMP_TAC bool_ss [valid_post_call_def, VALID_FC_1_def] THEN METIS_TAC []) THEN
    Q.UNABBREV_TAC `st3` THEN STRIP_TAC THEN
    METIS_TAC [POST_CALL_RESTORED_REGS_THM]
  );

(*---------------------------------------------------------------------------------*)
(*      Theorems showing that this implementation of function calls is correct     *)
(*---------------------------------------------------------------------------------*)

val sp_locate_lem_1 = Q.store_thm (
    "sp_locate_lem_1",
    `!x i1 i2 m2. locate_ge x (MAX i1 i2 + 13 + m2) ==>
       locate_ge x (MAX i1 i2 - i1 + 13 + i1 + m2)`,
    RW_TAC std_ss [locate_ge_def, MAX_DEF] THEN
    RW_TAC arith_ss []
  );

val FC_IMPLEMENTATION_LEM = Q.store_thm (
    "FC_IMPLEMENTATION_LEM",

   `!st m1 m2 caller_i callee_i caller_o callee_o.
     VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) /\ WELL_FORMED S_body /\
     locate_ge (read st SP) (MAX (LENGTH caller_i) (LENGTH caller_o) + 13 + m2) /\
     (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
     (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i) = k) /\
     (st' = run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) /\
     status_intact (run_cfl S_body st') st' /\
     same_content s st m1 /\
     same_content (run_hsl S_hsl (transfer (empty_s,s) (callee_i,caller_i))) (run_cfl S_body st') m2
       ==>
       same_content (run_hsl (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o) (m1,m2)) s)
                    (run_cfl (SC (SC (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) S_body)
                      (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1))) st) m1`,

    RW_TAC std_ss [] THEN
    MATCH_MP_TAC (SIMP_RULE std_ss [LET_THM, AND_IMP_INTRO] FC_SUFFICIENT_COND_LEM) THEN
    RW_TAC std_ss [] THENL [
      FULL_SIMP_TAC std_ss [valid_arg_list_def, VALID_FC_1_def],
      RW_TAC std_ss [WELL_FORMED_thm],
      FULL_SIMP_TAC std_ss [VALID_FC_1_def],
      `standard_frame st m1` by FULL_SIMP_TAC arith_ss [standard_frame_def, locate_ge_def] THEN
        IMP_RES_TAC sp_locate_lem_1 THEN
        METIS_TAC [VALID_FC_1_def, PRE_CALL_PRE_CALL_THM],
      Q.ABBREV_TAC `st' = run_cfl S_body (run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i,MAP conv_exp callee_i)
              (MAX (LENGTH caller_i) (LENGTH caller_o) - LENGTH caller_i) m2)) st)` THEN
        `valid_post_call (st,st') (m1,m2) (callee_o,caller_o)` by (
           Q.UNABBREV_TAC `st'` THEN METIS_TAC [VALID_BEFORE_POST_CALL]) THEN
        METIS_TAC [POST_CALL_PRE_CALL_THM],
      `standard_frame st m1` by FULL_SIMP_TAC arith_ss [standard_frame_def, locate_ge_def] THEN
        METIS_TAC [SIMP_RULE std_ss [LET_THM] FUN_CALL_VALUE_RESTORING]
    ]
  );

(*---------------------------------------------------------------------------------*)

val _ = export_theory();

