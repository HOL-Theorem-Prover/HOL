
open HolKernel boolLib bossLib Parse;
open wordsTheory;
open decompilerLib;
open mc_tailrecLib listTheory pred_setTheory arithmeticTheory;

val decompile_arm = decompile prog_armLib.arm_tools;
val decompile_ppc = decompile prog_ppcLib.ppc_tools;
val decompile_x86 = decompile prog_x86Lib.x86_tools;

val _ = new_theory "decompiler_demo";

(* ARM code for length of linked-list *)

val (arm_th,arm_defs) = decompile_arm "arm_length" `
  E3A00000  (*    mov r0,#0       *)
  E3510000  (* L: cmp r1,#0       *)
  12800001  (*    addne r0,r0,#1  *)
  15911000  (*    ldrne r1,[r1]   *)
  1AFFFFFB  (*    bne L           *)`;

(* formalising notion of linked-list *)

val llist_def = Define `
  (llist [] (a:word32,dm,m:word32->word32) <=> (a = 0w)) /\
  (llist (x::xs) (a,dm,m) <=>
     ~(a = 0w) /\ (a && 3w = 0w) /\ {a;a+4w} SUBSET dm /\
     ?a'. (m a = a') /\ (m (a+4w) = x) /\ llist xs (a',dm,m))`;

(* verification proof *)

val arm_length1_thm = prove(
  ``!ys a y dm m. llist ys (a,dm,m) ==> arm_length1_pre (y,a,dm,m) /\
                  (arm_length1 (y,a,dm,m) = (y + n2w (LENGTH ys),0w,dm,m))``,
  Induct THEN ONCE_REWRITE_TAC [arm_defs]
  THEN SIMP_TAC bool_ss [llist_def,LENGTH,WORD_ADD_0,LET_DEF,EMPTY_SUBSET,
    INSERT_SUBSET, ONCE_REWRITE_RULE [ADD_COMM] ADD1, GSYM word_add_n2w, WORD_ADD_ASSOC]
  THEN METIS_TAC [])

val arm_length_thm = prove(
  ``!ys y dm m. llist ys (y,dm,m) ==> arm_length_pre (y,dm,m) /\
                (arm_length (y,dm,m) = (n2w (LENGTH ys),0w,dm,m))``,
  ONCE_REWRITE_TAC [arm_defs]
  THEN SIMP_TAC (std_ss++helperLib.pbeta_ss) [LET_DEF]
  THEN METIS_TAC [arm_length1_thm,WORD_ADD_0]);

(* combining the verification proof with the generated theorem *)

val th = save_thm("ARM_LIST_SPEC",
  SIMP_RULE std_ss [LET_DEF] (INST_SPEC arm_th arm_length_thm));

(* implemented on PowerPC and IA-32 *)

val (ppc_th,ppc_defs) = decompile_ppc "ppc_length" `
  38A00000  (*     addi 5,0,0   *)
  2C140000  (* L1: cmpwi 20,0   *)
  41820010  (*     beq L2       *)
  82940000  (*     lwz 20,0(20) *)
  38A50001  (*     addi 5,5,1   *)
  4BFFFFF0  (*     b L1         *)
            (* L2:              *)`;

val (x86_th,x86_defs) = decompile_x86 "x86_length" `
  31C0  (*     xor eax, eax       *)
  85F6  (* L1: test esi, esi      *)
  7405  (*     jz L2              *)
  40    (*     inc eax            *)
  8B36  (*     mov esi, [esi]     *)
  EBF7  (*     jmp L1             *)
        (* L2:                    *)`;

(* verification proof *)

val ppc_length_eq = prove(
  ``(arm_length = ppc_length) /\ (arm_length_pre = ppc_length_pre)``,
  NTAC 2 TAILREC_TAC THEN SIMP_TAC std_ss [LET_DEF]);

val x86_length_eq = prove(
  ``(arm_length = x86_length) /\ (arm_length_pre = x86_length_pre)``,
  NTAC 2 TAILREC_TAC THEN SIMP_TAC std_ss [LET_DEF]);

val ppc_length_thm = REWRITE_RULE [ppc_length_eq] arm_length_thm;
val x86_length_thm = REWRITE_RULE [x86_length_eq] arm_length_thm;

(* combining the verification proof with the generated theorem *)

val th = save_thm("PPC_LIST_SPEC",
  SIMP_RULE std_ss [LET_DEF] (INST_SPEC ppc_th ppc_length_thm));

val th = save_thm("X86_LIST_SPEC",
  SIMP_RULE std_ss [LET_DEF] (INST_SPEC x86_th x86_length_thm));

(* example of non-nested loop *)

val (arm_th,arm_defs) = decompile_arm "arm_loop" `
  E2800001    (*      add r0,r0,#1     *)
  E2800001    (*  L:  add r0,r0,#1     *)
  E3100001    (*  M:  tst r0,#1        *)
  1AFFFFFC    (*      bne L            *)
  E2500002    (*      subs r0,r0,#2    *)
  1AFFFFFB    (*      bne M            *)`;

val _ = export_theory();
