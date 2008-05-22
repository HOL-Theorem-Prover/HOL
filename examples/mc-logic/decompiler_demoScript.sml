
open HolKernel boolLib bossLib Parse;
open tailrecTheory tailrecLib decompilerLib;
open listTheory pred_setTheory arithmeticTheory wordsTheory;

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
  (llist [] (a:word32,dm,m:word32->word32) = (a = 0w)) /\
  (llist (x::xs) (a,dm,m) = ~(a = 0w) /\  ALIGNED a /\ {a;a+4w} SUBSET dm /\
     ?a'. (m a = a') /\ (m (a+4w) = x) /\ llist xs (a',dm,m))`;

val llist_11 = prove(   
  ``!xs ys a m. llist xs (a,dm,m) ==> llist ys (a,dm,m) ==> (xs = ys)``,
  Induct THEN1 (Cases THEN SIMP_TAC bool_ss [llist_def])
  THEN STRIP_TAC THEN Cases THEN SIMP_TAC bool_ss [llist_def,CONS_11] THEN METIS_TAC []);

(* verification proof *)

val list_fun_pre_LEMMA = (SIMP_RULE std_ss [] o prove) (
  ``(\(a,x,df,f). ?xs. llist xs (x,df,f)) (a,x,df,f) ==> arm_length1_pre (a,x,df,f)``,
  SIMP_TAC (bool_ss++tailrec_ss()) [] 
  THEN HO_MATCH_MP_TAC TAILREC_PRE_IMP
  THEN FULL_SIMP_TAC (std_ss++tailrec_ss()) [pairTheory.FORALL_PROD,LET_DEF]
  THEN STRIP_TAC THEN1 
   (NTAC 4 STRIP_TAC THEN Cases_on `xs`
    THEN FULL_SIMP_TAC bool_ss [llist_def,addressTheory.ALIGNED_def,INSERT_SUBSET])   
  THEN Q.EXISTS_TAC `(\(a,x,dx,xs). @n. ?ys. llist ys (x,dx,xs) /\ (LENGTH ys = n))`
  THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
  THEN1 (Cases_on `xs` THEN FULL_SIMP_TAC bool_ss [llist_def] THEN METIS_TAC [])
  THEN `!ys. llist ys (p_1',p_1'',p_2) = (ys = xs)` by METIS_TAC [llist_11]
  THEN Cases_on `xs` THEN FULL_SIMP_TAC bool_ss [llist_def]
  THEN `!ys. llist ys (p_2 p_1',p_1'',p_2) = (ys = t)` by METIS_TAC [llist_11]
  THEN ASM_SIMP_TAC std_ss [LENGTH,ADD1]);

val list_fun_thm = prove(
  ``!ys a y dm m. llist ys (a,dm,m) ==> 
                  (arm_length1 (y,a,dm,m) = (y + n2w (LENGTH ys),0w,dm,m))``,
  Induct THEN SIMP_TAC (bool_ss++tailrec_ss()) [] THEN ONCE_REWRITE_TAC [TAILREC_def]
  THEN SIMP_TAC (bool_ss++tailrec_reverse_ss()) []
  THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
  THEN `arm_length1_pre (y,a,dm,m)` by METIS_TAC [list_fun_pre_LEMMA]
  THEN FULL_SIMP_TAC (bool_ss++tailrec_ss()) [llist_def,LENGTH,WORD_ADD_0,LET_DEF,
       ADD1,GSYM WORD_ADD_ASSOC,word_add_n2w, AC ADD_ASSOC ADD_COMM]);    

val arm_length_thm = prove(
  ``llist ys (a,dm,m) ==> 
      arm_length_pre (a,dm,m) /\ (arm_length (a,dm,m) = (n2w (LENGTH ys),0w,dm,m))``,
  SIMP_TAC (bool_ss++tailrec_ss()) [] 
  THEN SIMP_TAC (bool_ss++tailrec_reverse_ss()++helperLib.pbeta_ss) [LET_DEF,list_fun_thm]
  THEN METIS_TAC [WORD_ADD_0,list_fun_thm,list_fun_pre_LEMMA,pairTheory.PAIR]);

(* combining the verification proof with the generated theorem *)

val th = save_thm("ARM_LIST_SPEC",INST_SPEC arm_th arm_length_thm);

(* implemented on PowerPC and IA-32 *)

val (ppc_th,ppc_defs) = decompile_ppc "ppc_length" `
  38A00000  (*     addi 5,0,0   *)
  2C140000  (* L1: cmpwi 20,0   *)
  40820010  (*     bc 4,2,L2    *)
  82940000  (*     lwz 20,0(20) *)
  38A50001  (*     addi 5,5,1   *)
  4BFFFFF0  (*     b L1         *)
            (* L2:              *)`;

val (ia32_th,ia32_defs) = decompile_ia32 "ia32_length" `
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
  TAILREC_EQ_TAC());

val ia32_length_eq = prove(
  ``(arm_length = ia32_length) /\ (arm_length_pre = ia32_length_pre)``,
  TAILREC_EQ_TAC());

val ppc_length_thm = REWRITE_RULE [ppc_length_eq] arm_length_thm;
val ia32_length_thm = REWRITE_RULE [ia32_length_eq] arm_length_thm;

(* combining the verification proof with the generated theorem *)

val th = save_thm("PPC_LIST_SPEC",INST_SPEC ppc_th ppc_length_thm);
val th = save_thm("IA32_LIST_SPEC",INST_SPEC ia32_th ia32_length_thm);


val _ = export_theory();

