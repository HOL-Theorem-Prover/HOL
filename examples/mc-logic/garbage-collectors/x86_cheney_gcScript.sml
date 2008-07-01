
open HolKernel boolLib bossLib Parse; val _ = new_theory "x86_cheney_gc";

open decompilerLib tailrecLib tailrecTheory;
open arm_cheney_gcTheory pairTheory wordsTheory addressTheory;
open boolTools;

infix \\
val op \\ = op THEN;
val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val (th,x86_move) = decompile_ia32 "x86_move" `
  85D2            (* test edx, edx *)
  7426            (* je L1 *)
  8B2A            (* mov ebp,[edx] *)
  F7C501000000    (* test ebp,1 *)
  7519            (* jne L12 *)
  8929            (* mov [ecx],ebp *)
  8B7204          (* mov esi,[edx+4] *)
  8B6A08          (* mov ebp,[edx+8] *)
  897104          (* mov [ecx+4],esi *)
  896908          (* mov [ecx+8],ebp *)
  89CD            (* mov ebp,ecx *)
  45              (* inc ebp *)
  81C10C000000    (* add ecx,12 *)
  892A            (* mov [edx],ebp *)
  89EA            (* L12: mov edx,ebp *)
  4A              (* dec edx *)`;

val (th,x86_move2) = decompile_ia32 "x86_move2" `
  85DB            (* L1: test ebx, ebx *)
  7426            (* je L2 *)
  8B2B            (* mov ebp,[ebx] *)
  F7C501000000    (* test ebp,1 *)
  7519            (* jne L22 *)
  8929            (* mov [ecx],ebp *)
  8B7304          (* mov esi,[ebx+4] *)
  8B6B08          (* mov ebp,[ebx+8] *)
  897104          (* mov [ecx+4],esi *)
  896908          (* mov [ecx+8],ebp *)
  89CD            (* mov ebp,ecx *)
  45              (* inc ebp *)
  81C10C000000    (* add ecx,12 *)
  892B            (* mov [ebx],ebp *)
  89EB            (* L22: mov ebx,ebp *)
  4B              (* dec ebx *)`;

val (th,x86_cheney_step) = decompile_ia32 "x86_cheney_step" `
  8B10            (* mov edx,[eax] *)
  8B5804          (* mov ebx,[eax+4] *)
  insert: x86_move
  insert: x86_move2
  8910            (* L2: mov [eax],edx *)
  895804          (* mov [eax+4],ebx *)
  050C000000      (* add eax,12 *)`;

val (th,x86_cheney_loop) = decompile_ia32 "x86_cheney_loop" `
  39C8            (* CHENEY: cmp eax,ecx *)
  7465            (* je EXIT *)
  insert: x86_cheney_step
  EB97            (* jmp CHENEY *)`;

val (th,x86_move_roots) = decompile_ia32 "x86_move_roots" `
  85DB            (* ROOTS: test ebx,ebx *)
  7437            (* je CHENEY *)
  8B17            (* mov edx,[edi] *)
  insert: x86_move
  4B              (* RL:    dec ebx *)
  8917            (* mov [edi],edx *)
  81C704000000    (* add edi,4 *)
  EBC5            (* jmp ROOTS *)`;

val (th,x86_c_init) = decompile_ia32 "x86_c_init" `
  81F201000000    (* xor edx,1 *)
  0F44C1          (* cmove eax, ecx *)`;

val (th,x86_collect) = decompile_ia32 "x86_collect" `
  8B57E4          (* SKIP_J: mov edx,[edi-28] *)
  8B5FE0          (* mov ebx,[edi-32] *)
  89F8            (* mov eax,edi *)
  050C000000      (* add eax,12 *)
  89C1            (* mov ecx,eax *)
  01D9            (* add ecx,ebx *)
  insert: x86_c_init
  8957E4          (* mov [edi-28],edx *)
  89C2            (* mov edx,eax *)
  01DA            (* add edx,ebx *)
  89C1            (* mov ecx,eax *)
  895704          (* mov [edi+4],edx *)
  BB06000000      (* mov ebx,6 *)
  81EF18000000    (* sub edi,24  *)
  insert: x86_move_roots  
  insert: x86_cheney_loop  (* main loop *)
  8B4F04          (* EXIT:  mov ecx,[edi+4] *)`;

val (th,x86_alloc_gc) = decompile_ia32 "x86_alloc_gc" `
  39C8            (* cmp eax,ecx *)
  7405            (* je SKIP_J *)
  E9D8000000      (* jmp NO_GC *)
  insert: x86_collect`; 

val (th,x86_alloc_aux) = decompile_ia32 "x86_alloc_aux" `
  8B6FE8          (* NO_GC: mov ebp,[edi-24]   *)
  8B77EC          (* mov esi,[edi-20] *)
  31DB            (* xor ebx,ebx  *)
  39C8            (* cmp eax,ecx *)
  7410            (* je NG1 *)
  8947E8          (* mov [edi-24],eax *)
  8928            (* mov [eax],ebp *)
  897004          (* mov [eax+4],esi *)
  895808          (* mov [eax+8],ebx *)
  050C000000      (* add eax,12 *)
  8907            (* NG1: mov [edi],eax *)`;

val (th,x86_alloc_mem) = decompile_ia32 "x86_alloc_mem" `
  8B07            (* mov eax,[edi] *)
  8B4F04          (* mov ecx,[edi+4] *)
  insert: x86_alloc_gc   
  insert: x86_alloc_aux`; 

val (x86_alloc_thm,x86_alloc) = decompile_ia32 "x86_alloc" `
  8947E8          (* mov [edi-24],eax *)
  894FEC          (* mov [edi-20],ecx *)
  8957F0          (* mov [edi-16],edx *)
  895FF4          (* mov [edi-12],ebx *)
  896FF8          (* mov [edi-8],ebp *)
  8977FC          (* mov [edi-4],esi *)
  insert: x86_alloc_mem             
  8B47E8          (* mov eax,[edi-24] *)
  8B4FEC          (* mov ecx,[edi-20] *)
  8B57F0          (* mov edx,[edi-16] *)
  8B5FF4          (* mov ebx,[edi-12] *)
  8B6FF8          (* mov ebp,[edi-8] *)
  8B77FC          (* mov esi,[edi-4] *)`;

val _ = save_thm("x86_alloc_thm",x86_alloc_thm);



val x86_move_eq = prove(
  ``(x86_move = arm_move) /\ (x86_move_pre = arm_move_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r4 r5 r7 r8 df f. x = (r4,r5,r7,r8,df,f)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC bool_ss [arm_move,x86_move,LET_DEF]
  \\ SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma2]
  \\ SIMP_TAC std_ss [word_arith_lemma4,word_arith_lemma3,WORD_ADD_0]
  \\ Cases_on `r5' = 0w` \\ ASM_SIMP_TAC std_ss []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [WORD_AND_COMM]))
  \\ Cases_on `f r5' && 1w = 0w` \\ ASM_SIMP_TAC std_ss []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [WORD_AND_COMM]))
  \\ ASM_SIMP_TAC std_ss []);

val x86_move2_eq = prove(
  ``(x86_move2 = arm_move) /\ (x86_move2_pre = arm_move_pre)``,
  REWRITE_TAC [GSYM x86_move_eq] \\ TAILREC_EQ_TAC());

val arm_move2_eq = prove(
  ``(arm_move2 = arm_move) /\ (arm_move2_pre = arm_move_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r4 r5 r7 r8 df f. x = (r4,r5,r7,r8,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [arm_move,arm_move2]);

val x86_cheney_step_eq = prove(
  ``(x86_cheney_step = arm_cheney_step) /\ (x86_cheney_step_pre = arm_cheney_step_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r7 r8 df f. x = (r3,r4,r7,r8,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_cheney_step,arm_cheney_step,x86_move2_eq,x86_move_eq,arm_move2_eq]
  \\ SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]);    

val x86_cheney_loop_eq = prove(
  ``(x86_cheney_loop = arm_cheney_loop) /\ (x86_cheney_loop_pre = arm_cheney_loop_pre)``,
  STRIP_TAC
  \\ ASM_REWRITE_TAC [x86_cheney_step_eq,fetch "-" "x86_cheney_loop_def",arm_cheney_loop_def,
       fetch "-" "x86_cheney_loop_pre_def",arm_cheney_loop_pre_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = x1) /\ (y = y1) /\ (z = z1) ==> (f x y z = f x1 y1 z1)``)
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r5 r6 r7 r8 df f. x = (r3,r4,r5,r6,r7,r8,df,f)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC (std_ss++tailrec_part_ss()) [arm_cheney_loop_step_def,arm_cheney_loop_side_def,
      arm_cheney_loop_base_def,arm_cheney_loop_guard_def,x86_cheney_step_eq] 
  \\ SIMP_TAC std_ss [WORD_EQ_SUB_ZERO]);

val x86_move_roots_eq = prove(
  ``(x86_move_roots = arm_move_roots) /\ (x86_move_roots_pre = arm_move_roots_pre)``,
  STRIP_TAC
  \\ ASM_REWRITE_TAC [x86_move_eq,fetch "-" "x86_move_roots_def",arm_move_roots_def,
       fetch "-" "x86_move_roots_pre_def",arm_move_roots_pre_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = x1) /\ (y = y1) /\ (z = z1) ==> (f x y z = f x1 y1 z1)``)
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r5 r6 r7 r8 df f. x = (r3,r4,r5,r6,r7,r8,df,f)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC (std_ss++tailrec_part_ss()) [arm_move_roots_step_def,arm_move_roots_side_def,
      arm_move_roots_base_def,arm_move_roots_guard_def,x86_cheney_step_eq,LET_DEF,x86_move_eq]);

val x86_collect_eq = prove(
  ``(x86_collect = arm_collect) /\ (x86_collect_pre = arm_collect_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r7 r8 r9 df f. x = (r7,r8,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_collect,arm_collect,x86_move_roots_eq,x86_cheney_loop_eq,arm_c_init,x86_c_init]
  THEN1 (SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]
    \\ Cases_on `f (r9' - 28w) ?? 1w = 0w` \\ ASM_SIMP_TAC std_ss []
    \\ `?yr4 yr5 yr6 yr7 yr8 yr9 ydf' yf'. (arm_move_roots
           (r9' + 12w + f (r9' - 32w),
            r9' + 12w + f (r9' - 32w) + f (r9' - 32w),6w ,r7',r8',r9' - 24w,df,
            (r9' + 4w =+ r9' + 12w + f (r9' - 32w) + f (r9' - 32w))
              ((r9' - 28w =+ 0w) f))) = (yr4,yr5,yr6,yr7,yr8,yr9,ydf',yf')` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []
    \\ `?ir3 ir4 ir5 ir6 ir7 ir8 idf' if'. (arm_cheney_loop
           (r9' + 12w + f (r9' - 32w),yr4,yr5,yr6,yr7,yr8,ydf',yf'))
            = (ir3,ir4,ir5,ir6,ir7,ir8,idf',if')` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []) 
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `f (r9' - 28w) ?? 1w = 0w` \\ ASM_SIMP_TAC std_ss [] THENL [
    `?yr4 yr5 yr6 yr7 yr8 yr9 ydf' yf'. (arm_move_roots
        (r9' + 12w + f (r9' - 32w),r9' + 12w + f (r9' - 32w) + f (r9' - 32w),
         6w ,r7',r8',r9' - 24w,df,
          (r9' + 4w =+ r9' + 12w + f (r9' - 32w) + f (r9' - 32w))
            ((r9' - 28w =+ 0w) f)) = (yr4,yr5,yr6,yr7,yr8,yr9,ydf',yf'))` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []
    \\ `?ir3 ir4 ir5 ir6 ir7 ir8 idf jf. arm_cheney_loop
           (r9' + 12w + f (r9' - 32w),yr4,yr5,yr6,yr7,yr8,ydf',yf') =
        (ir3,ir4,ir5,ir6,ir7,ir8,idf,jf) ` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC (std_ss++bool_eq_imp_ss) [],
    `?yr4 yr5 yr6 yr7 yr8 yr9 ydf' yf'. (arm_move_roots
     (r9' + 12w,r9' + 12w + f (r9' - 32w),6w ,r7',r8',r9' - 24w,df,
          (r9' + 4w =+ r9' + 12w + f (r9' - 32w))
            ((r9' - 28w =+ f (r9' - 28w) ?? 1w) f)) = (yr4,yr5,yr6,yr7,yr8,yr9,ydf',yf'))` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []
    \\ `?ir3 ir4 ir5 ir6 ir7 ir8 idf jf. arm_cheney_loop
           (r9' + 12w,yr4,yr5,yr6,yr7,yr8,ydf',yf') =
        (ir3,ir4,ir5,ir6,ir7,ir8,idf,jf) ` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC (std_ss++bool_eq_imp_ss) []]); 

val x86_alloc_gc_eq = prove(
  ``(x86_alloc_gc = arm_alloc_gc) /\ (x86_alloc_gc_pre = arm_alloc_gc_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r5 r6 r7 r8 r9 df f. x = (r3,r4,r5,r6,r7,r8,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_collect_eq,x86_alloc_gc,arm_alloc_gc,WORD_EQ_SUB_ZERO]
  \\ Cases_on `r3' = r4'` \\ ASM_SIMP_TAC bool_ss []);

val x86_alloc_aux_eq = prove(
  ``(x86_alloc_aux = arm_alloc_aux) /\ (x86_alloc_aux_pre = arm_alloc_aux_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r9 df f. x = (r3,r4,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_alloc_aux,arm_alloc_aux,x86_alloc_gc_eq,WORD_EQ_SUB_ZERO]
  \\ Cases_on `r3' = r4'` \\ ASM_SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]);

val x86_alloc_mem_eq = prove(
  ``(x86_alloc_mem = arm_alloc_mem) /\ (x86_alloc_mem_pre = arm_alloc_mem_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r5 r6 r7 r8 r9 df f. x = (r5,r6,r7,r8,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_alloc_mem,arm_alloc_mem,x86_alloc_aux_eq,WORD_EQ_SUB_ZERO]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,word_arith_lemma1,x86_alloc_gc_eq]);
  
val x86_alloc_eq = store_thm("x86_alloc_eq",
  ``(x86_alloc = arm_alloc) /\ (x86_alloc_pre = arm_alloc_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ `?r3 r4 r5 r6 r7 r8 r9 df f. x = (r3,r4,r5,r6,r7,r8,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [x86_alloc,arm_alloc,x86_alloc_mem_eq,WORD_EQ_SUB_ZERO]);


val _ = export_theory();
