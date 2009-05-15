
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory;

open ppc_coretypesTheory ppc_astTheory;

open ppc_seq_monadTheory;

val _ = new_theory "ppc_opsem";


(* ---------------------------------------------------------------------------------- *>

  We define the semantics of an instruction. 

<* ---------------------------------------------------------------------------------- *)

val ppc_sint_cmp_def = Define `
  ppc_sint_cmp ii (a:word32) (b:word32) =
    (parT_unit (write_status ii (PPC_CR0 0w) (SOME (a < b))) 
    (parT_unit (write_status ii (PPC_CR0 1w) (SOME (b < a))) 
    (parT_unit (write_status ii (PPC_CR0 2w) (SOME (a = b))) 
               (write_status ii (PPC_CR0 3w) NONE))))`;

val ppc_uint_cmp_def = Define `
  ppc_uint_cmp ii (a:word32) (b:word32) =
    (parT_unit (write_status ii (PPC_CR0 0w) (SOME (a <+ b))) 
    (parT_unit (write_status ii (PPC_CR0 1w) (SOME (b <+ a))) 
    (parT_unit (write_status ii (PPC_CR0 2w) (SOME (a = b))) 
               (write_status ii (PPC_CR0 3w) NONE))))`;

val OK_nextinstr_def = Define `
  OK_nextinstr ii f = 
    parT_unit f (seqT (read_reg ii PPC_PC) (\x. write_reg ii PPC_PC (x + 4w)))`;

val reg_update_def = Define `
  reg_update ii rd f s1 s2 = 
    seqT (parT s1 s2) (\(x,y). write_reg ii (PPC_IR rd) (f x y))`;

val uint_reg_update_def = Define `
  uint_reg_update ii rd f s1 s2 =
    seqT (parT s1 s2)
         (\(x,y). parT_unit (write_reg ii (PPC_IR rd) (f x y)) (ppc_uint_cmp ii (f x y) 0w))`;

val sint_reg_update_def = Define `
  sint_reg_update ii rd f s1 s2 =
    seqT (parT s1 s2)
         (\(x,y). parT_unit (write_reg ii (PPC_IR rd) (f x y)) (ppc_sint_cmp ii (f x y) 0w))`;

val uint_compare_def = Define `
  uint_compare ii s1 s2 =
    seqT (parT s1 s2) (\(x,y). ppc_uint_cmp ii x y)`;

val sint_compare_def = Define `
  sint_compare ii s1 s2 =
    seqT (parT s1 s2) (\(x,y). ppc_sint_cmp ii x y)`;

val bit_update_def = Define `
  bit_update ii bd (f:bool->bool->bool) s1 s2 = 
    seqT (parT s1 s2) (\(x,y). write_status ii bd (SOME (f x y)))`;

val const_low_s_def  = Define `const_low_s w = constT ((sw2sw:word16->word32) w)`;
val const_high_s_def = Define `const_high_s w = constT (((sw2sw:word16->word32) w) << 16)`;

val const_low_def        = Define `const_low w = constT ((w2w:word16->word32) w)`;
val const_high_def       = Define `const_high w = constT ((w2w:word16->word32) w << 16)`;

val conditional_def = Define `conditional x y z = if x then y else z`;

val read_bit_word_def = Define `
  read_bit_word ii bit = 
    seqT (read_status ii bit) (\x. constT (conditional x 1w 0w))`;

val read_ireg_def = Define `
  read_ireg ii rd = read_reg ii (PPC_IR rd)`;

val gpr_or_zero_def = Define `gpr_or_zero ii d = if d = 0w then const_low 0w else read_ireg ii d`;

val no_carry_def = Define `
  no_carry ii = write_status ii PPC_CARRY NONE`;

val goto_label_def = Define `
  goto_label ii l = 
    seqT (read_reg ii PPC_PC) (\x. write_reg ii PPC_PC (x + sw2sw l * 4w))`;

val PREAD_M_LIST_def = Define `
  PREAD_M_LIST n a s =
    if n = 0 then [] else PREAD_M a s :: PREAD_M_LIST (n-1) (a+1w) s`;

val PWRITE_M_LIST_def = Define `
  (PWRITE_M_LIST a [] s = s) /\
  (PWRITE_M_LIST a (b::bs) s = PWRITE_M a (SOME b) (PWRITE_M_LIST (a+1w) bs s))`;

val effective_address_def = Define `
  effective_address s1 s2 = seqT (parT s1 s2) (\(x:word32,y:word32). constT (x + y))`;

val assertT_def = Define `
  assertT b f = seqT (if b then constT () else failureT) (\x. f)`;

val ppc_write_mem_aux_def = Define `
  (ppc_write_mem_aux ii addr [] = constT ()) /\
  (ppc_write_mem_aux ii addr (b::bytes) = 
     parT_unit (write_mem ii addr b) 
               (ppc_write_mem_aux ii (addr+1w) bytes))`;
    
val reg_store_def = Define `
  reg_store ii size rd s1 s2 =
    seqT (parT (effective_address s1 s2) (read_ireg ii rd))
         (\(addr,x). assertT (address_aligned size addr) 
                             (ppc_write_mem_aux ii addr (REVERSE (word2bytes size x))))`;

val read_mem_aux_def = Define `
  read_mem_aux ii size addr = 
    if size = 1 then 
      seqT (read_mem ii addr) 
           (\x. constT ((bytes2word [x]):word32)) 
    else if size = 2 then
      seqT (parT (read_mem ii addr) (read_mem ii (addr+1w))) 
           (\(x0,x1). constT (bytes2word [x1;x0])) 
    else
      seqT (parT (parT (read_mem ii (addr+0w)) (read_mem ii (addr+1w)))
                 (parT (read_mem ii (addr+2w)) (read_mem ii (addr+3w))))                 
           (\((x0,x1),(x2,x3)). constT (bytes2word [x3;x2;x1;x0]))`;

val load_word_def = Define `
  load_word ii size addr =
    assertT (address_aligned size addr) (read_mem_aux ii size addr)`;

val reg_load_def = Define `
  reg_load ii size rd s1 s2 =
    seqT (effective_address s1 s2)
         (\addr. seqT (load_word ii size addr)
                      (write_reg ii (PPC_IR rd)))`;

val ppc_exec_instr_def = Define `
  (ppc_exec_instr ii (Padd rd r1 r2) = 
       OK_nextinstr ii (reg_update ii rd $+ (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Paddi rd r1 cst) =
       OK_nextinstr ii (reg_update ii rd $+ (gpr_or_zero ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Paddis rd r1 cst ) = 
       OK_nextinstr ii (reg_update ii rd $+ (gpr_or_zero ii r1) (const_high_s cst))) /\

  (ppc_exec_instr ii (Paddze rd r1) = 
       OK_nextinstr ii (reg_update ii rd $+ (read_ireg ii r1) (read_bit_word ii PPC_CARRY))) /\

  (ppc_exec_instr ii (Pand_ rd r1 r2) = 
       OK_nextinstr ii (sint_reg_update ii rd $&& (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pandc rd r1 r2) =
       OK_nextinstr ii (reg_update ii rd (\x y. x && ~y) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pandi_ rd r1 cst) =
       OK_nextinstr ii (sint_reg_update ii rd $&& (read_ireg ii r1) (const_low cst))) /\

  (ppc_exec_instr ii (Pandis_ rd r1 cst) =
       OK_nextinstr ii (sint_reg_update ii rd $&& (read_ireg ii r1) (const_high cst))) /\

  (ppc_exec_instr ii (Pb lbl) =
       goto_label ii lbl) /\

  (ppc_exec_instr ii (Pbctr) =
       seqT (read_reg ii PPC_CTR) (write_reg ii PPC_PC)) /\

  (ppc_exec_instr ii (Pbctrl) =
       seqT (parT (read_reg ii PPC_PC) (read_reg ii PPC_CTR))
            (\(pc,ctr). parT_unit (write_reg ii PPC_PC ctr) (write_reg ii PPC_LR (pc + 4w)))) /\

  (ppc_exec_instr ii (Pbf bit lb1) =
       seqT (read_status ii (PPC_CR0 bit)) 
            (\b. if b then goto_label ii lb1 else OK_nextinstr ii (constT ()))) /\

  (ppc_exec_instr ii (Pbl ident) =
       seqT (read_reg ii PPC_PC) 
            (\x. parT_unit (write_reg ii PPC_PC (x + sw2sw ident * 4w)) (write_reg ii PPC_LR (x + 4w)))) /\

  (ppc_exec_instr ii (Pbs ident) =
       goto_label ii ident) /\

  (ppc_exec_instr ii (Pblr) =
       seqT (read_reg ii PPC_LR) (write_reg ii PPC_PC)) /\

  (ppc_exec_instr ii (Pbt bit lb1) =
       seqT (read_status ii (PPC_CR0 bit)) 
            (\b. if ~b then goto_label ii lb1 else OK_nextinstr ii (constT ()))) /\

  (ppc_exec_instr ii (Pcmplw r1 r2) =
      OK_nextinstr ii (uint_compare ii (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pcmplwi r1 cst) =
      OK_nextinstr ii (uint_compare ii (read_ireg ii r1) (const_low cst))) /\

  (ppc_exec_instr ii (Pcmpw r1 r2) =
      OK_nextinstr ii (sint_compare ii (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pcmpwi r1 cst) =
      OK_nextinstr ii (sint_compare ii (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Pcror bd b1 b2) =
      OK_nextinstr ii (bit_update ii (PPC_CR0 bd) $\/ 
         (read_status ii (PPC_CR0 b1)) (read_status ii (PPC_CR0 b2)))) /\

  (ppc_exec_instr ii (Pdivw rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pdivwu rd r1 r2) = 
      OK_nextinstr ii (reg_update ii rd (\x y. n2w (w2n x DIV w2n y)) 
        (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Peqv rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. ~(x ?? y)) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pextsb rd r1) =
      OK_nextinstr ii (reg_update ii rd (\x y. sw2sw ((w2w x):word8)) 
          (read_ireg ii r1) (constT ()))) /\

  (ppc_exec_instr ii (Pextsh rd r1) =
      OK_nextinstr ii (reg_update ii rd (\x y. sw2sw ((w2w x):word16)) 
        (read_ireg ii r1) (constT ()))) /\

  (ppc_exec_instr ii (Pfabs rd r1) = failureT) /\

  (ppc_exec_instr ii (Pfadd rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pfcmpu r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pfcti rd r1) = failureT) /\

  (ppc_exec_instr ii (Pfdiv rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pfmadd rd r1 r2 r3) = failureT) /\

  (ppc_exec_instr ii (Pfmr rd r1) = failureT) /\

  (ppc_exec_instr ii (Pfmsub rd r1 r2 r3) = failureT) /\

  (ppc_exec_instr ii (Pfmul rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pfneg rd r1) = failureT) /\

  (ppc_exec_instr ii (Pfrsp rd r1) = failureT) /\

  (ppc_exec_instr ii (Pfsub rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pictf rd r1) = failureT) /\

  (ppc_exec_instr ii (Piuctf rd r1) = failureT) /\

  (ppc_exec_instr ii (Plbz rd cst r1) =
      OK_nextinstr ii (reg_load ii 1 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Plbzx rd r1 r2) =
      OK_nextinstr ii (reg_load ii 1 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Plfd rd cst r1) = failureT) /\

  (ppc_exec_instr ii (Plfdx rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Plfs rd cst r1) = failureT) /\

  (ppc_exec_instr ii (Plfsx rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Plha rd cst r1) =
      OK_nextinstr ii (reg_load ii 2 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Plhax rd r1 r2) =
      OK_nextinstr ii (reg_load ii 2 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Plhz rd cst r1) =
      OK_nextinstr ii (reg_load ii 2 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Plhzx rd r1 r2) =
      OK_nextinstr ii (reg_load ii 2 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Plwz rd cst r1) =
      OK_nextinstr ii (reg_load ii 4 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Plwzx rd r1 r2) =
      OK_nextinstr ii (reg_load ii 4 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pmfcrbit v162 v163) = failureT) /\

  (ppc_exec_instr ii (Pmflr rd) =
      OK_nextinstr ii (seqT (read_reg ii PPC_LR) (write_reg ii (PPC_IR rd)))) /\

  (ppc_exec_instr ii (Pmr rd r1) =
      OK_nextinstr ii (seqT (read_ireg ii r1) (write_reg ii (PPC_IR rd)))) /\

  (ppc_exec_instr ii (Pmtctr r1) =
      OK_nextinstr ii (seqT (read_ireg ii r1) (write_reg ii PPC_CTR))) /\

  (ppc_exec_instr ii (Pmtlr r1) =
      OK_nextinstr ii (seqT (read_ireg ii r1) (write_reg ii PPC_LR))) /\

  (ppc_exec_instr ii (Pmulli rd r1 cst) =
      OK_nextinstr ii (reg_update ii rd $* (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Pmullw rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd $* (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pnand rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. ~(x && y)) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pnor rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. ~(x !! y)) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Por rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd $!! (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Porc rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. x !! ~y) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pori rd r1 cst) =
      OK_nextinstr ii (reg_update ii rd $!! (read_ireg ii r1) (const_low cst))) /\

  (ppc_exec_instr ii (Poris rd r1 cst) =
      OK_nextinstr ii (reg_update ii rd $!! (read_ireg ii r1) (const_high cst))) /\

  (ppc_exec_instr ii (Prlwinm rd r1 sh mb me) = failureT) /\

  (ppc_exec_instr ii (Pslw rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. x << w2n ((w2w y):word6)) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Psraw rd r1 r2) =
      OK_nextinstr ii (parT_unit (reg_update ii rd (\x y. x >>> w2n ((w2w y):word6)) (read_ireg ii r1) (read_ireg ii r2)) 
                                 (no_carry ii))) /\

  (ppc_exec_instr ii (Psrawi rd r1 sh) =
      OK_nextinstr ii (parT_unit (reg_update ii rd (\x:word32 y:word32. x >>> w2n ((w2w y):word6)) (read_ireg ii r1) (constT (w2w sh))) 
                                 (no_carry ii))) /\

  (ppc_exec_instr ii (Psrw rd r1 r2) =
      OK_nextinstr ii (reg_update ii rd (\x y. x >> w2n ((w2w y):word6)) (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pstb rd cst r1) =
      OK_nextinstr ii (reg_store ii 1 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Pstbx rd r1 r2) =
      OK_nextinstr ii (reg_store ii 1 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pstfd rd cst r1) = failureT) /\

  (ppc_exec_instr ii (Pstfdx rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Pstfs rd cst r1) = failureT) /\

  (ppc_exec_instr ii (Pstfsx rd r1 r2) = failureT) /\

  (ppc_exec_instr ii (Psth rd cst r1) =
      OK_nextinstr ii (reg_store ii 2 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Psthx rd r1 r2) =
      OK_nextinstr ii (reg_store ii 2 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pstw rd cst r1) =
      OK_nextinstr ii (reg_store ii 4 rd (read_ireg ii r1) (const_low_s cst))) /\

  (ppc_exec_instr ii (Pstwx rd r1 r2) =
      OK_nextinstr ii (reg_store ii 4 rd (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Psubfc rd r1 r2) =
      OK_nextinstr ii (parT_unit (reg_update ii rd $- (read_ireg ii r2) (read_ireg ii r1)) 
                                 (no_carry ii))) /\

  (ppc_exec_instr ii (Psubfic rd r1 cst) =
      OK_nextinstr ii (parT_unit (reg_update ii rd $- (const_low_s cst) (read_ireg ii r1))
                                 (no_carry ii))) /\

  (ppc_exec_instr ii (Pxor rd r1 r2) = 
      OK_nextinstr ii (reg_update ii rd $?? (read_ireg ii r1) (read_ireg ii r2))) /\

  (ppc_exec_instr ii (Pxori rd r1 cst) =
      OK_nextinstr ii (reg_update ii rd $?? (read_ireg ii r1) (const_low cst))) /\

  (ppc_exec_instr ii (Pxoris rd r1 cst ) = 
      OK_nextinstr ii (reg_update ii rd $?? (read_ireg ii r1) (const_high cst)))`;


val ppc_assertT_lemma = store_thm("ppc_assertT_lemma",
  ``!b f. b ==> (assertT b (f:'a ppc_M) = f)``,
  SIMP_TAC std_ss [assertT_def,seqT_def,constT_def,seq_monad_thm,FUN_EQ_THM]);

val _ = export_theory ();
