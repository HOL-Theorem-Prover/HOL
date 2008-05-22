open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open combinTheory arm_rulesTheory arm_evalTheory armTheory armTheory wordsLib;
open systemTheory;

val _ = new_theory "arm_aux";


(* definitions *)

val _ = Hol_datatype `arm_bit = sN | sZ | sC | sV`;

val ARM_MODE_def = Define `
  ARM_MODE x = DECODE_MODE ((4 >< 0) (CPSR_READ x))`;

val ARM_READ_STATUS_def = Define `
  (ARM_READ_STATUS sN s = (CPSR_READ s.psrs) ' 31) /\ 
  (ARM_READ_STATUS sZ s = (CPSR_READ s.psrs) ' 30) /\ 
  (ARM_READ_STATUS sC s = (CPSR_READ s.psrs) ' 29) /\ 
  (ARM_READ_STATUS sV s = (CPSR_READ s.psrs) ' 28)`;

val ARM_READ_MEM_def = Define `
  ARM_READ_MEM a s = s.memory a`;

val ARM_READ_UNDEF_def = Define `
  ARM_READ_UNDEF s = s.undefined`;

val ARM_READ_REG_def = Define `
  ARM_READ_REG a s = 
    REG_READ (s.registers) (ARM_MODE (s.psrs)) a - if a = 15w then 8w else 0w`;

val ARM_WRITE_REG_def = Define `
  ARM_WRITE_REG a w s = 
    <| registers := REG_WRITE (s.registers) (ARM_MODE (s.psrs)) a w; psrs := s.psrs; 
       memory := s.memory; undefined := s.undefined; cp_state := s.cp_state |>`;

val ARM_WRITE_MEM_def = Define `
  ARM_WRITE_MEM a w s = 
    <| registers := s.registers; psrs := s.psrs; 
       memory := (a =+ w) s.memory; undefined := s.undefined; cp_state := s.cp_state |>`;

val ARM_WRITE_STATUS_def = Define `
  (ARM_WRITE_STATUS x s = 
    <| registers := s.registers; psrs := CPSR_WRITE s.psrs (SET_NZCV x (CPSR_READ s.psrs)); 
       memory := s.memory; undefined := s.undefined; cp_state := s.cp_state |>)`;

val ARM_WRITE_UNDEF_def = Define `
  ARM_WRITE_UNDEF x s = 
    <| registers := s.registers; psrs := s.psrs; 
       memory := s.memory; undefined := x; cp_state := s.cp_state |>`;


(* theorems *)

val ARM_READ_WRITE_REG = prove(
  ``ARM_READ_REG r (ARM_WRITE_REG r' w s) = if r = r' then w else ARM_READ_REG r s``,
  REWRITE_TAC [ARM_WRITE_REG_def,ARM_READ_REG_def]
  THEN Cases_on `r = r'` THEN Cases_on `r = 15w` THEN ASM_SIMP_TAC std_ss []
  THEN SRW_TAC [] [ARM_MODE_def,REG_READ_def,REG_WRITE_def,APPLY_UPDATE_THM]
  THEN FULL_SIMP_TAC std_ss [GSYM num2register_thm,mode_reg2num_lt,num2register_11]
  THEN Q.ABBREV_TAC `m = (DECODE_MODE ((4 >< 0) (CPSR_READ s.psrs)))`
  THEN Q.PAT_ASSUM `Abbrev x` (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC)
  THEN REPEAT (Q.SPEC_TAC (`r`,`r`) THEN Cases_word)
  THEN REPEAT (Q.SPEC_TAC (`r'`,`r'`) THEN Cases_word)
  THEN FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  THEN Cases_on `m` THEN SRW_TAC [] [mode_reg2num_def,USER_def,num2register_thm,LET_DEF]
  THEN `F` by DECIDE_TAC);

val ARM_READ_WRITE_LEMMA = prove(
  ``(ARM_READ_REG r (ARM_WRITE_REG r' w s) = if r = r' then w else ARM_READ_REG r s) /\
    (ARM_READ_UNDEF (ARM_WRITE_UNDEF b s) = b) /\ 
    (ARM_READ_MEM a (ARM_WRITE_MEM a' x s) = if a = a' then x else ARM_READ_MEM a s) /\
    (ARM_READ_STATUS c (ARM_WRITE_STATUS y s) = 
      if c = sN then FST y else if c = sZ then FST (SND y) else
      if c = sC then FST (SND (SND y)) else if c = sV then SND (SND (SND y)) else 
        ARM_READ_STATUS c s)``,
  SRW_TAC [] [ARM_READ_UNDEF_def,ARM_WRITE_UNDEF_def,ARM_READ_MEM_def,ARM_READ_WRITE_REG,
    ARM_WRITE_MEM_def,APPLY_UPDATE_THM,ARM_READ_STATUS_def,ARM_WRITE_STATUS_def]
  THEN Cases_on `y` THEN Cases_on `r` THEN Cases_on `r'`
  THEN REPEAT (Cases_on `c` THEN FULL_SIMP_TAC std_ss [ARM_READ_STATUS_def])
  THEN SRW_TAC [] [CPSR_READ_def,CPSR_WRITE_def,APPLY_UPDATE_THM,
    arm_evalTheory.DECODE_NZCV_SET_NZCV])

val ARM_READ_WRITE = store_thm("ARM_READ_WRITE",
  ``(ARM_READ_REG r (ARM_WRITE_REG r' w s) = if r = r' then w else ARM_READ_REG r s) /\
    (ARM_READ_REG r (ARM_WRITE_MEM a w s) = ARM_READ_REG r s) /\ 
    (ARM_READ_REG r (ARM_WRITE_STATUS b s) = ARM_READ_REG r s) /\ 
    (ARM_READ_REG r (ARM_WRITE_UNDEF g s) = ARM_READ_REG r s) /\
    (ARM_READ_MEM a (ARM_WRITE_REG r v s) = ARM_READ_MEM a s) /\ 
    (ARM_READ_MEM a (ARM_WRITE_MEM a' x s) = if a = a' then x else ARM_READ_MEM a s) /\
    (ARM_READ_MEM a (ARM_WRITE_STATUS b s) = ARM_READ_MEM a s) /\ 
    (ARM_READ_MEM a (ARM_WRITE_UNDEF g s) = ARM_READ_MEM a s) /\
    (ARM_READ_STATUS z (ARM_WRITE_REG r v s) = ARM_READ_STATUS z s) /\ 
    (ARM_READ_STATUS z (ARM_WRITE_MEM a w s) = ARM_READ_STATUS z s) /\ 
    (ARM_READ_STATUS z (ARM_WRITE_STATUS y s) = 
      if z = sN then FST y else if z = sZ then FST (SND y) else
      if z = sC then FST (SND (SND y)) else if z = sV then SND (SND (SND y)) else 
        ARM_READ_STATUS z s) /\
    (ARM_READ_STATUS z (ARM_WRITE_UNDEF g s) = ARM_READ_STATUS z s) /\
    (ARM_READ_UNDEF (ARM_WRITE_REG r v s) = ARM_READ_UNDEF s) /\ 
    (ARM_READ_UNDEF (ARM_WRITE_MEM a w s) = ARM_READ_UNDEF s) /\ 
    (ARM_READ_UNDEF (ARM_WRITE_STATUS b s) = ARM_READ_UNDEF s) /\ 
    (ARM_READ_UNDEF (ARM_WRITE_UNDEF q s) = q)``,
  REWRITE_TAC [ARM_READ_WRITE_LEMMA]
  THEN Cases_on `z` THEN SRW_TAC [] [ARM_READ_REG_def,
    ARM_WRITE_STATUS_def, ARM_WRITE_UNDEF_def, ARM_READ_UNDEF_def,
    ARM_WRITE_REG_def, ARM_MODE_def, CPSR_WRITE_READ,
    ARM_WRITE_MEM_def, ARM_READ_MEM_def, ARM_READ_STATUS_def]
  THEN SIMP_TAC std_ss [word_extract_def,DECODE_IFMODE_SET_NZCV]); 

val ARM_WRITE_MEM_INTRO = store_thm("ARM_WRITE_MEM_INTRO",
  ``<| registers := r; psrs := p; 
       memory := (a =+ w) m; undefined := u; cp_state := c |> =
    ARM_WRITE_MEM a w <| registers := r; psrs := p; 
       memory := m; undefined := u; cp_state := c |>``,
  SRW_TAC [] [ARM_WRITE_MEM_def]);

val ARM_WRITE_REG_INTRO = store_thm("ARM_WRITE_REG_INTRO",
  ``<| registers := REG_WRITE r (ARM_MODE p) a w; psrs := p; 
       memory := m; undefined := u; cp_state := c |> =
    ARM_WRITE_REG a w <| registers := r; psrs := p; 
       memory := m; undefined := u; cp_state := c |>``,
  SRW_TAC [] [ARM_WRITE_REG_def]);

val ARM_WRITE_STATUS_INTRO = store_thm("ARM_WRITE_STATUS_INTRO",
  ``<| registers := r; psrs := CPSR_WRITE p (SET_NZCV x (CPSR_READ p)); 
       memory := m; undefined := u; cp_state := c |> =
    ARM_WRITE_STATUS x <| registers := r; psrs := p; 
       memory := m; undefined := u; cp_state := c |>``,
  SRW_TAC [] [ARM_WRITE_STATUS_def]);

val ARM_WRITE_UNDEF_INTRO = store_thm("ARM_WRITE_UNDEF_INTRO",
  ``<| registers := r; psrs := p; 
       memory := m; undefined := F; cp_state := s.cp_state |> =
    ARM_WRITE_UNDEF F <| registers := r; psrs := p; 
       memory := m; undefined := s.undefined; cp_state := s.cp_state |>``,
  SRW_TAC [] [ARM_WRITE_UNDEF_def]);

val COLLAPSE_ARM_STATE = save_thm("COLLAPSE_ARM_STATE",
  simpLib.SIMP_PROVE (srw_ss()) [arm_sys_state_component_equality]
  ``<| registers := s.registers; psrs := s.psrs; memory := s.memory;
       undefined := s.undefined; cp_state := s.cp_state |> = s``);

val ARM_READ_REG_INTRO = store_thm("ARM_READ_REG_INTRO",
  ``REG_READ (s.registers) (ARM_MODE s.psrs) x =
      if x = 15w then ARM_READ_REG x s + 8w else ARM_READ_REG x s``,
  Cases_on `x = 15w`
  THEN ASM_SIMP_TAC std_ss [ARM_READ_REG_def,WORD_SUB_ADD,WORD_SUB_RZERO]);

val SHIFT_IMMEDIATE2_THM = store_thm("SHIFT_IMMEDIATE2_THM",
  ``SHIFT_IMMEDIATE2 shift sh rm c =
      if sh = 0w then LSL rm shift c else
      if sh = 1w then LSR rm (if shift = 0w then 32w else shift) c else
      if sh = 2w then ASR rm (if shift = 0w then 32w else shift) c else
      if shift = 0w then word_rrx (c,rm) else ROR rm shift c``,
  SRW_TAC [] [armTheory.SHIFT_IMMEDIATE2_def]);    

val CONDITION_PASSED2_AL = store_thm("CONDITION_PASSED2_AL",
  ``!x. CONDITION_PASSED2 x AL``,
  Cases THEN Cases_on `r` THEN Cases_on `r'` THEN SRW_TAC [] [CONDITION_PASSED2_def]);

val ARM_READ_REG_15 = store_thm("ARM_READ_REG_15",
  ``!s. s.registers r15 = ARM_READ_REG 15w s``,
  SRW_TAC [] [ARM_READ_REG_def,REG_READ_def,WORD_ADD_SUB]);

val ARM_WRITE_REG_PC_INTRO = store_thm("ARM_WRITE_REG_PC_INTRO",
  ``(<| registers := INC_PC r; psrs := p; 
        memory := m; undefined := u; cp_state := c |> =
     ARM_WRITE_REG 15w (ARM_READ_REG 15w <| registers := r; psrs := p; 
        memory := m; undefined := u; cp_state := c |> + 4w) <| registers := r; psrs := p; 
        memory := m; undefined := u; cp_state := c |>) /\ 
    (<| registers := REG_WRITE r mm 15w x; psrs := p; 
        memory := m; undefined := u; cp_state := c |> =
     ARM_WRITE_REG 15w x <| registers := r; psrs := p; 
        memory := m; undefined := u; cp_state := c |>)``,
  SRW_TAC [wordsLib.SIZES_ss] [ARM_WRITE_REG_def, INC_PC_def, REG_WRITE_def,
    ARM_READ_REG_def, REG_READ_def, mode_reg2num_def, LET_DEF,num2register_thm]);
 
val ARM_REG_READ_INC_PC = store_thm("ARM_REG_READ_INC_PC",
  ``REG_READ (INC_PC s.registers) m r =
      if r = 15w then ARM_READ_REG 15w s + 12w else REG_READ (s.registers) m r``,
  Cases_on `r = 15w`
  THEN ASM_SIMP_TAC std_ss [REG_READ_def,INC_PC_def,APPLY_UPDATE_THM,ARM_READ_REG_def,WORD_ADD_SUB]  
  THEN SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  THEN `~(r15 = num2register (mode_reg2num m r))` by ALL_TAC
  THEN ASM_SIMP_TAC std_ss [GSYM num2register_thm]
  THEN SIMP_TAC std_ss [mode_reg2num_lt,num2register_11]
  THEN POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`r`,`r`) THEN Cases_word
  THEN FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  THEN Cases_on `m` THEN SRW_TAC [] [mode_reg2num_def,USER_def] THEN DECIDE_TAC);

val WORD_SUB_ONE_MULT = store_thm("WORD_SUB_ONE_MULT",
  ``!x y. x + $- 1w * y = x - y``,SRW_TAC [] [])

val _ = export_theory ();
