(* ===================================================================== *)
(* FILE          : armScript.sml                                         *)
(* DESCRIPTION   : Model of the ARM instruction set architecture (v4)    *)
(*                                                                       *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge              *)
(* DATE          : 2001 - 2005                                           *)
(* ===================================================================== *)

(* interactive use:
  app load ["io_onestepTheory","bitsTheory","word32Theory","rich_listTheory"];
*)

open HolKernel boolLib bossLib Q Parse prim_recTheory
     io_onestepTheory bitsTheory word32Theory rich_listTheory;

val _ = new_theory "arm";

(* --------------------------------------------------------
   The ARM State Space
   -------------------------------------------------------- *)

val _ = Hol_datatype `register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;
val _ = Hol_datatype `psrs = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und`;

val _ = type_abbrev("reg", ``:register->word32``);
val _ = type_abbrev("psr", ``:psrs->word32``);

val _ = Hol_datatype `exception = reset | undefined | software | pabort |
                                  dabort | address |interrupt | fast`;

val _ = Hol_datatype `state_arm = ARM of reg=>psr`;
val _ = Hol_datatype `state_arm_ex = ARM_EX of state_arm=>word32=>exception`;

(* ........................................................ *)

val _ = Hol_datatype `memop      = MemRead of word32 | MemWrite of bool=>word32=>word32`;
val _ = Hol_datatype `interrupts = Reset of state_arm | Prefetch | Dabort of num | Fiq | Irq`;
val _ = Hol_datatype `mode       = usr | fiq | irq | svc | abt | und | safe`;
val _ = Hol_datatype `condition  = EQ | CS | MI | VS | HI | GE | GT | AL |
                                   NE | CC | PL | VC | LS | LT | LE | NV`;
val _ = Hol_datatype `iclass     = swp | mrs_msr | data_proc | reg_shift | mla_mul |
                                   ldr | str | ldm | stm | br | swi_ex | cdp_und | unexec`;

(* ........................................................ *)

val SUBST_def = Define`SUBST m a b c = if a = c then b else m c`;

val _ = add_rule{term_name = "SUBST", fixity = Suffix 1,
  pp_elements = [HardSpace 1, TOK "{.", TM, BreakSpace(1,0),
                 TOK "<-", BreakSpace(1,0), TM, TOK ".}"],
  paren_style = OnlyIfNecessary, block_style = (AroundSameName, (PP.INCONSISTENT, 0))};

val _ = overload_on("w32",``n2w``);

(* --------------------------------------------------------
   General Purpose Register operations
   -------------------------------------------------------- *)

val USER_def = Define`USER mode = (mode = usr) \/ (mode = safe)`;

val mode_num2register_def = Define`
  mode_num2register m n =
    num2register
      (if (n = 15) \/ USER m \/ (m = fiq) /\ n < 8 \/ ~(m = fiq) /\ n < 13 then
         n
       else case m of
          fiq -> n + 8
       || irq -> n + 10
       || svc -> n + 12
       || abt -> n + 14
       || und -> n + 16
       || _ -> ARB)`;
         
val REG_READ_def = Define`
  REG_READ reg m n =
    if n = 15 then
      reg r15 + 8w
    else
      reg (mode_num2register m n)`;

val REG_WRITE_def = Define`
  REG_WRITE reg m n d = (reg {.mode_num2register m n <- d.})`;

(* ........................................................ *)

val INC_PC_def   = Define `INC_PC reg = (reg {.r15 <- reg r15 + 4w.})`;
val FETCH_PC_def = Define `FETCH_PC reg = reg r15`;

(* FETCH_PC needed because (REG_READ reg usr 15) gives PC+8 *)

(* --------------------------------------------------------
   Program Status Register operations
   -------------------------------------------------------- *)

val SET_NZCV_def = Define`
  SET_NZCV (N,Z,C,V) n =
    w32 (SBIT N 31 + SBIT Z 30 + SBIT C 29 + SBIT V 28 + WORD_BITS 27 0 n)`;

val SET_NZC_def = Define `SET_NZC (N,Z,C) n = SET_NZCV (N,Z,C,WORD_BIT 28 n) n`;

val mode_num_def = Define`
  mode_num mode =
    case mode of
       usr -> 16
    || fiq -> 17
    || irq -> 18
    || svc -> 19
    || abt -> 23
    || und -> 27
    || _ -> 0`;

val SET_IFMODE_def = Define`
  SET_IFMODE irq' fiq' mode n =
    w32 (WORD_SLICE 31 8 n + SBIT irq' 7 + SBIT fiq' 6 + WORD_SLICE 5 5 n + mode_num mode)`;

(* ........................................................ *)

val DECODE_MODE_def = Define`
  DECODE_MODE m =
     if m = 16 then usr else
     if m = 17 then fiq else
     if m = 18 then irq else
     if m = 19 then svc else
     if m = 23 then abt else
     if m = 27 then und else safe`;

val NZCV_def = Define`NZCV n = (BIT 31 n,BIT 30 n,BIT 29 n,BIT 28 n)`;

val DECODE_PSR_def = Define`
  DECODE_PSR cpsr = let n = w2n cpsr in (NZCV n,BIT 7 n,BIT 6 n,BITS 4 0 n)`;

val CARRY_def = Define`CARRY (n,z,c,v) = c`;

val mode2psr_def = Define`
   mode2psr mode =
     case mode of
        usr -> CPSR
     || fiq -> SPSR_fiq
     || irq -> SPSR_irq
     || svc -> SPSR_svc
     || abt -> SPSR_abt
     || und -> SPSR_und
     || _   -> CPSR`;

(* ........................................................ *)

val SPSR_READ_def = Define`SPSR_READ psr mode = psr (mode2psr mode)`;
val CPSR_READ_def = Define`CPSR_READ psr = psr CPSR`;

val CPSR_WRITE_def = Define`CPSR_WRITE psr cpsr = (psr {.CPSR <- cpsr.})`;

val SPSR_WRITE_def = Define`
  SPSR_WRITE psr mode spsr =
    if USER mode then psr else (psr {.mode2psr mode <- spsr.})`;

(* --------------------------------------------------------
   The Sofware Interrupt/Exception instruction class (swi_ex)
   -------------------------------------------------------- *)

val exception2mode_def = Define`
  exception2mode e =
    case e of
       reset     -> svc
    || undefined -> und
    || software  -> svc
    || address   -> svc
    || pabort    -> abt
    || dabort    -> abt
    || interrupt -> irq
    || fast      -> fiq`;

val EXCEPTION_def = Define`
  EXCEPTION (ARM reg psr) type =
    let cpsr = CPSR_READ psr in
    let fiq' = if (type = reset) \/ (type = fast) then T else WORD_BIT 6 cpsr
    and mode' = exception2mode type
    and pc = w32 (4 * exception2num type) in
    let reg' = REG_WRITE reg mode' 14 (FETCH_PC reg + 4w) in
      ARM (REG_WRITE reg' usr 15 pc)
         (CPSR_WRITE (SPSR_WRITE psr mode' cpsr) (SET_IFMODE T fiq' mode' cpsr))`;

(* --------------------------------------------------------
   The Branch instruction class (br)
   -------------------------------------------------------- *)

val SIGN_EX_OFFSET_def = Define`
  SIGN_EX_OFFSET n = w32 (SIGN_EXTEND 24 30 n)`;

val DECODE_BRANCH_def = Define`
  DECODE_BRANCH n = (BIT 24 n,BITS 23 0 n)`;

val BRANCH_def = Define`
  BRANCH (ARM reg psr) mode n =
    let (L,offset) = DECODE_BRANCH n
    and pc  = REG_READ reg usr 15 in
    let pc' = pc + SIGN_EX_OFFSET offset << 2 in
    let reg' = REG_WRITE reg usr 15 pc' in
      ARM (if L then REG_WRITE reg' mode 14 (FETCH_PC reg + 4w) else reg') psr`;

(* --------------------------------------------------------
   The Data Processing instruction class (data_proc, reg_shift)
   -------------------------------------------------------- *)

val LSL_def = Define`
  LSL m n c = if n = 0   then (c,m) else
              if n <= 32 then (WORD_BIT (32 - n) m,m << n)
                         else (F,0w)`;

val LSR_def = Define`
  LSR m n c = if n = 0   then LSL m 0 c else
              if n <= 32 then (WORD_BIT (n - 1) m,m >>> n)
                         else (F,0w)`;

val ASR_def = Define`
  ASR m n c = if n = 0   then LSL m 0 c else
              if n <= 32 then (WORD_BIT (n - 1) m,m >> n)
                         else (MSB m,m >> 32)`;

val ROR_def = Define`
  ROR m n c = if n = 0   then LSL m 0 c else
              if n <= 32 then (WORD_BIT (n - 1) m,m #>> n)
                         else let n' = BITS 4 0 n in
                                 (WORD_BIT (n' - 1) m,m #>> n')`;

val RRX2_def = Define `RRX2 m c = (LSB m,RRX c m)`;

val IMMEDIATE_def = Define`
  IMMEDIATE C opnd2 =
    let (rot,imm) = DIVMOD_2EXP 8 opnd2 in
       ROR (w32 imm) (2 * rot) C`;

val SHIFT_IMMEDIATE2_def = Define`
  SHIFT_IMMEDIATE2 shift sh rm c =
    if shift = 0 then
      if sh = 0 then LSL rm 0 c  else
      if sh = 1 then LSR rm 32 c else
      if sh = 2 then ASR rm 32 c else
      (* sh = 3 *)   RRX2 rm c
    else
      if sh = 0 then LSL rm shift c else
      if sh = 1 then LSR rm shift c else
      if sh = 2 then ASR rm shift c else
      (* sh = 3 *)   ROR rm shift c`;

val SHIFT_REGISTER2_def = Define`
  SHIFT_REGISTER2 shift sh rm c =
      if sh = 0 then LSL rm shift c else
      if sh = 1 then LSR rm shift c else
      if sh = 2 then ASR rm shift c else
      (* sh = 3 *)   ROR rm shift c`;

val SHIFT_IMMEDIATE_def = Define`
  SHIFT_IMMEDIATE reg mode C opnd2 =
    let rm = REG_READ reg mode (BITS 3 0 opnd2) in
      SHIFT_IMMEDIATE2 (BITS 11 7 opnd2) (BITS 6 5 opnd2) rm C`;

val SHIFT_REGISTER_def = Define`
  SHIFT_REGISTER reg mode C opnd2 =
    let shift = WORD_BITS 7 0 (REG_READ reg mode (BITS 11 8 opnd2))
    and rm = REG_READ (INC_PC reg) mode (BITS 3 0 opnd2) in
      SHIFT_REGISTER2 shift (BITS 6 5 opnd2) rm C`;

val ADDR_MODE1_def = Define`
  ADDR_MODE1 reg mode C Im opnd2 =
    if Im then
      IMMEDIATE C opnd2
    else if BIT 4 opnd2 then
      SHIFT_REGISTER reg mode C opnd2
    else
      SHIFT_IMMEDIATE reg mode C opnd2`;

(* ........................................................ *)

val ALU_arith_def = Define`
  ALU_arith op rn op2 =
    let  sign = MSB rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n op2)) in
    let   res = w32 r in
      ((MSB res,r = 0,ODD q,(MSB op2 = sign) /\ ~(MSB res = sign)),res)`;

val ALU_arith_neg_def = Define`
  ALU_arith_neg op rn op2 =
    let  sign = MSB rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n ~op2)) in
    let   res = w32 r in
      ((MSB res,r = 0,ODD q \/ (op2 = 0w),~(MSB op2 = sign) /\ ~(MSB res = sign)),res)`;

val ALU_logic_def = Define`
  ALU_logic res = ((MSB res,w2n res = 0,F,F),res)`;

val SUB_def = Define`
  SUB a b c = ALU_arith_neg (\x y.x+y+(if c then 0 else TWO_COMP 1)) a b`;
val ADD_def = Define`
  ADD a b c = ALU_arith (\x y.x+y+(if c then 1 else 0)) a b`;
val AND_def = Define`AND a b = ALU_logic (a & b)`;
val EOR_def = Define`EOR a b = ALU_logic (a # b)`;
val ORR_def = Define`ORR a b = ALU_logic (a | b)`;

val ALU_def = Define`
 ALU opc rn op2 c =
   if (opc = 0) \/ (opc = 8)  then AND rn op2    else
   if (opc = 1) \/ (opc = 9)  then EOR rn op2    else
   if (opc = 2) \/ (opc = 10) then SUB rn op2 T  else
   if (opc = 4) \/ (opc = 11) then ADD rn op2 F  else
   if opc = 3  then ADD (NOT rn) op2 T           else
   if opc = 5  then ADD rn op2 c                 else
   if opc = 6  then SUB rn op2 c                 else
   if opc = 7  then ADD (NOT rn) op2 c           else
   if opc = 12 then ORR rn op2                   else
   if opc = 13 then ALU_logic op2                else
   if opc = 14 then AND rn (NOT op2)             else
   (* opc = 15 *)   ALU_logic (NOT op2)`;

(* ........................................................ *)

val ARITHMETIC_def = Define`
  ARITHMETIC opcode = (1 < opcode /\ opcode < 8) \/ (opcode = 10) \/ (opcode = 11)`;

val TEST_OR_COMP_def = Define`
  TEST_OR_COMP opcode = 7 < opcode /\ opcode < 12`;

val DECODE_DATAP_def = Define`
  DECODE_DATAP n =
    (BIT 25 n,BITS 24 21 n,BIT 20 n,BITS 19 16 n,BITS 15 12 n,BITS 11 0 n)`;

val DATA_PROCESSING_def = Define`
  DATA_PROCESSING (ARM reg psr) C mode n =
    let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP n in
    let (C_s,op2) = ADDR_MODE1 reg mode C I opnd2
    and pc_reg = INC_PC reg in
    let rn = REG_READ (if ~I /\ (BIT 4 opnd2) then pc_reg else reg) mode Rn in
    let ((N,Z,C_alu,V),res) = ALU opcode rn op2 C in
      ARM (if TEST_OR_COMP opcode then pc_reg else REG_WRITE pc_reg mode Rd res)
        (if S then
           CPSR_WRITE psr
             (if Rd = 15 then SPSR_READ psr mode
                         else (if ARITHMETIC opcode
                                 then SET_NZCV (N,Z,C_alu,V)
                                 else SET_NZC  (N,Z,C_s)) (CPSR_READ psr))
         else psr)`;

(* --------------------------------------------------------
   The PSR Transfer instruction class (mrs_msr)
   -------------------------------------------------------- *)

val DECODE_MRS_def = Define`
  DECODE_MRS n = (BIT 22 n,BITS 15 12 n)`;

val MRS_def = Define`
  MRS (ARM reg psr) mode n =
    let (R,Rd) = DECODE_MRS n in
    let word = if R then SPSR_READ psr mode else CPSR_READ psr in
      ARM (REG_WRITE (INC_PC reg) mode Rd word) psr`;

(* ........................................................ *)

val SPLIT_WORD_def = Define`
  SPLIT_WORD a = (WORD_BITS 31 28 a,WORD_BITS 27 8 a,WORD_BITS 7 0 a)`;

val CONCAT_BYTES_def = Define`
  CONCAT_BYTES a b c = w32 (TIMES_2EXP 28 a + TIMES_2EXP 8 b + c)`;

val DECODE_MSR_def = Define`
  DECODE_MSR n = (BIT 25 n,BIT 22 n,BIT 19 n,BIT 16 n,BITS 3 0 n,BITS 11 0 n)`;

val MSR_def = Define`
  MSR (ARM reg psr) mode n =
    let (I,R,bit19,bit16,Rm,opnd) = DECODE_MSR n in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      ARM (INC_PC reg) psr
    else
      let xpsr = if R then SPSR_READ psr mode else CPSR_READ psr
      and  src = if I then SND (IMMEDIATE F opnd) else REG_READ reg mode Rm in
      let (x2,x1,x0) = SPLIT_WORD xpsr
      and (s2,s1,s0) = SPLIT_WORD src in
      let xpsr' = CONCAT_BYTES (if bit19 then s2 else x2) x1
                               (if bit16 /\ ~(USER mode) then s0 else x0) in
        ARM (INC_PC reg)
         (if R then SPSR_WRITE psr mode xpsr' else CPSR_WRITE psr xpsr')`;

(* --------------------------------------------------------
   The Multiply (and Accumulate) instruction class (mla_mul)
   -------------------------------------------------------- *)

val BORROW2_def = Define`
  BORROW2 rs n = ~(n = 0) /\ WORD_BIT (2 * n - 1) rs`;

val MSHIFT2_def = Define`
  MSHIFT2 borrow mul n =
    n * 2 + if borrow /\ (mul = 1) \/ ~borrow /\ (mul = 2) then 1 else 0`;

val MLA_MUL_DONE_def = Define`
  MLA_MUL_DONE rs n =
    ~(n = 0) /\ (WORD_BITS HB (2 * n) rs = 0) /\ ~BORROW2 rs n \/ ~(2 * n < WL)`;

val MLA_MUL_DUR_def = Define `MLA_MUL_DUR rs = LEAST n. MLA_MUL_DONE rs n`;

val MLA_MUL_CARRY_def = Define`
  MLA_MUL_CARRY rm rs C = let n = MLA_MUL_DUR rs - 1 in
    FST (LSL rm (MSHIFT2 (BORROW2 rs n) (BITS 1 0 (WORD_BITS HB (2 * n) rs)) n) C)`;

val ALU_multiply_def = Define`
  ALU_multiply A rm rs rn C =
    let res = if A then rm * rs + rn else rm * rs in
      (MSB res,res = 0w,MLA_MUL_CARRY rm rs C,res)`;

val DECODE_MLA_MUL_def = Define`
  DECODE_MLA_MUL n = (BIT 21 n,BIT 20 n,BITS 19 16 n,BITS 15 12 n,BITS 11 8 n,BITS 3 0 n)`;

val MLA_MUL_def = Define`
  MLA_MUL (ARM reg psr) C mode n =
    let (A,S,Rd,Rn,Rs,Rm) = DECODE_MLA_MUL n in
    let pc_reg = INC_PC reg in
    let rn = REG_READ reg mode Rn
    and rs = REG_READ reg mode Rs
    and rm = REG_READ pc_reg mode Rm in
    let (N,Z,C_s,res) = ALU_multiply A rm rs rn C in
      if (Rd = 15) \/ (Rd = Rm) then
        ARM pc_reg psr
      else
        ARM (REG_WRITE pc_reg mode Rd res)
          (if S then CPSR_WRITE psr (SET_NZC (N,Z,C_s) (CPSR_READ psr)) else psr)`;

(* --------------------------------------------------------
   The Single Data Transfer instruction class (ldr, str)
   -------------------------------------------------------- *)

val BW_READ_def = Define`
  BW_READ B align data =
    let l = 8 * align in
      if B then w32 (WORD_BITS (l + 7) l data) else data #>> l`;

val UP_DOWN_def = Define`UP_DOWN u = if u then $word_add else $word_sub`;

val ADDR_MODE2_def = Define`
  ADDR_MODE2 reg mode C Im P U Rn offset =
    let addr  = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr (if Im then SND (SHIFT_IMMEDIATE reg mode C offset)
                                      else w32 offset) in
      (if P then wb_addr else addr,wb_addr)`;

val DECODE_LDR_STR_def = Define`
  DECODE_LDR_STR n =
     (BIT 25 n,BIT 24 n,BIT 23 n,BIT 22 n,BIT 21 n,BIT 20 n,
      BITS 19 16 n,BITS 15 12 n,BITS 11 0 n)`;

val LDR_STR_def = Define`
  LDR_STR (ARM reg psr) C mode isdabort data n =
    let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in
    let (addr,wb_addr) = ADDR_MODE2 reg mode C I P U Rn offset in
    let pc_reg = INC_PC reg in
    let wb_reg = if P ==> W then REG_WRITE pc_reg mode Rn wb_addr else pc_reg in
      <| state :=
           ARM (if L ==> isdabort then
                  wb_reg
                else REG_WRITE wb_reg mode Rd (BW_READ B (WORD_BITS 1 0 addr) data))
               psr;
         out :=
           [if L then
              MemRead addr
            else
              MemWrite B addr (REG_READ pc_reg mode Rd)] |>`;

(* --------------------------------------------------------
   The Block Data Transfer instruction class (ldm, stm)
   -------------------------------------------------------- *)

val REGISTER_LIST_def = Define`
  REGISTER_LIST n = (MAP SND o FILTER FST) (GENLIST (\b. (BIT b n,b)) 16)`;

val ADDRESS_LIST_def = Define`
  ADDRESS_LIST start n = GENLIST (\a. start + w32 (4 * a)) n`;

val WB_ADDRESS_def = Define`
  WB_ADDRESS U base len = UP_DOWN U base (w32 (4 * len))`;

val FIRST_ADDRESS_def = Define`
  FIRST_ADDRESS P U base wb =
    if U then if P then base + 4w else base
         else if P then wb else wb + 4w`;

val ADDR_MODE4_def = Define`
  ADDR_MODE4 P U base n =
    let rp_list = REGISTER_LIST n in
    let len = LENGTH rp_list in
    let wb = WB_ADDRESS U base len in
    let addr_list = ADDRESS_LIST (FIRST_ADDRESS P U base wb) len in
      (rp_list,addr_list,wb)`;

val LDM_LIST_def = Define`
  LDM_LIST reg mode rp_list data =
    FOLDL (\reg' (rp,rd). REG_WRITE reg' mode rp rd) reg (ZIP (rp_list,data))`;

val STM_LIST_def = Define`
  STM_LIST reg mode bl_list =
    MAP (\(rp,addr). MemWrite F addr (REG_READ reg mode rp)) bl_list`;

val DECODE_LDM_STM_def = Define`
  DECODE_LDM_STM n = (BIT 24 n,BIT 23 n,BIT 22 n,BIT 21 n,BIT 20 n,BITS 19 16 n,BIT 15 n)`;

val LDM_STM_def = Define`
  LDM_STM (ARM reg psr) mode dabort_t data n =
    let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in
    let rn = REG_READ reg mode Rn in
    let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn n
    and mode' = if S /\ (L ==> ~pc_in_list) then usr else mode
    and pc_reg = INC_PC reg in
    let wb_reg = if W /\ ~(Rn = 15) then REG_WRITE pc_reg (if L then mode else mode') Rn rn' else pc_reg in
      <| state :=
           if L then
             ARM (let t = if IS_SOME dabort_t then THE dabort_t else LENGTH rp_list in
                  let ldm_reg = LDM_LIST wb_reg mode' (FIRSTN t rp_list) (FIRSTN t data) in
                    if IS_SOME dabort_t /\ ~(Rn = 15) then
                      REG_WRITE ldm_reg mode' Rn (REG_READ wb_reg mode' Rn)
                    else ldm_reg)
                 (if S /\ pc_in_list /\ ~IS_SOME dabort_t then
                    CPSR_WRITE psr (SPSR_READ psr mode)
                  else psr)
           else ARM wb_reg psr;
         out :=
           if L then
             MAP MemRead addr_list
           else
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg) mode' (ZIP (rp_list,addr_list)) |>`;

(* --------------------------------------------------------
   The Single Data Swap instruction class (swp)
   -------------------------------------------------------- *)

val DECODE_SWP_def = Define`
  DECODE_SWP n =
    (BIT 22 n,BITS 19 16 n,BITS 15 12 n,BITS 3 0 n)`;

val SWP_def = Define`
  SWP (ARM reg psr) mode isdabort data n =
    let (B,Rn,Rd,Rm) = DECODE_SWP n in
    let rn = REG_READ reg mode Rn
    and pc_reg = INC_PC reg in
    let rm = REG_READ pc_reg mode Rm in
      <| state :=
           ARM (if isdabort then
                  pc_reg
                else REG_WRITE pc_reg mode Rd (BW_READ B (WORD_BITS 1 0 rn) data))
                psr;
         out := [MemRead rn; MemWrite B rn rm] |>`;

(* --------------------------------------------------------
   Predicate for conditional execution
   -------------------------------------------------------- *)

val CONDITION_PASSED2_def = Define`
  CONDITION_PASSED2 (N,Z,C,V) cond =
    case cond of
       EQ -> Z
    || CS -> C
    || MI -> N
    || VS -> V
    || HI -> C /\ ~Z
    || GE -> N = V
    || GT -> ~Z /\ (N = V)
    || AL -> T`;

val CONDITION_PASSED_def = Define`
  CONDITION_PASSED nzcv n =
    let pass = CONDITION_PASSED2 nzcv (num2condition (BITS 31 29 n)) in
      if BIT 28 n then ~pass else pass`;

(* --------------------------------------------------------
   Top-level decode and execute functions
   -------------------------------------------------------- *)

val DECODE_INST_def = Define`
  DECODE_INST n = 
    if BITS 27 26 n = 0 then
      if BIT 24 n /\ ~BIT 23 n /\ ~BIT 20 n then
        if BIT 25 n \/ ~BIT 4 n then
          mrs_msr
        else
          if ~BIT 21 n /\ (BITS 11 5 n = 4) then swp else cdp_und
      else
        if ~BIT 25 n /\ BIT 4 n then
          if ~BIT 7 n then
            reg_shift
          else
            if ~BIT 24 n /\ (BITS 6 5 n = 0) then mla_mul else cdp_und
        else
          data_proc
    else
      if BITS 27 26 n = 1 then
        if BIT 25 n /\ BIT 4 n then
          cdp_und
        else
          if BIT 20 n then ldr else str
      else
        if BITS 27 26 n = 2 then
          if BIT 25 n then br else
            if BIT 20 n then ldm else stm
        else
          if BIT 25 n /\ BIT 24 n then swi_ex else cdp_und`;

val EXEC_INST_def = Define`
  EXEC_INST (ARM_EX (ARM reg psr) ireg exc) (dabort_t:num option) data =
    if ~(exc = software) then
      EXCEPTION (ARM reg psr) exc
    else
      let n = w2n ireg in
      let ic = DECODE_INST n
      and (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr)
      in
        if ~CONDITION_PASSED nzcv n then
          ARM (INC_PC reg) psr
        else let mode = DECODE_MODE m in
        if (ic = data_proc) \/ (ic = reg_shift) then
          DATA_PROCESSING (ARM reg psr) (CARRY nzcv) mode n
        else if ic = mla_mul then
          MLA_MUL (ARM reg psr) (CARRY nzcv) mode n
        else if ic = br then
          BRANCH (ARM reg psr) mode n
        else if (ic = ldr) \/ (ic = str) then
          (LDR_STR (ARM reg psr) (CARRY nzcv) mode (IS_SOME dabort_t) (HD data) n).state
        else if (ic = ldm) \/ (ic = stm) then
          (LDM_STM (ARM reg psr) mode dabort_t data n).state
        else if ic = swp then
          (SWP (ARM reg psr) mode (IS_SOME dabort_t) (HD data) n).state
        else if ic = swi_ex then
          EXCEPTION (ARM reg psr) software
        else if ic = mrs_msr then
          if BIT 21 n then
            MSR (ARM reg psr) mode n
          else
            MRS (ARM reg psr) mode n
        else (* undef *)
          ARM reg psr`;

(* --------------------------------------------------------
   External exception operations
   -------------------------------------------------------- *)

val IS_Dabort_def = Define`
  IS_Dabort irpt =
    (case irpt of SOME (Dabort x) -> T || _ -> F)`;

val IS_Reset_def = Define`
  IS_Reset irpt =
    (case irpt of SOME (Reset x) -> T || _ -> F)`;

val PROJ_Dabort_def = Define `PROJ_Dabort (SOME (Dabort x)) = x`;
val PROJ_Reset_def  = Define `PROJ_Reset  (SOME (Reset x))  = x`;

val interrupt2exception_def = Define`
  interrupt2exception (cpsr,exc,ireg) irpt =
    let (nzcv,i,f,m) = DECODE_PSR cpsr in
    (case irpt of
        NONE -> if (exc = software) /\
                   CONDITION_PASSED nzcv ireg /\
                   (DECODE_INST ireg = cdp_und) then
                  undefined
                else
                  software
     || SOME (Reset x)  -> reset
     || SOME Prefetch   -> pabort
     || SOME (Dabort t) -> dabort
     || SOME Fiq        -> fast
     || SOME Irq        -> interrupt)`;

val PROJ_TRIPLE_def = Define `
  PROJ_TRIPLE (ARM_EX (ARM reg psr) ireg exc) = (CPSR_READ psr,exc,w2n ireg)`;

(* --------------------------------------------------------
   The next state, output and state functions
   -------------------------------------------------------- *)

val NEXT_ARM_def = Define`
  NEXT_ARM state (irpt,ireg,data) =
    if IS_Reset irpt then
      ARM_EX (PROJ_Reset irpt) ireg reset
    else
      ARM_EX (EXEC_INST state (if IS_Dabort irpt then SOME (PROJ_Dabort irpt) else NONE) data)
             ireg (interrupt2exception (PROJ_TRIPLE state) irpt)`;

val OUT_ARM_def = Define`
  OUT_ARM (ARM_EX (ARM reg psr) ireg exc) =
    let n = w2n ireg in
    let ic = DECODE_INST n
    and (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in
      (if (exc = software) /\ CONDITION_PASSED nzcv n then
         let mode = DECODE_MODE m in
         if (ic = ldr) \/ (ic = str) then
           (LDR_STR (ARM reg psr) (CARRY nzcv) mode ARB ARB n).out
         else if (ic = ldm) \/ (ic = stm) then
           (LDM_STM (ARM reg psr) mode ARB ARB n).out
         else if ic = swp then
           (SWP (ARM reg psr) mode ARB ARB n).out
         else []
       else [])`;

val STATE_ARM_def = Define`
  (STATE_ARM 0 x = x.state) /\
  (STATE_ARM (SUC t) x = NEXT_ARM (STATE_ARM t x) (x.inp t))`;

val ARM_SPEC_def = Define`
  ARM_SPEC t x = let s = STATE_ARM t x in <| state := s; out := OUT_ARM s |>`;

(* --------------------------------------------------------
   Some useful theorems
   -------------------------------------------------------- *)

val STATE_ARM_THM = store_thm("STATE_ARM_THM",
  `IMAP ARM_SPEC I NEXT_ARM OUT_ARM`,
  RW_TAC (std_ss++boolSimps.LET_ss) [ARM_SPEC_def,STATE_ARM_def,IMAP_def,combinTheory.I_THM]
);

val STATE_ARM_THM2 = store_thm("STATE_ARM_THM2",
  `IS_IMAP ARM_SPEC`,
  PROVE_TAC [STATE_ARM_THM,IS_IMAP_def]
);

val STATE_ARM_THM3 = store_thm("STATE_ARM_THM3",
  `IS_IMAP_INIT ARM_SPEC I`,
  PROVE_TAC [STATE_ARM_THM,IS_IMAP_INIT_def]
);

val ARM_SPEC_STATE = save_thm("ARM_SPEC_STATE",
  (SIMP_CONV (srw_ss()++boolSimps.LET_ss) [ARM_SPEC_def]) ``(ARM_SPEC t x).state``
);

(* ........................................................ *)

val SUBST_NE_COMMUTES = store_thm("SUBST_NE_COMMUTES",
  `!m a b d e. ~(a = b) ==> (SUBST (SUBST m b d) a e = SUBST (SUBST m a e) b d)`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN RW_TAC std_ss [SUBST_def]
);

val SUBST_COMMUTES = store_thm("SUBST_COMMUTES",
  `!m (a:num) b d e. a < b ==> (SUBST (SUBST m b d) a e = SUBST (SUBST m a e) b d)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_NOT_EQ
    THEN ASM_SIMP_TAC std_ss [SUBST_NE_COMMUTES]
);

val SUBST_EQ = store_thm("SUBST_EQ",
  `!m a d e. SUBST (SUBST m a d) a e = SUBST m a e`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN RW_TAC std_ss [SUBST_def]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
