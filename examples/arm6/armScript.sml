(* app load ["prim_recTheory","combinTheory","onestepTheory","bitsTheory","word32Theory"]; *)
open HolKernel boolLib Q Parse bossLib prim_recTheory combinTheory
     onestepTheory bitsTheory word32Theory;

(* -------------------------------------------------------- *)

val _ = new_theory "arm";

(* -------------------------------------------------------- *)

val _ = overload_on("w32",``n2w``);

(* -------------------------------------------------------- *)

val _ = Hol_datatype `word30 = w30 of num`;
val _ = Hol_datatype `mode = usr | fiq | irq | svc | abt | und | safe`;
val _ = Hol_datatype `spsr = spsr_fiq | spsr_irq | spsr_svc | spsr_abt | spsr_und`;
val _ = Hol_datatype `reg_usr = w4 of num`;
val _ = Hol_datatype `reg_fiq = r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq |
                                r13_fiq | r14_fiq`;
val _ = Hol_datatype `reg_irq = r13_irq | r14_irq`;
val _ = Hol_datatype `reg_svc = r13_svc | r14_svc`;
val _ = Hol_datatype `reg_abt = r13_abt | r14_abt`;
val _ = Hol_datatype `reg_und = r13_und | r14_und`;
val _ = Hol_datatype `reg = REG of (reg_usr->word32)=>(reg_fiq->word32)=>(reg_irq->word32)=>
                                   (reg_svc->word32)=>(reg_abt->word32)=>(reg_und->word32)`;
val _ = Hol_datatype `psr = PSR of word32=>(spsr->word32)`;
val _ = Hol_datatype `state_ARM = ARM of (word30->word32)=>reg=>psr`;

val _ = Hol_datatype `iclass = swp | mrs_msr | data_proc | reg_shift |
                               ldr | str | br | swi_ex | undef | unexec`;

(* -------------------------------------------------------- *)

val SUBST_def = Define`SUBST m (a,w) b = if (a = b) then w else m b`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val SET_NZC_def = Define`
  SET_NZC N Z C n =
    w32 (SBIT N 31 + SBIT Z 30 + SBIT C 29 + BITSw 28 0 n)`;
 
val SET_NZCV_def = Define`
  SET_NZCV N Z C V n =
    w32 (SBIT N 31 + SBIT Z 30 + SBIT C 29 + SBIT V 28 + BITSw 27 0 n)`;

val SET_MODE_def = Define`
  SET_MODE mode cpsr =
    let m = case mode of
               usr -> 16
            || fiq -> 17
            || irq -> 18
            || svc -> 19
            || abt -> 23
            || und -> 27
            || _ -> 0 in
  w32 (SLICEw 31 5 cpsr + m)`;

val SET_IFMODE_def = Define`
  SET_IFMODE irq' fiq' mode n =
    SET_MODE mode (w32 (SLICEw 31 8 n + SBIT irq' 7 + SBIT fiq' 6 + SLICEw 5 5 n))`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val DECODE_MODE_def = Define`
  DECODE_MODE cpsr =
    let m = BITS 4 0 cpsr in
     if m = 16 then usr else
     if m = 17 then fiq else
     if m = 18 then irq else
     if m = 19 then svc else
     if m = 23 then abt else
     if m = 27 then und else safe`;

val DECODE_PSR_def = Define`
  DECODE_PSR cpsr =
    (BIT 31 cpsr,BIT 30 cpsr,BIT 29 cpsr,BIT 28 cpsr,DECODE_MODE cpsr)`;

val MODE_SPSR_def = Define`
   MODE_SPSR mode =
     case mode of
        fiq -> spsr_fiq
     || irq -> spsr_irq
     || svc -> spsr_svc
     || abt -> spsr_abt
     || und -> spsr_und
     || _   -> ARB`;

val USER_def = Define`
   USER mode = (mode = usr) \/ (mode = safe)`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val CPSR_READ_def = Define`CPSR_READ (PSR cpsr spsrs) = cpsr`;

val CPSR_WRITE_def = Define`
  CPSR_WRITE (PSR cpsr spsrs) cpsr' = PSR cpsr' spsrs`;

val SPSR_READ_def = Define`
  SPSR_READ (PSR cpsr spsrs) mode =
    if USER mode then
      cpsr
    else
      spsrs (MODE_SPSR mode)`;

val SPSR_WRITE_def = Define`
  SPSR_WRITE (PSR cpsr spsrs) mode spsr =
    if USER mode then
      PSR cpsr spsrs
    else
      PSR cpsr (SUBST spsrs (MODE_SPSR mode,spsr))`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val NUM_REG_fiq_def = Define `NUM_REG_fiq n = num2reg_fiq (n - 8)`;
val NUM_REG_irq_def = Define `NUM_REG_irq n = num2reg_irq (n - 13)`;
val NUM_REG_svc_def = Define `NUM_REG_svc n = num2reg_svc (n - 13)`;
val NUM_REG_abt_def = Define `NUM_REG_abt n = num2reg_abt (n - 13)`;
val NUM_REG_und_def = Define `NUM_REG_und n = num2reg_und (n - 13)`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val REG_READ_def = Define`
  REG_READ (REG reg_usr reg_fiq reg_irq reg_svc reg_abt reg_und) mode n =
    if n = 15 then
      reg_usr (w4 15) + w32 8
    else if USER mode \/ (mode = fiq) /\ n < 8 \/ ~(mode = fiq) /\ n < 13 then
      reg_usr (w4 n)
    else
      case mode of
         fiq -> reg_fiq (NUM_REG_fiq n)
      || irq -> reg_irq (NUM_REG_irq n)
      || svc -> reg_svc (NUM_REG_svc n)
      || abt -> reg_abt (NUM_REG_abt n)
      || und -> reg_und (NUM_REG_und n)
      || _ -> ARB`;

val REG_WRITE_def = Define`
  REG_WRITE (REG reg_usr reg_fiq reg_irq reg_svc reg_abt reg_und) mode n d =
    if (n = 15) \/ USER mode \/ (mode = fiq) /\ n < 8 \/ ~(mode = fiq) /\ n < 13 then
      REG (SUBST reg_usr (w4 n,d)) reg_fiq reg_irq reg_svc reg_abt reg_und
    else
      case mode of
         fiq -> REG reg_usr (SUBST reg_fiq (NUM_REG_fiq n,d)) reg_irq reg_svc reg_abt reg_und
      || irq -> REG reg_usr reg_fiq (SUBST reg_irq (NUM_REG_irq n,d)) reg_svc reg_abt reg_und
      || svc -> REG reg_usr reg_fiq reg_irq (SUBST reg_svc (NUM_REG_svc n,d)) reg_abt reg_und
      || abt -> REG reg_usr reg_fiq reg_irq reg_svc (SUBST reg_abt (NUM_REG_abt n,d)) reg_und
      || und -> REG reg_usr reg_fiq reg_irq reg_svc reg_abt (SUBST reg_und (NUM_REG_und n,d))
      || _ -> ARB`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val TO_W30_def = Define`TO_W30 n = w30 (BITSw 31 2 n)`;

val WORD_ALIGN_def = Define`WORD_ALIGN n = w32 (SLICEw 31 2 n)`;

val MEM_READ_WORD_def = Define`
  MEM_READ_WORD mem addr = mem (TO_W30 addr) #>> (8 * BITSw 1 0 addr)`;

val MEM_READ_BYTE_def = Define`
  MEM_READ_BYTE mem addr =
    let align = 8 * BITSw 1 0 addr in
      w32 (BITSw (align+7) align (mem (TO_W30 addr)))`;

val SET_BYTE_def = Define`
  SET_BYTE align byte word =
    if align = 0 then
       w32 (SLICEw 31 8 word + byte)
    else
       w32 (SLICEw 31 (align+8) word + TIMES_2EXP align byte + BITSw (align-1) 0 word)`;

val MEM_WRITE_BYTE_def = Define`
  MEM_WRITE_BYTE mem word addr =
    let addr' = TO_W30 addr in
      SUBST mem (addr',SET_BYTE (8 * BITSw 1 0 addr) (BITSw 7 0 word) (mem addr'))`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD mem word addr = SUBST mem (TO_W30 addr,word)`;

(* Memory read/write never gives an abort error *)
(* Can be adapted to give more realistic MMU behaviour *)

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val INC_PC_def = Define`
  INC_PC (REG reg_usr reg_fiq reg_irq reg_svc reg_abt reg_und) =
    REG (SUBST reg_usr (w4 15,reg_usr (w4 15) + w32 4))
         reg_fiq reg_irq reg_svc reg_abt reg_und`;

val FETCH_PC_def = Define`
  FETCH_PC (REG reg_usr reg_fiq reg_irq reg_svc reg_abt reg_und) = reg_usr (w4 15)`;

(* FETCH_PC needed because (REG_READ reg usr PC) gives PC+8 *)

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val EXCEPTION_def = Define`
  EXCEPTION (ARM mem reg psr) n =
    let cpsr = CPSR_READ psr in
    let fiq' = if (n = 1) \/ (n = 7) then T else BITw 6 cpsr
    and (mode',pc') =
          if n = 1 then (* RESET *)  (svc,w32 0)  else
          if n = 2 then (* UNDEF *)  (und,w32 4)  else
          if n = 3 then (* SWI *)    (svc,w32 8)  else
          if n = 4 then (* PABORT *) (abt,w32 12) else
          if n = 5 then (* DABORT *) (abt,w32 16) else
          if n = 6 then (* IRQ *)    (irq,w32 24) else
          (* n = 7 *)   (* FIQ *)    (fiq,w32 28) in
   let reg' = REG_WRITE reg mode' 14 (FETCH_PC reg + w32 4) in
     ARM mem (REG_WRITE reg' usr 15 pc')
         (CPSR_WRITE (SPSR_WRITE psr mode' cpsr) (SET_IFMODE T fiq' mode' cpsr))`;

(* Note that PC+4 is stored in r14. This is memory address of next instruction,
   accept after data aborts when it is (PC+4)+4 because PC wb occurs prior to call. *)

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val SIGN_EX_OFFSET_def = Define`
  SIGN_EX_OFFSET n =
    if BIT 23 n then
      w32 (2 EXP 32 - 2 EXP 24 + n)
    else
      w32 n`;

val DECODE_BRANCH_def = Define`
  DECODE_BRANCH n = (BIT 24 n,BITS 23 0 n)`;

val BRANCH_def = Define`
  BRANCH (ARM mem reg psr) mode n =
    let (L,offset) = DECODE_BRANCH n
    and pc  = REG_READ reg usr 15 in
    let pc' = pc + SIGN_EX_OFFSET offset << 2 in
    let reg' = REG_WRITE reg usr 15 pc' in
      if L then
        ARM mem (REG_WRITE reg' mode 14 (FETCH_PC reg + w32 4)) psr
      else
        ARM mem reg' psr`;

(* Note, when link is set PC+4=(PC+8)-4 is stored in r14. *)

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val LSL_def = Define`
  LSL m n c = if n = 0 then (c,m)
              else if n <= 32 then
                (BITw (32 - n) m,m << n)
              else
                (F,w32 0)`;

val LSR_def = Define`
  LSR m n c = if n = 0 then
                LSL m 0 c
              else if n <= 32 then
                (BITw (n - 1) m,m >>> n)
              else
                (F,w32 0)`;

val ASR_def = Define`
  ASR m n c = if n = 0 then
                LSL m 0 c
              else if n <= 32 then
                (BITw (n - 1) m,m >> n)
              else
                (MSB m,m >> 32)`;

val ROR_def = Define`
  ROR m n c = if n = 0 then
                LSL m 0 c
              else if n <= 32 then
                (BITw (n - 1) m,m #>> n)
              else let n' = BITS 4 0 n in
                (BITw (n' - 1) m,m #>> n')`;

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
    let shift = BITSw 7 0 (REG_READ reg mode (BITS 11 8 opnd2))
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
      
(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ALU_arith_def = Define`
  ALU_arith op rn op2 =
    let  sign = MSB rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n op2)) in
    let   res = w32 r in
      (MSB res,r = 0,ODD q,
        (MSB op2 = sign) /\ ~(MSB res = sign),res)`;

val ALU_logic_def = Define`
  ALU_logic res = (MSB res,w2n res = 0,F,F,res)`;

val SUB_def = Define`
  SUB a b c = let c' = SBIT c 0 in ALU_arith (\x y.x+y+c'-1) a ~b`;
val ADD_def = Define`
  ADD a b c = let c' = SBIT c 0 in ALU_arith (\x y.x+y+c') a b`;
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

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val ARITHMETIC_def = Define`
  ARITHMETIC opcode = (1 < opcode /\ opcode < 8) \/ (opcode = 10) \/ (opcode = 11)`;

val TEST_OR_COMP_def = Define`
  TEST_OR_COMP opcode = 7 < opcode /\ opcode < 12`;

val DECODE_DATAP_def = Define`
  DECODE_DATAP n =
    (BIT 25 n,BITS 24 21 n,BIT 20 n,BITS 19 16 n,BITS 15 12 n,BITS 11 0 n)`;

val DATA_PROCESSING_def = Define`
  DATA_PROCESSING (ARM mem reg psr) C mode n =
    let (Im,opcode,Sf,Rn,Rd,opnd2) = DECODE_DATAP n in
    let (C_s,op2) = ADDR_MODE1 reg mode C Im opnd2
    and reg' = INC_PC reg in
    let rn = REG_READ (if ~Im /\ (BIT 4 opnd2) then reg' else reg) mode Rn in
    let (N,Z,C',V,res) = ALU opcode rn op2 C in
      ARM mem (if TEST_OR_COMP opcode then reg' else REG_WRITE reg' mode Rd res)
        (if Sf then
           CPSR_WRITE psr
             (if Rd = 15 then SPSR_READ psr mode
                         else if ARITHMETIC opcode
                                 then SET_NZCV N Z C' V (CPSR_READ psr)
                                 else SET_NZC  N Z C_s (CPSR_READ psr))
         else psr)`;

(* Gives PC+12 behaviour, in case of shift by register *)

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val DECODE_MRS_def = Define`
  DECODE_MRS n = (BIT 22 n,BITS 15 12 n)`;

val MRS_def = Define`
  MRS (ARM mem reg psr) mode n =
    let (R,Rd) = DECODE_MRS n in
    let word = if R then SPSR_READ psr mode else CPSR_READ psr in
      ARM mem (REG_WRITE (INC_PC reg) mode Rd word) psr`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val SPLIT_WORD_def = Define`
  SPLIT_WORD a = (BITSw 31 28 a,BITSw 27 8 a,BITSw 7 0 a)`;

val CONCAT_BYTES_def = Define`
  CONCAT_BYTES a b c = w32 (TIMES_2EXP 28 a + TIMES_2EXP 8 b + c)`;

val DECODE_MSR_def = Define`
  DECODE_MSR n = (BIT 25 n,BIT 22 n,BIT 19 n,BIT 16 n,BITS 3 0 n,BITS 11 0 n)`;

val MSR_def = Define`
  MSR (ARM mem reg psr) mode n =
    let (Im,R,bit19,bit16,Rm,opnd) = DECODE_MSR n in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      ARM mem (INC_PC reg) psr
    else
      let xpsr = if R then SPSR_READ psr mode else CPSR_READ psr
      and  src = if Im then SND (IMMEDIATE F opnd) else REG_READ reg mode Rm in
      let (x2,x1,x0) = SPLIT_WORD xpsr
      and (s2,s1,s0) = SPLIT_WORD src in
      let xpsr' = CONCAT_BYTES (if bit19 then s2 else x2) x1
                               (if bit16 /\ ~(USER mode) then s0 else x0) in
        ARM mem (INC_PC reg)
         (if R then SPSR_WRITE psr mode xpsr' else CPSR_WRITE psr xpsr')`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val UP_DOWN_def = Define`
  (UP_DOWN T addr offset = addr + offset) /\
  (UP_DOWN F addr offset = addr - offset)`;

val ADDR_MODE2_def = Define`
  ADDR_MODE2 reg mode C Im P U Rn offset =
    let addr  = REG_READ reg mode Rn in
    let addr' = UP_DOWN U addr (if Im then SND (SHIFT_IMMEDIATE reg mode C offset)
                                      else w32 offset) in
      (if P then addr' else addr,addr')`;

val DECODE_LDR_STR_def = Define`
  DECODE_LDR_STR n =
     (BIT 25 n,BIT 24 n,BIT 23 n,BIT 22 n,BIT 21 n,BIT 20 n,
      BITS 19 16 n,BITS 15 12 n,BITS 11 0 n)`;

val PIPE_OKAY_def = Define`
  PIPE_OKAY addr pc =
     let aaddr = WORD_ALIGN addr in
       ~((aaddr = WORD_ALIGN (pc + w32 4)) \/
         (aaddr = WORD_ALIGN (pc + w32 8)))`;

val LDR_STR_def = Define`
  LDR_STR (ARM mem reg psr) C mode n =
    let (Im,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in
    let (addr,addr') = ADDR_MODE2 reg mode C Im P U Rn offset in
    let reg' = INC_PC reg in
    let wb_reg = if W \/ ~P then REG_WRITE reg' mode Rn addr' else reg' in
    if L then (* LDR *)
      if (Rn = 15) /\ (W \/ ~P) then
        ARM mem (INC_PC wb_reg) psr
      else
        let data = if B then MEM_READ_BYTE mem addr else MEM_READ_WORD mem addr in
          ARM mem (REG_WRITE wb_reg mode Rd data) psr
    else (* STR *)
      let rd = REG_READ reg' mode Rd in
      let mem' = if (Rn = 15) /\ (W \/ ~P) \/ PIPE_OKAY addr (FETCH_PC reg) then
                    if B then MEM_WRITE_BYTE mem rd addr else MEM_WRITE_WORD mem rd addr
                 else mem in
        ARM mem' wb_reg psr`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val DECODE_SWP_def = Define`
  DECODE_SWP n =
    (BIT 22 n,BITS 19 16 n,BITS 15 12 n,BITS 3 0 n)`;

val SWP_def = Define`
  SWP (ARM mem reg psr) mode n =
    let (B,Rn,Rd,Rm) = DECODE_SWP n in
    let rn = REG_READ reg mode Rn
    and reg' = INC_PC reg in
    let (MEM_READ,MEM_WRITE) = if B then (MEM_READ_BYTE,MEM_WRITE_BYTE)
                                    else (MEM_READ_WORD,MEM_WRITE_WORD)
    and rm = REG_READ reg' mode Rm in
    let word = MEM_READ mem rn
    and mem' = if PIPE_OKAY rn (FETCH_PC reg) then
                 MEM_WRITE mem rm rn
               else
                 mem in
      ARM mem' (REG_WRITE reg' mode Rd word) psr`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val SWI_def = Define`
  SWI (ARM mem reg psr) = EXCEPTION (ARM mem reg psr) 3`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val CONDITION_PASSED_def = Define`
  CONDITION_PASSED N Z C V cond =
    if      cond = 0  (* EQ *) then Z
    else if cond = 1  (* NE *) then ~Z
    else if cond = 2  (* CS *) then C
    else if cond = 3  (* CC *) then ~C
    else if cond = 4  (* MI *) then N
    else if cond = 5  (* PL *) then ~N
    else if cond = 6  (* VS *) then V
    else if cond = 7  (* VC *) then ~V
    else if cond = 8  (* HI *) then C /\ ~Z
    else if cond = 9  (* LS *) then ~C \/ Z
    else if cond = 10 (* GE *) then N = V
    else if cond = 11 (* LT *) then ~(N = V)
    else if cond = 12 (* GT *) then ~Z /\ (N = V)
    else if cond = 13 (* LE *) then Z \/ ~(N = V)
    else if cond = 14 (* AL *) then T
    else F`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val DECODE_INST_def = Define`
  DECODE_INST n = 
    if BITS 27 26 n = 0 then
      if BIT 24 n /\ ~BIT 23 n /\ ~BIT 20 n then
        if BIT 25 n \/ ~BIT 4 n then
          mrs_msr
        else
          if ~BIT 21 n /\ (BITS 11 5 n = 4) then swp else undef
      else
        if BIT 25 n \/ ~BIT 4 n then
          data_proc
        else
          if ~BIT 25 n /\ ~BIT 7 n /\ BIT 4 n then
            reg_shift
          else
            undef
    else
      if BITS 27 26 n = 1 then
        if BIT 25 n /\ BIT 4 n then
          undef
        else
          if BIT 20 n then ldr else str
      else
        if BITS 27 26 n = 2 then
          if BIT 25 n then br else undef
        else
          if BIT 25 n /\ BIT 24 n then swi_ex else undef`;

val NEXT_ARM_def = Define`
  NEXT_ARM (ARM mem reg psr) =
    let n = w2n (MEM_READ_WORD mem (WORD_ALIGN (FETCH_PC reg))) in
    let ic = DECODE_INST n
    and (N,Z,C,V,mode) = DECODE_PSR (w2n (CPSR_READ psr)) in
      if ~(CONDITION_PASSED N Z C V (BITS 31 28 n)) then
        ARM mem (INC_PC reg) psr
      else if ic = mrs_msr then
        if BIT 21 n then
          MSR (ARM mem reg psr) mode n
        else
          MRS (ARM mem reg psr) mode n
      else if (ic = data_proc) \/ (ic = reg_shift) then
        DATA_PROCESSING (ARM mem reg psr) C mode n
      else if (ic = ldr) \/ (ic = str) then
        LDR_STR (ARM mem reg psr) C mode n
      else if ic = swp then
        SWP (ARM mem reg psr) mode n
      else if ic = br then
        BRANCH (ARM mem reg psr) mode n
      else if ic = swi_ex then
        SWI (ARM mem reg psr)
      else
        EXCEPTION (ARM mem reg psr) 2`;

val STATE_ARM_def = Define`
  (STATE_ARM 0 a = a) /\
  (STATE_ARM (SUC t) a = NEXT_ARM (STATE_ARM t a))`;

val STATE_ARM_THM = store_thm("STATE_ARM_THM",
  `IMAP STATE_ARM I NEXT_ARM`,
  PROVE_TAC [STATE_ARM_def,IMAP_def,I_THM]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val SUBST_NE_COMMUTES = store_thm("SUBST_NE_COMMUTES",
  `!m a b d e. ~(a = b) ==> (SUBST (SUBST m (b,d)) (a,e) = SUBST (SUBST m (a,e)) (b,d))`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN RW_TAC std_ss [SUBST_def]
);

val SUBST_COMMUTES = store_thm("SUBST_COMMUTES",
  `!m a b d e. a < b ==> (SUBST (SUBST m (b,d)) (a,e) = SUBST (SUBST m (a,e)) (b,d))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_NOT_EQ
    THEN ASM_SIMP_TAC std_ss [SUBST_NE_COMMUTES]
);

val SUBST_EQ = store_thm("SUBST_EQ",
  `!m a d e. SUBST (SUBST m (a,d)) (a,e) = SUBST m (a,e)`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN RW_TAC std_ss [SUBST_def]
);

val STATE_ARM_COR = store_thm("STATE_ARM_COR",
  `!t a. STATE_ARM t a = if t = 0 then a else NEXT_ARM (STATE_ARM (t-1) a)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC STATE_ARM_THM
    THEN IMP_RES_TAC IMAP_COMP
    THEN POP_ASSUM (fn th =>
           GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [th])
    THEN REWRITE_TAC [I_THM]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
