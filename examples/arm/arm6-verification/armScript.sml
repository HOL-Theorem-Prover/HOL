(* ========================================================================= *)
(* FILE          : armScript.sml                                             *)
(* DESCRIPTION   : Model of the ARM instruction set architecture (v4)        *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "rich_listTheory", "io_onestepTheory"];
*)
Theory arm
Ancestors
  rich_list io_onestep words
Libs
  Q wordsLib wordsSyntax


(* ------------------------------------------------------------------------- *)
(*  The ARM State Space                                                      *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "%%" (Infixl 500);
val _ = overload_on ("%%", Term`$fcp_index`);

Datatype: register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und
End
Datatype:
  psrs = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
End

val _ = type_abbrev("reg", ``:register->word32``);
val _ = type_abbrev("psr", ``:psrs->word32``);

Datatype:
  exception = reset | undefined | software | pabort |
              dabort | address |interrupt | fast
End

Datatype: state_arm = ARM of reg=>psr
End
Datatype: state_arm_ex = ARM_EX of state_arm=>word32=>exception
End

(* ......................................................................... *)

Datatype:
  memop = MemRead of word32 | MemWrite of bool=>word32=>word32 |
          CPMemRead of bool=>word32 | CPMemWrite of bool=>word32 |
          CPWrite of word32
End

Datatype:
  interrupts = Reset of state_arm | Undef | Prefetch |
               Dabort of num | Fiq | Irq
End

Datatype: mode = usr | fiq | irq | svc | abt | und | safe
End

Datatype:
  condition  = EQ | CS | MI | VS | HI | GE | GT | AL |
               NE | CC | PL | VC | LS | LT | LE | NV
End

Datatype:
  iclass = swp | mrs_msr | data_proc | reg_shift | mla_mul |
           ldr | str | ldm | stm | br | swi_ex | cdp_und |
           mcr | mrc | ldc | stc | unexec
End

(* ------------------------------------------------------------------------- *)
(*  General Purpose Register operations                                      *)
(* ------------------------------------------------------------------------- *)

val Rg = inst [alpha |-> ``:32``, beta |-> ``:4``] word_extract_tm;

Definition USER_def:   USER mode <=> (mode = usr) \/ (mode = safe)
End

Definition mode_reg2num_def:
  mode_reg2num m (w:word4) = let n = w2n w in
    (if (n = 15) \/ USER m \/ (m = fiq) /\ n < 8 \/ ~(m = fiq) /\ n < 13 then
       n
     else case m of
       fiq => n + 8
     | irq => n + 10
     | svc => n + 12
     | abt => n + 14
     | und => n + 16
     | _ => ARB)
End

Definition REG_READ_def:
  REG_READ (reg:reg) m n =
    if n = 15w then
      reg r15 + 8w
    else
      reg (num2register (mode_reg2num m n))
End

Definition REG_WRITE_def:
  REG_WRITE (reg:reg) m n d =
    (num2register (mode_reg2num m n) =+ d) reg
End

Definition INC_PC_def:     INC_PC (reg:reg) = (r15 =+ reg r15 + 4w) reg
End
Definition FETCH_PC_def:   FETCH_PC (reg:reg) = reg r15
End

(*  FETCH_PC is needed because (REG_READ reg usr 15w) gives PC + 8.          *)

(* ------------------------------------------------------------------------- *)
(*  Program Status Register operations                                       *)
(* ------------------------------------------------------------------------- *)

Definition SET_NZCV_def:
  SET_NZCV (N,Z,C,V) w:word32 =
    word_modify (\i b. (i = 31) /\ N \/ (i = 30) /\ Z \/
                       (i = 29) /\ C \/ (i = 28) /\ V \/
                       (i < 28) /\ b) w
End

Definition SET_NZC_def:   SET_NZC (N,Z,C) w = SET_NZCV (N,Z,C,w %% 28) w
End

Definition mode_num_def:
  mode_num mode =
    case mode of
      usr => 16w
    | fiq => 17w
    | irq => 18w
    | svc => 19w
    | abt => 23w
    | und => 27w
    | _ => 0w:word5
End

Definition SET_IFMODE_def:
  SET_IFMODE irq' fiq' mode w:word32 =
     word_modify (\i b. (7 < i \/ (i = 5)) /\ b \/
                        (i = 7) /\ irq' \/ (i = 6) /\ fiq' \/
                        (i < 5) /\ (mode_num mode) %% i) w
End

Definition DECODE_MODE_def:
  DECODE_MODE (m:word5) =
    if m = 16w then usr else
    if m = 17w then fiq else
    if m = 18w then irq else
    if m = 19w then svc else
    if m = 23w then abt else
    if m = 27w then und else safe
End

Definition NZCV_def:   NZCV (w:word32) = (w %% 31, w %% 30, w %% 29, w %% 28)
End

Definition DECODE_PSR_def:
  DECODE_PSR (cpsr:word32) =
    (NZCV cpsr, cpsr %% 7, cpsr %% 6, ((4 >< 0) cpsr):word5)
End

Definition CARRY_def:   CARRY (n,z,c,v) = c
End

Definition mode2psr_def:
  mode2psr mode =
    case mode of
      usr => CPSR
    | fiq => SPSR_fiq
    | irq => SPSR_irq
    | svc => SPSR_svc
    | abt => SPSR_abt
    | und => SPSR_und
    | _   => CPSR
End

Definition SPSR_READ_def:   SPSR_READ (psr:psr) mode = psr (mode2psr mode)
End
Definition CPSR_READ_def:   CPSR_READ (psr:psr) = psr CPSR
End

Definition CPSR_WRITE_def:
  CPSR_WRITE (psr:psr) cpsr = (CPSR =+ cpsr) psr
End

Definition SPSR_WRITE_def:
  SPSR_WRITE (psr:psr) mode spsr =
    if USER mode then psr else (mode2psr mode =+ spsr) psr
End

(* ------------------------------------------------------------------------- *)
(* The Sofware Interrupt/Exception instruction class (swi_ex)                *)
(* ------------------------------------------------------------------------- *)

Definition exception2mode_def:
  exception2mode e =
    case e of
      reset     => svc
    | undefined => und
    | software  => svc
    | address   => svc
    | pabort    => abt
    | dabort    => abt
    | interrupt => irq
    | fast      => fiq
End

Definition EXCEPTION_def:
  EXCEPTION (ARM reg psr) type =
    let cpsr = CPSR_READ psr in
    let fiq' = (((type = reset) \/ (type = fast)) \/ cpsr %% 6)
    and mode' = exception2mode type
    and pc = n2w (4 * exception2num type):word32 in
    let reg' = REG_WRITE reg mode' 14w (FETCH_PC reg + 4w) in
      ARM (REG_WRITE reg' usr 15w pc)
         (CPSR_WRITE (SPSR_WRITE psr mode' cpsr)
            (SET_IFMODE T fiq' mode' cpsr))
End

(* ------------------------------------------------------------------------- *)
(* The Branch instruction class (br)                                         *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_BRANCH_def:
  DECODE_BRANCH (w:word32) = (w %% 24, ((23 >< 0) w):word24)
End

Definition BRANCH_def:
  BRANCH (ARM reg psr) mode ireg =
    let (L,offset) = DECODE_BRANCH ireg
    and pc = REG_READ reg usr 15w in
    let br_addr = pc + sw2sw offset << 2 in
    let pc_reg = REG_WRITE reg usr 15w br_addr in
      ARM (if L then
             REG_WRITE pc_reg mode 14w (FETCH_PC reg + 4w)
           else
             pc_reg) psr
End

(* ------------------------------------------------------------------------- *)
(* The Data Processing instruction class (data_proc, reg_shift)              *)
(* ------------------------------------------------------------------------- *)

Definition LSL_def:
  LSL (m:word32) (n:word8) c =
    if n = 0w then (c, m) else
      (n <=+ 32w /\ m %% (32 - w2n n), m << w2n n)
End

Definition LSR_def:
  LSR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (n <=+ 32w /\ m %% (w2n n - 1), m >>> w2n n)
End

Definition ASR_def:
  ASR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m %% MIN 31 (w2n n - 1), m >> w2n n)
End

Definition ROR_def:
  ROR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m %% (w2n ((w2w n):word5) - 1), m #>> w2n n)
End

Definition IMMEDIATE_def:
  IMMEDIATE C (opnd2:word12) =
    let rot = (11 >< 8) opnd2
    and imm = (7 >< 0) opnd2
    in
      ROR imm (2w * rot) C
End

Definition SHIFT_IMMEDIATE2_def:
  SHIFT_IMMEDIATE2 shift (sh:word2) rm c =
    if shift = 0w then
      if sh = 0w then LSL rm 0w c  else
      if sh = 1w then LSR rm 32w c else
      if sh = 2w then ASR rm 32w c else
      (* sh = 3w *)   word_rrx (c,rm)
    else
      if sh = 0w then LSL rm shift c else
      if sh = 1w then LSR rm shift c else
      if sh = 2w then ASR rm shift c else
      (* sh = 3w *)   ROR rm shift c
End

Definition SHIFT_REGISTER2_def:
  SHIFT_REGISTER2 shift (sh:word2) rm c =
      if sh = 0w then LSL rm shift c else
      if sh = 1w then LSR rm shift c else
      if sh = 2w then ASR rm shift c else
      (* sh = 3w *)   ROR rm shift c
End

Definition SHIFT_IMMEDIATE_def:
  SHIFT_IMMEDIATE reg mode C (opnd2:word12) =
    let Rm = (3 >< 0) opnd2 in
    let rm = REG_READ reg mode Rm
    and sh = (6 >< 5) opnd2
    and shift = (11 >< 7) opnd2
    in
      SHIFT_IMMEDIATE2 shift sh rm C
End

Definition SHIFT_REGISTER_def:
  SHIFT_REGISTER reg mode C (opnd2:word12) =
    let Rs = (11 >< 8) opnd2
    and Rm = (3 >< 0) opnd2 in
    let sh = (6 >< 5) opnd2
    and rm = REG_READ (INC_PC reg) mode Rm
    and shift = (7 >< 0) (REG_READ reg mode Rs) in
      SHIFT_REGISTER2 shift sh rm C
End

Definition ADDR_MODE1_def:
  ADDR_MODE1 reg mode C Im opnd2 =
    if Im then
      IMMEDIATE C opnd2
    else if opnd2 %% 4 then
      SHIFT_REGISTER reg mode C opnd2
    else
      SHIFT_IMMEDIATE reg mode C opnd2
End

(* ......................................................................... *)

Definition ALU_arith_def:
  ALU_arith op (rn:word32) (op2:word32) =
    let sign  = word_msb rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n op2)) in
    let res   = (n2w r):word32 in
      ((word_msb res,r = 0,ODD q,
        (word_msb op2 = sign) /\ ~(word_msb res = sign)),res)
End

Definition ALU_logic_def:
  ALU_logic (res:word32) = ((word_msb res,res = 0w,F,F),res)
End

Definition ADD_def:
  ADD a b c = ALU_arith (\x y.x+y+(if c then 1 else 0)) a b
End

Definition SUB_def:  SUB a b c = ADD a (~b) c
End
Definition AND_def:  AND a b = ALU_logic (a && b)
End
Definition EOR_def:  EOR a b = ALU_logic (a ?? b)
End
Definition ORR_def:  ORR a b = ALU_logic (a || b)
End

Definition ALU_def:
 ALU (opc:word4) rn op2 c =
   if (opc = 0w) \/ (opc = 8w)  then AND rn op2   else
   if (opc = 1w) \/ (opc = 9w)  then EOR rn op2   else
   if (opc = 2w) \/ (opc = 10w) then SUB rn op2 T else
   if (opc = 4w) \/ (opc = 11w) then ADD rn op2 F else
   if opc = 3w  then SUB op2 rn T                 else
   if opc = 5w  then ADD rn op2 c                 else
   if opc = 6w  then SUB rn op2 c                 else
   if opc = 7w  then SUB op2 rn c                 else
   if opc = 12w then ORR rn op2                   else
   if opc = 13w then ALU_logic op2                else
   if opc = 14w then AND rn (~op2)                else
   (* opc = 15w *)   ALU_logic (~op2)
End

(* ......................................................................... *)

Definition ARITHMETIC_def:
  ARITHMETIC (opcode:word4) <=>
    (opcode %% 2 \/ opcode %% 1) /\ (~(opcode %% 3) \/ ~(opcode %% 2))
End

Definition TEST_OR_COMP_def:
  TEST_OR_COMP (opcode:word4) = ((3 -- 2 ) opcode = 2w)
End

Definition DECODE_DATAP_def:
  DECODE_DATAP w =
    (w %% 25,^Rg 24 21 w,w %% 20,^Rg 19 16 w,^Rg 15 12 w,
     ((11 >< 0) w):word12)
End

Definition DATA_PROCESSING_def:
  DATA_PROCESSING (ARM reg psr) C mode ireg =
    let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP ireg in
    let (C_s,op2) = ADDR_MODE1 reg mode C I opnd2
    and pc_reg = INC_PC reg in
    let rn = REG_READ (if ~I /\ (opnd2 %% 4) then pc_reg else reg) mode Rn in
    let ((N,Z,C_alu,V),res) = ALU opcode rn op2 C
    and tc = TEST_OR_COMP opcode in
      ARM (if tc then pc_reg else REG_WRITE pc_reg mode Rd res)
        (if S then
           CPSR_WRITE psr
             (if (Rd = 15w) /\ ~tc then SPSR_READ psr mode
                         else (if ARITHMETIC opcode
                                 then SET_NZCV (N,Z,C_alu,V)
                                 else SET_NZC  (N,Z,C_s)) (CPSR_READ psr))
         else psr)
End

(* ------------------------------------------------------------------------- *)
(* The PSR Transfer instruction class (mrs_msr)                              *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_MRS_def:   DECODE_MRS w = (w %% 22,^Rg 15 12 w)
End

Definition MRS_def:
  MRS (ARM reg psr) mode ireg =
    let (R,Rd) = DECODE_MRS ireg in
    let word = if R then SPSR_READ psr mode else CPSR_READ psr in
      ARM (REG_WRITE (INC_PC reg) mode Rd word) psr
End

(* ......................................................................... *)

Definition DECODE_MSR_def:
  DECODE_MSR w =
    (w %% 25,w %% 22,w %% 19,w %% 16,^Rg 3 0 w,((11 >< 0) w):word12)
End

Definition MSR_def:
  MSR (ARM reg psr) mode ireg =
    let (I,R,bit19,bit16,Rm,opnd) = DECODE_MSR ireg in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      ARM (INC_PC reg) psr
    else
      let psrd = if R then SPSR_READ psr mode else CPSR_READ psr
      and  src = if I then SND (IMMEDIATE F opnd) else REG_READ reg mode Rm in
      let psrd' = word_modify
             (\i b. (28 <= i) /\ (if bit19 then src %% i else b) \/
                    (8 <= i) /\ (i <= 27) /\ b \/
                    (i <= 7) /\ (if bit16 /\ ~USER mode then src %% i else b))
             psrd
      in
        ARM (INC_PC reg)
         (if R then SPSR_WRITE psr mode psrd' else CPSR_WRITE psr psrd')
End

(* ------------------------------------------------------------------------- *)
(* The Multiply (and Accumulate) instruction class (mla_mul)                 *)
(* ------------------------------------------------------------------------- *)

Definition BORROW2_def:
  BORROW2 (rs:word32) n <=> ~(n = 0) /\ rs %% (2 * n - 1)
End

Definition MSHIFT2_def:
  MSHIFT2 borrow (mul:word2) (shift:word4) =
    w2w shift * (2w:word5) +
      if borrow /\ (mul = 1w) \/ ~borrow /\ (mul = 2w) then
        1w
      else
        0w
End

Definition MLA_MUL_DONE_def:
  MLA_MUL_DONE rs n <=>
    ~(n = 0) /\ ((31 -- (2 * n)) rs = 0w) /\ ~BORROW2 rs n \/ ~(2 * n < 32)
End

Definition MLA_MUL_DUR_def:   MLA_MUL_DUR rs = LEAST n. MLA_MUL_DONE rs n
End

Definition MLA_MUL_CARRY_def:
  MLA_MUL_CARRY rm rs C = let n = MLA_MUL_DUR rs - 1 in
    FST (LSL rm
      (w2w (MSHIFT2 (BORROW2 rs n) (((1 >< 0) ((31 -- (2 * n)) rs)))
         (n2w n))) C)
End

Definition ALU_multiply_def:
  ALU_multiply A (rm:word32) rs rn C =
    let res = if A then rm * rs + rn else rm * rs in
      (word_msb res,res = 0w,MLA_MUL_CARRY rm rs C,res)
End

Definition DECODE_MLA_MUL_def:
  DECODE_MLA_MUL w =
    (w %% 21,w %% 20,^Rg 19 16 w,^Rg 15 12 w,^Rg 11 8 w,^Rg 3 0 w)
End

Definition MLA_MUL_def:
  MLA_MUL (ARM reg psr) C mode ireg =
    let (A,S,Rd,Rn,Rs,Rm) = DECODE_MLA_MUL ireg in
    let pc_reg = INC_PC reg in
    let rn = REG_READ reg mode Rn
    and rs = REG_READ reg mode Rs
    and rm = REG_READ pc_reg mode Rm in
    let (N,Z,C_s,res) = ALU_multiply A rm rs rn C in
      if (Rd = 15w) \/ (Rd = Rm) then
        ARM pc_reg psr
      else
        ARM (REG_WRITE pc_reg mode Rd res)
          (if S then CPSR_WRITE psr (SET_NZC (N,Z,C_s) (CPSR_READ psr))
                else psr)
End

(* ------------------------------------------------------------------------- *)
(* The Single Data Transfer instruction class (ldr, str)                     *)
(* ------------------------------------------------------------------------- *)

Definition BW_READ_def:
  BW_READ B (align:word2) (data:word32) =
    let l = 8 * w2n align in
      if B then ((l + 7) -- l) data else data #>> l
End

Definition UP_DOWN_def:  UP_DOWN u = if u then $word_add else $word_sub
End

Definition ADDR_MODE2_def:
  ADDR_MODE2 reg mode C Im P U Rn offset =
    let addr  = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then SND (SHIFT_IMMEDIATE reg mode C offset)
                 else w2w offset) in
      (if P then wb_addr else addr,wb_addr)
End

Definition DECODE_LDR_STR_def:
  DECODE_LDR_STR w =
     (w %% 25,w %% 24,w %% 23,w %% 22,w %% 21,w %% 20,
      ^Rg 19 16 w,^Rg 15 12 w,((11 >< 0) w):word12)
End

Definition LDR_STR_def:
  LDR_STR (ARM reg psr) C mode isdabort data ireg =
    let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
    let (addr,wb_addr) = ADDR_MODE2 reg mode C I P U Rn offset in
    let pc_reg = INC_PC reg in
    let wb_reg = if P ==> W then
                   REG_WRITE pc_reg mode Rn wb_addr
                 else
                   pc_reg
    in
      <| state :=
           ARM (if L ==> isdabort then
                  wb_reg
                else
                  REG_WRITE wb_reg mode Rd (BW_READ B ((1 >< 0) addr) data))
               psr;
         out :=
           [if L then
              MemRead addr
            else
              MemWrite B addr (REG_READ pc_reg mode Rd)] |>
End

(* ------------------------------------------------------------------------- *)
(*  The Block Data Transfer instruction class (ldm, stm)                     *)
(* ------------------------------------------------------------------------- *)

Definition REGISTER_LIST_def:
  REGISTER_LIST (list:word16) =
    (MAP SND o FILTER FST) (GENLIST (\i. (list %% i,(n2w i):word4)) 16)
End

Definition ADDRESS_LIST_def:
  ADDRESS_LIST (start:word32) n = GENLIST (\i. start + 4w * n2w i) n
End

Definition WB_ADDRESS_def:
  WB_ADDRESS U base len = UP_DOWN U base (n2w (4 * len):word32)
End

Definition FIRST_ADDRESS_def:
  FIRST_ADDRESS P U (base:word32) wb =
    if U then if P then base + 4w else base
         else if P then wb else wb + 4w
End

Definition ADDR_MODE4_def:
  ADDR_MODE4 P U base (list:word16) =
    let rp_list = REGISTER_LIST list in
    let len = LENGTH rp_list in
    let wb = WB_ADDRESS U base len in
    let addr_list = ADDRESS_LIST (FIRST_ADDRESS P U base wb) len in
      (rp_list,addr_list,wb)
End

Definition LDM_LIST_def:
  LDM_LIST reg mode rp_list data =
    FOLDL (\reg' (rp,rd). REG_WRITE reg' mode rp rd) reg (ZIP (rp_list,data))
End

Definition STM_LIST_def:
  STM_LIST reg mode bl_list =
    MAP (\(rp,addr). MemWrite F addr (REG_READ reg mode rp)) bl_list
End

Definition DECODE_LDM_STM_def:
  DECODE_LDM_STM w =
    (w %% 24,w %% 23,w %% 22,w %% 21,w %% 20,^Rg 19 16 w,((15 >< 0) w):word16)
End

Definition LDM_STM_def:
  LDM_STM (ARM reg psr) mode dabort_t data ireg =
    let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
    let pc_in_list = list %% 15
    and rn = REG_READ reg mode Rn in
    let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list
    and mode' = if S /\ (L ==> ~pc_in_list) then usr else mode
    and pc_reg = INC_PC reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg (if L then mode else mode') Rn rn'
                 else
                   pc_reg
    in
      <| state :=
           if L then
             ARM (let t = if IS_SOME dabort_t then
                            THE dabort_t
                          else
                            LENGTH rp_list in
                  let ldm_reg = LDM_LIST wb_reg mode' (FIRSTN t rp_list)
                                  (FIRSTN t data) in
                    if IS_SOME dabort_t /\ ~(Rn = 15w) then
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
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg) mode'
               (ZIP (rp_list,addr_list)) |>
End

(* ------------------------------------------------------------------------- *)
(* The Single Data Swap instruction class (swp)                              *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_SWP_def:
  DECODE_SWP w = (w %% 22,^Rg 19 16 w,^Rg 15 12 w,^Rg 3 0 w)
End

Definition SWP_def:
  SWP (ARM reg psr) mode isdabort data ireg =
    let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
    let rn = REG_READ reg mode Rn
    and pc_reg = INC_PC reg in
    let rm = REG_READ pc_reg mode Rm in
      <| state :=
           ARM (if isdabort then
                  pc_reg
                else
                  REG_WRITE pc_reg mode Rd (BW_READ B ((1 ><  0) rn) data))
                psr;
         out := [MemRead rn; MemWrite B rn rm] |>
End

(* ------------------------------------------------------------------------- *)
(* Coprocessor Register Transfer (mrc, mcr)                                  *)
(* ------------------------------------------------------------------------- *)

Definition MRC_def:
  MRC (ARM reg psr) mode data ireg =
    let Rd = ^Rg 15 12 ireg
    and pc_reg = INC_PC reg in
      if Rd = 15w then
        ARM pc_reg (CPSR_WRITE psr (SET_NZCV (NZCV data) (CPSR_READ psr)))
      else
        ARM (REG_WRITE pc_reg mode Rd data) psr
End

Definition MCR_OUT_def:
  MCR_OUT (ARM reg psr) mode ireg =
    let Rn = ^Rg 15 12 ireg in
      [CPWrite (REG_READ (INC_PC reg) mode Rn)]
End

(* ------------------------------------------------------------------------- *)
(* Coprocessor Data Transfers (ldc, stc)                                     *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_LDC_STC_def:
  DECODE_LDC_STC w =
    (w %% 24,w %% 23,w %% 21,w %% 20,^Rg 19 16 w,((7 >< 0) w):word8)
End

Definition ADDR_MODE5_def:
  ADDR_MODE5 reg mode P U Rn (offset:word8) =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr (w2w offset << 2) in
      (if P then wb_addr else addr,wb_addr)
End

Definition LDC_STC_def:
  LDC_STC (ARM reg psr) mode ireg =
    let (P,U,W,L,Rn,offset) = DECODE_LDC_STC ireg in
    let (addr,wb_addr) = ADDR_MODE5 reg mode P U Rn offset in
    let pc_reg = INC_PC reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg mode Rn wb_addr
                 else
                   pc_reg in
      <| state := ARM wb_reg psr;
         out := [(if L then CPMemRead else CPMemWrite) U addr] |>
End

(* ------------------------------------------------------------------------- *)
(* Predicate for conditional execution                                       *)
(* ------------------------------------------------------------------------- *)

Definition CONDITION_PASSED2_def:
  CONDITION_PASSED2 (N,Z,C,V) cond =
    case cond of
      EQ => Z
    | CS => C
    | MI => N
    | VS => V
    | HI => C /\ ~Z
    | GE => N = V
    | GT => ~Z /\ (N = V)
    | AL => T
End

Definition CONDITION_PASSED_def:
  CONDITION_PASSED flags (ireg:word32) =
    let pass = CONDITION_PASSED2 flags (num2condition (w2n ((31 -- 29) ireg)))
    in
      if ireg %% 28 then ~pass else pass
End

(* ------------------------------------------------------------------------- *)
(* Top-level decode and execute functions                                    *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_INST_def:
  DECODE_INST (ireg:word32) =
    if (27 -- 26) ireg = 0w then
      if ireg %% 24 /\ ~(ireg %% 23) /\ ~(ireg %% 20) then
        if ireg %% 25 \/ ~(ireg %% 4) then
          mrs_msr
        else
          if ~(ireg %% 21) /\ ((11 -- 5) ireg = 4w) then swp else cdp_und
      else
        if ~(ireg %% 25) /\ ireg %% 4 then
          if ~(ireg %% 7) then
            reg_shift
          else
            if ~(ireg %% 24) /\ ((6 -- 5) ireg = 0w) then mla_mul else cdp_und
        else
          data_proc
    else
      if (27 -- 26) ireg = 1w then
        if ireg %% 25 /\ ireg %% 4 then
          cdp_und
        else
          if ireg %% 20 then ldr else str
      else
        if (27 -- 26) ireg = 2w then
          if ireg %% 25 then br else
            if ireg %% 20 then ldm else stm
        else (* 27 -- 26 = 3w *)
          if ireg %% 25 then
            if ireg %% 24 then swi_ex else
              if ireg %% 4 then
                if ireg %% 20 then mrc else mcr
              else
                cdp_und
          else
            if ireg %% 20 then
              ldc
            else
              stc
End

Definition EXEC_INST_def:
  EXEC_INST (ARM_EX (ARM reg psr) ireg exc)
    (dabort_t:num option) data cp_interrupt =
    if ~(exc = software) then
      EXCEPTION (ARM reg psr) exc
    else
      let ic = DECODE_INST ireg
      and (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr)
      in
        if ~CONDITION_PASSED nzcv ireg then
          ARM (INC_PC reg) psr
        else let mode = DECODE_MODE m in
        if (ic = data_proc) \/ (ic = reg_shift) then
          DATA_PROCESSING (ARM reg psr) (CARRY nzcv) mode ireg
        else if ic = mla_mul then
          MLA_MUL (ARM reg psr) (CARRY nzcv) mode ireg
        else if ic = br then
          BRANCH (ARM reg psr) mode ireg
        else if (ic = ldr) \/ (ic = str) then
          (LDR_STR (ARM reg psr) (CARRY nzcv) mode
             (IS_SOME dabort_t) (HD data) ireg).state
        else if (ic = ldm) \/ (ic = stm) then
          (LDM_STM (ARM reg psr) mode dabort_t data ireg).state
        else if ic = swp then
          (SWP (ARM reg psr) mode (IS_SOME dabort_t) (HD data) ireg).state
        else if ic = swi_ex then
          EXCEPTION (ARM reg psr) software
        else if ic = mrs_msr then
          if ireg %% 21 then
            MSR (ARM reg psr) mode ireg
          else
            MRS (ARM reg psr) mode ireg
        else if cp_interrupt then
          (* IS_BUSY inp b  - therefore CP_INTERRUPT iflags b *)
          ARM reg psr
        else if ic = mrc then
          MRC (ARM reg psr) mode (ELL 1 data) ireg
        else if (ic = ldc) \/ (ic = stc) then
          (LDC_STC (ARM reg psr) mode ireg).state
        else if (ic = cdp_und) \/ (ic = mcr) then
          ARM (INC_PC reg) psr
        else
          ARM reg psr
End

(* ------------------------------------------------------------------------- *)
(* Exception operations                                                      *)
(* ------------------------------------------------------------------------- *)

Definition IS_Dabort_def:
  IS_Dabort irpt =
    (case irpt of SOME (Dabort x) => T | _ => F)
End

Definition IS_Reset_def:
  IS_Reset irpt =
    (case irpt of SOME (Reset x) => T | _ => F)
End

Definition PROJ_Dabort_def:   PROJ_Dabort (SOME (Dabort x)) = x
End
Definition PROJ_Reset_def:    PROJ_Reset  (SOME (Reset x))  = x
End

Definition interrupt2exception_def:
  interrupt2exception (ARM_EX (ARM reg psr) ireg exc) (i',f') irpt =
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ psr) in
    let pass = (exc = software /\ CONDITION_PASSED flags ireg)
    and ic = DECODE_INST ireg in
    let old_flags = (pass /\ (ic = mrs_msr)) in
    (case irpt of
       NONE            => software
     | SOME (Reset x)  => reset
     | SOME Prefetch   => pabort
     | SOME (Dabort t) => dabort
     | SOME Undef      => if pass /\ ic IN {cdp_und; mrc; mcr; stc; ldc} then
                            undefined
                          else
                            software
     | SOME Fiq        => if (if old_flags then f else f') then
                            software
                          else
                            fast
     | SOME Irq        => if (if old_flags then i else i') then
                            software
                          else
                            interrupt)
End

Definition PROJ_IF_FLAGS_def:
  PROJ_IF_FLAGS (ARM reg psr) =
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)
End

(* ------------------------------------------------------------------------- *)
(* The next state, output and state functions                                *)
(* ------------------------------------------------------------------------- *)

Definition NEXT_ARM_def:
  NEXT_ARM state (irpt,cp_interrupt,ireg,data) =
    if IS_Reset irpt then
      ARM_EX (PROJ_Reset irpt) ireg reset
    else
      let state' =
        EXEC_INST state
          (if IS_Dabort irpt then SOME (PROJ_Dabort irpt) else NONE)
          data cp_interrupt
      in
        ARM_EX state' ireg
          (interrupt2exception state (PROJ_IF_FLAGS state') irpt)
End

Definition OUT_ARM_def:
  OUT_ARM (ARM_EX (ARM reg psr) ireg exc) =
    let ic = DECODE_INST ireg
    and (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in
      (if (exc = software) /\ CONDITION_PASSED nzcv ireg then
         let mode = DECODE_MODE m in
         if (ic = ldr) \/ (ic = str) then
           (LDR_STR (ARM reg psr) (CARRY nzcv) mode ARB ARB ireg).out
         else if (ic = ldm) \/ (ic = stm) then
           (LDM_STM (ARM reg psr) mode ARB ARB ireg).out
         else if ic = swp then
           (SWP (ARM reg psr) mode ARB ARB ireg).out
         else if (ic = ldc) \/ (ic = stc) then
           (LDC_STC (ARM reg psr) mode ireg).out
         else if ic = mcr then
           MCR_OUT (ARM reg psr) mode ireg
         else []
       else [])
End

Definition STATE_ARM_def:
  (STATE_ARM 0 x = x.state) /\
  (STATE_ARM (SUC t) x = NEXT_ARM (STATE_ARM t x) (x.inp t))
End

Definition ARM_SPEC_def:
  ARM_SPEC t x = let s = STATE_ARM t x in <| state := s; out := OUT_ARM s |>
End

(* ------------------------------------------------------------------------- *)
(* Some useful theorems                                                      *)
(* ------------------------------------------------------------------------- *)

val STATE_ARM_THM = store_thm("STATE_ARM_THM",
  `IMAP ARM_SPEC I NEXT_ARM OUT_ARM`,
  RW_TAC (std_ss++boolSimps.LET_ss)
    [ARM_SPEC_def,STATE_ARM_def,IMAP_def,combinTheory.I_THM]);

val STATE_ARM_THM2 = store_thm("STATE_ARM_THM2",
  `IS_IMAP ARM_SPEC`, PROVE_TAC [STATE_ARM_THM,IS_IMAP_def]);

val STATE_ARM_THM3 = store_thm("STATE_ARM_THM3",
  `IS_IMAP_INIT ARM_SPEC I`, PROVE_TAC [STATE_ARM_THM,IS_IMAP_INIT_def]);

val ARM_SPEC_STATE = save_thm("ARM_SPEC_STATE",
  (SIMP_CONV (srw_ss()++boolSimps.LET_ss) [ARM_SPEC_def])
  ``(ARM_SPEC t x).state``);

(* ......................................................................... *)

val UPDATE_LT_COMMUTES = store_thm("UPDATE_LT_COMMUTES",
  `!m a b c d. a <+ b ==>
     ((b =+ d) ((a =+ c) m) = (a =+ c) ((b =+ d) m))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC wordsTheory.WORD_LOWER_NOT_EQ
    \\ ASM_SIMP_TAC std_ss [combinTheory.UPDATE_COMMUTES]);

(* ------------------------------------------------------------------------- *)
