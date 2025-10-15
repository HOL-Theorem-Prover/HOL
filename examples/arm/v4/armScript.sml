(* ========================================================================= *)
(* FILE          : armScript.sml                                             *)
(* DESCRIPTION   : Model of the ARM instruction set architecture             *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2007                                               *)
(* ========================================================================= *)

Theory arm
Ancestors
  words rich_list update
Libs
  Q


val _ = ParseExtras.temp_loose_equality()
(* ------------------------------------------------------------------------- *)
(*  The ARM State Space                                                      *)
(* ------------------------------------------------------------------------- *)

Datatype: state_inp = <| state : 'a; inp : num -> 'b |>
End
Datatype: state_out = <| state : 'a; out : 'b |>
End

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
   psr = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
End

Datatype:
   exceptions = reset | undefined | software | pabort |
                dabort | address |interrupt | fast
End

val _ = type_abbrev("registers", ``:register->word32``);
val _ = type_abbrev("psrs",      ``:psr->word32``);

Datatype: regs = <| reg : registers; psr : psrs |>
End

Datatype:
   arm_state = <| regs : regs; ireg : word32; exception : exceptions |>
End

(* ......................................................................... *)

Datatype:
   formats = SignedByte | UnsignedByte | SignedHalfWord |
             UnsignedHalfWord | UnsignedWord
End

Datatype: data = Byte word8 | Half word16 | Word word32
End

Datatype:
  memop = MemRead word32 | MemWrite word32 data | CPWrite word32
End

Datatype:
  interrupt = Reset regs | Undef | Prefetch | Dabort num | Fiq | Irq
End

Datatype:
  arm_input = <| ireg : word32; data : word32 list;
                 interrupt : interrupt option; no_cp : bool |>
End

Datatype: mode = usr | fiq | irq | svc | abt | und | sys | safe
End

Datatype:
   condition = EQ | CS | MI | VS | HI | GE | GT | AL |
               NE | CC | PL | VC | LS | LT | LE | NV
End

Datatype:
   iclass = swp | mrs | msr | data_proc | mla_mul |
            ldr_str | ldrh_strh | ldm_stm | br | swi_ex | cdp_und |
            mcr | mrc | ldc_stc | unexec
End

Datatype:
  arm_output = <| transfers : memop list; cpi : bool; user : bool |>
End

(* ------------------------------------------------------------------------- *)
(*  Memory operations                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = wordsLib.guess_lengths();

Definition GET_BYTE_def:
  GET_BYTE (oareg:word2) (data:word32) =
    case oareg of
      0w => (7 >< 0) data
    | 1w => (15 >< 8) data
    | 2w => (23 >< 16) data
    | _  => (31 >< 24) data
End

Definition GET_HALF_def:
  GET_HALF (oareg:word2) (data:word32) =
    if oareg ' 1 then
      (31 >< 16) data
    else
      (15 >< 0) data
End

Definition FORMAT_def:
  FORMAT fmt oareg data =
    case fmt of
      SignedByte       => sw2sw (GET_BYTE oareg data)
    | UnsignedByte     => w2w (GET_BYTE oareg data)
    | SignedHalfWord   => sw2sw (GET_HALF oareg data)
    | UnsignedHalfWord => w2w (GET_HALF oareg data)
    | UnsignedWord     => data #>> (8 * w2n oareg)
End

(* ------------------------------------------------------------------------- *)
(*  General Purpose Register operations                                      *)
(* ------------------------------------------------------------------------- *)

Definition USER_def:   USER m = (m = usr) \/ (m = sys) \/ (m = safe)
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
  REG_READ (reg:registers) m n =
    if n = 15w then
      reg r15 + 8w
    else
      reg (num2register (mode_reg2num m n))
End

Definition REG_WRITE_def:
  REG_WRITE (reg:registers) m n d =
    (num2register (mode_reg2num m n) =+ d) reg
End

Definition INC_PC_def:     INC_PC (reg:registers) = (r15 =+ reg r15 + 4w) reg
End
Definition FETCH_PC_def:   FETCH_PC (reg:registers) = reg r15
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

Definition SET_NZC_def:   SET_NZC (N,Z,C) w = SET_NZCV (N,Z,C,w ' 28) w
End
Definition SET_NZ_def:    SET_NZ (N,Z) w = SET_NZC (N,Z,w ' 29) w
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
    | sys => 31w
    | _ => 0w:word5
End

Definition SET_IFMODE_def:
  SET_IFMODE irq' fiq' mode w:word32 =
     word_modify (\i b. (7 < i \/ (i = 5)) /\ b \/
                        (i = 7) /\ irq' \/ (i = 6) /\ fiq' \/
                        (i < 5) /\ (mode_num mode) ' i) w
End

Definition DECODE_MODE_def:
  DECODE_MODE (m:word5) =
    case m of
      16w => usr
    | 17w => fiq
    | 18w => irq
    | 19w => svc
    | 23w => abt
    | 27w => und
    | 31w => sys
    | _ => safe
End

Definition NZCV_def:   NZCV (w:word32) = (w ' 31, w ' 30, w ' 29, w ' 28)
End

Definition DECODE_PSR_def:
  DECODE_PSR (cpsr:word32) = (NZCV cpsr, cpsr ' 7, cpsr ' 6, (4 >< 0) cpsr)
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

Definition SPSR_READ_def:   SPSR_READ (psr:psrs) mode = psr (mode2psr mode)
End
Definition CPSR_READ_def:   CPSR_READ (psr:psrs) = psr CPSR
End

Definition CPSR_WRITE_def:
  CPSR_WRITE (psr:psrs) cpsr = (CPSR =+ cpsr) psr
End

Definition SPSR_WRITE_def:
  SPSR_WRITE (psr:psrs) mode spsr =
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
  EXCEPTION r type =
    let cpsr = CPSR_READ r.psr in
    let fiq' = ((type = reset) \/ (type = fast)) \/ cpsr ' 6
    and mode' = exception2mode type
    and pc = n2w (4 * exceptions2num type):word32 in
    let reg' = REG_WRITE r.reg mode' 14w (FETCH_PC r.reg + 4w) in
      <| reg := REG_WRITE reg' usr 15w pc;
         psr := CPSR_WRITE (SPSR_WRITE r.psr mode' cpsr)
                  (SET_IFMODE T fiq' mode' cpsr) |>
End

(* ------------------------------------------------------------------------- *)
(* The Branch instruction class (br)                                         *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_BRANCH_def:
  DECODE_BRANCH (w:word32) = (w ' 24, (23 >< 0) w)
End

Definition BRANCH_def:
  BRANCH r mode ireg =
    let (L,offset) = DECODE_BRANCH ireg
    and pc = REG_READ r.reg usr 15w in
    let br_addr = pc + sw2sw offset << 2 in
    let pc_reg = REG_WRITE r.reg usr 15w br_addr in
      <| reg := if L then
                  REG_WRITE pc_reg mode 14w (FETCH_PC r.reg + 4w)
                else
                  pc_reg;
         psr := r.psr |>
End

(* ------------------------------------------------------------------------- *)
(* The Data Processing instruction class (data_proc)                         *)
(* ------------------------------------------------------------------------- *)

Definition LSL_def:
  LSL (m:word32) (n:word8) c =
    if n = 0w then (c, m) else
      (n <=+ 32w /\ m ' (32 - w2n n), m << w2n n)
End

Definition LSR_def:
  LSR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (n <=+ 32w /\ m ' (w2n n - 1), m >>> w2n n)
End

Definition ASR_def:
  ASR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m ' (MIN 31 (w2n n - 1)), m >> w2n n)
End

Definition ROR_def:
  ROR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m ' (w2n ((w2w n):word5) - 1), m #>> w2n n)
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
    case sh of
      0w => LSL rm shift c
    | 1w => LSR rm (if shift = 0w then 32w else shift) c
    | 2w => ASR rm (if shift = 0w then 32w else shift) c
    | _  => if shift = 0w then word_rrx (c,rm) else ROR rm shift c
End

Definition SHIFT_REGISTER2_def:
  SHIFT_REGISTER2 shift (sh:word2) rm c =
    case sh of
      0w => LSL rm shift c
    | 1w => LSR rm shift c
    | 2w => ASR rm shift c
    | _  => ROR rm shift c
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
    else if opnd2 ' 4 then
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
    case opc of
      0w  => AND rn op2
    | 1w  => EOR rn op2
    | 2w  => SUB rn op2 T
    | 4w  => ADD rn op2 F
    | 3w  => SUB op2 rn T
    | 5w  => ADD rn op2 c
    | 6w  => SUB rn op2 c
    | 7w  => SUB op2 rn c
    | 8w  => AND rn op2
    | 9w  => EOR rn op2
    | 10w => SUB rn op2 T
    | 11w => ADD rn op2 F
    | 12w => ORR rn op2
    | 13w => ALU_logic op2
    | 14w => AND rn (~op2)
    | _   => ALU_logic (~op2)
End

(* ......................................................................... *)

Definition ARITHMETIC_def:
  ARITHMETIC (opcode:word4) =
    (opcode ' 2 \/ opcode ' 1) /\ (~(opcode ' 3) \/ ~(opcode ' 2))
End

Definition TEST_OR_COMP_def:
  TEST_OR_COMP (opcode:word4) = ((3 -- 2 ) opcode = 2w)
End

Definition DECODE_DATAP_def:
  DECODE_DATAP (w:word32) =
    (w ' 25,(24 >< 21) w,w ' 20,(19 >< 16) w,(15 >< 12) w,(11 >< 0) w)
End

Definition DATA_PROCESSING_def:
  DATA_PROCESSING r C mode ireg =
    let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP ireg in
    let (C_s,op2) = ADDR_MODE1 r.reg mode C I opnd2
    and pc_reg = INC_PC r.reg in
    let rn = REG_READ (if ~I /\ (opnd2 ' 4) then pc_reg else r.reg) mode Rn in
    let ((N,Z,C_alu,V),res) = ALU opcode rn op2 C
    and tc = TEST_OR_COMP opcode in
      <| reg := if tc then pc_reg else REG_WRITE pc_reg mode Rd res;
         psr := if S then
                  CPSR_WRITE r.psr
                    (if (Rd = 15w) /\ ~tc then SPSR_READ r.psr mode
                         else (if ARITHMETIC opcode
                                 then SET_NZCV (N,Z,C_alu,V)
                                 else SET_NZC  (N,Z,C_s)) (CPSR_READ r.psr))
                else r.psr |>
End

(* ------------------------------------------------------------------------- *)
(* The PSR Transfer instruction class (mrs and msr)                          *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_MRS_def:   DECODE_MRS (w:word32) = (w ' 22,(15 >< 12) w)
End

Definition MRS_def:
  MRS r mode ireg =
    let (R,Rd) = DECODE_MRS ireg in
    let word = if R then SPSR_READ r.psr mode else CPSR_READ r.psr in
      <| reg := REG_WRITE (INC_PC r.reg) mode Rd word; psr := r.psr |>
End

(* ......................................................................... *)

Definition DECODE_MSR_def:
  DECODE_MSR (w:word32) =
    (w ' 25,w ' 22,w ' 19,w ' 16,(3 >< 0) w,(11 >< 0) w)
End

Definition MSR_def:
  MSR r mode ireg =
    let (I,R,bit19,bit16,Rm,opnd) = DECODE_MSR ireg in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      <| reg := INC_PC r.reg; psr := r.psr |>
    else
      let psrd = if R then SPSR_READ r.psr mode else CPSR_READ r.psr
      and  src = if I then SND (IMMEDIATE F opnd) else REG_READ r.reg mode Rm in
      let psrd' = word_modify
             (\i b. (28 <= i) /\ (if bit19 then src ' i else b) \/
                    (8 <= i) /\ (i <= 27) /\ b \/
                    (i <= 7) /\ (if bit16 /\ ~USER mode then src ' i else b))
             psrd
      in
        <| reg := INC_PC r.reg;
           psr := if R then
                    SPSR_WRITE r.psr mode psrd'
                  else
                    CPSR_WRITE r.psr psrd' |>
End

(* ------------------------------------------------------------------------- *)
(* The Multiply instruction class (mla_mul)                                  *)
(* ------------------------------------------------------------------------- *)

Definition ALU_multiply_def:
  ALU_multiply L Sgn A rd rn rs rm =
    let res = (if A then
                 if L then rd @@ rn else w2w rn
               else
                  0w:word64) +
              (if L /\ Sgn then
                 sw2sw rm * sw2sw rs
               else
                 w2w rm * w2w rs) in
    let resHi = (63 >< 32) res
    and resLo = (31 >< 0) res in
      if L then
        (word_msb res,res = 0w,resHi,resLo)
      else
        (word_msb resLo,resLo = 0w,rd,resLo)
End

Definition DECODE_MLA_MUL_def:
  DECODE_MLA_MUL (w:word32) = (w ' 23,w ' 22,w ' 21,w ' 20,
    (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,(3 >< 0) w)
End

Definition MLA_MUL_def:
  MLA_MUL r mode ireg =
    let (L,Sgn,A,S,Rd,Rn,Rs,Rm) = DECODE_MLA_MUL ireg in
    let pc_reg = INC_PC r.reg in
    let rd = REG_READ r.reg mode Rd
    and rn = REG_READ r.reg mode Rn
    and rs = REG_READ r.reg mode Rs
    and rm = REG_READ r.reg mode Rm in
    let (N,Z,resHi,resLo) = ALU_multiply L Sgn A rd rn rs rm in
      if (Rd = 15w) \/ (Rd = Rm) \/
         L /\ ((Rn = 15w) \/ (Rn = Rm) \/ (Rd = Rn)) then
        <| reg := pc_reg; psr := r.psr |>
      else
        <| reg := if L then
                    REG_WRITE (REG_WRITE pc_reg mode Rn resLo) mode Rd resHi
                  else
                    REG_WRITE pc_reg mode Rd resLo;
           psr := if S then
                    CPSR_WRITE r.psr (SET_NZ (N,Z) (CPSR_READ r.psr))
                  else
                    r.psr |>
End

(* ------------------------------------------------------------------------- *)
(* The Single Data Transfer instruction class (ldr_str)                      *)
(* ------------------------------------------------------------------------- *)

Definition UP_DOWN_def:  UP_DOWN u = if u then $word_add else $word_sub
End

Definition ADDR_MODE2_def:
  ADDR_MODE2 reg mode C Im P U Rn offset =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then SND (SHIFT_IMMEDIATE reg mode C offset)
                 else w2w offset) in
      (if P then wb_addr else addr,wb_addr)
End

Definition DECODE_LDR_STR_def:
  DECODE_LDR_STR (w:word32) =
     (w ' 25,w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
      (19 >< 16) w,(15 >< 12) w,(11 >< 0) w)
End

Definition LDR_STR_def:
  LDR_STR r C mode ireg input =
    let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
    let (addr,wb_addr) = ADDR_MODE2 r.reg mode C I P U Rn offset in
    let pc_reg = INC_PC r.reg in
      case input of
        NONE => INL
           [if L then
              MemRead addr
            else
              let w = REG_READ pc_reg mode Rd in
                MemWrite addr (if B then Byte ((7 >< 0) w) else Word w)]
      | SOME (isdabort, data) =>
           let wb_reg = if P ==> W then
                          REG_WRITE pc_reg mode Rn wb_addr
                        else
                          pc_reg
           in INR
             <| reg :=
                  if L ==> isdabort then
                    wb_reg
                  else let fmt = if B then UnsignedByte else UnsignedWord in
                    REG_WRITE wb_reg mode Rd
                      (FORMAT fmt ((1 >< 0) addr) (HD data));
                psr := r.psr |>
End

(* ------------------------------------------------------------------------- *)
(* Half Word Single Data Transfer instruction class (ldrh_strh)              *)
(* ------------------------------------------------------------------------- *)

Definition ADDR_MODE3_def:
  ADDR_MODE3 reg mode Im P U Rn offsetH offsetL =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then offsetH @@ offsetL
                 else REG_READ reg mode offsetL) in
      (if P then wb_addr else addr,wb_addr)
End

Definition DECODE_LDRH_STRH_def:
  DECODE_LDRH_STRH (w:word32) =
     (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
      (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,w ' 6,w ' 5,(3 >< 0) w)
End

Definition LDRH_STRH_def:
  LDRH_STRH r mode ireg input =
    let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
    let (addr,wb_addr) = ADDR_MODE3 r.reg mode I P U Rn offsetH offsetL in
    let pc_reg = INC_PC r.reg in
      case input of
        NONE => INL
           [if L then
              MemRead addr
            else
              MemWrite addr (Half ((15 >< 0) (REG_READ pc_reg mode Rd)))]
      | SOME (isdabort, data) =>
           let wb_reg = if P ==> W then
                          REG_WRITE pc_reg mode Rn wb_addr
                        else
                          pc_reg
           in INR
             <| reg :=
                 if L ==> isdabort then
                   wb_reg
                 else
                   let fmt = case (S, H) of
                               (F,T) => UnsignedHalfWord
                             | (T,F) => SignedByte
                             | (T,T) => SignedHalfWord
                             | _ => ARB
                   in
                     REG_WRITE wb_reg mode Rd
                       (FORMAT fmt ((1 >< 0) addr) (HD data));
                psr := r.psr |>
End

(* ------------------------------------------------------------------------- *)
(*  The Block Data Transfer instruction class (ldm_stm)                      *)
(* ------------------------------------------------------------------------- *)

Definition REGISTER_LIST_def:
  REGISTER_LIST (list:word16) =
    (MAP SND o FILTER FST) (GENLIST (\i. (list ' i,(n2w i):word4)) 16)
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
    MAP (\(rp,addr). MemWrite addr (Word (REG_READ reg mode rp))) bl_list
End

Definition DECODE_LDM_STM_def:
  DECODE_LDM_STM (w:word32) =
    (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,(19 >< 16) w,(15 >< 0) w)
End

Definition LDM_STM_def:
  LDM_STM r mode ireg input =
    let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
    let pc_in_list = list ' 15
    and rn = REG_READ r.reg mode Rn in
    let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list
    and mode' = if S /\ (L ==> ~pc_in_list) then usr else mode
    and pc_reg = INC_PC r.reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg (if L then mode else mode') Rn rn'
                 else
                   pc_reg
    in
      case input of
        NONE => INL
          (if L then
             MAP MemRead addr_list
           else
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg) mode'
               (ZIP (rp_list,addr_list)))
      | SOME (dabort_t, data) => INR
          (if L then
             <| reg :=
                  let t = if IS_SOME dabort_t then
                            THE dabort_t
                          else
                            LENGTH rp_list in
                  let ldm_reg = LDM_LIST wb_reg mode' (FIRSTN t rp_list)
                                  (FIRSTN t data) in
                    if IS_SOME dabort_t /\ ~(Rn = 15w) then
                      REG_WRITE ldm_reg mode' Rn (REG_READ wb_reg mode' Rn)
                    else ldm_reg;
                 psr := if S /\ pc_in_list /\ IS_NONE dabort_t then
                          CPSR_WRITE r.psr (SPSR_READ r.psr mode)
                        else r.psr |>
           else <| reg := wb_reg; psr := r.psr |>)
End

(* ------------------------------------------------------------------------- *)
(* The Single Data Swap instruction class (swp)                              *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_SWP_def:
  DECODE_SWP (w:word32) = (w ' 22,(19 >< 16) w,(15 >< 12) w,(3 >< 0) w)
End

Definition SWP_def:
  SWP r mode ireg input =
    let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
    let rn = REG_READ r.reg mode Rn
    and pc_reg = INC_PC r.reg in
    let rm = REG_READ pc_reg mode Rm in
      case input of
        NONE => INL
           [MemRead rn;
            MemWrite rn (if B then Byte ((7 >< 0) rm) else Word rm)]
      | SOME (isdabort, data) => INR
          <| reg :=
                if isdabort then
                  pc_reg
                else let fmt = if B then UnsignedByte else UnsignedWord in
                  REG_WRITE pc_reg mode Rd
                    (FORMAT fmt ((1 ><  0) rn) (HD data));
              psr := r.psr |>
End

(* ------------------------------------------------------------------------- *)
(* Coprocessor Register Transfer (mrc, mcr)                                  *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_MRC_MCR_def:
  DECODE_MRC_MCR (w:word32) =
    ((23 >< 21) w,(19 >< 16) w,(15 >< 12) w,
     (11 >< 8) w, (7 >< 5) w,(3 >< 0) w)
End

Definition MRC_def:
  MRC r mode data ireg =
    let Rd = (15 >< 12) ireg
    and pc_reg = INC_PC r.reg in
      if Rd = 15w then
        <| reg := pc_reg;
           psr := CPSR_WRITE r.psr (SET_NZCV (NZCV data) (CPSR_READ r.psr)) |>
      else
        <| reg := REG_WRITE pc_reg mode Rd data; psr := r.psr |>
End

Definition MCR_OUT_def:
  MCR_OUT reg mode ireg =
    let Rd = (15 >< 12) ireg in
      [CPWrite (REG_READ (INC_PC reg) mode Rd)]
End

(* ------------------------------------------------------------------------- *)
(* Coprocessor Data Transfers (ldc_stc)                                      *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_LDC_STC_def:
  DECODE_LDC_STC (w:word32) =
    (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
     (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,(7 >< 0) w)
End

Definition ADDR_MODE5_def:
  ADDR_MODE5 reg mode P U Rn (offset:word8) =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr (w2w offset << 2) in
      (if P then wb_addr else addr,wb_addr)
End

Definition LDC_STC_def:
  LDC_STC r mode ireg input =
    let (P,U,N,W,L,Rn,CRd,CPN,offset) = DECODE_LDC_STC ireg in
    let (addr,wb_addr) = ADDR_MODE5 r.reg mode P U Rn offset in
      if input then
        let pc_reg = INC_PC r.reg in
        let wb_reg = if W /\ ~(Rn = 15w) then
                       REG_WRITE pc_reg mode Rn wb_addr
                     else
                       pc_reg
        in
          INR <| reg := wb_reg; psr := r.psr |>
      else
          INL [if L then MemRead addr else MemWrite addr ARB]
End

(* ------------------------------------------------------------------------- *)
(* Predicate for conditional execution                                       *)
(* ------------------------------------------------------------------------- *)

Definition CONDITION_PASSED2_def:
  CONDITION_PASSED2 (N,Z,C,V) cond =
    case cond of
      EQ => Z
    | NE => ~Z
    | CS => C
    | CC => ~C
    | MI => N
    | PL => ~N
    | VS => V
    | VC => ~V
    | HI => C /\ ~Z
    | LS => ~C \/ Z
    | GE => N = V
    | LT => ~(N = V)
    | GT => ~Z /\ (N = V)
    | LE => Z \/ ~(N = V)
    | AL => T
    | NV => F
End

Definition CONDITION_PASSED_def:
  CONDITION_PASSED flags (ireg:word32) =
    let pass = CONDITION_PASSED2 flags (num2condition (w2n ((31 -- 29) ireg)))
    in
      if ireg ' 28 then ~pass else pass
End

(* ------------------------------------------------------------------------- *)
(* Top-level decode and run functions                                        *)
(* ------------------------------------------------------------------------- *)

Definition DECODE_ARM_def:
  DECODE_ARM (ireg : word32) =
    let b n = ireg ' n in
      case (b 27,b 26,b 25,b 24,b 23,b 22,b 21,b 20,b 7,b 6,b 5,b 4) of
        (F,F,F,T,F,_,F,F,F,F,F,F) => mrs
      | (F,F,F,T,F,_,T,F,F,F,F,F) => msr
      | (F,F,F,_,_,_,_,_,_,_,_,F) => data_proc
      | (F,F,F,_,_,_,_,_,F,_,_,T) => data_proc
      | (F,F,F,F,F,F,_,_,T,F,F,T) => mla_mul
      | (F,F,F,F,T,_,_,_,T,F,F,T) => mla_mul
      | (F,F,F,T,F,_,F,F,T,F,F,T) => swp
      | (F,F,F,_,_,_,_,_,T,F,T,T) => ldrh_strh
      | (F,F,F,_,_,_,_,T,T,T,_,T) => ldrh_strh
      | (F,F,T,T,F,_,F,F,_,_,_,_) => cdp_und
      | (F,F,T,T,F,_,T,F,_,_,_,_) => msr
      | (F,F,T,_,_,_,_,_,_,_,_,_) => data_proc
      | (F,T,F,_,_,_,_,_,_,_,_,_) => ldr_str
      | (F,T,T,_,_,_,_,_,_,_,_,F) => ldr_str
      | (T,F,F,_,_,_,_,_,_,_,_,_) => ldm_stm
      | (T,F,T,_,_,_,_,_,_,_,_,_) => br
      | (T,T,F,_,_,_,_,_,_,_,_,_) => ldc_stc
      | (T,T,T,F,_,_,_,T,_,_,_,T) => mrc
      | (T,T,T,F,_,_,_,F,_,_,_,T) => mcr
      | (T,T,T,T,_,_,_,_,_,_,_,_) => swi_ex
      | _ => cdp_und
End

Definition RUN_ARM_def:
  RUN_ARM state (dabt:num option) data no_cp =
    let ireg = state.ireg and r = state.regs
    and inc_pc x = <| reg := INC_PC x.reg; psr := x.psr |>
    in
      if ~(state.exception = software) then
        EXCEPTION r state.exception
      else let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ r.psr) in
        if ~CONDITION_PASSED nzcv ireg then
          inc_pc r
        else let mode = DECODE_MODE m
             and coproc f = if no_cp then r else f r
        in
          case DECODE_ARM ireg of
            data_proc => DATA_PROCESSING r (CARRY nzcv) mode ireg
          | mla_mul   => MLA_MUL r mode ireg
          | swi_ex    => EXCEPTION r software
          | br        => BRANCH r mode ireg
          | msr       => MSR r mode ireg
          | mrs       => MRS r mode ireg
          | swp       => OUTR (SWP r mode ireg (SOME (IS_SOME dabt, data)))
          | ldm_stm   => OUTR (LDM_STM r mode ireg (SOME (dabt, data)))
          | ldr_str   => OUTR
               (LDR_STR r (CARRY nzcv) mode ireg (SOME (IS_SOME dabt, data)))
          | ldrh_strh => OUTR
               (LDRH_STRH r mode ireg (SOME (IS_SOME dabt, data)))
          | ldc_stc   => coproc (\x. (OUTR (LDC_STC x mode ireg T)))
          | mrc       => coproc (\x. MRC x mode (ELL 1 data) ireg)
          | mcr       => coproc inc_pc
          | cdp_und   => coproc inc_pc
          | _ => r
End

(* ------------------------------------------------------------------------- *)
(* Exception operations                                                      *)
(* ------------------------------------------------------------------------- *)

Definition IS_Reset_def:
  (IS_Reset (SOME (Reset x)) = T) /\ (IS_Reset _ = F)
End

Definition PROJ_Reset_def:
  PROJ_Reset (SOME (Reset x)) = x
End

Definition PROJ_Dabort_def:
  (PROJ_Dabort (SOME (Dabort x)) = SOME x) /\
  (PROJ_Dabort _ = NONE)
End

Definition interrupt2exception_def:
  interrupt2exception state (i',f') irpt =
    let ireg = state.ireg in
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ state.regs.psr) in
    let pass = (state.exception = software) /\ CONDITION_PASSED flags ireg
    and ic = DECODE_ARM ireg in
    let old_flags = pass /\ ((ic = mrs) \/ (ic = msr)) in
    (case irpt of
       NONE            => software
     | SOME (Reset x)  => reset
     | SOME Prefetch   => pabort
     | SOME (Dabort t) => dabort
     | SOME Undef      => if pass /\ ic IN {cdp_und; mrc; mcr; ldc_stc} then
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
  PROJ_IF_FLAGS psr =
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)
End

(* ------------------------------------------------------------------------- *)
(* The next state, output and state functions                                *)
(* ------------------------------------------------------------------------- *)

Definition NEXT_ARM_def:
  NEXT_ARM state inp =
    let r = if IS_Reset inp.interrupt then
              PROJ_Reset inp.interrupt
            else
              RUN_ARM state (PROJ_Dabort inp.interrupt) inp.data inp.no_cp
    in
      <| regs := r; ireg := inp.ireg;
         exception :=
           interrupt2exception state (PROJ_IF_FLAGS r.psr) inp.interrupt |>
End

Definition OUT_ARM_def:
  OUT_ARM state =
    let ireg = state.ireg and r = state.regs in
    let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ r.psr) in
    let mode = DECODE_MODE m in
      if (state.exception = software) /\ CONDITION_PASSED nzcv ireg then
        let ic = DECODE_ARM ireg in
           <| transfers :=
               (case ic of
                  ldr_str   => OUTL (LDR_STR r (CARRY nzcv) mode ireg NONE)
                | ldrh_strh => OUTL (LDRH_STRH r mode ireg NONE)
                | ldm_stm   => OUTL (LDM_STM r mode ireg NONE)
                | swp       => OUTL (SWP r mode ireg NONE)
                | ldc_stc   => OUTL (LDC_STC r mode ireg F)
                | mcr       => MCR_OUT r.reg mode ireg
                | _         => []);
              cpi := (ic IN {cdp_und; mcr; mrc; ldc_stc});
              user := USER mode
           |>
        else
           <| transfers := []; cpi := F; user := USER mode |>
End

Definition STATE_ARM_def:
  (STATE_ARM 0 x = x.state) /\
  (STATE_ARM (SUC t) x = NEXT_ARM (STATE_ARM t x) (x.inp t))
End

Definition ARM_SPEC_def:
  ARM_SPEC t x = let s = STATE_ARM t x in <| state := s; out := OUT_ARM s |>
End

(* ------------------------------------------------------------------------- *)

val _ = computeLib.add_persistent_funs
  (["pred_set.IN_INSERT",
    "pred_set.NOT_IN_EMPTY"] @
  ["register_EQ_register","num2register_thm","register2num_thm", "mode_EQ_mode",
   "mode2num_thm", "psr_EQ_psr", "psr2num_thm", "iclass_EQ_iclass",
   "iclass2num_thm", "num2condition_thm", "condition2num_thm",
   "exceptions_EQ_exceptions", "num2exceptions_thm", "exceptions2num_thm"])
