(* ========================================================================= *)
(* FILE          : armScript.sml                                             *)
(* DESCRIPTION   : Model of the ARM instruction set architecture             *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2007                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "rich_listTheory", "updateTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q wordsTheory rich_listTheory updateTheory;

val _ = new_theory "arm";

val _ = set_fixity "'" (Infixl 2000);
val _ = overload_on ("'", Term`$index`);

(* ------------------------------------------------------------------------- *)
(*  The ARM State Space                                                      *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;

val _ = Hol_datatype
  `psr = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und`;

val _ = Hol_datatype
  `exceptions = reset | undefined | software | pabort
              | dabort | address |interrupt | fast`;

val _ = type_abbrev("registers", ``:register->word32``);
val _ = type_abbrev("psrs",      ``:psr->word32``);

val _ = Hol_datatype `regs = <| reg : registers; psr : psrs |>`;

val _ = Hol_datatype
  `arm_state = <| regs : regs; exception : exceptions |>`;

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val _ = Hol_datatype
  `formats = SignedByte | UnsignedByte | SignedHalfWord
           | UnsignedHalfWord | UnsignedWord`;

val _ = Hol_datatype `data = Byte of word8 | Half of word16 | Word of word32`;

val _ = Hol_datatype `memop = MemRead of word32 | MemWrite of word32=>data`;

val _ = Hol_datatype`
  transfers = MemAccess of (num->word32 list->memop list)
            | CPWrite of word32`;

val _ = Hol_datatype`
  arm_output = <| transfers : transfers; cpi : bool; user : bool |>`;

val _ = Hol_datatype`
  interrupts = <| Reset : regs option; Prefetch : bool;
                  Dabort : num option; Fiq : bool; Irq : bool |>`;

val _ = Hol_datatype`
  arm_input = <| ireg : word32 ; data : word32 list;
                 interrupts : interrupts ; absent : bool |>`;

val _ = Hol_datatype `pipe_output = <| ireg : word32; abort : bool |>`;

val _ = Hol_datatype `mode = usr | fiq | irq | svc | abt | und | sys | safe`;

val _ = Hol_datatype
  `condition = EQ | CS | MI | VS | HI | GE | GT | AL
             | NE | CC | PL | VC | LS | LT | LE | NV`;

val _ = Hol_datatype
  `iclass = swp | mrs | msr | data_proc | mla_mul
          | ldr_str | ldrh_strh | ldm_stm | br | bx | swi_ex
          | cdp_und | mcr | mrc | ldc_stc | unexec`;

(* ------------------------------------------------------------------------- *)
(*  Byte/Half-Word/Word extraction (little-endian)                           *)
(* ------------------------------------------------------------------------- *)

val _ = wordsLib.guess_lengths();

val GET_BYTE_def = Define`
  GET_BYTE (oareg:word2) (data:word32) =
    case oareg of
       0w -> (7 >< 0) data
    || 1w -> (15 >< 8) data
    || 2w -> (23 >< 16) data
    || _  -> (31 >< 24) data`;

val GET_HALF_def = Define`
  GET_HALF (oareg:word2) (data:word32) =
    if oareg ' 1 then
      (31 >< 16) data
    else
      (15 >< 0) data`;

val FORMAT_def = Define`
  FORMAT fmt oareg data =
    case fmt of
       SignedByte       -> sw2sw (GET_BYTE oareg data)
    || UnsignedByte     -> w2w (GET_BYTE oareg data)
    || SignedHalfWord   -> sw2sw (GET_HALF oareg data)
    || UnsignedHalfWord -> w2w (GET_HALF oareg data)
    || UnsignedWord     -> data #>> (8 * w2n oareg)`;

(* ------------------------------------------------------------------------- *)
(*  General Purpose Register operations                                      *)
(* ------------------------------------------------------------------------- *)

val USER_def = Define `USER m = (m = usr) \/ (m = sys) \/ (m = safe)`;

val mode_reg2num_def = Define`
  mode_reg2num m (w:word4) = let n = w2n w in
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
  REG_READ t (reg:registers) m n =
    if n = 15w then
      reg r15 + (if t then 4w else 8w)
    else
      reg (num2register (mode_reg2num m n))`;

val REG_WRITE_def = Define`
  REG_WRITE (reg:registers) m n d =
    (num2register (mode_reg2num m n) =+ d) reg`;

val INC_PC_def   = Define`
  INC_PC t (reg:registers) = (r15 =+ reg r15 + (if t then 2w else 4w)) reg`;

val FETCH_PC_def = Define `FETCH_PC (reg:registers) = reg r15`;

(*  FETCH_PC is needed because (REG_READ t reg usr 15w) gives PC + 4/8.      *)

(* ------------------------------------------------------------------------- *)
(*  Program Status Register operations                                       *)
(* ------------------------------------------------------------------------- *)

val SET_NZCV_def = Define`
  SET_NZCV (N,Z,C,V) w:word32 =
    word_modify (\i b. (i = 31) /\ N \/ (i = 30) /\ Z \/
                       (i = 29) /\ C \/ (i = 28) /\ V \/
                       (i < 28) /\ b) w`;

val SET_NZC_def = Define `SET_NZC (N,Z,C) w = SET_NZCV (N,Z,C,w ' 28) w`;
val SET_NZ_def  = Define `SET_NZ (N,Z) w = SET_NZC (N,Z,w ' 29) w`;

val mode_num_def = Define`
  mode_num mode =
    case mode of
       usr -> 16w
    || fiq -> 17w
    || irq -> 18w
    || svc -> 19w
    || abt -> 23w
    || und -> 27w
    || sys -> 31w
    || _ -> 0w:word5`;

val SET_IFTM_def = Define`
  SET_IFTM i f t m w:word32 =
     word_modify (\x b. (7 < x) /\ b \/
                        (x = 7) /\ i \/ (x = 6) /\ f \/ (x = 5) /\ t \/
                        (x < 5) /\ (mode_num m) ' x) w`;

val SET_THUMB_def = Define `SET_THUMB b (w:word32) = (5 :+ b) w`;

val DECODE_MODE_def = Define`
  DECODE_MODE (m:word5) =
    case m of
       16w -> usr
    || 17w -> fiq
    || 18w -> irq
    || 19w -> svc
    || 23w -> abt
    || 27w -> und
    || 31w -> sys
    || _ -> safe`;

val NZCV_def = Define `NZCV (w:word32) = (w ' 31, w ' 30, w ' 29, w ' 28)`;

val DECODE_PSR_def = Define`
  DECODE_PSR (cpsr:word32) =
    (NZCV cpsr, cpsr ' 7, cpsr ' 6, cpsr ' 5, (4 >< 0) cpsr)`;

val CARRY_def = Define `CARRY (n,z,c,v) = c`;

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

val SPSR_READ_def = Define `SPSR_READ (psr:psrs) mode = psr (mode2psr mode)`;
val CPSR_READ_def = Define `CPSR_READ (psr:psrs) = psr CPSR`;

val CPSR_WRITE_def = Define`
  CPSR_WRITE (psr:psrs) cpsr = (CPSR =+ cpsr) psr`;

val SPSR_WRITE_def = Define`
  SPSR_WRITE (psr:psrs) mode spsr =
    if USER mode then psr else (mode2psr mode =+ spsr) psr`;

(* ------------------------------------------------------------------------- *)
(* The Sofware Interrupt/Exception instruction class (swi_ex)                *)
(* ------------------------------------------------------------------------- *)

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
  EXCEPTION r t type =
    let cpsr = CPSR_READ r.psr in
    let fiq' = ((type = reset) \/ (type = fast)) \/ cpsr ' 6
    and mode' = exception2mode type
    and pc = n2w (4 * exceptions2num type):word32 in
    let reg' = REG_WRITE r.reg mode' 14w
                 (FETCH_PC r.reg + (if t then 2w else 4w)) in
      <| reg := REG_WRITE reg' usr 15w pc;
         psr := CPSR_WRITE (SPSR_WRITE r.psr mode' cpsr)
                  (SET_IFTM T fiq' F mode' cpsr) |>`;

(* ------------------------------------------------------------------------- *)
(* The Branch instruction class (br)                                         *)
(* ------------------------------------------------------------------------- *)

val DECODE_BRANCH_def = Define`
  DECODE_BRANCH (w:word32) = (w ' 24, (23 >< 0) w)`;

val BRANCH_def = Define`
  BRANCH r t mode ireg =
    let (L,offset) = DECODE_BRANCH ireg
    and fpc = FETCH_PC r.reg
    and pc = REG_READ t r.reg usr 15w in
    let offset_11 = (21 >< 11) offset in
    let br_addr = if t /\ L then
                    if offset_11 = 0w then              (* thumb BL (pt 2.) *)
                      REG_READ t r.reg mode 14w + w2w ((10 >< 0) offset) << 1
                    else                                (* thumb BL (pt 1.) *)
                      fpc + 2w
                  else
                    pc + sw2sw offset << (if t then 1 else 2) in
    let pc_reg = REG_WRITE r.reg usr 15w br_addr in
      <| reg := if L then
                  let link =
                        if t then
                          if offset_11 = 0w then        (* thumb BL (pt 2.) *)
                            (fpc + 2w) !! 1w
                          else                          (* thumb BL (pt 1.) *)
                            pc + w2w ((sw2sw offset_11):word24) << 12
                        else
                          fpc + 4w
                  in
                    REG_WRITE pc_reg mode 14w link
                else
                  pc_reg;
         psr := r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* The Branch and Exchange instruction class (bx)                            *)
(* ------------------------------------------------------------------------- *)

val BRANCH_EXCHANGE_def = Define`
  BRANCH_EXCHANGE r t mode (ireg:word32) =
    let Rm = (3 >< 0) ireg in
    let rm = REG_READ t r.reg mode Rm in
      <| reg := REG_WRITE r.reg usr 15w ((31 <> 1) rm);
         psr := CPSR_WRITE r.psr (SET_THUMB (rm ' 0) (CPSR_READ r.psr))
      |>`;

(* ------------------------------------------------------------------------- *)
(* The Data Processing instruction class (data_proc)                         *)
(* ------------------------------------------------------------------------- *)

val LSL_def = Define`
  LSL (m:word32) (n:word8) c =
    if n = 0w then (c, m) else
      (n <=+ 32w /\ m ' (32 - w2n n), m << w2n n)`;

val LSR_def = Define`
  LSR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (n <=+ 32w /\ m ' (w2n n - 1), m >>> w2n n)`;

val ASR_def = Define`
  ASR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m ' (MIN 31 (w2n n - 1)), m >> w2n n)`;

val ROR_def = Define`
  ROR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m ' (w2n ((w2w n):word5) - 1), m #>> w2n n)`;

val IMMEDIATE_def = Define`
  IMMEDIATE C (opnd2:word12) =
    let rot = (11 >< 8) opnd2
    and imm = (7 >< 0) opnd2
    in
      ROR imm (2w * rot) C`;

val SHIFT_IMMEDIATE2_def = Define`
  SHIFT_IMMEDIATE2 shift (sh:word2) rm c =
    case sh of
       0w -> LSL rm shift c
    || 1w -> LSR rm (if shift = 0w then 32w else shift) c
    || 2w -> ASR rm (if shift = 0w then 32w else shift) c
    || _  -> if shift = 0w then word_rrx (c,rm) else ROR rm shift c`;

val SHIFT_REGISTER2_def = Define`
  SHIFT_REGISTER2 shift (sh:word2) rm c =
    case sh of
       0w -> LSL rm shift c
    || 1w -> LSR rm shift c
    || 2w -> ASR rm shift c
    || _  -> ROR rm shift c`;

val SHIFT_IMMEDIATE_def = Define`
  SHIFT_IMMEDIATE reg t mode C (opnd2:word12) =
    let Rm = (3 >< 0) opnd2 in
    let rm = REG_READ t reg mode Rm
    and sh = (6 >< 5) opnd2
    and shift = (11 >< 7) opnd2
    in
      SHIFT_IMMEDIATE2 shift sh rm C`;

val SHIFT_REGISTER_def = Define`
  SHIFT_REGISTER reg t mode C (opnd2:word12) =
    let Rs = (11 >< 8) opnd2
    and Rm = (3 >< 0) opnd2 in
    let sh = (6 >< 5) opnd2
    and rm = REG_READ t (INC_PC t reg) mode Rm
    and shift = (7 >< 0) (REG_READ t reg mode Rs) in
      SHIFT_REGISTER2 shift sh rm C`;

val ADDR_MODE1_def = Define`
  ADDR_MODE1 reg t mode C Im opnd2 =
    if Im then
      IMMEDIATE C opnd2
    else if opnd2 ' 4 then
      SHIFT_REGISTER reg t mode C opnd2
    else
      SHIFT_IMMEDIATE reg t mode C opnd2`;

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val ALU_arith_def = Define`
  ALU_arith op (rn:word32) (op2:word32) =
    let sign  = word_msb rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n op2)) in
    let res   = (n2w r):word32 in
      ((word_msb res,r = 0,ODD q,
        (word_msb op2 = sign) /\ ~(word_msb res = sign)),res)`;

val ALU_logic_def = Define`
  ALU_logic (res:word32) = ((word_msb res,res = 0w,F,F),res)`;

val ADD_def = Define`
  ADD a b c = ALU_arith (\x y.x+y+(if c then 1 else 0)) a b`;

val SUB_def = Define`SUB a b c = ADD a (~b) c`;

val AND_def = Define`AND a b = ALU_logic (a && b)`;
val EOR_def = Define`EOR a b = ALU_logic (a ?? b)`;
val ORR_def = Define`ORR a b = ALU_logic (a !! b)`;

val ALU_def = Define`
  ALU (opc:word4) rn op2 c =
    case opc of
       0w  -> AND rn op2
    || 1w  -> EOR rn op2
    || 2w  -> SUB rn op2 T
    || 4w  -> ADD rn op2 F
    || 3w  -> SUB op2 rn T
    || 5w  -> ADD rn op2 c
    || 6w  -> SUB rn op2 c
    || 7w  -> SUB op2 rn c
    || 8w  -> AND rn op2
    || 9w  -> EOR rn op2
    || 10w -> SUB rn op2 T
    || 11w -> ADD rn op2 F
    || 12w -> ORR rn op2
    || 13w -> ALU_logic op2
    || 14w -> AND rn (~op2)
    || _   -> ALU_logic (~op2)`;

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val ARITHMETIC_def = Define`
  ARITHMETIC (opcode:word4) =
    (opcode ' 2 \/ opcode ' 1) /\ (~(opcode ' 3) \/ ~(opcode ' 2))`;

val TEST_OR_COMP_def = Define`
  TEST_OR_COMP (opcode:word4) = ((3 -- 2 ) opcode = 2w)`;

val DECODE_DATAP_def = Define`
  DECODE_DATAP (w:word32) =
    (w ' 25,(24 >< 21) w,w ' 20,(19 >< 16) w,(15 >< 12) w,(11 >< 0) w)`;

val DATA_PROCESSING_def = Define`
  DATA_PROCESSING r t C mode ireg =
    let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP ireg in
    let (C_s,op2) = ADDR_MODE1 r.reg t mode C I opnd2
    and pc_reg = INC_PC t r.reg in
    let rn = REG_READ t (if ~I /\ (opnd2 ' 4) then pc_reg else r.reg) mode Rn
    in
    let ((N,Z,C_alu,V),res) = ALU opcode rn op2 C
    and tc = TEST_OR_COMP opcode in
      <| reg := if tc then pc_reg else REG_WRITE pc_reg mode Rd res;
         psr := if S then
                  CPSR_WRITE r.psr
                    (if (Rd = 15w) /\ ~tc then SPSR_READ r.psr mode
                         else (if ARITHMETIC opcode
                                 then SET_NZCV (N,Z,C_alu,V)
                                 else SET_NZC  (N,Z,C_s)) (CPSR_READ r.psr))
                else r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* The PSR Transfer instruction class (mrs and msr)                          *)
(* ------------------------------------------------------------------------- *)

val DECODE_MRS_def = Define `DECODE_MRS (w:word32) = (w ' 22,(15 >< 12) w)`;

val MRS_def = Define`
  MRS r mode ireg =
    let (R,Rd) = DECODE_MRS ireg in
    let word = if R then SPSR_READ r.psr mode else CPSR_READ r.psr in
      <| reg := REG_WRITE (INC_PC F r.reg) mode Rd word; psr := r.psr |>`;

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val DECODE_MSR_def = Define`
  DECODE_MSR (w:word32) =
    (w ' 25,w ' 22,w ' 19,w ' 16,(3 >< 0) w,(11 >< 0) w)`;

val MSR_def = Define`
  MSR r mode ireg =
    let (I,R,bit19,bit16,Rm,opnd) = DECODE_MSR ireg in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      <| reg := INC_PC F r.reg; psr := r.psr |>
    else
      let psrd = if R then SPSR_READ r.psr mode else CPSR_READ r.psr
      and  src = if I then SND (IMMEDIATE F opnd) else REG_READ F r.reg mode Rm
      in
      let psrd' = word_modify
             (\i b. (28 <= i) /\ (if bit19 then src ' i else b) \/
                    (8 <= i) /\ (i <= 27) /\ b \/
                    (i <= 7) /\ (if bit16 /\ ~USER mode then src ' i else b))
             psrd
      in
        <| reg := INC_PC F r.reg;
           psr := if R then
                    SPSR_WRITE r.psr mode psrd'
                  else
                    CPSR_WRITE r.psr psrd' |>`;

(* ------------------------------------------------------------------------- *)
(* The Multiply instruction class (mla_mul)                                  *)
(* ------------------------------------------------------------------------- *)

val ALU_multiply_def = Define`
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
        (word_msb resLo,resLo = 0w,rd,resLo)`;

val DECODE_MLA_MUL_def = Define`
  DECODE_MLA_MUL (w:word32) = (w ' 23,w ' 22,w ' 21,w ' 20,
    (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,(3 >< 0) w)`;

val MLA_MUL_def = Define`
  MLA_MUL r t mode ireg =
    let (L,Sgn,A,S,Rd,Rn,Rs,Rm) = DECODE_MLA_MUL ireg in
    let pc_reg = INC_PC t r.reg in
    let rd = REG_READ t r.reg mode Rd
    and rn = REG_READ t r.reg mode Rn
    and rs = REG_READ t r.reg mode Rs
    and rm = REG_READ t r.reg mode Rm in
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
                    r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* The Single Data Transfer instruction class (ldr_str)                      *)
(* ------------------------------------------------------------------------- *)

val UP_DOWN_def = Define`UP_DOWN u = if u then $word_add else $word_sub`;

val ADDR_MODE2_def = Define`
  ADDR_MODE2 reg t mode C Im P U Rn offset =
    let addr = REG_READ t reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then SND (SHIFT_IMMEDIATE reg t mode C offset)
                 else w2w offset) in
      (if P then wb_addr else addr,wb_addr)`;

val DECODE_LDR_STR_def = Define`
  DECODE_LDR_STR (w:word32) =
     (w ' 25,w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
      (19 >< 16) w,(15 >< 12) w,(11 >< 0) w)`;

val LDR_STR_def = Define`
  LDR_STR r t C mode ireg input =
    let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
    let (addr,wb_addr) = ADDR_MODE2 r.reg t mode C I P U Rn offset in
    let pc_reg = INC_PC t r.reg in
      case input of
         NONE -> INL (MemAccess (\n_ldc cp_data.
           [if L then
              MemRead addr
            else
              let w = REG_READ t pc_reg mode Rd in
                MemWrite addr (if B then Byte ((7 >< 0) w) else Word w)]))
      || SOME (isdabort, data) ->
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
                psr := r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* Half Word Single Data Transfer instruction class (ldrh_strh)              *)
(* ------------------------------------------------------------------------- *)

val ADDR_MODE3_def = Define`
  ADDR_MODE3 reg t mode Im P U Rn (offsetH:word4) offsetL =
    let addr = REG_READ t reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then offsetH @@ offsetL
                 else REG_READ t reg mode offsetL) in
      (if P then wb_addr else addr,wb_addr)`;

val DECODE_LDRH_STRH_def = Define`
  DECODE_LDRH_STRH (w:word32) =
     (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
      (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,w ' 6,w ' 5,(3 >< 0) w)`;

val LDRH_STRH_def = Define`
  LDRH_STRH r t mode ireg input =
    let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
    let (addr,wb_addr) = ADDR_MODE3 r.reg t mode I P U Rn offsetH offsetL in
    let pc_reg = INC_PC t r.reg in
      case input of
         NONE -> INL (MemAccess (\n_ldc cp_data.
           [if L then
              MemRead addr
            else
              MemWrite addr (Half ((15 >< 0) (REG_READ t pc_reg mode Rd)))]))
      || SOME (isdabort, data) ->
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
                                (F,T) -> UnsignedHalfWord
                             || (T,F) -> SignedByte
                             || (T,T) -> SignedHalfWord
                             || _ -> ARB
                   in
                     REG_WRITE wb_reg mode Rd
                       (FORMAT fmt ((1 >< 0) addr) (HD data));
                psr := r.psr |>`;

(* ------------------------------------------------------------------------- *)
(*  The Block Data Transfer instruction class (ldm_stm)                      *)
(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_def = Define`
  REGISTER_LIST (list:word16) =
    (MAP SND o FILTER FST) (GENLIST (\i. (list ' i,(n2w i):word4)) 16)`;

val ADDRESS_LIST_def = Define`
  ADDRESS_LIST (start:word32) n = GENLIST (\i. start + 4w * n2w i) n`;

val WB_ADDRESS_def = Define`
  WB_ADDRESS U base len = UP_DOWN U base (n2w (4 * len):word32)`;

val FIRST_ADDRESS_def = Define`
  FIRST_ADDRESS P U (base:word32) wb =
    if U then if P then base + 4w else base
         else if P then wb else wb + 4w`;

val ADDR_MODE4_def = Define`
  ADDR_MODE4 P U base (list:word16) =
    let rp_list = REGISTER_LIST list in
    let len = LENGTH rp_list in
    let wb = WB_ADDRESS U base len in
    let addr_list = ADDRESS_LIST (FIRST_ADDRESS P U base wb) len in
      (rp_list,addr_list,wb)`;

val LDM_LIST_def = Define`
  LDM_LIST reg mode rp_list data =
    FOLDL (\reg' (rp,rd). REG_WRITE reg' mode rp rd) reg (ZIP (rp_list,data))`;

val STM_LIST_def = Define `STM_LIST = MAP (\(a, d). MemWrite a (Word d))`;

val STM_DATA_def = Define`
  STM_DATA reg t mode rp_list = MAP (\rp. REG_READ t reg mode rp) rp_list`;

val DECODE_LDM_STM_def = Define`
  DECODE_LDM_STM (w:word32) =
    (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,(19 >< 16) w,(15 >< 0) w)`;

val LDM_STM_def = Define`
  LDM_STM r t mode ireg input =
    let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
    let pc_in_list = list ' 15
    and rn = REG_READ t r.reg mode Rn in
    let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list
    and mode' = if S /\ (L ==> ~pc_in_list) then usr else mode
    and pc_reg = INC_PC t r.reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg (if L then mode else mode') Rn rn'
                 else
                   pc_reg
    in
      case input of
         NONE -> INL (MemAccess (\n_ldc cp_data.
          (if L then
             MAP MemRead addr_list
           else
             STM_LIST (ZIP (addr_list,
               STM_DATA (if HD rp_list = Rn then pc_reg else wb_reg) t mode'
                 rp_list)))))
      || SOME (dabort_n, data) -> INR
          (if L then
             <| reg :=
                  let n = if IS_SOME dabort_n then
                            THE dabort_n
                          else
                            LENGTH rp_list in
                  let ldm_reg = LDM_LIST wb_reg mode' (FIRSTN n rp_list)
                                  (FIRSTN n data) in
                    if IS_SOME dabort_n /\ ~(Rn = 15w) then
                      REG_WRITE ldm_reg mode' Rn (REG_READ t wb_reg mode' Rn)
                    else ldm_reg;
                 psr := if S /\ pc_in_list /\ IS_NONE dabort_n then
                          CPSR_WRITE r.psr (SPSR_READ r.psr mode)
                        else r.psr |>
           else <| reg := wb_reg; psr := r.psr |>)`;

(* ------------------------------------------------------------------------- *)
(* The Single Data Swap instruction class (swp)                              *)
(* ------------------------------------------------------------------------- *)

val DECODE_SWP_def = Define`
  DECODE_SWP (w:word32) = (w ' 22,(19 >< 16) w,(15 >< 12) w,(3 >< 0) w)`;

val SWP_def = Define`
  SWP r mode ireg input =
    let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
    let rn = REG_READ F r.reg mode Rn
    and pc_reg = INC_PC F r.reg in
    let rm = REG_READ F pc_reg mode Rm in
      case input of
         NONE -> INL (MemAccess (\n_ldc cp_data.
           [MemRead rn;
            MemWrite rn (if B then Byte ((7 >< 0) rm) else Word rm)]))
      || SOME (isdabort, data) -> INR
          <| reg :=
                if isdabort then
                  pc_reg
                else let fmt = if B then UnsignedByte else UnsignedWord in
                  REG_WRITE pc_reg mode Rd
                    (FORMAT fmt ((1 ><  0) rn) (HD data));
              psr := r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* Coprocessor Register Transfer (mrc, mcr)                                  *)
(* ------------------------------------------------------------------------- *)

val DECODE_MRC_MCR_def = Define`
  DECODE_MRC_MCR (w:word32) =
    ((23 >< 21) w,(19 >< 16) w,(15 >< 12) w,
     (11 >< 8) w, (7 >< 5) w,(3 >< 0) w)`;

val MRC_def = Define`
  MRC r mode data ireg =
    let Rd = (15 >< 12) ireg
    and pc_reg = INC_PC F r.reg in
      if Rd = 15w then
        <| reg := pc_reg;
           psr := CPSR_WRITE r.psr (SET_NZCV (NZCV data) (CPSR_READ r.psr)) |>
      else
        <| reg := REG_WRITE pc_reg mode Rd data; psr := r.psr |>`;

val MCR_def = Define`
  MCR reg mode ireg =
    let Rd = (15 >< 12) ireg in
      CPWrite (REG_READ F (INC_PC F reg) mode Rd)`;

(* ------------------------------------------------------------------------- *)
(* Coprocessor Data Transfers (ldc_stc)                                      *)
(* ------------------------------------------------------------------------- *)

val DECODE_LDC_STC_def = Define`
  DECODE_LDC_STC (w:word32) =
    (w ' 24,w ' 23,w ' 22,w ' 21,w ' 20,
     (19 >< 16) w,(15 >< 12) w,(11 >< 8) w,(7 >< 0) w)`;

val ADDR_MODE5_def = Define`
  ADDR_MODE5 reg mode P U Rn (offset:word8) =
    let addr = REG_READ F reg mode Rn in
    let wb_addr = UP_DOWN U addr (w2w offset << 2) in
      (if P then wb_addr else addr,wb_addr)`;

val LDC_STC_def = Define`
  LDC_STC r mode ireg input =
    let (P,U,N,W,L,Rn,CRd,CPN,offset) = DECODE_LDC_STC ireg in
    let (addr,wb_addr) = ADDR_MODE5 r.reg mode P U Rn offset in
      if input then
        let pc_reg = INC_PC F r.reg in
        let wb_reg = if W /\ ~(Rn = 15w) then
                       REG_WRITE pc_reg mode Rn wb_addr
                     else
                       pc_reg
        in
          INR <| reg := wb_reg; psr := r.psr |>
      else
          INL (MemAccess (\n_ldc cp_data.
            if L then
              MAP MemRead (ADDRESS_LIST addr n_ldc)
            else
              STM_LIST (ZIP (ADDRESS_LIST addr (LENGTH cp_data), cp_data))))`;

(* ------------------------------------------------------------------------- *)
(* Predicate for conditional execution                                       *)
(* ------------------------------------------------------------------------- *)

val CONDITION_PASSED2_def = Define`
  CONDITION_PASSED2 (N,Z,C,V) cond =
    case cond of
       EQ -> Z
    || NE -> ~Z
    || CS -> C
    || CC -> ~C
    || MI -> N
    || PL -> ~N
    || VS -> V
    || VC -> ~V
    || HI -> C /\ ~Z
    || LS -> ~C \/ Z
    || GE -> N = V
    || LT -> ~(N = V)
    || GT -> ~Z /\ (N = V)
    || LE -> Z \/ ~(N = V)
    || AL -> T
    || NV -> F`;

val CONDITION_PASSED_def = Define`
  CONDITION_PASSED flags (ireg:word32) =
    let pass = CONDITION_PASSED2 flags (num2condition (w2n ((31 -- 29) ireg)))
    in
      if ireg ' 28 then ~pass else pass`;

(* ------------------------------------------------------------------------- *)
(* THUMB_TO_ARM                                                              *)
(* Maps a 16-bit Thumb instruction to its 32-bit ARM equivalent              *)
(*---------------------------------------------------------------------------*)

val THUMB_TO_ARM_def = Define`
  THUMB_TO_ARM (ireg:word16) =
    let b n = ireg ' n in
      case (b 15,b 14,b 13,b 12,b 11,b 10,b 9,b 8) of
         (F,F,F, T , T , F ,_9,_8) ->
(* SUB(3), ADD(3) *)
            (if _9 then 0xE0500000w else 0xE0900000w) !!
            (5 >< 3) ireg << 16 !! (2 >< 0) ireg << 12 !! (8 >< 6) ireg
      || (F,F,F, T , T , T ,_9,_8) ->
(* SUB(1), ADD(1) *)
            (if _9 then 0xE2500000w else 0xE2900000w) !!
            (5 >< 3) ireg << 16 !! (2 >< 0) ireg << 12 !! (8 >< 6) ireg
      || (F,F,F,_12,_11,_10,_9,_8) ->
           (case (_12,_11) of
(* LSL(1) *)    (F,F) -> 0xE1B00000w
(* LSR(1) *) || (F,T) -> 0xE1B00020w
(* ASR(1) *) || (T,F) -> 0xE1B00040w
             || (T,T) -> ARB) !!
             (2 >< 0) ireg << 12 !!(10 >< 6) ireg << 7 !! (5 >< 3) ireg
      || (F,F,T,_12,_11,_10,_9,_8) ->
         (let Rd = (10 >< 8) ireg in
            (case (_12,_11) of
(* MOV(1) *)    (F,F) -> 0xE3B00000w !! Rd << 12
(* CMP(1) *) || (F,T) -> 0xE3500000w !! Rd << 16
(* ADD(2) *) || (T,F) -> 0xE2900000w !! Rd << 16 !! Rd << 12
(* SUB(2) *) || (T,T) -> 0xE2500000w !! Rd << 16 !! Rd << 12) !! (7 >< 0) ireg)
      || (F,T,F, F , F , F ,_9,_8) ->
         (let Rm = (5 >< 3) ireg and Rd = (2 >< 0) ireg in
             case (_9,_8,b 7,b 6) of
(* AND    *)    (F,F,F,F) -> 0xE0100000w !! Rd << 16 !! Rd << 12 !! Rm
(* EOR    *) || (F,F,F,T) -> 0xE0300000w !! Rd << 16 !! Rd << 12 !! Rm
(* LSL(2) *) || (F,F,T,F) -> 0xE1B00010w !! Rd << 12 !! Rm << 8 !! Rd
(* LSR(2) *) || (F,F,T,T) -> 0xE1B00030w !! Rd << 12 !! Rm << 8 !! Rd
(* ASR(2) *) || (F,T,F,F) -> 0xE1B00050w !! Rd << 12 !! Rm << 8 !! Rd
(* ADC    *) || (F,T,F,T) -> 0xE0B00000w !! Rd << 16 !! Rd << 12 !! Rm
(* SBC    *) || (F,T,T,F) -> 0xE0D00000w !! Rd << 16 !! Rd << 12 !! Rm
(* ROR    *) || (F,T,T,T) -> 0xE1B00070w !! Rd << 12 !! Rm << 8 !! Rd
(* TST    *) || (T,F,F,F) -> 0xE1100000w !! Rd << 16 !! Rm
(* NEG    *) || (T,F,F,T) -> 0xE2700000w !! Rm << 16 !! Rd << 12
(* CMP(2) *) || (T,F,T,F) -> 0xE1500000w !! Rd << 16 !! Rm
(* CMN    *) || (T,F,T,T) -> 0xE1700000w !! Rd << 16 !! Rm
(* ORR    *) || (T,T,F,F) -> 0xE1900000w !! Rd << 16 !! Rd << 12 !! Rm
(* MUL    *) || (T,T,F,T) -> 0xE0100090w !! Rd << 16 !! Rd << 8 !! Rm
(* BIC    *) || (T,T,T,F) -> 0xE1D00000w !! Rd << 16 !! Rd << 12 !! Rm
(* MVN    *) || (T,T,T,T) -> 0xE1F00000w !! Rd << 12 !! Rm)
      || (F,T,F, F , F , T , T, T) ->
(* BX, UND .. v5 -> BLX(2) .. *)
            if b 7 then
              0xE6000010w (* v5 -> 0xE1200030w !! ... *)
            else
              0xE1200010w !! (6 >< 3) ireg
      || (F,T,F, F , F , T ,_9,_8) ->
          ((let Rd = (2 >< 0) ireg and H1 = (7 >< 7) ireg in
             case (_9,_8) of
(* ADD(4) *)    (F,F) -> 0xE0800000w !! H1 << 19 !! Rd << 16 !!
                                        H1 << 15 !! Rd << 12 
(* CMP(3) *) || (F,T) -> 0xE1500000w !! H1 << 19 !! Rd << 16
(* MOV(3) *) || (T,F) -> 0xE1A00000w !! H1 << 15 !! Rd << 12
             || (T,T) -> ARB) !! (6 >< 6) ireg << 3 !! (5 >< 3) ireg)
      || (F,T,F, F , T ,_10,_9,_8) ->
(* LDR(3) *) 0xE59F0000w !! (10 >< 8) ireg << 12 !! (7 >< 0) ireg << 2
      || (F,T,F, T ,_11,_10,_9,_8) ->
            (case (_11,_10,_9) of
(* STR(2)  *)   (F,F,F) -> 0xE7800000w
(* STRH(2) *)|| (F,F,T) -> 0xE18000B0w
(* STRB(2) *)|| (F,T,F) -> 0xE7C00000w
(* LDRSB   *)|| (F,T,T) -> 0xE19000D0w
(* LDR(2)  *)|| (T,F,F) -> 0xE7900000w
(* LDRH(2) *)|| (T,F,T) -> 0xE19000B0w
(* LDRB(2) *)|| (T,T,F) -> 0xE7D00000w
(* LDRSH   *)|| (T,T,T) -> 0xE19000F0w) !!
            (5 >< 3) ireg << 16 !! (2 >< 0) ireg << 12 !! (8 >< 6) ireg
      || (F,T,T,_12,_11,_10,_9,_8) ->
           (case (_12,_11) of
(* STR(1)  *)   (F,F) -> 0xE5800000w !! (10 >< 6) ireg << 2
(* LDR(1)  *)|| (F,T) -> 0xE5900000w !! (10 >< 6) ireg << 2
(* STRB(1) *)|| (T,F) -> 0xE5C00000w !! (10 >< 6) ireg
(* LDRB(1) *)|| (T,T) -> 0xE5D00000w !! (10 >< 6) ireg) !!
            (5 >< 3) ireg << 16 !! (2 >< 0) ireg << 12
      || (T,F,F, F ,_11,_10,_9,_8) ->
(* LDRH(1), STRH(1) *)
            (if _11 then 0xE1D000B0w else 0xE1C000B0w) !!
            (5 >< 3) ireg << 16 !! (2 >< 0) ireg << 12 !!
            (10 >< 9) ireg << 8 !! (8 >< 6) ireg << 1
      || (T,F,F, T ,_11,_10,_9,_8) ->
(* LDR(4), STR(3) *)
            (if _11 then 0xE59D0000w else 0xE58D0000w) !!
            (10 >< 8) ireg << 12 !! (7 >< 0) ireg << 2
      || (T,F,T, F ,_11,_10,_9,_8) ->
(* ADD(6), ADD(5) *)
            (if _11 then 0xE28D0F00w else 0xE28F0F00w) !!
            (10 >< 8) ireg << 12 !! (7 >< 0) ireg
      || (T,F,T, T , F , F , F, F) ->
(* ADD(7), SUB(4) *)
            (if b 7 then 0xE24DDF00w else 0xE28DDF00w) !! (6 >< 0) ireg
      || (T,F,T, T ,_11, T , F,_8) ->
(* POP, PUSH *)
            (if _11 then
               0xE8BD0000w !! (8 >< 8) ireg << 15
             else
               0xE92D0000w !! (8 >< 8) ireg << 14) !! (7 >< 0) ireg
      || (T,F,T, T , T , T , T, F) ->
(* UND .. v5 -> BKPT .. *)
            0xE6000010w
      || (T,T,F, F ,_11,_10,_9,_8) ->
(* LDMIA, STMIA *)
           (let Rn = (10 >< 8) ireg in
              (21 :+ (_11 ==> ~(ireg ' (w2n Rn))))
              ((if _11 then 0xE8900000w else 0xE8A00000w) !!
              Rn << 16 !! (7 >< 0) ireg))
      || (T,T,F, T , T , T , T, F) -> 
(* UND *)   0xE6000010w
      || (T,T,F, T , T , T , T, T) ->
(* SWI *)   0xEF000000w !! (7 >< 0) ireg
      || (T,T,F, T ,_11,_10,_9,_8) ->
(* B(1) *)  (11 >< 8) ireg << 28 !! 0xA000000w !!
            w2w ((sw2sw:word8->word24) ((7 >< 0) ireg))
      || (T,T,T, F , F ,_10,_9,_8) ->
(* B(2) *)  0xEA000000w !! w2w ((sw2sw:11 word->word24) ((10 >< 0) ireg))
      || (T,T,T, F , T ,_10,_9,_8) ->
(* UND .. v5 + BLX(1) .. *)
            0xE6000010w
      || (T,T,T, T , F ,_10,_9,_8) ->
(* BL (pt. 1) *)
           (let offset = (10 >< 0) ireg in
              if offset = 0w then
                0xE1A0E00Fw
              else
                0xEB000000w !! w2w (sw2sw offset :word24 << 11))
      || (T,T,T, T , T ,_10,_9,_8) ->
(* BL (pt. 2) *)
            0xEB000000w !! (10 >< 0) ireg
      || _ -> 0xE6000010w:word32`;

(* ------------------------------------------------------------------------- *)
(* Top-level decode and run functions                                        *)
(* ------------------------------------------------------------------------- *)

val DECODE_ARM_def = Define`
  DECODE_ARM (ireg : word32) =
    let b n = ireg ' n in
      case (b 27,b 26,b 25,b 24,b 23,b 22,b 21,b 20,b 7,b 6,b 5,b 4) of
         (F,F,F, T , F ,_22,b21, F , F, F, F, F) -> if b21 then msr else mrs
      || (F,F,F, T , F , F , T , F , F, F, F, T) -> bx
      || (F,F,F,_24,_23,_22,_21,_20,_7,_6,_5, F) -> data_proc
      || (F,F,F,_24,_23,_22,_21,_20, F,_6,_5, T) -> data_proc
      || (F,F,F, F , F , F ,_21,_20, T, F, F, T) -> mla_mul
      || (F,F,F, F , T ,_22,_21,_20, T, F, F, T) -> mla_mul
      || (F,F,F, T , F ,_22, F , F , T, F, F, T) -> swp
      || (F,F,F,_24,_23,_22,_21, L , T, F, T, T) -> ldrh_strh
      || (F,F,F,_24,_23,_22,_21, T , T, T,_5, T) -> ldrh_strh
      || (F,F,T, T , F ,_22, F , F ,_7,_6,_5,_4) -> cdp_und
      || (F,F,T, T , F ,_22, T , F ,_7,_6,_5,_4) -> msr
      || (F,F,T,_24,_23,_22,_21,_20,_7,_6,_5,_4) -> data_proc
      || (F,T,F,_24,_23,_22,_21, L ,_7,_6,_5,_4) -> ldr_str
      || (F,T,T,_24,_23,_22,_21, L ,_7,_6,_5, F) -> ldr_str
      || (T,F,F,_24,_23,_22,_21, L ,_7,_6,_5,_4) -> ldm_stm
      || (T,F,T,_24,_23,_22,_21,_20,_7,_6,_5,_4) -> br
      || (T,T,F,_24,_23,_22,_21, L ,_7,_6,_5,_4) -> ldc_stc
      || (T,T,T, F ,_23,_22,_21, T ,_7,_6,_5, T) -> mrc
      || (T,T,T, F ,_23,_22,_21, F ,_7,_6,_5, T) -> mcr
      || (T,T,T, T ,_23,_22,_21,_20,_7,_6,_5,_4) -> swi_ex
      || __ -> cdp_und`;

val RUN_ARM_def = Define`
  RUN_ARM (state,inp) =
    let r = state.regs in
    let (nzcv,i,f,t,m) = DECODE_PSR (CPSR_READ r.psr) in
      if ~(state.exception = software) then
        EXCEPTION r t state.exception
      else
        let ireg = if t then THUMB_TO_ARM ((15 >< 0) inp.ireg) else inp.ireg
        and inc_pc x = <| reg := INC_PC t x.reg; psr := x.psr |> in
          if ~CONDITION_PASSED nzcv ireg then
            inc_pc r
          else let mode = DECODE_MODE m
               and coproc f = if inp.absent then r else f r
               and dabt = inp.interrupts.Dabort
               and data = inp.data
          in
            case DECODE_ARM ireg of
               data_proc -> DATA_PROCESSING r t (CARRY nzcv) mode ireg
            || mla_mul   -> MLA_MUL r t mode ireg
            || swi_ex    -> EXCEPTION r t software
            || br        -> BRANCH r t mode ireg
            || bx        -> BRANCH_EXCHANGE r t mode ireg
            || msr       -> MSR r mode ireg
            || mrs       -> MRS r mode ireg
            || swp       -> OUTR (SWP r mode ireg (SOME (IS_SOME dabt, data)))
            || ldm_stm   -> OUTR (LDM_STM r t mode ireg (SOME (dabt, data)))
            || ldr_str   -> OUTR (LDR_STR r t (CARRY nzcv) mode ireg
                                    (SOME (IS_SOME dabt, data)))
            || ldrh_strh -> OUTR
                 (LDRH_STRH r t mode ireg (SOME (IS_SOME dabt, data)))
            || ldc_stc   -> coproc (\x. (OUTR (LDC_STC x mode ireg T)))
            || mrc       -> coproc (\x. MRC x mode (HD data) ireg)
            || mcr       -> coproc inc_pc
            || cdp_und   -> coproc inc_pc
            || _ -> r`;

(* ------------------------------------------------------------------------- *)
(* Exception operations                                                      *)
(* ------------------------------------------------------------------------- *)

val interrupt2exception_def = Define`
  interrupt2exception (state,inp) cpsr' =
    let (flags,i,f,t,m) = DECODE_PSR (CPSR_READ state.regs.psr)
    and (flags',i',f',t',m') = DECODE_PSR cpsr' in
    let ireg = if t then THUMB_TO_ARM ((15 >< 0) inp.ireg) else inp.ireg in
    let pass = (state.exception = software) /\ CONDITION_PASSED flags ireg
    and ic = DECODE_ARM ireg in
    let old_flags = pass /\ ((ic = mrs) \/ (ic = msr))
    and irpt = inp.interrupts in
      if IS_SOME irpt.Reset then
        reset
      else if IS_SOME irpt.Dabort then
        dabort
      else if irpt.Fiq /\ ~(if old_flags then f else f') then
        fast
      else if irpt.Irq /\ ~(if old_flags then i else i') then
        interrupt
      else if irpt.Prefetch then
        pabort
      else if pass /\ ic IN {cdp_und; mrc; mcr; ldc_stc} /\ inp.absent then
        undefined
      else
        software`;

(* ------------------------------------------------------------------------- *)
(* The next state, output and state functions                                *)
(* ------------------------------------------------------------------------- *)

val NEXT_ARM_def = Define`
  NEXT_ARM (state,inp) =
    let r = case inp.interrupts.Reset of
               SOME x -> x
            || NONE -> RUN_ARM (state,inp)
    in
      <| regs := r;
         exception := interrupt2exception (state,inp) (CPSR_READ r.psr) |>`;

val NoTransfers_def = Define `NoTransfers = MemAccess (\x y. [])`;

val OUT_ARM_def = Define`
  OUT_ARM (state, x) =
   let r = state.regs in
   let (nzcv,i,f,t,m) = DECODE_PSR (CPSR_READ r.psr) in
   let mode = DECODE_MODE m in
     case x of
        NONE -> <| transfers := NoTransfers; cpi := F; user := USER mode |>
     || SOME n ->
        let ireg = if t then THUMB_TO_ARM ((15 >< 0) n) else n in
          if (state.exception = software) /\ CONDITION_PASSED nzcv ireg then
            let ic = DECODE_ARM ireg in
              <| transfers := 
                 (case ic of
                     ldr_str   -> OUTL (LDR_STR r t (CARRY nzcv) mode ireg NONE)
                  || ldrh_strh -> OUTL (LDRH_STRH r t mode ireg NONE)
                  || ldm_stm   -> OUTL (LDM_STM r t mode ireg NONE)
                  || swp       -> OUTL (SWP r mode ireg NONE)
                  || ldc_stc   -> OUTL (LDC_STC r mode ireg F)
                  || mcr       -> MCR r.reg mode ireg
                  || _         -> NoTransfers);
                 cpi := (ic IN {cdp_und; mcr; mrc; ldc_stc});
                 user := USER mode
              |>
          else
             <| transfers := NoTransfers; cpi := F; user := USER mode |>`;

(* The output upon receiving a reset signal will actually be a prefix of     *)
(* the "normal" output.  However, as a simplifying mechanism, this is        *)
(* handled with the x = NONE case.                                           *)
(* In the ARM6 verification, the ISA reset output is accepted as "correct".  *)

(* ------------------------------------------------------------------------- *)

val _ = let open pred_setTheory in
  computeLib.add_persistent_funs
  ([("pred_setTheory.IN_INSERT", IN_INSERT),
    ("pred_setTheory.NOT_IN_EMPTY", NOT_IN_EMPTY)] @
  map (fn s => (s, theorem s))
  ["register_EQ_register","num2register_thm","register2num_thm", "mode_EQ_mode",
   "mode2num_thm", "psr_EQ_psr", "psr2num_thm", "iclass_EQ_iclass",
   "iclass2num_thm", "num2condition_thm", "condition2num_thm",
   "exceptions_EQ_exceptions", "num2exceptions_thm", "exceptions2num_thm"])
end;

val _ = export_theory();
