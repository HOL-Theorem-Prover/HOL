(* ========================================================================= *)
(* FILE          : armScript.sml                                             *)
(* DESCRIPTION   : Model of the ARM instruction set architecture             *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2006                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "rich_listTheory", "bsubstTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q wordsTheory rich_listTheory bsubstTheory;

val _ = new_theory "arm";

(* ------------------------------------------------------------------------- *)
(*  The ARM State Space                                                      *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `state_inp = <| state : 'a; inp : num -> 'b |>`;
val _ = Hol_datatype `state_out = <| state : 'a; out : 'b |>`;

val register_decl = `register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;

val psr_decl =
  `psr = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und`;

val exceptions_decl =
  `exceptions = reset | undefined | software | pabort |
                dabort | address |interrupt | fast`;

val _ = map Hol_datatype [register_decl, psr_decl, exceptions_decl];

val _ = type_abbrev("registers", ``:register->word32``);
val _ = type_abbrev("psrs",      ``:psr->word32``);

val _ = Hol_datatype `regs = <| reg : registers; psr : psrs |>`;

val _ = Hol_datatype
  `arm_state = <| regs : regs; ireg : word32; exception : exceptions |>`;

(* ......................................................................... *)

val _ = Hol_datatype`
  memop = MemRead of word32 | MemWrite of word32=>data | CPWrite of word32`;

val _ = Hol_datatype`
  interrupt = Reset of regs | Undef | Prefetch | Dabort of num | Fiq | Irq`;

val _ = Hol_datatype`
  arm_input = <| ireg : word32; data : word32 list;
                 interrupt : interrupt option; no_cp : bool |>`;

val mode_decl = `mode = usr | fiq | irq | svc | abt | und | sys | safe`;

val condition_decl =
  `condition = EQ | CS | MI | VS | HI | GE | GT | AL |
               NE | CC | PL | VC | LS | LT | LE | NV`;

val iclass_decl =
  `iclass = swp | mrs | msr | data_proc | mla_mul |
            ldr_str | ldrh_strh | ldm_stm | br | swi_ex | cdp_und |
            mcr | mrc | ldc_stc | unexec`;

val _ = map Hol_datatype [mode_decl, condition_decl, iclass_decl];

(* ------------------------------------------------------------------------- *)
(*  General Purpose Register operations                                      *)
(* ------------------------------------------------------------------------- *)

val Rg = inst [alpha |-> ``:i32``,beta |-> ``:i4``] wordsSyntax.word_extract_tm;

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
  REG_READ (reg:registers) m n =
    if n = 15w then
      reg r15 + 8w
    else
      reg (num2register (mode_reg2num m n))`;

val REG_WRITE_def = Define`
  REG_WRITE (reg:registers) m n d =
    (num2register (mode_reg2num m n) :- d) reg`;

val INC_PC_def   = Define `INC_PC (reg:registers) = (r15 :- reg r15 + 4w) reg`;
val FETCH_PC_def = Define `FETCH_PC (reg:registers) = reg r15`;

(*  FETCH_PC is needed because (REG_READ reg usr 15w) gives PC + 8.          *)

(* ------------------------------------------------------------------------- *)
(*  Program Status Register operations                                       *)
(* ------------------------------------------------------------------------- *)

val SET_NZCV_def = Define`
  SET_NZCV (N,Z,C,V) w:word32 =
    word_modify (\i b. (i = 31) /\ N \/ (i = 30) /\ Z \/
                       (i = 29) /\ C \/ (i = 28) /\ V \/
                       (i < 28) /\ b) w`;

val SET_NZC_def = Define `SET_NZC (N,Z,C) w = SET_NZCV (N,Z,C,w %% 28) w`;
val SET_NZ_def  = Define `SET_NZ (N,Z) w = SET_NZC (N,Z,w %% 29) w`;

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

val SET_IFMODE_def = Define`
  SET_IFMODE irq' fiq' mode w:word32 =
     word_modify (\i b. (7 < i \/ (i = 5)) /\ b \/
                        (i = 7) /\ irq' \/ (i = 6) /\ fiq' \/
                        (i < 5) /\ (mode_num mode) %% i) w`;

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

val NZCV_def = Define `NZCV (w:word32) = (w %% 31, w %% 30, w %% 29, w %% 28)`;

val DECODE_PSR_def = Define`
  DECODE_PSR (cpsr:word32) =
    (NZCV cpsr, cpsr %% 7, cpsr %% 6, ((4 >< 0) cpsr):word5)`;

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
  CPSR_WRITE (psr:psrs) cpsr = (CPSR :- cpsr) psr`;

val SPSR_WRITE_def = Define`
  SPSR_WRITE (psr:psrs) mode spsr =
    if USER mode then psr else (mode2psr mode :- spsr) psr`;

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
  EXCEPTION r type =
    let cpsr = CPSR_READ r.psr in
    let fiq' = ((type = reset) \/ (type = fast)) \/ cpsr %% 6
    and mode' = exception2mode type
    and pc = n2w (4 * exceptions2num type):word32 in
    let reg' = REG_WRITE r.reg mode' 14w (FETCH_PC r.reg + 4w) in
      <| reg := REG_WRITE reg' usr 15w pc;
         psr := CPSR_WRITE (SPSR_WRITE r.psr mode' cpsr)
                  (SET_IFMODE T fiq' mode' cpsr) |>`;

(* ------------------------------------------------------------------------- *)
(* The Branch instruction class (br)                                         *)
(* ------------------------------------------------------------------------- *)

val DECODE_BRANCH_def = Define`
  DECODE_BRANCH (w:word32) = (w %% 24, ((23 >< 0) w):word24)`;

val BRANCH_def = Define`
  BRANCH r mode ireg =
    let (L,offset) = DECODE_BRANCH ireg
    and pc = REG_READ r.reg usr 15w in
    let br_addr = pc + sw2sw offset << 2 in
    let pc_reg = REG_WRITE r.reg usr 15w br_addr in
      <| reg := if L then
                  REG_WRITE pc_reg mode 14w (FETCH_PC r.reg + 4w)
                else
                  pc_reg;
         psr := r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* The Data Processing instruction class (data_proc)                         *)
(* ------------------------------------------------------------------------- *)

val LSL_def = Define`
  LSL (m:word32) (n:word8) c =
    if n = 0w then (c, m) else
      (n <=+ 32w /\ m %% (32 - w2n n), m << w2n n)`;

val LSR_def = Define`
  LSR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (n <=+ 32w /\ m %% (w2n n - 1), m >>> w2n n)`;

val ASR_def = Define`
  ASR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m %% MIN 31 (w2n n - 1), m >> w2n n)`;

val ROR_def = Define`
  ROR (m:word32) (n:word8) c =
    if n = 0w then LSL m 0w c else
      (m %% (w2n ((w2w n):word5) - 1), m #>> w2n n)`;

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
  SHIFT_IMMEDIATE reg mode C (opnd2:word12) =
    let Rm = (3 >< 0) opnd2 in
    let rm = REG_READ reg mode Rm
    and sh = (6 >< 5) opnd2
    and shift = (11 >< 7) opnd2
    in
      SHIFT_IMMEDIATE2 shift sh rm C`;

val SHIFT_REGISTER_def = Define`
  SHIFT_REGISTER reg mode C (opnd2:word12) =
    let Rs = (11 >< 8) opnd2
    and Rm = (3 >< 0) opnd2 in
    let sh = (6 >< 5) opnd2
    and rm = REG_READ (INC_PC reg) mode Rm
    and shift = (7 >< 0) (REG_READ reg mode Rs) in
      SHIFT_REGISTER2 shift sh rm C`;

val ADDR_MODE1_def = Define`
  ADDR_MODE1 reg mode C Im opnd2 =
    if Im then
      IMMEDIATE C opnd2
    else if opnd2 %% 4 then
      SHIFT_REGISTER reg mode C opnd2
    else
      SHIFT_IMMEDIATE reg mode C opnd2`;

(* ......................................................................... *)

val ALU_arith_def = Define`
  ALU_arith op (rn:word32) (op2:word32) =
    let sign  = word_msb rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n op2)) in
    let res   = (n2w r):word32 in
      ((word_msb res,r = 0,ODD q,
        (word_msb op2 = sign) /\ ~(word_msb res = sign)),res)`;

val ALU_arith_neg_def = Define`
  ALU_arith_neg op (rn:word32) (op2:word32) =
    let sign  = word_msb rn
    and (q,r) = DIVMOD_2EXP 32 (op (w2n rn) (w2n ($- op2))) in
    let res   = (n2w r):word32 in
      ((word_msb res,r = 0,ODD q \/ (op2 = 0w),
      ~(word_msb op2 = sign) /\ ~(word_msb res = sign)),res)`;

val ALU_logic_def = Define`
  ALU_logic (res:word32) = ((word_msb res,res = 0w,F,F),res)`;

val SUB_def = Define`
  SUB a b c = ALU_arith_neg (\x y.x+y+(if c then 0 else 2 ** 32 - 1)) a b`;
val ADD_def = Define`
  ADD a b c = ALU_arith (\x y.x+y+(if c then 1 else 0)) a b`;
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
    || 3w  -> ADD (~rn) op2 T
    || 5w  -> ADD rn op2 c
    || 6w  -> SUB rn op2 c
    || 7w  -> ADD (~rn) op2 c
    || 8w  -> AND rn op2
    || 9w  -> EOR rn op2
    || 10w -> SUB rn op2 T
    || 11w -> ADD rn op2 F
    || 12w -> ORR rn op2
    || 13w -> ALU_logic op2
    || 14w -> AND rn (~op2)
    || _   -> ALU_logic (~op2)`;

(* ......................................................................... *)

val ARITHMETIC_def = Define`
  ARITHMETIC (opcode:word4) =
    (opcode %% 2 \/ opcode %% 1) /\ (~(opcode %% 3) \/ ~(opcode %% 2))`;

val TEST_OR_COMP_def = Define`
  TEST_OR_COMP (opcode:word4) = ((3 -- 2 ) opcode = 2w)`;

val DECODE_DATAP_def = Define`
  DECODE_DATAP w =
    (w %% 25,^Rg 24 21 w,w %% 20,^Rg 19 16 w,^Rg 15 12 w,
     ((11 >< 0) w):word12)`;

val DATA_PROCESSING_def = Define`
  DATA_PROCESSING r C mode ireg =
    let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP ireg in
    let (C_s,op2) = ADDR_MODE1 r.reg mode C I opnd2
    and pc_reg = INC_PC r.reg in
    let rn = REG_READ (if ~I /\ (opnd2 %% 4) then pc_reg else r.reg) mode Rn in
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

val DECODE_MRS_def = Define `DECODE_MRS w = (w %% 22,^Rg 15 12 w)`;

val MRS_def = Define`
  MRS r mode ireg =
    let (R,Rd) = DECODE_MRS ireg in
    let word = if R then SPSR_READ r.psr mode else CPSR_READ r.psr in
      <| reg := REG_WRITE (INC_PC r.reg) mode Rd word; psr := r.psr |>`;

(* ......................................................................... *)

val DECODE_MSR_def = Define`
  DECODE_MSR w =
    (w %% 25,w %% 22,w %% 19,w %% 16,^Rg 3 0 w,((11 >< 0) w):word12)`;

val MSR_def = Define`
  MSR r mode ireg =
    let (I,R,bit19,bit16,Rm,opnd) = DECODE_MSR ireg in
    if (USER mode /\ (R \/ (~bit19 /\ bit16))) \/ (~bit19 /\ ~bit16) then
      <| reg := INC_PC r.reg; psr := r.psr |>
    else
      let psrd = if R then SPSR_READ r.psr mode else CPSR_READ r.psr
      and  src = if I then SND (IMMEDIATE F opnd) else REG_READ r.reg mode Rm in
      let psrd' = word_modify
             (\i b. (28 <= i) /\ (if bit19 then src %% i else b) \/
                    (8 <= i) /\ (i <= 27) /\ b \/
                    (i <= 7) /\ (if bit16 /\ ~USER mode then src %% i else b))
             psrd
      in
        <| reg := INC_PC r.reg;
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
    let resHi = ((63 >< 32) res):word32
    and resLo = ((31 >< 0) res):word32 in
      if L then
        (word_msb res,res = 0w,resHi,resLo)
      else
        (word_msb resLo,resLo = 0w,rd,resLo)`;

val DECODE_MLA_MUL_def = Define`
  DECODE_MLA_MUL w = (w %% 23,w %% 22,w %% 21,w %% 20,
    ^Rg 19 16 w,^Rg 15 12 w,^Rg 11 8 w,^Rg 3 0 w)`;

val MLA_MUL_def = Define`
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
                    r.psr |>`;

(* ------------------------------------------------------------------------- *)
(* The Single Data Transfer instruction class (ldr_str)                      *)
(* ------------------------------------------------------------------------- *)

val UP_DOWN_def = Define`UP_DOWN u = if u then $word_add else $word_sub`;

val ADDR_MODE2_def = Define`
  ADDR_MODE2 reg mode C Im P U Rn offset =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then SND (SHIFT_IMMEDIATE reg mode C offset)
                 else w2w offset) in
      (if P then wb_addr else addr,wb_addr)`;

val DECODE_LDR_STR_def = Define`
  DECODE_LDR_STR w =
     (w %% 25,w %% 24,w %% 23,w %% 22,w %% 21,w %% 20,
      ^Rg 19 16 w,^Rg 15 12 w,((11 >< 0) w):word12)`;

val LDR_STR_def = Define`
  LDR_STR r C mode isdabort data ireg =
    let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
    let (addr,wb_addr) = ADDR_MODE2 r.reg mode C I P U Rn offset in
    let pc_reg = INC_PC r.reg in
    let wb_reg = if P ==> W then
                   REG_WRITE pc_reg mode Rn wb_addr
                 else
                   pc_reg
    in
      <| state :=
         <| reg :=
            if L ==> isdabort then
              wb_reg
            else
              let fmt = if B then UnsignedByte else UnsignedWord in
                REG_WRITE wb_reg mode Rd (FORMAT fmt ((1 >< 0) addr) (HD data));
            psr := r.psr |>;
         out :=
           [if L then
              MemRead addr
            else
              let w = REG_READ pc_reg mode Rd in
                MemWrite addr (if B then Byte ((7 >< 0) w) else Word w)] |>`;

(* ------------------------------------------------------------------------- *)
(* Half Word Single Data Transfer instruction class (ldrh_strh)              *)
(* ------------------------------------------------------------------------- *)

val ADDR_MODE3_def = Define`
  ADDR_MODE3 reg mode Im P U Rn offsetH offsetL =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr
          (if Im then offsetH @@ offsetL
                 else REG_READ reg mode offsetL) in
      (if P then wb_addr else addr,wb_addr)`;

val DECODE_LDRH_STRH_def = Define`
  DECODE_LDRH_STRH w =
     (w %% 24,w %% 23,w %% 22,w %% 21,w %% 20,
      ^Rg 19 16 w,^Rg 15 12 w,^Rg 11 8 w,w %% 6,w %% 5,^Rg 3 0 w)`;

val LDRH_STRH_def = Define`
  LDRH_STRH r mode isdabort data ireg =
    let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
    let (addr,wb_addr) = ADDR_MODE3 r.reg mode I P U Rn offsetH offsetL in
    let pc_reg = INC_PC r.reg in
    let wb_reg = if P ==> W then
                   REG_WRITE pc_reg mode Rn wb_addr
                 else
                   pc_reg
    in
      <| state :=
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
                REG_WRITE wb_reg mode Rd (FORMAT fmt ((1 >< 0) addr) (HD data));
            psr := r.psr |>;
         out :=
           [if L then
              MemRead addr
            else
              MemWrite addr (Half ((15 >< 0) (REG_READ pc_reg mode Rd))) ] |>`;

(* ------------------------------------------------------------------------- *)
(*  The Block Data Transfer instruction class (ldm_stm)                      *)
(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_def = Define`
  REGISTER_LIST (list:word16) =
    (MAP SND o FILTER FST) (GENLIST (\i. (list %% i,(n2w i):word4)) 16)`;

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

val STM_LIST_def = Define`
  STM_LIST reg mode bl_list =
    MAP (\(rp,addr). MemWrite addr (Word (REG_READ reg mode rp))) bl_list`;

val DECODE_LDM_STM_def = Define`
  DECODE_LDM_STM w =
    (w %% 24,w %% 23,w %% 22,w %% 21,w %% 20,^Rg 19 16 w,((15 >< 0) w):word16)`;

val LDM_STM_def = Define`
  LDM_STM r mode dabort_t data ireg =
    let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
    let pc_in_list = list %% 15
    and rn = REG_READ r.reg mode Rn in
    let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list
    and mode' = if S /\ (L ==> ~pc_in_list) then usr else mode
    and pc_reg = INC_PC r.reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg (if L then mode else mode') Rn rn'
                 else
                   pc_reg
    in
      <| state :=
           if L then
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
                 psr := if S /\ pc_in_list /\ ~IS_SOME dabort_t then
                          CPSR_WRITE r.psr (SPSR_READ r.psr mode)
                        else r.psr |>
           else <| reg := wb_reg; psr := r.psr |>;
         out :=
           if L then
             MAP MemRead addr_list
           else
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg) mode'
               (ZIP (rp_list,addr_list)) |>`;

(* ------------------------------------------------------------------------- *)
(* The Single Data Swap instruction class (swp)                              *)
(* ------------------------------------------------------------------------- *)

val DECODE_SWP_def = Define`
  DECODE_SWP w = (w %% 22,^Rg 19 16 w,^Rg 15 12 w,^Rg 3 0 w)`;

val SWP_def = Define`
  SWP r mode isdabort data ireg =
    let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
    let rn = REG_READ r.reg mode Rn
    and pc_reg = INC_PC r.reg in
    let rm = REG_READ pc_reg mode Rm in
      <| state :=
          <| reg :=
                if isdabort then
                  pc_reg
                else
                  let fmt = if B then UnsignedByte else UnsignedWord in
                    REG_WRITE pc_reg mode Rd
                      (FORMAT fmt ((1 ><  0) rn) (HD data));
              psr := r.psr |>;
         out := [MemRead rn;
                 MemWrite rn (if B then Byte ((7 >< 0) rm) else Word rm)] |>`;

(* ------------------------------------------------------------------------- *)
(* Coprocessor Register Transfer (mrc, mcr)                                  *)
(* ------------------------------------------------------------------------- *)

val MRC_def = Define`
  MRC r mode data ireg =
    let Rd = ^Rg 15 12 ireg
    and pc_reg = INC_PC r.reg in
      if Rd = 15w then
        <| reg := pc_reg;
           psr := CPSR_WRITE r.psr (SET_NZCV (NZCV data) (CPSR_READ r.psr)) |>
      else
        <| reg := REG_WRITE pc_reg mode Rd data; psr := r.psr |>`;

val MCR_OUT_def = Define`
  MCR_OUT reg mode ireg =
    let Rn = ^Rg 15 12 ireg in
      [CPWrite (REG_READ (INC_PC reg) mode Rn)]`;

(* ------------------------------------------------------------------------- *)
(* Coprocessor Data Transfers (ldc_stc)                                      *)
(* ------------------------------------------------------------------------- *)

val DECODE_LDC_STC_def = Define`
  DECODE_LDC_STC w =
    (w %% 24,w %% 23,w %% 21,w %% 20,^Rg 19 16 w,((7 >< 0) w):word8)`;

val ADDR_MODE5_def = Define`
  ADDR_MODE5 reg mode P U Rn (offset:word8) =
    let addr = REG_READ reg mode Rn in
    let wb_addr = UP_DOWN U addr (w2w offset << 2) in
      (if P then wb_addr else addr,wb_addr)`;

val LDC_STC_def = Define`
  LDC_STC r mode ireg =
    let (P,U,W,L,Rn,offset) = DECODE_LDC_STC ireg in
    let (addr,wb_addr) = ADDR_MODE5 r.reg mode P U Rn offset in
    let pc_reg = INC_PC r.reg in
    let wb_reg = if W /\ ~(Rn = 15w) then
                   REG_WRITE pc_reg mode Rn wb_addr
                 else
                   pc_reg in
      <| state := <| reg := wb_reg; psr := r.psr |>;
         out := [if L then MemRead addr else MemWrite addr ARB] |>`;

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
      if ireg %% 28 then ~pass else pass`;

(* ------------------------------------------------------------------------- *)
(* Top-level decode and run functions                                        *)
(* ------------------------------------------------------------------------- *)

val DECODE_ARM_def = Define`
  DECODE_ARM (ireg : word32) =
    let b n = ireg %% n in
      case (b 27,b 26,b 25,b 24,b 23,b 22,b 21,b 20,b 7,b 6,b 5,b 4) of
         (F,F,F, T , F ,_22,b21, F , F, F, F, F) -> if b21 then msr else mrs
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
  RUN_ARM state (dabt:num option) data no_cp =
    let ireg = state.ireg and r = state.regs
    and inc_pc x = <| reg := INC_PC x.reg; psr := x.psr |>
    in
      if ~(state.exception = software) then
        EXCEPTION r state.exception
      else let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ r.psr) in
        if ~CONDITION_PASSED nzcv ireg then
          inc_pc r
        else let ic = DECODE_ARM ireg and mode = DECODE_MODE m
             and coproc f = if no_cp then r else f r
        in
          case ic of
             data_proc -> DATA_PROCESSING r (CARRY nzcv) mode ireg
          || mla_mul   -> MLA_MUL r mode ireg
          || swi_ex    -> EXCEPTION r software
          || br        -> BRANCH r mode ireg
          || msr       -> MSR r mode ireg
          || mrs       -> MRS r mode ireg
          || swp       -> (SWP r mode (IS_SOME dabt) data ireg).state
          || ldm_stm   -> (LDM_STM r mode dabt data ireg).state
          || ldr_str   ->
               (LDR_STR r (CARRY nzcv) mode (IS_SOME dabt) data ireg).state
          || ldrh_strh   ->
               (LDRH_STRH r mode (IS_SOME dabt) data ireg).state
          || ldc_stc   -> coproc (\x. (LDC_STC x mode ireg).state)
          || mrc       -> coproc (\x. MRC x mode (ELL 1 data) ireg)
          || mcr       -> coproc inc_pc
          || cdp_und   -> coproc inc_pc
          || _ -> r`;

(* ------------------------------------------------------------------------- *)
(* Exception operations                                                      *)
(* ------------------------------------------------------------------------- *)

val IS_Reset_def = Define`
  (IS_Reset (SOME (Reset x)) = T) /\ (IS_Reset _ = F)`;

val PROJ_Reset_def = Define`
  PROJ_Reset (SOME (Reset x)) = x`;

val PROJ_Dabort_def = Define`
  (PROJ_Dabort (SOME (Dabort x)) = SOME x) /\
  (PROJ_Dabort _ = NONE)`;

val interrupt2exception_def = Define`
  interrupt2exception state (i',f') irpt =
    let ireg = state.ireg in
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ state.regs.psr) in
    let pass = (state.exception = software) /\ CONDITION_PASSED flags ireg
    and ic = DECODE_ARM ireg in
    let old_flags = pass /\ ((ic = mrs) \/ (ic = msr)) in
    (case irpt of
        NONE            -> software
     || SOME (Reset x)  -> reset
     || SOME Prefetch   -> pabort
     || SOME (Dabort t) -> dabort
     || SOME Undef      -> if pass /\ ic IN {cdp_und; mrc; mcr; ldc_stc} then
                             undefined
                           else
                             software
     || SOME Fiq        -> if (if old_flags then f else f') then
                             software
                           else
                             fast
     || SOME Irq        -> if (if old_flags then i else i') then
                             software
                           else
                             interrupt)`;

val PROJ_IF_FLAGS_def = Define`
  PROJ_IF_FLAGS psr =
    let (flags,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)`;

(* ------------------------------------------------------------------------- *)
(* The next state, output and state functions                                *)
(* ------------------------------------------------------------------------- *)

val NEXT_ARM_def = Define`
  NEXT_ARM state inp =
    let r = if IS_Reset inp.interrupt then
              PROJ_Reset inp.interrupt
            else
              RUN_ARM state (PROJ_Dabort inp.interrupt) inp.data inp.no_cp
    in
      <| regs := r; ireg := inp.ireg;
         exception :=
           interrupt2exception state (PROJ_IF_FLAGS r.psr) inp.interrupt |>`;

val OUT_ARM_def = Define`
  OUT_ARM state =
    let ireg = state.ireg and r = state.regs in
    let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ r.psr) in
      (if (state.exception = software) /\ CONDITION_PASSED nzcv ireg then
         let ic = DECODE_ARM ireg and mode = DECODE_MODE m in
           case ic of
              ldr_str   -> ((LDR_STR r (CARRY nzcv) mode ARB ARB ireg).out,F)
           || ldrh_strh -> ((LDRH_STRH r mode ARB ARB ireg).out,F)
           || ldm_stm   -> ((LDM_STM r mode ARB ARB ireg).out,F)
           || swp       -> ((SWP r mode ARB ARB ireg).out,F)
           || ldc_stc   -> ((LDC_STC r mode ireg).out,T)
           || mcr       -> (MCR_OUT r.reg mode ireg,T)
           || mrc       -> ([],T)
           || cdp_und   -> ([],T)
           || _         -> ([],F)
       else ([],F))`;

val STATE_ARM_def = Define`
  (STATE_ARM 0 x = x.state) /\
  (STATE_ARM (SUC t) x = NEXT_ARM (STATE_ARM t x) (x.inp t))`;

val ARM_SPEC_def = Define`
  ARM_SPEC t x = let s = STATE_ARM t x in <| state := s; out := OUT_ARM s |>`;

(* ------------------------------------------------------------------------- *)
(* A Model without I/O                                                       *)
(* ------------------------------------------------------------------------- *)

(* The State Space --------------------------------------------------------- *)

val _ = Hol_datatype
 `arm_mem_state = <| registers : registers; psrs : psrs;
                     memory : mem; undefined : bool |>`;

(* ------------------------------------------------------------------------- *)

val TRANSFER_def = Define`
  TRANSFER cpi (cpin,data,mem) t =
    case t of
       MemRead a ->
         if cpi then
           let (f, b) = SPLITP IS_SOME cpin in
             (b, data ++
                MAP (\addr. mem (ADDR30 addr)) (ADDRESS_LIST a (LENGTH f)), mem)
         else
           (cpin, data ++ [mem (ADDR30 a)], mem)
    || MemWrite a d ->
         if cpi then
           let (f, b) = SPLITP IS_NONE cpin in
             (b, data,
                FOLDL (\m (addr,cpd). MEM_WRITE mem addr (Word (THE cpd)))
                  mem (ZIP (ADDRESS_LIST a (LENGTH f), f)))
         else
            (cpin, data, MEM_WRITE mem a d)
    || CPWrite w ->
         (cpin, if cpi then data ++ [w] else data, mem)`;

val TRANSFERS_def = Define`
  TRANSFERS cpi cpin mem ts =
    if cpi /\ NULL ts then
      (MAP THE cpin, mem)
    else
      SND (FOLDL (TRANSFER cpi) (cpin, [], mem) ts)`;

val NEXT_ARM_MEM_def = Define`
  NEXT_ARM_MEM state =
    let ireg = state.memory (ADDR30 (FETCH_PC state.registers)) in
    let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
               ireg := ireg;
               exception := if state.undefined then undefined else software |>
    in
    let (transfers,cpi) = OUT_ARM s in
    let (data, mem) = TRANSFERS cpi [] state.memory transfers in
    let r = RUN_ARM s NONE data T
    in
      <| registers := r.reg; psrs := r.psr; memory := mem;
         undefined := (~state.undefined /\ cpi) |>`;

val STATE_ARM_MEM_def = Define`
  (STATE_ARM_MEM 0 s = s) /\
  (STATE_ARM_MEM (SUC t) s = NEXT_ARM_MEM (STATE_ARM_MEM t s))`;

(* ------------------------------------------------------------------------- *)
(* Some useful theorems                                                      *)
(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val SUBST_NE_COMMUTES = store_thm ("SUBST_NE_COMMUTES",
  `!m a b c d. ~(a = b) ==>
     ((a :- c) ((b :- d) m) = (b :- d) ((a :- c) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ RW_TAC std_ss [SUBST_def]);

val SUBST_COMMUTES = store_thm("SUBST_COMMUTES",
  `!m a b c d. a <+ b ==>
     ((b :- d) ((a :- c) m) = (a :- c) ((b :- d) m))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ
    \\ ASM_SIMP_TAC std_ss [SUBST_NE_COMMUTES]);

val SUBST_EQ = store_thm("SUBST_EQ",
  `!m a b c. (a :- c) ((a :- b) m) = (a :- c) m`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ RW_TAC std_ss [SUBST_def]);

val SUBST_EVAL = store_thm("SUBST_EVAL",
  `!a w b. (a :- w) m b = if a = b then w else m b`,
  RW_TAC std_ss [SUBST_def]);

(* ------------------------------------------------------------------------- *)
(* Add some definitions to the_compset                                       *)
(*---------------------------------------------------------------------------*)

val _ =
let open pred_setTheory
    val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
in
  computeLib.add_persistent_funs
  ([("rich_listTheory.GENLIST", SUC_RULE GENLIST),
    ("rich_listTheory.FIRSTN", SUC_RULE FIRSTN),
    ("rich_listTheory.SPLITP", SPLITP),
    ("rich_listTheory.SNOC", SNOC),
    ("pred_setTheory.IN_INSERT", IN_INSERT),
    ("pred_setTheory.NOT_IN_EMPTY", NOT_IN_EMPTY),
    ("SUBST_EVAL",  SUBST_EVAL)] @
  map (fn s => (s, theorem s))
  ["register_EQ_register","num2register_thm","register2num_thm", "mode_EQ_mode",
   "mode2num_thm", "psr_EQ_psr", "psr2num_thm", "iclass_EQ_iclass",
   "iclass2num_thm", "num2condition_thm", "condition2num_thm",
   "exceptions_EQ_exceptions", "num2exceptions_thm", "exceptions2num_thm"])
end;

(* ------------------------------------------------------------------------- *)
(* Export ML versions of functions                                           *)
(*---------------------------------------------------------------------------*)

open arithmeticTheory numeralTheory bitTheory;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val word_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++
  rewrites [n2w_def,word_extract_def,word_bits_n2w,w2w,
    BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
    DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def]

val MOD_DIMINDEX_32 = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
   Thm.INST_TYPE [alpha |-> ``:i32``]) MOD_DIMINDEX;

val DECODE_TAC = SIMP_TAC std_ss [DECODE_PSR_def,DECODE_BRANCH_def,
      DECODE_DATAP_def,DECODE_MRS_def,DECODE_MSR_def,DECODE_LDR_STR_def,
      DECODE_LDRH_STRH_def,DECODE_MLA_MUL_def,DECODE_LDM_STM_def,
      DECODE_SWP_def,DECODE_LDC_STC_def,SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,
      CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV rich_listTheory.GENLIST,
      NZCV_def,REGISTER_LIST_def,rich_listTheory.SNOC,word_extract_def]
 \\ SIMP_TAC word_ss [];

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,i) = DIVMOD_2EXP 1 (DIV2 q0) in
     let (q2,f) = DIVMOD_2EXP 1 q1 in
     let (q3,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q2) in
     let (q4,C) = DIVMOD_2EXP 1 q3 in
     let (q5,Z) = DIVMOD_2EXP 1 q4 in
       ((ODD q5,Z=1,C=1,V=1),f = 1,i = 1,n2w m)`, DECODE_TAC);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH (n2w n) =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,n2w offset)`, DECODE_TAC);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP (n2w n) =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,n2w opcode,S = 1,n2w Rn,n2w Rd,n2w opnd2)`, DECODE_TAC);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS (n2w n) =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),n2w Rd)`, DECODE_TAC);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR (n2w n) =
     let (q0,opnd) = DIVMOD_2EXP 12 n in
     let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
     let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
     let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
       (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,
        n2w (MOD_2EXP 4 opnd),n2w opnd)`,
  DECODE_TAC \\ `4096 = 16 * 256` by numLib.ARITH_TAC
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC arith_ss [MOD_MULT_MOD]);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 12 n in
    let (q1,Rd) = DIVMOD_2EXP 4 q0 in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,L) = DIVMOD_2EXP 1 q2 in
    let (q4,W) = DIVMOD_2EXP 1 q3 in
    let (q5,B) = DIVMOD_2EXP 1 q4 in
    let (q6,U) = DIVMOD_2EXP 1 q5 in
    let (q7,P) = DIVMOD_2EXP 1 q6 in
      (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,n2w Rn,n2w Rd,n2w offset)`,
   DECODE_TAC);

val DECODE_LDRH_STRH_THM = store_thm("DECODE_LDRH_STRH_THM",
  `!n. DECODE_LDRH_STRH (n2w n) =
    let (q0,offsetL) = DIVMOD_2EXP 4 n in
    let (q1,H) = DIVMOD_2EXP 1 (DIV2 q0) in
    let (q2,S) = DIVMOD_2EXP 1 q1 in
    let (q3,offsetH) = DIVMOD_2EXP 4 (DIV2 q2) in
    let (q4,Rd) = DIVMOD_2EXP 4 q3 in
    let (q5,Rn) = DIVMOD_2EXP 4 q4 in
    let (q6,L) = DIVMOD_2EXP 1 q5 in
    let (q7,W) = DIVMOD_2EXP 1 q6 in
    let (q8,I) = DIVMOD_2EXP 1 q7 in
    let (q9,U) = DIVMOD_2EXP 1 q8 in
      (ODD q9,U = 1,I = 1,W = 1,L = 1,n2w Rn,n2w Rd,
       n2w offsetH,S = 1,H = 1,n2w offsetL)`,
   DECODE_TAC);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,Rd) = DIVMOD_2EXP 4 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,A) = DIVMOD_2EXP 1 q4 in
    let (q6,Sgn) = DIVMOD_2EXP 1 q5 in
      (ODD q6,Sgn = 1,A = 1,S = 1,n2w Rd,n2w Rn,n2w Rs,n2w Rm)`, DECODE_TAC);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM (n2w n) =
    let (q0,list) = DIVMOD_2EXP 16 n in
    let (q1,Rn) = DIVMOD_2EXP 4 q0 in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,U) = DIVMOD_2EXP 1 q4 in
      (ODD q5, U = 1, S = 1, W = 1, L = 1,n2w Rn,n2w list)`, DECODE_TAC);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),n2w Rn,n2w Rd,n2w Rm)`, DECODE_TAC);

val DECODE_LDC_STC_THM = store_thm("DECODE_LDC_STC_THM",
  `!n. DECODE_LDC_STC (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 8 n in
    let (q1,Rn) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,U) = DIVMOD_2EXP 1 (DIV2 q3) in
      (ODD q4,U = 1,W = 1,L = 1,n2w Rn,n2w offset)`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

fun w2w_n2w_sizes a b = (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
  Thm.INST_TYPE [alpha |-> a, beta |-> b]) w2w_n2w;

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!reg mode C opnd2.
     SHIFT_IMMEDIATE reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let shift = MOD_2EXP 5 q1 in
       let rm = REG_READ reg mode (n2w Rm) in
         SHIFT_IMMEDIATE2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``) [``:i8``, ``:i4``, ``:i2``])
    \\ DECODE_TAC);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg mode C opnd2.
     SHIFT_REGISTER reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ reg mode (n2w Rs)))
       and rm = REG_READ (INC_PC reg) mode (n2w Rm) in
         SHIFT_REGISTER2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC [w2w_n2w_sizes ``:i32`` ``:i8``]
    \\ ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``)
          [``:i8``, ``:i4``, ``:i2``])
    \\ SIMP_TAC std_ss [SHIFT_REGISTER_def,word_extract_def,
         (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [n2w_w2n,BITS_THM,DIV_1,
            (GSYM o SIMP_RULE std_ss [] o SPEC `8`) MOD_2EXP_def] o
          SPECL [`7`,`0`,`w2n (a:word32)`] o
          Thm.INST_TYPE [alpha |-> ``:i32``]) word_bits_n2w]
    \\ SIMP_TAC word_ss []);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST (n2w n) =
       let (q0,b0) = DIVMOD_2EXP 1 n in
       let (q1,b1) = DIVMOD_2EXP 1 q0 in
       let (q2,b2) = DIVMOD_2EXP 1 q1 in
       let (q3,b3) = DIVMOD_2EXP 1 q2 in
       let (q4,b4) = DIVMOD_2EXP 1 q3 in
       let (q5,b5) = DIVMOD_2EXP 1 q4 in
       let (q6,b6) = DIVMOD_2EXP 1 q5 in
       let (q7,b7) = DIVMOD_2EXP 1 q6 in
       let (q8,b8) = DIVMOD_2EXP 1 q7 in
       let (q9,b9) = DIVMOD_2EXP 1 q8 in
       let (q10,b10) = DIVMOD_2EXP 1 q9 in
       let (q11,b11) = DIVMOD_2EXP 1 q10 in
       let (q12,b12) = DIVMOD_2EXP 1 q11 in
       let (q13,b13) = DIVMOD_2EXP 1 q12 in
       let (q14,b14) = DIVMOD_2EXP 1 q13 in
       MAP SND (FILTER FST
         [(b0 = 1,0w); (b1 = 1,1w); (b2 = 1,2w); (b3 = 1,3w);
          (b4 = 1,4w); (b5 = 1,5w); (b6 = 1,6w); (b7 = 1,7w);
          (b8 = 1,8w); (b9 = 1,9w); (b10 = 1,10w); (b11 = 1,11w);
          (b12 = 1,12w); (b13 = 1,13w); (b14 = 1,14w); (ODD q14,15w)])`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val DECODE_ARM_THM = store_thm("DECODE_ARM_THM",
  `!ireg. DECODE_ARM (ireg : word32) =
    let b n = ireg %% n in
      if b 27 then
        if b 26 then
          if b 25 then
            if b 24 then (* (T,T,T,T,...) *)
              swi_ex
            else (* (T,T,T,F,...) *)
              if b 4 then
                if b 20 then mrc else mcr
              else
                cdp_und
          else (* (T,T,F,...) *)
            ldc_stc
        else (* (T,F,...) *)
          if b 25 then br else ldm_stm
      else
         if b 26 then (* (F,T,...) *)
           if b 25 then
             if b 4 then cdp_und else ldr_str
           else
             ldr_str
         else
           if b 25 then (* (F,F,T,...) *)
             if b 24 /\ ~b 23 /\ ~b 20 then
               if b 21 then
                 msr
               else
                 cdp_und
             else
               data_proc
           else
             if b 24 then (* (F,F,F,T,...) *)
               if b 7 then
                 if b 4 then
                   if b 20 then
                     if b 6 then
                       ldrh_strh
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 6 then
                       cdp_und
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         if ~b 23 /\ ~b 21 then
                           swp
                         else
                           cdp_und
                 else
                   data_proc
               else
                 if b 4 then
                   data_proc
                 else
                   if ~b 23 /\ ~b 20 /\ ~b 6 /\ ~b 5 then
                     if b 21 then msr else mrs
                   else
                     data_proc
             else (* (F,F,F,F,...) *)
               if b 7 then
                 if b 4 then
                   if b 6 \/ b 5 then
                     if b 20 /\ b 6 then
                       ldrh_strh
                     else
                       if ~b 6 /\ b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 23 \/ ~b 22 then mla_mul else cdp_und
                 else
                   data_proc
               else
                 if b 4 then data_proc else data_proc`,
  SRW_TAC [boolSimps.LET_ss] [DECODE_ARM_def]
    \\ FULL_SIMP_TAC (srw_ss()) [bool_case_ID]);

(*---------------------------------------------------------------------------*)

val num2register = prove(
  `!n. num2register n =
         if n = 0 then r0 else
         if n = 1 then r1 else
         if n = 2 then r2 else
         if n = 3 then r3 else
         if n = 4 then r4 else
         if n = 5 then r5 else
         if n = 6 then r6 else
         if n = 7 then r7 else
         if n = 8 then r8 else
         if n = 9 then r9 else
         if n = 10 then r10 else
         if n = 11 then r11 else
         if n = 12 then r12 else
         if n = 13 then r13 else
         if n = 14 then r14 else
         if n = 15 then r15 else
         if n = 16 then r8_fiq else
         if n = 17 then r9_fiq else
         if n = 18 then r10_fiq else
         if n = 19 then r11_fiq else
         if n = 20 then r12_fiq else
         if n = 21 then r13_fiq else
         if n = 22 then r14_fiq else
         if n = 23 then r13_irq else
         if n = 24 then r14_irq else
         if n = 25 then r13_svc else
         if n = 26 then r14_svc else
         if n = 27 then r13_abt else
         if n = 28 then r14_abt else
         if n = 29 then r13_und else
         if n = 30 then r14_und else
           FAIL num2register ^(mk_var("30 < n",bool)) n`,
  SRW_TAC [] [theorem "num2register_thm", combinTheory.FAIL_THM]);

val num2condition = prove(
  `!n. num2condition n =
         if n = 0 then EQ else
         if n = 1 then CS else
         if n = 2 then MI else
         if n = 3 then VS else
         if n = 4 then HI else
         if n = 5 then GE else
         if n = 6 then GT else
         if n = 7 then AL else
         if n = 8 then NE else
         if n = 9 then CC else
         if n = 10 then PL else
         if n = 11 then VC else
         if n = 12 then LS else
         if n = 13 then LT else
         if n = 14 then LE else
         if n = 15 then NV else
           FAIL num2condition ^(mk_var("15 < n",bool)) n`,
  SRW_TAC [] [theorem "num2condition_thm", combinTheory.FAIL_THM]);

(*---------------------------------------------------------------------------*)

val LDR_STR_OUT = prove(
  `!r C mode ireg.
    (LDR_STR r C mode ARB ARB ireg).out =
      (let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
       let (addr,wb_addr) = ADDR_MODE2 r.reg mode C I P U Rn offset in
       let pc_reg = INC_PC r.reg
       in
         [(if L then
             MemRead addr
           else
             let w = REG_READ pc_reg mode Rd in
               MemWrite addr (if B then Byte ((7 >< 0) w) else Word w))])`,
  SRW_TAC [boolSimps.LET_ss] [LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def]);

val LDRH_STRH_OUT = prove(
  `!r C mode ireg.
    (LDRH_STRH r mode ARB ARB ireg).out =
      (let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
       let (addr,wb_addr) = ADDR_MODE3 r.reg mode I P U Rn offsetH offsetL in
       let pc_reg = INC_PC r.reg
       in
         [(if L then
             MemRead addr
           else
             MemWrite addr (Half ((15 >< 0) (REG_READ pc_reg mode Rd))))])`,
  SRW_TAC [boolSimps.LET_ss]
    [LDRH_STRH_def,DECODE_LDRH_STRH_def,ADDR_MODE3_def]);

val LDM_STM_OUT = prove(
   `!r mode ireg.
     (LDM_STM r mode ARB ARB ireg).out =
       (let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
        let pc_in_list = list %% 15 and rn = REG_READ r.reg mode Rn in
        let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list and
            mode' = (if S /\ (L ==> ~pc_in_list) then usr else mode) and
            pc_reg = INC_PC r.reg
        in
        let wb_reg =
              (if W /\ ~(Rn = 15w) then
                 REG_WRITE pc_reg (if L then mode else mode') Rn rn'
               else
                 pc_reg)
        in
          (if L then
             MAP MemRead addr_list
           else
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg)
               mode' (ZIP (rp_list,addr_list))))`,
  SRW_TAC [boolSimps.LET_ss] [LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def]);

val SWP_OUT = prove(
  `!r mode ireg.
    (SWP r mode ARB ARB ireg).out =
       (let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
        let rn = REG_READ r.reg mode Rn and pc_reg = INC_PC r.reg in
        let rm = REG_READ pc_reg mode Rm in
          [MemRead rn;
           MemWrite rn (if B then Byte ((7 >< 0) rm) else Word rm)])`,
  SRW_TAC [boolSimps.LET_ss] [SWP_def,DECODE_SWP_def]);

val OUT_ARM =
   REWRITE_RULE [LDR_STR_OUT,LDRH_STRH_OUT,LDM_STM_OUT,SWP_OUT] OUT_ARM_def;

(*---------------------------------------------------------------------------*)

val empty_registers_def = Define`empty_registers = (\n. 0w):registers`;
val empty_psrs_def      = Define`empty_psrs = (\x. SET_IFMODE F F usr 0w):psrs`;

val RHS_REWRITE_RULE =
  GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites;

val n2w_w2n_rule = GEN_ALL o SIMP_RULE bool_ss [wordsTheory.n2w_w2n];

val spec_word_rule16 = n2w_w2n_rule o Q.SPEC `w2n (w:word16)`;
val spec_word_rule32 = n2w_w2n_rule o Q.SPEC `w2n (w:word32)`;

val spec_word_rule12 =
  n2w_w2n_rule o INST [`opnd2` |-> `w2n (w:word12)`] o SPEC_ALL;

val mem_read_rule = ONCE_REWRITE_RULE [GSYM mem_read_def];

val _ = ConstMapML.insert ``dimword``;
val _ = ConstMapML.insert ``dimindex``;
val _ = ConstMapML.insert ``INT_MIN``;
val _ = ConstMapML.insert ``n2w_itself``;

fun mk_word n =
  let val s = Int.toString n
      val w = "type word" ^ s ^ " = wordsML.word" ^ s
  in
    EmitML.MLSIG w
  end;

val _ = let open EmitML in emitML (!Globals.emitMLDir)
    ("arm", OPEN ["num", "set", "fcp", "list", "rich_list", "bit", "words"]
         :: MLSIG "type 'a word = 'a wordsML.word"
         :: MLSIG "type num = numML.num"
         :: map (fn decl => DATATYPE decl)
             [register_decl, psr_decl, mode_decl, condition_decl]
          @ map (fn decl => EQDATATYPE ([], decl))
             [exceptions_decl, iclass_decl]
          @ ABSDATATYPE (["'a","'b"],
              `state_inp = <| state : 'a; inp : num -> 'b |>`)
         :: ABSDATATYPE (["'a","'b"],
              `state_out = <| state : 'a; out : 'b |>`)
         :: map mk_word [2,4,5,8,12,16,24,30,32]
          @ MLSTRUCT "type registers = register->word32"
         :: MLSTRUCT "type psrs = psr->word32"
         :: MLSTRUCT "type mem = bsubstML.mem"
         :: MLSTRUCT "type data = bsubstML.data"
         :: MLSIG "type registers = register->word32"
         :: MLSIG "type psrs = psr->word32"
         :: MLSIG "type mem = bsubstML.mem"
         :: MLSIG "type data = bsubstML.data"
         :: DATATYPE (`regs = <| reg : registers; psr : psrs |>`)
         :: DATATYPE (`arm_state = <| regs : regs; ireg : word32;
                         exception : exceptions |>`)
         :: DATATYPE (`arm_mem_state = <| registers : registers; psrs : psrs;
                         memory : mem; undefined : bool |>`)
         :: DATATYPE (`interrupt = Reset of regs | Undef | Prefetch |
                         Dabort of num | Fiq | Irq`)
         :: DATATYPE (`arm_input = <| ireg : word32; data : word32 list;
                         interrupt : interrupt option; no_cp : bool |>`)
         :: DATATYPE (
              `memop = MemRead of word32 | MemWrite of word32=>data |
                       CPWrite of word32`)
         :: MLSTRUCT "val mem_updates = ref ([]: word30 list)"
         :: MLSIG "val mem_updates : word30 list ref"
         :: map (DEFN o BETA_RULE o PURE_REWRITE_RULE
             [GSYM n2w_itself_def, GSYM w2w_itself_def, GSYM sw2sw_itself_def,
              GSYM word_concat_itself_def, GSYM word_extract_itself_def,
              literal_case_THM] o RHS_REWRITE_RULE [GSYM word_eq_def])
             (map spec_word_rule32
             [DECODE_PSR_THM, DECODE_BRANCH_THM, DECODE_DATAP_THM,
              DECODE_MRS_THM, DECODE_MSR_THM, DECODE_LDR_STR_THM,
              DECODE_MLA_MUL_THM, DECODE_LDM_STM_THM, DECODE_SWP_THM,
              DECODE_LDC_STC_THM, DECODE_LDRH_STRH_THM]
           @ [USER_def, mode_reg2num_def, DECODE_ARM_def,
              definition "state_out_state", definition "state_out_out",
              theorem "exceptions2num_thm", theorem "register2num_thm",
              num2register, num2condition,
              REG_READ_def, REG_WRITE_def, INC_PC_def, FETCH_PC_def,
              SET_NZCV_def, SET_NZC_def, SET_NZ_def, mode_num_def,
              SET_IFMODE_def,
              SIMP_RULE std_ss [literal_case_DEF] DECODE_MODE_def, NZCV_def,
              CARRY_def, mode2psr_def, SPSR_READ_def,
              CPSR_READ_def, CPSR_WRITE_def, SPSR_WRITE_def,
              exception2mode_def, SPECL [`r`,`e`]  EXCEPTION_def,
              BRANCH_def, LSL_def, LSR_def, ASR_def, ROR_def, IMMEDIATE_def,
              SHIFT_IMMEDIATE2_def, SHIFT_REGISTER2_def,
              spec_word_rule12 SHIFT_IMMEDIATE_THM,
              spec_word_rule12 SHIFT_REGISTER_THM, ADDR_MODE1_def,
              SPEC `f` ALU_arith_def, SPEC `f` ALU_arith_neg_def, ALU_logic_def,
              numLib.REDUCE_RULE SUB_def, ADD_def, AND_def, EOR_def, ORR_def,
              ALU_def, ARITHMETIC_def, TEST_OR_COMP_def, DATA_PROCESSING_def,
              MRS_def, MSR_def, ALU_multiply_def, MLA_MUL_def,
              UP_DOWN_def, ADDR_MODE2_def, IMP_DISJ_THM, LDR_STR_def,
              ADDR_MODE3_def, LDRH_STRH_def,spec_word_rule16 REGISTER_LIST_THM,
              ADDRESS_LIST_def, WB_ADDRESS_def, FIRST_ADDRESS_def,
              ADDR_MODE4_def, LDM_LIST_def, STM_LIST_def, LDM_STM_def,
              SWP_def, MRC_def, MCR_OUT_def, ADDR_MODE5_def, LDC_STC_def,
              CONDITION_PASSED2_def, CONDITION_PASSED_def,
              RUN_ARM_def, IS_Reset_def, PROJ_Dabort_def, PROJ_Reset_def ,
              interrupt2exception_def, PROJ_IF_FLAGS_def, NEXT_ARM_def,
              OUT_ARM, mem_read_rule TRANSFER_def, TRANSFERS_def,
              mem_read_rule NEXT_ARM_MEM_def, empty_registers_def]))
 end;

val _ = export_theory();
