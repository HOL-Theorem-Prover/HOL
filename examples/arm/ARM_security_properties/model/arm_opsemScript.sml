(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics (A and R profiles)                        *)
(*     =============================================                        *)
(*     Operational semantics for ARM                                        *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load
    ["arm_seq_monadTheory", "wordsLib", "intLib", "integer_wordTheory",
     "stringSimps", "parmonadsyntax"];
*)

open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib integer_wordTheory;

open arm_coretypesTheory arm_seq_monadTheory;

val _ = new_theory "arm_opsem";
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------ *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val _ = set_fixity ">>=" (Infixr 660);
val _ = set_fixity "|||" (Infixr 90);
val _ = overload_on(">>=", ``seqT``);
val _ = overload_on("|||", ``parT``);

val _ = temp_overload_on (parmonadsyntax.monad_bind, ``seqT``);
val _ = temp_overload_on (parmonadsyntax.monad_par,  ``parT``);
val _ = temp_overload_on ("return", ``constT``);

val _ = overload_on("UNKNOWN", ``ARB:bool``);
val _ = overload_on("UNKNOWN", ``ARB:word32``);
val _ = overload_on("BITS16_UNKNOWN", ``[ARB;ARB] : word8 list``);
val _ = overload_on("BITS32_UNKNOWN", ``[ARB;ARB;ARB;ARB] : word8 list``);

val _ = app temp_overload_on
  [("unit2", ``\(u1:unit,u2:unit). constT ()``),
   ("unit3", ``\(u1:unit,u2:unit,u3:unit). constT ()``),
   ("unit4", ``\(u1:unit,u2:unit,u3:unit,u4:unit). constT ()``)];

val _ = temp_overload_on
  ("ALL", ``(UNIV CROSS UNIV) : (ARMarch # ARMextensions set) set``);

val _ = temp_overload_on
  ("ARCH", ``\s. (s CROSS UNIV) : (ARMarch # ARMextensions set) set``);

val _ = temp_overload_on("BadReg", ``\n:word4. (n = 13w) \/ (n = 15w)``);

val _ = temp_overload_on("extend", ``\u. if u then w2w else sw2sw``);

val _ = temp_overload_on
  ("ARCH2",
     ``\enc a. ARCH (if enc = Encoding_Thumb2 then thumb2_support else a)``);

(* ------------------------------------------------------------------------ *)

val unaligned_support_def = Define`
  unaligned_support ii =
    read_info ii >>= (\info. constT (info.unaligned_support))`;

val dsp_support_def    = Define`
  dsp_support = COMPL {ARMv4; ARMv4T; ARMv5T}`;

val kernel_support_def = Define`
  kernel_support = {a | (a = ARMv6K) \/ version_number a >= 7}`;

val arch_version_def = Define`
  arch_version ii = seqT (read_arch ii) (constT o version_number)`;

val read_reg_literal_def = Define`
  read_reg_literal ii n =
    if n = 15w then
      read_reg ii 15w >>= (\pc. constT (align(pc,4)))
    else
      read_reg ii n`;

val read_flags_def = Define`
  read_flags ii =
    read_cpsr ii >>= (\cpsr. constT (cpsr.N,cpsr.Z,cpsr.C,cpsr.V))`;

val write_flags_def = Define`
  write_flags ii (n,z,c,v) =
    read_cpsr ii >>=
    (\cpsr. write_cpsr ii (cpsr with <| N := n; Z := z; C := c; V := v |>))`;

val read_cflag_def = Define`
  read_cflag ii = read_flags ii >>= (\(n,z,c,v). constT c)`;

val set_q_def = Define`
  set_q ii =
    read_cpsr ii >>= (\cpsr. write_cpsr ii (cpsr with Q := T))`;

val read_ge_def = Define`
  read_ge ii = read_cpsr ii >>= (\cpsr. constT (cpsr.GE))`;

val write_ge_def = Define`
  write_ge ii ge =
    read_cpsr ii >>= (\cpsr. write_cpsr ii (cpsr with GE := ge))`;

val write_e_def = Define`
  write_e ii e =
    read_cpsr ii >>= (\cpsr. write_cpsr ii (cpsr with E := e))`;

val IT_advance_def = Define`
  IT_advance ii =
    read_arch ii >>=
    (\arch.
      condT (arch IN thumb2_support)
       (read_cpsr ii >>=
        (\cpsr.
           if (cpsr.IT = 0w) \/ cpsr.T then
             write_cpsr ii (cpsr with IT := ITAdvance cpsr.IT)
           else
             errorT "IT_advance: unpredictable")))`;

val cpsr_write_by_instr_def = zDefine`
  cpsr_write_by_instr ii (value:word32, bytemask:word4, affect_execstate:bool) =
    let value_mode = (4 >< 0) value in
      (current_mode_is_priviledged ii ||| is_secure ii ||| read_nsacr ii |||
       bad_mode ii value_mode) >>=
      (\(priviledged,is_secure,nsacr,badmode).
          if bytemask ' 0 /\ priviledged /\
             (badmode \/
              ~is_secure /\ (value_mode = 0b10110w) \/
              ~is_secure /\ (value_mode = 0b10001w) /\ nsacr.RFR)
          then
            errorT "cpsr_write_by_instr: unpredictable"
          else
            (read_sctlr ii ||| read_scr ii ||| read_cpsr ii) >>=
            (\(sctlr,scr,cpsr).
              let cpsr = word_modify (\i b.
                 if 27 <= i /\ i <= 31 /\ bytemask ' 3 \/
                    24 <= i /\ i <= 26 /\ bytemask ' 3 /\
                                          affect_execstate \/
                    16 <= i /\ i <= 19 /\ bytemask ' 2 \/
                    10 <= i /\ i <= 15 /\ bytemask ' 1 /\
                                          affect_execstate \/
                               (i = 9) /\ bytemask ' 1 \/
                               (i = 8) /\ bytemask ' 1 /\
                                          priviledged /\
                                          (is_secure \/ scr.AW) \/
                               (i = 7) /\ bytemask ' 0 /\ priviledged \/
                               (i = 6) /\ bytemask ' 0 /\
                                          priviledged /\
                                          (is_secure \/ scr.FW) /\
                                          (~sctlr.NMFI \/ ~(value ' 6)) \/
                               (i = 5) /\ bytemask ' 0 /\
                                          affect_execstate \/
                               (i < 5) /\ bytemask ' 0 /\
                                          priviledged
                 then value ' i else b) (encode_psr cpsr)
              in
                write_cpsr ii (decode_psr cpsr)))`;

val spsr_write_by_instr_def = zDefine`
  spsr_write_by_instr ii (value:word32, bytemask:word4) =
    (current_mode_is_user_or_system ii ||| bad_mode ii ((4 >< 0) value)) >>=
    (\(user_or_system,badmode).
        if user_or_system \/ bytemask ' 0 /\ badmode then
          errorT "spsr_write_by_instr: unpredictable"
        else
          read_spsr ii >>=
          (\spsr.
              let spsr = word_modify (\i b.
                   if 24 <= i /\ i <= 31 /\ bytemask ' 3 \/
                      16 <= i /\ i <= 19 /\ bytemask ' 2 \/
                       8 <= i /\ i <= 15 /\ bytemask ' 1 \/
                                 i <= 7  /\ bytemask ' 0
                   then value ' i else b) (encode_psr spsr)
              in
                write_spsr ii (decode_psr spsr)))`;

val integer_zero_divide_trapping_enabled_def = Define`
  integer_zero_divide_trapping_enabled ii =
    read_sctlr ii >>= (\sctlr. constT sctlr.DZ)`;

(* ------------------------------------------------------------------------ *)

val branch_write_pc_def = Define`
  branch_write_pc ii (address:word32) =
    current_instr_set ii >>=
    (\iset.
       if iset = InstrSet_ARM then
         arch_version ii >>=
         (\version.
           if version < 6 /\ ((1 >< 0) address <> 0w:word2)
           then
             errorT "branch_write_pc: unpredictable"
           else
             branch_to ii ((31 '' 2) address))
       else
         branch_to ii ((31 '' 1) address))`;

val bx_write_pc_def = Define`
  bx_write_pc ii (address:word32) =
    current_instr_set ii >>=
    (\iset.
      if iset = InstrSet_ThumbEE then
        if address ' 0 then
          branch_to ii ((31 '' 1) address)
        else
          errorT "bx_write_pc: unpredictable"
      else
        if address ' 0 then
          select_instr_set ii InstrSet_Thumb >>=
          (\u. branch_to ii ((31 '' 1) address))
        else if ~(address ' 1) then
          select_instr_set ii InstrSet_ARM >>=
          (\u. branch_to ii address)
        else (* address<1:0> = '10' *)
          errorT "bx_write_pc: unpredictable")`;

val load_write_pc_def = Define`
  load_write_pc ii (address:word32) =
    arch_version ii >>=
    (\version.
       if version >= 5 then
         bx_write_pc ii address
       else
         branch_write_pc ii address)`;

val alu_write_pc_def = Define`
  alu_write_pc ii (address:word32) =
    (arch_version ii ||| current_instr_set ii) >>=
    (\(version,iset).
       if version >= 7 /\ (iset = InstrSet_ARM) then
         bx_write_pc ii address
       else
         branch_write_pc ii address)`;

(* ------------------------------------------------------------------------ *)

val decode_imm_shift_def = Define`
  decode_imm_shift (type:word2, imm5:word5) =
    case type
    of 0b00w => (SRType_LSL, w2n imm5)
     | 0b01w => (SRType_LSR, if imm5 = 0w then 32 else w2n imm5)
     | 0b10w => (SRType_ASR, if imm5 = 0w then 32 else w2n imm5)
     | 0b11w => if imm5 = 0w then
                  (SRType_RRX, 1)
                else
                  (SRType_ROR, w2n imm5)`;

val decode_reg_shift_def = Define`
  decode_reg_shift (type:word2) =
    case type
    of 0b00w => SRType_LSL
     | 0b01w => SRType_LSR
     | 0b10w => SRType_ASR
     | 0b11w => SRType_ROR`;

val shift_c_def = Define`
  shift_c (value:'a word, type:SRType, amount:num, carry_in:bool) =
    if (type = SRType_RRX) /\ (amount <> 1) then
      errorT "shift_c: RRX amount not 1"
    else
      constT
        (if amount = 0 then
          (value, carry_in)
         else
          (case type
           of SRType_LSL => LSL_C (value, amount)
            | SRType_LSR => LSR_C (value, amount)
            | SRType_ASR => ASR_C (value, amount)
            | SRType_ROR => ROR_C (value, amount)
            | SRType_RRX => RRX_C (value, carry_in)))`;

val shift_def = Define`
  shift (value:'a word, type:SRType, amount:num, carry_in:bool) =
    (shift_c (value, type, amount, carry_in)) >>=
    (\r. constT (FST r))`;

val arm_expand_imm_c_def = Define`
  arm_expand_imm_c (imm12:word12, carry_in:bool) =
    shift_c
      ((7 >< 0) imm12 : word32, SRType_ROR,
       2 * w2n ((11 -- 8) imm12), carry_in)`;

val arm_expand_imm_def = Define`
  arm_expand_imm ii (imm12:word12) =
    read_cflag ii >>=
    (\c.
      arm_expand_imm_c (imm12,c) >>=
      (\(imm32,c). constT imm32))`;

val thumb_expand_imm_c_def = Define`
  thumb_expand_imm_c (imm12:word12, carry_in:bool) : (word32 # bool) M =
    if (11 -- 10) imm12 = 0b00w then
      let imm8 = (7 >< 0) imm12 : word8 in
        case (9 >< 8) imm12 : word2
        of 0b00w =>
             constT (w2w imm8, carry_in)
         | 0b01w =>
             if imm8 = 0w then
               errorT "thumb_expand_imm_c: unpredictable"
             else
               constT (word32 [imm8; 0b00000000w; imm8; 0b00000000w], carry_in)
         | 0b10w =>
             if imm8 = 0w then
               errorT "thumb_expand_imm_c: unpredictable"
             else
               constT (word32 [0b00000000w; imm8; 0b00000000w; imm8], carry_in)
         | 0b11w =>
             if imm8 = 0w then
               errorT "thumb_expand_imm_c: unpredictable"
             else
               constT (word32 [imm8; imm8; imm8; imm8], carry_in)
    else
      let unrotated_value = (7 :+ T) ((6 >< 0) imm12) in
        constT (ROR_C (unrotated_value, w2n ((11 -- 7) imm12)))`;

(*
val thumb_expand_imm_def = Define`
  thumb_expand_imm ii (imm12:word12) =
    read_cflag ii >>=
    (\c.
      thumb_expand_imm_c (imm12,c) >>=
      (\(imm32,c). constT imm32))`;
*)

(* ------------------------------------------------------------------------ *)

val address_mode1_def = Define`
  (address_mode1 ii thumb2 (Mode1_immediate imm12) =
     read_cflag ii >>=
     (\c.
       if thumb2 then
         thumb_expand_imm_c (imm12,c)
       else
         arm_expand_imm_c (imm12,c))) /\
  (address_mode1 ii thumb2 (Mode1_register imm5 type rm) =
     (read_reg ii rm ||| read_cflag ii) >>=
     (\(rm,c).
        let (shift_t,shift_n) = decode_imm_shift (type,imm5) in
          shift_c (rm, shift_t, shift_n, c))) /\
  (address_mode1 ii thumb2 (Mode1_register_shifted_register rs type rm) =
     (read_reg ii rm ||| read_reg ii rs ||| read_cflag ii) >>=
     (\(rm,rs,c).
        let shift_t = decode_reg_shift type
        and shift_n = w2n ((7 -- 0) rs) in
          shift_c (rm, shift_t, shift_n, c)))`;

val address_mode2_def = Define`
  (address_mode2 ii indx add rn (Mode2_immediate imm12) =
     let imm32 = w2w imm12 in
     let offset_addr = if add then rn + imm32 else rn - imm32 in
       constT (offset_addr, if indx then offset_addr else rn)) /\
  (address_mode2 ii indx add rn (Mode2_register imm5 type rm) =
    (read_reg ii rm ||| read_cflag ii) >>=
    (\(rm,c).
      let (shift_t,shift_n) = decode_imm_shift (type,imm5) in
        shift (rm, shift_t, shift_n, c) >>=
        (\imm32.
           let offset_addr = if add then rn + imm32 else rn - imm32 in
             constT (offset_addr, if indx then offset_addr else rn))))`;

val address_mode3_def = Define`
  (address_mode3 ii indx add rn (Mode3_immediate imm12) =
    let imm32 = w2w imm12 in
    let offset_addr = if add then rn + imm32 else rn - imm32 in
      constT (offset_addr, if indx then offset_addr else rn)) /\
  (address_mode3 ii indx add rn (Mode3_register imm2 rm) =
    (read_reg ii rm ||| read_cflag ii) >>=
    (\(rm,c).
        shift (rm, SRType_LSL, w2n imm2, c) >>=
        (\imm32.
           let offset_addr = if add then rn + imm32 else rn - imm32 in
             constT (offset_addr, if indx then offset_addr else rn))))`;

val address_mode5_def = Define`
  address_mode5 indx add rn (imm8:word8) =
    let imm32 : word32 = (w2w imm8) << 2 in
    let offset_addr = if add then rn + imm32 else rn - imm32 in
      constT (offset_addr, if indx then offset_addr else rn)`;

(* ------------------------------------------------------------------------ *)

val data_processing_alu_def = Define`
  data_processing_alu (opc:word4) (a:word32) b c =
    case opc
    of 0b0000w => ( a && b ,  ARB, ARB)     (* AND *)
     | 0b0001w => ( a ?? b ,  ARB, ARB)     (* EOR *)
     | 0b0010w => add_with_carry( a,~b, T)  (* SUB *)
     | 0b0011w => add_with_carry(~a, b, T)  (* RSB *)
     | 0b0100w => add_with_carry( a, b, F)  (* ADD *)
     | 0b0101w => add_with_carry( a, b, c)  (* ADC *)
     | 0b0110w => add_with_carry( a,~b, c)  (* SBC *)
     | 0b0111w => add_with_carry(~a, b, c)  (* RSC *)
     | 0b1000w => ( a && b ,  ARB , ARB)    (* TST *)
     | 0b1001w => ( a ?? b ,  ARB , ARB)    (* TEQ *)
     | 0b1010w => add_with_carry( a,~b, T)  (* CMP *)
     | 0b1011w => add_with_carry( a, b, F)  (* CMN *)
     | 0b1100w => ( a || b ,  ARB , ARB)    (* ORR *)
     | 0b1101w => (      b ,  ARB , ARB)    (* MOV *)
     | 0b1110w => ( a && ~b , ARB , ARB)    (* BIC *)
     | _       => ( a || ~b , ARB , ARB)`;  (* MVN/ORN *)

val data_processing_thumb2_unpredictable_def = Define`
  (data_processing_thumb2_unpredictable
     (Data_Processing opc setflags n d (Mode1_immediate imm12)) =
   case opc
   of 0b0000w => (* AND *)
                 (d = 13w) \/ (d = 15w) /\ ~setflags \/ BadReg n
    | 0b0001w => (* EOR *)
                 (d = 13w) \/ (d = 15w) /\ ~setflags \/ BadReg n
    | 0b0010w => (* SUB *)
                 (if n = 13w then
                    (d = 15w) /\ ~setflags
                 else
                    (d = 13w) \/ (d = 15w) /\ ~setflags \/ (n = 15w))
    | 0b0100w => (* ADD *)
                 if n = 13w then
                   (d = 15w) /\ ~setflags
                 else
                   (d = 13w) \/ (d = 15w) /\ ~setflags \/ (n = 15w)
    | 0b0111w => T                                       (* RSC *)
    | 0b1000w => BadReg n                                (* TST *)
    | 0b1001w => BadReg n                                (* TEQ *)
    | 0b1010w => n = 15w                                 (* CMP *)
    | 0b1011w => n = 15w                                 (* CMN *)
    | 0b1101w => BadReg d                                (* MOV *)
    | 0b1111w => BadReg d \/ (n = 13w)                   (* MVN/ORN *)
    | _       => (* RSB,ADC,SBC,ORR,BIC *)
                 BadReg d \/ BadReg n) /\
  (data_processing_thumb2_unpredictable
     (Data_Processing opc setflags n d (Mode1_register imm5 typ m)) =
   case opc
   of 0b0000w => (* AND *)
                 (d = 13w) \/ (d = 15w) /\ ~setflags \/ BadReg n
    | 0b0001w => (* EOR *)
                 (d = 13w) \/ (d = 15w) /\ ~setflags \/ BadReg n
    | 0b0010w => (* SUB *)
                 if n = 13w then
                   (d = 13w) /\ (typ <> 0w \/ w2n imm5 > 3) \/
                   (d = 15w) \/ BadReg m
                 else
                   (d = 13w) \/ (d = 15w) /\ ~setflags \/ (n = 15w) \/ BadReg m
    | 0b0100w => (* ADD *)
                 if n = 13w then
                   (d = 13w) /\ (typ <> 0w \/ w2n imm5 > 3) \/
                   (d = 15w) \/ BadReg m
                 else
                   (d = 13w) \/ (d = 15w) /\ ~setflags \/ (n = 15w) \/ BadReg m
    | 0b0111w => T                                       (* RSC *)
    | 0b1000w => BadReg n \/ BadReg m                    (* TST *)
    | 0b1001w => BadReg n \/ BadReg m                    (* TEQ *)
    | 0b1010w => (n = 15w) \/ BadReg m                   (* CMP *)
    | 0b1011w => (n = 15w) \/ BadReg m                   (* CMN *)
    | 0b1101w => (* MOV *)
                 if setflags then
                   BadReg d \/ BadReg m
                 else
                   (d = 15w) \/ (m = 15w) \/ (d = 13w) /\ (m = 13w)
    | 0b1111w => BadReg d \/ (n = 13w) \/ BadReg m       (* MVN/ORN *)
    | _       => (* RSB,ADC,SBC,ORR,BIC *)
                 BadReg d \/ BadReg n \/ BadReg m) /\
  (data_processing_thumb2_unpredictable
     (Data_Processing opc setflags n d
        (Mode1_register_shifted_register s typ m)) =
     opc <> 0b1101w \/ BadReg d \/ BadReg s \/ BadReg m)`;

val _ = temp_overload_on ("top_half", ``( 31 >< 16 ) : word32 -> word16``);
val _ = temp_overload_on ("bot_half", ``( 15 >< 0  ) : word32 -> word16``);

val signed_parallel_add_sub_16_def = Define`
  signed_parallel_add_sub_16 op2 rn rm =
    let bn = SInt (bot_half rn) and bm = SInt (bot_half rm)
    and tn = SInt (top_half rn) and tm = SInt (top_half rm)
    in
      case op2
      of Parallel_add_16           => (bn + bm, tn + tm)
       | Parallel_add_sub_exchange => (bn - tm, tn + bm)
       | Parallel_sub_add_exchange => (bn + tm, tn - bm)
       | Parallel_sub_16           => (bn - bm, tn - tm)`;

val signed_normal_add_sub_16_def = Define`
  signed_normal_add_sub_16 op2 rn rm : word32 # word4 option =
    let (r1,r2) = signed_parallel_add_sub_16 op2 rn rm in
    let ge1 = if r1 >= 0i then 0b11w else 0b00w : word2
    and ge2 = if r2 >= 0i then 0b11w else 0b00w : word2
    in
      ((i2w r2 : word16) @@ (i2w r1 : word16), SOME (ge2 @@ ge1))`;

val signed_saturating_add_sub_16_def = Define`
  signed_saturating_add_sub_16 op2 rn rm : word32 # word4 option =
    let (r1,r2) = signed_parallel_add_sub_16 op2 rn rm in
      ((signed_sat (r2,16) : word16) @@ (signed_sat (r1,16) : word16), NONE)`;

val signed_halving_add_sub_16_def = Define`
  signed_halving_add_sub_16 op2 rn rm : word32 # word4 option =
    let (r1,r2) = signed_parallel_add_sub_16 op2 rn rm in
      ((i2w (r2 / 2) : word16) @@ (i2w (r1 / 2) : word16), NONE)`;

val signed_parallel_add_sub_8_def = Define`
  signed_parallel_add_sub_8 op2 rn rm =
    let n = MAP SInt (bytes (rn,4))
    and m = MAP SInt (bytes (rm,4))
    in
      case op2 of Parallel_add_8 => MAP (UNCURRY $+) (ZIP (n,m))
                | Parallel_sub_8 => MAP (UNCURRY $-) (ZIP (n,m))`;

val signed_normal_add_sub_8_def = Define`
  signed_normal_add_sub_8 op2 rn rm : word32 # word4 option =
    let r = signed_parallel_add_sub_8 op2 rn rm in
    let ge = FCP i. EL i r >= 0i in
      (word32 (MAP i2w r), SOME ge)`;

val signed_saturating_add_sub_8_def = Define`
  signed_saturating_add_sub_8 op2 rn rm : word32 # word4 option =
    (word32 (MAP (\i. signed_sat (i,8)) (signed_parallel_add_sub_8 op2 rn rm)),
     NONE)`;

val signed_halving_add_sub_8_def = Define`
  signed_halving_add_sub_8 op2 rn rm : word32 # word4 option =
   (word32 (MAP (\i. i2w (i / 2))
      (signed_parallel_add_sub_8 op2 rn rm)), NONE)`;

val unsigned_parallel_add_sub_16_def = Define`
  unsigned_parallel_add_sub_16 op2 rn rm =
    let bn = UInt (bot_half rn) and bm = UInt (bot_half rm)
    and tn = UInt (top_half rn) and tm = UInt (top_half rm)
    in
      case op2
      of Parallel_add_16           => (bn + bm, tn + tm)
       | Parallel_add_sub_exchange => (bn - tm, tn + bm)
       | Parallel_sub_add_exchange => (bn + tm, tn - bm)
       | Parallel_sub_16           => (bn - bm, tn - tm)`;

val unsigned_normal_add_sub_16_def = Define`
  unsigned_normal_add_sub_16 op2 rn rm : word32 # word4 option  =
    let (r1,r2) = unsigned_parallel_add_sub_16 op2 rn rm in
    let (ge1:word2,ge2:word2) =
          case op2
          of Parallel_add_16 =>
              (if r1 >= 0x10000i then 0b11w else 0b00w,
               if r2 >= 0x10000i then 0b11w else 0b00w)
           | Parallel_add_sub_exchange =>
              (if r1 >= 0i       then 0b11w else 0b00w,
               if r2 >= 0x10000i then 0b11w else 0b00w)
           | Parallel_sub_add_exchange =>
              (if r1 >= 0x10000i then 0b11w else 0b00w,
               if r2 >= 0i       then 0b11w else 0b00w)
           | Parallel_sub_16 =>
              (if r1 >= 0i       then 0b11w else 0b00w,
               if r2 >= 0i       then 0b11w else 0b00w)
    in
      ((i2w r2 : word16) @@ (i2w r1 : word16), SOME (ge2 @@ ge1))`;

val unsigned_saturating_add_sub_16_def = Define`
  unsigned_saturating_add_sub_16 op2 rn rm : word32 # word4 option =
    let (r1,r2) = unsigned_parallel_add_sub_16 op2 rn rm in
      ((unsigned_sat (r2,16) : word16) @@ (unsigned_sat (r1,16) : word16),
       NONE)`;

val unsigned_halving_add_sub_16_def = Define`
  unsigned_halving_add_sub_16 op2 rn rm : word32 # word4 option =
    let (r1,r2) = unsigned_parallel_add_sub_16 op2 rn rm in
      ((i2w (r2 / 2) : word16) @@ (i2w (r1 / 2) : word16), NONE)`;

val unsigned_parallel_add_sub_8_def = Define`
  unsigned_parallel_add_sub_8 op2 rn rm =
    let n = MAP UInt (bytes (rn,4))
    and m = MAP UInt (bytes (rm,4))
    in
      case op2 of Parallel_add_8 => MAP (UNCURRY $+) (ZIP (n,m))
                | Parallel_sub_8 => MAP (UNCURRY $-) (ZIP (n,m))`;

val unsigned_normal_add_sub_8_def = Define`
  unsigned_normal_add_sub_8 op2 rn rm : word32 # word4 option =
    let r = unsigned_parallel_add_sub_8 op2 rn rm
    and ge_lim = case op2 of Parallel_add_8 => 0x100i
                           | Parallel_sub_8 => 0i
    in
    let ge:word4 = FCP i. EL i r >= ge_lim in
      (word32 (MAP i2w r), SOME ge)`;

val unsigned_saturating_add_sub_8_def = Define`
  unsigned_saturating_add_sub_8 op2 rn rm : word32 # word4 option =
    (word32
       (MAP (\i. unsigned_sat (i,8))
          (unsigned_parallel_add_sub_8 op2 rn rm)), NONE)`;

val unsigned_halving_add_sub_8_def = Define`
  unsigned_halving_add_sub_8 op2 rn rm : word32 # word4 option =
    (word32 (MAP (\i. i2w (i / 2)) (unsigned_parallel_add_sub_8 op2 rn rm)),
     NONE)`;

val parallel_add_sub_def = Define`
  parallel_add_sub u (op1,op2) rn rm =
    case (u,op1,op2)
    of (F,Parallel_normal,Parallel_add_8) =>
         signed_normal_add_sub_8 op2 rn rm
     | (F,Parallel_normal,Parallel_sub_8) =>
         signed_normal_add_sub_8 op2 rn rm
     | (F,Parallel_normal,_) =>
         signed_normal_add_sub_16 op2 rn rm
     | (F,Parallel_saturating,Parallel_add_8) =>
         signed_saturating_add_sub_8 op2 rn rm
     | (F,Parallel_saturating,Parallel_sub_8) =>
         signed_saturating_add_sub_8 op2 rn rm
     | (F,Parallel_saturating,_) =>
         signed_saturating_add_sub_16 op2 rn rm
     | (F,Parallel_halving,Parallel_add_8) =>
         signed_halving_add_sub_8 op2 rn rm
     | (F,Parallel_halving,Parallel_sub_8) =>
         signed_halving_add_sub_8 op2 rn rm
     | (F,Parallel_halving,_) =>
         signed_halving_add_sub_16 op2 rn rm
     | (T,Parallel_normal,Parallel_add_8) =>
         unsigned_normal_add_sub_8 op2 rn rm
     | (T,Parallel_normal,Parallel_sub_8) =>
         unsigned_normal_add_sub_8 op2 rn rm
     | (T,Parallel_normal,_) =>
         unsigned_normal_add_sub_16 op2 rn rm
     | (T,Parallel_saturating,Parallel_add_8) =>
         unsigned_saturating_add_sub_8 op2 rn rm
     | (T,Parallel_saturating,Parallel_sub_8) =>
         unsigned_saturating_add_sub_8 op2 rn rm
     | (T,Parallel_saturating,_) =>
         unsigned_saturating_add_sub_16 op2 rn rm
     | (T,Parallel_halving,Parallel_add_8) =>
         unsigned_halving_add_sub_8 op2 rn rm
     | (T,Parallel_halving,Parallel_sub_8) =>
         unsigned_halving_add_sub_8 op2 rn rm
     | (T,Parallel_halving,_) =>
         unsigned_halving_add_sub_16 op2 rn rm`;

(* ------------------------------------------------------------------------ *)

val barrier_option_def = Define`
  barrier_option (option:word4) =
    case option
    of 0b0010w => (MBReqDomain_OuterShareable, MBReqTypes_Writes)
     | 0b0011w => (MBReqDomain_OuterShareable, MBReqTypes_All)
     | 0b0110w => (MBReqDomain_Nonshareable,   MBReqTypes_Writes)
     | 0b0111w => (MBReqDomain_Nonshareable,   MBReqTypes_All)
     | 0b1010w => (MBReqDomain_InnerShareable, MBReqTypes_Writes)
     | 0b1011w => (MBReqDomain_InnerShareable, MBReqTypes_All)
     | 0b1110w => (MBReqDomain_FullSystem,     MBReqTypes_Writes)
     | _       => (MBReqDomain_FullSystem,     MBReqTypes_All)`;

(* ------------------------------------------------------------------------ *)

val exc_vector_base_def = Define`
  exc_vector_base ii : word32 M =
    read_sctlr ii >>=
    (\sctlr.
      if sctlr.V then
        constT 0xFFFF0000w
      else
        (have_security_ext ii >>=
         (\have_security_exta.
            if have_security_exta then
              read_vbar ii
            else
              constT 0w)))`;

val take_reset_def = Define`
  take_reset ii =
    (exc_vector_base ii ||| have_security_ext ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(ExcVectorBase,have_security_exta,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b10011w)) >>=
       (\(u1:unit,u2:unit).
         ((read_cpsr ii >>=
          (\cpsr.
             write_cpsr ii (cpsr with
               <| I := T;
                  IT := 0b00000000w;
                  J := F; T := sctlr.TE;
                  E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 0w)) >>= unit2))`;

val take_undef_instr_exception_def = Define`
  take_undef_instr_exception ii =
    (read_reg ii 15w ||| exc_vector_base ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(pc,ExcVectorBase,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b11011w)) >>=
       (\(u1:unit,u2:unit).
         (write_spsr ii cpsr |||
          write_reg ii 14w (if cpsr.T then pc - 2w else pc - 4w) |||
          (read_cpsr ii >>=
           (\cpsr.
              write_cpsr ii (cpsr with
                <| I := T;
                   IT := 0b00000000w;
                   J := F; T := sctlr.TE;
                   E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 4w)) >>= unit4))`;

val take_svc_exception_def = Define`
  take_svc_exception ii =
    IT_advance ii >>=
    (\u:unit.
      (read_reg ii 15w ||| exc_vector_base ii |||
       read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
      (\(pc,ExcVectorBase,cpsr,scr,sctlr).
         (condT (cpsr.M = 0b10110w)
            (write_scr ii (scr with NS := F)) |||
          write_cpsr ii (cpsr with M := 0b10011w)) >>=
         (\(u1:unit,u2:unit).
           (write_spsr ii cpsr |||
            write_reg ii 14w (if cpsr.T then pc - 2w else pc - 4w) |||
            (read_cpsr ii >>=
             (\cpsr.
                write_cpsr ii (cpsr with
                  <| I := T;
                     IT := 0b00000000w;
                     J := F; T := sctlr.TE;
                     E := sctlr.EE |>))) |||
            branch_to ii (ExcVectorBase + 8w)) >>= unit4)))`;

val take_smc_exception_def = Define`
  take_smc_exception ii =
    IT_advance ii >>=
    (\u:unit.
      (read_reg ii 15w ||| read_mvbar ii |||
       read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
      (\(pc,mvbar,cpsr,scr,sctlr).
         (condT (cpsr.M = 0b10110w)
            (write_scr ii (scr with NS := F)) |||
          write_cpsr ii (cpsr with M := 0b10110w)) >>=
         (\(u1:unit,u2:unit).
           (write_spsr ii cpsr |||
            write_reg ii 14w (if cpsr.T then pc else pc - 4w) |||
            (read_cpsr ii >>=
             (\cpsr.
                write_cpsr ii (cpsr with
                  <| I := T; F := T; A := T;
                     IT := 0b00000000w;
                     J := F; T := sctlr.TE;
                     E := sctlr.EE |>))) |||
            branch_to ii (mvbar + 8w)) >>= unit4)))`;

(* For now assume trap_to_monitor is false, i.e. no external aborts *)
val take_prefetch_abort_exception_def = Define`
  take_prefetch_abort_exception ii =
    (read_reg ii 15w ||| exc_vector_base ii ||| have_security_ext ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(pc,ExcVectorBase,have_security_exta,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b10111w)) >>=
       (\(u1:unit,u2:unit).
         (write_spsr ii cpsr |||
          write_reg ii 14w (if cpsr.T then pc else pc - 4w) |||
          (read_cpsr ii >>=
           (\cpsr.
              write_cpsr ii (cpsr with
                <| I := T;
                   A := ((~have_security_exta \/ ~scr.NS \/ scr.AW) \/ cpsr.A);
                   IT := 0b00000000w;
                   J := F; T := sctlr.TE;
                   E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 12w)) >>= unit4))`;


val take_data_abort_exception_def = Define`
  take_data_abort_exception ii =
    (read_reg ii 15w ||| exc_vector_base ii ||| have_security_ext ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(pc,ExcVectorBase,have_security_exta,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b10111w)) >>=
       (\(u1:unit,u2:unit).
         (write_spsr ii cpsr |||
          write_reg ii 14w (if cpsr.T then pc else pc - 4w) |||
          (read_cpsr ii >>=
           (\cpsr.
              write_cpsr ii (cpsr with
                <| I := T;
                   A := ((~have_security_exta \/ ~scr.NS \/ scr.AW) \/ cpsr.A);
                   IT := 0b00000000w;
                   J := F; T := sctlr.TE;
                   E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 16w)) >>= unit4))`;


val take_irq_exception_def = Define`
  take_irq_exception ii =
    (read_reg ii 15w ||| exc_vector_base ii ||| have_security_ext ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(pc,ExcVectorBase,have_security_exta,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b10010w)) >>=
       (\(u1:unit,u2:unit).
         (write_spsr ii cpsr |||
          write_reg ii 14w (if cpsr.T then pc else pc - 4w) |||
          (read_cpsr ii >>=
           (\cpsr.
              write_cpsr ii (cpsr with
                <| I := T;
                   A := ((~have_security_exta \/ ~scr.NS \/ scr.AW) \/ cpsr.A);
                   IT := 0b00000000w;
                   J := F; T := sctlr.TE;
                   E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 24w)) >>= unit4))`;

val take_fiq_exception_def = Define`
  take_fiq_exception ii =
    (read_reg ii 15w ||| exc_vector_base ii ||| have_security_ext ii |||
     read_cpsr ii ||| read_scr ii ||| read_sctlr ii) >>=
    (\(pc,ExcVectorBase,have_security_exta,cpsr,scr,sctlr).
       (condT (cpsr.M = 0b10110w)
          (write_scr ii (scr with NS := F)) |||
        write_cpsr ii (cpsr with M := 0b10001w)) >>=
       (\(u1:unit,u2:unit).
         (write_spsr ii cpsr |||
          write_reg ii 14w (if cpsr.T then pc else pc - 4w) |||
          (read_cpsr ii >>=
           (\cpsr.
              write_cpsr ii (cpsr with
                <| I := T;
                   F := ((~have_security_exta \/ ~scr.NS \/ scr.AW) \/ cpsr.F);
                   A := ((~have_security_exta \/ ~scr.NS \/ scr.AW) \/ cpsr.A);
                   IT := 0b00000000w;
                   J := F; T := sctlr.TE;
                   E := sctlr.EE |>))) |||
          branch_to ii (ExcVectorBase + 28w)) >>= unit4))`;

(* ------------------------------------------------------------------------ *)

val null_check_if_thumbee_def = Define`
  null_check_if_thumbEE ii n (f:unit M) =
    current_instr_set ii >>=
    (\iset.
      if iset = InstrSet_ThumbEE then
        read_reg ii n >>=
        (\rn.
          if n = 15w then
            if align (rn, 4) = 0w then
              errorT ("null_check_if_thumbEE PC: unpredictable")
            else
              f
          else if n = 13w then
            if rn = 0w then
              errorT ("null_check_if_thumbEE SP: unpredictable")
            else
              f
          else if rn = 0w then
            (read_reg ii 15w ||| read_cpsr ii ||| read_teehbr ii) >>=
            (\(pc,cpsr,teehbr).
               (write_reg ii 14w ((0 :+ T) pc) |||
                write_cpsr ii (cpsr with IT := 0w)) >>=
               (\(u1:unit, u2:unit).
                 branch_write_pc ii (teehbr - 4w)))
          else
            f)
      else
        f)`;

val run_instruction_def = Define`
  run_instruction ii s n defined unpredictable c =
    read_info ii >>=
    (\info.
       if (info.arch,info.extensions) NOTIN defined then
         take_undef_instr_exception ii
       else if unpredictable (version_number info.arch) then
         errorT (s ++ ": unpredictable")
       else if IS_SOME n then
         null_check_if_thumbEE ii (THE n) c
       else
         c)`;

val null_check_instruction_def = Define`
  null_check_instruction ii s n defined unpredictable c =
    run_instruction ii s (SOME n) defined unpredictable c`;

val instruction_def = Define`
  instruction ii s defined unpredictable c =
    run_instruction ii s NONE defined unpredictable c`;

val instructions = ref ([] : (string * thm) list);

fun iDefine t =
let
  val thm = zDefine t
  val name = (fst o dest_const o fst o strip_comb o lhs o concl o SPEC_ALL) thm
  val _ = instructions := (name,thm) :: !instructions
in
  thm
end;

(* ........................................................................
   T,A: B<c>   <label>
   T2:  B<c>.W <label>
   ```````````````````````````````````````````````````````````````````````` *)
val branch_target_instr_def = iDefine`
  branch_target_instr ii enc (Branch_Target imm24) =
    instruction ii "branch_target" ALL {}
      (read_reg ii 15w >>=
       (\pc.
          let imm32 = sw2sw imm24 << (if enc = Encoding_ARM then 2 else 1) in
            branch_write_pc ii (pc + imm32)))`;

(* ........................................................................
   T,A: BX<c> <Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val branch_exchange_instr_def = iDefine`
  branch_exchange_instr ii (Branch_Exchange m) =
    instruction ii "branch_exchange" (ARCH {a | a <> ARMv4}) {}
      (read_reg ii m >>= (\rm. bx_write_pc ii rm))`;

(* ........................................................................
   T,A: BL<c>  <label>
   T,A: BLX<c> <label>
   ```````````````````````````````````````````````````````````````````````` *)
(* If toARM = F then Unpredictable for ARMv4*. *)
val branch_link_exchange_imm_instr_def = iDefine`
  branch_link_exchange_imm_instr ii enc
      (Branch_Link_Exchange_Immediate H toARM imm24) =
    instruction ii "branch_link_exchange_imm"
      (if (enc = Encoding_Thumb2) /\ toARM \/
          (enc = Encoding_ARM) /\ ~toARM
       then
         ARCH {a | version_number a >= 5}
       else
         ALL) {}
      (current_instr_set ii >>=
       (\CurrentInstrSet.
          if toARM /\ (CurrentInstrSet = InstrSet_ThumbEE) then
            take_undef_instr_exception ii
          else
            let targetInstrSet =
                  if toARM then
                    InstrSet_ARM
                  else if enc = Encoding_ARM then
                    InstrSet_Thumb
                  else
                    CurrentInstrSet
            and imm32 = sw2sw imm24 << 2 in
            let imm32 = if toARM then imm32 else (1 :+ H) imm32
            in
              read_reg ii 15w >>=
              (\pc.
                (if CurrentInstrSet = InstrSet_ARM then
                   write_reg ii 14w (pc - 4w)
                 else
                   write_reg ii 14w ((0 :+ T) pc)) >>=
                (\u. let targetAddress = if targetInstrSet = InstrSet_ARM then
                                           align(pc,4) + imm32
                                         else
                                           pc + imm32
                     in
                       select_instr_set ii targetInstrSet >>=
                       (\u. branch_write_pc ii targetAddress)))))`;

(* ........................................................................
   T,A: BLX<c> <Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val branch_link_exchange_reg_instr_def = iDefine`
  branch_link_exchange_reg_instr ii (Branch_Link_Exchange_Register m) =
    instruction ii "branch_link_exchange_reg"
      (ARCH {a | version_number a >= 5}) {}
      ((read_reg ii 15w ||| read_reg ii m ||| current_instr_set ii) >>=
       (\(pc,rm,iset).
         let next_instr_addr =
                if iset = InstrSet_ARM
                  then pc - 4w
                  else pc - 2w
         in
           (if iset = InstrSet_ARM then
              write_reg ii 14w next_instr_addr
            else
              write_reg ii 14w ((0 :+ T) next_instr_addr)) >>=
           (\u. bx_write_pc ii rm)))`;

(* ........................................................................
   T: CB{N}Z <Rn>,<label>
   ```````````````````````````````````````````````````````````````````````` *)
val compare_branch_instr_def = iDefine`
  compare_branch_instr ii (Compare_Branch nonzero imm6 n) =
    instruction ii "compare_branch" (ARCH thumb2_support) {}
      (read_reg ii (w2w n) >>=
       (\rn.
          if nonzero <=/=> (rn = 0w) then
            read_reg ii 15w >>=
            (\pc.
              let imm32 = w2w imm6 << 1 in
                branch_write_pc ii (pc + imm32))
          else
            increment_pc ii Encoding_Thumb))`;

(* ........................................................................
   T2: TBB<c> [<Rn>,<Rm>]
   T2: TBH<c> [<Rn>,<Rm>,LSL #1]
   ```````````````````````````````````````````````````````````````````````` *)
val table_branch_byte_instr_def = iDefine`
  table_branch_byte_instr ii (Table_Branch_Byte n is_tbh m) =
    null_check_instruction ii "table_branch_byte" n (ARCH thumb2_support)
      (\v. (n = 13w) \/ BadReg m)
      ((read_reg ii 15w ||| read_reg ii n ||| read_reg ii m) >>=
       (\(pc,rn,rm).
         (if is_tbh then
            read_memU ii (rn + LSL(rm,1), 2)
          else
            read_memU ii (rn + rm, 1)) >>=
         (\halfwords.
             branch_write_pc ii (pc + 2w * zero_extend32 halfwords))))`;

(* ........................................................................
   TX: CHKA<c> <Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val check_array_instr_def = iDefine`
  check_array_instr ii (Check_Array n m) =
    instruction ii "check_array" thumbee_support
      (\v. (n = 15w) \/ BadReg m)
      ((read_reg ii 15w ||| read_reg ii n ||| read_reg ii m |||
        read_cpsr ii ||| read_teehbr ii) >>=
       (\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg ii 14w ((0 :+ T) pc) |||
              write_cpsr ii (cpsr with IT := 0w)) >>=
             (\(u1:unit,u2:unit).
               branch_write_pc ii (teehbr - 8w)))
          else
            increment_pc ii Encoding_ThumbEE))`;

(* ........................................................................
   TX: HB{L}<c> #<HandlerID>
   ```````````````````````````````````````````````````````````````````````` *)
val handler_branch_link_instr_def = iDefine`
  handler_branch_link_instr ii (Handler_Branch_Link generate_link handler) =
    instruction ii "handler_branch_link" thumbee_support {}
      ((read_reg ii 15w ||| read_teehbr ii) >>=
       (\(pc,teehbr).
          let handler_offset = w2w handler << 5 in
            condT (generate_link)
              (let next_instr_addr = pc - 2w in
                 write_reg ii 14w ((0 :+ T) next_instr_addr)) >>=
            (\u:unit.
              branch_write_pc ii (teehbr + handler_offset))))`;

(* ........................................................................
   TX: HBLP<c> #<imm>,#<HandlerID>
   ```````````````````````````````````````````````````````````````````````` *)
val handler_branch_link_parameter_instr_def = iDefine`
  handler_branch_link_parameter_instr ii
    (Handler_Branch_Link_Parameter imm5 handler) =
    instruction ii "handler_branch_link_parameter" thumbee_support {}
      ((read_reg ii 15w ||| read_teehbr ii) >>=
       (\(pc,teehbr).
          let next_instr_addr = pc - 2w
          and handler_offset = w2w handler << 5
          in
            (write_reg ii 8w (w2w imm5) |||
             write_reg ii 14w ((0 :+ T) next_instr_addr)) >>=
            (\(u1:unit,u2:unit).
              branch_write_pc ii (teehbr + handler_offset))))`;

(* ........................................................................
   TX: HBP<c> #<imm>,#<HandlerID>
   ```````````````````````````````````````````````````````````````````````` *)
val handler_branch_parameter_instr_def = iDefine`
  handler_branch_parameter_instr ii (Handler_Branch_Parameter imm3 handler) =
    instruction ii "handler_branch_link_parameter" thumbee_support {}
      (read_teehbr ii >>=
       (\teehbr.
          let handler_offset = w2w handler << 5 in
            write_reg ii 8w (w2w imm3) >>=
            (\u:unit.
              branch_write_pc ii (teehbr + handler_offset))))`;

(* ........................................................................
   T2: ENTERX
   T2: LEAVEX
   ```````````````````````````````````````````````````````````````````````` *)
val enterx_leavex_def = iDefine`
  enterx_leavex_instr ii is_enterx =
    instruction ii "enterx_leavex" thumbee_support {}
      ((if is_enterx then
          select_instr_set ii InstrSet_ThumbEE
        else
          select_instr_set ii InstrSet_Thumb) >>=
        (\u:unit. increment_pc ii Encoding_Thumb2))`;

(* ........................................................................
   T: IT{<x>{<y>{<z>}}} <firstcond>
   where <x>, <y> and <z> are T or E.
   ```````````````````````````````````````````````````````````````````````` *)
val if_then_instr_def = iDefine`
  if_then_instr ii (If_Then firstcond mask) =
    instruction ii "if_then" (ARCH thumb2_support)
      (\v. (mask = 0w) \/ (firstcond = 0b1111w) \/
           (firstcond = 0b1110w) /\ (bit_count mask <> 1))
      (read_cpsr ii >>=
       (\cpsr.
          (increment_pc ii Encoding_Thumb |||
           write_cpsr ii (cpsr with IT := (firstcond @@ mask))) >>= unit2))`;

(* ........................................................................
   T2,A: CLZ<c> <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val count_leading_zeroes_instr_def = iDefine`
  count_leading_zeroes_instr ii enc (Count_Leading_Zeroes d m) =
    instruction ii "count_leading_zeroes"
      (ARCH2 enc {a | version_number a >= 5})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (read_reg ii m >>=
       (\rm.
          (increment_pc ii enc |||
           write_reg ii d (n2w (count_leading_zeroes rm))) >>=
          unit2))`;

(* ........................................................................
   T2,A: MOVW<c> <Rd>,#<imm16>
   T2,A: MOVT<c> <Rd>,#<imm16>
   ```````````````````````````````````````````````````````````````````````` *)
val move_halfword_instr_def = iDefine`
  move_halfword_instr ii enc (Move_Halfword high d imm16) =
    instruction ii "move_halfword" (ARCH thumb2_support)
      (\v. if enc = Encoding_Thumb2 then BadReg d else d = 15w)
      ((if high then
          read_reg ii d >>= (\rd. constT (imm16 @@ bot_half rd))
        else
          constT (w2w imm16)) >>=
       (\result.
          (increment_pc ii enc ||| write_reg ii d result) >>= unit2))`;

(* ........................................................................
   T,A:    ADR<c>    <Rd>,<label>
   T2:     ADR<c>.W  <Rd>,<label>
   T,T2,A: ADD<c><q> <Rd>, PC, #<const>
   T2,A :  SUB<c><q> <Rd>, PC, #<const>
   T2 :    ADDW<c>   <Rd>, <Rn>, #<imm12>
   T2 :    SUBW<c>   <Rd>, <Rn>, #<imm12>
   ```````````````````````````````````````````````````````````````````````` *)
val add_sub_instr_def = iDefine`
  add_sub_instr ii enc (Add_Sub add n d imm12) =
    instruction ii "add_sub"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\v. (enc = Encoding_Thumb2) /\ if n = 13w then d = 15w else BadReg d)
      ((read_reg_literal ii n |||
        (if enc = Encoding_ARM then
           arm_expand_imm ii imm12
         else
           constT (w2w imm12))) >>=
       (\(rn,imm32).
          let result = if add then rn + imm32 else rn - imm32 in
            if d = 15w then
              alu_write_pc ii result
            else
              (increment_pc ii enc ||| write_reg ii d result) >>= unit2))`;

(* ........................................................................
   For opc in {AND,EOR,ADC,SBC,ORR,BIC}
   T2,A: <opc>{S}<c>   <Rd>,<Rn>,#<const>
   T:    <opc>S        <Rd>,<Rm>                  (Outside IT block)
   T:    <opc><c>      <Rd>,<Rm>                  (Inside IT block)
   T2:   <opc>{S}<c>.W <Rd>,<Rn>,<Rm>{,<shift>}
   A:    <opc>{S}<c>   <Rd>,<Rn>,<Rm>{,<shift>}
   A:    <opc>{S}<c>   <Rd>,<Rn>,<Rm>,<type> <Rs>

   T:    ADDS        <Rd>,<Rn>,#<imm3>            (Outside IT block)
   T:    ADD<c>      <Rd>,<Rn>,#<imm3>            (Inside IT block)
   T:    ADDS        <Rdn>,#<imm8>                (Outside IT block)
   T:    ADD<c>      <Rdn>,#<imm8>                (Inside IT block)
   T2:   ADD{S}<c>.W <Rd>,<Rn>,#<const>
   A:    ADD{S}<c>   <Rd>,<Rn>,#<const>
   T:    ADDS        <Rd>,<Rn>,<Rm>               (Outside IT block)
   T:    ADD<c>      <Rd>,<Rn>,<Rm>               (Inside IT block)
   T:    ADD<c>      <Rdn>,<Rm>
   T2:   ADD{S}<c>.W <Rd>,<Rn>,<Rm>{,<shift>}
   A:    ADD{S}<c>   <Rd>,<Rn>,<Rm>{,<shift>}
   A:    ADD{S}<c>   <Rd>,<Rn>,<Rm>,<type> <Rs>

   T:    SUBS        <Rd>,<Rn>,#<imm3>            (Outside IT block)
   T:    SUB<c>      <Rd>,<Rn>,#<imm3>            (Inside IT block)
   T:    SUBS        <Rdn>,#<imm8>                (Outside IT block)
   T:    SUB<c>      <Rdn>,#<imm8>                (Inside IT block)
   T2:   SUB{S}<c>.W <Rd>,<Rn>,#<const>
   A:    SUB{S}<c>   <Rd>,<Rn>,#<const>
   T:    SUBS        <Rd>,<Rn>,<Rm>               (Outside IT block)
   T:    SUB<c>      <Rd>,<Rn>,<Rm>               (Inside IT block)
   T2:   SUB{S}<c>.W <Rd>,<Rn>,<Rm>{,<shift>}
   A:    SUB{S}<c>   <Rd>,<Rn>,<Rm>{,<shift>}
   A:    SUB{S}<c>   <Rd>,<Rn>,<Rm>,<type> <Rs>

   T:    RSBS        <Rd>,<Rn>,#0                 (Outside IT block)
   T:    RSB<c>      <Rd>,<Rn>,#0                 (Inside IT block)
   T2:   RSB{S}<c>.W <Rd>,<Rn>,#<const>
   A:    RSB{S}<c>   <Rd>,<Rn>,#<const>
   T2,A: RSB{S}<c>.W <Rd>,<Rn>,<Rm>{,<shift>}
   A:    RSB{S}<c>   <Rd>,<Rn>,<Rm>,<type> <Rs>

   A:    RSC{S}<c>   <Rd>,<Rn>,#<const>
   A:    RSC{S}<c>   <Rd>,<Rn>,<Rm>{,<shift>}
   A:    RSC{S}<c>   <Rd>,<Rn>,<Rm>,<type> <Rs>

   T2,A: TST<c>      <Rn>,#<const>
   T:    TST<c>      <Rn>,<Rm>
   T2:   TST<c>.W    <Rn>,<Rm>{,<shift>}
   A:    TST<c>      <Rn>,<Rm>{,<shift>}
   A:    TST<c>      <Rn>,<Rm>,<type> <Rs>

   T2,A: CMN<c>      <Rn>,#<const>
   T:    CMN<c>      <Rn>,<Rm>
   T2:   CMN<c>.W    <Rn>,<Rm>{,<shift>}
   A:    CMN<c>      <Rn>,<Rm>{,<shift>}
   A:    CMN<c>      <Rn>,<Rm>,<type> <Rs>

   T2,A: TEQ<c>      <Rn>,#<const>
   T2:   TEQ<c>      <Rn>,<Rm>{,<shift>}
   A:    TEQ<c>      <Rn>,<Rm>{,<shift>}
   A:    TEQ<c>      <Rn>,<Rm>,<type> <Rs>

   T:    CMP<c>      <Rn>,#<imm8>
   T2:   CMP<c>.W    <Rn>,#<const>
   A:    CMP<c>      <Rn>,#<const>
   T:    CMP<c>      <Rn>,<Rm>
   T2:   CMP<c>.W    <Rn>,<Rm>{,<shift>}
   A:    CMP<c>      <Rn>,<Rm>{,<shift>}
   A:    CMP<c>      <Rn>,<Rm>,<type> <Rs>

   T:    MOVS        <Rd>,#<imm8>                 (Outside IT block)
   T:    MOV<c>      <Rd>,#<imm8>                 (Inside IT block)
   T2:   MOV{S}<c>.W <Rd>,#<const>
   A:    MOV{S}<c>   <Rd>,#<const>
   T:    MOV         <Rd>,<Rm>                    (Outside IT block)
   T:    MOV<c>      <Rd>,<Rm>                    (Inside IT block)
   T:    MOVS        <Rd>,<Rm>                    (Outside IT block)
   T2:   MOV{S}<c>.W <Rd>,<Rm>{,<shift>}          (Covers LSL etc.)
   A:    MOV{S}<c>   <Rd>,<Rm>{,<shift>}          (Covers LSL etc.)
   A:    MOV{S}<c>   <Rd>,<Rm>,<type> <Rs>        (Covers LSL etc.)

   T2,A: MVN{S}<c>   <Rd>,#<const>
   T:    MVNS        <Rd>,<Rm>                    (Outside IT block)
   T:    MVN<c>      <Rd>,<Rm>                    (Inside IT block)
   T2:   MVN{S}<c>.W <Rn>,<Rm>{,<shift>}
   A:    MVN<c>      <Rn>,<Rm>{,<shift>}
   A:    MVN<c>      <Rn>,<Rm>,<type> <Rs>

   T2:   ORN{S}<c>   <Rd>,<Rn>,#<const>
   T2:   ORN{S}<c>   <Rn>,<Rn>,<Rm>{,<shift>}

   For opc in {LSL,LSR,ASR}
   T:    <opc>S        <Rd>,<Rm>,#<imm5>           (Outside IT block)
   T:    <opc><c>      <Rd>,<Rm>,#<imm5>           (Inside IT block)
   T2:   <opc>{S}<c>.W <Rd>,<Rm>,#<imm5>
   A:    <opc>{S}<c>   <Rd>,<Rm>,#<imm5>
   T:    <opc>S        <Rdn>,<Rm>                  (Outside IT block)
   T:    <opc><c>      <Rdn>,<Rm>                  (Inside IT block)
   T2:   <opc>{S}<c>.W <Rd>,<Rn>,<Rm>
   A:    <opc>{S}<c>   <Rd>,<Rn>,<Rm>
   T2,A: ROR{S}<c>     <Rd>,<Rm>,#<imm5>
   T:    RORS          <Rdn>,<Rm>                  (Outside IT block)
   T:    ROR<c>        <Rdn>,<Rm>                  (Inside IT block)
   T2:   ROR{S}<c>.W   <Rd>,<Rn>,<Rm>
   A:    ROR{S}<c>     <Rd>,<Rn>,<Rm>
   T2,A: RRX{S}<c>     <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val data_processing_instr_def = iDefine`
  data_processing_instr ii enc (Data_Processing opc setflags n d mode1) =
    let test_or_compare = ((3 -- 2 ) opc = 2w) in
      instruction ii "data_processing"
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\v. (enc = Encoding_Thumb2) /\
               data_processing_thumb2_unpredictable
                 (Data_Processing opc setflags n d mode1) \/
             (case mode1
              of Mode1_register_shifted_register s type m =>
                   (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ (s = 15w)
               | Mode1_immediate imm12 =>
                   opc IN {0b0010w; 0b0100w} /\ (n = 15w) /\ ~setflags
               | _ => F))
        (((if (opc = 0b1101w) \/
              (opc = 0b1111w) /\ (enc <> Encoding_Thumb2 \/ (n = 15w))
           then
             constT 0w
           else
             read_reg ii n) |||
           address_mode1 ii (enc = Encoding_Thumb2) mode1 |||
           read_flags ii) >>=
         (\(rn,(shifted,C_shift),(N,Z,C,V)).
           let (result,C_alu,V_alu) = data_processing_alu opc rn shifted C in
            ((if test_or_compare then
                increment_pc ii enc
              else if d = 15w then
                if setflags then
                  read_spsr ii >>=
                  (\spsr.
                     cpsr_write_by_instr ii (encode_psr spsr,0b1111w,T) >>=
                     (\u. branch_write_pc ii result))
                else
                  alu_write_pc ii result
              else
                (increment_pc ii enc ||| write_reg ii d result) >>= unit2) |||
             condT (setflags /\ ((d <> 15w) \/ test_or_compare))
                (if (opc ' 2 \/ opc ' 1) /\ (~opc ' 3 \/ ~opc ' 2)
                 then
                   write_flags ii (word_msb result,result = 0w,C_alu,V_alu)
                 else
                   write_flags ii (word_msb result,result = 0w,C_shift,V))) >>=
             unit2))`;

(* ........................................................................
   T:  MULS      <Rdm>,<Rn>,<Rdm>     (Outside IT block)
   T:  MUL<c>    <Rdm>,<Rn>,<Rdm>     (Inside IT block)
   T2: MUL<c>    <Rd>,<Rn>,<Rm>
   A:  MUL{S}<c> <Rd>,<Rn>,<Rm>
   T2: MLA<c>    <Rd>,<Rn>,<Rm>,<Ra>
   A:  MLA{S}<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val multiply_instr_def = iDefine`
  multiply_instr ii enc (Multiply acc setflags d a m n) =
    instruction ii "multiply"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\version.
          if enc = Encoding_Thumb2 then
            BadReg d \/ BadReg n \/ BadReg m \/ acc /\ (a = 13w)
          else
            (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ acc /\ (a = 15w) \/
            version < 6 /\ (d = n))
      ((read_reg ii a |||
        read_reg ii m |||
        read_reg ii n |||
        arch_version ii) >>=
       (\(ra,rm,rn,version).
          (let result = rn * rm + (if acc then ra else 0w) in
            (increment_pc ii enc |||
             write_reg ii d result |||
             condT setflags (read_flags ii >>=
             (\(N,Z,C,V).
                let C_flag = if version = 4 then UNKNOWN else C in
                  write_flags ii (word_msb result,result = 0w,C_flag,V)))) >>=
            unit3)))`;

(* ........................................................................
   T2: UMULL<c>    <RdLo>,<RdHi>,<Rn>,<Rm>
   A:  UMULL{S}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   T2: UMLAL<c>    <RdLo>,<RdHi>,<Rn>,<Rm>
   A:  UMLAL{S}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   T2: SMULL<c>    <RdLo>,<RdHi>,<Rn>,<Rm>
   A:  SMULL{S}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   T2: SMLAL<c>    <RdLo>,<RdHi>,<Rn>,<Rm>
   A:  SMLAL{S}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val multiply_long_instr_def = iDefine`
  multiply_long_instr ii enc (Multiply_Long signed acc setflags dhi dlo m n) =
    instruction ii "multiply_long"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\version.
         (if enc = Encoding_Thumb2 then
            BadReg dlo \/ BadReg dhi \/ BadReg n \/ BadReg m
          else
            (dlo = 15w) \/ (dhi = 15w) \/ (n = 15w) \/ (m = 15w) \/
            version < 6 /\ ((dhi = n) \/ (dlo = n))) \/
          (dhi = dlo))
      ((read_reg ii dhi |||
        read_reg ii dlo |||
        read_reg ii m |||
        read_reg ii n |||
        arch_version ii) >>=
       (\(rdhi,rdlo,rm,rn,version).
          (let result : word64 =
                 (if signed then sw2sw rn * sw2sw rm else w2w rn * w2w rm) +
                 (if acc then rdhi @@ rdlo else 0w)
           in
             (increment_pc ii enc |||
              write_reg ii dhi (( 63 >< 32 ) result) |||
              write_reg ii dlo (( 31 >< 0  ) result) |||
              condT setflags (read_flags ii >>=
              (\(N,Z,C,V).
                let (C_flag,V_flag) = if version = 4 then (UNKNOWN,UNKNOWN)
                                                     else (C,V)
                in
                  write_flags ii
                    (word_msb result,result = 0w,C_flag,V_flag)))) >>=
          unit4)))`;

(* ........................................................................
   T2,A: UMAAL<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val multiply_accumulate_accumulate_instr_def = iDefine`
  multiply_accumulate_accumulate_instr ii enc
      (Multiply_Accumulate_Accumulate dhi dlo m n) =
    instruction ii "multiply_accumulate_accumulate"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. (if enc = Encoding_Thumb2 then
              BadReg dlo \/ BadReg dhi \/ BadReg n \/ BadReg m
            else
              (dlo = 15w) \/ (dhi = 15w) \/ (n = 15w) \/ (m = 15w)) \/
            (dhi = dlo))
      ((read_reg ii dhi |||
        read_reg ii dlo |||
        read_reg ii m |||
        read_reg ii n) >>=
       (\(rdhi,rdlo,rm,rn).
          (let result : word64 = w2w rn * w2w rm + w2w rdhi + w2w rdlo in
             (increment_pc ii enc |||
              write_reg ii dhi (( 63 >< 32 ) result) |||
              write_reg ii dlo (( 31 >< 0  ) result)) >>=
          unit3)))`;

(* ........................................................................
   T2,A: MLS<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val multiply_subtract_instr_def = iDefine`
  multiply_subtract_instr ii enc (Multiply_Subtract d a m n) =
    instruction ii "multiply_subtract" (ARCH thumb2_support)
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m \/ BadReg a
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ (a = 15w))
      ((read_reg ii n ||| read_reg ii m ||| read_reg ii a) >>=
       (\(rn,rm,ra). let result = ra - rn * rm in
          (increment_pc ii enc ||| write_reg ii d result) >>= unit2))`;

(* ........................................................................
   T2,A: QADD<c> <Rd>,<Rm>,<Rn>
   T2,A: QSUB<c> <Rd>,<Rm>,<Rn>
   T2,A: QDADD<c> <Rd>,<Rm>,<Rn>
   T2,A: QDSUB<c> <Rd>,<Rm>,<Rn>
   ```````````````````````````````````````````````````````````````````````` *)
val saturating_add_subtract_instr_def = iDefine`
  saturating_add_subtract_instr ii enc (Saturating_Add_Subtract opc n d m) =
    instruction ii "saturating_add_subtract" (ARCH2 enc dsp_support)
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii m ||| read_reg ii n) >>=
       (\(rm,rn).
         let (result,sat) =
                case opc
                of 0b00w => signed_sat_q (SInt rm + SInt rn,32)
                 | 0b01w => signed_sat_q (SInt rm - SInt rn,32)
                 | 0b10w =>
                    (let (doubled:word32,sat1) =
                           signed_sat_q (2 * SInt rn,32) in
                     let (result,sat2) =
                           signed_sat_q (SInt rm + SInt doubled,32)
                     in
                       (result,sat1 \/ sat2))
                 | 0b11w =>
                    (let (doubled:word32,sat1) =
                           signed_sat_q (2 * SInt rn,32) in
                     let (result,sat2) =
                           signed_sat_q (SInt rm - SInt doubled,32)
                     in
                       (result,sat1 \/ sat2))
         in
           (increment_pc ii enc |||
            write_reg ii d result |||
            condT sat (set_q ii)) >>=
           unit3))`;

(* ........................................................................
   T2,A: SMLA<x><y><c> <Rd>,<Rn>,<Rm>,<Ra>
   where <x> and <y> are T (top) or B (bottom)
   ```````````````````````````````````````````````````````````````````````` *)
val signed_16_multiply_32_accumulate_instr_def = iDefine`
  signed_16_multiply_32_accumulate_instr ii enc
      (Signed_Halfword_Multiply opc m_high n_high d a m n) =
    instruction ii "signed_16_multiply_32_accumulate" (ARCH2 enc dsp_support)
      (\v. (opc <> 0w) \/
           (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg n \/ BadReg m \/ BadReg a
            else
              (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ (a = 15w)))
      ((read_reg ii m ||| read_reg ii n ||| read_reg ii a) >>=
       (\(rm,rn,ra).
          let operand1 = if n_high then top_half rn else bot_half rn
          and operand2 = if m_high then top_half rm else bot_half rm
          in
          let result = SInt operand1 * SInt operand2 + SInt ra in
          let result32 = i2w result
          in
            (increment_pc ii enc |||
             write_reg ii d result32 |||
             condT (result <> SInt result32) (set_q ii)) >>=
           unit3))`;

(* ........................................................................
   T2,A: SMUL<x><y><c> <Rd>,<Rn>,<Rm>
   where <x> and <y> are T (top) or B (bottom)
   ```````````````````````````````````````````````````````````````````````` *)
val signed_16_multiply_32_result_instr_def = iDefine`
  signed_16_multiply_32_result_instr ii enc
      (Signed_Halfword_Multiply opc m_high n_high d sbz m n) =
    instruction ii "signed_16_multiply_32_result" (ARCH2 enc dsp_support)
      (\v. (opc <> 3w) \/
           (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg n \/ BadReg m
            else
              (d = 15w) \/ (n = 15w) \/ (m = 15w)))
      ((read_reg ii m ||| read_reg ii n) >>=
       (\(rm,rn).
          let operand1 = if n_high then top_half rn else bot_half rn
          and operand2 = if m_high then top_half rm else bot_half rm
          in
          let result = SInt operand1 * SInt operand2
          in
            (increment_pc ii enc |||
             write_reg ii d (i2w result)) >>= unit2))`;

(* ........................................................................
   T2,A: SMLAW<y><c> <Rd>,<Rn>,<Rm>,<Ra>
   where <y> is T (top) or B (bottom)
   ```````````````````````````````````````````````````````````````````````` *)
val signed_16x32_multiply_32_accumulate_instr_def = iDefine`
  signed_16x32_multiply_32_accumulate_instr ii enc
      (Signed_Halfword_Multiply opc m_high n_high d a m n) =
    instruction ii "signed_16x32_multiply_32_accumulate" (ARCH2 enc dsp_support)
      (\v. (opc <> 1w) \/ n_high \/
           (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg n \/ BadReg m \/ BadReg a
            else
              (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ (a = 15w)))
      ((read_reg ii m ||| read_reg ii n ||| read_reg ii a) >>=
       (\(rm,rn,ra).
          let operand2 = if m_high then top_half rm else bot_half rm
          and sh16 = 2i ** 16
          in
          let result = (SInt rn * SInt operand2 + (SInt ra * sh16)) / sh16
          in
          let result32 = i2w result
          in
            (increment_pc ii enc |||
             write_reg ii d result32 |||
             condT (result <> SInt result32) (set_q ii)) >>=
           unit3))`;

(* ........................................................................
   T2,A: SMULW<y><c> <Rd>,<Rn>,<Rm>
   where <y> is T (top) or B (bottom)
   ```````````````````````````````````````````````````````````````````````` *)
val signed_16x32_multiply_32_result_instr_def = iDefine`
  signed_16x32_multiply_32_result_instr ii enc
      (Signed_Halfword_Multiply opc m_high n_high d sbz m n) =
    instruction ii "signed_16x32_multiply_32_result" (ARCH2 enc dsp_support)
      (\v. (opc <> 1w) \/ ~n_high \/
           (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg n \/ BadReg m
            else
              (d = 15w) \/ (n = 15w) \/ (m = 15w)))
      ((read_reg ii m ||| read_reg ii n) >>=
       (\(rm,rn).
          let operand2 = if m_high then top_half rm else bot_half rm
          in
          let result = (SInt rn * SInt operand2) / 2 ** 16
          in
            (increment_pc ii enc |||
             write_reg ii d (i2w result)) >>= unit2))`;

(* ........................................................................
   T2,A: SMLAL<x><y><c> <RdLo>,RdHi>,<Rn>,<Rm>
   where <x> and <y> are T (top) or B (bottom)
   ```````````````````````````````````````````````````````````````````````` *)
val signed_16_multiply_64_accumulate_instr_def = iDefine`
  signed_16_multiply_64_accumulate_instr ii enc
      (Signed_Halfword_Multiply opc m_high n_high dhi dlo m n) =
    instruction ii "signed_16_multiply_64_accumulate" (ARCH2 enc dsp_support)
      (\v. (opc <> 2w) \/
           (if enc = Encoding_Thumb2 then
              BadReg dlo \/ BadReg dhi \/ BadReg n \/ BadReg m
            else
              (dlo = 15w) \/ (dhi = 15w) \/ (n = 15w) \/ (m = 15w)) \/
           (dhi = dlo))
      ((read_reg ii m   ||| read_reg ii n |||
        read_reg ii dhi ||| read_reg ii dlo) >>=
       (\(rm,rn,rdhi,rdlo).
          let operand1 = if n_high then top_half rn else bot_half rn
          and operand2 = if m_high then top_half rm else bot_half rm
          in
          let result = (SInt operand1 * SInt operand2) +
                       (SInt ((rdhi @@ rdlo) : word64))
          in
            (increment_pc ii enc |||
             write_reg ii dlo (i2w result) |||
             write_reg ii dhi (i2w (result / 2 ** 32))) >>=
           unit3))`;

(* ........................................................................
   T2,A: SMUAD{X}<c> <Rd>,<Rn>,<Rm>
   T2,A: SMUSD{X}<c> <Rd>,<Rn>,<Rm>
   T2,A: SMLAD{X}<c> <Rd>,<Rn>,<Rm>,<Ra>
   T2,A: SMLSD{X}<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val signed_multiply_dual_instr_def = iDefine`
  signed_multiply_dual_instr ii enc (Signed_Multiply_Dual d a m sub m_swap n) =
    instruction ii "signed_multiply_dual"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m \/ (a = 13w)
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii m ||| read_reg ii n |||
        (if a = 15w then constT 0w else read_reg ii a)) >>=
       (\(rm,rn,ra).
          let operand2 = if m_swap then ROR (rm,16) else rm in
          let product1 = SInt (bot_half rn) * SInt (bot_half operand2)
          and product2 = SInt (top_half rn) * SInt (top_half operand2)
          in
          let result = if sub then product1 - product2 + SInt ra
                              else product1 + product2 + SInt ra
          in
          let result32 = i2w result
          in
            (increment_pc ii enc |||
             write_reg ii d result32 |||
             condT (result <> SInt result32) (set_q ii)) >>= unit3))`;

(* ........................................................................
   T2,A: SMLALD{X}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   T2,A: SMLSLD{X}<c> <RdLo>,<RdHi>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val signed_multiply_long_dual_instr_def = iDefine`
  signed_multiply_long_dual_instr ii enc
    (Signed_Multiply_Long_Dual dhi dlo m sub m_swap n) =
    instruction ii "signed_multiply_long_dual"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. (if enc = Encoding_Thumb2 then
              BadReg dlo \/ BadReg dhi \/ BadReg n /\ BadReg m
            else
              (dlo = 15w) \/ (dhi = 15w) \/ (n = 15w) \/ (m = 15w)) \/
           (dhi = dlo))
      ((read_reg ii m |||
        read_reg ii n |||
        read_reg ii dhi |||
        read_reg ii dlo) >>=
       (\(rm,rn,rdhi,rdlo).
          let operand2 = if m_swap then ROR (rm,16) else rm in
          let product1 = SInt (bot_half rn) * SInt (bot_half operand2)
          and product2 = SInt (top_half rn) * SInt (top_half operand2)
          and rd = (rdhi @@ rdlo) : word64
          in
          let result = if sub then product1 - product2 + SInt rd
                              else product1 + product2 + SInt rd
          in
          let result64 : word64 = i2w result
          in
            (increment_pc ii enc |||
             write_reg ii dhi (( 63 >< 32 ) result64) |||
             write_reg ii dlo (( 31 >< 0  ) result64)) >>= unit3))`;

(* ........................................................................
   T2,A: SMMUL{R}<c> <Rd>,<Rn>,<Rm>
   T2,A: SMMLA{R}<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val signed_most_significant_multiply_instr_def = iDefine`
  signed_most_significant_multiply_instr ii enc
    (Signed_Most_Significant_Multiply d a m round n) =
    instruction ii "signed_most_significant_multiply"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m \/ (a = 13w)
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii m ||| read_reg ii n |||
       (if a = 15w then constT 0w else read_reg ii a)) >>=
       (\(rm,rn,ra).
          let result = SInt ((w2w ra : word64) << 32) + SInt rn * SInt rm in
          let result = i2w (if round then result + 0x80000000 else result)
          in
            (increment_pc ii enc |||
             write_reg ii d ((63 >< 32) (result:word64))) >>= unit2))`;

(* ........................................................................
   T2,A: SMMLS{R}<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val signed_most_significant_multiply_subtract_instr_def = iDefine`
  signed_most_significant_multiply_subtract_instr ii enc
    (Signed_Most_Significant_Multiply_Subtract d a m round n) =
    instruction ii "signed_most_significant_multiply_subtract"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m \/ BadReg a
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w) \/ (a = 15w))
      ((read_reg ii m ||| read_reg ii n ||| read_reg ii a) >>=
       (\(rm,rn,ra).
          let result = SInt ((w2w ra :word64) << 32) - SInt rn * SInt rm in
          let result = i2w (if round then result + 0x80000000 else result)
          in
            (increment_pc ii enc |||
             write_reg ii d ((63 >< 32) (result:word64))) >>= unit2))`;

(* ........................................................................
   T2,A: SADD16<c>  <Rd>,<Rn>,<Rm>
   T2,A: SASX<c>    <Rd>,<Rn>,<Rm>
   T2,A: SSAX<c>    <Rd>,<Rn>,<Rm>
   T2,A: SSUB16<c>  <Rd>,<Rn>,<Rm>
   T2,A: SADD8<c>   <Rd>,<Rn>,<Rm>
   T2,A: SSUB8<c>   <Rd>,<Rn>,<Rm>

   T2,A: QADD16<c>  <Rd>,<Rn>,<Rm>
   T2,A: QASX<c>    <Rd>,<Rn>,<Rm>
   T2,A: QSAX<c>    <Rd>,<Rn>,<Rm>
   T2,A: QSUB16<c>  <Rd>,<Rn>,<Rm>
   T2,A: QADD8<c>   <Rd>,<Rn>,<Rm>
   T2,A: QSUB8<c>   <Rd>,<Rn>,<Rm>

   T2,A: SHADD16<c> <Rd>,<Rn>,<Rm>
   T2,A: SHASX<c>   <Rd>,<Rn>,<Rm>
   T2,A: SHSAX<c>   <Rd>,<Rn>,<Rm>
   T2,A: SHSUB16<c> <Rd>,<Rn>,<Rm>
   T2,A: SHADD8<c>  <Rd>,<Rn>,<Rm>
   T2,A: SHSUB8<c>  <Rd>,<Rn>,<Rm>

   T2,A: UADD16<c>  <Rd>,<Rn>,<Rm>
   T2,A: UASX<c>    <Rd>,<Rn>,<Rm>
   T2,A: USAX<c>    <Rd>,<Rn>,<Rm>
   T2,A: USUB16<c>  <Rd>,<Rn>,<Rm>
   T2,A: UADD8<c>   <Rd>,<Rn>,<Rm>
   T2,A: USUB8<c>   <Rd>,<Rn>,<Rm>

   T2,A: UQADD16<c> <Rd>,<Rn>,<Rm>
   T2,A: UQASX<c>   <Rd>,<Rn>,<Rm>
   T2,A: UQSAX<c>   <Rd>,<Rn>,<Rm>
   T2,A: UQSUB16<c> <Rd>,<Rn>,<Rm>
   T2,A: UQADD8<c>  <Rd>,<Rn>,<Rm>
   T2,A: UQSUB8<c>  <Rd>,<Rn>,<Rm>

   T2,A: UHADD16<c> <Rd>,<Rn>,<Rm>
   T2,A: UHASX<c>   <Rd>,<Rn>,<Rm>
   T2,A: UHSAX<c>   <Rd>,<Rn>,<Rm>
   T2,A: UHSUB16<c> <Rd>,<Rn>,<Rm>
   T2,A: UHADD8<c>  <Rd>,<Rn>,<Rm>
   T2,A: UHSUB8<c>  <Rd>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val parallel_add_subtract_instr_def = iDefine`
  parallel_add_subtract_instr ii enc (Parallel_Add_Subtract u op n d m) =
    instruction ii "parallel_add_subtract"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii n ||| read_reg ii m) >>=
       (\(rn,rm).
          let (result,ge) = parallel_add_sub u op rn rm in
            (increment_pc ii enc |||
             write_reg ii d result |||
             condT (IS_SOME ge) (write_ge ii (THE ge))) >>= unit3))`;

(* ........................................................................
   T2: SDIV<c> <Rd>,<Rn>,<Rm>
   T2: UDIV<c> <Rd>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val divide_instr_def = iDefine`
  divide_instr ii (Divide unsigned n d m) =
    instruction ii "divide" (ARCH {ARMv7_R})
      (\v. BadReg d \/ BadReg n \/ BadReg m)
      (read_reg ii m >>=
       (\rm.
          if rm = 0w then
            integer_zero_divide_trapping_enabled ii >>=
            (\trap.
               if trap then
                 take_undef_instr_exception ii
               else
                 (increment_pc ii Encoding_Thumb2 ||| write_reg ii d 0w) >>=
                 unit2)
          else
            read_reg ii n >>=
            (\rn.
              (increment_pc ii Encoding_Thumb2 |||
               write_reg ii d (if unsigned then rn // rm else rn / rm)) >>=
              unit2)))`;

(* ........................................................................
   T2,A: PKHBT<c> <Rd>,<Rn>,<Rm>{,LSL #<imm>}
   T2,A: PKHTB<c> <Rd>,<Rn>,<Rm>{,ASR #<imm>}
   ```````````````````````````````````````````````````````````````````````` *)
val pack_halfword_instr_def = iDefine`
  pack_halfword_instr ii enc (Pack_Halfword n d imm5 tbform m) =
    instruction ii "pack_halfword" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii n ||| read_reg ii m ||| read_cflag ii) >>=
       (\(rn,rm,c).
         let (shift_t,shift_n) = decode_imm_shift ((1 :+ tbform) 0w, imm5) in
           shift (rm, shift_t, shift_n, c) >>=
           (\operand2.
             let r1 = if tbform then bot_half operand2 else bot_half rn
             and r2 = if tbform then top_half rn else top_half operand2
             in
               (increment_pc ii enc |||
                write_reg ii d (r2 @@ r1)) >>= unit2)))`;

(* ........................................................................
   T2,A: SSAT<c> <Rd>,#<imm>, <Rn>{,<shift>}
   T2,A: USAT<c> <Rd>,#<imm5>,<Rn>{,<shift>}
   ```````````````````````````````````````````````````````````````````````` *)
val saturate_instr_def = iDefine`
  saturate_instr ii enc (Saturate unsigned sat_imm d imm5 sh n) =
    instruction ii "saturate" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n
           else
             (d = 15w) \/ (n = 15w))
      ((read_reg ii n ||| read_cflag ii) >>=
       (\(rn,c).
         let (shift_t,shift_n) = decode_imm_shift ((1 :+ sh) 0w, imm5) in
           shift (rn, shift_t, shift_n, c) >>=
           (\operand.
              let (result,sat) =
                      if unsigned then
                        unsigned_sat_q (SInt operand, w2n sat_imm)
                      else let saturate_to = w2n sat_imm + 1 in
                        (word_sign_extend saturate_to ## I)
                          (signed_sat_q (SInt operand, saturate_to))
              in
                (increment_pc ii enc |||
                 write_reg ii d result |||
                 condT sat (set_q ii)) >>= unit3)))`;

(* ........................................................................
   T2,A: SXTB16<c>  <Rd>,<Rm>{,<rotation>}
   T2,A: UXTB16<c>  <Rd>,<Rm>{,<rotation>}
   T2,A: SXTAB16<c> <Rd>,<Rn>,<Rm>{,<rotation>}
   T2,A: UXTAB16<c> <Rd>,<Rn>,<Rm>{,<rotation>}
   ```````````````````````````````````````````````````````````````````````` *)
val extend_byte_16_instr_def = iDefine`
  extend_byte_16_instr ii enc (Extend_Byte_16 unsigned n d rotate m) =
    instruction ii "extend_byte_16" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ (n = 13w) \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (((if n = 15w then constT 0w else read_reg ii n) |||
        read_reg ii m) >>=
       (\(rn,rm).
         let rotated = ROR (rm, w2n rotate * 8) in
         let r1 = bot_half rn + extend unsigned ((  7 >< 0  ) rotated : word8)
         and r2 = top_half rn + extend unsigned (( 23 >< 16 ) rotated : word8)
         in
           (increment_pc ii enc |||
            write_reg ii d (r2 @@ r1)) >>= unit2))`;

(* ........................................................................
   T2,A: SEL<c> <Rd>,<Rn>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val select_bytes_instr_def = iDefine`
  select_bytes_instr ii enc (Select_Bytes n d m) =
    instruction ii "select_bytes" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii n ||| read_reg ii m ||| read_ge ii) >>=
       (\(rn,rm,ge).
         let r1 = if ge ' 0 then (  7 >< 0  ) rn else (  7 >< 0  ) rm
         and r2 = if ge ' 1 then ( 15 >< 8  ) rn else ( 15 >< 8  ) rm
         and r3 = if ge ' 2 then ( 23 >< 16 ) rn else ( 23 >< 16 ) rm
         and r4 = if ge ' 3 then ( 31 >< 24 ) rn else ( 31 >< 24 ) rm
         in
           (increment_pc ii enc |||
            write_reg ii d (word32 [r1;r2;r3;r4])) >>= unit2))`;

(* ........................................................................
   T2,A: SSAT16<c> <Rd>,#<imm>,<Rn>
   T2,A: USAT16<c> <Rd>,#<imm>,<Rn>
   ```````````````````````````````````````````````````````````````````````` *)
val saturate_16_instr_def = iDefine`
  saturate_16_instr ii enc (Saturate_16 unsigned sat_imm d n) =
    instruction ii "saturate_16" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n
           else
             (d = 15w) \/ (n = 15w))
      (read_reg ii n >>=
       (\rn.
         let ((result1:word16,sat1),(result2:word16,sat2)) =
           if unsigned then
             let saturate_to = w2n sat_imm in
               unsigned_sat_q (SInt (bot_half rn), saturate_to),
               unsigned_sat_q (SInt (top_half rn), saturate_to)
           else
             let saturate_to = w2n sat_imm + 1 in
               (word_sign_extend saturate_to ## I)
                 (signed_sat_q (SInt (bot_half rn), saturate_to)),
               (word_sign_extend saturate_to ## I)
                 (signed_sat_q (SInt (top_half rn), saturate_to))
         in
           (increment_pc ii enc |||
            write_reg ii d (result2 @@ result1) |||
            condT (sat1 \/ sat2) (set_q ii)) >>= unit3))`;

(* ........................................................................
   T:    SXTB<c>   <Rd>,<Rm>
   T:    UXTB<c>   <Rd>,<Rm>
   T2:   SXTB<c>.W <Rd>,<Rm>{,<rotation>}
   T2:   UXTB<c>.W <Rd>,<Rm>{,<rotation>}
   A:    SXTB<c>   <Rd>,<Rm>{,<rotation>}
   A:    UXTB<c>   <Rd>,<Rm>{,<rotation>}
   T2,A: SXTAB<c>  <Rd>,<Rn>,<Rm>{,<rotation>}
   T2,A: UXTAB<c>  <Rd>,<Rn>,<Rm>{,<rotation>}
   ```````````````````````````````````````````````````````````````````````` *)
val extend_byte_instr_def = iDefine`
  extend_byte_instr ii enc (Extend_Byte unsigned n d rotate m) =
    instruction ii "extend_byte" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ (n = 13w) \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (((if n = 15w then constT 0w else read_reg ii n) |||
        read_reg ii m) >>=
       (\(rn,rm).
         let rotated = ROR (rm, w2n rotate * 8) in
         let r = rn + extend unsigned (( 7 >< 0 ) rotated : word8)
         in
           (increment_pc ii enc |||
            write_reg ii d r) >>= unit2))`;

(* ........................................................................
   T,A: REV<c>   <Rd>,<Rm>
   T2:  REV<c>.W <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val byte_reverse_word_instr_def = iDefine`
  byte_reverse_word_instr ii enc (Byte_Reverse_Word d m) =
    instruction ii "byte_reverse_word" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (read_reg ii m >>=
       (\rm.
         (increment_pc ii enc |||
          write_reg ii d (word32 (REVERSE (bytes (rm, 4))))) >>= unit2))`;

(* ........................................................................
   T:    SXTH<c>   <Rd>,<Rm>
   T:    UXTH<c>   <Rd>,<Rm>
   T2:   SXTH<c>.W <Rd>,<Rm>{,<rotation>}
   T2:   UXTH<c>.W <Rd>,<Rm>{,<rotation>}
   A:    SXTH<c>   <Rd>,<Rm>{,<rotation>}
   A:    UXTH<c>   <Rd>,<Rm>{,<rotation>}
   T2,A: SXTAH<c>  <Rd>,<Rn>,<Rm>{,<rotation>}
   T2,A: UXTAH<c>  <Rd>,<Rn>,<Rm>{,<rotation>}
   ```````````````````````````````````````````````````````````````````````` *)
val extend_halfword_instr_def = iDefine`
  extend_halfword_instr ii enc (Extend_Halfword unsigned n d rotate m) =
    instruction ii "extend_halfword" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ (n = 13w) \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (((if n = 15w then constT 0w else read_reg ii n) |||
        read_reg ii m) >>=
       (\(rn,rm).
         let rotated = ROR (rm, w2n rotate * 8) in
         let r = rn + extend unsigned (( 15 >< 0 ) rotated : word16)
         in
           (increment_pc ii enc |||
            write_reg ii d r) >>= unit2))`;

(* ........................................................................
   T,A: REV16<c>   <Rd>,<Rm>
   T2:  REV16<c>.W <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val byte_reverse_packed_halfword_instr_def = iDefine`
  byte_reverse_packed_halfword_instr ii enc (Byte_Reverse_Packed_Halfword d m) =
    instruction ii "byte_reverse_packed_halfword"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (read_reg ii m >>=
       (\rm.
          (increment_pc ii enc |||
           write_reg ii d
              (let w = bytes (rm, 4) in
                 word32 [EL 1 w; EL 0 w; EL 3 w; EL 2 w])) >>=
          unit2))`;

(* ........................................................................
   T2,A: RBIT<c> <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val reverse_bits_instr_def = iDefine`
  reverse_bits_instr ii enc (Reverse_Bits d m) =
    instruction ii "reverse_bits" (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (read_reg ii m >>=
       (\rm.
          (increment_pc ii enc |||
           write_reg ii d (word_reverse rm)) >>= unit2))`;

(* ........................................................................
   T,A: REVSH<c>   <Rd>,<Rm>
   T2:  REVSH<c>.W <Rd>,<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val byte_reverse_signed_halfword_instr_def = iDefine`
  byte_reverse_signed_halfword_instr ii enc (Byte_Reverse_Signed_Halfword d m) =
    instruction ii "byte_reverse_signed_halfword"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg m
           else
             (d = 15w) \/ (m = 15w))
      (read_reg ii m >>=
       (\rm.
          let r1 = sw2sw (( 7 >< 0 ) rm : word8) : word24
          and r2 = ( 15 >< 8 ) rm : word8
          in
            (increment_pc ii enc |||
             write_reg ii d (r1 @@ r2)) >>= unit2))`;

(* ........................................................................
   T2,A: USAD8<c>  <Rd>,<Rn>,<Rm>
   T2,A: USADA8<c> <Rd>,<Rn>,<Rm>,<Ra>
   ```````````````````````````````````````````````````````````````````````` *)
val unsigned_sum_absolute_differences_instr_def = iDefine`
  unsigned_sum_absolute_differences_instr ii enc
    (Unsigned_Sum_Absolute_Differences d a m n) =
    instruction ii "unsigned_sum_absolute_differences"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. if enc = Encoding_Thumb2 then
             BadReg d \/ BadReg n \/ BadReg m \/ (a = 13w)
           else
             (d = 15w) \/ (n = 15w) \/ (m = 15w))
      ((read_reg ii m ||| read_reg ii n |||
       (if a = 15w then constT 0w else read_reg ii a)) >>=
       (\(rm,rn,ra).
          let absdiff1 = ABS (UInt ((  7 -- 0  ) rn) - UInt ((  7 -- 0  ) rm))
          and absdiff2 = ABS (UInt (( 15 -- 8  ) rn) - UInt (( 15 -- 8  ) rm))
          and absdiff3 = ABS (UInt (( 23 -- 16 ) rn) - UInt (( 23 -- 16 ) rm))
          and absdiff4 = ABS (UInt (( 31 -- 24 ) rn) - UInt (( 31 -- 24 ) rm))
          in
          let result = UInt ra + absdiff1 + absdiff2 + absdiff3 + absdiff4
          in
            (increment_pc ii enc |||
             write_reg ii d (i2w result)) >>= unit2))`;

(* ........................................................................
   T2,A: SBFX<c> <Rd>,<Rn>,#<lsb>,#<width>
   T2,A: UBFX<c> <Rd>,<Rn>,#<lsb>,#<width>
   ```````````````````````````````````````````````````````````````````````` *)
val bit_field_extract_instr_def = iDefine`
  bit_field_extract_instr ii enc (Bit_Field_Extract unsigned widthm1 d lsb n) =
    let lsbit = w2n lsb and widthm1 = w2n widthm1 in
    let msbit = lsbit + widthm1
    in
      instruction ii "bit_field_extract" (ARCH thumb2_support)
        (\v. (if enc = Encoding_Thumb2 then
                BadReg d \/ BadReg n
              else
                (d = 15w) \/ (n = 15w)) \/ ~(msbit <= 31))
        (read_reg ii n >>=
         (\rn.
            let result =
              if unsigned then
                (msbit -- lsbit) rn
              else
                (msbit --- lsbit) rn
            in
              (increment_pc ii enc |||
               write_reg ii d result) >>= unit2))`;

(* ........................................................................
   T2,A: BFC<c> <Rd>,#<lsb>,#<width>
   T2,A: BFI<c> <Rd>,<Rn>,#<lsb>,#<width>
   ```````````````````````````````````````````````````````````````````````` *)
val bit_field_clear_insert_instr_def = iDefine`
  bit_field_clear_insert_instr ii enc (Bit_Field_Clear_Insert msb d lsb n) =
    let lsbit = w2n lsb and msbit = w2n msb in
      instruction ii "bit_field_clear_insert" (ARCH thumb2_support)
        (\v. (if enc = Encoding_Thumb2 then
                BadReg d \/ (n = 13w)
              else
                (d = 15w)) \/ msbit < lsbit)
        ((read_reg ii d |||
          (if n = 15w then constT 0w else read_reg ii n)) >>=
         (\(rd,rn).
            (increment_pc ii enc |||
             write_reg ii d (bit_field_insert msbit lsbit rn rd)) >>= unit2))`;

(* ........................................................................
   T2: PLD{W}<c> [<Rn>,#<imm12>]
   T2: PLD{W}<c> [<Rn>,#-<imm8>]
   A:  PLD{W}    [<Rn>,#+/-<imm12>]
   T2: PLD<c>    <label>
   A:  PLD       <label>
   T2: PLD{W}<c> [<Rn>,<Rm>{,LSL #<imm2>}]
   A:  PLD{W}    [<Rn>,+/-<Rm>{,<shift>}]
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val preload_data_instr_def = iDefine`
  preload_data_instr ii enc (Preload_Data add is_pldw n mode2) =
    instruction ii "preload_data"
      {(a,e) | (if enc = Encoding_Thumb2 then
                  a IN thumb2_support
                else
                  a IN dsp_support) /\
               (is_pldw ==>
                  Extension_Multiprocessing IN e /\ version_number a >= 7)}
      (\v. case mode2
           of Mode2_register imm5 type m =>
                if enc = Encoding_Thumb2 then
                  BadReg m
                else
                  (m = 15w) \/ (n = 15w) /\ is_pldw
            | Mode2_immediate imm12 => F)
      ((if is_mode2_immediate mode2 then
          read_reg_literal ii n
        else
          read_reg ii n) >>=
       (\base.
          address_mode2 ii T add base mode2 >>=
          (\(offset_addr,address).
            (increment_pc ii enc |||
             if is_pldw then
               hint_preload_data_for_write ii address
             else
               hint_preload_data ii address) >>= unit2)))`;

(* ........................................................................
   T2: PLI<c> [<Rn>,#<imm12>]
   T2: PLI<c> [<Rn>,#-<imm8>]
   A:  PLI    [<Rn>,#+/-<imm12>]
   T2: PLI<c> <label>
   A:  PLI    <label>
   T2: PLI<c> [<Rn>,<Rm>{,LSL #<imm2>}]
   A:  PLI    [<Rn>,+/-<Rm>{,<shift>}]
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val preload_instruction_instr_def = iDefine`
  preload_instruction_instr ii enc (Preload_Instruction add n mode2) =
    instruction ii "preload_instruction" (ARCH {a | version_number a >= 7})
      (\v. case mode2
           of Mode2_register imm5 type m =>
                if enc = Encoding_Thumb2 then BadReg m else m = 15w
            | Mode2_immediate imm12 => F)
      ((if is_mode2_immediate mode2 then
          read_reg_literal ii n
        else
          read_reg ii n) >>=
       (\base.
          address_mode2 ii T add base mode2 >>=
          (\(offset_addr,address).
            (increment_pc ii enc |||
             hint_preload_instr ii address) >>= unit2)))`;

(* ........................................................................
   T:   LDR{B}<c>   <Rt>,[<Rn>{,#<imm>}]
   T:   LDR<c>      <Rt>,[SP{,#<imm>}]
   T2:  LDR{B}<c>.W <Rt>,[<Rn>{,#<imm12>}]
   T2:  LDR{B}<c>   <Rt>,[<Rn>{,#-<imm8>}]
   T2:  LDR{B}<c>   <Rt>,[<Rn>],#+/-<imm8>
   T2:  LDR{B}<c>   <Rt>,[<Rn>,#+/-<imm8>]!
   A:   LDR{B}<c>   <Rt>,[<Rn>{,#+/-<imm12>}]
   A:   LDR{B}<c>   <Rt>,[<Rn>],#+/-<imm12>
   A:   LDR{B}<c>   <Rt>,[<Rn>,#+/-<imm12>]!
   T:   LDR<c>      <Rt>,<label>
   T2:  LDR<c>.W    <Rt>,<label>
   T2:  LDRB<c>     <Rt>,<label>
   A:   LDR{B}<c>   <Rt>,<label>
   T:   LDR{B}<c>   <Rt>,[<Rn>,<Rm>]
   T2:  LDR{B}<c>.W <Rt>,[<Rn>,<Rm>{,LSL #<imm2>}]
   A:   LDR{B}<c>   <Rt>,[<Rn>,+/-<Rm>{,<shift>}]{!}
   A:   LDR{B}<c>   <Rt>,[<Rn>],+/-<Rm>{,<shift>}
   Unprivileged:
   T2:  LDR{B}T<c>  <Rt>,[<Rn>{,#<imm8>}]
   A:   LDR{B}T<c>  <Rt>,[<Rn>]{,#+/-<imm12>}
   A:   LDR{B}T<c>  <Rt>,[<Rn>],+/-<Rm>{,<shift>}
   ```````````````````````````````````````````````````````````````````````` *)
val load_instr_def = iDefine`
  load_instr ii enc (Load indx add load_byte w unpriv n t mode2) =
    let wback = ~indx \/ w in
      null_check_instruction ii "load" n
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\version.
            unpriv /\ (if enc = Encoding_Thumb2 then
                         ~indx \/ ~add \/ w
                       else
                         indx \/ ~w) \/
            (load_byte \/ unpriv) /\
               (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/
            wback /\ ((n = 15w) \/ (n = t)) \/
            (case mode2
             of Mode2_register imm5 type m =>
                  if enc = Encoding_Thumb2 then
                    BadReg m
                  else
                    (m = 15w) \/ wback /\ version < 6 /\ (m = n)
              | Mode2_immediate imm12 => F))
        ((if is_mode2_immediate mode2 then
            read_reg_literal ii n
          else
            read_reg ii n) >>=
         (\base.
            address_mode2 ii indx add base mode2 >>=
            (\(offset_addr,address).
             (condT wback (write_reg ii n offset_addr) |||
             (if load_byte then
                (if unpriv then
                   read_memU_unpriv ii (address,1)
                 else
                   read_memU ii (address,1)) >>=
                (\data.
                   (increment_pc ii enc |||
                    write_reg ii t (zero_extend32 data)) >>= unit2)
              else
                (if unpriv then
                   read_memU_unpriv ii (address,4)
                 else
                   read_memU ii (address,4)) >>=
                (\data.
                   let data = word32 data in
                   if t = 15w then
                       if aligned(address,4) then
                         load_write_pc ii data
                       else
                         errorT "load: unpredictable"
                     else
                       (increment_pc ii enc |||
                        (unaligned_support ii >>=
                        (\has_unaligned_support.
                           if has_unaligned_support \/ aligned(address,4) then
                             write_reg ii t data
                           else
                             write_reg ii t
                               (ROR (data, 8 * w2n ((1 -- 0) address)))))) >>=
                       unit2))) >>=
              unit2)))`;

(* ........................................................................
   T:   STR{B}<c>   <Rt>,[<Rn>{,#<imm>}]
   T:   STR<c>      <Rt>,[SP{,#<imm>}]
   T2:  STR{B}<c>.W <Rt>,[<Rn>{,#<imm12>}]
   T2:  STR{B}<c>   <Rt>,[<Rn>{,#-<imm8>}]
   T2:  STR{B}<c>   <Rt>,[<Rn>],#+/-<imm8>
   T2:  STR{B}<c>   <Rt>,[<Rn>,#+/-<imm8>]!
   A:   STR{B}<c>   <Rt>,[<Rn>{,#+/-<imm12>}]
   A:   STR{B}<c>   <Rt>,[<Rn>],#+/-<imm12>
   A:   STR{B}<c>   <Rt>,[<Rn>,#+/-<imm12>]!
   T:   STR{B}<c>   <Rt>,[<Rn>,<Rm>]
   T2:  STR{B}<c>.W <Rt>,[<Rn>,<Rm>{,LSL #<imm2>}]
   A:   STR{B}<c>   <Rt>,[<Rn>,+/-<Rm>{,<shift>}]{!}
   A:   STR{B}<c>   <Rt>,[<Rn>],+/-<Rm>{,<shift>}
   Unprivileged:
   T2:  STR{B}T<c>  <Rt>,[<Rn>{,#<imm8>}]
   A:   STR{B}T<c>  <Rt>,[<Rn>]{,#+/-<imm12>}
   A:   STR{B}T<c>  <Rt>,[<Rn>],+/-<Rm>{,<shift>}
   ```````````````````````````````````````````````````````````````````````` *)
val store_instr_def = iDefine`
  store_instr ii enc (Store indx add store_byte w unpriv n t mode2) =
    let wback = ~indx \/ w in
      null_check_instruction ii "store" n
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\version.
            unpriv /\ (if enc = Encoding_Thumb2 then
                         ~indx \/ ~add \/ w
                       else
                         indx \/ ~w) \/
            (if enc = Encoding_Thumb2 then
               store_byte /\ (t = 13w) \/ (t = 15w)
             else
               store_byte /\ (t = 15w)) \/
            wback /\ ((n = 15w) \/ (n = t)) \/
            (case mode2
             of Mode2_register imm5 type m =>
                  if enc = Encoding_Thumb2 then
                    BadReg m
                  else
                    (m = 15w) \/ wback /\ version < 6 /\ (m = n)
              | Mode2_immediate imm12 => F))
        ((read_reg ii n |||
         (if t = 15w then pc_store_value ii else read_reg ii t)) >>=
         (\(base,data).
            address_mode2 ii indx add base mode2 >>=
            (\(offset_addr,address).
              ((if store_byte then
                  if unpriv then
                    write_memU_unpriv ii (address,1) (bytes(data,1))
                  else
                    write_memU ii (address,1) (bytes(data,1))
                else
                  unaligned_support ii >>=
                  (\has_unaligned_support.
                     let data = if has_unaligned_support \/ aligned(address,4)
                                  then bytes(data,4)
                                  else BITS32_UNKNOWN
                     in
                       (if unpriv then
                          write_memU_unpriv ii (address,4) data
                        else
                          write_memU ii (address,4) data))) |||
               increment_pc ii enc |||
               condT wback (write_reg ii n offset_addr)) >>=
               unit3)))`;

(* ........................................................................
   T:    LDR{S}H<c>   <Rt>,[<Rn>{,#<imm>}]
   T2:   LDR{S}H<c>.W <Rt>,[<Rn>{,#<imm12>}]
   T2:   LDR{S}H<c>   <Rt>,[<Rn>{,#-<imm8>}]
   A:    LDR{S}H<c>   <Rt>,[<Rn>{,#+/-<imm8>}]
   T2,A: LDR{S}H<c>   <Rt>,[<Rn>],#+/-<imm8>
   T2,A: LDR{S}H<c>   <Rt>,[<Rn>,#+/-<imm8>]!
   T2:   LDR{S}H<c>   <Rt>,<label>
   A:    LDR{S}H<c>   <Rt>,<label>
   T:    LDR{S}H<c>   <Rt>,[<Rn>,<Rm>]
   T2:   LDR{S}H<c>.W <Rt>,[<Rn>,<Rm>{,LSL #<imm2>}]
   A:    LDR{S}H<c>   <Rt>,[<Rn>,+/-<Rm>]{!}
   A:    LDR{S}H<c>   <Rt>,[<Rn>],+/-<Rm>
   Unprivileged:
   T2:   LDR{S}HT<c>  <Rt>,[<Rn>{,#<imm8>}]
   A:    LDR{S}HT<c>  <Rt>,[<Rn>]{,#+/-<imm8>}
   A:    LDR{S}HT<c>  <Rt>,[<Rn>],+/-<Rm>

   T2:   LDRSB<c>   <Rt>,[<Rn>{,#<imm12>}]
   T2:   LDRSB<c>   <Rt>,[<Rn>{,#-<imm8>}]
   A:    LDRSB<c>   <Rt>,[<Rn>{,#+/-<imm8>}]
   T2,A: LDRSB<c>   <Rt>,[<Rn>],#+/-<imm8>
   T2,A: LDRSB<c>   <Rt>,[<Rn>,#+/-<imm8>]!
   T2,A: LDRSB<c>   <Rt>,<label>
   T:    LDRSB<c>   <Rt>,[<Rn>,<Rm>]
   T2:   LDRSB<c>.W <Rt>,[<Rn>,<Rm>{,LSL #<imm2>}]
   A:    LDRSB<c>   <Rt>,[<Rn>,+/-<Rm>]{!}
   A:    LDRSB<c>   <Rt>,[<Rn>],+/-<Rm>
   Unprivileged:
   T2:   LDRSBT<c>  <Rt>,[<Rn>{,#<imm8>}]
   A:    LDRSBT<c>  <Rt>,[<Rn>]{,#+/-<imm8>}
   A:    LDRSBT<c>  <Rt>,[<Rn>],+/-<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
(* The decoder should guarantee: signed \/ half *)
val load_halfword_instr_def = iDefine`
  load_halfword_instr ii enc
    (Load_Halfword indx add w signed half unpriv n t mode3) =
    let wback = ~indx \/ w in
      null_check_instruction ii "load_halfword" n
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\version.
            unpriv /\ (if enc = Encoding_Thumb2 then
                         ~indx \/ ~add \/ w
                       else
                         indx \/ ~w) \/
            ~signed /\ ~half \/
            (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/
            wback /\ ((n = 15w) \/ (n = t)) \/
            (case mode3
             of Mode3_register imm2 m =>
                  if enc = Encoding_Thumb2 then
                    BadReg m
                  else
                    (m = 15w) \/ wback /\ version < 6 /\ (m = n)
              | Mode3_immediate imm12 => F))
        ((if is_mode3_immediate mode3 then
            read_reg_literal ii n
          else
            read_reg ii n) >>=
         (\base.
            address_mode3 ii indx add base mode3 >>=
            (\(offset_addr,address).
             (increment_pc ii enc |||
              condT wback (write_reg ii n offset_addr) |||
              (if half then
                (if unpriv then
                   read_memU_unpriv ii (address,2)
                 else
                   read_memU ii (address,2)) >>=
                (\data.
                  (unaligned_support ii >>=
                  (\has_unaligned_support.
                     if has_unaligned_support \/ aligned(address,2) then
                       if signed then
                         write_reg ii t (sign_extend32 data)
                       else
                         write_reg ii t (zero_extend32 data)
                     else
                       write_reg ii t UNKNOWN)))
               else
                 (if unpriv then
                   read_memU_unpriv ii (address,1)
                 else
                   read_memU ii (address,1)) >>=
                (\data.
                    write_reg ii t (sign_extend32 data)))) >>=
              unit3)))`;

(* ........................................................................
   T:    STRH<c>   <Rt>,[<Rn>{,#<imm>}]
   T2:   STRH<c>.W <Rt>,[<Rn>{,#<imm12>}]
   T2:   STRH<c>   <Rt>,[<Rn>{,#-<imm8>}]
   A:    STRH<c>   <Rt>,[<Rn>{,#+/-<imm8>}]
   T2,A: STRH<c>   <Rt>,[<Rn>],#+/-<imm8>
   T2,A: STRH<c>   <Rt>,[<Rn>,#+/-<imm8>]!
   T:    STRH<c>   <Rt>,[<Rn>,<Rm>]
   T2:   STRH<c>.W <Rt>,[<Rn>,<Rm>{,LSL #<imm2>}]
   A:    STRH<c>   <Rt>,[<Rn>,+/-<Rm>]{!}
   A:    STRH<c>   <Rt>,[<Rn>],+/-<Rm>
   Unprivileged:
   T2:   STRHT<c>  <Rt>,[<Rn>{,#<imm8>}]
   A:    STRHT<c>  <Rt>,[<Rn>]{,#+/-<imm8>}
   A:    STRHT<c>  <Rt>,[<Rn>],+/-<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val store_halfword_instr_def = iDefine`
  store_halfword_instr ii enc (Store_Halfword indx add w unpriv n t mode3) =
    let wback = ~indx \/ w in
      null_check_instruction ii "store_halfword" n
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\version.
            unpriv /\ (if enc = Encoding_Thumb2 then
                         ~indx \/ ~add \/ w
                       else
                         indx \/ ~w) \/
            (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/
            wback /\ ((n = 15w) \/ (n = t)) \/
            (case mode3
             of Mode3_register imm2 m =>
                  if enc = Encoding_Thumb2 then
                    BadReg m
                  else
                    (m = 15w) \/ wback /\ version < 6 /\ (m = n)
              | Mode3_immediate imm12 => F))
        ((read_reg ii n ||| read_reg ii t) >>=
         (\(base,rt).
            address_mode3 ii indx add base mode3 >>=
            (\(offset_addr,address).
              ((unaligned_support ii >>=
               (\has_unaligned_support.
                   let data = if has_unaligned_support \/ aligned(address,2)
                                then bytes(rt,2)
                                else BITS16_UNKNOWN
                   in
                     (if unpriv then
                        write_memU_unpriv ii (address,2) data
                      else
                        write_memU ii (address,2) data))) |||
               increment_pc ii enc |||
               condT wback (write_reg ii n offset_addr)) >>=
               unit3)))`;

(* ........................................................................
   T,A:  POP<c>   <registers>
   T2:   POP<c>.W <registers>
   T:    LDM<c>   <Rn>!,<registers>    (<Rn> not included in <registers>)
   T:    LDM<c>   <Rn>,<registers>     (<Rn> included in <registers>)
   T2:   LDM<c>.W <Rn>{!},<registers>
   A:    LDM<c>   <Rn>{!},<registers>
   A:    LDMDA<c> <Rn>{!},<registers>
   T2,A: LDMDB<c> <Rn>{!},<registers>
   A:    LDMIB<c> <Rn>{!},<registers>
   Exception return:
   A:    LDM{<amode>}<c> <Rn>{!},<registers_with_pc>^
   User registers:
   A:    LDM{<amode>}<c> <Rn>,<registers_without_pc>^
   where <amode> is DA, DB, IA or IB.
   ```````````````````````````````````````````````````````````````````````` *)
val load_multiple_instr_def = iDefine`
  load_multiple_instr ii enc (Load_Multiple indx add system wback n registers) =
    null_check_instruction ii "load_multiple" n
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\version.
         (n = 15w) \/ bit_count registers < 1 \/
         (enc = Encoding_Thumb2) /\
           (system \/ bit_count registers < 2 \/
            registers ' 15 /\ registers ' 14 \/ registers ' 13) \/
         system /\ wback /\ ~(registers ' 15) \/
         wback /\ registers ' (w2n n) /\
           ((enc = Encoding_Thumb2) \/ version >= 7))
      ((read_reg ii n ||| read_cpsr ii) >>=
      (\(base,cpsr).
         let mode = if system /\ ~(registers ' 15) then 0b10000w else cpsr.M
         and length = n2w (4 * bit_count registers) in
         let base_address = if add then base else base - length in
         let start_address = if indx = add then base_address + 4w
                                           else base_address
         in
         let address i = start_address +
                         n2w (4 * (bit_count_upto (i + 1) registers - 1))
         in
           forT 0 14
             (\i. condT (registers ' i)
                    (read_memA ii (address i,4) >>=
                    (\d. write_reg_mode ii (n2w i,mode) (word32 d)))) >>=
           (\unit_list:unit list.
              condT wback
                (if ~(registers ' (w2n n)) then
                   if add then
                     write_reg ii n (base + length)
                   else
                     write_reg ii n (base - length)
                 else
                   write_reg ii n UNKNOWN) >>=
              (\u:unit.
                 if registers ' 15 then
                   read_memA ii (address 15,4) >>=
                   (\d.
                      if system then
                        current_mode_is_user_or_system ii >>=
                        (\is_user_or_system.
                          if is_user_or_system then
                            errorT "load_multiple_instr: unpredictable"
                          else
                            read_spsr ii >>=
                            (\spsr.
                               cpsr_write_by_instr ii (encode_psr spsr, 0b1111w, T)
                                 >>= (\u. branch_write_pc ii (word32 d))))
                      else
                        load_write_pc ii (word32 d))
                 else
                   increment_pc ii enc))))`;


(* ........................................................................
   T,A:  PUSH<c>   <registers>
   T2:   PUSH<c>.W <registers>
   T:    STM<c>    <Rn>!,<registers>
   T2:   STM<c>.W  <Rn>{!},<registers>
   A:    STM<c>    <Rn>{!},<registers>
   A:    STMDA<c>  <Rn>{!},<registers>
   T2,A: STMDB<c>  <Rn>{!},<registers>
   A:    STMIB<c>  <Rn>{!},<registers>
   User registers:
   A:    STM{<amode>}<c> <Rn>,<registers>^
   where <amode> is DA, DB, IA or IB.
   ```````````````````````````````````````````````````````````````````````` *)
val store_multiple_instr_def = iDefine`
  store_multiple_instr ii enc
      (Store_Multiple indx add system wback n registers) =
    null_check_instruction ii "store_multiple" n
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\v. (n = 15w) \/ bit_count registers < 1 \/
           (enc = Encoding_Thumb2) /\
              (bit_count registers < 2 \/
               registers ' 15 \/ registers ' 13 \/
               wback /\ registers ' (w2n n)) \/
           system /\ wback)
      (current_mode_is_user_or_system ii >>=
       (\is_user_or_system.
         if system /\ is_user_or_system then
           errorT "store_multiple_instr: unpredictable"
         else
          (read_reg ii n ||| read_cpsr ii) >>=
          (\(base,cpsr).
            let mode = if system then 0b10000w else cpsr.M
            and length = n2w (4 * bit_count registers)
            and lowest = lowest_set_bit registers
            in
            let base_address = if add then base else base - length in
            let start_address = if indx = add then base_address + 4w
                                              else base_address
            in
            let address i = start_address +
                            n2w (4 * (bit_count_upto (i + 1) registers - 1))
            in
              forT 0 14
                (\i. condT (registers ' i)
                       (if (i = w2n n) /\ wback /\ (i <> lowest) then
                          write_memA ii (address i,4) BITS32_UNKNOWN
                        else
                          read_reg_mode ii (n2w i,mode) >>=
                          (\d. write_memA ii (address i,4) (bytes(d,4))))) >>=
              (\unit_list:unit list.
                (condT (registers ' 15)
                   (pc_store_value ii >>=
                    (\pc. write_memA ii (address 15,4) (bytes(pc,4)))) |||
                 increment_pc ii enc |||
                 condT wback
                   (if add then
                      write_reg ii n (base + length)
                    else
                      write_reg ii n (base - length))) >>=
                unit3))))`;

(* ........................................................................
   T2:   LDRD<c> <Rt>,<Rt2>,[<Rn>{,#+/-<imm>}]
   T2:   LDRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<imm>
   T2:   LDRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<imm>]!
   A:    LDRD<c> <Rt>,<Rt2>,[<Rn>{,#+/-<imm8>}]
   A:    LDRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<imm8>
   A:    LDRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<imm8>]!
   T2,A: LDRD<c> <Rt>,<Rt2>,<label>
   A:    LDRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<Rm>]{!}
   A:    LDRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val load_dual_instr_def = iDefine`
  load_dual_instr ii enc (Load_Dual indx add w n t t2 mode3) =
    let wback = ~indx \/ w in
      null_check_instruction ii "load_dual" n (ARCH2 enc {a | a IN dsp_support})
        (\version.
           (if enc = Encoding_Thumb2 then
              BadReg t \/ BadReg t2 \/ (t = t2)
            else
              ~indx /\ w \/ t ' 0 \/ t2 <> t + 1w \/ (t2 = 15w)) \/
            (case mode3
             of Mode3_register imm2 m =>
                  (imm2 <> 0w) \/ (m = 15w) \/ (m = t) \/ (m = t2) \/
                  version < 6 /\ wback /\ (m = n)
              | Mode3_immediate imm12 => F) \/
            wback /\ ((n = 15w) \/ (n = t) \/ (n = t2)))
        ((if is_mode3_immediate mode3 then
            read_reg_literal ii n
          else
            read_reg ii n) >>=
         (\base.
           address_mode3 ii indx add base mode3 >>=
           (\(offset_addr,address).
            (increment_pc ii enc |||
             condT wback (write_reg ii n offset_addr) |||
             read_memA ii (address,4) >>=
             (\data. write_reg ii t (word32 data)) |||
             read_memA ii (address + 4w,4) >>=
             (\data. write_reg ii t2 (word32 data))) >>=
             unit4)))`;

(* ........................................................................
   T2:   STRD<c> <Rt>,<Rt2>,[<Rn>{,#+/-<imm>}]
   T2:   STRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<imm>
   T2:   STRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<imm>]!
   A:    STRD<c> <Rt>,<Rt2>,[<Rn>{,#+/-<imm8>}]
   A:    STRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<imm8>
   A:    STRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<imm8>]!
   A:    STRD<c> <Rt>,<Rt2>,[<Rn>,#+/-<Rm>]{!}
   A:    STRD<c> <Rt>,<Rt2>,[<Rn>],#+/-<Rm>
   ```````````````````````````````````````````````````````````````````````` *)
val store_dual_instr_def = iDefine`
  store_dual_instr ii enc (Store_Dual indx add w n t t2 mode3) =
    let wback = ~indx \/ w in
      null_check_instruction ii "store_dual" n
        (ARCH2 enc {a | a IN dsp_support})
        (\version.
           (if enc = Encoding_Thumb2 then
              (n = 15w) \/ BadReg t \/ BadReg t2
            else
              ~indx /\ w \/ t ' 0 \/ t2 <> t + 1w \/ (t2 = 15w)) \/
            (case mode3
             of Mode3_register imm2 m =>
                  (imm2 <> 0w) \/ (m = 15w) \/ version < 6 /\ wback /\ (m = n)
              | Mode3_immediate imm12 =>
                  F) \/
            wback /\ ((n = 15w) \/ (n = t) \/ (n = t2)))
        ((read_reg ii n ||| read_reg ii t ||| read_reg ii t2) >>=
         (\(base,rt,rt2).
           address_mode3 ii indx add base mode3 >>=
           (\(offset_addr,address).
            (increment_pc ii enc |||
             condT wback (write_reg ii n offset_addr) |||
             write_memA ii (address,4) (bytes(rt,4)) |||
             write_memA ii (address + 4w,4) (bytes(rt2,4))) >>=
             unit4)))`;

(* ........................................................................
   T2: LDREX<c> <Rt>,[<Rn>{,#<imm>}]
   A:  LDREX<c> <Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val load_exclusive_instr_def = iDefine`
  load_exclusive_instr ii enc (Load_Exclusive n t imm8) =
    null_check_instruction ii "load_exclusive" n
      (ARCH2 enc {a | version_number a >= 6})
      (\v. (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/ (n = 15w))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\rn. let address = rn + (w2w imm8) << 2 in
          set_exclusive_monitors ii (address,4) >>=
          (\u:unit. read_memA ii (address,4) >>=
             (\d. write_reg ii t (word32 d))))) >>=
       unit2)`;

(* ........................................................................
   T2: STREX<c> <Rd>,<Rt>,[<Rn>{,#<imm>}]
   A:  STREX<c> <Rd>,<Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val store_exclusive_instr_def = iDefine`
  store_exclusive_instr ii enc (Store_Exclusive n d t imm8) =
    null_check_instruction ii "store_exclusive" n
      (ARCH2 enc {a | version_number a >= 6})
      (\v. (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg t
            else
              (d = 15w) \/ (t = 15w) \/ (imm8 <> 0w)) \/
           (n = 15w) \/ (d = n) \/ (d = t))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\rn. let address = rn + (w2w imm8) << 2 in
          (exclusive_monitors_pass ii (address,4) >>=
          (\pass.
             if pass then
               read_reg ii t >>=
               (\rt.
                 (write_memA ii (address,4) (bytes(rt,4)) |||
                  write_reg ii d 0w) >>=
                 unit2)
             else
               write_reg ii d 1w)))) >>=
       unit2)`;

(* ........................................................................
   T2,A: LDREXD<c> <Rt>,<Rt2>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val load_exclusive_doubleword_instr_def = iDefine`
  load_exclusive_doubleword_instr ii enc (Load_Exclusive_Doubleword n t t2) =
    null_check_instruction ii "load_exclusive_doubleword" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then
              BadReg t \/ BadReg t2 \/ (t = t2)
            else
              t ' 0 \/ (t = 0b1110w)) \/ (n = 15w))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          set_exclusive_monitors ii (address,8) >>=
          (\u:unit. (read_memA ii (address,8) ||| big_endian ii) >>=
             (\(d,E). let value = word64 d in
                write_reg ii t
                  (if E then (63 >< 32) value else (31 >< 0) value) |||
                write_reg ii (t + 1w)
                  (if E then (31 >< 0) value else (63 >< 32) value))))) >>=
       (\(u1:unit,u2:unit # unit). constT ()))`;

(* ........................................................................
   T2,A: STREXD<c> <Rd>,<Rt>,<Rt2>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val store_exclusive_doubleword_instr_def = iDefine`
  store_exclusive_doubleword_instr ii enc
      (Store_Exclusive_Doubleword n d t t2) =
    null_check_instruction ii "store_exclusive_doubleword" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg t \/ BadReg t2
            else
              (d = 15w) \/ t ' 0 \/ (t = 0b1110w)) \/
           (n = 15w) \/ (d = n) \/ (d = t) \/ (d = t2))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          exclusive_monitors_pass ii (address,8) >>=
          (\pass.
             if pass then
               (read_reg ii t ||| read_reg ii t2 ||| big_endian ii) >>=
               (\(rt,rt2,E).
                 let value = if E then bytes(rt,4) ++ bytes(rt2,4)
                                  else bytes(rt2,4) ++ bytes(rt,4)
                 in
                   (write_memA ii (address,8) value |||
                    write_reg ii d 0w) >>=
                   unit2)
             else
               write_reg ii d 1w))) >>=
       unit2)`;

(* ........................................................................
   T2,A: LDREXB<c> <Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val load_exclusive_byte_instr_def = iDefine`
  load_exclusive_byte_instr ii enc (Load_Exclusive_Byte n t) =
    null_check_instruction ii "load_exclusive_byte" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/ (n = 15w))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          set_exclusive_monitors ii (address,1) >>=
          (\u:unit. read_memA ii (address,1) >>=
             (\d. write_reg ii t (zero_extend32 d))))) >>=
       unit2)`;

(* ........................................................................
   T2,A: STREXB<c> <Rd>,<Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val store_exclusive_byte_instr_def = iDefine`
  store_exclusive_byte_instr ii enc (Store_Exclusive_Byte n d t) =
    null_check_instruction ii "store_exclusive_byte" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg t
            else
              (d = 15w) \/ (t = 15w)) \/
           (n = 15w) \/ (d = n) \/ (d = t))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          exclusive_monitors_pass ii (address,1) >>=
          (\pass.
             if pass then
               read_reg ii t >>=
               (\rt.
                 (write_memA ii (address,1) (bytes(rt,1)) |||
                  write_reg ii d 0w) >>=
                 unit2)
             else
               write_reg ii d 1w))) >>=
       unit2)`;

(* ........................................................................
   T2,A: LDREXH<c> <Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val load_exclusive_halfword_instr_def = iDefine`
  load_exclusive_halfword_instr ii enc (Load_Exclusive_Halfword n t) =
    null_check_instruction ii "load_exclusive_halfword" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then BadReg t else t = 15w) \/ (n = 15w))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          set_exclusive_monitors ii (address,2) >>=
          (\u:unit. read_memA ii (address,2) >>=
             (\d. write_reg ii t (zero_extend32 d))))) >>=
       unit2)`;

(* ........................................................................
   T2,A: STREXH<c> <Rd>,<Rt>,[<Rn>]
   ```````````````````````````````````````````````````````````````````````` *)
val store_exclusive_halfword_instr_def = iDefine`
  store_exclusive_halfword_instr ii enc (Store_Exclusive_Halfword n d t) =
    null_check_instruction ii "store_exclusive_halfword" n
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support))
      (\v. (if enc = Encoding_Thumb2 then
              BadReg d \/ BadReg t
            else
              (d = 15w) \/ (t = 15w)) \/
           (n = 15w) \/ (d = n) \/ (d = t))
      ((increment_pc ii enc |||
       read_reg ii n >>=
       (\address.
          exclusive_monitors_pass ii (address,2) >>=
          (\pass.
             if pass then
               read_reg ii t >>=
               (\rt.
                 (write_memA ii (address,2) (bytes(rt,2)) |||
                  write_reg ii d 0w) >>=
                 unit2)
             else
               write_reg ii d 1w))) >>=
       unit2)`;

(* ........................................................................
   T2: CLREX<c>
   A:  CLREX
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val clear_exclusive_instr_def = iDefine`
  clear_exclusive_instr ii enc =
    instruction ii "clear_exclusive"
      (ARCH (if enc = Encoding_Thumb2 then
               {a | version_number a >= 7}
             else
               kernel_support)) {}
      ((increment_pc ii enc ||| clear_exclusive_local ii) >>= unit2)`;

(* ........................................................................
   A: SWP{B}<c> <Rt>,<Rt2>,[<Rn>]   (deprecated for version >= 6)
   ```````````````````````````````````````````````````````````````````````` *)
val swap_instr_def = iDefine`
  swap_instr ii (Swap swap_byte n t t2) =
    instruction ii "swap" ALL
      (\v. (t = 15w) \/ (t2 = 15w) \/ (n = 15w) \/ (n = t) \/ (n = t2))
      (lockT
        ((read_reg ii n ||| read_reg ii t2) >>=
         (\(address,rt2).
            (if swap_byte then
               read_memA ii (address,1) |||
               write_memA ii (address,1) (bytes(rt2,1))
             else
               read_memA ii (address,4) |||
               write_memA ii (address,4) (bytes(rt2,4))) >>=
            (\(d,u:unit).
              (increment_pc ii Encoding_ARM |||
               (if swap_byte then
                  write_reg ii t (zero_extend32 d)
                else
                  write_reg ii t
                    (ROR (word32 d, 8 * w2n ((1 -- 0) address))))) >>=
               unit2))))`;

(* ........................................................................
   T2: SRSDB<c>     SP{!},#<mode>
   T2: SRS{IA}<c>   SP{!},#<mode>
   A:  SRS{<amode>} SP{!},#<mode>
   where <amode> is DA, DB, IA or IB.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val store_return_state_instr_def = iDefine`
  store_return_state_instr ii enc (Store_Return_State P inc wback mode) =
    (is_secure ii ||| read_nsacr ii) >>=
    (\(is_secure,nsacr).
      instruction ii "store_return_state"
        (ARCH2 enc {a | version_number a >= 6})
        (\v. ~is_secure /\
             ((mode = 0b10110w) \/ (mode = 0b10001w) /\ nsacr.RFR))
        ((current_mode_is_user_or_system ii ||| current_instr_set ii) >>=
         (\(is_user_or_system,iset).
           if is_user_or_system \/ (iset = InstrSet_ThumbEE) then
             errorT "store_return_state_instr: unpredictable"
           else
             (read_reg_mode ii (13w,mode) ||| read_reg ii 14w |||
              read_spsr ii) >>=
             (\(base,lr,spsr).
               let wordhigher = (P = inc)
               and address = if inc then base else base - 8w
               in
               let address = if wordhigher then address + 4w else address
               in
                 (increment_pc ii enc |||
                  write_memA ii (address,4) (bytes (lr,4)) |||
                  write_memA ii (address + 4w,4) (bytes (encode_psr spsr,4)) |||
                  condT wback
                    (write_reg_mode ii (13w,mode)
                       (if inc then base + 8w else base - 8w))) >>= unit4))))`;

(* ........................................................................
   T2: RFEDB<c>     <Rn>{!}
   T2: RFE{IA}<c>   <Rn>{!}
   A:  RFE{<amode>} <Rn>{!}
   where <amode> is DA, DB, IA or IB.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val return_from_exception_instr_def = iDefine`
  return_from_exception_instr ii enc (Return_From_Exception P inc wback n) =
    instruction ii "return_from_exception"
      (ARCH2 enc {a | version_number a >= 6}) {}
      ((current_mode_is_user_or_system ii ||| current_instr_set ii) >>=
       (\(is_user_or_system,iset).
        if is_user_or_system \/ (iset = InstrSet_ThumbEE) then
          errorT "return_from_exception_instr: unpredictable"
        else
          read_reg ii n >>=
          (\base.
             let wordhigher = (P = inc)
             and address = if inc then base else base - 8w
             in
             let address = if wordhigher then address + 4w else address
             in
               (read_memA ii (address + 4w,4) |||
                read_memA ii (address,4)) >>=
               (\(d1,d2).
                 (cpsr_write_by_instr ii (word32 d1, 0b1111w, T) |||
                  branch_write_pc ii (word32 d2) |||
                  condT wback
                    (write_reg ii n (if inc then base + 8w else base - 8w))) >>=
                 unit3))))`;

(* ........................................................................
   T2,A: MRS<c> <Rd>,<spec_reg>
   where <spec_reg> is APSR, CPSR or SPSR.
   ```````````````````````````````````````````````````````````````````````` *)
val status_to_register_instr_def = iDefine`
  status_to_register_instr ii enc (Status_to_Register readspsr d) =
    instruction ii "status_to_register"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\v. if enc = Encoding_Thumb2 then BadReg d else (d = 15w))
      ((increment_pc ii enc |||
        (if readspsr then
          current_mode_is_user_or_system ii >>=
          (\is_user_or_system_mode.
             if is_user_or_system_mode then
               errorT "status_to_register_instr: unpredictable"
             else
               read_spsr ii >>= (\spsr. write_reg ii d (encode_psr spsr)))
         else
           read_cpsr ii >>= (\cpsr. write_reg ii d
             (encode_psr cpsr && 0b11111000_11111111_00000011_11011111w)))) >>=
        unit2)`;

(* ........................................................................
   A: MSR<c> <spec_reg>,#<const>
   where <spec_reg> is APSR_<bits>, CPSR_<fields> or SPSR_<fields>
         <bits>     is nzcvq, g, or nzcvqg
         <fields>   is one or more of c, x, s and f.
   ```````````````````````````````````````````````````````````````````````` *)
val immediate_to_status_instr_def = iDefine`
  immediate_to_status_instr ii (Immediate_to_Status writespsr mask imm12) =
    instruction ii "immidiate_to_status" ALL (\v. mask = 0w)
      (arm_expand_imm ii imm12 >>=
       (\imm32.
        (increment_pc ii Encoding_ARM |||
         if writespsr then
           spsr_write_by_instr ii (imm32,mask)
         else
           cpsr_write_by_instr ii (imm32,mask,F)) >>=
       unit2))`;

(* ........................................................................
   T2,A: MSR<c> <spec_reg>,<Rn>
   where <spec_reg> is APSR_<bits>, CPSR_<fields> or SPSR_<fields>
         <bits>     is nzcvq, g, or nzcvqg
         <fields>   is one or more of c, x, s and f.
   ```````````````````````````````````````````````````````````````````````` *)
val register_to_status_instr_def = iDefine`
  register_to_status_instr ii enc (Register_to_Status writespsr mask n) =
    instruction ii "register_to_status"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
      (\v. (mask = 0w) \/ (n = 15w))
      (read_reg ii n >>=
       (\rn.
        (increment_pc ii enc |||
         if writespsr then
           spsr_write_by_instr ii (rn,mask)
         else
           cpsr_write_by_instr ii (rn,mask,F)) >>=
       unit2))`;

(* ........................................................................
   T:    CPS<effect>   <iflags>
   T2:   CPS<effect>.W <iflags>{,#<mode>}
   A:    CPS<effect>   <iflags>{,#<mode>}
   T2,A: CPS           #<mode>
   where <effect> is IE or ID
         <iflags> is one or more of a, i and f.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val change_processor_state_instr_def = iDefine`
  change_processor_state_instr ii enc
    (Change_Processor_State imod affectA affectI affectF mode) =
    instruction ii "change_processor_state"
      (ARCH2 enc {a | version_number a >= 6})
      (\v. ((imod = 0b00w) /\ IS_NONE mode) \/
           (imod ' 1 <=> ~affectA /\ ~affectI /\ ~affectF) \/
           (imod = 0b01w))
      (current_mode_is_priviledged ii >>=
       (\current_mode_is_priviledged.
          if current_mode_is_priviledged then
            read_cpsr ii >>=
            (\cpsr.
              let enable  = (imod = 0b10w)
              and disable = (imod = 0b11w)
              in
              let cpsr_val = word_modify (\i b.
                    if (i = 8) /\ affectA \/
                       (i = 7) /\ affectI \/
                       (i = 6) /\ affectF
                    then
                      ~enable /\ (disable \/ b)
                    else if i < 5 /\ IS_SOME mode then
                      (THE mode) ' i
                    else
                      b) (encode_psr cpsr)
              in
                (cpsr_write_by_instr ii (cpsr_val, 0b1111w, T) |||
                 increment_pc ii enc) >>= unit2)
          else
            increment_pc ii enc))`;

(* ........................................................................
   T,A: SETEND <endian_specifier>
   where <endian_specifier> is BE or LE.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val set_endianness_instr_def = iDefine`
  set_endianness_instr ii enc (Set_Endianness set_bigend) =
    instruction ii "set_endianness" (ARCH {a | version_number a >= 6}) {}
      ((write_e ii set_bigend ||| increment_pc ii enc) >>= unit2)`;

(* ........................................................................
   T2,A: SMC<c> #<imm4>   (previously SMI)
   ```````````````````````````````````````````````````````````````````````` *)
val secure_monitor_call_instr_def = iDefine`
  secure_monitor_call_instr ii =
    instruction ii "secure_monitor_call" security_support {}
      (current_mode_is_priviledged ii >>=
       (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             take_smc_exception ii
           else
             take_undef_instr_exception ii))`;

(* ........................................................................
   T: BKPT #<imm8>
   A: BKPT #<imm16>
   ```````````````````````````````````````````````````````````````````````` *)
val breakpoint_instr_def = iDefine`
  breakpoint_instr ii =
    instruction ii "breakpoint" (ARCH {a | version_number a >= 5}) {}
      (take_prefetch_abort_exception ii)`;

(* ........................................................................
   T2: DMB<c> <option>
   A:  DMB    <option>
   where <option> is SY, ST, ISH, ISHST, NSH, NSHST, OSH or OSHST.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val data_memory_barrier_instr_def = iDefine`
  data_memory_barrier_instr ii enc (Data_Memory_Barrier option) =
    instruction ii "data_memory_barrier" (ARCH {a | version_number a >= 7}) {}
      ((increment_pc ii enc |||
        data_memory_barrier ii (barrier_option option)) >>= unit2)`;

(* ........................................................................
   T2: DSB<c> <option>
   A:  DSB    <option>
   where <option> is SY, ST, ISH, ISHST, NSH, NSHST, OSH or OSHST.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val data_synchronization_barrier_instr_def = iDefine`
  data_synchronization_barrier_instr ii enc
      (Data_Synchronization_Barrier option) =
    instruction ii "data_synchronization_barrier"
      (ARCH {a | version_number a >= 7}) {}
      ((increment_pc ii enc |||
        data_synchronization_barrier ii (barrier_option option)) >>= unit2)`;

(* ........................................................................
   T2: ISB<c> <option>
   A:  ISB    <option>
   where <option> is optionally SY.
   ```````````````````````````````````````````````````````````````````````` *)
(* Unpredictable for ARMv4*. *)
val instruction_synchronization_barrier_instr_def = iDefine`
  instruction_synchronization_barrier_instr ii enc
      (Instruction_Synchronization_Barrier option) =
    instruction ii "instruction_synchronization_barrier"
      (ARCH {a | version_number a >= 7}) {}
      ((increment_pc ii enc |||
        instruction_synchronization_barrier ii) >>= unit2)`;

(* ........................................................................
   T2,A: CDP{2}<c> <coproc>,#<opc1>,<CRd>,<CRn>,<CRm>{,#<opc2>}
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val coprocessor_data_processing_instr_def = iDefine`
  coprocessor_data_processing_instr ii enc cond
      (Coprocessor_Data_Processing opc1 crn crd coproc opc2 crm) =
    instruction ii "coprocessor_data_processing"
      (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL) {}
      (let ThisInstr =
             (cond,Coprocessor_Data_Processing opc1 crn crd coproc opc2 crm)
       in
         coproc_accepted ii (coproc,ThisInstr) >>=
         (\accepted.
            if ~accepted then
              take_undef_instr_exception ii
            else
              (increment_pc ii enc |||
               coproc_internal_operation ii (coproc,ThisInstr)) >>=
              unit2))`;

(* ........................................................................
   T2,A: LDC{2}{L}<c> <coproc>,<CRd>,[<Rn>{,#+/-<imm>}]
   T2,A: LDC{2}{L}<c> <coproc>,<CRd>,[<Rn>,#+/-<imm>]!
   T2,A: LDC{2}{L}<c> <coproc>,<CRd>,[<Rn>],#+/-<imm>
   T2,A: LDC{2}{L}<c> <coproc>,<CRd>,[<Rn>],<option>
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val coprocessor_load_instr_def = iDefine`
  coprocessor_load_instr ii enc cond
      (Coprocessor_Load p u d w rn crd coproc mode5) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "coprocessor_load"
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\v. (rn = 15w) /\ (w \/ (~p /\ (iset <> InstrSet_ARM))))
        (let ThisInstr = (cond,Coprocessor_Load p u d w rn crd coproc mode5)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                read_reg_literal ii rn >>=
                (\base.
                   address_mode5 p u base mode5 >>=
                   (\(offset_addr,address).
                      let readm i =
                             (read_memA ii (address + n2w (4 * i),4)) >>=
                             (\data. constT (word32 data))
                      in
                        (coproc_send_loaded_words ii
                           (readm,coproc,ThisInstr) |||
                         increment_pc ii enc |||
                         condT w (write_reg ii rn offset_addr)) >>=
                        unit3)))))`;

(* ........................................................................
   T2,A: STC{2}{L}<c> <coproc>,<CRd>,[<Rn>{,#+/-<imm>}]
   T2,A: STC{2}{L}<c> <coproc>,<CRd>,[<Rn>,#+/-<imm>]!
   T2,A: STC{2}{L}<c> <coproc>,<CRd>,[<Rn>],#+/-<imm>
   T2,A: STC{2}{L}<c> <coproc>,<CRd>,[<Rn>],<option>
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val coprocessor_store_instr_def = iDefine`
  coprocessor_store_instr ii enc cond
      (Coprocessor_Store p u d w rn crd coproc mode5) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "coprocessor_store"
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\v. (rn = 15w) /\ (w \/ (iset <> InstrSet_ARM)))
        (let ThisInstr = (cond,Coprocessor_Store p u d w rn crd coproc mode5)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                read_reg ii rn >>=
                (\base.
                   (coproc_get_words_to_store ii (coproc,ThisInstr) |||
                    address_mode5 p u base mode5) >>=
                   (\(data,offset_addr,start_address).
                      let address i = start_address + n2w (4 * i) in
                       (forT 0 (LENGTH data - 1)
                          (\i. write_memA ii (address i,4)
                                 (bytes(EL i data,4))) |||
                        increment_pc ii enc |||
                        condT w (write_reg ii rn offset_addr)) >>=
                      (\(unit_list:unit list,u2:unit,u3:unit). constT ()))))))`;

(* ........................................................................
   T2,A: MRC{2}<c> <coproc>,#<opc1>,<Rt>,<CRn>,<CRm>{,#<opc2>}
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val coprocessor_register_to_arm_instr_def = iDefine`
  coprocessor_register_to_arm_instr ii enc cond
      (Coprocessor_Transfer opc1 T crn rt coproc opc2 crm) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "coprocessor_register_to_arm"
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\v. (rt = 13w) /\ (iset <> InstrSet_ARM))
        (let ThisInstr =
               (cond,Coprocessor_Transfer opc1 T crn rt coproc opc2 crm)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                coproc_get_one_word ii (coproc,ThisInstr) >>=
                (\value.
                   (increment_pc ii enc |||
                    if rt <> 15w then
                      write_reg ii rt value
                    else
                      write_flags ii
                        (value ' 31,value ' 30,value ' 29,value ' 28)) >>=
                   unit2))))`;

(* ........................................................................
   T2,A: MCR{2}<c> <coproc>,#<opc1>,<Rt>,<CRn>,<CRm>{,#<opc2>}
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val arm_register_to_coprocessor_instr_def = iDefine`
  arm_register_to_coprocessor_instr ii enc cond
      (Coprocessor_Transfer opc1 F crn rt coproc opc2 crm) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "arm_register_to_coprocessor"
        (if enc = Encoding_Thumb2 then ARCH thumb2_support else ALL)
        (\v. (rt = 15w) \/ (rt = 13w) /\ (iset <> InstrSet_ARM))
        (let ThisInstr =
               (cond,Coprocessor_Transfer opc1 F crn rt coproc opc2 crm)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                read_reg ii rt >>=
                (\value.
                   (increment_pc ii enc |||
                    coproc_send_one_word ii (value,coproc,ThisInstr)) >>=
                   unit2))))`;

(* ........................................................................
   T2,A: MRRC{2}<c> <coproc>,#<opc1>,<Rt>,<Rt2>,<CRm>
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val coprocessor_register_to_arm_two_instr_def = iDefine`
  coprocessor_register_to_arm_two_instr ii enc cond
      (Coprocessor_Transfer_Two T rt2 rt coproc opc1 crm) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "coprocessor_register_to_arm_two"
        (ARCH {a | if enc = Encoding_Thumb2 then
                     a IN thumb2_support
                   else if cond = 15w then
                     version_number a >= 6
                   else
                     a IN dsp_support})
        (\v. (rt = 15w) \/ (rt2 = 15w) \/ (rt = rt2) \/
            ((rt = 13w) \/ (rt2 = 13w)) /\ (iset <> InstrSet_ARM))
        (let ThisInstr =
               (cond,Coprocessor_Transfer_Two T rt2 rt coproc opc1 crm)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                coproc_get_two_words ii (coproc,ThisInstr) >>=
                (\(data1,data2).
                   (increment_pc ii enc |||
                    write_reg ii rt data1 |||
                    write_reg ii rt2 data2) >>=
                   unit3))))`;

(* ........................................................................
   T2,A: MCRR{2}<c> <coproc>,#<opc1>,<Rt>,<Rt2>,<CRm>
   ```````````````````````````````````````````````````````````````````````` *)
(* If cond = 15w then Unpredictable for ARMv4*. *)
val arm_register_to_coprocessor_two_instr_def = iDefine`
  arm_register_to_coprocessor_two_instr ii enc cond
      (Coprocessor_Transfer_Two F rt2 rt coproc opc1 crm) =
    current_instr_set ii >>=
    (\iset.
      instruction ii "arm_register_to_coprocessor_two"
        (ARCH {a | if enc = Encoding_Thumb2 then
                     a IN thumb2_support
                   else if cond = 15w then
                     version_number a >= 6
                   else
                     a IN dsp_support})
        (\v. (rt = 15w) \/ (rt2 = 15w) \/
            ((rt = 13w) \/ (rt2 = 13w)) /\ (iset <> InstrSet_ARM))
        (let ThisInstr =
               (cond,Coprocessor_Transfer_Two F rt2 rt coproc opc1 crm)
         in
           coproc_accepted ii (coproc,ThisInstr) >>=
           (\accepted.
              if ~accepted then
                take_undef_instr_exception ii
              else
                (read_reg ii rt ||| read_reg ii rt2) >>=
                (\data.
                   (increment_pc ii enc |||
                    coproc_send_two_words ii (data,coproc,ThisInstr)) >>=
                   unit2))))`;

(* ........................................................................
   T,A: NOP<c>
   T2:  NOP<c>.W
   ```````````````````````````````````````````````````````````````````````` *)
val no_operation_instr_def = iDefine`
  no_operation_instr ii enc =
    instruction ii "no_operation"
      (ARCH {a | a IN thumb2_support \/ (enc = Encoding_ARM) /\ (a = ARMv6K)})
      {} (increment_pc ii enc)`;

(* ........................................................................
   T,A: YIELD<c>
   T2:  YIELD<c>.W
   ```````````````````````````````````````````````````````````````````````` *)
val yield_instr_def = iDefine`
  yield_instr ii enc =
    read_arch ii >>=
    (\arch.
       if arch = ARMv6T2 then
         no_operation_instr ii enc
       else
         instruction ii "yield"
           (ARCH (if enc = Encoding_ARM then
                    kernel_support
                  else
                    {a | version_number a >= 7})) {}
           ((increment_pc ii enc ||| hint_yield ii) >>= unit2))`;

(* ........................................................................
   T,A: WFE<c>
   T2:  WFE<c>.W
   ```````````````````````````````````````````````````````````````````````` *)
val wait_for_event_instr_def = iDefine`
  wait_for_event_instr ii enc =
    read_arch ii >>=
    (\arch.
       if arch = ARMv6T2 then
         no_operation_instr ii enc
       else
         instruction ii "wait_for_event"
           (ARCH (if enc = Encoding_ARM then
                    kernel_support
                  else
                    {a | version_number a >= 7})) {}
           ((increment_pc ii enc |||
             event_registered ii >>=
             (\registered.
                if registered then
                  clear_event_register ii
                else
                  wait_for_event ii)) >>= unit2))`;

(* ........................................................................
   T,A: SEV<c>
   T2:  SEV<c>.W
   ```````````````````````````````````````````````````````````````````````` *)
val send_event_instr_def = iDefine`
  send_event_instr ii enc =
    read_arch ii >>=
    (\arch.
       if arch = ARMv6T2 then
         no_operation_instr ii enc
       else
         instruction ii "send_event"
           (ARCH (if enc = Encoding_ARM then
                    kernel_support
                  else
                    {a | version_number a >= 7})) {}
           ((increment_pc ii enc ||| send_event ii) >>= unit2))`;

(* ........................................................................
   T,A: WFI<c>
   T2:  WFI<c>.W
   ```````````````````````````````````````````````````````````````````````` *)
val wait_for_interrupt_instr_def = iDefine`
  wait_for_interrupt_instr ii enc =
    read_arch ii >>=
    (\arch.
       if arch = ARMv6T2 then
         no_operation_instr ii enc
       else
         instruction ii "wait_for_interrupt"
           (ARCH (if enc = Encoding_ARM then
                    kernel_support
                  else
                    {a | version_number a >= 7})) {}
           ((increment_pc ii enc ||| wait_for_interrupt ii) >>= unit2))`;

(* ........................................................................
   T2,A: DBG<c> #<option>
   ```````````````````````````````````````````````````````````````````````` *)
val debug_instr_def = iDefine`
  debug_instr ii enc option =
    read_arch ii >>=
    (\arch.
       if (arch = ARMv6T2) \/ (enc = Encoding_ARM) /\ (arch = ARMv6K) then
         no_operation_instr ii enc
       else
         instruction ii "debug" (ARCH {a | version_number a >= 7}) {}
           ((increment_pc ii enc ||| hint_debug ii option) >>= unit2))`;

(* ------------------------------------------------------------------------ *)

val condition_passed_def = Define`
  condition_passed ii (cond:word4) =
    read_flags ii >>=
    (\(n,z,c,v).
      let result =
        (case (3 >< 1) cond : word3
         of 0b000w => z                (* EQ or NE *)
          | 0b001w => c                (* CS or CC *)
          | 0b010w => n                (* MI or PL *)
          | 0b011w => v                (* VS or VC *)
          | 0b100w => c /\ ~z          (* HI or LS *)
          | 0b101w => n = v            (* GE or LT *)
          | 0b110w => (n = v) /\ ~z    (* GT or LE *)
          | 0b111w => T)               (* AL       *)
      in
       if cond ' 0 /\ (cond <> 15w) then
         constT (~result)
       else
         constT result)`;

val branch_instruction_def = Define`
  branch_instruction ii (enc,inst) =
    case inst
    of Branch_Target imm24 =>
         branch_target_instr ii enc inst
     | Branch_Exchange rm =>
         branch_exchange_instr ii inst
     | Branch_Link_Exchange_Immediate H toARM imm24 =>
         branch_link_exchange_imm_instr ii enc inst
     | Branch_Link_Exchange_Register rm =>
         branch_link_exchange_reg_instr ii inst
     | Compare_Branch nonzero imm6 rn =>
         compare_branch_instr ii inst
     | Table_Branch_Byte rn h rm =>
         table_branch_byte_instr ii inst
     | Check_Array rn rm =>
         check_array_instr ii inst
     | Handler_Branch_Link l handler =>
         handler_branch_link_instr ii inst
     | Handler_Branch_Link_Parameter imm5 handler =>
         handler_branch_link_parameter_instr ii inst
     | Handler_Branch_Parameter imm3 handler =>
         handler_branch_parameter_instr ii inst`;

val data_processing_instruction_def = Define`
  data_processing_instruction ii (enc,inst) =
    case inst
    of Data_Processing opc s rn rd mode1 =>
         data_processing_instr ii enc inst
     | Move_Halfword high rd imm16 =>
         move_halfword_instr ii enc inst
     | Add_Sub add n d imm12 =>
         add_sub_instr ii enc inst
     | Multiply a s rd ra rm rn =>
         multiply_instr ii enc inst
     | Multiply_Subtract rd ra rm rn =>
         multiply_subtract_instr ii enc inst
     | Signed_Halfword_Multiply 0w m n rd ra rm rn =>
         signed_16_multiply_32_accumulate_instr ii enc inst
     | Signed_Halfword_Multiply 1w m F rd ra rm rn =>
         signed_16x32_multiply_32_accumulate_instr ii enc inst
     | Signed_Halfword_Multiply 1w m T rd ra rm rn =>
         signed_16x32_multiply_32_result_instr ii enc inst
     | Signed_Halfword_Multiply 2w m n rd ra rm rn =>
         signed_16_multiply_64_accumulate_instr ii enc inst
     | Signed_Halfword_Multiply opc m n rd ra rm rn =>
         signed_16_multiply_32_result_instr ii enc inst
     | Signed_Multiply_Dual rd ra rm sub m_swap rn =>
         signed_multiply_dual_instr ii enc inst
     | Signed_Multiply_Long_Dual rdhi rdlo rm sub m_swap rn =>
         signed_multiply_long_dual_instr ii enc inst
     | Signed_Most_Significant_Multiply rd ra rm round rn =>
         signed_most_significant_multiply_instr ii enc inst
     | Signed_Most_Significant_Multiply_Subtract rd ra rm round rn =>
         signed_most_significant_multiply_subtract_instr ii enc inst
     | Multiply_Long u a s rdhi rdlo rm rn =>
         multiply_long_instr ii enc inst
     | Multiply_Accumulate_Accumulate rdhi rdlo rm rn =>
         multiply_accumulate_accumulate_instr ii enc inst
     | Saturate u sat_imm5 rd imm5 sh rn =>
         saturate_instr ii enc inst
     | Saturate_16 u sat_imm4 rd rn =>
         saturate_16_instr ii enc inst
     | Saturating_Add_Subtract opc rn rd rm =>
         saturating_add_subtract_instr ii enc inst
     | Pack_Halfword rn rd imm5 tbform rm =>
         pack_halfword_instr ii enc inst
     | Extend_Byte u rn rd rotate rm =>
         extend_byte_instr ii enc inst
     | Extend_Byte_16 u rn rd rotate rm =>
         extend_byte_16_instr ii enc inst
     | Extend_Halfword u rn rd rotate rm =>
         extend_halfword_instr ii enc inst
     | Bit_Field_Clear_Insert msb rd lsb rn =>
         bit_field_clear_insert_instr ii enc inst
     | Count_Leading_Zeroes rd rm =>
         count_leading_zeroes_instr ii enc inst
     | Reverse_Bits rd rm =>
         reverse_bits_instr ii enc inst
     | Byte_Reverse_Word rd rm =>
         byte_reverse_word_instr ii enc inst
     | Byte_Reverse_Packed_Halfword rd rm =>
         byte_reverse_packed_halfword_instr ii enc inst
     | Byte_Reverse_Signed_Halfword rd rm =>
         byte_reverse_signed_halfword_instr ii enc inst
     | Bit_Field_Extract u widthm1 rd lsb rn =>
         bit_field_extract_instr ii enc inst
     | Select_Bytes rn rd rm =>
         select_bytes_instr ii enc inst
     | Unsigned_Sum_Absolute_Differences rd ra rm rn =>
         unsigned_sum_absolute_differences_instr ii enc inst
     | Parallel_Add_Subtract u op rn rd rm =>
         parallel_add_subtract_instr ii enc inst
     | Divide u rn rd rm =>
         divide_instr ii inst`;

val status_access_instruction_def = Define`
  status_access_instruction ii (enc,inst) =
    case inst
    of Status_to_Register r rd =>
         status_to_register_instr ii enc inst
     | Immediate_to_Status r mask imm12 =>
         immediate_to_status_instr ii inst
     | Register_to_Status r mask rn =>
         register_to_status_instr ii enc inst
     | Change_Processor_State imod affectA affectI affectF mode =>
         change_processor_state_instr ii enc inst
     | Set_Endianness set_bigend =>
         set_endianness_instr ii enc inst`;

val load_store_instruction_def = Define`
  load_store_instruction ii (enc,inst) =
    case inst
    of Load p u b w unpriv rn rt mode2 =>
         load_instr ii enc inst
     | Store p u b w unpriv rn rt mode2 =>
         store_instr ii enc inst
     | Load_Halfword p u w s h unpriv rn rt mode3 =>
         load_halfword_instr ii enc inst
     | Store_Halfword p u w unpriv rn rt mode3 =>
         store_halfword_instr ii enc inst
     | Load_Dual p u w rn rt rt2 mode3 =>
         load_dual_instr ii enc inst
     | Store_Dual p u w rn rt rt2 mode3 =>
         store_dual_instr ii enc inst
     | Load_Multiple p u s w rn registers =>
         load_multiple_instr ii enc inst
     | Store_Multiple p u s w rn registers =>
         store_multiple_instr ii enc inst
     | Load_Exclusive rn rt imm8 =>
         load_exclusive_instr ii enc inst
     | Store_Exclusive rn rd rt imm8 =>
         store_exclusive_instr ii enc inst
     | Load_Exclusive_Doubleword rn rt rt2 =>
         load_exclusive_doubleword_instr ii enc inst
     | Store_Exclusive_Doubleword rn rd rt rt2 =>
         store_exclusive_doubleword_instr ii enc inst
     | Load_Exclusive_Halfword rn rt =>
         load_exclusive_halfword_instr ii enc inst
     | Store_Exclusive_Halfword rn rd rt =>
         store_exclusive_halfword_instr ii enc inst
     | Load_Exclusive_Byte rn rt =>
         load_exclusive_byte_instr ii enc inst
     | Store_Exclusive_Byte rn rd rt =>
         store_exclusive_byte_instr ii enc inst
     | Store_Return_State p u w mode =>
         store_return_state_instr ii enc inst
     | Return_From_Exception p u w rn =>
         return_from_exception_instr ii enc inst`;

val miscellaneous_instruction_def = Define`
  miscellaneous_instruction ii (enc,inst) =
    case inst
    of Hint Hint_nop =>
         no_operation_instr ii enc
     | Hint Hint_yield =>
         yield_instr ii enc
     | Hint Hint_wait_for_event =>
         wait_for_event_instr ii enc
     | Hint Hint_send_event =>
         send_event_instr ii enc
     | Hint Hint_wait_for_interrupt =>
         wait_for_interrupt_instr ii enc
     | Hint (Hint_debug option) =>
         debug_instr ii enc option
     | Breakpoint imm16 =>
         breakpoint_instr ii
     | Data_Memory_Barrier option =>
         data_memory_barrier_instr ii enc inst
     | Data_Synchronization_Barrier option =>
         data_synchronization_barrier_instr ii enc inst
     | Instruction_Synchronization_Barrier option =>
         instruction_synchronization_barrier_instr ii enc inst
     | Swap b rn rt rt2 =>
         swap_instr ii inst
     | Preload_Data u r rn mode2 =>
         preload_data_instr ii enc inst
     | Preload_Instruction u rn mode2 =>
         preload_instruction_instr ii enc inst
     | Supervisor_Call imm24 =>
         take_svc_exception ii
     | Secure_Monitor_Call imm4 =>
         secure_monitor_call_instr ii
     | Enterx_Leavex is_enterx =>
         enterx_leavex_instr ii is_enterx
     | Clear_Exclusive =>
         clear_exclusive_instr ii enc
     | If_Then firstcond mask =>
         if_then_instr ii inst`;

val coprocessor_instruction_def = Define`
  coprocessor_instruction ii (enc,cond,inst) =
    case inst
    of Coprocessor_Load p u d w rn crd coproc mode5 =>
         coprocessor_load_instr ii enc cond inst
     | Coprocessor_Store p u d w rn crd coproc mode5 =>
         coprocessor_store_instr ii enc cond inst
     | Coprocessor_Data_Processing opc1 crn crd coproc opc2 crm =>
         coprocessor_data_processing_instr ii enc cond inst
     | Coprocessor_Transfer opc1_1 F crn rt coproc opc2 crm =>
         arm_register_to_coprocessor_instr ii enc cond inst
     | Coprocessor_Transfer opc1_1 T crn rt coproc opc2 crm =>
         coprocessor_register_to_arm_instr ii enc cond inst
     | Coprocessor_Transfer_Two F rt2 rt coproc opc1 crm =>
         arm_register_to_coprocessor_two_instr ii enc cond inst
     | Coprocessor_Transfer_Two T rt2 rt coproc opc1 crm =>
         coprocessor_register_to_arm_two_instr ii enc cond inst`;

val arm_instr_def = Define`
  arm_instr ii (enc,cond,inst) =
    (condition_passed ii cond >>=
    (\pass.
       if pass then
         case inst
         of Branch b =>
              branch_instruction ii (enc,b)
          | DataProcessing d =>
              data_processing_instruction ii (enc,d)
          | StatusAccess s =>
              status_access_instruction ii (enc,s)
          | LoadStore l =>
              load_store_instruction ii (enc,l)
          | Miscellaneous m =>
              miscellaneous_instruction ii (enc,m)
          | Coprocessor c =>
              coprocessor_instruction ii (enc,cond,c)
          | Undefined =>
              take_undef_instr_exception ii
          | _ =>
              errorT "decode: unpredictable"
       else
         increment_pc ii enc)) >>=
    (\u:unit.
       condT (case inst
                of Miscellaneous (If_Then _ _) => F
                 | _ => T)
         (IT_advance ii))`;

(* ======================================================================== *)

infix \\ <<

val op \\ = op THEN;
val op << = op THENL;

val _ = wordsLib.guess_lengths();

val extract_modify =
   (GEN_ALL o SIMP_CONV (arith_ss++fcpLib.FCP_ss++boolSimps.CONJ_ss)
    [word_modify_def, word_extract_def, word_bits_def, w2w])
    ``(h >< l) (word_modify P w) = value``;

val CONCAT62_EQ = Q.prove(
  `(!a b c d.
     ((a:word6) @@ (b:word2) = (c:word6) @@ (d:word2)) = (a = c) /\ (b = d)) /\
   (!a b c.
     ((a:word6) @@ (b:word2) = c) = (a = (7 >< 2) c) /\ (b = (1 >< 0) c))`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []
  \\ DECIDE_TAC);

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val cpsr_write_by_instr_thm = Q.prove(
  `!cpsr value:word32 bytemask:word4 affect_execstate priviledged secure
    aw fw nmfi.
      decode_psr (word_modify (\i b.
         if 27 <= i /\ i <= 31 /\ bytemask ' 3 \/
            24 <= i /\ i <= 26 /\ bytemask ' 3 /\ affect_execstate \/
            16 <= i /\ i <= 19 /\ bytemask ' 2 \/
            10 <= i /\ i <= 15 /\ bytemask ' 1 /\ affect_execstate \/
                       (i = 9) /\ bytemask ' 1 \/
                       (i = 8) /\ bytemask ' 1 /\
                                  priviledged /\ (secure \/ aw) \/
                       (i = 7) /\ bytemask ' 0 /\ priviledged \/
                       (i = 6) /\ bytemask ' 0 /\
                                  priviledged /\ (secure \/ fw) /\
                                  (~nmfi \/ ~(value ' 6)) \/
                       (i = 5) /\ bytemask ' 0 /\ affect_execstate \/
                       (i < 5) /\ bytemask ' 0 /\ priviledged
           then value ' i else b) (encode_psr cpsr)) =
      cpsr with
        <| N := if bytemask ' 3 then value ' 31 else cpsr.N;
           Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
           C := if bytemask ' 3 then value ' 29 else cpsr.C;
           V := if bytemask ' 3 then value ' 28 else cpsr.V;
           Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
           IT := if affect_execstate then
                   if bytemask ' 3 then
                     if bytemask ' 1 then
                       (15 >< 10) value @@ (26 >< 25) value
                     else
                       (7 >< 2) cpsr.IT @@ (26 >< 25) value
                   else
                     if bytemask ' 1 then
                       (15 >< 10) value @@ (1 >< 0) cpsr.IT
                     else
                       cpsr.IT
                 else
                   cpsr.IT;
           J := if bytemask ' 3 /\ affect_execstate then value ' 24 else cpsr.J;
           GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
           E := if bytemask ' 1 then value ' 9 else cpsr.E;
           A := if bytemask ' 1 /\ priviledged /\ (secure \/ aw)
                then value ' 8
                else cpsr.A;
           I := if bytemask ' 0 /\ priviledged then value ' 7 else cpsr.I;
           F := if bytemask ' 0 /\ priviledged /\ (secure \/ fw) /\
                   (~nmfi \/ ~(value ' 6))
                then value ' 6
                else cpsr.F;
           T := if bytemask ' 0 /\ affect_execstate then value ' 5 else cpsr.T;
           M := if bytemask ' 0 /\ priviledged then (4 >< 0) value else cpsr.M
        |>`,
  STRIP_TAC
    \\ SIMP_TAC (srw_ss()++ARITH_ss) [ARMpsr_component_equality,
         WORD_MODIFY_BIT, decode_psr_def, encode_psr_bit, encode_psr_bits,
         extract_modify]
    \\ REPEAT STRIP_TAC
    << [
      SRW_TAC [ARITH_ss] [CONCAT62_EQ, extract_modify]
        \\ ASM_SIMP_TAC (arith_ss++wordsLib.WORD_BIT_EQ_ss) []
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      SRW_TAC [fcpLib.FCP_ss,ARITH_ss] [word_extract_def, w2w, word_bits_def]
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      SRW_TAC [fcpLib.FCP_ss,ARITH_ss] [word_extract_def, w2w, word_bits_def]
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit]]);

val spsr_write_by_instr_thm = Q.prove(
  `!spsr value:word32 bytemask:word4.
      decode_psr (word_modify (\i b.
         if 24 <= i /\ i <= 31 /\ bytemask ' 3 \/
            16 <= i /\ i <= 19 /\ bytemask ' 2 \/
             8 <= i /\ i <= 15 /\ bytemask ' 1 \/
                       i <= 7  /\ bytemask ' 0
         then value ' i else b) (encode_psr spsr)) =
      spsr with
        <| N := if bytemask ' 3 then value ' 31 else spsr.N;
           Z := if bytemask ' 3 then value ' 30 else spsr.Z;
           C := if bytemask ' 3 then value ' 29 else spsr.C;
           V := if bytemask ' 3 then value ' 28 else spsr.V;
           Q := if bytemask ' 3 then value ' 27 else spsr.Q;
           IT := if bytemask ' 3 then
                   if bytemask ' 1 then
                     (15 >< 10) value @@ (26 >< 25) value
                   else
                     (7 >< 2) spsr.IT @@ (26 >< 25) value
                 else
                   if bytemask ' 1 then
                     (15 >< 10) value @@ (1 >< 0) spsr.IT
                   else
                     spsr.IT;
           J := if bytemask ' 3 then value ' 24 else spsr.J;
           GE := if bytemask ' 2 then (19 >< 16) value else spsr.GE;
           E := if bytemask ' 1 then value ' 9 else spsr.E;
           A := if bytemask ' 1 then value ' 8 else spsr.A;
           I := if bytemask ' 0 then value ' 7 else spsr.I;
           F := if bytemask ' 0 then value ' 6 else spsr.F;
           T := if bytemask ' 0 then value ' 5 else spsr.T;
           M := if bytemask ' 0 then (4 >< 0) value else spsr.M
        |>`,
  STRIP_TAC
    \\ SIMP_TAC (srw_ss()++ARITH_ss) [ARMpsr_component_equality,
         WORD_MODIFY_BIT, decode_psr_def, encode_psr_bit, encode_psr_bits,
         extract_modify]
    \\ REPEAT STRIP_TAC
    << [
      SRW_TAC [ARITH_ss] [CONCAT62_EQ, extract_modify]
        \\ ASM_SIMP_TAC (arith_ss++wordsLib.WORD_BIT_EQ_ss) []
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      SRW_TAC [fcpLib.FCP_ss,ARITH_ss] [word_extract_def, w2w, word_bits_def]
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit],
      SRW_TAC [fcpLib.FCP_ss,ARITH_ss] [word_extract_def, w2w, word_bits_def]
        \\ FULL_SIMP_TAC std_ss [LESS_THM, encode_psr_bit]]);

val change_processor_state_thm = Q.prove(
  `!cpsr affectA affectI affectF enable disable mode.
      word_modify (\i b.
        if (i = 8) /\ affectA \/
           (i = 7) /\ affectI \/
           (i = 6) /\ affectF
        then
          ~enable /\ (disable \/ b)
        else if i < 5 /\ IS_SOME mode then
          (THE mode) ' i
        else
          b) (encode_psr cpsr) =
      encode_psr (cpsr with
        <| A := if affectA then ~enable /\ (disable \/ cpsr.A) else cpsr.A;
           I := if affectI then ~enable /\ (disable \/ cpsr.I) else cpsr.I;
           F := if affectF then ~enable /\ (disable \/ cpsr.F) else cpsr.F;
           M := if IS_SOME mode then THE mode else cpsr.M
        |>)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [encode_psr_bit]);

val cpsr_write_by_instr =
  SIMP_RULE (std_ss++boolSimps.LET_ss) [cpsr_write_by_instr_thm]
    cpsr_write_by_instr_def;

val spsr_write_by_instr =
  SIMP_RULE (std_ss++boolSimps.LET_ss) [spsr_write_by_instr_thm]
    spsr_write_by_instr_def;

(* ------------------------------------------------------------------------ *)

val eval_ss =
  std_ss++boolSimps.CONJ_ss++pred_setSimps.PRED_SET_ss++listSimps.LIST_ss -*
  ["lift_disj_eq", "lift_imp_disj"]

val instruction_rule = SIMP_RULE eval_ss
  [(GEN_ALL o SIMP_RULE std_ss [] o Q.ISPEC `\x. a NOTIN x`) COND_RAND,
   DECIDE ``~(a >= b) = a < b:num``,  condT_def,
   arm_coretypesTheory.NOT_IN_EMPTY_SPECIFICATION,
   instruction_def, run_instruction_def, null_check_instruction_def,
   dsp_support_def, kernel_support_def, change_processor_state_thm,
   arm_coretypesTheory.thumb2_support_def,
   arm_coretypesTheory.security_support_def,
   arm_coretypesTheory.thumbee_support_def];

val instructions =
  [("cpsr_write_by_instr", cpsr_write_by_instr),
   ("spsr_write_by_instr", spsr_write_by_instr)] @
  map (I ## instruction_rule) (!instructions);

val _ = map save_thm instructions;
val _ = computeLib.add_persistent_funs (map fst instructions);

val instructions = map fst (List.drop (instructions,2));

val instructions_list =
   "val instruction_list =\n  [" ^
   foldl (fn (t,s) => quote t ^ ",\n   " ^ s)
      (quote (hd instructions) ^ "]\n")  (tl instructions);

val _ = adjoin_to_theory
  {sig_ps = SOME (fn _ =>
     PP.add_string "val instruction_list : string list"),
   struct_ps = SOME (fn _ => PP.add_string instructions_list)};

(* ------------------------------------------------------------------------ *)

val _ = export_theory ();
