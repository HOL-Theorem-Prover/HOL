-----------------------------------------------------------------------
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- Instruction semantics ----------------------------------------------
-----------------------------------------------------------------------

construct LogicalOp {LogicalOp_AND LogicalOp_ORR LogicalOp_EOR}

construct MemOp {MemOp_LOAD MemOp_STORE MemOp_PREFETCH}

construct MemBarrierOp {MemBarrierOp_DSB MemBarrierOp_DMB MemBarrierOp_ISB}

construct MoveWideOp {MoveWideOp_N MoveWideOp_Z MoveWideOp_K}

construct RevOp {RevOp_RBIT RevOp_REV16 RevOp_REV32 RevOp_REV64}

construct SystemHintOp
{
   SystemHintOp_NOP SystemHintOp_YIELD SystemHintOp_WFE
   SystemHintOp_WFI SystemHintOp_SEV SystemHintOp_SEVL
}

construct PSTATEField {PSTATEField_DAIFSet PSTATEField_DAIFClr PSTATEField_SP}

-- ---------------------------------------------
-- ADR{P} <Xd>, <label>
-- ---------------------------------------------

define Address (page::bool, imm::dword, d::reg) =
{
   var base = PC;
   when page do base<11:0> <- 0;
   X(d) <- base + imm
}

-- ---------------------------------------------
-- 32-bit
-- ADC{S} <Wd>, <Wn>, <Wm>
-- SBC{S} <Wd>, <Wn>, <Wm>
--
-- 64-bit
-- ADC{S} <Xd>, <Xn>, <Xm>
-- SBC{S} <Xd>, <Xn>, <Xm>
-- ---------------------------------------------

define Data > AddSubCarry
       (sf::bits(N), sub_op::bool, setflags::bool, m::reg, n::reg, d::reg)
       with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = X(m);
   operand2 = if sub_op then ~operand2 else operand2;
   result`N, nzcv = AddWithCarry (operand1, operand2, PSTATE.C);
   SetTheFlags (setflags, nzcv);
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- ADD  <Wd|WSP>, <Wn|WSP>, <Wm>{, <extend> #<amount>}
-- ADDS <Wd>, <Wn|WSP>, <Wm>{, <extend> #<amount>}
-- SUB  <Wd|WSP>, <Wn|WSP>, <Wm>{, <extend> #<amount>}
-- SUBS <Wd>, <Wn|WSP>, <Wm>{, <extend> #<amount>}
--
-- 64-bit
-- ADD  <Xd|SP>, <Xn|SP>, <R><m>{, <extend> #<amount>}
-- ADDS <Xd>, <Xn|SP>, <R><m>{, <extend> #<amount>}
-- SUB  <Xd|SP>, <Xn|SP>, <R><m>{, <extend> #<amount>}
-- SUBS <Xd>, <Xn|SP>, <R><m>{, <extend> #<amount>}
-- ---------------------------------------------

define Data > AddSubExtendRegister
       (sf::bits(N), sub_op::bool, setflags::bool, m::reg,
        extend_type::ExtendType, imm3::bits(3), n::reg, d::reg)
       with N in 32, 64 =
{
   operand1 = if n == 31 then SP else X(n) :: bits(N);
   operand2 = ExtendReg (m, extend_type, [imm3]);
   operand2, carry_in = if sub_op then (~operand2, true) else (operand2, false);
   result`N, nzcv = AddWithCarry (operand1, operand2, carry_in);
   SetTheFlags (setflags, nzcv);
   if d == 31 and not setflags then
      SP <- result
   else
      X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- ADD  <Wd|WSP>, <Wn|WSP>, #<imm>{, <shift>}
-- ADDS <Wd>, <Wn|WSP>, #<imm>{, <shift>}
-- SUB  <Wd|WSP>, <Wn|WSP>, #<imm>{, <shift>}
-- SUBS <Wd>, <Wn|WSP>, #<imm>{, <shift>}
--
-- 64-bit
-- ADD  <Xd|SP>, <Xn|SP>, #<imm>{, <shift>}
-- ADDS <Xd>, <Xn|SP>, #<imm>{, <shift>}
-- SUB  <Xd|SP>, <Xn|SP>, #<imm>{, <shift>}
-- SUBS <Xd>, <Xn|SP>, #<imm>{, <shift>}
-- ---------------------------------------------

define Data > AddSubImmediate
       (sf::bits(N), sub_op::bool, setflags::bool,
        imm::bits(N), n::reg, d::reg) with N in 32, 64 =
{
   operand1 = if n == 31 then SP else X(n);
   operand2 = imm;
   operand2, carry_in = if sub_op then (~operand2, true) else (operand2, false);
   result`N, nzcv = AddWithCarry (operand1, operand2, carry_in);
   SetTheFlags (setflags, nzcv);
   if d == 31 and not setflags then
      SP <- result
   else
      X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- ADD{S} <Wd>, <Wn>, <Wm>{, <shift> #<amount>}
-- SUB{S} <Wd>, <Wn>, <Wm>{, <shift> #<amount>}
--
-- 64-bit
-- ADD{S} <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
-- SUB{S} <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
-- ---------------------------------------------

define Data > AddSubShiftedRegister
       (sf::bits(N), sub_op::bool, setflags::bool, shift_type::ShiftType,
        m::reg, imm::bits(6), n::reg, d::reg) with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = ShiftReg (m, shift_type, [imm]);
   operand2, carry_in = if sub_op then (~operand2, true) else (operand2, false);
   result`N, nzcv = AddWithCarry (operand1, operand2, carry_in);
   SetTheFlags (setflags, nzcv);
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- AND  <Wd|WSP>, <Wn>, #<imm>
-- ANDS <Wd>, <Wn>, #<imm>
-- EOR  <Wd|WSP>, <Wn>, #<imm>
-- ORR  <Wd|WSP>, <Wn>, #<imm>
--
-- 64-bit
-- AND  <Xd|SP>, <Xn>, #<imm>
-- ANDS <Xd>, <Xn>, #<imm>
-- EOR  <Xd|SP>, <Xn>, #<imm>
-- ORR  <Xd|SP>, <Xn>, #<imm>
-- ---------------------------------------------

define Data > LogicalImmediate
       (sf::bits(N), opc::LogicalOp, setflags::bool,
        imm::bits(N), n::reg, d::reg) with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = imm;
   result = match opc
            {
               case LogicalOp_AND => operand1 && operand2
               case LogicalOp_ORR => operand1 || operand2
               case LogicalOp_EOR => operand1 ?? operand2
            };
   SetTheFlags (setflags, Msb(result), result == 0, false, false);
   if d == 31 and not setflags then
      SP <- result
   else
      X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- AND{S} <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
-- BIC{S} <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
-- EON    <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
-- EOR    <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
-- ORN    <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
-- ORR    <Wd>, <Wn>, <Wm>{, <shift> #<ammount>}
--
-- 64-bit
-- AND{S} <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- BIC{S} <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- EON    <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- EOR    <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- ORN    <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- ORR    <Xd>, <Xn>, <Xm>{, <shift> #<ammount>}
-- ---------------------------------------------

define Data > LogicalShiftedRegister
       (sf::bits(N), opc::LogicalOp, invert::bool, setflags::bool,
        shift_type::ShiftType, shift_amount::nat, m::reg, n::reg, d::reg)
       with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = ShiftReg (m, shift_type, shift_amount) :: bits(N);
   operand2 = if invert then ~operand2 else operand2;
   result = match opc
            {
               case LogicalOp_AND => operand1 && operand2
               case LogicalOp_ORR => operand1 || operand2
               case LogicalOp_EOR => operand1 ?? operand2
            };
   SetTheFlags (setflags, Msb(result), result == 0, false, false);
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- ASRV <Wd>, <Wn>, <Wm>
-- LSLV <Wd>, <Wn>, <Wm>
-- LSRV <Wd>, <Wn>, <Wm>
-- RORV <Wd>, <Wn>, <Wm>
--
-- 64-bit
-- ASRV <Xd>, <Xn>, <Xm>
-- LSLV <Xd>, <Xn>, <Xm>
-- LSRV <Xd>, <Xn>, <Xm>
-- RORV <Xd>, <Xn>, <Xm>
-- ---------------------------------------------

define Data > Shift (sf::bits(N), shift_type::ShiftType, m::reg, n::reg, d::reg)
       with N in 32, 64 =
{
   operand2 = X(m) :: bits(N);
   result = ShiftReg (n, shift_type, [operand2] mod N) :: bits(N);
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- MOVK <Wd>, #<imm>{, LSL #<shift>}
-- MOVN <Wd>, #<imm>{, LSL #<shift>}
-- MOVZ <Wd>, #<imm>{, LSL #<shift>}
--
-- 64-bit
-- MOVK <Xd>, #<imm>{, LSL #<shift>}
-- MOVN <Xd>, #<imm>{, LSL #<shift>}
-- MOVZ <Xd>, #<imm>{, LSL #<shift>}
-- ---------------------------------------------

define Data > MoveWide
       (sf::bits(N), opcode::MoveWideOp, hw::bits(2), imm::half, d::reg)
       with N in 32, 64 =
{
   pos = [hw : '0000'];
   var result = if opcode == MoveWideOp_K then X(d) else 0`N;
   result<pos+15:pos> <- imm;
   result = if opcode == MoveWideOp_N then ~result else result;
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- BFM  <Wd>, <Wn>, #<immr>, #<imms>
-- SBFM <Wd>, <Wn>, #<immr>, #<imms>
-- UBFM <Wd>, <Wn>, #<immr>, #<imms>
--
-- 64-bit
-- BFM  <Xd>, <Xn>, #<immr>, #<imms>
-- SBFM <Xd>, <Xn>, #<immr>, #<imms>
-- UBFM <Xd>, <Xn>, #<immr>, #<imms>
-- ---------------------------------------------

define Data > BitfieldMove
       (sf::bits(N), inzero::bool, extend::bool, wmask::bits(N), tmask::bits(N),
        R::nat, S::nat, n::reg, d::reg)
       with N in 32, 64 =
{
   dst = if inzero then 0 else X(d);
   src = X(n);

   -- perform bitfield move on low bits
   bot = dst && ~wmask || ROR (src, R) && wmask;

   -- determine extension bits (sign, zero or dest register)
   top = if extend then Replicate ([src<S>]) else dst;

   -- combine extension bits and result bits
   X(d) <- top && ~tmask || bot && tmask
}

-- ---------------------------------------------
-- 32-bit
-- CCMN <Wn>, #<imm>, #<nzcv>, <cond>
-- CCMP <Wn>, #<imm>, #<nzcv>, <cond>
--
-- 64-bit
-- CCMN <Xn>, #<imm>, #<nzcv>, <cond>
-- CCMP <Xn>, #<imm>, #<nzcv>, <cond>
-- ---------------------------------------------

define Data > ConditionalCompareImmediate
       (sf::bits(N), sub_op::bool, imm::bits(N), cond::cond,
        nzcv::bool * bool * bool * bool, n::reg) with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = imm;
   if ConditionHolds(cond) then
   {
      operand2, carry_in =
         if sub_op then (~operand2, true) else (operand2, false);
      _, flags = AddWithCarry (operand1, operand2, carry_in);
      SetTheFlags (true, flags)
   }
   else
      SetTheFlags (true, nzcv)
}

-- ---------------------------------------------
-- 32-bit
-- CCMN <Wn>, <Wm>, #<nzcv>, <cond>
-- CCMP <Wn>, <Wm>, #<nzcv>, <cond>
--
-- 64-bit
-- CCMN <Xn>, <Xm>, #<nzcv>, <cond>
-- CCMP <Xn>, <Xm>, #<nzcv>, <cond>
-- ---------------------------------------------

define Data > ConditionalCompareRegister
       (sf::bits(N), sub_op::bool, cond::cond, nzcv::bool * bool * bool * bool,
        m::reg, n::reg) with N in 32, 64 =
{
   operand1 = X(n)::bits(N);
   operand2 = X(m);
   if ConditionHolds(cond) then
   {
      operand2, carry_in =
         if sub_op then (~operand2, true) else (operand2, false);
      _, flags = AddWithCarry (operand1, operand2, carry_in);
      SetTheFlags (true, flags)
   }
   else
      SetTheFlags (true, nzcv)
}

-- ---------------------------------------------
-- 32-bit
-- CSEL  <Wd>, <Wn>, <Wm>, <cond>
-- CSINC <Wd>, <Wn>, <Wm>, <cond>
-- CSINV <Wd>, <Wn>, <Wm>, <cond>
-- CSNEG <Wd>, <Wn>, <Wm>, <cond>
--
-- 64-bit
-- CSEL  <Xd>, <Xn>, <Xm>, <cond>
-- CSINC <Xd>, <Xn>, <Xm>, <cond>
-- CSINV <Xd>, <Xn>, <Xm>, <cond>
-- CSNEG <Xd>, <Xn>, <Xm>, <cond>
-- ---------------------------------------------

define Data > ConditionalSelect
       (sf::bits(N), else_inv::bool, else_inc::bool, cond::cond,
        m::reg, n::reg, d::reg)
       with N in 32, 64 =
{
   operand1 = X(n);
   operand2 = X(m);
   var result :: bits(N);
   if ConditionHolds (cond) then
      result <- operand1
   else
   {
      result <- operand2;
      when else_inv do result <- ~result;
      when else_inc do result <- result + 1
   };
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- CLS <Wd>, <Wn>
-- CLZ <Wd>, <Wn>
--
-- 64-bit
-- CLS <Xd>, <Xn>
-- CLZ <Xd>, <Xn>
-- ---------------------------------------------

define Data > CountLeading
       (sf::bits(N), count_clz::bool, n::reg, d::reg) with N in 32, 64 =
{
   operand1 = X(n) :: bits(N);
   result = if count_clz then
               CountLeadingZeroBits (operand1)
            else
               CountLeadingSignBits (operand1);
   X(d) <- [result] :: bits(N)
}

-- ---------------------------------------------
-- 32-bit
-- EXTR <Wd>, <Wn>, <Wm>, #<lsb>
--
-- 64-bit
-- EXTR <Xd>, <Xn>, <Xm>, #<lsb>
-- ---------------------------------------------

define Data > ExtractRegister
       (sf::bits(N), imms::bits(6), m::reg, n::reg, d::reg) with N in 32, 64 =
{
   lsb = [imms];
   operand1 = X(n) :: bits(N);
   operand2 = X(m) :: bits(N);
   concat = [operand1] : [operand2] :: bool list;
   result = [concat >>+ lsb] :: bits(N);
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- SDIV <Wd>, <Wn>, <Wm>
-- UDIV <Wd>, <Wn>, <Wm>
--
-- 64-bit
-- SDIV <Xd>, <Xn>, <Xm>
-- UDIV <Xd>, <Xn>, <Xm>
-- ---------------------------------------------

define Data > Division
       (sf::bits(N), unsigned::bool, m::reg, n::reg, d::reg) with N in 32, 64 =
{
   operand1 = X(n) :: bits(N);
   operand2 = X(m);
   result = if operand2 == 0 then
               0
            else if unsigned then
               operand1 div operand2
            else
               operand1 quot operand2;
   X(d) <- result
}

-- ---------------------------------------------
-- 32-bit
-- MADD <Wd>, <Wn>, <Wm>, <Wa>
-- MSUB <Wd>, <Wn>, <Wm>, <Wa>
--
-- 64-bit
-- MADD <Xd>, <Xn>, <Xm>, <Xa>
-- MSUB <Xd>, <Xn>, <Xm>, <Xa>
-- ---------------------------------------------

define Data > MultiplyAddSub
       (sf::bits(N), sub_op::bool, m::reg, a::reg, n::reg, d::reg)
       with N in 32, 64 =
{
   operand1 = X(n) :: bits(N);
   operand2 = X(m);
   operand3 = X(a);
   result = if sub_op then
               operand3 - operand1 * operand2
            else
               operand3 + operand1 * operand2;
   X(d) <- result
}

-- ---------------------------------------------
-- SMADDL <Xd>, <Wn>, <Wm>, <Xa>
-- UMADDL <Xd>, <Wn>, <Wm>, <Xa>
-- SMSUBL <Xd>, <Wn>, <Wm>, <Xa>
-- UMSUBL <Xd>, <Wn>, <Wm>, <Xa>
-- ---------------------------------------------

define Data > MultiplyAddSubLong
       (sub_op::bool, signed::bool, m::reg, a::reg, n::reg, d::reg) =
{
   operand1 = X(n)`32;
   operand2 = X(m)`32;
   operand3 = X(a)`64;
   product = ExtendWord (operand1, signed) * ExtendWord (operand2, signed);
   result = if sub_op then operand3 - product else operand3 + product;
   X(d) <- result
}

-- ---------------------------------------------
-- SMULH <Xd>, <Xn>, <Xm>
-- UMULH <Xd>, <Xn>, <Xm>
-- ---------------------------------------------

define Data > MultiplyHigh (signed::bool, m::reg, n::reg, d::reg) =
{
   operand1 = X(n)`64;
   operand2 = X(m)`64;
   result`128 = ExtendWord (operand1, signed) * ExtendWord (operand2, signed);
   X(d) <- result<127:64>
}

-- ---------------------------------------------
-- 32-bit
-- RBIT  <Wd>, <Wn>
-- REV16 <Wd>, <Wn>
-- REV   <Wd>, <Wn>
--
-- 64-bit
-- RBIT  <Xd>, <Xn>
-- REV16 <Xd>, <Xn>
-- REV32 <Xd>, <Xn>
-- REV   <Xd>, <Xn>
-- ---------------------------------------------

define Data > Reverse (sf::bits(N), op::RevOp, n::reg, d::reg)
       with N in 32, 64 =
{
    if N == 32 then
    {
       v = X(n)`32;
       result =
          match op
          {
             case RevOp_RBIT => Reverse (v)
             case RevOp_REV16 => v<23:16> : v<31:24> : v<7:0> : v<15:8>
             case RevOp_REV32 => v<7:0> : v<15:8> : v<23:16> : v<31:24>
             case RevOp_REV64 => UNKNOWN -- should be unreachable
          };
       X(d) <- result
    }
    else
    {
       v = X(n)`64;
       result =
          match op
          {
             case RevOp_RBIT => Reverse (v)
             case RevOp_REV16 =>
                 v<55:48> : v<63:56> : v<39:32> : v<47:40> :
                 v<23:16> : v<31:24> : v<7:0> : v<15:8>
             case RevOp_REV32 =>
                 v<39:32> : v<47:40> : v<55:48> : v<63:56> :
                 v<7:0> : v<15:8> : v<23:16> : v<31:24>
             case RevOp_REV64 =>
                 v<7:0> : v<15:8> : v<23:16> : v<31:24> :
                 v<39:32> : v<47:40> : v<55:48> : v<63:56>
          };
       X(d) <- result
    }
}

-- ---------------------------------------------
-- 32-bit
-- CRC32B <Wd>, <Wn>, <Wm>
-- CRC32H <Wd>, <Wn>, <Wm>
-- CRC32W <Wd>, <Wn>, <Wm>
--
-- 64-bit
-- CRC32X <Wd>, <Wn>, <Xm>
-- ---------------------------------------------

define CRCExt > CRC (sz::bits(N), crc32c::bool, m::reg, n::reg, d::reg)
       with N in 8, 16, 32, 64 =
{
   acc = X(n) :: bits(32);
   val = X(m) :: bits(N);
   poly = if crc32c then 0x1EDC6F41 else 0x04C11DB7;
   tempacc = Reverse ([acc]::bool list) : Zeros (N);
   tempval = Reverse ([val]::bool list) : Zeros (32);
   X(d) <- Reverse (Poly32Mod2 (tempacc ?? tempval, poly))
}

-- ---------------------------------------------
-- B.<cond> <label>
-- ---------------------------------------------

define Branch > BranchConditional (offset::dword, cond::cond) =
   when ConditionHolds(cond) do BranchTo (PC + offset, BranchType_JMP)

-- ---------------------------------------------
-- B  <label>
-- BL <label>
-- ---------------------------------------------

define Branch > BranchImmediate (offset::dword, branch_type::BranchType) =
{
   when branch_type == BranchType_CALL do X(30) <- PC + 4;
   BranchTo (PC + offset, branch_type)
}

-- ---------------------------------------------
-- BR  <Xn>
-- BLR <Xn>
-- RET {<Xn>}
-- ---------------------------------------------

define Branch > BranchRegister (n::reg, branch_type::BranchType) =
{
   target = X(n);
   when branch_type == BranchType_CALL do X(30) <- PC + 4;
   BranchTo (target, branch_type)
}

-- ---------------------------------------------
-- 32-bit
-- CBZ  <Wt>, <label>
-- CBNZ <Wt>, <label>
--
-- 64-bit
-- CBZ  <Xt>, <label>
-- CBNZ <Xt>, <label>
-- ---------------------------------------------

define Branch > CompareAndBranch
       (sf::bits(N), iszero::bool, offset::dword, t::reg) with N in 32, 64 =
{
   operand1 = X(t) :: bits(N);
   when (operand1 == 0) == iszero do BranchTo (PC + offset, BranchType_JMP)
}

-- ---------------------------------------------
-- 32-bit
-- TBZ  <Wt>, #<imm>, <label>
-- TBNZ <Wt>, #<imm>, <label>
--
-- 64-bit
-- TBZ  <Xt>, #<imm>, <label>
-- TBNZ <Xt>, #<imm>, <label>
-- ---------------------------------------------

define Branch > TestBitAndBranch
       (sf::bits(N), bit_pos::bits(6), bit_val::bool, offset::dword, t::reg)
       with N in 32, 64 =
{
   operand1 = X(t) :: bits(N);
   when operand1<[bit_pos]> == bit_val do BranchTo (PC + offset, BranchType_JMP)
}

-- ---------------------------------------------------------
-- Immediate:
--
-- LDR    <Wt|Xt>, [<Xn|SP>], #<simm>
-- LDRB   <Wt>, [<Xn|SP>], #<simm>
-- LDRH   <Wt>, [<Xn|SP>], #<simm>
-- LDRSB  <Wt|Xt>, [<Xn|SP>], #<simm>
-- LDRSH  <Wt|Xt>, [<Xn|SP>], #<simm>
-- LDRSW  <Xt>, [<Xn|SP>], #<simm>
--
-- LDR    <Wt|Xt>, [<Xn|SP>, #<imm>]{!}
-- LDRB   <Wt>, [<Xn|SP>, #<imm>]{!}
-- LDRH   <Wt>, [<Xn|SP>, #<imm>]{!}
-- LDRSB  <Wt|Xt>, [<Xn|SP>, #<imm>]{!}
-- LDRSH  <Wt|Xt>, [<Xn|SP>, #<imm>]{!}
-- LDRSW  <Xt>, [<Xn|SP>, #<imm>]{!}
--
-- LDUR   <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDURB  <Wt>, [<Xn|SP>, #<simm>]
-- LDURH  <Wt>, [<Xn|SP>, #<simm>]
-- LDURSB <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDURSH <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDURSW <Xt>, [<Xn|SP>, #<simm>]
--
-- LDTR   <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDTRB  <Wt>, [<Xn|SP>, #<simm>]
-- LDTRH  <Wt>, [<Xn|SP>, #<simm>]
-- LDTRSB <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDTRSH <Wt|Xt>, [<Xn|SP>, #<simm>]
-- LDTRSW <Xt>, [<Xn|SP>, #<simm>]
--
-- STR    <Wt|Xt>, [<Xn|SP>], #<simm>
-- STRB   <Wt>, [<Xn|SP>], #<simm>
-- STRH   <Wt>, [<Xn|SP>], #<simm>
--
-- STR    <Wt|Xt>, [<Xn|SP>, #<imm>]{!}
-- STRB   <Wt>, [<Xn|SP>, #<imm>]{!}
-- STRH   <Wt>, [<Xn|SP>, #<imm>]{!}
--
-- STUR   <Wt|Xt>, [<Xn|SP>, #<simm>]
-- STURB  <Wt>, [<Xn|SP>, #<simm>]
-- STURH  <Wt>, [<Xn|SP>, #<simm>]
--
-- STTR   <Wt|Xt>, [<Xn|SP>, #<simm>]
-- STTRB  <Wt>, [<Xn|SP>, #<simm>]
-- STTRH  <Wt>, [<Xn|SP>, #<simm>]
--
-- PRFM   <prfop>, [<Xn|SP>, #<pimm>]
-- PRFUM  <prfop>, [<Xn|SP>, #<simm>]
--
-- Register:
--
-- LDR    <Wt|Xt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- LDRB   <Wt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- LDRH   <Wt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- LDRSB  <Wt|Xt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- LDRSH  <Wt|Xt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- LDRSW  <Xt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
--
-- STR    <Wt|Xt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- STRB   <Wt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- STRH   <Wt>, [<Xn|SP>, <Xm|Wm>{, <extend> {<amount>}}]
-- ---------------------------------------------------------

unit LoadStoreSingle
       (size::bits(N), regsize_word::bool, memop::MemOp, acctype::AccType,
        signed::bool, wb_unknown::bool, rt_unknown::bool,
        wback::bool, postindex::bool, offset::dword, n::reg, t::reg)
       with N in 8, 16, 32, 64 =
{
   when n == 31 and memop <> MemOp_PREFETCH do CheckSPAlignment;
   address = if n == 31 then
                SP
             else
                X(n);
   address = if postindex then address else address + offset;
   match memop
   {
      case MemOp_STORE =>
      {
         data = if rt_unknown then
                   UNKNOWN`N
                else
                   X(t);
         Mem (address, N div 8, acctype) <- data
      }
      case MemOp_LOAD =>
      {
         data`N = Mem (address, N div 8, acctype);
         if regsize_word then
            X(t) <- ExtendWord (data, signed)`32
         else
            X(t) <- ExtendWord (data, signed)`64
      }
      case MemOp_PREFETCH => nothing -- stub
   };
   when wback do
   {
      address = if wb_unknown then
                   UNKNOWN
                else if postindex then
                   address + offset
                else address;
      if n == 31 then
         SP <- address
      else
         X(n) <- address
   }
}

define LoadStore > LoadStoreImmediate
       (size::bits(N), regsize_word::bool, memop::MemOp, acctype::AccType,
        signed::bool, wb_unknown::bool, rt_unknown::bool,
        wback::bool, postindex::bool, unsigned_offset::bool, offset::dword,
        n::reg, t::reg)
       with N in 8, 16, 32, 64 =
   LoadStoreSingle
     (size, regsize_word, memop, acctype, signed, wb_unknown, rt_unknown,
      wback, postindex, offset, n, t)

define LoadStore > LoadStoreRegister
       (size::bits(N), regsize_word::bool, memop::MemOp,
        signed::bool, m::reg, extend_type::ExtendType, shift::nat,
        n::reg, t::reg)
       with N in 8, 16, 32, 64 =
{
   offset = ExtendReg (m, extend_type, shift);
   LoadStoreSingle
     (size, regsize_word, memop, AccType_NORMAL, signed, false, false,
      false, false, offset, n, t)
}

-- ---------------------------------------------
-- 32-bit
-- LDNP <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]
-- LDP  <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]{!}
-- LDP  <Wt1>, <Wt2>, [<Xn|SP>], #<imm>
--
-- STNP <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]
-- STP  <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]{!}
-- STP  <Wt1>, <Wt2>, [<Xn|SP>], #<imm>
--
-- 64-bit
-- LDNP  <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]
-- LDP   <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]{!}
-- LDP   <Xt1>, <Xt2>, [<Xn|SP>], #<imm>
-- LDPSW <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]{!}
-- LDPSW <Xt1>, <Xt2>, [<Xn|SP>], #<imm>
--
-- STNP  <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]
-- STP   <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]{!}
-- STP   <Xt1>, <Xt2>, [<Xn|SP>], #<imm>
-- ---------------------------------------------

define LoadStore > LoadStorePair
       (size::bits(N), memop::MemOp, acctype::AccType, signed::bool,
        wb_unknown::bool, rt_unknown::bool, wback::bool,
        postindex::bool, offset::dword, n::reg, t::reg, t2::reg)
       with N in 32, 64 =
{
   dbytes = N div 8;
   when n == 31 do CheckSPAlignment;
   address = if n == 31 then
                SP
             else
                X(n);
   address = if postindex then address else address + offset;
   match memop
   {
      case MemOp_STORE =>
      {
         data1 = if rt_unknown and t == n then
                    UNKNOWN`N
                 else
                    X(t);
         data2 = if rt_unknown and t2 == n then
                    UNKNOWN`N
                 else
                    X(t2);
         Mem (address, dbytes, acctype) <- data1;
         Mem (address + [dbytes], dbytes, acctype) <- data2
      }
      case MemOp_LOAD =>
      {
         data1`N, data2`N =
            if rt_unknown then
               UNKNOWN
            else
               Mem (address, dbytes, acctype),
               Mem (address + [dbytes], dbytes, acctype);
         if signed {- and N == 32 -} then
         {
            X(t)  <- ExtendWord (data1, signed)`64;
            X(t2) <- ExtendWord (data2, signed)`64
         }
         else
         {
            X(t)  <- data1;
            X(t2) <- data2
         }
      }
      case _ => nothing -- should be unreachable
   };
   when wback do
   {
      address = if wb_unknown then
                   UNKNOWN
                else if postindex then
                   address + offset
                else address;
      if n == 31 then
         SP <- address
      else
         X(n) <- address
   }
}

-- ---------------------------------------------
-- LDAR   <Wt>, [<Xn|SP>{, #0}]
-- LDARB  <Wt>, [<Xn|SP>{, #0}]
-- LDARH  <Wt>, [<Xn|SP>{, #0}]
-- LDAXR  <Wt>, [<Xn|SP>{, #0}]
-- LDAXRB <Wt>, [<Xn|SP>{, #0}]
-- LDAXRH <Wt>, [<Xn|SP>{, #0}]
-- LDXR   <Wt>, [<Xn|SP>{, #0}]
-- LDXRB  <Wt>, [<Xn|SP>{, #0}]
-- LDXRH  <Wt>, [<Xn|SP>{, #0}]
--
-- LDAR   <Xt>, [<Xn|SP>{, #0}]
-- LDAXR  <Xt>, [<Xn|SP>{, #0}]
-- LDXR   <Xt>, [<Xn|SP>{, #0}]
--
-- STLR   <Wt>, [<Xn|SP>{, #0}]
-- STLRB  <Wt>, [<Xn|SP>{, #0}]
-- STLRH  <Wt>, [<Xn|SP>{, #0}]
-- STLXR  <Wt>, [<Xn|SP>{, #0}]
-- STLXRB <Wt>, [<Xn|SP>{, #0}]
-- STLXRH <Wt>, [<Xn|SP>{, #0}]
-- STXR   <Wt>, [<Xn|SP>{, #0}]
-- STXRB  <Wt>, [<Xn|SP>{, #0}]
-- STXRH  <Wt>, [<Xn|SP>{, #0}]
--
-- STLR   <Xt>, [<Xn|SP>{, #0}]
-- STLXR  <Xt>, [<Xn|SP>{, #0}]
-- STXR   <Xt>, [<Xn|SP>{, #0}]
-- ---------------------------------------------

-- Exclusive monitor stubs
bool ExclusiveMonitorPass (address::dword, n::nat) = UNKNOWN
unit SetExclusiveMonitors (address::dword, n::nat) = nothing
bits(1) ExclusiveMonitorStatus = UNKNOWN

define LoadStore > LoadStoreAcquire -- does not cover pair
       (size::bits(N), memop::MemOp, acctype::AccType, excl::bool,
       rn_unknown::bool, rt_unknown::bool, s::reg, n::reg, t::reg)
       with N in 8, 16, 32, 64 =
{
   dbytes = N div 8;
   when n == 31 do CheckSPAlignment;
   address = if n == 31 then
                SP
             else if rn_unknown then
                UNKNOWN
             else
                X(n);
   match memop
   {
      case MemOp_STORE =>
      {
         data = if rt_unknown then
                   UNKNOWN
                else
                   X(t)`N;
         if excl then
            if ExclusiveMonitorPass (address, dbytes) then
            {
               Mem (address, dbytes, acctype) <- data;
               status = ExclusiveMonitorStatus;
               X(s) <- [status]`32
            }
            else
               X(s) <- 1`32
         else
            Mem (address, dbytes, acctype) <- data
      }
      case MemOp_LOAD =>
      {
         when excl do SetExclusiveMonitors (address, dbytes);
         data`N = Mem (address, dbytes, acctype);
         if N == 64 then
            X(t) <- data
         else
            X(t) <- [data]`32
      }
      case _ => nothing -- should be unreachable
   }
}

-- ---------------------------------------------
-- LDXP  <Wt1>, <Wt2>, [<Xn|SP>{, #0}]
-- LDAXP <Wt1>, <Wt2>, [<Xn|SP>{, #0}]
-- STLXP <Wt1>, <Wt2>, [<Xn|SP>{, #0}]
-- STXP  <Wt1>, <Wt2>, [<Xn|SP>{, #0}]
--
-- LDXP  <Xt1>, <Xt2>, [<Xn|SP>{, #0}]
-- LDAXP <Xt1>, <Xt2>, [<Xn|SP>{, #0}]
-- STLXP <Xt1>, <Xt2>, [<Xn|SP>{, #0}]
-- STXP  <Xt1>, <Xt2>, [<Xn|SP>{, #0}]
-- ---------------------------------------------

define LoadStore > LoadStoreAcquirePair
       (size::bits(N), memop::MemOp, acctype::AccType,
        rn_unknown::bool, rt_unknown::bool, s::reg, n::reg, t::reg, t2::reg)
       with N in 64, 128 =
{
   dbytes = N div 8;
   when n == 31 do CheckSPAlignment;
   address = if n == 31 then
                SP
             else if rn_unknown then
                UNKNOWN
             else
                X(n);
   match memop
   {
      case MemOp_STORE =>
      {
         data`N =
            if rt_unknown then
               UNKNOWN
            else if N == 64 then
               if BigEndian then
                  [X(t)`32 : X(t2)`32]
               else
                  [X(t2)`32 : X(t)`32]
            else -- N == 128
               if BigEndian then
                  [X(t)`64 : X(t2)`64]
               else
                  [X(t2)`64 : X(t)`64];
         if ExclusiveMonitorPass (address, dbytes) then
         {
            Mem (address, dbytes, acctype) <- data;
            status = ExclusiveMonitorStatus;
            X(s) <- [status]`32
         }
         else
            X(s) <- 1`32
      }
      case MemOp_LOAD =>
      {
         SetExclusiveMonitors (address, dbytes);
         if rt_unknown then -- t == t2
            if N == 64 then
               X(t) <- UNKNOWN`32
            else
               X(t) <- UNKNOWN`64
         else if N == 64 then
         {
            data`N = Mem (address, dbytes, acctype);
            if BigEndian then
            {
               X(t)  <- data<63:32>;
               X(t2) <- data<31:0>
            }
            else
            {
               X(t)  <- data<31:0>;
               X(t2) <- data<63:32>
            }
         }
         else -- N == 128
         {
            when not Aligned (address, dbytes) do #ALIGNMENT_FAULT;
            X(t)  <- Mem (address, 8, acctype)`64;
            X(t2) <- Mem (address + 8, 8, acctype)`64
         }
      }
      case _ => nothing -- should be unreachable
   }
}

-- ---------------------------------------------
-- PRFM <prfop>, <label>
--
-- 32-bit
-- LDR   <Wt>, <label>
--
-- 64-bit
-- LDR   <Xt>, <label>
-- LDRSW <Xt>, <label>
-- ---------------------------------------------

define LoadStore > LoadLiteral
       (size::bits(N), memop::MemOp, signed::bool, offset::dword, t::reg)
       with N in 32, 64 =
{
   address = PC + offset;
   match memop
   {
      case MemOp_LOAD =>
      {
         data`N = Mem (address, N div 8, AccType_NORMAL);
         X(t) <- ExtendWord (data, signed)`64
      }
      case _ => nothing -- should be MemOp_PREFETCH -- stub
   }
}

-----------------------------------------------------------------------
-- Stubs --------------------------------------------------------------
-----------------------------------------------------------------------

-- DMB, DSB, ISB
define MemoryBarrier (op::MemBarrierOp, crm::bits(4)) =
   #UNDEFINED_FAULT ("MemoryBarrier")

-- CLREX
define ClearExclusive (imm::bits(4)) = #UNDEFINED_FAULT ("ClearExclusive")

-- HINT
define Hint (op::SystemHintOp) =
   if op == SystemHintOp_NOP then nothing else #UNDEFINED_FAULT ("Hint")

-- BRK
define Debug > Breakpoint (imm::half) = #UNDEFINED_FAULT ("Breakpoint")

-- DCPS1, DCPS2, DCPS3
define Debug > DebugSwitch (target_level::bits(2)) =
   #UNDEFINED_FAULT ("DebugSwitch")

-- DRPS
define Debug > DebugRestore = #UNDEFINED_FAULT ("DebugRestore")

-- HLT
define Debug > Halt (imm16::half) = #UNDEFINED_FAULT ("Halt")

-- SYS
define System > SystemInstruction
       (sys_op1::bits(3), sys_op2::bits(3), sys_crn::bits(4), sys_crm::bits(4),
        has_result::bool, t::reg) =
   #UNDEFINED_FAULT ("System")

-- MRS and MSR (register)
define System > MoveSystemRegister
       (read::bool, sys_op0::bits(3), sys_op1::bits(3), sys_op2::bits(3),
        sys_crn::bits(4), sys_crm::bits(4), t::reg) =
   #UNDEFINED_FAULT ("MoveSystemRegister")

-- MSR (immediate)
define System > MoveImmediateProcState (field::PSTATEField, operand::bits(4)) =
   #UNDEFINED_FAULT ("MoveImmediateProcState")

-- level 1, SVC
define System > SupervisorCall (imm16::half) =
   #UNDEFINED_FAULT ("SupervisorCall")

-- level 2, HVC
define System > HypervisorCall (imm16::half) =
   #UNDEFINED_FAULT ("HypervisorCall")

-- level 3, SMC
define System > SecureMonitorCall (imm16::half) =
   #UNDEFINED_FAULT ("SecureMonitorCall")

-- ERET
define System > ExceptionReturn = #UNDEFINED_FAULT ("ExceptionReturn")

define Unallocated = #UNDEFINED_FAULT ("Unallocated")

define Reserved = #UNDEFINED_FAULT ("Reserved")

define Run

-----------------------------------------------------------------------
-- Helper functions for decoding --------------------------------------
-----------------------------------------------------------------------

LogicalOp * bool DecodeLogicalOp (opc::bits(2)) =
   match opc
   {
      case 0b00 => LogicalOp_AND, false
      case 0b01 => LogicalOp_ORR, false
      case 0b10 => LogicalOp_EOR, false
      case 0b11 => LogicalOp_AND, true
   }

instruction NoOperation = Hint (SystemHintOp_NOP)

-- . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

instruction LoadStoreRegister
   (size::bits(2), regsize_word::bool, memop::MemOp,
    signed::bool, m::reg, extend_type::ExtendType, shift::nat, n::reg, t::reg) =
{
   a = regsize_word, memop, signed, m, extend_type, shift, n, t;
   match size
   {
      case 0b00 => LoadStore (LoadStoreRegister@8 (0, a))
      case 0b01 => LoadStore (LoadStoreRegister@16 (1, a))
      case 0b10 => LoadStore (LoadStoreRegister@32 (2, a))
      case 0b11 => LoadStore (LoadStoreRegister@64 (3, a))
   }
}

instruction LoadStoreImmediateN
   (size::bits(2), regsize_word::bool, memop::MemOp, acctype::AccType,
    signed::bool, wb_unknown::bool, rt_unknown::bool,
    wback::bool, postindex::bool, unsigned_offset::bool, offset::dword,
    n::reg, t::reg) =
{
   a = regsize_word, memop, acctype, signed, wb_unknown, rt_unknown,
       wback, postindex, unsigned_offset, offset, n, t;
   match size
   {
      case 0b00 => LoadStore (LoadStoreImmediate@8 (0, a))
      case 0b01 => LoadStore (LoadStoreImmediate@16 (1, a))
      case 0b10 => LoadStore (LoadStoreImmediate@32 (2, a))
      case 0b11 => LoadStore (LoadStoreImmediate@64 (3, a))
   }
}

instruction LoadStoreImmediate
   (size::bits(2), opc::bits(2), acctype::AccType,
    wback::bool, postindex::bool, unsigned_offset::bool, offset::dword,
    Rn::reg, Rt::reg) =
{
   memop, regsize_word, signed =
      if not opc<1> then -- store or zero-extending load
         (if opc<0> then MemOp_LOAD else MemOp_STORE), size <> '11', false
      else if size == '11' then
         MemOp_PREFETCH, UNKNOWN, UNKNOWN
      else -- sign-extending load
         MemOp_LOAD, opc<0>, true;
   wb_unknown = false;
   rt_unknown = false;
   if memop == MemOp_LOAD and wback and Rn == Rt and Rn <> 31 then
      -- this is constrained unpredictable, so take your pick
      -- SML will invoke case 0
      match UNKNOWN ("LoadImmediate unpredictable") :: bits(2)
      {
         case 0 =>
         {
            wback = false;
            LoadStoreImmediateN
              (size, regsize_word, memop, acctype, signed, wb_unknown,
               rt_unknown, wback, postindex, unsigned_offset, offset, Rn, Rt)
         }
         case 1 =>
         {
            wb_unknown = true;
            LoadStoreImmediateN
              (size, regsize_word, memop, acctype, signed, wb_unknown,
               rt_unknown, wback, postindex, unsigned_offset, offset, Rn, Rt)
         }
         case 2 => Unallocated
         case 3 => NoOperation
      }
   else if memop == MemOp_STORE and wback and Rn == Rt and Rn <> 31 then
      -- this is constrained unpredictable, so take your pick
      -- SML will invoke case 0
      match UNKNOWN ("StoreImmediate unpredictable") :: bits(2)
      {
         case 0 =>
            LoadStoreImmediateN
              (size, regsize_word, memop, acctype, signed, wb_unknown,
               rt_unknown, wback, postindex, unsigned_offset, offset, Rn, Rt)
         case 1 =>
         {
            rt_unknown = true;
            LoadStoreImmediateN
              (size, regsize_word, memop, acctype, signed, wb_unknown,
               rt_unknown, wback, postindex, unsigned_offset, offset, Rn, Rt)
         }
         case 2 => Unallocated
         case 3 => NoOperation
      }
   else
      LoadStoreImmediateN
        (size, regsize_word, memop, acctype, signed, wb_unknown,
         rt_unknown, wback, postindex, unsigned_offset, offset, Rn, Rt)
}

-- . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

instruction LoadStorePairN
   (sf::bits(1), memop::MemOp, acctype::AccType, signed::bool,
    wb_unknown::bool, rt_unknown::bool, wback::bool, postindex::bool,
    offset::dword, n::reg, t::reg, t2::reg) =
{
   a = memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex,
       offset, n, t, t2;
   if sf == '1' then
      LoadStore (LoadStorePair@64 (1, a))
   else
      LoadStore (LoadStorePair@32 (0, a))
}

instruction LoadStorePair
   (sf::bits(1), memop::MemOp, acctype::AccType, signed::bool, wback::bool,
    postindex::bool, offset::dword, Rn::reg, Rt::reg, Rt2::reg) =
{
   wb_unknown = false;
   rt_unknown = false;
   if memop == MemOp_LOAD and wback and (Rn == Rt or Rn == Rt2) and Rn <> 31
      then
      -- this is constrained unpredictable, so take your pick
      -- SML will invoke case 0
      match UNKNOWN ("LoadPair unpredictable") :: bits(2)
      {
         case 0 =>
         {
            wback = false;
            LoadStorePairN
              (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
               postindex, offset, Rn, Rt, Rt2)
         }
         case 1 =>
         {
            wb_unknown = true;
            LoadStorePairN
              (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
               postindex, offset, Rn, Rt, Rt2)
         }
         case 2 => Unallocated
         case 3 => NoOperation
      }
   else if memop == MemOp_STORE and wback and (Rn == Rt or Rn == Rt2) and
           Rn <> 31
      then
      -- this is constrained unpredictable, so take your pick
      -- SML will invoke case 0
      match UNKNOWN ("StorePair unpredictable") :: bits(2)
      {
         case 0 =>
            LoadStorePairN
              (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
               postindex, offset, Rn, Rt, Rt2)
         case 1 =>
         {
            rt_unknown = true;
            LoadStorePairN
              (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
               postindex, offset, Rn, Rt, Rt2)
         }
         case 2 => Unallocated
         case 3 => NoOperation
      }
   else if memop == MemOp_LOAD and Rt == Rt2 then
      -- this is constrained unpredictable, so take your pick
      -- SML will invoke case 0
      match UNKNOWN ("LoadPair Rt = Rt2 unpredictable") :: bits(2)
      {
         case 0 =>
         {
            rt_unknown = true;
            LoadStorePairN
              (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
               postindex, offset, Rn, Rt, Rt2)
         }
         case 1 => Unallocated
         case _ => NoOperation
      }
   else
      LoadStorePairN
        (sf, memop, acctype, signed, wb_unknown, rt_unknown, wback,
         postindex, offset, Rn, Rt, Rt2)
}

-- . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

instruction LoadStoreAcquireN
   (size::bits(2), memop::MemOp, acctype::AccType, excl::bool, pair::bool,
    rn_unknown::bool, rt_unknown::bool, s::reg, n::reg, t::reg, t2::reg) =
{
   if pair then
   {
      a = memop, acctype, rn_unknown, rt_unknown, s, n, t, t2;
      if size == 2 then
         LoadStore (LoadStoreAcquirePair@64 (2, a))
      else
         LoadStore (LoadStoreAcquirePair@128 (3, a))
   }
   else
   {
      a = memop, acctype, excl, rn_unknown, rt_unknown, s, n, t;
      match size
      {
         case 0b00 => LoadStore (LoadStoreAcquire@8 (0, a))
         case 0b01 => LoadStore (LoadStoreAcquire@16 (1, a))
         case 0b10 => LoadStore (LoadStoreAcquire@32 (2, a))
         case 0b11 => LoadStore (LoadStoreAcquire@64 (3, a))
      }
   }
}

instruction LoadStoreAcquire
   (size::bits(2), memop::MemOp, acctype::AccType, excl::bool, pair::bool,
    Rs::reg, Rn::reg, Rt::reg, Rt2::reg) =
{
   rt_unknown, rn_unknown, ast =
      if memop == MemOp_LOAD and pair and Rt == Rt2 then
         -- this is constrained unpredictable, so take your pick
         -- SML will invoke case 0
         match UNKNOWN ("LoadAcquire unpredictable") :: bits(2)
         {
            case 0 => true, false, None
            case 1 => false, false, Some (Unallocated)
            case _ => false, false, Some (NoOperation)
         }
      else (false, false, None);
   rt_unknown, rn_unknown, ast =
      if memop == MemOp_STORE and excl and Rs == Rt or (pair and Rs == Rt2) then
         -- this is constrained unpredictable, so take your pick
         -- SML will invoke case 0
         match UNKNOWN ("StoreAcquire Rs = Rt unpredictable") :: bits(2)
         {
            case 0 => true, rn_unknown, ast
            case 1 => rt_unknown, rn_unknown, ast
            case 2 => rt_unknown, rn_unknown, Some (Unallocated)
            case 3 => rt_unknown, rn_unknown, Some (NoOperation)
         }
      else
         (rt_unknown, rn_unknown, ast);
   rt_unknown, rn_unknown, ast =
      if memop == MemOp_STORE and excl and Rs == Rn and Rn <> 31 then
         -- this is constrained unpredictable, so take your pick
         -- SML will invoke case 0
         match UNKNOWN ("StoreAcquire Rs = Rn unpredictable") :: bits(2)
         {
            case 0 => rt_unknown, true, ast
            case 1 => rt_unknown, rn_unknown, ast
            case 2 => rt_unknown, rn_unknown, Some (Unallocated)
            case 3 => rt_unknown, rn_unknown, Some (NoOperation)
         }
      else
         (rt_unknown, rn_unknown, ast);
   match ast
   {
      case Some (i) => i
      case None =>
         LoadStoreAcquireN
           (size, memop, acctype, excl, pair, rn_unknown, rt_unknown,
            Rs, Rn, Rt, Rt2)
   }
}

-----------------------------------------------------------------------
-- Instruction decoding -----------------------------------------------
-----------------------------------------------------------------------

pattern
{
   op S sf         ` 1
   CRm             ` 4
   Rs Rm Rn
   Rd Rt Rt2       ` 5
   imm6 immr imms  ` 6
   imm7            ` 7
   imm9            ` 9
   imm12           ` 12
   imm16           ` 16
   imm19           ` 19
}

instruction Decode (w::word) =
   match w
   {
      -- Scalar floating-point (binary64 and integer-register transfers)
      case '0001111001100000010000 Rn Rd' => FloatingPoint (FMov (Rn, Rd))
      case '0001111001100000110000 Rn Rd' => FloatingPoint (FAbs (Rn, Rd))
      case '0001111001100001010000 Rn Rd' => FloatingPoint (FNeg (Rn, Rd))
      case '0001111001100001110000 Rn Rd' => FloatingPoint (FSqrt (Rn, Rd))
      case '0001111001100000000000 Rn Rd' => FloatingPoint (FToInt32 (Rn, Rd))
      case '0001111001100010000000 Rn Rd' => FloatingPoint (FFromInt32 (Rn, Rd))
      case '00011110011 Rm 001010 Rn Rd' => FloatingPoint (FAdd (Rm, Rn, Rd))
      case '00011110011 Rm 001110 Rn Rd' => FloatingPoint (FSub (Rm, Rn, Rd))
      case '00011110011 Rm 000010 Rn Rd' => FloatingPoint (FMul (Rm, Rn, Rd))
      case '00011110011 Rm 000110 Rn Rd' => FloatingPoint (FDiv (Rm, Rn, Rd))
      case '0001111000100110000000 Rn Rd' => FloatingPoint (FMovToGeneral@32 (0`32, Rn, Rd))
      case '1001111001100110000000 Rn Rd' => FloatingPoint (FMovToGeneral@64 (1`64, Rn, Rd))
      case '0001111000100111000000 Rn Rd' => FloatingPoint (FMovFromGeneral@32 (0`32, Rn, Rd))
      case '1001111001100111000000 Rn Rd' => FloatingPoint (FMovFromGeneral@64 (1`64, Rn, Rd))
      case '00011110011 Rm 001000 Rn 00000' => FloatingPoint (FCompare (Rn, Rm))
      case '00011111010 Rm 0 Ra`5 Rn Rd' => FloatingPoint (FMAdd (Rm, Ra, Rn, Rd))

      ------------------------
      -- Address
      ------------------------
      case 'op immlo`2 10000 immhi Rd' =>
      {
         page = [op];
         imm = if page then SignExtend (immhi : immlo : 0`12)
                       else SignExtend (immhi : immlo);
         Address (page, imm, Rd)
      }

      ------------------------
      -- AddSubShiftedRegister
      ------------------------
      case '_ op S 01011 11    0 Rm imm6 Rn Rd' => Reserved
      case '0 op S 01011 shift 0 Rm imm6 Rn Rd' =>
         if imm6<5> then Reserved
         else Data (AddSubShiftedRegister@32
                      (0, [op], [S], DecodeShift (shift), Rm, imm6, Rn, Rd))
      case '1 op S 01011 shift 0 Rm imm6 Rn Rd' =>
         Data (AddSubShiftedRegister@64
                 (1, [op], [S], DecodeShift (shift), Rm, imm6, Rn, Rd))

      ------------------------
      -- AddSubExtendRegister
      ------------------------
      case '0 op S 01011 00 1 Rm option imm3 Rn Rd' =>
         if imm3 >+ 4 then
            Reserved
         else
            Data (AddSubExtendRegister@32
                    (0, [op], [S], Rm, DecodeRegExtend (option), imm3, Rn, Rd))
      case '1 op S 01011 00 1 Rm option imm3 Rn Rd' =>
         if imm3 >+ 4 then
            Reserved
         else
            Data (AddSubExtendRegister@64
                    (1, [op], [S], Rm, DecodeRegExtend (option), imm3, Rn, Rd))

      ------------------------
      -- AddSubImmediate
      ------------------------
      case '_ op S 10001 1 _`1 imm12 Rn Rd' => Reserved
      case '0 op S 10001 shift imm12 Rn Rd' =>
      {
         imm = if shift == '00' then [imm12] else [imm12] << 12;
         Data (AddSubImmediate@32 (0, [op], [S], imm, Rn, Rd))
      }
      case '1 op S 10001 shift imm12 Rn Rd' =>
      {
         imm = if shift == '00' then [imm12] else [imm12] << 12;
         Data (AddSubImmediate@64 (1, [op], [S], imm, Rn, Rd))
      }

      ------------------------
      -- AddSubCarry
      ------------------------
      case '0 op S 11010000 Rm 000000 Rn Rd' =>
         Data (AddSubCarry@32 (0, [op], [S], Rm, Rn, Rd))
      case '1 op S 11010000 Rm 000000 Rn Rd' =>
         Data (AddSubCarry@64 (1, [op], [S], Rm, Rn, Rd))

      ------------------------
      -- LogicalShiftedRegister
      ------------------------
      case '0 opc`2 01010 shift N Rm imm6 Rn Rd' =>
         if imm6<5> then Reserved
         else
         {
            invert = N == '1';
            opc, setflags = DecodeLogicalOp (opc);
            Data (LogicalShiftedRegister@32
                      (0, opc, invert, setflags, DecodeShift (shift), [imm6],
                       Rm, Rn, Rd))
         }
      case '1 opc`2 01010 shift N Rm imm6 Rn Rd' =>
      {
         invert = N == '1';
         opc, setflags = DecodeLogicalOp (opc);
         Data (LogicalShiftedRegister@64
                   (1, opc, invert, setflags, DecodeShift (shift), [imm6],
                    Rm, Rn, Rd))
      }

      ------------------------
      -- LogicalImmediate
      ------------------------
      case '0 opc`2 100100 1 immr`6 imms`6 Rn Rd' => Reserved
      case '0 opc`2 100100 N immr`6 imms`6 Rn Rd' => -- N must be 0
         match DecodeBitMasks (N, imms, immr, true)
         {
            case Some (imm, _) =>
            {
               opc, setflags = DecodeLogicalOp (opc);
               Data (LogicalImmediate@32 (0, opc, setflags, imm, Rn, Rd))
            }
            case None => Reserved
         }
      case '1 opc`2 100100 N immr`6 imms`6 Rn Rd' =>
         match DecodeBitMasks (N, imms, immr, true)
         {
            case Some (imm, _) =>
            {
               opc, setflags = DecodeLogicalOp (opc);
               Data (LogicalImmediate@64 (1, opc, setflags, imm, Rn, Rd))
            }
            case None => Reserved
         }

      ------------------------
      -- Shift
      ------------------------
      case '0 00 11010110 Rm 0010 op2 Rn Rd' =>
         Data (Shift@32 (0, DecodeShift (op2), Rm, Rn, Rd))
      case '1 00 11010110 Rm 0010 op2 Rn Rd' =>
         Data (Shift@64 (1, DecodeShift (op2), Rm, Rn, Rd))

      ------------------------
      -- MoveWide
      ------------------------
      case '0 opc`2 100101 1 _ imm16 Rd' => Unallocated
      case 'sf 01 100101 hw imm16 Rd' => Unallocated
      case 'sf opc 100101 hw imm16 Rd' =>
      {
         opcode = match opc
                  {
                     case 0b00 => MoveWideOp_N
                     case 0b10 => MoveWideOp_Z
                     case 0b11 => MoveWideOp_K
                     case 0b01 => UNKNOWN -- unreachable
                  };
         if sf == '1' then
            Data (MoveWide@64 (1, opcode, hw, imm16, Rd))
         else
            Data (MoveWide@32 (0, opcode, hw, imm16, Rd))
      }

      ------------------------
      -- BitfieldMove
      ------------------------
      case '_`1 11  100110 N immr imms Rn Rd' => Unallocated
      case '0 opc 100110 N immr imms Rn Rd' =>
         if N == '1' or immr<5> or imms<5> then
            Reserved
         else
         {
            inzero, extend =
               match opc
               {
                  case 0b00 => true, true   -- SBFM
                  case 0b01 => false, false -- BFM
                  case 0b10 => true, false  -- UBFM
                  case _ => UNKNOWN
               };
            match DecodeBitMasks (N, imms, immr, false)
            {
               case Some (wmask, tmask) =>
                  Data
                   (BitfieldMove@32
                      (0, inzero, extend, wmask, tmask, [immr], [imms], Rn, Rd))
               case None => Reserved
            }
         }
      case '1 opc 100110 N immr imms Rn Rd' =>
         if N == '0' then
            Reserved
         else
         {
            inzero, extend =
               match opc
               {
                  case 0b00 => true, true   -- SBFM
                  case 0b01 => false, false -- BFM
                  case 0b10 => true, false  -- UBFM
                  case _ => UNKNOWN
               };
            match DecodeBitMasks (N, imms, immr, false)
            {
               case Some (wmask, tmask) =>
                  Data
                   (BitfieldMove@64
                      (1, inzero, extend, wmask, tmask, [immr], [imms], Rn, Rd))
               case None => Reserved
            }
         }

      ------------------------
      -- ConditionalCompareImmediate
      ------------------------
      case '0 op 111010010 imm5 cond 10 Rn 0 n`1 z`1 c`1 v`1' =>
      {
         nzcv = [n], [z], [c], [v];
         Data (ConditionalCompareImmediate@32 (0, [op], [imm5], cond, nzcv, Rn))
      }
      case '1 op 111010010 imm5 cond 10 Rn 0 n`1 z`1 c`1 v`1' =>
      {
         nzcv = [n], [z], [c], [v];
         Data (ConditionalCompareImmediate@64 (1, [op], [imm5], cond, nzcv, Rn))
      }

      ------------------------
      -- ConditionalCompareRegister
      ------------------------
      case '0 op 111010010 Rm cond 00 Rn 0 n`1 z`1 c`1 v`1' =>
      {
         nzcv = [n], [z], [c], [v];
         Data (ConditionalCompareRegister@32 (0, [op], cond, nzcv, Rm, Rn))
      }
      case '1 op 111010010 Rm cond 00 Rn 0 n`1 z`1 c`1 v`1' =>
      {
         nzcv = [n], [z], [c], [v];
         Data (ConditionalCompareRegister@64 (1, [op], cond, nzcv, Rm, Rn))
      }

      ------------------------
      -- ConditionalSelect
      ------------------------
      case '0 op 011010100 Rm cond 0 o2 Rn Rd' =>
         Data (ConditionalSelect@32 (0, [op], [o2], cond, Rm, Rn, Rd))
      case '1 op 011010100 Rm cond 0 o2 Rn Rd' =>
         Data (ConditionalSelect@64 (1, [op], [o2], cond, Rm, Rn, Rd))

      ------------------------
      -- CountLeading
      ------------------------
      case '0 10110101100000000010 op Rn Rd' =>
         Data (CountLeading@32 (0, [op], Rn, Rd))
      case '1 10110101100000000010 op Rn Rd' =>
         Data (CountLeading@64 (1, [op], Rn, Rd))

      ------------------------
      -- ExtractRegister
      ------------------------
      case '0 00100111 N 0 Rm imms Rn Rd' =>
         if N <> 0 then
            Unallocated
         else if imms<5> then
            Reserved
         else
            Data (ExtractRegister@32 (0, imms, Rm, Rn, Rd))
      case '1 00100111 N 0 Rm imms Rn Rd' =>
         if N <> 1 then
            Unallocated
         else
            Data (ExtractRegister@64 (1, imms, Rm, Rn, Rd))

      ------------------------
      -- Division
      ------------------------
      case '0 0011010110 Rm 00001 o1 Rn Rd' =>
         Data (Division@32 (0, o1 == '0', Rm, Rn, Rd))
      case '1 0011010110 Rm 00001 o1 Rn Rd' =>
         Data (Division@64 (1, o1 == '0', Rm, Rn, Rd))

      ------------------------
      -- MultiplyAddSub
      ------------------------
      case '0 0011011000 Rm o0 Ra Rn Rd' =>
         Data (MultiplyAddSub@32 (0, o0 == '1', Rm, Ra, Rn, Rd))
      case '1 0011011000 Rm o0 Ra Rn Rd' =>
         Data (MultiplyAddSub@64 (1, o0 == '1', Rm, Ra, Rn, Rd))

      ------------------------
      -- MultiplyAddSubLong
      ------------------------
      case '1 00 11011 U 01 Rm o0 Ra Rn Rd' =>
         Data (MultiplyAddSubLong ([o0], U == '0', Rm, Ra, Rn, Rd))

      ------------------------
      -- MultiplyHigh
      ------------------------
      case '1 00 11011 U 10 Rm 0 (11111) Rn Rd' =>
         Data (MultiplyHigh (U == '0', Rm, Rn, Rd))

      ------------------------
      -- Reverse
      ------------------------
      case '0 1011010110000000000 11 Rn Rd' => Unallocated
      case '0 1011010110000000000 opc Rn Rd' =>
         Data (Reverse@32 (0, [opc], Rn, Rd))
      case '1 1011010110000000000 opc Rn Rd' =>
         Data (Reverse@64 (1, [opc], Rn, Rd))

      ------------------------
      -- CRC
      ------------------------
      case '0 0011010110 Rm 010 C 00 Rn Rd' =>
         CRCExt (CRC@8 (0, [C], Rm, Rn, Rd))
      case '0 0011010110 Rm 010 C 01 Rn Rd' =>
         CRCExt (CRC@16 (1, [C], Rm, Rn, Rd))
      case '0 0011010110 Rm 010 C 10 Rn Rd' =>
         CRCExt (CRC@32 (2, [C], Rm, Rn, Rd))
      case '1 0011010110 Rm 010 C 11 Rn Rd' =>
         CRCExt (CRC@64 (3, [C], Rm, Rn, Rd))

      ------------------------
      -- BranchConditional
      ------------------------
      case '01010100 imm19 0 cond' =>
         Branch (BranchConditional (SignExtend (imm19 : '00'), cond))

      ------------------------
      -- BranchImmediate
      ------------------------
      case 'op 00101 imm26' =>
      {
         branch_type = if op == '1' then BranchType_CALL else BranchType_JMP;
         Branch (BranchImmediate (SignExtend (imm26 : '00'), branch_type))
      }

      ------------------------
      -- BranchRegister
      ------------------------
      case '110101100 00 11111000000 Rn 00000' =>
         Branch (BranchRegister (Rn, BranchType_JMP))
      case '110101100 01 11111000000 Rn 00000' =>
         Branch (BranchRegister (Rn, BranchType_CALL))
      case '110101100 10 11111000000 Rn 00000' =>
         Branch (BranchRegister (Rn, BranchType_RET))
      case '110101100 _  11111000000 Rn 00000' => Unallocated

      ------------------------
      -- CompareAndBranch
      ------------------------
      case 'sf 011010 op imm19 Rt' =>
      {
         iszero = op == '0';
         offset = SignExtend (imm19 : '00');
         if sf == '1' then
            Branch (CompareAndBranch@64 (1, iszero, offset, Rt))
         else
            Branch (CompareAndBranch@32 (0, iszero, offset, Rt))
      }

      ------------------------
      -- TestBitAndBranch
      ------------------------
      case 'sf 011011 op b40 imm14 Rt' =>
      {
         bit_pos = sf : b40;
         bit_val = [op];
         offset = SignExtend (imm14 : '00');
         if sf == '1' then
            Branch (TestBitAndBranch@64 (1, bit_pos, bit_val, offset, Rt))
         else
            Branch (TestBitAndBranch@32 (0, bit_pos, bit_val, offset, Rt))
      }

      ------------------------
      -- LoadStoreImmediate
      ------------------------
      case '10 111000 11 0 imm9 _`2 Rn Rt' => Unallocated
      case '10 111001 11 imm12 Rn Rt' => Unallocated
      case '11 111000 11 0 imm9 _`2 Rn Rt' => Unallocated
      case '11 111000 1 _ 0 imm9 1 0 Rn Rt' => Unallocated
      -- Pre-index and post-index
      -- LDR, LDRB, LDRH, LDRSB, LDRSH, LDRSW
      -- STR, STRB, STRH
      case 'size 111000 opc 0 imm9 P 1 Rn Rt' =>
      {
         wback = true;
         postindex = P == '0';
         offset = SignExtend (imm9);
         acctype = AccType_NORMAL;
         LoadStoreImmediate
           (size, opc, acctype, wback, postindex, false, offset, Rn, Rt)
      }
      -- Unscaled offset and unprivileged
      -- LDUR, LDURB, LDURH, LDURSB, LDURSH, LDURSW
      -- STUR, STURB, STURH
      -- LDTR, LDTRB, LDTRH, LDTRSB, LDTRSH, LDTRSW
      -- STTR, STTRB, STTRH
      -- PRFUM
      case 'size 111000 opc 0 imm9 U 0 Rn Rt' =>
      {
         wback = false;
         postindex = false;
         offset = SignExtend (imm9);
         acctype = if U == '1' then AccType_UNPRIV else AccType_NORMAL;
         LoadStoreImmediate
           (size, opc, acctype, wback, postindex, false, offset, Rn, Rt)
      }
      -- Unsigned offset
      -- LDR, LDRB, LDRH, LDRSB, LDRSH, LDRSW
      -- STR, STRB, STRH
      -- PRFM
      case 'size 111001 opc imm12 Rn Rt' =>
      {
         wback = false;
         postindex = false;
         offset = LSL (ZeroExtend (imm12), [size]);
         acctype = AccType_NORMAL;
         LoadStoreImmediate
           (size, opc, acctype, wback, postindex, true, offset, Rn, Rt)
      }

      ------------------------
      -- LoadStoreRegister
      ------------------------
      case '1 _`1 111000 11 1 Rm option`3 S 10 Rn Rt' => Unallocated
      case 'size`2 111000 opc`2 1 Rm 00 _`1 S 10 Rn Rt' => Reserved
      case 'size`2 111000 opc`2 1 Rm 10 _`1 S 10 Rn Rt' => Reserved
      case 'size 111000 opc 1 Rm option`3 S 10 Rn Rt' =>
      {
         scale = [size];
         extend_type = DecodeRegExtend (option);
         shift = if S == '1' then scale else 0;
         memop, regsize_word, signed =
            if not opc<1> then -- store or zero-extending load
               (if opc<0> then MemOp_LOAD else MemOp_STORE), size <> '11',
               false
            else if size == '11' then
               MemOp_PREFETCH, UNKNOWN, UNKNOWN
            else -- sign-extending load
               MemOp_LOAD, opc<0>, true;
         LoadStoreRegister
           (size, regsize_word, memop, signed, Rm, extend_type, shift,
            Rn, Rt)
      }

      ------------------------
      -- LoadLiteral
      ------------------------
      case 'opc 011000 imm19 Rt' =>
      {
         offset = SignExtend (imm19 : '00');
         match opc
         {
            case 0b00 =>
               LoadStore (LoadLiteral@32 (0, MemOp_LOAD, false, offset, Rt))
            case 0b01 =>
               LoadStore (LoadLiteral@64 (1, MemOp_LOAD, false, offset, Rt))
            case 0b10 =>
               LoadStore (LoadLiteral@32 (2, MemOp_LOAD, true, offset, Rt))
            case 0b11 =>
               LoadStore (LoadLiteral@32 (3, MemOp_PREFETCH, false, offset, Rt))
         }
      }

      ------------------------
      -- LoadStorePair
      ------------------------
      case '_`1 1 10100 _`2 0 imm7 Rt2 Rn Rt' => Unallocated
      case '11 10100 _ imm7 Rt2 Rn Rt' => Unallocated
      case 'sf S 10100 00 L imm7 Rt2 Rn Rt' => Unallocated
      case 'sf S 10100 P W L imm7 Rt2 Rn Rt' =>
      {
         wback = W == '1';
         signed = S == '1';
         postindex = P == '0';
         nontemporal = not (wback or signed) and postindex;
         postindex = not nontemporal and postindex;
         acctype = if nontemporal then AccType_STREAM else AccType_NORMAL;
         scale = 0n2 + [sf];
         offset = LSL (SignExtend (imm7), scale);
         memop = if L == '1' then MemOp_LOAD else MemOp_STORE;
         LoadStorePair
            (sf, memop, acctype, signed, wback, postindex, offset, Rn, Rt, Rt2)
      }

      ------------------------
      -- LoadStoreAcquire
      ------------------------
      case 'size`2 001000 1 L 0 Rs 0 Rt2 Rn Rt' => Unallocated
      case 'size`2 001000 1 L 1 Rs _`1 Rt2 Rn Rt' => Unallocated
      case '0 _`1 001000 o2`1 L 1 Rs o0`1 Rt2 Rn Rt' => Unallocated
      case 'size 001000 o2 L o1 Rs o0 Rt2 Rn Rt' =>
      {
         memop = if L == '1' then MemOp_LOAD else MemOp_STORE;
         acctype = if o0 == '1' then AccType_ORDERED else AccType_ATOMIC;
         excl = o2 == '0';
         pair = o1 == '1';
         LoadStoreAcquire (size, memop, acctype, excl, pair, Rs, Rn, Rt, Rt2)
      }

      ------------------------
      -- MoveSystemRegister
      ------------------------
      case '1101010100 L`1 1 o0`1 op1 CRn CRm op2 Rt' =>
         System (MoveSystemRegister ([L], 2 + [o0], op1, op2, CRn, CRm, Rt))

      ------------------------
      -- MoveImmediateProcState
      ------------------------
      case '1101010100000 000 0100 CRm 101 11111' =>
         System (MoveImmediateProcState (PSTATEField_SP, CRm))
      case '1101010100000 011 0100 CRm 110 11111' =>
         System (MoveImmediateProcState (PSTATEField_DAIFSet, CRm))
      case '1101010100000 011 0100 CRm 111 11111' =>
         System (MoveImmediateProcState (PSTATEField_DAIFClr, CRm))

      ------------------------
      -- MemoryBarrier
      ------------------------
      case '11010101000000110011 CRm 1 11 11111' => Unallocated
      case '11010101000000110011 CRm 1 opc 11111' => MemoryBarrier ([opc], CRm)

      ------------------------
      -- Breakpoint
      ------------------------
      case '11010100001 imm16 00000' => Debug (Breakpoint (imm16))

      ------------------------
      -- Hint
      ------------------------
      case '11010101000000110010 CRm op2 11111' =>
      {
         op = if CRm == 0 and op2 <+ 6 then [op2] else SystemHintOp_NOP;
         Hint (op)
      }

      ------------------------
      -- ClearExclusive
      ------------------------
      case '11010101000000110011 CRm 01011111' => ClearExclusive (CRm)

      ------------------------
      -- DebugRestore
      ------------------------
      case '11010110101111110000001111100000' => Debug (DebugRestore)

      ------------------------
      -- DebugSwith
      ------------------------
      case '11010100101 imm16 000 LL' => Debug (DebugSwitch (LL))

      ------------------------
      -- Halt
      ------------------------
      case '11010100010 imm16 00000' => Debug (Halt (imm16))

      ------------------------
      -- ExceptionReturn
      ------------------------
      case '11010110100111110000001111100000' => System (ExceptionReturn)

      ------------------------
      -- SupervisorCall
      -- HyperviorCall
      -- SecureMonitorCall
      ------------------------
      case '11010100000 imm16 00001' => System (SupervisorCall (imm16))
      case '11010100000 imm16 00010' => System (HypervisorCall (imm16))
      case '11010100000 imm16 00011' => System (SecureMonitorCall (imm16))

      ------------------------
      -- System
      ------------------------
      case '1101010100 L 01 op1 CRn CRm op2 Rt' =>
         System (SystemInstruction (op1, op2, CRn, CRm, [L], Rt))

      ------------------------
      -- Unallocated
      ------------------------
      case _ => Unallocated
   }

clear patterns

-----------------------------------------------------------------------
-- Next state ---------------------------------------------------------
-----------------------------------------------------------------------

word Fetch = Mem (PC, 4, AccType_IFETCH)

unit Next =
{
   branch_hint <- None;
   Run (Decode (Fetch));
   when not (IsSome (branch_hint)) do PC <- PC + 4
}
