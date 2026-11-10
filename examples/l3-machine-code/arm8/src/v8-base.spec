-----------------------------------------------------------------------
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-----------------------------------------------------------------------

-----------------------------------
-- Word sizes (64-bit architecture)
-----------------------------------

type cond = bits(4)
type reg  = bits(5)
type byte = bits(8)
type half = bits(16)
type word = bits(32)
type dword = bits(64)
type qword = bits(128)

-------------------
-- Model exceptions
-------------------

exception ASSERT :: string
exception UNDEFINED_FAULT :: string
exception ALIGNMENT_FAULT

---------------------------------------
-- Processor state and system registers
---------------------------------------

record ProcState
{
   N   :: bool    -- Negative condition flag
   Z   :: bool    -- Zero condition flag
   C   :: bool    -- Carry condition flag
   V   :: bool    -- oVerflow condition flag
   EL  :: bits(2) -- exception level
   SPS :: bool    -- Stack pointer select
}

register TCR_EL1 :: dword
{
   38 : TBI1  -- top-byte ignored (for address calculation)
   37 : TBI0
}

register TCR_EL2_EL3 :: word
{
   20 : TBI
}

register SCTLRType :: word
{
-- 26 : UCI
   25 : EE      -- Exception endianness
   24 : E0E     -- Endianness of explicit data access (1 - big-endian)
-- 19 : WXN
-- 18 : nTWE
-- 16 : nTWI
-- 15 : UCT
-- 14 : DZE
-- 12 : I
--  9 : UMA
--  8 : SED
--  7 : ITD
--  5 : CP15BEN
    4 : SA0     -- Stack alignment check enabled for EL0
    3 : SA      -- Stack alignment check enable
--  2 : C
    1 : A       -- Aligment check enable
--  0 : M
}

declare
{
   TCR_EL1   :: TCR_EL1
   TCR_EL2   :: TCR_EL2_EL3
   TCR_EL3   :: TCR_EL2_EL3
   SCTLR_EL1 :: SCTLRType
   SCTLR_EL2 :: SCTLRType
   SCTLR_EL3 :: SCTLRType
   PSTATE    :: ProcState
}

---------------------------
-- Registers
---------------------------

declare
{
   REG    :: reg -> dword
   FP_REG :: reg -> dword -- Scalar FP register bank (SIMD upper halves omitted)
   FPCR   :: word
   FPSR   :: word
   SP_EL0 :: dword
   SP_EL1 :: dword
   SP_EL2 :: dword
   SP_EL3 :: dword
   PC     :: dword
}

component X (n::reg) :: bits(N) with N in 8, 16, 32, 64
{
   value = if n == 31 then 0 else [REG (n)]
   assign value = -- when N not in set {32, 64} do #ASSERT ("bad X write")
      when n <> 31 do REG (n) <- [value]
}

component SP :: bits(N) with N in 8, 16, 32, 64
{
   value =
   {
      sp = if not PSTATE.SPS then
              SP_EL0
           else match PSTATE.EL
                {
                   case 0 => SP_EL0
                   case 1 => SP_EL1
                   case 2 => SP_EL2
                   case 3 => SP_EL3
                };
     [sp]
   }
   assign value = -- when N not in set {32, 64} do #ASSERT ("bad SP write")
   {
      v = [value];
      if not PSTATE.SPS then
         SP_EL0 <- v
      else match PSTATE.EL
           {
              case 0 => SP_EL0 <- v
              case 1 => SP_EL1 <- v
              case 2 => SP_EL2 <- v
              case 3 => SP_EL3 <- v
           }
   }
}

bits(2) TranslationRegime = if PSTATE.EL <> 0 then PSTATE.EL else 1

SCTLRType SCTLR =
{
   regime = TranslationRegime;
   match regime
   {
      case 1 => SCTLR_EL1
      case 2 => SCTLR_EL2
      case 3 => SCTLR_EL3
      case 0 => UNKNOWN -- unreachable
   }
}

construct BranchType
{
   BranchType_CALL    BranchType_ERET BranchType_DBGEXIT
   BranchType_RET     BranchType_JMP  BranchType_EXCEPTION
   BranchType_UNKNOWN
}

declare branch_hint :: BranchType option

unit Hint_Branch (branch_type::BranchType) = branch_hint <- Some (branch_type)

unit BranchTo (target::dword, branch_type::BranchType) =
{
   var target = target;
   Hint_Branch (branch_type);
   match PSTATE.EL
   {
       case 0 or 1 =>
       {
          when target<55> and TCR_EL1.TBI1 do
             target<63:56> <- '11111111';
          when not target<55> and TCR_EL1.TBI0 do
             target<63:56> <- '00000000'
       }
       case 2 => when TCR_EL2.TBI do target<63:56> <- '00000000'
       case 3 => when TCR_EL3.TBI do target<63:56> <- '00000000'
   };
   PC <- target
}

---------------------------
-- Memory
---------------------------

declare MEM :: dword -> byte

construct AccType
{
   AccType_NORMAL AccType_VEC        -- Normal loads and stores
   AccType_STREAM AccType_VECSTREAM  -- Streaming loads and stores
   AccType_ATOMIC                    -- Atomic loads and stores
   AccType_ORDERED                   -- Load-Acquire and Store-Release
   AccType_UNPRIV                    -- Load and store unprivileged
   AccType_IFETCH                    -- Instruction fetch
   AccType_PTW                       -- Page table walk
   -- Other operations
   AccType_DC                        -- Data cache maintenance
   AccType_IC                        -- Instruction cache maintenance
   AccType_AT                        -- Address translation
}

bits(N) Align (w::bits(N), n::nat) = [n * ([w] div n)]

bool Aligned (w::bits(N), n::nat) = w == Align (w, n)

unit CheckSPAlignment =
{
   sp = SP`64;
   stack_align_check = if PSTATE.EL == 0 then SCTLR_EL1.SA0 else SCTLR.SA;
   when stack_align_check and not Aligned (sp, 16) do #ALIGNMENT_FAULT
}

unit CheckAlignment
     (address::dword, size::nat, acctype::AccType, iswrite::bool) =
{
   if not Aligned (address, size) and
      (acctype == AccType_ATOMIC or acctype == AccType_ORDERED or SCTLR.A) then
      #ALIGNMENT_FAULT
   else nothing
}

bool BigEndian = (if PSTATE.EL == 0 then SCTLR_EL1.E0E else SCTLR.EE)

(bool list) list ByteList (l::bool list) =
    match l
    {
       case Nil => Nil
       case b0 @ b1 @ b2 @ b3 @ b4 @ b5 @ b6 @ v7 @ rest =>
          list {b0, b1, b2, b3, b4, b5, b6, v7} @ ByteList (rest)
       case rest => list {rest}
    }

bool list BigEndianReverse (l::bool list) = Concat (Reverse (ByteList (l)))

component Mem (address::dword, size::nat, acctype::AccType) :: bits(N)
          with N in 8, 16, 32, 64, 128
{
   value =
   {
      CheckAlignment (address, size, acctype, false);
      var value = Nil;
      for i in 0 .. size - 1 do value <- [MEM (address + [i])] : value;
      [if BigEndian then BigEndianReverse (value) else value]
   }
   assign value =
   {
      CheckAlignment (address, size, acctype, true);
      value = if BigEndian then BigEndianReverse ([value]) else [value];
      for i in 0 .. size - 1 do MEM (address + [i]) <- [value<8*i+7:8*i>]
   }
}

-----------------------------
-- General Operations
-----------------------------

bool ConditionTest (cond::cond, N::bool, Z::bool, C::bool, V::bool) =
{
   -- Evaluate base condition
   result =
     match cond<3:1>
     {
        case 0b000 => Z                -- EQ or NE
        case 0b001 => C                -- CS or CC
        case 0b010 => N                -- MI or PL
        case 0b011 => V                -- VS or VC
        case 0b100 => C and not Z      -- HI or LS
        case 0b101 => N == V           -- GE or LT
        case 0b110 => N == V and not Z -- GT or LE
        case 0b111 => true             -- AL
     };

   -- Condition flag values in the set '111x' indicate always true.
   -- Otherwise, invert condition if necessary.
   if cond<0> and cond != 0b1111 then
      not result
   else
      result
}

bool ConditionHolds (cond::cond) =
    ConditionTest (cond, PSTATE.N, PSTATE.Z, PSTATE.C, PSTATE.V)

bool list Ones  (n::nat) = PadLeft (true, n, Nil)
bool list Zeros (n::nat) = PadLeft (false, n, Nil)

bits(N) Replicate (l::bool list) = -- when N mod Length(l) == 0 do #ASSERT ("")
   [l ^ (N div Length (l))]

int HighestSetBit (w::bits(N)) = if w == 0 then -1 else [Log2 (w)]

nat CountLeadingZeroBits (w::bits(N)) = [[N] - 0i1 - HighestSetBit (w)]

nat CountLeadingSignBits (w::bits(N)) =
   CountLeadingZeroBits ((w >>+ 1) ?? (w && ~(1 #>> 1))) - 1

bool list Poly32Mod2_loop (i::nat, data::bool list, poly::bool list) =
   if i < 32 then
      data
   else
   {
      data = if data<i> then
                data<Length(data)-1:i> :
                data<i-1:0> ?? PadRight (false, i, poly)
             else
                data;
      Poly32Mod2_loop (i - 1, data, poly)
   }

word Poly32Mod2 (data::bool list, poly::word) =
   [Poly32Mod2_loop (Length (data) - 1, data, [poly])<31:0>]

{-
word Poly32Mod2 (data::bool list, poly::word) =
{
    N = Length (data);
    var data = data;
    poly = [poly] :: bool list;
    for i in N - 1 .. 32 do
       when data<i> do
          data<i-1:0> <- data<i-1:0> ?? PadRight (false, i, poly);
    [data<31:0>]
}
-}

-----------------------------
-- Addition and Subtraction
-----------------------------

bits(N) * bool * bool * bool * bool
   AddWithCarry (x::bits(N), y::bits(N), carry_in::bool) =
{
   unsigned_sum = [x] + [y] + [carry_in] :: nat;
   signed_sum = [x] + [y] + [carry_in] :: int;
   result = [unsigned_sum]::bits(N);
   n = Msb(result);
   z = result == 0;
   c = [result] != unsigned_sum;
   v = [result] != signed_sum;
   result, n, z, c, v
}

unit SetTheFlags (setflags::bool, n::bool, z::bool, c::bool, v::bool) =
   when setflags do
   {
      PSTATE.N <- n;
      PSTATE.Z <- z;
      PSTATE.C <- c;
      PSTATE.V <- v
   }

-------------
-- Shifting
-------------

inline bits(N) LSL (x::bits(N), shift::nat) = x << shift
inline bits(N) LSR (x::bits(N), shift::nat) = x >>+ shift
inline bits(N) ASR (x::bits(N), shift::nat) = x >> shift
inline bits(N) ROR (x::bits(N), shift::nat) = x #>> shift

construct ShiftType {ShiftType_LSL ShiftType_LSR ShiftType_ASR ShiftType_ROR}

ShiftType DecodeShift (sh::bits(2)) = [sh]

bits(N) ShiftValue (value::bits(N), ty::ShiftType, amount::nat) =
   match ty
   {
      case ShiftType_LSL => LSL (value, amount)
      case ShiftType_LSR => LSR (value, amount)
      case ShiftType_ASR => ASR (value, amount)
      case ShiftType_ROR => ROR (value, amount)
   }

bits(N) ShiftReg (reg::reg, ty::ShiftType, amount::nat) with N in 32, 64 =
   ShiftValue (X(reg)::bits(N), ty, amount)

-------------
-- Extension
-------------

bits(N) ExtendWord (w::bits(M), signed::bool) =
   if signed then SignExtend (w) else ZeroExtend (w)

bits(N) Extend (l::bool list, unsigned::bool) =
   if unsigned or not Head(l) then [l] else [PadLeft (true, N, l)]

construct ExtendType
{
   ExtendType_UXTB ExtendType_UXTH ExtendType_UXTW ExtendType_UXTX
   ExtendType_SXTB ExtendType_SXTH ExtendType_SXTW ExtendType_SXTX
}

ExtendType DecodeRegExtend (ext::bits(3)) = [ext]

bits(N) ExtendValue (value::bits(N), ty::ExtendType, sh::nat)
        with N in 8, 16, 32, 64 =
{
   value = [value] :: bool list;
   unsigned, len =
      match ty
      {
         case ExtendType_SXTB => false, 8
         case ExtendType_SXTH => false, 16
         case ExtendType_SXTW => false, 32
         case ExtendType_SXTX => false, 64
         case ExtendType_UXTB => true, 8
         case ExtendType_UXTH => true, 16
         case ExtendType_UXTW => true, 32
         case ExtendType_UXTX => true, 64
      };
   len = Min (len, N - sh);
   Extend (value<len-1:0> << sh, unsigned)
}

bits(N) ExtendReg (reg::reg, ty::ExtendType, sh::nat) with N in 8, 16, 32, 64 =
   ExtendValue (X(reg)::bits(N), ty, sh)

-------------
-- Masks
-------------

(bits(M) * bits(M)) option DecodeBitMasks
   (immN::bits(1), imms::bits(6), immr::bits(6), immediate::bool) =
{
   len = HighestSetBit (immN : ~imms);
   if len < 1 then
      None
   else
   {
      len = [len]::nat;
      levels = [Ones (len)]`6;
      S = imms && levels;
      R = immr && levels;
      if immediate and S == levels then
         None
      else
      {
         diff = [S - R] :: bool list;
         esize = 0n2 ** len;
         d = diff<len-1:0>;
         welem = PadLeft (false, esize, Ones ([S] + 0n1));
         telem = PadLeft (false, esize, Ones ([d] + 0n1));
         wmask = Replicate (welem #>> [R]);
         tmask = Replicate (telem);
         Some (wmask, tmask)
      }
   }
}
