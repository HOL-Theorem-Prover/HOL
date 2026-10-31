---------------------------------------------------------------------------
--
-- RISC-V Model
-- Based on the MIPS specification by Anthony Fox, University of Cambridge
--
-- Copyright (C) 2014, 2015 Anthony Fox, University of Cambridge
-- Copyright (C) 2014, 2015 Alexandre Joannou, University of Cambridge
-- Copyright (C) 2015, SRI International.
--
-- This software was developed by SRI International and the University
-- of Cambridge Computer Laboratory under DARPA/AFRL contract
-- FA8750-11-C-0249 ("MRC2"), as part of the DARPA MRC research
-- programme, and under DARPA/AFRL contract FA8750-10-C-0237
-- ("CTSRD"), as part of the DARPA CRASH research programme.
--
-- See the LICENSE file for details.
--
-- For syntax highlighting, treat this file as Haskell source.
---------------------------------------------------------------------------


---------------------------------------------------------------------------
-- Basic types
---------------------------------------------------------------------------

type id       = bits(8)           -- max 256 cores
type reg      = bits(5)
type creg     = bits(12)

type byte     = bits(8)
type half     = bits(16)
type word     = bits(32)
type dword    = bits(64)

type fprnd    = bits(3)         -- rounding mode
type fpval    = bits(64)

type exc_code = bits(4)

-- raw instructions
construct rawInstType
{ Half :: half
  Word :: word
}

-- instruction fields
type opcode   = bits(7)
type imm12    = bits(12)
type imm20    = bits(20)
type amo      = bits(1)

-- memory and caches

construct accessType { Read, Write }
construct fetchType  { Instruction, Data }

-- RV64* base.

type regType  = dword
type vAddr    = dword
type pAddr    = dword

type pAddrIdx = bits(61)        -- raw index into physical memory
                                -- arranged in 8-byte blocks

-- Miscellaneous
exception UNDEFINED         :: string
exception INTERNAL_ERROR    :: string

---------------------------------------------------------------------------
-- Memory types for Load/Store instructions
---------------------------------------------------------------------------

type memWidth       = bits(3)

memWidth BYTE       = 0
memWidth HALFWORD   = 1
memWidth WORD       = 3
memWidth DOUBLEWORD = 7

---------------------------------------------------------------------------
-- Processor architecture
---------------------------------------------------------------------------

type arch_base = bits(2)

construct Architecture
{
  RV32I, RV64I, RV128I
}

-- The misa.MXL encoding (P §3.1.1 Table 11 p.27).  Only RV64I is
-- implemented: XLEN is 64 in every mode.

arch_base archBase(a::Architecture) =
    match a
    { case RV32I      => 1
      case RV64I      => 2
      case RV128I     => 3
    }

Architecture architecture(ab::arch_base) =
    match ab
    { case 1          => RV32I
      case 2          => RV64I
      case 3          => RV128I
      case _          => #UNDEFINED("Unknown architecture: " : [[ab] :: nat])
    }

string archName(a::Architecture) =
    match a
    { case RV32I      => "RV32I"
      case RV64I      => "RV64I"
      case RV128I     => "RV128I"
    }

---------------------------------------------------------------------------
-- Privilege levels
---------------------------------------------------------------------------

-- Privilege levels and their encoding (P §1.2 Table 1 p.11).  This hart
-- has M, S and U; the encoding 10 is reserved.

type priv_level = bits(2)

construct Privilege
{ User
, Supervisor
, Machine
}

priv_level privLevel(p::Privilege) =
    match p
    { case User       => 0
      case Supervisor => 1
      case Machine    => 3
    }

-- Total: the reserved 10 decodes as User, which is also what
-- legalize_mstatus stores for an mstatus.MPP write of 10 ([D2]).
Privilege privilege(p::priv_level) =
    match p
    { case 1          => Supervisor
      case 3          => Machine
      case _          => User
    }

string privName(p::Privilege) =
    match p
    { case User       => "U"
      case Supervisor => "S"
      case Machine    => "M"
    }

---------------------------------------------------------------------------
-- Extension Context Status
---------------------------------------------------------------------------

type ext_status = bits(2)

construct ExtStatus
{ Off
, Initial
, Clean
, Dirty
}

ext_status ext_status(e::ExtStatus) =
    match e
    { case Off      => 0
      case Initial  => 1
      case Clean    => 2
      case Dirty    => 3
    }

ExtStatus extStatus(e::ext_status) =
    match e
    { case 0        => Off
      case 1        => Initial
      case 2        => Clean
      case 3        => Dirty
    }

string extStatusName(e::ExtStatus) =
    match e
    { case Off      => "Off"
      case Initial  => "Initial"
      case Clean    => "Clean"
      case Dirty    => "Dirty"
    }

---------------------------------------------------------------------------
-- Exceptions and Interrupts
---------------------------------------------------------------------------

-- Interrupts and their codes (P §3.1.15 Table 16 p.50): supervisor and
-- machine software, timer and external interrupts.
construct Interrupt
{ SSI, MSI, STI, MTI, SEI, MEI
}

exc_code interruptIndex(i::Interrupt) =
    match i
    { case SSI          => 1
      case MSI          => 3
      case STI          => 5
      case MTI          => 7
      case SEI          => 9
      case MEI          => 11
    }

-- Exceptions and their codes (P §3.1.15 Table 16 p.50).  Address
-- translation raises the page faults (translateAddr).
construct ExceptionType
{ Fetch_Misaligned
, Fetch_Fault
, Illegal_Instr
, Breakpoint
, Load_Misaligned
, Load_Fault
, Store_AMO_Misaligned
, Store_AMO_Fault
, UMode_Env_Call
, SMode_Env_Call
, MMode_Env_Call
, Fetch_PageFault
, Load_PageFault
, Store_AMO_PageFault
}

exc_code excCode(e::ExceptionType) =
    match e
    { case Fetch_Misaligned     => 0x0
      case Fetch_Fault          => 0x1
      case Illegal_Instr        => 0x2
      case Breakpoint           => 0x3

      case Load_Misaligned      => 0x4
      case Load_Fault           => 0x5
      case Store_AMO_Misaligned => 0x6
      case Store_AMO_Fault      => 0x7

      case UMode_Env_Call       => 0x8
      case SMode_Env_Call       => 0x9
      case MMode_Env_Call       => 0xB

      case Fetch_PageFault      => 0xC
      case Load_PageFault       => 0xD
      case Store_AMO_PageFault  => 0xF
    }

string excName(e::ExceptionType) =
    match e
    { case Fetch_Misaligned     => "MISALIGNED_FETCH"
      case Fetch_Fault          => "FAULT_FETCH"
      case Illegal_Instr        => "ILLEGAL_INSTRUCTION"
      case Breakpoint           => "BREAKPOINT"

      case Load_Misaligned      => "MISALIGNED_LOAD"
      case Load_Fault           => "FAULT_LOAD"
      case Store_AMO_Misaligned => "MISALIGNED_STORE_AMO"
      case Store_AMO_Fault      => "FAULT_STORE_AMO"

      case UMode_Env_Call       => "U-EnvCall"
      case SMode_Env_Call       => "S-EnvCall"
      case MMode_Env_Call       => "M-EnvCall"

      case Fetch_PageFault      => "PAGEFAULT_FETCH"
      case Load_PageFault       => "PAGEFAULT_LOAD"
      case Store_AMO_PageFault  => "PAGEFAULT_STORE_AMO"
    }

---------------------------------------------------------------------------
-- Control and Status Registers (CSRs)
---------------------------------------------------------------------------

-- Machine-Level CSRs

-- Machine ISA (P §3.1.1 Figure 2 p.27, Table 12 p.28).  The hart is
-- RV64 I M A F D C with S and U; only C is writable ([D14]).
register misa :: regType
{ 63-62 : MXL       -- machine XLEN: 1 = 32, 2 = 64, 3 = 128 (Table 11)
,    20 : U         -- user mode
,    18 : S         -- supervisor mode
,    12 : M         -- integer multiply/divide
,     8 : I         -- base integer ISA
,     5 : F         -- single-precision floating point
,     3 : D         -- double-precision floating point
,     2 : C         -- compressed instructions (IALIGN = 16)
,     0 : A         -- atomics
}

-- Machine status (P §3.1.6 Figure 8 p.32).  Only the writable fields are
-- stored: UXL, SXL and SD are produced when mstatus is read
-- (read_mstatus, [D20]) and every other field is read-only zero.
register mstatus :: regType
{    22 : TSR       -- trap SRET (P §3.1.6.6 p.37)
,    21 : TW        -- timeout wait
,    20 : TVM       -- trap virtual memory
,    19 : MXR       -- make executable readable (P §3.1.6.4 p.35)
,    18 : SUM       -- permit supervisor user memory access
,    17 : MPRV      -- modify privilege of loads and stores
, 14-13 : FS        -- floating-point context status (P §3.1.6.7 p.38)
, 12-11 : MPP       -- privilege before the last trap into M-mode
,     8 : SPP       -- privilege before the last trap into S-mode
,     7 : MPIE      -- MIE before the last trap into M-mode
,     5 : SPIE      -- SIE before the last trap into S-mode
,     3 : MIE       -- M-mode interrupt enable (P §3.1.6.1 p.32)
,     1 : SIE       -- S-mode interrupt enable
}

-- Interrupt pending and enable bits (P §3.1.9 Figures 15-16 p.43-44): bit
-- i is for interrupt code i.  Of mip only SSIP, STIP and the software
-- SEIP bit are stored; read_mip adds the others.
register mip :: regType
{    11 : MEIP      -- machine external
,     9 : SEIP      -- supervisor external
,     7 : MTIP      -- machine timer
,     5 : STIP      -- supervisor timer
,     3 : MSIP      -- machine software
,     1 : SSIP      -- supervisor software
}

register mie :: regType
{    11 : MEIE
,     9 : SEIE
,     7 : MTIE
,     5 : STIE
,     3 : MSIE
,     1 : SSIE
}

-- mcause and scause (P §3.1.15 Figure 22 p.49)
register mcause :: regType
{    63 : Int       -- interrupt
,  62-0 : EC        -- exception code
}

-- Machine-level CSRs (P §3.1).  medeleg, mideleg, mtvec, mcounteren,
-- menvcfg, mcountinhibit and the PMP CSRs are stored as raw values
-- (legalised on write).  mvendorid, marchid, mimpid, mconfigptr and the
-- hardware performance-monitoring CSRs are constant zero, and mcycle and
-- minstret are c_cycles and c_instret.

record MachineCSR
{ misa          :: misa         -- information registers
  mhartid       :: regType

  mstatus       :: mstatus      -- trap setup
  medeleg       :: regType
  mideleg       :: regType
  mie           :: mie
  mtvec         :: regType
  mcounteren    :: regType
  menvcfg       :: regType

  mcountinhibit :: regType      -- counter setup

  mscratch      :: regType      -- trap handling
  mepc          :: regType
  mcause        :: mcause
  mtval         :: regType
  mip           :: mip

  pmpcfg0       :: regType      -- physical memory protection
  pmpcfg2       :: regType
  pmpaddr0      :: regType
  pmpaddr1      :: regType
  pmpaddr2      :: regType
  pmpaddr3      :: regType
  pmpaddr4      :: regType
  pmpaddr5      :: regType
  pmpaddr6      :: regType
  pmpaddr7      :: regType
  pmpaddr8      :: regType
  pmpaddr9      :: regType
  pmpaddr10     :: regType
  pmpaddr11     :: regType
  pmpaddr12     :: regType
  pmpaddr13     :: regType
  pmpaddr14     :: regType
  pmpaddr15     :: regType
}

-- Supervisor-Level CSRs (P §12.1).  sstatus, sie and sip are views of
-- mstatus, mie and mip.

record SupervisorCSR
{ stvec         :: regType      -- trap setup
  scounteren    :: regType
  senvcfg       :: regType

  sscratch      :: regType      -- trap handling
  sepc          :: regType
  scause        :: mcause
  stval         :: regType

  satp          :: regType      -- address translation and protection
}

-- User-Level CSRs

-- floating point control and status

register FPCSR :: word          -- 32-bit control register
{ 7-5 : FRM         -- dynamic rounding mode
                    -- exception flags
,   4 : NV          --     invalid operation
,   3 : DZ          --     divide by zero
,   2 : OF          --     overflow
,   1 : UF          --     underflow
,   0 : NX          --     inexact
}

record UserCSR
{ fpcsr         :: FPCSR
}

-- Write legalisation (P §2.3 p.24-25): a write of a WARL field never
-- raises an exception, and stores a legal value.  The PMP address
-- registers, mie, mip and the views are legalised in CSRMap.

-- misa (P §3.1.1 p.27-29)

regType MISA_RESET = 0x800000000014112D -- MXL = 2; A C D F I M S U (P §3.4 p.63)

-- Only C is writable ([D14]).  "If an instruction that would write misa
-- increases IALIGN, and the subsequent instruction's address is not
-- IALIGN-bit aligned, the write to misa is suppressed" (p.29): clearing C
-- is ignored when bit 1 of the next pc is set.  pc is the address of the
-- CSR instruction, which is 32 bits long, so (pc + 4)<1> = pc<1>.
misa legalize_misa(v::regType, m::misa, pc::regType) =
    if not v<2> and m.C and pc<1> then m
    else { var n = m
         ; n.C <- v<2>
         ; n
         }

-- mstatus (P §3.1.6 p.31-41)

regType MSTATUS_WMASK = 0x7E79AA           -- the fields of register mstatus
regType MSTATUS_CONST = 0xA00000000        -- UXL = SXL = 2 (P §3.1.6.3 p.34)
regType MSTATUS_SD    = 0x8000000000000000

-- An explicit write.  Read-only and WPRI fields are dropped (P §2.3.1
-- p.24).  MPP is WARL and holds U, S or M (P §3.1.6.2 p.33); the reserved
-- 10 is stored as U ([D15]).
mstatus legalize_mstatus(v::regType) =
{ var m = mstatus(v && MSTATUS_WMASK)
; when m.MPP == 2 do m.MPP <- 0
; m
}

-- The value read.  XS and VS are read-only zero, so SD is set iff FS is
-- Dirty (P §3.1.6.7 p.40).
regType read_mstatus(m::mstatus) =
    (&m && MSTATUS_WMASK) || MSTATUS_CONST ||
    (if m.FS == ext_status(Dirty) then MSTATUS_SD else 0)

-- sstatus is a view of mstatus (P §12.1.1 p.113-114): its fields are the
-- homonymous fields of mstatus.  Of these, SIE SPIE SPP FS SUM MXR are
-- writable here.  SUM is writable because satp.MODE is not read-only zero
-- (P §3.1.6.4 p.35, §12.1.1.2 p.114, [S19]).

regType SSTATUS_MASK = 0x80000003018DE762  -- SD UXL SDT SPELP MXR SUM XS FS
                                           -- VS SPP UBE SPIE SIE

regType read_sstatus(m::mstatus) = read_mstatus(m) && SSTATUS_MASK

mstatus legalize_sstatus(v::regType, m::mstatus) =
    legalize_mstatus((&m && ~SSTATUS_MASK) || (v && SSTATUS_MASK))

-- mtvec and stvec (P §3.1.7 p.41-42, §12.1.2 p.116): MODE is Direct (0) or
-- Vectored (1), with a 4-byte aligned BASE in both.  A write of a reserved
-- MODE keeps the old MODE and still writes BASE ([D39]).
regType legalize_xtvec(v::regType, old::regType) =
    if v<1> then v<63:2> : old<1:0> else v

-- mepc and sepc (P §3.1.14 p.48, §12.1.7 p.119): bit 0 is always zero.
-- Bit 1 stays writable when IALIGN = 32 but is then masked when read, by
-- read_xepc ([D44]).
regType legalize_xepc(v::regType) = v && ~0x1

-- mcause and scause (P §3.1.15 p.49-50, §12.1.8 p.120): the exception
-- code is WLRL.  A write of a code this hart does not have leaves the
-- register unchanged; the legal codes are those of sail-riscv's
-- legalize_cause ([D33]).  scause holds any code from 0 to 31.
mcause legalize_mcause(v::regType, old::mcause) =
{ c = v<62:0>
; if (if v<63> then c == 1 or c == 3 or c == 5 or c == 7 or c == 9 or c == 11
      else (c <+ 16 and c != 10 and c != 14) or c == 19)
  then mcause(v) else old
}

mcause legalize_scause(v::regType, old::mcause) =
    if v<62:0> <=+ 31 then mcause(v) else legalize_mcause(v, old)

-- satp (P §12.1.11 p.124-126, Figure 64 p.125): MODE is Bare, Sv39, Sv48
-- or Sv57 (Table 40 p.126, [S7]), and if satp "is written with an
-- unsupported MODE, the entire write has no effect; no fields in satp are
-- modified" (p.125).  All 16 ASID bits and all 44 PPN bits are writable
-- ([S8], [S9]).  A write of Bare with a nonzero ASID or PPN, whose effect
-- is UNSPECIFIED (p.125), stores the value as written ([S10]).  MODE is
-- compared under a mask rather than extracted, so that HolBA's lifter
-- can translate the legaliser.
regType legalize_satp(v::regType, old::regType) =
{ m = v && 0xF000000000000000
; if m == 0 or m == 0x8000000000000000 or m == 0x9000000000000000
     or m == 0xA000000000000000
  then v else old
}

-- PMP configuration (P §3.7.1 Figures 31 and 34 p.71-72): one byte per
-- entry; pmpcfg0 holds entries 0-7 and pmpcfg2 entries 8-15.
register pmpcfg :: bits(8)
{     7 : L         -- locked
,   4-3 : A         -- 0 OFF, 1 TOR, 2 NA4, 3 NAPOT
,     2 : X
,     1 : W
,     0 : R
}

-- A locked entry ignores writes until reset (P §3.7.1.2 p.73).  Bits 6:5
-- are read-only zero.  R = 0 with W = 1 is reserved and is stored as
-- R = W = X = 0 ([D49]).  With grain G = 0 every A mode can be selected.
pmpcfg legalize_pmpcfg_byte(b::bits(8), old::pmpcfg) =
    if old.L then old
    else { var n = pmpcfg(b && 0x9F)
         ; when not n.R and n.W do { n.W <- false; n.X <- false }
         ; n
         }

-- The 8 entries of pmpcfg0 or pmpcfg2 are legalised separately.
regType legalize_pmpcfg(v::regType, old::regType) =
    &legalize_pmpcfg_byte(v<63:56>, pmpcfg(old<63:56>)) :
    &legalize_pmpcfg_byte(v<55:48>, pmpcfg(old<55:48>)) :
    &legalize_pmpcfg_byte(v<47:40>, pmpcfg(old<47:40>)) :
    &legalize_pmpcfg_byte(v<39:32>, pmpcfg(old<39:32>)) :
    &legalize_pmpcfg_byte(v<31:24>, pmpcfg(old<31:24>)) :
    &legalize_pmpcfg_byte(v<23:16>, pmpcfg(old<23:16>)) :
    &legalize_pmpcfg_byte(v<15:8>,  pmpcfg(old<15:8>))  :
    &legalize_pmpcfg_byte(v<7:0>,   pmpcfg(old<7:0>))

---------------------------------------------------------------------------
-- Instruction fetch control
---------------------------------------------------------------------------

record SynchronousTrap
{ trap            :: ExceptionType
  tval            :: regType        -- for mtval or stval (P §3.1.16 p.52-53)
}

construct TransferControl
{ Trap            :: SynchronousTrap
, BranchTo        :: regType
, Mret
, Sret
}

---------------------------------------------------------------------------
-- Register state space
---------------------------------------------------------------------------

-- Each register state is local to a core.

type RegFile    = reg  -> regType

declare
{ c_instret     :: id -> regType                -- minstret
  c_cycles      :: id -> regType                -- mcycle
  c_minstret_written :: id -> bool              -- minstret written in this step

  c_gpr         :: id -> RegFile                -- general purpose registers
  c_fpr         :: id -> RegFile                -- floating-point registers

  c_PC          :: id -> regType                -- program counter
  c_Skip        :: id -> regType                -- bytes to next instruction

  c_privilege   :: id -> priv_level             -- current privilege level

  c_UCSR        :: id -> UserCSR                -- user-level CSRs
  c_SCSR        :: id -> SupervisorCSR          -- supervisor-level CSRs
  c_MCSR        :: id -> MachineCSR             -- machine-level CSRs

  c_extMEIP     :: id -> bool                   -- platform interrupt lines:
  c_extSEIP     :: id -> bool                   --   MEIP and external SEIP

  -- interpreter execution context
  c_NextFetch   :: id -> TransferControl option
  c_ReserveLoad :: id -> pAddr option           -- load reservation for LR/SC
  c_ExitCode    :: id -> regType                -- set by the emulator
}

-- Number of cores
declare totalCore :: nat

-- ID of the core executing current instruction
declare procID :: id

unit scheduleCore(id :: nat) =
    when id < totalCore
    do procID <- [id]

-- The following components provide read/write access to state of the
-- core whose id equals procID.  For example, writing "gpr(r)" refers
-- general purpose register "r" in the core whose id equals procID.

component gpr(n::reg) :: regType
{ value        = { m = c_gpr(procID); m(n) }
  assign value = { var m = c_gpr(procID)
                 ; m(n) <- value
                 ; c_gpr(procID) <- m
                 }
}

-- Writing fcsr makes the floating-point state Dirty (P §3.1.6.7 Table 14).
component fcsr :: FPCSR
{ value        = c_UCSR(procID).fpcsr
  assign value = { c_UCSR(procID).fpcsr      <- value
                 ; c_MCSR(procID).mstatus.FS <- ext_status(Dirty)
                 }
}

component fpr(n::reg) :: regType
{ value        = { m = c_fpr(procID); m(n) }
  assign value = { var m = c_fpr(procID)
                 ; m(n) <- value
                 ; c_fpr(procID) <- m
                 }
}

component PC :: regType
{ value        = c_PC(procID)
  assign value = c_PC(procID) <- value
}

component Skip :: regType
{ value        = c_Skip(procID)
  assign value = c_Skip(procID) <- value
}

component UCSR :: UserCSR
{ value        = c_UCSR(procID)
  assign value = c_UCSR(procID) <- value
}

component SCSR :: SupervisorCSR
{ value        = c_SCSR(procID)
  assign value = c_SCSR(procID) <- value
}

component MCSR :: MachineCSR
{ value        = c_MCSR(procID)
  assign value = c_MCSR(procID) <- value
}

component NextFetch :: TransferControl option
{ value        = c_NextFetch(procID)
  assign value = c_NextFetch(procID) <- value
}

component ReserveLoad :: pAddr option
{ value        = c_ReserveLoad(procID)
  assign value = c_ReserveLoad(procID) <- value
}

component ExitCode :: regType
{ value        = c_ExitCode(procID)
  assign value = c_ExitCode(procID) <- value
}

-- physical memory

{- Original memory replaced by byte memory when exporting to HOL
declare MEM :: pAddrIdx -> regType -- raw memory, laid out in blocks
                                   -- of (|pAddr|-|pAddrIdx|) bits

unit initMem(val::regType) =
    MEM <- InitMap(val)
-}

declare MEM8 :: pAddr -> byte

component MEM (a::pAddrIdx) :: regType
{
  value =
    { b = [a] << 3
    ; ( MEM8 (b + 7) : MEM8 (b + 6) : MEM8 (b + 5) : MEM8 (b + 4) :
        MEM8 (b + 3) : MEM8 (b + 2) : MEM8 (b + 1) : MEM8 (b) )
    }
  assign val =
    { b = [a] << 3
    ; MEM8 (b + 7) <- val<63:56>
    ; MEM8 (b + 6) <- val<55:48>
    ; MEM8 (b + 5) <- val<47:40>
    ; MEM8 (b + 4) <- val<39:32>
    ; MEM8 (b + 3) <- val<31:24>
    ; MEM8 (b + 2) <- val<23:16>
    ; MEM8 (b + 1) <- val<15:8 >
    ; MEM8 (b    ) <- val<7 :0 >
    }
}

-- The core-local interruptor (CLINT) of sail-riscv's platform.  mtime,
-- mtimecmp and msip are memory-mapped registers (P §3.2.1 p.59, §3.1.9
-- p.44), so here they are words of memory ([D67]).  Nothing in the model
-- advances mtime: the emulator does that after every step ([D63]).

pAddr CLINT_BASE = 0x2000000

-- shared by all harts
regType mtime() = MEM((CLINT_BASE + 0xBFF8)<63:3>)

regType mtimecmp(h::id) = MEM((CLINT_BASE + 0x4000 + 8 * ZeroExtend(h))<63:3>)

-- bit 0 of the 32-bit msip register of hart h
bool msip(h::id) = MEM8(CLINT_BASE + 4 * ZeroExtend(h))<0>

-- machine state utilities

-- misa.MXL is read-only 2 ([D4]): initIdent accepts only RV64I, and
-- legalize_misa changes only C.  So this is false in every reachable
-- state, and the RV32 cases of the instructions are dead code.  They do not
-- make a complete RV32 (for one, addresses and the pc are not truncated
-- to 32 bits, and AMO*.D are not illegal): RV32 is not supported.
bool in32BitMode() =
    MCSR.misa.MXL == 1

bool haveRVC() =
    MCSR.misa.C

-- The F and D instructions, and every access to fflags, frm and fcsr, are
-- illegal while mstatus.FS is Off (P §3.1.6.7 p.38).  misa.F and misa.D
-- are read-only 1.
bool fpEnabled() =
    MCSR.mstatus.FS != ext_status(Off)

-- mepc and sepc as read, also by MRET and SRET: bit 1 reads as zero when
-- IALIGN = 32 (P §3.1.14 p.48, [D44]).
regType read_xepc(epc::regType) =
    if haveRVC() then epc else epc && ~0x3

-- The current privilege level (P §1.2 p.11) is not held in a CSR.  It is
-- written only by setPrivilege, so the reserved encoding 10 never occurs.
Privilege curPrivilege() =
    privilege(c_privilege(procID))

unit setPrivilege(p::Privilege) =
    c_privilege(procID) <- privLevel(p)

-- Explicit loads and stores use the privilege in mstatus.MPP while
-- mstatus.MPRV is set (P §3.1.6.4 p.35, [D22]); instruction fetches do
-- not.  Only an M-mode write of mstatus sets MPRV, and an xRET that leaves
-- M-mode clears it, so below M-mode it is 0 in every reachable state.
Privilege effectivePrivilege() =
    if MCSR.mstatus.MPRV then privilege(MCSR.mstatus.MPP) else curPrivilege()

-- mip as read (P §3.1.9 p.43-45): MSIP and MTIP come from the CLINT
-- (MTIP is pending while mtime >= mtimecmp, unsigned, P §3.2.1 p.59), MEIP
-- from the platform, and SEIP is the stored bit or the platform's line.
regType read_mip() =
{ var ip = mip(MCSR.&mip && 0x222)
; ip.MSIP <- msip(procID)
; ip.MTIP <- mtimecmp(procID) <=+ mtime()
; ip.SEIP <- MCSR.mip.SEIP or c_extSEIP(procID)
; ip.MEIP <- c_extMEIP(procID)
; &ip
}

-- cycle, time and instret are readable below M-mode only when enabled in
-- mcounteren, and in U-mode also in scounteren (P §3.1.11 p.47, §12.1.5
-- p.119).  hpmcounter3-31 do not exist ([D25]), so i is 0, 1 or 2.
bool counterReadAllowed(csr::creg, p::Privilege) =
{ i = [csr<4:0>]::nat
; match p
  { case Machine    => true
    case Supervisor => MCSR.mcounteren<i>
    case User       => MCSR.mcounteren<i> and SCSR.scounteren<i>
  }
}

-- PMP entry i (P §3.7.1 p.70-73)

pmpcfg pmpcfg_ent(i::bits(4)) =
{ r = if i<3> then MCSR.pmpcfg2 else MCSR.pmpcfg0
; pmpcfg((r >>+ (8 * ([i<2:0>]::nat)))<7:0>)
}

regType pmpaddr(i::bits(4)) =
    match i
    { case 0  => MCSR.pmpaddr0
      case 1  => MCSR.pmpaddr1
      case 2  => MCSR.pmpaddr2
      case 3  => MCSR.pmpaddr3
      case 4  => MCSR.pmpaddr4
      case 5  => MCSR.pmpaddr5
      case 6  => MCSR.pmpaddr6
      case 7  => MCSR.pmpaddr7
      case 8  => MCSR.pmpaddr8
      case 9  => MCSR.pmpaddr9
      case 10 => MCSR.pmpaddr10
      case 11 => MCSR.pmpaddr11
      case 12 => MCSR.pmpaddr12
      case 13 => MCSR.pmpaddr13
      case 14 => MCSR.pmpaddr14
      case 15 => MCSR.pmpaddr15
    }

-- pmpaddr<i> holds bits 55:2 of a physical address, so bits 63:54 are
-- read-only zero (Figure 33 p.71).  A write is ignored while entry i is
-- locked, or while entry i+1 is locked and TOR (P §3.7.1.2 p.73).
unit write_pmpaddr(i::bits(4), v::regType) =
    when not (pmpcfg_ent(i).L or
              (i != 15 and pmpcfg_ent(i + 1).L and pmpcfg_ent(i + 1).A == 1))
    do { a = v && 0x3FFFFFFFFFFFFF
       ; match i
         { case 0  => MCSR.pmpaddr0  <- a
           case 1  => MCSR.pmpaddr1  <- a
           case 2  => MCSR.pmpaddr2  <- a
           case 3  => MCSR.pmpaddr3  <- a
           case 4  => MCSR.pmpaddr4  <- a
           case 5  => MCSR.pmpaddr5  <- a
           case 6  => MCSR.pmpaddr6  <- a
           case 7  => MCSR.pmpaddr7  <- a
           case 8  => MCSR.pmpaddr8  <- a
           case 9  => MCSR.pmpaddr9  <- a
           case 10 => MCSR.pmpaddr10 <- a
           case 11 => MCSR.pmpaddr11 <- a
           case 12 => MCSR.pmpaddr12 <- a
           case 13 => MCSR.pmpaddr13 <- a
           case 14 => MCSR.pmpaddr14 <- a
           case 15 => MCSR.pmpaddr15 <- a
         }
       }

---------------------------------------------------------------------------
-- Floating Point
---------------------------------------------------------------------------


-- Rounding

construct Rounding
{ RNE, RTZ, RDN, RUP, RMM, RDYN }

-- instruction rounding mode
Rounding option rnd_mode_static(rnd::fprnd) =
    match rnd
    { case 0          => Some(RNE)
      case 1          => Some(RTZ)
      case 2          => Some(RDN)
      case 3          => Some(RUP)
      case 4          => Some(RMM)
      case 7          => Some(RDYN)     -- from rounding mode register
      case _          => None
    }

-- dynamic rounding mode
Rounding option rnd_mode_dynamic(rnd::fprnd) =
    match rnd
    { case 0          => Some(RNE)
      case 1          => Some(RTZ)
      case 2          => Some(RDN)
      case 3          => Some(RUP)
      case 4          => Some(RMM)
      case _          => None
    }

-- currently implemented rounding modes
ieee_rounding option l3round(rnd::Rounding) =
    match rnd
    { case RNE        => Some(roundTiesToEven)
      case RTZ        => Some(roundTowardZero)
      case RDN        => Some(roundTowardNegative)
      case RUP        => Some(roundTowardPositive)
      case RMM        => None  -- roundTiesToMaxMagnitude is neither in L3 nor
                               -- in HOL's binary_ieee (see validRounding)
      case RDYN       => None  -- invalid
    }

-- composed rounding mode
ieee_rounding option round(rnd::fprnd) =
    match rnd_mode_static(rnd)
    { case Some(RDYN) => match rnd_mode_dynamic(fcsr.FRM)
                         { case Some(frm) => l3round(frm)
                           case None      => None
                         }
      case Some(frm)  => l3round(frm)
      case None       => None
    }

-- rm of an instruction whose result is exact (FCVT.D.S, FCVT.D.W, FCVT.D.WU):
-- it is decoded as usual, so RMM is legal, but it is never used to round
-- (ISA manual 6.1.2)
bool validRounding(rnd::fprnd) =
    match rnd_mode_static(rnd)
    { case Some(RDYN) => IsSome(rnd_mode_dynamic(fcsr.FRM))
      case Some(_)    => true
      case None       => false
    }

-- NaNs

bits(32) RV32_CanonicalNan = 0x7fc00000
bits(64) RV64_CanonicalNan = 0x7ff8000000000000

-- a NaN result of an arithmetic or conversion instruction is the canonical
-- NaN (ISA manual 6.1.3 and 6.2)
bits(32) canonS(x::bits(32)) = if FP32_IsNan(x) then RV32_CanonicalNan else x
bits(64) canonD(x::bits(64)) = if FP64_IsNan(x) then RV64_CanonicalNan else x

-- Classification

bool FP32_IsSignalingNan(x::bits(32)) =
    (x<30:23> == 0xff`8)   and x<22> == false and (x<21:0> != 0x0`22)

bool FP64_IsSignalingNan(x::bits(64)) =
    (x<62:52> == 0x7ff`11) and x<51> == false and (x<50:0> != 0x0`51)

bool FP32_Sign(x::bits(32)) = x<31>
bool FP64_Sign(x::bits(64)) = x<63>

-- multiplicands of an FMA that must raise NV even when the addend is a quiet
-- NaN (ISA manual 6.1.6); IEEE 754-2008 leaves that case open, and neither
-- export's MulAdd raises it
bool FP32_InfTimesZero(a::bits(32), b::bits(32)) =
    (FP32_IsZero(a) and (b == FP32_PosInf or b == FP32_NegInf)) or
    (FP32_IsZero(b) and (a == FP32_PosInf or a == FP32_NegInf))

bool FP64_InfTimesZero(a::bits(64), b::bits(64)) =
    (FP64_IsZero(a) and (b == FP64_PosInf or b == FP64_NegInf)) or
    (FP64_IsZero(b) and (a == FP64_PosInf or a == FP64_NegInf))

-- setting exception flags (fcsr bits 4-0: NV DZ OF UF NX, ISA manual 6.1.2)

unit setFP_Invalid() =
    fcsr.NV <- true

unit setFP_DivZero() =
    fcsr.DZ <- true

unit setFP_Overflow() =
    fcsr.OF <- true

unit setFP_Underflow() =
    fcsr.UF <- true

unit setFP_Inexact() =
    fcsr.NX <- true

-- accrue the exception flags returned by an IEEE operation (ISA manual 6.1.2)
unit accrueFlags(f::ieee_flags) =
{ when f.InvalidOp    do setFP_Invalid()
; when f.DivideByZero do setFP_DivZero()
; when f.Overflow     do setFP_Overflow()
; when f.Underflow    do setFP_Underflow()
; when f.Precision    do setFP_Inexact()
}

---------------------------------------------------------------------------
-- CSR Register address map
---------------------------------------------------------------------------

-- CSR access control (P §2.1 p.13): csr<11:10> = 11 is read-only and
-- csr<9:8> is the lowest privilege level that can access the CSR.

type csrRW    = bits(2)         -- read/write check
type csrPR    = bits(2)         -- privilege check

csrRW csrRW(csr::creg)  = csr<11:10>
csrPR csrPR(csr::creg)  = csr<9:8>

-- this only checks register-level access.  some registers have
-- additional bit-specific read/write controls.
bool check_CSR_access(rw::csrRW, pr::csrPR, p::Privilege, a::accessType) =
    (a == Read or rw != 0b11) and (privLevel(p) >=+ pr)

-- The CSRs of this hart (P §2.2 Tables 3-8 p.14-23).  Every other address
-- is reserved, and accessing it is an illegal instruction (P §2.1 p.13,
-- [D24]).  This includes the RV32-only halves, hpmcounter3-31 ([D25]),
-- the odd pmpcfg registers and those of PMP entries 16-63.
bool is_CSR_defined(csr::creg) =
    -- unprivileged: floating point, counters and timer
    (csr >=+ 0x001 and csr <=+ 0x003)
 or (csr >=+ 0xC00 and csr <=+ 0xC02)

    -- supervisor-level
 or  csr == 0x100 or (csr >=+ 0x104 and csr <=+ 0x106) or csr == 0x10A
 or (csr >=+ 0x140 and csr <=+ 0x144) or csr == 0x180

    -- machine-level
 or (csr >=+ 0xF11 and csr <=+ 0xF15)
 or (csr >=+ 0x300 and csr <=+ 0x306) or csr == 0x30A
 or  csr == 0x320 or (csr >=+ 0x323 and csr <=+ 0x33F)
 or (csr >=+ 0x340 and csr <=+ 0x344)
 or  csr == 0x3A0 or csr == 0x3A2 or (csr >=+ 0x3B0 and csr <=+ 0x3BF)
 or  csr == 0xB00 or (csr >=+ 0xB02 and csr <=+ 0xB1F)

-- mhpmevent3-31 and mhpmcounter3-31: read-only zero, writes are ignored
-- (P §3.1.10 p.46, [D26])
bool is_mhpm_CSR(csr::creg) =
    (csr >=+ 0x323 and csr <=+ 0x33F) or (csr >=+ 0xB03 and csr <=+ 0xB1F)

-- Further conditions on CSR access ([D9])
bool check_CSR_conditions(csr::creg, p::Privilege) =
    -- fflags, frm, fcsr need mstatus.FS != Off (P §3.1.6.7 p.38)
    if csr >=+ 0x001 and csr <=+ 0x003 then fpEnabled()
    -- cycle, time, instret
    else if csr >=+ 0xC00 and csr <=+ 0xC02 then counterReadAllowed(csr, p)
    -- satp is illegal in S-mode while mstatus.TVM is set (P §3.1.6.6 p.37)
    else if csr == 0x180 then not (p == Supervisor and MCSR.mstatus.TVM)
    else true

-- The read values and write legalisation of the CSRs (P §3.1, §3.7.1,
-- §12.1; U §4.3, §6.1.2).  Writes never trap: those that checkCSROp
-- rejects do not get here.
component CSRMap(csr::creg) :: regType
{
  value =
      match csr
      { -- floating-point control and status (U §6.1.2 p.130-131)
        case 0x001  => ZeroExtend(c_UCSR(procID).&fpcsr<4:0>)
        case 0x002  => ZeroExtend(c_UCSR(procID).fpcsr.FRM)
        case 0x003  => ZeroExtend(c_UCSR(procID).&fpcsr<7:0>)

        -- counters and timer: mcycle, mtime, minstret (U §4.3 p.65-66)
        case 0xC00  => c_cycles(procID)
        case 0xC01  => mtime()
        case 0xC02  => c_instret(procID)

        -- supervisor trap setup
        case 0x100  => read_sstatus(c_MCSR(procID).mstatus)
        case 0x104  => c_MCSR(procID).&mie && c_MCSR(procID).mideleg
        case 0x105  => c_SCSR(procID).stvec
        case 0x106  => c_SCSR(procID).scounteren
        case 0x10A  => c_SCSR(procID).senvcfg

        -- supervisor trap handling
        case 0x140  => c_SCSR(procID).sscratch
        case 0x141  => read_xepc(c_SCSR(procID).sepc)
        case 0x142  => c_SCSR(procID).&scause
        case 0x143  => c_SCSR(procID).stval
        case 0x144  => read_mip() && c_MCSR(procID).mideleg

        -- supervisor protection and translation
        case 0x180  => c_SCSR(procID).satp

        -- machine information registers: mvendorid, marchid, mimpid and
        -- mconfigptr are zero (P §3.1.2-3.1.4 p.29-31, §3.1.17 p.53, [D31])
        case 0xF11  => 0
        case 0xF12  => 0
        case 0xF13  => 0
        case 0xF14  => c_MCSR(procID).mhartid
        case 0xF15  => 0

        -- machine trap setup
        case 0x300  => read_mstatus(c_MCSR(procID).mstatus)
        case 0x301  => c_MCSR(procID).&misa
        case 0x302  => c_MCSR(procID).medeleg
        case 0x303  => c_MCSR(procID).mideleg
        case 0x304  => c_MCSR(procID).&mie
        case 0x305  => c_MCSR(procID).mtvec
        case 0x306  => c_MCSR(procID).mcounteren
        case 0x30A  => c_MCSR(procID).menvcfg

        -- machine counter setup
        case 0x320  => c_MCSR(procID).mcountinhibit

        -- machine trap handling
        case 0x340  => c_MCSR(procID).mscratch
        case 0x341  => read_xepc(c_MCSR(procID).mepc)
        case 0x342  => c_MCSR(procID).&mcause
        case 0x343  => c_MCSR(procID).mtval
        case 0x344  => read_mip()

        -- machine memory protection
        case 0x3A0  => c_MCSR(procID).pmpcfg0
        case 0x3A2  => c_MCSR(procID).pmpcfg2
        case 0x3B0  => c_MCSR(procID).pmpaddr0
        case 0x3B1  => c_MCSR(procID).pmpaddr1
        case 0x3B2  => c_MCSR(procID).pmpaddr2
        case 0x3B3  => c_MCSR(procID).pmpaddr3
        case 0x3B4  => c_MCSR(procID).pmpaddr4
        case 0x3B5  => c_MCSR(procID).pmpaddr5
        case 0x3B6  => c_MCSR(procID).pmpaddr6
        case 0x3B7  => c_MCSR(procID).pmpaddr7
        case 0x3B8  => c_MCSR(procID).pmpaddr8
        case 0x3B9  => c_MCSR(procID).pmpaddr9
        case 0x3BA  => c_MCSR(procID).pmpaddr10
        case 0x3BB  => c_MCSR(procID).pmpaddr11
        case 0x3BC  => c_MCSR(procID).pmpaddr12
        case 0x3BD  => c_MCSR(procID).pmpaddr13
        case 0x3BE  => c_MCSR(procID).pmpaddr14
        case 0x3BF  => c_MCSR(procID).pmpaddr15

        -- machine counters
        case 0xB00  => c_cycles(procID)
        case 0xB02  => c_instret(procID)

        case _      => if is_mhpm_CSR(csr) then 0
                       else #UNDEFINED("unexpected CSR read at " : [csr])
      }

  assign value =
      match csr
      { -- floating-point control and status (U §6.1.2 p.130-131); a write
        -- makes the floating-point state Dirty (P §3.1.6.7 p.39)
        case 0x001  => { c_UCSR(procID).&fpcsr<4:0>     <- value<4:0>
                       ; c_MCSR(procID).mstatus.FS      <- ext_status(Dirty)
                       }
        case 0x002  => { c_UCSR(procID).fpcsr.FRM       <- value<2:0>
                       ; c_MCSR(procID).mstatus.FS      <- ext_status(Dirty)
                       }
        case 0x003  => { c_UCSR(procID).&fpcsr          <- ZeroExtend(value<7:0>)
                       ; c_MCSR(procID).mstatus.FS      <- ext_status(Dirty)
                       }

        -- supervisor trap setup; sie is mie restricted to the interrupts
        -- delegated in mideleg (P §12.1.3 p.117)
        case 0x100  => c_MCSR(procID).mstatus           <- legalize_sstatus(value, c_MCSR(procID).mstatus)
        case 0x104  => c_MCSR(procID).mie               <- mie((c_MCSR(procID).&mie && ~c_MCSR(procID).mideleg)
                                                               || (value && c_MCSR(procID).mideleg))
        case 0x105  => c_SCSR(procID).stvec             <- legalize_xtvec(value, c_SCSR(procID).stvec)
        -- CY, TM, IR (P §12.1.5 p.119, [D27])
        case 0x106  => c_SCSR(procID).scounteren        <- value && 0x7
        -- only FIOM (P §12.1.10 p.122, [D29])
        case 0x10A  => c_SCSR(procID).senvcfg           <- value && 0x1

        -- supervisor trap handling; of sip only SSIP is writable, and only
        -- when delegated (P §12.1.3 p.117-118)
        case 0x140  => c_SCSR(procID).sscratch          <- value
        case 0x141  => c_SCSR(procID).sepc              <- legalize_xepc(value)
        case 0x142  => c_SCSR(procID).scause            <- legalize_scause(value, c_SCSR(procID).scause)
        case 0x143  => c_SCSR(procID).stval             <- value
        case 0x144  => when c_MCSR(procID).mideleg<1>
                       do c_MCSR(procID).mip.SSIP       <- value<1>

        -- supervisor protection and translation
        case 0x180  => c_SCSR(procID).satp              <- legalize_satp(value, c_SCSR(procID).satp)

        -- machine trap setup.  medeleg: exceptions 0-9, 12, 13 and 15 can
        -- be delegated ([D40]; 11 and 16 are read-only zero, P §3.1.8 p.43);
        -- mideleg: SSI, STI, SEI ([D41]); mie: the six interrupts.
        case 0x300  => c_MCSR(procID).mstatus           <- legalize_mstatus(value)
        case 0x301  => c_MCSR(procID).misa              <- legalize_misa(value, c_MCSR(procID).misa, c_PC(procID))
        case 0x302  => c_MCSR(procID).medeleg           <- value && 0xB3FF
        case 0x303  => c_MCSR(procID).mideleg           <- value && 0x222
        case 0x304  => c_MCSR(procID).mie               <- mie(value && 0xAAA)
        case 0x305  => c_MCSR(procID).mtvec             <- legalize_xtvec(value, c_MCSR(procID).mtvec)
        -- CY, TM, IR (P §3.1.11 p.46-47, [D27])
        case 0x306  => c_MCSR(procID).mcounteren        <- value && 0x7
        -- only FIOM (P §3.1.18 p.54, [D29])
        case 0x30A  => c_MCSR(procID).menvcfg           <- value && 0x1

        -- machine counter setup: CY and IR (P §3.1.12 p.47, [D28])
        case 0x320  => c_MCSR(procID).mcountinhibit     <- value && 0x5

        -- machine trap handling; of mip only SSIP, STIP and SEIP are
        -- writable (P §3.1.9 p.44-45)
        case 0x340  => c_MCSR(procID).mscratch          <- value
        case 0x341  => c_MCSR(procID).mepc              <- legalize_xepc(value)
        case 0x342  => c_MCSR(procID).mcause            <- legalize_mcause(value, c_MCSR(procID).mcause)
        case 0x343  => c_MCSR(procID).mtval             <- value
        case 0x344  => c_MCSR(procID).mip               <- mip(value && 0x222)

        -- machine memory protection
        case 0x3A0  => c_MCSR(procID).pmpcfg0           <- legalize_pmpcfg(value, c_MCSR(procID).pmpcfg0)
        case 0x3A2  => c_MCSR(procID).pmpcfg2           <- legalize_pmpcfg(value, c_MCSR(procID).pmpcfg2)
        case 0x3B0  => write_pmpaddr(0, value)
        case 0x3B1  => write_pmpaddr(1, value)
        case 0x3B2  => write_pmpaddr(2, value)
        case 0x3B3  => write_pmpaddr(3, value)
        case 0x3B4  => write_pmpaddr(4, value)
        case 0x3B5  => write_pmpaddr(5, value)
        case 0x3B6  => write_pmpaddr(6, value)
        case 0x3B7  => write_pmpaddr(7, value)
        case 0x3B8  => write_pmpaddr(8, value)
        case 0x3B9  => write_pmpaddr(9, value)
        case 0x3BA  => write_pmpaddr(10, value)
        case 0x3BB  => write_pmpaddr(11, value)
        case 0x3BC  => write_pmpaddr(12, value)
        case 0x3BD  => write_pmpaddr(13, value)
        case 0x3BE  => write_pmpaddr(14, value)
        case 0x3BF  => write_pmpaddr(15, value)

        -- machine counters
        -- a write of minstret is done instead of the increment for the
        -- writing instruction (U §4.2.1 p.64; incrInstret)
        case 0xB00  => c_cycles(procID)                 <- value
        case 0xB02  => { c_instret(procID)              <- value
                       ; c_minstret_written(procID)     <- true
                       }

        case _      => when not is_mhpm_CSR(csr)
                       do #INTERNAL_ERROR("unexpected CSR write to " : [csr])
      }
}

string csrName(csr::creg) =
    match csr
    { -- floating-point control and status
      case 0x001  => "fflags"
      case 0x002  => "frm"
      case 0x003  => "fcsr"

      -- counters and timer
      case 0xC00  => "cycle"
      case 0xC01  => "time"
      case 0xC02  => "instret"

      -- supervisor trap setup
      case 0x100  => "sstatus"
      case 0x104  => "sie"
      case 0x105  => "stvec"
      case 0x106  => "scounteren"
      case 0x10A  => "senvcfg"

      -- supervisor trap handling
      case 0x140  => "sscratch"
      case 0x141  => "sepc"
      case 0x142  => "scause"
      case 0x143  => "stval"
      case 0x144  => "sip"

      -- supervisor protection and translation
      case 0x180  => "satp"

      -- machine information registers
      case 0xF11  => "mvendorid"
      case 0xF12  => "marchid"
      case 0xF13  => "mimpid"
      case 0xF14  => "mhartid"
      case 0xF15  => "mconfigptr"

      -- machine trap setup
      case 0x300  => "mstatus"
      case 0x301  => "misa"
      case 0x302  => "medeleg"
      case 0x303  => "mideleg"
      case 0x304  => "mie"
      case 0x305  => "mtvec"
      case 0x306  => "mcounteren"
      case 0x30A  => "menvcfg"

      -- machine counter setup
      case 0x320  => "mcountinhibit"

      -- machine trap handling
      case 0x340  => "mscratch"
      case 0x341  => "mepc"
      case 0x342  => "mcause"
      case 0x343  => "mtval"
      case 0x344  => "mip"

      -- machine memory protection
      case 0x3A0  => "pmpcfg0"
      case 0x3A2  => "pmpcfg2"

      -- machine counters
      case 0xB00  => "mcycle"
      case 0xB02  => "minstret"

      -- numbered CSRs, and the hexadecimal address of any other
      case _      =>
        if csr >=+ 0x3B0 and csr <=+ 0x3BF then "pmpaddr" : [[csr<3:0>]::nat]
        else if csr >=+ 0x323 and csr <=+ 0x33F then "mhpmevent" : [[csr<4:0>]::nat]
        else if csr >=+ 0xB03 and csr <=+ 0xB1F then "mhpmcounter" : [[csr<4:0>]::nat]
        else "0x" : PadLeft(#"0", 3, [csr])
    }

---------------------------------------------------------------------------
-- Tandem verification
---------------------------------------------------------------------------
-- This describes the state update due to every retired instruction,
-- which can be verified against an external oracle.  Currently, the
-- Cissr tool from Bluespec fills the role, and the record below is
-- designed against its API.

record StateDelta
{ exc_taken     :: bool                 -- whether an exception (interrupt/trap) was taken
  fetch_exc     :: bool                 -- whether that exception occured on fetch
                                --   if so, the retired instruction (rinstr) is undefined
  pc            :: regType              -- PC of retired instruction
  rinstr        :: rawInstType          -- the retired instruction

  addr          :: regType option       -- address argument for instruction:
                                --   new control flow target for jump, exception branch, ERET
                                --   memory address for memory ops and AMOs
                                --   CSR register address for CSR instructions

  data1         :: regType option       -- data result for instruction:
                                --   new value for rd for ALU ops, LOAD, LOAD_FP, LR, SC, CSR ops
                                --   new csr_status for exceptions and ERET

  data2         :: regType option       -- data argument for instruction:
                                --   new csr_cause for exceptions
                                --   new memory value for STORE, STORE_FP, SC, AMOs
                                --   argument for CSR ops

  fp_data       :: fpval option         -- floating point value

  st_width      :: word option          -- width of store (optimization for sub-word store checks)
}

declare c_update :: id -> StateDelta

component Delta :: StateDelta
{ value        = c_update(procID)
  assign value = c_update(procID) <- value
}

inline unit setupDelta(pc::regType, instr::rawInstType) =
{ Delta.exc_taken <- false
; Delta.fetch_exc <- false
; Delta.pc        <- pc
; Delta.rinstr    <- instr
; Delta.addr      <- None
; Delta.data1     <- None
; Delta.data2     <- None
; Delta.fp_data   <- None
; Delta.st_width  <- None
}

-- A load or store is recorded with its physical address, as sail-riscv
-- logs it ([S30]).
inline unit recordLoad(addr::pAddr, val::regType) =
when not PROVER_EXPORT do
{ Delta.addr      <- Some(addr)
; Delta.data1     <- Some(val)
}

inline unit recordStore(addr::pAddr, val::regType, width::word) =
when not PROVER_EXPORT do
{ Delta.addr      <- Some(addr)
; Delta.data2     <- Some(val)
; Delta.st_width  <- Some(width)
}

inline unit recordException() =
when not PROVER_EXPORT do
{ Delta.exc_taken <- true }

inline unit recordFetchException(pc::regType) =
when not PROVER_EXPORT do
{ Delta.fetch_exc <- true
; Delta.pc        <- pc
}

---------------------------------------------------------------------------
-- Logging
---------------------------------------------------------------------------
string hex32(x::word)  = PadLeft(#"0", 8, [x])
string hex64(x::dword) = PadLeft(#"0", 16, [x])

string log_w_csr(csr::creg, data::regType) =
    "CSR (" : csrName(csr) : ") <- 0x" : hex64(data)

string reg(r::reg) =
{ if      r ==  0 then "$0"
  else if r ==  1 then "ra"
  else if r ==  2 then "sp"
  else if r ==  3 then "gp"
  else if r ==  4 then "tp"
  else if r ==  5 then "t0"
  else if r ==  6 then "t1"
  else if r ==  7 then "t2"
  else if r ==  8 then "fp"
  else if r ==  9 then "s1"
  else if r == 10 then "a0"
  else if r == 11 then "a1"
  else if r == 12 then "a2"
  else if r == 13 then "a3"
  else if r == 14 then "a4"
  else if r == 15 then "a5"
  else if r == 16 then "a6"
  else if r == 17 then "a7"
  else if r == 18 then "s2"
  else if r == 19 then "s3"
  else if r == 20 then "s4"
  else if r == 21 then "s5"
  else if r == 22 then "s6"
  else if r == 23 then "s7"
  else if r == 24 then "s8"
  else if r == 25 then "s9"
  else if r == 26 then "s10"
  else if r == 27 then "s11"
  else if r == 28 then "t3"
  else if r == 29 then "t4"
  else if r == 30 then "t5"
  else                 "t6"
}

string fpreg(r::reg) =
{ if      r ==  0 then "fs0"
  else if r ==  1 then "fs1"
  else if r ==  2 then "fs2"
  else if r ==  3 then "fs3"
  else if r ==  4 then "fs4"
  else if r ==  5 then "fs5"
  else if r ==  6 then "fs6"
  else if r ==  7 then "fs7"
  else if r ==  8 then "fs8"
  else if r ==  9 then "fs9"
  else if r == 10 then "fs10"
  else if r == 11 then "fs11"
  else if r == 12 then "fs12"
  else if r == 13 then "fs13"
  else if r == 14 then "fs14"
  else if r == 15 then "fs15"
  else if r == 16 then "fv0"
  else if r == 17 then "fv1"
  else if r == 18 then "fa0"
  else if r == 19 then "fa1"
  else if r == 20 then "fa2"
  else if r == 21 then "fa3"
  else if r == 22 then "fa4"
  else if r == 23 then "fa5"
  else if r == 24 then "fa6"
  else if r == 25 then "fa7"
  else if r == 26 then "ft0"
  else if r == 27 then "ft1"
  else if r == 28 then "ft2"
  else if r == 29 then "ft3"
  else if r == 30 then "ft4"
  else                 "ft5"
}

string log_w_gpr(r::reg, data::regType) =
    "Reg " : reg(r) : " (" : [[r]::nat] : ") <- 0x" : hex64(data)

string log_w_fprs(r::reg, data::word) =
    "FPR " : reg(r) : " (" : [[r]::nat] : ") <- 0x" : hex32(data)

string log_w_fprd(r::reg, data::regType) =
    "FPR " : reg(r) : " (" : [[r]::nat] : ") <- 0x" : hex64(data)

string log_w_mem_mask(pAddrIdx::pAddrIdx, vAddr::vAddr, mask::regType,
                      data::regType, old::regType, new::regType) =
    "MEM[0x" : hex64([pAddrIdx]) : "/" : hex64(vAddr) :
    "] <- (data: 0x" : hex64(data) : ", mask: 0x" : hex64(mask) :
    ", old: 0x"  : hex64(old) : ", new: 0x"  : hex64(new) : ")"

string log_w_mem_mask_misaligned(pAddrIdx::pAddrIdx, vAddr::vAddr, mask::regType,
                                 data::regType, align::nat, old::regType, new::regType) =
    "MEM[0x" : hex64([pAddrIdx]) : "/" : hex64(vAddr) : "/ misaligned@" : [align] :
    "] <- (data: 0x" : hex64(data) : ", mask: 0x" : hex64(mask) :
    ", old: 0x"  : hex64(old) : ", new: 0x"  : hex64(new) : ")"

string log_w_mem(pAddrIdx::pAddrIdx, vAddr::vAddr, data::regType) =
    "MEM[0x" : hex64([pAddrIdx]) : "/" : hex64(vAddr) :
    "] <- (data: 0x" : hex64(data) : ")"

string log_r_mem(pAddrIdx::pAddrIdx, vAddr::vAddr, data::regType) =
    "data <- MEM[0x" : PadLeft(#"0", 10, [pAddrIdx]) : "/" : hex64(vAddr) :
    "]: 0x" : hex64(data)

string log_exc(e::ExceptionType) =
    " Exception " : excName(e) : " raised!"

inline nat LOG_IO      = 0
inline nat LOG_INSN    = 1
inline nat LOG_REG     = 2
inline nat LOG_MEM     = 3
inline nat LOG_ADDRTR  = 4

declare log :: (nat * string) list

inline unit mark_log(lvl::nat, s::string) =
  when not PROVER_EXPORT do log <- (lvl, s) @ log

unit clear_logs()                   = log <- Nil

---------------------------------------------------------------------------
-- Exception and Interrupt processing
---------------------------------------------------------------------------

-- Signalled exceptions are recorded as traps.  The trap value is the
-- faulting address, or zero; Next replaces it by the instruction bits for
-- an illegal instruction (P §3.1.16 p.52-53, [D43]).

unit setTrap(e::ExceptionType, tval::regType) =
{ var trap
; trap.trap        <- e
; trap.tval        <- tval
; NextFetch        <- Some(Trap(trap))
}

unit signalException(e::ExceptionType) =
{ mark_log(LOG_INSN, "signalling exception " : excName(e))
; setTrap(e, 0)
; recordException()
}

unit signalAddressException(e::ExceptionType, vAddr::vAddr) =
{ mark_log(LOG_INSN, "signalling address exception " : excName(e) : " at " : [vAddr])
; setTrap(e, vAddr)
; recordException()
}

-- ECALL (P §3.3.1 p.60-61)
unit signalEnvCall() =
{ e = match curPrivilege()
      { case User       => UMode_Env_Call
        case Supervisor => SMode_Env_Call
        case Machine    => MMode_Env_Call
      }
; signalException(e)
}

-- An exception goes to M-mode unless it is raised below M-mode and
-- delegated in medeleg: traps never go to a less privileged mode (P
-- §3.1.8 p.42-43).
Privilege excDest(ec::exc_code, p::Privilege) =
    if p != Machine and MCSR.medeleg<[ec]::nat> then Supervisor else Machine

-- The pending interrupt of highest priority among those in p: MEI, MSI,
-- MTI, SEI, SSI, STI (P §3.1.9 p.45).
Interrupt option highestInterrupt(p::regType) =
{ if      p<11> then Some(MEI)
  else if p<3>  then Some(MSI)
  else if p<7>  then Some(MTI)
  else if p<9>  then Some(SEI)
  else if p<1>  then Some(SSI)
  else if p<5>  then Some(STI)
  else None
}

-- The interrupt to take and the mode it goes to (P §3.1.9 p.43-45, §12.1.3
-- p.117).  An interrupt goes to M-mode unless delegated in mideleg.
-- Interrupts to M-mode are enabled below M-mode, and in M-mode when
-- mstatus.MIE is set; interrupts to S-mode are enabled in U-mode, and in
-- S-mode when mstatus.SIE is set (P §3.1.6.1 p.32).
(Interrupt * Privilege) option checkInterrupts() =
{ p    = curPrivilege()
; pend = read_mip() && MCSR.&mie
; m = if p != Machine or MCSR.mstatus.MIE
      then highestInterrupt(pend && ~MCSR.mideleg) else None
; s = if p == User or (p == Supervisor and MCSR.mstatus.SIE)
      then highestInterrupt(pend && MCSR.mideleg) else None
; match m, s
  { case Some(i), _    => Some(i, Machine)
    case None, Some(i) => Some(i, Supervisor)
    case None, None    => None
  }
}

-- The trap handler address (P §3.1.7 p.41-42): BASE, plus 4 times the
-- cause for an interrupt in Vectored mode.
regType trapVector(tvec::regType, intr::bool, ec::exc_code) =
{ base = tvec<63:2> : '00'
; if intr and tvec<1:0> == 1 then base + 4 * ZeroExtend(ec) else base
}

-- Trap entry (P §3.1.6.1 p.32, §3.1.14-3.1.16 p.48-53; §12.1.1 p.113,
-- §12.1.7-12.1.9 p.119-121).  mstatus.MPRV and the load reservation are
-- unchanged ([D45]).  A trap goes to M-mode or S-mode, as excDest or
-- checkInterrupts gives, never to U-mode.  Traps into S-mode are
-- validated like those into M-mode (design-smode.md §2.7-2.9).
unit takeTrap(intr::bool, ec::exc_code, epc::regType, tval::regType, toPriv::Privilege) =
{ fromP = curPrivilege()
; mark_log(LOG_INSN, ["trapping from " : privName(fromP) : " to " : privName(toPriv) :
                      " at pc " : [epc] : (if intr then " [intr] " else " [exc] ") : [[ec]::nat]])
; match toPriv
  { case User       => #INTERNAL_ERROR("Illegal trap to U-mode")
    case Supervisor =>
    { SCSR.scause.Int   <- intr
    ; SCSR.scause.EC    <- ZeroExtend(ec)
    ; SCSR.sepc         <- epc
    ; SCSR.stval        <- tval
    ; MCSR.mstatus.SPIE <- MCSR.mstatus.SIE
    ; MCSR.mstatus.SIE  <- false
    ; MCSR.mstatus.SPP  <- fromP != User
    ; setPrivilege(Supervisor)
    ; PC                <- trapVector(SCSR.stvec, intr, ec)
    }
    case Machine    =>
    { MCSR.mcause.Int   <- intr
    ; MCSR.mcause.EC    <- ZeroExtend(ec)
    ; MCSR.mepc         <- epc
    ; MCSR.mtval        <- tval
    ; MCSR.mstatus.MPIE <- MCSR.mstatus.MIE
    ; MCSR.mstatus.MIE  <- false
    ; MCSR.mstatus.MPP  <- privLevel(fromP)
    ; setPrivilege(Machine)
    ; PC                <- trapVector(MCSR.mtvec, intr, ec)
    }
  }
}

-- MRET returns to the mode in mstatus.MPP and SRET to the mode in
-- mstatus.SPP (P §3.3.2 p.61, §3.1.6.1 p.32-33); both clear MPRV when
-- they leave M-mode (P §3.1.6.4 p.35).  The load reservation is kept
-- ([D45]).

unit mret() =
{ p = privilege(MCSR.mstatus.MPP)
; mark_log(LOG_INSN, "ret-ing from M to " : privName(p))
; MCSR.mstatus.MIE  <- MCSR.mstatus.MPIE
; MCSR.mstatus.MPIE <- true
; MCSR.mstatus.MPP  <- privLevel(User)
; when p != Machine do MCSR.mstatus.MPRV <- false
; setPrivilege(p)
; PC                <- read_xepc(MCSR.mepc)
}

unit sret() =
{ p = if MCSR.mstatus.SPP then Supervisor else User
; mark_log(LOG_INSN, "ret-ing from " : privName(curPrivilege()) : " to " : privName(p))
; MCSR.mstatus.SIE  <- MCSR.mstatus.SPIE
; MCSR.mstatus.SPIE <- true
; MCSR.mstatus.SPP  <- false
; MCSR.mstatus.MPRV <- false
; setPrivilege(p)
; PC                <- read_xepc(SCSR.sepc)
}

---------------------------------------------------------------------------
-- CSR access with logging
---------------------------------------------------------------------------

component CSR(n::creg) :: regType
{ value        = CSRMap(n)
  assign value =  { CSRMap(n) <- value
                  ; mark_log(LOG_REG, log_w_csr(n, value))
                  }
}

unit writeCSR(csr::creg, val::regType) =
{ CSR(csr)      <- val;
  Delta.addr    <- Some(ZeroExtend(csr));
  Delta.data2   <- Some(CSR(csr))   -- Note that writes to CSR are intercepted
                                    -- and controlled by CSRMap, so we need to
                                    -- use what was finally written to the
                                    -- CSR, and not val itself.
}

---------------------------------------------------------------------------
-- GPR/FPR access with logging
---------------------------------------------------------------------------

component GPR(n::reg) :: regType
{ value        = if n == 0 then 0 else gpr(n)
  assign value = when n <> 0
                 do { gpr(n) <- value
                    ; mark_log(LOG_REG, log_w_gpr(n, value))
                    }
}

-- val is bound once, before the write: it may read GPR(rd), and the SML
-- export would otherwise re-evaluate it for Delta.data1 after the write
-- (e.g. DIV x2,x1,x2, which must not raise an exception: ISA manual 4.5.2)
inline unit writeRD(rd::reg, val::regType) =
{ v = val
; GPR(rd)       <- v
; when not PROVER_EXPORT do Delta.data1   <- Some(v)
}

-- Single-precision values are NaN-boxed (ISA manual 6.2.2): a write sets
-- bits 63:32 to all 1s, and a read of a register that does not hold a
-- NaN-boxed value gives the canonical NaN.  The transfers out of a register
-- (FSW, FMV.X.W) use FPRS_raw, which ignores bits 63:32.
component FPRS(n::reg) :: word
{ value        = { v = fpr(n)
                 ; if v<63:32> == 0xFFFFFFFF then v<31:0> else RV32_CanonicalNan
                 }
  assign value = { fpr(n) <- 0xFFFFFFFF`32 : value
                 ; mark_log(LOG_REG, log_w_fprs(n, value))
                 }
}

word FPRS_raw(n::reg) = fpr(n)<31:0>

component FPRD(n::reg) :: regType
{ value        = fpr(n)
  assign value = { fpr(n) <- value
                 ; mark_log(LOG_REG, log_w_fprd(n, value))
                 }
}

unit writeFPRS(rd::reg, val::word) =
{ FPRS(rd)          <- val
; MCSR.mstatus.FS   <- ext_status(Dirty)
; Delta.data1       <- Some(0xFFFFFFFF`32 : val)
}

unit writeFPRD(rd::reg, val::regType) =
{ FPRD(rd)          <- val
; MCSR.mstatus.FS   <- ext_status(Dirty)
; Delta.data1       <- Some(val)
}

---------------------------------------------------------------------------
-- Raw memory access
---------------------------------------------------------------------------

regType rawReadData(pAddr::pAddr) =
{ pAddrIdx = pAddr<63:3>
; align    = [pAddr<2:0>]::nat
; if align == 0   -- aligned read
  then { data = MEM(pAddrIdx)
       ; mark_log(LOG_MEM, log_r_mem(pAddrIdx,   pAddr, data))
       ; data
       }
  else { dw0   = MEM(pAddrIdx)
       ; dw1   = MEM(pAddrIdx+1)
       ; ddw   = (dw1 : dw0) >> (align * 8)
       ; data  = ddw<63:0>
       ; mark_log(LOG_MEM, log_r_mem(pAddrIdx,   pAddr, dw0))
       ; mark_log(LOG_MEM, log_r_mem(pAddrIdx+1, pAddr, dw1))
       ; mark_log(LOG_MEM, log_r_mem(pAddrIdx,   pAddr, data))
       ; data
       }
}

unit rawWriteData(pAddr::pAddr, data::regType, nbytes::nat) =
{ mask     = ([ZeroExtend(1`1)::regType] << (nbytes * 8)) - 1
; pAddrIdx = pAddr<63:3>
; align    = [pAddr<2:0>] :: nat
; old      = MEM(pAddrIdx)

; mark_log(LOG_MEM, log_r_mem(pAddrIdx, pAddr, old))

; if align == 0     -- aligned write
  then { new = old && ~mask || data && mask
       ; MEM(pAddrIdx) <- new
       ; mark_log(LOG_MEM, log_w_mem_mask(pAddrIdx, pAddr, mask, data, old, new))
       }
  else { if align + nbytes <= Size(mask) div 8      -- write to a single regType-sized block
         then { new = old && ~(mask << (align * 8)) || (data && mask) << (align * 8)
              ; MEM(pAddrIdx) <- new
              ; mark_log(LOG_MEM, log_w_mem_mask_misaligned(pAddrIdx, pAddr, mask, data, align, old, new))
              }
         -- write touching adjacent regType-sized blocks; not reached,
         -- since every store is naturally aligned ([D55])
         else { dw_old  = MEM(pAddrIdx+1) : old
              ; dw_data = ZeroExtend(data) << (align*8)
              ; dw_mask = ZeroExtend(mask) << (align*8)
              ; dw_new  = dw_old && ~dw_mask || dw_data && dw_mask
              ; MEM(pAddrIdx+1) <- dw_new<2*Size(data)-1:Size(data)>
              ; MEM(pAddrIdx)   <- dw_new<Size(data)-1:0>
              }
       }
}

rawInstType rawReadInst(pAddr::pAddr) =
{ h = MEM8 (pAddr)
; match h
  { case '_ 11' => { Skip <- 4 ;
                     Word (MEM8 (pAddr + 3) : MEM8 (pAddr + 2) :
                           MEM8 (pAddr + 1) : MEM8 (pAddr)) }
    case _      => { Skip <- 2 ;
                     Half (MEM8 (pAddr + 1) : MEM8 (pAddr)) }
  }
}

-- helper used to preload memory contents
unit rawWriteMem(pAddr::pAddr, data::regType) =
{ pAddrIdx = pAddr<63:3>
; MEM(pAddrIdx) <- data
; mark_log(LOG_MEM, log_w_mem(pAddrIdx, pAddr, data))
}

---------------------------------------------------------------------------
-- Physical Memory Protection
---------------------------------------------------------------------------

-- PMP (P §3.7 p.70-74) checks every instruction fetch and explicit data
-- access, by physical address.  The hart has 16 entries and the grain G
-- is 0, so pmpaddr is read as stored and every region is a multiple of 4
-- bytes (P §3.7.1.1 p.73, [D47], [D48]).

-- What an access needs from the entry that matches it (P §3.7.1 p.72): R
-- for a load or LR, W for a store or SC, both for an AMO, X for a fetch.
construct pmpAccess { PMP_Read, PMP_Write, PMP_ReadWrite, PMP_Execute }

bool pmpPermits(cfg::pmpcfg, kind::pmpAccess) =
    match kind
    { case PMP_Read      => cfg.R
      case PMP_Write     => cfg.W
      case PMP_ReadWrite => cfg.R and cfg.W
      case PMP_Execute   => cfg.X
    }

-- The bytes lo to hi - 1 that entry i matches, or None (P §3.7.1.1
-- p.72-73).  OFF matches nothing.  TOR matches pmpaddr(i-1) <= y <
-- pmpaddr(i), from 0 for entry 0 and whatever the A field of entry i-1,
-- and nothing if the bounds do not increase.  NA4 matches 4 bytes.  NAPOT
-- matches 2^(t+3) naturally aligned bytes when pmpaddr(i) ends in t ones
-- (Table 24 p.72); m has the t+1 lowest bits set.
(pAddr * pAddr) option pmpRegion(i::bits(4)) =
{ y = pmpaddr(i)
; match pmpcfg_ent(i).A
  { case 0 => None
    case 1 => { lo = if i == 0 then 0 else pmpaddr(i - 1) << 2
              ; hi = y << 2
              ; if lo <+ hi then Some(lo, hi) else None
              }
    case 2 => Some(y << 2, (y << 2) + 4)
    case 3 => { m  = y ?? (y + 1)
              ; lo = (y && ~m) << 2
              ; Some(lo, lo + ((m + 1) << 2))
              }
  }
}

-- The verdict of entry i on an access to the bytes a to last, or None if
-- the entry matches none of them.  It must match all of them, or the
-- access fails, also in M-mode; if it does, M-mode is allowed unless the
-- entry is locked (P §3.7.1.2-3.7.1.3 p.73).
bool option pmpEntryCheck(i::bits(4), a::pAddr, last::pAddr, kind::pmpAccess,
                          p::Privilege) =
    match pmpRegion(i)
    { case None         => None
      case Some(lo, hi) =>
        if last <+ lo or hi <=+ a then None
        else if lo <=+ a and last <+ hi
        then { cfg = pmpcfg_ent(i)
             ; Some((p == Machine and not cfg.L) or pmpPermits(cfg, kind))
             }
        else Some(false)
    }

-- Whether PMP allows an access of n bytes at a by privilege p (P
-- §3.7.1.3 p.73): the lowest-numbered entry that matches any of its bytes
-- decides, and if none does, only M-mode is allowed.  The access is
-- naturally aligned, so a + (n - 1) does not wrap.  The caller raises the
-- access fault ([D53]).
bool pmpCheck(a::pAddr, n::nat, kind::pmpAccess, p::Privilege) =
{ last = a + [n - 1]
; e0  = pmpEntryCheck(0,  a, last, kind, p)
; e1  = pmpEntryCheck(1,  a, last, kind, p)
; e2  = pmpEntryCheck(2,  a, last, kind, p)
; e3  = pmpEntryCheck(3,  a, last, kind, p)
; e4  = pmpEntryCheck(4,  a, last, kind, p)
; e5  = pmpEntryCheck(5,  a, last, kind, p)
; e6  = pmpEntryCheck(6,  a, last, kind, p)
; e7  = pmpEntryCheck(7,  a, last, kind, p)
; e8  = pmpEntryCheck(8,  a, last, kind, p)
; e9  = pmpEntryCheck(9,  a, last, kind, p)
; e10 = pmpEntryCheck(10, a, last, kind, p)
; e11 = pmpEntryCheck(11, a, last, kind, p)
; e12 = pmpEntryCheck(12, a, last, kind, p)
; e13 = pmpEntryCheck(13, a, last, kind, p)
; e14 = pmpEntryCheck(14, a, last, kind, p)
; e15 = pmpEntryCheck(15, a, last, kind, p)
; if      IsSome(e0)  then ValOf(e0)
  else if IsSome(e1)  then ValOf(e1)
  else if IsSome(e2)  then ValOf(e2)
  else if IsSome(e3)  then ValOf(e3)
  else if IsSome(e4)  then ValOf(e4)
  else if IsSome(e5)  then ValOf(e5)
  else if IsSome(e6)  then ValOf(e6)
  else if IsSome(e7)  then ValOf(e7)
  else if IsSome(e8)  then ValOf(e8)
  else if IsSome(e9)  then ValOf(e9)
  else if IsSome(e10) then ValOf(e10)
  else if IsSome(e11) then ValOf(e11)
  else if IsSome(e12) then ValOf(e12)
  else if IsSome(e13) then ValOf(e13)
  else if IsSome(e14) then ValOf(e14)
  else if IsSome(e15) then ValOf(e15)
  else p == Machine
}

---------------------------------------------------------------------------
-- Address Translation
---------------------------------------------------------------------------

-- Supervisor address translation with Sv39, Sv48 and Sv57 (P §12.1.11
-- p.124-126, §12.3-12.6 p.130-139, [S7]).  The hart has no
-- address-translation cache, so every access walks the page table as it is
-- in memory at that moment (P §12.3.2 p.135, [S4]).  A and D are managed
-- by software, as with Svade (P §12.3.1 p.132, [S3]), and Svnapot, Svpbmt
-- and Svrsw60t59b are absent ([S12]).  The walk only reads the state: it
-- reads the PTEs from memory without logging them ([S6]) and never writes
-- them.  PTE reads are physical and have no PMA check ([S14]).

-- The physical address of an access, or the exception it raises (P §3.1.15
-- Table 16 p.50, [S2]).
construct TransResult { TR_Address :: pAddr, TR_Fault :: ExceptionType }

-- What one level of the walk gives (P §12.3.2 p.134): the PPN of the
-- next table, the physical address, a page fault or an access fault.
construct walkResult
{ W_Next        :: bits(44)
, W_Address     :: pAddr
, W_PageFault
, W_AccessFault
}

-- The page fault and the access fault of an access (Table 16 p.50): a
-- fetch is (Instruction, Read); a load or LR is (Data, Read); a store, SC
-- or AMO is (Data, Write), since "AMOs never raise load page-fault
-- exceptions" (P §12.3.1 p.132).
ExceptionType pageFault(ft::fetchType, ac::accessType) =
    if ft == Instruction then Fetch_PageFault
    else if ac == Read then Load_PageFault else Store_AMO_PageFault

ExceptionType accessFault(ft::fetchType, ac::accessType) =
    if ft == Instruction then Fetch_Fault
    else if ac == Read then Load_Fault else Store_AMO_Fault

-- Whether a leaf PTE allows the access by privilege p (P §12.3.2 steps 6,
-- 8 and 9 p.134; Figure 70 p.136).  U-mode needs U = 1.  S-mode needs
-- U = 0, or U = 1 with mstatus.SUM set, but never executes from a page
-- with U = 1 (P §12.3.1 p.132, §3.1.6.4 p.35).  A fetch needs X, a load R,
-- or X with mstatus.MXR set, and a store W (p.35).  With Svade, an access
-- needs A = 1 and a store also D = 1 (step 9).
bool ptePermits(pte::dword, ft::fetchType, ac::accessType, p::Privilege) =
{ store = ft == Data and ac == Write
; uOK   = if p == User then pte<4>
          else not pte<4> or (ft == Data and MCSR.mstatus.SUM)
; xwrOK = if ft == Instruction then pte<3>
          else if ac == Read then pte<1> or (pte<3> and MCSR.mstatus.MXR)
          else pte<2>
; adOK  = pte<6> and (not store or pte<7>)
; uOK and xwrOK and adOK
}

-- Level i of the walk, with the page table at PPN ppn (P §12.3.2 steps
-- 2-5 and 10 p.134).  The PTE at ppn * 4096 + VPN[i] * 8 is read as an
-- implicit access by S-mode, which needs the PMP's read permission or
-- raises the access fault of the original access type (step 2; P §3.7.2
-- p.74, [S14]).  A PTE with V = 0, with W = 1 but R = 0, or with any of
-- bits 63-54 set is invalid, and so is a pointer (R = W = X = 0) with D,
-- A or U set: those bits are reserved (step 3; P §12.3.1 p.133, §12.4.1
-- p.137, [S12]).  A pointer at level 0 and a misaligned superpage are
-- page faults (steps 4 and 5).  Otherwise the leaf maps a page of
-- 2^(12 + 9i) bytes (step 10).
walkResult ptwLevel(i::nat, ppn::bits(44), va::vAddr, ft::fetchType,
                    ac::accessType, p::Privilege) =
{ pteAddr = ((ZeroExtend(ppn)::pAddr) << 12) + (((va >>+ (12 + 9 * i)) && 0x1FF) << 3)
; if not pmpCheck(pteAddr, 8, PMP_Read, Supervisor) then W_AccessFault
  else
  { pte  = MEM(pteAddr<63:3>)
  ; leaf = pte<1> or pte<3>
  ; if not pte<0> or (pte<2> and not pte<1>) or (pte && 0xFFC0000000000000) != 0
       or (not leaf and (pte && 0xD0) != 0)
    then W_PageFault
    else if not leaf then (if i == 0 then W_PageFault else W_Next(pte<53:10>))
    else
    { base = (ZeroExtend(pte<53:10>)::pAddr) << 12
    ; mask = ((1::pAddr) << (12 + 9 * i)) - 1
    ; if (base && mask) != 0 then W_PageFault
      else if not ptePermits(pte, ft, ac, p) then W_PageFault
      else W_Address(base || (va && mask))
    }
  }
}

-- Level i of a walk of the given number of levels: it runs only while the
-- walk descends and i is below the top level, levels - 1.
walkResult ptwStep(r::walkResult, i::nat, levels::nat, va::vAddr,
                   ft::fetchType, ac::accessType, p::Privilege) =
    match r
    { case W_Next(ppn) => if i < levels then ptwLevel(i, ppn, va, ft, ac, p) else r
      case _           => r
    }

-- The physical address of an access at va by privilege p, which is
-- curPrivilege() for a fetch and effectivePrivilege() for a load or store
-- (P §3.1.6.4 p.35, [S1]).  satp is active, and va translated, only if p
-- is S or U (P §12.1.11 p.126) and satp.MODE is not Bare (Table 40
-- p.126).  p is tested first, so that at M nothing else is read.
-- legalize_satp keeps the reserved MODEs out of satp; they would act as
-- Bare ([S11]).  A va whose bits 63 to VALEN - 1 are not all equal raises
-- a page fault before any PTE is read (P §12.4.1 p.136, §12.5.1 p.137,
-- §12.6.1 p.138).  The walk starts at level LEVELS - 1 with the root table
-- at satp.PPN (P §12.3.2 step 1 p.134); it is unrolled ([S5]), and the
-- levels at or above LEVELS pass the start on unchanged.
TransResult translateAddr(va::vAddr, ft::fetchType, ac::accessType, p::Privilege) =
  if p == Machine then TR_Address(va)
  else
  { satp   = SCSR.satp
  ; levels = match satp<63:60> { case 8 => 3::nat  case 9 => 4  case 10 => 5  case _ => 0 }
  ; if levels == 0 then TR_Address(va)
    else
    { sh = 64 - (12 + 9 * levels)
    ; if ((va << sh) >> sh) != va then TR_Fault(pageFault(ft, ac))
      else
      { r4 = ptwStep(W_Next(satp<43:0>), 4, levels, va, ft, ac, p)
      ; r3 = ptwStep(r4, 3, levels, va, ft, ac, p)
      ; r2 = ptwStep(r3, 2, levels, va, ft, ac, p)
      ; r1 = ptwStep(r2, 1, levels, va, ft, ac, p)
      ; r0 = ptwStep(r1, 0, levels, va, ft, ac, p)
      ; match r0
        { case W_Address(pa)  => TR_Address(pa)
          case W_AccessFault  => TR_Fault(accessFault(ft, ac))
          case _              => TR_Fault(pageFault(ft, ac))   -- W_Next cannot occur
        }
      }
    }
  }

-- The physical address of the 2-byte instruction parcel at vAddr.  The
-- parcel is translated with the current privilege, since MPRV does not
-- apply to fetches (P §3.1.6.4 p.35), and its physical address needs the
-- PMP's execute permission, or the fetch raises an access fault (P §3.7.1
-- p.72).
TransResult fetchAddr(vAddr::vAddr) =
{ p = curPrivilege()
; match translateAddr(vAddr, Instruction, Read, p)
  { case TR_Address(pAddr) => if pmpCheck(pAddr, 2, PMP_Execute, p) then TR_Address(pAddr)
                              else TR_Fault(Fetch_Fault)
    case f                 => f
  }
}

-- The physical address of an explicit, naturally aligned data access of n
-- bytes at vAddr.  The access is translated with the effective privilege
-- (P §3.1.6.4 p.35, [D22]), and its physical address needs the PMP's
-- permission for that privilege, or the access raises an access fault (P
-- §3.7 p.70).  A load or LR is a read, and a store, SC or AMO a write.
TransResult dataAddr(vAddr::vAddr, n::nat, kind::pmpAccess) =
{ p  = effectivePrivilege()
; ac = if kind == PMP_Read then Read else Write
; match translateAddr(vAddr, Data, ac, p)
  { case TR_Address(pAddr) => if pmpCheck(pAddr, n, kind, p) then TR_Address(pAddr)
                              else TR_Fault(accessFault(Data, ac))
    case f                 => f
  }
}

---------------------------------------------------------------------------
-- Load Reservation
---------------------------------------------------------------------------

-- The reservation is of a physical address, since the reservation set lies
-- within one physical page (P §12.3.1 p.133, [S17]).
bool matchLoadReservation(pAddr::pAddr) =
    IsSome(ReserveLoad) and ValOf(ReserveLoad) == pAddr

---------------------------------------------------------------------------
-- Control Flow
---------------------------------------------------------------------------

unit branchTo(newPC::regType) =
{ NextFetch  <- Some(BranchTo(newPC))
; when not PROVER_EXPORT do Delta.addr <- Some(newPC)
}

inline unit noBranch(nextPC::regType) =
when not PROVER_EXPORT do { Delta.addr <- Some(nextPC) }

---------------------------------------------------------------------------
-- Integer Computational Instructions
---------------------------------------------------------------------------

-- Integer register-immediate

-----------------------------------
-- ADDI  rd, rs1, imm
-----------------------------------
define ArithI > ADDI(rd::reg, rs1::reg, imm::imm12) =
    writeRD(rd, GPR(rs1) + SignExtend(imm))

-----------------------------------
-- ADDIW rd, rs1, imm   (RV64I)
-----------------------------------
define ArithI > ADDIW(rd::reg, rs1::reg, imm::imm12) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { temp = GPR(rs1) + SignExtend(imm)
         ; writeRD(rd, SignExtend(temp<31:0>))
         }

-----------------------------------
-- SLTI  rd, rs1, imm
-----------------------------------
define ArithI > SLTI(rd::reg, rs1::reg, imm::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; writeRD(rd, [v1 < SignExtend(imm)])
}

-----------------------------------
-- SLTIU rd, rs1, imm
-----------------------------------
define ArithI > SLTIU(rd::reg, rs1::reg, imm::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; writeRD(rd, [v1 <+ SignExtend(imm)])
}

-----------------------------------
-- ANDI  rd, rs1, imm
-----------------------------------
define ArithI > ANDI(rd::reg, rs1::reg, imm::imm12) =
    writeRD(rd, GPR(rs1) && SignExtend(imm))

-----------------------------------
-- ORI   rd, rs1, imm
-----------------------------------
define ArithI > ORI(rd::reg, rs1::reg, imm::imm12) =
    writeRD(rd, GPR(rs1) || SignExtend(imm))

-----------------------------------
-- XORI  rd, rs1, imm
-----------------------------------
define ArithI > XORI(rd::reg, rs1::reg, imm::imm12) =
    writeRD(rd, GPR(rs1) ?? SignExtend(imm))


-----------------------------------
-- SLLI  rd, rs1, imm
-----------------------------------
define Shift > SLLI(rd::reg, rs1::reg, imm::bits(6)) =
    if in32BitMode() and imm<5>
    then signalException(Illegal_Instr)
    else writeRD(rd, GPR(rs1) << [imm])

-----------------------------------
-- SRLI  rd, rs1, imm
-----------------------------------
define Shift > SRLI(rd::reg, rs1::reg, imm::bits(6)) =
    if in32BitMode() and imm<5>
    then signalException(Illegal_Instr)
    else { v1 = if in32BitMode() then ZeroExtend(GPR(rs1)<31:0>) else GPR(rs1)
         ; writeRD(rd, v1 >>+ [imm])
         }

-----------------------------------
-- SRAI  rd, rs1, imm
-----------------------------------
define Shift > SRAI(rd::reg, rs1::reg, imm::bits(6)) =
    if in32BitMode() and imm<5>
    then signalException(Illegal_Instr)
    else { v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
         ; writeRD(rd, v1 >> [imm])
         }

-----------------------------------
-- SLLIW rd, rs1, imm   (RV64I)
-----------------------------------
define Shift > SLLIW(rd::reg, rs1::reg, imm::bits(5)) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> << [imm]))

-----------------------------------
-- SRLIW rd, rs1, imm   (RV64I)
-----------------------------------
define Shift > SRLIW(rd::reg, rs1::reg, imm::bits(5)) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> >>+ [imm]))

-----------------------------------
-- SRAIW rd, rs1, imm   (RV64I)
-----------------------------------
define Shift > SRAIW(rd::reg, rs1::reg, imm::bits(5)) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> >> [imm]))

-----------------------------------
-- LUI   rd, imm
-----------------------------------
define ArithI > LUI(rd::reg, imm::imm20) =
    writeRD(rd, SignExtend(imm : 0`12))

-----------------------------------
-- AUIPC rd, imm
-----------------------------------
define ArithI > AUIPC(rd::reg, imm::imm20) =
    writeRD(rd, PC + SignExtend(imm : 0`12))


-- Integer register-register

-----------------------------------
-- ADD   rd, rs1, rs2
-----------------------------------
define ArithR > ADD(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) + GPR(rs2))

-----------------------------------
-- ADDW  rd, rs1, rs2   (RV64I)
-----------------------------------
define ArithR > ADDW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> + GPR(rs2)<31:0>))

-----------------------------------
-- SUB   rd, rs1, rs2
-----------------------------------
define ArithR > SUB(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) - GPR(rs2))

-----------------------------------
-- SUBW  rd, rs1, rs2   (RV64I)
-----------------------------------
define ArithR > SUBW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> - GPR(rs2)<31:0>))

-----------------------------------
-- SLT   rd, rs1, rs2
-----------------------------------
define ArithR > SLT(rd::reg, rs1::reg, rs2::reg) =
{ v1  = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2  = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; writeRD(rd, [v1 < v2])
}

-----------------------------------
-- SLTU  rd, rs1, rs2
-----------------------------------
define ArithR > SLTU(rd::reg, rs1::reg, rs2::reg) =
{ v1  = if in32BitMode() then ZeroExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2  = if in32BitMode() then ZeroExtend(GPR(rs2)<31:0>) else GPR(rs2)
; writeRD(rd, [v1 <+ v2])
}

-----------------------------------
-- AND   rd, rs1, rs2
-----------------------------------
define ArithR > AND(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) && GPR(rs2))

-----------------------------------
-- OR    rd, rs1, rs2
-----------------------------------
define ArithR > OR(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) || GPR(rs2))

-----------------------------------
-- XOR   rd, rs1, rs2
-----------------------------------
define ArithR > XOR(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) ?? GPR(rs2))

-----------------------------------
-- SLL   rd, rs1, rs2
-----------------------------------
define Shift > SLL(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then writeRD(rd, GPR(rs1) << ZeroExtend(GPR(rs2)<4:0>))
    else writeRD(rd, GPR(rs1) << ZeroExtend(GPR(rs2)<5:0>))

-----------------------------------
-- SLLW  rd, rs1, rs2   (RV64I)
-----------------------------------
define Shift > SLLW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> << ZeroExtend(GPR(rs2)<4:0>)))

-----------------------------------
-- SRL   rd, rs1, rs2
-----------------------------------
define Shift > SRL(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then writeRD(rd, ZeroExtend(GPR(rs1)<31:0> >>+ ZeroExtend(GPR(rs2)<4:0>)))
    else writeRD(rd, GPR(rs1) >>+ ZeroExtend(GPR(rs2)<5:0>))

-----------------------------------
-- SRLW  rd, rs1, rs2   (RV64I)
-----------------------------------
define Shift > SRLW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> >>+ ZeroExtend(GPR(rs2)<4:0>)))

-----------------------------------
-- SRA   rd, rs1, rs2
-----------------------------------
define Shift > SRA(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then writeRD(rd, SignExtend(GPR(rs1)<31:0> >> ZeroExtend(GPR(rs2)<4:0>)))
    else writeRD(rd, GPR(rs1) >> ZeroExtend(GPR(rs2)<5:0>))

-----------------------------------
-- SRAW  rd, rs1, rs2   (RV64I)
-----------------------------------
define Shift > SRAW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else writeRD(rd, SignExtend(GPR(rs1)<31:0> >> ZeroExtend(GPR(rs2)<4:0>)))

---------------------------------------------------------------------------
-- Multiply and Divide
---------------------------------------------------------------------------

-----------------------------------
-- MUL   rd, rs1, rs2
-----------------------------------
define MulDiv > MUL(rd::reg, rs1::reg, rs2::reg) =
    writeRD(rd, GPR(rs1) * GPR(rs2))

-----------------------------------
-- MULH  rd, rs1, rs2
-----------------------------------
define MulDiv > MULH(rd::reg, rs1::reg, rs2::reg) =
{ v1  = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2  = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; prod`128 = SignExtend(v1) * SignExtend(v2)
; res = if in32BitMode() then SignExtend(prod<63:32>) else SignExtend(prod<127:64>)
; writeRD(rd, res)
}

-----------------------------------
-- MULHU rd, rs1, rs2
-----------------------------------
define MulDiv > MULHU(rd::reg, rs1::reg, rs2::reg) =
{ v1  = if in32BitMode() then ZeroExtend(GPR(rs1)<31:0>) else ZeroExtend(GPR(rs1))
; v2  = if in32BitMode() then ZeroExtend(GPR(rs2)<31:0>) else ZeroExtend(GPR(rs2))
; prod`128 = v1 * v2
; res = if in32BitMode() then ZeroExtend(prod<63:32>) else prod<127:64>
; writeRD(rd, res)
}

-----------------------------------
-- MULHSU rd, rs1, rs2
-----------------------------------
define MulDiv > MULHSU(rd::reg, rs1::reg, rs2::reg) =
{ v1  = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else SignExtend(GPR(rs1))
; v2  = if in32BitMode() then ZeroExtend(GPR(rs2)<31:0>) else ZeroExtend(GPR(rs2))
; prod`128 = v1 * v2
; res = if in32BitMode() then SignExtend(prod<63:32>) else prod<127:64>
; writeRD(rd, res)
}

-----------------------------------
-- MULW  rd, rs1, rs2
-----------------------------------
define MulDiv > MULW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { prod`64 = SignExtend(GPR(rs1)<31:0> * GPR(rs2)<31:0>)
         ; writeRD(rd, SignExtend(prod<31:0>))
         }

-----------------------------------
-- DIV   rd, rs1, rs2
-----------------------------------
define MulDiv > DIV(rd::reg, rs1::reg, rs2::reg) =
    if GPR(rs2) == 0x0
    then writeRD(rd, SignExtend(1`1))
    else writeRD(rd, GPR(rs1) quot GPR(rs2))

-----------------------------------
-- REM   rd, rs1, rs2
-----------------------------------
define MulDiv > REM(rd::reg, rs1::reg, rs2::reg) =
    if GPR(rs2) == 0x0
    then writeRD(rd, GPR(rs1))
    else writeRD(rd, GPR(rs1) rem GPR(rs2))

-----------------------------------
-- DIVU  rd, rs1, rs2
-----------------------------------
define MulDiv > DIVU(rd::reg, rs1::reg, rs2::reg) =
{ v1 = if in32BitMode() then ZeroExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then ZeroExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v2 == 0x0
  then writeRD(rd, SignExtend(1`1))
  else writeRD(rd, v1 div v2)
}

-----------------------------------
-- REMU  rd, rs1, rs2
-----------------------------------
define MulDiv > REMU(rd::reg, rs1::reg, rs2::reg) =
    if GPR(rs2) == 0x0
    then writeRD(rd, GPR(rs1))
    else writeRD(rd, GPR(rs1) mod GPR(rs2))

-----------------------------------
-- DIVW  rd, rs1, rs2
-----------------------------------
define MulDiv > DIVW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { s1 = GPR(rs1)<31:0>
         ; s2 = GPR(rs2)<31:0>
         ; if s2 == 0x0
           then writeRD(rd, SignExtend(1`1))
           else writeRD(rd, SignExtend(s1 quot s2))
         }

-----------------------------------
-- REMW  rd, rs1, rs2
-----------------------------------
define MulDiv > REMW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { s1 = GPR(rs1)<31:0>
         ; s2 = GPR(rs2)<31:0>
         ; if s2 == 0x0
           then writeRD(rd, SignExtend(s1))
           else writeRD(rd, SignExtend(s1 rem s2))
         }

-----------------------------------
-- DIVUW rd, rs1, rs2
-----------------------------------
define MulDiv > DIVUW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { s1 = GPR(rs1)<31:0>
         ; s2 = GPR(rs2)<31:0>
         ; if s2 == 0x0
           then writeRD(rd, SignExtend(1`1))
           else writeRD(rd, SignExtend(s1 div s2))
         }

-----------------------------------
-- REMUW rd, rs1, rs2
-----------------------------------
define MulDiv > REMUW(rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { s1 = GPR(rs1)<31:0>
         ; s2 = GPR(rs2)<31:0>
         ; if s2 == 0x0
           then writeRD(rd, SignExtend(s1))
           else writeRD(rd, SignExtend(s1 mod s2))
         }

---------------------------------------------------------------------------
-- Control Transfer Instructions
---------------------------------------------------------------------------

-- Unconditional jumps
--
-- If the C extension is enabled, IALIGN = 16,
-- meaning JAL and JALR never raise instruction-address-misaligned exceptions.

-----------------------------------
-- JAL   rd, offs
-----------------------------------
define Branch > JAL(rd::reg, imm::imm20) =
{ addr = PC + SignExtend(imm) << 1
; if addr<1> and not haveRVC()
  then signalAddressException(Fetch_Misaligned, addr)
  else { writeRD(rd, PC + Skip)
       ; branchTo(addr)
       }
}

-----------------------------------
-- JALR  rd, rs1, imm
-----------------------------------
define Branch > JALR(rd::reg, rs1::reg, imm::imm12) =
{ addr = (GPR(rs1) + SignExtend(imm)) && SignExtend('10')
; if addr<1> and not haveRVC()
  then signalAddressException(Fetch_Misaligned, addr)
  else { writeRD(rd, PC + Skip)
       ; branchTo(addr)
       }
}

-- conditional branches

-----------------------------------
-- BEQ   rs1, rs2, offs
-----------------------------------
define Branch > BEQ(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 == v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

-----------------------------------
-- BNE   rs1, rs2, offs
-----------------------------------
define Branch > BNE(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 <> v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

-----------------------------------
-- BLT   rs1, rs2, offs
-----------------------------------
define Branch > BLT(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 < v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

-----------------------------------
-- BLTU  rs1, rs2, offs
-----------------------------------
define Branch > BLTU(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 <+ v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

-----------------------------------
-- BGE   rs1, rs2, offs
-----------------------------------
define Branch > BGE(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 >= v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

-----------------------------------
-- BGEU  rs1, rs2, offs
-----------------------------------
define Branch > BGEU(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 >=+ v2
  then { addr = PC + (SignExtend(offs) << 1)
       ; if addr<1> and not haveRVC()
         then signalAddressException(Fetch_Misaligned, addr)
         else branchTo(addr)
       }
  else noBranch(PC + Skip)
}

---------------------------------------------------------------------------
-- Load and Store Instructions
---------------------------------------------------------------------------

-- A load or store that is not naturally aligned raises an
-- address-misaligned exception (U §2.1.6 p.37, [D55]) before any other
-- check, translation included (P §3.1.15 Table 17 p.51, [S15]), so no
-- access is ever split or crosses a page.  An aligned access is
-- translated and needs the permission of the PMP (dataAddr), or raises the
-- page fault or access fault that dataAddr gives.  The trap value is the
-- virtual address, for an access fault too (P §3.1.16 p.52).  The access
-- is recorded with its physical address.  The same holds for the
-- floating-point loads and stores, LR/SC and the AMOs.

-----------------------------------
-- LW    rd, rs1, offs
-----------------------------------
define Load > LW(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; if vAddr<1:0> != 0
  then signalAddressException(Load_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_Read)
       { case TR_Address(pAddr) => { val       = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; GPR(rd)  <- val
                                   ; recordLoad(pAddr, val)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- LWU   rd, rs1, offs  (RV64I)
-----------------------------------
define Load > LWU(rd::reg, rs1::reg, offs::imm12) =
{ if in32BitMode()
  then signalException(Illegal_Instr)
  else { vAddr = GPR(rs1) + SignExtend(offs)
       ; if vAddr<1:0> != 0
         then signalAddressException(Load_Misaligned, vAddr)
         else match dataAddr(vAddr, 4, PMP_Read)
              { case TR_Address(pAddr) => { val        = ZeroExtend(rawReadData(pAddr)<31:0>)
                                          ; GPR(rd)   <- val
                                          ; recordLoad(pAddr, val)
                                          }
                case TR_Fault(e)       => signalAddressException(e, vAddr)
              }
       }
}

-----------------------------------
-- LH    rd, rs1, offs
-----------------------------------
define Load > LH(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; if vAddr<0>
  then signalAddressException(Load_Misaligned, vAddr)
  else match dataAddr(vAddr, 2, PMP_Read)
       { case TR_Address(pAddr) => { val       = SignExtend(rawReadData(pAddr)<15:0>)
                                   ; GPR(rd)  <- val
                                   ; recordLoad(pAddr, val)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- LHU   rd, rs1, offs
-----------------------------------
define Load > LHU(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; if vAddr<0>
  then signalAddressException(Load_Misaligned, vAddr)
  else match dataAddr(vAddr, 2, PMP_Read)
       { case TR_Address(pAddr) => { val       = ZeroExtend(rawReadData(pAddr)<15:0>)
                                   ; GPR(rd)  <- val
                                   ; recordLoad(pAddr, val)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- LB    rd, rs1, offs
-----------------------------------
define Load > LB(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match dataAddr(vAddr, 1, PMP_Read)
  { case TR_Address(pAddr) => { val       = SignExtend(rawReadData(pAddr)<7:0>)
                              ; GPR(rd)  <- val
                              ; recordLoad(pAddr, val)
                              }
    case TR_Fault(e)       => signalAddressException(e, vAddr)
  }
}

-----------------------------------
-- LBU   rd, rs1, offs
-----------------------------------
define Load > LBU(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match dataAddr(vAddr, 1, PMP_Read)
  { case TR_Address(pAddr) => { val       = ZeroExtend(rawReadData(pAddr)<7:0>)
                              ; GPR(rd)  <- val
                              ; recordLoad(pAddr, val)
                              }
    case TR_Fault(e)       => signalAddressException(e, vAddr)
  }
}

-----------------------------------
-- LD    rd, rs1, offs  (RV64I)
-----------------------------------
define Load > LD(rd::reg, rs1::reg, offs::imm12) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<2:0> != 0
           then signalAddressException(Load_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Read)
                { case TR_Address(pAddr) => { val      = rawReadData(pAddr)
                                            ; GPR(rd) <- val
                                            ; recordLoad(pAddr, val)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-----------------------------------
-- SW    rs1, rs2, offs
-----------------------------------
define Store > SW(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_Write)
       { case TR_Address(pAddr) => { data = GPR(rs2)
                                   ; rawWriteData(pAddr, data, 4)
                                   ; recordStore(pAddr, data, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- SH    rs1, rs2, offs
-----------------------------------
define Store > SH(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; if vAddr<0>
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 2, PMP_Write)
       { case TR_Address(pAddr) => { data = GPR(rs2)
                                   ; rawWriteData(pAddr, data, 2)
                                   ; recordStore(pAddr, data, 2)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- SB    rs1, rs2, offs
-----------------------------------
define Store > SB(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match dataAddr(vAddr, 1, PMP_Write)
  { case TR_Address(pAddr) => { data = GPR(rs2)
                              ; rawWriteData(pAddr, data, 1)
                              ; recordStore(pAddr, data, 1)
                              }
    case TR_Fault(e)       => signalAddressException(e, vAddr)
  }
}

-----------------------------------
-- SD    rs1, rs2, offs (RV64I)
-----------------------------------
define Store > SD(rs1::reg, rs2::reg, offs::imm12) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<2:0> != 0
           then signalAddressException(Store_AMO_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Write)
                { case TR_Address(pAddr) => { data = GPR(rs2)
                                            ; rawWriteData(pAddr, data, 8)
                                            ; recordStore(pAddr, data, 8)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

---------------------------------------------------------------------------
-- Memory model
---------------------------------------------------------------------------

-----------------------------------
-- FENCE rd, rs1, pred, succ
-----------------------------------
define FENCE(rd::reg, rs1::reg, pred::bits(4), succ::bits(4)) = nothing

-----------------------------------
-- FENCE.I rd, rs1, imm
-----------------------------------
define FENCE_I(rd::reg, rs1::reg, imm::imm12) = nothing

-- Atomics --

-----------------------------------
-- LR.W [aq,rl] rd, rs1
-----------------------------------
-- LR is a load, so a misaligned LR raises a load exception ([D57]).
define AMO > LR_W(aq::amo, rl::amo, rd::reg, rs1::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Load_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_Read)
       { case TR_Address(pAddr) => { writeRD(rd, SignExtend(rawReadData(pAddr)<31:0>))
                                   ; ReserveLoad  <- Some(pAddr)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- LR.D [aq,rl] rd, rs1
-----------------------------------
define AMO > LR_D(aq::amo, rl::amo, rd::reg, rs1::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1)
         ; if vAddr<2:0> != 0
           then signalAddressException(Load_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Read)
                { case TR_Address(pAddr) => { writeRD(rd, rawReadData(pAddr))
                                            ; ReserveLoad <- Some(pAddr)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-----------------------------------
-- SC.W [aq,rl] rd, rs1, rs2
-----------------------------------
-- An SC is translated and needs the PMP's write permission also when it
-- fails for want of a reservation (P §3.7.1 p.72, [D60], [S18]).  The
-- reservation is of the physical address (matchLoadReservation).
define AMO > SC_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_Write)
       { case TR_Address(pAddr) =>
           if not matchLoadReservation(pAddr)
           then { writeRD(rd, 1)
                ; ReserveLoad <- None   -- ISA manual 5.2: a failed SC also invalidates it
                }
           else { data = GPR(rs2)
                ; rawWriteData(pAddr, data, 4)
                ; recordStore(pAddr, data, 4)
                ; writeRD(rd, 0)
                ; ReserveLoad  <- None
                }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- SC.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > SC_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1)
         ; if vAddr<2:0> != 0
           then signalAddressException(Store_AMO_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Write)
                { case TR_Address(pAddr) =>
                    if not matchLoadReservation(pAddr)
                    then { writeRD(rd, 1)
                         ; ReserveLoad <- None   -- ISA manual 5.2: a failed SC also invalidates it
                         }
                    else { data = GPR(rs2)
                         ; rawWriteData(pAddr, data, 8)
                         ; recordStore(pAddr, data, 8)
                         ; writeRD(rd, 0)
                         ; ReserveLoad  <- None
                         }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-----------------------------------
-- AMOSWAP.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOSWAP_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; rawWriteData(pAddr, data, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, data, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOSWAP.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOSWAP_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; rawWriteData(pAddr, data, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, data, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOADD.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOADD_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data + memv
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOADD.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOADD_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data + memv
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOXOR.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOXOR_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data ?? memv
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOXOR.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOXOR_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data ?? memv
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOAND.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOAND_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data && memv
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOAND.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOAND_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data && memv
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOOR.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOOR_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data || memv
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOOR.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOOR_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = data || memv
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMIN.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMIN_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = SignExtend(GPR(rs2)<31:0>)  -- ISA manual 5.6: ignore rs2<63:32>
                                   ; GPR(rd) <- memv
                                   ; val  = SignedMin(data, memv)
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMIN.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMIN_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = SignedMin(data, memv)
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMAX.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAX_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = SignExtend(GPR(rs2)<31:0>)  -- ISA manual 5.6: ignore rs2<63:32>
                                   ; GPR(rd) <- memv
                                   ; val  = SignedMax(data, memv)
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMAX.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAX_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = SignedMax(data, memv)
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMINU.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMINU_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = SignExtend(GPR(rs2)<31:0>)  -- ISA manual 5.6: ignore rs2<63:32>
                                   ; GPR(rd) <- memv
                                   ; val  = Min(data, memv)
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMINU.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMINU_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = Min(data, memv)
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMAXU.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAXU_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 4, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                                   ; data = SignExtend(GPR(rs2)<31:0>)  -- ISA manual 5.6: ignore rs2<63:32>
                                   ; GPR(rd) <- memv
                                   ; val  = Max(data, memv)
                                   ; rawWriteData(pAddr, val, 4)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 4)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}

-----------------------------------
-- AMOMAXU.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAXU_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(Store_AMO_Misaligned, vAddr)
  else match dataAddr(vAddr, 8, PMP_ReadWrite)
       { case TR_Address(pAddr) => { memv = rawReadData(pAddr)
                                   ; data = GPR(rs2)
                                   ; GPR(rd) <- memv
                                   ; val  = Max(data, memv)
                                   ; rawWriteData(pAddr, val, 8)
                                   ; recordLoad(pAddr, memv)
                                   ; recordStore(pAddr, val, 8)
                                   }
         case TR_Fault(e)       => signalAddressException(e, vAddr)
       }
}


---------------------------------------------------------------------------
-- Floating Point Instructions (Single Precision)
---------------------------------------------------------------------------

-- Load/Store

-----------------------------------
-- FLW   rd, rs2, offs
-----------------------------------

define FPLoad > FLW(rd::reg, rs1::reg, offs::imm12) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<1:0> != 0
           then signalAddressException(Load_Misaligned, vAddr)
           else match dataAddr(vAddr, 4, PMP_Read)
                { case TR_Address(pAddr) => { val       = rawReadData(pAddr)<31:0>
                                            ; writeFPRS(rd, val)  -- sets FS to Dirty (privileged manual 3.1.6.7)
                                            ; recordLoad(pAddr, ZeroExtend(val))
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-----------------------------------
-- FSW   rs1, rs2, offs
-----------------------------------

define FPStore > FSW(rs1::reg, rs2::reg, offs::imm12) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<1:0> != 0
           then signalAddressException(Store_AMO_Misaligned, vAddr)
           else match dataAddr(vAddr, 4, PMP_Write)
                { case TR_Address(pAddr) => { data = FPRS_raw(rs2)
                                            ; rawWriteData(pAddr, ZeroExtend(data), 4)
                                            ; recordStore(pAddr, ZeroExtend(data), 4)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-- Computational

-- Arithmetic accrues the flags of the IEEE operation (ISA manual 6.1.2);
-- tininess is detected after rounding (6.1.4) by SSE and by HOL's
-- Underflow_AfterRounding alike.

-----------------------------------
-- FADD.S   rd, rs1, rs2
-----------------------------------

define FArith > FADD_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_Add_(r, FPRS(rs1), FPRS(rs2))
                             ; accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FSUB.S   rd, rs1, rs2
-----------------------------------

define FArith > FSUB_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_Sub_(r, FPRS(rs1), FPRS(rs2))
                             ; accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMUL.S   rd, rs1, rs2
-----------------------------------

define FArith > FMUL_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_Mul_(r, FPRS(rs1), FPRS(rs2))
                             ; accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FDIV.S   rd, rs1, rs2
-----------------------------------

define FArith > FDIV_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_Div_(r, FPRS(rs1), FPRS(rs2))
                             ; accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FSQRT.S   rd, rs
-----------------------------------

define FArith > FSQRT_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { a = FPRS(rs)
                             ; (f, v) = FP32_Sqrt_(r, a)
                             -- no flag for a quiet NaN (IEEE 754-2008 6.2); HOL's
                             -- float_sqrt raises NV for a negative one
                             ; when not FP32_IsNan(a) or FP32_IsSignalingNan(a)
                               do accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMIN.S    rd, rs1, rs2
-----------------------------------
define FArith > FMIN_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRS(rs1)
         ; f2  = FPRS(rs2)
         -- ISA manual 6.1.6: -0.0 < +0.0, a NaN operand gives the other operand (the
         -- canonical NaN if both are NaNs), and a signalling NaN raises NV
         ; when FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2) do setFP_Invalid()
         ; res = if FP32_IsNan(f1) and FP32_IsNan(f2) then RV32_CanonicalNan
                 else if FP32_IsNan(f1) then f2
                 else if FP32_IsNan(f2) then f1
                 else if FP32_IsZero(f1) and FP32_IsZero(f2)
                 then (if FP32_Sign(f1) then f1 else f2)
                 else if FP32_LessThan(f1, f2) then f1 else f2
         ; writeFPRS(rd, res)
         }

-----------------------------------
-- FMAX.S    rd, rs1, rs2
-----------------------------------
define FArith > FMAX_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRS(rs1)
         ; f2  = FPRS(rs2)
         -- ISA manual 6.1.6: -0.0 < +0.0, a NaN operand gives the other operand (the
         -- canonical NaN if both are NaNs), and a signalling NaN raises NV
         ; when FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2) do setFP_Invalid()
         ; res = if FP32_IsNan(f1) and FP32_IsNan(f2) then RV32_CanonicalNan
                 else if FP32_IsNan(f1) then f2
                 else if FP32_IsNan(f2) then f1
                 else if FP32_IsZero(f1) and FP32_IsZero(f2)
                 then (if FP32_Sign(f1) then f2 else f1)
                 else if FP32_LessThan(f1, f2) then f2 else f1
         ; writeFPRS(rd, res)
         }

-----------------------------------
-- FMADD.S   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused (rs1*rs2)+rs3, rounded once
define FArith > FMADD_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_MulAdd_(r, FPRS(rs1), FPRS(rs2), FPRS(rs3))
                             ; accrueFlags(f)
                             ; when FP32_InfTimesZero(FPRS(rs1), FPRS(rs2)) do setFP_Invalid()
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMSUB.S   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused (rs1*rs2)-rs3, rounded once
define FArith > FMSUB_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_MulAdd_(r, FPRS(rs1), FPRS(rs2), FP32_Neg(FPRS(rs3)))
                             ; accrueFlags(f)
                             ; when FP32_InfTimesZero(FPRS(rs1), FPRS(rs2)) do setFP_Invalid()
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FNMADD.S   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused -(rs1*rs2)-rs3, rounded once; the product is
-- negated, not the result
define FArith > FNMADD_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_MulAdd_(r, FP32_Neg(FPRS(rs1)), FPRS(rs2), FP32_Neg(FPRS(rs3)))
                             ; accrueFlags(f)
                             ; when FP32_InfTimesZero(FPRS(rs1), FPRS(rs2)) do setFP_Invalid()
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FNMSUB.S   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused -(rs1*rs2)+rs3, rounded once; the product is
-- negated, not the result
define FArith > FNMSUB_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP32_MulAdd_(r, FP32_Neg(FPRS(rs1)), FPRS(rs2), FPRS(rs3))
                             ; accrueFlags(f)
                             ; when FP32_InfTimesZero(FPRS(rs1), FPRS(rs2)) do setFP_Invalid()
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-- Conversions

-----------------------------------
-- FCVT.S.W   rd, rs
-----------------------------------

define FConv > FCVT_S_W(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { i = [GPR(rs)<31:0>]::int
                             ; v = FP32_FromInt(r, i)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP32_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRS(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.S.WU  rd, rs
-----------------------------------

define FConv > FCVT_S_WU(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { i = [0`1 : GPR(rs)<31:0>]::int
                             ; v = FP32_FromInt(r, i)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP32_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRS(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.W.S   rd, rs
-----------------------------------

define FConv > FCVT_W_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRS(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP32_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                                     then [0n2 ** 31 - 1]
                                     else if inp == FP32_NegInf
                                     then -[0n2 ** 31]
                                     else if val > 2 ** 31 - 1
                                     then [0n2 ** 31 - 1]
                                     else if val < -2 ** 31
                                     then -[0n2 ** 31]
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP32_IsFinite(inp)
                                    or val > 2 ** 31 - 1 or val < -2 ** 31
                               then setFP_Invalid()
                               else when not FP32_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.WU.S  rd, rs
-----------------------------------

define FConv > FCVT_WU_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRS(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP32_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                                     then [0n2 ** 32 - 1]
                                     else if inp == FP32_NegInf
                                     then 0x0
                                     else if val > 2 ** 32 - 1
                                     then [0n2 ** 32 - 1]
                                     else if val < 0
                                     then 0x0
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP32_IsFinite(inp)
                                    or val > 2 ** 32 - 1 or val < 0
                               then setFP_Invalid()
                               else when not FP32_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, SignExtend(res::word))  -- sign-extended (ISA manual 6.1.7)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.S.L   rd, rs
-----------------------------------

define FConv > FCVT_S_L(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { i = [GPR(rs)]::int
                             ; v = FP32_FromInt(r, i)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP32_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRS(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.S.LU  rd, rs
-----------------------------------

define FConv > FCVT_S_LU(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { x = GPR(rs)
                             ; i = [0`1 : x]::int
                             -- FP32.fromInt of L3's SML runtime takes only signed 64-bit
                             -- values (above 2^63-1 it raises Fail).  The SML export
                             -- therefore converts x >= 2^63 as x/2, rounded to odd so
                             -- that every rounding mode gives the same result, times
                             -- 2.0 (exact); the HOL export converts x directly.
                             ; v = if PROVER_EXPORT or not x<63> then FP32_FromInt(r, i)
                                   else FP32_Mul(r, FP32_FromInt(r, [(x >>+ 1) || (x && 1)]::int),
                                                 0x40000000)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP32_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRS(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.L.S   rd, rs
-----------------------------------

define FConv > FCVT_L_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRS(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP32_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                                     then [0n2 ** 63 - 1]
                                     else if inp == FP32_NegInf
                                     then -[0n2 ** 63]
                                     else if val > 2 ** 63 - 1
                                     then [0n2 ** 63 - 1]
                                     else if val < -2 ** 63
                                     then -[0n2 ** 63]
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP32_IsFinite(inp)
                                    or val > 2 ** 63 - 1 or val < -2 ** 63
                               then setFP_Invalid()
                               else when not FP32_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.LU.S  rd, rs
-----------------------------------

define FConv > FCVT_LU_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRS(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP32_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                                     then [0n2 ** 64 - 1]
                                     else if inp == FP32_NegInf
                                     then 0x0
                                     else if val > 2 ** 64 - 1
                                     then [0n2 ** 64 - 1]
                                     else if val < 0
                                     then 0x0
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP32_IsFinite(inp)
                                    or val > 2 ** 64 - 1 or val < 0
                               then setFP_Invalid()
                               else when not FP32_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-- Sign injection

-----------------------------------
-- FSGNJ.S   rd, rs
-----------------------------------

define FConv > FSGNJ_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRS(rs1)
         ; f2 = FPRS(rs2)
         ; writeFPRS(rd, ([FP32_Sign(f2)]::bits(1)):f1<30:0>)
         }

-----------------------------------
-- FSGNJN.S  rd, rs
-----------------------------------

define FConv > FSGNJN_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRS(rs1)
         ; f2 = FPRS(rs2)
         ; writeFPRS(rd, ([!FP32_Sign(f2)]::bits(1)):f1<30:0>)
         }

-----------------------------------
-- FSGNJX.S  rd, rs
-----------------------------------

define FConv > FSGNJX_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRS(rs1)
         ; f2 = FPRS(rs2)
         ; writeFPRS(rd, ([FP32_Sign(f2)]::bits(1) ?? [FP32_Sign(f1)]::bits(1)) : f1<30:0>)
         }

-- Movement

-----------------------------------
-- FMV.X.S   rd, rs
-----------------------------------

define FConv > FMV_X_S(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else GPR(rd) <- SignExtend(FPRS_raw(rs))

-----------------------------------
-- FMV.S.X   rd, rs
-----------------------------------

define FConv > FMV_S_X(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else writeFPRS(rd, GPR(rs)<31:0>)

-- Comparisons

-----------------------------------
-- FEQ.S   rd, rs
-----------------------------------

define FArith > FEQ_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRS(rs1)
         ; f2  = FPRS(rs2)
         ; if FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP32_Compare(f1, f2)
                        { case FP_LT => 0x0
                          case FP_EQ => 0x1
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-----------------------------------
-- FLT.S   rd, rs
-----------------------------------

define FArith > FLT_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRS(rs1)
         ; f2  = FPRS(rs2)
         ; if   FP32_IsNan(f1) or FP32_IsNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP32_Compare(f1, f2)
                        { case FP_LT => 0x1
                          case FP_EQ => 0x0
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-----------------------------------
-- FLE.S   rd, rs
-----------------------------------

define FArith > FLE_S(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRS(rs1)
         ; f2  = FPRS(rs2)
         ; if   FP32_IsNan(f1) or FP32_IsNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP32_Compare(f1, f2)
                        { case FP_LT => 0x1
                          case FP_EQ => 0x1
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-- Classification

-----------------------------------
-- FCLASS.S  rd, rs
-----------------------------------

define FConv > FCLASS_S(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { var ret = 0x0`10
         ; val = FPRS(rs)
         ; ret<0> <- val == FP32_NegInf
         ; ret<1> <- FP32_Sign(val) and FP32_IsNormal(val)
         ; ret<2> <- FP32_Sign(val) and FP32_IsSubnormal(val)
         ; ret<3> <- val == FP32_NegZero
         ; ret<4> <- val == FP32_PosZero
         ; ret<5> <- !FP32_Sign(val) and FP32_IsSubnormal(val)
         ; ret<6> <- !FP32_Sign(val) and FP32_IsNormal(val)
         ; ret<7> <- val == FP32_PosInf
         ; ret<8> <- FP32_IsSignalingNan(val)
         ; ret<9> <- FP32_IsNan(val) and not FP32_IsSignalingNan(val)  -- any quiet NaN (ISA manual 6.1.9)
         ; writeRD(rd, ZeroExtend(ret))
         }

---------------------------------------------------------------------------
-- Floating Point Instructions (Double Precision)
---------------------------------------------------------------------------

-- Load/Store

-----------------------------------
-- FLD   rd, rs2, offs
-----------------------------------

define FPLoad > FLD(rd::reg, rs1::reg, offs::imm12) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<2:0> != 0
           then signalAddressException(Load_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Read)
                { case TR_Address(pAddr) => { val       = rawReadData(pAddr)
                                            ; writeFPRD(rd, val)  -- sets FS to Dirty (privileged manual 3.1.6.7)
                                            ; recordLoad(pAddr, val)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-----------------------------------
-- FSD   rs1, rs2, offs
-----------------------------------

define FPStore > FSD(rs1::reg, rs2::reg, offs::imm12) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; if vAddr<2:0> != 0
           then signalAddressException(Store_AMO_Misaligned, vAddr)
           else match dataAddr(vAddr, 8, PMP_Write)
                { case TR_Address(pAddr) => { data = FPRD(rs2)
                                            ; rawWriteData(pAddr, data, 8)
                                            ; recordStore(pAddr, data, 8)
                                            }
                  case TR_Fault(e)       => signalAddressException(e, vAddr)
                }
         }

-- Computational

-- Arithmetic accrues the flags of the IEEE operation (ISA manual 6.1.2);
-- tininess is detected after rounding (6.1.4) by SSE and by HOL's
-- Underflow_AfterRounding alike.

-----------------------------------
-- FADD.D   rd, rs1, rs2
-----------------------------------

define FArith > FADD_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_Add_(r, FPRD(rs1), FPRD(rs2))
                             ; accrueFlags(f)
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FSUB.D   rd, rs1, rs2
-----------------------------------

define FArith > FSUB_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_Sub_(r, FPRD(rs1), FPRD(rs2))
                             ; accrueFlags(f)
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMUL.D   rd, rs1, rs2
-----------------------------------

define FArith > FMUL_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_Mul_(r, FPRD(rs1), FPRD(rs2))
                             ; accrueFlags(f)
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FDIV.D   rd, rs1, rs2
-----------------------------------

define FArith > FDIV_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_Div_(r, FPRD(rs1), FPRD(rs2))
                             ; accrueFlags(f)
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FSQRT.D   rd, rs
-----------------------------------

define FArith > FSQRT_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { a = FPRD(rs)
                             ; (f, v) = FP64_Sqrt_(r, a)
                             -- no flag for a quiet NaN (IEEE 754-2008 6.2); HOL's
                             -- float_sqrt raises NV for a negative one
                             ; when not FP64_IsNan(a) or FP64_IsSignalingNan(a)
                               do accrueFlags(f)
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMIN.D    rd, rs1, rs2
-----------------------------------
define FArith > FMIN_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRD(rs1)
         ; f2 = FPRD(rs2)
         -- ISA manual 6.1.6: -0.0 < +0.0, a NaN operand gives the other operand (the
         -- canonical NaN if both are NaNs), and a signalling NaN raises NV
         ; when FP64_IsSignalingNan(f1) or FP64_IsSignalingNan(f2) do setFP_Invalid()
         ; res = if FP64_IsNan(f1) and FP64_IsNan(f2) then RV64_CanonicalNan
                 else if FP64_IsNan(f1) then f2
                 else if FP64_IsNan(f2) then f1
                 else if FP64_IsZero(f1) and FP64_IsZero(f2)
                 then (if FP64_Sign(f1) then f1 else f2)
                 else if FP64_LessThan(f1, f2) then f1 else f2
         ; writeFPRD(rd, res)
         }

-----------------------------------
-- FMAX.D    rd, rs1, rs2
-----------------------------------
define FArith > FMAX_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRD(rs1)
         ; f2 = FPRD(rs2)
         -- ISA manual 6.1.6: -0.0 < +0.0, a NaN operand gives the other operand (the
         -- canonical NaN if both are NaNs), and a signalling NaN raises NV
         ; when FP64_IsSignalingNan(f1) or FP64_IsSignalingNan(f2) do setFP_Invalid()
         ; res = if FP64_IsNan(f1) and FP64_IsNan(f2) then RV64_CanonicalNan
                 else if FP64_IsNan(f1) then f2
                 else if FP64_IsNan(f2) then f1
                 else if FP64_IsZero(f1) and FP64_IsZero(f2)
                 then (if FP64_Sign(f1) then f2 else f1)
                 else if FP64_LessThan(f1, f2) then f2 else f1
         ; writeFPRD(rd, res)
         }

-----------------------------------
-- FMADD.D   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused (rs1*rs2)+rs3, rounded once
define FArith > FMADD_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_MulAdd_(r, FPRD(rs1), FPRD(rs2), FPRD(rs3))
                             ; accrueFlags(f)
                             ; when FP64_InfTimesZero(FPRD(rs1), FPRD(rs2)) do setFP_Invalid()
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FMSUB.D   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused (rs1*rs2)-rs3, rounded once
define FArith > FMSUB_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_MulAdd_(r, FPRD(rs1), FPRD(rs2), FP64_Neg(FPRD(rs3)))
                             ; accrueFlags(f)
                             ; when FP64_InfTimesZero(FPRD(rs1), FPRD(rs2)) do setFP_Invalid()
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FNMADD.D   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused -(rs1*rs2)-rs3, rounded once; the product is
-- negated, not the result
define FArith > FNMADD_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_MulAdd_(r, FP64_Neg(FPRD(rs1)), FPRD(rs2), FP64_Neg(FPRD(rs3)))
                             ; accrueFlags(f)
                             ; when FP64_InfTimesZero(FPRD(rs1), FPRD(rs2)) do setFP_Invalid()
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FNMSUB.D   rd, rs1, rs2, rs3
-----------------------------------

-- ISA manual 6.1.6: fused -(rs1*rs2)+rs3, rounded once; the product is
-- negated, not the result
define FArith > FNMSUB_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_MulAdd_(r, FP64_Neg(FPRD(rs1)), FPRD(rs2), FPRD(rs3))
                             ; accrueFlags(f)
                             ; when FP64_InfTimesZero(FPRD(rs1), FPRD(rs2)) do setFP_Invalid()
                             ; writeFPRD(rd, canonD(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-- Conversions

-----------------------------------
-- FCVT.D.W   rd, rs
-----------------------------------

define FConv > FCVT_D_W(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else if validRounding(fprnd)  -- exact (ISA manual 6.2.5)
    then writeFPRD(rd, FP64_FromInt(roundTiesToEven, [GPR(rs)<31:0>]::int))
    else signalException(Illegal_Instr)

-----------------------------------
-- FCVT.D.WU  rd, rs
-----------------------------------

define FConv > FCVT_D_WU(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else if validRounding(fprnd)  -- exact (ISA manual 6.2.5)
    then writeFPRD(rd, FP64_FromInt(roundTiesToEven, [0`1 : GPR(rs)<31:0>]::int))
    else signalException(Illegal_Instr)

-----------------------------------
-- FCVT.W.D   rd, rs
-----------------------------------

define FConv > FCVT_W_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRD(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP64_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                                     then [0n2 ** 31 - 1]
                                     else if inp == FP64_NegInf
                                     then -[0n2 ** 31]
                                     else if val > 2 ** 31 - 1
                                     then [0n2 ** 31 - 1]
                                     else if val < -2 ** 31
                                     then -[0n2 ** 31]
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP64_IsFinite(inp)
                                    or val > 2 ** 31 - 1 or val < -2 ** 31
                               then setFP_Invalid()
                               else when not FP64_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.WU.D  rd, rs
-----------------------------------

define FConv > FCVT_WU_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRD(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP64_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                                     then [0n2 ** 32 - 1]
                                     else if inp == FP64_NegInf
                                     then 0x0
                                     else if val > 2 ** 32 - 1
                                     then [0n2 ** 32 - 1]
                                     else if val < 0
                                     then 0x0
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP64_IsFinite(inp)
                                    or val > 2 ** 32 - 1 or val < 0
                               then setFP_Invalid()
                               else when not FP64_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, SignExtend(res::word))  -- sign-extended (ISA manual 6.1.7)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.D.L   rd, rs
-----------------------------------

define FConv > FCVT_D_L(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { x = GPR(rs)
                             ; i = [x]::int
                             -- FP64.fromInt of L3's SML runtime (Poly/ML's
                             -- Real.fromLargeInt) rounds a value below -2^62 towards
                             -- the wrong infinity in RDN and RUP.  The SML export
                             -- therefore converts such an x as -(|x|/2, rounded to
                             -- odd) times 2.0 (exact), as in FCVT.S.LU; the HOL export
                             -- converts x directly.
                             ; v = if PROVER_EXPORT or x<63:62> != 0b10 then FP64_FromInt(r, i)
                                   else FP64_Mul(r, FP64_FromInt(r, -([((-x) >>+ 1) || ((-x) && 1)]::int)),
                                                 0x4000000000000000)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP64_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRD(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.D.LU  rd, rs
-----------------------------------

define FConv > FCVT_D_LU(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { i = [0`1 : GPR(rs)]::int
                             ; v = FP64_FromInt(r, i)
                             -- ISA manual 6.1.7: NX when the result is not exact
                             ; when FP64_ToInt(roundTowardZero, v) != Some(i)
                               do setFP_Inexact()
                             ; writeFPRD(rd, v)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.L.D   rd, rs
-----------------------------------

define FConv > FCVT_L_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRD(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP64_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                                     then [0n2 ** 63 - 1]
                                     else if inp == FP64_NegInf
                                     then -[0n2 ** 63]
                                     else if val > 2 ** 63 - 1
                                     then [0n2 ** 63 - 1]
                                     else if val < -2 ** 63
                                     then -[0n2 ** 63]
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP64_IsFinite(inp)
                                    or val > 2 ** 63 - 1 or val < -2 ** 63
                               then setFP_Invalid()
                               else when not FP64_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.LU.D  rd, rs
-----------------------------------

define FConv > FCVT_LU_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { inp = FPRD(rs)
                             -- None for a NaN or an infinity, which saturate below
                             -- (ISA manual 6.1.7, Table 29) before val is used
                             ; val = match FP64_ToInt(r, inp)
                                     { case Some(i) => i
                                       case None    => 0
                                     }
                             ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                                     then [0n2 ** 64 - 1]
                                     else if inp == FP64_NegInf
                                     then 0x0
                                     else if val > 2 ** 64 - 1
                                     then [0n2 ** 64 - 1]
                                     else if val < 0
                                     then 0x0
                                     else [val]
                             -- ISA manual 6.1.7: NV for a NaN, infinite or out-of-range
                             -- input, otherwise NX if the input is not an integer
                             ; if   not FP64_IsFinite(inp)
                                    or val > 2 ** 64 - 1 or val < 0
                               then setFP_Invalid()
                               else when not FP64_IsIntegral(inp) do setFP_Inexact()
                             ; writeRD(rd, res)
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.S.D  rd, rs
-----------------------------------

define FConv > FCVT_S_D(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { match round(fprnd)
           { case Some(r) => { (f, v) = FP64_ToFP32_(r, FPRD(rs))
                             ; accrueFlags(f)
                             ; writeFPRS(rd, canonS(v))
                             }
             case None    => signalException(Illegal_Instr)
           }
         }

-----------------------------------
-- FCVT.D.S  rd, rs
-----------------------------------

define FConv > FCVT_D_S(rd::reg, rs::reg, fprnd::fprnd) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else if validRounding(fprnd)  -- exact (ISA manual 6.2.5)
    then { a = FPRS(rs)
         -- only a signalling NaN raises a flag (NV)
         ; when FP32_IsSignalingNan(a) do setFP_Invalid()
         ; writeFPRD(rd, canonD(FP32_ToFP64(a)))
         }
    else signalException(Illegal_Instr)

-- Sign injection

-----------------------------------
-- FSGNJ.D  rd, rs
-----------------------------------

define FConv > FSGNJ_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRD(rs1)
         ; f2 = FPRD(rs2)
         ; writeFPRD(rd, ([FP64_Sign(f2)]::bits(1)):f1<62:0>)
         }

-----------------------------------
-- FSGNJN.D  rd, rs
-----------------------------------

define FConv > FSGNJN_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRD(rs1)
         ; f2 = FPRD(rs2)
         ; writeFPRD(rd, ([!FP64_Sign(f2)]::bits(1)):f1<62:0>)
         }

-----------------------------------
-- FSGNJX.D  rd, rs
-----------------------------------

define FConv > FSGNJX_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1 = FPRD(rs1)
         ; f2 = FPRD(rs2)
         ; writeFPRD(rd, ([FP64_Sign(f2)]::bits(1) ?? [FP64_Sign(f1)]::bits(1)) : f1<62:0>)
         }

-- Movement

-----------------------------------
-- FMV.X.D   rd, rs
-----------------------------------

define FConv > FMV_X_D(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else GPR(rd) <- SignExtend(FPRD(rs))

-----------------------------------
-- FMV.D.X   rd, rs
-----------------------------------

define FConv > FMV_D_X(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else writeFPRD(rd, GPR(rs))

-- Comparisons

-----------------------------------
-- FEQ.D   rd, rs
-----------------------------------

define FArith > FEQ_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRD(rs1)
         ; f2  = FPRD(rs2)
         ; if FP64_IsSignalingNan(f1) or FP64_IsSignalingNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP64_Compare(f1, f2)
                        { case FP_LT => 0x0
                          case FP_EQ => 0x1
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-----------------------------------
-- FLT.D   rd, rs
-----------------------------------

define FArith > FLT_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRD(rs1)
         ; f2  = FPRD(rs2)
         ; if   FP64_IsNan(f1) or FP64_IsNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP64_Compare(f1, f2)
                        { case FP_LT => 0x1
                          case FP_EQ => 0x0
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-----------------------------------
-- FLE.D   rd, rs
-----------------------------------

define FArith > FLE_D(rd::reg, rs1::reg, rs2::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { f1  = FPRD(rs1)
         ; f2  = FPRD(rs2)
         ; if   FP64_IsNan(f1) or FP64_IsNan(f2)
           then { writeRD(rd, 0x0)
                ; setFP_Invalid()
                }
           else { res = match FP64_Compare(f1, f2)
                        { case FP_LT => 0x1
                          case FP_EQ => 0x1
                          case FP_GT => 0x0
                          case FP_UN => 0x0
                        }
                ; writeRD(rd, res)
                }
         }

-- Classification

-----------------------------------
-- FCLASS.D  rd, rs
-----------------------------------

define FConv > FCLASS_D(rd::reg, rs::reg) =
    if not fpEnabled() then signalException(Illegal_Instr)
    else { var ret = 0x0`10
         ; val = FPRD(rs)
         ; ret<0> <- val == FP64_NegInf
         ; ret<1> <- FP64_Sign(val) and FP64_IsNormal(val)
         ; ret<2> <- FP64_Sign(val) and FP64_IsSubnormal(val)
         ; ret<3> <- val == FP64_NegZero
         ; ret<4> <- val == FP64_PosZero
         ; ret<5> <- !FP64_Sign(val) and FP64_IsSubnormal(val)
         ; ret<6> <- !FP64_Sign(val) and FP64_IsNormal(val)
         ; ret<7> <- val == FP64_PosInf
         ; ret<8> <- FP64_IsSignalingNan(val)
         ; ret<9> <- FP64_IsNan(val) and not FP64_IsSignalingNan(val)  -- any quiet NaN (ISA manual 6.1.9)
         ; writeRD(rd, ZeroExtend(ret))
         }


---------------------------------------------------------------------------
-- System Instructions
---------------------------------------------------------------------------

-----------------------------------
-- ECALL
-----------------------------------
define System > ECALL  = signalEnvCall()

-----------------------------------
-- EBREAK
-----------------------------------
-- The trap value is the address of the EBREAK (P §3.1.16 p.52, [D43]).
define System > EBREAK = signalAddressException(Breakpoint, PC)

-----------------------------------
-- MRET
-----------------------------------
-- MRET is legal only in M-mode (P §3.3.2 p.61).  Next does the return.
define System > MRET   =
    if curPrivilege() == Machine then NextFetch <- Some(Mret)
    else signalException(Illegal_Instr)

-----------------------------------
-- SRET
-----------------------------------
-- SRET is illegal in U-mode, and in S-mode while mstatus.TSR is set; it is
-- legal in M-mode whatever TSR is (P §3.3.2 p.61, §3.1.6.6 p.37).
define System > SRET   =
    match curPrivilege()
    { case User       => signalException(Illegal_Instr)
      case Supervisor => if MCSR.mstatus.TSR then signalException(Illegal_Instr)
                         else NextFetch <- Some(Sret)
      case Machine    => NextFetch <- Some(Sret)
    }

-----------------------------------
-- WFI
-----------------------------------
-- WFI does not wait (P §3.3.3 p.62 allows a no-op).  In S-mode with
-- mstatus.TW set it is illegal unless it completes within the time limit
-- (P §3.1.6.6 p.37), which is zero here: it completes at once iff an
-- interrupt is pending and enabled in mie, whatever mstatus.MIE,
-- mstatus.SIE and mideleg are (P §3.3.3 p.62, [S20]).  In U-mode it is
-- always illegal: with S-mode implemented, WFI is not available to U-mode
-- (P §3.1.6.6 p.37, §3.3.3 p.61, [D23]).
define System > WFI    =
    match curPrivilege()
    { case User       => signalException(Illegal_Instr)
      case Supervisor => when MCSR.mstatus.TW and (read_mip() && MCSR.&mie) == 0
                         do signalException(Illegal_Instr)
      case Machine    => nothing
    }

-- Control and Status Registers

bool checkCSROp(csr::imm12, rs1::reg, a::accessType) =
    is_CSR_defined(csr) and
    check_CSR_access(csrRW(csr), csrPR(csr), curPrivilege(), a) and
    check_CSR_conditions(csr, curPrivilege())

construct csrOp { CSR_Write, CSR_Set, CSR_Clear }

-- The six Zicsr instructions (U §4.2.1 p.62-63, Table 21).  f is the rs1
-- or uimm field and src the value it stands for.  CSRRW and CSRRWI always
-- write; the others write iff f is not 0, whatever the value of src, and
-- only a write needs a writable CSR.  Standard CSRs have no side effects
-- on reads (P §2.1 p.13), so the CSR is read also when rd = 0 ([D36]).
-- The CSRRS and CSRRC of mip see SEIP without the platform's line (P
-- §3.1.9 p.45).  Those of sip see the value read, line included, but
-- SEIP is read-only in sip (P §12.1.3 p.118), so the line never reaches
-- mip ([S21]).
unit accessCSR(op::csrOp, rd::reg, f::reg, src::regType, csr::creg) =
{ isWrite = op == CSR_Write or f != 0
; if checkCSROp(csr, f, if isWrite then Write else Read)
  then { old = CSR(csr)
       ; when isWrite
         do { base = if csr == 0x344 then (old && ~0x200) || (MCSR.&mip && 0x200)
                     else old
            ; writeCSR(csr, match op
                            { case CSR_Write => src
                              case CSR_Set   => base || src
                              case CSR_Clear => base && ~src
                            })
            }
       ; writeRD(rd, old)
       }
  else signalException(Illegal_Instr)
}

-----------------------------------
-- CSRRW  rd, rs1, csr
-----------------------------------
define System > CSRRW(rd::reg, rs1::reg, csr::imm12) =
    accessCSR(CSR_Write, rd, rs1, GPR(rs1), csr)

-----------------------------------
-- CSRRS  rd, rs1, csr
-----------------------------------
define System > CSRRS(rd::reg, rs1::reg, csr::imm12) =
    accessCSR(CSR_Set, rd, rs1, GPR(rs1), csr)

-----------------------------------
-- CSRRC  rd, rs1, csr
-----------------------------------
define System > CSRRC(rd::reg, rs1::reg, csr::imm12) =
    accessCSR(CSR_Clear, rd, rs1, GPR(rs1), csr)

-----------------------------------
-- CSRRWI rd, uimm, csr
-----------------------------------
define System > CSRRWI(rd::reg, zimm::reg, csr::imm12) =
    accessCSR(CSR_Write, rd, zimm, ZeroExtend(zimm), csr)

-----------------------------------
-- CSRRSI rd, uimm, csr
-----------------------------------
define System > CSRRSI(rd::reg, zimm::reg, csr::imm12) =
    accessCSR(CSR_Set, rd, zimm, ZeroExtend(zimm), csr)

-----------------------------------
-- CSRRCI rd, uimm, csr
-----------------------------------
define System > CSRRCI(rd::reg, zimm::reg, csr::imm12) =
    accessCSR(CSR_Clear, rd, zimm, ZeroExtend(zimm), csr)

-- Address translation cache flush

-----------------------------------
-- SFENCE.VMA rs1, rs2
-----------------------------------
-- The hart has no address-translation cache, so the fence has nothing to
-- do: every access uses the translation current when it is made, which is
-- always one that the fence allows (P §12.2.1 p.128, [S4]).
-- SFENCE.VMA is illegal in U-mode, and in S-mode while mstatus.TVM is set
-- (P §12.2.1 p.127, §3.1.6.6 p.37, [D46]).
define System > SFENCE_VMA(rs1::reg, rs2::reg) =
    match curPrivilege()
    { case User       => signalException(Illegal_Instr)
      case Supervisor => when MCSR.mstatus.TVM do signalException(Illegal_Instr)
      case Machine    => nothing
    }

-----------------------------------
-- Unsupported instructions
-----------------------------------
define UnknownInstruction =
    signalException(Illegal_Instr)

-----------------------------------
-- Internal pseudo-instructions
-----------------------------------

-- The argument is the value from the PC.

define Internal > FETCH_MISALIGNED(addr::regType) =
{ signalAddressException(Fetch_Misaligned, [addr])
; recordFetchException(addr)
}

-- e is the instruction page fault or access fault that fetchAddr gives.
define Internal > FETCH_FAULT(e::ExceptionType, addr::regType) =
{ signalAddressException(e, [addr])
; recordFetchException(addr)
}

define Run

--------------------------------------------------
-- Instruction fetch
--------------------------------------------------

construct FetchResult
{ F_Error   :: instruction
, F_Result  :: rawInstType
}

-- An instruction is fetched in 2-byte parcels, each translated and
-- checked by the PMP, the upper half of a 32-bit instruction only after
-- the lower one, since it can lie in another page or PMP region ([D59],
-- [S16]).  A parcel that fails raises the instruction page fault or
-- access fault of fetchAddr, with the virtual address of the parcel as the
-- trap value (P §3.1.16 p.52, §12.1.9 p.121).
FetchResult Fetch() =
{ vPC = PC
; if vPC<0> or (vPC<1> and not haveRVC())
  then F_Error(Internal(FETCH_MISALIGNED(vPC)))
  else match fetchAddr(vPC)
       { case TR_Address(pPC) =>
           match rawReadInst(pPC)
           { case Half(h) => { setupDelta(vPC, Half(h))
                             ; F_Result(Half(h))
                             }
             case Word(w) =>
               match fetchAddr(vPC + 2)
               { case TR_Address(pPC2) => { instw = Word(MEM8(pPC2 + 1) : MEM8(pPC2) : w<15:0>)
                                          ; setupDelta(vPC, instw)
                                          ; F_Result(instw)
                                          }
                 case TR_Fault(e)       => F_Error(Internal(FETCH_FAULT(e, vPC + 2)))
               }
           }
         case TR_Fault(e)      => F_Error(Internal(FETCH_FAULT(e, vPC)))
       }
}

---------------------------------------------------------------------------
-- Instruction decoding
---------------------------------------------------------------------------

-- helpers to assemble various immediates from their pieces
imm12 asImm12(imm12::bits(1), imm11::bits(1), immhi::bits(6), immlo::bits(4)) =
    imm12 : imm11 : immhi : immlo

imm20 asImm20(imm20::bits(1), immhi::bits(8), imm11::bits(1), immlo::bits(10)) =
    imm20 : immhi : imm11 : immlo

imm12 asSImm12(immhi::bits(7), immlo::bits(5)) =  immhi : immlo

instruction Decode(w::word) =
   match w
   { case 'i12 ihi rs2 rs1 000 ilo i11 11000 11' => Branch( BEQ(rs1, rs2, asImm12(i12, i11, ihi, ilo)))
     case 'i12 ihi rs2 rs1 001 ilo i11 11000 11' => Branch( BNE(rs1, rs2, asImm12(i12, i11, ihi, ilo)))
     case 'i12 ihi rs2 rs1 100 ilo i11 11000 11' => Branch( BLT(rs1, rs2, asImm12(i12, i11, ihi, ilo)))
     case 'i12 ihi rs2 rs1 101 ilo i11 11000 11' => Branch( BGE(rs1, rs2, asImm12(i12, i11, ihi, ilo)))
     case 'i12 ihi rs2 rs1 110 ilo i11 11000 11' => Branch(BLTU(rs1, rs2, asImm12(i12, i11, ihi, ilo)))
     case 'i12 ihi rs2 rs1 111 ilo i11 11000 11' => Branch(BGEU(rs1, rs2, asImm12(i12, i11, ihi, ilo)))

     case 'imm           rs1 000  rd 11001 11' => Branch( JALR(rd, rs1, imm))
     case 'i20 ilo i11 ihi        rd 11011 11' => Branch(  JAL(rd, asImm20(i20, ihi, i11, ilo)))

     case 'imm                    rd 01101 11' => ArithI(  LUI(rd, imm))
     case 'imm                    rd 00101 11' => ArithI(AUIPC(rd, imm))

     case 'imm           rs1 000  rd 00100 11' => ArithI( ADDI(rd, rs1, imm))
     case '000000  shamt rs1 001  rd 00100 11' =>  Shift( SLLI(rd, rs1, shamt))
     case 'imm           rs1 010  rd 00100 11' => ArithI( SLTI(rd, rs1, imm))
     case 'imm           rs1 011  rd 00100 11' => ArithI(SLTIU(rd, rs1, imm))
     case 'imm           rs1 100  rd 00100 11' => ArithI( XORI(rd, rs1, imm))
     case '000000  shamt rs1 101  rd 00100 11' =>  Shift( SRLI(rd, rs1, shamt))
     case '010000  shamt rs1 101  rd 00100 11' =>  Shift( SRAI(rd, rs1, shamt))
     case 'imm           rs1 110  rd 00100 11' => ArithI(  ORI(rd, rs1, imm))
     case 'imm           rs1 111  rd 00100 11' => ArithI( ANDI(rd, rs1, imm))

     case '0000000   rs2 rs1 000  rd 01100 11' => ArithR(  ADD(rd, rs1, rs2))
     case '0100000   rs2 rs1 000  rd 01100 11' => ArithR(  SUB(rd, rs1, rs2))
     case '0000000   rs2 rs1 001  rd 01100 11' =>  Shift(  SLL(rd, rs1, rs2))
     case '0000000   rs2 rs1 010  rd 01100 11' => ArithR(  SLT(rd, rs1, rs2))
     case '0000000   rs2 rs1 011  rd 01100 11' => ArithR( SLTU(rd, rs1, rs2))
     case '0000000   rs2 rs1 100  rd 01100 11' => ArithR(  XOR(rd, rs1, rs2))
     case '0000000   rs2 rs1 101  rd 01100 11' =>  Shift(  SRL(rd, rs1, rs2))
     case '0100000   rs2 rs1 101  rd 01100 11' =>  Shift(  SRA(rd, rs1, rs2))
     case '0000000   rs2 rs1 110  rd 01100 11' => ArithR(   OR(rd, rs1, rs2))
     case '0000000   rs2 rs1 111  rd 01100 11' => ArithR(  AND(rd, rs1, rs2))

     case 'imm           rs1 000  rd 00110 11' => ArithI(ADDIW(rd, rs1, imm))
     case '0000000 shamt rs1 001  rd 00110 11' =>  Shift(SLLIW(rd, rs1, shamt))
     case '0000000 shamt rs1 101  rd 00110 11' =>  Shift(SRLIW(rd, rs1, shamt))
     case '0100000 shamt rs1 101  rd 00110 11' =>  Shift(SRAIW(rd, rs1, shamt))

     case '0000000   rs2 rs1 000  rd 01110 11' => ArithR( ADDW(rd, rs1, rs2))
     case '0100000   rs2 rs1 000  rd 01110 11' => ArithR( SUBW(rd, rs1, rs2))
     case '0000000   rs2 rs1 001  rd 01110 11' =>  Shift( SLLW(rd, rs1, rs2))
     case '0000000   rs2 rs1 101  rd 01110 11' =>  Shift( SRLW(rd, rs1, rs2))
     case '0100000   rs2 rs1 101  rd 01110 11' =>  Shift( SRAW(rd, rs1, rs2))

     case '0000001   rs2 rs1 000  rd 01100 11' => MulDiv(   MUL(rd, rs1, rs2))
     case '0000001   rs2 rs1 001  rd 01100 11' => MulDiv(  MULH(rd, rs1, rs2))
     case '0000001   rs2 rs1 010  rd 01100 11' => MulDiv(MULHSU(rd, rs1, rs2))
     case '0000001   rs2 rs1 011  rd 01100 11' => MulDiv( MULHU(rd, rs1, rs2))
     case '0000001   rs2 rs1 100  rd 01100 11' => MulDiv(   DIV(rd, rs1, rs2))
     case '0000001   rs2 rs1 101  rd 01100 11' => MulDiv(  DIVU(rd, rs1, rs2))
     case '0000001   rs2 rs1 110  rd 01100 11' => MulDiv(   REM(rd, rs1, rs2))
     case '0000001   rs2 rs1 111  rd 01100 11' => MulDiv(  REMU(rd, rs1, rs2))

     case '0000001   rs2 rs1 000  rd 01110 11' => MulDiv(  MULW(rd, rs1, rs2))
     case '0000001   rs2 rs1 100  rd 01110 11' => MulDiv(  DIVW(rd, rs1, rs2))
     case '0000001   rs2 rs1 101  rd 01110 11' => MulDiv( DIVUW(rd, rs1, rs2))
     case '0000001   rs2 rs1 110  rd 01110 11' => MulDiv(  REMW(rd, rs1, rs2))
     case '0000001   rs2 rs1 111  rd 01110 11' => MulDiv( REMUW(rd, rs1, rs2))

     case 'imm           rs1 000  rd 00000 11' =>   Load(   LB(rd, rs1, imm))
     case 'imm           rs1 001  rd 00000 11' =>   Load(   LH(rd, rs1, imm))
     case 'imm           rs1 010  rd 00000 11' =>   Load(   LW(rd, rs1, imm))
     case 'imm           rs1 011  rd 00000 11' =>   Load(   LD(rd, rs1, imm))
     case 'imm           rs1 100  rd 00000 11' =>   Load(  LBU(rd, rs1, imm))
     case 'imm           rs1 101  rd 00000 11' =>   Load(  LHU(rd, rs1, imm))
     case 'imm           rs1 110  rd 00000 11' =>   Load(  LWU(rd, rs1, imm))

     case 'ihi       rs2 rs1 000 ilo 01000 11' =>  Store(   SB(rs1, rs2, asSImm12(ihi, ilo)))
     case 'ihi       rs2 rs1 001 ilo 01000 11' =>  Store(   SH(rs1, rs2, asSImm12(ihi, ilo)))
     case 'ihi       rs2 rs1 010 ilo 01000 11' =>  Store(   SW(rs1, rs2, asSImm12(ihi, ilo)))
     case 'ihi       rs2 rs1 011 ilo 01000 11' =>  Store(   SD(rs1, rs2, asSImm12(ihi, ilo)))

     case '_`4 pred succ rs1 000  rd 00011 11' =>        FENCE(rd, rs1, pred, succ)
     case 'imm           rs1 001  rd 00011 11' =>      FENCE_I(rd, rs1, imm)

     case 'rs3  00   rs2 rs1 frm  rd 10000 11' => FArith(  FMADD_S(rd, rs1, rs2, rs3, frm))
     case 'rs3  00   rs2 rs1 frm  rd 10001 11' => FArith(  FMSUB_S(rd, rs1, rs2, rs3, frm))
     case 'rs3  00   rs2 rs1 frm  rd 10010 11' => FArith( FNMSUB_S(rd, rs1, rs2, rs3, frm))
     case 'rs3  00   rs2 rs1 frm  rd 10011 11' => FArith( FNMADD_S(rd, rs1, rs2, rs3, frm))

     case '0000000   rs2 rs1 frm  rd 10100 11' => FArith(   FADD_S(rd, rs1, rs2, frm))
     case '0000100   rs2 rs1 frm  rd 10100 11' => FArith(   FSUB_S(rd, rs1, rs2, frm))
     case '0001000   rs2 rs1 frm  rd 10100 11' => FArith(   FMUL_S(rd, rs1, rs2, frm))
     case '0001100   rs2 rs1 frm  rd 10100 11' => FArith(   FDIV_S(rd, rs1, rs2, frm))
     case '0101100 00000 rs1 frm  rd 10100 11' => FArith(  FSQRT_S(rd, rs1, frm))

     case '0010100   rs2 rs1 000  rd 10100 11' => FArith(  FMIN_S(rd,  rs1, rs2))
     case '0010100   rs2 rs1 001  rd 10100 11' => FArith(  FMAX_S(rd,  rs1, rs2))
     case '1010000   rs2 rs1 010  rd 10100 11' => FArith(   FEQ_S(rd,  rs1, rs2))
     case '1010000   rs2 rs1 001  rd 10100 11' => FArith(   FLT_S(rd,  rs1, rs2))
     case '1010000   rs2 rs1 000  rd 10100 11' => FArith(   FLE_S(rd,  rs1, rs2))

     case '0010000   rs2 rs1 000  rd 10100 11' => FConv (  FSGNJ_S(rd,  rs1, rs2))
     case '0010000   rs2 rs1 001  rd 10100 11' => FConv ( FSGNJN_S(rd,  rs1, rs2))
     case '0010000   rs2 rs1 010  rd 10100 11' => FConv ( FSGNJX_S(rd,  rs1, rs2))

     case '1100000 00000 rs1 frm  rd 10100 11' => FConv(  FCVT_W_S(rd, rs1, frm))
     case '1100000 00001 rs1 frm  rd 10100 11' => FConv( FCVT_WU_S(rd, rs1, frm))
     case '1110000 00000 rs1 000  rd 10100 11' => FConv(   FMV_X_S(rd, rs1))
     case '1110000 00000 rs1 001  rd 10100 11' => FConv(  FCLASS_S(rd, rs1))
     case '1101000 00000 rs1 frm  rd 10100 11' => FConv(  FCVT_S_W(rd, rs1, frm))
     case '1101000 00001 rs1 frm  rd 10100 11' => FConv( FCVT_S_WU(rd, rs1, frm))
     case '1111000 00000 rs1 000  rd 10100 11' => FConv(   FMV_S_X(rd, rs1))

     case 'rs3  01   rs2 rs1 frm  rd 10000 11' => FArith(  FMADD_D(rd, rs1, rs2, rs3, frm))
     case 'rs3  01   rs2 rs1 frm  rd 10001 11' => FArith(  FMSUB_D(rd, rs1, rs2, rs3, frm))
     case 'rs3  01   rs2 rs1 frm  rd 10010 11' => FArith( FNMSUB_D(rd, rs1, rs2, rs3, frm))
     case 'rs3  01   rs2 rs1 frm  rd 10011 11' => FArith( FNMADD_D(rd, rs1, rs2, rs3, frm))

     case '0000001   rs2 rs1 frm  rd 10100 11' => FArith(   FADD_D(rd, rs1, rs2, frm))
     case '0000101   rs2 rs1 frm  rd 10100 11' => FArith(   FSUB_D(rd, rs1, rs2, frm))
     case '0001001   rs2 rs1 frm  rd 10100 11' => FArith(   FMUL_D(rd, rs1, rs2, frm))
     case '0001101   rs2 rs1 frm  rd 10100 11' => FArith(   FDIV_D(rd, rs1, rs2, frm))
     case '0101101 00000 rs1 frm  rd 10100 11' => FArith(  FSQRT_D(rd, rs1, frm))

     case '0010101   rs2 rs1 000  rd 10100 11' => FArith(  FMIN_D(rd,  rs1, rs2))
     case '0010101   rs2 rs1 001  rd 10100 11' => FArith(  FMAX_D(rd,  rs1, rs2))
     case '1010001   rs2 rs1 010  rd 10100 11' => FArith(   FEQ_D(rd,  rs1, rs2))
     case '1010001   rs2 rs1 001  rd 10100 11' => FArith(   FLT_D(rd,  rs1, rs2))
     case '1010001   rs2 rs1 000  rd 10100 11' => FArith(   FLE_D(rd,  rs1, rs2))

     case '0010001   rs2 rs1 000  rd 10100 11' => FConv (  FSGNJ_D(rd,  rs1, rs2))
     case '0010001   rs2 rs1 001  rd 10100 11' => FConv ( FSGNJN_D(rd,  rs1, rs2))
     case '0010001   rs2 rs1 010  rd 10100 11' => FConv ( FSGNJX_D(rd,  rs1, rs2))

     case '1100001 00000 rs1 frm  rd 10100 11' => FConv(  FCVT_W_D(rd, rs1, frm))
     case '1100001 00001 rs1 frm  rd 10100 11' => FConv( FCVT_WU_D(rd, rs1, frm))
     case '1110001 00000 rs1 001  rd 10100 11' => FConv(  FCLASS_D(rd, rs1))
     case '1101001 00000 rs1 frm  rd 10100 11' => FConv(  FCVT_D_W(rd, rs1, frm))
     case '1101001 00001 rs1 frm  rd 10100 11' => FConv( FCVT_D_WU(rd, rs1, frm))

     case '1100000 00010 rs1 frm  rd 10100 11' => FConv(  FCVT_L_S(rd, rs1, frm))
     case '1100000 00011 rs1 frm  rd 10100 11' => FConv( FCVT_LU_S(rd, rs1, frm))
     case '1101000 00010 rs1 frm  rd 10100 11' => FConv(  FCVT_S_L(rd, rs1, frm))
     case '1101000 00011 rs1 frm  rd 10100 11' => FConv( FCVT_S_LU(rd, rs1, frm))

     case '1100001 00010 rs1 frm  rd 10100 11' => FConv(  FCVT_L_D(rd, rs1, frm))
     case '1100001 00011 rs1 frm  rd 10100 11' => FConv( FCVT_LU_D(rd, rs1, frm))
     case '1101001 00010 rs1 frm  rd 10100 11' => FConv(  FCVT_D_L(rd, rs1, frm))
     case '1101001 00011 rs1 frm  rd 10100 11' => FConv( FCVT_D_LU(rd, rs1, frm))
     case '1110001 00000 rs1 000  rd 10100 11' => FConv(   FMV_X_D(rd, rs1))
     case '1111001 00000 rs1 000  rd 10100 11' => FConv(   FMV_D_X(rd, rs1))

     case '0100000 00001 rs1 frm  rd 10100 11' => FConv(  FCVT_S_D(rd, rs1, frm))
     case '0100001 00000 rs1 frm  rd 10100 11' => FConv(  FCVT_D_S(rd, rs1, frm))

     case 'imm           rs1 010  rd 00001 11' => FPLoad(  FLW(rd, rs1, imm))
     case 'imm           rs1 011  rd 00001 11' => FPLoad(  FLD(rd, rs1, imm))
     case 'ihi       rs2 rs1 010 ilo 01001 11' => FPStore( FSW(rs1, rs2, asSImm12(ihi, ilo)))
     case 'ihi       rs2 rs1 011 ilo 01001 11' => FPStore( FSD(rs1, rs2, asSImm12(ihi, ilo)))

     case '00010 aq rl 00000  rs1 010 rd 01011 11' => AMO(     LR_W(aq, rl, rd, rs1))
     case '00010 aq rl 00000  rs1 011 rd 01011 11' => AMO(     LR_D(aq, rl, rd, rs1))
     case '00011 aq rl rs2    rs1 010 rd 01011 11' => AMO(     SC_W(aq, rl, rd, rs1, rs2))
     case '00011 aq rl rs2    rs1 011 rd 01011 11' => AMO(     SC_D(aq, rl, rd, rs1, rs2))

     case '00001 aq rl rs2    rs1 010 rd 01011 11' => AMO(AMOSWAP_W(aq, rl, rd, rs1, rs2))
     case '00000 aq rl rs2    rs1 010 rd 01011 11' => AMO( AMOADD_W(aq, rl, rd, rs1, rs2))
     case '00100 aq rl rs2    rs1 010 rd 01011 11' => AMO( AMOXOR_W(aq, rl, rd, rs1, rs2))
     case '01100 aq rl rs2    rs1 010 rd 01011 11' => AMO( AMOAND_W(aq, rl, rd, rs1, rs2))
     case '01000 aq rl rs2    rs1 010 rd 01011 11' => AMO(  AMOOR_W(aq, rl, rd, rs1, rs2))
     case '10000 aq rl rs2    rs1 010 rd 01011 11' => AMO( AMOMIN_W(aq, rl, rd, rs1, rs2))
     case '10100 aq rl rs2    rs1 010 rd 01011 11' => AMO( AMOMAX_W(aq, rl, rd, rs1, rs2))
     case '11000 aq rl rs2    rs1 010 rd 01011 11' => AMO(AMOMINU_W(aq, rl, rd, rs1, rs2))
     case '11100 aq rl rs2    rs1 010 rd 01011 11' => AMO(AMOMAXU_W(aq, rl, rd, rs1, rs2))

     case '00001 aq rl rs2    rs1 011 rd 01011 11' => AMO(AMOSWAP_D(aq, rl, rd, rs1, rs2))
     case '00000 aq rl rs2    rs1 011 rd 01011 11' => AMO( AMOADD_D(aq, rl, rd, rs1, rs2))
     case '00100 aq rl rs2    rs1 011 rd 01011 11' => AMO( AMOXOR_D(aq, rl, rd, rs1, rs2))
     case '01100 aq rl rs2    rs1 011 rd 01011 11' => AMO( AMOAND_D(aq, rl, rd, rs1, rs2))
     case '01000 aq rl rs2    rs1 011 rd 01011 11' => AMO(  AMOOR_D(aq, rl, rd, rs1, rs2))
     case '10000 aq rl rs2    rs1 011 rd 01011 11' => AMO( AMOMIN_D(aq, rl, rd, rs1, rs2))
     case '10100 aq rl rs2    rs1 011 rd 01011 11' => AMO( AMOMAX_D(aq, rl, rd, rs1, rs2))
     case '11000 aq rl rs2    rs1 011 rd 01011 11' => AMO(AMOMINU_D(aq, rl, rd, rs1, rs2))
     case '11100 aq rl rs2    rs1 011 rd 01011 11' => AMO(AMOMAXU_D(aq, rl, rd, rs1, rs2))

     case 'csr                rs1 001 rd 11100 11' => System( CSRRW(rd, rs1, csr))
     case 'csr                rs1 010 rd 11100 11' => System( CSRRS(rd, rs1, csr))
     case 'csr                rs1 011 rd 11100 11' => System( CSRRC(rd, rs1, csr))
     case 'csr                imm 101 rd 11100 11' => System(CSRRWI(rd, imm, csr))
     case 'csr                imm 110 rd 11100 11' => System(CSRRSI(rd, imm, csr))
     case 'csr                imm 111 rd 11100 11' => System(CSRRCI(rd, imm, csr))

     case '000000000000  00000 000 00000 11100 11' => System( ECALL)
     case '000000000001  00000 000 00000 11100 11' => System(EBREAK)
     case '000100000010  00000 000 00000 11100 11' => System(  SRET)
     case '001100000010  00000 000 00000 11100 11' => System(  MRET)
     case '000100000101  00000 000 00000 11100 11' => System(   WFI)

     case '0001001  rs2  rs1 000 00000 11100 11' => System(SFENCE_VMA(rs1, rs2))

     -- unsupported instructions
     case _                                        => UnknownInstruction
   }

-- instruction printer

string imm(i::bits(N))  = "0x" : [i]
string instr(o::string) = PadRight(#" ", 12, o)

string amotype(aq::amo, rl::amo) =
    match aq, rl
    { case 0, 0 => ""
      case 1, 0 => ".aq"
      case 0, 1 => ".rl"
      case 1, 1 => ".sc"
    }

string pRtype(o::string, rd::reg, rs1::reg, rs2::reg) =
    instr(o) : " " : reg(rd) : ", " : reg(rs1) : ", " : reg(rs2)

string pARtype(o::string, aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
    pRtype([o : amotype(aq, rl)], rd, rs1, rs2)

string pLRtype(o::string, aq::amo, rl::amo, rd::reg, rs1::reg) =
    instr([o : amotype(aq, rl)]) : " " : reg(rd) : ", " : reg(rs1)

string pItype(o::string, rd::reg, rs1::reg, i::bits(N)) =
    instr(o) : " " : reg(rd) : ", " : reg(rs1) : ", " : imm(i)

string pCSRtype(o::string, rd::reg, rs1::reg, csr::creg) =
    instr(o) : " " : reg(rd) : ", " : reg(rs1) : ", " : csrName(csr)

string pCSRItype(o::string, rd::reg, i::bits(N), csr::creg) =
    instr(o) : " " : reg(rd) : ", " : imm(i) : ", " : csrName(csr)

string pStype(o::string, rs1::reg, rs2::reg, i::bits(N)) =
    instr(o) : " " : reg(rs2) : ", " : reg(rs1) : ", " : imm(i)

string pSBtype(o::string, rs1::reg, rs2::reg, i::bits(N)) =
    instr(o) : " " : reg(rs1) : ", " : reg(rs2) : ", " : imm(i<<1)

string pUtype(o::string, rd::reg, i::bits(N)) =
    instr(o) : " " : reg(rd) : ", " : imm(i)

string pUJtype(o::string, rd::reg, i::bits(N)) =
    instr(o) : " " : reg(rd) : ", " : imm(i<<1)

string pN0type(o::string) =
    instr(o)

string pN1type(o::string, r::reg) =
    instr(o) : " " : reg(r)

string pN2type(o::string, r1::reg, r2::reg) =
    instr(o) : " " : reg(r1) : ", " : reg(r2)

string pFRtype(o::string, rd::reg, rs1::reg, rs2::reg) =
    instr(o) : " " : fpreg(rd) : ", " : fpreg(rs1) : ", " : fpreg(rs2)

string pFR1type(o::string, rd::reg, rs::reg) =
    instr(o) : " " : fpreg(rd) : ", " : fpreg(rs)

string pFR3type(o::string, rd::reg, rs1::reg, rs2::reg, rs3::reg) =
    instr(o) : " " : fpreg(rd) : ", " : fpreg(rs1) : ", " : fpreg(rs2) : ", " : fpreg(rs3)

string pFItype(o::string, rd::reg, rs1::reg, i::bits(N)) =
    instr(o) : " " : fpreg(rd) : ", " : reg(rs1) : ", " : imm(i)

string pFStype(o::string, rs1::reg, rs2::reg, i::bits(N)) =
    instr(o) : " " : fpreg(rs2) : ", " : reg(rs1) : ", " : imm(i)

string pCFItype(o::string, rd::reg, rs::reg) =
    instr(o) : " " : fpreg(rd) : ", " : reg(rs)

string pCIFtype(o::string, rd::reg, rs::reg) =
    instr(o) : " " : reg(rd) : ", " : fpreg(rs)

string instructionToString(i::instruction) =
   match i
   { case Branch(  BEQ(rs1, rs2, imm))      => pSBtype("BEQ",  rs1, rs2, imm)
     case Branch(  BNE(rs1, rs2, imm))      => pSBtype("BNE",  rs1, rs2, imm)
     case Branch(  BLT(rs1, rs2, imm))      => pSBtype("BLT",  rs1, rs2, imm)
     case Branch(  BGE(rs1, rs2, imm))      => pSBtype("BGE",  rs1, rs2, imm)
     case Branch( BLTU(rs1, rs2, imm))      => pSBtype("BLTU", rs1, rs2, imm)
     case Branch( BGEU(rs1, rs2, imm))      => pSBtype("BGEU", rs1, rs2, imm)

     case Branch( JALR(rd, rs1, imm))       => pItype("JALR",  rd, rs1, imm)
     case Branch(  JAL(rd, imm))            => pUJtype("JAL",  rd, imm)

     case ArithI(  LUI(rd, imm))            => pUtype("LUI",   rd, imm)
     case ArithI(AUIPC(rd, imm))            => pUtype("AUIPC", rd, imm)

     case ArithI( ADDI(rd, rs1, imm))       => pItype("ADDI",  rd, rs1, imm)
     case  Shift( SLLI(rd, rs1, imm))       => pItype("SLLI",  rd, rs1, imm)
     case ArithI( SLTI(rd, rs1, imm))       => pItype("SLTI",  rd, rs1, imm)
     case ArithI(SLTIU(rd, rs1, imm))       => pItype("SLTIU", rd, rs1, imm)
     case ArithI( XORI(rd, rs1, imm))       => pItype("XORI",  rd, rs1, imm)
     case  Shift( SRLI(rd, rs1, imm))       => pItype("SRLI",  rd, rs1, imm)
     case  Shift( SRAI(rd, rs1, imm))       => pItype("SRAI",  rd, rs1, imm)
     case ArithI(  ORI(rd, rs1, imm))       => pItype("ORI",   rd, rs1, imm)
     case ArithI( ANDI(rd, rs1, imm))       => pItype("ANDI",  rd, rs1, imm)

     case ArithR(  ADD(rd, rs1, rs2))       => pRtype("ADD",   rd, rs1, rs2)
     case ArithR(  SUB(rd, rs1, rs2))       => pRtype("SUB",   rd, rs1, rs2)
     case  Shift(  SLL(rd, rs1, rs2))       => pRtype("SLL",   rd, rs1, rs2)
     case ArithR(  SLT(rd, rs1, rs2))       => pRtype("SLT",   rd, rs1, rs2)
     case ArithR( SLTU(rd, rs1, rs2))       => pRtype("SLTU",  rd, rs1, rs2)
     case ArithR(  XOR(rd, rs1, rs2))       => pRtype("XOR",   rd, rs1, rs2)
     case  Shift(  SRL(rd, rs1, rs2))       => pRtype("SRL",   rd, rs1, rs2)
     case  Shift(  SRA(rd, rs1, rs2))       => pRtype("SRA",   rd, rs1, rs2)
     case ArithR(   OR(rd, rs1, rs2))       => pRtype("OR",    rd, rs1, rs2)
     case ArithR(  AND(rd, rs1, rs2))       => pRtype("AND",   rd, rs1, rs2)

     case ArithI(ADDIW(rd, rs1, imm))       => pItype("ADDIW", rd, rs1, imm)
     case  Shift(SLLIW(rd, rs1, imm))       => pItype("SLLIW", rd, rs1, imm)
     case  Shift(SRLIW(rd, rs1, imm))       => pItype("SRLIW", rd, rs1, imm)
     case  Shift(SRAIW(rd, rs1, imm))       => pItype("SRAIW", rd, rs1, imm)

     case ArithR( ADDW(rd, rs1, rs2))       => pRtype("ADDW",  rd, rs1, rs2)
     case ArithR( SUBW(rd, rs1, rs2))       => pRtype("SUBW",  rd, rs1, rs2)
     case  Shift( SLLW(rd, rs1, rs2))       => pRtype("SLLW",  rd, rs1, rs2)
     case  Shift( SRLW(rd, rs1, rs2))       => pRtype("SRLW",  rd, rs1, rs2)
     case  Shift( SRAW(rd, rs1, rs2))       => pRtype("SRAW",  rd, rs1, rs2)

     case MulDiv(    MUL(rd, rs1, rs2))     => pRtype("MUL",     rd, rs1, rs2)
     case MulDiv(   MULH(rd, rs1, rs2))     => pRtype("MULH",    rd, rs1, rs2)
     case MulDiv( MULHSU(rd, rs1, rs2))     => pRtype("MULHSU",  rd, rs1, rs2)
     case MulDiv(  MULHU(rd, rs1, rs2))     => pRtype("MULHU",   rd, rs1, rs2)
     case MulDiv(    DIV(rd, rs1, rs2))     => pRtype("DIV",     rd, rs1, rs2)
     case MulDiv(   DIVU(rd, rs1, rs2))     => pRtype("DIVU",    rd, rs1, rs2)
     case MulDiv(    REM(rd, rs1, rs2))     => pRtype("REM",     rd, rs1, rs2)
     case MulDiv(   REMU(rd, rs1, rs2))     => pRtype("REMU",    rd, rs1, rs2)

     case MulDiv(   MULW(rd, rs1, rs2))     => pRtype("MULW",    rd, rs1, rs2)
     case MulDiv(   DIVW(rd, rs1, rs2))     => pRtype("DIVW",    rd, rs1, rs2)
     case MulDiv(  DIVUW(rd, rs1, rs2))     => pRtype("DIVUW",   rd, rs1, rs2)
     case MulDiv(   REMW(rd, rs1, rs2))     => pRtype("REMW",    rd, rs1, rs2)
     case MulDiv(  REMUW(rd, rs1, rs2))     => pRtype("REMUW",   rd, rs1, rs2)

     case   Load(   LB(rd, rs1, imm))       => pItype("LB",    rd, rs1, imm)
     case   Load(   LH(rd, rs1, imm))       => pItype("LH",    rd, rs1, imm)
     case   Load(   LW(rd, rs1, imm))       => pItype("LW",    rd, rs1, imm)
     case   Load(   LD(rd, rs1, imm))       => pItype("LD",    rd, rs1, imm)
     case   Load(  LBU(rd, rs1, imm))       => pItype("LBU",   rd, rs1, imm)
     case   Load(  LHU(rd, rs1, imm))       => pItype("LHU",   rd, rs1, imm)
     case   Load(  LWU(rd, rs1, imm))       => pItype("LWU",   rd, rs1, imm)

     case  Store(   SB(rs1, rs2, imm))      => pStype("SB",    rs1, rs2, imm)
     case  Store(   SH(rs1, rs2, imm))      => pStype("SH",    rs1, rs2, imm)
     case  Store(   SW(rs1, rs2, imm))      => pStype("SW",    rs1, rs2, imm)
     case  Store(   SD(rs1, rs2, imm))      => pStype("SD",    rs1, rs2, imm)

     case   FENCE(rd, rs1, pred, succ)      => pN0type("FENCE")
     case FENCE_I(rd, rs1, imm)             => pN0type("FENCE.I")

     case FArith(  FADD_S(rd, rs1, rs2, frm)) => pFRtype("FADD.S", rd, rs1, rs2)
     case FArith(  FSUB_S(rd, rs1, rs2, frm)) => pFRtype("FSUB.S", rd, rs1, rs2)
     case FArith(  FMUL_S(rd, rs1, rs2, frm)) => pFRtype("FMUL.S", rd, rs1, rs2)
     case FArith(  FDIV_S(rd, rs1, rs2, frm)) => pFRtype("FDIV.S", rd, rs1, rs2)

     case FArith( FSQRT_S(rd, rs, frm))       => pFR1type("FSQRT.S", rd, rs)

     case FArith(  FMIN_S(rd, rs1, rs2))      => pFRtype("FMIN.S", rd, rs1, rs2)
     case FArith(  FMAX_S(rd, rs1, rs2))      => pFRtype("FMAX.S", rd, rs1, rs2)
     case FArith(   FEQ_S(rd, rs1, rs2))      => pFRtype("FEQ.S",  rd, rs1, rs2)
     case FArith(   FLT_S(rd, rs1, rs2))      => pFRtype("FLT.S",  rd, rs1, rs2)
     case FArith(   FLE_S(rd, rs1, rs2))      => pFRtype("FLE.S",  rd, rs1, rs2)

     case FArith( FMADD_S(rd, rs1, rs2, rs3, frm)) => pFR3type("FMADD.S",  rd, rs1, rs2, rs3)
     case FArith( FMSUB_S(rd, rs1, rs2, rs3, frm)) => pFR3type("FMSUB.S",  rd, rs1, rs2, rs3)
     case FArith(FNMADD_S(rd, rs1, rs2, rs3, frm)) => pFR3type("FNMADD.S", rd, rs1, rs2, rs3)
     case FArith(FNMSUB_S(rd, rs1, rs2, rs3, frm)) => pFR3type("FNMSUB.S", rd, rs1, rs2, rs3)

     case FArith(  FADD_D(rd, rs1, rs2, frm)) => pFRtype("FADD.D", rd, rs1, rs2)
     case FArith(  FSUB_D(rd, rs1, rs2, frm)) => pFRtype("FSUB.D", rd, rs1, rs2)
     case FArith(  FMUL_D(rd, rs1, rs2, frm)) => pFRtype("FMUL.D", rd, rs1, rs2)
     case FArith(  FDIV_D(rd, rs1, rs2, frm)) => pFRtype("FDIV.D", rd, rs1, rs2)

     case FArith( FSQRT_D(rd, rs, frm))       => pFR1type("FSQRT.D", rd, rs)

     case FArith(  FMIN_D(rd, rs1, rs2))      => pFRtype("FMIN.D", rd, rs1, rs2)
     case FArith(  FMAX_D(rd, rs1, rs2))      => pFRtype("FMAX.D", rd, rs1, rs2)
     case FArith(   FEQ_D(rd, rs1, rs2))      => pFRtype("FEQ.D",  rd, rs1, rs2)
     case FArith(   FLT_D(rd, rs1, rs2))      => pFRtype("FLT.D",  rd, rs1, rs2)
     case FArith(   FLE_D(rd, rs1, rs2))      => pFRtype("FLE.D",  rd, rs1, rs2)

     case FArith( FMADD_D(rd, rs1, rs2, rs3, frm)) => pFR3type("FMADD.D",  rd, rs1, rs2, rs3)
     case FArith( FMSUB_D(rd, rs1, rs2, rs3, frm)) => pFR3type("FMSUB.D",  rd, rs1, rs2, rs3)
     case FArith(FNMADD_D(rd, rs1, rs2, rs3, frm)) => pFR3type("FNMADD.D", rd, rs1, rs2, rs3)
     case FArith(FNMSUB_D(rd, rs1, rs2, rs3, frm)) => pFR3type("FNMSUB.D", rd, rs1, rs2, rs3)

     case FConv(  FSGNJ_S(rd, rs1, rs2))      => pFRtype("FSGNJ.S",    rd, rs1, rs2)
     case FConv( FSGNJN_S(rd, rs1, rs2))      => pFRtype("FSGNJN.S",   rd, rs1, rs2)
     case FConv( FSGNJX_S(rd, rs1, rs2))      => pFRtype("FSGNJX.S",   rd, rs1, rs2)

     case FConv( FCVT_W_S(rd, rs, frm))       => pCIFtype("FCVT.W.S",  rd, rs)
     case FConv(FCVT_WU_S(rd, rs, frm))       => pCIFtype("FCVT.WU.S", rd, rs)
     case FConv(  FMV_X_S(rd, rs))            => pCIFtype("FMV.X.S",   rd, rs)
     case FConv( FCLASS_S(rd, rs))            => pCIFtype("FCLASS.S",  rd, rs)
     case FConv( FCVT_S_W(rd, rs, frm))       => pCFItype("FCVT.S.W",  rd, rs)
     case FConv(FCVT_S_WU(rd, rs, frm))       => pCFItype("FCVT.S.WU", rd, rs)
     case FConv(  FMV_S_X(rd, rs))            => pCFItype("FMV.S.X",   rd, rs)

     case FConv(  FSGNJ_D(rd, rs1, rs2))      => pFRtype("FSGNJ.D",    rd, rs1, rs2)
     case FConv( FSGNJN_D(rd, rs1, rs2))      => pFRtype("FSGNJN.D",   rd, rs1, rs2)
     case FConv( FSGNJX_D(rd, rs1, rs2))      => pFRtype("FSGNJX.D",   rd, rs1, rs2)

     case FConv( FCVT_W_D(rd, rs, frm))       => pCIFtype("FCVT.W.D",  rd, rs)
     case FConv(FCVT_WU_D(rd, rs, frm))       => pCIFtype("FCVT.WU.D", rd, rs)
     case FConv( FCLASS_D(rd, rs))            => pCIFtype("FCLASS.D",  rd, rs)
     case FConv( FCVT_D_W(rd, rs, frm))       => pCFItype("FCVT.D.W",  rd, rs)
     case FConv(FCVT_D_WU(rd, rs, frm))       => pCFItype("FCVT.D.WU", rd, rs)

     case FConv( FCVT_L_S(rd, rs, frm))       => pCIFtype("FCVT.L.S",  rd, rs)
     case FConv(FCVT_LU_S(rd, rs, frm))       => pCIFtype("FCVT.LU.S", rd, rs)
     case FConv( FCVT_S_L(rd, rs, frm))       => pCFItype("FCVT.S.L",  rd, rs)
     case FConv(FCVT_S_LU(rd, rs, frm))       => pCFItype("FCVT.S.LU", rd, rs)
     case FConv( FCVT_L_D(rd, rs, frm))       => pCIFtype("FCVT.L.D",  rd, rs)
     case FConv(FCVT_LU_D(rd, rs, frm))       => pCIFtype("FCVT.LU.D", rd, rs)
     case FConv(  FMV_X_D(rd, rs))            => pCIFtype("FMV.X.D",   rd, rs)
     case FConv( FCVT_D_L(rd, rs, frm))       => pCFItype("FCVT.D.L",  rd, rs)
     case FConv(FCVT_D_LU(rd, rs, frm))       => pCFItype("FCVT.D.LU", rd, rs)
     case FConv(  FMV_D_X(rd, rs))            => pCFItype("FMV.D.X",   rd, rs)
     case FConv( FCVT_D_S(rd, rs, frm))       => pCFItype("FCVT.D.S",  rd, rs)
     case FConv( FCVT_S_D(rd, rs, frm))       => pCFItype("FCVT.S.D",  rd, rs)

     case FPLoad(  FLW(rd, rs1, imm))         => pFItype("FLW",    rd, rs1, imm)
     case FPLoad(  FLD(rd, rs1, imm))         => pFItype("FLD",    rd, rs1, imm)
     case FPStore( FSW(rs1, rs2, imm))        => pFStype("FSW",   rs1, rs2, imm)
     case FPStore( FSD(rs1, rs2, imm))        => pFStype("FSD",   rs1, rs2, imm)

     case AMO(     LR_W(aq, rl, rd, rs1))       => pLRtype("LR.W",      aq, rl, rd, rs1)
     case AMO(     LR_D(aq, rl, rd, rs1))       => pLRtype("LR.D",      aq, rl, rd, rs1)
     case AMO(     SC_W(aq, rl, rd, rs1, rs2))  => pARtype("SC.W",      aq, rl, rd, rs1, rs2)
     case AMO(     SC_D(aq, rl, rd, rs1, rs2))  => pARtype("SC.D",      aq, rl, rd, rs1, rs2)

     case AMO(AMOSWAP_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOSWAP.W", aq, rl, rd, rs1, rs2)
     case AMO( AMOADD_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOADD.W",  aq, rl, rd, rs1, rs2)
     case AMO( AMOXOR_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOXOR.W",  aq, rl, rd, rs1, rs2)
     case AMO( AMOAND_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOAND.W",  aq, rl, rd, rs1, rs2)
     case AMO(  AMOOR_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOOR.W",   aq, rl, rd, rs1, rs2)
     case AMO( AMOMIN_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOMIN.W",  aq, rl, rd, rs1, rs2)
     case AMO( AMOMAX_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOMAX.W",  aq, rl, rd, rs1, rs2)
     case AMO(AMOMINU_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOMINU.W", aq, rl, rd, rs1, rs2)
     case AMO(AMOMAXU_W(aq, rl, rd, rs1, rs2))  => pARtype("AMOMAXU.W", aq, rl, rd, rs1, rs2)

     case AMO(AMOSWAP_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOSWAP.D", aq, rl, rd, rs1, rs2)
     case AMO( AMOADD_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOADD.D",  aq, rl, rd, rs1, rs2)
     case AMO( AMOXOR_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOXOR.D",  aq, rl, rd, rs1, rs2)
     case AMO( AMOAND_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOAND.D",  aq, rl, rd, rs1, rs2)
     case AMO(  AMOOR_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOOR.D",   aq, rl, rd, rs1, rs2)
     case AMO( AMOMIN_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOMIN.D",  aq, rl, rd, rs1, rs2)
     case AMO( AMOMAX_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOMAX.D",  aq, rl, rd, rs1, rs2)
     case AMO(AMOMINU_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOMINU.D", aq, rl, rd, rs1, rs2)
     case AMO(AMOMAXU_D(aq, rl, rd, rs1, rs2))  => pARtype("AMOMAXU.D", aq, rl, rd, rs1, rs2)

     case System( ECALL)                    => pN0type("ECALL")
     case System(EBREAK)                    => pN0type("EBREAK")
     case System(  MRET)                    => pN0type("MRET")
     case System(  SRET)                    => pN0type("SRET")
     case System(   WFI)                    => pN0type("WFI")

     case System( CSRRW(rd, rs1, csr))      => pCSRtype("CSRRW",  rd, rs1, csr)
     case System( CSRRS(rd, rs1, csr))      => pCSRtype("CSRRS",  rd, rs1, csr)
     case System( CSRRC(rd, rs1, csr))      => pCSRtype("CSRRC",  rd, rs1, csr)
     case System(CSRRWI(rd, imm, csr))      => pCSRItype("CSRRWI", rd, imm, csr)
     case System(CSRRSI(rd, imm, csr))      => pCSRItype("CSRRSI", rd, imm, csr)
     case System(CSRRCI(rd, imm, csr))      => pCSRItype("CSRRCI", rd, imm, csr)

     case System(SFENCE_VMA(rs1, rs2))      => pN2type("SFENCE.VMA", rs1, rs2)

     case UnknownInstruction                => pN0type("UNKNOWN")

     case Internal(FETCH_MISALIGNED(_))     => pN0type("FETCH_MISALIGNED")
     case Internal(FETCH_FAULT(_))          => pN0type("FETCH_FAULT")
   }


word Rtype(o::opcode, f3::bits(3), rd::reg, rs1::reg, rs2::reg, f7::bits(7)) =
    f7 : rs2 : rs1 : f3 : rd : o

word R4type(o::opcode, f3::bits(3), rd::reg, rs1::reg, rs2::reg, rs3::reg, f2::bits(2)) =
    rs3 : f2 : rs2 : rs1 : f3 : rd : o

word Itype(o::opcode, f3::bits(3), rd::reg, rs1::reg, imm::imm12) =
    imm : rs1 : f3 : rd : o

word Stype(o::opcode, f3::bits(3), rs1::reg, rs2::reg, imm::imm12) =
    imm<11:5> : rs2 : rs1 : f3 : imm<4:0> : o

word SBtype(o::opcode, f3::bits(3), rs1::reg, rs2::reg, imm::imm12) =
    [imm<11>]::bits(1) : imm<9:4> : rs2 : rs1 : f3 : imm<3:0> : [imm<10>]::bits(1) : o

word Utype(o::opcode, rd::reg, imm::imm20) =
    imm : rd : o

word UJtype(o::opcode, rd::reg, imm::imm20) =
    [imm<19>]::bits(1) : imm<9:0> : [imm<10>]::bits(1) : imm<18:11> : rd : o

opcode opc(code::bits(8)) = code<4:0> : '11'

bits(7) amofunc(code::bits(5), aq::amo, rl::amo) =
    code : aq : rl

word Encode(i::instruction) =
   match i
   { case Branch(  BEQ(rs1, rs2, imm))      => SBtype(opc(0x18), 0, rs1, rs2, imm)
     case Branch(  BNE(rs1, rs2, imm))      => SBtype(opc(0x18), 1, rs1, rs2, imm)
     case Branch(  BLT(rs1, rs2, imm))      => SBtype(opc(0x18), 4, rs1, rs2, imm)
     case Branch(  BGE(rs1, rs2, imm))      => SBtype(opc(0x18), 5, rs1, rs2, imm)
     case Branch( BLTU(rs1, rs2, imm))      => SBtype(opc(0x18), 6, rs1, rs2, imm)
     case Branch( BGEU(rs1, rs2, imm))      => SBtype(opc(0x18), 7, rs1, rs2, imm)

     case Branch( JALR(rd, rs1, imm))       =>  Itype(opc(0x19), 0, rd, rs1, imm)
     case Branch(  JAL(rd, imm))            => UJtype(opc(0x1b), rd, imm)

     case ArithI(  LUI(rd, imm))            =>  Utype(opc(0x0D), rd, imm)
     case ArithI(AUIPC(rd, imm))            =>  Utype(opc(0x05), rd, imm)

     case ArithI( ADDI(rd, rs1, imm))       =>  Itype(opc(0x04), 0, rd, rs1, imm)
     case  Shift( SLLI(rd, rs1, imm))       =>  Itype(opc(0x04), 1, rd, rs1, '000000' : imm)
     case ArithI( SLTI(rd, rs1, imm))       =>  Itype(opc(0x04), 2, rd, rs1, imm)
     case ArithI(SLTIU(rd, rs1, imm))       =>  Itype(opc(0x04), 3, rd, rs1, imm)
     case ArithI( XORI(rd, rs1, imm))       =>  Itype(opc(0x04), 4, rd, rs1, imm)
     case  Shift( SRLI(rd, rs1, imm))       =>  Itype(opc(0x04), 5, rd, rs1, '000000' : imm)
     case  Shift( SRAI(rd, rs1, imm))       =>  Itype(opc(0x04), 5, rd, rs1, '010000' : imm)
     case ArithI(  ORI(rd, rs1, imm))       =>  Itype(opc(0x04), 6, rd, rs1, imm)
     case ArithI( ANDI(rd, rs1, imm))       =>  Itype(opc(0x04), 7, rd, rs1, imm)

     case ArithR(  ADD(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, 0)
     case ArithR(  SUB(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, 0x20)
     case  Shift(  SLL(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 1, rd, rs1, rs2, 0)
     case ArithR(  SLT(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 2, rd, rs1, rs2, 0)
     case ArithR( SLTU(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 3, rd, rs1, rs2, 0)
     case ArithR(  XOR(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 4, rd, rs1, rs2, 0)
     case  Shift(  SRL(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, 0)
     case  Shift(  SRA(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, 0x20)
     case ArithR(   OR(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 6, rd, rs1, rs2, 0)
     case ArithR(  AND(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 7, rd, rs1, rs2, 0)

     case ArithI(ADDIW(rd, rs1, imm))       =>  Itype(opc(0x06), 0, rd, rs1, imm)
     case  Shift(SLLIW(rd, rs1, imm))       =>  Itype(opc(0x06), 1, rd, rs1, '0000000' : imm)
     case  Shift(SRLIW(rd, rs1, imm))       =>  Itype(opc(0x06), 5, rd, rs1, '0000000' : imm)
     case  Shift(SRAIW(rd, rs1, imm))       =>  Itype(opc(0x06), 5, rd, rs1, '0100000' : imm)

     case ArithR( ADDW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0000000')
     case ArithR( SUBW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0100000')
     case  Shift( SLLW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 1, rd, rs1, rs2, '0000000')
     case  Shift( SRLW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0000000')
     case  Shift( SRAW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0100000')

     case MulDiv(    MUL(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, '0000001')
     case MulDiv(   MULH(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 1, rd, rs1, rs2, '0000001')
     case MulDiv( MULHSU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 2, rd, rs1, rs2, '0000001')
     case MulDiv(  MULHU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 3, rd, rs1, rs2, '0000001')
     case MulDiv(    DIV(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 4, rd, rs1, rs2, '0000001')
     case MulDiv(   DIVU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, '0000001')
     case MulDiv(    REM(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 6, rd, rs1, rs2, '0000001')
     case MulDiv(   REMU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 7, rd, rs1, rs2, '0000001')

     case MulDiv(   MULW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0000001')
     case MulDiv(   DIVW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 4, rd, rs1, rs2, '0000001')
     case MulDiv(  DIVUW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0000001')
     case MulDiv(   REMW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 6, rd, rs1, rs2, '0000001')
     case MulDiv(  REMUW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 7, rd, rs1, rs2, '0000001')

     case   Load(   LB(rd, rs1, imm))       =>  Itype(opc(0x00), 0, rd, rs1, imm)
     case   Load(   LH(rd, rs1, imm))       =>  Itype(opc(0x00), 1, rd, rs1, imm)
     case   Load(   LW(rd, rs1, imm))       =>  Itype(opc(0x00), 2, rd, rs1, imm)
     case   Load(   LD(rd, rs1, imm))       =>  Itype(opc(0x00), 3, rd, rs1, imm)
     case   Load(  LBU(rd, rs1, imm))       =>  Itype(opc(0x00), 4, rd, rs1, imm)
     case   Load(  LHU(rd, rs1, imm))       =>  Itype(opc(0x00), 5, rd, rs1, imm)
     case   Load(  LWU(rd, rs1, imm))       =>  Itype(opc(0x00), 6, rd, rs1, imm)

     case  Store(   SB(rs1, rs2, imm))      =>  Stype(opc(0x08), 0, rs1, rs2, imm)
     case  Store(   SH(rs1, rs2, imm))      =>  Stype(opc(0x08), 1, rs1, rs2, imm)
     case  Store(   SW(rs1, rs2, imm))      =>  Stype(opc(0x08), 2, rs1, rs2, imm)
     case  Store(   SD(rs1, rs2, imm))      =>  Stype(opc(0x08), 3, rs1, rs2, imm)

     case   FENCE(rd, rs1, pred, succ)      =>  Itype(opc(0x03), 0, rd, rs1, '0000' : pred : succ)
     case FENCE_I(rd, rs1, imm)             =>  Itype(opc(0x03), 1, rd, rs1, imm)

     case FArith(  FADD_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x00)
     case FArith(  FSUB_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x04)
     case FArith(  FMUL_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x08)
     case FArith(  FDIV_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x0c)
     case FArith( FSQRT_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs,    0, 0x2c)
     case FArith(  FMIN_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x14)
     case FArith(  FMAX_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x14)
     case FArith(   FEQ_S(rd, rs1, rs2))      => Rtype(opc(0x14), 2,   rd, rs1, rs2, 0x50)
     case FArith(   FLT_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x50)
     case FArith(   FLE_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x50)

     case FArith(  FADD_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x01)
     case FArith(  FSUB_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x05)
     case FArith(  FMUL_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x09)
     case FArith(  FDIV_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x0d)
     case FArith( FSQRT_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs,    0, 0x2d)
     case FArith(  FMIN_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x15)
     case FArith(  FMAX_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x15)
     case FArith(   FEQ_D(rd, rs1, rs2))      => Rtype(opc(0x14), 2,   rd, rs1, rs2, 0x51)
     case FArith(   FLT_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x51)
     case FArith(   FLE_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x51)

     case FPLoad(  FLW(rd, rs1, imm))         => Itype(opc(0x01), 2, rd, rs1, imm)
     case FPLoad(  FLD(rd, rs1, imm))         => Itype(opc(0x01), 3, rd, rs1, imm)
     case FPStore( FSW(rs1, rs2, imm))        => Stype(opc(0x09), 2, rs1, rs2, imm)
     case FPStore( FSD(rs1, rs2, imm))        => Stype(opc(0x09), 3, rs1, rs2, imm)

     case FArith( FMADD_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x10), frm, rd, rs1, rs2, rs3, 0)
     case FArith( FMSUB_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x11), frm, rd, rs1, rs2, rs3, 0)
     case FArith(FNMSUB_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x12), frm, rd, rs1, rs2, rs3, 0)
     case FArith(FNMADD_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x13), frm, rd, rs1, rs2, rs3, 0)

     case FArith( FMADD_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x10), frm, rd, rs1, rs2, rs3, 1)
     case FArith( FMSUB_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x11), frm, rd, rs1, rs2, rs3, 1)
     case FArith(FNMSUB_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x12), frm, rd, rs1, rs2, rs3, 1)
     case FArith(FNMADD_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x13), frm, rd, rs1, rs2, rs3, 1)

     case FConv(  FSGNJ_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0, rd, rs1, rs2, 0x10)
     case FConv( FSGNJN_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1, rd, rs1, rs2, 0x10)
     case FConv( FSGNJX_S(rd, rs1, rs2))      => Rtype(opc(0x14), 2, rd, rs1, rs2, 0x10)

     case FConv( FCVT_W_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x60)
     case FConv(FCVT_WU_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x60)
     case FConv(  FMV_X_S(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x70)
     case FConv( FCLASS_S(rd, rs))            => Rtype(opc(0x14), 1,   rd, rs, 0, 0x70)
     case FConv( FCVT_S_W(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x68)
     case FConv(FCVT_S_WU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x68)
     case FConv(  FMV_S_X(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x78)

     case FConv(  FSGNJ_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0, rd, rs1, rs2, 0x11)
     case FConv( FSGNJN_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1, rd, rs1, rs2, 0x11)
     case FConv( FSGNJX_D(rd, rs1, rs2))      => Rtype(opc(0x14), 2, rd, rs1, rs2, 0x11)

     case FConv( FCVT_W_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x61)
     case FConv(FCVT_WU_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x61)
     case FConv( FCLASS_D(rd, rs))            => Rtype(opc(0x14), 1,   rd, rs, 0, 0x71)
     case FConv( FCVT_D_W(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x69)
     case FConv(FCVT_D_WU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x69)
     case FConv( FCVT_S_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x20)
     case FConv( FCVT_D_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x21)

     case FConv( FCVT_L_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x60)
     case FConv(FCVT_LU_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x60)
     case FConv( FCVT_S_L(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x68)
     case FConv(FCVT_S_LU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x68)
     case FConv( FCVT_L_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x61)
     case FConv(FCVT_LU_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x61)
     case FConv(  FMV_X_D(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x71)
     case FConv( FCVT_D_L(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x69)
     case FConv(FCVT_D_LU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x69)
     case FConv(  FMV_D_X(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x79)

     case AMO(     LR_W(aq, rl, rd, rs1))       => Rtype(opc(0x0B), 2, rd, rs1, 0,   amofunc('00010', aq, rl))
     case AMO(     LR_D(aq, rl, rd, rs1))       => Rtype(opc(0x0B), 3, rd, rs1, 0,   amofunc('00010', aq, rl))
     case AMO(     SC_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00011', aq, rl))
     case AMO(     SC_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00010', aq, rl))

     case AMO(AMOSWAP_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00001', aq, rl))
     case AMO( AMOADD_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00000', aq, rl))
     case AMO( AMOXOR_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00100', aq, rl))
     case AMO( AMOAND_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('01100', aq, rl))
     case AMO(  AMOOR_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('01000', aq, rl))
     case AMO( AMOMIN_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('10000', aq, rl))
     case AMO( AMOMAX_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('10100', aq, rl))
     case AMO(AMOMINU_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('11000', aq, rl))
     case AMO(AMOMAXU_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('11100', aq, rl))

     case AMO(AMOSWAP_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00001', aq, rl))
     case AMO( AMOADD_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00000', aq, rl))
     case AMO( AMOXOR_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00100', aq, rl))
     case AMO( AMOAND_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('01100', aq, rl))
     case AMO(  AMOOR_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('01000', aq, rl))
     case AMO( AMOMIN_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('10000', aq, rl))
     case AMO( AMOMAX_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('10100', aq, rl))
     case AMO(AMOMINU_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('11000', aq, rl))
     case AMO(AMOMAXU_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('11100', aq, rl))

     case System( ECALL)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x000)
     case System(EBREAK)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x001)
     case System(  MRET)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x302)
     case System(  SRET)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x102)
     case System(   WFI)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x105)

     case System(SFENCE_VMA(rs1, rs2))      =>  Rtype(opc(0x1C), 0, 0, rs1, rs2, '0001001')

     case System( CSRRW(rd, rs1, csr))      =>  Itype(opc(0x1C), 1, rd, rs1, csr)
     case System( CSRRS(rd, rs1, csr))      =>  Itype(opc(0x1C), 2, rd, rs1, csr)
     case System( CSRRC(rd, rs1, csr))      =>  Itype(opc(0x1C), 3, rd, rs1, csr)
     case System(CSRRWI(rd, imm, csr))      =>  Itype(opc(0x1C), 5, rd, imm, csr)
     case System(CSRRSI(rd, imm, csr))      =>  Itype(opc(0x1C), 6, rd, imm, csr)
     case System(CSRRCI(rd, imm, csr))      =>  Itype(opc(0x1C), 7, rd, imm, csr)

     case UnknownInstruction                => 0

     case Internal(FETCH_MISALIGNED(_))     => 0
     case Internal(FETCH_FAULT(_))          => 0
   }

---------------------------------------------------------------------------
-- RVC instruction decoding
---------------------------------------------------------------------------

instruction DecodeRVC(h::half) =
   match h
   { case '000 00000000              rd 00' => UnknownInstruction
     case '000 ilo`2 ihi`4 i2`1 i3`1 rd 00' => ArithI(ADDI('01' : rd, 2, '00' : ihi : ilo : i3 : i2 : '00'))

     case '001 ilo`3 rs1 ihi`2     rd 00' => FPLoad(FLD('01' : rd, '01' : rs1, '0000'        : ihi : ilo : '000' ))
     case '010 imi`3 rs1 i2`1 i6`1 rd 00' => Load(   LW('01' : rd, '01' : rs1, '00000' : i6  : imi : i2  : '00'  ))
     case '011 ilo`3 rs1 ihi`2     rd 00' => Load(   LD('01' : rd, '01' : rs1, '0000'        : ihi : ilo : '000' ))

     case '101 ilo`3 rs1 ihi`2     rs2 00' => FPStore(FSD('01' : rs1, '01' : rs2, '0000'        : ihi : ilo : '000' ))
     case '110 imi`3 rs1 i2`1 i6`1 rs2 00' => Store(   SW('01' : rs1, '01' : rs2, '00000' : i6  : imi : i2  : '00'  ))
     case '111 ilo`3 rs1 ihi`2     rs2 00' => Store(   SD('01' : rs1, '01' : rs2, '0000'        : ihi : ilo : '000' ))

     case '000 0 00000 00000 01' => ArithI(ADDI(0, 0, 0))

     case '000 i5`1 r     imi`5                01' => ArithI( ADDI( r, r, i5 ^ 7 : imi))
     case '001 i5`1 00000 imi`5                01' => UnknownInstruction  -- ISA manual 7.1.4.2: C.ADDIW rd=x0 is reserved
     case '001 i5`1 r     imi`5                01' => ArithI(ADDIW( r, r, i5 ^ 7 : imi))
     case '010 i5`1 rd    imi`5                01' => ArithI( ADDI(rd, 0, i5 ^ 7 : imi))
     case '011 0    00010 00000                01' => UnknownInstruction
     case '011 i9`1 00010 i4`1 i6`1 imi`2 i5`1 01' => ArithI( ADDI( 2, 2, i9 ^ 3 : imi : i6 : i5 : i4 : '0000'))

     case '011 0     rd 00000 01' => UnknownInstruction
     case '011 i17`1 rd imi`5 01' => ArithI(LUI(rd, i17 ^ 15 : imi))

     case '100 i5`1 00 r imi`5 01' => Shift(SRLI('01' : r, '01' : r, i5 : imi))
     case '100 i5`1 01 r imi`5 01' => Shift(SRAI('01' : r, '01' : r, i5 : imi))

     case '100 i5`1 10 r imi`5 01' => ArithI(ANDI('01' : r, '01' : r, i5 ^ 7 : imi))

     case '100 0 11 r 00 rs2 01' => ArithR( SUB('01' : r, '01' : r, '01' : rs2))
     case '100 0 11 r 01 rs2 01' => ArithR( XOR('01' : r, '01' : r, '01' : rs2))
     case '100 0 11 r 10 rs2 01' => ArithR(  OR('01' : r, '01' : r, '01' : rs2))
     case '100 0 11 r 11 rs2 01' => ArithR( AND('01' : r, '01' : r, '01' : rs2))
     case '100 1 11 r 00 rs2 01' => ArithR(SUBW('01' : r, '01' : r, '01' : rs2))
     case '100 1 11 r 01 rs2 01' => ArithR(ADDW('01' : r, '01' : r, '01' : rs2))

     case '101 i11`1 i4`1 ihi`2 i10`1 i6`1 i7`1 ilo`3 i5`1 01' => Branch(JAL(0, i11 ^ 10 : i10 : ihi : i7 : i6 : i5 : i4 : ilo))

     case '110 i8`1 imi`2 rs1 ihi`2 ilo`2 i5`1 01' => Branch(BEQ('01' : rs1, 0, i8 ^ 5 : ihi : i5 : imi : ilo))
     case '111 i8`1 imi`2 rs1 ihi`2 ilo`2 i5`1 01' => Branch(BNE('01' : rs1, 0, i8 ^ 5 : ihi : i5 : imi : ilo))

     case '000 i5`1 r imi`5 10' => Shift(SLLI(r, r, i5 : imi))

     case '001 i5`1 rd    ilo`2 ihi`3 10' => FPLoad(FLD(rd, 2, '000'  : ihi : i5 : ilo : '000'))
     case '010 i5`1 00000 ilo`3 ihi`2 10' => UnknownInstruction
     case '010 i5`1 rd    ilo`3 ihi`2 10' => Load(   LW(rd, 2, '0000' : ihi : i5 : ilo : '00' ))
     case '011 i5`1 00000 ilo`2 ihi`3 10' => UnknownInstruction
     case '011 i5`1 rd    ilo`2 ihi`3 10' => Load(   LD(rd, 2, '000'  : ihi : i5 : ilo : '000'))

     case '100 0 00000 00000 10' => UnknownInstruction
     case '100 0 rs1   00000 10' => Branch(JALR( 0, rs1,   0))
     case '100 0 rd    rs2   10' => ArithR( ADD(rd,   0, rs2))
     case '100 1 00000 00000 10' => System(EBREAK)
     case '100 1 rs1   00000 10' => Branch(JALR( 1, rs1,   0))
     case '100 1 r     rs2   10' => ArithR( ADD( r,   r, rs2))

     case '101 ilo`3 ihi`3 rs2 10' => FPStore(FSD(2, rs2, '000'  : ihi : ilo : '000'))
     case '110 ilo`4 ihi`2 rs2 10' => Store(   SW(2, rs2, '0000' : ihi : ilo : '00' ))
     case '111 ilo`3 ihi`3 rs2 10' => Store(   SD(2, rs2, '000'  : ihi : ilo : '000'))

     case _ => UnknownInstruction
   }

---------------------------------------------------------------------------
-- The next state function
---------------------------------------------------------------------------

string log_instruction(w::word, inst::instruction) =
    "instr " : [procID] : " " : [[c_instret(procID)]::nat] :
    " 0x" : hex64(PC) : " : " : hex32(w) : "   " : instructionToString(inst)

-- Termination for an emulator.  Nothing in the model sets these: the
-- host-target interface (HTIF) belongs to the emulator ([D13]).
declare done :: bool   -- Flag to request termination

nat exitCode() =
    [ExitCode]::nat

-- minstret counts the instructions that retire (P §3.1.10 p.46): not
-- those that raise an exception (U §4.3 p.67), nor a step that takes an
-- interrupt ([D64]).  It does not count while mcountinhibit.IR is set,
-- sampled before the step (P §3.1.12 p.47), nor for an instruction that
-- writes minstret itself (U §4.2.1 p.64, [D65]).
unit incrInstret(incIR::bool) =
    when incIR and not c_minstret_written(procID)
    do c_instret(procID) <- c_instret(procID) + 1

-- Fetch and run one instruction.  The result is the trap value of an
-- illegal instruction: the instruction bits, zero-extended (P §3.1.16
-- p.52-53, [D43]).
regType fetchAndExecute() =
    match Fetch()
    { case F_Result(Half(h)) =>
      { inst = if haveRVC() then DecodeRVC(h) else UnknownInstruction
      ; mark_log(LOG_INSN, log_instruction(ZeroExtend(h), inst))
      ; Run(inst)
      ; ZeroExtend(h)
      }
      case F_Result(Word(w)) =>
      { inst = Decode(w)
      ; mark_log(LOG_INSN, log_instruction(w, inst))
      ; Run(inst)
      ; ZeroExtend(w)
      }
      case F_Error(inst)  =>
      { mark_log(LOG_INSN, log_instruction([0::word], inst))
      ; Run(inst)
      ; 0
      }
    }

-- One step of the hart, in M-, S- or U-mode; all three are validated
-- (design-smode.md §2).
unit Next =
{ clear_logs()
; c_minstret_written(procID) <- false
; incIR = not MCSR.mcountinhibit<2>

-- An interrupt is taken between instructions, at the start of a step:
-- the step does not fetch, and mepc is the instruction not executed
-- (P §3.1.14 p.49, [D38]).
; match checkInterrupts()
  { case Some(i, p) => takeTrap(true, interruptIndex(i), PC, 0, p)
    case None =>
    { ibits = fetchAndExecute()

    -- A trapping instruction does not retire (P §3.3.1 p.61).
    ; match NextFetch
      { case None =>
                 { incrInstret(incIR)
                 ; PC <- PC + Skip
                 }
        case Some(BranchTo(addr)) =>
                 { incrInstret(incIR)
                 ; NextFetch    <- None
                 ; PC           <- addr
                 }
        case Some(Mret) =>
                 { incrInstret(incIR)
                 ; NextFetch    <- None
                 ; mret()
                 }
        case Some(Sret) =>
                 { incrInstret(incIR)
                 ; NextFetch    <- None
                 ; sret()
                 }
        case Some(Trap(t)) =>
                 { NextFetch    <- None
                 ; ec   = excCode(t.trap)
                 ; tval = if t.trap == Illegal_Instr then ibits else t.tval
                 ; takeTrap(false, ec, PC, tval, excDest(ec, curPrivilege()))
                 }
      }
    }
  }

-- mcycle counts every step, unless mcountinhibit.CY is set after it
-- (P §3.1.10 p.46, §3.1.12 p.47, [D63], [D66]).  An emulator advances
-- mtime by one after each step, so mtime counts steps too ([D67]).
; when not MCSR.mcountinhibit<0>
  do c_cycles(procID) <- c_cycles(procID) + 1
}

-- Reset (P §3.4 p.63): M-mode, mstatus.MIE = mstatus.MPRV = 0, misa
-- with every extension, mcause = 0 and every PMP entry OFF and unlocked.
-- What the reset leaves unspecified is zero ([D62], [D70], [D71]): the
-- read value of mstatus is 0x0000000A00000000 (FS Off, MPP U), mtvec and
-- stvec are Direct at address 0, and the counters are zero.  The
-- emulator sets the pc and the CLINT memory.

unit initIdent(arch::Architecture) =
{ when arch != RV64I do #UNDEFINED("only RV64I is implemented")
; MCSR.misa <- misa(MISA_RESET)
}

unit initMachine(hartid::id) =
{ setPrivilege(Machine)
; MCSR.mhartid       <- ZeroExtend(hartid)
; MCSR.mstatus       <- mstatus(0)
; MCSR.medeleg       <- 0
; MCSR.mideleg       <- 0
; MCSR.mie           <- mie(0)
; MCSR.mtvec         <- 0
; MCSR.mcounteren    <- 0
; MCSR.menvcfg       <- 0
; MCSR.mcountinhibit <- 0
; MCSR.mscratch      <- 0
; MCSR.mepc          <- 0
; MCSR.mcause        <- mcause(0)
; MCSR.mtval         <- 0
; MCSR.mip           <- mip(0)
; MCSR.pmpcfg0       <- 0
; MCSR.pmpcfg2       <- 0
; MCSR.pmpaddr0  <- 0; MCSR.pmpaddr1  <- 0; MCSR.pmpaddr2  <- 0; MCSR.pmpaddr3  <- 0
; MCSR.pmpaddr4  <- 0; MCSR.pmpaddr5  <- 0; MCSR.pmpaddr6  <- 0; MCSR.pmpaddr7  <- 0
; MCSR.pmpaddr8  <- 0; MCSR.pmpaddr9  <- 0; MCSR.pmpaddr10 <- 0; MCSR.pmpaddr11 <- 0
; MCSR.pmpaddr12 <- 0; MCSR.pmpaddr13 <- 0; MCSR.pmpaddr14 <- 0; MCSR.pmpaddr15 <- 0

; SCSR.stvec         <- 0
; SCSR.scounteren    <- 0
; SCSR.senvcfg       <- 0
; SCSR.sscratch      <- 0
; SCSR.sepc          <- 0
; SCSR.scause        <- mcause(0)
; SCSR.stval         <- 0
; SCSR.satp          <- 0

; UCSR.fpcsr         <- FPCSR(0)

; c_cycles(procID)           <- 0
; c_instret(procID)          <- 0
; c_minstret_written(procID) <- false
; c_extMEIP(procID)          <- false
; c_extSEIP(procID)          <- false
; ReserveLoad        <- None
; ExitCode           <- 0
}

-- This initializes each core (via setting procID appropriately) on
-- startup before execution begins.  The registers are UNSPECIFIED after
-- reset (P §3.4 p.63) and zero here ([D71]); an emulator then sets a0 and
-- a1 as its boot convention requires ([D72]).
unit initRegs(pc::nat) =
{ for i in 0 .. 31 do
    gpr([i])   <- 0x0
; for i in 0 .. 31 do
    fpr([i])   <- 0x0

; PC           <- [pc]
; NextFetch    <- None
; done         <- false
}
