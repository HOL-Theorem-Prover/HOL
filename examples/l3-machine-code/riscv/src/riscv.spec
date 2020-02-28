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

type permType = bits(4)         -- memory permissions

nat ASID_SIZE       = 6
nat PAGESIZE_BITS   = 12
nat LEVEL_BITS      = 9

type asidType       = bits(6)

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

arch_base archBase(a::Architecture) =
    match a
    { case RV32I      => 0
      case RV64I      => 2
      case RV128I     => 3
    }

Architecture architecture(ab::arch_base) =
    match ab
    { case 0          => RV32I
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

type priv_level = bits(2)

construct Privilege
{ User
, Supervisor
, Hypervisor
, Machine
}

priv_level privLevel(p::Privilege) =
    match p
    { case User       => 0
      case Supervisor => 1
      case Hypervisor => 2
      case Machine    => 3
    }

Privilege privilege(p::priv_level) =
    match p
    { case 0          => User
      case 1          => Supervisor
      case 2          => Hypervisor
      case 3          => Machine
    }

string privName(p::Privilege) =
    match p
    { case User       => "U"
      case Supervisor => "S"
      case Hypervisor => "H"
      case Machine    => "M"
    }

---------------------------------------------------------------------------
-- Memory management and virtualization
---------------------------------------------------------------------------

type vm_mode    = bits(5)

construct VM_Mode
{ Mbare
, Mbb
, Mbbid
, Sv32
, Sv39
, Sv48
, Sv57
, Sv64
}

VM_Mode vmType(vm::vm_mode) =
    match vm
    { case  0     => Mbare
      case  1     => Mbb
      case  2     => Mbbid
      case  8     => Sv32
      case  9     => Sv39
      case 10     => Sv48
      case 11     => Sv57
      case 12     => Sv64
      case  _     => #UNDEFINED("Unknown address translation mode: " : [[vm]::nat])
    }

bool isValidVM(vm::vm_mode) =
    match vm
    { case 0 or 1 or 2 or 8 or 9 or 10 or 11 or 12 => true
      case _                                       => false
    }

vm_mode vmMode(vm::VM_Mode) =
    match vm
    { case Mbare  => 0
      case Mbb    => 1
      case Mbbid  => 2
      case Sv32   => 8
      case Sv39   => 9
      case Sv48   => 10
      case Sv57   => 11
      case Sv64   => 12
    }

string vmModeName(vm::VM_Mode) =
    match vm
    { case Mbare  => "Mbare"
      case Mbb    => "Mbb"
      case Mbbid  => "Mbbid"
      case Sv32   => "Sv32"
      case Sv39   => "Sv39"
      case Sv48   => "Sv48"
      case Sv57   => "Sv57"
      case Sv64   => "Sv64"
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

construct Interrupt
{ Software
, Timer
}

exc_code interruptIndex(i::Interrupt) =
    match i
    { case Software     => 0
      case Timer        => 1
    }

construct ExceptionType
{ Fetch_Misaligned
, Fetch_Fault
, Illegal_Instr
, Breakpoint
, Load_Fault
, AMO_Misaligned
, Store_AMO_Fault
, UMode_Env_Call
, SMode_Env_Call
, HMode_Env_Call
, MMode_Env_Call
}

exc_code excCode(e::ExceptionType) =
    match e
    { case Fetch_Misaligned   => 0x0
      case Fetch_Fault        => 0x1
      case Illegal_Instr      => 0x2
      case Breakpoint         => 0x3

      case Load_Fault         => 0x5
      case AMO_Misaligned     => 0x6
      case Store_AMO_Fault    => 0x7

      case UMode_Env_Call     => 0x8
      case SMode_Env_Call     => 0x9
      case HMode_Env_Call     => 0xA
      case MMode_Env_Call     => 0xB
    }

ExceptionType excType(e::exc_code) =
    match e
    { case 0x0 => Fetch_Misaligned
      case 0x1 => Fetch_Fault
      case 0x2 => Illegal_Instr
      case 0x3 => Breakpoint

      case 0x5 => Load_Fault
      case 0x6 => AMO_Misaligned
      case 0x7 => Store_AMO_Fault

      case 0x8 => UMode_Env_Call
      case 0x9 => SMode_Env_Call
      case 0xA => HMode_Env_Call
      case 0xB => MMode_Env_Call

      case _   => #UNDEFINED("Unknown exception: " : [[e]::nat])
    }

string excName(e::ExceptionType) =
    match e
    { case Fetch_Misaligned   => "MISALIGNED_FETCH"
      case Fetch_Fault        => "FAULT_FETCH"
      case Illegal_Instr      => "ILLEGAL_INSTRUCTION"
      case Breakpoint         => "BREAKPOINT"

      case Load_Fault         => "FAULT_LOAD"
      case AMO_Misaligned     => "MISALIGNED_AMO"
      case Store_AMO_Fault    => "FAULT_STORE_AMO"

      case UMode_Env_Call     => "U-EnvCall"
      case SMode_Env_Call     => "S-EnvCall"
      case HMode_Env_Call     => "H-EnvCall"
      case MMode_Env_Call     => "M-EnvCall"
    }

---------------------------------------------------------------------------
-- Control and Status Registers (CSRs)
---------------------------------------------------------------------------

-- Machine-Level CSRs

register mcpuid :: regType
{ 63-62 : ArchBase  -- base architecture, machine mode on reset
,    20 : U         -- user-mode support
,    18 : S         -- supervisor-mode support
,    12 : M         -- integer multiply/divide support
,     8 : I         -- integer base ISA support (XXX: this seems unnecessary)
}

register mimpid :: regType
{ 63-16 : RVImpl
,  15-0 : RVSource
}

register mstatus :: regType
{    63 : MSD       -- extended context dirty status
, 21-17 : VM        -- memory management and virtualization
,    16 : MMPRV     -- load/store memory privilege
, 15-14 : MXS       -- extension context status
, 13-12 : MFS       -- floating-point context status
            -- privilege and global interrupt-enable stack
, 11-10 : MPRV3
,     9 : MIE3
,   8-7 : MPRV2
,     6 : MIE2
,   5-4 : MPRV1
,     3 : MIE1
,   2-1 : MPRV
,     0 : MIE
}

register mtdeleg :: regType
{ 63-16 : Intr_deleg
, 15-0  : Exc_deleg
}

register mip :: regType
{           -- pending timer interrupts (read-only)
      7 : MTIP
,     6 : HTIP
,     5 : STIP
            -- pending software interrupts (read/write)
,     3 : MSIP
,     2 : HSIP
,     1 : SSIP
}

register mie :: regType
{           -- enable timer interrupts (read-only)
      7 : MTIE
,     6 : HTIE
,     5 : STIE
            -- enable software interrupts (read/write)
,     3 : MSIE
,     2 : HSIE
,     1 : SSIE
}

register mcause :: regType
{    63 : Int   -- Interrupt
    3-0 : EC    -- Exception Code
}

-- Timers and counters are stored as deltas from their system-values
-- at each privilege level; the hardware motivation is explained in
-- the specification.

record MachineCSR
{ mcpuid        :: mcpuid       -- information registers
  mimpid        :: mimpid
  mhartid       :: regType

  mstatus       :: mstatus      -- trap setup
  mtvec         :: regType
  mtdeleg       :: mtdeleg
  mie           :: mie
  mtimecmp      :: regType

  mtime_delta   :: regType      -- time wrt global clock

  mscratch      :: regType      -- trap handling
  mepc          :: regType
  mcause        :: mcause
  mbadaddr      :: regType
  mip           :: mip

  mbase         :: regType      -- protection and translation
  mbound        :: regType
  mibase        :: regType
  mibound       :: regType
  mdbase        :: regType
  mdbound       :: regType

                   -- host-target interface (berkeley extensions)
  mtohost       :: regType      -- output register to host
  mfromhost     :: regType      -- input register from host
}

-- Hypervisor-Level CSRs

record HypervisorCSR
{ hstatus       :: mstatus      -- trap setup
  htvec         :: regType
  htdeleg       :: mtdeleg
  htimecmp      :: regType

  htime_delta   :: regType      -- time wrt to global clock

  hscratch      :: regType      -- trap handling
  hepc          :: regType
  hcause        :: mcause
  hbadaddr      :: regType
}

-- Supervisor-Level CSRs

register sstatus :: regType
{    63 : SSD       -- extended context dirty status
,    16 : SMPRV     -- load/store memory privilege
, 15-14 : SXS       -- extension context status
, 13-12 : SFS       -- floating-point context status
,     4 : SPS       -- previous privilege level before entering supervisor mode
,     3 : SPIE      -- interrupt-enable before entering supervisor mode
,     0 : SIE       -- supervisor-level interrupt-enable
}

register sip :: regType
{     5 : STIP      -- pending timer interrupt
,     1 : SSIP      -- pending software interrupt
}

register sie :: regType
{     5 : STIE      -- enable timer interrupt
,     1 : SSIE      -- enable software interrupt
}

record SupervisorCSR
{ -- sstatus :: sstatus is a projection of mstatus :: mstatus
  stvec         :: regType      -- trap setup
  -- sie :: sie is a projection of mie :: mie
  stimecmp      :: regType

  stime_delta   :: regType      -- time wrt global clock

  sscratch      :: regType      -- trap handling
  sepc          :: regType
  scause        :: mcause
  sbadaddr      :: regType
  -- sip :: sip is a projection of mip :: mip

  sptbr         :: regType      -- memory protection and translation
  sasid         :: regType
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
{ cycle_delta   :: regType      -- timers and counters wrt base values
  time_delta    :: regType
  instret_delta :: regType
  fpcsr         :: FPCSR
}

-- Machine state projections

sip lift_mip_sip(mip::mip) =
{ var sip = sip(0)
; sip.STIP  <- mip.STIP
; sip.SSIP  <- mip.SSIP
; sip
}

sie lift_mie_sie(mie::mie) =
{ var sie = sie(0)
; sie.STIE  <- mie.STIE
; sie.SSIE  <- mie.SSIE
; sie
}

mip lower_sip_mip(sip::sip, mip::mip) =
{ var m = mip
; m.STIP    <- sip.STIP
; m.SSIP    <- sip.SSIP
; m
}

mie lower_sie_mie(sie::sie, mie::mie) =
{ var m = mie
; m.STIE    <- sie.STIE
; m.SSIE    <- sie.SSIE
; m
}

mstatus update_mstatus(orig::mstatus, v::mstatus) =
{ var mt = orig
-- update privilege stack
; mt.MIE   <- v.MIE
; mt.MPRV  <- v.MPRV
; mt.MIE1  <- v.MIE1
; mt.MPRV1 <- v.MPRV1
; mt.MIE2  <- v.MIE2
; mt.MPRV2 <- v.MPRV2
; mt.MIE3  <- v.MIE3
; mt.MPRV3 <- v.MPRV3

-- ensure a valid address translation mode
; when isValidVM(v.VM)
  do mt.VM <- v.VM
; mt.MMPRV <- v.MMPRV

-- update extension context status
; mt.MFS   <- v.MFS
; mt.MXS   <- v.MXS
; mt.MSD   <- extStatus(v.MXS) == Dirty or extStatus(v.MFS) == Dirty

; mt
}

sstatus lift_mstatus_sstatus(mst::mstatus) =
{ var st = sstatus(0)
; st.SMPRV  <- mst.MMPRV

-- shared state
; st.SXS    <- mst.MXS
; st.SFS    <- mst.MFS
; st.SSD    <- extStatus(mst.MXS) == Dirty or extStatus(mst.MFS) == Dirty

-- projected state
; st.SPS    <- not (privilege(mst.MPRV1) == User)
; st.SPIE   <- mst.MIE1
; st.SIE    <- mst.MIE

; st
}

mstatus lower_sstatus_mstatus(sst::sstatus, mst::mstatus) =
{ var mt = mstatus(&mst)

; mt.MMPRV  <- sst.SMPRV
; mt.MXS    <- sst.SXS
; mt.MFS    <- sst.SFS

; mt.MPRV1  <- privLevel(if sst.SPS then Supervisor else User)
; mt.MIE1   <- sst.SPIE
; mt.MIE    <- sst.SIE

; update_mstatus(mst, mt)
}

-- pop the privilege stack for ERET
mstatus popPrivilegeStack(mst::mstatus) =
{ var st = mst
; st.MIE    <- mst.MIE1
; st.MPRV   <- mst.MPRV1
; st.MIE1   <- mst.MIE2
; st.MPRV1  <- mst.MPRV2
; st.MIE2   <- true
; st.MPRV2  <- privLevel(User)
; st
}

mstatus pushPrivilegeStack(mst::mstatus, p::Privilege) =
{ var st = mst
; st.MIE2   <- mst.MIE1
; st.MPRV2  <- mst.MPRV1
; st.MIE1   <- mst.MIE
; st.MPRV1  <- mst.MPRV
; st.MIE    <- false
; st.MPRV   <- privLevel(p)
; st
}

---------------------------------------------------------------------------
-- Instruction fetch control
---------------------------------------------------------------------------

record SynchronousTrap
{ trap            :: ExceptionType
  badaddr         :: vAddr option
}

construct TransferControl
{ Trap            :: SynchronousTrap
, BranchTo        :: regType
, Ereturn
, Mrts
}

---------------------------------------------------------------------------
-- Register state space
---------------------------------------------------------------------------

-- Each register state is local to a core.

type RegFile    = reg  -> regType

declare
{ clock         :: regType                      -- global clock and counters

  c_instret     :: id -> regType                -- per-core counters
  c_cycles      :: id -> regType

  c_gpr         :: id -> RegFile                -- general purpose registers
  c_fpr         :: id -> RegFile                -- floating-point registers

  c_PC          :: id -> regType                -- program counter
  c_Skip        :: id -> regType                -- bytes to next instruction

  c_UCSR        :: id -> UserCSR                -- user-level CSRs
  c_SCSR        :: id -> SupervisorCSR          -- supervisor-level CSRs
  c_HCSR        :: id -> HypervisorCSR          -- hypervisor-level CSRs
  c_MCSR        :: id -> MachineCSR             -- machine-level CSRs

  -- interpreter execution context
  c_NextFetch   :: id -> TransferControl option
  c_ReserveLoad :: id -> vAddr option           -- load reservation for LL/SC
  c_ExitCode    :: id -> regType                -- derived from Berkeley HTIF
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

component fcsr :: FPCSR
{ value        = c_UCSR(procID).fpcsr
  assign value = { c_UCSR(procID).fpcsr       <- value
                 ; c_MCSR(procID).mstatus.MFS <- ext_status(Dirty)
                 ; c_MCSR(procID).mstatus.MSD <- true
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

component HCSR :: HypervisorCSR
{ value        = c_HCSR(procID)
  assign value = c_HCSR(procID) <- value
}

component MCSR :: MachineCSR
{ value        = c_MCSR(procID)
  assign value = c_MCSR(procID) <- value
}

component NextFetch :: TransferControl option
{ value        = c_NextFetch(procID)
  assign value = c_NextFetch(procID) <- value
}

component ReserveLoad :: vAddr option
{ value        = c_ReserveLoad(procID)
  assign value = c_ReserveLoad(procID) <- value
}

component ExitCode :: regType
{ value        = c_ExitCode(procID)
  assign value = c_ExitCode(procID) <- value
}

-- machine state utilities

Architecture curArch() =
    architecture(MCSR.mcpuid.ArchBase)

bool in32BitMode() =
    curArch() == RV32I

Privilege curPrivilege() =
    privilege(MCSR.mstatus.MPRV)

regType curEPC() =
    match curPrivilege()
    { case User         => #INTERNAL_ERROR("No EPC in U-mode")
      case Supervisor   => SCSR.sepc
      case Hypervisor   => HCSR.hepc
      case Machine      => MCSR.mepc
    }

unit sendIPI(core::regType) =
{ id = [core]::id
; when [id]::nat < totalCore
  do c_MCSR(id).mip.MSIP <- true
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
      case RMM        => None  -- roundTiesToMaxMagnitude not in L3
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

-- NaNs

bits(32) RV32_CanonicalNan = 0x7fc00000
bits(64) RV64_CanonicalNan = 0x7ff8000000000000

-- Classification

bool FP32_IsSignalingNan(x::bits(32)) =
    (x<30:23> == 0xff`8)   and x<22> == false and (x<21:0> != 0x0`22)

bool FP64_IsSignalingNan(x::bits(64)) =
    (x<62:52> == 0x7ff`11) and x<51> == false and (x<50:0> != 0x0`51)

bool FP32_Sign(x::bits(32)) = x<31>
bool FP64_Sign(x::bits(64)) = x<63>

-- setting exception flags

unit setFP_Invalid() =
    fcsr.NV <- true

unit setFP_DivZero() =
    fcsr.DZ <- true

unit setFP_Overflow() =
    fcsr.OF <- true

unit setFP_Underflow() =
    fcsr.OF <- true

unit setFP_Inexact() =
    fcsr.OF <- true

---------------------------------------------------------------------------
-- CSR Register address map
---------------------------------------------------------------------------

-- CSR access control

type csrRW    = bits(2)         -- read/write check
type csrPR    = bits(2)         -- privilege check

csrRW csrRW(csr::creg)  = csr<11:10>
csrPR csrPR(csr::creg)  = csr<9:8>

-- this only checks register-level access.  some registers have
-- additional bit-specific read/write controls.
bool check_CSR_access(rw::csrRW, pr::csrPR, p::Privilege, a::accessType) =
    (a == Read or rw != 0b11) and (privLevel(p) >=+ pr)

-- XXX: Revise this to handle absence of counter regs in RV32E.
bool is_CSR_defined(csr::creg) =
    -- user-mode
    (csr >= 0x001 and csr <= 0x003)
 or (csr >= 0xC00 and csr <= 0xC02)
 or (csr >= 0xC80 and csr <= 0xC82 and in32BitMode())

    -- supervisor-mode
 or (csr >= 0x100 and csr <= 0x101)
 or  csr == 0x104 or  csr == 0x121

 or  csr == 0xD01 or (csr == 0xD81 and in32BitMode())

 or (csr >= 0x140 and csr <= 0x141) or csr == 0x144
 or (csr >= 0xD42 and csr <= 0xD43)

 or (csr >= 0x180 and csr <= 0x181)

 or (csr >= 0x900 and csr <= 0x902)
 or (csr >= 0x980 and csr <= 0x982 and in32BitMode())

    -- machine-mode
 or (csr >= 0xF00 and csr <= 0xF01) or csr == 0xF10
 or (csr >= 0x300 and csr <= 0x302) or csr == 0x304 or csr == 0x321
 or  csr == 0x701 or (csr == 0x741 and in32BitMode())
 or (csr >= 0x340 and csr <= 0x344)
 or (csr >= 0x380 and csr <= 0x385)
 or  csr >= 0xB01 or (csr == 0xB81 and in32BitMode())
 or (csr >= 0x780 and csr <= 0x783 and csr != 0x782)

--- XXX: the CSRMap below is broken in 32-bit mode, since we need to
--- convert from 64-bit regType to 32-bit XLEN.
component CSRMap(csr::creg) :: regType
{
  value =
      match csr
      { -- user floating-point context
        case 0x001  => ZeroExtend(c_UCSR(procID).&fpcsr<4:0>)
        case 0x002  => ZeroExtend(c_UCSR(procID).fpcsr.FRM)
        case 0x003  => ZeroExtend(c_UCSR(procID).&fpcsr<7:0>)

        -- user counter/timers
        case 0xC00  => c_cycles(procID)  + c_UCSR(procID).cycle_delta
        case 0xC01  => clock             + c_UCSR(procID).time_delta
        case 0xC02  => c_instret(procID) + c_UCSR(procID).instret_delta
        case 0xC80  => SignExtend((c_cycles(procID)  + c_UCSR(procID).cycle_delta)<63:32>)
        case 0xC81  => SignExtend((clock             + c_UCSR(procID).time_delta)<63:32>)
        case 0xC82  => SignExtend((c_instret(procID) + c_UCSR(procID).instret_delta)<63:32>)

        -- supervisor trap setup
        case 0x100  => &lift_mstatus_sstatus(c_MCSR(procID).mstatus)
        case 0x101  => c_SCSR(procID).stvec
        case 0x104  => &lift_mie_sie(c_MCSR(procID).mie)
        case 0x121  => c_SCSR(procID).stimecmp

        -- supervisor timer
        case 0xD01  => clock + c_SCSR(procID).stime_delta
        case 0xD81  => SignExtend((clock + c_SCSR(procID).stime_delta)<63:32>)

        -- supervisor trap handling
        case 0x140  => c_SCSR(procID).sscratch
        case 0x141  => c_SCSR(procID).sepc
        case 0xD42  => c_SCSR(procID).&scause
        case 0xD43  => c_SCSR(procID).sbadaddr
        case 0x144  => &lift_mip_sip(c_MCSR(procID).mip)

        -- supervisor protection and translation
        case 0x180  => c_SCSR(procID).sptbr
        case 0x181  => c_SCSR(procID).sasid

        -- supervisor read/write shadow of user read-only registers
        case 0x900  => c_cycles(procID)  + c_UCSR(procID).cycle_delta
        case 0x901  => clock             + c_UCSR(procID).time_delta
        case 0x902  => c_instret(procID) + c_UCSR(procID).instret_delta
        case 0x980  => SignExtend((c_cycles(procID)  + c_UCSR(procID).cycle_delta)<63:32>)
        case 0x981  => SignExtend((clock             + c_UCSR(procID).time_delta)<63:32>)
        case 0x982  => SignExtend((c_instret(procID) + c_UCSR(procID).instret_delta)<63:32>)

        -- hypervisor trap setup
        case 0x200  => c_HCSR(procID).&hstatus
        case 0x201  => c_HCSR(procID).htvec
        case 0x202  => c_HCSR(procID).&htdeleg
        case 0x221  => c_HCSR(procID).htimecmp

        -- hypervisor timer
        case 0xE01  => clock + c_HCSR(procID).htime_delta
        case 0xE81  => SignExtend((clock + c_HCSR(procID).htime_delta)<63:32>)

        -- hypervisor trap handling
        case 0x240  => c_HCSR(procID).hscratch
        case 0x241  => c_HCSR(procID).hepc
        case 0x242  => c_HCSR(procID).&hcause
        case 0x243  => c_HCSR(procID).hbadaddr

        -- hypervisor read/write shadow of supervisor read-only registers
        case 0xA01  => clock + c_SCSR(procID).stime_delta
        case 0xA81  => SignExtend((clock + c_SCSR(procID).stime_delta)<63:32>)

        -- machine information registers
        case 0xF00  => c_MCSR(procID).&mcpuid
        case 0xF01  => c_MCSR(procID).&mimpid
        case 0xF10  => c_MCSR(procID).mhartid

        -- machine trap setup
        case 0x300  => c_MCSR(procID).&mstatus
        case 0x301  => c_MCSR(procID).mtvec
        case 0x302  => c_MCSR(procID).&mtdeleg
        case 0x304  => c_MCSR(procID).&mie
        case 0x321  => c_MCSR(procID).mtimecmp

        -- machine timers and counters
        case 0x701  => clock + c_MCSR(procID).mtime_delta
        case 0x741  => SignExtend((clock + c_MCSR(procID).mtime_delta)<63:32>)

        -- machine trap handling
        case 0x340  => c_MCSR(procID).mscratch
        case 0x341  => c_MCSR(procID).mepc
        case 0x342  => c_MCSR(procID).&mcause
        case 0x343  => c_MCSR(procID).mbadaddr
        case 0x344  => c_MCSR(procID).&mip

        -- machine protection and translation
        case 0x380  => c_MCSR(procID).mbase
        case 0x381  => c_MCSR(procID).mbound
        case 0x382  => c_MCSR(procID).mibase
        case 0x383  => c_MCSR(procID).mibound
        case 0x384  => c_MCSR(procID).mdbase
        case 0x385  => c_MCSR(procID).mdbound

        -- machine read-write shadow of hypervisor read-only registers
        case 0xB01  => clock + c_HCSR(procID).htime_delta
        case 0xB81  => SignExtend((clock + c_HCSR(procID).htime_delta)<63:32>)

        -- machine host-target interface (berkeley extension)
        case 0x780  => c_MCSR(procID).mtohost
        case 0x781  => c_MCSR(procID).mfromhost
        case 0x783  => 0

        case _      => #UNDEFINED("unexpected CSR read at " : [csr])
      }

  assign value =
      match csr
      { -- user floating-point context
        case 0x001  => { c_UCSR(procID).&fpcsr<4:0>     <- value<4:0>
                       ; c_MCSR(procID).mstatus.MFS     <- ext_status(Dirty)
                       ; c_MCSR(procID).mstatus.MSD     <- true
                       }
        case 0x002  => { c_UCSR(procID).fpcsr.FRM       <- value<2:0>
                       ; c_MCSR(procID).mstatus.MFS     <- ext_status(Dirty)
                       ; c_MCSR(procID).mstatus.MSD     <- true
                       }
        case 0x003  => { c_UCSR(procID).&fpcsr          <- value<31:0>
                       ; c_MCSR(procID).mstatus.MFS     <- ext_status(Dirty)
                       ; c_MCSR(procID).mstatus.MSD     <- true
                       }
        -- user counters/timers are URO

        -- supervisor trap setup
        case 0x100  => c_MCSR(procID).mstatus           <- lower_sstatus_mstatus(sstatus(value),
                                                                                 c_MCSR(procID).mstatus)

        case 0x101  => c_SCSR(procID).stvec             <- value
        -- sie back-projects to mie
        case 0x104  => c_MCSR(procID).mie               <- lower_sie_mie(sie(value), c_MCSR(procID).mie)
        case 0x121  =>
        { c_SCSR(procID).stimecmp <- value
        ; c_MCSR(procID).mip.STIP <- false
        }

        -- supervisor trap handling
        case 0x140  => c_SCSR(procID).sscratch          <- value
        case 0x141  => c_SCSR(procID).sepc              <- (value && SignExtend(0b100`3))  -- no 16-bit instr support
        -- scause, sbadaddr are SRO
        -- sip back-projects to mip
        case 0x144  => c_MCSR(procID).mip               <- lower_sip_mip(sip(value), c_MCSR(procID).mip)

        -- supervisor protection and translation
        case 0x180  => c_SCSR(procID).sptbr             <- value
        case 0x181  => c_SCSR(procID).sasid             <- value

        -- supervisor read/write shadow of user read-only registers
        case 0x900  => c_UCSR(procID).cycle_delta       <- value - c_cycles(procID)
        case 0x901  => c_UCSR(procID).time_delta        <- value - clock
        case 0x902  => c_UCSR(procID).instret_delta     <- value - c_instret(procID)

        case 0x980  => c_UCSR(procID).cycle_delta<63:32>    <- (value<31:0> - c_cycles(procID)<63:32>)  << 32
        case 0x981  => c_UCSR(procID).time_delta<63:32>     <- (value<31:0> - clock<63:32>)             << 32
        case 0x982  => c_UCSR(procID).instret_delta<63:32>  <- (value<31:0> - c_instret(procID)<63:32>) << 32

        -- TODO: hypervisor register write support

        -- machine information registers are MRO

        -- machine trap setup
        case 0x300  => c_MCSR(procID).mstatus           <- update_mstatus(c_MCSR(procID).mstatus, mstatus(value))
        case 0x301  => c_MCSR(procID).mtvec             <- value
        case 0x302  => c_MCSR(procID).mtdeleg           <- mtdeleg(value)
        case 0x304  => c_MCSR(procID).mie               <- mie(value)
        case 0x321  =>
        { c_MCSR(procID).mtimecmp <- value
        ; c_MCSR(procID).mip.MTIP <- false
        }

        -- machine timers and counters
        case 0x701  => c_MCSR(procID).mtime_delta           <- value - clock
        case 0x741  => c_MCSR(procID).mtime_delta<63:32>    <- (value<31:0> - clock<63:32>) << 32

        -- machine trap handling
        case 0x340  => c_MCSR(procID).mscratch          <- value
        case 0x341  => c_MCSR(procID).mepc              <- (value && SignExtend(0b100`3))  -- no 16-bit instr support
        case 0x342  => c_MCSR(procID).mcause            <- mcause(value)
        case 0x343  => c_MCSR(procID).mbadaddr          <- value
        case 0x344  => c_MCSR(procID).mip               <- mip(value)

        -- machine protection and translation
        case 0x380  => c_MCSR(procID).mbase             <- value
        case 0x381  => c_MCSR(procID).mbound            <- value
        case 0x382  => c_MCSR(procID).mibase            <- value
        case 0x383  => c_MCSR(procID).mibound           <- value
        case 0x384  => c_MCSR(procID).mdbase            <- value
        case 0x385  => c_MCSR(procID).mdbound           <- value

        -- machine read-write shadow of hypervisor read-only registers
        case 0xB01  => c_HCSR(procID).htime_delta           <- value - clock
        case 0xB81  => c_HCSR(procID).htime_delta<63:32>    <- (value<31:0> - clock<63:32>) << 32

        -- machine host-target interface (berkeley extension)
        -- TODO: XXX: set I/O pending bit
        case 0x780  =>
        { c_MCSR(procID).mtohost    <- value }
        case 0x781  =>
        { c_MCSR(procID).mfromhost  <- value }
        case 0x783  =>
        { sendIPI(value) }

        case _      => #INTERNAL_ERROR("unexpected CSR write to " : [csr])
      }
}

string csrName(csr::creg) =
    match csr
    { -- user floating-point context
      case 0x001  => "fflags"
      case 0x002  => "frm"
      case 0x003  => "fcsr"

      -- user counter/timers
      case 0xC00  => "cycle"
      case 0xC01  => "time"
      case 0xC02  => "instret"
      case 0xC80  => "cycleh"
      case 0xC81  => "timeh"
      case 0xC82  => "instreth"

      -- supervisor trap setup
      case 0x100  => "sstatus"
      case 0x101  => "stvec"
      case 0x104  => "sie"
      case 0x121  => "stimecmp"

      -- supervisor timer
      case 0xD01  => "stime"
      case 0xD81  => "stimeh"

      -- supervisor trap handling
      case 0x140  => "sscratch"
      case 0x141  => "sepc"
      case 0xD42  => "scause"
      case 0xD43  => "sbadaddr"
      case 0x144  => "mip"

      -- supervisor protection and translation
      case 0x180  => "sptbr"
      case 0x181  => "sasid"

      -- supervisor read/write shadow of user read-only registers
      case 0x900  => "cycle"
      case 0x901  => "time"
      case 0x902  => "instret"
      case 0x980  => "cycleh"
      case 0x981  => "timeh"
      case 0x982  => "instreth"

      -- hypervisor trap setup
      case 0x200  => "hstatus"
      case 0x201  => "htvec"
      case 0x202  => "htdeleg"
      case 0x221  => "htimecmp"

      -- hypervisor timer
      case 0xE01  => "htime"
      case 0xE81  => "htimeh"

      -- hypervisor trap handling
      case 0x240  => "hscratch"
      case 0x241  => "hepc"
      case 0x242  => "hcause"
      case 0x243  => "hbadaddr"

      -- hypervisor read/write shadow of supervisor read-only registers
      case 0xA01  => "stime"
      case 0xA81  => "stimeh"

      -- machine information registers
      case 0xF00  => "mcpuid"
      case 0xF01  => "mimpid"
      case 0xF10  => "mhartid"

      -- machine trap setup
      case 0x300  => "mstatus"
      case 0x301  => "mtvec"
      case 0x302  => "mtdeleg"
      case 0x304  => "mie"
      case 0x321  => "mtimecmp"

      -- machine timers and counters
      case 0x701  => "mtime"
      case 0x741  => "mtimeh"

      -- machine trap handling
      case 0x340  => "mscratch"
      case 0x341  => "mepc"
      case 0x342  => "mcause"
      case 0x343  => "mbadaddr"
      case 0x344  => "mip"

      -- machine protection and translation
      case 0x380  => "mbase"
      case 0x381  => "mbound"
      case 0x382  => "mibase"
      case 0x383  => "mibound"
      case 0x384  => "mdbase"
      case 0x385  => "mdbound"

      -- machine read-write shadow of hypervisor read-only registers
      case 0xB01  => "htime"
      case 0xB81  => "htimeh"

      -- machine host-target interface (berkeley extension)
      case 0x780  => "mtohost"
      case 0x781  => "mfromhost"

      case 0x783  => "send_ipi"

      case _      => "UNKNOWN"
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

inline unit recordLoad(addr::vAddr, val::regType) =
when not PROVER_EXPORT do
{ Delta.addr      <- Some(addr)
; Delta.data1     <- Some(val)
}

inline unit recordStore(addr::vAddr, val::regType, width::word) =
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

string log_tohost(tohost::regType) =
    "-> host: " : [[tohost<7:0>]::char]

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

-- Signalled exceptions are recorded as traps.

unit setTrap(e::ExceptionType, badaddr::vAddr option) =
{ var trap
; trap.trap        <- e
; trap.badaddr     <- badaddr
; NextFetch        <- Some(Trap(trap))
}

unit signalException(e::ExceptionType) =
{ mark_log(LOG_INSN, "signalling exception " : excName(e))
; setTrap(e, None)
; recordException()
}

unit signalAddressException(e::ExceptionType, vAddr::vAddr) =
{ mark_log(LOG_INSN, "signalling address exception " : excName(e) : " at " : [vAddr])
; setTrap(e, Some(vAddr))
; recordException()
}

unit signalEnvCall() =
{ e = match privilege(MCSR.mstatus.MPRV)
      { case User       => UMode_Env_Call
        case Supervisor => SMode_Env_Call
        case Hypervisor => HMode_Env_Call
        case Machine    => MMode_Env_Call
      }
; signalException(e)
}

-- Delegation logic.

Privilege checkDelegation(curPriv::Privilege, intr::bool, ec::exc_code)
          HOL "checkDelegation.sml" measure [curPriv] =
{ e = [ec]::nat
; match curPriv
  { case User       => #INTERNAL_ERROR("No user-level delegation!")
    case Supervisor => #INTERNAL_ERROR("No supervisor-level delegation!")
    case Hypervisor =>
         if ((intr and HCSR.htdeleg.Intr_deleg<e>)
             or (!intr and HCSR.htdeleg.Exc_deleg<e>))
         then Supervisor else curPriv
    case Machine    =>
         if ((intr and MCSR.mtdeleg.Intr_deleg<e>)
             or (!intr and MCSR.mtdeleg.Exc_deleg<e>))
         then checkDelegation(Hypervisor, intr, ec) else curPriv
  }
}

-- The spec doesn't define a priority between a timer interrupt and a
-- software interrupt.  We treat timer interrupts at higher priority.

(Interrupt * Privilege) option checkPrivInterrupt(curPriv::Privilege) =
{ ip = MCSR.mip
; ie = MCSR.mie
; match curPriv
  { case User       => #INTERNAL_ERROR("No user-level interrupts!")
    case Supervisor => if ip.STIP and ie.STIE then Some(Timer, curPriv)
                       else if ip.SSIP and ie.SSIE then Some(Software, curPriv)
                       else None
    case Hypervisor => if ip.HTIP and ie.HTIE then Some(Timer, curPriv)
                       else if ip.HSIP and ie.HSIE then Some(Software, curPriv)
                       else None
    case Machine    => if ip.MTIP and ie.MTIE then Some(Timer, curPriv)
                       else if ip.MSIP and ie.MSIE then Some(Software, curPriv)
                       else None
  }
}

-- The spec says:
--
--    When a hart is running in a given privileged mode, interrupts
--    for higher privileged modes are always enabled while interrupts
--    for lower privileged modes are always disabled.
--    Higher-privilege-level code can use separate per-interrupt
--    enable bits to disable selected interrupts before ceding control
--    to a lower privilege level.
--
-- This is critical to ensuring the monotonically non-decreasing
-- privilege levels in the privilege stack.

(Interrupt * Privilege) option checkInterrupts() =
{ curIE = MCSR.mstatus.MIE  -- if interrupts are enabled at curPrivilege
; p     = curPrivilege()
; match p
  { case User or Supervisor =>
         match checkPrivInterrupt(Machine)
         { case None =>
           { match checkPrivInterrupt(Hypervisor)
             { case None => -- Always check S-mode interrupts in U-mode
                            if p == User or curIE
                            then checkPrivInterrupt(Supervisor) else None
               case i    => i
             }
           }
           case i    => i
         }
    case Hypervisor =>
         match checkPrivInterrupt(Machine)
         { case None => if curIE then checkPrivInterrupt(Hypervisor) else None
           case i    => i
         }
    case Machine =>
         if curIE then checkPrivInterrupt(Machine) else None
  }
}

unit takeTrap(intr::bool, ec::exc_code, epc::regType, badaddr::vAddr option, toPriv::Privilege) =
{ fromP = curPrivilege()
; mark_log(LOG_INSN, ["trapping from " : privName(fromP) : " to " : privName(toPriv) :
                      " at pc " : [epc] : (if intr then " [intr] " else " [exc] ") : [[ec]::nat]])

; ReserveLoad        <- None        -- cancel any load reservation
; MCSR.mstatus.MMPRV <- false       -- unset MPRV in each privilege level

; MCSR.mstatus       <- pushPrivilegeStack(MCSR.mstatus, toPriv)

; match toPriv
  { case User       => #INTERNAL_ERROR("Illegal trap to U-mode")
    case Supervisor =>
    { SCSR.scause.Int   <- intr
    ; SCSR.scause.EC    <- ec
    ; SCSR.sepc         <- epc
    ; when IsSome(badaddr)
      do SCSR.sbadaddr  <- ValOf(badaddr)

    ; PC    <- SCSR.stvec
    }
    case Hypervisor => #INTERNAL_ERROR("Unsupported trap to H-mode")
    case Machine    =>
    { MCSR.mcause.Int   <- intr
    ; MCSR.mcause.EC    <- ec
    ; MCSR.mepc         <- epc
    ; when IsSome(badaddr)
      do MCSR.mbadaddr  <- ValOf(badaddr)

    ; PC    <- MCSR.mtvec + ([privLevel(fromP)]::regType) * 0x40
    }
  }
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

inline unit writeRD(rd::reg, val::regType) =
{ GPR(rd)       <- val
; when not PROVER_EXPORT do Delta.data1   <- Some(val)
}

component FPRS(n::reg) :: word
{ value        = fpr(n)<31:0>
  assign value = { fpr(n)<31:0> <- value
                 ; mark_log(LOG_REG, log_w_fprs(n, value))
                 }
}

component FPRD(n::reg) :: regType
{ value        = fpr(n)
  assign value = { fpr(n) <- value
                 ; mark_log(LOG_REG, log_w_fprd(n, value))
                 }
}

unit writeFPRS(rd::reg, val::word) =
{ FPRS(rd)          <- val
; MCSR.mstatus.MFS  <- ext_status(Dirty)
; MCSR.mstatus.MSD  <- true
; Delta.data1       <- Some(ZeroExtend(val))
}

unit writeFPRD(rd::reg, val::regType) =
{ FPRD(rd)          <- val
; MCSR.mstatus.MFS  <- ext_status(Dirty)
; MCSR.mstatus.MSD  <- true
; Delta.data1       <- Some(val)
}

---------------------------------------------------------------------------
-- Raw memory access
---------------------------------------------------------------------------

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
         -- write touching adjacent regType-sized blocks
         else { dw_old  = MEM(pAddrIdx+1) : old
              ; dw_data = ZeroExtend(data) << (align*8)
              ; dw_mask = ZeroExtend(mask) << (align*8)
              ; dw_new  = dw_old && ~dw_mask || dw_data && dw_mask
              ; MEM(pAddrIdx+1) <- dw_new<2*Size(data)-1:Size(data)>
              ; MEM(pAddrIdx)   <- dw_new<Size(data)-1:0>
              }
       }
}

half rawReadHalf(pAddr::pAddr) =
{ pAddrIdx = pAddr<63:3>
; data     = MEM(pAddrIdx)
; mark_log(LOG_MEM, log_r_mem(pAddrIdx, pAddr, data))
; match pAddr<2:1>
  { case '00' => data<63:48>
    case '01' => data<47:32>
    case '10' => data<31:16>
    case '11' => data<15:0>
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
-- Address Translation
---------------------------------------------------------------------------

-- memory permissions

bool checkMemPermission(ft::fetchType, ac::accessType, priv::Privilege, perm::permType) =
    match perm
    { case  0   => #INTERNAL_ERROR("Checking perm on Page-Table pointer!")
      case  1   => #INTERNAL_ERROR("Checking perm on Page-Table pointer!")
      case  2   => if priv == User then ac != Write else (ac == Read and ft == Data)
      case  3   => if priv == User then true else ft != Instruction
      case  4   => ac == Read and ft == Data
      case  5   => ft != Instruction
      case  6   => ac != Write
      case  7   => true
      case  8   => priv != User and ac == Read and ft == Data
      case  9   => priv != User and ft != Instruction
      case 10   => priv != User and ac != Write
      case 11   => priv != User
      case 12   => priv != User and ac == Read and ft == Data
      case 13   => priv != User and ft != Instruction
      case 14   => priv != User and ac != Write
      case 15   => priv != User
    }

bool isGlobal(perm::permType) =
    perm<3:2> == 3

-- page table walking (currently 64-bit only)

register SV_PTE :: regType
{ 47-10 : PTE_PPNi  -- PPN[2,1,0]
    9-7 : PTE_SW    -- reserved for software
      6 : PTE_D     -- dirty bit
      5 : PTE_R     -- referenced bit
    4-1 : PTE_T     -- PTE type
      0 : PTE_V     -- valid bit
}

register SV_Vaddr :: regType
{ 47-12 : Sv_VPNi
  11-0  : Sv_PgOfs
}

(pAddr * SV_PTE * nat * bool * pAddr) option
 walk64(vAddr::vAddr, ft::fetchType, ac::accessType, priv::Privilege, ptb::regType, level::nat) measure level =
{ va        = SV_Vaddr(vAddr)
; pt_ofs    = ZeroExtend((va.Sv_VPNi >>+ (level * LEVEL_BITS))<(LEVEL_BITS-1):0>) << 3
; pte_addr  = ptb + pt_ofs
; pte       = SV_PTE(rawReadData(pte_addr))
; mark_log(LOG_ADDRTR, ["translate(vaddr=0x" : PadLeft(#"0", 16, [vAddr]) : "): level=" : [level]
                        : " pt_base=0x" : PadLeft(#"0", 16, [ptb])
                        : " pt_ofs=" : [[pt_ofs]::nat]
                        : " pte_addr=0x" : PadLeft(#"0", 16, [pte_addr])
                        : " pte=0x" : PadLeft(#"0", 16, [&pte])])
; if not pte.PTE_V
  then { mark_log(LOG_ADDRTR, "addr_translate: invalid PTE")
       ; None
       }
  else { if pte.PTE_T == 0 or pte.PTE_T == 1
         then { -- ptr to next level table
                if level == 0
                then { mark_log(LOG_ADDRTR, "last-level pt contains a pointer PTE!")
                     ; None
                     }
                else walk64(vAddr, ft, ac, priv, ZeroExtend(pte.PTE_PPNi << PAGESIZE_BITS), level - 1)
              }
         else { -- leaf PTE
                if not checkMemPermission(ft, ac, priv, pte.PTE_T)
                then { mark_log(LOG_ADDRTR, "PTE permission check failure!")
                     ; None
                     }
                else { var pte_w = pte
                     -- update referenced and dirty bits
                     ; old_r = pte.PTE_R
                     ; old_d = pte.PTE_D
                     ; pte_w.PTE_R <- true
                     ; when ac == Write
                       do pte_w.PTE_D <- true
                     ; when old_r !=  pte_w.PTE_R or old_d !=  pte_w.PTE_D
                       do rawWriteData(pte_addr, &pte_w, 8)
                     -- compute translated address
                     ; ppn = if level > 0
                             then ((ZeroExtend((pte.PTE_PPNi >>+ (level * LEVEL_BITS)) << (level * LEVEL_BITS)))
                                   || ZeroExtend(va.Sv_VPNi && ((1 << (level * LEVEL_BITS)) - 1)))
                             else pte.PTE_PPNi
                     ; Some(ZeroExtend(ppn : va.Sv_PgOfs), pte_w, level, isGlobal(pte.PTE_T), pte_addr)
                     }
              }
       }
}

-- TLB
---------------------------------------------------------------------------
-- We maintain an internal model of a TLB.  The spec leaves the TLB
-- unspecified, but we would like to capture the semantics of SFENCE.
-- The TLB also improves simulation speed.

-- This implementation stores the global mapping bit from the PTE in
-- the TLB.  This causes an asymmetry between TLB lookup and TLB
-- flush, due to the spec's treatment of an ASID=0 in SFENCE.VM:
--
-- * in TLB lookup, the global bit is used to check for a global
--   match, and this global bit when set overrides the input ASID.
--
-- * in TLB flush, an input ASID of 0 overrides the global bit when
--   checking if a TLB entry needs to be flushed.

-- Each TLBEntry also stores the full PTE and its pAddr, so that it
-- can write back the PTE when its dirty bit needs to be updated.

asidType curASID() =
    SCSR.sasid<ASID_SIZE-1:0>

record TLBEntry
{ asid          :: asidType
  global        :: bool
  vAddr         :: vAddr        -- VPN
  vMatchMask    :: vAddr        -- matching mask for superpages

  pAddr         :: pAddr        -- PPN
  vAddrMask     :: vAddr        -- selection mask for superpages

  pte           :: SV_PTE       -- permissions and dirty bit writeback
  pteAddr       :: pAddr

  age           :: regType      -- derived from instret
}

TLBEntry mkTLBEntry(asid::asidType, global::bool, vAddr::vAddr, pAddr::pAddr,
                    pte::SV_PTE, i::nat, pteAddr::pAddr) =
{ var ent :: TLBEntry
; ent.asid          <- asid
; ent.global        <- global
; ent.pte           <- pte
; ent.pteAddr       <- pteAddr
; ent.vAddrMask     <- ((1::vAddr) << ((LEVEL_BITS*i) + PAGESIZE_BITS)) - 1
; ent.vMatchMask    <- (SignExtend('1')::vAddr) ?? ent.vAddrMask
; ent.vAddr         <- vAddr && ent.vMatchMask
; ent.pAddr         <- (pAddr >> (PAGESIZE_BITS + (LEVEL_BITS*i))) << (PAGESIZE_BITS + (LEVEL_BITS*i))
; ent.age           <- c_cycles(procID)
; ent
}

nat  TLBEntries = 16
type tlbIdx     = bits(4)
type TLBMap     = tlbIdx -> TLBEntry option

(TLBEntry * tlbIdx) option lookupTLB(asid::asidType, vAddr::vAddr, tlb::TLBMap) =
{ var ent = None
; for i in 0 .. TLBEntries - 1 do
  { match tlb([i])
    { case Some(e) => when ent == None and (e.global or e.asid == asid)
                           and (e.vAddr == vAddr && e.vMatchMask)
                      do ent <- Some(e, [i])
      case None    => ()
    }
  }
; ent
}

TLBMap addToTLB(asid::asidType, vAddr::vAddr, pAddr::pAddr, pte::SV_PTE, pteAddr::pAddr,
                i::nat, global::bool, curTLB::TLBMap) =
{ var ent       = mkTLBEntry(asid, global, vAddr, pAddr, pte, i, pteAddr)
; var tlb       = curTLB
; var oldest    = SignExtend('1')
; var addIdx    = 0
; var added     = false
; for i in 0 .. TLBEntries - 1 do
  { match tlb([i])
    { case Some(e)  => when e.age <+ oldest
                       do { oldest      <- e.age
                          ; addIdx      <- i
                          }
      case None     => when not added
                       do { tlb([i])    <- Some(ent)
                          ; added       <- true
                          }
    }
  }
; when not added
  do tlb([addIdx]) <- Some(ent)
; tlb
}

TLBMap flushTLB(asid::asidType, addr::vAddr option, curTLB::TLBMap) =
{ var tlb = curTLB
; for i in 0 .. TLBEntries - 1 do
  { match tlb([i]), addr
    { case Some(e), Some(va)    => when (asid == 0 or (asid == e.asid and not e.global))
                                        and (e.vAddr == va && e.vMatchMask)
                                   do tlb([i]) <- None
      case Some(e), None        => when asid == 0 or (asid == e.asid and not e.global)
                                   do tlb([i]) <- None
      case None,    _           => ()
    }
  }
; tlb
}

declare  c_tlb  :: id -> TLBMap

component TLB :: TLBMap
{ value        = c_tlb(procID)
  assign value = c_tlb(procID) <- value
}

-- address translation

pAddr option translate64(vAddr::regType, ft::fetchType, ac::accessType, priv::Privilege, level::nat) =
{ asid = curASID()
; match lookupTLB(asid, vAddr, TLB)
  { case Some(e, idx) =>
    { if checkMemPermission(ft, ac, priv, e.pte.PTE_T)
      then { mark_log(LOG_ADDRTR, "TLB hit!")
           -- update dirty bit in page table and TLB if needed
           ; when ac == Write and not e.pte.PTE_D
             do { var ent = e
                ; ent.pte.PTE_D <- true
                ; rawWriteData(ent.pteAddr, ent.&pte, 8)
                ; var tlb = TLB
                ; tlb([idx]) <- Some(ent)
                ; TLB <- tlb
                }
           ; Some(e.pAddr || (vAddr && e.vAddrMask))
           }
      else { mark_log(LOG_ADDRTR, "TLB permission check failure")
           ; None
           }
    }
    case None =>
    { mark_log(LOG_ADDRTR, "TLB miss!")
    ; match walk64(vAddr, ft, ac, priv, SCSR.sptbr, level)
      { case Some(pAddr, pte, i, global, pteAddr)  =>
        { TLB <- addToTLB(asid, vAddr, pAddr, pte, pteAddr, i, global, TLB)
        ; Some(pAddr)
        }
        case None   => None
      }
    }
  }
}

pAddr option translateAddr(vAddr::regType, ft::fetchType, ac::accessType) =
{ priv = privilege(if MCSR.mstatus.MMPRV and ft == Data
                   then MCSR.mstatus.MPRV1 else MCSR.mstatus.MPRV)
; match vmType(MCSR.mstatus.VM), priv
  { case Mbare,          _
    or       _,    Machine  => Some(vAddr)  -- no translation
    case Sv39,           _  => translate64(vAddr, ft, ac, priv, 2)
    case Sv48,           _  => translate64(vAddr, ft, ac, priv, 3)

    {- Comment out base/bound modes since there are no tests for them.

    case Mbb,   Machine
    or   Mbbid, Machine     => Some(vAddr)

     -}

    case     _,          _  => None
  }
}

---------------------------------------------------------------------------
-- Load Reservation
---------------------------------------------------------------------------

bool matchLoadReservation(vAddr::vAddr) =
    IsSome(ReserveLoad) and ValOf(ReserveLoad) == vAddr

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

-----------------------------------
-- JAL   rd, offs
-----------------------------------
define Branch > JAL(rd::reg, imm::imm20) =
{ addr = PC + SignExtend(imm) << 1
; if addr<0>
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
; if addr<0>
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
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

-----------------------------------
-- BNE   rs1, rs2, offs
-----------------------------------
define Branch > BNE(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 <> v2
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

-----------------------------------
-- BLT   rs1, rs2, offs
-----------------------------------
define Branch > BLT(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 < v2
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

-----------------------------------
-- BLTU  rs1, rs2, offs
-----------------------------------
define Branch > BLTU(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 <+ v2
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

-----------------------------------
-- BGE   rs1, rs2, offs
-----------------------------------
define Branch > BGE(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 >= v2
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

-----------------------------------
-- BGEU  rs1, rs2, offs
-----------------------------------
define Branch > BGEU(rs1::reg, rs2::reg, offs::imm12) =
{ v1 = if in32BitMode() then SignExtend(GPR(rs1)<31:0>) else GPR(rs1)
; v2 = if in32BitMode() then SignExtend(GPR(rs2)<31:0>) else GPR(rs2)
; if v1 >=+ v2
  then branchTo(PC + (SignExtend(offs) << 1))
  else noBranch(PC + Skip)
}

---------------------------------------------------------------------------
-- Load and Store Instructions
---------------------------------------------------------------------------

-----------------------------------
-- LW    rd, rs1, offs
-----------------------------------
define Load > LW(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = SignExtend(rawReadData(pAddr)<31:0>)
                        ; GPR(rd)  <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- LWU   rd, rs1, offs  (RV64I)
-----------------------------------
define Load > LWU(rd::reg, rs1::reg, offs::imm12) =
{ if in32BitMode()
  then signalException(Illegal_Instr)
  else { vAddr = GPR(rs1) + SignExtend(offs)
       ; match translateAddr(vAddr, Data, Read)
         { case Some(pAddr) => { val        = ZeroExtend(rawReadData(pAddr)<31:0>)
                               ; GPR(rd)   <- val
                               ; recordLoad(vAddr, val)
                               }
           case None        => signalAddressException(Load_Fault, vAddr)
         }
       }
}

-----------------------------------
-- LH    rd, rs1, offs
-----------------------------------
define Load > LH(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = SignExtend(rawReadData(pAddr)<15:0>)
                        ; GPR(rd)  <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- LHU   rd, rs1, offs
-----------------------------------
define Load > LHU(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = ZeroExtend(rawReadData(pAddr)<15:0>)
                        ; GPR(rd)  <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- LB    rd, rs1, offs
-----------------------------------
define Load > LB(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = SignExtend(rawReadData(pAddr)<7:0>)
                        ; GPR(rd)  <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- LBU   rd, rs1, offs
-----------------------------------
define Load > LBU(rd::reg, rs1::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = ZeroExtend(rawReadData(pAddr)<7:0>)
                        ; GPR(rd)  <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- LD    rd, rs1, offs  (RV64I)
-----------------------------------
define Load > LD(rd::reg, rs1::reg, offs::imm12) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; match translateAddr(vAddr, Data, Read)
           { case Some(pAddr) => { val      = rawReadData(pAddr)
                                 ; GPR(rd) <- val
                                 ; recordLoad(vAddr, val)
                                 }
             case None        => signalAddressException(Load_Fault, vAddr)
           }
         }

-----------------------------------
-- SW    rs1, rs2, offs
-----------------------------------
define Store > SW(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Write)
  { case Some(pAddr) => { data = GPR(rs2)
                        ; rawWriteData(pAddr, data, 4)
                        ; recordStore(vAddr, data, 4)
                        }
    case None        => signalAddressException(Store_AMO_Fault, vAddr)
  }
}

-----------------------------------
-- SH    rs1, rs2, offs
-----------------------------------
define Store > SH(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Write)
  { case Some(pAddr) => { data = GPR(rs2)
                        ; rawWriteData(pAddr, data, 2)
                        ; recordStore(vAddr, data, 2)
                        }
    case None        => signalAddressException(Store_AMO_Fault, vAddr)
  }
}

-----------------------------------
-- SB    rs1, rs2, offs
-----------------------------------
define Store > SB(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Write)
  { case Some(pAddr) => { data = GPR(rs2)
                        ; rawWriteData(pAddr, data, 1)
                        ; recordStore(vAddr, data, 1)
                        }
    case None        => signalAddressException(Store_AMO_Fault, vAddr)
  }
}

-----------------------------------
-- SD    rs1, rs2, offs (RV64I)
-----------------------------------
define Store > SD(rs1::reg, rs2::reg, offs::imm12) =
    if in32BitMode()
    then signalException(Illegal_Instr)
    else { vAddr = GPR(rs1) + SignExtend(offs)
         ; match translateAddr(vAddr, Data, Write)
           { case Some(pAddr) => { data = GPR(rs2)
                                 ; rawWriteData(pAddr, data, 8)
                                 ; recordStore(vAddr, data, 8)
                                 }
             case None        => signalAddressException(Store_AMO_Fault, vAddr)
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
define AMO > LR_W(aq::amo, rl::amo, rd::reg, rs1::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Read)
       { case Some(pAddr) => { writeRD(rd, SignExtend(rawReadData(pAddr)<31:0>))
                             ; ReserveLoad  <- Some(vAddr)
                             }
         case None        => signalAddressException(Load_Fault, vAddr)
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
           then signalAddressException(AMO_Misaligned, vAddr)
           else match translateAddr(vAddr, Data, Read)
                { case Some(pAddr) => { writeRD(rd, rawReadData(pAddr))
                                      ; ReserveLoad <- Some(vAddr)
                                      }
                  case None        => signalAddressException(Load_Fault, vAddr)
                }
         }

-----------------------------------
-- SC.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > SC_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else if not matchLoadReservation(vAddr)
       then writeRD(rd, 1)
       else match translateAddr(vAddr, Data, Read)
            { case Some(pAddr) => { data = GPR(rs2)
                                  ; rawWriteData(pAddr, data, 4)
                                  ; recordStore(vAddr, data, 4)
                                  ; writeRD(rd, 0)
                                  ; ReserveLoad  <- None
                                  }
              case None        => signalAddressException(Store_AMO_Fault, vAddr)
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
           then signalAddressException(AMO_Misaligned, vAddr)
           else if not matchLoadReservation(vAddr)
                then writeRD(rd, 1)
                else match translateAddr(vAddr, Data, Read)
                     { case Some(pAddr) => { data = GPR(rs2)
                                           ; rawWriteData(pAddr, data, 8)
                                           ; recordStore(vAddr, data, 8)
                                           ; writeRD(rd, 0)
                                           ; ReserveLoad  <- None
                                           }
                       case None        => signalAddressException(Store_AMO_Fault, vAddr)
                     }
         }

-----------------------------------
-- AMOSWAP.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOSWAP_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; rawWriteData(pAddr, data, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, data, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOSWAP.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOSWAP_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; rawWriteData(pAddr, data, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, data, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOADD.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOADD_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data + memv
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOADD.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOADD_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data + memv
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOXOR.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOXOR_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data ?? memv
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOXOR.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOXOR_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data ?? memv
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOAND.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOAND_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data && memv
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOAND.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOAND_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data && memv
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOOR.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOOR_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data || memv
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOOR.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOOR_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = data || memv
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMIN.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMIN_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = SignedMin(data, memv)
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMIN.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMIN_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = SignedMin(data, memv)
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMAX.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAX_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = SignedMax(data, memv)
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMAX.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAX_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = SignedMax(data, memv)
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMINU.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMINU_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = Min(data, memv)
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMINU.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMINU_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = Min(data, memv)
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMAXU.W [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAXU_W(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<1:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = SignExtend(rawReadData(pAddr)<31:0>)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = Max(data, memv)
                             ; rawWriteData(pAddr, val, 4)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 4)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
       }
}

-----------------------------------
-- AMOMAXU.D [aq,rl] rd, rs1, rs2
-----------------------------------
define AMO > AMOMAXU_D(aq::amo, rl::amo, rd::reg, rs1::reg, rs2::reg) =
{ vAddr = GPR(rs1)
; if vAddr<2:0> != 0
  then signalAddressException(AMO_Misaligned, vAddr)
  else match translateAddr(vAddr, Data, Write)
       { case Some(pAddr) => { memv = rawReadData(pAddr)
                             ; data = GPR(rs2)
                             ; GPR(rd) <- memv
                             ; val  = Max(data, memv)
                             ; rawWriteData(pAddr, val, 8)
                             ; recordLoad(vAddr, memv)
                             ; recordStore(vAddr, val, 8)
                             }
         case None        => signalAddressException(Store_AMO_Fault, vAddr)
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
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = rawReadData(pAddr)<31:0>
                        ; FPRS(rd) <- val
                        ; recordLoad(vAddr, ZeroExtend(val))
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- FSW   rs1, rs2, offs
-----------------------------------

define FPStore > FSW(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Write)
  { case Some(pAddr) => { data = FPRS(rs2)
                        ; rawWriteData(pAddr, ZeroExtend(data), 4)
                        ; recordStore(vAddr, ZeroExtend(data), 4)
                        }
    case None        => signalAddressException(Store_AMO_Fault, vAddr)
  }
}

-- Computational

-- TODO: Check for underflow after all rounding

-----------------------------------
-- FADD.S   rd, rs1, rs2
-----------------------------------

define FArith > FADD_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Add(r, FPRS(rs1), FPRS(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FSUB.S   rd, rs1, rs2
-----------------------------------

define FArith > FSUB_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Sub(r, FPRS(rs1), FPRS(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMUL.S   rd, rs1, rs2
-----------------------------------

define FArith > FMUL_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Mul(r, FPRS(rs1), FPRS(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FDIV.S   rd, rs1, rs2
-----------------------------------

define FArith > FDIV_S(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Div(r, FPRS(rs1), FPRS(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FSQRT.S   rd, rs
-----------------------------------

define FArith > FSQRT_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Sqrt(r, FPRS(rs)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMIN.S    rd, rs1, rs2
-----------------------------------
define FArith > FMIN_S(rd::reg, rs1::reg, rs2::reg) =
{ f1  = FPRS(rs1)
; f2  = FPRS(rs2)
; res = match FP32_Compare(f1, f2)
        { case FP_LT   => f1
          case FP_EQ   => f1
          case FP_GT   => f2
          case FP_UN   => if (   (FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2))
                              or (f1 == RV32_CanonicalNan and f2 == RV32_CanonicalNan))
                          then RV32_CanonicalNan
                          else -- either f1 or f2 should be a quiet NaN
                              if f1 == RV32_CanonicalNan then f2 else f1
        }
; writeFPRS(rd, res)
}

-----------------------------------
-- FMAX.S    rd, rs1, rs2
-----------------------------------
define FArith > FMAX_S(rd::reg, rs1::reg, rs2::reg) =
{ f1  = FPRS(rs1)
; f2  = FPRS(rs2)
; res = match FP32_Compare(f1, f2)
        { case FP_LT   => f2
          case FP_EQ   => f2
          case FP_GT   => f1
          case FP_UN   => if (   (FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2))
                              or (f1 == RV32_CanonicalNan and f2 == RV32_CanonicalNan))
                          then RV32_CanonicalNan
                          else -- either f1 or f2 should be a quiet NaN
                              if f1 == RV32_CanonicalNan then f2 else f1
        }
; writeFPRS(rd, res)
}

-----------------------------------
-- FMADD.S   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FMADD_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Add(r, FP32_Mul(r, FPRS(rs1), FPRS(rs2)), FPRS(rs3)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMSUB.S   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FMSUB_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Sub(r, FP32_Mul(r, FPRS(rs1), FPRS(rs2)), FPRS(rs3)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FNMADD.S   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FNMADD_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Neg(FP32_Add(r, FP32_Mul(r, FPRS(rs1), FPRS(rs2)), FPRS(rs3))))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FNMSUB.S   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FNMSUB_S(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_Neg(FP32_Sub(r, FP32_Mul(r, FPRS(rs1), FPRS(rs2)), FPRS(rs3))))
    case None    => signalException(Illegal_Instr)
  }
}

-- Conversions

-----------------------------------
-- FCVT.S.W   rd, rs
-----------------------------------

define FConv > FCVT_S_W(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_FromInt(r, [GPR(rs)<31:0>]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.S.WU  rd, rs
-----------------------------------

define FConv > FCVT_S_WU(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_FromInt(r, [0`1 : GPR(rs)<31:0>]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.W.S   rd, rs
-----------------------------------

define FConv > FCVT_W_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRS(rs)
                    ; val = ValOf(FP32_ToInt(r, inp))
                    ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                            then [0n2 ** 31 - 1]
                            else if inp == FP32_NegInf
                            then -[0n2 ** 31]
                            else if val > 2 ** 31 - 1
                            then [0n2 ** 31 - 1]
                            else if val < -2 ** 31
                            then -[0n2 ** 31]
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.WU.S  rd, rs
-----------------------------------

define FConv > FCVT_WU_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRS(rs)
                    ; val = ValOf(FP32_ToInt(r, inp))
                    ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                            then [0n2 ** 32 - 1]
                            else if inp == FP32_NegInf
                            then 0x0
                            else if val > 2 ** 32 - 1
                            then [0n2 ** 32 - 1]
                            else if val < 0
                            then 0x0
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.S.L   rd, rs
-----------------------------------

define FConv > FCVT_S_L(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_FromInt(r, [GPR(rs)]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.S.LU  rd, rs
-----------------------------------

define FConv > FCVT_S_LU(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP32_FromInt(r, [0`1 : GPR(rs)]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.L.S   rd, rs
-----------------------------------

define FConv > FCVT_L_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRS(rs)
                    ; val = ValOf(FP32_ToInt(r, inp))
                    ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                            then [0n2 ** 63 - 1]
                            else if inp == FP32_NegInf
                            then -[0n2 ** 63]
                            else if val > 2 ** 63 - 1
                            then [0n2 ** 63 - 1]
                            else if val < -2 ** 63
                            then -[0n2 ** 63]
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.LU.S  rd, rs
-----------------------------------

define FConv > FCVT_LU_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRS(rs)
                    ; val = ValOf(FP32_ToInt(r, inp))
                    ; res = if   FP32_IsNan(inp) or inp == FP32_PosInf
                            then [0n2 ** 64 - 1]
                            else if inp == FP32_NegInf
                            then 0x0
                            else if val > 2 ** 64 - 1
                            then [0n2 ** 64 - 1]
                            else if val < 0
                            then 0x0
                            else [val]
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
{ f1 = FPRS(rs1)
; f2 = FPRS(rs2)
; writeFPRS(rd, ([FP32_Sign(f2)]::bits(1)):f1<30:0>)
}

-----------------------------------
-- FSGNJN.S  rd, rs
-----------------------------------

define FConv > FSGNJN_S(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRS(rs1)
; f2 = FPRS(rs2)
; writeFPRS(rd, ([!FP32_Sign(f2)]::bits(1)):f1<30:0>)
}

-----------------------------------
-- FSGNJX.S  rd, rs
-----------------------------------

define FConv > FSGNJX_S(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRS(rs1)
; f2 = FPRS(rs2)
; writeFPRS(rd, ([FP32_Sign(f2)]::bits(1) ?? [FP32_Sign(f1)]::bits(1)) : f1<30:0>)
}

-- Movement

-----------------------------------
-- FMV.X.S   rd, rs
-----------------------------------

define FConv > FMV_X_S(rd::reg, rs::reg) =
    GPR(rd) <- SignExtend(FPRS(rs))

-----------------------------------
-- FMV.S.X   rd, rs
-----------------------------------

define FConv > FMV_S_X(rd::reg, rs::reg) =
    writeFPRS(rd, GPR(rs)<31:0>)

-- Comparisons

-----------------------------------
-- FEQ.S   rd, rs
-----------------------------------

define FArith > FEQ_S(rd::reg, rs1::reg, rs2::reg) =
{ f1  = FPRS(rs1)
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
{ f1  = FPRS(rs1)
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
{ f1  = FPRS(rs1)
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
{ var ret = 0x0`10
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
; ret<9> <- val == RV32_CanonicalNan
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
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Read)
  { case Some(pAddr) => { val       = rawReadData(pAddr)
                        ; FPRD(rd) <- val
                        ; recordLoad(vAddr, val)
                        }
    case None        => signalAddressException(Load_Fault, vAddr)
  }
}

-----------------------------------
-- FSD   rs1, rs2, offs
-----------------------------------

define FPStore > FSD(rs1::reg, rs2::reg, offs::imm12) =
{ vAddr = GPR(rs1) + SignExtend(offs)
; match translateAddr(vAddr, Data, Write)
  { case Some(pAddr) => { data = FPRD(rs2)
                        ; rawWriteData(pAddr, data, 8)
                        ; recordStore(vAddr, data, 8)
                        }
    case None        => signalAddressException(Store_AMO_Fault, vAddr)
  }
}

-- Computational

-- TODO: Check for underflow after all rounding

-----------------------------------
-- FADD.D   rd, rs1, rs2
-----------------------------------

define FArith > FADD_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Add(r, FPRD(rs1), FPRD(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FSUB.D   rd, rs1, rs2
-----------------------------------

define FArith > FSUB_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Sub(r, FPRD(rs1), FPRD(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMUL.D   rd, rs1, rs2
-----------------------------------

define FArith > FMUL_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Mul(r, FPRD(rs1), FPRD(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FDIV.D   rd, rs1, rs2
-----------------------------------

define FArith > FDIV_D(rd::reg, rs1::reg, rs2::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Div(r, FPRD(rs1), FPRD(rs2)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FSQRT.D   rd, rs
-----------------------------------

define FArith > FSQRT_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Sqrt(r, FPRD(rs)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMIN.D    rd, rs1, rs2
-----------------------------------
define FArith > FMIN_D(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRD(rs1)
; f2 = FPRD(rs2)
; res = match FP64_Compare(f1, f2)
        { case FP_LT => f1
          case FP_EQ => f1
          case FP_GT => f2
          case FP_UN => if (   (FP64_IsSignalingNan(f1) or FP64_IsSignalingNan(f2))
                            or (f1 == RV64_CanonicalNan and f2 == RV64_CanonicalNan))
                        then RV64_CanonicalNan
                        else -- either f1 or f2 should be a quiet NaN
                            if f1 == RV64_CanonicalNan then f2 else f1

        }
; writeFPRD(rd, res)
}

-----------------------------------
-- FMAX.D    rd, rs1, rs2
-----------------------------------
define FArith > FMAX_D(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRD(rs1)
; f2 = FPRD(rs2)
; res = match FP64_Compare(f1, f2)
        { case FP_LT => f2
          case FP_EQ => f2
          case FP_GT => f1
          case FP_UN => if (   (FP64_IsSignalingNan(f1) or FP64_IsSignalingNan(f2))
                            or (f1 == RV64_CanonicalNan and f2 == RV64_CanonicalNan))
                        then RV64_CanonicalNan
                        else -- either f1 or f2 should be a quiet NaN
                            if f1 == RV64_CanonicalNan then f2 else f1
  }
; writeFPRD(rd, res)
}

-----------------------------------
-- FMADD.D   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FMADD_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Add(r, FP64_Mul(r, FPRD(rs1), FPRD(rs2)), FPRD(rs3)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FMSUB.D   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FMSUB_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Sub(r, FP64_Mul(r, FPRD(rs1), FPRD(rs2)), FPRD(rs3)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FNMADD.D   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FNMADD_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Neg(FP64_Add(r, FP64_Mul(r, FPRD(rs1), FPRD(rs2)), FPRD(rs3))))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FNMSUB.D   rd, rs1, rs2, rs3
-----------------------------------

define FArith > FNMSUB_D(rd::reg, rs1::reg, rs2::reg, rs3::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_Neg(FP64_Sub(r, FP64_Mul(r, FPRD(rs1), FPRD(rs2)), FPRD(rs3))))
    case None    => signalException(Illegal_Instr)
  }
}

-- Conversions

-----------------------------------
-- FCVT.D.W   rd, rs
-----------------------------------

define FConv > FCVT_D_W(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_FromInt(r, [GPR(rs)<31:0>]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.D.WU  rd, rs
-----------------------------------

define FConv > FCVT_D_WU(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_FromInt(r, [0`1 : GPR(rs)<31:0>]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.W.D   rd, rs
-----------------------------------

define FConv > FCVT_W_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRD(rs)
                    ; val = ValOf(FP64_ToInt(r, inp))
                    ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                            then [0n2 ** 31 - 1]
                            else if inp == FP64_NegInf
                            then -[0n2 ** 31]
                            else if val > 2 ** 31 - 1
                            then [0n2 ** 31 - 1]
                            else if val < -2 ** 31
                            then -[0n2 ** 31]
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.WU.D  rd, rs
-----------------------------------

define FConv > FCVT_WU_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRD(rs)
                    ; val = ValOf(FP64_ToInt(r, inp))
                    ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                            then [0n2 ** 32 - 1]
                            else if inp == FP64_NegInf
                            then 0x0
                            else if val > 2 ** 32 - 1
                            then [0n2 ** 32 - 1]
                            else if val < 0
                            then 0x0
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.D.L   rd, rs
-----------------------------------

define FConv > FCVT_D_L(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_FromInt(r, [GPR(rs)]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.D.LU  rd, rs
-----------------------------------

define FConv > FCVT_D_LU(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP64_FromInt(r, [0`1 : GPR(rs)]::int))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.L.D   rd, rs
-----------------------------------

define FConv > FCVT_L_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRD(rs)
                    ; val = ValOf(FP64_ToInt(r, inp))
                    ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                            then [0n2 ** 63 - 1]
                            else if inp == FP64_NegInf
                            then -[0n2 ** 63]
                            else if val > 2 ** 63 - 1
                            then [0n2 ** 63 - 1]
                            else if val < -2 ** 63
                            then -[0n2 ** 63]
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.LU.D  rd, rs
-----------------------------------

define FConv > FCVT_LU_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => { inp = FPRD(rs)
                    ; val = ValOf(FP64_ToInt(r, inp))
                    ; res = if   FP64_IsNan(inp) or inp == FP64_PosInf
                            then [0n2 ** 64 - 1]
                            else if inp == FP64_NegInf
                            then 0x0
                            else if val > 2 ** 64 - 1
                            then [0n2 ** 64 - 1]
                            else if val < 0
                            then 0x0
                            else [val]
                    ; writeRD(rd, res)
                    }
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.S.D  rd, rs
-----------------------------------

define FConv > FCVT_S_D(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRS(rd, FP64_ToFP32(r, FPRD(rs)))
    case None    => signalException(Illegal_Instr)
  }
}

-----------------------------------
-- FCVT.D.S  rd, rs
-----------------------------------

define FConv > FCVT_D_S(rd::reg, rs::reg, fprnd::fprnd) =
{ match round(fprnd)
  { case Some(r) => writeFPRD(rd, FP32_ToFP64(FPRS(rs)))
    case None    => signalException(Illegal_Instr)
  }
}

-- Sign injection

-----------------------------------
-- FSGNJ.D  rd, rs
-----------------------------------

define FConv > FSGNJ_D(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRD(rs1)
; f2 = FPRD(rs2)
; writeFPRD(rd, ([FP64_Sign(f2)]::bits(1)):f1<62:0>)
}

-----------------------------------
-- FSGNJN.D  rd, rs
-----------------------------------

define FConv > FSGNJN_D(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRD(rs1)
; f2 = FPRD(rs2)
; writeFPRD(rd, ([!FP64_Sign(f2)]::bits(1)):f1<62:0>)
}

-----------------------------------
-- FSGNJX.D  rd, rs
-----------------------------------

define FConv > FSGNJX_D(rd::reg, rs1::reg, rs2::reg) =
{ f1 = FPRD(rs1)
; f2 = FPRD(rs2)
; writeFPRD(rd, ([FP64_Sign(f2)]::bits(1) ?? [FP64_Sign(f1)]::bits(1)) : f1<62:0>)
}

-- Movement

-----------------------------------
-- FMV.X.D   rd, rs
-----------------------------------

define FConv > FMV_X_D(rd::reg, rs::reg) =
    GPR(rd) <- SignExtend(FPRD(rs))

-----------------------------------
-- FMV.D.X   rd, rs
-----------------------------------

define FConv > FMV_D_X(rd::reg, rs::reg) =
    writeFPRD(rd, GPR(rs))

-- Comparisons

-----------------------------------
-- FEQ.D   rd, rs
-----------------------------------

define FArith > FEQ_D(rd::reg, rs1::reg, rs2::reg) =
{ f1  = FPRD(rs1)
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
{ f1  = FPRD(rs1)
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
{ f1  = FPRD(rs1)
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
{ var ret = 0x0`10
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
; ret<9> <- val == RV64_CanonicalNan
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

define System > EBREAK = signalException(Breakpoint)

-----------------------------------
-- ERET
-----------------------------------
define System > ERET   =
    NextFetch <- Some(Ereturn)

-----------------------------------
-- MRTS
-----------------------------------
define System > MRTS   =
{ SCSR.scause       <- MCSR.mcause
; SCSR.sbadaddr     <- MCSR.mbadaddr
; SCSR.sepc         <- MCSR.mepc

; MCSR.mstatus.MPRV <- privLevel(Supervisor)

; NextFetch         <- Some(Mrts)
}

-----------------------------------
-- WFI
-----------------------------------
define System > WFI    = nothing

-- Control and Status Registers

bool checkCSROp(csr::imm12, rs1::reg, a::accessType) =
    is_CSR_defined(csr) and check_CSR_access(csrRW(csr), csrPR(csr), curPrivilege(), a)

-----------------------------------
-- CSRRW  rd, rs1, imm
-----------------------------------
define System > CSRRW(rd::reg, rs1::reg, csr::imm12) =
    if checkCSROp(csr, rs1, Write)
    then { val = CSR(csr)
         ; writeCSR(csr, GPR(rs1))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-----------------------------------
-- CSRRS  rd, rs1, imm
-----------------------------------
define System > CSRRS(rd::reg, rs1::reg, csr::imm12) =
    if checkCSROp(csr, rs1, if rs1 == 0 then Read else Write)
    then { val = CSR(csr)
         ; when rs1 != 0
           do writeCSR(csr, val || GPR(rs1))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-----------------------------------
-- CSRRC  rd, rs1, imm
-----------------------------------
define System > CSRRC(rd::reg, rs1::reg, csr::imm12) =
    if checkCSROp(csr, rs1, if rs1 == 0 then Read else Write)
    then { val = CSR(csr)
         ; when rs1 != 0
           do writeCSR(csr, val && ~GPR(rs1))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-----------------------------------
-- CSRRWI rd, rs1, imm
-----------------------------------
define System > CSRRWI(rd::reg, zimm::reg, csr::imm12) =
    if checkCSROp(csr, zimm, if zimm == 0 then Read else Write)
    then { val = CSR(csr)
         ; when zimm != 0
           do writeCSR(csr, ZeroExtend(zimm))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-----------------------------------
-- CSRRSI rd, rs1, imm
-----------------------------------
define System > CSRRSI(rd::reg, zimm::reg, csr::imm12) =
    if checkCSROp(csr, zimm, if zimm == 0 then Read else Write)
    then { val = CSR(csr)
         ; when zimm != 0
           do writeCSR(csr, val || ZeroExtend(zimm))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-----------------------------------
-- CSRRCI rd, rs1, imm
-----------------------------------
define System > CSRRCI(rd::reg, zimm::reg, csr::imm12) =
    if checkCSROp(csr, zimm, if zimm == 0 then Read else Write)
    then { val = CSR(csr)
         ; when zimm != 0
           do writeCSR(csr, val && ~ZeroExtend(zimm))
         ; writeRD(rd, val)
         }
    else signalException(Illegal_Instr)

-- Address translation cache flush

-----------------------------------
-- SFENCE.VM
-----------------------------------
define System > SFENCE_VM(rs1::reg) =
{ addr = if rs1 == 0 then None else Some(GPR(rs1))
; TLB <- flushTLB(curASID(), addr, TLB)
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

define Internal > FETCH_FAULT(addr::regType) =
{ signalAddressException(Fetch_Fault, [addr])
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

FetchResult Fetch() =
{ vPC = PC
; if vPC<0>
  then F_Error(Internal(FETCH_MISALIGNED(vPC)))
  else match translateAddr(vPC, Instruction, Read)
       { case Some(pPC) => { instw = rawReadInst(pPC)
                           ; setupDelta(vPC, instw)
                           ; F_Result(instw)
                           }
         case None      => F_Error(Internal(FETCH_FAULT(vPC)))
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
     case '000100000000  00000 000 00000 11100 11' => System(  ERET)
     case '001100000101  00000 000 00000 11100 11' => System( MRTS)
     case '000100000010  00000 000 00000 11100 11' => System(  WFI)

     case '000100000001    rs1 000 00000 11100 11' => System(SFENCE_VM(rs1))

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
     case System(  ERET)                    => pN0type("ERET")
     case System(  MRTS)                    => pN0type("MRTS")
     case System(   WFI)                    => pN0type("WFI")

     case System( CSRRW(rd, rs1, csr))      => pCSRtype("CSRRW",  rd, rs1, csr)
     case System( CSRRS(rd, rs1, csr))      => pCSRtype("CSRRS",  rd, rs1, csr)
     case System( CSRRC(rd, rs1, csr))      => pCSRtype("CSRRC",  rd, rs1, csr)
     case System(CSRRWI(rd, imm, csr))      => pCSRItype("CSRRWI", rd, imm, csr)
     case System(CSRRSI(rd, imm, csr))      => pCSRItype("CSRRSI", rd, imm, csr)
     case System(CSRRCI(rd, imm, csr))      => pCSRItype("CSRRCI", rd, imm, csr)

     case System(SFENCE_VM(rs1))            => pN1type("SFENCE.VM", rs1)

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
     case System(  ERET)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x100)
     case System(  MRTS)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x305)
     case System(   WFI)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x102)

     case System(SFENCE_VM(rs1))            =>  Itype(opc(0x1C), 0, 0, rs1, 0x101)

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
     case '001 i5`1 r     imi`5                01' => ArithI(ADDIW( r, r, i5 ^ 7 : imi))
     case '010 i5`1 rd    imi`5                01' => ArithI( ADDI(rd, 0, i5 ^ 7 : imi))
     case '011 0    00010 00000                01' => UnknownInstruction
     case '011 i9`1 00010 i4`1 i6`1 imi`2 i5`1 01' => ArithI( ADDI( 2, 2, i9 ^ 3 : imi : i6 : i5 : i4 : '0000'))

     case '011 0     rd 00000 01' => UnknownInstruction
     case '011 i17`1 rd imi`5 01' => ArithI(LUI(rd, i17 ^ 3 : imi : '000000000000'))

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

type rvcreg = bits(3)

half CBtype(o::bits(2), f3::bits(3), rs1::rvcreg, imm::bits(8)) =
    f3 : [imm<7>]::bits(1) : imm<3:2> : rs1 : imm<6:5> : imm<1:0> : [imm<5>]::bits(1) : o

construct rvc { Comp :: half, Full :: word }

rvc EncodeRVC(i::instruction) =
   match i
   { case Branch(  BEQ('01 rs1', '00000', '00000 imm')) => Comp(CBtype(1, 0, rs1, '0' : imm))
     case Branch(  BEQ('01 rs1', '00000', '11111 imm')) => Comp(CBtype(1, 0, rs1, '1' : imm))
     -- case Branch(  BNE(rs1, rs2, imm))      => SBtype(opc(0x18), 1, rs1, rs2, imm)
     -- case Branch(  BLT(rs1, rs2, imm))      => SBtype(opc(0x18), 4, rs1, rs2, imm)
     -- case Branch(  BGE(rs1, rs2, imm))      => SBtype(opc(0x18), 5, rs1, rs2, imm)
     -- case Branch( BLTU(rs1, rs2, imm))      => SBtype(opc(0x18), 6, rs1, rs2, imm)
     -- case Branch( BGEU(rs1, rs2, imm))      => SBtype(opc(0x18), 7, rs1, rs2, imm)

     -- case Branch( JALR(rd, rs1, imm))       =>  Itype(opc(0x19), 0, rd, rs1, imm)
     -- case Branch(  JAL(rd, imm))            => UJtype(opc(0x1b), rd, imm)

     -- case ArithI(  LUI(rd, imm))            =>  Utype(opc(0x0D), rd, imm)
     -- case ArithI(AUIPC(rd, imm))            =>  Utype(opc(0x05), rd, imm)

     -- case ArithI( ADDI(rd, rs1, imm))       =>  Itype(opc(0x04), 0, rd, rs1, imm)
     -- case  Shift( SLLI(rd, rs1, imm))       =>  Itype(opc(0x04), 1, rd, rs1, '000000' : imm)
     -- case ArithI( SLTI(rd, rs1, imm))       =>  Itype(opc(0x04), 2, rd, rs1, imm)
     -- case ArithI(SLTIU(rd, rs1, imm))       =>  Itype(opc(0x04), 3, rd, rs1, imm)
     -- case ArithI( XORI(rd, rs1, imm))       =>  Itype(opc(0x04), 4, rd, rs1, imm)
     -- case  Shift( SRLI(rd, rs1, imm))       =>  Itype(opc(0x04), 5, rd, rs1, '000000' : imm)
     -- case  Shift( SRAI(rd, rs1, imm))       =>  Itype(opc(0x04), 5, rd, rs1, '010000' : imm)
     -- case ArithI(  ORI(rd, rs1, imm))       =>  Itype(opc(0x04), 6, rd, rs1, imm)
     -- case ArithI( ANDI(rd, rs1, imm))       =>  Itype(opc(0x04), 7, rd, rs1, imm)

     -- case ArithR(  ADD(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, 0)
     -- case ArithR(  SUB(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, 0x20)
     -- case  Shift(  SLL(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 1, rd, rs1, rs2, 0)
     -- case ArithR(  SLT(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 2, rd, rs1, rs2, 0)
     -- case ArithR( SLTU(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 3, rd, rs1, rs2, 0)
     -- case ArithR(  XOR(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 4, rd, rs1, rs2, 0)
     -- case  Shift(  SRL(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, 0)
     -- case  Shift(  SRA(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, 0x20)
     -- case ArithR(   OR(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 6, rd, rs1, rs2, 0)
     -- case ArithR(  AND(rd, rs1, rs2))       =>  Rtype(opc(0x0C), 7, rd, rs1, rs2, 0)

     -- case ArithI(ADDIW(rd, rs1, imm))       =>  Itype(opc(0x06), 0, rd, rs1, imm)
     -- case  Shift(SLLIW(rd, rs1, imm))       =>  Itype(opc(0x06), 1, rd, rs1, '0000000' : imm)
     -- case  Shift(SRLIW(rd, rs1, imm))       =>  Itype(opc(0x06), 5, rd, rs1, '0000000' : imm)
     -- case  Shift(SRAIW(rd, rs1, imm))       =>  Itype(opc(0x06), 5, rd, rs1, '0100000' : imm)

     -- case ArithR( ADDW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0000000')
     -- case ArithR( SUBW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0100000')
     -- case  Shift( SLLW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 1, rd, rs1, rs2, '0000000')
     -- case  Shift( SRLW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0000000')
     -- case  Shift( SRAW(rd, rs1, rs2))       =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0100000')

     -- case MulDiv(    MUL(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 0, rd, rs1, rs2, '0000001')
     -- case MulDiv(   MULH(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 1, rd, rs1, rs2, '0000001')
     -- case MulDiv( MULHSU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 2, rd, rs1, rs2, '0000001')
     -- case MulDiv(  MULHU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 3, rd, rs1, rs2, '0000001')
     -- case MulDiv(    DIV(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 4, rd, rs1, rs2, '0000001')
     -- case MulDiv(   DIVU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 5, rd, rs1, rs2, '0000001')
     -- case MulDiv(    REM(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 6, rd, rs1, rs2, '0000001')
     -- case MulDiv(   REMU(rd, rs1, rs2))     =>  Rtype(opc(0x0C), 7, rd, rs1, rs2, '0000001')

     -- case MulDiv(   MULW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 0, rd, rs1, rs2, '0000001')
     -- case MulDiv(   DIVW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 4, rd, rs1, rs2, '0000001')
     -- case MulDiv(  DIVUW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 5, rd, rs1, rs2, '0000001')
     -- case MulDiv(   REMW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 6, rd, rs1, rs2, '0000001')
     -- case MulDiv(  REMUW(rd, rs1, rs2))     =>  Rtype(opc(0x0E), 7, rd, rs1, rs2, '0000001')

     -- case   Load(   LB(rd, rs1, imm))       =>  Itype(opc(0x00), 0, rd, rs1, imm)
     -- case   Load(   LH(rd, rs1, imm))       =>  Itype(opc(0x00), 1, rd, rs1, imm)
     -- case   Load(   LW(rd, rs1, imm))       =>  Itype(opc(0x00), 2, rd, rs1, imm)
     -- case   Load(   LD(rd, rs1, imm))       =>  Itype(opc(0x00), 3, rd, rs1, imm)
     -- case   Load(  LBU(rd, rs1, imm))       =>  Itype(opc(0x00), 4, rd, rs1, imm)
     -- case   Load(  LHU(rd, rs1, imm))       =>  Itype(opc(0x00), 5, rd, rs1, imm)
     -- case   Load(  LWU(rd, rs1, imm))       =>  Itype(opc(0x00), 6, rd, rs1, imm)

     -- case  Store(   SB(rs1, rs2, imm))      =>  Stype(opc(0x08), 0, rs1, rs2, imm)
     -- case  Store(   SH(rs1, rs2, imm))      =>  Stype(opc(0x08), 1, rs1, rs2, imm)
     -- case  Store(   SW(rs1, rs2, imm))      =>  Stype(opc(0x08), 2, rs1, rs2, imm)
     -- case  Store(   SD(rs1, rs2, imm))      =>  Stype(opc(0x08), 3, rs1, rs2, imm)

     -- case   FENCE(rd, rs1, pred, succ)      =>  Itype(opc(0x03), 0, rd, rs1, '0000' : pred : succ)
     -- case FENCE_I(rd, rs1, imm)             =>  Itype(opc(0x03), 1, rd, rs1, imm)

     -- case FArith(  FADD_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x00)
     -- case FArith(  FSUB_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x04)
     -- case FArith(  FMUL_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x08)
     -- case FArith(  FDIV_S(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x0c)
     -- case FArith( FSQRT_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs,    0, 0x2c)
     -- case FArith(  FMIN_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x14)
     -- case FArith(  FMAX_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x14)
     -- case FArith(   FEQ_S(rd, rs1, rs2))      => Rtype(opc(0x14), 2,   rd, rs1, rs2, 0x50)
     -- case FArith(   FLT_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x50)
     -- case FArith(   FLE_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x50)

     -- case FArith(  FADD_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x01)
     -- case FArith(  FSUB_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x05)
     -- case FArith(  FMUL_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x09)
     -- case FArith(  FDIV_D(rd, rs1, rs2, frm)) => Rtype(opc(0x14), frm, rd, rs1, rs2, 0x0d)
     -- case FArith( FSQRT_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs,    0, 0x2d)
     -- case FArith(  FMIN_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x15)
     -- case FArith(  FMAX_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x15)
     -- case FArith(   FEQ_D(rd, rs1, rs2))      => Rtype(opc(0x14), 2,   rd, rs1, rs2, 0x51)
     -- case FArith(   FLT_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1,   rd, rs1, rs2, 0x51)
     -- case FArith(   FLE_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0,   rd, rs1, rs2, 0x51)

     -- case FPLoad(  FLW(rd, rs1, imm))         => Itype(opc(0x01), 2, rd, rs1, imm)
     -- case FPLoad(  FLD(rd, rs1, imm))         => Itype(opc(0x01), 3, rd, rs1, imm)
     -- case FPStore( FSW(rs1, rs2, imm))        => Stype(opc(0x09), 2, rs1, rs2, imm)
     -- case FPStore( FSD(rs1, rs2, imm))        => Stype(opc(0x09), 3, rs1, rs2, imm)

     -- case FArith( FMADD_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x10), frm, rd, rs1, rs2, rs3, 0)
     -- case FArith( FMSUB_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x11), frm, rd, rs1, rs2, rs3, 0)
     -- case FArith(FNMSUB_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x12), frm, rd, rs1, rs2, rs3, 0)
     -- case FArith(FNMADD_S(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x13), frm, rd, rs1, rs2, rs3, 0)

     -- case FArith( FMADD_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x10), frm, rd, rs1, rs2, rs3, 1)
     -- case FArith( FMSUB_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x11), frm, rd, rs1, rs2, rs3, 1)
     -- case FArith(FNMSUB_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x12), frm, rd, rs1, rs2, rs3, 1)
     -- case FArith(FNMADD_D(rd, rs1, rs2, rs3, frm)) => R4type(opc(0x13), frm, rd, rs1, rs2, rs3, 1)

     -- case FConv(  FSGNJ_S(rd, rs1, rs2))      => Rtype(opc(0x14), 0, rd, rs1, rs2, 0x10)
     -- case FConv( FSGNJN_S(rd, rs1, rs2))      => Rtype(opc(0x14), 1, rd, rs1, rs2, 0x10)
     -- case FConv( FSGNJX_S(rd, rs1, rs2))      => Rtype(opc(0x14), 2, rd, rs1, rs2, 0x10)

     -- case FConv( FCVT_W_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x60)
     -- case FConv(FCVT_WU_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x60)
     -- case FConv(  FMV_X_S(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x70)
     -- case FConv( FCLASS_S(rd, rs))            => Rtype(opc(0x14), 1,   rd, rs, 0, 0x70)
     -- case FConv( FCVT_S_W(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x68)
     -- case FConv(FCVT_S_WU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x68)
     -- case FConv(  FMV_S_X(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x78)

     -- case FConv(  FSGNJ_D(rd, rs1, rs2))      => Rtype(opc(0x14), 0, rd, rs1, rs2, 0x11)
     -- case FConv( FSGNJN_D(rd, rs1, rs2))      => Rtype(opc(0x14), 1, rd, rs1, rs2, 0x11)
     -- case FConv( FSGNJX_D(rd, rs1, rs2))      => Rtype(opc(0x14), 2, rd, rs1, rs2, 0x11)

     -- case FConv( FCVT_W_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x61)
     -- case FConv(FCVT_WU_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x61)
     -- case FConv( FCLASS_D(rd, rs))            => Rtype(opc(0x14), 1,   rd, rs, 0, 0x71)
     -- case FConv( FCVT_D_W(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x69)
     -- case FConv(FCVT_D_WU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x69)
     -- case FConv( FCVT_S_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 1, 0x20)
     -- case FConv( FCVT_D_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 0, 0x21)

     -- case FConv( FCVT_L_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x60)
     -- case FConv(FCVT_LU_S(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x60)
     -- case FConv( FCVT_S_L(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x68)
     -- case FConv(FCVT_S_LU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x68)
     -- case FConv( FCVT_L_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x61)
     -- case FConv(FCVT_LU_D(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x61)
     -- case FConv(  FMV_X_D(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x71)
     -- case FConv( FCVT_D_L(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 2, 0x69)
     -- case FConv(FCVT_D_LU(rd, rs, frm))       => Rtype(opc(0x14), frm, rd, rs, 3, 0x69)
     -- case FConv(  FMV_D_X(rd, rs))            => Rtype(opc(0x14), 0,   rd, rs, 0, 0x79)

     -- case AMO(     LR_W(aq, rl, rd, rs1))       => Rtype(opc(0x0B), 2, rd, rs1, 0,   amofunc('00010', aq, rl))
     -- case AMO(     LR_D(aq, rl, rd, rs1))       => Rtype(opc(0x0B), 3, rd, rs1, 0,   amofunc('00010', aq, rl))
     -- case AMO(     SC_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00011', aq, rl))
     -- case AMO(     SC_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00010', aq, rl))

     -- case AMO(AMOSWAP_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00001', aq, rl))
     -- case AMO( AMOADD_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00000', aq, rl))
     -- case AMO( AMOXOR_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('00100', aq, rl))
     -- case AMO( AMOAND_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('01100', aq, rl))
     -- case AMO(  AMOOR_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('01000', aq, rl))
     -- case AMO( AMOMIN_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('10000', aq, rl))
     -- case AMO( AMOMAX_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('10100', aq, rl))
     -- case AMO(AMOMINU_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('11000', aq, rl))
     -- case AMO(AMOMAXU_W(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 2, rd, rs1, rs2, amofunc('11100', aq, rl))

     -- case AMO(AMOSWAP_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00001', aq, rl))
     -- case AMO( AMOADD_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00000', aq, rl))
     -- case AMO( AMOXOR_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('00100', aq, rl))
     -- case AMO( AMOAND_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('01100', aq, rl))
     -- case AMO(  AMOOR_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('01000', aq, rl))
     -- case AMO( AMOMIN_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('10000', aq, rl))
     -- case AMO( AMOMAX_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('10100', aq, rl))
     -- case AMO(AMOMINU_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('11000', aq, rl))
     -- case AMO(AMOMAXU_D(aq, rl, rd, rs1, rs2))  => Rtype(opc(0x0B), 3, rd, rs1, rs2, amofunc('11100', aq, rl))

     -- case System( ECALL)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x000)
     -- case System(EBREAK)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x001)
     -- case System(  ERET)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x100)
     -- case System(  MRTS)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x305)
     -- case System(   WFI)                    =>  Itype(opc(0x1C), 0, 0, 0, 0x102)

     -- case System(SFENCE_VM(rs1))            =>  Itype(opc(0x1C), 0, 0, rs1, 0x101)

     -- case System( CSRRW(rd, rs1, csr))      =>  Itype(opc(0x1C), 1, rd, rs1, csr)
     -- case System( CSRRS(rd, rs1, csr))      =>  Itype(opc(0x1C), 2, rd, rs1, csr)
     -- case System( CSRRC(rd, rs1, csr))      =>  Itype(opc(0x1C), 3, rd, rs1, csr)
     -- case System(CSRRWI(rd, imm, csr))      =>  Itype(opc(0x1C), 5, rd, imm, csr)
     -- case System(CSRRSI(rd, imm, csr))      =>  Itype(opc(0x1C), 6, rd, imm, csr)
     -- case System(CSRRCI(rd, imm, csr))      =>  Itype(opc(0x1C), 7, rd, imm, csr)

     -- case UnknownInstruction                => 0

     -- case Internal(FETCH_MISALIGNED(_))     => 0
     -- case Internal(FETCH_FAULT(_))          => 0
     case _ => Full(Encode(i))
   }

---------------------------------------------------------------------------
-- The next state function
---------------------------------------------------------------------------

string log_instruction(w::word, inst::instruction) =
    "instr " : [procID] : " " : [[c_instret(procID)]::nat] :
    " 0x" : hex64(PC) : " : " : hex32(w) : "   " : instructionToString(inst)

declare done :: bool   -- Flag to request termination

nat exitCode() =
    [ExitCode]::nat

-- The clock/timer factor here is arbitrary, except it that if it is
-- >= approx 200, some 32-bit -pt- tests unexpectedly pass.

nat CYCLES_PER_TIMER_TICK = 200

unit tickClock() =
{ cycles             = c_cycles(procID) + 1
; c_cycles(procID)  <- cycles
; clock             <- cycles div [CYCLES_PER_TIMER_TICK]
}

unit incrInstret() =
    c_instret(procID) <- c_instret(procID) + 1

unit checkTimers() =
{ when (clock >+ MCSR.mtimecmp + MCSR.mtime_delta)
  do MCSR.mip.MTIP <- true
; when (clock >+ SCSR.stimecmp + SCSR.stime_delta)
  do MCSR.mip.STIP <- true
}

unit Next =
{ clear_logs()

-- Handle the char i/o section of the Berkeley HTIF protocol
-- following cissrStandalone.c.
; when MCSR.mtohost <> 0x0
  do   { mark_log(LOG_IO, log_tohost(MCSR.mtohost))
       -- The HTIF protocol sets bit 0 to indicate exit, with actual
       -- exit code left-shifted by 1 bit.
       ; if MCSR.mtohost<0>
         then { done <- true
              ; ExitCode <- MCSR.mtohost >> 1
              }
         else MCSR.mtohost <- 0x0   -- TODO: rest of relevant HTIF protocol
       }

; match Fetch()
  { case F_Result(Half(h)) =>
    { inst = DecodeRVC(h)
    ; mark_log(LOG_INSN, log_instruction(ZeroExtend(h), inst))
    ; Run(inst)
    }
    case F_Result(Word(w)) =>
    { inst = Decode(w)
    ; mark_log(LOG_INSN, log_instruction(w, inst))
    ; Run(inst)
    }
    case F_Error(inst)  =>
    { mark_log(LOG_INSN, log_instruction([0::word], inst))
    ; Run(inst)
    }
  }

; checkTimers()     -- this can trigger timer interrupts

; match NextFetch, checkInterrupts()
  { case None, None =>
             { incrInstret()
             ; PC <- PC + Skip
             }
    case None, Some(i, p) =>
             { incrInstret()
             ; takeTrap(true, interruptIndex(i), PC + Skip, None, p)
             }
    case Some(BranchTo(addr)), _ =>
             { incrInstret()
             ; NextFetch    <- None
             ; PC           <- addr
             }
    case Some(Ereturn), _ =>
             { incrInstret()
             ; NextFetch    <- None
             ; PC           <- curEPC()

             ; from = curPrivilege()
             ; MCSR.mstatus <- popPrivilegeStack(MCSR.mstatus)
             ; to   = curPrivilege()

             ; mark_log(LOG_INSN, ["exception return from " : privName(from)
                                   : " to " : privName(to)])
             }
    case Some(Trap(t)), _ =>
             { NextFetch    <- None
             -- We currently don't implement delegation, so always trap to M-mode.
             ; takeTrap(false, excCode(t.trap), PC, t.badaddr, Machine)
             }
    case Some(Mrts), _ =>
             { incrInstret()
             ; NextFetch    <- None
             ; PC           <- SCSR.stvec
             }
  }

; tickClock()
}

unit initIdent(arch::Architecture) =
{ MCSR.mcpuid.ArchBase <- archBase(arch)
; MCSR.mcpuid.U        <- true
; MCSR.mcpuid.S        <- true
; MCSR.mcpuid.M        <- true
; MCSR.mcpuid.I        <- true

; MCSR.mimpid.RVSource <- 0x8000 -- anonymous source
; MCSR.mimpid.RVImpl   <- 0x0
}

unit initMachine(hartid::id) =
{ -- Startup in Mbare machine mode, with interrupts disabled.
  MCSR.mstatus.VM   <- vmMode(Mbare)
; MCSR.mstatus.MPRV <- privLevel(Machine)
; MCSR.mstatus.MIE  <- false
  -- initialize extension context state
; MCSR.mstatus.MFS  <- ext_status(Initial)
; MCSR.mstatus.MXS  <- ext_status(Off)
; MCSR.mstatus.MSD  <- false

  -- MPRV1/MIE1 and MPRV2/MIE2 are unspecified.

  -- Setup hartid
; MCSR.mhartid      <- ZeroExtend(hartid)
  -- Initialize mtvec to lower address (other option is 0xF...FFE00)
; MCSR.mtvec        <- ZeroExtend(0x100`16)
}
-- This initializes each core (via setting procID appropriately) on
-- startup before execution begins.
unit initRegs(pc::nat) =
{ -- TODO: Check if the specs specify the initial values of the registers
  -- on startup.  Initializing to an arbitrary value causes issues with
  -- the verifier, which assumes 0-valued initialization.
  for i in 0 .. 31 do
    gpr([i])   <- 0x0
; for i in 0 .. 31 do
    fpr([i])   <- 0x0

; PC           <- [pc]
; NextFetch    <- None
; done         <- false
}
