(* ------------------------------------------------------------------------
   Selftest of riscv_stepLib, run by Holmake when HOLSELFTESTLEVEL is set.

   riscv_step_hex is run on one encoding of every riscv_dict entry (for the
   floating-point instructions with a rounding-mode field, one with RNE,
   one with RMM and one with the dynamic mode; for the CSR instructions,
   one for each CSR that the
   step theorems must cover), on a read and two writes of every CSR of the
   hart and of some addresses that are not CSRs, and on some edge cases.
   Each theorem must be

     hyps |- NextRISCV s = SOME s'

   with s' a record update of s, and with hyps exactly the hypotheses that
   the M-mode contract of riscv_stepTheory allows for the instruction:

     M-mode         s.c_privilege s.procID = 3w               always
     MPRV clear     ~(s.c_MCSR s.procID).mstatus.MPRV         data accesses
     unlocked       pmpcfg0/2 && 0x8080808080808080w = 0w     always
     OFF or NAPOT   ((pmpcfg0/2 >>> 1) ?? pmpcfg0/2) &&
                    0x0808080808080808w = 0w                  8-byte accesses
     aligned        aligned k (address), k = log2 width       accesses of 2,
                                                              4 and 8 bytes
     MIE clear      ~(s.c_MCSR s.procID).mstatus.MIE          always

   and the preconditions of NextRISCV (exception and NextFetch), the fetch
   (pc alignment and the instruction bytes), and the conditions under which
   the instruction is legal: misa.C for a compressed instruction, misa.C or
   a 4-byte aligned target for a jump or branch, misa.MXL <> 1w for the
   RV64-only instructions, mstatus.FS <> 0w for the F and D instructions
   and for the CSR instructions on fflags, frm and fcsr, and for those with
   the dynamic rounding mode fcsr.frm in RNE, RTZ, RDN, RUP or RMM
   (fcsr.frm <+ 5w).  The address in an alignment hypothesis, and the
   target in
   the jump condition, must be those of the decoded instruction: an
   alignment hypothesis must be equivalent to the alignment of rs1 + offs
   (of rs1 for an AMO, LR or SC), and a target hypothesis to bit 1 of
   pc + offs (of rs1 + offs with bit 0 cleared for JALR); both are decided
   by bit-blasting.  An address or target given by x0 and an offset is a
   constant, which riscv_step decides: no hypothesis is left for it.

   These categories (the table exact below and the patterns that follow
   it) are exhaustive: any other hypothesis is UNEXPECTED, and fails the
   test.  So there is none on satp: address translation is off in M-mode,
   and the contract needs no hypothesis on it.  Nor may any hypothesis
   mention c_SCSR, and a conclusion may mention it only for a CSR
   instruction on one of the S-mode CSRs stored there (stvec, scounteren,
   senvcfg, sscratch, sepc, scause, stval and satp), whose value it reads
   or writes.

   No model function may be left in the conclusion (bad_consts: address
   translation and the PMP check; for the CSR instructions, the read and
   write of the CSR, its legalisation and the access checks; for ECALL,
   EBREAK and MRET, the trap entry and the return).  For the edge cases,
   which include ECALL, EBREAK, MRET, WFI, SFENCE.VMA and CSR instructions
   on the CSRs whose values are legalised (satp and the sstatus view of
   mstatus among them), fields of the state after the step are checked
   against values written out here by hand (field checks).

   Encodings that cannot step must make riscv_step_hex fail: reserved
   encodings, which are illegal; SRET, which returns to S-mode or U-mode;
   a CSR instruction on an address that is not a CSR, or that writes a
   read-only CSR, which is illegal (decided here from a list of the CSRs of
   the model, independently of the step library); rm = 5 or 6 (reserved);
   and a misaligned constant address.  ECALL,
   EBREAK and MRET step: their theorems take the trap to M-mode
   (riscv_stepTheory.NextRISCV_trap) or return from it (NextRISCV_mret).
   ------------------------------------------------------------------------ *)

open HolKernel Parse boolLib bossLib testutils riscv_stepLib

(* the field checks prove goals, which needs a current theory *)
val _ = new_theory "scratch"

val () = Feedback.emit_MESG := false
val () = Feedback.emit_WARNING := false

(* ------------------------------------------------------------------------
   Decoding
   ------------------------------------------------------------------------ *)

fun hex_int h = Option.valOf (StringCvt.scanString (Int.scan StringCvt.HEX) h)

fun is_compressed h = String.size h <= 4

(* bits 14:12, the rm field of an F or D instruction *)
fun rm_of h = (hex_int h div 4096) mod 8

(* (outer constructor, instruction name, arguments) of the decoded
   instruction, e.g. ("Load", "LW", [rd, rs1, offs]) *)
fun decoded h =
  let
    val ast = utilsLib.rhsc (riscv_decode_hex h)
    val (c, args) = boolSyntax.strip_comb ast
    val outer = fst (Term.dest_const c)
  in
    case args of
       [a] =>
         let
           val (c', args') = boolSyntax.strip_comb a
         in
           if Term.is_const c' andalso not (pairSyntax.is_pair a) then
             (outer, fst (Term.dest_const c'),
              List.concat (List.map pairSyntax.strip_pair args'))
           else (outer, outer, pairSyntax.strip_pair a)
         end
     | _ => (outer, outer, args)
  end

fun name_of (_, inner, _) = inner

fun closed_value tm = utilsLib.rhsc (EVAL tm)
fun is_zero_reg r = Teq (closed_value ``^r = 0w : word5``)

(* ------------------------------------------------------------------------
   Allowed hypotheses
   ------------------------------------------------------------------------ *)

val s = ``s:riscv_state``
val mcsr = ``^s.c_MCSR ^s.procID``
val rvc = ``^mcsr.misa.C``
fun conjs th = boolSyntax.strip_conj (utilsLib.rhsc (Thm.SPEC mcsr th))
val (unlocked0, unlocked2) =
  case conjs riscv_stepTheory.pmp_unlocked_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_unlocked_def"
val (off_or_napot0, off_or_napot2) =
  case conjs riscv_stepTheory.pmp_off_or_napot_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_off_or_napot_def"

val exact =
  [("M-mode", ``^s.c_privilege ^s.procID = 3w``),
   ("MPRV clear", ``~^mcsr.mstatus.MPRV``),
   ("unlocked.pmpcfg0", unlocked0), ("unlocked.pmpcfg2", unlocked2),
   ("OFF or NAPOT.pmpcfg0", off_or_napot0),
   ("OFF or NAPOT.pmpcfg2", off_or_napot2),
   ("MIE clear", ``~^mcsr.mstatus.MIE``),
   ("exception", ``^s.exception = NoException``),
   ("NextFetch", ``^s.c_NextFetch ^s.procID = NONE``),
   ("pc<0>", ``~word_bit 0 (^s.c_PC ^s.procID)``),
   ("pc<1>|C", ``~word_bit 1 (^s.c_PC ^s.procID) \/ ^rvc``),
   ("C", rvc),
   ("RV64", ``^mcsr.misa.MXL <> 1w``),
   ("FS", ``^mcsr.mstatus.FS <> 0w``),
   ("frm<5", ``(^s.c_UCSR ^s.procID).fpcsr.FRM <+ 5w``)]

val mem_pat0 = ``^s.MEM8 (^s.c_PC ^s.procID) = v2w (l: bool list)``
val mem_pat = ``^s.MEM8 (^s.c_PC ^s.procID + k) = v2w (l: bool list)``
val aligned_pat = ``aligned n (a: word64)``
val target_pat = ``~word_bit 1 (a: word64) \/ ^rvc``

(* the data address of a load, store, AMO, LR or SC, if it is not given by
   x0, which makes it a constant *)
fun data_address (outer, inner, args) =
  let
    val gpr = fn r => ``^s.c_gpr ^s.procID ^r``
    val base_offs =
      case (outer, args) of
         ("Load", [_, rs1, offs]) => SOME (rs1, SOME offs)
       | ("FPLoad", [_, rs1, offs]) => SOME (rs1, SOME offs)
       | ("Store", [rs1, _, offs]) => SOME (rs1, SOME offs)
       | ("FPStore", [rs1, _, offs]) => SOME (rs1, SOME offs)
       | ("AMO", _ :: _ :: _ :: rs1 :: _) => SOME (rs1, NONE)
       | _ => NONE
  in
    case base_offs of
       NONE => NONE
     | SOME (rs1, offs) =>
         if is_zero_reg rs1 then NONE
         else
           SOME (case offs of
                    SOME offs =>
                      ``^(gpr rs1) + sw2sw (^offs : word12) : word64``
                  | NONE => gpr rs1)
  end

(* the target of a 32-bit jump or branch, if it is not a constant *)
fun jump_target (outer, inner, args) =
  case (inner, args) of
     ("JAL", [_, imm]) =>
       SOME ``^s.c_PC ^s.procID + sw2sw (^imm : word20) << 1``
   | ("JALR", [_, rs1, imm]) =>
       if is_zero_reg rs1 then NONE
       else
         SOME ``(^s.c_gpr ^s.procID ^rs1 + sw2sw (^imm : word12)) &&
                0xFFFFFFFFFFFFFFFEw : word64``
   | (_, [_, _, offs]) =>
       if outer = "Branch" then
         SOME ``^s.c_PC ^s.procID + sw2sw (^offs : word12) << 1``
       else NONE
   | _ => NONE

(* JALR from x0 to a target with bit 1 set: legal only with misa.C *)
fun constant_target_bit1 (_, inner, args) =
  case (inner, args) of
     ("JALR", [_, rs1, imm]) =>
       is_zero_reg rs1 andalso
       Teq (closed_value
              ``word_bit 1 (sw2sw (^imm : word12) &&
                            0xFFFFFFFFFFFFFFFEw : word64)``)
   | _ => false

(* a <=> b, by bit-blasting (atoms such as s.c_gpr s.procID r are kept) *)
local
  val conv =
    Conv.QCONV
      (REWRITE_CONV [alignmentTheory.aligned_extract]
       THENC numLib.REDUCE_CONV
       THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
in
  fun equivalent a b =
    Lib.can (fn tm => blastLib.BBLAST_PROVE (utilsLib.rhsc (conv tm)))
      (boolSyntax.mk_eq (a, b))
end

fun category inst h =
  case List.find (fn (_, t) => Term.aconv t h) exact of
     SOME (c, _) => c
   | NONE =>
       if Lib.can (Term.match_term mem_pat0) h orelse
          Lib.can (Term.match_term mem_pat) h
         then "mem"
       else case Lib.total (Term.match_term aligned_pat) h of
          SOME (sub, _) =>
            let
              val n = Term.subst sub ``n:num``
            in
              case data_address inst of
                 SOME a =>
                   if equivalent h ``aligned ^n ^a``
                     then "aligned." ^ Parse.term_to_string n
                   else "UNEXPECTED (not the address of the instruction): " ^
                        Parse.term_to_string h
               | NONE => "UNEXPECTED: " ^ Parse.term_to_string h
            end
        | NONE =>
            if Lib.can (Term.match_term target_pat) h then
              case jump_target inst of
                 SOME t =>
                   if equivalent h ``~word_bit 1 ^t \/ ^rvc``
                     then "target<1>|C"
                   else "UNEXPECTED (not the target of the instruction): " ^
                        Parse.term_to_string h
               | NONE => "UNEXPECTED: " ^ Parse.term_to_string h
            else "UNEXPECTED: " ^ Parse.term_to_string h

(* ------------------------------------------------------------------------
   What each instruction needs
   ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------
   CSR instructions

   Whether a CSR instruction is legal in M-mode, decided here independently
   of the step library, from a list of the 114 CSR addresses of the model:
   the CSR must exist, and a write (CSRRW and CSRRWI always, the others
   when their rs1 or uimm field is not 0) must not be to a read-only CSR
   (bits 11:10 of the number are 3).  fflags, frm and fcsr also need
   mstatus.FS <> Off, a hypothesis.
   ------------------------------------------------------------------------ *)

val csr_insts = ["CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"]

fun range a b = List.tabulate (b - a + 1, fn i => a + i)

val present_csrs =
  range 0x001 0x003 @ range 0xC00 0xC02 @ [0x100] @ range 0x104 0x106 @
  [0x10A] @ range 0x140 0x144 @ [0x180] @ range 0xF11 0xF15 @
  range 0x300 0x306 @ [0x30A, 0x320] @ range 0x323 0x33F @
  range 0x340 0x344 @ [0x3A0, 0x3A2] @ range 0x3B0 0x3BF @ [0xB00] @
  range 0xB02 0xB1F

(* the CSRs that the step theorems must cover *)
val required_csrs =
  [0x300, 0x301, 0x304, 0x305, 0x340, 0x341, 0x342, 0x343, 0x344, 0x306,
   0x320, 0x3A0, 0x3A2] @ range 0x3B0 0x3BF @
  [0x001, 0x002, 0x003, 0xC00, 0xC02, 0xB00, 0xB02, 0xF14, 0x106]

fun csr_of h = hex_int h div 1048576
fun csr_field h = (hex_int h div 32768) mod 32

fun csr_write (inner, h) =
  Lib.mem inner ["CSRRW", "CSRRWI"] orelse csr_field h <> 0

(* NONE when legal in M-mode, SOME why otherwise *)
fun csr_illegal inner h =
  let
    val c = csr_of h
  in
    if not (Lib.mem c present_csrs) then SOME "no such CSR"
    else if csr_write (inner, h) andalso c div 1024 = 3
      then SOME "write of a read-only CSR"
    else NONE
  end

fun width inner =
  if Lib.mem inner ["LB", "LBU", "SB"] then 1
  else if Lib.mem inner ["LH", "LHU", "SH"] then 2
  else if Lib.mem inner ["LW", "LWU", "SW", "FLW", "FSW", "LR_W", "SC_W"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_W" inner then 4
  else if Lib.mem inner ["LD", "SD", "FLD", "FSD", "LR_D", "SC_D"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_D" inner then 8
  else 0

val rv64_only =
  ["ADDIW", "SLLIW", "SRLIW", "SRAIW", "ADDW", "SUBW", "SLLW", "SRLW",
   "SRAW", "MULW", "DIVW", "REMW", "DIVUW", "REMUW", "LD", "LWU", "SD",
   "LR_D", "SC_D"]

(* the instructions with a rounding-mode field *)
val rounding =
  ["FADD_S", "FSUB_S", "FMUL_S", "FDIV_S", "FSQRT_S", "FMADD_S", "FMSUB_S",
   "FNMADD_S", "FNMSUB_S", "FCVT_S_W", "FCVT_S_WU", "FCVT_S_L", "FCVT_S_LU",
   "FCVT_W_S", "FCVT_WU_S", "FCVT_L_S", "FCVT_LU_S",
   "FADD_D", "FSUB_D", "FMUL_D", "FDIV_D", "FSQRT_D", "FMADD_D", "FMSUB_D",
   "FNMADD_D", "FNMSUB_D", "FCVT_D_W", "FCVT_D_WU", "FCVT_D_L", "FCVT_D_LU",
   "FCVT_W_D", "FCVT_WU_D", "FCVT_L_D", "FCVT_LU_D", "FCVT_S_D", "FCVT_D_S"]

(* required hypotheses, and those that may also occur *)
fun expected h (inst as (outer, inner, _)) =
  let
    val compressed = is_compressed h
    val w = width inner
    val fp = Lib.mem outer ["FPLoad", "FPStore", "FArith", "FConv"]
    val dyn = not compressed andalso Lib.mem inner rounding andalso
              rm_of h = 7
    val const_c = constant_target_bit1 inst
    val required =
      ["M-mode", "unlocked.pmpcfg0", "unlocked.pmpcfg2", "MIE clear",
       "exception", "NextFetch",
       "pc<0>", "mem", if compressed orelse const_c then "C" else "pc<1>|C"] @
      (if w > 0 then ["MPRV clear"] else []) @
      (if w = 8 then ["OFF or NAPOT.pmpcfg0", "OFF or NAPOT.pmpcfg2"]
       else []) @
      (case (data_address inst, w) of
          (SOME _, 2) => ["aligned.1"]
        | (SOME _, 4) => ["aligned.2"]
        | (SOME _, 8) => ["aligned.3"]
        | _ => []) @
      (if not compressed andalso Option.isSome (jump_target inst)
         then ["target<1>|C"] else []) @
      (if Lib.mem inner rv64_only then ["RV64"] else []) @
      (if fp orelse
          Lib.mem inner csr_insts andalso Lib.mem (csr_of h) [1, 2, 3]
         then ["FS"] else []) @
      (if dyn then ["frm<5"] else [])
    (* SLLI, SRLI and SRAI with shamt<5> set are RV64-only *)
    val optional =
      if Lib.mem inner ["SLLI", "SRLI", "SRAI"] then ["RV64"] else []
  in
    (required, optional)
  end

(* The instructions the step library cannot step, and why *)
fun no_step h (inst as (outer, inner, _)) =
  if outer = "UnknownInstruction" then SOME "reserved encoding"
  else if inner = "SRET"
    then SOME "SRET returns to S-mode or U-mode, which NextRISCV does not model"
  else if Lib.mem inner csr_insts then csr_illegal inner h
  else if not (is_compressed h) andalso Lib.mem inner rounding then
    case rm_of h of
       5 => SOME "reserved rounding mode"
     | 6 => SOME "reserved rounding mode"
     | _ => NONE
  else NONE

(* ------------------------------------------------------------------------
   Checking one theorem
   ------------------------------------------------------------------------ *)

val bad_consts =
  [``signalException``, ``signalAddressException``, ``raise'exception``,
   ``dataAddr``, ``fetchAddr``, ``pmpCheck``, ``round``, ``validRounding``,
   ``accrueFlags``, ``curPrivilege``, ``in32BitMode``, ``haveRVC``,
   (* address translation *)
   ``translateAddr``, ``effectivePrivilege``, ``ptwLevel``, ``ptwStep``,
   ``ptePermits``,
   (* traps and MRET *)
   ``takeTrap``, ``mret``, ``excDest``, ``excCode``, ``trapVector``,
   ``rawInstBits``, ``privilege``, ``privLevel``, ``setPrivilege``,
   ``read_xepc``,
   (* CSRs: the read, the write, the legalisers and the access checks *)
   ``CSR``, ``write'CSR``, ``CSRMap``, ``write'CSRMap``, ``writeCSR``,
   ``checkCSROp``, ``is_CSR_defined``, ``check_CSR_access``,
   ``check_CSR_conditions``, ``counterReadAllowed``, ``fpEnabled``,
   ``is_mhpm_CSR``, ``read_mip``, ``read_mstatus``, ``read_sstatus``,
   ``legalize_mstatus``, ``legalize_sstatus``, ``legalize_misa``,
   ``legalize_xtvec``, ``legalize_xepc``, ``legalize_mcause``,
   ``legalize_scause``, ``legalize_satp``, ``legalize_pmpcfg``,
   ``legalize_pmpcfg_byte``, ``write_pmpaddr``, ``pmpcfg_ent``, ``mtime``,
   ``mtimecmp``, ``msip``, ``MEM``, ``Delta``, ``write'Delta``]

(* s' is s with a sequence of field updates *)
fun is_update tm =
  Term.aconv tm s orelse
  (case boolSyntax.strip_comb tm of
      (f, [_, r]) =>
        Term.is_const f andalso
        String.isSuffix "_fupd" (fst (Term.dest_const f)) andalso
        is_update r
    | _ => false)

fun sort_uniq l = Lib.mk_set (Listsort.sort String.compare l)

(* c_SCSR, read or updated: the S-mode CSRs.  M-mode code does not depend
   on them, so no hypothesis mentions c_SCSR, and a conclusion only for a
   CSR instruction on one of the CSRs stored there (riscv.spec, record
   SupervisorCSR), whose value it reads or writes. *)
val scsr_consts =
  [Term.rator ``^s.c_SCSR``,
   fst (boolSyntax.strip_comb ``^s with c_SCSR := f``)]

fun mentions_scsr tm =
  List.exists (fn c => Lib.can (HolKernel.find_term (Term.same_const c)) tm)
    scsr_consts

val scsr_csrs = [0x105, 0x106, 0x10A, 0x140, 0x141, 0x142, 0x143, 0x180]

fun scsr_access h (_, inner, _) =
  Lib.mem inner csr_insts andalso Lib.mem (csr_of h) scsr_csrs

fun check h inst th =
  let
    val (required, optional) = expected h inst
    val cats = List.map (category inst) (Thm.hyp th)
    val ucats = sort_uniq cats
    val (l, r) = boolSyntax.dest_eq (Thm.concl th)
    val errors =
      List.filter (String.isPrefix "UNEXPECTED") ucats @
      List.mapPartial
        (fn c => if Lib.mem c ucats then NONE else SOME ("missing " ^ c))
        required @
      List.mapPartial
        (fn c => if Lib.mem c (required @ optional) orelse
                    String.isPrefix "UNEXPECTED" c
                   then NONE
                 else SOME ("not allowed: " ^ c)) ucats @
      (* one hypothesis per condition, besides the instruction bytes *)
      List.mapPartial
        (fn c => if c <> "mem" andalso
                    List.length (List.filter (equal c) cats) > 1
                   then SOME ("more than one hypothesis " ^ c) else NONE)
        ucats @
      (if List.exists Feq (Thm.hyp th) then ["vacuous"] else []) @
      (if List.exists mentions_scsr (Thm.hyp th)
         then ["hypothesis on c_SCSR"] else []) @
      (if mentions_scsr r andalso not (scsr_access h inst)
         then ["c_SCSR in the conclusion, not a CSR instruction on it"]
       else []) @
      (if Term.aconv l ``riscv_step$NextRISCV ^s`` andalso
          optionSyntax.is_some r andalso is_update (optionSyntax.dest_some r)
         then []
       else ["conclusion is not NextRISCV s = SOME (s with ...)"]) @
      List.mapPartial
        (fn c => if Lib.can (HolKernel.find_term (Term.same_const c)) r
                   then SOME ("left in conclusion: " ^
                              fst (Term.dest_const c))
                 else NONE) bad_consts
  in
    (ucats, errors)
  end

(* ------------------------------------------------------------------------
   Test cases
   ------------------------------------------------------------------------ *)

(* A deterministic choice of the free bits of a riscv_dict pattern *)
local
  val seed = ref 0w42 : Word32.word ref
  fun next () =
    ( seed := Word32.+ (Word32.* (!seed, 0w1664525), 0w1013904223)
    ; Word32.andb (Word32.>> (!seed, 0w16), 0w1) = 0w1 )
in
  fun random_bit () = next ()
end

fun bits_to_hex bs =
  let
    val n = List.foldl (fn (b, a) => 2 * a + (if b then 1 else 0)) 0 bs
    val digits = List.length bs div 4
  in
    StringCvt.padLeft #"0" digits
      (String.map Char.toLower (Int.fmt StringCvt.HEX n))
  end

(* the pattern's bits, MSB first, with rm (bits 14:12) set when given *)
fun instantiate rm pat =
  let
    val (l, _) = listSyntax.dest_list pat
    val n = List.length l
    val bits =
      List.map
        (fn t => if Teq t then true else if Feq t then false
                 else random_bit ()) l
    val bits =
      case rm of
         NONE => bits
       | SOME v =>
           List.tabulate
             (n, fn i =>
                   if i >= 17 andalso i <= 19
                     then (v div (if i = 17 then 4 else if i = 18 then 2
                                  else 1)) mod 2 = 1
                   else List.nth (bits, i))
  in
    bits_to_hex bits
  end

(* Encodings at the edges of the contract, with whether they must step,
   and for some the values of fields of the state after the step, written
   out by hand: each is an equation between a field of s' (the argument)
   and its value, in terms of s. *)
local
  val m = ``^s.c_MCSR ^s.procID``
  val st = ``(^s.c_MCSR ^s.procID).mstatus``
  fun gpr n = ``^s.c_gpr ^s.procID ^(wordsSyntax.mk_wordii (n, 5))``
  fun mcsr s' = ``^s'.c_MCSR ^s'.procID``
  fun scsr s' = ``^s'.c_SCSR ^s'.procID``
  fun same_regs s' = ``^s'.c_gpr = ^s.c_gpr``
  fun same_mcsr s' = ``^s'.c_MCSR = ^s.c_MCSR``
  fun same_scsr s' = ``^s'.c_SCSR = ^s.c_SCSR``
  (* bit i, and bits 12:11 (MPP), of mstatus as stored *)
  fun st_bit i = ``word_bit ^(numSyntax.term_of_int i) (reg'mstatus ^st)``
  val st_mpp = ``(12 >< 11) (reg'mstatus ^st) : word2``
  fun next_pc n s' =
    ``^s'.c_PC ^s'.procID =
      ^s.c_PC ^s.procID + ^(wordsSyntax.mk_wordii (n, 64))``
  (* the trap of an ECALL or EBREAK from M-mode, with cause ec and trap value
     tval *)
  fun trap ec tval =
    [fn s' => ``^s'.c_privilege ^s'.procID = 3w``,
     fn s' => ``^s'.c_PC ^s'.procID = ^m.mtvec && ~3w``,
     fn s' => ``(^(mcsr s')).mcause =
                <| EC := ^(wordsSyntax.mk_wordii (ec, 63)); Int := F |>``,
     fn s' => ``(^(mcsr s')).mepc = ^s.c_PC ^s.procID``,
     fn s' => ``(^(mcsr s')).mtval = ^tval``,
     fn s' => ``(^(mcsr s')).mstatus =
                ^st with <| MIE := F; MPIE := ^st.MIE; MPP := 3w |>``,
     fn s' => ``(^(mcsr s')).mtvec = ^m.mtvec``,
     same_regs]
in
  val edge_cases = [
  ("002000e7", "jalr ra,2(zero): constant target, bit 1 set", true, []),
  ("004000e7", "jalr ra,4(zero): constant target, 4-byte aligned", true, []),
  ("00802503", "lw a0,8(zero): constant aligned address", true, []),
  ("00803503", "ld a0,8(zero): constant aligned address", true, []),
  ("00602503", "lw a0,6(zero): constant misaligned address", false, []),
  ("00101503", "lh a0,1(zero): constant misaligned address", false, []),
  ("0000a02f", "amoadd.w zero,zero,(ra)", true, []),
  ("1000302f", "lr.d zero,(zero)", true, []),
  ("00c5c553", "fadd.s fa0,fa1,fa2,rmm", true, []),
  ("00c5d553", "fadd.s fa0,fa1,fa2 with rm = 5", false, []),
  ("d205c553", "fcvt.d.w fa0,a1,rmm", true, []),
  ("d205e553", "fcvt.d.w fa0,a1 with rm = 6", false, []),
  ("0000", "c.illegal", false, []),
  (* traps, MRET, SRET and WFI *)
  ("00000073", "ecall: trap to M-mode with cause 11", true,
   trap 11 ``0w: word64``),
  ("00100073", "ebreak: trap to M-mode with cause 3, mtval = pc", true,
   trap 3 ``^s.c_PC ^s.procID``),
  ("9002", "c.ebreak: as ebreak", true, trap 3 ``^s.c_PC ^s.procID``),
  ("30200073", "mret", true,
   [fn s' => ``^s'.c_privilege ^s'.procID =
                if ^st.MPP = 2w then 0w else ^st.MPP``,
    fn s' => ``^s'.c_PC ^s'.procID =
                if ^m.misa.C then ^m.mepc else ^m.mepc && ~3w``,
    fn s' => ``(^(mcsr s')).mstatus =
                ^st with <| MIE := ^st.MPIE; MPIE := T; MPP := 0w;
                            MPRV := (^st.MPRV /\ (^st.MPP = 3w)) |>``,
    fn s' => ``(^(mcsr s')).mepc = ^m.mepc``,
    same_regs]),
  ("10200073", "sret", false, []),
  ("10500073", "wfi: a no-op in M-mode", true,
   [next_pc 4, same_mcsr, same_regs,
    fn s' => ``^s'.c_privilege = ^s.c_privilege``]),
  ("12000073", "sfence.vma: a no-op, with no address-translation cache", true,
   [next_pc 4, same_mcsr, same_scsr, same_regs,
    fn s' => ``^s'.c_privilege = ^s.c_privilege``]),
  (* CSR instructions *)
  ("30529073", "csrw mtvec,t0: legalised mtvec", true,
   [fn s' => ``(^(mcsr s')).mtvec =
                if word_bit 1 ^(gpr 5) then
                  ((63 >< 2) ^(gpr 5) : 62 word) @@ ((1 >< 0) ^m.mtvec : word2)
                else ^(gpr 5)``,
    next_pc 4, same_regs]),
  ("300020f3", "csrrs ra,mstatus,zero: the mstatus read, SD from FS", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 1w =
                reg'mstatus ^st && 0x7E79AAw || 0xA00000000w ||
                (if ^st.FS = 3w then 0x8000000000000000w else 0w)``,
    same_mcsr, next_pc 4]),
  ("10002573", "csrr a0,sstatus: the mstatus read, through SSTATUS_MASK",
   true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w =
                (reg'mstatus ^st && 0x7E79AAw || 0xA00000000w ||
                 (if ^st.FS = 3w then 0x8000000000000000w else 0w)) &&
                0x80000003018DE762w``,
    same_mcsr, next_pc 4]),
  ("10029073", "csrw sstatus,t0: SIE SPIE SPP FS SUM MXR written", true,
   [fn s' => ``(^(mcsr s')).mstatus.SIE = word_bit 1 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SPIE = word_bit 5 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SPP = word_bit 8 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.FS = (14 >< 13) ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SUM = word_bit 18 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.MXR = word_bit 19 ^(gpr 5)``,
    (* the fields that sstatus does not show keep their stored bits *)
    fn s' => ``(^(mcsr s')).mstatus.MIE = ^(st_bit 3)``,
    fn s' => ``(^(mcsr s')).mstatus.MPIE = ^(st_bit 7)``,
    fn s' => ``(^(mcsr s')).mstatus.MPRV = ^(st_bit 17)``,
    fn s' => ``(^(mcsr s')).mstatus.TVM = ^(st_bit 20)``,
    fn s' => ``(^(mcsr s')).mstatus.TW = ^(st_bit 21)``,
    fn s' => ``(^(mcsr s')).mstatus.TSR = ^(st_bit 22)``,
    fn s' => ``(^(mcsr s')).mstatus.MPP =
                if ^st_mpp = 2w then 0w else ^st_mpp``,
    same_scsr, same_regs, next_pc 4]),
  ("18029073", "csrw satp,t0: written iff MODE is Bare, Sv39, Sv48 or Sv57",
   true,
   [fn s' => ``(^(scsr s')).satp =
                if (^(gpr 5) && 0xF000000000000000w = 0w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0x8000000000000000w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0x9000000000000000w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0xA000000000000000w)
                then ^(gpr 5) else (^s.c_SCSR ^s.procID).satp``,
    same_mcsr, same_regs, next_pc 4]),
  ("18005073", "csrwi satp,0: Bare", true,
   [fn s' => ``(^(scsr s')).satp = 0w``, same_mcsr, same_regs, next_pc 4]),
  ("18002573", "csrr a0,satp: the value stored", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w = (^s.c_SCSR ^s.procID).satp``,
    same_mcsr, same_scsr, next_pc 4]),
  ("3a0fd073", "csrwi pmpcfg0,0x1f: entry 0 NAPOT RWX", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 0x1Fw``, same_regs]),
  ("3a015073", "csrwi pmpcfg0,2: W without R, so W cleared", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 0w``]),
  ("3a075073", "csrwi pmpcfg0,14: W and X without R, so both cleared", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 8w``]),
  ("3b329073", "csrw pmpaddr3,t0: bits 63:54 read-only zero", true,
   [fn s' => ``(^(mcsr s')).pmpaddr3 = ^(gpr 5) && 0x3FFFFFFFFFFFFFw``]),
  ("34129073", "csrw mepc,t0: bit 0 cleared", true,
   [fn s' => ``(^(mcsr s')).mepc = ^(gpr 5) && ~1w``]),
  ("34102573", "csrr a0,mepc: bit 1 masked without C", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w =
                if ^m.misa.C then ^m.mepc else ^m.mepc && ~3w``,
    same_mcsr]),
  ("30429073", "csrw mie,t0: the six interrupts", true,
   [fn s' => ``reg'mie (^(mcsr s')).mie = ^(gpr 5) && 0xAAAw``]),
  ("3067d073", "csrwi mcounteren,15: CY, TM, IR", true,
   [fn s' => ``(^(mcsr s')).mcounteren = 7w``]),
  ("32005073", "csrwi mcountinhibit,0", true,
   [fn s' => ``(^(mcsr s')).mcountinhibit = 0w``]),
  ("340110f3", "csrrw ra,mscratch,sp: swap", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 1w = ^m.mscratch``,
    fn s' => ``(^(mcsr s')).mscratch = ^(gpr 2)``]),
  ("f1402673", "csrr a2,mhartid", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 12w = ^m.mhartid``, same_mcsr]),
  ("c0002573", "rdcycle a0", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w = ^s.c_cycles ^s.procID``,
    same_mcsr]),
  ("b0229073", "csrw minstret,t0: no increment for this instruction", true,
   [fn s' => ``^s'.c_instret ^s'.procID = ^(gpr 5)``,
    fn s' => ``^s'.c_minstret_written ^s'.procID``]),
  ("0010d073", "csrwi fflags,1: NX, and FS Dirty", true,
   [fn s' => ``reg'FPCSR (^s'.c_UCSR ^s'.procID).fpcsr =
                reg'FPCSR (^s.c_UCSR ^s.procID).fpcsr && 0xFFFFFFE0w || 1w``,
    fn s' => ``(^(mcsr s')).mstatus.FS = 3w``]),
  ("30029073", "csrw mstatus,t0: MIE, SUM, and MPP 2 written as 0", true,
   [fn s' => ``(^(mcsr s')).mstatus.MIE = word_bit 3 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SUM = word_bit 18 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.MPP =
                if (12 >< 11) ^(gpr 5) = 2w: word2 then 0w
                else (12 >< 11) ^(gpr 5)``]),
  ("c0001073", "unimp (csrrw zero,cycle,zero): write of a read-only CSR",
   false, []),
  ("7c002573", "csrrs a0,0x7c0,zero: no such CSR", false, []),
  ("3a1020f3", "csrrs ra,pmpcfg1,zero: odd pmpcfg, absent on RV64", false,
   []),
  ("c8002573", "csrrs a0,cycleh,zero: RV32 only", false, [])
  ]
end

(* ------------------------------------------------------------------------
   Running
   ------------------------------------------------------------------------ *)

fun fail msg = die ("FAILED: " ^ msg)

fun must_not_step name h why =
  if Lib.can riscv_step_hex h
    then fail (name ^ " " ^ h ^ ": stepped, but " ^ why)
  else ()

(* A field check holds if it simplifies to T, or is then proved by
   bit-blasting (the fields of s as atoms), after a case split on the
   conditions in it.  rec'mstatus is expanded for the checks of the fields
   of a written mstatus. *)
local
  val ss = srw_ss() ++ bitstringLib.v2w_n2w_ss
  val rwts =
    [riscvTheory.Skip_def, riscv_stepTheory.reg_rec_id,
     riscvTheory.rec'mstatus_def]
  fun blast tm = TAC_PROOF (([], tm), rw [] \\ blastLib.FULL_BBLAST_TAC)
in
  fun field_holds tm =
    let
      val r = utilsLib.rhsc (Conv.QCONV (SIMP_CONV ss rwts) tm)
    in
      Teq r orelse Lib.can blast r
    end
    handle HOL_ERR _ => false
end

(* Checks the theorem of an encoding that must step, and the fields of the
   state after it (checks); returns false when riscv_step finds that the
   instruction traps (on a misaligned constant address, or a CSR access
   that is illegal), and then has no step theorem *)
fun must_step_with checks name h inst =
  let
    val th = SOME (riscv_step_hex h)
             handle e as HOL_ERR herr =>
               if String.isPrefix "instruction traps"
                    (Feedback.message_of herr)
                 then NONE
               else raise e
  in
    case th of
       NONE => false
     | SOME th =>
         let
           val (_, errors) = check h inst th
           val s' =
             optionSyntax.dest_some (boolSyntax.rhs (Thm.concl th))
             handle HOL_ERR _ => s
           val field_errors =
             List.mapPartial
               (fn f =>
                  let
                    val tm = f s'
                  in
                    if field_holds tm then NONE
                    else SOME ("field check fails: " ^ Parse.term_to_string tm)
                  end) checks
         in
           List.app (fn e => fail (name ^ " " ^ h ^ " (" ^ name_of inst ^
                                   "): " ^ e)) (errors @ field_errors)
           ; true
         end
  end

val must_step = must_step_with []

(* One test: the encoding h steps with the hypotheses of its instruction, or
   does not step when it must not; false if it has no step theorem because
   it traps. *)
fun test name h =
  let
    val () = tprint (name ^ " " ^ h)
    val inst = decoded h
    val stepped =
      case no_step h inst of
         SOME why => (must_not_step name h why; true)
       | NONE => must_step name h inst
  in
    (if stepped then OK () else print "traps\n"); stepped
  end

(* every riscv_dict entry; an encoding with a misaligned constant address
   is retried with other bits *)
val () =
  List.app
    (fn (name, pat) =>
       let
         val base =
           if String.isSuffix "_NOP" name
             then String.substring (name, 0, String.size name - 4)
           else name
         val rms =
           if Lib.mem base rounding then [SOME 0, SOME 4, SOME 7]
           else [NONE]
         (* a 32-bit entry is named after the instruction it decodes to *)
         fun named h =
           String.isPrefix "RVC_" name orelse
           name_of (decoded h) = base orelse
           (fail (name ^ " " ^ h ^ " decodes to " ^ name_of (decoded h))
            ; false)
         fun go rm k =
           if k = 0 then fail (name ^ ": no encoding that steps found")
           else
             let
               val h = instantiate rm pat
             in
               if not (named h) orelse test name h then () else go rm (k - 1)
             end
         (* a CSR entry: each of the required CSRs, with the other free
            bits chosen as for the other entries *)
         fun with_csr c =
           let
             val h = instantiate NONE pat
             val n = hex_int h mod 1048576 + c * 1048576
           in
             StringCvt.padLeft #"0" 8
               (String.map Char.toLower (Int.fmt StringCvt.HEX n))
           end
         (* for the CSR entries, an instruction that must step and does
            not is a failure (test returns false for it) *)
         fun csr_test c =
           let
             val h = with_csr c
           in
             if not (named h) orelse test name h then ()
             else fail (name ^ " " ^ h ^ ": no step")
           end
       in
         if Lib.mem base csr_insts then List.app csr_test required_csrs
         else List.app (fn rm => go rm 8) rms
       end)
    riscv_dict

(* every CSR of the hart, read with CSRRS (csrr a0) and written with CSRRW
   from t0 and CSRRCI with uimm 3 (each also tests that a write of a
   read-only CSR does not step), and some addresses that are not CSRs *)
local
  fun enc c f3 rd f =
    StringCvt.padLeft #"0" 8
      (String.map Char.toLower
         (Int.fmt StringCvt.HEX
            (c * 1048576 + f * 32768 + f3 * 4096 + rd * 128 + 0x73)))
  val absent =
    [0x000, 0x004, 0x008, 0x015, 0xC03, 0xC1F, 0xC80, 0x101, 0x120, 0x14D,
     0x15D, 0x181, 0x200, 0x310, 0x312, 0x321, 0x322, 0x34A, 0x3A1, 0x3A3,
     0x3A4, 0x3C0, 0x747, 0x7A0, 0x7B0, 0x7C0, 0xB01, 0xB80, 0xF00, 0xF10,
     0xFFF]
in
  val () =
    List.app
      (fn c =>
         List.app
           (fn (txt, f3, rd, f) =>
              let
                val name = "CSR 0x" ^ Int.fmt StringCvt.HEX c ^ " " ^ txt
                val h = enc c f3 rd f
              in
                if test name h then () else fail (name ^ " " ^ h ^ ": no step")
              end)
           [("csrrs a0,csr,zero", 2, 10, 0), ("csrrw zero,csr,t0", 1, 0, 5),
            ("csrrci t1,csr,3", 7, 6, 3)])
      (present_csrs @ absent)
end

(* the rm values that make an instruction with a rounding mode illegal *)
val () =
  List.app
    (fn (name, pat) =>
       if Lib.mem name rounding then
         List.app (fn rm => ignore (test (name ^ " rm=" ^ Int.toString rm)
                                       (instantiate (SOME rm) pat)))
           [5, 6]
       else ())
    riscv_dict

(* the edge cases *)
val () =
  List.app
    (fn (h, txt, steps, checks) =>
       let
         val name = "edge: " ^ txt
         val () = tprint (name ^ " " ^ h)
         val inst = decoded h
       in
         if steps then
           (if must_step_with checks name h inst then OK ()
            else fail (name ^ " " ^ h ^ ": no step"))
         else (must_not_step name h "edge case"; OK ())
       end)
    edge_cases
