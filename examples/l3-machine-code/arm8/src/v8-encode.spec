-- ARMv8 instruction encoding, recovered from the existing generated HOL model.

-- See COPYRIGHT for the original model licence.

construct MachineCode { ARM8 :: word BadCode :: string }

nat CountTrailing (b::bool, w::bits(N))
HOL "CountTrailing.tac"
measure [w] =
  if w<0> == b or (if b then w == 0 else w == -1) then 0
  else 1 + CountTrailing (b, w >>+ 1)


(nat * nat * nat) EncodeBitMaskAux (imm::bits(N)) =
{
pref0 = CountTrailing ((true, imm));
if (pref0 == 0n0) then {
pref1 = CountTrailing ((false, imm));
run0 = CountTrailing ((true, (imm #>> pref1)));
run1 = CountTrailing ((false, (imm #>> (pref1 + run0))));
((run0 + run1), run1, (run1 - pref1))
} else {
run1 = CountTrailing ((false, (imm #>> pref0)));
run0 = CountTrailing ((true, (imm #>> (pref0 + run1))));
((run0 + run1), run1, ((run0 + run1) - pref0))
}
}


((bits(1) * bits(6) * bits(6)) option) EncodeBitMask (imm::bits(N)) =
{
(e, S, R) = EncodeBitMaskAux (imm);
((immN::bits(1)), (imms::bits(6)), (immr::bits(6))) = (if ((e::nat) == 0n64) then ((1`1), ([((S::nat) - 0n1)]::bits(6)), ([(R::nat)]::bits(6))) else ((0`1), ((~([(((e::nat) * 0n2) - 0n1)]::bits(6))) || ([((S::nat) - 0n1)]::bits(6))), ([(R::nat)]::bits(6))));
match DecodeBitMasks ((immN, imms, immr, true)) {
case Some ((imm2, _)) =>
      if (imm == imm2) then Some ((immN, imms, immr)) else (None::((bits(1) * (bits(6) * bits(6)))) option)
case (None::((bits(N) * bits(N))) option) =>
      (None::((bits(1) * (bits(6) * bits(6)))) option)
}
}


(bits(1)) e_sf (sf::bits(N)) =
([(Size ((0`N)) == 0n64)]::bits(1))


((bits(2)) option) EncodeLogicalOp (opc::LogicalOp, setflags::bool) =
match (opc, setflags) {
case (LogicalOp_AND, false) =>
      Some ((0`2))
case (LogicalOp_ORR, false) =>
      Some ((1`2))
case (LogicalOp_EOR, false) =>
      Some ((2`2))
case (LogicalOp_AND, true) =>
      Some ((3`2))
case (_::(LogicalOp * bool)) =>
      (None::(bits(2)) option)
}


(MachineCode) e_data (i::Data) =
match i {
case AddSubShiftedRegister@32 ((_, opc, s, sh, rm, imm6, rn, rd)) =>
      if (imm6)<0n5> then BadCode ("AddSubShiftedRegister32") else ARM8 (((0`1) : ([opc]::bits(1)) : ([s]::bits(1)) : (11`5) : ([sh]::bits(2)) : (0`1) : rm : imm6 : rn : rd))
case AddSubShiftedRegister@64 ((_, opc, s, sh, rm, imm6, rn, rd)) =>
      ARM8 (((1`1) : ([opc]::bits(1)) : ([s]::bits(1)) : (11`5) : ([sh]::bits(2)) : (0`1) : rm : imm6 : rn : rd))
case AddSubExtendRegister@32 ((sf, opc, s, rm, sty, imm3, rn, rd)) =>
      ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (89`8) : rm : ([sty]::bits(3)) : imm3 : rn : rd))
case AddSubExtendRegister@64 ((sf, opc, s, rm, sty, imm3, rn, rd)) =>
      ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (89`8) : rm : ([sty]::bits(3)) : imm3 : rn : rd))
case AddSubImmediate@32 ((sf, opc, s, imm, rn, rd)) =>
      (if ((imm && (~(4095`32))) == (0`32)) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (68`7) : (imm)<11:0> : rn : rd)) else (if ((imm && (~(16773120`32))) == (0`32)) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (69`7) : (imm)<23:12> : rn : rd)) else BadCode ("AddSubImmediate")))
case AddSubImmediate@64 ((sf, opc, s, imm, rn, rd)) =>
      (if ((imm && (~(4095`64))) == (0`64)) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (68`7) : (imm)<11:0> : rn : rd)) else (if ((imm && (~(16773120`64))) == (0`64)) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : ([s]::bits(1)) : (69`7) : (imm)<23:12> : rn : rd)) else BadCode ("AddSubImmediate")))
case AddSubCarry@32 ((_, opc, s, rm, rn, rd)) =>
      ARM8 (((0`1) : ([opc]::bits(1)) : ([s]::bits(1)) : (208`8) : rm : (0`6) : rn : rd))
case AddSubCarry@64 ((_, opc, s, rm, rn, rd)) =>
      ARM8 (((1`1) : ([opc]::bits(1)) : ([s]::bits(1)) : (208`8) : rm : (0`6) : rn : rd))
case LogicalShiftedRegister@32 ((sf, opc, invert, s, sh, imm, rm, rn, rd)) =>
      match EncodeLogicalOp ((opc, s)) {
case Some (opc) =>
      {
imm6 = ([imm]::bits(6));
if (imm == ([imm6]::nat)) then ARM8 ((e_sf (sf) : opc : (10`5) : ([sh]::bits(2)) : ([invert]::bits(1)) : rm : imm6 : rn : rd)) else BadCode ("LogicalShiftedRegister")
}
case (None::(bits(2)) option) =>
      BadCode ("LogicalShiftedRegister")
}
case LogicalShiftedRegister@64 ((sf, opc, invert, s, sh, imm, rm, rn, rd)) =>
      match EncodeLogicalOp ((opc, s)) {
case Some (opc) =>
      {
imm6 = ([imm]::bits(6));
if (imm == ([imm6]::nat)) then ARM8 ((e_sf (sf) : opc : (10`5) : ([sh]::bits(2)) : ([invert]::bits(1)) : rm : imm6 : rn : rd)) else BadCode ("LogicalShiftedRegister")
}
case (None::(bits(2)) option) =>
      BadCode ("LogicalShiftedRegister")
}
case LogicalImmediate@32 ((_, opc, s, imm, rn, rd)) =>
      match (EncodeBitMask (imm), EncodeLogicalOp ((opc, s))) {
case (Some ((_, imms, immr)), Some (opc)) =>
      ARM8 (((0`1) : opc : (72`7) : immr : imms : rn : rd))
case (_::(((bits(1) * (bits(6) * bits(6)))) option * (bits(2)) option)) =>
      BadCode ("LogicalImmediate32")
}
case LogicalImmediate@64 ((_, opc, s, imm, rn, rd)) =>
      match (EncodeBitMask (imm), EncodeLogicalOp ((opc, s))) {
case (Some ((N, imms, immr)), Some (opc)) =>
      ARM8 (((1`1) : opc : (36`6) : N : immr : imms : rn : rd))
case (_::(((bits(1) * (bits(6) * bits(6)))) option * (bits(2)) option)) =>
      BadCode ("LogicalImmediate64")
}
case Shift@32 ((_, sh, rm, rn, rd)) =>
      ARM8 (((214`11) : rm : (2`4) : ([sh]::bits(2)) : rn : rd))
case Shift@64 ((_, sh, rm, rn, rd)) =>
      ARM8 (((1238`11) : rm : (2`4) : ([sh]::bits(2)) : rn : rd))
case MoveWide@32 ((_, opc, hw, imm16, rd)) =>
      ARM8 (((0`1) : (match opc {
case MoveWideOp_N =>
      (0`2)
case MoveWideOp_Z =>
      (2`2)
case MoveWideOp_K =>
      (3`2)
}) : (37`6) : hw : imm16 : rd))
case MoveWide@64 ((_, opc, hw, imm16, rd)) =>
      ARM8 (((1`1) : (match opc {
case MoveWideOp_N =>
      (0`2)
case MoveWideOp_Z =>
      (2`2)
case MoveWideOp_K =>
      (3`2)
}) : (37`6) : hw : imm16 : rd))
case BitfieldMove@32 ((sf, inzero, extend, wmask, tmask, immr, imms, rn, rd)) =>
      {
sz = e_sf (sf);
match (match (inzero, extend) {
case (true, true) =>
      Some ((0`2))
case (false, false) =>
      Some ((1`2))
case (true, false) =>
      Some ((2`2))
case (_::(bool * bool)) =>
      (None::(bits(2)) option)
}) {
case Some (opc) =>
      {
r = ([immr]::bits(6));
s = ([imms]::bits(6));
if ((immr == ([r]::nat)) and ((imms == ([s]::nat)) and (DecodeBitMasks ((sz, s, r, false)) == Some ((wmask, tmask))))) then ARM8 ((sz : opc : (38`6) : sz : r : s : rn : rd)) else BadCode ("BitfieldMove")
}
case (None::(bits(2)) option) =>
      BadCode ("BitfieldMove")
}
}
case BitfieldMove@64 ((sf, inzero, extend, wmask, tmask, immr, imms, rn, rd)) =>
      {
sz = e_sf (sf);
match (match (inzero, extend) {
case (true, true) =>
      Some ((0`2))
case (false, false) =>
      Some ((1`2))
case (true, false) =>
      Some ((2`2))
case (_::(bool * bool)) =>
      (None::(bits(2)) option)
}) {
case Some (opc) =>
      {
r = ([immr]::bits(6));
s = ([imms]::bits(6));
if ((immr == ([r]::nat)) and ((imms == ([s]::nat)) and (DecodeBitMasks ((sz, s, r, false)) == Some ((wmask, tmask))))) then ARM8 ((sz : opc : (38`6) : sz : r : s : rn : rd)) else BadCode ("BitfieldMove")
}
case (None::(bits(2)) option) =>
      BadCode ("BitfieldMove")
}
}
case ConditionalCompareImmediate@32 ((sf, opc, imm, cd, (n, z, c, v), rn)) =>
      {
imm5 = ([imm]::bits(5));
if (imm == ([imm5]::bits(32))) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : (466`9) : imm5 : cd : (2`2) : rn : (0`1) : ([n]::bits(1)) : ([z]::bits(1)) : ([c]::bits(1)) : ([v]::bits(1)))) else BadCode ("ConditionalCompareImmediate")
}
case ConditionalCompareImmediate@64 ((sf, opc, imm, cd, (n, z, c, v), rn)) =>
      {
imm5 = ([imm]::bits(5));
if (imm == ([imm5]::bits(64))) then ARM8 ((e_sf (sf) : ([opc]::bits(1)) : (466`9) : imm5 : cd : (2`2) : rn : (0`1) : ([n]::bits(1)) : ([z]::bits(1)) : ([c]::bits(1)) : ([v]::bits(1)))) else BadCode ("ConditionalCompareImmediate")
}
case ConditionalCompareRegister@32 ((sf, opc, cd, (n, z, c, v), rm, rn)) =>
      ARM8 ((e_sf (sf) : ([opc]::bits(1)) : (466`9) : rm : cd : (0`2) : rn : (0`1) : ([n]::bits(1)) : ([z]::bits(1)) : ([c]::bits(1)) : ([v]::bits(1))))
case ConditionalCompareRegister@64 ((sf, opc, cd, (n, z, c, v), rm, rn)) =>
      ARM8 ((e_sf (sf) : ([opc]::bits(1)) : (466`9) : rm : cd : (0`2) : rn : (0`1) : ([n]::bits(1)) : ([z]::bits(1)) : ([c]::bits(1)) : ([v]::bits(1))))
case ConditionalSelect@32 ((_, op, o2, cd, rm, rn, rd)) =>
      ARM8 (((0`1) : ([op]::bits(1)) : (212`9) : rm : cd : (0`1) : ([o2]::bits(1)) : rn : rd))
case ConditionalSelect@64 ((_, op, o2, cd, rm, rn, rd)) =>
      ARM8 (((1`1) : ([op]::bits(1)) : (212`9) : rm : cd : (0`1) : ([o2]::bits(1)) : rn : rd))
case CountLeading@32 ((_, op, rn, rd)) =>
      ARM8 (((743426`21) : ([op]::bits(1)) : rn : rd))
case CountLeading@64 ((_, op, rn, rd)) =>
      ARM8 (((1792002`21) : ([op]::bits(1)) : rn : rd))
case ExtractRegister@32 ((_, imms, rm, rn, rd)) =>
      if (imms)<0n5> then BadCode ("ExtractRegister32") else ARM8 (((156`11) : rm : imms : rn : rd))
case ExtractRegister@64 ((_, imms, rm, rn, rd)) =>
      ARM8 (((1182`11) : rm : imms : rn : rd))
case Division@32 ((_, o1, rm, rn, rd)) =>
      ARM8 (((214`11) : rm : (1`5) : ([(not o1)]::bits(1)) : rn : rd))
case Division@64 ((_, o1, rm, rn, rd)) =>
      ARM8 (((1238`11) : rm : (1`5) : ([(not o1)]::bits(1)) : rn : rd))
case MultiplyAddSub@32 ((_, o0, rm, ra, rn, rd)) =>
      ARM8 (((216`11) : rm : ([o0]::bits(1)) : ra : rn : rd))
case MultiplyAddSub@64 ((_, o0, rm, ra, rn, rd)) =>
      ARM8 (((1240`11) : rm : ([o0]::bits(1)) : ra : rn : rd))
case MultiplyAddSubLong ((o0, u, rm, ra, rn, rd)) =>
      ARM8 (((155`8) : ([(not u)]::bits(1)) : (1`2) : rm : ([o0]::bits(1)) : ra : rn : rd))
case MultiplyHigh ((u, rm, rn, rd)) =>
      ARM8 (((155`8) : ([(not u)]::bits(1)) : (2`2) : rm : (31`6) : rn : rd))
case Reverse@32 ((_, opc, rn, rd)) =>
      if (opc == RevOp_REV64) then BadCode ("Reverse32") else ARM8 (((371712`20) : ([opc]::bits(2)) : rn : rd))
case Reverse@64 ((_, opc, rn, rd)) =>
      ARM8 (((896000`20) : ([opc]::bits(2)) : rn : rd))
}


(word) e_debug (i::Debug) =
match i {
case Breakpoint (imm16) =>
      ((1697`11) : imm16 : (0`5))
case DebugRestore =>
      (3602842592`32)
case DebugSwitch (LL) =>
      ((1701`11) : (0`16) : (0`3) : LL)
case Halt (imm16) =>
      ((1698`11) : imm16 : (0`5))
}


(word) e_crc (i::CRCExt) =
match i {
case CRC@8 ((_, c, rm, rn, rd)) =>
      ((214`11) : rm : (2`3) : ([c]::bits(1)) : (0`2) : rn : rd)
case CRC@16 ((_, c, rm, rn, rd)) =>
      ((214`11) : rm : (2`3) : ([c]::bits(1)) : (1`2) : rn : rd)
case CRC@32 ((_, c, rm, rn, rd)) =>
      ((214`11) : rm : (2`3) : ([c]::bits(1)) : (2`2) : rn : rd)
case CRC@64 ((_, c, rm, rn, rd)) =>
      ((1238`11) : rm : (2`3) : ([c]::bits(1)) : (3`2) : rn : rd)
}


(MachineCode) e_branch (i::Branch) =
match i {
case BranchConditional ((imm, cd)) =>
      {
imm19 = (imm)<20:2>;
if (imm == (SignExtend ((imm19 : (0`2)))::bits(64))) then ARM8 (((84`8) : imm19 : (0`1) : cd)) else BadCode ("BranchConditional")
}
case BranchImmediate ((imm, btype)) =>
      {
imm26 = (imm)<27:2>;
if ((imm == (SignExtend ((imm26 : (0`2)))::bits(64))) and (btype in set {BranchType_CALL, BranchType_JMP})) then ARM8 ((([(btype == BranchType_CALL)]::bits(1)) : (5`5) : imm26)) else BadCode ("BranchImmediate")
}
case BranchRegister ((rn, btype)) =>
      {
opc = (match btype {
case BranchType_JMP =>
      (0`2)
case BranchType_CALL =>
      (1`2)
case BranchType_RET =>
      (2`2)
case _ =>
      (3`2)
});
if (opc == (3`2)) then BadCode ("BranchRegister") else ARM8 (((428`9) : opc : (1984`11) : rn : (0`5)))
}
case CompareAndBranch@32 ((_, iszero, offset, rt)) =>
      {
imm19 = (offset)<20:2>;
if (offset == (SignExtend ((imm19 : (0`2)))::bits(64))) then ARM8 (((26`7) : ([(not iszero)]::bits(1)) : imm19 : rt)) else BadCode ("CompareAndBranch32")
}
case CompareAndBranch@64 ((_, iszero, offset, rt)) =>
      {
imm19 = (offset)<20:2>;
if (offset == (SignExtend ((imm19 : (0`2)))::bits(64))) then ARM8 (((90`7) : ([(not iszero)]::bits(1)) : imm19 : rt)) else BadCode ("CompareAndBranch64")
}
case TestBitAndBranch@32 ((_, bit_pos, bit_val, offset, rt)) =>
      {
imm14 = (offset)<15:2>;
if ((offset == (SignExtend ((imm14 : (0`2)))::bits(64))) and (not (bit_pos)<0n5>)) then ARM8 (((27`7) : ([bit_val]::bits(1)) : (bit_pos)<4:0> : imm14 : rt)) else BadCode ("TestBitAndBranch32")
}
case TestBitAndBranch@64 ((_, bit_pos, bit_val, offset, rt)) =>
      {
imm14 = (offset)<15:2>;
if ((offset == (SignExtend ((imm14 : (0`2)))::bits(64))) and (bit_pos)<0n5>) then ARM8 (((91`7) : ([bit_val]::bits(1)) : (bit_pos)<4:0> : imm14 : rt)) else BadCode ("TestBitAndBranch64")
}
}


(word) e_system (i::System) =
match i {
case MoveSystemRegister ((l, op0, op1, op2, crn, crm, rt)) =>
      ((852`10) : ([l]::bits(1)) : (1`1) : ([(op0 - (2`3))]::bits(1)) : op1 : crn : crm : op2 : rt)
case MoveImmediateProcState ((PSTATEField_SP, crm)) =>
      ((872452`20) : crm : (191`8))
case MoveImmediateProcState ((PSTATEField_DAIFSet, crm)) =>
      ((872500`20) : crm : (223`8))
case MoveImmediateProcState ((PSTATEField_DAIFClr, crm)) =>
      ((872500`20) : crm : (255`8))
case ExceptionReturn =>
      (3600745440`32)
case SupervisorCall (imm16) =>
      ((1696`11) : imm16 : (1`5))
case HypervisorCall (imm16) =>
      ((1696`11) : imm16 : (2`5))
case SecureMonitorCall (imm16) =>
      ((1696`11) : imm16 : (3`5))
case SystemInstruction ((op1, op2, crn, crm, l, rt)) =>
      ((852`10) : ([l]::bits(1)) : (1`2) : op1 : crn : crm : op2 : rt)
}


(MachineCode) e_LoadStoreImmediate (size::bits(2), regsize_word::bool, memop::MemOp, acctype::AccType, signed::bool, wback::bool, postindex::bool, unsigned_offset::bool, offset::bits(64), rn::bits(5), rt::bits(5)) =
{
(sz::bits(2)) = (if ((memop::MemOp) == (MemOp_PREFETCH::MemOp)) then (3`2) else (size::bits(2)));
imm9 = (offset)<8:0>;
imm12 = ((offset >>+ ([sz]::nat)))<11:0>;
(opc::bits(2)) = (if ((memop::MemOp) == (MemOp_STORE::MemOp)) then (0`2) else (if (((memop::MemOp) == (MemOp_LOAD::MemOp)) and (not (signed::bool))) then (1`2) else ((1`1) : ([(regsize_word::bool)]::bits(1)))));
(if (wback::bool) then (if (((offset::bits(64)) == (SignExtend ((imm9::bits(9)))::bits(64))) and ((acctype::AccType) == (AccType_NORMAL::AccType))) then ARM8 (((sz::bits(2)) : (56`6) : (opc::bits(2)) : (0`1) : (imm9::bits(9)) : ([(not (postindex::bool))]::bits(1)) : (1`1) : (rn::bits(5)) : (rt::bits(5)))) else BadCode ("LoadStoreImmediate")) else (if (postindex::bool) then BadCode ("LoadStoreImmediate") else (if ((unsigned_offset::bool) and (((offset::bits(64)) == (([(imm12::bits(12))]::bits(64)) << ([(sz::bits(2))]::nat))) and ((acctype::AccType) == (AccType_NORMAL::AccType)))) then ARM8 (((sz::bits(2)) : (57`6) : (opc::bits(2)) : (imm12::bits(12)) : (rn::bits(5)) : (rt::bits(5)))) else (if ((offset::bits(64)) == (SignExtend ((imm9::bits(9)))::bits(64))) then ARM8 (((sz::bits(2)) : (56`6) : (opc::bits(2)) : (0`1) : (imm9::bits(9)) : ([((acctype::AccType) == (AccType_UNPRIV::AccType))]::bits(1)) : (0`1) : (rn::bits(5)) : (rt::bits(5)))) else BadCode ("LoadStoreImmediate")))))
}


(MachineCode) e_LoadStoreRegister (size::bits(2), regsize_word::bool, memop::MemOp, signed::bool, rm::bits(5), extend_type::ExtendType, shift::nat, rn::bits(5), rt::bits(5)) =
ARM8 (((if (memop == MemOp_PREFETCH) then (3`2) else size) : (56`6) : (if (memop == MemOp_STORE) then (0`2) else (if ((memop == MemOp_LOAD) and (not signed)) then (1`2) else ((1`1) : ([regsize_word]::bits(1))))) : (1`1) : rm : ([extend_type]::bits(3)) : ([(not (shift == 0n0))]::bits(1)) : (2`2) : rn : rt))


(MachineCode) e_load_store (i::LoadStore) =
match i {
case LoadStoreImmediate@8 ((size, regsize_word, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)) =>
      e_LoadStoreImmediate ((([size]::bits(2)), regsize_word, memop, acctype, signed, wback, postindex, unsigned_offset, offset, rn, rt))
case LoadStoreImmediate@16 ((size, regsize_word, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)) =>
      e_LoadStoreImmediate ((([size]::bits(2)), regsize_word, memop, acctype, signed, wback, postindex, unsigned_offset, offset, rn, rt))
case LoadStoreImmediate@32 ((size, regsize_word, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)) =>
      e_LoadStoreImmediate ((([size]::bits(2)), regsize_word, memop, acctype, signed, wback, postindex, unsigned_offset, offset, rn, rt))
case LoadStoreImmediate@64 ((size, regsize_word, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)) =>
      e_LoadStoreImmediate ((([size]::bits(2)), regsize_word, memop, acctype, signed, wback, postindex, unsigned_offset, offset, rn, rt))
case LoadStoreRegister@8 ((size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)) =>
      e_LoadStoreRegister ((([size]::bits(2)), regsize_word, memop, signed, rm, extend_type, shift, rn, rt))
case LoadStoreRegister@16 ((size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)) =>
      e_LoadStoreRegister ((([size]::bits(2)), regsize_word, memop, signed, rm, extend_type, shift, rn, rt))
case LoadStoreRegister@32 ((size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)) =>
      e_LoadStoreRegister ((([size]::bits(2)), regsize_word, memop, signed, rm, extend_type, shift, rn, rt))
case LoadStoreRegister@64 ((size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)) =>
      e_LoadStoreRegister ((([size]::bits(2)), regsize_word, memop, signed, rm, extend_type, shift, rn, rt))
case LoadLiteral@32 ((_, memop, signed, offset, rt)) =>
      {
imm19 = (offset)<20:2>;
(opc::(bits(2)) option) = (match (memop, signed) {
case (MemOp_LOAD, false) =>
      Some ((0`2))
case (MemOp_LOAD, true) =>
      Some ((2`2))
case (MemOp_PREFETCH, false) =>
      Some ((3`2))
case (_::(MemOp * bool)) =>
      (None::(bits(2)) option)
});
if (IsSome ((opc::(bits(2)) option)) and (offset == (SignExtend ((imm19 : (0`2)))::bits(64)))) then ARM8 ((ValOf ((opc::(bits(2)) option)) : (24`6) : imm19 : rt)) else BadCode ("LoadLiteral32")
}
case LoadLiteral@64 ((_, MemOp_LOAD, false, offset, rt)) =>
      {
imm19 = (offset)<20:2>;
if (offset == (SignExtend ((imm19 : (0`2)))::bits(64))) then ARM8 (((88`8) : imm19 : rt)) else BadCode ("LoadLiteral64")
}
case LoadLiteral@64 ((_::(bits(64) * (MemOp * (bool * (bits(64) * bits(5))))))) =>
      BadCode ("LoadLiteral64")
case LoadStorePair@32 ((size, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, offset, rn, rt, rt2)) =>
      {
sf = ([size]::bits(1));
scale = (0n2 + ([sf]::nat));
imm7 = ((offset >>+ scale))<6:0>;
if (((sf == (1`1)) == (Size (size) == 0n64)) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and ((acctype in set {AccType_STREAM, AccType_NORMAL}) and (offset == ((SignExtend (imm7)::bits(64)) << scale))))) then ARM8 ((sf : ([signed]::bits(1)) : (20`5) : ([(not postindex)]::bits(1)) : ([wback]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : imm7 : rt2 : rn : rt)) else BadCode ("LoadStorePair")
}
case LoadStorePair@64 ((size, memop, acctype, signed, wb_unknown, rt_unknown, wback, postindex, offset, rn, rt, rt2)) =>
      {
sf = ([size]::bits(1));
scale = (0n2 + ([sf]::nat));
imm7 = ((offset >>+ scale))<6:0>;
if (((sf == (1`1)) == (Size (size) == 0n64)) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and ((acctype in set {AccType_STREAM, AccType_NORMAL}) and (offset == ((SignExtend (imm7)::bits(64)) << scale))))) then ARM8 ((sf : ([signed]::bits(1)) : (20`5) : ([(not postindex)]::bits(1)) : ([wback]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : imm7 : rt2 : rn : rt)) else BadCode ("LoadStorePair")
}
case LoadStoreAcquire@8 ((size, memop, acctype, excl, rn_unknown, rt_unknown, rs, rn, rt)) =>
      if ((match Size (size) {
case 0n8 =>
      (size == (0`8))
case 0n16 =>
      (size == (1`8))
case 0n32 =>
      (size == (2`8))
case _ =>
      (size == (3`8))
}) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (8`6) : ([(not excl)]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : (0`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : (31`5) : rn : rt)) else BadCode ("LoadStoreAcquire")
case LoadStoreAcquire@16 ((size, memop, acctype, excl, rn_unknown, rt_unknown, rs, rn, rt)) =>
      if ((match Size (size) {
case 0n8 =>
      (size == (0`16))
case 0n16 =>
      (size == (1`16))
case 0n32 =>
      (size == (2`16))
case _ =>
      (size == (3`16))
}) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (8`6) : ([(not excl)]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : (0`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : (31`5) : rn : rt)) else BadCode ("LoadStoreAcquire")
case LoadStoreAcquire@32 ((size, memop, acctype, excl, rn_unknown, rt_unknown, rs, rn, rt)) =>
      if ((match Size (size) {
case 0n8 =>
      (size == (0`32))
case 0n16 =>
      (size == (1`32))
case 0n32 =>
      (size == (2`32))
case _ =>
      (size == (3`32))
}) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (8`6) : ([(not excl)]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : (0`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : (31`5) : rn : rt)) else BadCode ("LoadStoreAcquire")
case LoadStoreAcquire@64 ((size, memop, acctype, excl, rn_unknown, rt_unknown, rs, rn, rt)) =>
      if ((match Size (size) {
case 0n8 =>
      (size == (0`64))
case 0n16 =>
      (size == (1`64))
case 0n32 =>
      (size == (2`64))
case _ =>
      (size == (3`64))
}) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (8`6) : ([(not excl)]::bits(1)) : ([(memop == MemOp_LOAD)]::bits(1)) : (0`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : (31`5) : rn : rt)) else BadCode ("LoadStoreAcquire")
case LoadStoreAcquirePair@64 ((size, memop, acctype, rn_unknown, rt_unknown, rs, rn, rt, rt2)) =>
      if ((size == (if (Size (size) == 0n64) then (2`64) else (3`64))) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (16`7) : ([(memop == MemOp_LOAD)]::bits(1)) : (1`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : rt2 : rn : rt)) else BadCode ("LoadStoreAcquirePair")
case LoadStoreAcquirePair@128 ((size, memop, acctype, rn_unknown, rt_unknown, rs, rn, rt, rt2)) =>
      if ((size == (if (Size (size) == 0n64) then (2`128) else (3`128))) and ((memop in set {MemOp_LOAD, MemOp_STORE}) and (acctype in set {AccType_ORDERED, AccType_ATOMIC}))) then ARM8 ((([size]::bits(2)) : (16`7) : ([(memop == MemOp_LOAD)]::bits(1)) : (1`1) : rs : ([(acctype == AccType_ORDERED)]::bits(1)) : rt2 : rn : rt)) else BadCode ("LoadStoreAcquirePair")
}


word e_fp (i::FloatingPoint) =
match i
{
   case FMov (n, d) =>
      0b0001111001100000010000`22 : n : d
   case FAbs (n, d) =>
      0b0001111001100000110000`22 : n : d
   case FNeg (n, d) =>
      0b0001111001100001010000`22 : n : d
   case FSqrt (n, d) =>
      0b0001111001100001110000`22 : n : d
   case FToInt32 (n, d) =>
      0b0001111001100000000000`22 : n : d
   case FFromInt32 (n, d) =>
      0b0001111001100010000000`22 : n : d
   case FAdd (m, n, d) =>
      0b00011110011`11 : m : 0b001010`6 : n : d
   case FSub (m, n, d) =>
      0b00011110011`11 : m : 0b001110`6 : n : d
   case FMul (m, n, d) =>
      0b00011110011`11 : m : 0b000010`6 : n : d
   case FDiv (m, n, d) =>
      0b00011110011`11 : m : 0b000110`6 : n : d
   case FMovToGeneral@32 (_, n, d) =>
      0b0001111000100110000000`22 : n : d
   case FMovToGeneral@64 (_, n, d) =>
      0b1001111001100110000000`22 : n : d
   case FMovFromGeneral@32 (_, n, d) =>
      0b0001111000100111000000`22 : n : d
   case FMovFromGeneral@64 (_, n, d) =>
      0b1001111001100111000000`22 : n : d
   case FCompare (n, m) =>
      0b00011110011`11 : m : 0b001000`6 : n : 0`5
   case FMAdd (m, a, n, d) =>
      0b00011111010`11 : m : 0`1 : a : n : d
}

(MachineCode) Encode (i::instruction) =
match i {
case Address ((page, imm, rd)) =>
      if page then {
immlo = (imm)<13:12>;
immhi = (imm)<32:14>;
if ((SignExtend ((immhi : immlo : (0`12)))::bits(64)) == imm) then ARM8 (((1`1) : immlo : (16`5) : immhi : rd)) else BadCode ("Address")
} else {
immlo = (imm)<1:0>;
immhi = (imm)<20:2>;
if ((SignExtend ((immhi : immlo))::bits(64)) == imm) then ARM8 (((0`1) : immlo : (16`5) : immhi : rd)) else BadCode ("Address")
}
case FloatingPoint (x) =>
      ARM8 (e_fp (x))
case Data (x) =>
      e_data (x)
case Branch (x) =>
      e_branch (x)
case LoadStore (x) =>
      e_load_store (x)
case CRCExt (x) =>
      ARM8 (e_crc (x))
case Debug (x) =>
      ARM8 (e_debug (x))
case System (x) =>
      ARM8 (e_system (x))
case MemoryBarrier ((opc, crm)) =>
      ARM8 (((872499`20) : crm : (1`1) : ([opc]::bits(2)) : (31`5)))
case ClearExclusive (crm) =>
      ARM8 (((872499`20) : crm : (95`8)))
case Hint (opc) =>
      ARM8 (((13959968`24) : ([opc]::bits(3)) : (31`5)))
case Unallocated =>
      BadCode ("Unallocated")
case Reserved =>
      BadCode ("Reserved")
}
