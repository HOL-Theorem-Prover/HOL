(* ------------------------------------------------------------------------
   Definitions and theorems used by RISC-V step evaluator (riscv_stepLib)
   ------------------------------------------------------------------------ *)
Theory riscv_step
Ancestors
  alignment riscv
Libs
  utilsLib wordsLib blastLib


val _ = ParseExtras.temp_loose_equality()

val ERR = mk_HOL_ERR "riscv_stepTheory";

val () =
  ( List.app (fn f => f ())
      [numLib.temp_prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]
  ; HOLFlags.set_bflag (Parse.show_assums, true)
  ; General.ignore (Parse.hide "imm")
  )

fun uprove a b = utilsLib.STRIP_UNDISCH (Q.prove (a, b))

(* ------------------------------------------------------------------------
   Simplified Fetch and Next functions
   ------------------------------------------------------------------------ *)

(* Fetch() of riscv.spec without its logging (setupDelta).  Where the spec
   returns F_Error (a misaligned pc, or a parcel that the PMP does not let
   the current privilege execute), which makes Next take a trap, this one
   raises UNDEFINED, which makes NextRISCV return NONE.  As in the spec, an
   instruction is fetched in 2-byte parcels: the PMP must allow the parcel
   at the pc and, for a 32-bit instruction, the one at pc + 2, whose bytes
   are read from the address that fetchAddr gives for it.  NextRISCV only
   refines Next if it fetches exactly what Next would, so this must mirror
   the spec (doc/design-privileged.md §1.1 F1, §5.6.3). *)

Definition Fetch_def:
  Fetch s =
  let pc = PC s in
  if word_bit 0 pc \/ word_bit 1 pc /\ ~haveRVC () s then
    raise'exception (UNDEFINED "fetch misaligned") s
  else
    case fetchAddr pc s of
       NONE => raise'exception (UNDEFINED "fetch fault") s
     | SOME ppc =>
         let (w, s) = rawReadInst ppc s in
         case w of
            Half h => (Half h, s)
          | Word i =>
              case fetchAddr (pc + 2w) s of
                 NONE => raise'exception (UNDEFINED "fetch fault") s
               | SOME ppc2 =>
                   (Word (s.MEM8 (ppc2 + 1w) @@ s.MEM8 ppc2 @@ (15 >< 0) i), s)
End

Definition update_pc_def:   update_pc v s = SOME (write'PC v s)
End

Definition DecodeAny_def:
  DecodeAny rvc f =
  case f of
     Half h => if rvc then DecodeRVC h else UnknownInstruction
   | Word w => Decode w
End

(* The fetched instruction bits, zero-extended: the trap value (mtval) of
   an illegal instruction, which the spec's Next takes from fetchAndExecute
   (P §3.1.16 p.52-53, [D43]). *)
Definition rawInstBits_def:
  (rawInstBits (Half h) = w2w h : word64) /\
  (rawInstBits (Word w) = w2w w : word64)
End

(* One step of the spec's Next: the instruction at the pc runs, and then,
   as in Next, the pc moves on, branches, returns from a trap (MRET) or
   takes the trap that the instruction raised (an ECALL, an EBREAK or an
   illegal instruction; excDest, takeTrap, and the instruction bits as the
   trap value of an illegal instruction).  NONE when Next would trap in the
   fetch (Fetch above raises UNDEFINED instead), when the instruction raises
   an UNDEFINED, and for SRET, which returns to S-mode or U-mode through
   sepc: S-mode is outside the validated scope (doc/design-privileged.md
   Scope).  NextRISCV does not model what Next does besides running the
   instruction: it takes no interrupts (see H6 below), leaves out the
   setupDelta and clear_logs of Next (although an instruction may still
   write c_update, as writeCSR, writeFPRS and writeFPRD do), and does not
   count (c_cycles, c_instret, c_minstret_written). *)
Definition NextRISCV_def:
  NextRISCV s =
  let rvc = haveRVC () s in
  let (f, s) = Fetch s in
  let s = Run (DecodeAny rvc f) s in
  if s.exception <> NoException then
    NONE
  else
    let pc = PC s in
    case NextFetch s of
       NONE => update_pc (pc + Skip s) s
     | SOME (BranchTo a) => update_pc a (write'NextFetch NONE s)
     | SOME Mret => SOME (mret () (write'NextFetch NONE s))
     | SOME (Trap t) =>
         let ec = excCode t.trap in
         let tval = if t.trap = Illegal_Instr then rawInstBits f else t.tval
         in
           SOME (takeTrap (F, ec, pc, tval, excDest (ec, curPrivilege () s) s)
                   (write'NextFetch NONE s))
     | SOME Sret => NONE
End

(* ------------------------------------------------------------------------
   The hypotheses of the M-mode step theorems (design-privileged.md §1.5)

   H1  s.c_privilege s.procID = 3w            the hart is in M-mode
   H2  ~(s.c_MCSR s.procID).mstatus.MPRV      loads and stores use M-mode
   H3  pmp_unlocked (s.c_MCSR s.procID)       no PMP entry is locked
   H4  pmp_off_or_napot (s.c_MCSR s.procID)   every PMP entry is OFF or NAPOT
   H5  the data address is naturally aligned
   H6  ~(s.c_MCSR s.procID).mstatus.MIE       no interrupt can be taken

   The step theorems carry H3 and H4 as their word-level conjuncts, so that
   a lifter can turn each one into an assertion on a word; the definitions
   below are for consumers (prog, CakeML, HolBA) that state the contract
   once.
   ------------------------------------------------------------------------ *)

(* H3: bit 7 (L) of every entry configuration byte is clear. *)
Definition pmp_unlocked_def:
  pmp_unlocked (mcsr: MachineCSR) <=>
    (mcsr.pmpcfg0 && 0x8080808080808080w = 0w) /\
    (mcsr.pmpcfg2 && 0x8080808080808080w = 0w)
End

(* H4: bits 4 and 3 (A) of every entry configuration byte are equal, so A
   is 0 (OFF) or 3 (NAPOT). *)
Definition pmp_off_or_napot_def:
  pmp_off_or_napot (mcsr: MachineCSR) <=>
    ((mcsr.pmpcfg0 >>> 1 ?? mcsr.pmpcfg0) && 0x0808080808080808w = 0w) /\
    ((mcsr.pmpcfg2 >>> 1 ?? mcsr.pmpcfg2) && 0x0808080808080808w = 0w)
End

(* H3 and H4 say the same of the configuration byte of each entry, which
   pmpcfg_ent selects from pmpcfg0 or pmpcfg2. *)
Theorem pmpcfg_ent_unlocked:
  pmp_unlocked (s.c_MCSR s.procID) ==> ~(pmpcfg_ent i s).L
Proof
  rw [pmp_unlocked_def, pmpcfg_ent_def, rec'pmpcfg_def, MCSR_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 0) i : word3`
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem pmpcfg_ent_off_or_napot:
  pmp_off_or_napot (s.c_MCSR s.procID) ==>
  ((pmpcfg_ent i s).A = 0w) \/ ((pmpcfg_ent i s).A = 3w)
Proof
  rw [pmp_off_or_napot_def, pmpcfg_ent_def, rec'pmpcfg_def, MCSR_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 0) i : word3`
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC
QED

(* The legalised value of a write of pmpcfg0 or pmpcfg2 (P §3.7.1 p.71-72,
   doc/design-privileged.md §5.2.3), for the step theorems of the CSR
   instructions: each byte keeps its L, A, X, W and R bits (bits 6 and 5 are
   read-only zero), except that W and X are cleared when W is set without R
   (R = 0 and W = 1 is reserved).  A locked entry would keep its old byte;
   with H3 none is locked, so the value does not depend on the old one. *)

val legalize_pmpcfg_byte_unlocked = Q.prove(
  `~c.L ==>
   (reg'pmpcfg (legalize_pmpcfg_byte (b, c)) =
    b && 0x9Fw && ~((b >>> 1 && ~b && 1w) << 1) &&
    ~((b >>> 1 && ~b && 1w) << 2))`,
  rw [legalize_pmpcfg_byte_def]
  \\ fs ([rec'pmpcfg_def, reg'pmpcfg_def] @
         TypeBase.updates_of ``:pmpcfg`` @ TypeBase.accessors_of ``:pmpcfg``)
  \\ blastLib.FULL_BBLAST_TAC)

val pmpcfg_bytes_unlocked = Q.prove(
  `((x: word64) && 0x8080808080808080w = 0w) ==>
   ~(rec'pmpcfg ((63 >< 56) x)).L /\ ~(rec'pmpcfg ((55 >< 48) x)).L /\
   ~(rec'pmpcfg ((47 >< 40) x)).L /\ ~(rec'pmpcfg ((39 >< 32) x)).L /\
   ~(rec'pmpcfg ((31 >< 24) x)).L /\ ~(rec'pmpcfg ((23 >< 16) x)).L /\
   ~(rec'pmpcfg ((15 >< 8) x)).L /\ ~(rec'pmpcfg ((7 >< 0) x)).L`,
  simp_tac (srw_ss()) (rec'pmpcfg_def :: TypeBase.accessors_of ``:pmpcfg``)
  \\ blastLib.BBLAST_TAC)

(* For one byte b, c = b >>> 1 && ~b && 1w is 1 when W is set and R is
   clear, and c << 1 and c << 2 are then the W and X bits; for all eight
   bytes at once, c has bit 8k set when byte k has W set and R clear. *)
Theorem legalize_pmpcfg_unlocked:
  (old && 0x8080808080808080w = 0w) ==>
  (legalize_pmpcfg (v, old) =
   v && 0x9F9F9F9F9F9F9F9Fw &&
   ~((v >>> 1 && ~v && 0x0101010101010101w) << 1) &&
   ~((v >>> 1 && ~v && 0x0101010101010101w) << 2))
Proof
  strip_tac
  \\ imp_res_tac pmpcfg_bytes_unlocked
  \\ asm_simp_tac std_ss [legalize_pmpcfg_def, legalize_pmpcfg_byte_unlocked]
  \\ rpt (pop_assum kall_tac)
  \\ blastLib.BBLAST_TAC
QED

(* With grain 0 every region bound is a multiple of 4, and a NAPOT region
   (at least 8 bytes, naturally aligned) has bounds that are multiples of
   8: m = y ?? (y + 1w) has bit 0 set for every y, whatever pmpaddr
   holds. *)

val napot_m = blastLib.BBLAST_PROVE ``word_bit 0 ((y: word64) ?? (y + 1w))``

val napot_lo = Q.prove(
  `word_bit 0 (m: word64) ==> aligned 3 ((y && ~m) << 2)`,
  rw [aligned_extract] \\ blastLib.FULL_BBLAST_TAC)

val napot_size = Q.prove(
  `word_bit 0 (m: word64) ==> aligned 3 ((m + 1w) << 2)`,
  rw [aligned_extract] \\ blastLib.FULL_BBLAST_TAC)

val aligned_3_2 = Q.prove(
  `aligned 3 (x: word64) ==> aligned 2 x`,
  rw [aligned_extract] \\ blastLib.FULL_BBLAST_TAC)

val na4_bounds = Q.prove(
  `aligned 2 ((y: word64) << 2) /\ aligned 2 ((y << 2) + 4w)`,
  rw [aligned_extract] \\ blastLib.BBLAST_TAC)

val napot_bounds3 = Q.prove(
  `aligned 3 (((y: word64) && ~(y ?? y + 1w)) << 2) /\
   aligned 3 ((y && ~(y ?? y + 1w)) << 2 + ((y ?? y + 1w) + 1w) << 2)`,
  metis_tac [napot_m, napot_lo, napot_size, aligned_add_sub_cor])

val napot_bounds2 = Q.prove(
  `aligned 2 (((y: word64) && ~(y ?? y + 1w)) << 2) /\
   aligned 2 ((y && ~(y ?? y + 1w)) << 2 + ((y ?? y + 1w) + 1w) << 2)`,
  metis_tac [napot_bounds3, aligned_3_2])

Theorem pmpRegion_aligned:
  (pmpRegion i s = SOME (lo, hi)) ==>
  aligned 2 lo /\ aligned 2 hi /\
  (((pmpcfg_ent i s).A = 3w) ==> aligned 3 lo /\ aligned 3 hi)
Proof
  simp_tac (std_ss ++ wordsLib.SIZES_ss)
    [pmpRegion_def, LET_THM, wordsTheory.n2w_11]
  \\ wordsLib.Cases_on_word_value `(pmpcfg_ent i s).A`
  \\ simp_tac (std_ss ++ wordsLib.SIZES_ss) [wordsTheory.n2w_11]
  \\ rpt strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ simp_tac std_ss
       [na4_bounds, napot_bounds3, napot_bounds2, aligned_0, aligned_lsl,
        COND_RAND]
QED

(* An entry that is OFF matches nothing; with H4 the only other mode is
   NAPOT, whose bounds pmpRegion_aligned makes multiples of 8. *)
Theorem pmpRegion_OFF:
  ((pmpcfg_ent i s).A = 0w) ==> (pmpRegion i s = NONE)
Proof
  simp_tac (std_ss ++ wordsLib.SIZES_ss)
    [pmpRegion_def, LET_THM, wordsTheory.n2w_11]
QED

(* An entry can match only some of the bytes of an access, and so fail it
   even in M-mode (P §3.7.1.3 p.73), only when a region bound falls inside
   the access.  For a naturally aligned access of at most 4 bytes, and for
   an aligned 8-byte one when the bounds are multiples of 8, none does. *)
Theorem pmp_no_partial:
  aligned 2 (lo: word64) /\ aligned 2 (hi: word64) /\
  ((n = 1) \/ (n = 2) /\ aligned 1 a \/ (n = 4) /\ aligned 2 a \/
   (n = 8) /\ aligned 3 a /\ aligned 3 lo /\ aligned 3 hi) ==>
  (a + n2w (n - 1) <+ lo \/ hi <=+ a \/ lo <=+ a /\ a + n2w (n - 1) <+ hi)
Proof
  rw [aligned_extract] \\ blastLib.FULL_BBLAST_TAC
QED

(* So in M-mode, with the entry unlocked, the entry either does not match
   or allows the access. *)
Theorem pmpEntryCheck_Machine:
  ~(pmpcfg_ent i s).L /\
  ((n = 1) \/ (n = 2) /\ aligned 1 a \/ (n = 4) /\ aligned 2 a \/
   (n = 8) /\ aligned 3 a /\
   (((pmpcfg_ent i s).A = 0w) \/ ((pmpcfg_ent i s).A = 3w))) ==>
  (pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s = NONE) \/
  (pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s = SOME T)
Proof
  strip_tac
  \\ simp_tac std_ss [pmpEntryCheck_def, LET_THM]
  \\ Cases_on `pmpRegion i s`
  \\ simp_tac std_ss []
  \\ PairCases_on `x`
  \\ simp_tac std_ss []
  \\ `aligned 2 x0 /\ aligned 2 x1 /\
      (((pmpcfg_ent i s).A = 3w) ==> aligned 3 x0 /\ aligned 3 x1)`
     by (match_mp_tac pmpRegion_aligned \\ asm_rewrite_tac [])
  \\ `a + n2w (n - 1) <+ x0 \/ x1 <=+ a \/ x0 <=+ a /\ a + n2w (n - 1) <+ x1`
     by (match_mp_tac pmp_no_partial
         \\ asm_rewrite_tac []
         \\ metis_tac [pmpRegion_OFF, optionTheory.NOT_NONE_SOME])
  \\ asm_simp_tac std_ss []
  \\ rw_tac std_ss []
  \\ fs []
QED

(* pmpCheck is unrolled over the 16 entries, with the verdicts of the
   entries let-bound and chained through IS_SOME and THE; it is T when
   every entry that matches allows the access, since in M-mode an access
   that no entry matches is allowed. *)
val IS_SOME_THE_cond = Q.prove(
  `(IS_SOME x ==> THE x) ==>
   ((if IS_SOME x then THE x else b) = (IS_SOME x \/ b))`,
  Cases_on `x` \\ rw [])

Theorem pmpCheck_chain:
  (!i. IS_SOME (pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s) ==>
       THE (pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s)) ==>
  pmpCheck (a, n, kind, Machine) s
Proof
  strip_tac \\ asm_simp_tac std_ss [pmpCheck_def, LET_THM, IS_SOME_THE_cond]
QED

(* The lemma of design-privileged.md §1.5: in M-mode, with no PMP entry
   locked (H3), every naturally aligned access of at most 4 bytes and every
   2-byte fetch parcel is allowed, and with every entry OFF or NAPOT (H4)
   so is every aligned 8-byte access. *)
Theorem pmpCheck_Machine:
  pmp_unlocked (s.c_MCSR s.procID) /\
  ((n = 1) \/ (n = 2) /\ aligned 1 a \/ (n = 4) /\ aligned 2 a \/
   (n = 8) /\ aligned 3 a /\ pmp_off_or_napot (s.c_MCSR s.procID)) ==>
  pmpCheck (a, n, kind, Machine) s
Proof
  DISCH_TAC
  \\ match_mp_tac pmpCheck_chain
  \\ gen_tac
  \\ `(pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s = NONE) \/
      (pmpEntryCheck (i, a, a + n2w (n - 1), kind, Machine) s = SOME T)`
     by (match_mp_tac pmpEntryCheck_Machine
         \\ metis_tac [pmpcfg_ent_unlocked, pmpcfg_ent_off_or_napot])
  \\ asm_simp_tac std_ss []
QED

(* Fetches use the current privilege (H1); translateAddr is the identity. *)
Theorem fetchAddr_Machine:
  (s.c_privilege s.procID = 3w) /\ pmp_unlocked (s.c_MCSR s.procID) /\
  aligned 1 a ==>
  (fetchAddr a s = SOME a)
Proof
  rw [fetchAddr_def, translateAddr_def, curPrivilege_def, privilege_def]
  \\ match_mp_tac pmpCheck_Machine
  \\ simp []
QED

(* Loads and stores use the effective privilege, which is the current one
   unless mstatus.MPRV is set (H2). *)
Theorem dataAddr_Machine:
  (s.c_privilege s.procID = 3w) /\ ~(s.c_MCSR s.procID).mstatus.MPRV /\
  pmp_unlocked (s.c_MCSR s.procID) /\
  ((n = 1) \/ (n = 2) /\ aligned 1 a \/ (n = 4) /\ aligned 2 a \/
   (n = 8) /\ aligned 3 a /\ pmp_off_or_napot (s.c_MCSR s.procID)) ==>
  (dataAddr (a, n, kind) s = SOME a)
Proof
  rw [dataAddr_def, translateAddr_def, effectivePrivilege_def, MCSR_def,
      curPrivilege_def, privilege_def]
  \\ match_mp_tac pmpCheck_Machine
  \\ simp []
QED

(* H6.  NextRISCV takes no interrupts: it always fetches and runs the
   instruction at the pc.  The spec's Next first checks for an interrupt
   that is pending, enabled and allowed in the current mode
   (checkInterrupts), and if there is one it takes it instead of running
   the instruction.  So a NextRISCV step theorem describes a step of Next
   only in a state in which no interrupt can be taken, and the theorems
   below add that hypothesis.  In M-mode (H1) an interrupt is taken only if
   mstatus.MIE is set, whatever is pending: interrupts delegated to S-mode
   are not taken in M-mode, and the others are taken only when MIE is set
   (P §3.1.6.1 p.32, §3.1.9 p.45).  Note that mie && 0x888 = 0w would not
   do: a pending, enabled and not delegated S-level interrupt (SSI, STI,
   SEI) is taken in M-mode too; what would do is that no enabled interrupt
   is undelegated, checkInterrupts_Machine_mie below. *)
Theorem checkInterrupts_Machine:
  (s.c_privilege s.procID = 3w) /\ ~(s.c_MCSR s.procID).mstatus.MIE ==>
  (checkInterrupts () s = NONE)
Proof
  rw [checkInterrupts_def, curPrivilege_def, privilege_def, MCSR_def]
QED

Theorem checkInterrupts_Machine_mie:
  (s.c_privilege s.procID = 3w) /\
  (reg'mie (s.c_MCSR s.procID).mie && ~(s.c_MCSR s.procID).mideleg = 0w) ==>
  (checkInterrupts () s = NONE)
Proof
  rw [checkInterrupts_def, curPrivilege_def, privilege_def, MCSR_def]
  \\ `!x. x && reg'mie (s.c_MCSR s.procID).mie &&
          ~(s.c_MCSR s.procID).mideleg = 0w`
     by metis_tac [wordsTheory.WORD_AND_ASSOC, wordsTheory.WORD_AND_CLAUSES]
  \\ simp [highestInterrupt_def]
QED

(* ------------------------------------------------------------------------
   Evaluation theorems

   As before the priv-1.13 model, these are equations about NextRISCV
   only, which does not depend on mstatus.MIE.  riscv_stepLib adds H6 to
   every step theorem that it builds from them, because NextRISCV refines
   Next only when no interrupt can be taken (checkInterrupts_Machine).
   ------------------------------------------------------------------------ *)

Theorem NextRISCV:
   (Fetch s = (w, s')) /\
   (DecodeAny ((s.c_MCSR s.procID).misa.C) w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = NONE) ==>
   (NextRISCV s = update_pc (nxt.c_PC nxt.procID + Skip nxt) nxt)
Proof
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def,
       haveRVC_def, MCSR_def]
QED

Theorem NextRISCV_branch:
   (Fetch s = (w, s')) /\
   (DecodeAny ((s.c_MCSR s.procID).misa.C) w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = SOME (BranchTo a)) ==>
   (NextRISCV s =
      update_pc a
        (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))
Proof
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def,
       haveRVC_def, MCSR_def]
QED

Theorem NextRISCV_cond_branch:
   (Fetch s = (w, s')) /\
   (DecodeAny ((s.c_MCSR s.procID).misa.C) w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = if b then SOME (BranchTo a) else NONE) ==>
   (NextRISCV s =
      update_pc (if b then a else nxt.c_PC nxt.procID + Skip nxt)
        (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))
Proof
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def,
       haveRVC_def, MCSR_def]
  \\ fs [update_pc_def, write'PC_def, riscv_state_component_equality,
         combinTheory.UPDATE_APPLY_IMP_ID]
QED

(* MRET (P §3.3.2 p.61, §3.1.6.1 p.32-33, §3.1.6.4 p.35): the privilege
   becomes mstatus.MPP (privilege maps the reserved 2 to U-mode, and
   privLevel back to 0), MIE becomes MPIE, MPIE becomes 1, MPP becomes U,
   MPRV is cleared unless MPP is M, and the pc becomes mepc, with bit 1
   masked when misa.C is clear (read_xepc). *)
Theorem mret_eval:
  mret () s =
  s with
  <| c_MCSR :=
       (s.procID =+
          s.c_MCSR s.procID with
          mstatus :=
            (s.c_MCSR s.procID).mstatus with
            <| MIE := (s.c_MCSR s.procID).mstatus.MPIE;
               MPIE := T;
               MPP := 0w;
               MPRV := ((s.c_MCSR s.procID).mstatus.MPRV /\
                        ((s.c_MCSR s.procID).mstatus.MPP = 3w)) |>)
       s.c_MCSR;
     c_privilege :=
       (s.procID =+
          if (s.c_MCSR s.procID).mstatus.MPP = 2w then 0w
          else (s.c_MCSR s.procID).mstatus.MPP) s.c_privilege;
     c_PC :=
       (s.procID =+
          if (s.c_MCSR s.procID).misa.C then (s.c_MCSR s.procID).mepc
          else (s.c_MCSR s.procID).mepc && ~3w) s.c_PC |>
Proof
  simp [mret_def, write'MCSR_def, MCSR_def, setPrivilege_def, read_xepc_def,
        haveRVC_def, write'PC_def]
  \\ wordsLib.Cases_on_word_value `(s.c_MCSR s.procID).mstatus.MPP`
  \\ simp [privilege_def, privLevel_def, riscv_state_component_equality,
           combinTheory.UPDATE_EQ]
QED

(* Trap entry to M-mode (P §3.1.6.1 p.32, §3.1.14-3.1.16 p.48-53): mcause,
   mepc and mtval are set, MPIE becomes MIE, MIE becomes 0, MPP becomes the
   privilege that the trap is taken from, the privilege becomes M, and the
   pc becomes the trap vector of mtvec. *)
Theorem takeTrap_Machine:
  takeTrap (intr, ec, epc, tval, Machine) s =
  s with
  <| c_MCSR :=
       (s.procID =+
          s.c_MCSR s.procID with
          <| mcause := <| EC := w2w ec; Int := intr |>;
             mepc := epc;
             mtval := tval;
             mstatus :=
               (s.c_MCSR s.procID).mstatus with
               <| MIE := F;
                  MPIE := (s.c_MCSR s.procID).mstatus.MIE;
                  MPP := if s.c_privilege s.procID = 2w then 0w
                         else s.c_privilege s.procID |> |>)
       s.c_MCSR;
     c_privilege := (s.procID =+ 3w) s.c_privilege;
     c_PC :=
       (s.procID =+ trapVector ((s.c_MCSR s.procID).mtvec, intr, ec)) s.c_PC |>
Proof
  simp [takeTrap_def, write'MCSR_def, MCSR_def, setPrivilege_def,
        curPrivilege_def, write'PC_def, privLevel_def]
  \\ wordsLib.Cases_on_word_value `s.c_privilege s.procID`
  \\ simp [privilege_def, privLevel_def, riscv_state_component_equality,
           combinTheory.UPDATE_EQ, MachineCSR_component_equality,
           mcause_component_equality]
QED

(* An exception is not an interrupt, so it goes to the base of mtvec, in
   Direct and in Vectored mode (P §3.1.7 p.41-42). *)
val trapVector_exception = Q.prove(
  `trapVector (tvec, F, ec) = tvec && ~3w`,
  simp [trapVector_def] \\ blastLib.BBLAST_TAC)

Theorem NextRISCV_mret:
   (Fetch s = (w, s')) /\
   (DecodeAny ((s.c_MCSR s.procID).misa.C) w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = SOME Mret) ==>
   (NextRISCV s =
      SOME
        (nxt with
         <| c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch;
            c_MCSR :=
              (nxt.procID =+
                 nxt.c_MCSR nxt.procID with
                 mstatus :=
                   (nxt.c_MCSR nxt.procID).mstatus with
                   <| MIE := (nxt.c_MCSR nxt.procID).mstatus.MPIE;
                      MPIE := T;
                      MPP := 0w;
                      MPRV := ((nxt.c_MCSR nxt.procID).mstatus.MPRV /\
                               ((nxt.c_MCSR nxt.procID).mstatus.MPP = 3w)) |>)
              nxt.c_MCSR;
            c_privilege :=
              (nxt.procID =+
                 if (nxt.c_MCSR nxt.procID).mstatus.MPP = 2w then 0w
                 else (nxt.c_MCSR nxt.procID).mstatus.MPP) nxt.c_privilege;
            c_PC :=
              (nxt.procID =+
                 if (nxt.c_MCSR nxt.procID).misa.C then
                   (nxt.c_MCSR nxt.procID).mepc
                 else (nxt.c_MCSR nxt.procID).mepc && ~3w) nxt.c_PC |>))
Proof
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def,
       haveRVC_def, MCSR_def, mret_eval]
  \\ simp [riscv_state_component_equality]
QED

(* A trap that the instruction raised, taken to M-mode, with the cause of
   the exception (Int = 0), the pc of the instruction in mepc, the trap
   value in mtval (the instruction bits for an illegal instruction) and the
   base of mtvec as the new pc.  The trap goes to M-mode, whatever medeleg
   holds, when it is taken from M-mode, and from a lower mode when medeleg
   does not delegate its cause (excDest; P §3.1.8 p.42-43).  riscv_stepLib
   uses it for ECALL, EBREAK and C.EBREAK; it has no step theorems for
   illegal instructions, which NextRISCV takes as traps too. *)
Theorem NextRISCV_trap:
   (Fetch s = (w, s')) /\
   (DecodeAny ((s.c_MCSR s.procID).misa.C) w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = SOME (Trap t)) /\
   ((nxt.c_privilege nxt.procID = 3w) \/
    ~word_bit (w2n (excCode t.trap)) (nxt.c_MCSR nxt.procID).medeleg) ==>
   (NextRISCV s =
      SOME
        (nxt with
         <| c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch;
            c_MCSR :=
              (nxt.procID =+
                 nxt.c_MCSR nxt.procID with
                 <| mcause := <| EC := w2w (excCode t.trap); Int := F |>;
                    mepc := nxt.c_PC nxt.procID;
                    mtval :=
                      (if t.trap = Illegal_Instr then rawInstBits w
                       else t.tval);
                    mstatus :=
                      (nxt.c_MCSR nxt.procID).mstatus with
                      <| MIE := F;
                         MPIE := (nxt.c_MCSR nxt.procID).mstatus.MIE;
                         MPP := if nxt.c_privilege nxt.procID = 2w then 0w
                                else nxt.c_privilege nxt.procID |> |>)
              nxt.c_MCSR;
            c_privilege := (nxt.procID =+ 3w) nxt.c_privilege;
            c_PC :=
              (nxt.procID =+ (nxt.c_MCSR nxt.procID).mtvec && ~3w) nxt.c_PC
         |>))
Proof
  strip_tac
  \\ `excDest (excCode t.trap, curPrivilege () nxt) nxt = Machine`
     by fs [excDest_def, curPrivilege_def, privilege_def, MCSR_def]
  \\ lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def,
          haveRVC_def, MCSR_def, takeTrap_Machine, trapVector_exception]
  \\ fs [riscv_state_component_equality]
QED

(* With misa.C clear a 16-bit instruction is illegal: NextRISCV takes the
   trap, with the parcel as the trap value (before the priv-1.13 model,
   NextRISCV gave NONE). *)
Theorem NextRISCV_Half_noC:
   (Fetch s = (Half h, s')) /\ ~(s.c_MCSR s.procID).misa.C /\
   (s'.exception = NoException) ==>
   (NextRISCV s =
      SOME (takeTrap (F, 2w, s'.c_PC s'.procID, w2w h,
                      excDest (2w, curPrivilege () s') s')
              (s' with c_NextFetch := (s'.procID =+ NONE) s'.c_NextFetch)))
Proof
  rw [NextRISCV_def, DecodeAny_def, haveRVC_def, MCSR_def, Run_def,
      dfn'UnknownInstruction_def, signalException_def, setTrap_def,
      write'NextFetch_def, NextFetch_def, PC_def, excCode_def,
      rawInstBits_def, excDest_def, curPrivilege_def, combinTheory.UPDATE_EQ]
QED

(* ------------------------------------------------------------------------
   Sub-word select operation (temporary)
   ------------------------------------------------------------------------ *)

Definition select_def[nocompute]:
  select (p:'a word) (w: word64) =
  let sz = 64 DIV (2 ** dimindex(:'a)) in
  let l = w2n p * sz in
    (l + sz - 1 >< l) w : 'b word
End

(* ------------------------------------------------------------------------
   Word extend abbreviations
   ------------------------------------------------------------------------ *)

val () = List.app Parse.temp_overload_on
   [
    ("s_extend32", ``\w: word64. sw2sw ((31 >< 0) w : word32) : word64``),
    ("z_extend32", ``\w: word64. w2w ((31 >< 0) w : word32) : word64``),
    ("s_extend16", ``\w: word64. sw2sw ((15 >< 0) w : word16) : word64``),
    ("z_extend16", ``\w: word64. w2w ((15 >< 0) w : word16) : word64``),
    ("s_extend8",  ``\w: word64. sw2sw ((7 >< 0) w : word8) : word64``),
    ("z_extend8",  ``\w: word64. w2w ((7 >< 0) w : word8) : word64``)
   ]

(* ------------------------------------------------------------------------
   Simplifying Rewrites
   ------------------------------------------------------------------------ *)

Theorem word_bit_1_0[simp]:
    (word_bit 1 ((v2w [x0; x1; x2; x3; x4; x5; x6; x7]):word8) = x6) /\
    (word_bit 0 ((v2w [x0; x1; x2; x3; x4; x5; x6; x7]):word8) = x7)
Proof
  blastLib.BBLAST_TAC
QED

val cond_lem1 = Q.prove(
  `(if b1 then (if b2 then x else y1) else (if b2 then x else y2)) =
   (if b2 then x else if b1 then y1 else y2)`,
  rw []
  )

val cond_rand_shift = Q.prove(
  `((if b then x else y) << n = if b then x << n else y << n) /\
   ((if b then x else y) >>> n = if b then x >>> n else y >>> n)`,
  rw []
  )

Theorem word_bit_0_lemmas:
   !w. ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64) /\
       word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w:word64) + v) = word_bit 0 v
Proof
  blastLib.BBLAST_TAC
QED

val cond_rand_thms =
  utilsLib.mk_cond_rand_thms
    [pairSyntax.fst_tm,
     pairSyntax.snd_tm,
     wordsSyntax.sw2sw_tm,
     wordsSyntax.w2w_tm,
     wordsSyntax.word_add_tm,
     wordsSyntax.word_and_tm,
     wordsSyntax.word_or_tm,
     wordsSyntax.word_xor_tm,
     ``(=):Architecture -> Architecture -> bool``,
     ``(=):'a word -> 'a word -> bool``,
     ``(h >< l) : 'a word -> 'b word``
    ]

val ifTF = Q.prove(`(if b then T else F) = b`, rw [])

Theorem v2w_0_rwts:
   ((v2w [F; F; F; F; T] = 1w: word5)) /\
   ((v2w [F; F; F; F; F] = 0w: word5)) /\
   ((v2w [T; b3; b2; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; T; b2; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; T; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; b1; T; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; b1; b0; T] = 0w: word5) = F)
Proof
   blastLib.BBLAST_TAC
QED

val aligned2 = Q.prove(
  `(!w: word64. ((1 >< 0) w = 0w: word2) = aligned 2 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val aligned3 = Q.prove(
  `(!w: word64. (w2n ((2 >< 0) w: word3) = 0) = aligned 3 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

(* The misaligned-access tests of the loads and stores, as alignment. *)

val aligned3w = Q.prove(
  `(!w: word64. ((2 >< 0) w = 0w: word3) = aligned 3 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val aligned1 = Q.prove(
  `(!w: word64. word_bit 0 w = ~aligned 1 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val address_align = blastLib.BBLAST_PROVE
  ``w2w ((63 >< 3) a : 61 word) << 3 = (63 '' 3) (a: word64)``

val address_align2 = blastLib.BBLAST_PROVE
  ``w2w ((63 >< 3) a + 1w: 61 word) << 3 = (63 '' 3) (a: word64) + 8w``

val address_aligned3 = uprove
  `aligned 3 (a: word64) ==> ((63 '' 3) a = a)`
  (
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val words_of_dword = Q.prove(
  `!b7:word8 b6:word8 b5:word8 b4:word8 b3:word8 b2:word8 b1:word8 b0:word8.
     ((63 >< 32) ( b7 @@ b6 @@ b5 @@ b4 @@ b3 @@ b2 @@ b1 @@ b0 ) =
                   b7 @@ b6 @@ b5 @@ b4) /\
     ((31 >< 0 ) ( b7 @@ b6 @@ b5 @@ b4 @@ b3 @@ b2 @@ b1 @@ b0 ) =
                   b3 @@ b2 @@ b1 @@ b0)`,
  simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )

val read_word = uprove
  `aligned 2 (a: word64) ==>
   ((if word_bit 2 a then
       (63 >< 32)
         (mem ((63 '' 3) a + 7w) @@
          mem ((63 '' 3) a + 6w) @@
          mem ((63 '' 3) a + 5w) @@
          mem ((63 '' 3) a + 4w) @@
          mem ((63 '' 3) a + 3w) @@
          mem ((63 '' 3) a + 2w) @@
          mem ((63 '' 3) a + 1w) @@
          mem ((63 '' 3) a)) : word32
     else
       (31 >< 0)
         (mem ((63 '' 3) a + 7w) @@
          mem ((63 '' 3) a + 6w) @@
          mem ((63 '' 3) a + 5w) @@
          mem ((63 '' 3) a + 4w) @@
          mem ((63 '' 3) a + 3w) @@
          mem ((63 '' 3) a + 2w) @@
          mem ((63 '' 3) a + 1w) @@
          mem ((63 '' 3) a))) =
    mem (a + 3w) @@ mem (a + 2w) @@ mem (a + 1w) @@ (mem a : word8))`
  (
  rewrite_tac [GSYM aligned2, words_of_dword]
  \\ strip_tac
  \\ CASE_TAC
  >| [
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  )

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  >| [
    `(2 >< 2) x = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) x = 1w: word1) /\
     ((2 >< 0) x = 4w: word3)` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 2) y = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) y = 1w: word1) /\
     ((2 >< 0) y = 4w: word3)` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC

val aligned_select_word_s = uprove
  `aligned 2 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       s_extend32 w0
     else
       s_extend32
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     s_extend32 (select (if b then (2 >< 2) x else (2 >< 2) y : word1) w0))`
   tac

val aligned_select_word_z = uprove
  `aligned 2 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       z_extend32 w0
     else
       z_extend32
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     z_extend32 (select (if b then (2 >< 2) x else (2 >< 2) y : word1) w0))`
   tac

val select_word = Q.prove(
  `aligned 2 (a: word64) ==>
   ((31 >< 0)
      (select ((2 >< 2) a : word1)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    mem (a + 3w) @@ mem (a + 2w) @@ mem (a + 1w) @@ (mem a : word8))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 2) a : word1`
  >| [
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]
  |> utilsLib.STRIP_UNDISCH

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  >| [
    `(2 >< 1) x = 0w: word2` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 1) x IN {1w; 2w; 3w: word2}`
    by (wordsLib.Cases_on_word_value `(2 >< 1) x : word2`
        \\ fs []
        \\ blastLib.FULL_BBLAST_TAC
       )
    \\ fs []
    >| [
      `(2 >< 0) x = 2w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) x = 4w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) x = 6w: word3` by blastLib.FULL_BBLAST_TAC
    ],
    `(2 >< 1) y = 0w: word2` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 1) y IN {1w; 2w; 3w: word2}`
    by (wordsLib.Cases_on_word_value `(2 >< 1) y : word2`
        \\ fs []
        \\ blastLib.FULL_BBLAST_TAC
       )
    \\ fs []
    >| [
      `(2 >< 0) y = 2w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) y = 4w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) y = 6w: word3` by blastLib.FULL_BBLAST_TAC
    ]
  ]
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC

val aligned_select_half_s = uprove
  `aligned 1 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       s_extend16 w0
     else
       s_extend16
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     s_extend16 (select (if b then (2 >< 1) x else (2 >< 1) y : word2) w0))`
  tac

val aligned_select_half_z = uprove
  `aligned 1 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       z_extend16 w0
     else
       z_extend16
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     z_extend16 (select (if b then (2 >< 1) x else (2 >< 1) y : word2) w0))`
  tac

val select_half = Q.prove(
  `aligned 1 (a: word64) ==>
   ((15 >< 0)
      (select ((2 >< 1) a : word2)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    mem (a + 1w) @@ (mem a : word8))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 1) a : word2`
  >| [
    `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]
  |> utilsLib.STRIP_UNDISCH

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  \\ fs []
  >| [
    `(2 >< 0) x : word3 = 0w` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 0) y : word3 = 0w` by blastLib.FULL_BBLAST_TAC,
    wordsLib.Cases_on_word_value `(2 >< 0) x : word3`,
    wordsLib.Cases_on_word_value `(2 >< 0) y : word3`
  ]
  \\ simp []
  \\ blastLib.BBLAST_TAC

val aligned_select_byte_s = Q.prove(
  `(if aligned 3 (if b then (x: word64) else y) then
      s_extend8 w0
    else
      s_extend8
        ((63 >< 0)
           (((w1: word64) @@ w0) >>
             (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
    s_extend8 (select (if b then (2 >< 0) x else (2 >< 0) y : word3) w0)`,
  tac
  )

val aligned_select_byte_z = Q.prove(
  `(if aligned 3 (if b then (x: word64) else y) then
      z_extend8 w0
    else
      z_extend8
        ((63 >< 0)
           (((w1: word64) @@ w0) >>
             (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
    z_extend8 (select (if b then (2 >< 0) x else (2 >< 0) y : word3) w0)`,
  tac
  )

val select_byte = Q.prove(
  `((7 >< 0)
      (select ((2 >< 0) a : word3)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    ((mem: word64 -> word8) a))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 0) a : word3`
  >| [
    `(63 '' 3) a = a - 7w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 5w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 3w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 1w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]

val byte_access = Q.prove(
  `w2n ((2 >< 0) a : word3) + 1 <= 8`,
  wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val aligned1_aligned3 = uprove
  `aligned 1 (a: word64) ==> (aligned 3 a = ((2 >< 1) a = 0w: word2))`
  (simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC)

val aligned1_aligned3b = uprove
  `aligned 1 (a: word64) ==> w2n ((2 >< 0) a : word3) + 2 <= 8`
  (
  rw [alignmentTheory.aligned_extract]
  \\ wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val aligned2_aligned3 = uprove
  `aligned 2 (a: word64) ==> (aligned 3 a = ((2 >< 2) a = 0w: word1))`
  (simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC)

val aligned2_aligned3b = uprove
  `aligned 2 (a: word64) ==> w2n ((2 >< 0) a : word3) + 4 <= 8`
  (
  rw [alignmentTheory.aligned_extract]
  \\ wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val w =
  List.tabulate (8, fn i => Term.mk_var ("b" ^ Int.toString i, ``:word8``))
val w = List.foldl wordsSyntax.mk_word_concat (hd w) (tl w)

val extract_thms = Q.prove(
  `((7  >< 0 ) ^w = b0) /\ ((15 >< 8 ) ^w = b1) /\ ((23 >< 16) ^w = b2) /\
   ((31 >< 24) ^w = b3) /\ ((39 >< 32) ^w = b4) /\ ((47 >< 40) ^w = b5) /\
   ((55 >< 48) ^w = b6) /\ ((63 >< 56) ^w = b7)`,
  simp_tac (std_ss++wordsLib.SIZES_ss++wordsLib.WORD_EXTRACT_ss)
    [wordsTheory.SHIFT_ZERO, wordsTheory.WORD_OR_CLAUSES]
  )

val extract_over_add =
  wordsTheory.WORD_EXTRACT_OVER_ADD
  |> Q.ISPECL [`a: word64`, `b: word64`, `31n`]
  |> INST_TYPE [Type.beta |-> ``:32``]
  |> SIMP_RULE (srw_ss()) []
  |> GSYM

val jal = uprove
  `aligned 2 (pc: word64) /\ ~word_lsb (imm: word20) ==>
   aligned 2 (pc + sw2sw imm << 1)`
  (
  simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC
  )

val jalr = uprove
  `(b \/ aligned 2 x) /\ ~(imm: word12 ' 1) ==>
   aligned 2 (if b then sw2sw imm && 0xFFFFFFFFFFFFFFFEw : word64
              else x + sw2sw imm && 0xFFFFFFFFFFFFFFFEw)`
  (
  rw [alignmentTheory.aligned_extract]
  \\ blastLib.FULL_BBLAST_TAC
  )

Theorem Decode_IMP_DecodeAny:
    (Decode w = i) ==> (DecodeAny rvc (Word w) = i)
Proof
  fs [DecodeAny_def]
QED

Theorem DecodeRVC_IMP_DecodeAny:
    (DecodeRVC h = i) ==> rvc ==> (DecodeAny rvc (Half h) = i)
Proof
  fs [DecodeAny_def]
QED

Theorem avoid_signalAddressException:
    ~b ==> ((if b then signalAddressException t u else s) = s)
Proof
  fs []
QED

Theorem word_bit_add_lsl_simp:
    word_bit 0 (x + w << 1) = word_bit 0 (x:word64)
Proof
  blastLib.BBLAST_TAC
QED

(* ------------------------------------------------------------------------
   Evaluation setup
   ------------------------------------------------------------------------ *)

val s = ``s:riscv_state``
val rd0 = ``rd = 0w: word5``
val archbase = ``(^s.c_MCSR ^s.procID).misa.MXL``
val rvc = ``(^s.c_MCSR ^s.procID).misa.C``
(* in32BitMode is misa.MXL = 1w; the RV64-only instructions are illegal
   then, and SLLI/SRLI/SRAI also with shamt<5> set. *)
val rv64 = ``^archbase <> 1w``
val shift = ``~((^archbase = 1w) /\ word_bit 5n (imm: word6))``
fun ialign_ok a = ``~(word_bit 1 (^a: word64) /\ ~^rvc)``
val pc_ok =
  [``~word_bit 0 (^s.c_PC ^s.procID)``, ialign_ok ``^s.c_PC ^s.procID``]

(* H5: the address of a load or store, rs1 + offs, and of an AMO, LR or SC,
   rs1, is naturally aligned.  A misaligned access raises an exception
   before any other check ([D55]), so without this hypothesis the step
   theorem would have a trap branch. *)
local
  val addr =
    ``if rs1 = 0w then sw2sw offs
      else ^s.c_gpr ^s.procID rs1 + sw2sw (offs:word12)``
  val amo_addr = ``if rs1 = 0w then 0w else ^s.c_gpr ^s.procID rs1``
  fun al n a = ``aligned ^(numSyntax.term_of_int n) (^a: word64)``
in
  val aligned_h = al 1 addr
  val aligned_w = al 2 addr
  val aligned_d = al 3 addr
  val aligned_amo_w = al 2 amo_addr
  val aligned_amo_d = al 3 amo_addr
end

(* H1 to H4 as word-level conjuncts *)
val h1 = ``^s.c_privilege ^s.procID = 3w``
val h2 = ``~(^s.c_MCSR ^s.procID).mstatus.MPRV``
val h3 =
  [``(^s.c_MCSR ^s.procID).pmpcfg0 && 0x8080808080808080w = 0w``,
   ``(^s.c_MCSR ^s.procID).pmpcfg2 && 0x8080808080808080w = 0w``]
val h4 =
  [``((^s.c_MCSR ^s.procID).pmpcfg0 >>> 1 ?? (^s.c_MCSR ^s.procID).pmpcfg0) &&
     0x0808080808080808w = 0w``,
   ``((^s.c_MCSR ^s.procID).pmpcfg2 >>> 1 ?? (^s.c_MCSR ^s.procID).pmpcfg2) &&
     0x0808080808080808w = 0w``]

(* The F and D instructions are illegal while mstatus.FS is Off. *)
val fp_on = ``(^s.c_MCSR ^s.procID).mstatus.FS <> 0w``

local
  (* The CSR records inside the state.  An F or D instruction can set an
     fcsr flag, and so mstatus.FS, under a condition; the conditional record
     that this gives is pushed into its fields, and the updates of one field
     are merged, so that the step theorem updates each field once.  (Not
     datatype_rewrites, whose literal rewrites loop on UserCSR, a record of
     one field.) *)
  val cond_updates =
    utilsLib.mk_cond_update_thms
      [``:riscv_state``, ``:MachineCSR``, ``:mstatus``, ``:UserCSR``,
       ``:FPCSR``]
  val csr_record_rwts =
    [MachineCSR_accfupds, MachineCSR_fupdfupds, MachineCSR_fupdcanon,
     mstatus_accfupds, mstatus_fupdfupds, mstatus_fupdcanon,
     UserCSR_accfupds, UserCSR_fupdfupds,
     FPCSR_accfupds, FPCSR_fupdfupds, FPCSR_fupdcanon,
     combinTheory.UPDATE_EQ]
  val datatype_rwts =
    utilsLib.datatype_rewrites true "riscv"
      ["riscv_state", "Architecture", "Privilege", "pmpAccess", "ExtStatus"]
  fun riscv_thms thms =
    thms @ cond_updates @ csr_record_rwts @ datatype_rwts @
    [wordsTheory.WORD_EXTRACT_ZERO2, wordsTheory.ZERO_SHIFT,
     wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES,
     wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
     wordsTheory.WORD_XOR_CLAUSES, wordsTheory.w2w_0, wordsTheory.sw2sw_0,
     ifTF, cond_lem1, extract_over_add, cond_rand_shift, cond_rand_thms
     ]
in
  fun step_conv b =
    utilsLib.setStepConv
       (if b then
          Conv.DEPTH_CONV wordsLib.SIZES_CONV
          THENC utilsLib.WGROUND_CONV
        else
          ALL_CONV)
  val ev = utilsLib.STEP (riscv_thms, s)
  fun EV a b c d = hd (ev a b c d)
end

local
  val word_eq_ss =
    simpLib.std_conv_ss
      {name = "word_eq", conv = wordsLib.word_EQ_CONV,
       pats = [``n2w a = n2w b: word64``]}
in
  val store_tac =
    asm_simp_tac (std_ss++wordsLib.WORD_ss)
       [GSYM wordsTheory.WORD_EXTRACT_OVER_BITWISE, extract_thms]
    \\ simp_tac (std_ss++wordsLib.SIZES_ss++wordsLib.WORD_EXTRACT_ss)
         [wordsTheory.SHIFT_ZERO, wordsTheory.WORD_OR_CLAUSES]
    \\ simp_tac
         (std_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_CANCEL_ss++word_eq_ss)
         [updateTheory.UPDATE_APPLY_IMP_ID, combinTheory.UPDATE_APPLY]
end

(* ------------------------------------------------------------------------
   Architecture Rewrites
   ------------------------------------------------------------------------ *)

val () = step_conv false

(* Address translation is the identity: satp.MODE is Bare. *)
val translateAddr = EV [translateAddr_def] [] []
  ``translateAddr (vPC, ft, ac)``

(* misa.MXL is 2 in every reachable state, so this is false; the RV32 cases
   stay in the step theorems as before. *)
val in32BitMode = EV [in32BitMode_def, MCSR_def] [] [] ``in32BitMode()``

val haveRVC = EV [haveRVC_def, MCSR_def] [] [] ``haveRVC()``

val PC = EV [PC_def] [] [] ``PC``

val Skip = save_thm("Skip",EV [Skip_def,boolify8_def] [] [] ``Skip``);

val rawReadInst = EV
  [rawReadInst_def, MEM_def, address_align, read_word] [] []
  ``rawReadInst a``

val rawReadData = EV
  [rawReadData_def, aligned3, MEM_def, address_align, address_align2]
  [] []
  ``rawReadData a``

val branchTo = EV
  [branchTo_def, write'NextFetch_def] [] []
  ``branchTo newPC``

val GPR = EV [GPR_def, gpr_def] [] [] ``GPR n``

val write'GPR0 =
  ev [write'GPR_def] [[``d = 0w:word5``]] []
  ``write'GPR (n, d)`` |> hd

val write'GPR =
  ev [write'GPR_def, write'gpr_def] [[``d <> 0w:word5``]] []
  ``write'GPR (n, d)`` |> hd

val update_pc = Theory.save_thm("update_pc",
  EV [update_pc_def, write'PC_def] [] [] ``update_pc v``)

(* The PMP check of a fetch parcel in M-mode, from H1 and H3. *)
val fetchAddr = uprove
  `^h1 /\ ^(hd h3) /\ ^(hd (tl h3)) /\ ~word_bit 0 a ==>
   (fetchAddr a s = SOME a)`
  (
  rw [] \\ match_mp_tac fetchAddr_Machine
  \\ fs [pmp_unlocked_def, aligned1]
  )

val Fetch =
  EV [Fetch_def, PC, haveRVC, fetchAddr, rawReadInst, boolify8_def,
      write'Skip_def] [pc_ok] []
    ``Fetch``

(* The second parcel of a 32-bit instruction, at pc + 2, is as aligned as
   the first. *)
val word_bit_0_add2 = blastLib.BBLAST_PROVE
  ``word_bit 0 ((a: word64) + 2w) = word_bit 0 a``

(* The fetch of a 32-bit and of a 16-bit instruction in M-mode.  The PMP
   allows both parcels (fetchAddr_Machine): H1, the hart is in M-mode, and
   H3, no PMP entry is locked, suffice because a 2-byte parcel at an even
   address never straddles a region bound. *)

Theorem Fetch32:
    !xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
        y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF.
       (xs = [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9; yA; yB; yC; yD; yE; yF;
              x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       (s.c_privilege s.procID = 3w) ∧
       ((s.c_MCSR s.procID).pmpcfg0 && 0x8080808080808080w = 0w) ∧
       ((s.c_MCSR s.procID).pmpcfg2 && 0x8080808080808080w = 0w) ∧
       ~word_bit 0 (s.c_PC s.procID) ∧
       (~word_bit 1 (s.c_PC s.procID) ∨ (s.c_MCSR s.procID).misa.C) ∧
       (s.MEM8 (s.c_PC s.procID + 3w) = v2w [y0; y1; y2; y3; y4; y5; y6; y7]) ∧
       (s.MEM8 (s.c_PC s.procID + 2w) = v2w [y8; y9; yA; yB; yC; yD; yE; yF]) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       xE ∧ xF ⇒
       (Fetch s =
        (Word (v2w xs), s with c_Skip := (s.procID =+ 4w) s.c_Skip))
Proof
  simp [Fetch |> DISCH_ALL, word_bit_0_add2] \\ rw [] \\ blastLib.BBLAST_TAC
QED

Theorem Fetch16:
    !xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF.
       (xs = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       (s.c_privilege s.procID = 3w) ∧
       ((s.c_MCSR s.procID).pmpcfg0 && 0x8080808080808080w = 0w) ∧
       ((s.c_MCSR s.procID).pmpcfg2 && 0x8080808080808080w = 0w) ∧
       ~word_bit 0 (s.c_PC s.procID) ∧
       (~word_bit 1 (s.c_PC s.procID) ∨ (s.c_MCSR s.procID).misa.C) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       ~(xE ∧ xF) ⇒
       (Fetch s =
        (Half (v2w xs), s with c_Skip := (s.procID =+ 2w) s.c_Skip))
Proof
  simp [Fetch |> DISCH_ALL, word_bit_0_add2] \\ rw [] \\ blastLib.BBLAST_TAC
QED

(* ------------------------------------------------------------------------
   Memory Store Rewrites
   ------------------------------------------------------------------------ *)

val () = step_conv true

val write'MEM = EV [write'MEM_def] [] [] ``write'MEM (d, a)``

fun write_data_ev l1 l2 =
  EV ([rawWriteData_def, aligned3, MEM_def, write'MEM, address_align] @ l1) l2
     []

val rawWriteData8 =
  write_data_ev [address_aligned3] [[``aligned 3 (a: word64)``]]
  ``rawWriteData (a, d, 8)``

fun get_mem8 thm =
  thm |> utilsLib.rhsc
      |> boolSyntax.rator
      |> boolSyntax.rand
      |> boolSyntax.rand

val rawWriteData4 = write_data_ev [aligned2_aligned3, aligned2_aligned3b] []
  ``rawWriteData (a, d, 4)``

val tm = get_mem8 rawWriteData4

val thm = uprove
  `aligned 2 a ==>
   (^tm = (a =+ (7 >< 0) d) ((a + 1w =+ (15 >< 8) d)
             ((a + 2w =+ (23 >< 16) d) ((a + 3w =+ (31 >< 24) d) s.MEM8))))`
  (
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ `(2 >< 0) a : word3 = 4w: word3` by blastLib.FULL_BBLAST_TAC
  \\ `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC
  \\ store_tac
  )

val rawWriteData4 = utilsLib.INST_REWRITE_RULE [thm] rawWriteData4

val rawWriteData2 = write_data_ev [aligned1_aligned3, aligned1_aligned3b] []
  ``rawWriteData (a, d, 2)``

val tm = get_mem8 rawWriteData2

val thm = uprove
  `aligned 1 a ==> (^tm = (a =+ (7 >< 0) d) ((a + 1w =+ (15 >< 8) d) s.MEM8))`
  (
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ `(2 >< 0) a : word3 IN {2w; 4w; 6w: word3}`
  by (simp [] \\ blastLib.FULL_BBLAST_TAC)
  \\ fs []
  >| [
     `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC
  ]
  \\ store_tac
  )

val rawWriteData2 = utilsLib.INST_REWRITE_RULE [thm] rawWriteData2

val rawWriteData1 = write_data_ev [byte_access] [] ``rawWriteData (a, d, 1)``

val tm = get_mem8 rawWriteData1

val thm = Q.prove(
  `^tm = (a =+ (7 >< 0) d) s.MEM8`,
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ wordsLib.Cases_on_word_value `(2 >< 0) a: word3`
  \\ fs []
  >| [
     `(63 '' 3) a = a - 7w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 5w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 3w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 1w` by blastLib.FULL_BBLAST_TAC,
     blastLib.FULL_BBLAST_TAC
  ]
  \\ store_tac
  )

val rawWriteData1 = REWRITE_RULE [thm] rawWriteData1

(* ------------------------------------------------------------------------
   Data access and privilege rewrites
   ------------------------------------------------------------------------ *)

(* The PMP check of a naturally aligned data access in M-mode (H1, H2, H3,
   and H4 for 8 bytes).  The alignment is the hypothesis H5 of the step
   theorem, which has already eliminated the misaligned-access trap. *)

val dataAddr1 = uprove
  `^h1 /\ ^h2 /\ ^(hd h3) /\ ^(hd (tl h3)) ==>
   (dataAddr (a, 1, k) s = SOME a)`
  (rw [] \\ match_mp_tac dataAddr_Machine \\ fs [pmp_unlocked_def])

val dataAddr2 = uprove
  `^h1 /\ ^h2 /\ ^(hd h3) /\ ^(hd (tl h3)) /\ aligned 1 a ==>
   (dataAddr (a, 2, k) s = SOME a)`
  (rw [] \\ match_mp_tac dataAddr_Machine \\ fs [pmp_unlocked_def])

val dataAddr4 = uprove
  `^h1 /\ ^h2 /\ ^(hd h3) /\ ^(hd (tl h3)) /\ aligned 2 a ==>
   (dataAddr (a, 4, k) s = SOME a)`
  (rw [] \\ match_mp_tac dataAddr_Machine \\ fs [pmp_unlocked_def])

val dataAddr8 = uprove
  `^h1 /\ ^h2 /\ ^(hd h3) /\ ^(hd (tl h3)) /\ ^(hd h4) /\ ^(hd (tl h4)) /\
   aligned 3 a ==>
   (dataAddr (a, 8, k) s = SOME a)`
  (
  rw [] \\ match_mp_tac dataAddr_Machine
  \\ fs [pmp_unlocked_def, pmp_off_or_napot_def]
  )

(* WFI and SFENCE.VMA depend on the current privilege (H1). *)
val curPrivilege = uprove
  `^h1 ==> (curPrivilege () s = Machine)`
  (rw [curPrivilege_def, privilege_def])

(* mstatus.FS <> Off; the F and D step theorems assume it (fp_on). *)
val fpEnabled = EV [fpEnabled_def, MCSR_def, ext_status_def] [] []
  ``fpEnabled ()``

(* The reservation test of SC, kept in its step theorem, as one equation:
   the reservation is set, at the address of the SC. *)
val matchLoadReservation = Q.prove(
  `matchLoadReservation a s = (s.c_ReserveLoad s.procID = SOME a)`,
  rw [matchLoadReservation_def, ReserveLoad_def]
  \\ Cases_on `s.c_ReserveLoad s.procID`
  \\ simp [])

(* A 32-bit load into an FPR: as aligned_select_word_s, without the
   extension. *)
val aligned_select_word = uprove
  `aligned 2 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       (31 >< 0) w0 : word32
     else
       (31 >< 0)
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8))
          : word64)) =
     (31 >< 0) (select (if b then (2 >< 2) x else (2 >< 2) y : word1) w0
                : word64))`
  (
  lrw [select_def, alignmentTheory.aligned_extract]
  >| [
    `(2 >< 2) x = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) x = 1w: word1) /\
     ((2 >< 0) x = 4w: word3)` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 2) y = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) y = 1w: word1) /\
     ((2 >< 0) y = 4w: word3)` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC
  )

(* The 32-bit read of an AMO, whose value is used twice (written to rd, and
   combined with rs2 and stored): reading it in one rewrite, before the
   conditional of rawReadData is distributed over the two uses. *)
val read_word32 = uprove
  `aligned 2 (a: word64) ==>
   ((31 >< 0) (rawReadData a s) : word32 =
    s.MEM8 (a + 3w) @@ s.MEM8 (a + 2w) @@ s.MEM8 (a + 1w) @@ s.MEM8 a)`
  (
  rewrite_tac [rawReadData]
  \\ strip_tac
  \\ qabbrev_tac `mem = s.MEM8`
  \\ Cases_on `aligned 3 a`
  \\ asm_rewrite_tac []
  >- (`(63 '' 3) a = a` by (fs [alignmentTheory.aligned_extract]
                             \\ blastLib.FULL_BBLAST_TAC)
      \\ asm_simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) [])
  \\ `((63 '' 3) a = a - 4w) /\ ((2 >< 0) a = 4w: word3)`
  by (fs [alignmentTheory.aligned_extract] \\ blastLib.FULL_BBLAST_TAC)
  \\ asm_simp_tac std_ss []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )

(* ------------------------------------------------------------------------
   Floating-point rounding modes
   ------------------------------------------------------------------------ *)

(* The rounding modes that L3 implements, by their rm encoding: RNE, RTZ,
   RDN and RUP.  An instruction that rounds is illegal with rm = 4 (RMM,
   which neither L3 nor HOL's binary_ieee implements), 5 or 6, and with
   rm = 7 (dynamic) when fcsr.frm is not one of the four.  So its step
   theorem for a static rm needs nothing more, and the one for rm = 7 needs
   ~word_bit 2 fcsr.frm. *)
Definition frm_rounding_def:
  frm_rounding (frm: word3) =
    if frm = 0w then roundTiesToEven
    else if frm = 1w then roundTowardZero
    else if frm = 2w then roundTowardNegative
    else roundTowardPositive
End

(* For the step theorems of instructions whose rm field is static ... *)
Theorem round_static:
  fprnd <> 4w /\ fprnd <> 5w /\ fprnd <> 6w /\ fprnd <> 7w ==>
  (round fprnd s = SOME (frm_rounding fprnd))
Proof
  wordsLib.Cases_on_word_value `fprnd`
  \\ simp [round_def, rnd_mode_static_def, l3round_def, frm_rounding_def]
QED

(* ... and dynamic. *)
Theorem round_dynamic:
  (fprnd = 7w) /\ ~word_bit 2 (s.c_UCSR s.procID).fpcsr.FRM ==>
  (round fprnd s = SOME (frm_rounding (s.c_UCSR s.procID).fpcsr.FRM))
Proof
  rw [round_def, rnd_mode_static_def, fcsr_def]
  \\ wordsLib.Cases_on_word_value `(s.c_UCSR s.procID).fpcsr.FRM`
  \\ fs [rnd_mode_dynamic_def, l3round_def, frm_rounding_def]
QED

(* FCVT.D.W, FCVT.D.WU and FCVT.D.S are exact: they never round, and only
   test that their rm field is a valid encoding (validRounding).  So RMM
   (4) is legal for them, as a static mode and as fcsr.frm, and the step
   theorem for rm = 7 needs fcsr.frm <+ 5w, which is exactly the legality
   of the dynamic mode (riscv.spec, validRounding). *)
Theorem validRounding_static:
  fprnd <> 5w /\ fprnd <> 6w /\ fprnd <> 7w ==> validRounding fprnd s
Proof
  wordsLib.Cases_on_word_value `fprnd`
  \\ simp [validRounding_def, rnd_mode_static_def]
QED

Theorem validRounding_dynamic:
  (fprnd = 7w) /\ (s.c_UCSR s.procID).fpcsr.FRM <+ 5w ==>
  validRounding fprnd s
Proof
  rw [validRounding_def, rnd_mode_static_def, fcsr_def]
  \\ wordsLib.Cases_on_word_value `(s.c_UCSR s.procID).fpcsr.FRM`
  \\ fs [rnd_mode_dynamic_def]
QED

(* Used by riscv_stepLib once the rm field of a static theorem is known. *)
Theorem frm_rounding_v2w:
  (frm_rounding (v2w [F; F; F]) = roundTiesToEven) /\
  (frm_rounding (v2w [F; F; T]) = roundTowardZero) /\
  (frm_rounding (v2w [F; T; F]) = roundTowardNegative) /\
  (frm_rounding (v2w [F; T; T]) = roundTowardPositive)
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Floating-point exception flags
   ------------------------------------------------------------------------ *)

(* accrueFlags sets the fflags bits that an IEEE operation raised, one
   flag at a time, each with a write of fcsr that also makes mstatus.FS
   Dirty.  Evaluated as it stands, each of the five steps reads fcsr from
   the state of the step before, under its condition, and the state grows
   exponentially with the steps.  accrueFlags_update states the effect as
   one update of each field: a flag is set if it was set or is raised, and
   FS is Dirty if any flag is raised.  It is proved one flag at a time,
   each intermediate state being simplified before the next step reads
   it. *)

local
  (* srw_ss writes an update of UserCSR, a record of one field, as a
     literal *)
  val UserCSR_literal = Q.prove(
    `<| fpcsr := u.fpcsr |> = u: UserCSR`,
    simp [UserCSR_component_equality])
  (* if b then setFP_X () s else s, for the flag X of setFP_X *)
  fun flag_thm (f, x) =
    let
      val fpcsr = "(s.c_UCSR s.procID).fpcsr"
      val mstatus = "(s.c_MCSR s.procID).mstatus"
    in
      Q.prove(
        [QUOTE ("(if b then " ^ f ^ " () s else s) = \
                \s with <| c_UCSR := (s.procID =+ s.c_UCSR s.procID with \
                \fpcsr := " ^ fpcsr ^ " with " ^ x ^ " := (" ^ fpcsr ^
                "." ^ x ^ " \\/ b)) s.c_UCSR; c_MCSR := (s.procID =+ \
                \s.c_MCSR s.procID with mstatus := " ^ mstatus ^ " with \
                \FS := if b then 3w else " ^ mstatus ^ ".FS) s.c_MCSR |>")],
        Cases_on `b`
        \\ simp_tac (srw_ss())
             [setFP_Invalid_def, setFP_DivZero_def, setFP_Overflow_def,
              setFP_Underflow_def, setFP_Inexact_def, write'fcsr_def,
              fcsr_def, ext_status_def, LET_THM, UserCSR_literal,
              riscv_state_fupdselfid, MachineCSR_fupdselfid,
              mstatus_fupdselfid, UserCSR_fupdselfid, FPCSR_fupdselfid,
              combinTheory.APPLY_UPDATE_ID, combinTheory.UPDATE_EQ])
    end
  val flag_thms =
    List.map flag_thm
      [("setFP_Invalid", "NV"), ("setFP_DivZero", "DZ"),
       ("setFP_Overflow", "OF"), ("setFP_Underflow", "UF"),
       ("setFP_Inexact", "NX")]
  val cond_or = Q.prove(
    `(if a then x else if b then x else y) = (if a \/ b then x else y)`,
    Cases_on `a` \\ Cases_on `b` \\ rewrite_tac [])
  val simp_state =
    SIMP_CONV std_ss
      (cond_or :: flag_thms @
       [riscv_state_accfupds, riscv_state_fupdfupds, riscv_state_fupdcanon,
        UserCSR_accfupds, UserCSR_fupdfupds,
        FPCSR_accfupds, FPCSR_fupdfupds, FPCSR_fupdcanon,
        MachineCSR_accfupds, MachineCSR_fupdfupds,
        mstatus_accfupds, mstatus_fupdfupds,
        combinTheory.K_o_THM, combinTheory.UPDATE_EQ,
        combinTheory.APPLY_UPDATE_THM])
  (* let s = v in t: simplify v, then substitute it *)
  fun let_conv tm =
    if boolSyntax.is_let tm then
      (Conv.RAND_CONV simp_state THENC Conv.REWR_CONV LET_THM
       THENC Thm.BETA_CONV THENC let_conv) tm
    else simp_state tm
in
  val accrueFlags_steps =
    (Conv.RATOR_CONV (Conv.REWR_CONV accrueFlags_def) THENC Thm.BETA_CONV
     THENC let_conv) ``accrueFlags f s``
end

Theorem accrueFlags_update:
  accrueFlags f s =
  s with
  <| c_UCSR :=
       (s.procID =+
          s.c_UCSR s.procID with
          fpcsr :=
            (s.c_UCSR s.procID).fpcsr with
            <| NV := ((s.c_UCSR s.procID).fpcsr.NV \/ f.InvalidOp);
               DZ := ((s.c_UCSR s.procID).fpcsr.DZ \/ f.DivideByZero);
               OF := ((s.c_UCSR s.procID).fpcsr.OF \/ f.Overflow);
               UF := ((s.c_UCSR s.procID).fpcsr.UF \/
                      f.Underflow_AfterRounding);
               NX := ((s.c_UCSR s.procID).fpcsr.NX \/ f.Precision) |>)
         s.c_UCSR;
     c_MCSR :=
       (s.procID =+
          s.c_MCSR s.procID with
          mstatus :=
            (s.c_MCSR s.procID).mstatus with
            FS := if f.InvalidOp \/ f.DivideByZero \/ f.Overflow \/
                     f.Underflow_AfterRounding \/ f.Precision
                  then 3w
                  else (s.c_MCSR s.procID).mstatus.FS)
         s.c_MCSR |>
Proof
  rewrite_tac [accrueFlags_steps]
  \\ simp_tac std_ss
       [riscv_state_fupdcanon, FPCSR_fupdcanon, AC DISJ_ASSOC DISJ_COMM]
QED

(* ------------------------------------------------------------------------
   Instruction Rewrites
   ------------------------------------------------------------------------ *)

local
  val l =
    [GPR, in32BitMode, haveRVC, PC, wordsTheory.word_len_def,
     branchTo, translateAddr, jal, jalr, aligned2, aligned3w,
     dataAddr1, dataAddr2, dataAddr4, dataAddr8, curPrivilege,
     matchLoadReservation, write'ReserveLoad_def,
     aligned_select_word_s, aligned_select_word_z, aligned_select_word,
     select_word,
     aligned_select_half_s, aligned_select_half_z, select_half,
     aligned_select_byte_s, aligned_select_byte_z, select_byte,
     rawReadData, rawWriteData8, rawWriteData4, rawWriteData2, rawWriteData1,
     fpEnabled, ext_status_def, FPRS_def, FPRD_def, fpr_def,
     write'FPRS_def, write'FPRD_def, write'fpr_def,
     writeFPRS_def, writeFPRD_def, MCSR_def, write'MCSR_def,
     Delta_def, write'Delta_def, fcsr_def, write'fcsr_def,
     FPRS_raw_def, accrueFlags_update, setFP_Invalid_def, setFP_DivZero_def,
     setFP_Overflow_def, setFP_Underflow_def, setFP_Inexact_def] @
    (* Record and pair reductions for the call-by-value pass of the
       evaluation, which otherwise leaves a field of an updated state, or
       a component of a pair, unreduced.  An F or D instruction passes the
       state through several updates (accrueFlags, a conditional flag,
       writeFPRS), each reading the state before it; unreduced, each read
       copies that whole state. *)
    [riscv_state_accfupds, pairTheory.FST, pairTheory.SND,
     MachineCSR_accfupds, MachineCSR_fupdfupds,
     mstatus_accfupds, mstatus_fupdfupds,
     UserCSR_accfupds, UserCSR_fupdfupds,
     FPCSR_accfupds, FPCSR_fupdfupds,
     combinTheory.K_o_THM, combinTheory.UPDATE_EQ]
  val hyp_eq_rule =
    utilsLib.ALL_HYP_CONV_RULE (Conv.DEPTH_CONV wordsLib.word_EQ_CONV)
  (* No trap branch, and no PMP check or rounding mode left. *)
  val bad =
    List.map Term.same_const
      [``signalAddressException``, ``signalException``, ``raise'exception``,
       ``dataAddr``, ``fetchAddr``, ``round``, ``validRounding``]
  (* Nor any other function of the model that reads or writes the state:
     the result must be s with field updates only.  Skip is the exception:
     NextRISCV adds it to the pc, and as before the priv-1.13 model the
     step theorems keep it, applied to the state after the fetch, whose
     c_Skip the fetch sets (consumers rewrite it with Skip_def, e.g.
     HolBA's lifter). *)
  val state_ty = ``:riscv_state``
  (* the prefix of the names of the field selectors and updates *)
  val field =
    TypeBasePure.mk_recordtype_fieldsel {tyname = "riscv_state", fieldname = ""}
  fun unevaluated allowed tm =
    Term.is_const tm andalso
    let
      val {Thy, Name, Ty} = Term.dest_thy_const tm
    in
      Thy = "riscv" andalso not (String.isPrefix field Name) andalso
      not (Lib.mem Name ("Skip" :: allowed)) andalso
      List.exists (fn ty => ty = state_ty) (fst (HolKernel.strip_fun Ty))
    end
  fun check allowed n th =
    case List.find (fn p => Lib.can (HolKernel.find_term p) (Thm.concl th))
           bad of
       SOME _ =>
         ( print_thm th; print "\n"
         ; raise ERR "class" ("trap or check left in " ^ n))
     | NONE =>
         case Lib.total (HolKernel.find_term (unevaluated allowed))
                (boolSyntax.rhs (Thm.concl th)) of
            SOME c =>
              ( print_thm th; print "\n"
              ; raise ERR "class"
                  (Parse.term_to_string c ^ " left in " ^ n))
          | NONE => th
  (* 8-byte loads read one aligned double-word *)
  val reads8 = ["LD", "FLD", "LR_D"] @
    List.map (fn s => "AMO" ^ s ^ "_D")
      ["SWAP", "ADD", "XOR", "AND", "OR", "MIN", "MAX", "MINU", "MAXU"]
  (* LH, LHU and SH test bit 0 of the address for misalignment *)
  val half = ["LH", "LHU", "SH"]
  (* LR.W and the 32-bit AMOs read the word with read_word32: the
     select_word rewrites need an address of the form rs1 + offs *)
  val amo_w = "LR_W" ::
    List.map (fn s => "AMO" ^ s ^ "_W")
      ["SWAP", "ADD", "XOR", "AND", "OR", "MIN", "MAX", "MINU", "MAXU"]
  val l_amo_w =
    read_word32 ::
    List.filter (fn th => not (aconv (Thm.concl th) (Thm.concl rawReadData))) l
in
  (* allowed: the functions of the model, besides Skip, that may stay in
     the conclusion; only the CSR instructions have any (see below) *)
  fun class_gen allowed extra suffix args avoid n =
    let
      val name = "dfn'" ^ n
      val read = if Lib.mem n reads8 then [address_aligned3] else []
      val align = if Lib.mem n half then [aligned1] else []
      val l = if Lib.mem n amo_w then l_amo_w else l
      val (write, n) =
        if List.exists (tmem rd0) avoid then
          ([write'GPR0], n ^ "_NOP")
        else
          ([write'GPR], n)
      val thms = DB.fetch "riscv" (name ^ "_def") :: write @ read @ align @ extra
    in
      case ev (thms @ l) avoid [] (Parse.Term ([QUOTE name] @ args)) of
         [th] =>
           utilsLib.save_thms (n ^ suffix) [check allowed n (hyp_eq_rule th)]
       | _ => raise ERR "class" ("more than one theorem" ^ n)
    end
  val class_with = class_gen []
  val class = class_with [] ""
end

fun add_rd0 avoid =
  case avoid of
     [] => [[rd0]]
   | [l] => [rd0 :: l]
   | _ => raise ERR "" ""

fun class_rd0 args avoid n =
  let
    val f = class args
  in
    (f avoid n, f (add_rd0 avoid) n)
  end

val arithi = class_rd0 `(rd, rs1, imm)`

val ADDI  = arithi [] "ADDI"
val ADDIW = arithi [[rv64]] "ADDIW"
val SLTI  = arithi [] "SLTI"
val SLTIU = arithi [] "SLTIU"
val ANDI  = arithi [] "ANDI"
val ORI   = arithi [] "ORI"
val XORI  = arithi [] "XORI"
val SLLI  = arithi [[shift]] "SLLI"
val SRLI  = arithi [[shift]] "SRLI"
val SRAI  = arithi [[shift]] "SRAI"
val SLLIW = arithi [[rv64]] "SLLIW"
val SRLIW = arithi [[rv64]] "SRLIW"
val SRAIW = arithi [[rv64]] "SRAIW"

val arithi = class_rd0 `(rd, imm)` []

val LUI   = arithi "LUI"
val AUIPC = arithi "AUIPC"

val arithr = class_rd0 `(rd, rs1, rs2)`

val ADD   = arithr [] "ADD"
val ADDW  = arithr [[rv64]] "ADDW"
val SUB   = arithr [] "SUB"
val SUBW  = arithr [[rv64]] "SUBW"
val SLT   = arithr [] "SLT"
val SLTU  = arithr [] "SLTU"
val AND   = arithr [] "AND"
val OR    = arithr [] "OR"
val XOR   = arithr [] "XOR"
val SLL   = arithr [] "SLL"
val SRL   = arithr [] "SRL"
val SRA   = arithr [] "SRA"
val SLLW  = arithr [[rv64]] "SLLW"
val SRLW  = arithr [[rv64]] "SRLW"
val SRAW  = arithr [[rv64]] "SRAW"

val MUL    = arithr [] "MUL"
val MULH   = arithr [] "MULH"
val MULHU  = arithr [] "MULHU"
val MULHSU = arithr [] "MULHSU"
val MULW   = arithr [[rv64]] "MULW"
val DIV    = arithr [] "DIV"
val REM    = arithr [] "REM"
val DIVU   = arithr [] "DIVU"
val REMU   = arithr [] "REMU"
val DIVW   = arithr [[rv64]] "DIVW"
val REMW   = arithr [[rv64]] "REMW"
val DIVUW  = arithr [[rv64]] "DIVUW"
val REMUW  = arithr [[rv64]] "REMUW"

val JAL  = class_rd0 `(rd, imm)`
  [[ialign_ok ``^s.c_PC ^s.procID + sw2sw (imm: word20) << 1``]] "JAL"
val JALR = class_rd0 `(rd, rs1, imm)`
  [[ialign_ok ``if rs1 = 0w then sw2sw (imm: word12) && 0xFFFFFFFFFFFFFFFEw
              else ^s.c_gpr ^s.procID rs1 + sw2sw imm && 0xFFFFFFFFFFFFFFFEw``]]
  "JALR"

val cbranch = class `(rs1, rs2, offs)`
  [[ialign_ok ``^s.c_PC ^s.procID + sw2sw (offs: word12) << 1``]]

val BEQ  = cbranch "BEQ"
val BNE  = cbranch "BNE"
val BLT  = cbranch "BLT"
val BLTU = cbranch "BLTU"
val BGE  = cbranch "BGE"
val BGEU = cbranch "BGEU"

(* Loads and stores carry the alignment of their address (H5), except for
   the byte accesses, which cannot be misaligned. *)

val load = class_rd0 `(rd, rs1, offs)`

val LD  = load [[rv64, aligned_d]] "LD"
val LW  = load [[aligned_w]] "LW"
val LH  = load [[aligned_h]] "LH"
val LB  = load [] "LB"
val LWU = load [[rv64, aligned_w]] "LWU"
val LHU = load [[aligned_h]] "LHU"
val LBU = load [] "LBU"

val store = class `(rs1, rs2, offs)`

val SD  = store [[rv64, aligned_d]] "SD"
val SW  = store [[aligned_w]] "SW"
val SH  = store [[aligned_h]] "SH"
val SB  = store [] "SB"

(* Atomics.  The aq and rl bits have no effect on a single hart.  An SC
   needs the PMP's write permission whether or not it succeeds, and its
   step theorem keeps the test of the reservation. *)

val amo = class_rd0 `(aq, rl, rd, rs1, rs2)`

val AMOSWAP_W = amo [[aligned_amo_w]] "AMOSWAP_W"
val AMOADD_W  = amo [[aligned_amo_w]] "AMOADD_W"
val AMOXOR_W  = amo [[aligned_amo_w]] "AMOXOR_W"
val AMOAND_W  = amo [[aligned_amo_w]] "AMOAND_W"
val AMOOR_W   = amo [[aligned_amo_w]] "AMOOR_W"
val AMOMIN_W  = amo [[aligned_amo_w]] "AMOMIN_W"
val AMOMAX_W  = amo [[aligned_amo_w]] "AMOMAX_W"
val AMOMINU_W = amo [[aligned_amo_w]] "AMOMINU_W"
val AMOMAXU_W = amo [[aligned_amo_w]] "AMOMAXU_W"
val AMOSWAP_D = amo [[aligned_amo_d]] "AMOSWAP_D"
val AMOADD_D  = amo [[aligned_amo_d]] "AMOADD_D"
val AMOXOR_D  = amo [[aligned_amo_d]] "AMOXOR_D"
val AMOAND_D  = amo [[aligned_amo_d]] "AMOAND_D"
val AMOOR_D   = amo [[aligned_amo_d]] "AMOOR_D"
val AMOMIN_D  = amo [[aligned_amo_d]] "AMOMIN_D"
val AMOMAX_D  = amo [[aligned_amo_d]] "AMOMAX_D"
val AMOMINU_D = amo [[aligned_amo_d]] "AMOMINU_D"
val AMOMAXU_D = amo [[aligned_amo_d]] "AMOMAXU_D"

val SC_W = amo [[aligned_amo_w]] "SC_W"
val SC_D = amo [[rv64, aligned_amo_d]] "SC_D"

val lr = class_rd0 `(aq, rl, rd, rs1)`

val LR_W = lr [[aligned_amo_w]] "LR_W"
val LR_D = lr [[rv64, aligned_amo_d]] "LR_D"

(* Floating-point loads and stores.  FLW and FLD write the FPR with
   writeFPRS and writeFPRD, which NaN-box a single and make mstatus.FS
   Dirty; FSW stores the low word of the FPR as it is (FPRS_raw). *)

val FLW = class `(rd, rs1, offs)` [[fp_on, aligned_w]] "FLW"
val FLD = class `(rd, rs1, offs)` [[fp_on, aligned_d]] "FLD"
val FSW = class `(rs1, rs2, offs)` [[fp_on, aligned_w]] "FSW"
val FSD = class `(rs1, rs2, offs)` [[fp_on, aligned_d]] "FSD"

(* Floating-point instructions.  Those with an rm field get two step
   theorems: one for a static rounding mode, and one, named _DYN, for the
   dynamic one, which has the legality of fcsr.frm as hypothesis
   (round_dynamic, or validRounding_dynamic for the exact conversions).  A
   single operand is read through its NaN-boxing test, and the fflags that
   the operation raises are accrued in fcsr (accrueFlags_update). *)

local
  val static = [utilsLib.STRIP_UNDISCH round_static]
  val dynamic = [utilsLib.STRIP_UNDISCH round_dynamic]
  val exact_static = [utilsLib.STRIP_UNDISCH validRounding_static]
  val exact_dynamic = [utilsLib.STRIP_UNDISCH validRounding_dynamic]
in
  fun fp_rnd args n =
    (class_with static "" args [[fp_on]] n,
     class_with dynamic "_DYN" args [[fp_on]] n)
  fun fp_exact args n =
    (class_with exact_static "" args [[fp_on]] n,
     class_with exact_dynamic "_DYN" args [[fp_on]] n)
  fun fp_rnd_rd0 args n =
    (class_with static "" args [[fp_on]] n,
     class_with static "" args [[rd0, fp_on]] n,
     class_with dynamic "_DYN" args [[fp_on]] n,
     class_with dynamic "_DYN" args [[rd0, fp_on]] n)
end

val fp = class `(rd, rs1, rs2)` [[fp_on]]
val fp_rd0 = class_rd0 `(rd, rs1, rs2)` [[fp_on]]
val fp1 = class `(rd, rs)` [[fp_on]]
val fp1_rd0 = class_rd0 `(rd, rs)` [[fp_on]]

val FADD_S   = fp_rnd `(rd, rs1, rs2, fprnd)` "FADD_S"
val FSUB_S   = fp_rnd `(rd, rs1, rs2, fprnd)` "FSUB_S"
val FMUL_S   = fp_rnd `(rd, rs1, rs2, fprnd)` "FMUL_S"
val FDIV_S   = fp_rnd `(rd, rs1, rs2, fprnd)` "FDIV_S"
val FSQRT_S  = fp_rnd `(rd, rs, fprnd)` "FSQRT_S"
val FMADD_S  = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FMADD_S"
val FMSUB_S  = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FMSUB_S"
val FNMADD_S = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FNMADD_S"
val FNMSUB_S = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FNMSUB_S"
val FMIN_S   = fp "FMIN_S"
val FMAX_S   = fp "FMAX_S"
val FSGNJ_S  = fp "FSGNJ_S"
val FSGNJN_S = fp "FSGNJN_S"
val FSGNJX_S = fp "FSGNJX_S"
val FEQ_S    = fp_rd0 "FEQ_S"
val FLT_S    = fp_rd0 "FLT_S"
val FLE_S    = fp_rd0 "FLE_S"
val FMV_X_S  = fp1_rd0 "FMV_X_S"
val FMV_S_X  = fp1 "FMV_S_X"
val FCLASS_S = fp1_rd0 "FCLASS_S"
val FCVT_S_W  = fp_rnd `(rd, rs, fprnd)` "FCVT_S_W"
val FCVT_S_WU = fp_rnd `(rd, rs, fprnd)` "FCVT_S_WU"
val FCVT_S_L  = fp_rnd `(rd, rs, fprnd)` "FCVT_S_L"
val FCVT_S_LU = fp_rnd `(rd, rs, fprnd)` "FCVT_S_LU"
val FCVT_W_S  = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_W_S"
val FCVT_WU_S = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_WU_S"
val FCVT_L_S  = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_L_S"
val FCVT_LU_S = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_LU_S"

val FADD_D   = fp_rnd `(rd, rs1, rs2, fprnd)` "FADD_D"
val FSUB_D   = fp_rnd `(rd, rs1, rs2, fprnd)` "FSUB_D"
val FMUL_D   = fp_rnd `(rd, rs1, rs2, fprnd)` "FMUL_D"
val FDIV_D   = fp_rnd `(rd, rs1, rs2, fprnd)` "FDIV_D"
val FSQRT_D  = fp_rnd `(rd, rs, fprnd)` "FSQRT_D"
val FMADD_D  = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FMADD_D"
val FMSUB_D  = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FMSUB_D"
val FNMADD_D = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FNMADD_D"
val FNMSUB_D = fp_rnd `(rd, rs1, rs2, rs3, fprnd)` "FNMSUB_D"
val FMIN_D   = fp "FMIN_D"
val FMAX_D   = fp "FMAX_D"
val FSGNJ_D  = fp "FSGNJ_D"
val FSGNJN_D = fp "FSGNJN_D"
val FSGNJX_D = fp "FSGNJX_D"
val FEQ_D    = fp_rd0 "FEQ_D"
val FLT_D    = fp_rd0 "FLT_D"
val FLE_D    = fp_rd0 "FLE_D"
val FMV_X_D  = fp1_rd0 "FMV_X_D"
val FMV_D_X  = fp1 "FMV_D_X"
val FCLASS_D = fp1_rd0 "FCLASS_D"
val FCVT_D_W  = fp_exact `(rd, rs, fprnd)` "FCVT_D_W"
val FCVT_D_WU = fp_exact `(rd, rs, fprnd)` "FCVT_D_WU"
val FCVT_D_L  = fp_rnd `(rd, rs, fprnd)` "FCVT_D_L"
val FCVT_D_LU = fp_rnd `(rd, rs, fprnd)` "FCVT_D_LU"
val FCVT_W_D  = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_W_D"
val FCVT_WU_D = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_WU_D"
val FCVT_L_D  = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_L_D"
val FCVT_LU_D = fp_rnd_rd0 `(rd, rs, fprnd)` "FCVT_LU_D"
val FCVT_S_D  = fp_rnd `(rd, rs, fprnd)` "FCVT_S_D"
val FCVT_D_S  = fp_exact `(rd, rs, fprnd)` "FCVT_D_S"

(* WFI and SFENCE.VMA do nothing in M-mode.  FENCE and FENCE.I do nothing
   at all: Run rewrites them to the identity, so they need no theorem. *)

val WFI = class [] [] "WFI"
val SFENCE_VMA = class `(rs1, rs2)` [] "SFENCE_VMA"

(* ECALL and EBREAK raise their exception, which NextRISCV takes
   (NextRISCV_trap): ECALL the environment call from the current privilege,
   M-mode by H1 (P §3.3.1 p.60-61), and EBREAK a breakpoint, with its own
   address as the trap value (P §3.1.16 p.52, [D43]).  MRET is legal in
   M-mode (H1) and leaves the return to NextRISCV (NextRISCV_mret). *)

local
  val trap_thms =
    [signalEnvCall_def, signalException_def, signalAddressException_def,
     setTrap_def, write'NextFetch_def]
in
  val ECALL = class_with trap_thms "" [] [] "ECALL"
  val EBREAK = class_with trap_thms "" [] [] "EBREAK"
  val MRET = class_with trap_thms "" [] [] "MRET"
end

(* ------------------------------------------------------------------------
   CSR instructions (doc/design-privileged.md §3.2)

   The step theorems of the six Zicsr instructions below are for any CSR
   number csr: the CSR is read with CSRMap csr and written with writeCSR,
   both left as they are, and riscv_stepLib evaluates them for the CSR
   number of the instruction.  They assume what checkCSROp checks in M-mode
   (H1, by which every CSR is accessible: privLevel Machine = 3w), which
   riscv_stepLib also decides for the CSR number: that the CSR exists
   (is_CSR_defined), for a write that it is not read-only (bits 11:10 of
   its number are not 3), and the further conditions of the CSR
   (check_CSR_conditions: mstatus.FS <> Off for fflags, frm and fcsr).
   CSRRW and CSRRWI always write the CSR; CSRRS, CSRRC, CSRRSI and CSRRCI
   write it unless their rs1 or uimm field is 0, which the theorems named
   _READ assume (U §4.2.1 p.62-63, Table 21).  The _NOP theorems have
   rd = 0, as for the other instructions.
   ------------------------------------------------------------------------ *)

(* For the CSR step theorems, which riscv_stepLib evaluates for one CSR
   number: rewrites that keep a CSR value a word expression.  A register
   type of the spec (mstatus, misa, mie, mip, mcause, fcsr) keeps every bit
   of the word that it is made from, so reading back a value written with
   rec' gives the word. *)
Theorem reg_rec_id:
  (reg'FPCSR (rec'FPCSR x1) = x1) /\ (reg'mstatus (rec'mstatus x2) = x2) /\
  (reg'misa (rec'misa x3) = x3) /\ (reg'mie (rec'mie x4) = x4) /\
  (reg'mip (rec'mip x5) = x5) /\ (reg'mcause (rec'mcause x6) = x6)
Proof
  simp [reg'FPCSR_def, rec'FPCSR_def, reg'mstatus_def, rec'mstatus_def,
        reg'misa_def, rec'misa_def, reg'mie_def, rec'mie_def, reg'mip_def,
        rec'mip_def, reg'mcause_def, rec'mcause_def]
  \\ blastLib.BBLAST_TAC
QED

(* The word of mip with one of the bits set that read_mip sets from the
   platform and the CLINT (for read_mip_eval). *)
Theorem reg'mip_updates:
  (reg'mip (m with MEIP := b) =
   reg'mip m && ~0x800w || (if b then 0x800w else 0w)) /\
  (reg'mip (m with SEIP := b) =
   reg'mip m && ~0x200w || (if b then 0x200w else 0w)) /\
  (reg'mip (m with MTIP := b) =
   reg'mip m && ~0x80w || (if b then 0x80w else 0w)) /\
  (reg'mip (m with MSIP := b) =
   reg'mip m && ~0x8w || (if b then 0x8w else 0w))
Proof
  Cases_on `m` \\ Cases_on `b`
  \\ simp_tac (srw_ss()) (reg'mip_def :: TypeBase.updates_of ``:mip``)
  \\ blastLib.BBLAST_TAC
QED

(* mip as read (P §3.1.9 p.43-45, design-privileged.md §4.1.3): the stored
   SSIP and STIP, MSIP and MTIP from the CLINT, SEIP as stored or from the
   platform, and MEIP from the platform. *)
Theorem read_mip_eval:
  read_mip () s =
  reg'mip (s.c_MCSR s.procID).mip && 0x22w ||
  (if msip s.procID s then 0x8w else 0w) ||
  (if mtimecmp s.procID s <=+ mtime () s then 0x80w else 0w) ||
  (if (s.c_MCSR s.procID).mip.SEIP \/ s.c_extSEIP s.procID then 0x200w
   else 0w) ||
  (if s.c_extMEIP s.procID then 0x800w else 0w)
Proof
  simp [read_mip_def, MCSR_def, reg'mip_updates, reg_rec_id]
  \\ Cases_on `(s.c_MCSR s.procID).mip`
  \\ simp [reg'mip_def]
  \\ rw []
  \\ blastLib.BBLAST_TAC
QED

(* A write of fflags replaces bits 4:0 of fcsr. *)
Theorem fflags_insert:
  bit_field_insert 4 0 (x: word5) (w: word32) = w && 0xFFFFFFE0w || w2w x
Proof
  simp [wordsTheory.bit_field_insert_def] \\ blastLib.BBLAST_TAC
QED

(* The address of mtimecmp is a multiple of 8, so the double-word of MEM
   that holds it starts at the address itself. *)
Theorem mtimecmp_address:
  w2w ((63 >< 3) (0x2004000w + 8w * w2w (h: word8) : word64) : 61 word) << 3 =
  0x2004000w + 8w * w2w h : word64
Proof
  blastLib.BBLAST_TAC
QED

(* A read of a CSR that exists leaves the state as it is: CSRMap raises an
   exception only at an address that is_CSR_defined rejects. *)
val CSR_defined = uprove
  `is_CSR_defined csr ==> (CSR csr s = (FST (CSRMap csr s), s))`
  (
  strip_tac
  \\ `SND (CSRMap csr s) = s`
     by (pop_assum mp_tac
         \\ simp_tac std_ss [CSRMap_def, boolTheory.literal_case_DEF]
         \\ rpt (IF_CASES_TAC \\ simp_tac std_ss [])
         \\ fs [is_CSR_defined_def, is_mhpm_CSR_def]
         \\ blastLib.FULL_BBLAST_TAC)
  \\ simp [CSR_def]
  \\ metis_tac [pairTheory.PAIR]
  )

(* Every CSR is accessible in M-mode, whose level is the highest. *)
val privLevel_Machine_hs = blastLib.BBLAST_PROVE ``(3w: word2) >=+ pr``

local
  val defined = ``is_CSR_defined csr``
  val writable = ``(11 >< 10) (csr: word12) <> 3w``
  val conditions = ``check_CSR_conditions (csr, Machine) ^s``
  val csr_thms =
    [accessCSR_def, checkCSROp_def, check_CSR_access_def, csrRW_def,
     csrPR_def, privLevel_def, privLevel_Machine_hs, CSR_defined] @
    utilsLib.datatype_rewrites true "riscv" ["csrOp", "accessType"]
  val csr_class = class_gen ["CSRMap", "writeCSR"] csr_thms
  (* CSRRW and CSRRWI: always a write *)
  fun write_class args n =
    (csr_class "" args [[defined, writable, conditions]] n,
     csr_class "" args [[rd0, defined, writable, conditions]] n)
  (* CSRRS, CSRRC, CSRRSI and CSRRCI: a write unless the field f is 0 *)
  fun set_class args f n =
    let
      val f0 = ``^f = 0w: word5``
      val f1 = ``^f <> 0w: word5``
    in
      (csr_class "" args [[f1, defined, writable, conditions]] n,
       csr_class "" args [[rd0, f1, defined, writable, conditions]] n,
       csr_class "_READ" args [[f0, defined, conditions]] n,
       csr_class "_READ" args [[rd0, f0, defined, conditions]] n)
    end
in
  val CSRRW = write_class `(rd, rs1, csr)` "CSRRW"
  val CSRRS = set_class `(rd, rs1, csr)` ``rs1: word5`` "CSRRS"
  val CSRRC = set_class `(rd, rs1, csr)` ``rs1: word5`` "CSRRC"
  val CSRRWI = write_class `(rd, uimm, csr)` "CSRRWI"
  val CSRRSI = set_class `(rd, uimm, csr)` ``uimm: word5`` "CSRRSI"
  val CSRRCI = set_class `(rd, uimm, csr)` ``uimm: word5`` "CSRRCI"
end

(* ------------------------------------------------------------------------ *)

val () = Theory.delete_const "select";
