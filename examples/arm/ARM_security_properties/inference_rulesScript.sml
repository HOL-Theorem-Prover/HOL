open HolKernel boolLib bossLib Parse;
open MMU_SetupTheory MMUTheory arm_opsemTheory arm_seq_monadTheory arm_coretypesTheory arm_stepTheory;
open tacticsLib;

val _ =  new_theory("inference_rules");
val _ = ParseExtras.temp_loose_equality()


val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val comb_def = Define `comb invr1 invr2 invr3 = (!s. invr3 s = (invr1 s \/ invr2 s))`;
val assert_mode_def = Define `assert_mode k s = (ARM_MODE s = k)`;


(* =============     Untouched   ==========================*)
(* smc mode is not involved yet, also RName_LRmon,RName_SPmon*)

val untouched_def = Define `untouched id state1 state2 =
(state1.coprocessors  = state2.coprocessors)

/\
(state1.information =
 state2.information)

/\

 (! a.
 (((id <> guest1) /\ (id<>guest2))                             ==>
        ((state1.memory a) = (state2.memory a)))
 /\
 (((id = guest1) /\ ((a >+ (* UNSIGNED *) guest1_max_adr) \/ (a <+ (* UNSIGNED *) guest1_min_adr))) ==>
((state1.memory a) = (state2.memory a)))
 /\
 (((id = guest2) /\ ((a >+ (* UNSIGNED *) guest2_max_adr) \/ (a <+ (* UNSIGNED *) guest2_min_adr))) ==>
((state1.memory a) = (state2.memory a))))

/\

((state1.psrs (0, CPSR)).F = (state2.psrs (0, CPSR)).F)

/\
let user_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC} in
let irq_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC; RName_SPirq; RName_LRirq} in
let fiq_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC; RName_8fiq; RName_9fiq;
                       RName_10fiq; RName_11fiq; RName_12fiq; RName_SPfiq; RName_LRfiq} in
let abort_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC; RName_SPabt; RName_LRabt} in
let svc_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC; RName_SPsvc; RName_LRsvc} in
let und_regs = {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC; RName_SPund; RName_LRund} in


(((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 16w)) ==>
   ((!reg .  (reg NOTIN  user_regs)
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR) ==> (state1.psrs (0, psr) = state2.psrs (0, psr))))
/\
((state1.psrs (0, CPSR)).I = (state2.psrs (0, CPSR)).I)
))

/\
((((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 17w))
\/
((ARM_MODE state1 = 17w) /\
 (ARM_MODE state2 = 17w))) ==>
   ((!reg .  ((reg NOTIN  user_regs) /\ (reg NOTIN  fiq_regs))
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR)  /\ (psr <> SPSR_fiq)) ==> (state1.psrs (0, psr) = state2.psrs (0, psr))))
)

/\
((((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 18w))
\/
((ARM_MODE state1 = 18w) /\
 (ARM_MODE state2 = 18w))) ==>
   ((!reg .  ((reg NOTIN  user_regs) /\ (reg NOTIN  irq_regs))
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR)  /\ (psr <> SPSR_irq)) ==> (state1.psrs (0, psr) = state2.psrs (0, psr)))))
/\

(*this is also the mode of reset, check again*)
((((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 19w))
\/
((ARM_MODE state1 = 19w) /\
 (ARM_MODE state2 = 19w))) ==>
   ((!reg .  ((reg NOTIN  user_regs) /\ (reg NOTIN  svc_regs))
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR)  /\ (psr <> SPSR_svc)) ==> (state1.psrs (0, psr) = state2.psrs (0, psr)))))
/\

((((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 23w))
\/
((ARM_MODE state1 = 23w) /\
 (ARM_MODE state2 = 23w))) ==>
   ((!reg .  ((reg NOTIN  user_regs) /\ (reg NOTIN  abort_regs))
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR)  /\ (psr <> SPSR_abt)) ==> (state1.psrs (0, psr) = state2.psrs (0, psr)))))
/\

((((ARM_MODE state1 = 16w) /\
 (ARM_MODE state2 = 27w))
\/
((ARM_MODE state1 = 27w) /\
 (ARM_MODE state2 = 27w))) ==>
   ((!reg .  ((reg NOTIN  user_regs) /\ (reg NOTIN  und_regs))
          ==> (state1.registers (0, reg) = state2.registers (0, reg)))
/\
(!psr . ((psr <> CPSR)  /\ (psr <> SPSR_und)) ==> (state1.psrs (0, psr) = state2.psrs (0, psr)))))
`;

(* only for arm_next
val priv_mode_similar_def =
    Define `priv_mode_similar (g:bool[32]) state1 state2 =
    (ARM_MODE state2 <> 16w) ==>
    (let (lr_reg,spsr) = case (ARM_MODE state2) of
                17w -> (RName_LRfiq,SPSR_fiq)
             || 18w -> (RName_LRirq,SPSR_irq)
             || 19w -> (RName_LRsvc,SPSR_svc)
             || 22w -> (RName_LRmon,SPSR_mon)
             || 23w -> (RName_LRabt,SPSR_abt)
             || 27w -> (RName_LRund,SPSR_und)
             || _   -> (RName_LRusr,CPSR)
    in
        (state1.registers(0,lr_reg) = state2.registers(0,lr_reg))
                /\
         (state1.psrs(0,spsr) = state2.psrs(0,spsr)))

        `;*)


val get_spsr_by_mode_def =
    Define `get_spsr_by_mode (mode:bool[5]) =
        case (mode) of
               17w => SPSR_fiq
             | 18w => SPSR_irq
             | 19w => SPSR_svc
             | 22w => SPSR_mon
             | 23w => SPSR_abt
             | 27w => SPSR_und
             |  _  => CPSR`;

val get_lr_by_mode_def =
    Define `get_lr_by_mode (mode:bool[5]) =
        case (mode) of
               17w => RName_LRfiq
             | 18w => RName_LRirq
             | 19w => RName_LRsvc
             | 22w => RName_LRmon
             | 23w => RName_LRabt
             | 27w => RName_LRund
             |  _  => RName_LRusr `;

val priv_mode_similar_def =
    Define `priv_mode_similar (g:bool[32]) state1 state2 =
    (ARM_MODE state2 <> 16w) ==>
    (let (lr_reg,spsr) = (get_lr_by_mode(ARM_MODE state2) ,
get_spsr_by_mode(ARM_MODE state2))
    in
        (state1.registers(0,lr_reg) = state2.registers(0,lr_reg))
                /\
         (state1.psrs(0,spsr) = state2.psrs(0,spsr)))

        `;


val untouched_trans = store_thm (
    "untouched_trans",
    ``!g st1 st2 st3 .
      (untouched g st1 st2 ) ==> (untouched g st2 st3 )
      ==>  ((ARM_MODE st3 = ARM_MODE st2) \/
            (ARM_MODE st1 = ARM_MODE st2)) ==>
      (untouched g st1 st3 )``,
    RW_TAC (srw_ss()) [untouched_def]
    THEN FULL_SIMP_TAC (let_ss) []
    THEN RW_TAC (srw_ss()) []
);

val untouched_memory_eq_lem = store_thm(
    "untouched_memory_eq_lem",
    ``!s1 s2 g . (untouched g s1 s2 ) ==>
                (!addr. (addr <+ (*UNSIGNED*) guest1_min_adr (*ADR*)) ==> (s1.memory addr = s2.memory addr))``,
    REPEAT STRIP_TAC
       THEN Cases_on `(g<>guest1) /\ (g<>guest2)`
       THENL [ALL_TAC, IMP_RES_TAC address_trans (*ADR*)]
       THEN FULL_SIMP_TAC (let_ss) [untouched_def]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]);


val untouched_permissions_lem = store_thm(
    "untouched_permissions_lem",
    ``!s1 s2 g priv .
         (mmu_requirements s1 g) ==>
         (untouched g s1 s2 )
     ==> (!addr isw c1 c3.
          (permitted_byte addr isw c1 s1.coprocessors.state.cp15.C2 c3 priv s1.memory
         = permitted_byte addr isw c1 s1.coprocessors.state.cp15.C2 c3 priv s2.memory))``,
    REPEAT STRIP_TAC
       THEN IMP_RES_TAC untouched_memory_eq_lem
       THEN FULL_SIMP_TAC (srw_ss()) [permitted_byte_def]
       THEN UNDISCH_TAC ``mmu_requirements s1 g``
       THEN PURE_ONCE_REWRITE_TAC [mmu_requirements_def]
       THEN STRIP_TAC
       THEN Cases_on `permitted_byte addr F s1.coprocessors.state.cp15.C1 s1.coprocessors.state.cp15.C2 s1.coprocessors.state.cp15.C3 F s1.memory`
       THEN Cases_on `r`
       THEN PAT_X_ASSUM (``!A1 A2 A3 A4 A5. (B ==> C)``) (fn th => (MP_TAC (SPECL [``addr:word32``, ``F``,``q:bool``, ``q':bool``, ``r':string``] th)))
       THEN RW_TAC (srw_ss()) [read_mem32_def]
       THEN `content_of_sd = content_of_sd'` by
            (UNABBREV_ALL_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF, read_mem32_def]
                THEN IMP_RES_TAC (blastLib.BBLAST_PROVE ``!(addr:word32). ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) >=+ (*UNSIGNED*) 0w) ==> ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) <+ (*UNSIGNED*) (guest1_min_adr:word32) (*ADR*))  ==> ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 16383w <+ (*UNSIGNED*) guest1_min_adr (*ADR*)) ==>
     (((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(addr >>> (*UNSIGNED*) 20)      <+ (*UNSIGNED*) guest1_min_adr (*ADR*))  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(addr >>> (*UNSIGNED*) 20) + 1w <+ (*UNSIGNED*) guest1_min_adr (*ADR*))  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(addr >>> (*UNSIGNED*) 20) + 2w <+ (*UNSIGNED*)guest1_min_adr (*ADR*))  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(addr >>> (*UNSIGNED*) 20) + 3w <+ (*UNSIGNED*) guest1_min_adr (*ADR*)) )``)
                THEN METIS_TAC [])
       THEN UNABBREV_ALL_TAC
       THEN METIS_TAC []);


val untouched_permissions_lem2 = store_thm(
    "untouched_permissions_lem2",
    ``!s1 s2 g priv .
         (mmu_requirements s1 g) ==>
         (untouched g s1 s2 )
     ==> (!addr isw.
          (permitted_byte addr isw s1.coprocessors.state.cp15.C1 s1.coprocessors.state.cp15.C2 s1.coprocessors.state.cp15.C3 priv s1.memory
         = permitted_byte addr isw s2.coprocessors.state.cp15.C1 s2.coprocessors.state.cp15.C2 s2.coprocessors.state.cp15.C3 priv s2.memory))``,
   REPEAT STRIP_TAC
       THEN IMP_RES_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``] untouched_permissions_lem)
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]
       THEN METIS_TAC []);


val untouched_mmu_setup_lem = store_thm(
    "untouched_mmu_setup_lem",
    ``!s1 s2 g .
          (mmu_requirements s1 g) ==>
          (untouched g s1 s2 )
        ==>
          (mmu_requirements s2 g)``,
    REPEAT STRIP_TAC
       THEN IMP_RES_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``] untouched_permissions_lem)
       THEN UNDISCH_TAC ``mmu_requirements s1 g``
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]
       THEN PURE_ONCE_REWRITE_TAC [mmu_requirements_def]
       THEN METIS_TAC []);


val trivially_untouched_mmu_setup_lem = store_thm(
    "trivially_untouched_mmu_setup_lem",
    ``!s t gst. (s.coprocessors = t.coprocessors) ==>
                (s.memory = t.memory)
       ==>
      (mmu_requirements s gst = mmu_requirements t gst)``,
    RW_TAC (srw_ss()) [mmu_requirements_def]);


val trivially_untouched_av_lem = store_thm(
    "trivially_untouched_av_lem",
    ``!s t gst. (mmu_requirements s gst)          ==>
                (s.coprocessors = t.coprocessors) ==>
                (s.memory = t.memory)             ==>
                (s.accesses = t.accesses)
       ==> (access_violation s = access_violation t)``,
    REPEAT STRIP_TAC
       THEN `mmu_requirements t gst` by IMP_RES_TAC trivially_untouched_mmu_setup_lem
       THEN IMP_RES_TAC access_violation_req
       THEN RW_TAC (srw_ss()) [access_violation_pure_def]);


val trivially_untouched_mmu_setup_lem2 = store_thm(
    "trivially_untouched_mmu_setup_lem2",
    ``!s t gst. (s.coprocessors.state.cp15.C1 = t.coprocessors.state.cp15.C1)  ==>
                (s.coprocessors.state.cp15.C2 = t.coprocessors.state.cp15.C2)  ==>
                (s.coprocessors.state.cp15.C3 = t.coprocessors.state.cp15.C3)  ==>
                (s.memory = t.memory)
       ==>
      (mmu_requirements s gst = mmu_requirements t gst)``,
    RW_TAC (srw_ss()) [mmu_requirements_def]);





val trivially_untouched_av_lem2 = store_thm(
    "trivially_untouched_av_lem2",
    ``!s t gst. (mmu_requirements s gst)                                       ==>
                (s.coprocessors.state.cp15.C1 = t.coprocessors.state.cp15.C1)  ==>
                (s.coprocessors.state.cp15.C2 = t.coprocessors.state.cp15.C2)  ==>
                (s.coprocessors.state.cp15.C3 = t.coprocessors.state.cp15.C3)  ==>
                (s.memory = t.memory)                                          ==>
                (s.accesses = t.accesses)
       ==> (access_violation s = access_violation t)``,
    REPEAT STRIP_TAC
       THEN `mmu_requirements t gst` by IMP_RES_TAC trivially_untouched_mmu_setup_lem2
       THEN IMP_RES_TAC access_violation_req
       THEN RW_TAC (srw_ss()) [access_violation_pure_def]);



(* =============   Similar    ==========================*)

val equal_user_register_def = Define `equal_user_register s t  =
(! reg.  reg IN  {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC}
             ==> (s.registers (0, reg) = t.registers (0, reg)))`;



val similar_def = Define `similar  gst s1 s2 =
(! addr.
 (((addr <=+ (*UNSIGNED*)  guest1_max_adr) /\ (addr >=+ (*UNSIGNED*) guest1_min_adr) /\ (gst = guest1)) ==>
        ((s1.memory addr) = (s2.memory addr)))
   /\
 (((addr <=+ (*UNSIGNED*) guest2_max_adr) /\ (addr >=+ (*UNSIGNED*) guest2_min_adr) /\ (gst = guest2)) ==>
        ((s1.memory addr) = (s2.memory addr))))                       /\
((s1.psrs (0,CPSR)= s2.psrs (0,CPSR)))           /\
(equal_user_register s1 s2)                                        /\
(s1.coprocessors.state = s2.coprocessors.state)  /\

(s1.interrupt_wait 0 = s2.interrupt_wait 0)        /\

(access_violation s1 = access_violation s2)   /\
(s1.information = s2.information)                                   /\

(* to be checked*)
(s1.monitors = s2.monitors)
                                    /\
(s1.event_register = s2.event_register)

`;


val similar_refl = store_thm(
    "similar_refl",
    ``!gst s  . similar  gst s s``,
    RW_TAC (srw_ss()) [similar_def, equal_user_register_def]);


(*********************** preserve ****************************)

val trans_fun_def = Define `trans_fun uf =
!g st1 st2 st3 .
      (uf g st1 st2) ==>
      (uf g st2 st3)
      ==>  (uf g st1 st3)`;


val preserve_relation_mmu_def =
Define `preserve_relation_mmu comp invr1 invr2 f y =
    !g s1 s2 .
    mmu_requirements s1 g    ==>
    mmu_requirements s2 g    ==>
    similar  g s1 s2         ==>
    (y  g s1 s2)            ==>
    invr1 s1                 ==>
    invr1 s2                 ==>
    ((?a s1' s2'.((comp s1 = ValueState a s1') /\  (comp s2 = ValueState a s2') /\
                  (untouched g s1 s1' ) /\
                  (untouched g s2 s2' ) /\
                  (f  g s1 s1') /\
                  (f  g s2 s2') /\
                  (y  g s1' s2') /\
                  (invr2 s1') /\
                  (invr2 s2') /\
                  (similar  g s1' s2')))
\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;



val preserve_relation_mmu_abs_def = Define `preserve_relation_mmu_abs  comp invr1 invr2 f y =
    !c g s1 s2 .
    mmu_requirements s1 g    ==>
    mmu_requirements s2 g    ==>
    similar  g s1 s2          ==>
    (y  g s1 s2)            ==>
    invr1 s1   ==>
    invr1 s2   ==>
  ((?a s1' s2'.((comp c s1 = ValueState a s1') /\  (comp c s2 = ValueState a s2') /\
                     (untouched g s1 s1' )   /\
                     (untouched g s2 s2' )   /\
                     (f  g s1 s1') /\
                     (f  g s2 s2') /\
                     (y  g s1' s2') /\
                     (invr2 s1') /\
                     (invr2 s2') /\
                     (similar  g s1' s2')))
\/   (? e. (comp c s1 = Error e) /\ (comp c s2 = Error e)))`;

val comb_rel_lem = store_thm (
    "comb_rel_lem",
    ``!i1 i2 i3 s. (comb i1 i2 i3)
       ==> ((i1 s) ==> (i3 s)) /\ ((i2 s) ==> (i3 s))``,
    RW_TAC (srw_ss()) [comb_def]);

val seqT_preserves_relation_up_proof =
  (RW_TAC (srw_ss()) [arm_seq_monadTheory.seqT_def,arm_seq_monadTheory.constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def,trans_fun_def])
    THEN (UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THENL [UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN METIS_TAC [untouched_trans, comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def,comb_def]
THEN Cases_on `f2 a b`
THEN Cases_on `f2 a' b'`
(* THEN *)
(* SPEC_ASSUM_TAC (``∀(c:'a) (s1:arm_state) (s2:arm_state) (x:'b). X ==> Y``, [``a:'a``]) *)
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
THEN
(TRY (PAT_X_ASSUM `` ∀g st1 st2 st3. X`` (fn th => ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s1:arm_state``, ``b:arm_state``, ``b'':arm_state``] th) THEN ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s2:arm_state``, ``b':arm_state``, ``b''':arm_state``] th))))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []))
THEN METIS_TAC [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []];

val seqT_preserves_relation_up1_thm =
    store_thm ("seqT_preserves_relation_up1_thm",
    ``! f1 f2 k k' invr23  uf uy.
          (comb  (assert_mode k) (assert_mode k') invr23) ==>
          (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k) (assert_mode k') uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) invr23 uf uy)
``,
   seqT_preserves_relation_up_proof);



val seqT_preserves_relation_up2_thm =
    store_thm ("seqT_preserves_relation_up2_thm",
    ``! f1 f2 k k'  uf uy.
          (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k') uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k') (assert_mode k') uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) (assert_mode k') uf uy)
``,
seqT_preserves_relation_up_proof  );


val seqT_preserves_relation_uc_thm =
    store_thm ("seqT_preserves_relation_uc_thm",
    ``! f1 f2 k k' comb_inv  uf uy.
          (comb  (assert_mode k) (assert_mode k') comb_inv) ==>
          (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k) (comb_inv) uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) comb_inv uf uy)
``,
    (RW_TAC (srw_ss()) [arm_seq_monadTheory.seqT_def,arm_seq_monadTheory.constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def,trans_fun_def])
    THEN (UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THENL [UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN METIS_TAC [untouched_trans, comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def,comb_def]
THEN Cases_on `f2 a b`
THEN Cases_on `f2 a' b'`
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
THEN
(TRY (PAT_X_ASSUM `` ∀g st1 st2 st3. X`` (fn th => ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s1:arm_state``, ``b:arm_state``, ``b'':arm_state``] th) THEN ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s2:arm_state``, ``b':arm_state``, ``b''':arm_state``] th))))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [])),
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []]);


val seqT_preserves_relation_uu_thm =
    store_thm ("seqT_preserves_relation_uu_thm",
    ``! f1 f2 k  uf uy.
          (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k) (assert_mode k) uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) (assert_mode k) uf uy)
``,
               (RW_TAC (srw_ss()) [arm_seq_monadTheory.seqT_def,arm_seq_monadTheory.constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def,trans_fun_def])
                   THEN (UNDISCH_ALL_TAC
                             THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
                   THENL [UNDISCH_ALL_TAC
                              THEN RW_TAC (srw_ss()) []
                              THEN FULL_SIMP_TAC (srw_ss()) []
                              THEN RES_TAC
                              THEN IMP_RES_TAC untouched_trans
                              THEN FULL_SIMP_TAC (srw_ss()) []
                              THEN METIS_TAC [untouched_trans, comb_rel_lem],
                          RW_TAC (srw_ss()) []
                                 THEN RES_TAC
                                 THEN RW_TAC (srw_ss()) []
                                 THEN FULL_SIMP_TAC (srw_ss()) []
                                 THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
                                 THEN FULL_SIMP_TAC (srw_ss()) [],
                          RW_TAC (srw_ss()) []
                                 THEN Cases_on `assert_mode k s2`
                                 THEN RES_TAC
                                 THEN FULL_SIMP_TAC (srw_ss()) []
                                 THEN FULL_SIMP_TAC (srw_ss()) []
                                 THEN FULL_SIMP_TAC (srw_ss()) [],
                          RW_TAC (srw_ss()) []
                                 THEN RES_TAC
                                 THEN RW_TAC (srw_ss()) []
                                 THEN FULL_SIMP_TAC (srw_ss()) []
                                 THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
                                 THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def,comb_def,trans_fun_def]
THEN Cases_on `f2 a b`
THEN Cases_on `f2 a' b'`
THEN
SPEC_ASSUM_TAC (``∀(c:'a) (s1:arm_state) (s2:arm_state) (x:'b). X ==> Y``, [``a:'a``])
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [])),
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []]);


val reflexive_comp_def = Define `reflexive_comp  f invr =
                       ! s g. (invr s) ==> f g s s`;


val condT_preserves_relation_thm = store_thm("condT_preserves_relation_thm",
``! b f invr1:(arm_state -> bool)  uf uy.
          (reflexive_comp  uf invr1) ==>
          (preserve_relation_mmu  f invr1 invr1 uf uy)  ==>
          (preserve_relation_mmu  (condT b f ) invr1 invr1 uf uy)``,
(RW_TAC (srw_ss()) [preserve_relation_mmu_def,condT_def,similar_def,constT_def,untouched_def,reflexive_comp_def] )
THEN (RW_TAC (srw_ss()) [] ));

val first_abs_lemma = store_thm ("first_abs_lemma",
``(!f g i1 i2  uf uy. (f=g) ==> ((preserve_relation_mmu  f i1 i2 uf uy) =
                                (preserve_relation_mmu  g i1 i2 uf uy)))``,
 RW_TAC (srw_ss()) []);


val second_abs_lemma = store_thm ("second_abs_lemma",
``! f i1 i2 uf uy. (! y. preserve_relation_mmu  (f y) i1 i2 uf uy) =
                       preserve_relation_mmu_abs  f i1 i2 uf uy``,
 RW_TAC (srw_ss()) [preserve_relation_mmu_def,preserve_relation_mmu_abs_def]);


val constT_preserves_relation_thm = store_thm(
    "constT_preserves_relation_thm",
    ``!invr:(arm_state->bool) x  uf uy.  (reflexive_comp  uf invr) ==>
                              preserve_relation_mmu  (constT x) invr invr uf uy``,
    RW_TAC (srw_ss()) [constT_def, preserve_relation_mmu_def, untouched_def, similar_def,reflexive_comp_def] THEN
RW_TAC (srw_ss()) [] );


val parT_alternative_thm = store_thm(
    "parT_alternative_thm",
    ``!(f1:'a M) (f2:'b M) s. ((f1 ||| f2) s ) = (case f1 s of ValueState x t =>
      if access_violation t then ValueState (ARB:'a#'b) t else (f2 >>= (\y. constT (x,y))) t | Error e => Error e)``,
    RW_TAC (srw_ss()) [arm_seq_monadTheory.parT_def, arm_seq_monadTheory.constT_def, arm_seq_monadTheory.seqT_def]);

val parT_latter_part_hlem = store_thm (
    "parT_latter_part_hlem",
    ``!f2 i2 i3 (x:'a) uf uy. (preserve_relation_mmu  f2 i2 i3 uf uy) ==>
                                      preserve_relation_mmu (f2 >>= (λy. constT (x,y))) i2 i3 uf uy``,
    REPEAT STRIP_TAC
        THEN ASSUME_TAC (SPEC ``i3:arm_state->bool`` constT_preserves_relation_thm)
        THEN UNDISCH_ALL_TAC
        THEN RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def]
        THEN (UNDISCH_ALL_TAC THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
        THEN FIRST_PROVE [
                          RW_TAC (srw_ss()) []
                             THEN Cases_on `i2 s2`
                             THEN RES_TAC
                             THEN (NTAC 3 (FULL_SIMP_TAC (srw_ss()) [])),
                          RW_TAC (srw_ss()) []
                             THEN RES_TAC
                             THEN RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
                             THEN FULL_SIMP_TAC (srw_ss()) [],
                          RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN Cases_on `f2 s1`
                             THEN Cases_on `f2 s2`
                             THEN (NTAC 2 (RES_TAC
                                              THEN IMP_RES_TAC untouched_trans
                                              THEN FULL_SIMP_TAC (srw_ss()) []
                                              THEN IMP_RES_TAC untouched_mmu_setup_lem
                                              THEN UNDISCH_ALL_TAC
                                              THEN RW_TAC (srw_ss()) []
                                              THEN FULL_SIMP_TAC (srw_ss()) []))
                                              THEN METIS_TAC []]);

val parT_preserves_relation_up_thm = store_thm("parT_preserves_relation_up_thm",
    `` ! f1 f2 k k' invr23  uf uy.
          (trans_fun uf) ==> (comb  (assert_mode k) (assert_mode k') invr23)     ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu  f2 (assert_mode k) (assert_mode k') uf uy) ==>
               (preserve_relation_mmu  (parT f1 f2) (assert_mode k) invr23 uf uy) ``,
     REPEAT STRIP_TAC
        THEN IMP_RES_TAC parT_latter_part_hlem
        THEN WEAKEN_TAC is_forall
        THEN THROW_ONE_AWAY_TAC ``preserve_relation_mmu (*II*) f2  (assert_mode k) (assert_mode k') uf uy``
        THEN UNDISCH_ALL_TAC
        THEN RW_TAC (srw_ss()) [parT_alternative_thm, preserve_relation_mmu_def,trans_fun_def]
        THEN UNDISCH_ALL_TAC
        THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [comb_def])
        THEN FIRST_PROVE [
                          RW_TAC (srw_ss()) []
                             THEN Cases_on `(assert_mode k)  s2`
                             THEN RES_TAC
                             THEN (NTAC 3 (FULL_SIMP_TAC (srw_ss()) [])),
                          RW_TAC (srw_ss()) []
                             THEN RES_TAC
                             THEN RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
                             THEN FULL_SIMP_TAC (srw_ss()) [],
                          ASSERT_ASSUM_TAC ``access_violation b``
                             THEN UNDISCH_ALL_TAC
                             THEN RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN RES_TAC
                             THEN IMP_RES_TAC untouched_trans
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN METIS_TAC [untouched_trans, comb_rel_lem],
                         RW_TAC (srw_ss()) [assert_mode_def]
                             THEN Cases_on `(f2 >>= (λy. constT (a,y))) b`
                             THEN Cases_on `(f2 >>= (λy. constT (a,y))) b'`
                             THEN SPEC_ASSUM_TAC (``∀x (g:word32) (s1:arm_state) (s2:arm_state). X``, [``a:'a``, ``g:word32``, ``b:arm_state``, ``b':arm_state``])
                             THEN (NTAC 2 (RES_TAC
                                           THEN IMP_RES_TAC untouched_trans
                                           THEN FULL_SIMP_TAC (srw_ss()) []
                                           THEN IMP_RES_TAC untouched_mmu_setup_lem
                                           THEN TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
                                           THEN UNDISCH_ALL_TAC
                                           THEN RW_TAC (srw_ss()) []
                                           THEN FULL_SIMP_TAC (srw_ss()) []))
                             THEN METIS_TAC [comb_rel_lem]]);


val parT_preserves_relation_uu_thm = store_thm("parT_preserves_relation_uu_thm",
    `` ! f1 f2 k  uf uy.
         (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy) ==>
          (preserve_relation_mmu  f2 (assert_mode k) (assert_mode k) uf uy)   ==>
           (preserve_relation_mmu  (parT f1 f2) (assert_mode k) (assert_mode k) uf uy) ``,
     REPEAT STRIP_TAC
        THEN IMP_RES_TAC parT_latter_part_hlem
        THEN WEAKEN_TAC is_forall
        THEN THROW_ONE_AWAY_TAC ``preserve_relation_mmu (*II*) f2  (assert_mode k) (assert_mode k) uf uy``
        THEN UNDISCH_ALL_TAC
        THEN RW_TAC (srw_ss()) [parT_alternative_thm, preserve_relation_mmu_def,trans_fun_def]
        THEN UNDISCH_ALL_TAC
        THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
        THEN FIRST_PROVE [
                          RW_TAC (srw_ss()) []
                             THEN Cases_on `(assert_mode k)  s2`
                             THEN RES_TAC
                             THEN (NTAC 3 (FULL_SIMP_TAC (srw_ss()) [])),
                          RW_TAC (srw_ss()) []
                             THEN RES_TAC
                             THEN RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
                             THEN FULL_SIMP_TAC (srw_ss()) [],
                          ASSERT_ASSUM_TAC ``access_violation b``
                             THEN UNDISCH_ALL_TAC
                             THEN RW_TAC (srw_ss()) []
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN RES_TAC
                             THEN IMP_RES_TAC untouched_trans
                             THEN FULL_SIMP_TAC (srw_ss()) []
                             THEN METIS_TAC [untouched_trans, comb_rel_lem],
                          RW_TAC (srw_ss()) [assert_mode_def]
                        THEN Cases_on `(f2 >>= (λy. constT (a,y))) b`
                             THEN Cases_on `(f2 >>= (λy. constT (a,y))) b'`
                             THEN SPEC_ASSUM_TAC (``∀x (g:word32) (s1':arm_state) (s2':arm_state). X``, [``a:'a``, ``g:word32``, ``b:arm_state``, ``b':arm_state``])
                             THEN (NTAC 2 (RES_TAC
                                           THEN IMP_RES_TAC untouched_trans
                                           THEN FULL_SIMP_TAC (srw_ss()) []
                                           THEN IMP_RES_TAC untouched_mmu_setup_lem
                                           THEN TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
                                           THEN UNDISCH_ALL_TAC
                                           THEN RW_TAC (srw_ss()) []
                                           THEN FULL_SIMP_TAC (srw_ss()) []))
                             THEN METIS_TAC [comb_rel_lem]]);

val comb_monot_thm = store_thm("comb_monot_thm",
                               ``!a:(arm_state -> bool). comb a a a``,
                               RW_TAC (srw_ss()) [comb_def]);



val preserve_relation_comb_thm1 =
    store_thm ("preserve_relation_comb_thm1",
               ``! a b c d f  uf uy.
              preserve_relation_mmu  f d a uf uy
              ==>
              comb a b c ==>
              preserve_relation_mmu  f d c uf uy``,
               RW_TAC (srw_ss()) [preserve_relation_mmu_def,comb_def]
                      THEN PAT_X_ASSUM ``∀g s1 s2. X``
                      (fn thm => ASSUME_TAC (SPECL [``g:bool[32]``,
                                                    ``s1:arm_state``, ``s2:arm_state``] thm))
    THEN RES_TAC
         THEN RW_TAC (srw_ss()) []);

val preserve_relation_comb_v2_thm =
    store_thm ("preserve_relation_comb_v2_thm",
               ``! a b c d f  uf uy.
              preserve_relation_mmu  f d a uf uy
              ==>
              comb a b c ==>
              preserve_relation_mmu  f d c uf uy``,
               RW_TAC (srw_ss()) [preserve_relation_mmu_def,comb_def]
                      THEN PAT_X_ASSUM ``∀g s1 s2. X``
                      (fn thm => ASSUME_TAC (SPECL [``g:bool[32]``,
                                                    ``s1:arm_state``, ``s2:arm_state``] thm))
    THEN RES_TAC
         THEN RW_TAC (srw_ss()) []);

val preserve_relation_comb_abs_thm =
    store_thm ("preserve_relation_comb_abs_thm",
               ``! a b c d f uf uy. preserve_relation_mmu_abs f d b uf uy
              ==>  comb a b c ==>
              preserve_relation_mmu_abs f d c uf uy``,
               RW_TAC (srw_ss()) [preserve_relation_mmu_abs_def,comb_def]
                      THEN PAT_X_ASSUM ``∀ c g s1 s2. X``
                      (fn thm => ASSUME_TAC (SPECL [``c':'a``,``g:bool[32]``,
                                                    ``s1:arm_state``, ``s2:arm_state``] thm))
    THEN RES_TAC
         THEN RW_TAC (srw_ss()) []);


val comb_mode_def = Define `comb_mode m n s = (assert_mode m s \/ assert_mode n s)`;

val comb_mode_thm =
    store_thm ("comb_mode_thm",
``! m n. comb (assert_mode m) (assert_mode n) (comb_mode m n)``,
RW_TAC (srw_ss()) [ assert_mode_def,comb_mode_def,comb_def]);



(*********    3-parts-lem   *********)

val keep_mode_relation_def = Define `keep_mode_relation comp i1 i2 =
  (!g s s' x. (mmu_requirements s g) ==> (i1 s) ==> (comp s = ValueState x s') ==> (i2 s'))`;

val keep_similar_relation_def = Define `keep_similar_relation comp invr1 y =
    !g s1 s2.
    mmu_requirements s1 g    ==>
    mmu_requirements s2 g    ==>
    similar g s1 s2          ==>
    (y  g s1 s2)            ==>
    invr1 s1                 ==>
    invr1 s2                 ==>
    ((?a s1' s2'.((comp s1 = ValueState a s1') /\  (comp s2 = ValueState a s2') /\
           (y  g s1' s2') /\        (similar g s1' s2')))
\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;

val keep_untouched_relation_def = Define `keep_untouched_relation comp invr1 f =
    !g s s' a. (mmu_requirements s g) ==> (invr1 s) ==> (comp s = ValueState a s') ==> ((untouched g s s') /\  (f g s s'))`;

val three_parts_thm = store_thm(
    "three_parts_thm",
    ``!comp i1 i2 f y. (keep_mode_relation comp i1 i2) ==> (keep_similar_relation comp i1 y) ==> (keep_untouched_relation comp i1 f) ==> (preserve_relation_mmu comp i1 i2 f y)``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def] THEN METIS_TAC []);

val refl_rel_def = Define `refl_rel y = (!gg ss. y gg ss ss)`;



val downgrade_thm = store_thm (
    "downgrade_thm",
    ``!comp i1 i2 f y. (preserve_relation_mmu comp i1 i2 f y) ==> (refl_rel y)
       ==> (keep_mode_relation comp i1 i2 /\ keep_similar_relation comp i1 y /\ keep_untouched_relation comp i1 f)``,
    RW_TAC (srw_ss()) [refl_rel_def, preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def]
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (TRY (METIS_TAC []))
       THEN ASSUME_TAC (SPECL [``g:word32``, ``s:arm_state``] similar_refl)
       THEN SPEC_ASSUM_TAC (``!gg ss. y gg ss``, [``g:word32``, ``s:arm_state``])
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN METIS_TAC []);








(******  handling forT loops   *******)


val comb_gen_lem = store_thm(
    "comb_gen_lem",
    ``!comp i1 i2 i3 i23 f y. (comb i2 i3 i23 \/ comb i3 i2 i23) ==> (preserve_relation_mmu comp i1 i2 f y) ==> (preserve_relation_mmu comp i1 i23 f y)``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, comb_def]
        THEN METIS_TAC[]);



val constT_unit_preserving_lem = store_thm(
    "constT_unit_preserving_lem",
    ``!invr:(arm_state->bool) uf uy.  (reflexive_comp  uf invr) ==>
                              preserve_relation_mmu  (constT ()) invr invr uf uy``,
    RW_TAC (srw_ss()) [constT_def, preserve_relation_mmu_def, untouched_def, similar_def,reflexive_comp_def] THEN
(RW_TAC (srw_ss()) [] ));



val SEQT_UNTOUCHED_TAC =
    UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [seqT_def, keep_untouched_relation_def, trans_fun_def]
       THEN UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN RES_TAC
       THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) [];




val forT_untouching_thm = store_thm(
    "forT_untouching_thm",
    ``!f k uf uy.
            (trans_fun uf)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!l h. keep_untouched_relation (forT l h f) (assert_mode k) uf)``,
    REPEAT STRIP_TAC
      THEN Induct_on `h - l`
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF])
                THEN RW_TAC arith_ss [keep_untouched_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_X_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN REPEAT STRIP_TAC
                THEN SEQT_UNTOUCHED_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, reflexive_comp_def]
                THEN RW_TAC (srw_ss()) [LET_DEF],
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss [constT_def]
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_X_ASSUM ``!(h:num) (l:num). (X:bool) ==> Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN REPEAT (PAT_X_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th))))
                THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def]
                THEN REPEAT STRIP_TAC
                THEN SEQT_UNTOUCHED_TAC
                THEN METIS_TAC [assert_mode_def]]);


val SEQT_PRESERVE_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,keep_similar_relation_def,keep_untouched_relation_def, keep_mode_relation_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN METIS_TAC []);


val SEQT_PRESERVE_BEGIN_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,keep_similar_relation_def,keep_untouched_relation_def, keep_mode_relation_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]);

val forT_similar_thm = store_thm(
    "forT_similar_thm",
    ``!f k uf uy.
            (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!a. keep_similar_relation (f a) (assert_mode k) uy)
        ==> (!l h. keep_similar_relation (forT l h f) (assert_mode k) uy)``,
    REPEAT STRIP_TAC
      THEN IMP_RES_TAC forT_untouching_thm
      THEN Induct_on `h - l`
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN (REPEAT STRIP_TAC)
                THEN (NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]))
                THEN RW_TAC arith_ss [keep_similar_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_X_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN (REPEAT STRIP_TAC)
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_TAC "f l",


             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss []
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_X_ASSUM ``!h l. X ==> Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN REPEAT (PAT_X_ASSUM ``!(a:num). Z (x)`` (fn th => ASSUME_TAC (SPEC ``l:num`` th)))
                THEN REPEAT STRIP_TAC
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_BEGIN_TAC "f l"
                THEN Cases_on `forT (l + 1) h f b`
                THEN Cases_on `forT (l + 1) h f b'`
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN PAT_X_ASSUM ``∀g s1 s2. mmu_requirements s1 g ⇒
                                           mmu_requirements s2 g ⇒
                                           similar g s1 s2 ⇒
                                           uy g s1 s2 ==>
                                           (invr s1) ==>
                                           (invr s2) ==>
                                   (∃a s1' s2'.
                                       (forT (l + 1) h f s1 = ValueState a s1') ∧
                                       (forT (l + 1) h f s2 = ValueState a s2') ∧ (uy g s1' s2') /\ similar g s1' s2') ∨
                                    ∃e.
                                       (forT (l + 1) h f s1 = Error e) ∧
                                       (forT (l + 1) h f s2 = Error e)``
                     (fn th => ASSUME_TAC (SPECL [``g:word32``, ``b:arm_state``, ``b':arm_state``] th))
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT IF_CASES_TAC THEN RW_TAC (srw_ss()) []
                THEN (`access_violation b'' = access_violation b'''` by METIS_TAC [similar_def])
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val forT_mode_thm = store_thm(
    "forT_mode_thm",
    ``!f k uf.
            (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!l h. keep_mode_relation (forT l h f)  (assert_mode k) (assert_mode k))``,
    REPEAT STRIP_TAC
      THEN Induct_on `h - l`
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF])
                THEN RW_TAC arith_ss [keep_untouched_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_X_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN REPEAT STRIP_TAC
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) [seqT_def, keep_mode_relation_def]
                THEN UNDISCH_ALL_TAC
                THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [],
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss [constT_def]
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_X_ASSUM ``!h l. X ==> Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN REPEAT (PAT_X_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th))))
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) [seqT_def, keep_mode_relation_def]
                THEN UNDISCH_ALL_TAC
                THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [keep_untouched_relation_def]
                THEN RES_TAC
                THEN IMP_RES_TAC untouched_mmu_setup_lem
                THEN RES_TAC]);



val forT_preserves_user_relation_thm = store_thm(
    "forT_preserves_user_relation_thm",
    ``!f k uf uy.
            (trans_fun uf)
        ==> (refl_rel uy)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (!a. preserve_relation_mmu (f a) (assert_mode k) (assert_mode k) uf uy)
        ==> (!l h. preserve_relation_mmu (forT l h f) (assert_mode k) (assert_mode k) uf uy)``,
        METIS_TAC [forT_similar_thm, forT_mode_thm, forT_untouching_thm, three_parts_thm, downgrade_thm]);


val forT_preserving_thm = store_thm(
    "forT_preserving_thm",
    ``!f k uf uy.
            (trans_fun uf)
        ==> (refl_rel uy)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (preserve_relation_mmu_abs f (assert_mode k) (assert_mode k) uf uy)
        ==> (!l h. preserve_relation_mmu (forT l h f) (assert_mode k) (assert_mode k) uf uy)``,
   RW_TAC (srw_ss()) [] THEN METIS_TAC [forT_preserves_user_relation_thm, second_abs_lemma]);


(*********    errorT   *********)


val errorT_thm =
    store_thm("errorT_thm",
              ``! inv s uf1 uy1. preserve_relation_mmu (errorT s) inv inv uf1 uy1 ``,
              (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,
                                  assert_mode_def,errorT_def,untouched_def]));

val errorT_comb_thm =
    store_thm("errorT_comb_thm",
              ``! inv1 inv2 s uf1 uy1. preserve_relation_mmu (errorT s) inv1 inv2 uf1 uy1 ``,
              (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,
                                  assert_mode_def,errorT_def,untouched_def]));



val _ = export_theory();
