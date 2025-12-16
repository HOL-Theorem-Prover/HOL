
Theory straightline
Ancestors
  words pair list relation pred_set arithmetic combin arm_decomp
  set_sep prog address triple GraphLang
Libs
  wordsLib

Definition arm_assert_def:
  arm_assert (p,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,n,z,c,v,
              mode,dmem,memory,dom_stack,stack) =
    arm_PC p *
    arm_REG (R_mode mode 0w) r0 *
    arm_REG (R_mode mode 1w) r1 *
    arm_REG (R_mode mode 2w) r2 *
    arm_REG (R_mode mode 3w) r3 *
    arm_REG (R_mode mode 4w) r4 *
    arm_REG (R_mode mode 5w) r5 *
    arm_REG (R_mode mode 6w) r6 *
    arm_REG (R_mode mode 7w) r7 *
    arm_REG (R_mode mode 8w) r8 *
    arm_REG (R_mode mode 9w) r9 *
    arm_REG (R_mode mode 10w) r10 *
    arm_REG (R_mode mode 11w) r11 *
    arm_REG (R_mode mode 12w) r12 *
    arm_REG (R_mode mode 13w) r13 *
    arm_REG (R_mode mode 14w) r14 *
    arm_CPSR_N n *
    arm_CPSR_Z z *
    arm_CPSR_C c *
    arm_CPSR_V v *
    arm_OK mode *
    arm_MEMORY dmem memory *
    arm_STACK_MEMORY dom_stack stack
End

Theorem TRIPLE_INTRO:
    (c_post ==> SPEC model (assert p) code (assert post)) ==>
    TRIPLE (assert,model) (pre,p) code (pre /\ c_post,post)
Proof
  full_simp_tac std_ss [tripleTheory.TRIPLE_def]
QED

Theorem SPEC_VAR_PC:
    SPEC m (pre * res w) code q ==>
    !p. (p = w) ==> SPEC m (pre * res p) code q
Proof
  fs []
QED

Theorem TRIPLE_NOP:
    TRIPLE (arm_assert,ARM_MODEL)
     (pre,p,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,n,z,c,v,
      mode,dmem,memory,dom_stack,stack) code
     (pre,p,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,n,z,c,v,
      mode,dmem,memory,dom_stack,stack)
Proof
  fs [TRIPLE_def,SPEC_REFL]
QED

Theorem COMBINE1:
    ((x1 = x2) ==> (t1 = t2)) /\ ((y1 = y2) ==> (u1 = u2)) ==>
    (((x1,y1) = (x2,y2)) ==> ((t1,u1) = (t2,u2)))
Prooffs []
QED

Theorem COMBINE2:
    ((x1 = x2) ==> (t1 = t2)) /\ ((u1 = u2)) ==>
    (((x1) = (x2)) ==> ((t1,u1) = (t2,u2)))
Prooffs []
QED

Theorem COMBINE3:
    ((t1 = t2)) /\ ((y1 = y2) ==> (u1 = u2)) ==>
    (((y1) = (y2)) ==> ((t1,u1) = (t2,u2)))
Prooffs []
QED

Theorem COMBINE4:
    (t1 = t2) /\ (u1 = u2) ==> ((t1,u1) = (t2,u2))
Prooffs []
QED

Definition DO_NOTHING_def:   DO_NOTHING x = x
End

