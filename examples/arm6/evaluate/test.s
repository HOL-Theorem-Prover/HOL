0x8000:
B label
B 0x8004
label: B label
SWI
ADDCS r4, r3, #5
B label
ANDVSS r4, r3, r2
TST r4, r2, LSL #1
MOV r4, r2, ASR #32
MVNS r4, r2, RRX
RSC r4, r3, r2, LSL r1
MULS r4, r3, r2
MLA r4, r3, r2, r1
LDR r4, [r3]
LDRB r4, [r3], #-4
LDRB r4, [r3, #4]!
LDR r4, [r3], -r2
LDR r4, [r3], -r2, RRX
STR r4, [r3], -r2, LSL #4
STRB r4, [r3, r2, LSL #4]!
LDMIB r4!, {r0-r7, r12-r15}^
STMDA r4, {r15}
SWP r3, r2, [r1]
SWPB r3, r2, [r1]
MRS r1, CPSR
MRS r1, SPSR
MSR CPSR_f, #1342177280
MSR CPSR_c, #1342177280
MSR SPSR, #1342177280
MSR SPSR, r5
CDP p1, 2, c3, c4, c5, 6
LDC p1, c2, [r3], #-16
STC p1, c2, [r3, #16]!
MCR p1, 2, r3, c4, c5, 6
MRC p1, 2, r3, c4, c5, 6
0xE6000010
