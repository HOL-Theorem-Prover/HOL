0x8000:	stmdb	sp!, {r4, r5, r6, r7, r8, r9, sl, fp, ip, lr}
0x8004:	ldmia	r0!, {r3, r4}
0x8008:	ldmia	r1!, {r8, r9}
0x800c:	adds	r3, r3, r8
0x8010:	adcs	r4, r4, r9
0x8014:	stmia	r2!, {r3, r4}
0x8018:	bl	0x8034
0x801c:	bl	0x8034
0x8020:	bl	0x8034
0x8024:	movcs	r0, #1	; 0x1
0x8028:	movcc	r0, #0	; 0x0
0x802c:	ldmia	sp!, {r4, r5, r6, r7, r8, r9, sl, fp, ip, lr}
0x8030:	mov	pc, lr
0x8034:	ldmia	r0!, {r3, r4, r5, r6, r7}
0x8038:	ldmia	r1!, {r8, r9, sl, fp, ip}
0x803c:	adcs	r3, r3, r8
0x8040:	adcs	r4, r4, r9
0x8044:	adcs	r5, r5, sl
0x8048:	adcs	r6, r6, fp
0x804c:	adcs	r7, r7, ip
0x8050:	stmia	r2!, {r3, r4, r5, r6, r7}
0x8054:	mov	pc, lr
