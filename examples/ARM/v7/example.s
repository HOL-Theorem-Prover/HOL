	ARCH	armv5te

	THUMB

	blx	label

	ARM

label:
	ldreq	r1,[r2],#4
	add	r1,r2

	WORD	0xFEED,0xACE
