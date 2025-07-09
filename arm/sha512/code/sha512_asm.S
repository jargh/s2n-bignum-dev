	.arch armv8-a+nosimd
	.file	"sha512.c"
	.text
	.align	2
	.p2align 5,,15
	.type	msg_schedule, %function
msg_schedule:
.LFB12:
	.cfi_startproc
	mov	x3, 0
	.p2align 5,,15
.L2:
	ldrb	w5, [x1]
	mov	x2, 0
	add	x1, x1, 8
	ldrb	w4, [x1, -7]
	ldrb	w6, [x1, -6]
	bfi	x2, x5, 0, 8
	ldrb	w5, [x1, -5]
	bfi	x2, x4, 8, 8
	ldrb	w4, [x1, -4]
	bfi	x2, x6, 16, 8
	ldrb	w6, [x1, -3]
	bfi	x2, x5, 24, 8
	ldrb	w5, [x1, -2]
	bfi	x2, x4, 32, 8
	ldrb	w4, [x1, -1]
	bfi	x2, x6, 40, 8
	bfi	x2, x5, 48, 8
	bfi	x2, x4, 56, 8
	rev	x2, x2
	str	x2, [x0, x3, lsl 3]
	add	x3, x3, 1
	cmp	x3, 16
	bne	.L2
	mov	x2, x0
	add	x11, x0, 520
	ldp	x9, x8, [x0, 80]
	ldp	x7, x6, [x0, 96]
	ldp	x3, x0, [x0, 112]
	ldr	x10, [x2, 72]
	ldr	x4, [x2], 8
	.p2align 5,,15
.L3:
	add	x5, x4, x10
	ror	x1, x3, 61
	ldr	x4, [x2]
	eor	x1, x1, x3, ror 19
	mov	x10, x9
	mov	x9, x8
	mov	x8, x7
	eor	x1, x1, x3, lsr 6
	mov	x7, x6
	mov	x6, x3
	mov	x3, x0
	add	x2, x2, 8
	ror	x0, x4, 8
	eor	x0, x0, x4, ror 1
	eor	x0, x0, x4, lsr 7
	add	x0, x0, x1
	add	x0, x0, x5
	str	x0, [x2, 112]
	cmp	x11, x2
	bne	.L3
	ret
	.cfi_endproc
.LFE12:
	.size	msg_schedule, .-msg_schedule
	.align	2
	.p2align 5,,15
	.type	sha512_process_block, %function
sha512_process_block:
.LFB13:
	.cfi_startproc
	sub	sp, sp, #720
	.cfi_def_cfa_offset 720
	mov	x12, x0
	add	x0, sp, 80
	stp	x29, x30, [sp]
	.cfi_offset 29, -720
	.cfi_offset 30, -712
	mov	x29, sp
	bl	msg_schedule
	tst	x12, 15
	bne	.L8
	ldp	x6, x7, [x12]
	ldp	x4, x5, [x12, 16]
	ldp	x2, x3, [x12, 32]
	ldp	x0, x1, [x12, 48]
	stp	x6, x7, [sp, 16]
	stp	x4, x5, [sp, 32]
	stp	x2, x3, [sp, 48]
	stp	x0, x1, [sp, 64]
.L9:
	adrp	x14, K
	mov	x6, 1
	add	x14, x14, :lo12:K
	ldp	x5, x8, [sp, 16]
	ldp	x7, x13, [sp, 32]
	ldp	x3, x10, [sp, 48]
	ldp	x9, x11, [sp, 64]
	b	.L10
	.p2align 2,,3
.L11:
	mov	x7, x8
	mov	x9, x10
	mov	x8, x5
	mov	x10, x3
	mov	x5, x0
	mov	x3, x2
.L10:
	lsl	x1, x6, 3
	add	x4, sp, 80
	ror	x0, x3, 18
	add	x2, x14, x1
	add	x15, x4, x1
	eor	x0, x0, x3, ror 14
	ror	x1, x5, 34
	ldr	x16, [x2, -8]
	eor	x1, x1, x5, ror 28
	bic	x4, x9, x3
	eor	x0, x0, x3, ror #(64 - 23)
	and	x18, x3, x10
	eor	x2, x7, x8
	ldr	x17, [x15, -8]
	eor	x4, x4, x18
	eor	x1, x1, x5, ror #(64 - 25)
	add	x0, x0, x4
	and	x2, x2, x5
	and	x4, x7, x8
	add	x6, x6, 1
	eor	x2, x2, x4
	add	x1, x1, x2
	add	x2, x16, x17
	add	x0, x0, x2
	add	x0, x0, x11
	mov	x11, x9
	add	x2, x13, x0
	add	x0, x0, x1
	mov	x13, x7
	cmp	x6, 81
	bne	.L11
	ldp	x6, x4, [x12]
	ldp	x29, x30, [sp]
	add	x6, x6, x0
	add	x4, x4, x5
	ldp	x0, x5, [x12, 24]
	stp	x6, x4, [x12]
	add	x0, x0, x7
	add	x5, x5, x2
	ldr	x1, [x12, 16]
	str	x5, [x12, 32]
	add	x1, x1, x8
	stp	x1, x0, [x12, 16]
	ldp	x4, x1, [x12, 40]
	ldr	x0, [x12, 56]
	add	x2, x4, x3
	add	x1, x1, x10
	stp	x2, x1, [x12, 40]
	add	x0, x0, x9
	str	x0, [x12, 56]
	add	sp, sp, 720
	.cfi_remember_state
	.cfi_restore 29
	.cfi_restore 30
	.cfi_def_cfa_offset 0
	ret
.L8:
	.cfi_restore_state
	ldp	x1, x0, [x12]
	ldr	x2, [x12, 16]
	stp	x1, x0, [sp, 16]
	ldp	x1, x0, [x12, 24]
	str	x2, [sp, 32]
	ldr	x2, [x12, 40]
	stp	x1, x0, [sp, 40]
	ldp	x1, x0, [x12, 48]
	str	x2, [sp, 56]
	stp	x1, x0, [sp, 64]
	b	.L9
	.cfi_endproc
.LFE13:
	.size	sha512_process_block, .-sha512_process_block
	.align	2
	.p2align 5,,15
	.type	sha512_process_blocks, %function
sha512_process_blocks:
.LFB14:
	.cfi_startproc
	cbz	x2, .L21
	stp	x29, x30, [sp, -48]!
	.cfi_def_cfa_offset 48
	.cfi_offset 29, -48
	.cfi_offset 30, -40
	mov	x29, sp
	stp	x19, x20, [sp, 16]
	.cfi_offset 19, -32
	.cfi_offset 20, -24
	mov	x19, x1
	sub	x20, x2, #1
	str	x21, [sp, 32]
	.cfi_offset 21, -16
	mov	x21, x0
	.p2align 5,,15
.L15:
	mov	x1, x19
	mov	x0, x21
	sub	x20, x20, #1
	add	x19, x19, 128
	bl	sha512_process_block
	cmn	x20, #1
	bne	.L15
	ldp	x19, x20, [sp, 16]
	ldr	x21, [sp, 32]
	ldp	x29, x30, [sp], 48
	.cfi_restore 30
	.cfi_restore 29
	.cfi_restore 21
	.cfi_restore 19
	.cfi_restore 20
	.cfi_def_cfa_offset 0
	ret
	.p2align 2,,3
.L21:
	ret
	.cfi_endproc
.LFE14:
	.size	sha512_process_blocks, .-sha512_process_blocks
	.align	2
	.p2align 5,,15
	.global	sha512_init
	.type	sha512_init, %function
sha512_init:
.LFB11:
	.cfi_startproc
	mov	x1, 51464
	mov	x7, 42811
	stp	xzr, xzr, [x0, 64]
	movk	x1, 0xf3bc, lsl 16
	movk	x7, 0x84ca, lsl 16
	movk	x1, 0xe667, lsl 32
	movk	x7, 0xae85, lsl 32
	movk	x1, 0x6a09, lsl 48
	movk	x7, 0xbb67, lsl 48
	strb	wzr, [x0, 208]
	mov	x6, 63531
	mov	x5, 14065
	mov	x4, 33489
	mov	x3, 27679
	stp	x1, x7, [x0]
	mov	x2, 48491
	mov	x1, 8569
	movk	x6, 0xfe94, lsl 16
	movk	x5, 0x5f1d, lsl 16
	movk	x4, 0xade6, lsl 16
	movk	x3, 0x2b3e, lsl 16
	movk	x2, 0xfb41, lsl 16
	movk	x1, 0x137e, lsl 16
	movk	x6, 0xf372, lsl 32
	movk	x5, 0xf53a, lsl 32
	movk	x4, 0x527f, lsl 32
	movk	x3, 0x688c, lsl 32
	movk	x2, 0xd9ab, lsl 32
	movk	x1, 0xcd19, lsl 32
	movk	x6, 0x3c6e, lsl 48
	movk	x5, 0xa54f, lsl 48
	movk	x4, 0x510e, lsl 48
	movk	x3, 0x9b05, lsl 48
	movk	x2, 0x1f83, lsl 48
	movk	x1, 0x5be0, lsl 48
	stp	x6, x5, [x0, 16]
	stp	x4, x3, [x0, 32]
	str	x2, [x0, 48]
	str	x1, [x0, 56]
	ret
	.cfi_endproc
.LFE11:
	.size	sha512_init, .-sha512_init
	.align	2
	.p2align 5,,15
	.global	sha512_update
	.type	sha512_update, %function
sha512_update:
.LFB15:
	stp	x29, x30, [sp, -48]!
	mov	x29, sp
	stp	x19, x20, [sp, 16]
	str	x21, [sp, 32]
	mov	x21, x0
	mov	x19, x1
	mov	x20, x2
	lsl	x3, x20, 3
	lsr	x5, x20, 61
	ldr	x0, [x21, 64]
	ldr	x2, [x21, 72]
	adds	x0, x0, x3
	adc	x2, x2, x5
    stp	x0, x2, [x21, 64]   // Update message length information
	ldrb	w4, [x21, 208]  // x4 contains cur_pos
    cbz	x4, .L29            // Jump if cur_pos == 0
    mov x0, 128
    sub x0, x0, x4          // x0 contains the number of vacant bytes in cur_block
    cmp x0, x20
    bls .L30                // Jump if in_data can fill up cur_block
    mov x0, x20             // x0 contains the number of bytes to move to cur_block
.L30:
    add x1, x21, 80         // x1 contains cur_block
    mov x2, xzr             // x2 is the loop counter
    b .L31                  // Start memcpy loop
.L32:
    ldrb w3, [x19, x2]      // While counter < number of bytes to move
    strb w3, [x1, x4]       //      Move a byte from in_data to cur_block[cur_pos]
    add x2, x2, 1           //      Increment counter and cur_pos
    add x4, x4, 1
.L31:
    cmp x2, x0
    bne .L32
    add x19, x19, x0        // Update in_data and in_len
    sub x20, x20, x0
    cmp x4, 128
    bne .L33                // Jump if cur_pos < 128 (iff in_data could not fill up cur_block)
    mov x0, x21
    bl sha512_process_block // Process the filled block
.L29:
    cmp x20, 128
    blo .L34                // Jump if in_len < SHA512_BLOCK_LENGTH
    mov x0, x21
    mov x1, x19
    lsr x2, x20, 7          // Compute the number of blocks to process
    lsl x3, x2, 7
    add x19, x19, x3        // x19 points to the data to be copied to cur_block later 
    and x20, x20, 127       // in_len mod 128
    bl sha512_process_blocks
.L34:                       // Move the leftover data to cur_block (x20 < SHA512_BLOCK_LENGTH == 128)
    mov x4, xzr             // x4 is the loop counter
    add x1, x21, 80         // x1 contains to cur_block
    b .L35
.L36:
    ldrb w2, [x19, x4]
    strb w2, [x1, x4]
    add x4, x4, 1
.L35:
    cmp x4, x20
    bne .L36
.L33:
    strb w4, [x21, 208]     // Store cur_pos
	ldp	x19, x20, [sp, 16]
	ldr	x21, [sp, 32]
	ldp	x29, x30, [sp], 48
    ret
.LFE15:
	.size	sha512_update, .-sha512_update
	.align	2
	.p2align 5,,15
	.global	sha512_final
	.type	sha512_final, %function
sha512_final:
.LFB16:
	stp	x29, x30, [sp, -48]!
	mov	x29, sp
	stp	x19, x20, [sp, 16]
	mov	x20, x0                 // x20 points to output buffer
	mov	x19, x1                 // x19 points to sha context
	str	x21, [sp, 32]
	add	x21, x19, 80            // x21 contains cur_block
	ldrb	w2, [x19, 208]      // x2 contains cur_pos
    mov	w3, 0x80
    strb    w3, [x21, x2] // First byte of padding is 0x80
    add x2, x2, 1               // Increment cur_pos
    cmp x2, 112                 // Compare cur_pos with SHA512_BLOCK_LENGTH - 16
    bls .L112                   // Jump if there is only one block left
    b .L113                     // Start of memset loop
.L114:
    strb	wzr, [x21, x2]      // While cur_pos < SHA512_BLOCK_LENGTH
    add x2, x2, 1               //   store a zero byte at cur_block[cur_pos] and increment cur_pos
.L113:
    cmp x2, 128
    bne .L114
	mov	x0, x19                 // Prepare to call subroutine
	mov	x1, x21
    bl	sha512_process_block    // Process the second last block
    mov x2, xzr                 // Set cur_pos to zero
.L112:
    b .L115                     // Start memset loop
.L116:
    strb    wzr, [x21, x2]      // While cur_pos < SHA512_BLOCK_LENGTH - 16
    add x2, x2, 1               //   store a zero byte at cur_block[cur_pos] and increment cur_pos
.L115:
    cmp x2, 112
    bne .L116
    ldr	x0, [x19, 72]           // Move message length information into the block
	rev	x0, x0
	str	x0, [x19, 192]
	ldr	x0, [x19, 64]
	rev	x0, x0
	str	x0, [x19, 200]
	mov	x0, x19                 // Prepare to call subroutine
	mov	x1, x21
	bl	sha512_process_block    // Process the last block
    ldr	x0, [x19]               // Store the digest in big-endian in output buffer
	rev	x0, x0
	str	x0, [x20]
	ldr	x0, [x19, 8]
	rev	x0, x0
	str	x0, [x20, 8]
	ldr	x0, [x19, 16]
	rev	x0, x0
	str	x0, [x20, 16]
	ldr	x0, [x19, 24]
	rev	x0, x0
	str	x0, [x20, 24]
	ldr	x0, [x19, 32]
	rev	x0, x0
	str	x0, [x20, 32]
	ldr	x0, [x19, 40]
	rev	x0, x0
	str	x0, [x20, 40]
	ldr	x0, [x19, 48]
	rev	x0, x0
	str	x0, [x20, 48]
	ldr	x0, [x19, 56]
	rev	x0, x0
	str	x0, [x20, 56]
	ldp	x19, x20, [sp, 16]
	ldr	x21, [sp, 32]
	ldp	x29, x30, [sp], 48
	ret
.LFE16:
	.size	sha512_final, .-sha512_final
	.global	K
	.section	.rodata
	.align	3
	.type	K, %object
	.size	K, 640
K:
	.xword	4794697086780616226
	.xword	8158064640168781261
	.xword	-5349999486874862801
	.xword	-1606136188198331460
	.xword	4131703408338449720
	.xword	6480981068601479193
	.xword	-7908458776815382629
	.xword	-6116909921290321640
	.xword	-2880145864133508542
	.xword	1334009975649890238
	.xword	2608012711638119052
	.xword	6128411473006802146
	.xword	8268148722764581231
	.xword	-9160688886553864527
	.xword	-7215885187991268811
	.xword	-4495734319001033068
	.xword	-1973867731355612462
	.xword	-1171420211273849373
	.xword	1135362057144423861
	.xword	2597628984639134821
	.xword	3308224258029322869
	.xword	5365058923640841347
	.xword	6679025012923562964
	.xword	8573033837759648693
	.xword	-7476448914759557205
	.xword	-6327057829258317296
	.xword	-5763719355590565569
	.xword	-4658551843659510044
	.xword	-4116276920077217854
	.xword	-3051310485924567259
	.xword	489312712824947311
	.xword	1452737877330783856
	.xword	2861767655752347644
	.xword	3322285676063803686
	.xword	5560940570517711597
	.xword	5996557281743188959
	.xword	7280758554555802590
	.xword	8532644243296465576
	.xword	-9096487096722542874
	.xword	-7894198246740708037
	.xword	-6719396339535248540
	.xword	-6333637450476146687
	.xword	-4446306890439682159
	.xword	-4076793802049405392
	.xword	-3345356375505022440
	.xword	-2983346525034927856
	.xword	-860691631967231958
	.xword	1182934255886127544
	.xword	1847814050463011016
	.xword	2177327727835720531
	.xword	2830643537854262169
	.xword	3796741975233480872
	.xword	4115178125766777443
	.xword	5681478168544905931
	.xword	6601373596472566643
	.xword	7507060721942968483
	.xword	8399075790359081724
	.xword	8693463985226723168
	.xword	-8878714635349349518
	.xword	-8302665154208450068
	.xword	-8016688836872298968
	.xword	-6606660893046293015
	.xword	-4685533653050689259
	.xword	-4147400797238176981
	.xword	-3880063495543823972
	.xword	-3348786107499101689
	.xword	-1523767162380948706
	.xword	-757361751448694408
	.xword	500013540394364858
	.xword	748580250866718886
	.xword	1242879168328830382
	.xword	1977374033974150939
	.xword	2944078676154940804
	.xword	3659926193048069267
	.xword	4368137639120453308
	.xword	4836135668995329356
	.xword	5532061633213252278
	.xword	6448918945643986474
	.xword	6902733635092675308
	.xword	7801388544844847127
	.ident	"GCC: (GNU) 11.5.0 20240719 (Red Hat 11.5.0-5)"
	.section	.note.GNU-stack,"",@progbits
