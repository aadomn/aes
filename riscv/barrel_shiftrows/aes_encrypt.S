/******************************************************************************
* Bitsliced AES-128 and AES-256 (encryption-only) implementations in RV32I
* assembly, using the base instruction set only (no RISC-V extension needed).
*
* The implementation relies on the barrel-shiftrows representation introduced 
* in the following article: https:// 
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     August 2020
******************************************************************************/

.text
/******************************************************************************
* Implementation of the SWAPMOVE technique for the packing/unpacking routines.
*
* - out0-out1 are output registers.
* - in0-in1 are output registers.
* - mask is the mask.
* - c0 is the shift index (must be an immediate value)
* - r0 is used as a temporary register
******************************************************************************/
.macro swapmove out0,out1, in0,in1, mask, imm, r0
    srli   \r0, \in0, \imm
    xor    \r0, \r0, \in1
    and    \r0, \r0, \mask
    xor    \out1, \in1, \r0
    slli   \r0, \r0, \imm
    xor    \out0, \in0, \r0
.endm

/******************************************************************************
* Addition of the round key on a quarter of the internal state.
*
* - b0-b7 contains a quarter of the state.
* - rk points to the round key.
* - r0-r1 are temporary registers.
******************************************************************************/
.macro addroundkey b0,b1,b2,b3,b4,b5,b6,b7, rk, r0,r1
    lw      \r0,  0+\rk
    lw      \r1,  4+\rk
    xor     \b0, \b0, \r0
    xor     \b1, \b1, \r1
    lw      \r0,  8+\rk
    lw      \r1, 12+\rk
    xor     \b2, \b2, \r0
    xor     \b3, \b3, \r1
    lw      \r0, 16+\rk
    lw      \r1, 20+\rk
    xor     \b4, \b4, \r0
    xor     \b5, \b5, \r1
    lw      \r0, 24+\rk
    lw      \r1, 28+\rk
    xor     \b6, \b6, \r0
    xor     \b7, \b7, \r1
.endm

/******************************************************************************
* Computes the SBox on a quarter of the internal state.
* Credits to Ko Stoffelen (see https://github.com/Ko-/riscvcrypto/).
*
* - b0-b7 contains a quarter of the state.
* - r0-r17 are temporary registers.
******************************************************************************/
.macro sbox b0,b1,b2,b3,b4,b5,b6,b7, r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17
    xor     \r0, \b3, \b5       // Exec y14 = U3 ^ U5 into r0
    xor     \r1, \b0, \b6       // Exec y13 = U0 ^ U6 into r1
    xor     \r2, \r1, \r0       // Exec y12 = y13 ^ y14 into r2
    xor     \r3, \b4, \r2       // Exec t1 = U4 ^ y12 into r3
    xor     \r4, \r3, \b5       // Exec y15 = t1 ^ U5 into r4
    and     \r5, \r2, \r4       // Exec t2 = y12 & y15 into r5
    xor     \r6, \r4, \b7       // Exec y6 = y15 ^ U7 into r6
    xor     \r7, \r3, \b1       // Exec y20 = t1 ^ U1 into r7
    xor     \r8, \b0, \b3       // Exec y9 = U0 ^ U3 into r8
    xor     \r9, \r7, \r8       // Exec y11 = y20 ^ y9 into r9
    and     \r10, \r8, \r9      // Exec t12 = y9 & y11 into r10
    xor     \r11, \b7, \r9      // Exec y7 = U7 ^ y11 into r11
    xor     \r12, \b0, \b5      // Exec y8 = U0 ^ U5 into r12
    xor     \r13, \b1, \b2      // Exec t0 = U1 ^ U2 into r13
    xor     \r14, \r4, \r13     // Exec y10 = y15 ^ t0 into r14
    xor     \r15, \r14, \r9     // Exec y17 = y10 ^ y11 into r15
    and     \r16, \r0, \r15     // Exec t13 = y14 & y17 into r16
    xor     \r17, \r16, \r10    // Exec t14 = t13 ^ t12 into r17
    xor     \b1, \r14, \r12     // Exec y19 = y10 ^ y8 into b1
    and     \b2, \r12, \r14     // Exec t15 = y8 & y10 into b2
    xor     \b2, \b2, \r10      // Exec t16 = t15 ^ t12 into b2
    xor     \b4, \r13, \r9      // Exec y16 = t0 ^ y11 into b4
    xor     \b5, \r1, \b4       // Exec y21 = y13 ^ y16 into b5
    and     \r3, \r1, \b4       // Exec t7 = y13 & y16 into r3
    xor     \r10, \b0, \b4      // Exec y18 = U0 ^ y16 into r10
    xor     \r13, \r13, \b7     // Exec y1 = t0 ^ U7 into r13
    xor     \b3, \r13, \b3      // Exec y4 = y1 ^ U3 into b3
    and     \r16, \b3, \b7      // Exec t5 = y4 & U7 into r16
    xor     \r16, \r16, \r5     // Exec t6 = t5 ^ t2 into r16
    xor     \r16, \r16, \b2     // Exec t18 = t6 ^ t16 into r16
    xor     \b1, \r16, \b1      // Exec t22 = t18 ^ y19 into b1
    xor     \b0, \r13, \b0      // Exec y2 = y1 ^ U0 into b0
    and     \r16, \b0, \r11     // Exec t10 = y2 & y7 into r16
    xor     \r16, \r16, \r3     // Exec t11 = t10 ^ t7 into r16
    xor     \b2, \r16, \b2      // Exec t20 = t11 ^ t16 into b2
    xor     \b2, \b2, \r10      // Exec t24 = t20 ^ y18 into b2
    xor     \b6, \r13, \b6      // Exec y5 = y1 ^ U6 into b6
    and     \r10, \b6, \r13     // Exec t8 = y5 & y1 into r10
    xor     \r3, \r10, \r3      // Exec t9 = t8 ^ t7 into r3
    xor     \r3, \r3, \r17      // Exec t19 = t9 ^ t14 into r3
    xor     \b5, \r3, \b5       // Exec t23 = t19 ^ y21 into b5
    xor     \r3, \b6, \r12      // Exec y3 = y5 ^ y8 into r3
    and     \r10, \r3, \r6      // Exec t3 = y3 & y6 into r10
    xor     \r5, \r10, \r5      // Exec t4 = t3 ^ t2 into r5
    xor     \r5, \r5, \r7       // Exec t17 = t4 ^ y20 into r5
    xor     \r5, \r5, \r17      // Exec t21 = t17 ^ t14 into r5
    and     \r7, \r5, \b5       // Exec t26 = t21 & t23 into r7
    xor     \r10, \b2, \r7      // Exec t27 = t24 ^ t26 into r10
    xor     \r7, \b1, \r7       // Exec t31 = t22 ^ t26 into r7
    xor     \r5, \r5, \b1       // Exec t25 = t21 ^ t22 into r5
    and     \r16, \r5, \r10     // Exec t28 = t25 & t27 into r16
    xor     \b1, \r16, \b1      // Exec t29 = t28 ^ t22 into b1
    and     \r17, \b1, \b0      // Exec z14 = t29 & y2 into r17
    and     \r11, \b1, \r11     // Exec z5 = t29 & y7 into r11
    xor     \r16, \b5, \b2      // Exec t30 = t23 ^ t24 into r16
    and     \r7, \r7, \r16      // Exec t32 = t31 & t30 into r7
    xor     \r7, \r7, \b2       // Exec t33 = t32 ^ t24 into r7
    xor     \r16, \r10, \r7     // Exec t35 = t27 ^ t33 into r16
    and     \b2, \b2, \r16      // Exec t36 = t24 & t35 into b2
    xor     \r10, \r10, \b2     // Exec t38 = t27 ^ t36 into r10
    and     \r10, \b1, \r10     // Exec t39 = t29 & t38 into r10
    xor     \r5, \r5, \r10      // Exec t40 = t25 ^ t39 into r5
    xor     \r10, \b1, \r5      // Exec t43 = t29 ^ t40 into r10
    and     \b4, \r10, \b4      // Exec z3 = t43 & y16 into b4
    xor     \r11, \b4, \r11     // Exec tc12 = z3 ^ z5 into r11
    and     \r1, \r10, \r1      // Exec z12 = t43 & y13 into r1
    and     \b6, \r5, \b6       // Exec z13 = t40 & y5 into b6
    and     \r10, \r5, \r13     // Exec z4 = t40 & y1 into r10
    xor     \b4, \b4, \r10      // Exec tc6 = z3 ^ z4 into b4
    xor     \b5, \b5, \r7       // Exec t34 = t23 ^ t33 into b5
    xor     \b2, \b2, \b5       // Exec t37 = t36 ^ t34 into b2
    xor     \b5, \r5, \b2       // Exec t41 = t40 ^ t37 into b5
    and     \r5, \b5, \r14      // Exec z8 = t41 & y10 into r5
    and     \r10, \b5, \r12     // Exec z17 = t41 & y8 into r10
    xor     \r12, \r7, \b2      // Exec t44 = t33 ^ t37 into r12
    and     \r4, \r12, \r4      // Exec z0 = t44 & y15 into r4
    and     \r2, \r12, \r2      // Exec z9 = t44 & y12 into r2
    and     \r3, \b2, \r3       // Exec z10 = t37 & y3 into r3
    and     \b2, \b2, \r6       // Exec z1 = t37 & y6 into b2
    xor     \b2, \b2, \r4       // Exec tc5 = z1 ^ z0 into b2
    xor     \r13, \b4, \b2      // Exec tc11 = tc6 ^ tc5 into r13
    and     \b3, \r7, \b3       // Exec z11 = t33 & y4 into b3
    xor     \b1, \b1, \r7       // Exec t42 = t29 ^ t33 into b1
    xor     \b5, \b1, \b5       // Exec t45 = t42 ^ t41 into b5
    and     \r6, \b5, \r15      // Exec z7 = t45 & y17 into r6
    xor     \b4, \r6, \b4       // Exec tc8 = z7 ^ tc6 into b4
    and     \r0, \b5, \r0       // Exec z16 = t45 & y14 into r0
    and     \b5, \b1, \r9       // Exec z6 = t42 & y11 into b5
    xor     \b5, \b5, \b4       // Exec tc16 = z6 ^ tc8 into b5
    and     \b1, \b1, \r8       // Exec z15 = t42 & y9 into b1
    xor     \r6, \b1, \b5       // Exec tc20 = z15 ^ tc16 into r6
    xor     \r0, \b1, \r0       // Exec tc1 = z15 ^ z16 into r0
    xor     \b1, \r3, \r0       // Exec tc2 = z10 ^ tc1 into b1
    xor     \r15, \b1, \b3      // Exec tc21 = tc2 ^ z11 into r15
    xor     \r2, \r2, \b1       // Exec tc3 = z9 ^ tc2 into r2
    xor     \b0, \r2, \b5       // Exec S0 = tc3 ^ tc16 into b0
    xor     \b3, \r2, \r13      // Exec S3 = tc3 ^ tc11 into b3
    xor     \b1, \b3, \b5       // Exec S1 = S3 ^ tc16 ^ 1 into b1   
    xor     \r0, \b6, \r0       // Exec tc13 = z13 ^ tc1 into r0
    and     \b5, \r7, \b7       // Exec z2 = t33 & U7 into b5
    xor     \r14, \r4, \b5      // Exec tc4 = z0 ^ z2 into r14
    xor     \b6, \r1, \r14      // Exec tc7 = z12 ^ tc4 into b6
    xor     \b6, \r5, \b6       // Exec tc9 = z8 ^ tc7 into b6
    xor     \b6, \b4, \b6       // Exec tc10 = tc8 ^ tc9 into b6
    xor     \b2, \r17, \b6      // Exec tc17 = z14 ^ tc10 into b2
    xor     \b5, \r15, \b2      // Exec S5 = tc21 ^ tc17 into b5
    xor     \b2, \b2, \r6       // Exec tc26 = tc17 ^ tc20 into b2
    xor     \b2, \b2, \r10      // Exec S2 = tc26 ^ z17 ^ 1 into b2
    xor     \r14, \r14, \r11    // Exec tc14 = tc4 ^ tc12 into r14
    xor     \r0, \r0, \r14      // Exec tc18 = tc13 ^ tc14 into r0
    xor     \b6, \b6, \r0       // Exec S6 = tc10 ^ tc18 ^ 1 into b6
    xor     \b7, \r1, \r0       // Exec S7 = z12 ^ tc18 ^ 1 into b7
    xor     \b4, \r14, \b3      // Exec S4 = tc14 ^ S3 into b4
.endm

/******************************************************************************
* Computes a 32-bit rotation to the right.
*
*   - out is the output register
*   - in is the input register
*   - imm is the shift index (must be an immediate value)
*   - r0, r1 are temporary registers
******************************************************************************/
.macro ror out, in, imm, r0, r1
    srli   \r0, \in, \imm
    slli   \r1, \in, 32-\imm
    or     \out, \r0, \r1
.endm

/******************************************************************************
* Computes the ShiftRows operation on the entire state.
* Only 32-bit word rotations are required thanks to the barrel-shiftrows
* representation.
*
* Requires:
*   - s0-s7 to contain state[24]...state[31].
* At the output:
*   - s0-s7 contains state[8]...state[15]
*   - s8, s10 contain state[16], state[23]
*   - s9, s11 contain state[24], state[31]
*   - the rest of the state is stored on the stack
******************************************************************************/
.macro shiftrows
    addi    sp, sp, -128
    ror     s9, s0, 24, t0, t1
    ror     s1, s1, 24, t0, t1
    ror     s2, s2, 24, t0, t1
    ror     s3, s3, 24, t0, t1
    ror     s4, s4, 24, t0, t1
    ror     s5, s5, 24, t0, t1
    ror     s6, s6, 24, t0, t1
    ror     s11, s7, 24, t0, t1
    sw      s1, 100(sp)
    sw      s2, 104(sp)
    sw      s3, 108(sp)
    sw      s4, 112(sp)
    sw      s5, 116(sp)
    sw      s6, 120(sp)
    lw      s0, 64(sp)
    lw      s1, 68(sp)
    lw      s2, 72(sp)
    lw      s3, 76(sp)
    lw      s4, 80(sp)
    lw      s5, 84(sp)
    lw      s6, 88(sp)
    lw      s7, 92(sp)
    ror     s8, s0, 16, t0, t1
    ror     s1, s1, 16, t0, t1
    ror     s2, s2, 16, t0, t1
    ror     s3, s3, 16, t0, t1
    ror     s4, s4, 16, t0, t1
    ror     s5, s5, 16, t0, t1
    ror     s6, s6, 16, t0, t1
    ror     s10, s7, 16, t0, t1
    sw      s1, 68(sp)
    sw      s2, 72(sp)
    sw      s3, 76(sp)
    sw      s4, 80(sp)
    sw      s5, 84(sp)
    sw      s6, 88(sp)
    lw      s0, 32(sp)
    lw      s1, 36(sp)
    lw      s2, 40(sp)
    lw      s3, 44(sp)
    lw      s4, 48(sp)
    lw      s5, 52(sp)
    lw      s6, 56(sp)
    lw      s7, 60(sp)
    ror     s0, s0, 8, t0, t1
    ror     s1, s1, 8, t0, t1
    ror     s2, s2, 8, t0, t1
    ror     s3, s3, 8, t0, t1
    ror     s4, s4, 8, t0, t1
    ror     s5, s5, 8, t0, t1
    ror     s6, s6, 8, t0, t1
    ror     s7, s7, 8, t0, t1
.endm

/******************************************************************************
* Computes the MixColumns operation on the entire state.
* Only XORs are required thanks to the barrel-shiftrows representation.
*
* Requires:
*   - s0-s7 to contain state[8]...state[15]
*   - s8, s10 contain state[16], state[23]
*   - s9, s11 contain state[24], state[31]
*   - the rest of the state is stored on the stack
* At the output:
*   - s0-s7 contains state[0]...state[7]
*   - the rest of the state is stored on the stack
******************************************************************************/
.macro mixcolumns
    lw      a1, 0(sp)       // a1 <- S0
    lw      a2, 4(sp)       // a2 <- S1
    lw      a3, 8(sp)       // a3 <- S2
    lw      a4, 12(sp)      // a4 <- S3
    lw      a5, 16(sp)      // a5 <- S4
    lw      a6, 20(sp)      // a6 <- S5
    lw      a7, 24(sp)      // a7 <- S6
    lw      t4, 28(sp)      // t4 <- S7
	xor 	t0, a1, s0 		// t0 <- S0 ^ S8
	xor 	t1, s0, s8 		// t1 <- S8 ^ S16
	xor 	t2, s8, s9 		// t2 <- S16 ^ S24
	xor 	t3, s9, a1 		// t3 <- S24 ^ S0
    xor     a2, s11, t4     // a2 <- S31 ^ S7 (overwrites S1)
	xor 	t4, t4, s7 		// t4 <- S7 ^ S15
	xor 	t5, s7, s10 	// t5 <- S15 ^ S23
	xor 	t6, s10, s11 	// t6 <- S23 ^ S31
	xor 	a3, t0, t6 		// a3 <- S0 ^ S8 ^ S23 ^ S31 (overwrites S2)
	xor 	s7, a3, s7 		// s7 <- S0 ^ S8 ^ S23 ^ S31 ^ S15
	lw 		a3, 28(sp) 		// load S7
	xor 	a3, a3, t6 		// a3 <- S23 ^ S31 ^ S7
	xor 	a3, a3, t1 		// a3 <- S8 ^ S16 ^ S23 ^ S31 ^ S7
	sw 		a3, 60(sp) 		// store new S15
	xor 	a3, t2, t4 		// a3 <- S16 ^ S24 ^ S7 ^ S15
	xor 	a3, a3, s11 	// a3 <- S16 ^ S24 ^ S7 ^ S15 ^ S31
	sw 		a3, 92(sp) 		// store new S23
	lw 		s11, 88(sp) 	// load S22
	xor 	a3, t3, t4 		// a3 <- S24 ^ S0 ^ S7 ^ S15
	xor 	a3, a3, s10 	// a3 <- S24 ^ S0 ^ S7 ^ S15
	sw 		a3, 124(sp) 	// store new S31
	lw 		s10, 120(sp) 	// load S30
	xor 	a3, s10, a7 	// a3 <- S30 ^ S6
    xor     t6, t6, t2      // t6 <- S23 ^ S31 ^ S16 ^ S24
    xor     t6, t6, a3      // t6 <- S23 ^ S31 ^ S16 ^ S24 ^ S30 ^ S6
    xor     t6, t6, s6      // t6 <- S23 ^ S31 ^ S16 ^ S24 ^ S30 ^ S6 ^ S14
    sw      t6, 88(sp)      // store new S22
    xor     t6, a7, s6      // t6 <- S6 ^ S14
	xor 	s10, s11, s10 	// s10 <- S22 ^ S30
	xor 	a2, a2, t3 		// a2 <- S31 ^ S7 ^ S24 ^ S0
	xor 	a2, a2, t6 		// a2 <- S31 ^ S7 ^ S24 ^ S0 ^ S6 ^ S14
	xor 	a2, a2, s11 	// a2 <- a2 ^ S22
	sw 		a2, 120(sp) 	// store new S30
	xor 	t5, t5, t1 		// t5 <- S15 ^ S23 ^ S8 ^ S16
	xor 	t5, t5, s10 	// t5 <- S15 ^ S23 ^ S8 ^ S16 ^ S22 ^ S30
	xor 	t5, t5, a7 		// t5 <- S15 ^ S23 ^ S8 ^ S16 ^ S22 ^ S30 ^ S6
	sw 		t5, 56(sp) 		// store new S14
	xor 	t4, t4, t0 		// t4 <- S7 ^ S15 ^ S0 ^ S8
	xor 	t4, t4, s10 	// t4 <- S7 ^ S15 ^ S0 ^ S8 ^ S22 ^ S30
	xor 	t5, s6, s11 	// t5 <- S14 ^ S22
	xor 	s6, t4, s6 		// s6 <- S7 ^ S15 ^ S0 ^ S8 ^ S22 ^ S30 ^ S14
	lw 		s11, 84(sp) 	// load S21
	lw 		a7, 116(sp) 	// load S29
	xor 	a2, a7, s11 	// S29 ^ S21
	xor 	t4, a6, s5 		// t4 <- S5 ^ S13
	xor 	a3, a3, t4 		// a3 <- S30 ^ S6 ^ S5 ^ S13
	xor 	a3, a3, s11 	// a3 <- a3 ^ S21
	sw 		a3, 116(sp) 	// store new S29
	xor 	a3, a7, a6 		// a3 <- S29 ^ S5
	xor 	s10, s10, a3 	// s10 <- S22 ^ S30 ^ S29 ^ S5
	xor 	s10, s10, s5 	// s10 <- S22 ^ S30 ^ S29 ^ S5 ^ S13
	sw 		s10, 84(sp)     // store new S21
	xor 	t5, t5, a2 		// t5 <- S14 ^ S22 ^ S21 ^ S29
	xor 	t5, t5, a6 		// t5 <- t5 ^ S5
	sw 		t5, 52(sp) 		// store new S13
	xor 	t5, s5, s11 	// t5 <- S13 ^ S21
	xor 	t6, t6, t5 		// a7 <- S6 ^ S14 ^ S13 ^ S21
	xor 	s5, t6, a7 		// a7 <- a7 ^ S29
	lw 		s11, 80(sp) 	// load S20
	lw 		s10, 112(sp) 	// load S28
	xor 	t6, s10, s11 	// t6 <- S28 ^ S20
	xor 	a7, s4, a5 		// a7 <- S12 ^ S4
	xor 	a3, a3, t3 		// a3 <- S29 ^ S5 ^ S24 ^ S0
	xor 	a3, a3, a7 		// a3 <- S29 ^ S5 ^ S24 ^ S0 ^ S12 ^S4
	xor 	a3, a3, s11 	// a3 <- S29 ^ S5 ^ S24 ^ S0 ^ S12 ^S4 ^ S20
	sw 		a3, 112(sp) 	// store new S28
	xor 	a3, s10, a5 	// a3 <- S28 ^ S4
	xor 	a2, a2, t2 		// a2 <- S21 ^ S29 ^ S16 ^ S24
	xor 	a2, a2, a3 		// a2 <- S21 ^ S29 ^ S16 ^ S24 ^ S28 ^ S4
	xor 	a2, a2, s4 		// a2 <- a2 ^ S12
	sw 		a2, 80(sp) 		// store new S20
	xor 	t5, t5, t1 		// t5 <- S13 ^ S21 ^ S8 ^ S16
	xor 	t5, t5, t6 		// t5 <- S13 ^ S21 ^ S8 ^ S16 ^ S20 ^ S28
	xor 	t5, t5, a5 		// t5 <- S13 ^ S21 ^ S8 ^ S16 ^ S20 ^ S28 ^ S4
	sw 		t5, 48(sp) 		// store new S12
	xor 	a6, s4, s11 	// a6 <- S12 ^ S20
	xor 	t4, t4, t0 		// t4 <- S5 ^ S13 ^ S0 ^ S8
	xor 	t4, t4, s10 	// t4 <- S5 ^ S13 ^ S0 ^ S8 ^ S28
	xor 	s4, t4, a6 		// t4 <- S5 ^ S13 ^ S0 ^ S8 ^ S28 ^ S12 ^ S20 
	lw 		s11, 76(sp) 	// load S19
	lw 		s10, 108(sp) 	// load S27
    xor     t4, s3, a4      // t4 <- S11 ^ S3
	xor 	a4, s10, a4 	// a4 <- S27 ^ S3
	xor	 	a3, a3, t3 		// a3 <- S28 ^ S4 ^ S24 ^S0
	xor	 	a3, a3, t4 		// a3 <- S28 ^ S4 ^ S24 ^S0 ^ S11 ^ S3
	xor 	a3, a3, s11 	// a3 <- S28 ^ S4 ^ S24 ^S0 ^ S11 ^ S3 ^S19
	sw 		a3, 108(sp) 	// store new S27
	xor 	t6, t6, t2 		// t6 <- S20 ^ S28 ^ S16 ^ S24
	xor 	t6, t6, t4 		// t6 <- S20 ^ S28 ^ S16 ^ S24 ^ S11 ^ S3
	xor 	t6, t6, s10 	// t6 <- S20 ^ S28 ^ S16 ^ S24 ^ S11 ^ S3 ^ S27
	sw 		t6, 76(sp) 		// store new S19
	xor 	a3, s10, s11 	// a3 <- S27 ^ S19
	xor 	a6, a6, t1 		// a6 <- S12 ^ S20 ^ S8 ^ S16
	xor 	a6, a6, a4 		// a6 <- S12 ^ S20 ^ S8 ^ S16 ^ S27 ^S3
	xor 	a6, a6, s11 	// a6 <- S12 ^ S20 ^ S8 ^ S16 ^ S27 ^S3 ^ S19
	sw 		a6, 44(sp) 		// store new S11
	xor 	a6, s11, s3 	// a6 <- S19 ^ S11
	xor 	a7, a7, t0 		// a7 <- S12 ^ S4 ^ S0 ^ S8
	xor 	a7, a7, a3 		// a7 <- S12 ^ S4 ^ S0 ^ S8 ^ S19 ^ S27
	xor 	s3, a7, s3 		// s3 <- S12 ^ S4 ^ S0 ^ S8 ^ S19 ^ S27 ^ S11
	lw 		s11, 72(sp) 	// load S18
	lw 		s10, 104(sp) 	// load S26
	lw 		a5, 8(sp) 		// load S2
	xor 	a7, s2, a5      // a7 <- S10 ^ s2
	xor 	a4, a4, a7 		// a4 <- S27 ^ S3 ^ S10 ^ S2
	xor	 	a4, a4, s11 	// a4 <- S27 ^ S3 ^ S10 ^ S2 ^ S18
	sw 		a4, 104(sp) 	// store new S26
	xor 	a4, s10, a5 	// a4 <- S26 ^ S2
	xor 	a3, a3, a4     	// a2 <- S19 ^ S27 ^ S26 ^ S2
	xor 	a3, a3, s2 		// a2 <- S19 ^ S27 ^ S26 ^ S2 ^ S10
	sw 		a3, 72(sp) 		// store new S18
	xor 	a3, s10, s11 	// a3 <- S26 ^ S18
	xor 	a6, a6, a3 		// a6 <- S11 ^ S19 ^ S26 ^ S18
	xor 	a6, a6, a5 		// a6 <- S11 ^ S19 ^ S26 ^ S18 ^ S2
	sw 		a6, 40(sp) 		// store new S10
	xor 	t5, s2, s11 	// t5 <- S10 ^ S18
	xor 	t4, t4, t5 		// t4 <- S11 ^ S3 ^ S10 ^ S18
	xor 	s2, t4, s10 	// s2 <- S11 ^ S3 ^ S10 ^ S18 ^ S26
	lw 		s11, 68(sp) 	// load S17
	lw 		s10, 100(sp) 	// load S25
	lw 		a5, 4(sp) 		// load S1
	xor 	a6, s1, a5 		// a6 <- S9 ^ S1
	xor 	a4, a4, a6 		// a4 <- S26 ^ S2 ^ S9 ^ S1
	xor 	a4, a4, s11 	// a4 <- S26 ^ S2 ^ S9 ^ S1 ^ S17
	sw 		a4, 100(sp) 	// store new S25
	xor 	t4, s10, a5 	// t4 <- S25 ^ S1
	xor 	a3, a3, t4 		// a3 <- S26 ^ S18 ^ S25 ^ S1
	xor 	a3, a3, s1 		// a3 <- S26 ^ S18 ^ S25 ^ S1 ^ S9
	sw 		a3, 68(sp) 		// store new S17
	xor 	t6, s10, s11 	// t6 <- S25 ^ S17
	xor 	t5, t5, t6 		// t5 <- S10 ^ S18 ^ S25 ^ S17
	xor 	t5, t5, a5 		// t5 <- S10 ^ S18 ^ S25 ^ S17 ^ S1
	sw 		t5, 36(sp) 		// store new S9
	xor		a2, s11, s1 	// a2 <- S17 ^ s9
	xor 	a7, a7, a2 		// a7 <- S10 ^ S2 ^ S17 ^ S9
	xor 	s1, a7, s10 	// a7 <- S10 ^ S2 ^ S17 ^ S9 ^ S25
	xor 	t4, t4, t0 		// t4 <- S25 ^ S1 ^ S8 ^ S0
	xor 	t4, t4, s8 		// t4 <- S25 ^ S1 ^ S8 ^ S0 ^ S16
	sw 		t4, 96(sp) 		// store new S24
	xor 	t6, t6, t3 		// t6 <- S25 ^ S17 ^ S24 ^ S0
	xor	 	t6, t6, s0 		// t6 <- S25 ^ S17 ^ S24 ^ S0 ^ S8
	sw 		t6, 64(sp) 		// store new S16
	xor		a2, a2, t2 		// a2 <- S17 ^ s9 ^ S24 ^ S16
	xor 	a2, a2, a1 		// a2 <- S17 ^ s9 ^ S24 ^ S16 ^ S0
	sw 		a2, 32(sp) 		// store new S8
	xor 	a6, a6, t1 		// a6 <- S9 ^ S1 ^ S8 ^ S16
	xor 	s0, a6, s9 		// a6 < - S9 ^ S1 ^ S8 ^ S16 ^ S24
.endm

/******************************************************************************
* Encrypts 8 blocks at a time using AES-128, without any operation mode.
*
* The function prototype is:
*   - void aes128_encrypt(uint8_t*, const uint8_t*, const uint32_t*)
******************************************************************************/
.globl aes128_encrypt
.type aes128_encrypt, %function
.align 2
aes128_encrypt:
    addi    sp, sp, -192                    // allocate space on the stack
    sw      ra, 60(sp)                      // save context
    sw      a1, 56(sp)                      // save context
    sw      a0, 52(sp)                      // save context
    sw      a2, 48(sp)                      // save context
    sw      s0, 44(sp)                      // save context
    sw      s1, 40(sp)                      // save context
    sw      s2, 36(sp)                      // save context
    sw      s3, 32(sp)                      // save context
    sw      s4, 28(sp)                      // save context
    sw      s5, 24(sp)                      // save context
    sw      s6, 20(sp)                      // save context
    sw      s7, 16(sp)                      // save context
    sw      s8, 12(sp)                      // save context
    sw      s9, 8(sp)                       // save context
    sw      s10, 4(sp)                      // save context
    sw      s11, 0(sp)                      // save context
    addi    sp, sp, 64                      // now points to the internal state
    addi    a5, a1, 128                     // set packing_loop_0 counter
    li      t4, 0x00ff00ff                  // mask for SWAPMOVE
packing_loop_0:                             // for(i=0; i < 8; i) 
    lw          s0, 0(a1)                   // load input word
    lw          s1, 4(a1)                   // load input word
    lw          s2, 8(a1)                   // load input word
    lw          s3, 12(a1)                  // load input word
    addi        a1, a1, 16                  // now points to the next input word
    swapmove    s0, s1, s0, s1, t4, 8, a6   // SWAPMOVE(s0, s1, 0x00ff00ff, 8)
    swapmove    s2, s3, s2, s3, t4, 8, a6   // SWAPMOVE(s2, s3, 0x00ff00ff, 8)
    sw          s0, 0(sp)                   // state[i] <- s0
    sw          s1, 32(sp)                  // state[i+8] <- s1
    sw          s2, 64(sp)                  // state[i+16] <- s2
    sw          s3, 96(sp)                  // state[i+24] <- s3
    addi        sp, sp, 4                   // i <- i+1
    bne         a1, a5, packing_loop_0      // loop until i <8
    addi        sp, sp, -32                 // i <- 0
    addi        a5, sp, 64                  // set packing_loop_1 counter
    li          t4, 0x0000ffff              // mask for SWAPMOVE
packing_loop_1:                             // for(i = 0; i < 16; i) 
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 64(sp)                  // load state[i+16]
    swapmove    s0, s1, s0, s1, t4, 16, a6  // SWAPMOVE(s0, s1, 0x0000ffff, 16)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 64(sp)                  // store state[i+16]
    addi        sp, sp, 4                   // i <- i + 1
    bne         sp, a5, packing_loop_1      // loop until i < 16
    li          t4, 0x55555555              // mask for SWAPMOVE
    li          t5, 0x33333333              // mask for SWAPMOVE
    li          t6, 0x0f0f0f0f              // mask for SWAPMOVE
    addi        sp, sp, 32                  // points to state[24]
    addi        a5, sp, -128                // set packing_loop_2 counter
packing_loop_2:                             // for(i = 24; i >= 0; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
    swapmove    s1, s0, s1, s0, t4, 1, a6   // SWAPMOVE(s1, s0, 0x55555555, 1)
    swapmove    s3, s2, s3, s2, t4, 1, a6   // SWAPMOVE(s3, s2, 0x55555555, 1)
    swapmove    s5, s4, s5, s4, t4, 1, a6   // SWAPMOVE(s5, s4, 0x55555555, 1)
    swapmove    s7, s6, s7, s6, t4, 1, a6   // SWAPMOVE(s7, s6, 0x55555555, 1)
    swapmove    s2, s0, s2, s0, t5, 2, a6   // SWAPMOVE(s2, s0, 0x33333333, 2)
    swapmove    s3, s1, s3, s1, t5, 2, a6   // SWAPMOVE(s3, s1, 0x33333333, 2)
    swapmove    s6, s4, s6, s4, t5, 2, a6   // SWAPMOVE(s6, s4, 0x33333333, 2)
    swapmove    s7, s5, s7, s5, t5, 2, a6   // SWAPMOVE(s7, s5, 0x33333333, 2)
    swapmove    s4, s0, s4, s0, t6, 4, a6   // SWAPMOVE(s4, s0, 0x0f0f0f0f, 4)
    swapmove    s5, s1, s5, s1, t6, 4, a6   // SWAPMOVE(s5, s1, 0x0f0f0f0f, 4)
    swapmove    s6, s2, s6, s2, t6, 4, a6   // SWAPMOVE(s6, s2, 0x0f0f0f0f, 4)
    swapmove    s7, s3, s7, s3, t6, 4, a6   // SWAPMOVE(s7, s3, 0x0f0f0f0f, 4)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 4(sp)                   // store state[i+1]
    sw          s2, 8(sp)                   // store state[i+2]
    sw          s3, 12(sp)                  // store state[i+3]
    sw          s4, 16(sp)                  // store state[i+4]
    sw          s5, 20(sp)                  // store state[i+5]
    sw          s6, 24(sp)                  // store state[i+6]
    sw          s7, 28(sp)                  // store state[i+7]
    addi        sp, sp, -32                 // i <- i - 8
    bne         sp, a5, packing_loop_2      // loop until i >= 0
    addi        sp, sp, 32                  // now points to state[0]
    addi        ra, zero, 40                // set main loop counter
    xor         a0, a2, zero                // put the rkeys address in a0
aes128_addroundkey_sbox:                    // for(j = 40; j > 0; j)
    addi        ra, ra, -1                  // j <- j - 1
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7,0(a0), t0,t1
    addi        a0, a0, 32                  // points to the next rkey
    sbox        s0,s1,s2,s3,s4,s5,s6,s7, t0,t1,t2,t3,t4,t5,t6,a1,a2,a3,a4,a5,a6,a7,s8,s9,s10,s11
    addi        sp, sp, 32                  // i <- i + 8
    andi        s11, ra, 3                  // if(j % 4 == 0)
    beqz        s11, aes128_linear_layer    // then jump to the linear layer
    sw          s0, -32(sp)                 // store state[i-8]
    sw          s1, -28(sp)                 // store state[i-7]
    sw          s2, -24(sp)                 // store state[i-6]
    sw          s3, -20(sp)                 // store state[i-5]
    sw          s4, -16(sp)                 // store state[i-4]
    sw          s5, -12(sp)                 // store state[i-3]
    sw          s6, -8(sp)                  // store state[i-2]
    sw          s7, -4(sp)                  // store state[i-1]
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
    j           aes128_addroundkey_sbox     // ark and sbox on the rest of the state
aes128_linear_layer:
    shiftrows                               // shiftrows on the entire state
    beqz         ra, unpacking              // omit mixcolumns during last round
    mixcolumns                              // mixcolumns on the entire state
    j           aes128_addroundkey_sbox     // go to next round
unpacking:
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 32(a0), t0,t1
    sw          s0, 32(sp)                  // store state[8] after last addroundkey
    sw          s1, 36(sp)                  // store state[9] after last addroundkey
    sw          s2, 40(sp)                  // store state[10] after last addroundkey
    sw          s3, 44(sp)                  // store state[11] after last addroundkey
    sw          s4, 48(sp)                  // store state[12] after last addroundkey
    sw          s5, 52(sp)                  // store state[13] after last addroundkey
    sw          s6, 56(sp)                  // store state[14] after last addroundkey
    sw          s7, 60(sp)                  // store state[15] after last addroundkey
    lw          s1, 68(sp)                  // load state[17]
    lw          s2, 72(sp)                  // load state[18]
    lw          s3, 76(sp)                  // load state[19]
    lw          s4, 80(sp)                  // load state[20]
    lw          s5, 84(sp)                  // load state[21]
    lw          s6, 88(sp)                  // load state[22]
    addroundkey s8,s1,s2,s3,s4,s5,s6,s10, 64(a0), t0,t1
    sw          s8, 64(sp)                  // store state[16] after last addroundkey
    sw          s1, 68(sp)                  // store state[17] after last addroundkey
    sw          s2, 72(sp)                  // store state[18] after last addroundkey
    sw          s3, 76(sp)                  // store state[19] after last addroundkey
    sw          s4, 80(sp)                  // store state[20] after last addroundkey
    sw          s5, 84(sp)                  // store state[21] after last addroundkey
    sw          s6, 88(sp)                  // store state[22] after last addroundkey
    sw          s10, 92(sp)                 // store state[23] after last addroundkey
    lw          s1, 100(sp)                 // load state[25]
    lw          s2, 104(sp)                 // load state[26]
    lw          s3, 108(sp)                 // load state[27]
    lw          s4, 112(sp)                 // load state[28]
    lw          s5, 116(sp)                 // load state[29]
    lw          s6, 120(sp)                 // load state[30]
    addroundkey s9,s1,s2,s3,s4,s5,s6,s11, 96(a0), t0,t1
    sw          s9, 96(sp)                  // store state[24] after last addroundkey
    sw          s1, 100(sp)                 // store state[25] after last addroundkey
    sw          s2, 104(sp)                 // store state[26] after last addroundkey
    sw          s3, 108(sp)                 // store state[27] after last addroundkey
    sw          s4, 112(sp)                 // store state[28] after last addroundkey
    sw          s5, 116(sp)                 // store state[29] after last addroundkey
    sw          s6, 120(sp)                 // store state[30] after last addroundkey
    sw          s11, 124(sp)                // store state[31] after last addroundkey
    lw          s0, 0(sp)                   // load state[0]
    lw          s1, 4(sp)                   // load state[1]
    lw          s2, 8(sp)                   // load state[2]
    lw          s3, 12(sp)                  // load state[3]
    lw          s4, 16(sp)                  // load state[4]
    lw          s5, 20(sp)                  // load state[5]
    lw          s6, 24(sp)                  // load state[6]
    lw          s7, 28(sp)                  // load state[7]
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), t0,t1
    li          t4, 0x55555555              // mask for SWAPMOVE
    li          t5, 0x33333333              // mask for SWAPMOVE
    li          t6, 0x0f0f0f0f              // mask for SWAPMOVE
    addi        a5, sp, 128                 // set unpacking_loop_2_bis counter
    j           unpacking_loop_2_bis        // state[0...7] already in s0-s7, no need loads
unpacking_loop_2:                           // for(i = 0; i < 32; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
unpacking_loop_2_bis:
    swapmove    s4, s0, s4, s0, t6, 4, a6   // SWAPMOVE(s4, s0, 0x0f0f0f0f, 4)
    swapmove    s5, s1, s5, s1, t6, 4, a6   // SWAPMOVE(s5, s1, 0x0f0f0f0f, 4)
    swapmove    s6, s2, s6, s2, t6, 4, a6   // SWAPMOVE(s6, s2, 0x0f0f0f0f, 4)
    swapmove    s7, s3, s7, s3, t6, 4, a6   // SWAPMOVE(s7, s3, 0x0f0f0f0f, 4)
    swapmove    s2, s0, s2, s0, t5, 2, a6   // SWAPMOVE(s2, s0, 0x33333333, 2)
    swapmove    s3, s1, s3, s1, t5, 2, a6   // SWAPMOVE(s3, s1, 0x33333333, 2)
    swapmove    s6, s4, s6, s4, t5, 2, a6   // SWAPMOVE(s6, s4, 0x33333333, 2)
    swapmove    s7, s5, s7, s5, t5, 2, a6   // SWAPMOVE(s7, s5, 0x33333333, 2)
    swapmove    s1, s0, s1, s0, t4, 1, a6   // SWAPMOVE(s1, s0, 0x55555555, 1)
    swapmove    s3, s2, s3, s2, t4, 1, a6   // SWAPMOVE(s3, s2, 0x55555555, 1)
    swapmove    s5, s4, s5, s4, t4, 1, a6   // SWAPMOVE(s5, s4, 0x55555555, 1)
    swapmove    s7, s6, s7, s6, t4, 1, a6   // SWAPMOVE(s7, s6, 0x55555555, 1)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 4(sp)                   // store state[i+1]
    sw          s2, 8(sp)                   // store state[i+2]
    sw          s3, 12(sp)                  // store state[i+3]
    sw          s4, 16(sp)                  // store state[i+4]
    sw          s5, 20(sp)                  // store state[i+5]
    sw          s6, 24(sp)                  // store state[i+6]
    sw          s7, 28(sp)                  // store state[i+7]
    addi        sp, sp, 32                  // i <- i + 8
    bne         sp, a5, unpacking_loop_2    // loop until i < 32
    addi        sp, sp, -128                // points to state[0]
    addi        a5, sp, 64                  // set unpacking_loop_1 counter
    li          t4, 0x0000ffff              // mask for SWAPMOVE
unpacking_loop_1:                           // for(i = 0; i < 16; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 64(sp)                  // load state[i+16]
    swapmove    s0, s1, s0, s1, t4, 16, a6  // SWAPMOVE(s0, s1, 0x0000ffff, 16)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 64(sp)                  // store state[i+16]
    addi        sp, sp, 4                   // i <- i + 1
    bne         sp, a5, unpacking_loop_1    // loop until i < 16
    addi        sp, sp, -64                 // points to state[0]
    lw          a0, -12(sp)                 // restore output address      
    addi        a5, sp, 32                  // set unpacking_loop_0 counter
    li          t4, 0x00ff00ff              // mask for SWAPMOVE
unpacking_loop_0:                           // for (i = 0; i < 8; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 32(sp)                  // load state[i+8]
    lw          s2, 64(sp)                  // load state[i+16]
    lw          s3, 96(sp)                  // load state[i+24]
    addi        sp, sp, 4                   // i <- i + 1
    swapmove    s0, s1, s0, s1, t4, 8, a6   // SWAPMOVE(s0, s1, 0x00ff00ff, 8) 
    swapmove    s2, s3, s2, s3, t4, 8, a6   // SWAPMOVE(s2, s3, 0x00ff00ff, 8) 
    sw          s0, 0(a0)                   // store state[i] in output array
    sw          s1, 4(a0)                   // store state[i+8] in output array
    sw          s2, 8(a0)                   // store state[i+16] in output array
    sw          s3, 12(a0)                  // store state[i+24] in output array
    addi        a0, a0, 16                  // increments output array address
    bne         sp, a5, unpacking_loop_0    // loop until i < 8
    addi        sp, sp, -96                 // now points at the bottom of the stack
    lw          ra, 60(sp)                  // restore context
    lw          a0, 52(sp)                  // restore context
    lw          a1, 56(sp)                  // restore context
    lw          a2, 48(sp)                  // restore context
    lw          s0, 44(sp)                  // restore context
    lw          s1, 40(sp)                  // restore context
    lw          s2, 36(sp)                  // restore context
    lw          s3, 32(sp)                  // restore context
    lw          s4, 28(sp)                  // restore context
    lw          s5, 24(sp)                  // restore context
    lw          s6, 20(sp)                  // restore context
    lw          s7, 16(sp)                  // restore context
    lw          s8, 12(sp)                  // restore context
    lw          s9, 8(sp)                   // restore context
    lw          s10, 4(sp)                  // restore context
    lw          s11, 0(sp)                  // restore context
    addi        sp, sp, 192                 // restore stack pointer
    ret                                     // exit function
.size aes128_encrypt,.-aes128_encrypt

/******************************************************************************
* Encrypts 8 blocks at a time using AES-256, without any operation mode.
*
* The function prototype is:
*   - void aes256_encrypt(uint8_t*, const uint8_t*, const uint32_t*)
******************************************************************************/
.globl aes256_encrypt
.type aes256_encrypt, %function
.align 2
aes256_encrypt:
    addi    sp, sp, -192                    // allocate space on the stack
    sw      ra, 60(sp)                      // save context
    sw      a1, 56(sp)                      // save context
    sw      a0, 52(sp)                      // save context
    sw      a2, 48(sp)                      // save context
    sw      s0, 44(sp)                      // save context
    sw      s1, 40(sp)                      // save context
    sw      s2, 36(sp)                      // save context
    sw      s3, 32(sp)                      // save context
    sw      s4, 28(sp)                      // save context
    sw      s5, 24(sp)                      // save context
    sw      s6, 20(sp)                      // save context
    sw      s7, 16(sp)                      // save context
    sw      s8, 12(sp)                      // save context
    sw      s9, 8(sp)                       // save context
    sw      s10, 4(sp)                      // save context
    sw      s11, 0(sp)                      // save context
    addi    sp, sp, 64                      // now points to the internal state
    addi    a5, a1, 128                     // set packing_loop_0 counter
    li      t4, 0x00ff00ff                  // mask for SWAPMOVE
aes256_packing_loop0:                       // for(i=0; i < 8; i) 
    lw          s0, 0(a1)                   // load input word
    lw          s1, 4(a1)                   // load input word
    lw          s2, 8(a1)                   // load input word
    lw          s3, 12(a1)                  // load input word
    addi        a1, a1, 16                  // now points to the next input word
    swapmove    s0, s1, s0, s1, t4, 8, a6   // SWAPMOVE(s0, s1, 0x00ff00ff, 8)
    swapmove    s2, s3, s2, s3, t4, 8, a6   // SWAPMOVE(s2, s3, 0x00ff00ff, 8)
    sw          s0, 0(sp)                   // state[i] <- s0
    sw          s1, 32(sp)                  // state[i+8] <- s1
    sw          s2, 64(sp)                  // state[i+16] <- s2
    sw          s3, 96(sp)                  // state[i+24] <- s3
    addi        sp, sp, 4                   // i <- i+1
    bne         a1, a5, aes256_packing_loop0// loop until i <8
    addi        sp, sp, -32                 // i <- 0
    addi        a5, sp, 64                  // set packing_loop_1 counter
    li          t4, 0x0000ffff              // mask for SWAPMOVE
aes256_packing_loop1:                       // for(i = 0; i < 16; i) 
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 64(sp)                  // load state[i+16]
    swapmove    s0, s1, s0, s1, t4, 16, a6  // SWAPMOVE(s0, s1, 0x0000ffff, 16)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 64(sp)                  // store state[i+16]
    addi        sp, sp, 4                   // i <- i + 1
    bne         sp, a5, aes256_packing_loop1// loop until i < 16
    li          t4, 0x55555555              // mask for SWAPMOVE
    li          t5, 0x33333333              // mask for SWAPMOVE
    li          t6, 0x0f0f0f0f              // mask for SWAPMOVE
    addi        sp, sp, 32                  // points to state[24]
    addi        a5, sp, -128                // set packing_loop_2 counter
aes256_packing_loop2:                       // for(i = 24; i >= 0; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
    swapmove    s1, s0, s1, s0, t4, 1, a6   // SWAPMOVE(s1, s0, 0x55555555, 1)
    swapmove    s3, s2, s3, s2, t4, 1, a6   // SWAPMOVE(s3, s2, 0x55555555, 1)
    swapmove    s5, s4, s5, s4, t4, 1, a6   // SWAPMOVE(s5, s4, 0x55555555, 1)
    swapmove    s7, s6, s7, s6, t4, 1, a6   // SWAPMOVE(s7, s6, 0x55555555, 1)
    swapmove    s2, s0, s2, s0, t5, 2, a6   // SWAPMOVE(s2, s0, 0x33333333, 2)
    swapmove    s3, s1, s3, s1, t5, 2, a6   // SWAPMOVE(s3, s1, 0x33333333, 2)
    swapmove    s6, s4, s6, s4, t5, 2, a6   // SWAPMOVE(s6, s4, 0x33333333, 2)
    swapmove    s7, s5, s7, s5, t5, 2, a6   // SWAPMOVE(s7, s5, 0x33333333, 2)
    swapmove    s4, s0, s4, s0, t6, 4, a6   // SWAPMOVE(s4, s0, 0x0f0f0f0f, 4)
    swapmove    s5, s1, s5, s1, t6, 4, a6   // SWAPMOVE(s5, s1, 0x0f0f0f0f, 4)
    swapmove    s6, s2, s6, s2, t6, 4, a6   // SWAPMOVE(s6, s2, 0x0f0f0f0f, 4)
    swapmove    s7, s3, s7, s3, t6, 4, a6   // SWAPMOVE(s7, s3, 0x0f0f0f0f, 4)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 4(sp)                   // store state[i+1]
    sw          s2, 8(sp)                   // store state[i+2]
    sw          s3, 12(sp)                  // store state[i+3]
    sw          s4, 16(sp)                  // store state[i+4]
    sw          s5, 20(sp)                  // store state[i+5]
    sw          s6, 24(sp)                  // store state[i+6]
    sw          s7, 28(sp)                  // store state[i+7]
    addi        sp, sp, -32                 // i <- i - 8
    bne         sp, a5, aes256_packing_loop2// loop until i >= 0
    addi        sp, sp, 32                  // now points to state[0]
    addi        ra, zero, 56                // set main loop counter
    xor         a0, a2, zero                // put the rkeys address in a0
aes256_addroundkey_sbox:                    // for(j = 56; j >0; j)
    addi        ra, ra, -1                  // j <- j - 1
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7,0(a0), t0,t1
    addi        a0, a0, 32                  // points to the next rkey
    sbox        s0,s1,s2,s3,s4,s5,s6,s7, t0,t1,t2,t3,t4,t5,t6,a1,a2,a3,a4,a5,a6,a7,s8,s9,s10,s11
    addi        sp, sp, 32                  // i <- i + 8
    andi        s11, ra, 3                  // if(j % 4 == 0)
    beqz        s11, aes256_linear_layer    // then jump to the linear layer
    sw          s0, -32(sp)                 // store state[i-8]
    sw          s1, -28(sp)                 // store state[i-7]
    sw          s2, -24(sp)                 // store state[i-6]
    sw          s3, -20(sp)                 // store state[i-5]
    sw          s4, -16(sp)                 // store state[i-4]
    sw          s5, -12(sp)                 // store state[i-3]
    sw          s6, -8(sp)                  // store state[i-2]
    sw          s7, -4(sp)                  // store state[i-1]
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
    j           aes256_addroundkey_sbox     // ark and sbox on the rest of the state
aes256_linear_layer:
    shiftrows                               // shiftrows on the entire state
    beqz         ra, aes256_unpacking       // omit mixcolumns during last round
    mixcolumns                              // mixcolumns on the entire state
    j           aes256_addroundkey_sbox     // go to next round
aes256_unpacking:
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 32(a0), t0,t1
    sw          s0, 32(sp)                  // store state[8] after last addroundkey
    sw          s1, 36(sp)                  // store state[9] after last addroundkey
    sw          s2, 40(sp)                  // store state[10] after last addroundkey
    sw          s3, 44(sp)                  // store state[11] after last addroundkey
    sw          s4, 48(sp)                  // store state[12] after last addroundkey
    sw          s5, 52(sp)                  // store state[13] after last addroundkey
    sw          s6, 56(sp)                  // store state[14] after last addroundkey
    sw          s7, 60(sp)                  // store state[15] after last addroundkey
    lw          s1, 68(sp)                  // load state[17]
    lw          s2, 72(sp)                  // load state[18]
    lw          s3, 76(sp)                  // load state[19]
    lw          s4, 80(sp)                  // load state[20]
    lw          s5, 84(sp)                  // load state[21]
    lw          s6, 88(sp)                  // load state[22]
    addroundkey s8,s1,s2,s3,s4,s5,s6,s10, 64(a0), t0,t1
    sw          s8, 64(sp)                  // store state[16] after last addroundkey
    sw          s1, 68(sp)                  // store state[17] after last addroundkey
    sw          s2, 72(sp)                  // store state[18] after last addroundkey
    sw          s3, 76(sp)                  // store state[19] after last addroundkey
    sw          s4, 80(sp)                  // store state[20] after last addroundkey
    sw          s5, 84(sp)                  // store state[21] after last addroundkey
    sw          s6, 88(sp)                  // store state[22] after last addroundkey
    sw          s10, 92(sp)                 // store state[23] after last addroundkey
    lw          s1, 100(sp)                 // load state[25]
    lw          s2, 104(sp)                 // load state[26]
    lw          s3, 108(sp)                 // load state[27]
    lw          s4, 112(sp)                 // load state[28]
    lw          s5, 116(sp)                 // load state[29]
    lw          s6, 120(sp)                 // load state[30]
    addroundkey s9,s1,s2,s3,s4,s5,s6,s11, 96(a0), t0,t1
    sw          s9, 96(sp)                  // store state[24] after last addroundkey
    sw          s1, 100(sp)                 // store state[25] after last addroundkey
    sw          s2, 104(sp)                 // store state[26] after last addroundkey
    sw          s3, 108(sp)                 // store state[27] after last addroundkey
    sw          s4, 112(sp)                 // store state[28] after last addroundkey
    sw          s5, 116(sp)                 // store state[29] after last addroundkey
    sw          s6, 120(sp)                 // store state[30] after last addroundkey
    sw          s11, 124(sp)                // store state[31] after last addroundkey
    lw          s0, 0(sp)                   // load state[0]
    lw          s1, 4(sp)                   // load state[1]
    lw          s2, 8(sp)                   // load state[2]
    lw          s3, 12(sp)                  // load state[3]
    lw          s4, 16(sp)                  // load state[4]
    lw          s5, 20(sp)                  // load state[5]
    lw          s6, 24(sp)                  // load state[6]
    lw          s7, 28(sp)                  // load state[7]
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), t0,t1
    li          t4, 0x55555555              // mask for SWAPMOVE
    li          t5, 0x33333333              // mask for SWAPMOVE
    li          t6, 0x0f0f0f0f              // mask for SWAPMOVE
    addi        a5, sp, 128                 // set unpacking_loop_2_bis counter
    j           aes256_unpacking_loop2_bis  // state[0...7] already in s0-s7, no need loads
aes256_unpacking_loop2:                     // for(i = 0; i < 32; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 4(sp)                   // load state[i+1]
    lw          s2, 8(sp)                   // load state[i+2]
    lw          s3, 12(sp)                  // load state[i+3]
    lw          s4, 16(sp)                  // load state[i+4]
    lw          s5, 20(sp)                  // load state[i+5]
    lw          s6, 24(sp)                  // load state[i+6]
    lw          s7, 28(sp)                  // load state[i+7]
aes256_unpacking_loop2_bis:
    swapmove    s4, s0, s4, s0, t6, 4, a6   // SWAPMOVE(s4, s0, 0x0f0f0f0f, 4)
    swapmove    s5, s1, s5, s1, t6, 4, a6   // SWAPMOVE(s5, s1, 0x0f0f0f0f, 4)
    swapmove    s6, s2, s6, s2, t6, 4, a6   // SWAPMOVE(s6, s2, 0x0f0f0f0f, 4)
    swapmove    s7, s3, s7, s3, t6, 4, a6   // SWAPMOVE(s7, s3, 0x0f0f0f0f, 4)
    swapmove    s2, s0, s2, s0, t5, 2, a6   // SWAPMOVE(s2, s0, 0x33333333, 2)
    swapmove    s3, s1, s3, s1, t5, 2, a6   // SWAPMOVE(s3, s1, 0x33333333, 2)
    swapmove    s6, s4, s6, s4, t5, 2, a6   // SWAPMOVE(s6, s4, 0x33333333, 2)
    swapmove    s7, s5, s7, s5, t5, 2, a6   // SWAPMOVE(s7, s5, 0x33333333, 2)
    swapmove    s1, s0, s1, s0, t4, 1, a6   // SWAPMOVE(s1, s0, 0x55555555, 1)
    swapmove    s3, s2, s3, s2, t4, 1, a6   // SWAPMOVE(s3, s2, 0x55555555, 1)
    swapmove    s5, s4, s5, s4, t4, 1, a6   // SWAPMOVE(s5, s4, 0x55555555, 1)
    swapmove    s7, s6, s7, s6, t4, 1, a6   // SWAPMOVE(s7, s6, 0x55555555, 1)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 4(sp)                   // store state[i+1]
    sw          s2, 8(sp)                   // store state[i+2]
    sw          s3, 12(sp)                  // store state[i+3]
    sw          s4, 16(sp)                  // store state[i+4]
    sw          s5, 20(sp)                  // store state[i+5]
    sw          s6, 24(sp)                  // store state[i+6]
    sw          s7, 28(sp)                  // store state[i+7]
    addi        sp, sp, 32                  // i <- i + 8
    bne         sp,a5,aes256_unpacking_loop2// loop until i < 32
    addi        sp, sp, -128                // points to state[0]
    addi        a5, sp, 64                  // set unpacking_loop_1 counter
    li          t4, 0x0000ffff              // mask for SWAPMOVE
aes256_unpacking_loop1:                     // for(i = 0; i < 16; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 64(sp)                  // load state[i+16]
    swapmove    s0, s1, s0, s1, t4, 16, a6  // SWAPMOVE(s0, s1, 0x0000ffff, 16)
    sw          s0, 0(sp)                   // store state[i]
    sw          s1, 64(sp)                  // store state[i+16]
    addi        sp, sp, 4                   // i <- i + 1
    bne         sp,a5,aes256_unpacking_loop1// loop until i < 16
    addi        sp, sp, -64                 // points to state[0]
    lw          a0, -12(sp)                 // restore output address      
    addi        a5, sp, 32                  // set unpacking_loop_0 counter
    li          t4, 0x00ff00ff              // mask for SWAPMOVE
aes256_unpacking_loop0:                     // for (i = 0; i < 8; i)
    lw          s0, 0(sp)                   // load state[i]
    lw          s1, 32(sp)                  // load state[i+8]
    lw          s2, 64(sp)                  // load state[i+16]
    lw          s3, 96(sp)                  // load state[i+24]
    addi        sp, sp, 4                   // i <- i + 1
    swapmove    s0, s1, s0, s1, t4, 8, a6   // SWAPMOVE(s0, s1, 0x00ff00ff, 8) 
    swapmove    s2, s3, s2, s3, t4, 8, a6   // SWAPMOVE(s2, s3, 0x00ff00ff, 8) 
    sw          s0, 0(a0)                   // store state[i] in output array
    sw          s1, 4(a0)                   // store state[i+8] in output array
    sw          s2, 8(a0)                   // store state[i+16] in output array
    sw          s3, 12(a0)                  // store state[i+24] in output array
    addi        a0, a0, 16                  // increments output array address
    bne         sp,a5,aes256_unpacking_loop0// loop until i < 8
    addi        sp, sp, -96                 // now points at the bottom of the stack
    lw          ra, 60(sp)                  // restore context
    lw          a0, 52(sp)                  // restore context
    lw          a1, 56(sp)                  // restore context
    lw          a2, 48(sp)                  // restore context
    lw          s0, 44(sp)                  // restore context
    lw          s1, 40(sp)                  // restore context
    lw          s2, 36(sp)                  // restore context
    lw          s3, 32(sp)                  // restore context
    lw          s4, 28(sp)                  // restore context
    lw          s5, 24(sp)                  // restore context
    lw          s6, 20(sp)                  // restore context
    lw          s7, 16(sp)                  // restore context
    lw          s8, 12(sp)                  // restore context
    lw          s9, 8(sp)                   // restore context
    lw          s10, 4(sp)                  // restore context
    lw          s11, 0(sp)                  // restore context
    addi        sp, sp, 192                 // restore stack pointer
    ret                                     // exit function
.size aes256_encrypt,.-aes256_encrypt
