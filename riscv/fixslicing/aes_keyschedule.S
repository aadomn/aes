/******************************************************************************
* RV32I assembly implementations of the AES-128 and AES-256 key schedule
* according to fixslicing.
* Note that those implementations are fully bitsliced and do not rely on any
* Look-Up Table (LUT).
*
* See the paper "Fixslicing AES-like Ciphers" at https:// for more details.
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
* Parameters:
* 	- out0-out1		output registers
* 	- in0-in1 		input registers
* 	- mask 			mask
* 	- c0  			shift value (must be an immediate value)
* 	- tmp 			temporary register
******************************************************************************/
.macro swapmove out0,out1, in0,in1, mask, imm, tmp
    srli   \tmp, \in0, \imm
    xor    \tmp, \tmp, \in1
    and    \tmp, \tmp, \mask
    xor    \out1, \in1, \tmp
    slli   \tmp, \tmp, \imm
    xor    \out0, \in0, \tmp
.endm

/******************************************************************************
* Computes a 32-bit rotation to the right.
*
* Parameters:
*   - out       output register
*   - in        input register
*   - imm       rotation value (must be an immediate value)
*   - tmp0-1    temporary registers
******************************************************************************/
.macro rori out, in, imm, tmp0, tmp1
    srli   \tmp0, \in, \imm
    slli   \tmp1, \in, 32-\imm
    or     \out, \tmp0, \tmp1
.endm

/******************************************************************************
* Store the round keys in the corresponding array.
*
* Parameters:
* - rk0-rk7 are the round key words
* - addr is the address of the round keys array
******************************************************************************/
.macro store_rkey r0, r1, r2, r3, r4, r5, r6, r7, addr
    sw      \r0, 0+\addr
    sw      \r1, 4+\addr
    sw      \r2, 8+\addr
    sw      \r3, 12+\addr
    sw      \r4, 16+\addr
    sw      \r5, 20+\addr
    sw      \r6, 24+\addr
    sw      \r7, 28+\addr
.endm

/******************************************************************************
* Applies NOT to the round keys to save some cycles during Sbox calculations.
*
* Parameters:
* - rk0-rk7 are the round key words
* - addr is the address of the round keys array
******************************************************************************/
.macro store_not_rkey r0, r1, r2, r3, r4, r5, r6, r7, addr
	not 	\r1, \r1 						// NOT omitted in sbox
	not 	\r2, \r2 						// NOT omitted in sbox
	not 	\r6, \r6 						// NOT omitted in sbox
	not 	\r7, \r7 						// NOT omitted in sbox
    sw      \r0, 0+\addr
    sw      \r1, 4+\addr
    sw      \r2, 8+\addr
    sw      \r3, 12+\addr
    sw      \r4, 16+\addr
    sw      \r5, 20+\addr
    sw      \r6, 24+\addr
    sw      \r7, 28+\addr
.endm

/******************************************************************************
* Packing routine. Note that it is the same as the one used in the encryption
* function so some code size could be saved by merging the two files.
******************************************************************************/
.macro packing
    swapmove    s1, s0, s1, s0, t0, 1, s8
    swapmove    s3, s2, s3, s2, t0, 1, s8
    swapmove    s5, s4, s5, s4, t0, 1, s8
    swapmove    s7, s6, s7, s6, t0, 1, s8
    swapmove    s2, s0, s2, s0, t1, 2, s8
    swapmove    s3, s1, s3, s1, t1, 2, s8
    swapmove    s6, s4, s6, s4, t1, 2, s8
    swapmove    s7, s5, s7, s5, t1, 2, s8
    swapmove    s4, s0, s4, s0, t2, 4, s8
    swapmove    s5, s1, s5, s1, t2, 4, s8
    swapmove    s6, s2, s6, s2, t2, 4, s8
    swapmove    s7, s3, s7, s3, t2, 4, s8
.endm

/******************************************************************************
* Subroutine that computes S-box. Note that the same code is used in the
* encryption function, so some code size could be saved by merging the 2 files.
* Credits to https://github.com/Ko-/riscvcrypto.
******************************************************************************/
sbox:
    xor     t0, s3, s5                  // Exec y14 = U3 ^ U5 into r0
    xor     t1, s0, s6                  // Execy13 = U0 ^ U6 into r1
    xor     t2, t1, t0                  // Execy12 = y13 ^ y14 into r2
    xor     t3, s4, t2                  // Exect1 = U4 ^ y12 into r3
    xor     t4, t3, s5                  // Execy15 = t1 ^ U5 into r4
    and     t5, t2, t4                  // Exect2 = y12 & y15 into r5
    xor     t6, t4, s7                  // Execy6 = y15 ^ U7 into r6
    xor     a1, t3, s1                  // Execy20 = t1 ^ U1 into r7
    xor     a2, s0, s3                  // Execy9 = U0 ^ U3 into r8
    xor     a3, a1, a2                  // Execy11 = y20 ^ y9 into r9
    and     a4, a2, a3                  // Exec t12 = y9 & y11 into r10
    xor     a5, s7, a3                  // Exec y7 = U7 ^ y11 into r11
    xor     a6, s0, s5                  // Exec y8 = U0 ^ U5 into r12
    xor     a7, s1, s2                  // Exec t0 = U1 ^ U2 into r13
    xor     s8, t4, a7                  // Exec y10 = y15 ^ t0 into r14
    xor     s9, s8, a3                  // Exec y17 = y10 ^ y11 into r15
    and     s10, t0, s9                 // Exec t13 = y14 & y17 into r16
    xor     s11, s10, a4                // Exec t14 = t13 ^ t12 into r17
    xor     s1, s8, a6                  // Exec y19 = y10 ^ y8 into b1
    and     s2, a6, s8                  // Exec t15 = y8 & y10 into b2
    xor     s2, s2, a4                  // Exec t16 = t15 ^ t12 into b2
    xor     s4, a7, a3                  // Exec y16 = t0 ^ y11 into b4
    xor     s5, t1, s4                  // Execy21 = y13 ^ y16 into b5
    and     t3, t1, s4                  // Exect7 = y13 & y16 into r3
    xor     a4, s0, s4                  // Exec y18 = U0 ^ y16 into r10
    xor     a7, a7, s7                  // Exec y1 = t0 ^ U7 into r13
    xor     s3, a7, s3                  // Exec y4 = y1 ^ U3 into b3
    and     s10, s3, s7                 // Exec t5 = y4 & U7 into r16
    xor     s10, s10, t5                // Exec t6 = t5 ^ t2 into r16
    xor     s10, s10, s2                // Exec t18 = t6 ^ t16 into r16
    xor     s1, s10, s1                 // Exec t22 = t18 ^ y19 into b1
    xor     s0, a7, s0                  // Exec y2 = y1 ^ U0 into b0
    and     s10, s0, a5                 // Exec t10 = y2 & y7 into r16
    xor     s10, s10, t3                // Exec t11 = t10 ^ t7 into r16
    xor     s2, s10, s2                 // Exec t20 = t11 ^ t16 into b2
    xor     s2, s2, a4                  // Exec t24 = t20 ^ y18 into b2
    xor     s6, a7, s6                  // Exec y5 = y1 ^ U6 into b6
    and     a4, s6, a7                  // Exec t8 = y5 & y1 into r10
    xor     t3, a4, t3                  // Exec t9 = t8 ^ t7 into r3
    xor     t3, t3, s11                 // Exec t19 = t9 ^ t14 into r3
    xor     s5, t3, s5                  // Exect23 = t19 ^ y21 into b5
    xor     t3, s6, a6                  // Exec y3 = y5 ^ y8 into r3
    and     a4, t3, t6                  // Exec t3 = y3 & y6 into r10
    xor     t5, a4, t5                  // Exec t4 = t3 ^ t2 into r5
    xor     t5, t5, a1                  // Exect17 = t4 ^ y20 into r5
    xor     t5, t5, s11                 // Exec t21 = t17 ^ t14 into r5
    and     a1, t5, s5                  // Exect26 = t21 & t23 into r7
    xor     a4, s2, a1                  // Exec t27 = t24 ^ t26 into r10
    xor     a1, s1, a1                  // Exect31 = t22 ^ t26 into r7
    xor     t5, t5, s1                  // Exect25 = t21 ^ t22 into r5
    and     s10, t5, a4                 // Exec t28 = t25 & t27 into r16
    xor     s1, s10, s1                 // Exec t29 = t28 ^ t22 into b1
    and     s11, s1, s0                 // Exec z14 = t29 & y2 into r17
    and     a5, s1, a5                  // Exec z5 = t29 & y7 into r11
    xor     s10, s5, s2                 // Exec t30 = t23 ^ t24 into r16
    and     a1, a1, s10                 // Exec t32 = t31 & t30 into r7
    xor     a1, a1, s2                  // Exect33 = t32 ^ t24 into r7
    xor     s10, a4, a1                 // Exec t35 = t27 ^ t33 into r16
    and     s2, s2, s10                 // Exec t36 = t24 & t35 into b2
    xor     a4, a4, s2                  // Exec t38 = t27 ^ t36 into r10
    and     a4, s1, a4                  // Exec t39 = t29 & t38 into r10
    xor     t5, t5, a4                  // Exec t40 = t25 ^ t39 into r5
    xor     a4, s1, t5                  // Exec t43 = t29 ^ t40 into r10
    and     s4, a4, s4                  // Exec z3 = t43 & y16 into b4
    xor     a5, s4, a5                  // Exec tc12 = z3 ^ z5 into r11
    and     t1, a4, t1                  // Exec z12 = t43 & y13 into r1
    and     s6, t5, s6                  // Execz13 = t40 & y5 into b6
    and     a4, t5, a7                  // Exec z4 = t40 & y1 into r10
    xor     s4, s4, a4                  // Exec tc6 = z3 ^ z4 into b4
    xor     s5, s5, a1                  // Exect34 = t23 ^ t33 into b5
    xor     s2, s2, s5                  // Exect37 = t36 ^ t34 into b2
    xor     s5, t5, s2                  // Exect41 = t40 ^ t37 into b5
    and     t5, s5, s8                  // Exec z8 = t41 & y10 into r5
    and     a4, s5, a6                  // Exec z17 = t41 & y8 into r10
    xor     a6, a1, s2                  // Exec t44 = t33 ^ t37 into r12
    and     t4, a6, t4                  // Exec z0 = t44 & y15 into r4
    and     t2, a6, t2                  // Exec z9 = t44 & y12 into r2
    and     t3, s2, t3                  // Execz10 = t37 & y3 into r3
    and     s2, s2, t6                  // Execz1 = t37 & y6 into b2
    xor     s2, s2, t4                  // Exectc5 = z1 ^ z0 into b2
    xor     a7, s4, s2                  // Exec tc11 = tc6 ^ tc5 into r13
    and     s3, a1, s3                  // Execz11 = t33 & y4 into b3
    xor     s1, s1, a1                  // Exect42 = t29 ^ t33 into b1
    xor     s5, s1, s5                  // Exect45 = t42 ^ t41 into b5
    and     t6, s5, s9                  // Exec z7 = t45 & y17 into r6
    xor     s4, t6, s4                  // Exectc8 = z7 ^ tc6 into b4
    and     t0, s5, t0                  // Execz16 = t45 & y14 into r0
    and     s5, s1, a3                  // Execz6 = t42 & y11 into b5
    xor     s5, s5, s4                  // Exectc16 = z6 ^ tc8 into b5
    and     s1, s1, a2                  // Execz15 = t42 & y9 into b1
    xor     t6, s1, s5                  // Exectc20 = z15 ^ tc16 into r6
    xor     t0, s1, t0                  // Exectc1 = z15 ^ z16 into r0
    xor     s1, t3, t0                  // Exectc2 = z10 ^ tc1 into b1
    xor     s9, s1, s3                  // Exec tc21 = tc2 ^ z11 into r15
    xor     t2, t2, s1                  // Exectc3 = z9 ^ tc2 into r2
    xor     s0, t2, s5                  // ExecS0 = tc3 ^ tc16 into b0
    xor     s3, t2, a7                  // Exec S3 = tc3 ^ tc11 into b3
    xor     s1, s3, s5                  // ExecS1 = S3 ^ tc16 ^ 1 into b1   
    xor     t0, s6, t0                  // Exectc13 = z13 ^ tc1 into r0
    and     s5, a1, s7                  // Execz2 = t33 & U7 into b5
    xor     s8, t4, s5                  // Exec tc4 = z0 ^ z2 into r14
    xor     s6, t1, s8                  // Exec tc7 = z12 ^ tc4 into b6
    xor     s6, t5, s6                  // Exectc9 = z8 ^ tc7 into b6
    xor     s6, s4, s6                  // Exectc10 = tc8 ^ tc9 into b6
    xor     s2, s11, s6                 // Exec tc17 = z14 ^ tc10 into b2
    xor     s5, s9, s2                  // Exec S5 = tc21 ^ tc17 into b5
    xor     s2, s2, t6                  // Exectc26 = tc17 ^ tc20 into b2
    xor     s2, s2, a4                  // Exec S2 = tc26 ^ z17 ^ 1 into b2
    xor     s8, s8, a5                  // Exec tc14 = tc4 ^ tc12 into r14
    xor     t0, t0, s8                  // Exec tc18 = tc13 ^ tc14 into r0
    xor     s6, s6, t0                  // ExecS6 = tc10 ^ tc18 ^ 1 into b6
    xor     s7, t1, t0                  // ExecS7 = z12 ^ tc18 ^ 1 into b7
    xor     s4, s8, s3                  // Exec S4 = tc14 ^ S3 into b4
    not     s1, s1 						// can be moved outside to match with the round func
    not     s2, s2 						// can be moved outside to match with the round func
    not     s6, s6 						// can be moved outside to match with the round func
    not     s7, s7 						// can be moved outside to match with the round func
    ret

/******************************************************************************
* Applies the ShiftRows transformation twice (i.e. SR^2) on the internal state.
* Note that the same subroutine is used in the encryption function so some code
* size could be saved by merging the two files.
******************************************************************************/
double_shiftrows:
	li 		a1, 0x00ff00ff
	li 		a2, 0x0f000f00
	slli 	a6, a2, 4
	and 	s8, t0, a1 					// s8 <- state[0] & 0x00ff00ff
	rori 	s9, t0, 4, s10, s11 	    // s9 <- state[0] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t0, 28, s10, s11        // s9 <- state[0] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t0, s8, s9 					// t0 <- s8 | s9
	and 	s8, t1, a1 					// s8 <- state[1] & 0x00ff00ff
	rori 	s9, t1, 4, s10, s11 		// s9 <- state[1] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t1, 28, s10, s11 		// s9 <- state[1] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t1, s8, s9 					// s1 <- s8 | s9
	and 	s8, t2, a1 					// s8 <- state[2] & 0x00ff00ff
	rori 	s9, t2, 4, s10, s11 		// s9 <- state[2] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t2, 28, s10, s11 		// s9 <- state[2] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t2, s8, s9 					// s2 <- s8 | s9
	and 	s8, t3, a1 					// s8 <- state[3] & 0x00ff00ff
	rori 	s9, t3, 4, s10, s11 		// s9 <- state[3] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t3, 28, s10, s11 		// s9 <- state[3] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t3, s8, s9 					// s3 <- s8 | s9
	and 	s8, t4, a1 					// s8 <- state[4] & 0x00ff00ff
	rori 	s9, t4, 4, s10, s11 		// s9 <- state[4] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t4, 28, s10, s11 		// s9 <- state[4] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t4, s8, s9 					// s4 <- s8 | s9
	and 	s8, t5, a1 					// s8 <- state[5] & 0x00ff00ff
	rori 	s9, t5, 4, s10, s11         // s9 <- state[5] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t5, 28, s10, s11 		// s9 <- state[5] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t5, s8, s9 					// s5 <- s8 | s9
	and 	s8, t6, a1 					// s8 <- state[6] & 0x00ff00ff
	rori 	s9, t6, 4, s10, s11 		// s9 <- state[6] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, t6, 28, s10, s11 		// s9 <- state[6] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		t6, s8, s9 					// s6 <- s8 | s9
	and 	s8, a7, a1 					// s8 <- state[7] & 0x00ff00ff
	rori 	s9, a7, 4, s10, s11 		// s9 <- state[7] >>> 4
	and 	s9, s9, a2 					// s9 <- s9 & 0x0f00f00
	or 		s8, s8, s9 					// s8 <- s8 | s9
	rori 	s9, a7, 28, s10, s11 		// s9 <- state[7] >>> 28
	and 	s9, s9, a6 					// s9 <- s9 & 0xf000f000
	or 		a7, s8, s9 					// s7 <- s8 | s9
    ret

/******************************************************************************
* Compute ShiftRows^(-x) for x = 1/3 on a register r
*
* Parameters:
*   - r       	input/output register
* 	- tmp0-1  	temporary registers
* Prerequisites:
*	- a1  		to contain 0x00003f00/0x00000300
*	- a2  		to contain 0x00000300/0x00003f00
*	- a3  		to contain 0x000f0000/0x000f0000
*	- a4  		to contain 0x03000000/0x3f000000
*	- a5  		to contain 0x3f000000/0x03000000
******************************************************************************/
.macro inv_shiftrows r, tmp0, tmp1, x
	srli 	\tmp0, \r, \x
	and 	\tmp0, \tmp0, a1
	and 	\tmp1, \r, a2
	slli 	\tmp1, \tmp1, 8-\x
	or 		\tmp0, \tmp0, \tmp1
	srli 	\tmp1, \r, 4
	and 	\tmp1, \tmp1, a3
	or 		\tmp0, \tmp0, \tmp1
	and 	\tmp1, \r, a3
	slli 	\tmp1, \tmp1, 4
	or 		\tmp0, \tmp0, \tmp1
	srli 	\tmp1, \r, 8-\x
	and 	\tmp1, \tmp1, a4
	or 		\tmp0, \tmp0, \tmp1
	and 	\tmp1, \r, a5
	slli 	\tmp1, \tmp1, \x
	or 		\tmp0, \tmp0, \tmp1
	andi 	\r, \r, 0xff
	or 		\r, \r, \tmp0
.endm

/******************************************************************************
* Compute ShiftRows^(-1) on the entire round key in order to match fixslicing.
******************************************************************************/
inv_shiftrows_1:
    li     			a1, 0x00003f00 			// a1 <- 0x00003f00
    li     			a2, 0x00000300 			// a2 <- 0x00000300
    li     			a3, 0x000f0000 			// a3 <- 0x000f0000
    slli 			a4, a2, 16 				// a4 <- 0x03000000
    slli 			a5, a1, 16 				// a5 <- 0x3f000000
    inv_shiftrows 	a7, s8, s9, 2
    inv_shiftrows 	t6, s8, s9, 2
    inv_shiftrows 	t5, s8, s9, 2
    inv_shiftrows 	t4, s8, s9, 2
    inv_shiftrows 	t3, s8, s9, 2
    inv_shiftrows 	t2, s8, s9, 2
    inv_shiftrows 	t1, s8, s9, 2
    inv_shiftrows 	t0, s8, s9, 2
    ret

/******************************************************************************
* Compute ShiftRows^(-3) on the entire round key in order to match fixslicing.
******************************************************************************/
inv_shiftrows_3:
    li     			a1, 0x00000300 			// a1 <- 0x00000300
    li     			a2, 0x00003f00 			// a2 <- 0x00003f00
    li     			a3, 0x000f0000 			// a3 <- 0x000f0000
    slli 			a4, a2, 16 				// a4 <- 0x3f000000
    slli 			a5, a1, 16 				// a5 <- 0x03000000
    inv_shiftrows 	a7, s8, s9, 6
    inv_shiftrows 	t6, s8, s9, 6
    inv_shiftrows 	t5, s8, s9, 6
    inv_shiftrows 	t4, s8, s9, 6
    inv_shiftrows 	t3, s8, s9, 6
    inv_shiftrows 	t2, s8, s9, 6
    inv_shiftrows 	t1, s8, s9, 6
    inv_shiftrows 	t0, s8, s9, 6
    ret

/******************************************************************************
* XOR two columns during a round of the AES-128 key schedule.
*
* Parameters:
*   - new       new round key
*   - old       round key from the previous round
*   - tmp0-1    temporary registers
*   - imm       immediate value for rotation
* Prerequisites:
*	- a1  		to contain 0xc0c0c0c0
*	- a2  		to contain 0x30303030
*	- a3  		to contain 0x0c0c0c0c
*	- a4  		to contain 0x03030303
******************************************************************************/
.macro xor_column new, old, tmp0, tmp1, imm
    rori 	\new, \new,\imm,\tmp0,\tmp1 // new <- ROR(s7,imm)
    xor 	\new, \new, \old 			// new <- new ^ old
    and 	\new, \new, a1 				// new <- new & 0xc0c0c0c0
    srli 	\tmp0, \new, 2	 			// tmp <- new >> 2
    xor 	\tmp0, \tmp0, \old 			// tmp <- tmp ^ old
    and 	\tmp0, \tmp0, a2 			// tmp <- tmp & 0x30303030
    or 		\new, \new, \tmp0 			// new <- new | tmp
    srli 	\tmp0, \new, 2	 			// tmp <- new >> 2
    xor 	\tmp0, \tmp0, \old 			// tmp <- tmp ^ old
    and 	\tmp0, \tmp0, a3 			// tmp <- tmp & 0x0c0c0c0c
    or 		\new, \new, \tmp0 			// new <- new | tmp
    srli 	\tmp0, \new, 2	 			// tmp <- new >> 2
    xor 	\tmp0, \tmp0, \old 			// tmp <- tmp ^ old
    and 	\tmp0, \tmp0, a4 			// tmp <- tmp & 0x03030303
    or 		\new, \new, \tmp0 			// new <- new | tmp
.endm

/******************************************************************************
* XOR all the columns during a round of the AES-128 key schedule.
******************************************************************************/
aes128_xorcolumns_rotword:
	li 			a1, 0xc0c0c0c0 			// a1 <- 0xc0c0c0c0
	srli 		a2, a1, 2 				// a2 <- 0x30303030
	srli 		a3, a1, 4 				// a3 <- 0x0c0c0c0c
	srli 		a4, a1, 6  				// a4 <- 0x03030303	
	lw 			t0, 0(a0) 				// load 1st prev rkey word
	lw 			t1, 4(a0) 				// load 2nd prev rkey word
	lw 			t2, 8(a0) 				// load 3rd prev rkey word
	lw 			t3, 12(a0) 				// load 4th prev rkey word
	lw 			t4, 16(a0) 				// load 5th prev rkey word
	lw 			t5, 20(a0) 	            // load 6th prev rkey word
	lw 			t6, 24(a0) 				// load 7th prev rkey word
	lw 			a7, 28(a0) 				// load 8th prev rkey word
	xor_column 	s7, a7, a5, a6, 2
	xor_column 	s6, t6, a5, a6, 2
	xor_column 	s5, t5, a5, a6, 2
	xor_column 	s4, t4, a5, a6, 2
	xor_column 	s3, t3, a5, a6, 2
	xor_column 	s2, t2, a5, a6, 2
	xor_column 	s1, t1, a5, a6, 2
	xor_column 	s0, t0, a5, a6, 2
	store_rkey 	s0,s1,s2,s3,s4,s5,s6,s7,32(a0)
	addi 		a0, a0, 32 				// points to the next rkey
	ret

/******************************************************************************
* XOR all the columns during a round of the AES-128 key schedule.
******************************************************************************/
aes256_xorcolumns_rotword:
    li          a1, 0xc0c0c0c0          // a1 <- 0xc0c0c0c0
    srli        a2, a1, 2               // a2 <- 0x30303030
    srli        a3, a1, 4               // a3 <- 0x0c0c0c0c
    srli        a4, a1, 6               // a4 <- 0x03030303 
    lw          t0, 0(a0)               // load 1st prev rkey word
    lw          t1, 4(a0)               // load 2nd prev rkey word
    lw          t2, 8(a0)               // load 3rd prev rkey word
    lw          t3, 12(a0)              // load 4th prev rkey word
    lw          t4, 16(a0)              // load 5th prev rkey word
    lw          t5, 20(a0)              // load 6th prev rkey word
    lw          t6, 24(a0)              // load 7th prev rkey word
    lw          a7, 28(a0)              // load 8th prev rkey word
    xor_column  s7, a7, a5, a6, 2
    xor_column  s6, t6, a5, a6, 2
    xor_column  s5, t5, a5, a6, 2
    xor_column  s4, t4, a5, a6, 2
    xor_column  s3, t3, a5, a6, 2
    xor_column  s2, t2, a5, a6, 2
    xor_column  s1, t1, a5, a6, 2
    xor_column  s0, t0, a5, a6, 2
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7,64(a0)
    addi        a0, a0, 32              // points to the next rkey
    ret

/******************************************************************************
* XOR all the columns during a round of the AES-128 key schedule.
******************************************************************************/
aes256_xorcolumns:
    li          a1, 0xc0c0c0c0          // a1 <- 0xc0c0c0c0
    srli        a2, a1, 2               // a2 <- 0x30303030
    srli        a3, a1, 4               // a3 <- 0x0c0c0c0c
    srli        a4, a1, 6               // a4 <- 0x03030303 
    lw          t0, 0(a0)               // load 1st prev rkey word
    lw          t1, 4(a0)               // load 2nd prev rkey word
    lw          t2, 8(a0)               // load 3rd prev rkey word
    lw          t3, 12(a0)              // load 4th prev rkey word
    lw          t4, 16(a0)              // load 5th prev rkey word
    lw          t5, 20(a0)              // load 6th prev rkey word
    lw          t6, 24(a0)              // load 7th prev rkey word
    lw          a7, 28(a0)              // load 8th prev rkey word
    xor_column  s7, a7, a5, a6, 26
    xor_column  s6, t6, a5, a6, 26
    xor_column  s5, t5, a5, a6, 26
    xor_column  s4, t4, a5, a6, 26
    xor_column  s3, t3, a5, a6, 26
    xor_column  s2, t2, a5, a6, 26
    xor_column  s1, t1, a5, a6, 26
    xor_column  s0, t0, a5, a6, 26
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7,64(a0)
    addi        a0, a0, 32              // points to the next rkey
    ret

/******************************************************************************
* Fully bitsliced AES-128 key schedule according to the fully-fixsliced (ffs)
* representation. 
*
* The function prototype is:
*   - void aes128_keyschedule_ffs(uint32_t* rkeys, const uint8_t* key0,
*                           const uint8_t* key1);
******************************************************************************/
.globl aes128_keyschedule_ffs
.type aes128_keyschedule_ffs, %function
.align 2
aes128_keyschedule_ffs:
    addi        sp, sp, -64             // allocate space on the stack
    sw          a0, 0(sp)               // save context
    sw          a1, 4(sp)               // save context
    sw          s0, 8(sp)               // save context
    sw          s1, 12(sp)              // save context
    sw          s2, 16(sp)              // save context
    sw          s3, 20(sp)              // save context
    sw          s4, 24(sp)              // save context
    sw          s5, 28(sp)              // save context
    sw          s6, 32(sp)              // save context
    sw          s7, 36(sp)              // save context
    sw          s8, 40(sp)              // save context
    sw          ra, 44(sp)              // save context
    sw          s10, 48(sp)             // save context
    sw          s11, 52(sp)             // save context
    sw          s9, 56(sp)              // save context
    lw          s0, 0(a1)               // load input word
    lw          s1, 0(a2)               // load input word
    lw          s2, 4(a1)               // load input word
    lw          s3, 4(a2)               // load input word
    lw          s4, 8(a1)               // load input word
    lw          s5, 8(a2)               // load input word
    lw          s6, 12(a1)              // load input word
    lw          s7, 12(a2)              // load input word
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey 	s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    jal 		sbox
    xori 		s7, s7, 0x300 			// add the 1st rconst
    jal 		aes128_xorcolumns_rotword
    jal 		sbox
    xori 		s6, s6, 0x300 			// add the 2nd rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s5, s5, 0x300 			// add the 3rd rconst
    jal 		aes128_xorcolumns_rotword
    jal 		double_shiftrows
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s4, s4, 0x300 			// add the 4th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_3
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s3, s3, 0x300 			// add the 5th rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s2, s2, 0x300 			// add the 6th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s1, s1, 0x300 			// add the 7th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		double_shiftrows
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s0, s0, 0x300 			// add the 8th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_3
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s7, s7, 0x300 			// add the 9th rconst
    xori 		s6, s6, 0x300 			// add the 9th rconst
    xori 		s4, s4, 0x300 			// add the 9th rconst
    xori 		s3, s3, 0x300 			// add the 9th rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s6, s6, 0x300 			// add the 10th rconst
    xori 		s5, s5, 0x300 			// add the 10th rconst
    xori 		s3, s3, 0x300 			// add the 10th rconst
    xori 		s2, s2, 0x300 			// add the 10th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    store_not_rkey 	s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    lw          a0, 0(sp)               // restore context
    lw          a1, 4(sp)               // restore context
    lw          s0, 8(sp)               // restore context
    lw          s1, 12(sp)              // restore context
    lw          s2, 16(sp)              // restore context
    lw          s3, 20(sp)              // restore context
    lw          s4, 24(sp)              // restore context
    lw          s5, 28(sp)              // restore context
    lw          s6, 32(sp)              // restore context
    lw          s7, 36(sp)              // restore context
    lw          s8, 40(sp)              // restore context
    lw          ra, 44(sp)              // restore context
    lw          s10, 48(sp)             // restore context
    lw          s11, 52(sp)             // restore context
    lw          s9, 56(sp)              // restore context
    addi        sp, sp, 64              // restore stack pointer
    ret                                 // exit
.size aes128_keyschedule_ffs,.-aes128_keyschedule_ffs

/******************************************************************************
* Fully bitsliced AES-256 key schedule according to the fully-fixsliced (ffs)
* representation. 
*
* The function prototype is:
*   - void aes256_keyschedule_ffs(uint32_t* rkeys, const uint8_t* key0,
*                           const uint8_t* key1);
******************************************************************************/
.globl aes256_keyschedule_ffs
.type aes256_keyschedule_ffs, %function
.align 2
aes256_keyschedule_ffs:
    addi        sp, sp, -64             // allocate space on the stack
    sw          a0, 0(sp)               // save context
    sw          a1, 4(sp)               // save context
    sw          s0, 8(sp)               // save context
    sw          s1, 12(sp)              // save context
    sw          s2, 16(sp)              // save context
    sw          s3, 20(sp)              // save context
    sw          s4, 24(sp)              // save context
    sw          s5, 28(sp)              // save context
    sw          s6, 32(sp)              // save context
    sw          s7, 36(sp)              // save context
    sw          s8, 40(sp)              // save context
    sw          ra, 44(sp)              // save context
    sw          s10, 48(sp)             // save context
    sw          s11, 52(sp)             // save context
    sw          s9, 56(sp)              // save context
    lw          s0, 0(a1)               // load first 128 key bits
    lw          s1, 0(a2)               // load first 128 key bits
    lw          s2, 4(a1)               // load first 128 key bits
    lw          s3, 4(a2)               // load first 128 key bits
    lw          s4, 8(a1)               // load first 128 key bits
    lw          s5, 8(a2)               // load first 128 key bits
    lw          s6, 12(a1)              // load first 128 key bits
    lw          s7, 12(a2)              // load first 128 key bits
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    lw          s0, 16(a1)              // load last 128 key bits
    lw          s1, 16(a2)              // load last 128 key bits
    lw          s2, 20(a1)              // load last 128 key bits
    lw          s3, 20(a2)              // load last 128 key bits
    lw          s4, 24(a1)              // load last 128 key bits
    lw          s5, 24(a2)              // load last 128 key bits
    lw          s6, 28(a1)              // load last 128 key bits
    lw          s7, 28(a2)              // load last 128 key bits
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 32(a0)
    jal         sbox
    xori        s7, s7, 0x300           // add the 1st rconst
    jal         aes256_xorcolumns_rotword
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s6, s6, 0x300           // add the 2nd rconst
    jal         aes256_xorcolumns_rotword
    jal         double_shiftrows
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_3
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s5, s5, 0x300           // add the 3rd rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s4, s4, 0x300           // add the 4th rconst
    jal         aes256_xorcolumns_rotword
    jal         double_shiftrows
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_3
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s3, s3, 0x300           // add the 5th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s2, s2, 0x300           // add the 6th rconst
    jal         aes256_xorcolumns_rotword
    jal         double_shiftrows
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_3
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s1, s1, 0x300           // add the 7th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    lw          t0, 0(a0)               // load 1st prev rkey word
    lw          t1, 4(a0)               // load 2nd prev rkey word
    lw          t2, 8(a0)               // load 3rd prev rkey word
    lw          t3, 12(a0)              // load 4th prev rkey word
    lw          t4, 16(a0)              // load 5th prev rkey word
    lw          t5, 20(a0)              // load 6th prev rkey word
    lw          t6, 24(a0)              // load 7th prev rkey word
    lw          a7, 28(a0)              // load 8th prev rkey word
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, 0(a0)
    store_not_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 32(a0)
    lw          a0, 0(sp)               // restore context
    lw          a1, 4(sp)               // restore context
    lw          s0, 8(sp)               // restore context
    lw          s1, 12(sp)              // restore context
    lw          s2, 16(sp)              // restore context
    lw          s3, 20(sp)              // restore context
    lw          s4, 24(sp)              // restore context
    lw          s5, 28(sp)              // restore context
    lw          s6, 32(sp)              // restore context
    lw          s7, 36(sp)              // restore context
    lw          s8, 40(sp)              // restore context
    lw          ra, 44(sp)              // restore context
    lw          s10, 48(sp)             // restore context
    lw          s11, 52(sp)             // restore context
    lw          s9, 56(sp)              // restore context
    addi        sp, sp, 64              // restore stack pointer
    ret                                 // exit
.size aes256_keyschedule_ffs,.-aes256_keyschedule_ffs

/******************************************************************************
* Fully bitsliced AES-128 key schedule according to the semi-fixsliced (sfs)
* representation. 
*
* The function prototype is:
*   - void aes128_keyschedule_sfs(uint32_t* rkeys, const uint8_t* key0,
*                           const uint8_t* key1);
******************************************************************************/
.globl aes128_keyschedule_sfs
.type aes128_keyschedule_sfs, %function
.align 2
aes128_keyschedule_sfs:
    addi        sp, sp, -64             // allocate space on the stack
    sw          a0, 0(sp)               // save context
    sw          a1, 4(sp)               // save context
    sw          s0, 8(sp)               // save context
    sw          s1, 12(sp)              // save context
    sw          s2, 16(sp)              // save context
    sw          s3, 20(sp)              // save context
    sw          s4, 24(sp)              // save context
    sw          s5, 28(sp)              // save context
    sw          s6, 32(sp)              // save context
    sw          s7, 36(sp)              // save context
    sw          s8, 40(sp)              // save context
    sw          ra, 44(sp)              // save context
    sw          s10, 48(sp)             // save context
    sw          s11, 52(sp)             // save context
    sw          s9, 56(sp)              // save context
    lw          s0, 0(a1)               // load input word
    lw          s1, 0(a2)               // load input word
    lw          s2, 4(a1)               // load input word
    lw          s3, 4(a2)               // load input word
    lw          s4, 8(a1)               // load input word
    lw          s5, 8(a2)               // load input word
    lw          s6, 12(a1)              // load input word
    lw          s7, 12(a2)              // load input word
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey 	s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    jal 		sbox
    xori 		s7, s7, 0x300 		    // add the 1st rconst
    jal 		aes128_xorcolumns_rotword
    jal 		sbox
    xori 		s6, s6, 0x300 		    // add the 2nd rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s5, s5, 0x300 		    // add the 3rd rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s4, s4, 0x300 		    // add the 4th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s3, s3, 0x300 		    // add the 5th rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s2, s2, 0x300 		    // add the 6th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s1, s1, 0x300 	        // add the 7th rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s0, s0, 0x300 	        // add the 8th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s7, s7, 0x300 		    // add the 9th rconst
    xori 		s6, s6, 0x300 		    // add the 9th rconst
    xori 		s4, s4, 0x300 		    // add the 9th rconst
    xori 		s3, s3, 0x300 		    // add the 9th rconst
    jal 		aes128_xorcolumns_rotword
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal 		sbox
    xori 		s6, s6, 0x300 			// add the 10th rconst
    xori 		s5, s5, 0x300 			// add the 10th rconst
    xori 		s3, s3, 0x300 			// add the 10th rconst
    xori 		s2, s2, 0x300 			// add the 10th rconst
    jal 		aes128_xorcolumns_rotword
    jal 		inv_shiftrows_1
	store_not_rkey 	t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    store_not_rkey 	s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    lw          a0, 0(sp)               // restore context
    lw          a1, 4(sp)               // restore context
    lw          s0, 8(sp)               // restore context
    lw          s1, 12(sp)              // restore context
    lw          s2, 16(sp)              // restore context
    lw          s3, 20(sp)              // restore context
    lw          s4, 24(sp)              // restore context
    lw          s5, 28(sp)              // restore context
    lw          s6, 32(sp)              // restore context
    lw          s7, 36(sp)              // restore context
    lw          s8, 40(sp)              // restore context
    lw          ra, 44(sp)              // restore context
    lw          s10, 48(sp)             // restore context
    lw          s11, 52(sp)             // restore context
    lw          s9, 56(sp)              // restore context
    addi        sp, sp, 64              // restore stack pointer
    ret                                 // exit
.size aes128_keyschedule_sfs,.-aes128_keyschedule_sfs

/******************************************************************************
* Fully bitsliced AES-256 key schedule according to the semi-fixsliced (sfs)
* representation. 
*
* The function prototype is:
*   - void aes256_keyschedule_sfs(uint32_t* rkeys, const uint8_t* key0,
*                           const uint8_t* key1);
******************************************************************************/
.globl aes256_keyschedule_sfs
.type aes256_keyschedule_sfs, %function
.align 2
aes256_keyschedule_sfs:
    addi        sp, sp, -64             // allocate space on the stack
    sw          a0, 0(sp)               // save context
    sw          a1, 4(sp)               // save context
    sw          s0, 8(sp)               // save context
    sw          s1, 12(sp)              // save context
    sw          s2, 16(sp)              // save context
    sw          s3, 20(sp)              // save context
    sw          s4, 24(sp)              // save context
    sw          s5, 28(sp)              // save context
    sw          s6, 32(sp)              // save context
    sw          s7, 36(sp)              // save context
    sw          s8, 40(sp)              // save context
    sw          ra, 44(sp)              // save context
    sw          s10, 48(sp)             // save context
    sw          s11, 52(sp)             // save context
    sw          s9, 56(sp)              // save context
    lw          s0, 0(a1)               // load first 128 key bits
    lw          s1, 0(a2)               // load first 128 key bits
    lw          s2, 4(a1)               // load first 128 key bits
    lw          s3, 4(a2)               // load first 128 key bits
    lw          s4, 8(a1)               // load first 128 key bits
    lw          s5, 8(a2)               // load first 128 key bits
    lw          s6, 12(a1)              // load first 128 key bits
    lw          s7, 12(a2)              // load first 128 key bits
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 0(a0)
    lw          s0, 16(a1)              // load last 128 key bits
    lw          s1, 16(a2)              // load last 128 key bits
    lw          s2, 20(a1)              // load last 128 key bits
    lw          s3, 20(a2)              // load last 128 key bits
    lw          s4, 24(a1)              // load last 128 key bits
    lw          s5, 24(a2)              // load last 128 key bits
    lw          s6, 28(a1)              // load last 128 key bits
    lw          s7, 28(a2)              // load last 128 key bits
    li          t0, 0x55555555          // mask for SWAPMOVE
    li          t1, 0x33333333          // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f          // mask for SWAPMOVE
    packing
    store_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 32(a0)
    jal         sbox
    xori        s7, s7, 0x300           // add the 1st rconst
    jal         aes256_xorcolumns_rotword
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s6, s6, 0x300           // add the 2nd rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s5, s5, 0x300           // add the 3rd rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s4, s4, 0x300           // add the 4th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s3, s3, 0x300           // add the 5th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s2, s2, 0x300           // add the 6th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    jal         aes256_xorcolumns
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    jal         sbox
    xori        s1, s1, 0x300           // add the 7th rconst
    jal         aes256_xorcolumns_rotword
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, -32(a0)
    lw          t0, 0(a0)               // load 1st prev rkey word
    lw          t1, 4(a0)               // load 2nd prev rkey word
    lw          t2, 8(a0)               // load 3rd prev rkey word
    lw          t3, 12(a0)              // load 4th prev rkey word
    lw          t4, 16(a0)              // load 5th prev rkey word
    lw          t5, 20(a0)              // load 6th prev rkey word
    lw          t6, 24(a0)              // load 7th prev rkey word
    lw          a7, 28(a0)              // load 8th prev rkey word
    jal         inv_shiftrows_1
    store_not_rkey  t0,t1,t2,t3,t4,t5,t6,a7, 0(a0)
    store_not_rkey  s0,s1,s2,s3,s4,s5,s6,s7, 32(a0)
    lw          a0, 0(sp)               // restore context
    lw          a1, 4(sp)               // restore context
    lw          s0, 8(sp)               // restore context
    lw          s1, 12(sp)              // restore context
    lw          s2, 16(sp)              // restore context
    lw          s3, 20(sp)              // restore context
    lw          s4, 24(sp)              // restore context
    lw          s5, 28(sp)              // restore context
    lw          s6, 32(sp)              // restore context
    lw          s7, 36(sp)              // restore context
    lw          s8, 40(sp)              // restore context
    lw          ra, 44(sp)              // restore context
    lw          s10, 48(sp)             // restore context
    lw          s11, 52(sp)             // restore context
    lw          s9, 56(sp)              // restore context
    addi        sp, sp, 64              // restore stack pointer
    ret                                 // exit
.size aes256_keyschedule_sfs,.-aes256_keyschedule_sfs
