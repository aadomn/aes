/******************************************************************************
* Fixsliced AES-128 and AES-256 implementations (encryption-only) in RV32I
* assembly language, using the base instruction set only.
*
* See the paper at https://eprint.iacr.org/2020/1123.pdf for more details.
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
* Computes byte-wise rotations on a 32-bit word
*
* Parameters:
*   - out         output register
*   - in          input register
*   - imm         rotation value (must be an immediate value)
*   - mask0-1     masks
*   - tmp0-1      temporary registers
******************************************************************************/
.macro byte_rori out, in, mask0, mask1, imm, tmp0, tmp1
    srli    \tmp0, \in, \imm
    and     \tmp0, \tmp0, \mask0
    and     \tmp1, \in, \mask1
    slli    \tmp1, \tmp1, 8-\imm
    or      \out, \tmp0, \tmp1
.endm 

/******************************************************************************
* Computes byte-wise rotations on a 32-bit word
*
* Parameters:
*   - out         output register
*   - in          input register
*   - rval        rotation value (must be a register)
*   - inv_rval    8 - rotation value (must be a register)
*   - mask0-1     masks
*   - tmp0-1      temporary registers
******************************************************************************/
.macro byte_ror out, in, mask0, mask1, rval, inv_rval, tmp0, tmp1
    srl     \tmp0, \in, \rval
    and     \tmp0, \tmp0, \mask0
    and     \tmp1, \in, \mask1
    sll     \tmp1, \tmp1, \inv_rval
    or      \out, \tmp0, \tmp1
.endm 

/******************************************************************************
* Addition of the round key on a quarter of the internal state.
*
* Parameters:
* 	- b0-b7  	a quarter of the state
* 	- rk 		pointer to the round key
* 	- r0-r1  	temporary registers
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
* Subroutine that computes the AddRoundKey and the S-box.
* Credits to https://github.com/Ko-/riscvcrypto for the S-box implementation
******************************************************************************/
ark_sbox:
    addroundkey     s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), s8,s9
    addi    a0, a0, 32
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
    ret

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* Note that it can be used for rounds i s.t. i % 4 == 0 or i % 4 == 2.
*
* Requirements:
*   - for i % 4 == 0:
*       - t4 to contain 0x03030303
*       - t5 to contain 0x3f3f3f3f
*       - a2 to contain 6
*       - a3 to contain 2
*   - for i % 4 == 2:
*       - t4 to contain 0x3f3f3f3f
*       - t5 to contain 0x03030303
*       - a2 to contain 2
*       - a3 to contain 6
******************************************************************************/
mixcolumns0:
    li          t6, 0x0f0f0f0f
    byte_ror    t3,s0,t4,t5,a2,a3,s8,s9     // t3 <- BYTE_ROR_6(state[0])
    rori        t3, t3, 8, s8, s9           // t3 <- BYTE_ROR_6(state[0]) >>> 8
    xor         t0, s0, t3                  // t0 <- state[0] ^ t3
    byte_ror    t1,s7,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[7])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[7]) >>> 8
    xor         t2, s7, t1                  // t2 <- state[7] ^ t1
    byte_rori   a1, t2, t6, t6, 4, s8, s9   // a1 <- BYTE_ROR_4(t2)
    rori        a1, a1, 16, s8, s9          // a1 <- BYTE_ROR_4(t2) >>> 16
    xor         s7, a1, t0                  // s7 <- a1 ^ t0
    xor         s7, s7, t1                  // s7 <- a1 ^ t0 ^ t1
    byte_ror    t1,s6,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[6])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[6]) >>> 8
    xor         a1, t1, s6                  // a1 <- t1 ^ s6
    byte_rori   a4, a1, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(a1)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(a1) >>> 16
    xor         s6, t2, t0                  // s6 <- t2 ^ t0
    xor         s6, s6, t1                  // s6 <- t2 ^ t0 ^ t1
    xor         s6, s6, a4                  // s6 <- t2 ^ t0 ^ t1 ^ a4
    byte_ror    t1,s5,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[5])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[5]) >>> 8
    xor         t2, t1, s5                  // t2 <- t1 ^ state[5]
    byte_rori   a4, t2, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(t2)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(t2) >>> 16
    xor         s5, a1, t1                  // s5 <- a1 ^ t1
    xor         s5, s5, a4                  // s5 <- a1 ^ t1 ^ a4
    byte_ror    t1,s4,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[4])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[4]) >>> 8
    xor         a1, t1, s4                  // a1 <- t1 ^ state[4]
    byte_rori   a4, a1, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(a1)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(a1) >>> 16
    xor         s4, t2, t0                  // s4 <- t2 ^ t0
    xor         s4, s4, t1                  // s4 <- t2 ^ t0 ^ t1
    xor         s4, s4, a4                  // s4 <- t2 ^ t0 ^ t1 ^ a4
    byte_ror    t1,s3,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[3])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[3]) >>> 8
    xor         t2, t1, s3                  // t2 <- t1 ^ state[3]
    byte_rori   a4, t2, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(t2)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(t2) >>> 16
    xor         s3, a1, t0                  // s3 <- a1 ^ t0
    xor         s3, s3, t1                  // s3 <- a1 ^ t0 ^ t1
    xor         s3, s3, a4                  // s3 <- a1 ^ t0 ^ t1 ^ a4
    byte_ror    t1,s2,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[2])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[2]) >>> 8
    xor         a1, t1, s2                  // a1 <- t1 ^ state[2]
    byte_rori   a4, a1, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(a1)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(a1) >>> 16
    xor         s2, t2, t1                  // s2 <- t2 ^ t1
    xor         s2, s2, a4                  // s2 <- t2 ^ t1 ^ a4
    byte_ror    t1,s1,t4,t5,a2,a3,s8,s9     // t1 <- BYTE_ROR_6(state[1])
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_ROR_6(state[1]) >>> 8
    xor         t2, t1, s1                  // t2 <- t1 ^ state[1]
    byte_rori   a4, t2, t6, t6, 4, s8, s9   // a4 <- BYTE_ROR_4(t2)
    rori        a4, a4, 16, s8, s9          // a4 <- BYTE_ROR_4(t2) >>> 16
    xor         s1, a1, t1                  // s1 <- a1 ^ t1
    xor         s1, s1, a4                  // s1 <- a1 ^ t1 ^ a4
    byte_rori   t0, t0, t6, t6, 4, s8, s9   // t0 <- BYTE_ROR_4(t0)
    rori        t0, t0, 16, s8, s9          // t0 <- BYTE_ROR_4(t0) >>> 16
    xor         s0, t2, t3                  // s0 <- t2 ^ t3
    xor         s0, s0, t0                  // s0 <- t2 ^ t3 ^ t0
    ret

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations only, for round i s.t. (i%4) == 1.
******************************************************************************/
mixcolumns1:
    li          t5, 0x0f0f0f0f              // mask for byte_rori
    byte_rori   t0, s0, t5, t5, 4, s8, s9   // t0 <- BYTE_rori(state[0],4)
    rori        a2, t0, 8, s8, s9           // a2 <- BYTE_rori(state[0],4) >>> 8
    xor         t0, a2, s0                  // t0 <- state[0] ^ a2
    byte_rori   t1, s7, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[7],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[7],4) >>> 8
    xor         t1, t1, s7                  // t1 <- state[7] ^ t1
    xor         t3, t1, t0                  // t3 <- t1 ^ t0
    rori        t4, t1, 16, s8, s9          // t4 <- t1 >>> 16
    xor         s7, s7, t3                  // s7 <- s7 ^ t1 ^ t0
    xor         s7, s7, t4                  // s7 <- s7 ^ t1 ^ t0 ^ (t1 >>> 16)
    byte_rori   t1, s6, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[6],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[6],4) >>> 8
    xor         t2, s6, t1                  // t2 <- state[6] ^ t1
    xor         s6, t3, t1                  // s6 <- t3 ^ t1
    rori        t4, t2, 16, s8, s9          // t4 <- t2 >>> 16
    xor         s6, s6, t4                  // s6 <- s6 ^ (t2 >>> 16)
    byte_rori   t1, s5, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[5],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[5],4) >>> 8
    xor         t3, s5, t1                  // t3 <- state[5] ^ t1
    xor         s5, t2, t1                  // s5 <- t2 ^ t1
    rori        t4, t3, 16, s8, s9          // t4 <- t3 >>> 16
    xor         s5, s5, t4                  // s5 <- s5 ^ (t3 >>> 16)
    byte_rori   t1, s4, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[4],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[4],4) >>> 8
    xor         t2, s4, t1                  // t2 <- state[4] ^ t1
    xor         s4, t3, t1                  // s4 <- t3 ^ t1
    xor         s4, s4, t0                  // s4 <- t3 ^ t1 ^ t0
    rori        t4, t2, 16, s8, s9          // t4 <- t2 >>> 16
    xor         s4, s4, t4                  // s4 <- s4 ^ (t2 >>> 16)
    byte_rori   t1, s3, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[3],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[3],4) >>> 8
    xor         t3, s3, t1                  // t3 <- state[3] ^ t1
    xor         s3, t2, t1                  // s3 <- t2 ^ t1
    xor         s3, s3, t0                  // s3 <- t2 ^ t1 ^ t0
    rori        t4, t3, 16, s8, s9          // t4 <- t3 >>> 16
    xor         s3, s3, t4                  // s3 <- s3 ^ (t3 >>> 16)
    byte_rori   t1, s2, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[2],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[2],4) >>> 8
    xor         t2, s2, t1                  // t2 <- state[2] ^ t1
    xor         s2, t3, t1                  // s2 <- t3 ^ t1
    rori        t4, t2, 16, s8, s9          // t4 <- t2 >>> 16
    xor         s2, s2, t4                  // s2 <- s2 ^ (t2 >>> 16)
    byte_rori   t1, s1, t5, t5, 4, s8, s9   // t1 <- BYTE_rori(state[1],4)
    rori        t1, t1, 8, s8, s9           // t1 <- BYTE_rori(state[1],4) >>> 8
    xor         t3, s1, t1                  // t3 <- state[1] ^ t1
    xor         s1, t2, t1                  // s1 <- t2 ^ t1
    rori        t4, t3, 16, s8, s9          // t4 <- t3 >>> 16
    xor         s1, s1, t4                  // s1 <- s1 ^ (t3 >>> 16)
    xor         t2, s0, a2                  // t2 <- state[0] ^ t1
    xor         s0, t3, a2                  // s0 <- t3 ^ t1
    rori        t4, t2, 16, s8, s9          // t4 <- t2 >>> 16
    xor         s0, s0, t4                  // s0 <- s0 ^ (t2 >>> 16)
    ret

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations, it is used for rounds i s.t. (i%4) == 3.
* For semi-fixsliced implementations, it is used for rounds i s.t. (i%2) == 1.
* Based on Käsper-Schwabe, similar to https://github.com/Ko-/riscvcrypto.
******************************************************************************/
mixcolumns3:
    rori    t3, s7, 8, s8, s9               // t3 <- state[7] >>> 8
    xor     t0, t3, s7                      // t0 <- state[7] ^ (state[7] >>> 8)
    rori    t5, s0, 8, s8, s9               // t5 <- state[0] >>> 8
    xor     t2, t5, s0                      // t2 <- state[0] ^ (state[0] >>> 8)
    rori    t4, t0, 16, s8, s9              // t4 <- t0 >>> 16
    xor     s7, t3, t4                      // s7 <- t0 >>> 16 ^ state[7] >>> 8
    xor     s7, s7, t2                      // s7 <- s7 ^ t2
    rori    t3, s6, 8, s8, s9               // t3 <- state[6] >>> 8
    xor     t1, t3, s6                      // t1 <- state[6] ^ (state[6] >>> 8)
    rori    t4, t1, 16, s8, s9              // t4 <- t1 >>> 16
    xor     s6, t3, t4                      // s6 <- t1 >>> 16 ^ state[6] >>> 8
    xor     s6, s6, t0                      // s6 <- s6 ^ t0
    xor     s6, s6, t2                      // s6 <- s6 ^ t2
    rori    t3, s5, 8, s8, s9               // t3 <- state[5] >>> 8
    xor     t0, t3, s5                      // t0 <- state[5] ^ (state[5] >>> 8)
    rori    t4, t0, 16, s8, s9              // t4 <- t0 >>> 16
    xor     s5, t3, t4                      // s5 <- t0 >>> 16 ^ state[5] >>> 8
    xor     s5, s5, t1                      // s5 <- s5 ^ t1
    rori    t3, s4, 8, s8, s9               // t3 <- state[4] >>> 8
    xor     t1, t3, s4                      // t1 <- state[4] ^ (state[4] >>> 8)
    rori    t4, t1, 16, s8, s9              // t4 <- t1 >>> 16
    xor     s4, t3, t4                      // s4 <- t1 >>> 16 ^ state[4] >>> 8
    xor     s4, s4, t0                      // s4 <- s4 ^ t0
    xor     s4, s4, t2                      // s4 <- s4 ^ t2
    rori    t3, s3, 8, s8, s9               // t3 <- state[3] >>> 8
    xor     t0, t3, s3                      // t0 <- state[3] ^ (state[3] >>> 8)
    rori    t4, t0, 16, s8, s9              // t4 <- t0 >>> 16
    xor     s3, t3, t4                      // s3 <- t0 >>> 16 ^ state[3] >>> 8
    xor     s3, s3, t1                      // s3 <- s3 ^ t1
    xor     s3, s3, t2                      // s3 <- s3 ^ t2
    rori    t3, s2, 8, s8, s9               // t3 <- state[2] >>> 8
    xor     t1, t3, s2                      // t1 <- state[2] ^ (state[2] >>> 8)
    rori    t4, t1, 16, s8, s9              // t4 <- t1 >>> 16
    xor     s2, t3, t4                      // s2 <- t1 >>> 16 ^ state[2] >>> 8
    xor     s2, s2, t0                      // s2 <- s2 ^ t0
    rori    t3, s1, 8, s8, s9               // t3 <- state[1] >>> 8
    xor     t0, t3, s1                      // t0 <- state[1] ^ (state[1] >>> 8)
    rori    t4, t0, 16, s8, s9              // t4 <- t0 >>> 16
    xor     s1, t3, t4                      // s3 <- t0 >>> 16 ^ state[1] >>> 8
    xor     s1, s1, t1                      // s3 <- s3 ^ t1
    rori    t4, t2, 16, s8, s9              // t4 <- t2 >>> 16
    xor     s0, t5, t4                      // s0 <- t5 ^ t4
    xor     s0, s0, t0                      // s0 <- s0 ^ t0
    ret

/******************************************************************************
* Applies the ShiftRows transformation twice (i.e. SR^2) on the internal state.
******************************************************************************/
double_shiftrows:
    li         t1, 0x0f000f00
    swapmove   s0,s0,s0,s0, t1, 4, t0
    swapmove   s1,s1,s1,s1, t1, 4, t0
    swapmove   s2,s2,s2,s2, t1, 4, t0
    swapmove   s3,s3,s3,s3, t1, 4, t0
    swapmove   s4,s4,s4,s4, t1, 4, t0
    swapmove   s5,s5,s5,s5, t1, 4, t0
    swapmove   s6,s6,s6,s6, t1, 4, t0
    swapmove   s7,s7,s7,s7, t1, 4, t0
    ret

/******************************************************************************
* Subroutine to bitslice the two 128-bit input blocs as follows
* s0 = b_24 b_56 b_88 b_120 || ... || b_0 b_32 b_64 b_96
* s1 = b_25 b_57 b_89 b_121 || ... || b_1 b_33 b_65 b_97
* s2 = b_26 b_58 b_90 b_122 || ... || b_2 b_34 b_66 b_98
* s3 = b_27 b_59 b_91 b_123 || ... || b_3 b_35 b_67 b_99
* s4 = b_28 b_60 b_92 b_124 || ... || b_4 b_36 b_68 b_100
* s5 = b_29 b_61 b_93 b_125 || ... || b_5 b_37 b_69 b_101
* s6 = b_30 b_62 b_94 b_126 || ... || b_6 b_38 b_70 b_102
* s7 = b_31 b_63 b_95 b_127 || ... || b_7 b_39 b_71 b_103
* Note that it has been divided in 3 subroutine to avoid additional code size
* to unpack.
******************************************************************************/
packing_0:
    swapmove    s1, s0, s1, s0, t0, 1, s8
    swapmove    s3, s2, s3, s2, t0, 1, s8
    swapmove    s5, s4, s5, s4, t0, 1, s8
    swapmove    s7, s6, s7, s6, t0, 1, s8
    ret
packing_1:
    swapmove    s2, s0, s2, s0, t1, 2, s8
    swapmove    s3, s1, s3, s1, t1, 2, s8
    swapmove    s6, s4, s6, s4, t1, 2, s8
    swapmove    s7, s5, s7, s5, t1, 2, s8
    ret
packing_2:
    swapmove    s4, s0, s4, s0, t2, 4, s8
    swapmove    s5, s1, s5, s1, t2, 4, s8
    swapmove    s6, s2, s6, s2, t2, 4, s8
    swapmove    s7, s3, s7, s3, t2, 4, s8
    ret

/******************************************************************************
* Fully-fixsliced implementation of AES-128.
* Two blocks are encrypted in parallel, without any operating mode.
*
* The function prototype is:
*   - void aes128_encrypt_ffs(uint8_t* out0, uint8_t* out1, const uint8_t* in0,
                        const uint8_t* in1, const uint32_t* rkeys)
******************************************************************************/
.globl aes128_encrypt_ffs
.type aes128_encrypt_ffs, %function
.align 2
aes128_encrypt_ffs:
    addi sp, sp, -72
    sw          ra, 68(sp)                  // save context
    sw          a0, 64(sp)                  // save context
    sw          a1, 60(sp)                  // save context
    sw          a2, 56(sp)                  // save context
    sw          a3, 52(sp)                  // save context
    sw          a4, 48(sp)                  // save context
    sw          s0, 44(sp)                  // save context
    sw          s1, 40(sp)                  // save context
    sw          s2, 36(sp)                  // save context
    sw          s3, 32(sp)                  // save context
    sw          s4, 28(sp)                  // save context
    sw          s5, 24(sp)                  // save context
    sw          s6, 20(sp)                  // save context
    sw          s7, 16(sp)                  // save context
    sw          s8, 12(sp)                  // save context
    sw          s9, 8(sp)                   // save context
    sw          s10, 4(sp)                  // save context
    sw          s11, 0(sp)                  // save context
    add         a0, a4, zero                // put rkeys address in a0
    lw          s0, 0(a2)                   // load input word
    lw          s1, 0(a3)                   // load input word
    lw          s2, 4(a2)                   // load input word
    lw          s3, 4(a3)                   // load input word
    lw          s4, 8(a2)                   // load input word
    lw          s5, 8(a3)                   // load input word
    lw          s6, 12(a2)                  // load input word
    lw          s7, 12(a3)                  // load input word
    li          t0, 0x55555555              // mask for SWAPMOVE
    li          t1, 0x33333333              // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f              // mask for SWAPMOVE
    jal         packing_0
    jal         packing_1
    jal         packing_2
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns1
    jal         ark_sbox
    li          t5, 0x03030303              // mask for byte_rori
    li          t4, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 2
    addi        a3, a2, 4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns1
    jal         ark_sbox
    li          t5, 0x03030303              // mask for byte_rori
    li          t4, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 2
    addi        a3, a2, 4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // double shiftrows for resynch
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), s8,s9
    li          t0, 0x55555555
    li          t1, 0x33333333
    li          t2, 0x0f0f0f0f
    jal         packing_2
    jal         packing_1
    jal         packing_0
    lw          a0, 64(sp)                  // restore pointer to output array
    lw          a1, 60(sp)                  // restore pointer to output array
    sw          s0, 0(a0)                   // store output
    sw          s1, 0(a1)                   // store ouput
    sw          s2, 4(a0)                   // store ouput
    sw          s3, 4(a1)                   // store ouput
    sw          s4, 8(a0)                   // store ouput
    sw          s5, 8(a1)                   // store ouput
    sw          s6, 12(a0)                  // store ouput
    sw          s7, 12(a1)                  // store ouput
    lw          ra, 68(sp)                  // save context
    lw          a2, 56(sp)                  // save context
    lw          a3, 52(sp)                  // save context
    lw          a4, 48(sp)                  // save context
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
    addi        sp, sp, 72
    ret
.size aes128_encrypt_ffs,.-aes128_encrypt_ffs

/******************************************************************************
* Fully-fixsliced implementation of AES-256.
* Two blocks are encrypted in parallel, without any operating mode.
*
* The function prototype is:
*   - void aes256_encrypt_ffs(uint8_t* out0, uint8_t* out1, const uint8_t* in0,
                        const uint8_t* in1, const uint32_t* rkeys)
******************************************************************************/
.globl aes256_encrypt_ffs
.type aes256_encrypt_ffs, %function
.align 2
aes256_encrypt_ffs:
    addi sp, sp, -72
    sw          ra, 68(sp)                  // save context
    sw          a0, 64(sp)                  // save context
    sw          a1, 60(sp)                  // save context
    sw          a2, 56(sp)                  // save context
    sw          a3, 52(sp)                  // save context
    sw          a4, 48(sp)                  // save context
    sw          s0, 44(sp)                  // save context
    sw          s1, 40(sp)                  // save context
    sw          s2, 36(sp)                  // save context
    sw          s3, 32(sp)                  // save context
    sw          s4, 28(sp)                  // save context
    sw          s5, 24(sp)                  // save context
    sw          s6, 20(sp)                  // save context
    sw          s7, 16(sp)                  // save context
    sw          s8, 12(sp)                  // save context
    sw          s9, 8(sp)                   // save context
    sw          s10, 4(sp)                  // save context
    sw          s11, 0(sp)                  // save context
    add         a0, a4, zero                // put rkeys address in a0
    lw          s0, 0(a2)                   // load input word
    lw          s1, 0(a3)                   // load input word
    lw          s2, 4(a2)                   // load input word
    lw          s3, 4(a3)                   // load input word
    lw          s4, 8(a2)                   // load input word
    lw          s5, 8(a3)                   // load input word
    lw          s6, 12(a2)                  // load input word
    lw          s7, 12(a3)                  // load input word
    li          t0, 0x55555555              // mask for SWAPMOVE
    li          t1, 0x33333333              // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f              // mask for SWAPMOVE
    jal         packing_0
    jal         packing_1
    jal         packing_2
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns1
    jal         ark_sbox
    li          t5, 0x03030303              // mask for byte_rori
    li          t4, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 2
    addi        a3, a2, 4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns1
    jal         ark_sbox
    li          t5, 0x03030303              // mask for byte_rori
    li          t4, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 2
    addi        a3, a2, 4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns1
    jal         ark_sbox
    li          t5, 0x03030303              // mask for byte_rori
    li          t4, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 2
    addi        a3, a2, 4
    jal         mixcolumns0
    jal         ark_sbox
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // double shiftrows for resynch
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), s8,s9
    li          t0, 0x55555555
    li          t1, 0x33333333
    li          t2, 0x0f0f0f0f
    jal         packing_2
    jal         packing_1
    jal         packing_0
    lw          a0, 64(sp)                  // restore pointer to output array
    lw          a1, 60(sp)                  // restore pointer to output array
    sw          s0, 0(a0)                   // store output
    sw          s1, 0(a1)                   // store ouput
    sw          s2, 4(a0)                   // store ouput
    sw          s3, 4(a1)                   // store ouput
    sw          s4, 8(a0)                   // store ouput
    sw          s5, 8(a1)                   // store ouput
    sw          s6, 12(a0)                  // store ouput
    sw          s7, 12(a1)                  // store ouput
    lw          ra, 68(sp)                  // save context
    lw          a2, 56(sp)                  // save context
    lw          a3, 52(sp)                  // save context
    lw          a4, 48(sp)                  // save context
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
    addi        sp, sp, 72
    ret
.size aes256_encrypt_ffs,.-aes256_encrypt_ffs

/******************************************************************************
* Semi-fixsliced implementation of AES-128.
* Two blocks are encrypted in parallel, without any operating mode.
*
* The function prototype is:
*   - void aes128_encrypt_sfs(uint8_t* out0, uint8_t* out1, const uint8_t* in0,
                        const uint8_t* in1, const uint32_t* rkeys)
******************************************************************************/
.globl aes128_encrypt_sfs
.type aes128_encrypt_sfs, %function
.align 2
aes128_encrypt_sfs:
    addi sp, sp, -72
    sw          ra, 68(sp)                  // save context
    sw          a0, 64(sp)                  // save context
    sw          a1, 60(sp)                  // save context
    sw          a2, 56(sp)                  // save context
    sw          a3, 52(sp)                  // save context
    sw          a4, 48(sp)                  // save context
    sw          s0, 44(sp)                  // save context
    sw          s1, 40(sp)                  // save context
    sw          s2, 36(sp)                  // save context
    sw          s3, 32(sp)                  // save context
    sw          s4, 28(sp)                  // save context
    sw          s5, 24(sp)                  // save context
    sw          s6, 20(sp)                  // save context
    sw          s7, 16(sp)                  // save context
    sw          s8, 12(sp)                  // save context
    sw          s9, 8(sp)                   // save context
    sw          s10, 4(sp)                  // save context
    sw          s11, 0(sp)                  // save context
    add         a0, a4, zero                // put rkeys address in a0
    lw          s0, 0(a2)                   // load input word
    lw          s1, 0(a3)                   // load input word
    lw          s2, 4(a2)                   // load input word
    lw          s3, 4(a3)                   // load input word
    lw          s4, 8(a2)                   // load input word
    lw          s5, 8(a3)                   // load input word
    lw          s6, 12(a2)                  // load input word
    lw          s7, 12(a3)                  // load input word
    li          t0, 0x55555555              // mask for SWAPMOVE
    li          t1, 0x33333333              // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f              // mask for SWAPMOVE
    jal         packing_0
    jal         packing_1
    jal         packing_2
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), s8,s9
    li          t0, 0x55555555
    li          t1, 0x33333333
    li          t2, 0x0f0f0f0f
    jal         packing_2
    jal         packing_1
    jal         packing_0
    lw          a0, 64(sp)                  // restore pointer to output array
    lw          a1, 60(sp)                  // restore pointer to output array
    sw          s0, 0(a0)                   // store output
    sw          s1, 0(a1)                   // store ouput
    sw          s2, 4(a0)                   // store ouput
    sw          s3, 4(a1)                   // store ouput
    sw          s4, 8(a0)                   // store ouput
    sw          s5, 8(a1)                   // store ouput
    sw          s6, 12(a0)                  // store ouput
    sw          s7, 12(a1)                  // store ouput
    lw          ra, 68(sp)                  // save context
    lw          a2, 56(sp)                  // save context
    lw          a3, 52(sp)                  // save context
    lw          a4, 48(sp)                  // save context
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
    addi sp, sp, 72
    ret
.size aes128_encrypt_sfs,.-aes128_encrypt_sfs

/******************************************************************************
* Semi-fixsliced implementation of AES-256.
* Two blocks are encrypted in parallel, without any operating mode.
*
* The function prototype is:
*   - void aes256_encrypt_sfs(uint8_t* out0, uint8_t* out1, const uint8_t* in0,
                        const uint8_t* in1, const uint32_t* rkeys)
******************************************************************************/
.globl aes256_encrypt_sfs
.type aes256_encrypt_sfs, %function
.align 2
aes256_encrypt_sfs:
    addi sp, sp, -72
    sw          ra, 68(sp)                  // save context
    sw          a0, 64(sp)                  // save context
    sw          a1, 60(sp)                  // save context
    sw          a2, 56(sp)                  // save context
    sw          a3, 52(sp)                  // save context
    sw          a4, 48(sp)                  // save context
    sw          s0, 44(sp)                  // save context
    sw          s1, 40(sp)                  // save context
    sw          s2, 36(sp)                  // save context
    sw          s3, 32(sp)                  // save context
    sw          s4, 28(sp)                  // save context
    sw          s5, 24(sp)                  // save context
    sw          s6, 20(sp)                  // save context
    sw          s7, 16(sp)                  // save context
    sw          s8, 12(sp)                  // save context
    sw          s9, 8(sp)                   // save context
    sw          s10, 4(sp)                  // save context
    sw          s11, 0(sp)                  // save context
    add         a0, a4, zero                // put rkeys address in a0
    lw          s0, 0(a2)                   // load input word
    lw          s1, 0(a3)                   // load input word
    lw          s2, 4(a2)                   // load input word
    lw          s3, 4(a3)                   // load input word
    lw          s4, 8(a2)                   // load input word
    lw          s5, 8(a3)                   // load input word
    lw          s6, 12(a2)                  // load input word
    lw          s7, 12(a3)                  // load input word
    li          t0, 0x55555555              // mask for SWAPMOVE
    li          t1, 0x33333333              // mask for SWAPMOVE
    li          t2, 0x0f0f0f0f              // mask for SWAPMOVE
    jal         packing_0
    jal         packing_1
    jal         packing_2
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    jal         mixcolumns3
    jal         ark_sbox
    li          t4, 0x03030303              // mask for byte_rori
    li          t5, 0x3f3f3f3f              // mask for byte_rori
    addi        a2, zero, 6
    addi        a3, a2, -4
    jal         mixcolumns0
    jal         ark_sbox
    jal         double_shiftrows            // shiftrows every 2 rounds
    addroundkey s0,s1,s2,s3,s4,s5,s6,s7, 0(a0), s8,s9
    li          t0, 0x55555555
    li          t1, 0x33333333
    li          t2, 0x0f0f0f0f
    jal         packing_2
    jal         packing_1
    jal         packing_0
    lw          a0, 64(sp)                  // restore pointer to output array
    lw          a1, 60(sp)                  // restore pointer to output array
    sw          s0, 0(a0)                   // store output
    sw          s1, 0(a1)                   // store ouput
    sw          s2, 4(a0)                   // store ouput
    sw          s3, 4(a1)                   // store ouput
    sw          s4, 8(a0)                   // store ouput
    sw          s5, 8(a1)                   // store ouput
    sw          s6, 12(a0)                  // store ouput
    sw          s7, 12(a1)                  // store ouput
    lw          ra, 68(sp)                  // save context
    lw          a2, 56(sp)                  // save context
    lw          a3, 52(sp)                  // save context
    lw          a4, 48(sp)                  // save context
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
    addi sp, sp, 72
    ret
.size aes256_encrypt_sfs,.-aes256_encrypt_sfs
