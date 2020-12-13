/******************************************************************************
* ARM assembly 1st-order masked fixsliced implementation of the AES-128.
*
* The masking scheme is the one described in "Masking AES with 2 random bits"
* available at https://eprint.iacr.org/2018/1007.
* See supplementary material at https://github.com/LaurenDM/TwoRandomBits
*
* All bytes within the internal state are masked in the following way:
* m1 || m0^m1 || m0^m1 || m0 || m0 || m1 || m0 || m1 where m0, m1 are random
* bits. Note that because each round key is assumed to be masked using the same
* masking scheme with different random bits, the mask is updated at every
* AddRoundKey operation.
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     October 2020
******************************************************************************/

.syntax unified
.thumb

/******************************************************************************
* Macro to compute the SWAPMOVE technique: swap the bits in 'in1' masked by 'm'
* by the bits in 'in0' masked by 'm << n' and put the results in 'out0', 'out1'
******************************************************************************/
.macro swpmv out0, out1, in0, in1, m, n, tmp
    eor     \tmp, \in1, \in0, lsr \n
    and     \tmp, \m
    eor     \out1, \in1, \tmp
    eor     \out0, \in0, \tmp, lsl \n
.endm

/******************************************************************************
* Packs two 128-bit input blocs stored in r4-r7 and r8-r11, respectively, into
* the 256-bit internal state where the bits are packed as follows:
* r4 = b_24 b_56 b_88 b_120 || ... || b_0 b_32 b_64 b_96
* r5 = b_25 b_57 b_89 b_121 || ... || b_1 b_33 b_65 b_97
* r6 = b_26 b_58 b_90 b_122 || ... || b_2 b_34 b_66 b_98
* r7 = b_27 b_59 b_91 b_123 || ... || b_3 b_35 b_67 b_99
* r8 = b_28 b_60 b_92 b_124 || ... || b_4 b_36 b_68 b_100
* r9 = b_29 b_61 b_93 b_125 || ... || b_5 b_37 b_69 b_101
* r10 = b_30 b_62 b_94 b_126 || ... || b_6 b_38 b_70 b_102
* r11 = b_31 b_63 b_95 b_127 || ... || b_7 b_39 b_71 b_103
******************************************************************************/
.align 2
packing:
    movw    r3, #0x0f0f
    movt    r3, #0x0f0f             // r3 <- 0x0f0f0f0f (mask for SWAPMOVE)
    eor     r2, r3, r3, lsl #2      // r2 <- 0x33333333 (mask for SWAPMOVE)
    eor     r1, r2, r2, lsl #1      // r1 <- 0x55555555 (mask for SWAPMOVE)
    swpmv   r8, r4, r8, r4, r1, #1, r12
    swpmv   r9, r5, r9, r5, r1, #1, r12
    swpmv   r10, r6, r10, r6, r1, #1, r12
    swpmv   r11, r7, r11, r7, r1, #1, r12
    swpmv   r0, r4, r5, r4, r2, #2, r12
    swpmv   r9, r5, r9, r8, r2, #2, r12
    swpmv   r7, r8, r7, r6, r2, #2, r12
    swpmv   r11, r2, r11, r10, r2, #2, r12
    swpmv   r8, r4, r8, r4, r3, #4, r12
    swpmv   r10, r6, r7, r0, r3, #4, r12
    swpmv   r11, r7, r11, r9, r3, #4, r12
    swpmv   r9, r5, r2, r5, r3, #4, r12
    bx      lr

/******************************************************************************
* Unpacks the 256-bit internal state in two 128-bit blocs.
******************************************************************************/
.align 2
unpacking:
    movw    r3, #0x0f0f
    movt    r3, #0x0f0f                 // r3 <- 0x0f0f0f0f (mask for SWAPMOVE)
    swpmv   r2, r5, r9, r5, r3, #4, r12
    swpmv   r11, r9, r11, r7, r3, #4, r12
    swpmv   r7, r1, r10, r6, r3, #4, r12
    swpmv   r8, r4, r8, r4, r3, #4, r12
    eor     r3, r3, r3, lsl #2          // r3 <- 0x33333333 (mask for SWAPMOVE)
    swpmv   r11, r10,r11, r2, r3, #2, r12
    swpmv   r7, r6, r7, r8, r3, #2, r12
    swpmv   r9, r8, r9, r5, r3, #2, r12
    swpmv   r5, r4, r1, r4, r3, #2, r12
    eor     r1, r3, r3, lsl #1          // r1 <- 0x55555555 (mask for SWAPMOVE)
    swpmv   r8, r4, r8, r4, r1, #1, r12
    swpmv   r9, r5,r9, r5, r1, #1, r12
    swpmv   r10, r6, r10, r6, r1, #1, r12
    swpmv   r11, r7, r11, r7, r1, #1, r12
    bx      lr

/******************************************************************************
* Subroutine that computes the AddRoundKey.
* Note that the masks are updated since all round keys are assumed to be masked
* with different shares by following the same masking scheme that the one used
* in the encrption function.
******************************************************************************/
.align 2
add_round_key:
    str     r14, [sp]                   // save link register
    ldr.w   r3, [sp, #116]              // load 'rkey' argument from the stack
    ldr     r12, [sp, #128]             // load m0 in r12
    ldrd    r1, r14, [r3], #8           // load km0, km1
    eor     r12, r12, r1                // m0 ^ km0
    eor     r2, r2, r14                 // m1 ^ km1
    ldr.w   r1, [r3], #4                // load km0 ^ km1
    eor     r0, r0, r1                  // m0 ^ m1 ^ km0 ^ km1
    ldr.w   r1, [r3], #4
    ldr     r14, [r3], #4
    str.w   r12, [sp, #128]             // store new m0
    eor     r4, r4, r1
    eor     r5, r5, r14
    ldr.w   r1, [r3], #4
    ldr     r14, [r3], #4
    str.w   r2, [sp, #124]              // store new m1
    eor     r6, r6, r1
    eor     r7, r7, r14
    ldr.w   r1, [r3], #4
    ldr     r14, [r3], #4
    str.w   r0, [sp, #120]              // store new m0 ^ m1
    eor     r8, r8, r1
    eor     r9, r9, r14
    ldr     r14, [r3, #4]
    ldr.w   r1, [r3], #8
    str.w   r3, [sp, #116]
    eor     r10, r10, r1
    eor     r11, r11, r14
    ldr.w   r14, [sp]                   // restore link register
    bx      lr

/******************************************************************************
* 1st-order masked implementation of the S-box in a bitsliced manner.
* Credits to https://github.com/LaurenDM/TwoRandomBits.
* The bitsliced key state should be contained in r4-r11 while the masks
* m2=m0^m1, m1, m0 are supposed to be stored in sp[120,124,128].
******************************************************************************/
.align 2
sbox:
    str     r14, [sp, #132]             // save link register
    mov.w   r14, r2
    orr   r0, r12, r14                  //Exec (m0 | m1) = m0 | m1 into r0
    eor   r2,  r7,  r9                  //Exec y14 = i4 ^ i2 into r2
    str.w r0, [sp, #112]                //Store r0/(m0 | m1) on stack
    eor   r0,  r4, r10                  //Exec y13 = i7 ^ i1 into r0
    eor   r1,  r0, r14                  //Exec hy13 = y13 ^ m1 into r1
    eor   r3,  r4,  r7                  //Exec y9 = i7 ^ i4 into r3
    str.w r3, [sp, #108]                //Store r3/y9 on stack
    eor   r3,  r3, r14                  //Exec hy9 = y9 ^ m1 into r3
    str.w r1, [sp, #104]                //Store r1/hy13 on stack
    eor   r1,  r4,  r9                  //Exec y8 = i7 ^ i2 into r1
    eor   r6,  r5,  r6                  //Exec t0 = i6 ^ i5 into r6
    str.w r3, [sp, #100]                //Store r3/hy9 on stack
    eor   r3,  r6, r11                  //Exec y1 = t0 ^ i0 into r3
    str.w r6, [sp, #96]                 //Store r6/t0 on stack
    eor   r6,  r3, r14                  //Exec hy1 = y1 ^ m1 into r6
    eor   r7,  r6,  r7                  //Exec y4 = hy1 ^ i4 into r7
    str.w r7, [sp, #92]                 //Store r7/y4 on stack
    eor   r7,  r7, r12                  //Exec hy4 = y4 ^ m0 into r7
    str.w r0, [sp, #88]                 //Store r0/y13 on stack
    eor   r0,  r0,  r2                  //Exec y12 = y13 ^ y14 into r0
    str.w r6, [sp, #84]                 //Store r6/hy1 on stack
    eor   r6,  r3,  r4                  //Exec y2 = y1 ^ i7 into r6
    eor  r10,  r3, r10                  //Exec y5 = y1 ^ i1 into r10
    str.w r2, [sp, #80]                 //Store r2/y14 on stack
    eor   r2, r10,  r1                  //Exec y3 = y5 ^ y8 into r2
    str  r10, [sp, #60]                 //Store r10/y5 on stack
    eor   r2,  r2, r14                  //Exec hy3 = y3 ^ m1 into r2
    eor   r8,  r8,  r0                  //Exec t1 = i3 ^ y12 into r8
    eor   r9,  r8,  r9                  //Exec y15 = t1 ^ i2 into r9
    str.w r6, [sp, #76]                 //Store r6/y2 on stack
    eor   r6,  r9, r14                  //Exec hy15 = y15 ^ m1 into r6
    eor   r5,  r8,  r5                  //Exec y20 = t1 ^ i6 into r5
    eor   r8,  r9, r11                  //Exec y6 = y15 ^ i0 into r8
    str.w r6, [sp, #72]                 //Store r6/hy15 on stack
    eor   r6,  r8, r12                  //Exec hy6 = y6 ^ m0 into r6
    str.w r6, [sp, #68]                 //Store r6/hy6 on stack
    ldr.w r6, [sp, #96]                 //Load t0 into r6
    str.w r3, [sp, #64]                 //Store r3/y1 on stack
    eor   r3,  r9,  r6                  //Exec y10 = y15 ^ t0 into r3
    eor  r10,  r3, r12                  //Exec hy10 = y10 ^ m0 into r10
    str  r10, [sp, #56]                 //Store r10/hy10 on stack
    ldr  r10, [sp, #100]                //Load hy9 into r10
    str.w r5, [sp, #100]                //Store r5/y20 on stack
    eor  r10,  r5, r10                  //Exec y11 = y20 ^ hy9 into r10
    eor   r5, r10, r12                  //Exec hy11 = y11 ^ m0 into r5
    eor  r14, r11,  r5                  //Exec y7 = i0 ^ hy11 into r14
    eor   r5,  r3,  r5                  //Exec y17 = y10 ^ hy11 into r5
    str.w r1, [sp, #52]                 //Store r1/y8 on stack
    eor   r1,  r3,  r1                  //Exec y19 = y10 ^ y8 into r1
    str.w r1, [sp, #96]                 //Store r1/y19 on stack
    eor   r6,  r6, r10                  //Exec y16 = t0 ^ y11 into r6
    ldr.w r1, [sp, #104]                //Load hy13 into r1
    str.w r3, [sp, #48]                 //Store r3/y10 on stack
    eor   r3,  r1,  r6                  //Exec y21 = hy13 ^ y16 into r3
    str.w r3, [sp, #32]                 //Store r3/y21 on stack
    eor   r4,  r4,  r6                  //Exec y18 = i7 ^ y16 into r4
    str.w r4, [sp, #44]                 //Store r4/y18 on stack
    and   r4,  r0,  r9                  //Exec t2_0 = y12 & y15 into r4
    str.w r0, [sp, #40]                 //Store r0/y12 on stack
    and   r0,  r0, r12                  //Exec t2_1 = y12 & m0 into r0
    str.w r0, [sp, #36]                 //Store r0/t2_1 on stack
    eor   r0,  r0, r12                  //Exec t2_2 = t2_1 ^ m0 into r0
    eor   r0,  r4,  r0                  //Exec t2_3 = t2_0 ^ t2_2 into r0
    ldr.w r4, [sp, #120]                //Load m2 into r4
    ldr.w r3, [sp, #112]                //Load (m0 | m1) into r3
    and   r9,  r4,  r9                  //Exec t2_4 = m2 & y15 into r9
    eor   r9,  r9,  r3                  //Exec t2_5 = t2_4 ^ (m0 | m1) into r9
    eor   r0,  r0,  r9                  //Exec t2 = t2_3 ^ t2_5 into r0
    and   r9,  r2,  r8                  //Exec t3_0 = hy3 & y6 into r9
    str.w r2, [sp, #28]                 //Store r2/hy3 on stack
    and   r2,  r2,  r4                  //Exec t3_1 = hy3 & m2 into r2
    str.w r2, [sp, #24]                 //Store r2/t3_1 on stack
    eor   r2,  r2,  r4                  //Exec t3_2 = t3_1 ^ m2 into r2
    eor   r2,  r9,  r2                  //Exec t3_3 = t3_0 ^ t3_2 into r2
    and   r8, r12,  r8                  //Exec t3_4 = m0 & y6 into r8
    eor   r8,  r8,  r3                  //Exec t3_5 = t3_4 ^ (m0 | m1) into r8
    eor   r2,  r2,  r8                  //Exec t3 = t3_3 ^ t3_5 into r2
    eor   r2,  r2,  r0                  //Exec t4 = t3 ^ t2 into r2
    and   r8, r11,  r7                  //Exec t5_0 = i0 & hy4 into r8
    and   r9, r11,  r4                  //Exec t5_1 = i0 & m2 into r9
    str   r9, [sp, #20]                 //Store r9/t5_1 on stack
    eor   r9,  r9,  r4                  //Exec t5_2 = t5_1 ^ m2 into r9
    eor   r8,  r8,  r9                  //Exec t5_3 = t5_0 ^ t5_2 into r8
    ldr   r9, [sp, #124]                //Load m1 into r9
    and   r7,  r9,  r7                  //Exec t5_4 = m1 & hy4 into r7
    eor   r7,  r7,  r3                  //Exec t5_5 = t5_4 ^ (m0 | m1) into r7
    eor   r7,  r8,  r7                  //Exec t5 = t5_3 ^ t5_5 into r7
    eor   r0,  r7,  r0                  //Exec t6 = t5 ^ t2 into r0
    and   r7,  r1,  r6                  //Exec t7_0 = hy13 & y16 into r7
    and   r1,  r1, r12                  //Exec t7_1 = hy13 & m0 into r1
    eor   r1,  r1, r12                  //Exec t7_2 = t7_1 ^ m0 into r1
    eor   r1,  r7,  r1                  //Exec t7_3 = t7_0 ^ t7_2 into r1
    and   r7,  r6,  r4                  //Exec t7_4 = y16 & m2 into r7
    eor   r8,  r7,  r3                  //Exec t7_5 = t7_4 ^ (m0 | m1) into r8
    str.w r7, [sp, #104]                //Store r7/t7_4 on stack
    eor   r1,  r1,  r8                  //Exec t7 = t7_3 ^ t7_5 into r1
    ldr   r8, [sp, #64]                 //Load y1 into r8
    ldr.w r7, [sp, #60]                 //Load y5 into r7
    str.w r6, [sp, #16]                 //Store r6/y16 on stack
    and   r6,  r8,  r7                  //Exec t8_0 = y1 & y5 into r6
    and   r8,  r8,  r9                  //Exec t8_1 = y1 & m1 into r8
    eor   r8,  r8,  r9                  //Exec t8_2 = t8_1 ^ m1 into r8
    eor   r6,  r6,  r8                  //Exec t8_3 = t8_0 ^ t8_2 into r6
    and   r8,  r7, r12                  //Exec t8_4 = y5 & m0 into r8
    str   r8, [sp, #64]                 //Store r8/t8_4 on stack
    eor   r8,  r8,  r3                  //Exec t8_5 = t8_4 ^ (m0 | m1) into r8
    eor   r6,  r6,  r8                  //Exec t8 = t8_3 ^ t8_5 into r6
    ldr   r8, [sp, #76]                 //Load y2 into r8
    str  r14, [sp, #12]                 //Store r14/y7 on stack
    eor   r6,  r6,  r1                  //Exec t9 = t8 ^ t7 into r6
    and   r7, r14,  r8                  //Exec t10_0 = y7 & y2 into r7
    and  r14, r14,  r4                  //Exec t10_1 = y7 & m2 into r14
    eor  r14, r14,  r4                  //Exec t10_2 = t10_1 ^ m2 into r14
    eor   r7,  r7, r14                  //Exec t10_3 = t10_0 ^ t10_2 into r7
    and  r14, r12,  r8                  //Exec t10_4 = m0 & y2 into r14
    eor  r14, r14,  r3                  //Exec t10_5 = t10_4 ^ (m0 | m1) into r14
    eor   r7,  r7, r14                  //Exec t10 = t10_3 ^ t10_5 into r7
    eor   r1,  r7,  r1                  //Exec t11 = t10 ^ t7 into r1
    ldr.w r7, [sp, #108]                //Load y9 into r7
    and  r14, r10,  r7                  //Exec t12_0 = y11 & y9 into r14
    and   r8, r10,  r4                  //Exec t12_1 = y11 & m2 into r8
    eor   r8,  r8,  r4                  //Exec t12_2 = t12_1 ^ m2 into r8
    eor   r8, r14,  r8                  //Exec t12_3 = t12_0 ^ t12_2 into r8
    and  r14,  r9,  r7                  //Exec t12_4 = m1 & y9 into r14
    eor  r14, r14,  r3                  //Exec t12_5 = t12_4 ^ (m0 | m1) into r14
    eor   r8,  r8, r14                  //Exec t12 = t12_3 ^ t12_5 into r8
    ldr  r14, [sp, #80]                 //Load y14 into r14
    str.w r5, [sp, #8 ]                 //Store r5/y17 on stack
    and   r7,  r5, r14                  //Exec t13_0 = y17 & y14 into r7
    and   r5,  r5,  r9                  //Exec t13_1 = y17 & m1 into r5
    eor   r5,  r5,  r9                  //Exec t13_2 = t13_1 ^ m1 into r5
    eor   r5,  r7,  r5                  //Exec t13_3 = t13_0 ^ t13_2 into r5
    and   r7, r12, r14                  //Exec t13_4 = m0 & y14 into r7
    eor   r7,  r7,  r3                  //Exec t13_5 = t13_4 ^ (m0 | m1) into r7
    eor   r5,  r5,  r7                  //Exec t13 = t13_3 ^ t13_5 into r5
    eor   r5,  r5,  r8                  //Exec t14 = t13 ^ t12 into r5
    ldr.w r7, [sp, #52]                 //Load y8 into r7
    ldr  r14, [sp, #48]                 //Load y10 into r14
    str  r10, [sp, #4 ]                 //Store r10/y11 on stack
    and  r10,  r7, r14                  //Exec t15_0 = y8 & y10 into r10
    and   r7,  r7,  r9                  //Exec t15_1 = y8 & m1 into r7
    str.w r7, [sp, #0 ]                 //Store r7/t15_1 on stack
    eor   r7,  r7,  r9                  //Exec t15_2 = t15_1 ^ m1 into r7
    eor   r7, r10,  r7                  //Exec t15_3 = t15_0 ^ t15_2 into r7
    and  r10, r12, r14                  //Exec t15_4 = m0 & y10 into r10
    eor  r10, r10,  r3                  //Exec t15_5 = t15_4 ^ (m0 | m1) into r10
    eor   r7,  r7, r10                  //Exec t15 = t15_3 ^ t15_5 into r7
    eor   r7,  r7,  r8                  //Exec t16 = t15 ^ t12 into r7
    ldr   r8, [sp, #100]                //Load y20 into r8
    eor   r2,  r2,  r8                  //Exec t17 = t4 ^ y20 into r2
    eor   r0,  r0,  r7                  //Exec t18 = t6 ^ t16 into r0
    eor   r6,  r6,  r5                  //Exec t19 = t9 ^ t14 into r6
    eor   r1,  r1,  r7                  //Exec t20 = t11 ^ t16 into r1
    eor   r2,  r2,  r5                  //Exec t21 = t17 ^ t14 into r2
    ldr.w r5, [sp, #96]                 //Load y19 into r5
    eor   r0,  r0,  r5                  //Exec t22 = t18 ^ y19 into r0
    ldr.w r5, [sp, #32]                 //Load y21 into r5
    ldr.w r7, [sp, #44]                 //Load y18 into r7
    str  r11, [sp, #100]                //Store r11/i0 on stack
    eor   r5,  r6,  r5                  //Exec t23 = t19 ^ y21 into r5
    eor   r6,  r5, r12                  //Exec ht23 = t23 ^ m0 into r6
    eor   r1,  r1,  r7                  //Exec t24 = t20 ^ y18 into r1
    eor   r7,  r1, r12                  //Exec ht24 = t24 ^ m0 into r7
    eor   r8,  r2,  r0                  //Exec t25 = t21 ^ t22 into r8
    and  r10,  r5,  r2                  //Exec t26_0 = t23 & t21 into r10
    and  r14,  r5,  r9                  //Exec t26_1 = t23 & m1 into r14
    eor  r14, r14,  r9                  //Exec t26_2 = t26_1 ^ m1 into r14
    eor  r10, r10, r14                  //Exec t26_3 = t26_0 ^ t26_2 into r10
    and   r2,  r4,  r2                  //Exec t26_4 = m2 & t21 into r2
    eor   r2,  r2,  r3                  //Exec t26_5 = t26_4 ^ (m0 | m1) into r2
    eor   r2, r10,  r2                  //Exec t26 = t26_3 ^ t26_5 into r2
    eor  r10,  r1,  r2                  //Exec t27 = t24 ^ t26 into r10
    and  r14,  r8, r10                  //Exec t28_0 = t25 & t27 into r14
    and  r11,  r8, r12                  //Exec t28_1 = t25 & m0 into r11
    eor  r11, r11, r12                  //Exec t28_2 = t28_1 ^ m0 into r11
    eor  r11, r14, r11                  //Exec t28_3 = t28_0 ^ t28_2 into r11
    and  r14,  r4, r10                  //Exec t28_4 = m2 & t27 into r14
    eor  r14, r14,  r3                  //Exec t28_5 = t28_4 ^ (m0 | m1) into r14
    eor  r11, r11, r14                  //Exec t28 = t28_3 ^ t28_5 into r11
    eor  r11, r11,  r0                  //Exec t29 = t28 ^ t22 into r11
    eor   r5,  r5,  r1                  //Exec t30 = t23 ^ t24 into r5
    eor   r0,  r0,  r2                  //Exec t31 = t22 ^ t26 into r0
    and   r2,  r5,  r0                  //Exec t32_0 = t30 & t31 into r2
    and   r5,  r5,  r9                  //Exec t32_1 = t30 & m1 into r5
    eor   r5,  r5,  r9                  //Exec t32_2 = t32_1 ^ m1 into r5
    eor   r2,  r2,  r5                  //Exec t32_3 = t32_0 ^ t32_2 into r2
    and   r0, r12,  r0                  //Exec t32_4 = m0 & t31 into r0
    eor   r0,  r0,  r3                  //Exec t32_5 = t32_4 ^ (m0 | m1) into r0
    eor   r0,  r2,  r0                  //Exec t32 = t32_3 ^ t32_5 into r0
    eor   r0,  r0,  r1                  //Exec t33 = t32 ^ t24 into r0
    eor   r1,  r0, r12                  //Exec ht33 = t33 ^ m0 into r1
    eor   r2,  r6,  r0                  //Exec t34 = ht23 ^ t33 into r2
    eor   r5, r10,  r0                  //Exec t35 = t27 ^ t33 into r5
    and   r6,  r5,  r7                  //Exec t36_0 = t35 & ht24 into r6
    and   r5,  r5,  r4                  //Exec t36_1 = t35 & m2 into r5
    eor   r5,  r5,  r4                  //Exec t36_2 = t36_1 ^ m2 into r5
    eor   r5,  r6,  r5                  //Exec t36_3 = t36_0 ^ t36_2 into r5
    and   r6,  r9,  r7                  //Exec t36_4 = m1 & ht24 into r6
    eor   r6,  r6,  r3                  //Exec t36_5 = t36_4 ^ (m0 | m1) into r6
    eor   r5,  r5,  r6                  //Exec t36 = t36_3 ^ t36_5 into r5
    eor   r2,  r5,  r2                  //Exec t37 = t36 ^ t34 into r2
    eor   r5, r10,  r5                  //Exec t38 = t27 ^ t36 into r5
    and   r6, r11,  r5                  //Exec t39_0 = t29 & t38 into r6
    and   r7, r11,  r4                  //Exec t39_1 = t29 & m2 into r7
    eor   r7,  r7,  r4                  //Exec t39_2 = t39_1 ^ m2 into r7
    eor   r6,  r6,  r7                  //Exec t39_3 = t39_0 ^ t39_2 into r6
    str.w r7, [sp, #96]                 //Store r7/t39_2 on stack
    and   r5,  r9,  r5                  //Exec t39_4 = m1 & t38 into r5
    eor   r5,  r5,  r3                  //Exec t39_5 = t39_4 ^ (m0 | m1) into r5
    eor   r5,  r6,  r5                  //Exec t39 = t39_3 ^ t39_5 into r5
    eor   r5,  r8,  r5                  //Exec t40 = t25 ^ t39 into r5
    eor   r6,  r5,  r2                  //Exec t41 = t40 ^ t37 into r6
    eor   r8, r11,  r0                  //Exec t42 = t29 ^ t33 into r8
    eor  r10, r11,  r5                  //Exec t43 = t29 ^ t40 into r10
    eor   r1,  r1,  r2                  //Exec t44 = ht33 ^ t37 into r1
    eor  r14,  r8,  r6                  //Exec t45 = t42 ^ t41 into r14
    ldr.w r7, [sp, #72]                 //Load hy15 into r7
    str.w r6, [sp, #48]                 //Store r6/t41 on stack
    and   r6,  r1,  r7                  //Exec z0_0 = t44 & hy15 into r6
    str.w r1, [sp, #44]                 //Store r1/t44 on stack
    and   r1,  r1,  r4                  //Exec z0_1 = t44 & m2 into r1
    eor   r1,  r1,  r4                  //Exec z0_2 = z0_1 ^ m2 into r1
    eor   r6,  r6,  r1                  //Exec z0_3 = z0_0 ^ z0_2 into r6
    and   r7, r12,  r7                  //Exec z0_4 = m0 & hy15 into r7
    eor   r7,  r7,  r3                  //Exec z0_5 = z0_4 ^ (m0 | m1) into r7
    eor   r6,  r6,  r7                  //Exec z0 = z0_3 ^ z0_5 into r6
    ldr.w r7, [sp, #68]                 //Load hy6 into r7
    str.w r6, [sp, #72]                 //Store r6/z0 on stack
    and   r6,  r7,  r2                  //Exec z1_0 = hy6 & t37 into r6
    and   r7,  r7,  r4                  //Exec z1_1 = hy6 & m2 into r7
    eor   r7,  r7,  r4                  //Exec z1_2 = z1_1 ^ m2 into r7
    eor   r6,  r6,  r7                  //Exec z1_3 = z1_0 ^ z1_2 into r6
    and   r7,  r9,  r2                  //Exec z1_4 = m1 & t37 into r7
    eor   r7,  r7,  r3                  //Exec z1_5 = z1_4 ^ (m0 | m1) into r7
    eor   r6,  r6,  r7                  //Exec z1 = z1_3 ^ z1_5 into r6
    ldr.w r7, [sp, #100]                //Load i0 into r7
    str.w r6, [sp, #100]                //Store r6/z1 on stack
    and   r7,  r0,  r7                  //Exec z2_0 = t33 & i0 into r7
    and   r6,  r0,  r9                  //Exec z2_1 = t33 & m1 into r6
    eor   r6,  r6,  r9                  //Exec z2_2 = z2_1 ^ m1 into r6
    str.w r6, [sp, #68]                 //Store r6/z2_2 on stack
    eor   r7,  r7,  r6                  //Exec z2_3 = z2_0 ^ z2_2 into r7
    ldr.w r6, [sp, #20]                 //Load t5_1 into r6
    eor   r6,  r6,  r3                  //Exec z2_5 = t5_1 ^ (m0 | m1) into r6
    eor   r6,  r7,  r6                  //Exec z2 = z2_3 ^ z2_5 into r6
    str.w r6, [sp, #32]                 //Store r6/z2 on stack
    ldr.w r7, [sp, #16]                 //Load y16 into r7
    ldr.w r6, [sp, #104]                //Load t7_4 into r6
    and   r7,  r7, r10                  //Exec z3_0 = y16 & t43 into r7
    eor   r6,  r6,  r4                  //Exec z3_2 = t7_4 ^ m2 into r6
    eor   r6,  r7,  r6                  //Exec z3_3 = z3_0 ^ z3_2 into r6
    and   r7, r12, r10                  //Exec z3_4 = m0 & t43 into r7
    str.w r7, [sp, #104]                //Store r7/z3_4 on stack
    eor   r7,  r7,  r3                  //Exec z3_5 = z3_4 ^ (m0 | m1) into r7
    eor   r6,  r6,  r7                  //Exec z3 = z3_3 ^ z3_5 into r6
    ldr.w r7, [sp, #84]                 //Load hy1 into r7
    str.w r6, [sp, #20]                 //Store r6/z3 on stack
    and   r6,  r7,  r5                  //Exec z4_0 = hy1 & t40 into r6
    and   r7,  r7, r12                  //Exec z4_1 = hy1 & m0 into r7
    eor   r7,  r7, r12                  //Exec z4_2 = z4_1 ^ m0 into r7
    eor   r6,  r6,  r7                  //Exec z4_3 = z4_0 ^ z4_2 into r6
    and   r7,  r4,  r5                  //Exec z4_4 = m2 & t40 into r7
    eor   r7,  r7,  r3                  //Exec z4_5 = z4_4 ^ (m0 | m1) into r7
    eor   r6,  r6,  r7                  //Exec z4 = z4_3 ^ z4_5 into r6
    ldr.w r7, [sp, #12]                 //Load y7 into r7
    str.w r6, [sp, #84]                 //Store r6/z4 on stack
    and   r6, r11,  r7                  //Exec z5_0 = t29 & y7 into r6
    str  r11, [sp, #16]                 //Store r11/t29 on stack
    and  r11, r11, r12                  //Exec z5_1 = t29 & m0 into r11
    eor  r11, r11, r12                  //Exec z5_2 = z5_1 ^ m0 into r11
    eor   r6,  r6, r11                  //Exec z5_3 = z5_0 ^ z5_2 into r6
    and   r7,  r9,  r7                  //Exec z5_4 = m1 & y7 into r7
    eor   r7,  r7,  r3                  //Exec z5_5 = z5_4 ^ (m0 | m1) into r7
    eor   r6,  r6,  r7                  //Exec z5 = z5_3 ^ z5_5 into r6
    ldr.w r7, [sp, #4 ]                 //Load y11 into r7
    and  r11,  r7,  r8                  //Exec z6_0 = y11 & t42 into r11
    and   r7,  r7, r12                  //Exec z6_1 = y11 & m0 into r7
    eor   r7,  r7, r12                  //Exec z6_2 = z6_1 ^ m0 into r7
    eor   r7, r11,  r7                  //Exec z6_3 = z6_0 ^ z6_2 into r7
    and  r11,  r9,  r8                  //Exec z6_4 = m1 & t42 into r11
    eor  r11, r11,  r3                  //Exec z6_5 = z6_4 ^ (m0 | m1) into r11
    eor   r7,  r7, r11                  //Exec z6 = z6_3 ^ z6_5 into r7
    ldr  r11, [sp, #8 ]                 //Load y17 into r11
    str.w r7, [sp, #12]                 //Store r7/z6 on stack
    and   r7, r11, r14                  //Exec z7_0 = y17 & t45 into r7
    and  r11, r11,  r4                  //Exec z7_1 = y17 & m2 into r11
    eor  r11, r11,  r4                  //Exec z7_2 = z7_1 ^ m2 into r11
    eor   r7,  r7, r11                  //Exec z7_3 = z7_0 ^ z7_2 into r7
    and  r11, r12, r14                  //Exec z7_4 = m0 & t45 into r11
    eor  r11, r11,  r3                  //Exec z7_5 = z7_4 ^ (m0 | m1) into r11
    eor   r7,  r7, r11                  //Exec z7 = z7_3 ^ z7_5 into r7
    ldr  r11, [sp, #56]                 //Load hy10 into r11
    str.w r6, [sp, #8 ]                 //Store r6/z5 on stack
    eor   r6,  r5,  r2              //Recompute t41 = t40 ^ t37 into r6
    str.w r7, [sp, #4 ]                 //Store r7/z7 on stack
    and   r7, r11,  r6                  //Exec z8_0 = hy10 & t41 into r7
    and  r11, r11,  r9                  //Exec z8_1 = hy10 & m1 into r11
    eor  r11, r11,  r9                  //Exec z8_2 = z8_1 ^ m1 into r11
    eor   r7,  r7, r11                  //Exec z8_3 = z8_0 ^ z8_2 into r7
    and  r11,  r4,  r6                  //Exec z8_4 = m2 & t41 into r11
    eor  r11, r11,  r3                  //Exec z8_5 = z8_4 ^ (m0 | m1) into r11
    eor   r7,  r7, r11                  //Exec z8 = z8_3 ^ z8_5 into r7
    str.w r7, [sp, #56]                 //Store r7/z8 on stack
    ldr  r11, [sp, #44]                 //Load t44 into r11
    ldr.w r7, [sp, #40]                 //Load y12 into r7
    and   r7, r11,  r7                  //Exec z9_0 = t44 & y12 into r7
    eor   r1,  r7,  r1                  //Exec z9_3 = z9_0 ^ z0_2 into r1
    ldr.w r7, [sp, #36]                 //Load t2_1 into r7
    eor   r7,  r7,  r3                  //Exec z9_5 = t2_1 ^ (m0 | m1) into r7
    eor   r1,  r1,  r7                  //Exec z9 = z9_3 ^ z9_5 into r1
    ldr.w r7, [sp, #28]                 //Load hy3 into r7
    and   r7,  r2,  r7                  //Exec z10_0 = t37 & hy3 into r7
    and   r2,  r2, r12                  //Exec z10_1 = t37 & m0 into r2
    eor   r2,  r2, r12                  //Exec z10_2 = z10_1 ^ m0 into r2
    eor   r2,  r7,  r2                  //Exec z10_3 = z10_0 ^ z10_2 into r2
    ldr.w r7, [sp, #24]                 //Load t3_1 into r7
    eor   r7,  r7,  r3                  //Exec z10_5 = t3_1 ^ (m0 | m1) into r7
    eor   r2,  r2,  r7                  //Exec z10 = z10_3 ^ z10_5 into r2
    ldr.w r7, [sp, #92]                 //Load y4 into r7
    ldr  r11, [sp, #68]                 //Load z2_2 into r11
    and   r0,  r0,  r7                  //Exec z11_0 = t33 & y4 into r0
    eor   r0,  r0, r11                  //Exec z11_3 = z11_0 ^ z2_2 into r0
    and   r7,  r4,  r7                  //Exec z11_4 = m2 & y4 into r7
    eor   r7,  r7,  r3                  //Exec z11_5 = z11_4 ^ (m0 | m1) into r7
    eor   r0,  r0,  r7                  //Exec z11 = z11_3 ^ z11_5 into r0
    ldr.w r7, [sp, #88]                 //Load y13 into r7
    ldr  r11, [sp, #104]                //Load z3_4 into r11
    and  r10, r10,  r7                  //Exec z12_0 = t43 & y13 into r10
    eor  r11, r11, r12                  //Exec z12_2 = z3_4 ^ m0 into r11
    eor  r10, r10, r11                  //Exec z12_3 = z12_0 ^ z12_2 into r10
    and   r7,  r4,  r7                  //Exec z12_4 = m2 & y13 into r7
    eor   r7,  r7,  r3                  //Exec z12_5 = z12_4 ^ (m0 | m1) into r7
    eor   r7, r10,  r7                  //Exec z12 = z12_3 ^ z12_5 into r7
    ldr  r10, [sp, #60]                 //Load y5 into r10
    ldr  r11, [sp, #64]                 //Load t8_4 into r11
    str.w r0, [sp, #104]                //Store r0/z11 on stack
    and  r10, r10,  r5                  //Exec z13_0 = y5 & t40 into r10
    eor  r11, r11, r12                  //Exec z13_2 = t8_4 ^ m0 into r11
    eor  r10, r10, r11                  //Exec z13_3 = z13_0 ^ z13_2 into r10
    and   r5,  r9,  r5                  //Exec z13_4 = m1 & t40 into r5
    eor   r5,  r5,  r3                  //Exec z13_5 = z13_4 ^ (m0 | m1) into r5
    eor   r5, r10,  r5                  //Exec z13 = z13_3 ^ z13_5 into r5
    ldr  r10, [sp, #16]                 //Load t29 into r10
    ldr  r11, [sp, #76]                 //Load y2 into r11
    ldr.w r0, [sp, #96]                 //Load t39_2 into r0
    and  r10, r10, r11                  //Exec z14_0 = t29 & y2 into r10
    eor   r0, r10,  r0                  //Exec z14_3 = z14_0 ^ t39_2 into r0
    and  r10,  r9, r11                  //Exec z14_4 = m1 & y2 into r10
    eor  r10, r10,  r3                  //Exec z14_5 = z14_4 ^ (m0 | m1) into r10
    eor   r0,  r0, r10                  //Exec z14 = z14_3 ^ z14_5 into r0
    ldr  r10, [sp, #108]                //Load y9 into r10
    and  r11, r10,  r8                  //Exec z15_0 = y9 & t42 into r11
    and  r10, r10, r12                  //Exec z15_1 = y9 & m0 into r10
    eor  r10, r10, r12                  //Exec z15_2 = z15_1 ^ m0 into r10
    eor  r10, r11, r10                  //Exec z15_3 = z15_0 ^ z15_2 into r10
    and   r8,  r4,  r8                  //Exec z15_4 = m2 & t42 into r8
    eor   r8,  r8,  r3                  //Exec z15_5 = z15_4 ^ (m0 | m1) into r8
    eor   r8, r10,  r8                  //Exec z15 = z15_3 ^ z15_5 into r8
    ldr  r10, [sp, #80]                 //Load y14 into r10
    and  r11, r10, r14                  //Exec z16_0 = y14 & t45 into r11
    and  r10, r10,  r4                  //Exec z16_1 = y14 & m2 into r10
    eor  r10, r10,  r4                  //Exec z16_2 = z16_1 ^ m2 into r10
    eor  r10, r11, r10                  //Exec z16_3 = z16_0 ^ z16_2 into r10
    and  r11,  r9, r14                  //Exec z16_4 = m1 & t45 into r11
    eor  r11, r11,  r3                  //Exec z16_5 = z16_4 ^ (m0 | m1) into r11
    eor  r10, r10, r11                  //Exec z16 = z16_3 ^ z16_5 into r10
    ldr  r11, [sp, #52]                 //Load y8 into r11
    and  r11,  r6, r11                  //Exec z17_0 = t41 & y8 into r11
    and   r6,  r6, r12                  //Exec z17_1 = t41 & m0 into r6
    eor   r6,  r6, r12                  //Exec z17_2 = z17_1 ^ m0 into r6
    eor   r6, r11,  r6                  //Exec z17_3 = z17_0 ^ z17_2 into r6
    ldr  r11, [sp, #0 ]                 //Load t15_1 into r11
    eor   r3, r11,  r3                  //Exec z17_5 = t15_1 ^ (m0 | m1) into r3
    eor   r3,  r6,  r3                  //Exec z17 = z17_3 ^ z17_5 into r3
    eor   r6,  r8, r10                  //Exec tc1 = z15 ^ z16 into r6
    eor   r2,  r2,  r6                  //Exec tc2 = z10 ^ tc1 into r2
    eor   r1,  r1,  r2                  //Exec tc3 = z9 ^ tc2 into r1
    ldr  r10, [sp, #72]                 //Load z0 into r10
    ldr  r11, [sp, #32]                 //Load z2 into r11
    ldr     r14, [sp, #100]             //Load z1 into r14
    str.w   r3, [sp, #112]              //Store r3/z17 on stack
    eor     r11, r10, r11               //Exec tc4 = z0 ^ z2 into r11
    eor     r10, r14, r10               //Exec tc5 = z1 ^ z0 into r10
    ldr     r14, [sp, #20]              //Load z3 into r14
    ldr.w r4, [sp, #84]                 //Load z4 into r4
    ldr   r9, [sp, #4 ]                 //Load z7 into r9
    ldr.w r3, [sp, #56]                 //Load z8 into r3
    eor   r4, r14,  r4                  //Exec tc6 = z3 ^ z4 into r4
    eor  r12,  r7, r11                  //Exec tc7 = z12 ^ tc4 into r12
    eor   r9,  r9,  r4                  //Exec tc8 = z7 ^ tc6 into r9
    eor   r3,  r3, r12                  //Exec tc9 = z8 ^ tc7 into r3
    eor   r3,  r9,  r3                  //Exec tc10 = tc8 ^ tc9 into r3
    eor   r4,  r4, r10                  //Exec tc11 = tc6 ^ tc5 into r4
    ldr  r10, [sp, #8 ]                 //Load z5 into r10
    eor  r10, r14, r10                  //Exec tc12 = z3 ^ z5 into r10
    eor   r5,  r5,  r6                  //Exec tc13 = z13 ^ tc1 into r5
    eor   r6, r11, r10                  //Exec tc14 = tc4 ^ tc12 into r6
    eor   r4,  r1,  r4                  //Exec S3 = tc3 ^ tc11 into r4
    ldr  r10, [sp, #12]                 //Load z6 into r10
    eor   r9, r10,  r9                  //Exec tc16 = z6 ^ tc8 into r9
    eor   r0,  r0,  r3                  //Exec tc17 = z14 ^ tc10 into r0
    eor   r5,  r5,  r6                  //Exec tc18 = tc13 ^ tc14 into r5
    eor   r7,  r7,  r5                  //Exec S7 = z12 ^ tc18 ^ 1 into r7
    eor   r8,  r8,  r9                  //Exec tc20 = z15 ^ tc16 into r8
    ldr  r10, [sp, #104]                //Load z11 into r10
    eor   r2,  r2, r10                  //Exec tc21 = tc2 ^ z11 into r2
    eor   r1,  r1,  r9                  //Exec o7 = tc3 ^ tc16 into r1
    eor   r3,  r3,  r5                  //Exec o1 = tc10 ^ tc18 ^ 1 into r3
    eor   r5,  r6,  r4                  //Exec S4 = tc14 ^ S3 into r5
    eor   r6,  r4,  r9                  //Exec S1 = S3 ^ tc16 ^ 1 into r6
    ldr   r9, [sp, #112]                //Load z17 into r9
    eor   r8,  r0,  r8                  //Exec tc26 = tc17 ^ tc20 into r8
    eor   r8,  r8,  r9                  //Exec S2 = tc26 ^ z17 ^ 1 into r8
    eor   r0,  r2,  r0                  //Exec S5 = tc21 ^ tc17 into r0
    ldr.w r2, [sp, #124]                //Load m1 into r2
    ldr   r9, [sp, #128]                //Load m0 into r9
    ldr  r10, [sp, #120]                //Load m2 into r10
    ldr     r14, [sp, #132]             // restore link register
    eor     r12,  r8,  r9               //Exec o5 = S2 ^ m0 into r12
    eor     r8,  r5,  r2                //Exec o3 = S4 ^ m1 into r8
    eor     r5,  r6,  r2                //Exec o6 = S1 ^ m1 into r5
    eor     r4,  r4, r10                //Exec o4 = S3 ^ m2 into r4
    eor     r0,  r0,  r9                //Exec o2 = S5 ^ m0 into r0
    eor     r6,  r7, r10                //Exec o0 = S7 ^ m2 into r6
    bx      lr 
    //[('r0', 'S5'), ('r1', 'S0'), ('r2', 'm1'), ('r3', 'S6'), ('r4', 'S3'),('r5', 'S1'),
    //('r6', 'S7'), ('r7', -), ('r8', 'S4'), ('r9', 'm0'), ('r10', 'm0^m1'), ('r11', -),
    //('r12', 'S2'), ('r14', -)]

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations, it is used for rounds i s.t. (i%4) == 0.
* For semi-fixsliced implementations, it is used for rounds i s.t. (i%2) == 0.
* Note that 1st-order masking forces to do some remasking to ensure that masks
* are not cancelled through XOR operations.
******************************************************************************/
.align 2
mixcolumns_0:
    str     r14, [sp, #132]
    eor     r14, r1, r9                 // r14<- S0 ^ m1 ^ m0           remask S0
    movw    r9, #0x0303
    movt    r9, #0x0303                 // r9<- 0x03030303 (mask for BYTE_ROR_6)
    and     r11, r9, r14, lsr #6        // r11<- (S0 ^ m0 ^ m1 >> 6) & 0x03030303
    bic     r14, r14, r9, ror #2        // r14<- S0 ^ m0 ^ m1 & 0x3f3f3f3f
    orr     r7, r11, r14, lsl #2        // r7 <- BYTE_ROR_6(S0 ^ m0 ^ m1)
    eor     r14, r1, r7, ror #8         // r14<- S0 ^ BYTE_ROR_6(S0 >>> 8) ^ m0
    and     r11, r9, r6, lsr #6         // r11<- (S7 ^ m1 >> 6) & 0x03030303
    bic     r7, r6, r9, ror #2          // r7 <- S7^m1 & 0x3f3f3f3f
    orr     r7, r11, r7, lsl #2         // r7 <- BYTE_ROR_6(S7 ^ m1)
    eor     r10, r7, r10                // r10 <- BYTE_ROR_6(S7 ^ m1) ^ (m0 ^ m1)    remask r7
    eor     r10, r6, r10, ror #8        // r10 <- S7 ^ (BYTE_ROR_6(S7) >>> 8) ^ m0 ^ m1
    bic     r11, r6, r9                 // r11<- S7 ^ m1 & 0xfcfcfcfc
    and     r6, r6, r9                  // r6 <- S7 ^m1 & 0x03030303
    orr     r6, r6, r11, ror #8         // r6 <- r6 ^r11 >>> 8
    eor     r11, r14, r6, ror #18       // r11<- S0 ^ BYTE_ROR_6(S0 >>> 8) ^ BYTE_ROR_2(S7 >>> 24) ^ m0
    eor     r7, r10, r2                 // r7 <- S7 ^ (BYTE_ROR_6(S7) >>> 8) ^ m0   remask r10
    and     r6, r9, r7, lsr #6          // r6 <- (r7 >> 6) & 0x03030303
    bic     r7, r7, r9, ror #2          // r7 <- r7 & 0x3f3f3f3f
    orr     r7, r6, r7, lsl #2          // r7 <- BYTE_ROR_6(r7) ^ m0
    eor     r11, r11, r7, ror #8        // r11<- S'7 ^ m1
    eor     r10, r10, r14               // r10<- S7^S0 ^ BYTE_ROR_6(S7^S0 >>> 8) ^ m1 
    and     r7, r9, r3, lsr #6          // r7 <- (S6 ^m0^m1 >> 6) & 0x03030303
    bic     r6, r3, r9, ror #2          // r6 <- S6^m0^m1 & 0x3f3f3f3f
    orr     r6, r7, r6, lsl #2          // r6 <- BYTE_ROR_6(S6 ^m0^m1)
    eor     r6, r6, r2                  // r6 <- BYTE_ROR_6(S6 ^m0)             remask r6
    eor     r6, r3, r6, ror #8          // r6 <- S6 ^ BYTE_ROR_6(S6 >>> 8)^m1
    bic     r7, r3, r9                  // r7 <- S6 ^m0^m1 & 0xfcfcfcfc
    and     r3, r3, r9                  // r3 <- S6 ^m0^m1 & 0x03030303
    orr     r3, r3, r7, ror #8          // r3 <- r3 ^r7 >>> 8
    eor     r10, r10, r3, ror #18       // r10<- ^m0
    and     r3, r9, r6, lsr #6          // r3 <- (r6 >> 6) & 0x03030303
    bic     r7, r6, r9, ror #2          // r7 <- r6 & 0x3f3f3f3f
    orr     r7, r3, r7, lsl #2          // r7 <- BYTE_ROR_6(r6) ^ m0
    eor     r10, r10, r7, ror #8
    mov.w   r3, r9                      // move the mask for BYTEROR to r3
    and     r7, r3, r0, lsr #6          // r7 <- (S5 ^m0^m1 >> 6) & 0x03030303
    bic     r9, r0, r3, ror #2          // r9 <- S5^m0^m1 & 0x3f3f3f3f
    orr     r9, r7, r9, lsl #2          // r9 <- BYTE_ROR_6(S5 ^m0^m1)
    eor     r9, r9, r2                  // r9 <- BYTE_ROR_6(S5 ^m0)             remask r6
    eor     r7, r0, r9, ror #8          // r7 <- S5 ^ BYTE_ROR_6(S5) ^ m1
    bic     r9, r0, r3                  // r9 <- S5 ^m0^m1 & 0xfcfcfcfc
    and     r0, r0, r3                  // r0 <- S5 ^m0^m1 & 0x03030303
    orr     r0, r0, r9, ror #8          // r0 <- r0 ^r9 >>> 8
    eor     r9, r6, r0, ror #18         // r9 <- S6 ^ BYTE_ROR_6(S6 >>> 8) ^ BYTE_ROR_2(S5 >>> 24) ^m0
    and     r0, r3, r7, lsr #6          // r3 <- (r7 >> 6) & 0x03030303
    bic     r6, r7, r3, ror #2          // r6 <- r7 & 0x3f3f3f3f
    orr     r6, r0, r6, lsl #2          // r6 <- BYTE_ROR_6(r7) ^ m1
    eor     r9, r9, r6, ror #8          // r9 <- S'5 ^ m0 ^ m1
    and     r6, r3, r8, lsr #6          // r6 <- (S4 ^m0 >> 6) & 0x03030303
    bic     r0, r8, r3, ror #2          // r0 <- S4^m0 & 0x3f3f3f3f
    orr     r6, r6, r0, lsl #2          // r6 <- BYTE_ROR_6(S4 ^m0)
    ldr.w   r0, [sp, #120]              // load m0 ^ m1
    str.w   r1, [sp]                    // store S0 ^ m1 to free r1
    eor     r6, r6, r0                  // r6 <- BYTE_ROR_6(S4) ^ m1        remask r6
    eor     r6, r8, r6, ror #8          // r6 <- S4 ^ BYTE_ROR_6(S4 >>> 8) ^ m0 ^ m1
    bic     r1, r8, r3                  // r1 <- S4 ^m0 & 0xfcfcfcfc
    and     r8, r8, r3                  // r8 <- S4 ^m0 & 0x03030303
    orr     r8, r8, r1, ror #8          // r8 <- r8^r1 >>> 8
    eor     r8, r7, r8, ror #18         // r8 <- S5 ^ BYTE_ROR_6(S5 >>> 8) ^ BYTE_ROR_2(S4 >>> 24) ^m0^m1
    eor     r8, r8, r14                 // r8 <- S5^S0 ^ BYTE_ROR_6(S5^S0 >>> 8) ^ BYTE_ROR_2(S4 >>> 24) ^m1
    and     r1, r3, r6, lsr #6          // r1 <- (r6 >> 6) & 0x03030303
    bic     r7, r6, r3, ror #2          // r7 <- r6 & 0x3f3f3f3f
    orr     r7, r1, r7, lsl #2          // r7 <- BYTE_ROR_6(r6) ^ m0 ^ m1
    eor     r8, r8, r7, ror #8          // r8 <- S'4 ^ m0
    and     r7, r3, r4, lsr #6          // r7 <- (S3 ^m0 >> 6) & 0x03030303
    bic     r1, r4, r3, ror #2          // r1 <- S3^m0 & 0x3f3f3f3f
    orr     r7, r7, r1, lsl #2          // r7 <- BYTE_ROR_6(S3 ^m0)
    eor     r7, r7, r0                  // r7 <- BYTE_ROR_6(S3) ^ m1        remask r7
    eor     r1, r4, r7, ror #8          // r1 <- S3 ^ BYTE_ROR_6(S3) ^ m0 ^ m1
    bic     r7, r4, r3                  // r1 <- S3 ^m0 & 0xfcfcfcfc
    and     r4, r4, r3                  // r8 <- S3 ^m0 & 0x03030303
    orr     r4, r4, r7, ror #8          // r8 <- r8^r7 >>> 8
    eor     r7, r6, r4, ror #18         // r8 <- S4 ^ BYTE_ROR_6(S4 >>> 8) ^ BYTE_ROR_2(S3 >>> 24) ^m1
    and     r6, r3, r1, lsr #6          // r6 <- (r1 >> 6) & 0x03030303
    bic     r4, r1, r3, ror #2          // r4 <- r1 & 0x3f3f3f3f
    orr     r6, r6, r4, lsl #2          // r6 <- BYTE_ROR_6(r1) ^ m0 ^ m1
    eor     r7, r7, r6, ror #8          // r7 <- ^ m0
    eor     r7, r7, r0                  // r7 <- ^ m1 remask r7
    eor     r7, r7, r14                 // r7 <- S'3 ^ m0 ^ m1
    eor     r7, r7, r2                  // r7 <- S'3  ^  m0     remask r7
    and     r4, r3, r12, lsr #6         // r4 <- (S2 ^m1 >> 6) & 0x03030303
    bic     r6, r12, r3, ror #2         // r6 <- S2^m1 & 0x3f3f3f3f
    orr     r4, r4, r6, lsl #2          // r4 <- BYTE_ROR_6(S2 ^m1)
    eor     r4, r4, r0                  // r4 <- BYTE_ROR_6(S2) ^m0         remask r4
    eor     r4, r12, r4, ror #8         // r4 <- S2 ^ BYTE_ROR_6(s2) ^ m0^m1
    bic     r6, r12, r3                 // r1 <- S2 ^m1 & 0xfcfcfcfc
    and     r12, r12, r3                // r12<- S2 ^m1 & 0x03030303
    orr     r12, r12, r6, ror #8        // r12<- r12^r6 >>> 8
    eor     r6, r1, r12, ror #18        // r6 <- S3 ^ BYTE_ROR_6(S3 >>> 8) ^ BYTE_ROR_2(S2 >>> 24) ^m0
    and     r12, r3, r4, lsr #6         // r12<- (r4 >> 6) & 0x03030303
    bic     r1, r4, r3, ror #2          // r1 <- r4 & 0x3f3f3f3f
    orr     r12, r12, r1, lsl #2        // r12<- BYTE_ROR_6(r4) ^ m0 ^ m1
    eor     r6, r6, r12, ror #8         // r6 <- S'2 ^ m1
    and     r1, r3, r5, lsr #6          // r1 <- (S1 ^m0 >> 6) & 0x03030303
    bic     r12, r5, r3, ror #2         // r12<- S1^m0 & 0x3f3f3f3f
    orr     r1, r1, r12, lsl #2         // r1 <- BYTE_ROR_6(S1 ^m0)
    eor     r1, r1, r0                  // r1 <- BYTE_ROR_6(S1) ^m1
    eor     r1, r5, r1, ror #8          // r1 <- S1 ^ BYTE_ROR_6(S1) ^ m0 ^m1
    bic     r12, r5, r3                 // r12<- S1 ^m0 & 0xfcfcfcfc
    and     r5, r5, r3                  // r5 <- S1 ^m0 & 0x03030303
    orr     r5, r5, r12, ror #8         // r5 <- r5^r12 >>> 8
    eor     r5, r4, r5, ror #18         // r6 <- S2 ^ BYTE_ROR_6(S2 >>> 8) ^ BYTE_ROR_2(S1 >>> 24) ^m1
    and     r12, r3, r1, lsr #6         // r12<- (r1 >> 6) & 0x03030303
    bic     r4, r1, r3, ror #2          // r4 <- r1 & 0x3f3f3f3f
    orr     r12, r12, r4, lsl #2        // r12<- BYTE_ROR_6(r1) ^ m0 ^ m1
    eor     r5, r5, r12, ror #8         // r5 <- S'1 ^ m0
    eor     r1, r1, r2                  // r1 <- S1^ BYTE_ROR_6(S1) ^ m0        remask r1
    ldr.w   r4, [sp]                    // load S0
    and     r12, r3, r14, lsr #6        // r12<- (r14 >> 6) & 0x03030303
    bic     r14, r14, r3, ror #2        // r4 <- r14 & 0x3f3f3f3f
    orr     r12, r12, r14, lsl #2       // r12<- BYTE_ROR_6(r14)
    bic     r14, r4, r3                 // r14<- S0 ^m1 & 0xfcfcfcfc
    and     r4, r4, r3                  // r4 <- S0 ^m1 & 0x03030303
    orr     r4, r4, r14, ror #8         // r4 <- r4^r14 >>> 8
    ldr.w   r14, [sp, #132]             // restore link register
    eor     r4, r1, r4, ror #18         // r4 <- S1^ BYTE_ROR_6(S1) ^ BYTE_ROR_2(S0) ^ m0 ^ m1
    eor     r4, r4, r12, ror #8         // r4 <- S'0 ^ m1
    bx      lr
    //(r0, m0^m1), (r1, S0), (r2, m1), (r3, S6), (r4, S0),(r5, S1), (r6, S2),
    //(r7, S3), (r8, S4), (r9, S5), (r10, S6), (r11, S7), (r12, -), (r14, -)]

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations only, for round i s.t. (i%4) == 1.
* Note that 1st-order masking forces to do some remasking to ensure that masks
* are not cancelled through XOR operations.
******************************************************************************/
.align 2
mixcolumns_1:
    str     r14, [sp, #132]
    eor     r14, r1, r9                 // r14<- S0 ^ m1 ^ m0           remask S0
    movw    r9, #0x0f0f
    movt    r9, #0x0f0f                 // r9<- 0x0f0f0f0f (mask for BYTE_ROR_4)
    and     r11, r9, r6, lsr #4         // r11<- (S7 ^ m1 >> 4) & 0x0f0f0f0f
    and     r7, r9, r6                  // r7 <- (S7 ^ m1) & 0x0f0f0f0f
    orr     r11, r11, r7, lsl #4        // r11<- BYTE_ROR_4(S7 ^ m1)
    eor     r7, r11, r10                // r7 <- BYTE_ROR_4(S7 ^ m1) ^ (m0 ^ m1)    remask r7
    eor     r7, r6, r7, ror #8          // r7 <- S7 ^ (BYTE_ROR_4(S7) >>> 8) ^ m0 ^ m1
    eor     r10, r2, r7, ror #16        // r10<- (S7 ^ (BYTE_ROR_4(S7) >>> 8)) >>> 16 ^ m0 remask r7
    eor     r11, r10, r11, ror #8       // r11<- ^ m0 ^ m1
    and     r10, r9, r14, lsr #4        // r10<- (S0 ^ m0 ^ m1 >> 4) & 0x0f0f0f0f
    and     r14, r9, r14                // r14<- (S0 ^ m0 ^ m1) & 0x0f0f0f0f
    orr     r6, r10, r14, lsl #4        // r6 <- BYTE_ROR_4(S0 ^ m0 ^ m1)
    eor     r14, r1, r6, ror #8         // r14<- S0 ^ (BYTE_ROR_4(S0) >>> 8) ^ m0
    mov.w   r1, r6                      // r1 <- BYTE_ROR_4(S0) ^ m0 ^ m1
    eor     r11, r11, r14               // r11<- S'7 ^ m1
    eor     r10, r7, r14                // r10 <- S7 ^ (BYTE_ROR_4(S7) >>> 8) ^ S0 ^ (BYTE_ROR_4(S0) >>> 8) ^ m1
    and     r6, r9, r3, lsr #4          // r6 <- (S6 ^ m0 ^ m1 >> 4) & 0x0f0f0f0f
    and     r7, r9, r3                  // r7 <- (S6 ^ m0 ^ m1) & 0x0f0f0f0f
    orr     r7, r6, r7, lsl #4          // r7 <- BYTE_ROR_4(S6 ^ m0 ^ m1)
    eor     r10, r10, r7, ror #8        // r10 <- ^ m0
    eor     r6, r3, r2                  // r6 <- S6 ^ m0                remask S6
    eor     r7, r6, r7, ror #8          // r7 <- S6 ^  BYTE_ROR_4(S6) >>> 8 ^ m1
    eor     r10, r10, r7, ror #16       // r10 <- S'6 ^ m0 ^ m1
    mov.w   r3, r9                      // move the mask for BYTEROR to r3
    and     r6, r3, r0, lsr #4          // r6 <- (S5 ^ m0 ^ m1 >> 4) & 0x0f0f0f0f
    and     r9, r3, r0                  // r9 <- (S5 ^ m0 ^ m1) & 0x0f0f0f0f
    orr     r6, r6, r9, lsl #4          // r6 <- BYTE_ROR_4(S5 ^ m0 ^ m1)
    eor     r7, r7, r6, ror #8          // r7 <- S6 ^  BYTE_ROR_4(S6) >>> 8 ^ BYTE_ROR_4(S5) ^ m0
    eor     r9, r0, r2                  // r9 <- S5 ^ m0                remask S5
    eor     r6, r9, r6, ror #8          // r6 <- S5 ^ BYTE_ROR4(S5) >>> 8 ^ m1
    eor     r9, r7, r6, ror #16         // r9 <- S'5 ^ m0 ^ m1
    and     r7, r3, r8, lsr #4          // r7 <- (S4 ^ m0 >> 4) & 0x0f0f0f0f
    and     r0, r3, r8                  // r0 <- (S4 ^ m0) & 0x0f0f0f0f
    orr     r7, r7, r0, lsl #4          // r7 <- BYTE_ROR_4(S4 ^ m0)
    eor     r6, r6, r7, ror #8          // r6 <- S5 ^ BYTE_ROR4(S5) >>> 8 ^ BYTE_ROR_4(S4) >>>8 ^ m1 ^ m0
    ldr.w   r0, [sp, #120]              // load m0 ^ m1 in r0
    eor     r7, r7, r0                  // r7 <- BYTE_ROR_4(S4) ^ m1    remask r7
    eor     r7, r8, r7, ror #8          // r7 <- S4 ^ BYTE_ROR_4(S4)>>>8 ^ m0 ^ m1
    eor     r8, r6, r14                 // r8 <- ^ m1
    eor     r8, r8, r7, ror #16         // r8 <- S'4 ^ m0 
    eor     r7, r7, r2                  // r7 <- S4 ^ BYTE_ROR_4(S4)>>>8 ^ m0   remask r7
    and     r6, r3, r4, lsr #4          // r6 <- (S3 ^ m0 >> 4) & 0x0f0f0f0f
    and     r2, r3, r4                  // r2 <- (S3 ^ m0) & 0x0f0f0f0f
    orr     r6, r6, r2, lsl #4          // r6 <- BYTE_ROR_4(S3 ^ m0)
    eor     r2, r6, r0                  // r2 <- BYTE_ROR_4(S3) ^ m1        remask S3
    eor     r2, r4, r2, ror #8          // r2 <- S3 ^ BYTE_ROR_4(S3) >>> 8 ^ m0 ^ m1
    eor     r7, r7, r2, ror #16         // r7 <- ^ m1
    eor     r7, r7, r6, ror #8          // r7 <- ^ m0 ^ m1
    eor     r7, r7, r14                 // r7 <- S'3 ^ m1
    eor     r7, r7, r0                  // r7 <- S'3 ^ m0                   remask S'3
    and     r4, r3, r12, lsr #4         // r4 <- (S2 ^ m1 >> 4) & 0x0f0f0f0f
    and     r6, r3, r12                 // r3 <- (S2 ^ m1) & 0x0f0f0f0f
    orr     r4, r4, r6, lsl #4          // r4 <- BYTE_ROR_4(S2 ^ m1)
    eor     r6, r2, r4, ror #8          // r6 <- S3 ^ BYTE_ROR_4(S3) >>> 8 ^ BYTE_ROR_4(S2)>>>8 ^ m0
    eor     r4, r4, r0                  // r4 <- BYTE_ROR_4(S2) ^ m0        remask r4
    eor     r4, r12, r4, ror #8         // r4 <- S2 ^ BYTE_ROR_4(S2)>>>8 ^ m1 ^ m0
    eor     r6, r6, r4, ror #16         // r6 <- S'2 ^ m1
    and     r12, r3, r5, lsr #4         // r12<- (S1 ^ m0 >> 4) & 0x0f0f0f0f
    and     r3, r3, r5                  // r3 <- (S1 ^ m0) & 0x0f0f0f0f
    orr     r12, r12, r3, lsl #4        // r12<- BYTE_ROR_4(S1 ^ m0)
    eor     r4, r4, r12, ror #8         // r4 <- S2 ^ BYTE_ROR_4(S2)>>>8 ^ BYTE_ROR_4(S1)>>>8 ^ m1
    eor     r12, r12, r0                // r12<- BYTE_ROR_4(S1) ^ m1        remask r12
    eor     r12, r5, r12, ror #8        // r12<- S1 ^ BYTE_ROR_4(S1)>>>8 ^ m0 ^ m1
    eor     r5, r4, r12, ror #16        // r5 <- S'1 ^ m0
    eor     r4, r12, r14, ror #16       // r4 <- S1^BYTE_ROR_4(S1)>>>8 ^ (S0^BYTE_ROR_4(S0) >>> 8)>>>16 ^ m1
    eor     r4, r4, r1, ror #8          // r4 <- ^ m0
    eor     r4, r4, r0                  // r4 <- S'0 ^ m1                   remask
    ldr     r14, [sp, #132]              // restore link register
    ldr.w   r2, [sp, #124]              // load m1 in r2
    bx      lr
    //(r0, m0^m1), (r1, S0), (r2, m1), (r3, S6), (r4, S0),(r5, S1), (r6, S2),
    //(r7, S3), (r8, S4), (r9, S5), (r10, S6), (r11, S7), (r12, -), (r14, -)]

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations only, for rounds i s.t. (i%4) == 2.
* Note that 1st-order masking forces to do some remasking to ensure that masks
* are not cancelled through XOR operations.
******************************************************************************/
.align 2
mixcolumns_2:
    str     r14, [sp, #132]
    eor     r14, r1, r9                 // r14<- S0 ^ m1 ^ m0           remask S0
    movw    r9, #0x3f3f
    movt    r9, #0x3f3f                 // r9 <- 0x03030303 (mask for BYTE_ROR_2)
    and     r11, r9, r14, lsr #2        // r11<- (S0 ^ m0 ^ m1 >> 2) & 0x3f3f3f3f
    bic     r14, r14, r9, ror #6        // r14<- S0 ^ m0 ^ m1 & 0x03030303
    orr     r7, r11, r14, lsl #6        // r7 <- BYTE_ROR_2(S0 ^ m0 ^ m1)
    eor     r14, r1, r7, ror #8         // r14<- S0 ^ BYTE_ROR_2(S0 >>> 8) ^ m0
    and     r11, r9, r6, lsr #2         // r11<- (S7 ^ m1 >> 2) & 0x3f3f3f3f
    bic     r7, r6, r9, ror #6          // r7 <- S7^m1 & 0x03030303
    orr     r7, r11, r7, lsl #6         // r7 <- BYTE_ROR_2(S7 ^ m1)
    eor     r10, r7, r10                // r10<- BYTE_ROR_2(S7 ^ m1) ^ (m0 ^ m1)    remask r7
    eor     r10, r6, r10, ror #8        // r10<- S7 ^ (BYTE_ROR_2(S7) >>> 8) ^ m0 ^ m1
    bic     r11, r6, r9                 // r11<- S7 ^ m1 & 0xfcfcfcfc
    and     r6, r6, r9                  // r6 <- S7 ^m1 & 0x3f3f3f3f
    orr     r6, r6, r11, ror #8         // r6 <- r6 ^r11 >>> 8
    eor     r11, r14, r6, ror #22       // r11<- S0 ^ BYTE_ROR_2(S0 >>> 8) ^ BYTE_ROR_6(S7 >>> 24) ^ m0
    eor     r7, r10, r2                 // r7 <- S7 ^ (BYTE_ROR_2(S7) >>> 8) ^ m0   remask r10
    and     r6, r9, r7, lsr #2          // r6 <- (r7 >> 2) & 0x3f3f3f3f
    bic     r7, r7, r9, ror #6          // r7 <- r7 & 0x03030303
    orr     r7, r6, r7, lsl #6          // r7 <- BYTE_ROR_2(r7) ^ m0
    eor     r11, r11, r7, ror #8        // r11<- S'7 ^ m1
    eor     r10, r10, r14               // r10<- S7^S0 ^ BYTE_ROR_2(S7^S0 >>> 8) ^ m1 
    and     r7, r9, r3, lsr #2          // r7 <- (S6 ^m0^m1 >> 2) & 0x3f3f3f3f
    bic     r6, r3, r9, ror #6          // r6 <- S6^m0^m1 & 0x03030303
    orr     r6, r7, r6, lsl #6          // r6 <- BYTE_ROR_2(S6 ^m0^m1)
    eor     r6, r6, r2                  // r6 <- BYTE_ROR_2(S6 ^m0)             remask r6
    eor     r6, r3, r6, ror #8          // r6 <- S6 ^ BYTE_ROR_2(S6 >>> 8)^m1
    bic     r7, r3, r9                  // r7 <- S6 ^m0^m1 & 0xfcfcfcfc
    and     r3, r3, r9                  // r3 <- S6 ^m0^m1 & 0x3f3f3f3f
    orr     r3, r3, r7, ror #8          // r3 <- r3 ^r7 >>> 8
    eor     r10, r10, r3, ror #22       // r10<- ^m0
    and     r3, r9, r6, lsr #2          // r3 <- (r6 >> 2) & 0x3f3f3f3f
    bic     r7, r6, r9, ror #6          // r7 <- r6 & 0x03030303
    orr     r7, r3, r7, lsl #6          // r7 <- BYTE_ROR_2(r6) ^ m0
    eor     r10, r10, r7, ror #8
    mov.w   r3, r9                      // move the mask for BYTEROR to r3
    and     r7, r3, r0, lsr #2          // r7 <- (S5 ^m0^m1 >> 2) & 0x3f3f3f3f
    bic     r9, r0, r3, ror #6          // r9 <- S5^m0^m1 & 0x03030303
    orr     r9, r7, r9, lsl #6          // r9 <- BYTE_ROR_2(S5 ^m0^m1)
    eor     r9, r9, r2                  // r9 <- BYTE_ROR_2(S5 ^m0)             remask r6
    eor     r7, r0, r9, ror #8          // r7 <- S5 ^ BYTE_ROR_2(S5) ^ m1
    bic     r9, r0, r3                  // r9 <- S5 ^m0^m1 & 0xfcfcfcfc
    and     r0, r0, r3                  // r0 <- S5 ^m0^m1 & 0x3f3f3f3f
    orr     r0, r0, r9, ror #8          // r0 <- r0 ^r9 >>> 8
    eor     r9, r6, r0, ror #22         // r9 <- S6 ^ BYTE_ROR_2(S6 >>> 8) ^ BYTE_ROR_6(S5 >>> 24) ^m0
    and     r0, r3, r7, lsr #2          // r3 <- (r7 >> 2) & 0x3f3f3f3f
    bic     r6, r7, r3, ror #6          // r6 <- r7 & 0x03030303
    orr     r6, r0, r6, lsl #6          // r6 <- BYTE_ROR_2(r7) ^ m1
    eor     r9, r9, r6, ror #8          // r9 <- S'5 ^ m0 ^ m1
    and     r6, r3, r8, lsr #2          // r6 <- (S4 ^m0 >> 2) & 0x3f3f3f3f
    bic     r0, r8, r3, ror #6          // r0 <- S4^m0 & 0x03030303
    orr     r6, r6, r0, lsl #6          // r6 <- BYTE_ROR_2(S4 ^m0)
    ldr.w   r0, [sp, #120]              // load m0 ^ m1
    str.w   r1, [sp]                    // store S0 ^ m1 to free r1
    eor     r6, r6, r0                  // r6 <- BYTE_ROR_2(S4) ^ m1        remask r6
    eor     r6, r8, r6, ror #8          // r6 <- S4 ^ BYTE_ROR_2(S4 >>> 8) ^ m0 ^ m1
    bic     r1, r8, r3                  // r1 <- S4 ^m0 & 0xfcfcfcfc
    and     r8, r8, r3                  // r8 <- S4 ^m0 & 0x3f3f3f3f
    orr     r8, r8, r1, ror #8          // r8 <- r8^r1 >>> 8
    eor     r8, r7, r8, ror #22         // r8 <- S5 ^ BYTE_ROR_2(S5 >>> 8) ^ BYTE_ROR_6(S4 >>> 24) ^m0^m1
    eor     r8, r8, r14                 // r8 <- S5^S0 ^ BYTE_ROR_2(S5^S0 >>> 8) ^ BYTE_ROR_6(S4 >>> 24) ^m1
    and     r1, r3, r6, lsr #2          // r1 <- (r6 >> 2) & 0x3f3f3f3f
    bic     r7, r6, r3, ror #6          // r7 <- r6 & 0x03030303
    orr     r7, r1, r7, lsl #6          // r7 <- BYTE_ROR_2(r6) ^ m0 ^ m1
    eor     r8, r8, r7, ror #8          // r8 <- S'4 ^ m0
    and     r7, r3, r4, lsr #2          // r7 <- (S3 ^m0 >> 2) & 0x3f3f3f3f
    bic     r1, r4, r3, ror #6          // r1 <- S3^m0 & 0x03030303
    orr     r7, r7, r1, lsl #6          // r7 <- BYTE_ROR_2(S3 ^m0)
    eor     r7, r7, r0                  // r7 <- BYTE_ROR_2(S3) ^ m1        remask r7
    eor     r1, r4, r7, ror #8          // r1 <- S3 ^ BYTE_ROR_2(S3) ^ m0 ^ m1
    bic     r7, r4, r3                  // r1 <- S3 ^m0 & 0xfcfcfcfc
    and     r4, r4, r3                  // r8 <- S3 ^m0 & 0x3f3f3f3f
    orr     r4, r4, r7, ror #8          // r8 <- r8^r7 >>> 8
    eor     r7, r6, r4, ror #22         // r8 <- S4 ^ BYTE_ROR_2(S4 >>> 8) ^ BYTE_ROR_6(S3 >>> 24) ^m1
    and     r6, r3, r1, lsr #2          // r6 <- (r1 >> 2) & 0x3f3f3f3f
    bic     r4, r1, r3, ror #6          // r4 <- r1 & 0x03030303
    orr     r6, r6, r4, lsl #6          // r6 <- BYTE_ROR_2(r1) ^ m0 ^ m1
    eor     r7, r7, r6, ror #8          // r7 <- ^ m0
    eor     r7, r7, r0                  // r7 <- ^ m1 remask r7
    eor     r7, r7, r14                 // r7 <- S'3 ^ m0 ^ m1
    eor     r7, r7, r2                  // r7 <- S'3  ^  m0     remask r7
    and     r4, r3, r12, lsr #2         // r4 <- (S2 ^m1 >> 2) & 0x3f3f3f3f
    bic     r6, r12, r3, ror #6         // r6 <- S2^m1 & 0x03030303
    orr     r4, r4, r6, lsl #6          // r4 <- BYTE_ROR_2(S2 ^m1)
    eor     r4, r4, r0                  // r4 <- BYTE_ROR_2(S2) ^m0         remask r4
    eor     r4, r12, r4, ror #8         // r4 <- S2 ^ BYTE_ROR_2(s2) ^ m0^m1
    bic     r6, r12, r3                 // r1 <- S2 ^m1 & 0xfcfcfcfc
    and     r12, r12, r3                // r12<- S2 ^m1 & 0x3f3f3f3f
    orr     r12, r12, r6, ror #8        // r12<- r12^r6 >>> 8
    eor     r6, r1, r12, ror #22        // r6 <- S3 ^ BYTE_ROR_2(S3 >>> 8) ^ BYTE_ROR_6(S2 >>> 24) ^m0
    and     r12, r3, r4, lsr #2         // r12<- (r4 >> 2) & 0x3f3f3f3f
    bic     r1, r4, r3, ror #6          // r1 <- r4 & 0x03030303
    orr     r12, r12, r1, lsl #6        // r12<- BYTE_ROR_2(r4) ^ m0 ^ m1
    eor     r6, r6, r12, ror #8         // r6 <- S'2 ^ m1
    and     r1, r3, r5, lsr #2          // r1 <- (S1 ^m0 >> 2) & 0x3f3f3f3f
    bic     r12, r5, r3, ror #6         // r12<- S1^m0 & 0x03030303
    orr     r1, r1, r12, lsl #6         // r1 <- BYTE_ROR_2(S1 ^m0)
    eor     r1, r1, r0                  // r1 <- BYTE_ROR_2(S1) ^m1
    eor     r1, r5, r1, ror #8          // r1 <- S1 ^ BYTE_ROR_2(S1) ^ m0 ^m1
    bic     r12, r5, r3                 // r12<- S1 ^m0 & 0xfcfcfcfc
    and     r5, r5, r3                  // r5 <- S1 ^m0 & 0x3f3f3f3f
    orr     r5, r5, r12, ror #8         // r5 <- r5^r12 >>> 8
    eor     r5, r4, r5, ror #22         // r6 <- S2 ^ BYTE_ROR_2(S2 >>> 8) ^ BYTE_ROR_6(S1 >>> 24) ^m1
    and     r12, r3, r1, lsr #2         // r12<- (r1 >> 2) & 0x3f3f3f3f
    bic     r4, r1, r3, ror #6          // r4 <- r1 & 0x03030303
    orr     r12, r12, r4, lsl #6        // r12<- BYTE_ROR_2(r1) ^ m0 ^ m1
    eor     r5, r5, r12, ror #8         // r5 <- S'1 ^ m0
    eor     r1, r1, r2                  // r1 <- S1^ BYTE_ROR_2(S1) ^ m0        remask r1
    ldr.w   r4, [sp]                    // load S0
    and     r12, r3, r14, lsr #2        // r12<- (r14 >> 2) & 0x3f3f3f3f
    bic     r14, r14, r3, ror #6        // r4 <- r14 & 0x03030303
    orr     r12, r12, r14, lsl #6       // r12<- BYTE_ROR_2(r14)
    bic     r14, r4, r3                 // r14<- S0 ^m1 & 0xfcfcfcfc
    and     r4, r4, r3                  // r4 <- S0 ^m1 & 0x3f3f3f3f
    orr     r4, r4, r14, ror #8         // r4 <- r4^r14 >>> 8
    ldr     r14, [sp, #132]
    eor     r4, r1, r4, ror #22         // r4 <- S1^ BYTE_ROR_2(S1) ^ BYTE_ROR_6(S0) ^ m0 ^ m1
    eor     r4, r4, r12, ror #8         // r4 <- S'0 ^ m1
    bx      lr
    //(r0, m0^m1), (r1, S0), (r2, m1), (r3, S6), (r4, S0),(r5, S1), (r6, S2),
    //(r7, S3), (r8, S4), (r9, S5), (r10, S6), (r11, S7), (r12, -), (r14, -)]

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations, it is used for rounds i s.t. (i%4) == 3.
* For semi-fixsliced implementations, it is used for rounds i s.t. (i%2) == 1.
* Based on Käsper-Schwabe, similar to https://github.com/Ko-/aes-armcortexm.
* Note that 1st-order masking forces to do some remasking to ensure that masks
* are not cancelled through XOR operations.
******************************************************************************/
.align 2
mixcolumns_3:
    str     r14, [sp, #132]
    eor     r14, r1, r9                 // r14<- S0 ^ m1 ^ m0           remask S0
    eor     r14, r1, r14, ror #8        // r14<- (S0 ^ S0 >>> 8) ^ m0
    eor     r7, r6, r10                 // r7 <- S7 ^ m1 ^ (m0 ^ m1)    remask S7
    eor     r7, r6, r7, ror #8          // r7 <- (S7 ^ S7 >>> 8) ^ m0 ^ m1
    eor     r11, r7, r2                 // r11<- (S7 ^ S7 >>> 8) ^ m0   remask r7
    eor     r11, r6, r11, ror #8        // r11<- (S7 ^ S7 >>> 8 ^ S7 >>> 16) ^ m0 ^ m1
    eor     r11, r14, r11, ror #8       // r11<- S'7 ^ m1
    eor     r9, r3, r2                  // r9 <- S6 ^ m0 ^ m1 ^ m1      remask S6
    eor     r9, r3, r9, ror #8          // r9 <- (S6 ^ S6 >>> 8) ^ m1
    eor     r10, r7, r9, ror #16        // r10<- (S7 ^ S7 >>> 8) ^(S6 >>> 16 ^ S6 >>> 24) ^ m0
    eor     r10, r10, r3, ror #8        // r10<- r10 ^ S6 >>> 8 ^ m0 ^ m1
    eor     r10, r10, r14               // r10<- S'6 ^ m0 ^ m1
    eor     r6, r0, r2                  // r5 <- S5 ^ m0 ^ m1 ^ m1      remask S5
    eor     r6, r0, r6, ror #8          // r5 <- (S5 ^ S5 >>> 8) ^ m1
    eor     r9, r9, r0, ror #8          // r9 <- (S6 ^ S6 >>> 8) ^ S5 >>> 8 ^ m0
    ldr.w   r0, [sp, #120]              // load m0 ^ m1
    eor     r9, r9, r6, ror #16         // r9 <- S'5 ^ m0 ^ m1 
    eor     r7, r8, r0                  // r7 <- S4 ^ m0 ^ (m0 ^ m1)    remask S4
    eor     r7, r8, r7, ror #8          // r7 <- (S4 ^ S4 >>> 8) ^ m0 ^ m1
    eor     r3, r14, r7, ror #16        // r3 <- r7 >>> 8 ^ (S0 ^ S0 >>> 8) ^ m0
    eor     r3, r3, r8, ror #8          // r3 <- r3 ^ S4 >>> 8 ^ m0
    eor     r8, r3, r6                  // r8 <- S'4 ^ m0
    eor     r6, r4, r0                  // r6 <- S3 ^ m0 ^ (m0 ^ m1)    remask S3
    eor     r6, r4, r6, ror #8          // r6 <- (S3 ^ S3 >>> 8) ^ m0 ^ m1
    eor     r7, r7, r2                  // r7 <- (S4 ^ S4 >>> 8) ^ m0   remask r7
    eor     r7, r7, r6, ror #16         // r7 <- ^ m1
    eor     r7, r7, r4, ror #8          // r7 <- ^ m1 ^ m0
    eor     r7, r7, r14                 // r7 <- S'3 ^ m1
    eor     r7, r7, r0                  // r7 <- S'3 ^ m0               remask S'3
    eor     r3, r12, r0                 // r3 <- S2 ^ m1 ^ (m0 ^ m1)    remask S2
    eor     r3, r12, r3, ror #8         // r3 <- (S2 ^ S2 >>> 8) ^ m0 ^ m1
    eor     r6, r6, r12, ror #8         // r6 <- ^ m0
    eor     r6, r6, r3, ror #16         // r6 <- S'6 ^ m1
    eor     r4, r5, r0                  // r4 <- S1 ^ m0 ^ m0 ^ m1      remask S1
    eor     r4, r5, r4, ror #8          // r4 <- (S1 ^ S1 >>> 8) ^ m0 ^ m1
    eor     r5, r3, r5, ror #8          // r5 <- ^ m1
    eor     r5, r5, r4, ror #16         // r5 <- S'1 ^ m0
    eor     r4, r4, r2                  // r4 <- (S1 ^ S1 >>> 8) ^ m0   remask r4
    eor     r4, r4, r1, ror #8          // r4 <- S1 ^ S1 >>> 8 ^ S0 >>> 8 ^ m0 ^ m1
    eor     r4, r4, r14, ror #16        // r4 <- S'0 ^ m1
    ldr     r14, [sp, #132]
    bx      lr
    //(r0, m0^m1), (r1, S0), (r2, m1), (r3, S6), (r4, S0),(r5, S1), (r6, S2),
    //(r7, S3), (r8, S4), (r9, S5), (r10, S6), (r11, S7), (r12, -), (r14, -)]

/******************************************************************************
* Applies the ShiftRows transformation twice (i.e. SR^2) on the internal state.
******************************************************************************/
.align 2
double_shiftrows:
    str     r14, [sp, #132]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00
    swpmv   r6,r6,r6,r6, r14, #4, r11
    swpmv   r3,r3,r3,r3, r14, #4, r11
    swpmv   r0,r0,r0,r0, r14, #4, r11
    swpmv   r8,r8,r8,r8, r14, #4, r11
    swpmv   r4,r4,r4,r4, r14, #4, r11
    swpmv   r12,r12,r12,r12, r14, #4, r11
    swpmv   r5,r5,r5,r5, r14, #4, r11
    swpmv   r1,r1,r1,r1, r14, #4, r11
    ldr     r14, [sp, #132]
    ldr.w   r2, [sp, #124]          // loads m1 in r2
    bx      lr

/******************************************************************************
* Fully fixsliced implementation of AES-128 with 1st-order masking.
*
* Two blocks are encrypted in parallel.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
*
* The masking step is specific to the STM32F407VG due to some specific values
* values and addresses related to the randomn number generator (RNG).
******************************************************************************/
@ void aes128_encrypt_ffs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                        const u8* ptext_bis, const u32* rkey);
.global aes128_encrypt_ffs
.type   aes128_encrypt_ffs,%function
.align 2
aes128_encrypt_ffs:
    push    {r0-r12,r14}
    sub.w   sp, #136
    ldr.w   r4, [r2]                // load the 1st 128-bit blocks in r4-r7
    ldr     r5, [r2, #4]
    ldr     r6, [r2, #8]
    ldr     r7, [r2, #12]
    ldr.w   r8, [r3]                // load the 2nd 128-bit blocks in r8-r11
    ldr     r9, [r3, #4]
    ldr     r10,[r3, #8]
    ldr     r11,[r3, #12]
    bl      packing
    // ------------------ MASKING ------------------
    // generation of 1 random word
    movw    r0, 0x0804
    movt    r0, 0x5006              // r0 <- RNG_SR = 0x50060804
    add.w   r1, r0, #4              // r1 <- RNG_DR = 0x50060808
aes128_ffs_get_random_mask:
    ldr.w   r2, [r0]
    cmp     r2, #1                  // check if RNG_SR == RNG_SR_DRDY
    bne     aes128_ffs_get_random_mask   // loop while RNG status is not ready
    ldr.w   r2, [r1]                // load the random number in r2
    ubfx    r12, r2, #0, #2         // r1 <- ab 
    orr     r12, r12, r12, lsl #2   // r1 <- abab
    orr     r12, r12, r12, lsl #4   // r1 <- abababab
    orr     r12, r12, r12, lsl #8   // r1 <- abababababababab
    orr     r12, r12, r12, lsl #16  // r1 <- abababababababababababababababab
    ubfx.w  r2, r2, #2, #2          // r2 <- cd 
    orr     r2, r2, r2, lsl #2      // r2 <- cdcd
    orr     r2, r2, r2, lsl #4      // r2 <- cdcdcdcd
    orr     r2, r2, r2, lsl #8      // r2 <- cdcdcdcdcdcdcdcd
    orr     r2, r2, r2, lsl #16     // r2 <- cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
    eor     r0, r12, r2             // r2 <- m0 ^ m1
    eor     r4, r4, r2              // r4 <- state[0] ^ m1
    eor     r5, r5, r12             // r5 <- state[1] ^ m0
    eor     r6, r6, r2              // r6 <- state[2] ^ m1
    eor     r7, r7, r12             // r7 <- state[3] ^ m0
    eor     r8, r8, r12             // r8 <- state[4] ^ m0
    eor     r9, r9, r0              // r9 <- state[5] ^ m2
    eor     r10, r10, r0            // r10<- state[6] ^ m2
    eor     r11, r11, r2            // r11<- state[7] ^ m1
    // ------------------ MASKING ------------------
    // ------------------ CORE FUNCTION ------------------
    ldr.w   r3, [sp, #192]          // to match add_round_key routine
    str.w   r3, [sp, #116]          // to match add_round_key routine
    str     r12, [sp, #128]
    strd    r0, r2, [sp, #120]
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_1
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_2
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_1
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_2
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    mov     r11, r6                 // to match add_round_key routine
    mov     r10, r3                 // to match add_round_key routine
    mov     r9, r0                  // to match add_round_key routine
    mov.w   r7, r4                  // to match add_round_key routine
    mov.w   r6, r12                 // to match add_round_key routine
    mov.w   r4, r1                  // to match add_round_key routine
    ldr.w   r0, [sp, #120]          // loads m0^m1 in r0
    bl      add_round_key
    // ------------------ CORE FUNCTION ------------------
    // ------------------ UNMASKING ------------------
    eor     r4, r4, r2              // r4 <- state[0] ^ m1
    eor     r5, r5, r12             // r5 <- state[1] ^ m0
    eor     r6, r6, r2              // r6 <- state[2] ^ m1
    eor     r7, r7, r12             // r7 <- state[3] ^ m0
    eor     r8, r8, r12             // r8 <- state[4] ^ m0
    eor     r9, r9, r0              // r9 <- state[5] ^ m0 ^ m1
    eor     r10, r10, r0            // r10<- state[6] ^ m0 ^ m1
    eor     r11, r11, r2            // r11<- state[7] ^ m1
    // ------------------ UNMASKING ------------------
    bl      unpacking
    ldrd    r0, r1, [sp, #136]
    add.w   sp, #144
    stm     r0, {r4-r7}
    stm     r1, {r8-r11}
    pop     {r2-r12, r14}
    bx      lr

/******************************************************************************
* Semi fixsliced implementation of AES-128 with 1st-order masking.
*
* Two blocks are encrypted in parallel.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
*
* The masking step is specific to the STM32F407VG due to some specific values
* values and addresses related to the randomn number generator (RNG).
******************************************************************************/
@ void aes128_encrypt_sfs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                        const u8* ptext_bis, const u32* rkey);
.global aes128_encrypt_sfs
.type   aes128_encrypt_sfs,%function
.align 2
aes128_encrypt_sfs:
    push    {r0-r12,r14}
    sub.w   sp, #136
    ldr.w   r4, [r2]                // load the 1st 128-bit blocks in r4-r7
    ldr     r5, [r2, #4]
    ldr     r6, [r2, #8]
    ldr     r7, [r2, #12]
    ldr.w   r8, [r3]                // load the 2nd 128-bit blocks in r8-r11
    ldr     r9, [r3, #4]
    ldr     r10,[r3, #8]
    ldr     r11,[r3, #12]
    bl      packing
    // ------------------ MASKING ------------------
    // generation of 1 random word
    movw    r0, 0x0804
    movt    r0, 0x5006              // r0 <- RNG_SR = 0x50060804
    add.w   r1, r0, #4              // r1 <- RNG_DR = 0x50060808
aes128_sfs_get_random_mask:
    ldr.w   r2, [r0]
    cmp     r2, #1                  // check if RNG_SR == RNG_SR_DRDY
    bne     aes128_sfs_get_random_mask   // loop while RNG status is not ready
    ldr.w   r2, [r1]                // load the random number in r2
    ubfx    r12, r2, #0, #2         // r1 <- ab 
    orr     r12, r12, r12, lsl #2   // r1 <- abab
    orr     r12, r12, r12, lsl #4   // r1 <- abababab
    orr     r12, r12, r12, lsl #8   // r1 <- abababababababab
    orr     r12, r12, r12, lsl #16  // r1 <- abababababababababababababababab
    ubfx.w  r2, r2, #2, #2          // r2 <- cd 
    orr     r2, r2, r2, lsl #2      // r2 <- cdcd
    orr     r2, r2, r2, lsl #4      // r2 <- cdcdcdcd
    orr     r2, r2, r2, lsl #8      // r2 <- cdcdcdcdcdcdcdcd
    orr     r2, r2, r2, lsl #16     // r2 <- cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
    eor     r0, r12, r2             // r2 <- m0 ^ m1
    eor     r4, r4, r2              // r4 <- state[0] ^ m1
    eor     r5, r5, r12             // r5 <- state[1] ^ m0
    eor     r6, r6, r2              // r6 <- state[2] ^ m1
    eor     r7, r7, r12             // r7 <- state[3] ^ m0
    eor     r8, r8, r12             // r8 <- state[4] ^ m0
    eor     r9, r9, r0              // r9 <- state[5] ^ m2
    eor     r10, r10, r0            // r10<- state[6] ^ m2
    eor     r11, r11, r2            // r11<- state[7] ^ m1
    // ------------------ MASKING ------------------
    // ------------------ CORE FUNCTION ------------------
    ldr.w   r3, [sp, #192]          // to be compliant with add_round_key routine
    str.w   r3, [sp, #116]          // to be compliant with add_round_key routine
    str     r12, [sp, #128]
    strd    r0, r2, [sp, #120]
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    bl      mixcolumns_3
    bl      add_round_key
    bl      sbox
    bl      mixcolumns_0
    bl      add_round_key
    bl      sbox
    bl      double_shiftrows
    mov     r11, r6                 // to match add_round_key routine
    mov     r10, r3                 // to match add_round_key routine
    mov     r9, r0                  // to match add_round_key routine
    mov.w   r7, r4                  // to match add_round_key routine
    mov.w   r6, r12                 // to match add_round_key routine
    mov.w   r4, r1                  // to match add_round_key routine
    ldr.w   r0, [sp, #120]          // loads m0^m1 in r0
    bl      add_round_key
    // ------------------ CORE FUNCTION ------------------
    // ------------------ UNMASKING ------------------
    eor     r4, r4, r2              // r4 <- state[0] ^ m1
    eor     r5, r5, r12             // r5 <- state[1] ^ m0
    eor     r6, r6, r2              // r6 <- state[2] ^ m1
    eor     r7, r7, r12             // r7 <- state[3] ^ m0
    eor     r8, r8, r12             // r8 <- state[4] ^ m0
    eor     r9, r9, r0              // r9 <- state[5] ^ m0 ^ m1
    eor     r10, r10, r0            // r10<- state[6] ^ m0 ^ m1
    eor     r11, r11, r2            // r11<- state[7] ^ m1
    // ------------------ UNMASKING ------------------
    bl      unpacking
    ldrd    r0, r1, [sp, #136]
    add.w   sp, #144
    stm     r0, {r4-r7}
    stm     r1, {r8-r11}
    pop     {r2-r12, r14}
    bx      lr
