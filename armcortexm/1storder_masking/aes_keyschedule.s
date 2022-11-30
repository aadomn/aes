/******************************************************************************
* First-order masked bitsliced implementation of the AES-128 key schedule in
* ARM assembly.
*
* The masking scheme is the one described in "Masking AES with 2 random bits"
* available at https://eprint.iacr.org/2018/1007.
* All bytes within a round key are masked in the following way:
* m1 || m0^m1 || m0^m1 || m0 || m0 || m1 || m0 || m1 where m0, m1 are random
* bits. For each round key, m0 and m1 are picked randomly.
* Note that because the function prototype allows to pass 2 different keys as
* input parameters, 4 random bits are used instead of 2 to ensure that
* different round keys are masked with different masks.
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
* Packing routine. Note that it is the same as the one used in the encryption
* function so some code size could be saved by merging the two files.
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
* 1st-order masked implementation of the S-box in a bitsliced manner.
* Credits to https://github.com/LaurenDM/TwoRandomBits.
* The bitsliced key state should be contained in r4-r11 while the masks
* m2=m0^m1, m1, m0 are supposed to be stored in sp[120,124,128].
* Note that it is the same subroutine as the one used in the encryption
* function so some code size could be saved by merging the two files.
******************************************************************************/
.align 2
sbox:
    str     r14, [sp, #132]             // save link register
    mov.w   r14, r2
    orr     r0, r12, r14                //Exec (m0 | m1) = m0 | m1 into r0
    eor     r2,  r7,  r9                //Exec y14 = i4 ^ i2 into r2
    str.w   r0, [sp, #112]              //Store r0/(m0 | m1) on stack
    eor     r0,  r4, r10                //Exec y13 = i7 ^ i1 into r0
    eor     r1,  r0, r14                //Exec hy13 = y13 ^ m1 into r1
    eor     r3,  r4,  r7                //Exec y9 = i7 ^ i4 into r3
    str.w   r3, [sp, #108]              //Store r3/y9 on stack
    eor     r3,  r3, r14                //Exec hy9 = y9 ^ m1 into r3
    str.w   r1, [sp, #104]              //Store r1/hy13 on stack
    eor     r1,  r4,  r9                //Exec y8 = i7 ^ i2 into r1
    eor     r6,  r5,  r6                //Exec t0 = i6 ^ i5 into r6
    str.w   r3, [sp, #100]              //Store r3/hy9 on stack
    eor     r3,  r6, r11                //Exec y1 = t0 ^ i0 into r3
    str.w   r6, [sp, #96]               //Store r6/t0 on stack
    eor     r6,  r3, r14                //Exec hy1 = y1 ^ m1 into r6
    eor     r7,  r6,  r7                //Exec y4 = hy1 ^ i4 into r7
    str.w   r7, [sp, #92]               //Store r7/y4 on stack
    eor     r7,  r7, r12                //Exec hy4 = y4 ^ m0 into r7
    str.w   r0, [sp, #88]               //Store r0/y13 on stack
    eor     r0,  r0,  r2                //Exec y12 = y13 ^ y14 into r0
    str.w   r6, [sp, #84]               //Store r6/hy1 on stack
    eor     r6,  r3,  r4                //Exec y2 = y1 ^ i7 into r6
    eor     r10,  r3, r10                //Exec y5 = y1 ^ i1 into r10
    str.w   r2, [sp, #80]               //Store r2/y14 on stack
    eor     r2, r10,  r1                //Exec y3 = y5 ^ y8 into r2
    str     r10, [sp, #60]               //Store r10/y5 on stack
    eor     r2,  r2, r14                //Exec hy3 = y3 ^ m1 into r2
    eor     r8,  r8,  r0                //Exec t1 = i3 ^ y12 into r8
    eor     r9,  r8,  r9                //Exec y15 = t1 ^ i2 into r9
    str.w   r6, [sp, #76]               //Store r6/y2 on stack
    eor     r6,  r9, r14                //Exec hy15 = y15 ^ m1 into r6
    eor     r5,  r8,  r5                //Exec y20 = t1 ^ i6 into r5
    eor     r8,  r9, r11                //Exec y6 = y15 ^ i0 into r8
    str.w   r6, [sp, #72]               //Store r6/hy15 on stack
    eor     r6,  r8, r12                //Exec hy6 = y6 ^ m0 into r6
    str.w   r6, [sp, #68]               //Store r6/hy6 on stack
    ldr.w   r6, [sp, #96]               //Load t0 into r6
    str.w   r3, [sp, #64]               //Store r3/y1 on stack
    eor     r3,  r9,  r6                //Exec y10 = y15 ^ t0 into r3
    eor     r10,  r3, r12               //Exec hy10 = y10 ^ m0 into r10
    str     r10, [sp, #56]              //Store r10/hy10 on stack
    ldr     r10, [sp, #100]             //Load hy9 into r10
    str.w   r5, [sp, #100]              //Store r5/y20 on stack
    eor     r10,  r5, r10               //Exec y11 = y20 ^ hy9 into r10
    eor     r5, r10, r12                //Exec hy11 = y11 ^ m0 into r5
    eor     r14, r11,  r5               //Exec y7 = i0 ^ hy11 into r14
    eor     r5,  r3,  r5                //Exec y17 = y10 ^ hy11 into r5
    str.w   r1, [sp, #52]               //Store r1/y8 on stack
    eor     r1,  r3,  r1                //Exec y19 = y10 ^ y8 into r1
    str.w   r1, [sp, #96]               //Store r1/y19 on stack
    eor     r6,  r6, r10                //Exec y16 = t0 ^ y11 into r6
    ldr.w   r1, [sp, #104]              //Load hy13 into r1
    str.w   r3, [sp, #48]               //Store r3/y10 on stack
    eor     r3,  r1,  r6                //Exec y21 = hy13 ^ y16 into r3
    str.w   r3, [sp, #32]               //Store r3/y21 on stack
    eor     r4,  r4,  r6                //Exec y18 = i7 ^ y16 into r4
    str.w   r4, [sp, #44]               //Store r4/y18 on stack
    and     r4,  r0,  r9                //Exec t2_0 = y12 & y15 into r4
    str.w   r0, [sp, #40]               //Store r0/y12 on stack
    and     r0,  r0, r12                //Exec t2_1 = y12 & m0 into r0
    str.w   r0, [sp, #36]               //Store r0/t2_1 on stack
    eor     r0,  r0, r12                //Exec t2_2 = t2_1 ^ m0 into r0
    eor     r0,  r4,  r0                //Exec t2_3 = t2_0 ^ t2_2 into r0
    ldr.w   r4, [sp, #120]              //Load m2 into r4
    ldr.w   r3, [sp, #112]              //Load (m0 | m1) into r3
    and     r9,  r4,  r9                //Exec t2_4 = m2 & y15 into r9
    eor     r9,  r9,  r3                //Exec t2_5 = t2_4 ^ (m0 | m1) into r9
    eor     r0,  r0,  r9                //Exec t2 = t2_3 ^ t2_5 into r0
    and     r9,  r2,  r8                //Exec t3_0 = hy3 & y6 into r9
    str.w   r2, [sp, #28]               //Store r2/hy3 on stack
    and     r2,  r2,  r4                //Exec t3_1 = hy3 & m2 into r2
    str.w   r2, [sp, #24]               //Store r2/t3_1 on stack
    eor     r2,  r2,  r4                //Exec t3_2 = t3_1 ^ m2 into r2
    eor     r2,  r9,  r2                //Exec t3_3 = t3_0 ^ t3_2 into r2
    and     r8, r12,  r8                //Exec t3_4 = m0 & y6 into r8
    eor     r8,  r8,  r3                //Exec t3_5 = t3_4 ^ (m0 | m1) into r8
    eor     r2,  r2,  r8                //Exec t3 = t3_3 ^ t3_5 into r2
    eor     r2,  r2,  r0                //Exec t4 = t3 ^ t2 into r2
    and     r8, r11,  r7                //Exec t5_0 = i0 & hy4 into r8
    and     r9, r11,  r4                //Exec t5_1 = i0 & m2 into r9
    str     r9, [sp, #20]               //Store r9/t5_1 on stack
    eor     r9,  r9,  r4                //Exec t5_2 = t5_1 ^ m2 into r9
    eor     r8,  r8,  r9                //Exec t5_3 = t5_0 ^ t5_2 into r8
    ldr     r9, [sp, #124]              //Load m1 into r9
    and     r7,  r9,  r7                //Exec t5_4 = m1 & hy4 into r7
    eor     r7,  r7,  r3                //Exec t5_5 = t5_4 ^ (m0 | m1) into r7
    eor     r7,  r8,  r7                //Exec t5 = t5_3 ^ t5_5 into r7
    eor     r0,  r7,  r0                //Exec t6 = t5 ^ t2 into r0
    and     r7,  r1,  r6                //Exec t7_0 = hy13 & y16 into r7
    and     r1,  r1, r12                //Exec t7_1 = hy13 & m0 into r1
    eor     r1,  r1, r12                //Exec t7_2 = t7_1 ^ m0 into r1
    eor     r1,  r7,  r1                //Exec t7_3 = t7_0 ^ t7_2 into r1
    and     r7,  r6,  r4                //Exec t7_4 = y16 & m2 into r7
    eor     r8,  r7,  r3                //Exec t7_5 = t7_4 ^ (m0 | m1) into r8
    str.w   r7, [sp, #104]              //Store r7/t7_4 on stack
    eor     r1,  r1,  r8                //Exec t7 = t7_3 ^ t7_5 into r1
    ldr     r8, [sp, #64]               //Load y1 into r8
    ldr.w   r7, [sp, #60]               //Load y5 into r7
    str.w   r6, [sp, #16]               //Store r6/y16 on stack
    and     r6,  r8,  r7                //Exec t8_0 = y1 & y5 into r6
    and     r8,  r8,  r9                //Exec t8_1 = y1 & m1 into r8
    eor     r8,  r8,  r9                //Exec t8_2 = t8_1 ^ m1 into r8
    eor     r6,  r6,  r8                //Exec t8_3 = t8_0 ^ t8_2 into r6
    and     r8,  r7, r12                //Exec t8_4 = y5 & m0 into r8
    str     r8, [sp, #64]               //Store r8/t8_4 on stack
    eor     r8,  r8,  r3                //Exec t8_5 = t8_4 ^ (m0 | m1) into r8
    eor     r6,  r6,  r8                //Exec t8 = t8_3 ^ t8_5 into r6
    ldr     r8, [sp, #76]               //Load y2 into r8
    str     r14, [sp, #12]              //Store r14/y7 on stack
    eor     r6,  r6,  r1                //Exec t9 = t8 ^ t7 into r6
    and     r7, r14,  r8                //Exec t10_0 = y7 & y2 into r7
    and     r14, r14,  r4               //Exec t10_1 = y7 & m2 into r14
    eor     r14, r14,  r4               //Exec t10_2 = t10_1 ^ m2 into r14
    eor     r7,  r7, r14                //Exec t10_3 = t10_0 ^ t10_2 into r7
    and     r14, r12,  r8               //Exec t10_4 = m0 & y2 into r14
    eor     r14, r14,  r3               //Exec t10_5 = t10_4 ^ (m0 | m1) into r14
    eor     r7,  r7, r14                //Exec t10 = t10_3 ^ t10_5 into r7
    eor     r1,  r7,  r1                //Exec t11 = t10 ^ t7 into r1
    ldr.w   r7, [sp, #108]              //Load y9 into r7
    and     r14, r10,  r7               //Exec t12_0 = y11 & y9 into r14
    and     r8, r10,  r4                //Exec t12_1 = y11 & m2 into r8
    eor     r8,  r8,  r4                //Exec t12_2 = t12_1 ^ m2 into r8
    eor     r8, r14,  r8                //Exec t12_3 = t12_0 ^ t12_2 into r8
    and     r14,  r9,  r7               //Exec t12_4 = m1 & y9 into r14
    eor     r14, r14,  r3               //Exec t12_5 = t12_4 ^ (m0 | m1) into r14
    eor     r8,  r8, r14                //Exec t12 = t12_3 ^ t12_5 into r8
    ldr     r14, [sp, #80]              //Load y14 into r14
    str.w   r5, [sp, #8 ]               //Store r5/y17 on stack
    and     r7,  r5, r14                //Exec t13_0 = y17 & y14 into r7
    and     r5,  r5,  r9                //Exec t13_1 = y17 & m1 into r5
    eor     r5,  r5,  r9                //Exec t13_2 = t13_1 ^ m1 into r5
    eor     r5,  r7,  r5                //Exec t13_3 = t13_0 ^ t13_2 into r5
    and     r7, r12, r14                //Exec t13_4 = m0 & y14 into r7
    eor     r7,  r7,  r3                //Exec t13_5 = t13_4 ^ (m0 | m1) into r7
    eor     r5,  r5,  r7                //Exec t13 = t13_3 ^ t13_5 into r5
    eor     r5,  r5,  r8                //Exec t14 = t13 ^ t12 into r5
    ldr.w   r7, [sp, #52]               //Load y8 into r7
    ldr     r14, [sp, #48]              //Load y10 into r14
    str     r10, [sp, #4 ]              //Store r10/y11 on stack
    and     r10,  r7, r14               //Exec t15_0 = y8 & y10 into r10
    and     r7,  r7,  r9                //Exec t15_1 = y8 & m1 into r7
    str.w   r7, [sp, #0 ]               //Store r7/t15_1 on stack
    eor     r7,  r7,  r9                //Exec t15_2 = t15_1 ^ m1 into r7
    eor     r7, r10,  r7                //Exec t15_3 = t15_0 ^ t15_2 into r7
    and     r10, r12, r14               //Exec t15_4 = m0 & y10 into r10
    eor     r10, r10,  r3               //Exec t15_5 = t15_4 ^ (m0 | m1) into r10
    eor     r7,  r7, r10                //Exec t15 = t15_3 ^ t15_5 into r7
    eor     r7,  r7,  r8                //Exec t16 = t15 ^ t12 into r7
    ldr     r8, [sp, #100]              //Load y20 into r8
    eor     r2,  r2,  r8                //Exec t17 = t4 ^ y20 into r2
    eor     r0,  r0,  r7                //Exec t18 = t6 ^ t16 into r0
    eor     r6,  r6,  r5                //Exec t19 = t9 ^ t14 into r6
    eor     r1,  r1,  r7                //Exec t20 = t11 ^ t16 into r1
    eor     r2,  r2,  r5                //Exec t21 = t17 ^ t14 into r2
    ldr.w   r5, [sp, #96]               //Load y19 into r5
    eor     r0,  r0,  r5                //Exec t22 = t18 ^ y19 into r0
    ldr.w   r5, [sp, #32]               //Load y21 into r5
    ldr.w   r7, [sp, #44]               //Load y18 into r7
    str     r11, [sp, #100]             //Store r11/i0 on stack
    eor     r5,  r6,  r5                //Exec t23 = t19 ^ y21 into r5
    eor     r6,  r5, r12                //Exec ht23 = t23 ^ m0 into r6
    eor     r1,  r1,  r7                //Exec t24 = t20 ^ y18 into r1
    eor     r7,  r1, r12                //Exec ht24 = t24 ^ m0 into r7
    eor     r8,  r2,  r0                //Exec t25 = t21 ^ t22 into r8
    and     r10,  r5,  r2               //Exec t26_0 = t23 & t21 into r10
    and     r14,  r5,  r9               //Exec t26_1 = t23 & m1 into r14
    eor     r14, r14,  r9               //Exec t26_2 = t26_1 ^ m1 into r14
    eor     r10, r10, r14               //Exec t26_3 = t26_0 ^ t26_2 into r10
    and     r2,  r4,  r2                //Exec t26_4 = m2 & t21 into r2
    eor     r2,  r2,  r3                //Exec t26_5 = t26_4 ^ (m0 | m1) into r2
    eor     r2, r10,  r2                //Exec t26 = t26_3 ^ t26_5 into r2
    eor     r10,  r1,  r2               //Exec t27 = t24 ^ t26 into r10
    and     r14,  r8, r10               //Exec t28_0 = t25 & t27 into r14
    and     r11,  r8, r12               //Exec t28_1 = t25 & m0 into r11
    eor     r11, r11, r12               //Exec t28_2 = t28_1 ^ m0 into r11
    eor     r11, r14, r11               //Exec t28_3 = t28_0 ^ t28_2 into r11
    and     r14,  r4, r10               //Exec t28_4 = m2 & t27 into r14
    eor     r14, r14,  r3               //Exec t28_5 = t28_4 ^ (m0 | m1) into r14
    eor     r11, r11, r14               //Exec t28 = t28_3 ^ t28_5 into r11
    eor     r11, r11,  r0               //Exec t29 = t28 ^ t22 into r11
    eor     r5,  r5,  r1                //Exec t30 = t23 ^ t24 into r5
    eor     r0,  r0,  r2                //Exec t31 = t22 ^ t26 into r0
    and     r2,  r5,  r0                //Exec t32_0 = t30 & t31 into r2
    and     r5,  r5,  r9                //Exec t32_1 = t30 & m1 into r5
    eor     r5,  r5,  r9                //Exec t32_2 = t32_1 ^ m1 into r5
    eor     r2,  r2,  r5                //Exec t32_3 = t32_0 ^ t32_2 into r2
    and     r0, r12,  r0                //Exec t32_4 = m0 & t31 into r0
    eor     r0,  r0,  r3                //Exec t32_5 = t32_4 ^ (m0 | m1) into r0
    eor     r0,  r2,  r0                //Exec t32 = t32_3 ^ t32_5 into r0
    eor     r0,  r0,  r1                //Exec t33 = t32 ^ t24 into r0
    eor     r1,  r0, r12                //Exec ht33 = t33 ^ m0 into r1
    eor     r2,  r6,  r0                //Exec t34 = ht23 ^ t33 into r2
    eor     r5, r10,  r0                //Exec t35 = t27 ^ t33 into r5
    and     r6,  r5,  r7                //Exec t36_0 = t35 & ht24 into r6
    and     r5,  r5,  r4                //Exec t36_1 = t35 & m2 into r5
    eor     r5,  r5,  r4                //Exec t36_2 = t36_1 ^ m2 into r5
    eor     r5,  r6,  r5                //Exec t36_3 = t36_0 ^ t36_2 into r5
    and     r6,  r9,  r7                //Exec t36_4 = m1 & ht24 into r6
    eor     r6,  r6,  r3                //Exec t36_5 = t36_4 ^ (m0 | m1) into r6
    eor     r5,  r5,  r6                //Exec t36 = t36_3 ^ t36_5 into r5
    eor     r2,  r5,  r2                //Exec t37 = t36 ^ t34 into r2
    eor     r5, r10,  r5                //Exec t38 = t27 ^ t36 into r5
    and     r6, r11,  r5                //Exec t39_0 = t29 & t38 into r6
    and     r7, r11,  r4                //Exec t39_1 = t29 & m2 into r7
    eor     r7,  r7,  r4                //Exec t39_2 = t39_1 ^ m2 into r7
    eor     r6,  r6,  r7                //Exec t39_3 = t39_0 ^ t39_2 into r6
    str.w   r7, [sp, #96]               //Store r7/t39_2 on stack
    and     r5,  r9,  r5                //Exec t39_4 = m1 & t38 into r5
    eor     r5,  r5,  r3                //Exec t39_5 = t39_4 ^ (m0 | m1) into r5
    eor     r5,  r6,  r5                //Exec t39 = t39_3 ^ t39_5 into r5
    eor     r5,  r8,  r5                //Exec t40 = t25 ^ t39 into r5
    eor     r6,  r5,  r2                //Exec t41 = t40 ^ t37 into r6
    eor     r8, r11,  r0                //Exec t42 = t29 ^ t33 into r8
    eor     r10, r11,  r5               //Exec t43 = t29 ^ t40 into r10
    eor     r1,  r1,  r2                //Exec t44 = ht33 ^ t37 into r1
    eor     r14,  r8,  r6               //Exec t45 = t42 ^ t41 into r14
    ldr.w   r7, [sp, #72]               //Load hy15 into r7
    str.w   r6, [sp, #48]               //Store r6/t41 on stack
    and     r6,  r1,  r7                //Exec z0_0 = t44 & hy15 into r6
    str.w   r1, [sp, #44]               //Store r1/t44 on stack
    and     r1,  r1,  r4                //Exec z0_1 = t44 & m2 into r1
    eor     r1,  r1,  r4                //Exec z0_2 = z0_1 ^ m2 into r1
    eor     r6,  r6,  r1                //Exec z0_3 = z0_0 ^ z0_2 into r6
    and     r7, r12,  r7                //Exec z0_4 = m0 & hy15 into r7
    eor     r7,  r7,  r3                //Exec z0_5 = z0_4 ^ (m0 | m1) into r7
    eor     r6,  r6,  r7                //Exec z0 = z0_3 ^ z0_5 into r6
    ldr.w   r7, [sp, #68]               //Load hy6 into r7
    str.w   r6, [sp, #72]               //Store r6/z0 on stack
    and     r6,  r7,  r2                //Exec z1_0 = hy6 & t37 into r6
    and     r7,  r7,  r4                //Exec z1_1 = hy6 & m2 into r7
    eor     r7,  r7,  r4                //Exec z1_2 = z1_1 ^ m2 into r7
    eor     r6,  r6,  r7                //Exec z1_3 = z1_0 ^ z1_2 into r6
    and     r7,  r9,  r2                //Exec z1_4 = m1 & t37 into r7
    eor     r7,  r7,  r3                //Exec z1_5 = z1_4 ^ (m0 | m1) into r7
    eor     r6,  r6,  r7                //Exec z1 = z1_3 ^ z1_5 into r6
    ldr.w   r7, [sp, #100]              //Load i0 into r7
    str.w   r6, [sp, #100]              //Store r6/z1 on stack
    and     r7,  r0,  r7                //Exec z2_0 = t33 & i0 into r7
    and     r6,  r0,  r9                //Exec z2_1 = t33 & m1 into r6
    eor     r6,  r6,  r9                //Exec z2_2 = z2_1 ^ m1 into r6
    str.w   r6, [sp, #68]               //Store r6/z2_2 on stack
    eor     r7,  r7,  r6                //Exec z2_3 = z2_0 ^ z2_2 into r7
    ldr.w   r6, [sp, #20]               //Load t5_1 into r6
    eor     r6,  r6,  r3                //Exec z2_5 = t5_1 ^ (m0 | m1) into r6
    eor     r6,  r7,  r6                //Exec z2 = z2_3 ^ z2_5 into r6
    str.w   r6, [sp, #32]               //Store r6/z2 on stack
    ldr.w   r7, [sp, #16]               //Load y16 into r7
    ldr.w   r6, [sp, #104]              //Load t7_4 into r6
    and     r7,  r7, r10                //Exec z3_0 = y16 & t43 into r7
    eor     r6,  r6,  r4                //Exec z3_2 = t7_4 ^ m2 into r6
    eor     r6,  r7,  r6                //Exec z3_3 = z3_0 ^ z3_2 into r6
    and     r7, r12, r10                //Exec z3_4 = m0 & t43 into r7
    str.w   r7, [sp, #104]              //Store r7/z3_4 on stack
    eor     r7,  r7,  r3                //Exec z3_5 = z3_4 ^ (m0 | m1) into r7
    eor     r6,  r6,  r7                //Exec z3 = z3_3 ^ z3_5 into r6
    ldr.w   r7, [sp, #84]               //Load hy1 into r7
    str.w   r6, [sp, #20]               //Store r6/z3 on stack
    and     r6,  r7,  r5                //Exec z4_0 = hy1 & t40 into r6
    and     r7,  r7, r12                //Exec z4_1 = hy1 & m0 into r7
    eor     r7,  r7, r12                //Exec z4_2 = z4_1 ^ m0 into r7
    eor     r6,  r6,  r7                //Exec z4_3 = z4_0 ^ z4_2 into r6
    and     r7,  r4,  r5                //Exec z4_4 = m2 & t40 into r7
    eor     r7,  r7,  r3                //Exec z4_5 = z4_4 ^ (m0 | m1) into r7
    eor     r6,  r6,  r7                //Exec z4 = z4_3 ^ z4_5 into r6
    ldr.w   r7, [sp, #12]               //Load y7 into r7
    str.w   r6, [sp, #84]               //Store r6/z4 on stack
    and     r6, r11,  r7                //Exec z5_0 = t29 & y7 into r6
    str     r11, [sp, #16]              //Store r11/t29 on stack
    and     r11, r11, r12               //Exec z5_1 = t29 & m0 into r11
    eor     r11, r11, r12               //Exec z5_2 = z5_1 ^ m0 into r11
    eor     r6,  r6, r11                //Exec z5_3 = z5_0 ^ z5_2 into r6
    and     r7,  r9,  r7                //Exec z5_4 = m1 & y7 into r7
    eor     r7,  r7,  r3                //Exec z5_5 = z5_4 ^ (m0 | m1) into r7
    eor     r6,  r6,  r7                //Exec z5 = z5_3 ^ z5_5 into r6
    ldr.w   r7, [sp, #4 ]               //Load y11 into r7
    and     r11,  r7,  r8               //Exec z6_0 = y11 & t42 into r11
    and     r7,  r7, r12                //Exec z6_1 = y11 & m0 into r7
    eor     r7,  r7, r12                //Exec z6_2 = z6_1 ^ m0 into r7
    eor     r7, r11,  r7                //Exec z6_3 = z6_0 ^ z6_2 into r7
    and     r11,  r9,  r8               //Exec z6_4 = m1 & t42 into r11
    eor     r11, r11,  r3               //Exec z6_5 = z6_4 ^ (m0 | m1) into r11
    eor     r7,  r7, r11                //Exec z6 = z6_3 ^ z6_5 into r7
    ldr     r11, [sp, #8 ]              //Load y17 into r11
    str.w   r7, [sp, #12]               //Store r7/z6 on stack
    and     r7, r11, r14                //Exec z7_0 = y17 & t45 into r7
    and     r11, r11,  r4               //Exec z7_1 = y17 & m2 into r11
    eor     r11, r11,  r4               //Exec z7_2 = z7_1 ^ m2 into r11
    eor     r7,  r7, r11                //Exec z7_3 = z7_0 ^ z7_2 into r7
    and     r11, r12, r14               //Exec z7_4 = m0 & t45 into r11
    eor     r11, r11,  r3               //Exec z7_5 = z7_4 ^ (m0 | m1) into r11
    eor     r7,  r7, r11                //Exec z7 = z7_3 ^ z7_5 into r7
    ldr     r11, [sp, #56]              //Load hy10 into r11
    str.w   r6, [sp, #8 ]               //Store r6/z5 on stack
    eor     r6,  r5,  r2                //Recompute t41 = t40 ^ t37 into r6
    str.w   r7, [sp, #4 ]               //Store r7/z7 on stack
    and     r7, r11,  r6                //Exec z8_0 = hy10 & t41 into r7
    and     r11, r11,  r9               //Exec z8_1 = hy10 & m1 into r11
    eor     r11, r11,  r9               //Exec z8_2 = z8_1 ^ m1 into r11
    eor     r7,  r7, r11                //Exec z8_3 = z8_0 ^ z8_2 into r7
    and     r11,  r4,  r6               //Exec z8_4 = m2 & t41 into r11
    eor     r11, r11,  r3               //Exec z8_5 = z8_4 ^ (m0 | m1) into r11
    eor     r7,  r7, r11                //Exec z8 = z8_3 ^ z8_5 into r7
    str.w   r7, [sp, #56]               //Store r7/z8 on stack
    ldr     r11, [sp, #44]              //Load t44 into r11
    ldr.w   r7, [sp, #40]               //Load y12 into r7
    and     r7, r11,  r7                //Exec z9_0 = t44 & y12 into r7
    eor     r1,  r7,  r1                //Exec z9_3 = z9_0 ^ z0_2 into r1
    ldr.w   r7, [sp, #36]               //Load t2_1 into r7
    eor     r7,  r7,  r3                //Exec z9_5 = t2_1 ^ (m0 | m1) into r7
    eor     r1,  r1,  r7                //Exec z9 = z9_3 ^ z9_5 into r1
    ldr.w   r7, [sp, #28]               //Load hy3 into r7
    and     r7,  r2,  r7                //Exec z10_0 = t37 & hy3 into r7
    and     r2,  r2, r12                //Exec z10_1 = t37 & m0 into r2
    eor     r2,  r2, r12                //Exec z10_2 = z10_1 ^ m0 into r2
    eor     r2,  r7,  r2                //Exec z10_3 = z10_0 ^ z10_2 into r2
    ldr.w   r7, [sp, #24]               //Load t3_1 into r7
    eor     r7,  r7,  r3                //Exec z10_5 = t3_1 ^ (m0 | m1) into r7
    eor     r2,  r2,  r7                //Exec z10 = z10_3 ^ z10_5 into r2
    ldr.w   r7, [sp, #92]               //Load y4 into r7
    ldr     r11, [sp, #68]              //Load z2_2 into r11
    and     r0,  r0,  r7                //Exec z11_0 = t33 & y4 into r0
    eor     r0,  r0, r11                //Exec z11_3 = z11_0 ^ z2_2 into r0
    and     r7,  r4,  r7                //Exec z11_4 = m2 & y4 into r7
    eor     r7,  r7,  r3                //Exec z11_5 = z11_4 ^ (m0 | m1) into r7
    eor     r0,  r0,  r7                //Exec z11 = z11_3 ^ z11_5 into r0
    ldr.w   r7, [sp, #88]               //Load y13 into r7
    ldr     r11, [sp, #104]             //Load z3_4 into r11
    and     r10, r10,  r7               //Exec z12_0 = t43 & y13 into r10
    eor     r11, r11, r12               //Exec z12_2 = z3_4 ^ m0 into r11
    eor     r10, r10, r11               //Exec z12_3 = z12_0 ^ z12_2 into r10
    and     r7,  r4,  r7                //Exec z12_4 = m2 & y13 into r7
    eor     r7,  r7,  r3                //Exec z12_5 = z12_4 ^ (m0 | m1) into r7
    eor     r7, r10,  r7                //Exec z12 = z12_3 ^ z12_5 into r7
    ldr     r10, [sp, #60]              //Load y5 into r10
    ldr     r11, [sp, #64]              //Load t8_4 into r11
    str.w   r0, [sp, #104]              //Store r0/z11 on stack
    and     r10, r10,  r5               //Exec z13_0 = y5 & t40 into r10
    eor     r11, r11, r12               //Exec z13_2 = t8_4 ^ m0 into r11
    eor     r10, r10, r11               //Exec z13_3 = z13_0 ^ z13_2 into r10
    and     r5,  r9,  r5                //Exec z13_4 = m1 & t40 into r5
    eor     r5,  r5,  r3                //Exec z13_5 = z13_4 ^ (m0 | m1) into r5
    eor     r5, r10,  r5                //Exec z13 = z13_3 ^ z13_5 into r5
    ldr     r10, [sp, #16]              //Load t29 into r10
    ldr     r11, [sp, #76]              //Load y2 into r11
    ldr.w   r0, [sp, #96]               //Load t39_2 into r0
    and     r10, r10, r11               //Exec z14_0 = t29 & y2 into r10
    eor     r0, r10,  r0                //Exec z14_3 = z14_0 ^ t39_2 into r0
    and     r10,  r9, r11               //Exec z14_4 = m1 & y2 into r10
    eor     r10, r10,  r3               //Exec z14_5 = z14_4 ^ (m0 | m1) into r10
    eor     r0,  r0, r10                //Exec z14 = z14_3 ^ z14_5 into r0
    ldr     r10, [sp, #108]             //Load y9 into r10
    and     r11, r10,  r8               //Exec z15_0 = y9 & t42 into r11
    and     r10, r10, r12               //Exec z15_1 = y9 & m0 into r10
    eor     r10, r10, r12               //Exec z15_2 = z15_1 ^ m0 into r10
    eor     r10, r11, r10               //Exec z15_3 = z15_0 ^ z15_2 into r10
    and     r8,  r4,  r8                //Exec z15_4 = m2 & t42 into r8
    eor     r8,  r8,  r3                //Exec z15_5 = z15_4 ^ (m0 | m1) into r8
    eor     r8, r10,  r8                //Exec z15 = z15_3 ^ z15_5 into r8
    ldr     r10, [sp, #80]              //Load y14 into r10
    and     r11, r10, r14               //Exec z16_0 = y14 & t45 into r11
    and     r10, r10,  r4               //Exec z16_1 = y14 & m2 into r10
    eor     r10, r10,  r4               //Exec z16_2 = z16_1 ^ m2 into r10
    eor     r10, r11, r10               //Exec z16_3 = z16_0 ^ z16_2 into r10
    and     r11,  r9, r14               //Exec z16_4 = m1 & t45 into r11
    eor     r11, r11,  r3               //Exec z16_5 = z16_4 ^ (m0 | m1) into r11
    eor     r10, r10, r11               //Exec z16 = z16_3 ^ z16_5 into r10
    ldr     r11, [sp, #52]              //Load y8 into r11
    and     r11,  r6, r11               //Exec z17_0 = t41 & y8 into r11
    and     r6,  r6, r12                //Exec z17_1 = t41 & m0 into r6
    eor     r6,  r6, r12                //Exec z17_2 = z17_1 ^ m0 into r6
    eor     r6, r11,  r6                //Exec z17_3 = z17_0 ^ z17_2 into r6
    ldr     r11, [sp, #0 ]              //Load t15_1 into r11
    eor     r3, r11,  r3                //Exec z17_5 = t15_1 ^ (m0 | m1) into r3
    eor     r3,  r6,  r3                //Exec z17 = z17_3 ^ z17_5 into r3
    eor     r6,  r8, r10                //Exec tc1 = z15 ^ z16 into r6
    eor     r2,  r2,  r6                //Exec tc2 = z10 ^ tc1 into r2
    eor     r1,  r1,  r2                //Exec tc3 = z9 ^ tc2 into r1
    ldr     r10, [sp, #72]              //Load z0 into r10
    ldr     r11, [sp, #32]              //Load z2 into r11
    ldr     r14, [sp, #100]             //Load z1 into r14
    str.w   r3, [sp, #112]              //Store r3/z17 on stack
    eor     r11, r10, r11               //Exec tc4 = z0 ^ z2 into r11
    eor     r10, r14, r10               //Exec tc5 = z1 ^ z0 into r10
    ldr     r14, [sp, #20]              //Load z3 into r14
    ldr.w   r4, [sp, #84]               //Load z4 into r4
    ldr     r9, [sp, #4 ]               //Load z7 into r9
    ldr.w   r3, [sp, #56]               //Load z8 into r3
    eor     r4, r14,  r4                //Exec tc6 = z3 ^ z4 into r4
    eor     r12,  r7, r11               //Exec tc7 = z12 ^ tc4 into r12
    eor     r9,  r9,  r4                //Exec tc8 = z7 ^ tc6 into r9
    eor     r3,  r3, r12                //Exec tc9 = z8 ^ tc7 into r3
    eor     r3,  r9,  r3                //Exec tc10 = tc8 ^ tc9 into r3
    eor     r4,  r4, r10                //Exec tc11 = tc6 ^ tc5 into r4
    ldr     r10, [sp, #8 ]              //Load z5 into r10
    eor     r10, r14, r10               //Exec tc12 = z3 ^ z5 into r10
    eor     r5,  r5,  r6                //Exec tc13 = z13 ^ tc1 into r5
    eor     r6, r11, r10                //Exec tc14 = tc4 ^ tc12 into r6
    eor     r4,  r1,  r4                //Exec S3 = tc3 ^ tc11 into r4
    ldr     r10, [sp, #12]              //Load z6 into r10
    eor     r9, r10,  r9                //Exec tc16 = z6 ^ tc8 into r9
    eor     r0,  r0,  r3                //Exec tc17 = z14 ^ tc10 into r0
    eor     r5,  r5,  r6                //Exec tc18 = tc13 ^ tc14 into r5
    eor     r7,  r7,  r5                //Exec S7 = z12 ^ tc18 ^ 1 into r7
    eor     r8,  r8,  r9                //Exec tc20 = z15 ^ tc16 into r8
    ldr     r10, [sp, #104]             //Load z11 into r10
    eor     r2,  r2, r10                //Exec tc21 = tc2 ^ z11 into r2
    eor     r1,  r1,  r9                //Exec o7 = tc3 ^ tc16 into r1
    eor     r3,  r3,  r5                //Exec o1 = tc10 ^ tc18 ^ 1 into r3
    eor     r5,  r6,  r4                //Exec S4 = tc14 ^ S3 into r5
    eor     r6,  r4,  r9                //Exec S1 = S3 ^ tc16 ^ 1 into r6
    ldr     r9, [sp, #112]              //Load z17 into r9
    eor     r8,  r0,  r8                //Exec tc26 = tc17 ^ tc20 into r8
    eor     r8,  r8,  r9                //Exec S2 = tc26 ^ z17 ^ 1 into r8
    eor     r0,  r2,  r0                //Exec S5 = tc21 ^ tc17 into r0
    ldr.w   r2, [sp, #124]              //Load m1 into r2
    ldr     r9, [sp, #128]              //Load m0 into r9
    ldr     r10, [sp, #120]             //Load m2 into r10
    ldr     r14, [sp, #132]             // restore link register
    eor     r12,  r8,  r9               //Exec o5 = S2 ^ m0 into r12
    eor     r8,  r5,  r2                //Exec o3 = S4 ^ m1 into r8
    eor     r5,  r6,  r2                //Exec o6 = S1 ^ m1 into r5
    eor     r4,  r4, r10                //Exec o4 = S3 ^ m2 into r4
    eor     r0,  r0,  r9                //Exec o2 = S5 ^ m0 into r0
    eor     r6,  r7, r10                //Exec o0 = S7 ^ m2 into r6
    bx      lr 

/******************************************************************************
* Subroutine that applies a new mask on the round key right after the sbox.
* Before this subroutine the rkey is masked with m0, m1, m0^m1 while after the
* masks are now m0^m'0, m1^m'1, m0^m1^m'0^m'1 where m' refers to new masks.
******************************************************************************/
.align 2
remask_rkey:
    ldr.w   r2, [sp, #136]          // load NEW mask
    lsr     r2, r2, #4              // r2 <- r2 >> 4 (discard the 4 bits used in the prev round)
    ubfx    r9, r2, #0, #2          // r9 <- ab 
    orr     r9, r9, r9, lsl #2      // r9 <- abab
    orr     r9, r9, r9, lsl #4      // r9 <- abababab
    orr     r9, r9, r9, lsl #8      // r9 <- abababababababab
    orr     r9, r9, r9, lsl #16     // r9 <- abababababababababababababababab
    str.w   r2, [sp, #136]          // store the shifted mask for the next round
    ubfx.w  r2, r2, #2, #2          // r2 <- cd 
    orr     r2, r2, r2, lsl #2      // r2 <- cdcd
    orr     r2, r2, r2, lsl #4      // r2 <- cdcdcdcd
    orr     r2, r2, r2, lsl #8      // r2 <- cdcdcdcdcdcdcdcd
    orr     r2, r2, r2, lsl #16     // r2 <- cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
    eor     r10, r9, r2             // r10<- new_m0 ^ new_m1
    eor     r11, r6, r9             // r11<- key[7] ^ m1 ^ new_m1
    eor     r6, r12, r9             // r6 <- key[2] ^ m1 ^ new_m1
    eor     r8, r8, r2              // r8 <- key[4] ^ m0 ^ new_m0
    eor     r7, r4, r2              // r7 <- key[3] ^ m0 ^ new_m0
    eor     r1, r1, r9              // r1 <- key[0] ^ m1 ^ new_m1
    eor     r0, r0, r10             // r0 <- key[5] ^ m0 ^ m1 ^ new_m0 ^ new_m1
    eor     r4, r3, r10             // r4 <- key[6] ^ m0 ^ m1 ^ new_m0 ^ new_m1
    eor     r3, r5, r2              // r3 <- key[1] ^ m0 ^ new_m0
    ldr     r12, [sp, #116]         // restore 'rkeys' address
    ldr.w   r5, [r12, #40]          // load rkey word of rkey from prev round
    str     r10, [r12, #52]         // store new km0 ^ km1 in output array
    str     r10, [sp, #120]         // store new km0 ^ km1 on the stack
    strd    r2, r9, [r12, #44]      // store new km0, km1 in output array
    strd    r9, r2, [sp, #124]      // store new km0, km1 on the stack
    mov.w   r2, r4                  // mov r4 to r2 to be compliant with 'xor_columns' routines
    bx      lr

/******************************************************************************
* Subroutine that XORs the columns after the S-box during the key schedule
* round function, for rounds i such that (i % 4) == 0.
* Note that the code size could be reduced at the cost of some instructions
* since some redundant code is applied on different registers.
******************************************************************************/
.align 2
xor_columns_0:
    str     r14, [sp, #132]         // store link register
    ldr     r14, [r12, #4]          // load old mask
    movw    r4, #0xc0c0
    movt    r4, #0xc0c0             // r4 <- 0xc0c0c0c0
    eor     r11, r5, r11, ror #2    // r11<- r5 ^ (r11 >>> 2)
    bic     r11, r4, r11            // r11<- ~r11 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r11, r11, r9            // r11<- r11 | r9
    mvn     r9, r5                  // NOT omitted in sbox
    eor     r5, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r5, lsr #2    // r14<- r14 & 0x33333333
    eor     r11, r11, r14           // remask half of register
    ldr.w   r5, [r12, #36]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #8]          // load old mask
    str     r9, [r12, #40]          // store prev rkey word after NOT
    str     r11, [r12, #84]         // store new rkey word in 'rkeys'
    eor     r10, r5, r2, ror #2     // r10<- r5 ^ (r2 >>> 2)
    bic     r10, r4, r10            // r10<- ~r10 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r10, r10, r9            // r10<- r10 | r9
    mvn     r9, r5                  // NOT omitted in sbox
    eor     r5, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r5, lsr #2    // r14<- r14 & 0x33333333
    eor     r10, r10, r14           // remask half of register
    ldr.w   r2, [r12, #32]          // load rkey word of rkey from prev round
    str     r9, [r12, #36]          // store new rkey word after NOT
    str     r10, [r12, #80]         // store new rkey word in 'rkeys'
    eor     r9, r2, r0, ror #2      // r9 <- r2 ^ (r9 >>> 2)
    and     r9, r4, r9              // r9 <- r9 & 0xc0c0c0c0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r9, r9, r14             // remask half of register
    ldr.w   r2, [r12, #28]          // load rkey word of rkey from prev round
    ldr     r14, [r12]              // load old mask
    str.w   r9, [r12, #76]          // store new rkey word in 'rkeys'
    eor     r8, r2, r8, ror #2      // r8 <- r2 ^ (r8 >>> 2)
    and     r8, r4, r8              // r8 <- r8 & 0xc0c0c0c0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r8, r8, r14             // remask half of register
    ldr.w   r2, [r12, #24]          // load rkey word of rkey from prev round
    str.w   r8, [r12, #72]          // store new rkey word in 'rkeys'
    eor     r7, r2, r7, ror #2      // r7 <- r2 ^ (r7 >>> 2)
    and     r7, r4, r7              // r7 <- r7 & 0xc0c0c0c0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r7, r7, r14             // remask half of register
    ldr.w   r2, [r12, #20]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]          // load old mask
    str.w   r7, [r12, #68]          // store new rkey word in 'rkeys'
    eor     r6, r2, r6, ror #2      // r6 <- r2 ^ (r6 >>> 2)
    bic     r6, r4, r6              // r6 <- ~r6 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r6, r6, r0              // r6 <- r6 | r0
    mvn     r0, r2                  // NOT omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r6, r6, r14             // remask of half register
    ldr.w   r2, [r12, #16]          // load rkey word of rkey from prev round
    ldr     r14, [r12]              // load old mask
    str.w   r0, [r12, #20]          // store new rkey word after NOT
    str.w   r6, [r12, #64]          // store new rkey word in 'rkeys'
    eor     r5, r2, r3, ror #2      // r5 <- r2 ^ (r3 >>> 2)
    bic     r5, r4, r5              // r5 <- ~r5 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r5, r5, r0              // r5 <- r5 | r0
    mvn     r0, r2                  // NOT omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r5, r5, r14             // remask half of register
    ldr.w   r2, [r12, #12]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]          // load old mask
    str.w   r0, [r12, #16]          // store new rkey word after NOT
    str.w   r5, [r12, #60]          // store new rkey word in 'rkeys'
    eor     r3, r2, r1, ror #2      // r3 <- r2 ^ (r1 >>> 2)
    and     r3, r4, r3              // r3 <- r3 & 0xc0c0c0c0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    orr     r4, r3, r0              // r4 <- r3 | r0
    eor     r4, r4, r14             // remask half of register
    add     r12, #44                // point to the next rkey address
    str.w   r4, [r12, #12]          // store new rkey[0]
    ldr.w   r14, [sp, #132]         // restore link register
    str.w   r12, [sp, #116]         // store the new rkeys address on the stack
    ldrd    r12, r2, [r12]          // load masks MASK1 and MASK2 in r12, r2 (for sbox routine)
    bx      lr

/******************************************************************************
* Subroutine that XORs the columns after the S-box during the key schedule
* round function, for rounds i such that (i % 4) == 1.
* Note that the code size could be reduced at the cost of some instructions
* since some redundant code is applied on different registers.
******************************************************************************/
.align 2
xor_columns_1:
    str     r14, [sp, #132]
    ldr     r14, [r12, #4]          // load old mask
    movw    r4, #0xc0c0
    movt    r4, #0xc0c0             // r4 <- 0xc0c0c0c0
    eor     r11, r5, r11, ror #2    // r11<- r5 ^ (r11 >>> 2)
    bic     r11, r4, r11            // r11<- ~r11 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r11, r11, r9            // r11<- r11 | r9
    // applies ShiftRows^[-1]
    and     r9, r5, #0xfc00         // r9 <- r5 & 0x0000fc00
    and     r10, r5, #0x0300        // r10<- r5 & 0x00000300
    orr     r9, r9, r10, lsl #8     // r9 <- r9 | r10 << 8
    and     r10, r5, #0xf00000      // r10<- r5 & 0x00f00000
    orr     r9, r9, r10, lsr #2     // r9 <- r9 | r10 >> 2
    and     r10, r5, #0xf0000       // r10<- r5 & 0x000f0000
    orr     r9, r9, r10, lsl #6     // r9 <- r9 | r10 << 6
    and     r10, r5, #0xc0000000    // r10<- r5 & 0xc0000000
    orr     r9, r9, r10, lsr #4     // r9 <- r9 | r10 >> 4
    and     r10, r5, #0x3f000000    // r10<- r5 & 0x3f000000
    orr     r9, r9, r10, ror #28    // r9 <- r9 | (r10 >>> 28)
    and     r10, r5, #0xff          // r10<- r5 & 0xff
    orr     r9, r10, r9, ror #2     // r9 <- ShiftRows^[-1](r5)
    mvn     r9, r9                  // NOT that is omitted in sbox
    eor     r5, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r5, lsr #2    // r14<- r14 & 0x33333333
    eor     r11, r11, r14           // remask half of register
    ldr.w   r5, [r12, #36]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #8]          // load old mask
    str     r9, [r12, #40]          // store the prev rkey word after ShiftRows^[-1]
    str     r11, [r12, #84]         // store new rkey word in 'rkeys'
    eor     r10, r5, r2, ror #2     // r10<- r5 ^ (r2 >>> 2)
    bic     r10, r4, r10            // r10<- ~r10 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r10, r10, r9            // r10<- r10 | r9
    // applies ShiftRows^[-1]
    and     r9, r5, #0xfc00         // r9 <- r5 & 0x0000fc00
    and     r2, r5, #0x0300         // r2 <- r5 & 0x00000300
    orr     r9, r9, r2, lsl #8      // r9 <- r9 | r2 << 8
    and     r2, r5, #0xf00000       // r2 <- r5 & 0x00f00000
    orr     r9, r9, r2, lsr #2      // r9 <- r9 | r2 >> 2
    and     r2, r5, #0xf0000        // r2 <- r5 & 0x000f0000
    orr     r9, r9, r2, lsl #6      // r9 <- r9 | r2 << 6
    and     r2, r5, #0xc0000000     // r2 <- r5 & 0xc0000000
    orr     r9, r9, r2, lsr #4      // r9 <- r9 | r2 >> 4
    and     r2, r5, #0x3f000000     // r2 <- r5 & 0x3f000000
    orr     r9, r9, r2, ror #28     // r9 <- r9 | (r2 >>> 28)
    and     r2, r5, #0xff           // r2 <- r5 & 0xff
    orr     r5, r2, r9, ror #2      // r5 <- ShiftRows^[-1](r5)
    mvn     r5, r5                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r10, r10, r14           // remask half of register
    ldr.w   r2, [r12, #32]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #36]          // store the rkey word after ShiftRows^[-1]
    str     r10, [r12, #80]         // store new rkey word in 'rkeys'
    eor     r9, r2, r0, ror #2      // r9 <- r2 ^ (r9 >>> 2)
    and     r9, r4, r9              // r9 <- r9 & 0xc0c0c0c0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r9, r9, r0              // r9 <- r9 | r0
    // applies ShiftRows^[-1]
    and     r5, r2, #0xfc00         // r5 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsr #2      // r5 <- r5 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #6      // r5 <- r5 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r5, r5, r0, lsr #4      // r5 <- r5 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #2      // r5 <- ShiftRows^[-1](r2)
    eor     r9, r9, r14
    ldr.w   r2, [r12, #28]          // load rkey word of rkey from prev round
    ldr     r14, [r12]
    str.w   r5, [r12, #32]          // store the rkey word after ShiftRows^[-1]
    str.w   r9, [r12, #76]          // store new rkey word in 'rkeys'
    eor     r8, r2, r8, ror #2      // r8 <- r2 ^ (r8 >>> 2)
    and     r8, r4, r8              // r8 <- r8 & 0xc0c0c0c0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r8, r8, r0              // r8 <- r8 | r0
    // applies ShiftRows^[-1]
    and     r5, r2, #0xfc00         // r5 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsr #2      // r5 <- r5 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #6      // r5 <- r5 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r5, r5, r0, lsr #4      // r5 <- r5 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #2      // r5 <- ShiftRows^[-1](r2)
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r8, r8, r14             // remask half of register
    ldr.w   r2, [r12, #24]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #28]          // store the rkey word after ShiftRows^[-1]
    str.w   r8, [r12, #72]          // store new rkey word in 'rkeys'
    eor     r7, r2, r7, ror #2      // r7 <- r2 ^ (r7 >>> 2)
    and     r7, r4, r7              // r7 <- r7 & 0xc0c0c0c0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r7, r7, r0              // r7 <- r7 | r0
    // applies ShiftRows^[-1]
    and     r5, r2, #0xfc00         // r5 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsr #2      // r5 <- r5 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #6      // r5 <- r5 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r5, r5, r0, lsr #4      // r5 <- r5 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #2      // r5 <- ShiftRows^[-1](r2)
    eor     r7, r7, r14             // remask half of register
    ldr.w   r2, [r12, #20]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]          // load old mask
    str.w   r5, [r12, #24]          // store the rkey word after ShiftRows^[-1]
    str.w   r7, [r12, #68]          // store new rkey word in 'rkeys'
    eor     r6, r2, r6, ror #2      // r6 <- r2 ^ (r6 >>> 2)
    bic     r6, r4, r6              // r6 <- ~r6 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r6, r6, r0              // r6 <- r6 | r0
    // applies ShiftRows^[-1]
    and     r5, r2, #0xfc00         // r5 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsr #2      // r5 <- r5 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #6      // r5 <- r5 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r5, r5, r0, lsr #4      // r5 <- r5 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #2      // r5 <- ShiftRows^[-1](r2)
    mvn     r5, r5                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r6, r6, r14             // remask half of register
    ldr.w   r2, [r12, #16]          // load rkey word of rkey from prev round
    ldr     r14, [r12]              // load old mask
    str.w   r5, [r12, #20]          // store the rkey word after ShiftRows^[-1]
    str.w   r6, [r12, #64]          // store new rkey word in 'rkeys'
    eor     r5, r2, r3, ror #2      // r5 <- r2 ^ (r3 >>> 2)
    bic     r5, r4, r5              // r5 <- ~r5 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r5, r5, r0              // r5 <- r5 | r0
    // applies ShiftRows^[-1]
    and     r3, r2, #0xfc00         // r3 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r3, r3, r0, lsl #8      // r3 <- r3 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r3, r3, r0, lsr #2      // r3 <- r3 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r3, r3, r0, lsl #6      // r3 <- r3 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r3, r3, r0, lsr #4      // r3 <- r3 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r3, r3, r0, ror #28     // r3 <- r3 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r3, r0, r3, ror #2      // r3 <- ShiftRows^[-1](r2)
    mvn     r3, r3                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r5, r5, r14             // remask half of register
    ldr.w   r2, [r12, #12]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]          // load old mask
    str.w   r3, [r12, #16]          // store new rkey word in 'rkeys'
    str.w   r5, [r12, #60]
    eor     r3, r2, r1, ror #2      // r3 <- r2 ^ (r1 >>> 2)
    and     r3, r4, r3              // r3 <- r3 & 0xc0c0c0c0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    eor     r1, r4, r4, lsr #4      // r1 <- 0xcccccccc
    and     r14, r14, r1, lsr #2    // r14<- r14 & 0x33333333
    orr     r4, r3, r0              // r4 <- r3 | r0
    eor     r4, r4, r14             // remask half of register
    and     r3, r2, #0xfc00         // r3 <- r2 & 0x0000fc00
    and     r0, r2, #0x0300         // r0 <- r2 & 0x00000300
    orr     r3, r3, r0, lsl #8      // r3 <- r3 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r3, r3, r0, lsr #2      // r3 <- r3 | r0 >> 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r3, r3, r0, lsl #6      // r3 <- r3 | r0 << 6
    and     r0, r2, #0xc0000000     // r0 <- r2 & 0xc0000000
    orr     r3, r3, r0, lsr #4      // r3 <- r3 | r0 >> 4
    and     r0, r2, #0x3f000000     // r0 <- r2 & 0x3f000000
    orr     r3, r3, r0, ror #28     // r3 <- r3 | (r0 >>> 28)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r3, r0, r3, ror #2      // r3 <- ShiftRows^[-1](r2)
    add     r12, #44                // point to the next rkey addr
    ldr.w   r14, [sp, #132]
    str.w   r4, [r12, #12]          // store tmp rkey[0]
    str.w   r3, [r12, #-32]         // store prev rkey after ShiftRows^[-1]
    str.w   r12, [sp, #116]         // store the new rkeys address on the stack
    ldrd    r12, r2, [r12]          // load masks MASK1 and MASK2 in r12, r2 (for sbox routine)
    bx      lr

/******************************************************************************
* Subroutine that XORs the columns after the S-box during the key schedule
* round function, for rounds i such that (i % 4) == 2.
* Note that the code size could be reduced at the cost of some instructions
* since some redundant code is applied on different registers.
******************************************************************************/
.align 2
xor_columns_2:
    str.w   r14, [sp, #112]          // store link register
    movw    r4, #0xc0c0
    movt    r4, #0xc0c0             // r4 <- 0xc0c0c0c0
    eor     r11, r5, r11, ror #2    // r11<- r5 ^ (r11 >>> 2)
    bic     r11, r4, r11            // r11<- ~r11 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r11, r11, r9            // r11<- r11 | r9
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r9, r14, r5, lsr #4     // r9 <- (r5 >> 4) & 0x0f000f00
    and     r10, r14, r5            // r10<- r5 & 0x0f000f00
    orr     r9, r9, r10, lsl #4     // r9 <- r9 | r10 << 4
    eor     r10, r14, r14, lsl #4   // r10<- 0xff00ff00
    ldr     r14, [r12, #4]          // load prev mask
    and     r10, r5, r10, ror #8    // r10<- r5 & 0x00ff00f00
    orr     r9, r9, r10             // r9 <- ShiftRows^[-2](r5)
    mvn     r9, r9                  // NOT that is omitted in sbox
    eor     r5, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r5, lsr #2    // r14<- r14 & 0x33333333
    eor     r11, r11, r14           // remask half of register
    ldr.w   r5, [r12, #36]          // load rkey word of rkey from prev round
    str     r9, [r12, #40]          // store the rkey word after ShiftRows^[-1]
    str     r11, [r12, #84]         // store new rkey word in 'rkeys'
    eor     r10, r5, r2, ror #2     // r10<- r5 ^ (r2 >>> 2)
    bic     r10, r4, r10            // r10<- ~r10 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r10, r10, r9            // r10<- r10 | r9
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r9, r14, r5, lsr #4     // r9 <- (r5 >> 4) & 0x0f000f00
    and     r2, r14, r5             // r2 <- r5 & 0x0f000f00
    orr     r9, r9, r2, lsl #4      // r9 <- r9 | r2 << 4
    eor     r2, r14, r14, lsl #4    // r2 <- 0xff00ff00
    ldr     r14, [r12, #8]          // load old mask
    and     r2, r5, r2, ror #8      // r2 <- r5 & 0x00ff00f00
    orr     r5, r9, r2              // r9 <- ShiftRows^[-2](r5)
    mvn     r5, r5                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r10, r10, r14           // remask half of register
    ldr.w   r2, [r12, #32]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #36]          // store the rkey word after ShiftRows^[-1]
    str     r10, [r12, #80]         // store new rkey word in 'rkeys'
    eor     r9, r2, r0, ror #2      // r9 <- r2 ^ (r9 >>> 2)
    and     r9, r4, r9              // r9 <- r9 & 0xc0c0c0c0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r9, r9, r0              // r9 <- r9 | r0
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r5, r14, r2, lsr #4     // r5 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r5, r5, r0, lsl #4      // r5 <- r5 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    ldr     r14, [r12, #8]          // load old mask
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r5, r5, r0              // r5 <- ShiftRows^[-2](r2)
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r9, r9, r14             // remask half of register
    ldr.w   r2, [r12, #28]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #32]          // store the rkey word after ShiftRows^[-1]
    str.w   r9, [r12, #76]          // store new rkey word in 'rkeys'
    eor     r8, r2, r8, ror #2      // r8 <- r2 ^ (r8 >>> 2)
    and     r8, r4, r8              // r8 <- r8 & 0xc0c0c0c0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r8, r8, r0              // r8 <- r8 | r0
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r5, r14, r2, lsr #4     // r5 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r5, r5, r0, lsl #4      // r5 <- r5 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    ldr     r14, [r12]              // load old mask
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r5, r5, r0              // r5 <- ShiftRows^[-2](r2)
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r8, r8, r14             // remask half of register
    ldr.w   r2, [r12, #24]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #28]          // store the rkey word after ShiftRows^[-1]
    str.w   r8, [r12, #72]          // store new rkey word in 'rkeys'
    eor     r7, r2, r7, ror #2      // r7 <- r2 ^ (r7 >>> 2)
    and     r7, r4, r7              // r7 <- r7 & 0xc0c0c0c0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r7, r7, r0              // r7 <- r7 | r0
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r5, r14, r2, lsr #4     // r5 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r5, r5, r0, lsl #4      // r5 <- r5 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    ldr     r14, [r12]              // load old mask
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r5, r5, r0              // r5 <- ShiftRows^[-2](r2)
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r7, r7, r14             // remask half of register
    ldr.w   r2, [r12, #20]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #24]          // store the rkey word after ShiftRows^[-1]
    str.w   r7, [r12, #68]          // store new rkey word in 'rkeys'
    eor     r6, r2, r6, ror #2      // r6 <- r2 ^ (r6 >>> 2)
    bic     r6, r4, r6              // r6 <- ~r6 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r6, r6, r0              // r6 <- r6 | r0
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r5, r14, r2, lsr #4     // r5 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r5, r5, r0, lsl #4      // r5 <- r5 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    ldr     r14, [r12, #4]          // load old mask
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r5, r5, r0              // r5 <- ShiftRows^[-2](r2)
    mvn     r5, r5                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r6, r6, r14             // remask half of register
    ldr.w   r2, [r12, #16]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #20]          // store the rkey word after ShiftRows^[-1]
    str.w   r6, [r12, #64]          // store new rkey word in 'rkeys'
    eor     r5, r2, r3, ror #2      // r5 <- r2 ^ (r3 >>> 2)
    bic     r5, r4, r5              // r5 <- ~r5 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r5, r5, r0              // r5 <- r5 | r0
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r3, r14, r2, lsr #4     // r3 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r3, r3, r0, lsl #4      // r3 <- r3 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    ldr     r14, [r12]              // load old mask
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r3, r3, r0              // r3 <- ShiftRows^[-2](r2)
    mvn     r3, r3                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r5, r5, r14             // remask half of register
    ldr.w   r2, [r12, #12]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]          // load old mask
    str.w   r3, [r12, #16]          // store new rkey word in 'rkeys'
    str.w   r5, [r12, #60]
    eor     r3, r2, r1, ror #2      // r3 <- r2 ^ (r1 >>> 2)
    and     r3, r4, r3              // r3 <- r3 & 0xc0c0c0c0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    eor     r1, r4, r4, lsr #4      // r1 <- 0xcccccccc
    orr     r4, r3, r0              // r4 <- r3 | r0
    and     r14, r14, r1, lsr #2    // r14<- r14 & 0x33333333
    eor     r4, r4, r14             // remask half of register
    // applies ShiftRows^[-2]
    movw    r14, #0x0f00
    movt    r14, #0x0f00            // r14<- 0x0f000f00 for ShiftRows^[-2]
    and     r3, r14, r2, lsr #4     // r3 <- (r2 >> 4) & 0x0f000f00
    and     r0, r14, r2             // r0 <- r2 & 0x0f000f00
    orr     r3, r3, r0, lsl #4      // r3 <- r3 | r0 << 4
    eor     r0, r14, r14, lsl #4    // r0 <- 0xff00ff00
    and     r0, r2, r0, ror #8      // r0 <- r2 & 0x00ff00f00
    orr     r3, r3, r0              // r3 <- ShiftRows^[-2](r2)
    add     r12, #44
    ldr     r14, [sp, #112]         // restore link register
    str.w   r3, [r12, #-32]
    str.w   r4, [r12, #12]
    str     r12, [sp, #116]         // store the new rkeys address on the stack
    ldrd    r12, r2, [r12]          // load masks MASK1 and MASK2 in r12, r2 (for sbox routine)
    bx      lr

/******************************************************************************
* Subroutine that XORs the columns after the S-box during the key schedule
* round function, for rounds i such that (i % 4) == 3.
* Note that the code size could be reduced at the cost of some instructions
* since some redundant code is applied on different registers.
******************************************************************************/
.align 2
xor_columns_3:
    str     r14, [sp, #112]         // store link register on the stack 
    ldr     r14, [r12, #4]          // load old mask
    movw    r4, #0xc0c0
    movt    r4, #0xc0c0             // r4 <- 0xc0c0c0c0
    eor     r11, r5, r11, ror #2    // r11<- r5 ^ (r11 >>> 2)
    bic     r11, r4, r11            // r11<- ~r11 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r11, r11, r9            // r11<- r11 | r9
    eor     r9, r5, r11, ror #2     // r9 <- r5 ^ (r11 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r11, r11, r9            // r11<- r11 | r9
    // applies ShiftRows^[-3]
    and     r9, r5, #0xc000         // r9 <- r5 & 0x0000c000
    and     r10, r5, #0x3f00        // r10<- r5 & 0x00003f00
    orr     r9, r9, r10, lsl #8     // r9 <- r9 | r10 << 8
    and     r10, r5, #0xf00000      // r10<- r5 & 0x00f00000
    orr     r9, r9, r10, lsl #2     // r9 <- r9 | r10 << 2
    and     r10, r5, #0xf0000       // r10<- r5 & 0x000f0000
    orr     r9, r9, r10, lsl #10    // r9 <- r9 | r10 << 10
    and     r10, r5, #0xfc000000    // r10<- r5 & 0xfc000000
    orr     r9, r9, r10, ror #28     // r9 <- r9 | r10 >>> 8
    and     r10, r5, #0x03000000    // r10<- r5 & 0x03000000
    orr     r9, r9, r10, ror #20    // r9 <- r9 | (r10 >>> 20)
    and     r10, r5, #0xff          // r10<- r5 & 0xff
    orr     r9, r10, r9, ror #6     // r9 <- ShiftRows^[-3](r5)
    mvn     r9, r9                  // NOT that is omitted in sbox
    eor     r5, r4, r4, lsr #4      // r5 <- 0xcccccccc
    and     r14, r14, r5, lsr #2    // r14<- r14 & 0x33333333
    eor     r11, r11, r14           // remask half of register
    ldr.w   r5, [r12, #36]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #8]          // load old mask
    str     r9, [r12, #40]          // store the rkey word after ShiftRows^[-1]
    str     r11, [r12, #84]         // store new rkey word in 'rkeys'
    eor     r10, r5, r2, ror #2     // r10<- r5 ^ (r2 >>> 2)
    bic     r10, r4, r10            // r10<- ~r10 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #2      // r9 <- r9 & 0x30303030
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #4      // r9 <- r9 & 0x0c0c0c0c
    orr     r10, r10, r9            // r10<- r10 | r9
    eor     r9, r5, r10, ror #2     // r9 <- r5 ^ (r10 >>> 2)
    and     r9, r9, r4, ror #6      // r9 <- r9 & 0x03030303
    orr     r10, r10, r9            // r10<- r10 | r9
    // applies ShiftRows^[-3]
    and     r9, r5, #0xc000         // r9 <- r5 & 0x0000c000
    and     r2, r5, #0x3f00         // r2 <- r5 & 0x00003f00
    orr     r9, r9, r2, lsl #8      // r9 <- r9 | r2 << 8
    and     r2, r5, #0xf00000       // r2 <- r5 & 0x00f00000
    orr     r9, r9, r2, lsl #2      // r9 <- r9 | r2 << 2
    and     r2, r5, #0xf0000        // r2 <- r5 & 0x000f0000
    orr     r9, r9, r2, lsl #10     // r9 <- r9 | r2 << 10
    and     r2, r5, #0xfc000000     // r2 <- r5 & 0xfc000000
    orr     r9, r9, r2, ror #28     // r9 <- r9 | r2 >>> 8
    and     r2, r5, #0x03000000     // r2 <- r5 & 0x03000000
    orr     r9, r9, r2, ror #20     // r9 <- r9 | (r2 >>> 20)
    and     r2, r5, #0xff           // r2 <- r5 & 0xff
    orr     r5, r2, r9, ror #6      // r5 <- ShiftRows^[-3](r5)
    mvn     r5, r5                  // NOT that is omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r10, r10, r14           // remask half of register
    ldr.w   r2, [r12, #32]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #36]          // store the rkey word after ShiftRows^[-1]
    str     r10, [r12, #80]         // store new rkey word in 'rkeys'
    eor     r9, r2, r0, ror #2      // r9 <- r2 ^ (r9 >>> 2)
    and     r9, r4, r9              // r9 <- r9 & 0xc0c0c0c0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r9, r9, r0              // r9 <- r9 | r0
    eor     r0, r2, r9, ror #2      // r0 <- r2 ^ (r9 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r9, r9, r0              // r9 <- r9 | r0
    // applies ShiftRows^[-3]
    and     r5, r2, #0xc000         // r5 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsl #2      // r5 <- r5 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #10     // r5 <- r5 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r5, r5, r0, ror #20     // r5 <- r5 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #6      // r5 <- ShiftRows^[-3](r2)
    eor     r9, r9, r14             // remask half of register
    ldr.w   r2, [r12, #28]          // load rkey word of rkey from prev round
    ldr     r14, [r12]
    str.w   r5, [r12, #32]          // store the rkey word after ShiftRows^[-1]
    str.w   r9, [r12, #76]          // store new rkey word in 'rkeys'
    eor     r8, r2, r8, ror #2      // r8 <- r2 ^ (r8 >>> 2)
    and     r8, r4, r8              // r8 <- r8 & 0xc0c0c0c0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r8, r8, r0              // r8 <- r8 | r0
    eor     r0, r2, r8, ror #2      // r0 <- r2 ^ (r8 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r8, r8, r0              // r8 <- r8 | r0
    // applies ShiftRows^[-3]
    and     r5, r2, #0xc000         // r5 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsl #2      // r5 <- r5 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #10     // r5 <- r5 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r5, r5, r0, ror #20     // r5 <- r5 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #6      // r5 <- ShiftRows^[-3](r2)
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r8, r8, r14             // remask half register
    ldr.w   r2, [r12, #24]          // load rkey word of rkey from prev round
    str.w   r5, [r12, #28]          // store the rkey word after ShiftRows^[-1]
    str.w   r8, [r12, #72]          // store new rkey word in 'rkeys'
    eor     r7, r2, r7, ror #2      // r7 <- r2 ^ (r7 >>> 2)
    and     r7, r4, r7              // r7 <- r7 & 0xc0c0c0c0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r7, r7, r0              // r7 <- r7 | r0
    eor     r0, r2, r7, ror #2      // r0 <- r2 ^ (r7 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r7, r7, r0              // r7 <- r7 | r0
    // applies ShiftRows^[-3]
    and     r5, r2, #0xc000         // r5 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsl #2      // r5 <- r5 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #10     // r5 <- r5 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r5, r5, r0, ror #20     // r5 <- r5 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #6      // r5 <- ShiftRows^[-3](r2)
    eor     r7, r7, r14             // remask half register
    ldr.w   r2, [r12, #20]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]
    str.w   r5, [r12, #24]          // store the rkey word after ShiftRows^[-1]
    str.w   r7, [r12, #68]          // store new rkey word in 'rkeys'
    eor     r6, r2, r6, ror #2      // r6 <- r2 ^ (r6 >>> 2)
    bic     r6, r4, r6              // r6 <- ~r6 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r6, r6, r0              // r6 <- r6 | r0
    eor     r0, r2, r6, ror #2      // r0 <- r2 ^ (r6 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r6, r6, r0              // r6 <- r6 | r0
    // applies ShiftRows^[-3]
    and     r5, r2, #0xc000         // r5 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r5, r5, r0, lsl #8      // r5 <- r5 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r5, r5, r0, lsl #2      // r5 <- r5 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r5, r5, r0, lsl #10     // r5 <- r5 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r5, r5, r0, ror #28     // r5 <- r5 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r5, r5, r0, ror #20     // r5 <- r5 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r5, r0, r5, ror #6      // r5 <- ShiftRows^[-3](r2)
    mvn     r5, r5                  // NOT omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r6, r6, r14             // remask half register
    ldr.w   r2, [r12, #16]          // load rkey word of rkey from prev round
    ldr     r14, [r12]              // load prev mask
    str.w   r5, [r12, #20]          // store the rkey word after ShiftRows^[-1]
    str.w   r6, [r12, #64]          // store new rkey word in 'rkeys'
    eor     r5, r2, r3, ror #2      // r5 <- r2 ^ (r3 >>> 2)
    bic     r5, r4, r5              // r5 <- ~r5 & 0xc0c0c0c0 (NOT omitted in sbox)
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r5, r5, r0              // r5 <- r5 | r0
    eor     r0, r2, r5, ror #2      // r0 <- r2 ^ (r5 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    orr     r5, r5, r0              // r5 <- r5 | r0
    // applies ShiftRows^[-3]
    and     r3, r2, #0xc000         // r3 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r3, r3, r0, lsl #8      // r3 <- r3 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r3, r3, r0, lsl #2      // r3 <- r3 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r3, r3, r0, lsl #10     // r3 <- r3 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r3, r3, r0, ror #28     // r3 <- r3 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r3, r3, r0, ror #20     // r3 <- r3 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r3, r0, r3, ror #6      // r3 <- ShiftRows^[-3](r2)
    mvn     r3, r3                  // NOT omitted in sbox
    eor     r2, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r2, lsr #2    // r14<- r14 & 0x33333333
    eor     r5, r5, r14             // remask half register
    ldr.w   r2, [r12, #12]          // load rkey word of rkey from prev round
    ldr     r14, [r12, #4]
    str.w   r3, [r12, #16]          // store new rkey word in 'rkeys'
    str.w   r5, [r12, #60]
    eor     r3, r2, r1, ror #2      // r3 <- r2 ^ (r1 >>> 2)
    and     r3, r4, r3              // r3 <- r3 & 0xc0c0c0c0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #2      // r0 <- r0 & 0x30303030
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #4      // r0 <- r0 & 0x0c0c0c0c
    orr     r3, r3, r0              // r3 <- r3 | r0
    eor     r0, r2, r3, ror #2      // r0 <- r2 ^ (r3 >>> 2)
    and     r0, r0, r4, ror #6      // r0 <- r0 & 0x03030303
    eor     r1, r4, r4, lsr #4      // r2 <- 0xcccccccc
    and     r14, r14, r1, lsr #2    // r14<- r14 & 0x33333333
    orr     r4, r3, r0              // r4 <- r3 | r0
    eor     r4, r4, r14             // remask half register
    // applies ShiftRows^[-3]
    and     r3, r2, #0xc000         // r3 <- r2 & 0x0000c000
    and     r0, r2, #0x3f00         // r0 <- r2 & 0x00003f00
    orr     r3, r3, r0, lsl #8      // r3 <- r3 | r0 << 8
    and     r0, r2, #0xf00000       // r0 <- r2 & 0x00f00000
    orr     r3, r3, r0, lsl #2      // r3 <- r3 | r0 << 2
    and     r0, r2, #0xf0000        // r0 <- r2 & 0x000f0000
    orr     r3, r3, r0, lsl #10     // r3 <- r3 | r0 << 10
    and     r0, r2, #0xfc000000     // r0 <- r2 & 0xfc000000
    orr     r3, r3, r0, ror #28     // r3 <- r3 | r0 >>> 8
    and     r0, r2, #0x03000000     // r0 <- r2 & 0x03000000
    orr     r3, r3, r0, ror #20     // r3 <- r3 | (r0 >>> 20)
    and     r0, r2, #0xff           // r0 <- r2 & 0xff
    orr     r3, r0, r3, ror #6      // r3 <- ShiftRows^[-3](r2)
    add     r12, #44
    ldr     r14, [sp, #112]
    str.w   r4, [r12, #12]
    str.w   r3, [r12, #-32]
    str.w   r12, [sp, #116]         // store the new rkeys address on the stack
    ldrd    r12, r2, [r12]          // load masks MASK1 and MASK2 in r12, r2 (for sbox routine)
    bx      lr

/******************************************************************************
* First-order masked AES-128 key schedule to match the fully-fixsliced (ffs)
* representation.
******************************************************************************/
@ void aes128_keyschedule_ffs(u32* rkeys, const u8* key);
.global aes128_keyschedule_ffs
.type   aes128_keyschedule_ffs,%function
.align 2
aes128_keyschedule_ffs:
    push    {r0-r12,r14}
    ldr.w   r4, [r1]                // load the 1st 128-bit key in r4-r7
    ldr     r5, [r1, #4]
    ldr     r6, [r1, #8]
    ldr     r7, [r1, #12]
    ldr.w   r8, [r2]                // load the 2nd 128-bit key in r8-r11
    ldr     r9, [r2, #4]
    ldr     r10,[r2, #8]
    ldr     r11,[r2, #12]
    bl      packing                 // pack the master key
    // ------------------ MASKING ------------------
    // generation of 2 random words
    movw    r0, 0x0804
    movt    r0, 0x5006              // r0 <- RNG_SR = 0x50060804
    add     r12, r0, #4             // r1 <- RNG_DR = 0x50060808
    mov     r14, #2                 // 2 random words to be generated
ffs_get_random_mask:
    ldr.w   r2, [r0]
    cmp     r2, #1                  // check if RNG_SR == RNG_SR_DRDY
    bne     ffs_get_random_mask     // loop while RNG status is not ready
    ldr.w   r1, [r12]               // load the random number in r1
    push    {r1}                    // push the random word on the stack
    subs    r14, #1                 // r14<- r14 -1
    bne     ffs_get_random_mask     // loop till r14 > 0
    ldr.w   r1, [sp]                // load back the last rnd generated
    ubfx    r2, r1, #0, #2          // r2 <- ab 
    orr     r2, r2, r2, lsl #2      // r2 <- abab
    orr     r2, r2, r2, lsl #4      // r2 <- abababab
    orr     r2, r2, r2, lsl #8      // r2 <- abababababababab
    orr     r2, r2, r2, lsl #16     // r2 <- abababababababababababababababab
    ubfx.w  r1, r1, #2, #2          // r1 <- cd 
    orr     r1, r1, r1, lsl #2      // r1 <- cdcd
    orr     r1, r1, r1, lsl #4      // r1 <- cdcdcdcd
    orr     r1, r1, r1, lsl #8      // r1 <- cdcdcdcdcdcdcdcd
    orr     r1, r1, r1, lsl #16     // r1 <- cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
    eor     r0, r1, r2              // r0 <- m0 ^ m1
    eor     r4, r4, r1              // r4 <- key[0] ^ m1
    eor     r5, r5, r2              // r5 <- key[1] ^ m0
    eor     r6, r6, r1              // r6 <- key[2] ^ m1
    eor     r7, r7, r2              // r7 <- key[3] ^ m0
    eor     r8, r8, r2              // r8 <- key[4] ^ m0
    eor     r9, r9, r0              // r9 <- key[5] ^ m2
    eor     r10, r10, r0            // r10<- key[6] ^ m2
    eor     r11, r11, r1            // r11<- key[7] ^ m1
    // ------------------ MASKING ------------------
    sub.w   sp, #136                // allow space on the stack for tmp var
    ldr     r14, [sp, #144]         // restore 'rkeys' address
    add     r14, #12
    stm     r14, {r4-r11}           // store masked master key
    strd    r2, r1, [r14, #-12]!    // store the corresponding masks
    str.w   r0, [r14, #8]           // store the corresponding masks
    str     r14, [sp ,#116]         // store the rkey address on the stack
    str     r0, [sp, #120]          // store the current masks on the stack for sbox computations
    strd    r1, r2, [sp, #124]      // store the current masks on the stack for sbox computations
    mov     r12, r2                 // for compliance to sbox routine
    mov     r2, r1                  // for compliance to sbox routine
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r11, r11, #0x00000300   // add the 1st rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r2, r2, #0x00000300     // add the 2nd rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r0, r0, #0x00000300     // add the 3rd rconst
    bl      xor_columns_2
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r8, r8, #0x00000300     // add the 4th rconst
    bl      xor_columns_3
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r7, r7, #0x00000300     // add the 5th rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r6, r6, #0x00000300     // add the 6th rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r3, r3, #0x00000300     // add the 7th rconst
    bl      xor_columns_2
    bl      sbox                    // apply the sbox to the master key
    ldr.w   r2, [sp, #140]          // all bits within previous 32-bit random have been used
    str.w   r2, [sp, #136]          // put the other random word at the right place for 'remask_rkey'
    bl      remask_rkey
    eor     r1, r1, #0x00000300     // add the 8th rconst
    bl      xor_columns_3
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r11, r11, #0x00000300   // add the 9th rconst
    eor     r2, r2, #0x00000300     // add the 9th rconst
    eor     r8, r8, #0x00000300     // add the 9th rconst
    eor     r7, r7, #0x00000300     // add the 9th rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r2, r2, #0x00000300     // add the 10th rconst
    eor     r0, r0, #0x00000300     // add the 10th rconst
    eor     r7, r7, #0x00000300     // add the 10th rconst
    eor     r6, r6, #0x00000300     // add the 10th rconst
    bl      xor_columns_1
    mvn     r5, r5                  // add the NOT omitted on sbox for the last rkey
    mvn     r6, r6                  // add the NOT omitted on sbox for the last rkey
    mvn     r10, r10                // add the NOT omitted on sbox for the last rkey
    mvn     r11, r11                // add the NOT omitted on sbox for the last rkey
    ldr.w   r12, [sp, #116]         // restore rkeys addr
    strd    r5, r6, [r12, #16]      // store the last rkeys after adding the NOT
    strd    r10, r11, [r12, #36]    // store the last rkeys after adding the NOT
    ldrd    r0, r1, [r12, #-424]
    ldrd    r2, r3, [r12, #-404]
    mvn     r0, r0                  // remove the NOT omitted on sbox for the master rkey
    mvn     r1, r1                  // remove the NOT omitted on sbox for the master rkey
    mvn     r2, r2                  // remove the NOT omitted on sbox for the master rkey
    mvn     r3, r3                  // remove the NOT omitted on sbox for the master rkey
    strd    r0, r1, [r12, #-424]
    strd    r2, r3, [r12, #-404]
    add.w   sp, #144                // restore stack
    pop     {r0-r12, r14}           // restore context
    bx      lr

/******************************************************************************
* First-order masked AES-128 key schedule to match the semi-fixsliced (sfs)
* representation.
******************************************************************************/
@ void aes128_keyschedule_sfs(u32* rkeys, const u8* key);
.global aes128_keyschedule_sfs
.type   aes128_keyschedule_sfs,%function
.align 2
aes128_keyschedule_sfs:
    push    {r0-r12,r14}
    ldr.w   r4, [r1]                // load the 1st 128-bit key in r4-r7
    ldr     r5, [r1, #4]
    ldr     r6, [r1, #8]
    ldr     r7, [r1, #12]
    ldr.w   r8, [r2]                // load the 2nd 128-bit key in r8-r11
    ldr     r9, [r2, #4]
    ldr     r10,[r2, #8]
    ldr     r11,[r2, #12]
    bl      packing                 // pack the master key

    // ------------------ MASKING ------------------
    // generation of 2 random words
    movw    r0, 0x0804
    movt    r0, 0x5006              // r0 <- RNG_SR = 0x50060804
    add     r12, r0, #4             // r1 <- RNG_DR = 0x50060808
    mov     r14, #2                 // 2 random words to be generated
sfs_get_random_mask:
    ldr.w   r2, [r0]
    cmp     r2, #1                  // check if RNG_SR == RNG_SR_DRDY
    bne     sfs_get_random_mask     // loop while RNG status is not ready
    ldr.w   r1, [r12]               // load the random number in r1
    push    {r1}                    // push the random word on the stack
    subs    r14, #1                 // r14<- r14 - 1
    bne     sfs_get_random_mask     // loop till r14 > 0
    ldr.w   r1, [sp]                // load back the last rnd generated
    ubfx    r2, r1, #0, #2          // r2 <- ab 
    orr     r2, r2, r2, lsl #2      // r2 <- abab
    orr     r2, r2, r2, lsl #4      // r2 <- abababab
    orr     r2, r2, r2, lsl #8      // r2 <- abababababababab
    orr     r2, r2, r2, lsl #16     // r2 <- abababababababababababababababab
    ubfx.w  r1, r1, #2, #2          // r1 <- cd 
    orr     r1, r1, r1, lsl #2      // r1 <- cdcd
    orr     r1, r1, r1, lsl #4      // r1 <- cdcdcdcd
    orr     r1, r1, r1, lsl #8      // r1 <- cdcdcdcdcdcdcdcd
    orr     r1, r1, r1, lsl #16     // r1 <- cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
    eor     r0, r1, r2              // r0 <- m0 ^ m1
    eor     r4, r4, r1              // r4 <- key[0] ^ m1
    eor     r5, r5, r2              // r5 <- key[1] ^ m0
    eor     r6, r6, r1              // r6 <- key[2] ^ m1
    eor     r7, r7, r2              // r7 <- key[3] ^ m0
    eor     r8, r8, r2              // r8 <- key[4] ^ m0
    eor     r9, r9, r0              // r9 <- key[5] ^ m2
    eor     r10, r10, r0            // r10<- key[6] ^ m2
    eor     r11, r11, r1            // r11<- key[7] ^ m1
    // ------------------ MASKING ------------------

    sub.w   sp, #136                // allow space on the stack for tmp var
    ldr     r14, [sp, #144]         // restore 'rkeys' address
    add     r14, #12
    stm     r14, {r4-r11}           // store masked master key
    strd    r2, r1, [r14, #-12]!    // store the corresponding masks
    str.w   r0, [r14, #8]           // store the corresponding masks
    str     r14, [sp ,#116]         // store the rkey address on the stack
    str     r0, [sp, #120]          // store the current masks on the stack for sbox computations
    strd    r1, r2, [sp, #124]      // store the current masks on the stack for sbox computations
    mov     r12, r2                 // for compliance to sbox routine
    mov     r2, r1                  // for compliance to sbox routine
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r11, r11, #0x00000300   // add the 1st rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r2, r2, #0x00000300     // add the 2nd rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r0, r0, #0x00000300     // add the 3rd rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r8, r8, #0x00000300     // add the 4th rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r7, r7, #0x00000300     // add the 5th rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r6, r6, #0x00000300     // add the 6th rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r3, r3, #0x00000300     // add the 7th rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    ldr.w   r2, [sp, #140]          // all bits within previous 32-bit random have been used
    str.w   r2, [sp, #136]          // put the other random word at the right place for 'remask_rkey'
    bl      remask_rkey
    eor     r1, r1, #0x00000300     // add the 8th rconst
    bl      xor_columns_1
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r11, r11, #0x00000300   // add the 9th rconst
    eor     r2, r2, #0x00000300     // add the 9th rconst
    eor     r8, r8, #0x00000300     // add the 9th rconst
    eor     r7, r7, #0x00000300     // add the 9th rconst
    bl      xor_columns_0
    bl      sbox                    // apply the sbox to the master key
    bl      remask_rkey
    eor     r2, r2, #0x00000300     // add the 10th rconst
    eor     r0, r0, #0x00000300     // add the 10th rconst
    eor     r7, r7, #0x00000300     // add the 10th rconst
    eor     r6, r6, #0x00000300     // add the 10th rconst
    bl      xor_columns_1
    mvn     r5, r5                  // add the NOT omitted on sbox for the last rkey
    mvn     r6, r6                  // add the NOT omitted on sbox for the last rkey
    mvn     r10, r10                // add the NOT omitted on sbox for the last rkey
    mvn     r11, r11                // add the NOT omitted on sbox for the last rkey
    ldr.w   r12, [sp, #116]         // restore rkeys addr
    strd    r5, r6, [r12, #16]      // store the last rkeys after adding the NOT
    strd    r10, r11, [r12, #36]    // store the last rkeys after adding the NOT
    ldrd    r0, r1, [r12, #-424]
    ldrd    r2, r3, [r12, #-404]
    mvn     r0, r0                  // remove the NOT omitted on sbox for the master rkey
    mvn     r1, r1                  // remove the NOT omitted on sbox for the master rkey
    mvn     r2, r2                  // remove the NOT omitted on sbox for the master rkey
    mvn     r3, r3                  // remove the NOT omitted on sbox for the master rkey
    strd    r0, r1, [r12, #-424]
    strd    r2, r3, [r12, #-404]
    add.w   sp, #144                // restore stack
    pop     {r0-r12, r14}           // restore context
    bx      lr
