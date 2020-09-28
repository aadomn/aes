/******************************************************************************
* Assembly fixsliced implementation of AES-128 and AES-256 (encryption only).
*
* Fully-fixsliced implementation runs faster than the semi-fixsliced variant
* at the cost of a larger code size.
*
* See the paper at https://eprint.iacr.org/2020/1123.pdf for more details.
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     August 2020
******************************************************************************/

.syntax unified
.thumb

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
    eor     r12, r4, r8, lsr #1     // SWAPMOVE(r8, r4, 0x55555555, 1) ....
    and     r12, r1
    eor     r4, r12
    eor     r8, r8, r12, lsl #1     // .... SWAPMOVE(r8, r4, 0x55555555, 1)
    eor     r12, r5, r9, lsr #1     // SWAPMOVE(r9, r5, 0x55555555, 1) ....
    and     r12, r1
    eor     r5, r12
    eor     r9, r9, r12, lsl #1     // .... SWAPMOVE(r9, r5, 0x55555555, 1)
    eor     r12, r6, r10, lsr #1    // SWAPMOVE(r10, r6, 0x55555555, 1) ....
    and     r12, r1
    eor     r6, r12
    eor     r10, r10, r12, lsl #1   // .... SWAPMOVE(r10, r6, 0x55555555, 1)
    eor     r12, r7, r11, lsr #1    // SWAPMOVE(r11, r7, 0x55555555, 1) ....
    and     r12, r1
    eor     r7, r12
    eor     r11, r11, r12, lsl #1   // .... SWAPMOVE(r11, r7, 0x55555555, 1)
    eor     r12, r4, r5, lsr #2     // SWAPMOVE(r5, r4, 0x33333333, 2) ....
    and     r12, r2
    eor     r4, r12
    eor     r0, r5, r12, lsl #2     // .... SWAPMOVE(r5, r4, 0x33333333, 2)
    eor     r12, r8, r9, lsr #2     // SWAPMOVE(r9, r8, 0x33333333, 2) ....
    and     r12, r2
    eor     r5, r8, r12
    eor     r9, r9, r12, lsl #2     // .... SWAPMOVE(r9, r8, 0x33333333, 2)
    eor     r12, r6, r7, lsr #2     // SWAPMOVE(r7, r6, 0x33333333, 2) ....
    and     r12, r2
    eor     r8, r6, r12
    eor     r7, r7, r12, lsl #2     // .... SWAPMOVE(r7, r6, 0x33333333, 2)
    eor     r12, r10, r11, lsr #2   // SWAPMOVE(r11, r10, 0x33333333, 2) ....
    and     r12, r2
    eor     r2, r10, r12
    eor     r11, r11, r12, lsl #2   // .... SWAPMOVE(r11, r10, 0x33333333, 2)
    eor     r12, r4, r8, lsr #4     // SWAPMOVE(r8, r4, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r4, r12
    eor     r8, r8, r12, lsl #4     // .... SWAPMOVE(r8, r4, 0x0f0f0f0f,4)
    eor     r12, r0, r7, lsr #4     // SWAPMOVE(r7, r1, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r6, r0, r12
    eor     r10, r7, r12, lsl #4    // .... SWAPMOVE(r7, r1, 0x0f0f0f0f, 4)
    eor     r12, r9, r11, lsr #4    // SWAPMOVE(r11, r9, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r7, r9, r12
    eor     r11, r11, r12, lsl #4   // .... SWAPMOVE(r11,r9, 0x0f0f0f0f, 4)
    eor     r12, r5, r2, lsr #4     // SWAPMOVE(r2, r5, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r5, r12
    eor     r9, r2, r12, lsl #4     // .... SWAPMOVE(r2, r5, 0x0f0f0f0f, 4)
    bx      lr

/******************************************************************************
* Unpacks the 256-bit internal state in two 128-bit blocs.
******************************************************************************/
.align 2
unpacking:
    movw    r3, #0x0f0f
    movt    r3, #0x0f0f             // r3 <- 0x0f0f0f0f (mask for SWAPMOVE)
    eor     r12, r5, r9, lsr #4     // SWAPMOVE(r9, r5, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r5, r12
    eor     r2, r9, r12, lsl #4     // .... SWAPMOVE(r9, r5, 0x0f0f0f0f, 4)
    eor     r12, r7, r11, lsr #4    // SWAPMOVE(r11, r7, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r9, r7, r12
    eor     r11, r11, r12, lsl #4     // .... SWAPMOVE(r11, r7, 0x0f0f0f0f, 4)
    eor     r12, r6, r10, lsr #4     // SWAPMOVE(r10, r6, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r1, r6, r12
    eor     r7, r10, r12, lsl #4     // .... SWAPMOVE(r10, r6, 0x0f0f0f0f, 4)
    eor     r12, r4, r8, lsr #4     // SWAPMOVE(r8, r4, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r4, r12
    eor     r8, r8, r12, lsl #4     // .... SWAPMOVE(r8, r4, 0x0f0f0f0f,4)
    eor     r3, r3, r3, lsl #2      // r3 <- 0x33333333 (mask for SWAPMOVE)
    eor     r12, r2, r11, lsr #2     // SWAPMOVE(r11, r2, 0x33333333, 2) ....
    and     r12, r3
    eor     r10, r2, r12
    eor     r11, r11, r12, lsl #2     // .... SWAPMOVE(r11, r2, 0x33333333, 2)
    eor     r12, r8, r7, lsr #2     // SWAPMOVE(r7, r8, 0x33333333, 2) ....
    and     r12, r3
    eor     r6, r8, r12
    eor     r7, r7, r12, lsl #2     // .... SWAPMOVE(r7, r8, 0x33333333, 2)
    eor     r12, r5, r9, lsr #2     // SWAPMOVE(r9, r5, 0x33333333, 2) ....
    and     r12, r3
    eor     r8, r5, r12
    eor     r9, r9, r12, lsl #2     // .... SWAPMOVE(r9, r5, 0x33333333, 2)
    eor     r12, r4, r1, lsr #2     // SWAPMOVE(r1, r4, 0x33333333, 2) ....
    and     r12, r3
    eor     r4, r12
    eor     r5, r1, r12, lsl #2     // .... SWAPMOVE(r1, r4, 0x33333333, 2)
    eor     r1, r3, r3, lsl #1      // r1 <- 0x33333333 (mask for SWAPMOVE)
    eor     r12, r4, r8, lsr #1     // SWAPMOVE(r8, r4, 0x55555555, 1) ....
    and     r12, r1
    eor     r4, r12
    eor     r8, r8, r12, lsl #1     // .... SWAPMOVE(r8, r4, 0x55555555, 1)
    eor     r12, r5, r9, lsr #1     // SWAPMOVE(r9, r5, 0x55555555, 1) ....
    and     r12, r1
    eor     r5, r12
    eor     r9, r9, r12, lsl #1     // .... SWAPMOVE(r9, r5, 0x55555555, 1)
    eor     r12, r6, r10, lsr #1     // SWAPMOVE(r10, r6, 0x55555555, 1) ....
    and     r12, r1
    eor     r6, r12
    eor     r10, r10, r12, lsl #1     // .... SWAPMOVE(r10, r6, 0x55555555, 1)
    eor     r12, r7, r11, lsr #1     // SWAPMOVE(r11, r7, 0x55555555, 1) ....
    and     r12, r1
    eor     r7, r12
    eor     r11, r11, r12, lsl #1     // .... SWAPMOVE(r11, r7, 0x55555555, 1)
    bx      lr

/******************************************************************************
* Subroutine that computes the AddRoundKey and the S-box.
* Credits to https://github.com/Ko-/aes-armcortexm for the S-box implementation
******************************************************************************/
.align 2
ark_sbox:
    // add round key
    ldr.w   r1, [sp, #48]
    ldmia   r1!, {r0,r2,r3,r12}
    eor     r4, r0
    eor     r5, r2
    eor     r6, r3
    eor     r7, r12
    ldmia   r1!, {r0,r2,r3,r12}
    eor     r8, r0
    eor     r9, r2
    eor     r10, r3
    eor     r11, r12
    str.w   r1, [sp, #48]
    str     r14, [sp, #52]
    // sbox: credits to https://github.com/Ko-/aes-armcortexm
    eor     r1, r7, r9              //Exec y14 = U3 ^ U5; into r1
    eor     r3, r4, r10             //Exec y13 = U0 ^ U6; into r3
    eor     r2, r3, r1              //Exec y12 = y13 ^ y14; into r2
    eor     r0, r8, r2              //Exec t1 = U4 ^ y12; into r0
    eor     r14, r0, r9             //Exec y15 = t1 ^ U5; into r14
    and     r12, r2, r14            //Exec t2 = y12 & y15; into r12
    eor     r8, r14, r11            //Exec y6 = y15 ^ U7; into r8
    eor     r0, r0, r5              //Exec y20 = t1 ^ U1; into r0
    str.w   r2, [sp, #44]           //Store r2/y12 on stack
    eor     r2, r4, r7              //Exec y9 = U0 ^ U3; into r2
    str     r0, [sp, #40]           //Store r0/y20 on stack
    eor     r0, r0, r2              //Exec y11 = y20 ^ y9; into r0
    str     r2, [sp, #36]           //Store r2/y9 on stack
    and     r2, r2, r0              //Exec t12 = y9 & y11; into r2
    str     r8, [sp, #32]           //Store r8/y6 on stack
    eor     r8, r11, r0             //Exec y7 = U7 ^ y11; into r8
    eor     r9, r4, r9              //Exec y8 = U0 ^ U5; into r9
    eor     r6, r5, r6              //Exec t0 = U1 ^ U2; into r6
    eor     r5, r14, r6             //Exec y10 = y15 ^ t0; into r5
    str     r14, [sp, #28]          //Store r14/y15 on stack
    eor     r14, r5, r0             //Exec y17 = y10 ^ y11; into r14
    str.w   r1, [sp, #24]           //Store r1/y14 on stack
    and     r1, r1, r14             //Exec t13 = y14 & y17; into r1
    eor     r1, r1, r2              //Exec t14 = t13 ^ t12; into r1
    str     r14, [sp, #20]          //Store r14/y17 on stack
    eor     r14, r5, r9             //Exec y19 = y10 ^ y8; into r14
    str.w   r5, [sp, #16]           //Store r5/y10 on stack
    and     r5, r9, r5              //Exec t15 = y8 & y10; into r5
    eor     r2, r5, r2              //Exec t16 = t15 ^ t12; into r2
    eor     r5, r6, r0              //Exec y16 = t0 ^ y11; into r5
    str.w   r0, [sp, #12]           //Store r0/y11 on stack
    eor     r0, r3, r5              //Exec y21 = y13 ^ y16; into r0
    str     r3, [sp, #8]            //Store r3/y13 on stack
    and     r3, r3, r5              //Exec t7 = y13 & y16; into r3
    str     r5, [sp, #4]            //Store r5/y16 on stack
    str     r11, [sp, #0]           //Store r11/U7 on stack
    eor     r5, r4, r5              //Exec y18 = U0 ^ y16; into r5
    eor     r6, r6, r11             //Exec y1 = t0 ^ U7; into r6
    eor     r7, r6, r7              //Exec y4 = y1 ^ U3; into r7
    and     r11, r7, r11            //Exec t5 = y4 & U7; into r11
    eor     r11, r11, r12           //Exec t6 = t5 ^ t2; into r11
    eor     r11, r11, r2            //Exec t18 = t6 ^ t16; into r11
    eor     r14, r11, r14           //Exec t22 = t18 ^ y19; into r14
    eor     r4, r6, r4              //Exec y2 = y1 ^ U0; into r4
    and     r11, r4, r8             //Exec t10 = y2 & y7; into r11
    eor     r11, r11, r3            //Exec t11 = t10 ^ t7; into r11
    eor     r2, r11, r2             //Exec t20 = t11 ^ t16; into r2
    eor     r2, r2, r5              //Exec t24 = t20 ^ y18; into r2
    eor     r10, r6, r10            //Exec y5 = y1 ^ U6; into r10
    and     r11, r10, r6            //Exec t8 = y5 & y1; into r11
    eor     r3, r11, r3             //Exec t9 = t8 ^ t7; into r3
    eor     r3, r3, r1              //Exec t19 = t9 ^ t14; into r3
    eor     r3, r3, r0              //Exec t23 = t19 ^ y21; into r3
    eor     r0, r10, r9             //Exec y3 = y5 ^ y8; into r0
    ldr     r11, [sp, #32]          //Load y6 into r11
    and     r5, r0, r11             //Exec t3 = y3 & y6; into r5
    eor     r12, r5, r12            //Exec t4 = t3 ^ t2; into r12
    ldr     r5, [sp, #40]           //Load y20 into r5
    str     r7, [sp, #32]           //Store r7/y4 on stack
    eor     r12, r12, r5            //Exec t17 = t4 ^ y20; into r12
    eor     r1, r12, r1             //Exec t21 = t17 ^ t14; into r1
    and     r12, r1, r3             //Exec t26 = t21 & t23; into r12
    eor     r5, r2, r12             //Exec t27 = t24 ^ t26; into r5
    eor     r12, r14, r12           //Exec t31 = t22 ^ t26; into r12
    eor     r1, r1, r14             //Exec t25 = t21 ^ t22; into r1
    and     r7, r1, r5              //Exec t28 = t25 & t27; into r7
    eor     r14, r7, r14            //Exec t29 = t28 ^ t22; into r14
    and     r4, r14, r4             //Exec z14 = t29 & y2; into r4
    and     r8, r14, r8             //Exec z5 = t29 & y7; into r8
    eor     r7, r3, r2              //Exec t30 = t23 ^ t24; into r7
    and     r12, r12, r7            //Exec t32 = t31 & t30; into r12
    eor     r12, r12, r2            //Exec t33 = t32 ^ t24; into r12
    eor     r7, r5, r12             //Exec t35 = t27 ^ t33; into r7
    and     r2, r2, r7              //Exec t36 = t24 & t35; into r2
    eor     r5, r5, r2              //Exec t38 = t27 ^ t36; into r5
    and     r5, r14, r5             //Exec t39 = t29 & t38; into r5
    eor     r1, r1, r5              //Exec t40 = t25 ^ t39; into r1
    eor     r5, r14, r1             //Exec t43 = t29 ^ t40; into r5
    ldr.w   r7, [sp, #4]            //Load y16 into r7
    and     r7, r5, r7              //Exec z3 = t43 & y16; into r7
    eor     r8, r7, r8              //Exec tc12 = z3 ^ z5; into r8
    str     r8, [sp, #40]           //Store r8/tc12 on stack
    ldr     r8, [sp, #8]            //Load y13 into r8
    and     r8, r5, r8              //Exec z12 = t43 & y13; into r8
    and     r10, r1, r10            //Exec z13 = t40 & y5; into r10
    and     r6, r1, r6              //Exec z4 = t40 & y1; into r6
    eor     r6, r7, r6              //Exec tc6 = z3 ^ z4; into r6
    eor     r3, r3, r12             //Exec t34 = t23 ^ t33; into r3
    eor     r3, r2, r3              //Exec t37 = t36 ^ t34; into r3
    eor     r1, r1, r3              //Exec t41 = t40 ^ t37; into r1
    ldr.w   r5, [sp, #16]           //Load y10 into r5
    and     r2, r1, r5              //Exec z8 = t41 & y10; into r2
    and     r9, r1, r9              //Exec z17 = t41 & y8; into r9
    str     r9, [sp, #16]           //Store r9/z17 on stack
    eor     r5, r12, r3             //Exec t44 = t33 ^ t37; into r5
    ldr     r9, [sp, #28]           //Load y15 into r9
    ldr.w   r7, [sp, #44]           //Load y12 into r7
    and     r9, r5, r9              //Exec z0 = t44 & y15; into r9
    and     r7, r5, r7              //Exec z9 = t44 & y12; into r7
    and     r0, r3, r0              //Exec z10 = t37 & y3; into r0
    and     r3, r3, r11             //Exec z1 = t37 & y6; into r3
    eor     r3, r3, r9              //Exec tc5 = z1 ^ z0; into r3
    eor     r3, r6, r3              //Exec tc11 = tc6 ^ tc5; into r3
    ldr     r11, [sp, #32]          //Load y4 into r11
    ldr.w   r5, [sp, #20]           //Load y17 into r5
    and     r11, r12, r11           //Exec z11 = t33 & y4; into r11
    eor     r14, r14, r12           //Exec t42 = t29 ^ t33; into r14
    eor     r1, r14, r1             //Exec t45 = t42 ^ t41; into r1
    and     r5, r1, r5              //Exec z7 = t45 & y17; into r5
    eor     r6, r5, r6              //Exec tc8 = z7 ^ tc6; into r6
    ldr     r5, [sp, #24]           //Load y14 into r5
    str     r4, [sp, #32]           //Store r4/z14 on stack
    and     r1, r1, r5              //Exec z16 = t45 & y14; into r1
    ldr     r5, [sp, #12]           //Load y11 into r5
    ldr     r4, [sp, #36]           //Load y9 into r4
    and     r5, r14, r5             //Exec z6 = t42 & y11; into r5
    eor     r5, r5, r6              //Exec tc16 = z6 ^ tc8; into r5
    and     r4, r14, r4             //Exec z15 = t42 & y9; into r4
    eor     r14, r4, r5             //Exec tc20 = z15 ^ tc16; into r14
    eor     r4, r4, r1              //Exec tc1 = z15 ^ z16; into r4
    eor     r1, r0, r4              //Exec tc2 = z10 ^ tc1; into r1
    eor     r0, r1, r11             //Exec tc21 = tc2 ^ z11; into r0
    eor     r7, r7, r1              //Exec tc3 = z9 ^ tc2; into r7
    eor     r1, r7, r5              //Exec S0 = tc3 ^ tc16; into r1
    eor     r7, r7, r3              //Exec S3 = tc3 ^ tc11; into r7
    eor     r3, r7, r5              //Exec S1 = S3 ^ tc16 ^ 1; into r3
    eor     r11, r10, r4            //Exec tc13 = z13 ^ tc1; into r11
    ldr.w   r4, [sp, #0]            //Load U7 into r4
    and     r12, r12, r4            //Exec z2 = t33 & U7; into r12
    eor     r9, r9, r12             //Exec tc4 = z0 ^ z2; into r9
    eor     r12, r8, r9             //Exec tc7 = z12 ^ tc4; into r12
    eor     r2, r2, r12             //Exec tc9 = z8 ^ tc7; into r2
    eor     r2, r6, r2              //Exec tc10 = tc8 ^ tc9; into r2
    ldr.w   r4, [sp, #32]           //Load z14 into r4
    eor     r12, r4, r2             //Exec tc17 = z14 ^ tc10; into r12
    eor     r0, r0, r12             //Exec S5 = tc21 ^ tc17; into r0
    eor     r6, r12, r14            //Exec tc26 = tc17 ^ tc20; into r6
    ldr.w   r4, [sp, #16]           //Load z17 into r4
    ldr     r12, [sp, #40]          //Load tc12 into r12
    eor     r6, r6, r4              //Exec S2 = tc26 ^ z17 ^ 1; into r6
    eor     r12, r9, r12            //Exec tc14 = tc4 ^ tc12; into r12
    eor     r14, r11, r12           //Exec tc18 = tc13 ^ tc14; into r14
    eor     r2, r2, r14             //Exec S6 = tc10 ^ tc18 ^ 1; into r2
    eor     r11, r8, r14            //Exec S7 = z12 ^ tc18 ^ 1; into r11
    ldr     r14, [sp, #52]          // restore link register
    eor     r8, r12, r7             //Exec S4 = tc14 ^ S3; into r8
    bx      lr
    // [('r0', 'S5'), ('r1', 'S0'), ('r2', 'S6'), ('r3', 'S1'),
    // ('r6', 'S2'),('r7', 'S3'), ('r8', 'S4'), ('r11', 'S7')]

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations, it is used for rounds i s.t. (i%4) == 0.
* For semi-fixsliced implementations, it is used for rounds i s.t. (i%2) == 0.
******************************************************************************/
.align 2
mixcolumns_0:
    movw    r12, #0x0303
    movt    r12, #0x0303
    and     r5, r12, r1, lsr #6     // r5 <- (S0 >> 6) & 0x03030303
    bic     r9, r1, r12, ror #2     // r9 <- S0 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #2      // r5 <- BYTE_ROR_6(S0)
    eor     r4, r1, r5, ror #8      // r4 <- S0 ^ (BYTE_ROR_6(S0) >>> 8)
    and     r5, r12, r11, lsr #6    // r5 <- (S7 >> 6) & 0x03030303
    bic     r9, r11, r12, ror #2    // r9 <- S7 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #2      // r5 <- BYTE_ROR_6(S7)
    eor     r10, r11, r5, ror #8    // r10<- S7 ^ BYTE_ROR_6(S7 >>> 8)
    bic     r9, r11, r12            // r9 <- S7 & 0xfcfcfcfc
    eor     r5, r4, r9, ror #26     // r5 <- r4 ^ (r9 >>> 26)
    and     r9, r11, r12            // r9 <- S7 & 0x03030303
    eor     r11, r5, r9, ror #18    // r11<- r4 ^ BYTE_ROR_2(S7 >>> 24)
    and     r9, r12, r10, lsr #6    // r9 <- (r10 >> 6) & 0x03030303
    bic     r5, r10, r12, ror #2    // r5 <- r10 & 0x3f3f3f3f
    orr     r5, r9, r5, lsl #2      // r5 <- BYTE_ROR_6(r10)
    eor     r11, r11, r5, ror #8    // r11 <- S'7
    eor     r10, r10, r4            // S0^S7 ^ BYTE_ROR_6(S0^S7 >>> 8)
    and     r5, r12, r2, lsr #6     // r5 <- (S6 >> 6) & 0x03030303
    bic     r9, r2, r12, ror #2     // r9 <- S6 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #2      // r5 <- BYTE_ROR_6(S6)
    eor     r9, r2, r5, ror #8      // r9 <- S6 ^ BYTE_ROR_6(S6 >>> 8)
    bic     r5, r2, r12             // r5 <- S6 & 0xfcfcfcfc
    eor     r10, r10, r5, ror #26   // r10<- r10 ^ (r5 >>> 26)
    and     r2, r2, r12             // r2 <- S6 & 0x03030303
    eor     r10, r10, r2, ror #18   // r10<- r4 ^ S7 ^ BYTE_ROR_6(S7 >>> 8) ^ BYTE_ROR_2(S6 >>> 24)
    and     r5, r12, r9, lsr #6     // r5 <- (r9 >> 6) & 0x03030303
    bic     r2, r9, r12, ror #2     // r2 <- r9 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #2      // r2 <- BYTE_ROR_6(r9)
    eor     r10, r10, r2, ror #8    // r10<- S'6
    and     r5, r12, r0, lsr #6     // r5 <- (S5 >> 6) & 0x03030303
    bic     r2, r0, r12, ror #2     // r2 <- S5 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #2      // r5 <- BYTE_ROR_6(S5)
    eor     r2, r0, r5, ror #8      // r2 <- S5 ^ BYTE_ROR_6(S5 >>> 8)
    bic     r5, r0, r12             // r5 <- S5 & 0xfcfcfcfc
    eor     r9, r9, r5, ror #26     // r9 <- r9 ^ (r5 >>> 26)
    and     r0, r0, r12             // r0 <- S5 & 0x03030303
    eor     r9, r9, r0, ror #18     // r9 <- S6 ^ BYTE_ROR_6(S6 >>> 8) ^ BYTE_ROR_2(S5 >>> 24)
    and     r5, r12, r2, lsr #6     // r5 <- (r2 >> 6) & 0x03030303
    bic     r0, r2, r12, ror #2     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #2      // r0 <- BYTE_ROR_6(r2)
    eor     r9, r9, r0, ror #8      // r9 <- S'5
    eor     r2, r2, r4              // r2 <- S0^S5 ^ BYTE_ROR_6(S0^S5 >>> 8)
    and     r5, r12, r8, lsr #6     // r5 <- (S4 >> 6) & 0x03030303
    bic     r0, r8, r12, ror #2     // r0 <- S4 & 0x3f3f3f3f
    orr     r5, r5, r0, lsl #2      // r5 <- BYTE_ROR_6(S4)
    eor     r0, r8, r5, ror #8      // r0 <- S4 ^ BYTE_ROR_6(S4 >>> 8)
    bic     r5, r8, r12             // r5 <- S4 & 0xfcfcfcfc
    eor     r2, r2, r5, ror #26     // r2 <- r2 ^ (r5 >>> 26)
    and     r8, r8, r12             // r8 <- S4 & 0x03030303
    eor     r8, r2, r8, ror #18     // r8 <- S0^S5 ^ BYTE_ROR_6(S0^S4^S5 >>> 8)^ BYTE_ROR_2(S4 >>> 24)
    and     r5, r12, r0, lsr #6     // r5 <- (r0 >> 6) & 0x03030303
    bic     r2, r0, r12, ror #2     // r2 <- r0 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #2      // r2 <- BYTE_ROR_6(r0)
    eor     r8, r8, r2, ror #8      // r8 <- S'4
    eor     r0, r0, r4              // r0 <- S0^S4 ^ BYTE_ROR_6(S0^S4 >>> 8)
    and     r5, r12, r7, lsr #6     // r5 <- (S3 >> 6) & 0x03030303
    bic     r2, r7, r12, ror #2     // r2 <- S3 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #2      // r5 <- BYTE_ROR_6(S3)
    eor     r2, r7, r5, ror #8      // r2 <- S3 ^ BYTE_ROR_6(S3 >>> 8)
    bic     r5, r7, r12             // r5 <- S3 & 0xfcfcfcfc
    eor     r0, r0, r5, ror #26     // r0 <- r0 ^ (r5 >>> 26)
    and     r7, r7, r12             // r7 <- S3 & 0x03030303
    eor     r7, r0, r7, ror #18     // r7 <- S0^S4 ^ BYTE_ROR_6(S0^S4^S3 >>> 8)^ BYTE_ROR_2(S3 >>> 24)
    and     r5, r12, r2, lsr #6     // r5 <- (r2 >> 6) & 0x03030303
    bic     r0, r2, r12, ror #2     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #2      // r0 <- BYTE_ROR_6(r2)
    eor     r7, r7, r0, ror #8      // r7 <- S'3
    and     r5, r12, r6, lsr #6     // r5 <- (S2 >> 6) & 0x03030303
    bic     r0, r6, r12, ror #2     // r0 <- S2 & 0x3f3f3f3f
    orr     r5, r5, r0, lsl #2      // r5 <- BYTE_ROR_6(S2)
    eor     r0, r6, r5, ror #8      // r0 <- S2 ^ BYTE_ROR_6(S2 >>> 8)
    bic     r5, r6, r12             // r5 <- S2 & 0xfcfcfcfc
    eor     r2, r2, r5, ror #26     // r2 <- r2 ^ (r5 >>> 26)
    and     r6, r6, r12             // r6 <- S2 & 0x03030303
    eor     r6, r2, r6, ror #18     // r6 <- S3 ^ BYTE_ROR_6(S3^S2 >>> 8)^ BYTE_ROR_2(S2 >>> 24)
    and     r5, r12, r0, lsr #6     // r5 <- (r0 >> 6) & 0x03030303
    bic     r2, r0, r12, ror #2     // r2 <- r0 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #2      // r2 <- BYTE_ROR_6(r0)
    eor     r6, r6, r2, ror #8      // r6 <- S'2
    and     r5, r12, r3, lsr #6     // r5 <- (S1 >> 6) & 0x03030303
    bic     r2, r3, r12, ror #2     // r2 <- S1 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #2      // r5 <- BYTE_ROR_6(S2)
    eor     r2, r3, r5, ror #8      // r2 <- S1 ^ BYTE_ROR_6(S1 >>> 8)
    bic     r5, r3, r12             // r5 <- S1 & 0xfcfcfcfc
    eor     r0, r0, r5, ror #26     // r0 <- r0 ^ (r5 >>> 26)
    and     r3, r3, r12             // r3 <- S1 & 0x03030303
    eor     r3, r0, r3, ror #18     // r3 <- S2 ^ BYTE_ROR_6(S2^S1 >>> 8)^ BYTE_ROR_2(S1 >>> 24)
    and     r5, r12, r2, lsr #6     // r5 <- (r2 >> 6) & 0x03030303
    bic     r0, r2, r12, ror #2     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #2      // r0 <- BYTE_ROR_6(r2)
    eor     r5, r3, r0, ror #8      // r5 <- S'1
    bic     r3, r1, r12             // r3 <- S0 & 0xfcfcfcfc
    eor     r2, r2, r3, ror #26     // r2 <- r2 ^ (r3 >>> 26)
    and     r1, r1, r12             // r1 <- S0 & 0x03030303
    eor     r1, r2, r1, ror #18     // r1 <- S1 ^ BYTE_ROR_6(S1 >>> 8)^ BYTE_ROR_2(S0 >>> 24)
    and     r3, r12, r4, lsr #6     // r3 <- (r4 >> 6) & 0x03030303
    bic     r4, r4, r12, ror #2     // r4 <- r4 & 0x3f3f3f3f
    orr     r4, r3, r4, lsl #2      // r4 <- BYTE_ROR_6(r4)
    eor     r4, r1, r4, ror #8      // r4 <- S'0
    bx      lr

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations only, for round i s.t. (i%4) == 1.
******************************************************************************/
.align 2
mixcolumns_1:
    str     r14, [sp, #52]          // store link register
    movw    r14, #0x0f0f
    movt    r14, #0x0f0f            // r14<- 0x0f0f0f0f (mask for BYTE_ROR_4)
    and     r5, r14, r1, lsr #4     // r5 <- (S0 >> 4) & 0x0f0f0f0f
    and     r9, r14, r1             // r9 <- S0 & 0x0f0f0f0f
    orr     r5, r5, r9, lsl #4      // r5 <- BYTE_ROR_4(S0)
    eor     r4, r1, r5, ror #8      // r4 <- S0 ^ (BYTE_ROR_4(S0) >>> 8)
    mov.w   r1, r5, ror #8          // r1 <- (BYTE_ROR_4(S0) >>> 8)
    and     r5, r14, r11, lsr #4    // r5 <- (S7 >> 4) & 0x0f0f0f0f
    and     r9, r14, r11            // r9 <- S7 & 0x0f0f0f0f
    orr     r5, r5, r9, lsl #4      // r5 <- BYTE_ROR_4(S7)
    eor     r12, r11, r5, ror #8    // r12<- S7 ^ (BYTE_ROR_4(S7) >>> 8)
    eor     r10, r4, r12            // r10<- r4 ^ r12
    eor     r11, r10                // r11<- S7 ^ r4 ^ r12
    eor     r11, r11, r12, ror #16  // r11<- r11 ^ (r12 >>> 16)
    and     r5, r14, r2, lsr #4     // r5 <- (S6 >> 4) & 0x0f0f0f0f
    and     r9, r14, r2             // r9 <- S6 & 0x0f0f0f0f
    orr     r5, r5, r9, lsl #4      // r5 <- BYTE_ROR_4(S6)
    eor     r10, r10, r5, ror #8    // r10<- r10 ^ (BYTE_ROR_4(S6) >>> 8)
    eor     r12, r2, r5, ror #8     // r12<- S6 ^ (BYTE_ROR_4(S6) >>> 8)
    eor     r10, r10, r12, ror #16  // r10<- r10 ^ (r12 >>> 16)
    and     r5, r14, r0, lsr #4     // r5 <- (S5 >> 4) & 0x0f0f0f0f
    and     r9, r14, r0             // r9 <- S5 & 0x0f0f0f0f
    orr     r5, r5, r9, lsl #4      // r5 <- BYTE_ROR_4(S5)
    eor     r9, r12, r5, ror #8     // r9 <- r12 ^ (BYTE_ROR_4(S5) >>> 8)
    eor     r12, r0, r5, ror #8     // r12<- S5 ^ (BYTE_ROR_4(S5) >>> 8)
    eor     r9, r9, r12, ror #16    // r9 <- (r9 ^ r12 >>> 16)
    eor     r0, r4, r12             // r0 <- r12 ^ S0 ^ (BYTE_ROR_4(S0) >>> 8)
    and     r5, r14, r8, lsr #4     // r5 <- (S4 >> 4) & 0x0f0f0f0f
    and     r2, r14, r8             // r2 <- S4 & 0x0f0f0f0f
    orr     r2, r5, r2, lsl #4      // r2 <- BYTE_ROR_4(S4)
    eor     r0, r0, r2, ror #8      // r0 <- r0 ^ (BYTE_ROR_4(S4) >>> 8)
    eor     r2, r8, r2, ror #8      // r2 <- S4 ^ (BYTE_ROR_4(S4) >>> 8)
    eor     r8, r0, r2, ror #16     // r8 <- r0 ^ (r2 >>> 16)
    eor     r2, r4                  // r2 <- r2 ^ S0 ^ (BYTE_ROR_4(S0) >>> 8)
    and     r5, r14, r7, lsr #4     // r5 <- (S3 >> 4) & 0x0f0f0f0f
    and     r0, r14, r7             // r0 <- S3 & 0x0f0f0f0f
    orr     r0, r5, r0, lsl #4      // r0 <- BYTE_ROR_4(S3)
    eor     r2, r2, r0, ror #8      // r2 <- r2 ^ (BYTE_ROR_4(S3) >>> 8)
    eor     r0, r7, r0, ror #8      // r0 <- S3 ^ (BYTE_ROR_4(S3) >>> 8)
    eor     r7, r2, r0, ror #16     // r7 <- r2 ^ (r0 >>> 16)
    and     r5, r14, r6, lsr #4     // r5 <- (S2 >> 4) & 0x0f0f0f0f
    and     r2, r14, r6             // r2 <- S2 & 0x0f0f0f0f
    orr     r2, r5, r2, lsl #4      // r2 <- BYTE_ROR_4(S2)
    eor     r0, r0, r2, ror #8      // r0 <- r0 ^ (BYTE_ROR_4(S2) >>> 8)
    eor     r2, r6, r2, ror #8      // r2 <- S2 ^ (BYTE_ROR_4(S2) >>> 8)
    eor     r6, r0, r2, ror #16     // r6 <- r0 ^ (r2 >>> 16)
    and     r5, r14, r3, lsr #4     // r5 <- (S1 >> 4) & 0x0f0f0f0f
    and     r0, r14, r3             // r0 <- S1 & 0x0f0f0f0f
    orr     r0, r5, r0, lsl #4      // r0 <- BYTE_ROR_4(S1)
    ldr     r14, [sp, #52]          // restore link register
    eor     r2, r2, r0, ror #8      // r2 <- r2 ^ (BYTE_ROR_4(S1) >>> 8)
    eor     r0, r3, r0, ror #8      // r0 <- S1 ^ (BYTE_ROR_4(S1) >>> 8)
    eor     r5, r2, r0, ror #16     // r5 <- r2 <- (r0 >>> 16)
    eor     r1, r0, r1              // r1 <- r0 ^ BYTE_ROR_4(S0) >>> 8
    eor     r4, r1, r4, ror #16     // r4 <- r4 ^ (r0 >>> 16)
    bx      lr

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations only, for rounds i s.t. (i%4) == 2.
******************************************************************************/
.align 2
mixcolumns_2:
    movw    r12, #0x3f3f
    movt    r12, #0x3f3f
    and     r5, r12, r1, lsr #2     // r5 <- (S0 >> 2) & 0x03030303
    bic     r9, r1, r12, ror #6     // r9 <- S0 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #6      // r5 <- BYTE_ROR_2(S0)
    eor     r4, r1, r5, ror #8      // r4 <- S0 ^ (BYTE_ROR_2(S0) >>> 8)
    and     r5, r12, r11, lsr #2    // r5 <- (S7 >> 2) & 0x03030303
    bic     r9, r11, r12, ror #6    // r9 <- S7 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #6      // r5 <- BYTE_ROR_2(S7)
    eor     r10, r11, r5, ror #8    // r10<- S7 ^ BYTE_ROR_2(S7 >>> 8)
    bic     r9, r11, r12            // r9 <- S7 & 0xfcfcfcfc
    eor     r5, r4, r9, ror #30     // r5 <- r4 ^ (r9 >>> 30)
    and     r9, r11, r12            // r9 <- S7 & 0x03030303
    eor     r11, r5, r9, ror #22    // r11<- r4 ^ BYTE_ROR_2(S7 >>> 24)
    and     r9, r12, r10, lsr #2    // r9 <- (r10 >> 2) & 0x03030303
    bic     r5, r10, r12, ror #6    // r5 <- r10 & 0x3f3f3f3f
    orr     r5, r9, r5, lsl #6      // r5 <- BYTE_ROR_2(r10)
    eor     r11, r11, r5, ror #8    // r11 <- S'7
    eor     r10, r10, r4            // S0^S7 ^ BYTE_ROR_2(S0^S7 >>> 8)
    and     r5, r12, r2, lsr #2     // r5 <- (S6 >> 2) & 0x03030303
    bic     r9, r2, r12, ror #6     // r9 <- S6 & 0x3f3f3f3f
    orr     r5, r5, r9, lsl #6      // r5 <- BYTE_ROR_2(S6)
    eor     r9, r2, r5, ror #8      // r9 <- S6 ^ BYTE_ROR_2(S6 >>> 8)
    bic     r5, r2, r12             // r5 <- S6 & 0xfcfcfcfc
    eor     r10, r10, r5, ror #30   // r10<- r10 ^ (r5 >>> 30)
    and     r2, r2, r12             // r2 <- S6 & 0x03030303
    eor     r10, r10, r2, ror #22   // r10<- r4 ^ S7 ^ BYTE_ROR_2(S7 >>> 8) ^ BYTE_ROR_6(S6 >>> 24)
    and     r5, r12, r9, lsr #2     // r5 <- (r9 >> 2) & 0x03030303
    bic     r2, r9, r12, ror #6     // r2 <- r9 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #6      // r2 <- BYTE_ROR_2(r9)
    eor     r10, r10, r2, ror #8    // r10<- S'6
    and     r5, r12, r0, lsr #2     // r5 <- (S5 >> 2) & 0x03030303
    bic     r2, r0, r12, ror #6     // r2 <- S5 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #6      // r5 <- BYTE_ROR_2(S5)
    eor     r2, r0, r5, ror #8      // r2 <- S5 ^ BYTE_ROR_2(S5 >>> 8)
    bic     r5, r0, r12             // r5 <- S5 & 0xfcfcfcfc
    eor     r9, r9, r5, ror #30     // r9 <- r9 ^ (r5 >>> 30)
    and     r0, r0, r12             // r0 <- S5 & 0x03030303
    eor     r9, r9, r0, ror #22     // r9 <- S6 ^ BYTE_ROR_2(S6 >>> 8) ^ BYTE_ROR_6(S5 >>> 24)
    and     r5, r12, r2, lsr #2     // r5 <- (r2 >> 2) & 0x03030303
    bic     r0, r2, r12, ror #6     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #6      // r0 <- BYTE_ROR_2(r2)
    eor     r9, r9, r0, ror #8      // r9 <- S'5
    eor     r2, r2, r4              // r2 <- S0^S5 ^ BYTE_ROR_2(S0^S5 >>> 8)
    and     r5, r12, r8, lsr #2     // r5 <- (S4 >> 2) & 0x03030303
    bic     r0, r8, r12, ror #6     // r0 <- S4 & 0x3f3f3f3f
    orr     r5, r5, r0, lsl #6      // r5 <- BYTE_ROR_2(S4)
    eor     r0, r8, r5, ror #8      // r0 <- S4 ^ BYTE_ROR_2(S4 >>> 8)
    bic     r5, r8, r12             // r5 <- S4 & 0xfcfcfcfc
    eor     r2, r2, r5, ror #30     // r2 <- r2 ^ (r5 >>> 30)
    and     r8, r8, r12             // r8 <- S4 & 0x03030303
    eor     r8, r2, r8, ror #22     // r8 <- S0^S5 ^ BYTE_ROR_2(S0^S4^S5 >>> 8)^ BYTE_ROR_6(S4 >>> 24)
    and     r5, r12, r0, lsr #2     // r5 <- (r0 >> 2) & 0x03030303
    bic     r2, r0, r12, ror #6     // r2 <- r0 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #6      // r2 <- BYTE_ROR_2(r0)
    eor     r8, r8, r2, ror #8      // r8 <- S'4
    eor     r0, r0, r4              // r0 <- S0^S4 ^ BYTE_ROR_2(S0^S4 >>> 8)
    and     r5, r12, r7, lsr #2     // r5 <- (S3 >> 2) & 0x03030303
    bic     r2, r7, r12, ror #6     // r2 <- S3 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #6      // r5 <- BYTE_ROR_2(S3)
    eor     r2, r7, r5, ror #8      // r2 <- S3 ^ BYTE_ROR_2(S3 >>> 8)
    bic     r5, r7, r12             // r5 <- S3 & 0xfcfcfcfc
    eor     r0, r0, r5, ror #30     // r0 <- r0 ^ (r5 >>> 30)
    and     r7, r7, r12             // r7 <- S3 & 0x03030303
    eor     r7, r0, r7, ror #22     // r7 <- S0^S4 ^ BYTE_ROR_2(S0^S4^S3 >>> 8)^ BYTE_ROR_6(S3 >>> 24)
    and     r5, r12, r2, lsr #2     // r5 <- (r2 >> 2) & 0x03030303
    bic     r0, r2, r12, ror #6     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #6      // r0 <- BYTE_ROR_2(r2)
    eor     r7, r7, r0, ror #8      // r7 <- S'3
    and     r5, r12, r6, lsr #2     // r5 <- (S2 >> 2) & 0x03030303
    bic     r0, r6, r12, ror #6     // r0 <- S2 & 0x3f3f3f3f
    orr     r5, r5, r0, lsl #6      // r5 <- BYTE_ROR_2(S2)
    eor     r0, r6, r5, ror #8      // r0 <- S2 ^ BYTE_ROR_2(S2 >>> 8)
    bic     r5, r6, r12             // r5 <- S2 & 0xfcfcfcfc
    eor     r2, r2, r5, ror #30     // r2 <- r2 ^ (r5 >>> 30)
    and     r6, r6, r12             // r6 <- S2 & 0x03030303
    eor     r6, r2, r6, ror #22     // r6 <- S3 ^ BYTE_ROR_2(S3^S2 >>> 8)^ BYTE_ROR_6(S2 >>> 24)
    and     r5, r12, r0, lsr #2     // r5 <- (r0 >> 2) & 0x03030303
    bic     r2, r0, r12, ror #6     // r2 <- r0 & 0x3f3f3f3f
    orr     r2, r5, r2, lsl #6      // r2 <- BYTE_ROR_2(r0)
    eor     r6, r6, r2, ror #8      // r6 <- S'2
    and     r5, r12, r3, lsr #2     // r5 <- (S1 >> 2) & 0x03030303
    bic     r2, r3, r12, ror #6     // r2 <- S1 & 0x3f3f3f3f
    orr     r5, r5, r2, lsl #6      // r5 <- BYTE_ROR_2(S2)
    eor     r2, r3, r5, ror #8      // r2 <- S1 ^ BYTE_ROR_2(S1 >>> 8)
    bic     r5, r3, r12             // r5 <- S1 & 0xfcfcfcfc
    eor     r0, r0, r5, ror #30     // r0 <- r0 ^ (r5 >>> 30)
    and     r3, r3, r12             // r3 <- S1 & 0x03030303
    eor     r3, r0, r3, ror #22     // r3 <- S2 ^ BYTE_ROR_2(S2^S1 >>> 8)^ BYTE_ROR_6(S1 >>> 24)
    and     r5, r12, r2, lsr #2     // r5 <- (r2 >> 2) & 0x03030303
    bic     r0, r2, r12, ror #6     // r0 <- r2 & 0x3f3f3f3f
    orr     r0, r5, r0, lsl #6      // r0 <- BYTE_ROR_2(r2)
    eor     r5, r3, r0, ror #8      // r5 <- S'1
    bic     r3, r1, r12             // r3 <- S0 & 0xfcfcfcfc
    eor     r2, r2, r3, ror #30     // r2 <- r2 ^ (r3 >>> 30)
    and     r1, r1, r12             // r1 <- S0 & 0x03030303
    eor     r1, r2, r1, ror #22     // r1 <- S1 ^ BYTE_ROR_2(S1 >>> 8)^ BYTE_ROR_6(S0 >>> 24)
    and     r3, r12, r4, lsr #2     // r3 <- (r4 >> 2) & 0x03030303
    bic     r4, r4, r12, ror #6     // r4 <- r4 & 0x3f3f3f3f
    orr     r4, r3, r4, lsl #6      // r4 <- BYTE_ROR_2(r4)
    eor     r4, r1, r4, ror #8      // r4 <- S'0
    bx      lr

/******************************************************************************
* Computation of the MixColumns transformation in the fixsliced representation.
* For fully-fixsliced implementations, it is used for rounds i s.t. (i%4) == 3.
* For semi-fixsliced implementations, it is used for rounds i s.t. (i%2) == 1.
* Based on Käsper-Schwabe, similar to https://github.com/Ko-/aes-armcortexm.
******************************************************************************/
.align 2
mixcolumns_3:
    eor     r12, r11, r11, ror #8   // r12<- S7 ^ (S7 >>> 8)
    eor     r4, r1, r1, ror #8      // r4 <- S0 ^ (S0 >>> 8)
    eor     r11, r4, r11, ror #8    // r11<- S0 ^ (S0 >>> 8) ^ (S7 >>> 8)
    eor     r11, r11, r12, ror #16  // r11<- r11 ^ (S7 >>> 16) ^ (S7 >>> 24)
    eor     r10, r12, r2, ror #8    // r10<- S7 ^ (S7 >>> 8) ^ (S6 >>> 8)
    eor     r12, r2, r2, ror #8     // r12<- S6 ^ (S6 >>> 8)
    eor     r10, r10, r12, ror #16  // r10<- r10 ^ (S6 >>> 16) ^ (S6 >>> 24)
    eor     r10, r4                 // r10<- r10 ^ S0 ^ (S0 >>> 8)
    eor     r9, r12, r0, ror #8     // r9 <- S6 ^ (S6 >>> 8) ^ (S5 >>> 8)
    eor     r12, r0, r0, ror #8     // r12<- S5 ^ (S5 >>> 8)
    eor     r9, r9, r12, ror #16    // r9 <- r9 ^ (S5 >>> 16) ^ (S5 >>> 24)
    eor     r2, r8, r8, ror #8      // r2 <- S4 ^ (S4 >>> 8)
    eor     r8, r12, r8, ror #8     // r8 <- S5 ^ (S5 >>> 8) ^ (S4 >>> 8)
    eor     r8, r4                  // r8 <- r8 ^ S0 ^ (S0 >>> 8)
    eor     r8, r8, r2, ror #16     // r8 <- r8 ^ (S4 >>> 16) ^ (S4 >>> 24)
    eor     r12, r7, r7, ror #8     // r12<- S3 ^ (S3 >>> 8)
    eor     r7, r2, r7, ror #8      // r7 <- S4 ^ (S4 >>> 8) ^ (S3 >>> 8)
    eor     r7, r4                  // r7 <- r7 ^ S0 ^ (S0 >>> 8)
    eor     r7, r7, r12, ror #16    // r7 <- r7 ^ (S3 >>> 16) ^ (S3 >>> 24)
    eor     r2, r6, r6, ror #8      // r2 <- S2 ^ (S2 >>> 8)
    eor     r6, r12, r6, ror #8     // r6 <- S3 ^ (S3 >>> 8) ^ (S2 >>> 8)
    eor     r6, r6, r2, ror #16     // r6 <- r6 ^ (S2 >>> 16) ^ (S2 >>> 24)
    eor     r12, r3, r3, ror #8     // r12<- S1 ^ (S1 >>> 8)
    eor     r5, r2, r3, ror #8      // r5 <- S2 ^ (S2 >>> 8) ^ (S1 >>> 8)
    eor     r5, r5, r12, ror #16    // r5 <- r5 ^ (S1 >>> 16) ^ (S1 >>> 24)
    eor     r4, r12, r4, ror #16    // r4 <- S1 ^ (S1 >>> 8) ^ (r4 >>> 16)
    eor     r4, r4, r1, ror #8      // r4 <- r4 ^ (S0 >>> 8)
    bx      lr

/******************************************************************************
* Applies the ShiftRows transformation twice (i.e. SR^2) on the internal state.
******************************************************************************/
.align 2
double_shiftrows:
    movw    r10, #0x0f00
    movt    r10, #0x0f00            // r10<- 0x0f000f00 (mask)
    eor     r12, r10, r10, ror #4   // r12<- 0x0ff00ff0 (mask)
    and     r5, r10, r11, ror #4    // r5 <- (S7 >>> 4) & 0x0f000f00
    and     r4, r10, r11            // r4 <- S7 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r11, r11, r12, ror #4   // r11<- S7 & 0x00ff00ff
    orr     r11, r5                 // r11<- r11 | r5
    and     r5, r10, r2, ror #4     // r5 <- (S6 >>> 4) & 0x0f000f00
    and     r4, r10, r2             // r4 <- S6 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r2, r2, r12, ror #4     // r2 <- S6 & 0x00ff00ff
    orr     r2, r5                  // r2 <- r2 | r5
    and     r5, r10, r0, ror #4     // r5 <- (S5 >>> 4) & 0x0f000f00
    and     r4, r10, r0             // r4 <- S5 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r0, r0, r12, ror #4     // r0 <- S5 & 0x00ff00ff
    orr     r0, r5                  // r0 <- r0 | r5
    and     r5, r10, r8, ror #4     // r5 <- (S4 >>> 4) & 0x0f000f00
    and     r4, r10, r8             // r4 <- S4 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r8, r8, r12, ror #4     // r8 <- S4 & 0x00ff00ff
    orr     r8, r5                  // r8 <- r8 | r5
    and     r5, r10, r7, ror #4     // r5 <- (S3 >>> 4) & 0x0f000f00
    and     r4, r10, r7             // r4 <- S3 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r7, r7, r12, ror #4     // r7 <- S3 & 0x00ff00ff
    orr     r7, r5                  // r7 <- r7 | r5
    and     r5, r10, r6, ror #4     // r5 <- (S2 >>> 4) & 0x0f000f00
    and     r4, r10, r6             // r4 <- S2 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r6, r6, r12, ror #4     // r6 <- S2 & 0x00ff00ff
    orr     r6, r5                  // r6 <- r6 | r5
    and     r5, r10, r3, ror #4     // r5 <- (S1 >>> 4) & 0x0f000f00
    and     r4, r10, r3             // r4 <- S1 & 0x0f000f00
    orr     r5, r5, r4, ror #28     // r5 <- r5 | (r4 >>> 28)
    and     r3, r3, r12, ror #4     // r3 <- S1 & 0x00ff00ff
    orr     r3, r5                  // r3 <- r3 | r5
    and     r5, r10, r1, ror #4     // r3 <- (S0 >>> 4) & 0x0f000f00
    and     r4, r10, r1             // r4 <- S0 & 0x0f000f00
    orr     r4, r5, r4, ror #28     // r4 <- r3 | (r4 >>> 28)
    and     r1, r1, r12, ror #4     // r1 <- S1 & 0x00ff00ff
    orr     r1, r4                  // r1 <- r1 | r4
    bx      lr

/******************************************************************************
* Fully-fixsliced implementation of AES-128.
*
* Two blocks are encrypted in parallel, without any operating mode.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
******************************************************************************/
@ void aes128_encrypt_ffs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                   const u8* ptext_bis, const u32* rkey);
.global aes128_encrypt_ffs
.type   aes128_encrypt_ffs,%function
.align 2
aes128_encrypt_ffs:
    push    {r0-r12,r14}
    sub.w   sp, #56                 // allow space on the stack for tmp var
    ldm     r2, {r4-r7}             // load the 1st 128-bit blocks in r4-r7
    ldm     r3, {r8-r11}            // load the 2nd 128-bit blocks in r8-r11
    ldr.w   r1, [sp, #112]          // load 'rkey' argument from the stack
    str.w   r1, [sp, #48]           // store it there for 'add_round_key'
    bl      packing                 // pack the 2 input blocks
    bl      ark_sbox                // ark + sbox (round 0)
    bl      mixcolumns_0            // mixcolumns (round 0)
    bl      ark_sbox                // ark + sbox (round 1)
    bl      mixcolumns_1            // mixcolumns (round 1)
    bl      ark_sbox                // ark + sbox (round 2)
    bl      mixcolumns_2            // mixcolumns (round 2)
    bl      ark_sbox                // ark + sbox (round 3)
    bl      mixcolumns_3            // mixcolumns (round 3)
    bl      ark_sbox                // ark + sbox (round 4)
    bl      mixcolumns_0            // mixcolumns (round 4)
    bl      ark_sbox                // ark + sbox (round 5)
    bl      mixcolumns_1            // mixcolumns (round 5)
    bl      ark_sbox                // ark + sbox (round 6)
    bl      mixcolumns_2            // mixcolumns (round 6)
    bl      ark_sbox                // ark + sbox (round 7)
    bl      mixcolumns_3            // mixcolumns (round 7)
    bl      ark_sbox                // ark + sbox (round 8)
    bl      mixcolumns_0            // mixcolumns (round 8)
    bl      ark_sbox                // ark + sbox (round 9)
    bl      double_shiftrows        // to resynchronize with the classical rep
    ldr     r14, [sp, #48]          // ---------------------------------------
    ldmia   r14!, {r4,r5,r10,r12}   // 
    eor     r4, r1                  // 
    eor     r5, r3                  // 
    eor     r6, r10                 // 
    eor     r7, r12                 //  Last add_round_key
    ldmia   r14!, {r1,r3,r10,r12}   // 
    eor     r8, r1                  // 
    eor     r9, r0, r3              // 
    eor     r10, r2                 // 
    eor     r11, r12                // ---------------------------------------
    bl      unpacking               // unpack the internal state
    ldrd    r0, r1, [sp, #56]       // restore the addr to store the ciphertext
    add.w   sp, #64                 // restore the stack pointer
    stm     r0, {r4-r7}             // store the ciphertext
    stm     r1, {r8-r11}            // store the ciphertext
    pop     {r2-r12, r14}           // restore context
    bx      lr

/******************************************************************************
* Fully-fixsliced implementation of AES-256.
*
* Two blocks are encrypted in parallel, without any operating mode.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
******************************************************************************/
@ void aes256_encrypt_ffs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                   const u8* ptext_bis, const u32* rkey);
.global aes256_encrypt_ffs
.type   aes256_encrypt_ffs,%function
.align 2
aes256_encrypt_ffs:
    push    {r0-r12,r14}
    sub.w   sp, #56                 // allow space on the stack for tmp var
    ldm     r2, {r4-r7}             // load the 1st 128-bit blocks in r4-r7
    ldm     r3, {r8-r11}            // load the 2nd 128-bit blocks in r8-r11
    ldr.w   r1, [sp, #112]          // load 'rkey' argument from the stack
    str.w   r1, [sp, #48]           // store it there for 'add_round_key'
    bl      packing                 // pack the 2 input blocks
    bl      ark_sbox                // ark + sbox (round 0)
    bl      mixcolumns_0            // mixcolumns (round 0)
    bl      ark_sbox                // ark + sbox (round 1)
    bl      mixcolumns_1            // mixcolumns (round 1)
    bl      ark_sbox                // ark + sbox (round 2)
    bl      mixcolumns_2            // mixcolumns (round 2)
    bl      ark_sbox                // ark + sbox (round 3)
    bl      mixcolumns_3            // mixcolumns (round 3)
    bl      ark_sbox                // ark + sbox (round 4)
    bl      mixcolumns_0            // mixcolumns (round 4)
    bl      ark_sbox                // ark + sbox (round 5)
    bl      mixcolumns_1            // mixcolumns (round 5)
    bl      ark_sbox                // ark + sbox (round 6)
    bl      mixcolumns_2            // mixcolumns (round 6)
    bl      ark_sbox                // ark + sbox (round 7)
    bl      mixcolumns_3            // mixcolumns (round 7)
    bl      ark_sbox                // ark + sbox (round 8)
    bl      mixcolumns_0            // mixcolumns (round 8)
    bl      ark_sbox                // ark + sbox (round 9)
    bl      mixcolumns_1            // mixcolumns (round 9)
    bl      ark_sbox                // ark + sbox (round 10)
    bl      mixcolumns_2            // mixcolumns (round 10)
    bl      ark_sbox                // ark + sbox (round 11)
    bl      mixcolumns_3            // mixcolumns (round 11)
    bl      ark_sbox                // ark + sbox (round 12)
    bl      mixcolumns_0            // mixcolumns (round 12)
    bl      ark_sbox                // ark + sbox (round 13)
    bl      double_shiftrows        // to resynchronize with the classical rep
    ldr     r14, [sp, #48]          // ---------------------------------------
    ldmia   r14!, {r4,r5,r10,r12}   // 
    eor     r4, r1                  // 
    eor     r5, r3                  // 
    eor     r6, r10                 // 
    eor     r7, r12                 //  Last add_round_key
    ldmia   r14!, {r1,r3,r10,r12}   // 
    eor     r8, r1                  // 
    eor     r9, r0, r3              // 
    eor     r10, r2                 // 
    eor     r11, r12                // ---------------------------------------
    bl      unpacking               // unpack the internal state
    ldrd    r0, r1, [sp, #56]       // restore the addr to store the ciphertext
    add.w   sp, #64                 // restore the stack pointer
    stm     r0, {r4-r7}             // store the ciphertext
    stm     r1, {r8-r11}            // store the ciphertext
    pop     {r2-r12, r14}           // restore context
    bx      lr

/******************************************************************************
* Semi-fixsliced and loop-based implementation of AES-128.
*
* Two blocks are encrypted in parallel.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
******************************************************************************/
@ void aes128_encrypt_sfs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                   const u8* ptext_bis, const u32* rkey);
.global aes128_encrypt_sfs
.type   aes128_encrypt_sfs,%function
.align 2
aes128_encrypt_sfs:
    push    {r0-r12,r14}
    sub.w   sp, #56                 // allow space on the stack for tmp var
    ldm     r2, {r4-r7}             // load the 1st 128-bit blocks in r4-r7
    ldm     r3, {r8-r11}            // load the 2nd 128-bit blocks in r8-r11
    ldr.w   r1, [sp, #112]          // load 'rkey' argument from the stack
    str.w   r1, [sp, #48]           // store it there for 'add_round_key'
    bl      packing                 // pack the 2 input blocks
    bl      ark_sbox                // ark + sbox (round 0)
    bl      mixcolumns_0            // mixcolumns (round 0)
    bl      ark_sbox                // ark + sbox (round 1)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 1)
    bl      ark_sbox                // ark + sbox (round 2)
    bl      mixcolumns_0            // mixcolumns (round 2)
    bl      ark_sbox                // ark + sbox (round 3)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 3)
    bl      ark_sbox                // ark + sbox (round 4)
    bl      mixcolumns_0            // mixcolumns (round 4)
    bl      ark_sbox                // ark + sbox (round 5)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 5)
    bl      ark_sbox                // ark + sbox (round 6)
    bl      mixcolumns_0            // mixcolumns (round 6)
    bl      ark_sbox                // ark + sbox (round 7)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 7)
    bl      ark_sbox                // ark + sbox (round 8)
    bl      mixcolumns_0            // mixcolumns (round 8)
    bl      ark_sbox                // ark + sbox (round 9)
    bl      double_shiftrows        // to resynchronize with the classical rep
    ldr   r14, [sp, #48]            // ---------------------------------------
    ldmia   r14!, {r4,r5,r10,r12}   // 
    eor     r4, r1                  // 
    eor     r5, r3                  // 
    eor     r6, r10                 // 
    eor     r7, r12                 //  Last add_round_key
    ldmia   r14!, {r1,r3,r10,r12}   // 
    eor     r8, r1                  // 
    eor     r9, r0, r3              // 
    eor     r10, r2                 // 
    eor     r11, r12                // ---------------------------------------
    bl      unpacking               // unpack the internal state
    ldrd    r0, r1, [sp, #56]       // restore the addr to store the ciphertext
    add.w   sp, #64                 // restore the stack pointer
    stm     r0, {r4-r7}             // store the ciphertext
    stm     r1, {r8-r11}            // store the ciphertext
    pop     {r2-r12, r14}           // restore context
    bx      lr

/******************************************************************************
* Semi-fixsliced and loop-based implementation of AES-256.
*
* Two blocks are encrypted in parallel.
*
* Note that additional 4 bytes are allocated on the stack as the function takes
* 5 arguments as input.
******************************************************************************/
@ void aes256_encrypt_sfs(u8* ctext, u8* ctext_bis, const u8* ptext,
@                   const u8* ptext_bis, const u32* rkey);
.global aes256_encrypt_sfs
.type   aes256_encrypt_sfs,%function
.align 2
aes256_encrypt_sfs:
    push    {r0-r12,r14}
    sub.w   sp, #56                 // allow space on the stack for tmp var
    ldm     r2, {r4-r7}             // load the 1st 128-bit blocks in r4-r7
    ldm     r3, {r8-r11}            // load the 2nd 128-bit blocks in r8-r11
    ldr.w   r1, [sp, #112]          // load 'rkey' argument from the stack
    str.w   r1, [sp, #48]           // store it there for 'add_round_key'
    bl      packing                 // pack the 2 input blocks
    bl      ark_sbox                // ark + sbox (round 0)
    bl      mixcolumns_0            // mixcolumns (round 0)
    bl      ark_sbox                // ark + sbox (round 1)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 1)
    bl      ark_sbox                // ark + sbox (round 2)
    bl      mixcolumns_0            // mixcolumns (round 2)
    bl      ark_sbox                // ark + sbox (round 3)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 3)
    bl      ark_sbox                // ark + sbox (round 4)
    bl      mixcolumns_0            // mixcolumns (round 4)
    bl      ark_sbox                // ark + sbox (round 5)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 5)
    bl      ark_sbox                // ark + sbox (round 6)
    bl      mixcolumns_0            // mixcolumns (round 6)
    bl      ark_sbox                // ark + sbox (round 7)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 7)
    bl      ark_sbox                // ark + sbox (round 8)
    bl      mixcolumns_0            // mixcolumns (round 8)
    bl      ark_sbox                // ark + sbox (round 9)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 9)
    bl      ark_sbox                // ark + sbox (round 10)
    bl      mixcolumns_0            // mixcolumns (round 10)
    bl      ark_sbox                // ark + sbox (round 11)
    bl      double_shiftrows        // to resynchronize with the classical rep
    bl      mixcolumns_3            // mixcolumns (round 11)
    bl      ark_sbox                // ark + sbox (round 12)
    bl      mixcolumns_0            // mixcolumns (round 12)
    bl      ark_sbox                // ark + sbox (round 13)
    bl      double_shiftrows        // to resynchronize with the classical rep
    ldr   r14, [sp, #48]            // ---------------------------------------
    ldmia   r14!, {r4,r5,r10,r12}   // 
    eor     r4, r1                  // 
    eor     r5, r3                  // 
    eor     r6, r10                 // 
    eor     r7, r12                 //  Last add_round_key
    ldmia   r14!, {r1,r3,r10,r12}   // 
    eor     r8, r1                  // 
    eor     r9, r0, r3              // 
    eor     r10, r2                 // 
    eor     r11, r12                // ---------------------------------------
    bl      unpacking               // unpack the internal state
    ldrd    r0, r1, [sp, #56]       // restore the addr to store the ciphertext
    add.w   sp, #64                 // restore the stack pointer
    stm     r0, {r4-r7}             // store the ciphertext
    stm     r1, {r8-r11}            // store the ciphertext
    pop     {r2-r12, r14}           // restore context
    bx      lr
