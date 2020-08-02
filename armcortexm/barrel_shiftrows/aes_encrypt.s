/******************************************************************************
* Bitsliced implementations of AES-128 and AES-256 (encryption only) in C using
* the barrel-shiftrows representation.
*
* See the paper available at https:// for more details.
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     August 2020
******************************************************************************/

.syntax unified
.thumb

/******************************************************************************
* AddRoundKey on the entire 1024-bit internal state.
******************************************************************************/
.align 2
add_round_key:
    ldm     r12, {r4-r11}       //state[0] ... state[7]
    ldr.w   r12, [sp, #180]     //load rkeys' address
    ldmia.w r12!, {r0-r3}       //rkeys for state[0]...state[3]
    eor     r4, r0, r4
    eor     r5, r1, r5
    eor     r6, r2, r6
    eor     r7, r3, r7
    ldmia.w r12!, {r0-r3}       //rkeys for state[4]...state[7]
    eor     r8, r0, r8
    eor     r9, r1, r9
    eor     r10, r2, r10
    eor     r11, r3, r11
    str     r12, [sp, #180]     //save rkeys' address
    bx      lr

/******************************************************************************
* Bitsliced implementation of the AES Sbox based on Boyar, Peralta and Calik.
* See http://www.cs.yale.edu/homes/peralta/CircuitStuff/SLP_AES_113.txt
* Note that the 4 NOT (^= 0xffffffff) are moved to the key schedule.
* Updates only a quarter of the state (i.e. 256 bits) => need to be applied 4
* times per round when considering the barrel-shiftrows representation.
******************************************************************************/
.align 2
sbox:
    str.w   r14, [sp, #176] //save link register
    eor     r1, r7, r9      //Exec y14 = U3 ^ U5; into r1
    eor     r3, r4, r10     //Exec y13 = U0 ^ U6; into r3
    eor     r2, r3, r1      //Exec y12 = y13 ^ y14; into r2
    eor     r0, r8, r2      //Exec t1 = U4 ^ y12; into r0
    eor     r14, r0, r9     //Exec y15 = t1 ^ U5; into r14
    and     r12, r2, r14    //Exec t2 = y12 & y15; into r12
    eor     r8, r14, r11    //Exec y6 = y15 ^ U7; into r8
    eor     r0, r0, r5      //Exec y20 = t1 ^ U1; into r0
    str.w   r2, [sp, #172]  //Store r2/y12 on stack
    eor     r2, r4, r7      //Exec y9 = U0 ^ U3; into r2
    str.w   r0, [sp, #168]  //Store r0/y20 on stack
    eor     r0, r0, r2      //Exec y11 = y20 ^ y9; into r0
    str.w   r2, [sp, #164]  //Store r2/y9 on stack
    and     r2, r2, r0      //Exec t12 = y9 & y11; into r2
    str.w   r8, [sp, #160]   //Store r8/y6 on stack
    eor     r8, r11, r0     //Exec y7 = U7 ^ y11; into r8
    eor     r9, r4, r9      //Exec y8 = U0 ^ U5; into r9
    eor     r6, r5, r6      //Exec t0 = U1 ^ U2; into r6
    eor     r5, r14, r6     //Exec y10 = y15 ^ t0; into r5
    str.w   r14, [sp, #156]  //Store r14/y15 on stack
    eor     r14, r5, r0     //Exec y17 = y10 ^ y11; into r14
    str.w   r1, [sp, #152]   //Store r1/y14 on stack
    and     r1, r1, r14     //Exec t13 = y14 & y17; into r1
    eor     r1, r1, r2      //Exec t14 = t13 ^ t12; into r1
    str.w   r14, [sp, #148]  //Store r14/y17 on stack
    eor     r14, r5, r9     //Exec y19 = y10 ^ y8; into r14
    str.w   r5, [sp, #144]   //Store r5/y10 on stack
    and     r5, r9, r5      //Exec t15 = y8 & y10; into r5
    eor     r2, r5, r2      //Exec t16 = t15 ^ t12; into r2
    eor     r5, r6, r0      //Exec y16 = t0 ^ y11; into r5
    str.w   r0, [sp, #140]   //Store r0/y11 on stack
    eor     r0, r3, r5      //Exec y21 = y13 ^ y16; into r0
    str.w   r3, [sp, #136]   //Store r3/y13 on stack
    and     r3, r3, r5      //Exec t7 = y13 & y16; into r3
    str.w   r5, [sp, #132]   //Store r5/y16 on stack
    str.w   r11, [sp, #128]  //Store r11/U7 on stack
    eor     r5, r4, r5      //Exec y18 = U0 ^ y16; into r5
    eor     r6, r6, r11     //Exec y1 = t0 ^ U7; into r6
    eor     r7, r6,  r7     //Exec y4 = y1 ^ U3; into r7
    and     r11, r7, r11    //Exec t5 = y4 & U7; into r11
    eor     r11, r11, r12   //Exec t6 = t5 ^ t2; into r11
    eor     r11, r11, r2    //Exec t18 = t6 ^ t16; into r11
    eor     r14, r11, r14   //Exec t22 = t18 ^ y19; into r14
    eor     r4, r6, r4      //Exec y2 = y1 ^ U0; into r4
    and     r11, r4, r8     //Exec t10 = y2 & y7; into r11
    eor     r11, r11, r3    //Exec t11 = t10 ^ t7; into r11
    eor     r2, r11, r2     //Exec t20 = t11 ^ t16; into r2
    eor     r2, r2, r5      //Exec t24 = t20 ^ y18; into r2
    eor     r10, r6, r10    //Exec y5 = y1 ^ U6; into r10
    and     r11, r10, r6    //Exec t8 = y5 & y1; into r11
    eor     r3, r11, r3     //Exec t9 = t8 ^ t7; into r3
    eor     r3, r3, r1      //Exec t19 = t9 ^ t14; into r3
    eor     r3, r3, r0      //Exec t23 = t19 ^ y21; into r3
    eor     r0, r10, r9     //Exec y3 = y5 ^ y8; into r0
    ldr.w   r11, [sp, #160] //Load y6 into r11
    and     r5, r0, r11     //Exec t3 = y3 & y6; into r5
    eor     r12,  r5, r12   //Exec t4 = t3 ^ t2; into r12
    ldr.w   r5, [sp, #168]  //Load y20 into r5
    str.w   r7, [sp, #160]  //Store r7/y4 on stack
    eor     r12, r12, r5    //Exec t17 = t4 ^ y20; into r12
    eor     r1, r12, r1     //Exec t21 = t17 ^ t14; into r1
    and     r12, r1, r3     //Exec t26 = t21 & t23; into r12
    eor     r5, r2, r12     //Exec t27 = t24 ^ t26; into r5
    eor     r12, r14, r12   //Exec t31 = t22 ^ t26; into r12
    eor     r1, r1, r14     //Exec t25 = t21 ^ t22; into r1
    and     r7, r1, r5      //Exec t28 = t25 & t27; into r7
    eor     r14, r7, r14    //Exec t29 = t28 ^ t22; into r14
    and     r4, r14, r4     //Exec z14 = t29 & y2; into r4
    and     r8, r14, r8     //Exec z5 = t29 & y7; into r8
    eor     r7, r3, r2      //Exec t30 = t23 ^ t24; into r7
    and     r12, r12, r7    //Exec t32 = t31 & t30; into r12
    eor     r12, r12, r2    //Exec t33 = t32 ^ t24; into r12
    eor     r7, r5, r12     //Exec t35 = t27 ^ t33; into r7
    and     r2, r2, r7      //Exec t36 = t24 & t35; into r2
    eor     r5, r5, r2      //Exec t38 = t27 ^ t36; into r5
    and     r5, r14, r5     //Exec t39 = t29 & t38; into r5
    eor     r1, r1, r5      //Exec t40 = t25 ^ t39; into r1
    eor     r5, r14, r1     //Exec t43 = t29 ^ t40; into r5
    ldr.w   r7, [sp, #132]  //Load y16 into r7
    and     r7, r5, r7      //Exec z3 = t43 & y16; into r7
    eor     r8, r7, r8      //Exec tc12 = z3 ^ z5; into r8
    str.w   r8, [sp, #168]  //Store r8/tc12 on stack
    and     r10, r1, r10    //Exec z13 = t40 & y5; into r10
    ldr.w   r8, [sp, #136]  //Load y13 into r8
    and     r8, r5, r8      //Exec z12 = t43 & y13; into r8
    and     r6, r1, r6      //Exec z4 = t40 & y1; into r6
    eor     r6, r7, r6      //Exec tc6 = z3 ^ z4; into r6
    eor     r3, r3, r12     //Exec t34 = t23 ^ t33; into r3
    eor     r3, r2, r3      //Exec t37 = t36 ^ t34; into r3
    eor     r1, r1, r3      //Exec t41 = t40 ^ t37; into r1
    ldr.w   r5, [sp, #144]  //Load y10 into r5
    and     r2, r1, r5      //Exec z8 = t41 & y10; into r2
    and     r9, r1, r9      //Exec z17 = t41 & y8; into r9
    str.w   r9, [sp, #144]  //Store r9/z17 on stack
    eor     r5, r12, r3     //Exec t44 = t33 ^ t37; into r5
    ldr.w   r7, [sp, #156]  //Load y15 into r7
    ldr.w   r9, [sp, #172]  //Load y12 into r9
    and     r7, r5, r7      //Exec z0 = t44 & y15; into r7
    and     r9, r5, r9      //Exec z9 = t44 & y12; into r9
    and     r0, r3, r0      //Exec z10 = t37 & y3; into r0
    and     r3, r3, r11     //Exec z1 = t37 & y6; into r3
    eor     r3, r3, r7      //Exec tc5 = z1 ^ z0; into r3
    eor     r3, r6, r3      //Exec tc11 = tc6 ^ tc5; into r3
    ldr.w   r11, [sp, #160]  //Load y4 into r11
    ldr.w   r5, [sp, #148]   //Load y17 into r5
    and     r11, r12, r11   //Exec z11 = t33 & y4; into r11
    eor     r14, r14, r12   //Exec t42 = t29 ^ t33; into r14
    eor     r1, r14, r1     //Exec t45 = t42 ^ t41; into r1
    and     r5, r1, r5      //Exec z7 = t45 & y17; into r5
    eor     r6, r5, r6      //Exec tc8 = z7 ^ tc6; into r6
    ldr.w   r5, [sp, #152]   //Load y14 into r5
    str.w   r4, [sp, #160]   //Store r4/z14 on stack
    and     r1, r1, r5      //Exec z16 = t45 & y14; into r1
    ldr.w   r5, [sp, #140]   //Load y11 into r5
    ldr.w   r4, [sp, #164]  //Load y9 into r4
    and     r5, r14, r5     //Exec z6 = t42 & y11; into r5
    eor     r5, r5, r6      //Exec tc16 = z6 ^ tc8; into r5
    and     r4, r14, r4     //Exec z15 = t42 & y9; into r4
    eor     r14, r4, r5     //Exec tc20 = z15 ^ tc16; into r14
    eor     r4, r4, r1      //Exec tc1 = z15 ^ z16; into r4
    eor     r1, r0, r4      //Exec tc2 = z10 ^ tc1; into r1
    eor     r0, r1, r11     //Exec tc21 = tc2 ^ z11; into r0
    eor     r9, r9, r1      //Exec tc3 = z9 ^ tc2; into r9
    eor     r1, r9, r5      //Exec S0 = tc3 ^ tc16; into r1
    eor     r9, r9, r3      //Exec S3 = tc3 ^ tc11; into r9
    eor     r3, r9, r5      //Exec S1 = S3 ^ tc16 ^ 1; into r3
    eor     r11, r10, r4    //Exec tc13 = z13 ^ tc1; into r11
    ldr.w   r4, [sp, #128]    //Load U7 into r4
    and     r12, r12, r4    //Exec z2 = t33 & U7; into r12
    eor     r7, r7, r12     //Exec tc4 = z0 ^ z2; into r7
    eor     r12, r8, r7     //Exec tc7 = z12 ^ tc4; into r12
    eor     r2, r2, r12     //Exec tc9 = z8 ^ tc7; into r2
    eor     r2, r6, r2      //Exec tc10 = tc8 ^ tc9; into r2
    ldr.w   r4, [sp, #160]   //Load z14 into r4
    eor     r12, r4, r2     //Exec tc17 = z14 ^ tc10; into r12
    eor     r0, r0, r12     //Exec S5 = tc21 ^ tc17; into r0
    eor     r6, r12, r14    //Exec tc26 = tc17 ^ tc20; into r6
    ldr.w   r4, [sp, #144]   //Load z17 into r4
    ldr.w   r12, [sp, #168]  //Load tc12 into r12
    eor     r6,  r6,  r4    //Exec S2 = tc26 ^ z17 ^ 1; into r6
    eor     r12, r7, r12    //Exec tc14 = tc4 ^ tc12; into r12
    eor     r14, r11, r12   //Exec tc18 = tc13 ^ tc14; into r14
    eor     r2, r2, r14     //Exec S6 = tc10 ^ tc18 ^ 1; into r2
    eor     r11, r8, r14    //Exec S7 = z12 ^ tc18 ^ 1; into r11
    ldr     r14, [sp, #176]     //restore link register
    eor     r4, r12,  r9    //Exec S4 = tc14 ^ S3; into r4
    bx      lr
    //[('r0', 'S5'), ('r1', 'S0'), ('r2', 'S6'), ('r3', 'S1'), ('r4', 'S4'), ('r6', 'S2'), ('r9', 'S3'), ('r11', 'S7')] 

/******************************************************************************
* Shifts the second row.
* Note that one can take advantage of the inline barrel-shiftrows to compute
* the rotations for free by doing some rework.
******************************************************************************/
.align 2
shiftrows_1:
    ror     r0, r0, #8
    ror     r1, r1, #8
    ror     r2, r2, #8
    ror     r3, r3, #8
    ror     r4, r4, #8
    ror     r6, r6, #8
    ror     r9, r9, #8
    ror     r11, r11, #8
    strd    r1, r3, [sp, #32]
    strd    r6, r9, [sp, #40]
    strd    r4, r0, [sp, #48]
    strd    r2, r11, [sp, #56]
    bx      lr

/******************************************************************************
* Shifts the third row.
* Note that one can take advantage of the inline barrel-shiftrows to compute
* the rotations for free by doing some rework.
******************************************************************************/
.align 2
shiftrows_2:
    ror     r0, r0, #16
    ror     r1, r1, #16
    ror     r2, r2, #16
    ror     r3, r3, #16
    ror     r4, r4, #16
    ror     r6, r6, #16
    ror     r9, r9, #16
    ror     r11, r11, #16
    strd    r1, r3, [sp, #64]
    strd    r6, r9, [sp, #72]
    strd    r4, r0, [sp, #80]
    strd    r2, r11, [sp, #88]
    bx      lr

/******************************************************************************
* Shifts the fourth row.
* Note that one can take advantage of the inline barrel-shiftrows to compute
* the rotations for free by doing some rework.
******************************************************************************/
.align 2
shiftrows_3:
    ror     r0, r0, #24
    ror     r1, r1, #24
    ror     r2, r2, #24
    ror     r3, r3, #24
    ror     r4, r4, #24
    ror     r6, r6, #24
    ror     r9, r9, #24
    ror     r11, r11, #24
    bx      lr

/******************************************************************************
* MixColumns according to the barrel-shiftrows representation.
******************************************************************************/
.align 2
mixcolumns:
    str.w   r14, [sp, #176]         //save link register
    ldr.w   r0, [sp]                //load S0 in r0
    ldr.w   r2, [sp, #32]           //load s8 in r2
    ldr.w   r3, [sp, #64]           //load s16 in r3
    ldr.w   r12, [sp, #28]          //load S7 in r12
    ldr.w   r10, [sp, #60]          //load S15 in r12
    ldr.w   r14, [sp, #92]          //load S23 in r14
    str.w   r4, [sp, #112]          //store S28 (interleaving saves some cycles)
    eor     r6, r0, r2              //r6 <- S0 ^ S8
    eor     r7, r2, r3              //r7 <- S8 ^ S16
    eor     r8, r3, r1              //r8 <- S16 ^ S24
    eor     r9, r1, r0              //r9 <- S24 ^ S0
    eor     r0, r12, r10            //r0 <- S7 ^ S15
    eor     r1, r10, r14            //r1 <- S15 ^ S23
    eor     r2, r14, r11            //r2 <- S23 ^ S31
    eor     r3, r11, r12            //r3 <- S31 ^ S7
    eor     r4, r6, r2              //r4 <- S0 ^ S8 ^ S23 ^ S31
    eor     r4, r4, r10             //r4 <- S'7 = S0 ^ S8 ^ S23 ^ S31 ^ S15
    ldr.w   r10, [sp, #24]          //load S6 in r10
    str.w   r4, [sp, #28]           //store S'7
    eor     r4, r7, r2              //r4 <- S8 ^ S16 ^ S23 ^ S31
    eor     r4, r4, r12             //r4 <- S'15 = S8 ^ S16 ^ S23 ^ S31 ^ S7
    ldr.w   r12, [sp, #56]          //load S14 in r12
    str.w   r4, [sp, #60]           //store S'15
    eor     r4, r8, r0              //r4 <- S16 ^ S24 ^ S7 ^ S15
    eor     r4, r4, r11             //r4 <- S'23 = S16 ^ S24 ^ S7 ^ S15 ^ S31
    ldr.w   r11, [sp, #88]          //load S22 in r11
    str.w   r4, [sp,#92]            //store S'23
    eor     r4, r9, r0              //r4 <- S24 ^ S0 ^ S7 ^ S15
    eor     r4, r4, r14             //r4 <- S'31 = S24 ^ S0 ^ S7 ^ S15 ^ S23
    ldr.w   r14, [sp, #120]         //load S30 in r14
    str.w   r4, [sp, #124]          //store S'31
    eor     r4, r11, r14            //r4 <- S22 ^ S30
    eor     r5, r14, r10            //r5 <- S30 ^ S6 
    eor     r0, r0, r6              //r0 <- S7 ^ S15 ^ S0 ^ S8
    eor     r0, r0, r4              //r0 <- S7 ^ S15 ^ S0 ^ S8 ^ S22 ^ S30
    eor     r0, r0, r12             //r0 <- S'6 = S7 ^ S15 ^ S0 ^ S8 ^ S22 ^ S30 ^ S14
    str.w   r0, [sp, #24]           //store S'6
    eor     r1, r1, r7              //r1 <- S7 ^ S15 ^ S8 ^ S16
    eor     r1, r1, r4              //r1 <- S7 ^ S15 ^ S8 ^ S16 ^ S22 ^ S30
    eor     r1, r1, r10             //r1 <- S'14 = S7 ^ S15 ^ S8 ^ S16 ^ S22 ^ S30 ^ S6
    str.w   r1, [sp, #56]           //store S'14
    eor     r0, r10, r12            //r0 <- S6 ^ S14
    eor     r1, r12, r11            //r1 <- S14 ^ S22
    eor     r2, r2, r8              //r2 <- S23 ^ S31 ^ S16 ^ S24
    eor     r2, r2, r5              //r2 <- S23 ^ S31 ^ S16 ^ S24 ^ S30 ^ S6
    eor     r2, r2, r12             //r2 <- S'22 = S23 ^ S31 ^ S16 ^ S24 ^ S30 ^ S6 ^ S14
    ldr.w   r10, [sp, #20]          //load S5 in r10
    ldr.w   r12, [sp, #52]          //load S13 in r12
    str.w   r2, [sp, #88]           //store S'22
    eor     r3, r3, r9              //r3 <- S31 ^ S7 ^ S24 ^ S0
    eor     r3, r3, r0              //r3 <- S31 ^ S7 ^ S24 ^ S0 ^ S6 ^ S14
    eor     r3, r3, r11             //r3 <- S'30 = S31 ^ S7 ^ S24 ^ S0 ^ S6 ^ S14 ^ S22
    ldr.w   r11, [sp, #84]          //load S21 in r11
    ldr.w   r14, [sp, #116]         //load S29 in r14
    str.w   r3, [sp, #120]          //store S'30
    eor     r2, r12, r11            //r2 <- S13 ^ S21
    eor     r3, r11, r14            //r3 <- S21 ^ S29
    eor     r0, r0, r2              //r0 <- S6 ^ S14 ^ S13 ^ S21
    eor     r0, r0, r14             //r0 <- S'5 = S6 ^ S14 ^ S13 ^ S21 ^ S29
    str.w   r0, [sp, #20]           //store S'5
    eor     r1, r1, r3              //r1 <- S14 ^ S22 ^ S21 ^ S29
    eor     r1, r1, r10             //r1 <- S'13 = S14 ^ S22 ^ S21 ^ S29 ^ S5
    str.w   r1, [sp, #52]           //store S'13
    eor     r0, r14, r10            //r0 <- S29 ^ S5
    eor     r1, r10, r12            //r1 <- S5 ^ S13
    eor     r4, r4, r0              //r4 <- S22 ^ S30 ^ S29 ^ S5
    eor     r4, r4, r12             //r4 <- S'21 = S22 ^ S30 ^ S29 ^ S5 ^ S13
    ldr.w   r10, [sp, #16]          //load S4 in r10
    ldr.w   r12, [sp, #48]          //load S12 in r12
    str.w   r4, [sp, #84]           //store S'21
    eor     r5, r5, r1              //r5 <- S30 ^ S6 ^ S5 ^ S13
    eor     r5, r5, r11             //r5 <- S'29 = S30 ^ S6 ^ S5 ^ S13 ^ S21
    ldr.w   r11, [sp, #80]          //load S20 in r11
    ldr.w   r14, [sp, #112]         //load S28 in r14
    str.w   r5, [sp, #116]          //store S'29
    eor     r4, r12, r11            //r4 <- S12 ^ S20
    eor     r5, r11, r14            //r5 <- S20 ^ S28
    eor     r1, r1, r6              //r1 <- S5 ^ S13 ^ S0 ^ S8
    eor     r1, r1, r4              //r1 <- S5 ^ S13 ^ S0 ^ S8 ^ S12 ^ S20
    eor     r1, r1, r14             //r1 <- S'4 = S5 ^ S13 ^ S0 ^ S8 ^ S12 ^ S20 ^ S28
    str.w   r1, [sp, #16]           //store S'4
    eor     r2, r2, r7              //r2 <- S13 ^ S21 ^ S8 ^ S16
    eor     r2, r2, r5              //r2 <- S13 ^ S21 ^ S8 ^ S16 ^ S20 ^ S28
    eor     r2, r2, r10             //r2 <- S'12 = S13 ^ S21 ^ S8 ^ S16 ^ S20 ^ S28 ^ S4
    str.w   r2, [sp, #48]           //store S'12
    eor     r1, r14, r10            //r1 <- S28 ^ S4
    eor     r2, r10, r12            //r2 <- S4 ^ S12
    eor     r3, r3, r8              //r3 <- S21 ^ S29 ^ S16 ^ S24
    eor     r3, r3, r1              //r3 <- S21 ^ S29 ^ S16 ^ S24 ^ S28 ^ S4
    eor     r3, r3, r12             //r3 <- S'20 = S21 ^ S29 ^ S16 ^ S24 ^ S28 ^ S4 ^ S12
    ldr.w   r10, [sp, #12]          //load S3 in r10
    ldr.w   r12, [sp, #44]          //load S11 in r12
    str.w   r3, [sp, #80]           //store S'20
    eor     r0, r0, r9              //r0 <- S29 ^ S5 ^ S24 ^ S0
    eor     r0, r0, r2              //r0 <- S29 ^ S5 ^ S24 ^ S0 ^ S4 ^ S12
    eor     r0, r0, r11             //r0 <- S'28 = S29 ^ S5 ^ S24 ^ S0 ^ S4 ^ S12 ^ S20
    ldr.w   r11, [sp, #76]          //load S19 in r11
    ldr.w   r14, [sp, #108]         //load S27 in r14
    str.w   r0, [sp, #112]          //store S'28
    eor     r0, r12, r11            //r0 <- S11 ^ S19
    eor     r3, r11, r14            //r3 <- S19 ^ S27
    eor     r2, r2, r6              //r2 <- S4 ^ S12 ^ S0 ^ S8
    eor     r2, r2, r0              //r2 <- S4 ^ S12 ^ S0 ^ S8 ^ S11 ^ S19
    eor     r2, r2, r14             //r2 <- S'3 = S4 ^ S12 ^ S0 ^ S8 ^ S11 ^ S19 ^ S27
    str.w   r2, [sp, #12]           //store S'3
    eor     r4, r4, r7              //r4 <- S12 ^ S20 ^ S8 ^ S16
    eor     r4, r4, r3              //r4 <- S12 ^ S20 ^ S8 ^ S16 ^ S19 ^ S27
    eor     r4, r4, r10             //r4 <- S'11 = S12 ^ S20 ^ S8 ^ S16 ^ S19 ^ S27 ^ S3
    str.w   r4, [sp, #44]           //store S'11
    eor     r4, r14, r10            //r4 <- S27 ^ S3
    eor     r2, r10, r12            //r2 <- S3 ^ S11
    eor     r5, r5, r8              //r5 <- S20 ^ S28 ^ S16 ^ S24
    eor     r5, r5, r4              //r5 <- S20 ^ S28 ^ S16 ^ S24 ^ S27 ^ S3
    eor     r5, r5, r12             //r5 <- S'19 = S20 ^ S28 ^ S16 ^ S24 ^ S27 ^ S3 ^ S11
    ldr.w   r10, [sp, #8]           //load S2 in r10
    ldr.w   r12, [sp, #40]          //load S10 in r12
    str.w   r5, [sp, #76]           //store S'19
    eor     r1, r1, r9              //r1 <- S28 ^ S4 ^ S24 ^ S0
    eor     r1, r1, r2              //r1 <- S28 ^ S4 ^ S24 ^ S0 ^ S3 ^ S11
    eor     r1, r1, r11             //r1 <- S'27 = S28 ^ S4 ^ S24 ^ S0 ^ S3 ^ S11 ^ S19
    ldr.w   r11, [sp, #72]          //load S18 in r11
    ldr.w   r14, [sp, #104]         //load S26 in r14
    str.w   r1, [sp, #108]          //store S'27
    eor     r1, r12, r11            //r1 <- S10 ^ S18
    eor     r5, r11, r14            //r5 <- S18 ^ S26
    eor     r2, r2, r1              //r2 <- S3 ^ S11 ^ S10 ^ S18
    eor     r2, r2, r14             //r2 <- S'2 = S3 ^ S11 ^ S10 ^ S18 ^ S26
    str.w   r2, [sp, #8]            //store S'2
    eor     r0, r0, r5              //r0 <- S11 ^ S19 ^ S18 ^ S26
    eor     r0, r0, r10             //r0 <- S'10 = S11 ^ S19 ^ S18 ^ S26 ^ S2
    str.w   r0, [sp, #40]           //store S'10
    eor     r2, r14, r10            //r2 <- S26 ^ S2
    eor     r0, r10, r12            //r0 <- S2 ^ S10
    eor     r3, r3, r2              //r3 <- S19 ^ S27 ^ S26 ^ S2
    eor     r3, r3, r12             //r3 <- S'18 = S19 ^ S27 ^ S26 ^ S2 ^S10
    ldr.w   r10, [sp, #4]           //load S1 in r10
    ldr.w   r12, [sp, #36]          //load S9 in r12
    str.w   r3, [sp, #72]           //store S'18
    eor     r4, r4, r0              //r4 <- S27 ^ S3 ^ S2 ^ S10
    eor     r4, r4, r11             //r4 <- S'26 = S27 ^ S3 ^ S2 ^ S10 ^ S18
    ldr.w   r11, [sp, #68]          //load S17 in r11
    ldr.w   r14, [sp, #100]         //load S25 in r14
    str.w   r4, [sp, #104]          //store S'26
    eor     r3, r12, r11            //r3 <- S9 ^ S17
    eor     r4, r11, r14            //r4 <- S17 ^ S25
    eor     r0, r0, r3              //r0 <- S2 ^ S10 ^ S9 ^ S17
    eor     r0, r0, r14             //r0 <- S'1 = S2 ^ S10 ^ S9 ^ S17 ^ S25
    str.w   r0, [sp, #4]            //store S'1
    eor     r1, r1, r4              //r1 <- S10 ^ S18 ^ S17 ^ S25
    eor     r1, r1, r10             //r1 <- S'9 = S10 ^ S18 ^ S17 ^ S25 ^ S1
    str.w   r1, [sp, #36]           //store S'9
    eor     r0, r14, r10            //r0 <- S25 ^ S1
    eor     r1, r10, r12            //r1 <- S1 ^ S9
    eor     r5, r5, r0              //r5 <- S18 ^ S26 ^  S25 ^ S1
    eor     r5, r5, r12             //r5 <- S'17 =  S18 ^ S26 ^  S25 ^ S1 ^ S9
    ldr.w   r10, [sp]               //load S0 in r10
    ldr.w   r12, [sp, #32]          //load S8 in r12
    str.w   r5, [sp, #68]           //store S'17
    eor     r2, r2, r1              //r2 <- S26 ^ S2 ^ S1 ^ S9
    eor     r2, r2, r11             //r2 <- S'25 = S26 ^ S2 ^ S1 ^ S9 ^ S17
    ldr.w   r11, [sp, #64]          //load S16 in r11
    ldr.w   r14, [sp, #96]          //load S24 in r14
    str.w   r2, [sp, #100]          //store S'25
    eor     r1, r1, r7              //r1 <- S1 ^ S9 ^ S8 ^ S16
    eor     r1, r1, r14             //r1 <- S'0 = S1 ^ S9 ^ S8 ^ S16 ^ S24
    str.w   r1, [sp]                //store S'0
    eor     r3, r3, r8              //r3 <- S9 ^ S17 ^ S16 ^ S24
    eor     r3, r3, r10             //r3 <- S'8 = S9 ^ S17 ^ S16 ^ S24 ^ S0
    str.w   r3, [sp, #32]           //store S'8
    eor     r4, r4, r9              //r4 <- S17 ^ S25 ^ S24 ^ S0
    eor     r4, r4, r12             //r4 <- S'16 = S17 ^ S25 ^ S24 ^ S0 ^ S8
    ldr.w   r14, [sp, #176]         //restore link register
    str.w   r4, [sp, #64]           //store S'16
    eor     r0, r0, r6              //r0 <- S25 ^ S1 ^ S0 ^ S8
    eor     r0, r0, r11             //r0 <- S'24 = S25 ^ S1 ^ S0 ^ S8 ^ S16
    str     r0, [sp, #96]
    bx      lr

/******************************************************************************
* Subroutine for the first layer of packing.
******************************************************************************/
.align 2
packing_0:
    movw    r0, #0x00ff
    movt    r0, #0x00ff             // mask for SWAPMOVE
    mov     r3, #0                  // loop counter
loop_p0:
    ldmia   r2!, {r4-r7}            // load input
    add.w   r3, r3, 1               // increment loop counter
    eor     r12, r5, r4, lsr #8
    and     r12, r12, r0
    eor     r5, r5, r12
    eor     r4, r4, r12, lsl #8     // SWAPMOVE(r4, r5, 0x00ff00ff, 8)
    eor     r12, r7, r6, lsr #8
    and     r12, r12, r0
    eor     r7, r7, r12
    eor     r6, r6, r12, lsl #8     // SWAPMOVE(r6, r7, 0x00ff00ff, 8)
    str.w   r4, [sp], #4            // store state words on the stack
    str.w   r5, [sp, #28]           // store state words on the stack
    str.w   r6, [sp, #60]           // store state words on the stack
    str.w   r7, [sp, #92]           // store state words on the stack
    cmp     r3, #7      
    ble     loop_p0                 // loop until r3 <= 7
    bx      lr

/******************************************************************************
* Subroutine for the second layer of packing.
******************************************************************************/
.align 2
packing_1:
    movw    r0, #0xffff             // mask for SWAPMOVE
    mov     r3, #0                  // loop counter
loop_p1:
    ldrd    r4, r5, [sp]            // load state from the stack
    ldrd    r6, r7, [sp, #64]       // load state from the stack
    add.w   r3, r3, 1               // increment loop counter
    eor     r12, r6, r4, lsr #16
    and     r12, r12, r0
    eor     r6, r6, r12
    eor     r4, r4, r12, lsl #16    //SWAPMOVE(r4, r6, 0x0000ffff, 16)
    eor     r12, r7, r5, lsr #16
    and     r12, r12, r0
    eor     r7, r7, r12
    eor     r5, r5, r12, lsl #16     //SWAPMOVE(r5, r7, 0x0000ffff, 8)
    strd    r4, r5, [sp], #8         // store state words on the stack
    strd    r6, r7, [sp, #56]        // store state words on the stack    
    cmp     r3, #7
    ble     loop_p1
    bx      lr

/******************************************************************************
* Subroutine for the third layer of packing.
******************************************************************************/
.align 2
packing_2:
    movw    r2, #0x0f0f
    movt    r2, #0x0f0f             // mask for SWAPMOVE
    eor     r1, r2, r2, lsl #2      // mask for SWAPMOVE (0x33333333)
    eor     r0, r1, r1, lsl #1      // mask for SWAPMOVE (0x55555555)
    mov     r3, #0                  // loop counter
loop_p2:
    ldm     sp, {r4-r11}
    add.w   r3, r3, 1
    eor     r12, r4, r5, lsr #1
    and     r12, r12, r0
    eor     r4, r4, r12
    eor     r5, r5, r12, lsl #1     //SWAPMOVE(r5, r4, 0x55555555, 1)
    eor     r12, r6, r7, lsr #1
    and     r12, r12, r0
    eor     r6, r6, r12
    eor     r7, r7, r12, lsl #1     //SWAPMOVE(r7, r6, 0x55555555, 1)
    eor     r12, r8, r9, lsr #1
    and     r12, r12, r0
    eor     r8, r8, r12
    eor     r9, r9, r12, lsl #1     //SWAPMOVE(r9, r8, 0x55555555, 1)
    eor     r12, r10, r11, lsr #1
    and     r12, r12, r0
    eor     r10, r10, r12
    eor     r11, r11, r12, lsl #1   //SWAPMOVE(r11, r10, 0x55555555, 1)
    eor     r12, r4, r6, lsr #2
    and     r12, r12, r1
    eor     r4, r4, r12
    eor     r6, r6, r12, lsl #2     //SWAPMOVE(r6, r4, 0x33333333, 2)
    eor     r12, r5, r7, lsr #2
    and     r12, r12, r1
    eor     r5, r5, r12
    eor     r7, r7, r12, lsl #2     //SWAPMOVE(r7, r5, 0x33333333, 2)
    eor     r12, r8, r10, lsr #2
    and     r12, r12, r1
    eor     r8, r8, r12
    eor     r10, r10, r12, lsl #2   //SWAPMOVE(r10, r8, 0x33333333, 2)
    eor     r12, r9, r11, lsr #2
    and     r12, r12, r1
    eor     r9, r9, r12
    eor     r11, r11, r12, lsl #2   //SWAPMOVE(r11, r9, 0x33333333, 2)
    eor     r12, r4, r8, lsr #4
    and     r12, r12, r2
    eor     r4, r4, r12
    eor     r8, r8, r12, lsl #4     //SWAPMOVE(r8, r4, 0x0f0f0f0f, 4)
    eor     r12, r5, r9, lsr #4
    and     r12, r12, r2
    eor     r5, r5, r12
    eor     r9, r9, r12, lsl #4     //SWAPMOVE(r9, r5, 0x0f0f0f0f, 4)
    eor     r12, r6, r10, lsr #4
    and     r12, r12, r2
    eor     r6, r6, r12
    eor     r10, r10, r12, lsl #4   //SWAPMOVE(r10, r6, 0x0f0f0f0f, 4)
    eor     r12, r7, r11, lsr #4
    and     r12, r12, r2
    eor     r7, r7, r12
    eor     r11, r11, r12, lsl #4   //SWAPMOVE(r11, r7, 0x0f0f0f0f, 4)
    stmia   sp!, {r4-r11}           // store the state words on the stack
    cmp     r3, #3
    ble     loop_p2                 //loop until r3 <= 3
    bx      lr

/******************************************************************************
* Subroutine for the first layer of unpacking.
******************************************************************************/
.align 2
unpacking_0:
    movw    r0, #0x00ff
    movt    r0, #0x00ff             // mask for SWAPMOVE
    mov     r3, #0                  // loop counter
loop_up0:
    ldr.w   r4, [sp], #4
    ldr.w   r5, [sp, #28]
    ldr.w   r6, [sp, #60]
    ldr.w   r7, [sp, #92]
    add.w   r3, r3, 1               // increment loop counter
    eor     r12, r5, r4, lsr #8
    and     r12, r12, r0
    eor     r5, r5, r12
    eor     r4, r4, r12, lsl #8     // SWAPMOVE(r4, r5, 0x00ff00ff, 8)
    eor     r12, r7, r6, lsr #8
    and     r12, r12, r0
    eor     r7, r7, r12
    eor     r6, r6, r12, lsl #8     // SWAPMOVE(r6, r7, 0x00ff00ff, 8)
    stmia   r2!, {r4-r7}            // store to output array
    cmp     r3, #7      
    ble     loop_up0                // loop until r3 <= 7
    bx      lr

/******************************************************************************
* Subroutine for the third layer of unpacking.
******************************************************************************/
.align 2
unpacking_2:
    movw    r2, #0x0f0f
    movt    r2, #0x0f0f             // mask for SWAPMOVE
    eor     r1, r2, r2, lsl #2      // mask for SWAPMOVE (0x33333333)
    eor     r0, r1, r1, lsl #1      // mask for SWAPMOVE (0x55555555)
    mov     r3, #0                  // loop counter
loop_up2:
    ldm     sp, {r4-r11}
    add.w   r3, r3, 1
    eor     r12, r4, r8, lsr #4
    and     r12, r12, r2
    eor     r4, r4, r12
    eor     r8, r8, r12, lsl #4     //SWAPMOVE(r8, r4, 0x0f0f0f0f, 4)
    eor     r12, r5, r9, lsr #4
    and     r12, r12, r2
    eor     r5, r5, r12
    eor     r9, r9, r12, lsl #4     //SWAPMOVE(r9, r5, 0x0f0f0f0f, 4)
    eor     r12, r6, r10, lsr #4
    and     r12, r12, r2
    eor     r6, r6, r12
    eor     r10, r10, r12, lsl #4   //SWAPMOVE(r10, r6, 0x0f0f0f0f, 4)
    eor     r12, r7, r11, lsr #4
    and     r12, r12, r2
    eor     r7, r7, r12
    eor     r11, r11, r12, lsl #4   //SWAPMOVE(r11, r7, 0x0f0f0f0f, 4)
    eor     r12, r4, r6, lsr #2
    and     r12, r12, r1
    eor     r4, r4, r12
    eor     r6, r6, r12, lsl #2     //SWAPMOVE(r6, r4, 0x33333333, 2)
    eor     r12, r5, r7, lsr #2
    and     r12, r12, r1
    eor     r5, r5, r12
    eor     r7, r7, r12, lsl #2     //SWAPMOVE(r7, r5, 0x33333333, 2)
    eor     r12, r8, r10, lsr #2
    and     r12, r12, r1
    eor     r8, r8, r12
    eor     r10, r10, r12, lsl #2   //SWAPMOVE(r10, r8, 0x33333333, 2)
    eor     r12, r9, r11, lsr #2
    and     r12, r12, r1
    eor     r9, r9, r12
    eor     r11, r11, r12, lsl #2   //SWAPMOVE(r11, r9, 0x33333333, 2)
    eor     r12, r4, r5, lsr #1
    and     r12, r12, r0
    eor     r4, r4, r12
    eor     r5, r5, r12, lsl #1     //SWAPMOVE(r5, r4, 0x55555555, 1)
    eor     r12, r6, r7, lsr #1
    and     r12, r12, r0
    eor     r6, r6, r12
    eor     r7, r7, r12, lsl #1     //SWAPMOVE(r7, r6, 0x55555555, 1)
    eor     r12, r8, r9, lsr #1
    and     r12, r12, r0
    eor     r8, r8, r12
    eor     r9, r9, r12, lsl #1     //SWAPMOVE(r9, r8, 0x55555555, 1)
    eor     r12, r10, r11, lsr #1
    and     r12, r12, r0
    eor     r10, r10, r12
    eor     r11, r11, r12, lsl #1   //SWAPMOVE(r11, r10, 0x55555555, 1)
    stmia   sp!, {r4-r11}           // store the state words on the stack
    cmp     r3, #3
    ble     loop_up2                //loop until r3 <= 3
    bx      lr

/******************************************************************************
* Encryption of 8 128-bit blocks of data in parallel using AES-128 with the
* barrel-shiftrows representation.
* The round keys are assumed to be pre-computed.
******************************************************************************/
.align 2
@ void aes128_encrypt(param* ctext, u32* rkey, const u8* ptext)
.global aes128_encrypt
.type   aes128_encrypt,%function
aes128_encrypt:
    push {r0-r12,r14}
    sub.w   sp, sp, #188
    str.w   r1, [sp, #180]      // store pointer to rkey on the stack
    mov     r1, #0              // init loop counter
    str.w   r1, [sp, #184]      // store loop counter on the stack
    bl      packing_0           // 1st packing layer
    sub.w   sp, sp, #32
    bl      packing_1           // 2nd packing layer
    sub.w   sp, sp, #64
    bl      packing_2           // 3rd packing layer
    sub.w   sp, sp, #128
loop_aes128_core:
    mov     r12, sp             // r12 points to 1st quarter state
    bl      add_round_key       // addroundkey on 1st quarter state
    bl      sbox                // sbox on 1st quarter state
    stm     sp, {r1,r3,r6,r9}
    strd    r4, r0, [sp, #16]
    strd    r2, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // addroundkey on 2nd quarter state
    bl      sbox                // sbox on 2nd quarter state
    bl      shiftrows_1         // shiftrows on 2nd quarter state
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // addroundkey on 3rd quarter state
    bl      sbox                // sbox on 3rd quarter state
    bl      shiftrows_2         // shiftrows on 3rd quarter state
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // addroundkey on 4th quarter state
    bl      sbox                // sbox on 4th quarter state
    bl      shiftrows_3         // shiftrows on 4t quarter state
    strd    r1, r3, [sp, #96]
    strd    r6, r9, [sp, #104]
    strd    r0, r2, [sp, #116]
    bl      mixcolumns          // mixcolumns on the entire state
    ldr.w   r1, [sp, #184]      // load loop counter
    add.w   r1, r1, #1          // increment loop counter
    str.w   r1, [sp, #184]      // store loop counter on the stack
    cmp     r1, #8
    ble     loop_aes128_core    // loop until r1 <= 8
    // Last round
    mov     r12, sp             // r12 points to 1st quarter state
    bl      add_round_key       // addroundkey on 1st quarter state
    bl      sbox                // sbox on 1st quarter state
    stm     sp, {r1,r3,r6,r9}
    strd    r4, r0, [sp, #16]
    strd    r2, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // addroundkey on 2nd quarter state
    bl      sbox                // sbox on 2nd quarter state
    bl      shiftrows_1         // shiftrows on 2nd quarter state
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // addroundkey on 3rd quarter state
    bl      sbox                // sbox on 3rd quarter state
    bl      shiftrows_2         // shiftrows on 3rd quarter state
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // addroundkey on 4th quarter state
    bl      sbox                // sbox on 4th quarter state
    bl      shiftrows_3         // shiftrows on 4t quarter state
    strd    r1, r3, [sp, #96]
    strd    r6, r9, [sp, #104]
    strd    r4, r0, [sp, #112]
    strd    r2, r11, [sp, #120]
    mov     r12, sp             // r12 points to 1st quarter state     
    bl      add_round_key       // last addroundkey on 1st quarter state
    strd    r4, r5, [sp]
    strd    r6, r7, [sp, #8]
    strd    r8, r9, [sp, #16]
    strd    r10, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // last addroundkey on 2nd quarter state
    strd    r4, r5, [sp, #32]
    strd    r6, r7, [sp, #40]
    strd    r8, r9, [sp, #48]
    strd    r10, r11, [sp, #56]
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // last addroundkey on 3rd quarter state
    strd    r4, r5, [sp, #64]
    strd    r6, r7, [sp, #72]
    strd    r8, r9, [sp, #80]
    strd    r10, r11, [sp, #88]
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // last addroundkey on 4th quarter state
    strd    r4, r5, [sp, #96]
    strd    r6, r7, [sp, #104]
    strd    r8, r9, [sp, #112]
    strd    r10, r11, [sp, #120]
    bl      unpacking_2         // order matters, have to use another routine
    sub.w   sp, sp, #128
    bl      packing_1           // order does not matter, can reuse packing routine
    sub.w   sp, sp, #64
    ldr     r2, [sp, #188]      // restore output address in r2
    bl      unpacking_0         // use another routine for input/output arrays
    add.w   sp, sp, #156
    pop     {r0-r12, r14}
    bx      lr

/******************************************************************************
* Encryption of 8 128-bit blocks of data in parallel using AES-128 with the
* barrel-shiftrows representation.
* The round keys are assumed to be pre-computed.
******************************************************************************/
.align 2
@ void aes256_encrypt(param* ctext, u32* rkey, const u8* ptext)
.global aes256_encrypt
.type   aes256_encrypt,%function
aes256_encrypt:
    push {r0-r12,r14}
    sub.w   sp, sp, #188
    str.w   r1, [sp, #180]      // store pointer to rkey on the stack
    mov     r1, #0              // init loop counter
    str.w   r1, [sp, #184]      // store loop counter on the stack
    bl      packing_0           // 1st packing layer
    sub.w   sp, sp, #32
    bl      packing_1           // 2nd packing layer
    sub.w   sp, sp, #64
    bl      packing_2           // 3rd packing layer
    sub.w   sp, sp, #128
loop_aes256_core:
    mov     r12, sp             // r12 points to 1st quarter state
    bl      add_round_key       // addroundkey on 1st quarter state
    bl      sbox                // sbox on 1st quarter state
    stm     sp, {r1,r3,r6,r9}
    strd    r4, r0, [sp, #16]
    strd    r2, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // addroundkey on 2nd quarter state
    bl      sbox                // sbox on 2nd quarter state
    bl      shiftrows_1         // shiftrows on 2nd quarter state
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // addroundkey on 3rd quarter state
    bl      sbox                // sbox on 3rd quarter state
    bl      shiftrows_2         // shiftrows on 3rd quarter state
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // addroundkey on 4th quarter state
    bl      sbox                // sbox on 4th quarter state
    bl      shiftrows_3         // shiftrows on 4t quarter state
    strd    r1, r3, [sp, #96]
    strd    r6, r9, [sp, #104]
    strd    r0, r2, [sp, #116]
    bl      mixcolumns          // mixcolumns on the entire state
    ldr.w   r1, [sp, #184]      // load loop counter
    add.w   r1, r1, #1          // increment loop counter
    str.w   r1, [sp, #184]      // store loop counter on the stack
    cmp     r1, #12
    ble     loop_aes256_core    // loop until r1 <= 8
    // Last round
    mov     r12, sp             // r12 points to 1st quarter state
    bl      add_round_key       // addroundkey on 1st quarter state
    bl      sbox                // sbox on 1st quarter state
    stm     sp, {r1,r3,r6,r9}
    strd    r4, r0, [sp, #16]
    strd    r2, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // addroundkey on 2nd quarter state
    bl      sbox                // sbox on 2nd quarter state
    bl      shiftrows_1         // shiftrows on 2nd quarter state
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // addroundkey on 3rd quarter state
    bl      sbox                // sbox on 3rd quarter state
    bl      shiftrows_2         // shiftrows on 3rd quarter state
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // addroundkey on 4th quarter state
    bl      sbox                // sbox on 4th quarter state
    bl      shiftrows_3         // shiftrows on 4t quarter state
    strd    r1, r3, [sp, #96]
    strd    r6, r9, [sp, #104]
    strd    r4, r0, [sp, #112]
    strd    r2, r11, [sp, #120]
    mov     r12, sp             // r12 points to 1st quarter state     
    bl      add_round_key       // last addroundkey on 1st quarter state
    strd    r4, r5, [sp]
    strd    r6, r7, [sp, #8]
    strd    r8, r9, [sp, #16]
    strd    r10, r11, [sp, #24]
    add.w   r12, sp, #32        // r12 points to 2nd quarter state
    bl      add_round_key       // last addroundkey on 2nd quarter state
    strd    r4, r5, [sp, #32]
    strd    r6, r7, [sp, #40]
    strd    r8, r9, [sp, #48]
    strd    r10, r11, [sp, #56]
    add.w   r12, sp, #64        // r12 points to 3rd quarter state
    bl      add_round_key       // last addroundkey on 3rd quarter state
    strd    r4, r5, [sp, #64]
    strd    r6, r7, [sp, #72]
    strd    r8, r9, [sp, #80]
    strd    r10, r11, [sp, #88]
    add.w   r12, sp, #96        // r12 points to 4th quarter state
    bl      add_round_key       // last addroundkey on 4th quarter state
    strd    r4, r5, [sp, #96]
    strd    r6, r7, [sp, #104]
    strd    r8, r9, [sp, #112]
    strd    r10, r11, [sp, #120]
    bl      unpacking_2         // order matters, have to use another routine
    sub.w   sp, sp, #128
    bl      packing_1           // order does not matter, can reuse packing routine
    sub.w   sp, sp, #64
    ldr     r2, [sp, #188]      // restore output address in r2
    bl      unpacking_0         // use another routine for input/output arrays
    add.w   sp, sp, #156
    pop     {r0-r12, r14}
    bx      lr
