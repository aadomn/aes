/******************************************************************************
* ARM assembly implementations of the AES-128 key schedule to match the barrel-
* shiftrows representation. Note that those implementations rely on Look-Up 
* Tables (LUT).
*
* See the paper available at https:// for more details.
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     July 2020
******************************************************************************/

.syntax unified
.thumb

/******************************************************************************
* LUT of the AES Sbox used in the key schedule.
******************************************************************************/
.align 2
.type AES_Sbox_compact,%object
AES_Sbox_compact:
    .word   0x7b777c63, 0xc56f6bf2, 0x2b670130, 0x76abd7fe
    .word   0x7dc982ca, 0xf04759fa, 0xafa2d4ad, 0xc072a49c
    .word   0x2693fdb7, 0xccf73f36, 0xf1e5a534, 0x1531d871
    .word   0xc323c704, 0x9a059618, 0xe2801207, 0x75b227eb
    .word   0x1a2c8309, 0xa05a6e1b, 0xb3d63b52, 0x842fe329
    .word   0xed00d153, 0x5bb1fc20, 0x39becb6a, 0xcf584c4a
    .word   0xfbaaefd0, 0x85334d43, 0x7f02f945, 0xa89f3c50
    .word   0x8f40a351, 0xf5389d92, 0x21dab6bc, 0xd2f3ff10
    .word   0xec130ccd, 0x1744975f, 0x3d7ea7c4, 0x73195d64
    .word   0xdc4f8160, 0x88902a22, 0x14b8ee46, 0xdb0b5ede
    .word   0x0a3a32e0, 0x5c240649, 0x62acd3c2, 0x79e49591
    .word   0x6d37c8e7, 0xa94ed58d, 0xeaf4566c, 0x08ae7a65
    .word   0x2e2578ba, 0xc6b4a61c, 0x1f74dde8, 0x8a8bbd4b
    .word   0x66b53e70, 0x0ef60348, 0xb9573561, 0x9e1dc186
    .word   0x1198f8e1, 0x948ed969, 0xe9871e9b, 0xdf2855ce
    .word   0x0d89a18c, 0x6842e6bf, 0x0f2d9941, 0x16bb54b0

/******************************************************************************
* Round function of the AES-128 key expansion.
* Note that it expects r2 to contain the corresponding round constant and r3 to
* contain the S-box address.
******************************************************************************/
.align 2
keyschedule_round_func:
    movw    r1, #0xfc
    and     r8, r1, r7, lsr #8
    and     r9, r1, r7, lsr #16
    and     r10, r1, r7, lsr #24
    and     r11, r1, r7
    ldr     r8, [r3, r8]            // computes the sbox using the LUT
    ldr     r9, [r3, r9]            // computes the sbox using the LUT
    ldr     r10, [r3, r10]          // computes the sbox using the LUT
    ldr     r11, [r3, r11]          // computes the sbox using the LUT
    movw    r1, #0x18
    and     r12, r1, r7, lsr #5     
    lsr     r8, r8, r12
    and     r8, #0xff
    and     r12, r1, r7, lsr #13     
    lsr     r9, r9, r12
    and     r9, #0xff
    and     r12, r1, r7, lsr #21     
    lsr     r10, r10, r12
    and     r10, #0xff
    and     r12, r1, r7, lsl #3     
    lsr     r11, r11, r12
    and     r11, #0xff
    eor     r4, r2                  // adds the rconst
    eor     r4, r8                  // xor the columns
    eor     r4, r4, r9, ror #24     // xor the columns
    eor     r4, r4, r10, ror #16    // xor the columns
    eor     r4, r4, r11, ror #8     // r4 <- rk[4]
    eor     r5, r4                  // r5 <- rk[5]
    eor     r6, r5                  // r6 <- rk[6]  
    eor     r7, r6                  // r7 <- rk[7]
    strd    r4, r5, [sp], #8        // store on the stack for bitslicing
    strd    r6, r7, [sp], #8        // store on the stack for bitslicing
    bx      lr


/******************************************************************************
* SWAPMOVE calls used in the packing_rkey subroutine.
******************************************************************************/
.align 2
swapmove_rkey:
    str.w   r14, [sp, #-4]          // store link register on the stack
    eor     r14, r5, r4, lsr #8     // SWAPMOVE(r4, r5, 0x00ff00ff, 8) ...
    and     r14, r14, r3
    eor     r5, r5, r14
    eor     r4, r4, r14, lsl #8     // ... SWAPMOVE(r4, r5, 0x00ff00ff, 8)
    eor     r14, r7, r6, lsr #8     // SWAPMOVE(r6, r7, 0x00ff00ff, 8) ...
    and     r14, r14, r3
    eor     r7, r7, r14
    eor     r6, r6, r14, lsl #8     // ... SWAPMOVE(r6, r7, 0x00ff00ff, 8)
    eor     r14, r6, r4, lsr #16    // SWAPMOVE(r4, r6, 0x0000ffff, 16) ...
    and     r14, r14, r2
    eor     r6, r6, r14
    eor     r4, r4, r14, lsl #16    // ... SWAPMOVE(r4, r6, 0x0000ffff, 16)
    eor     r14, r7, r5, lsr #16    // SWAPMOVE(r5, r7, 0x0000ffff, 16) ...
    and     r14, r14, r2
    eor     r7, r7, r14
    eor     r5, r5, r14, lsl #16    // ... SWAPMOVE(r5, r7, 0x0000ffff, 16)
    ldr.w   r14, [sp, #-4]          // restore link register
    bx      lr

/******************************************************************************
* Packing subroutine used to rearrange the rkeys to match the barrel-shiftrows.
* It is about twice more efficient than the 'packing' func. This optimization
* is possible because the 8 16-byte blocks to pack are all equal.
******************************************************************************/
.align 2
packing_rkey:
    and     r8, r4, r1              // r8 <- r4 & 0x80808080
    orr     r8, r8, r8, lsr #1      // r8 <- r8 | r8 >> 1
    orr     r8, r8, r8, lsr #2      // r8 <- r8 | r8 >> 2
    orr     r8, r8, r8, lsr #4      // r8 <- r8 | r8 >> 4
    and     r9, r1, r4, lsl #1      // r9 <- r4 << 1 & 0x80808080
    orr     r9, r9, r9, lsr #1      // r9 <- r9 | r9 >> 1
    orr     r9, r9, r9, lsr #2      // r9 <- r9 | r9 >> 2
    orr     r9, r9, r9, lsr #4      // r9 <- r9 | r9 >> 4
    and     r10, r1, r4, lsl #2     // r10<- r4 << 2 & 0x80808080
    orr     r10, r10, r10, lsr #1   // r10<- r10 | r10 >> 1
    orr     r10, r10, r10, lsr #2   // r10<- r10 | r10 >> 2
    orr     r10, r10, r10, lsr #4   // r10<- r10 | r10 >> 4
    and     r11, r1, r4, lsl #3     // r11<- r4 << 3 & 0x80808080
    orr     r11, r11, r11, lsr #1   // r11<- r11 | r11 >> 1
    orr     r11, r11, r11, lsr #2   // r11<- r11 | r11 >> 2
    orr     r11, r11, r11, lsr #4   // r11<- r11 | r11 >> 4
    stmia   r0!, {r8-r11}
    and     r8, r1, r4, lsl #4      // r8 <- r4 << 4 & 0x80808080
    orr     r8, r8, r8, lsr #1      // r8 <- r8 | r8 >> 1
    orr     r8, r8, r8, lsr #2      // r8 <- r8 | r8 >> 2
    orr     r8, r8, r8, lsr #4      // r8 <- r8 | r8 >> 4
    and     r9, r1, r4, lsl #5      // r9 <- r4 << 5 & 0x80808080
    orr     r9, r9, r9, lsr #1      // r9 <- r9 | r9 >> 1
    orr     r9, r9, r9, lsr #2      // r9 <- r9 | r9 >> 2
    orr     r9, r9, r9, lsr #4      // r9 <- r9 | r9 >> 4
    and     r10, r1, r4, lsl #6     // r10<- r4 << 6 & 0x80808080
    orr     r10, r10, r10, lsr #1   // r10<- r10 | r10 >> 1
    orr     r10, r10, r10, lsr #2   // r10<- r10 | r10 >> 2
    orr     r10, r10, r10, lsr #4   // r10<- r10 | r10 >> 4
    and     r11, r1, r4, lsl #7     // r11<- r4 << 7 & 0x80808080
    orr     r11, r11, r11, lsr #1   // r11<- r11 | r11 >> 1
    orr     r11, r11, r11, lsr #2   // r11<- r11 | r11 >> 2
    orr     r11, r11, r11, lsr #4   // r11<- r11 | r11 >> 4
    stmia   r0!, {r8-r11}
    bx      lr

/******************************************************************************
* Packing subroutine used to rearrange the rkeys to match the barrel-shiftrows.
* Same as 'packing_rkey' but includes NOT to speed up SBox calculations in the
* encryption function. Could be removed by adding 'mvn' instructions manually
* instead of taking advantage of the 'bic' instruction to save some cycles.
******************************************************************************/
.align 2
packing_rkey_not:
    and     r8, r4, r1              // r8 <- r4 & 0x80808080
    orr     r8, r8, r8, lsr #1      // r8 <- r8 | r8 >> 1
    orr     r8, r8, r8, lsr #2      // r8 <- r8 | r8 >> 2
    orr     r8, r8, r8, lsr #4      // r8 <- r8 | r8 >> 4
    bic     r9, r1, r4, lsl #1      // r9 <- r4 << 1 & 0x80808080
    orr     r9, r9, r9, lsr #1      // r9 <- r9 | r9 >> 1
    orr     r9, r9, r9, lsr #2      // r9 <- r9 | r9 >> 2
    orr     r9, r9, r9, lsr #4      // r9 <- r9 | r9 >> 4
    bic     r10, r1, r4, lsl #2     // r10<- r4 << 2 & 0x80808080
    orr     r10, r10, r10, lsr #1   // r10<- r10 | r10 >> 1
    orr     r10, r10, r10, lsr #2   // r10<- r10 | r10 >> 2
    orr     r10, r10, r10, lsr #4   // r10<- r10 | r10 >> 4
    and     r11, r1, r4, lsl #3     // r11<- r4 << 3 & 0x80808080
    orr     r11, r11, r11, lsr #1   // r11<- r11 | r11 >> 1
    orr     r11, r11, r11, lsr #2   // r11<- r11 | r11 >> 2
    orr     r11, r11, r11, lsr #4   // r11<- r11 | r11 >> 4
    stmia   r0!, {r8-r11}
    and     r8, r1, r4, lsl #4      // r8 <- r4 << 4 & 0x80808080
    orr     r8, r8, r8, lsr #1      // r8 <- r8 | r8 >> 1
    orr     r8, r8, r8, lsr #2      // r8 <- r8 | r8 >> 2
    orr     r8, r8, r8, lsr #4      // r8 <- r8 | r8 >> 4
    and     r9, r1, r4, lsl #5      // r9 <- r4 << 5 & 0x80808080
    orr     r9, r9, r9, lsr #1      // r9 <- r9 | r9 >> 1
    orr     r9, r9, r9, lsr #2      // r9 <- r9 | r9 >> 2
    orr     r9, r9, r9, lsr #4      // r9 <- r9 | r9 >> 4
    bic     r10, r1, r4, lsl #6     // r10<- r4 << 6 & 0x80808080
    orr     r10, r10, r10, lsr #1   // r10<- r10 | r10 >> 1
    orr     r10, r10, r10, lsr #2   // r10<- r10 | r10 >> 2
    orr     r10, r10, r10, lsr #4   // r10<- r10 | r10 >> 4
    bic     r11, r1, r4, lsl #7     // r11<- r4 << 7 & 0x80808080
    orr     r11, r11, r11, lsr #1   // r11<- r11 | r11 >> 1
    orr     r11, r11, r11, lsr #2   // r11<- r11 | r11 >> 2
    orr     r11, r11, r11, lsr #4   // r11<- r11 | r11 >> 4
    stmia   r0!, {r8-r11}
    bx      lr

/******************************************************************************
* Pre-computes all the AES-128 round keys according to the barrel-shiftrows 
* representation. Note that additional NOTs are incorporated to speed up SBox
* calculations in the encryption function.
******************************************************************************/
@ void aes128_keyschedule_lut(u32* rkeys, const u8* key);
.global aes128_keyschedule_lut
.type   aes128_keyschedule_lut,%function
.align 2
aes128_keyschedule_lut:
    push    {r0-r12,r14}
    sub.w   sp, #160                // allocate space to store the 11 rkeys
    ldm     r1, {r4-r7}             // load the encryption key
    adr     r3, AES_Sbox_compact    // load the sbox LUT address in r3
    movw    r2, #0x01               // 1st const
    bl      keyschedule_round_func  // 1st round
    movw    r2, #0x02               // 2nd rconst
    bl      keyschedule_round_func  // 2nd round
    movw    r2, #0x04               // 3rd rconst
    bl      keyschedule_round_func  // 3rd round
    movw    r2, #0x08               // 4th rconst
    bl      keyschedule_round_func  // 4th round
    movw    r2, #0x10               // 5th rconst
    bl      keyschedule_round_func  // 5th round
    movw    r2, #0x20               // 6th rconst
    bl      keyschedule_round_func  // 6th round
    movw    r2, #0x40               // 7th rconst
    bl      keyschedule_round_func  // 7th round
    movw    r2, #0x80               // 8th rconst
    bl      keyschedule_round_func  // 8th round
    movw    r2, #0x1b               // 9th rconst
    bl      keyschedule_round_func  // 9th round
    movw    r2, #0x36               // 10th rconst
    bl      keyschedule_round_func  // 10th round
    //done expanding, now start bitslicing
    ldr.w   r1, [sp, #4]
    ldm     r1, {r4-r7}             // load the encryption key
    sub.w   sp, #160                // stack now points to the 1st key
    movw    r1, #0x8080
    movt    r1, #0x8080             // r1 <- 0x80808080
    movw    r2, #0xffff             // r2 <- 0x0000ffff
    eor     r3, r2, r2, lsl #8      // r3 <- 0x00ff00ff
    bl      swapmove_rkey
    bl      packing_rkey            // do not apply NOT on the 1st key
    mov     r4, r5
    bl      packing_rkey            // do not apply NOT on the 1st key
    mov     r4, r6
    bl      packing_rkey            // do not apply NOT on the 1st key
    mov     r4, r7
    bl      packing_rkey            // do not apply NOT on the 1st key
    movw    r12, #10
loop_keyschedule:
    ldmia   sp!, {r4-r7} 
    bl      swapmove_rkey
    bl      packing_rkey_not
    mov     r4, r5
    bl      packing_rkey_not
    mov     r4, r6
    bl      packing_rkey_not
    mov     r4, r7
    bl      packing_rkey_not
    subs    r12, #1
    bne     loop_keyschedule
    pop     {r0-r12, r14}           // restore context
    bx      lr
