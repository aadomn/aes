/******************************************************************************
* ARM assembly implementations of the AES-128 key schedule to match fixslicing.
* Note that those implementations rely on Look-Up Tables (LUT).
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
* LUT of the AES S-box.
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
    eor     r4, r2                  // adds the first rconst
    eor     r4, r8                  // xor the columns
    eor     r4, r4, r9, ror #24     // xor the columns
    eor     r4, r4, r10, ror #16    // xor the columns
    eor     r4, r4, r11, ror #8     // r4 <- rk[4]
    eor     r5, r4                  // r5 <- rk[5]
    eor     r6, r5                  // r6 <- rk[6]  
    eor     r7, r6                  // r7 <- rk[7]
    push.w   {r4-r7}
    bx      lr

/******************************************************************************
* Packing routine. Note that it is the same as the one used in the encryption
* function so some code size could be saved by merging the two files.
******************************************************************************/
.align 2
packing_rkey:
    eor     r12, r8, r8, lsr #1     // SWAPMOVE(r8, r4, 0x55555555, 1) ....
    and     r12, r1
    eor     r4, r8, r12
    eor     r8, r8, r12, lsl #1     // .... SWAPMOVE(r8, r4, 0x55555555, 1)
    eor     r12, r9, r9, lsr #1     // SWAPMOVE(r9, r5, 0x55555555, 1) ....
    and     r12, r1
    eor     r5, r9, r12
    eor     r9, r9, r12, lsl #1     // .... SWAPMOVE(r9, r5, 0x55555555, 1)
    eor     r12, r10, r10, lsr #1   // SWAPMOVE(r10, r6, 0x55555555, 1) ....
    and     r12, r1
    eor     r6, r10, r12
    eor     r10, r10, r12, lsl #1   // .... SWAPMOVE(r10, r6, 0x55555555, 1)
    eor     r12, r11, r11, lsr #1   // SWAPMOVE(r11, r7, 0x55555555, 1) ....
    and     r12, r1
    eor     r7, r11, r12
    eor     r11, r11, r12, lsl #1   // .... SWAPMOVE(r11, r7, 0x55555555, 1)
    eor     r12, r4, r5, lsr #2     // SWAPMOVE(r5, r4, 0x33333333, 2) ....
    and     r12, r2
    eor     r4, r12
    eor     r5, r5, r12, lsl #2     // .... SWAPMOVE(r5, r4, 0x33333333, 2)
    eor     r12, r8, r9, lsr #2     // SWAPMOVE(r9, r8, 0x33333333, 2) ....
    and     r12, r2
    eor     r8, r8, r12
    eor     r9, r9, r12, lsl #2     // .... SWAPMOVE(r9, r8, 0x33333333, 2)
    eor     r12, r6, r7, lsr #2     // SWAPMOVE(r7, r6, 0x33333333, 2) ....
    and     r12, r2
    eor     r6, r6, r12
    eor     r7, r7, r12, lsl #2     // .... SWAPMOVE(r7, r6, 0x33333333, 2)
    eor     r12, r10, r11, lsr #2   // SWAPMOVE(r11, r10, 0x33333333, 2) ....
    and     r12, r2
    eor     r10, r10, r12
    eor     r11, r11, r12, lsl #2   // .... SWAPMOVE(r11, r10, 0x33333333, 2)
    eor     r12, r4, r6, lsr #4     // SWAPMOVE(r6, r4, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r4, r12
    eor     r6, r6, r12, lsl #4     // .... SWAPMOVE(r6, r4, 0x0f0f0f0f,4)
    eor     r12, r5, r7, lsr #4     // SWAPMOVE(r7, r5, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r5, r5, r12
    eor     r7, r7, r12, lsl #4     // .... SWAPMOVE(r7, r5, 0x0f0f0f0f, 4)
    eor     r12, r8, r10, lsr #4    // SWAPMOVE(r10, r8, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r8, r8, r12
    eor     r10, r10, r12, lsl #4   // .... SWAPMOVE(r10,r8, 0x0f0f0f0f, 4)
    eor     r12, r9, r11, lsr #4    // SWAPMOVE(r11, r9, 0x0f0f0f0f, 4) ....
    and     r12, r3
    eor     r9, r12
    eor     r11, r11, r12, lsl #4   // .... SWAPMOVE(r11, r9, 0x0f0f0f0f, 4)
    mvn     r5, r5
    mvn     r8, r8
    mvn     r7, r7
    mvn     r11, r11
    strd    r7, r11, [r0, #-8]
    strd    r6, r10, [r0, #-16]
    strd    r5, r9, [r0, #-24]
    strd    r4, r8, [r0, #-32]!
    bx      lr

/******************************************************************************
* Applies ShiftRows^(-1) on a round key to match fully/semi-fixslicing.
******************************************************************************/
.align 2
inv_shiftrows_1:
    and     r8, r4, #0xff
    and     r12, r7, #0xff00
    orr     r8, r8, r12
    and     r12, r6, #0xff0000
    orr     r8, r8, r12
    and     r12, r5, #0xff000000
    orr     r8, r8, r12
    and     r9, r5, #0xff
    and     r12, r4, #0xff00
    orr     r9, r9, r12
    and     r12, r7, #0xff0000
    orr     r9, r9, r12
    and     r12, r6, #0xff000000
    orr     r9, r9, r12
    and     r10, r6, #0xff
    and     r12, r5, #0xff00
    orr     r10, r10, r12
    and     r12, r4, #0xff0000
    orr     r10, r10, r12
    and     r12, r7, #0xff000000
    orr     r10, r10, r12
    and     r11, r7, #0xff
    and     r12, r6, #0xff00
    orr     r11, r11, r12
    and     r12, r5, #0xff0000
    orr     r11, r11, r12
    and     r12, r4, #0xff000000
    orr     r11, r11, r12
    bx      lr

/******************************************************************************
* Applies ShiftRows^(-2) on a round key to match full-fixslicing.
******************************************************************************/
.align 2
inv_shiftrows_2:
    movw    r12, #0xff00
    movt    r12, #0xff00
    eor     r8, r4, r6
    and     r8, r8, r12
    eor     r10, r8, r6
    eor     r8, r8, r4
    eor     r9, r5, r7
    and     r9, r9, r12
    eor     r11, r9, r7
    eor     r9, r9, r5
    bx      lr

/******************************************************************************
* Applies ShiftRows^(-3) on a round key to match fully-fixslicing.
******************************************************************************/
.align 2
inv_shiftrows_3:
    and     r8, r4, #0xff
    and     r12, r5, #0xff00
    orr     r8, r8, r12
    and     r12, r6, #0xff0000
    orr     r8, r8, r12
    and     r12, r7, #0xff000000
    orr     r8, r8, r12
    and     r9, r5, #0xff
    and     r12, r6, #0xff00
    orr     r9, r9, r12
    and     r12, r7, #0xff0000
    orr     r9, r9, r12
    and     r12, r4, #0xff000000
    orr     r9, r9, r12
    and     r10, r6, #0xff
    and     r12, r7, #0xff00
    orr     r10, r10, r12
    and     r12, r4, #0xff0000
    orr     r10, r10, r12
    and     r12, r5, #0xff000000
    orr     r10, r10, r12
    and     r11, r7, #0xff
    and     r12, r4, #0xff00
    orr     r11, r11, r12
    and     r12, r5, #0xff0000
    orr     r11, r11, r12
    and     r12, r6, #0xff000000
    orr     r11, r11, r12
    bx      lr

/******************************************************************************
* Pre-computes all the round keys for a given encryption key, according to the
* fully-fixsliced (ffs) representation.
* Note that the round keys also include the NOTs omitted in the S-box. 
******************************************************************************/
@ void aes128_keyschedule_ffs_lut(u32* rkeys, const u8* key);
.global aes128_keyschedule_ffs_lut
.type   aes128_keyschedule_ffs_lut,%function
.align 2
aes128_keyschedule_ffs_lut:
    push    {r1-r12,r14}
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
    //set r0 to end of rk, to be filled backwards
    add     r0, #352
    movw    r3, #0x0f0f
    movt    r3, #0x0f0f             // r3 <- 0x0f0f0f0f (mask for SWAPMOVE)
    eor     r2, r3, r3, lsl #2      // r2 <- 0x33333333 (mask for SWAPMOVE)
    eor     r1, r2, r2, lsl #1      // r1 <- 0x55555555 (mask for SWAPMOVE)
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_3
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_2
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_3
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_2
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    ldr     r12, [sp]
    ldm     r12, {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    mvn     r5, r5              // cancels the NOT applied in 'packing_rkey'
    mvn     r8, r8              // cancels the NOT applied in 'packing_rkey'
    mvn     r7, r7              // cancels the NOT applied in 'packing_rkey'
    mvn     r11, r11            // cancels the NOT applied in 'packing_rkey'
    strd    r7, r11, [r0, #24]  // restore after fix
    strd    r6, r10, [r0, #16]  // restore after fix
    strd    r5, r9, [r0, #8]    // restore after fix
    strd    r4, r8, [r0]        // restore after fix
    pop     {r1-r12, r14}       // restore context
    bx      lr

/******************************************************************************
* Pre-computes all the round keys for a given encryption key, according to the
* semi-fixsliced (sfs) representation.
* Note that the round keys also include the NOTs omitted in the S-box. 
******************************************************************************/
@ void aes128_keyschedule_sfs_lut(u32* rkeys, const u8* key);
.global aes128_keyschedule_sfs_lut
.type   aes128_keyschedule_sfs_lut,%function
.align 2
aes128_keyschedule_sfs_lut:
    push    {r1-r12,r14}
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
    //set r0 to end of rk, to be filled backwards
    add     r0, #352
    movw    r3, #0x0f0f
    movt    r3, #0x0f0f             // r3 <- 0x0f0f0f0f (mask for SWAPMOVE)
    eor     r2, r3, r3, lsl #2      // r2 <- 0x33333333 (mask for SWAPMOVE)
    eor     r1, r2, r2, lsl #1      // r1 <- 0x55555555 (mask for SWAPMOVE)
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    pop.w   {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    pop.w   {r4-r7}
    bl      inv_shiftrows_1
    bl      packing_rkey
    ldr     r12, [sp]
    ldm     r12, {r4-r7}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    bl      packing_rkey
    mvn     r5, r5              // cancels the NOT applied in 'packing_rkey'
    mvn     r8, r8              // cancels the NOT applied in 'packing_rkey'
    mvn     r7, r7              // cancels the NOT applied in 'packing_rkey'
    mvn     r11, r11            // cancels the NOT applied in 'packing_rkey'
    strd    r7, r11, [r0, #24]  // restore after fix
    strd    r6, r10, [r0, #16]  // restore after fix
    strd    r5, r9, [r0, #8]    // restore after fix
    strd    r4, r8, [r0]        // restore after fix
    pop     {r1-r12, r14}       // restore context
    bx      lr
