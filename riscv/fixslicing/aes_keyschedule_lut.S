/******************************************************************************
* RV32I assembly implememtations of the AES-128 key schedule according to
* fixslicing.
*
* Note that this implementation relies on Look-Up Tables (LUT) and therefore
* might not run in constant-time on some platforms. See the 'aes_keyschedule.S'
* file for fully bitsliced implementation of the key schedule.
*
* For more details about the implementations see https:// 
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     July 2020
******************************************************************************/

.data
/******************************************************************************
* The AES Sbox represented as a look-up-table.
******************************************************************************/
.align 2
sbox_lut:
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
* The AES round constants represented as a look-up-table.
******************************************************************************/
.align 2
rconst_lut:
    .word   0x00000001, 0x00000002, 0x00000004, 0x00000008
    .word   0x00000010, 0x00000020, 0x00000040, 0x00000080
    .word   0x0000001b, 0x00000036

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
* Applies NOT to the round keys to save some cycles during Sbox calculations.
******************************************************************************/
.macro not_rkey
    not     s1, s1
    not     s2, s2
    not     s6, s6
    not     s7, s7
.endm

/******************************************************************************
* Store the round keys in the corresponding array.
******************************************************************************/
.macro store_rkey
    sw      s0, 0(a0)
    sw      s1, 4(a0)
    sw      s2, 8(a0)
    sw      s3, 12(a0)
    sw      s4, 16(a0)
    sw      s5, 20(a0)
    sw      s6, 24(a0)
    sw      s7, 28(a0)
    addi    a0, a0, 32                      // points to the next rkey
.endm

/******************************************************************************
* Applies NOT to the round keys to save some cycles during Sbox calculations.
******************************************************************************/
store_not_rkey:
    not     s1, s1
    not     s2, s2
    not     s6, s6
    not     s7, s7
    sw      s0, 0(a0)
    sw      s1, 4(a0)
    sw      s2, 8(a0)
    sw      s3, 12(a0)
    sw      s4, 16(a0)
    sw      s5, 20(a0)
    sw      s6, 24(a0)
    sw      s7, 28(a0)
    addi    a0, a0, 32                      // points to the next rkey
    ret

/******************************************************************************
* Compute ShiftRows^(-1) on the entire round key in order to match fixslicing.
******************************************************************************/
inv_shiftrows_1:
    andi    s1, a2, 0xff                    // s1 <- rkey[i] & 0x000000ff
    and     t6, a5, t3                      // t6 <- rkeys[i+3] & 0x0000ff00
    or      s1, s1, t6                      // s1 <- s1 | t6
    and     t6, a4, t4                      // t6 <- rkeys[i+2] & 0x00ff0000
    or      s1, s1, t6                      // s1 <- s1 | t6
    and     t6, a3, t5                      // t6 <- rkeys[i+1] & 0xff000000
    or      s1, s1, t6                      // s1 <- s1 | t6
    andi    s3, a3, 0xff                    // s3 <- rkeys[i+1] & 0x000000ff
    and     t6, a2, t3                      // t6 <- rkeys[i] & 0x0000ff00
    or      s3, s3, t6                      // s3 <- s3 | t6
    and     t6, a5, t4                      // t6 <- rkeys[i+3] & 0x00ff0000
    or      s3, s3, t6                      // s3 <- s3 | t6
    and     t6, a4, t5                      // t6 <- rkeys[i+2] & 0xff000000
    or      s3, s3, t6                      // s3 <- s3 | t6
    andi    s5, a4, 0xff                    // s5 <- rkeys[i+2] & 0x000000ff
    and     t6, a3, t3                      // t6 <- rkeys[i+1] & 0x0000ff00
    or      s5, s5, t6                      // s5 <- s5 | t6
    and     t6, a2, t4                      // t6 <- rkeys[i] & 0x00ff0000
    or      s5, s5, t6                      // s5 <- s5 | t6
    and     t6, a5, t5                      // t6 <- rkeys[i+3] & 0xff000000
    or      s5, s5, t6                      // s5 <- s5 | t6
    andi    s7, a5, 0xff                    // s7 <- rkeys[i+3] & 0x000000ff
    and     t6, a4, t3                      // t6 <- rkeys[i+2] & 0x0000ff00
    or      s7, s7, t6                      // s7 <- s7 | t6
    and     t6, a3, t4                      // t6 <- rkeys[i+1] & 0x00ff0000
    or      s7, s7, t6                      // s7 <- s7 | t6
    and     t6, a2, t5                      // t6 <- rkeys[i] & 0xff000000
    or      s7, s7, t6                      // s7 <- s7 | t6
    ret

/******************************************************************************
* Compute ShiftRows^(-2) on the entire round key in order to match fixslicing.
******************************************************************************/
inv_shiftrows_2:
    and     s1, a2, s10                     // s1 <- rkey[i] & 0x00ff00ff
    and     t6, a4, s11                     // t6 <- rkey[i+2] & 0xff00ff00
    or      s1, s1, t6                      // s1 <- s1 | t6
    and     s3, a3, s10                     // s3 <- rkey[i+1] & 0x00ff00ff
    and     t6, a5, s11                     // t6 <- rkey[i+3] & 0xff00ff00
    or      s3, s3, t6                      // s3 <- s3 | t6
    and     s5, a4, s10                     // s5 <- rkey[i+2] & 0x00ff00ff
    and     t6, a2, s11                     // t6 <- rkey[i] & 0xff00ff00
    or      s5, s5, t6                      // s5 <- s5 | t6
    and     s7, a5, s10                     // s7 <- rkey[i+3] & 0x00ff00ff
    and     t6, a3, s11                     // t6 <- rkey[i+1] & 0xff00ff00
    or      s7, s7, t6                      // s7 <- s7 | t6
    ret

/******************************************************************************
* Compute ShiftRows^(-3) on the entire round key in order to match fixslicing.
******************************************************************************/
inv_shiftrows_3:
    andi    s1, a2, 0xff                    // s1 <- rkey[i] & 0x000000ff
    and     t6, a3, t3                      // t6 <- rkeys[i+1] & 0x0000ff00
    or      s1, s1, t6                      // s1 <- s1 | t6
    and     t6, a4, t4                      // t6 <- rkeys[i+2] & 0x00ff0000
    or      s1, s1, t6                      // s1 <- s1 | t6
    and     t6, a5, t5                      // t6 <- rkeys[i+3] & 0xff000000
    or      s1, s1, t6                      // s1 <- s1 | t6
    andi    s3, a3, 0xff                    // s3 <- rkeys[i+1] & 0x000000ff
    and     t6, a4, t3                      // t6 <- rkeys[i+2] & 0x0000ff00
    or      s3, s3, t6                      // s3 <- s3 | t6
    and     t6, a5, t4                      // t6 <- rkeys[i+3] & 0x00ff0000
    or      s3, s3, t6                      // s3 <- s3 | t6
    and     t6, a2, t5                      // t6 <- rkeys[i] & 0xff000000
    or      s3, s3, t6                      // s3 <- s3 | t6
    andi    s5, a4, 0xff                    // s5 <- rkeys[i+2] & 0x000000ff
    and     t6, a5, t3                      // t6 <- rkeys[i+3] & 0x0000ff00
    or      s5, s5, t6                      // s5 <- s5 | t6
    and     t6, a2, t4                      // t6 <- rkeys[i] & 0x00ff0000
    or      s5, s5, t6                      // s5 <- s5 | t6
    and     t6, a3, t5                      // t6 <- rkeys[i+1] & 0xff000000
    or      s5, s5, t6                      // s5 <- s5 | t6
    andi    s7, a5, 0xff                    // s7 <- rkeys[i+3] & 0x000000ff
    and     t6, a2, t3                      // t6 <- rkeys[i] & 0x0000ff00
    or      s7, s7, t6                      // s7 <- s7 | t6
    and     t6, a3, t4                      // t6 <- rkeys[i+1] & 0x00ff0000
    or      s7, s7, t6                      // s7 <- s7 | t6
    and     t6, a4, t5                      // t6 <- rkeys[i+2] & 0xff000000
    or      s7, s7, t6                      // s7 <- s7 | t6
    ret

/******************************************************************************
* Execute a round of the AES-128 key schedule in the classical representation.
******************************************************************************/
key_expansion:
    andi        s8, a5, 0xff                // s8 <- a5 & 0xff
    andi        t6, s8, 0xfc                // ensure a 4-byte aligned address
    add         t6, t6, a6                  // t6 points to the right sbox address
    lw          t6, 0(t6)                   // t6 <- sbox[a5 & 0xfc]
    andi        s8, s8, 0x03                // mask to extract the shift value
    slli        s8, s8, 3                   // shift to compute the shift value
    srl         t6, t6, s8                  // shift the 32-bit word
    andi        t6, t6, 0xff                // extract the right byte
    slli        t6, t6, 24                  // t6 <- sbox[a5 & 0xff] << 24
    xor         a2, a2, t6                  // a2 <- a2 ^ (sbox[a5 & 0xff] << 24)
    srli        s8, a5, 8                   // s8 <- a5 >> 8
    andi        s8, s8, 0xff                // s8 <- (a5 >> 8) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6                  // t6 points to the right sbox address
    lw          t6, 0(t6)                   // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    xor         a2, a2, t6                  // a2 <- a2 ^ t6
    srli        s8, a5, 24                  // s8 <- a5 >> 24
    andi        s8, s8, 0xff                // s8 <- (a5 >> 24) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6                  // t6 points to the right sbox address
    lw          t6, 0(t6)                   // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 16                  // t6 <- sbox[(a5 >> 24) & 0xff] << 16
    xor         a2, a2, t6                  // a2 <- a2 ^ (sbox[(a5 >> 24) & 0xff] << 16)
    srl         s8, a5, 16                  // s8 <- a5 >> 16
    andi        s8, s8, 0xff                // s8 <- (a5 >> 16) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6                  // t6 points to the right sbox address
    lw          t6, 0(t6)                   // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 8                   // t6 <- sbox[(a5 >> 16) & 0xff] << 8
    xor         a2, a2, t6                  // a2 <- a2 ^ ( sbox[(a5 >> 16) & 0xff] << 8)
    lw          t6, 0(a7)                   // load rconst
    xor         a2, a2, t6                  // add rconst
    addi        a7, a7, 4                   // point to the next rconst
    xor         a3, a3, a2                  // update the rkey words
    xor         a4, a4, a3                  // update the rkey words
    xor         a5, a5, a4                  // update the rkey words
    ret

/******************************************************************************
* Subroutine to pack the round keys in order to match fixslicing.
******************************************************************************/
subpacking_rkey:
    swapmove    s2,s0, s2, s0, t1, 2, t6    // SWAPMOVE(s2,s0, 0x33333333, 2)
    swapmove    s3,s1, s3, s1, t1, 2, t6    // SWAPMOVE(s3,s1, 0x33333333, 2)
    swapmove    s6,s4, s6, s4, t1, 2, t6    // SWAPMOVE(s6,s4, 0x33333333, 2)
    swapmove    s7,s5, s7, s5, t1, 2, t6    // SWAPMOVE(s7,s5, 0x33333333, 2)
    swapmove    s4,s0, s4, s0, t2, 4, t6    // SWAPMOVE(s4,s0, 0x0f0f0f0f, 4)
    swapmove    s5,s1, s5, s1, t2, 4, t6    // SWAPMOVE(s5,s1, 0x0f0f0f0f, 4)
    swapmove    s6,s2, s6, s2, t2, 4, t6    // SWAPMOVE(s6,s2, 0x0f0f0f0f, 4)
    swapmove    s7,s3, s7, s3, t2, 4, t6    // SWAPMOVE(s7,s3, 0x0f0f0f0f, 4)
    ret

/******************************************************************************
* Subroutine to pack the round keys in order to match fixslicing.
******************************************************************************/
.macro packing_rkey rk0, rk1, rk2, rk3
    swapmove    s1,s0, \rk0,\rk0, t0, 1, t6 // SWAPMOVE(a2,a2, 0x55555555, 1)
    swapmove    s3,s2, \rk1,\rk1, t0, 1, t6 // SWAPMOVE(a3,a3, 0x55555555, 1)
    swapmove    s5,s4, \rk2,\rk2, t0, 1, t6 // SWAPMOVE(a4,a4, 0x55555555, 1)
    swapmove    s7,s6, \rk3,\rk3, t0, 1, t6 // SWAPMOVE(a5,a5, 0x55555555, 1)
    jal         subpacking_rkey
 .endm

/******************************************************************************
* Expansion of the encryption key according to the fully-fixsliced representa-
* tion. 
*
* The function prototype is:
*   - void aes128_keyschedule_ffs_lut(uint32_t* rkeys, const uint8_t key);
******************************************************************************/
.globl aes128_keyschedule_ffs_lut
.type aes128_keyschedule_ffs_lut, %function
.align 2
aes128_keyschedule_ffs_lut:
    addi        sp, sp, -64                 // allocate space on the stack
    sw          a0, 0(sp)                   // save context
    sw          a1, 4(sp)                   // save context
    sw          s0, 8(sp)                   // save context
    sw          s1, 12(sp)                  // save context
    sw          s2, 16(sp)                  // save context
    sw          s3, 20(sp)                  // save context
    sw          s4, 24(sp)                  // save context
    sw          s5, 28(sp)                  // save context
    sw          s6, 32(sp)                  // save context
    sw          s7, 36(sp)                  // save context
    sw          s8, 40(sp)                  // save context
    sw          ra, 44(sp)                  // save context
    sw          s10, 48(sp)                 // save context
    sw          s11, 52(sp)                 // save context
    sw          s9, 56(sp)                  // save context
    addi        s9, zero, 2                 // init loop counter
    lw          a2, 0(a1)                   // load 1st key word
    lw          a3, 4(a1)                   // load 2nd key word
    lw          a4, 8(a1)                   // load 3rd key word
    lw          a5, 12(a1)                  // load 4th key word
    la          a6, sbox_lut                // load sbox address
    la          a7, rconst_lut              // load rconst address
    li          t0, 0x55555555              // mask for SWAPMOVE routines
    li          t1, 0x33333333              // mask for SWAPMOVE routines
    li          t2, 0x0f0f0f0f              // mask for packing_rkey_loop
    li          t3, 0x0000ff00              // mask for inv_shiftrows_1/3
    slli        t4, t3, 8                   // mask for inv_shiftrows_1/3
    slli        t5, t3, 16                  // mask for inv_shiftrows_1/3
    li          s10, 0x00ff00ff             // mask for inv_shiftrows_2
    slli        s11, s10, 8                 // mask for inv_shiftrows_2
    packing_rkey a2, a3, a4, a5
    store_rkey
key_exp_loop_ffs:
    addi            s9, s9, -1              // decrement loop counter
    jal             key_expansion
    jal             inv_shiftrows_1         // inv_shiftrows to match semi-fixslicing
    packing_rkey    s1, s3, s5, s7
    jal             store_not_rkey
    jal             key_expansion
    jal             inv_shiftrows_2         // inv_shiftrows to match semi-fixslicing
    packing_rkey    s1, s3, s5, s7
    jal             store_not_rkey
    jal             key_expansion
    jal             inv_shiftrows_3         // inv_shiftrows to match semi-fixslicing
    packing_rkey    s1, s3, s5, s7
    jal             store_not_rkey
    jal             key_expansion
    packing_rkey    a2, a3, a4, a5
    jal             store_not_rkey
    bne             s9, zero, key_exp_loop_ffs
    jal             key_expansion
    jal             inv_shiftrows_1         // inv_shiftrows to match semi-fixslicing
    packing_rkey    s1, s3, s5, s7
    jal             store_not_rkey
    jal             key_expansion
    packing_rkey    a2, a3, a4, a5
    jal             store_not_rkey
    lw          a0, 0(sp)                   // restore context
    lw          a1, 4(sp)                   // restore context
    lw          s0, 8(sp)                   // restore context
    lw          s1, 12(sp)                  // restore context
    lw          s2, 16(sp)                  // restore context
    lw          s3, 20(sp)                  // restore context
    lw          s4, 24(sp)                  // restore context
    lw          s5, 28(sp)                  // restore context
    lw          s6, 32(sp)                  // restore context
    lw          s7, 36(sp)                  // restore context
    lw          s8, 40(sp)                  // restore context
    lw          ra, 44(sp)                  // restore context
    lw          s10, 48(sp)                 // restore context
    lw          s11, 52(sp)                 // restore context
    lw          s9, 56(sp)                  // restore context
    addi        sp, sp, 64                  // restore stack pointer
    ret                                     // exit
.size aes128_keyschedule_ffs_lut,.-aes128_keyschedule_ffs_lut

/******************************************************************************
* Expansion of the encryption key according to the semi-fixsliced representa-
* tion. 
*
* The function prototype is:
*   - void aes128_keyschedule_sfs_lut(uint32_t* rkeys, const uint8_t key);
******************************************************************************/
.globl aes128_keyschedule_sfs_lut
.type aes128_keyschedule_sfs_lut, %function
.align 2
aes128_keyschedule_sfs_lut:
    addi        sp, sp, -56                 // allocate space on the stack
    sw          a0, 0(sp)                   // save context
    sw          a1, 4(sp)                   // save context
    sw          s0, 8(sp)                   // save context
    sw          s1, 12(sp)                  // save context
    sw          s2, 16(sp)                  // save context
    sw          s3, 20(sp)                  // save context
    sw          s4, 24(sp)                  // save context
    sw          s5, 28(sp)                  // save context
    sw          s6, 32(sp)                  // save context
    sw          s7, 36(sp)                  // save context
    sw          s8, 40(sp)                  // save context
    sw          s9, 44(sp)                  // save context
    sw          ra, 48(sp)                  // save context
    addi        s9, zero, 5                 // set key_expansion_loop counter
    lw          a2, 0(a1)                   // load 1st key word
    lw          a3, 4(a1)                   // load 2nd key word
    lw          a4, 8(a1)                   // load 3rd key word
    lw          a5, 12(a1)                  // load 4th key word
    la          a6, sbox_lut                // load sbox address
    la          a7, rconst_lut              // load rconst address
    li          t0, 0x55555555              // mask for SWAPMOVE routines
    li          t1, 0x33333333              // mask for SWAPMOVE routines
    li          t2, 0x0f0f0f0f              // mask for packing_rkey_loop
    li          t3, 0x0000ff00              // mask for inv_shiftrows_1
    slli        t4, t3, 8                   // mask for inv_shiftrows_1
    slli        t5, t3, 16                  // mask for inv_shiftrows_1
    packing_rkey a2, a3, a4, a5
    store_rkey
key_exp_loop_sfs:
    addi            s9, s9, -1              // decrement loop counter
    jal             key_expansion
    jal             inv_shiftrows_1         // inv_shiftrows to match semi-fixslicing
    packing_rkey    s1, s3, s5, s7
    jal             store_not_rkey
    jal             key_expansion
    packing_rkey    a2, a3, a4, a5
    jal             store_not_rkey
    bne             s9, zero, key_exp_loop_sfs
    lw          a0, 0(sp)                   // restore context
    lw          a1, 4(sp)                   // restore context
    lw          s0, 8(sp)                   // restore context
    lw          s1, 12(sp)                  // restore context
    lw          s2, 16(sp)                  // restore context
    lw          s3, 20(sp)                  // restore context
    lw          s4, 24(sp)                  // restore context
    lw          s5, 28(sp)                  // restore context
    lw          s6, 32(sp)                  // restore context
    lw          s7, 36(sp)                  // restore context
    lw          s8, 40(sp)                  // restore context
    lw          s9, 44(sp)                  // restore context
    lw          ra, 48(sp)                  // restore context
    addi        sp, sp, 56                  // restore stack pointer
    ret                                     // exit
.size aes128_keyschedule_sfs_lut,.-aes128_keyschedule_sfs_lut
