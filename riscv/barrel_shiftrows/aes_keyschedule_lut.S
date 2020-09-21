/******************************************************************************
* RV32I assembly implementations of the AES-128 and AES-256 key schedules
*  according to the barrel-shiftrows representation.
*
* See the paper at https://eprint.iacr.org/2020/1123.pdf for more details.
*
* @author   Alexandre Adomnicai, Nanyang Technological University, Singapore
*           alexandre.adomnicai@ntu.edu.sg
*
* @date     August 2020
******************************************************************************/

.data
/******************************************************************************
* The AES Sbox represented as a look-up-table. Used during the key schedule.
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
* The AES round constants represented as a look-up-table. Used during the key
* schedule.
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
* Routine to spread the rkey bits in the entire 32-bit word to match the barrel
* shiftrows representation.
*
* Parameters:
* - ins0-ins2 are srli or slli instruction
* - mask is a mask to extract the  right bits
******************************************************************************/
.macro spread_bits  ins0, ins1, ins2, mask
    and         s1, t3, \mask
    \ins0       s2, s1, 1
    or          s1, s1, s2
    \ins1       s2, s1, 2
    or          s1, s1, s2
    \ins2       s2, s1, 4
    or          s1, s1, s2
    and         s2, t4, \mask
    \ins0       s3, s2, 1
    or          s2, s2, s3
    \ins1       s3, s2, 2
    or          s2, s2, s3
    \ins2       s3, s2, 4
    or          s2, s2, s3
    and         s3, t5, \mask
    \ins0       s11, s3, 1
    or          s3, s3, s11
    \ins1       s11, s3, 2
    or          s3, s3, s11
    \ins2       s11, s3, 4
    or          s3, s3, s11
    and         s11, t6, \mask
    \ins0       a1, s11, 1
    or          s11, s11, a1
    \ins1       a1, s11, 2
    or          s11, s11, a1
    \ins2       a1, s11, 4
    or          s11, s11, a1
.endm

/******************************************************************************
* Applies NOT to the round keys to save some cycles during Sbox calculations.
*
* Parameters:
* - rk0-rk3 are the round key words
******************************************************************************/
.macro not_rkeys     rk0,rk1,rk2,rk3
    not     \rk0, \rk0
    not     \rk1, \rk1
    not     \rk2, \rk2
    not     \rk3, \rk3
.endm

/******************************************************************************
* Store the round keys in the corresponding array.
*
* Parameters:
* - rk0-rk3 are the round key words
* - addr is the address of the round keys array
******************************************************************************/
.macro store_rkeys      rk0,rk1,rk2,rk3, addr
    sw      \rk0, \addr
    sw      \rk1, 32+\addr
    sw      \rk2, 64+\addr
    sw      \rk3, 96+\addr
.endm

/******************************************************************************
* Subroutine to pack the round keys according to the barrel-shiftrows rep.
******************************************************************************/
redundant_code:
    store_rkeys s1, s2, s3, s11, 8(a0)      // store round key words
    spread_bits slli, slli, srli, s6        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 12(a0)     // store round key words
    spread_bits srli, srli, slli, s7        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 16(a0)     // store round key words
    spread_bits slli, srli, slli, s8        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 20(a0)     // store round key words
    spread_bits srli, slli, slli, s9        // extract and spread bits of t3-t6
    ret
    
/******************************************************************************
* Subroutine to pack the round keys according to the barrel-shiftrows rep.
******************************************************************************/
swapmove_rkey:
    swapmove    t3, t4, a2, a3, t0, 8, s1   // SWAPMOVE(a2,a3, 0x00ff00ff, 8)
    swapmove    t5, t6, a4, a5, t0, 8, s1   // SWAPMOVE(a4,a5, 0x00ff00ff, 8)
    swapmove    t3, t5, t3, t5, t1, 16, s1  // SWAPMOVE(t3,t5, 0x0000ffff, 16)
    swapmove    t4, t6, t4, t6, t1, 16, s1  // SWAPMOVE(t4,t6, 0x0000ffff, 16)
    ret

/******************************************************************************
* Round function of the AES-256 key schedule in the classical representation
* for rounds i s.t. i % 2 == 0. The key words are contained in registers a2-a5.
******************************************************************************/
aes256_rfunc_ks_0:
    andi        s8, t3, 0xff            // s8 <- t3 & 0xff
    andi        t6, s8, 0xfc            // ensure a 4-byte aligned address
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[t3 & 0xfc]
    andi        s8, s8, 0x03            // mask to extract the shift value
    slli        s8, s8, 3               // shift to compute the shift value
    srl         t6, t6, s8              // shift the 32-bit word
    andi        t6, t6, 0xff            // extract the right byte
    slli        t6, t6, 24              // t6 <- sbox[t3 & 0xff] << 24
    xor         a2, a2, t6              // a2 <- a2 ^ (sbox[t3 & 0xff] << 24)
    srli        s8, t3, 8               // s8 <- t3 >> 8
    andi        s8, s8, 0xff            // s8 <- (t3 >> 8) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[t3 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    xor         a2, a2, t6              // a2 <- a2 ^ t6
    srli        s8, t3, 24              // s8 <- t3 >> 24
    andi        s8, s8, 0xff            // s8 <- (t3 >> 24) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[t3 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 16              // t6 <- sbox[(t3 >> 24) & 0xff] << 16
    xor         a2, a2, t6              // a2 <- a2 ^ (sbox[(t3 >> 24) & 0xff] << 16)
    srl         s8, t3, 16              // s8 <- t3 >> 16
    andi        s8, s8, 0xff            // s8 <- (t3 >> 16) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[t3 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 8               // t6 <- sbox[(t3 >> 16) & 0xff] << 8
    xor         a2, a2, t6              // a2 <- a2 ^ ( sbox[(t3 >> 16) & 0xff] << 8)
    lw          t6, 0(a7)               // load rconst
    xor         a2, a2, t6              // add rconst
    addi        a7, a7, 4               // point to the next rconst
    xor         a3, a3, a2              // update the rkey words
    xor         a4, a4, a3              // update the rkey words
    xor         a5, a5, a4              // update the rkey words
    addi        sp, sp, -16             // store rkey words on stack, to be packed later
    sw          a2, 0(sp)               // store 1st rkey word
    sw          a3, 4(sp)               // store 2nd rkey word
    sw          a4, 8(sp)               // store 3rd rkey word
    sw          a5, 12(sp)              // store 4th rkey word
    ret

/******************************************************************************
* Round function of the AES-256 key schedule in the classical representation
* for rounds i s.t. i % 2 == 1. The key words are contained in registers t0-t3.
******************************************************************************/
aes256_rfunc_ks_1:
    andi        s8, a5, 0xff            // s8 <- a5 & 0xff
    andi        t6, s8, 0xfc            // ensure a 4-byte aligned address
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[a5 & 0xfc]
    andi        s8, s8, 0x03            // mask to extract the shift value
    slli        s8, s8, 3               // shift to compute the shift value
    srl         t6, t6, s8              // shift the 32-bit word
    andi        t6, t6, 0xff            // extract the right byte
    xor         t0, t0, t6              // t0 <- t0 ^ (sbox[a5 & 0xff])
    srli        s8, a5, 8               // s8 <- a5 >> 8
    andi        s8, s8, 0xff            // s8 <- (a5 >> 8) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 8
    xor         t0, t0, t6              // t0 <- t0 ^ t6
    srli        s8, a5, 24              // s8 <- a5 >> 24
    andi        s8, s8, 0xff            // s8 <- (a5 >> 24) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 24              // t6 <- sbox[(a5 >> 24) & 0xff] << 24
    xor         t0, t0, t6              // t0 <- t0 ^ (sbox[(a5 >> 24) & 0xff] << 24)
    srl         s8, a5, 16              // s8 <- a5 >> 16
    andi        s8, s8, 0xff            // s8 <- (a5 >> 16) & 0xff
    andi        t6, s8, 0xfc                
    add         t6, t6, a6              // t6 points to the right sbox address
    lw          t6, 0(t6)               // t6 <- sbox[a5 & 0xff]
    andi        s8, s8, 0x03
    slli        s8, s8, 3
    srl         t6, t6, s8
    andi        t6, t6, 0xff
    slli        t6, t6, 16              // t6 <- sbox[(a5 >> 16) & 0xff] << 16
    xor         t0, t0, t6              // t0 <- t0 ^ ( sbox[(a5 >> 16) & 0xff] << 16)
    xor         t1, t1, t0              // update the rkey words
    xor         t2, t2, t1              // update the rkey words
    xor         t3, t3, t2              // update the rkey words
    addi        sp, sp, -16             // store rkey words on stack, to be packed later
    sw          t0, 0(sp)               // store 5th rkey word
    sw          t1, 4(sp)               // store 6th rkey word
    sw          t2, 8(sp)               // store 7th rkey word
    sw          t3, 12(sp)              // store 8th rkey word
    ret


/******************************************************************************
* AES-128 key schedule according to the barrel-shiftrows representation. 
*
* The function prototype is:
*   - void aes128_keyschedule_lut(uint32_t rkeys[352], const uint8_t key[16]);
******************************************************************************/
.globl aes128_keyschedule_lut
.type aes128_keyschedule_lut, %function
.align 2
aes128_keyschedule_lut:
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
    sw          s9, 44(sp)                  // save context
    sw          s10, 48(sp)                 // save context
    sw          s11, 52(sp)                 // save context
    sw          ra, 56(sp)                  // save context
    lw          a2, 0(a1)                   // load 1st key word
    lw          a3, 4(a1)                   // load 2nd key word
    lw          a4, 8(a1)                   // load 3rd key word
    lw          a5, 12(a1)                  // load 4th key word
    addi        s0, zero, 10                // set key_expansion loop counter
    la          a6, sbox_lut                // load sbox address
    la          a7, rconst_lut              // load rconst address
    li          t0, 0x00ff00ff              // load mask for SWAPMOVE routines
    li          t1, 0x0000ffff              // load mask for SWAPMOVE routines
    li          t2, 0x80808080              // mask for packing_rkey_loop
    srli        s4, t2, 1                   // mask for packing_rkey_loop
    srli        s5, t2, 2                   // mask for packing_rkey_loop
    srli        s6, t2, 3                   // mask for packing_rkey_loop
    srli        s7, t2, 4                   // mask for packing_rkey_loop
    srli        s8, t2, 5                   // mask for packing_rkey_loop
    srli        s9, t2, 6                   // mask for packing_rkey_loop
    srli        s10, t2, 7                  // mask for packing_rkey_loop
    jal         swapmove_rkey
    spread_bits srli, srli, srli, t2        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 0(a0)      // store round key words
    spread_bits slli, srli, srli, s4        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 4(a0)      // store round key words
    spread_bits srli, slli, srli, s5        // extract and spread bits of t3-t6
    jal         redundant_code
    store_rkeys s1, s2, s3, s11, 24(a0)     // store round key words
    spread_bits slli, slli, slli, s10       // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 28(a0)     // store round key words
    addi        a0, a0, 128                 // points to the next rkey
key_expansion:                              // key expansion routine
    addi        s0, s0, -1                  // dec key_expansion loop counter
    andi        t3, a5, 0xff                // t3 <- a5 & 0xff
    andi        t4, t3, 0xfc                // ensure a 4-byte aligned address
    add         t4, t4, a6                  // t4 points to the right sbox address
    lw          t4, 0(t4)                   // t4 <- sbox[a5 & 0xfc]
    andi        t3, t3, 0x03                // mask to extract the shift value
    slli        t3, t3, 3                   // shift to compute the shift value
    srl         t4, t4, t3                  // shift the 32-bit word
    andi        t4, t4, 0xff                // extract the right byte
    slli        t4, t4, 24                  // t4 <- sbox[a5 & 0xff] << 24
    xor         a2, a2, t4                  // a2 <- a2 ^ (sbox[a5 & 0xff] << 24)
    srli        t3, a5, 8                   // t3 <- a5 >> 8
    andi        t3, t3, 0xff                // t3 <- (a5 >> 8) & 0xff
    andi        t4, t3, 0xfc                // ensure a 4-byte aligned address
    add         t4, t4, a6                  // t4 points to the right sbox address
    lw          t4, 0(t4)                   // t4 <- sbox[(a5 >> 8) & 0xff]
    andi        t3, t3, 0x03                // mask to extract the shift value
    slli        t3, t3, 3                   // shift to compute the shift value
    srl         t4, t4, t3                  // shift the 32-bit word
    andi        t4, t4, 0xff                // extract the right byte
    xor         a2, a2, t4                  // a2 <- a2 ^ t4
    srli        t3, a5, 24                  // t3 <- a5 >> 24
    andi        t3, t3, 0xff                // t3 <- (a5 >> 24) & 0xff
    andi        t4, t3, 0xfc                // ensure a 4-byte aligned address
    add         t4, t4, a6                  // t4 points to the right sbox address
    lw          t4, 0(t4)                   // t4 <- sbox[(a5 >> 24) & 0xff]
    andi        t3, t3, 0x03                // mask to extract the shift value
    slli        t3, t3, 3                   // shift to compute the shift value
    srl         t4, t4, t3                  // shift the 32-bit word
    andi        t4, t4, 0xff                // extract the right byte
    slli        t4, t4, 16                  // t4 <- sbox[(a5 >> 24) & 0xff] << 16
    xor         a2, a2, t4                  // a2 <- a2 ^ (sbox[(a5 >> 24) & 0xff] << 16)
    srli        t3, a5, 16                  // t3 <- a5 >> 16
    andi        t3, t3, 0xff                // t3 <- (a5 >> 16) & 0xff
    andi        t4, t3, 0xfc                // ensure a 4-byte aligned address
    add         t4, t4, a6                  // t4 points to the right sbox address
    lw          t4, 0(t4)                   // t4 <- sbox[(a5 >> 16) & 0xff]
    andi        t3, t3, 0x03                // mask to extract the shift value
    slli        t3, t3, 3                   // shift to compute the shift value
    srl         t4, t4, t3                  // shift the 32-bit word
    andi        t4, t4, 0xff                // extract the right byte
    slli        t4, t4, 8                   // t4 <- sbox[(a5 >> 16) & 0xff] << 8
    xor         a2, a2, t4                  // a2 <- a2 ^ ( sbox[(a5 >> 16) & 0xff] << 8)
    lw          t4, 0(a7)                   // load rconst
    xor         a2, a2, t4                  // add rconst
    addi        a7, a7, 4                   // point to the next rconst
    xor         a3, a3, a2                  // update the rkey words
    xor         a4, a4, a3                  // update the rkey words
    xor         a5, a5, a4                  // update the rkey words
    jal         swapmove_rkey
    spread_bits srli, srli, srli, t2        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 0(a0)      // store round key words
    spread_bits slli, srli, srli, s4        // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 4(a0)      // store round key words
    spread_bits srli, slli, srli, s5        // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    jal         redundant_code
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 24(a0)     // store round key words
    spread_bits slli, slli, slli, s10       // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 28(a0)     // store round key words
    addi        a0, a0, 128                 // points to the next rkey
    bne         s0, zero, key_expansion     // loop until necessary
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
    lw          s10, 48(sp)                 // restore context
    lw          s11, 52(sp)                 // restore context
    lw          ra, 56(sp)
    addi        sp, sp, 64                  // restore stack pointer
    ret                                     // exit
.size aes128_keyschedule_lut,.-aes128_keyschedule_lut

/******************************************************************************
* AES-256 key schedule according to the barrel-shiftrows representation. 
*
* The function prototype is:
*   - void aes256_keyschedule_lut(uint32_t rkeys[480], const uint8_t key[32]);
******************************************************************************/
.globl aes256_keyschedule_lut
.type aes256_keyschedule_lut, %function
.align 2
aes256_keyschedule_lut:
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
    sw          s9, 44(sp)                  // save context
    sw          s10, 48(sp)                 // save context
    sw          s11, 52(sp)                 // save context
    sw          ra, 56(sp)                  // save context
    lw          a2, 0(a1)                   // load 1st key word
    lw          a3, 4(a1)                   // load 2nd key word
    lw          a4, 8(a1)                   // load 3rd key word
    lw          a5, 12(a1)                  // load 4th key word
    lw          t0, 16(a1)                  // load 5th key word
    lw          t1, 20(a1)                  // load 6th key word
    lw          t2, 24(a1)                  // load 7th key word
    lw          t3, 28(a1)                  // load 8th key word
    la          a6, sbox_lut                // load sbox address
    la          a7, rconst_lut              // load rconst address
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    jal         aes256_rfunc_ks_1
    jal         aes256_rfunc_ks_0
    // Now pack all round key to match the semi-fixsliced representation
    li          t0, 0x00ff00ff              // load mask for SWAPMOVE routines
    li          t1, 0x0000ffff              // load mask for SWAPMOVE routines
    li          t2, 0x80808080              // mask for packing_rkey_loop
    srli        s4, t2, 1                   // mask for packing_rkey_loop
    srli        s5, t2, 2                   // mask for packing_rkey_loop
    srli        s6, t2, 3                   // mask for packing_rkey_loop
    srli        s7, t2, 4                   // mask for packing_rkey_loop
    srli        s8, t2, 5                   // mask for packing_rkey_loop
    srli        s9, t2, 6                   // mask for packing_rkey_loop
    srli        s10, t2, 7                  // mask for packing_rkey_loop
    lw          a2, 0(a1)                   // load 1st key word
    lw          a3, 4(a1)                   // load 2nd key word
    lw          a4, 8(a1)                   // load 3rd key word
    lw          a5, 12(a1)                  // load 4th key word
    jal         swapmove_rkey
    spread_bits srli, srli, srli, t2        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 0(a0)      // store round key words
    spread_bits slli, srli, srli, s4        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 4(a0)      // store round key words
    spread_bits srli, slli, srli, s5        // extract and spread bits of t3-t6
    jal         redundant_code
    store_rkeys s1, s2, s3, s11, 24(a0)     // store round key words
    spread_bits slli, slli, slli, s10       // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 28(a0)     // store round key words
    addi        a0, a0, 128                 // points to the next rkey
    lw          a1, 212(sp)                 // restore key address
    lw          a2, 16(a1)                  // load 5th key word
    lw          a3, 20(a1)                  // load 6th key word
    lw          a4, 24(a1)                  // load 7th key word
    lw          a5, 28(a1)                  // load 8th key word
    addi        s0, zero, 14
    addi        sp, sp, 192                 // points to the 1st rkey to pack
aes256_packing_rkeys:
    addi        s0, s0, -1                  // dec loop counter
    jal         swapmove_rkey
    spread_bits srli, srli, srli, t2        // extract and spread bits of t3-t6
    store_rkeys s1, s2, s3, s11, 0(a0)      // store round key words
    spread_bits slli, srli, srli, s4        // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 4(a0)      // store round key words
    spread_bits srli, slli, srli, s5        // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    jal         redundant_code
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 24(a0)     // store round key words
    spread_bits slli, slli, slli, s10       // extract and spread bits of t3-t6
    not_rkeys   s1, s2, s3, s11             // apply NOTs to speedup the sbox
    store_rkeys s1, s2, s3, s11, 28(a0)     // store round key words
    lw          a2, 0(sp)                   // load next rkey words from the stack
    lw          a3, 4(sp)                   // load next rkey words from the stack
    lw          a4, 8(sp)                   // load next rkey words from the stack
    lw          a5, 12(sp)                  // load next rkey words from the stack
    addi        sp, sp, -16                 // points to the next rkey
    addi        a0, a0, 128                 // points to the next rkey
    bne         s0,zero,aes256_packing_rkeys// loop until necessary

    addi        sp, sp, 304                 // restore stack pointer
    lw          a0, -64(sp)                 // restore context
    lw          a1, -60(sp)                 // restore context
    lw          s0, -56(sp)                 // restore context
    lw          s1, -52(sp)                 // restore context
    lw          s2, -48(sp)                 // restore context
    lw          s3, -44(sp)                 // restore context
    lw          s4, -40(sp)                 // restore context
    lw          s5, -36(sp)                 // restore context
    lw          s6, -32(sp)                 // restore context
    lw          s7, -28(sp)                 // restore context
    lw          s8, -24(sp)                 // restore context
    lw          s9, -20(sp)                 // restore context
    lw          s10, -16(sp)                // restore context
    lw          s11, -12(sp)                // restore context
    lw          ra, -8(sp)
    ret                                     // exit
.size aes256_keyschedule_lut,.-aes256_keyschedule_lut