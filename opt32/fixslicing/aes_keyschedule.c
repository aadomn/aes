/******************************************************************************
* C language implementations of the AES-128 key schedule to match the fixsliced
* representation. Note that those implementations are fully bitsliced and do
* not rely on any Look-Up Table (LUT).
*
* See the paper "Fixslicing AES-like Ciphers" at https:// for more details.
*
* @author 	Alexandre Adomnicai, Nanyang Technological University, Singapore
*			alexandre.adomnicai@ntu.edu.sg
*
* @date		July 2020
******************************************************************************/
#include <string.h>
#include "aes.h"
#include "internal-aes.h"

/******************************************************************************
* Applies ShiftRows^(-1) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_1(uint32_t* rkey) {
	uint32_t t;
	for(int i = 0; i < 8; i++) {
		t = (rkey[i] >> 2) & 0x00003f00;
		t |= (rkey[i] & 0x00000300) << 6;
		t |= (rkey[i] >> 4) & 0x000f0000;
		t |= (rkey[i] & 0x000f0000) << 4;
		t |= (rkey[i] >> 6) & 0x03000000;
		t |= (rkey[i] & 0x3f000000) << 2;
		rkey[i] &= 0x000000ff;
		rkey[i] |= t;
	}
}

/******************************************************************************
* Applies ShiftRows^(-2) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_2(uint32_t* rkey) {
	uint32_t t;
	for(int i = 0; i < 8; i++) {
		t = (rkey[i] >> 4) & 0x0f000f00;
		t |= ((rkey[i] << 4) & 0xf000f000);
		rkey[i] = t | (rkey[i] & 0x00ff00ff);
	}
}

/******************************************************************************
* Applies ShiftRows^(-3) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_3(uint32_t* rkey) {
	uint32_t t;
	for(int i = 0; i < 8; i++) {
		t = (rkey[i] >> 6) & 0x00000300;
		t |= (rkey[i] & 0x00003f00) << 2;
		t |= (rkey[i] >> 4) & 0x000f0000;
		t |= (rkey[i] & 0x000f0000) << 4;
		t |= (rkey[i] >> 2) & 0x3f000000;
		t |= (rkey[i] & 0x03000000) << 6;
		rkey[i] = t | (rkey[i] & 0x000000ff);
	}
}

/******************************************************************************
* XOR the columns after the S-box during the key schedule round function.
* Note that the NOT omitted in the S-box are applied here.
******************************************************************************/
static void xor_columns(uint32_t* rkeys) {
	rkeys[1] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[2] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[6] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[7] ^= 0xffffffff; 			// NOT that are omitted in S-box
	for(int i = 0; i < 8; i++) {
		rkeys[i] = (rkeys[i-8] ^ ROR(rkeys[i],2))  & 0xc0c0c0c0;
		rkeys[i] |= ((rkeys[i-8] ^ rkeys[i] >> 2) & 0x30303030);
		rkeys[i] |= ((rkeys[i-8] ^ rkeys[i] >> 2) & 0x0c0c0c0c);
		rkeys[i] |= ((rkeys[i-8] ^ rkeys[i] >> 2) & 0x03030303);
	}
}

void aes128_keyschedule_ffs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 	// packs the keys into the bitsliced state
	memcpy(rkeys+8, rkeys, 32);
	sbox(rkeys+8);
	rkeys[15] ^= 0x00000300; 		// 1st rconst
	xor_columns(rkeys+8);
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[22] ^= 0x00000300;		// 2nd rconst
	xor_columns(rkeys+16);
	inv_shiftrows_1(rkeys+8);
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	rkeys[29] ^= 0x00000300;		// 3rd rconst
	xor_columns(rkeys+24);
	inv_shiftrows_2(rkeys+16);
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[36] ^= 0x00000300; 		// 4th rconst
	xor_columns(rkeys+32);
	inv_shiftrows_3(rkeys+24);
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	rkeys[43] ^= 0x00000300; 		// 5th rconst
	xor_columns(rkeys+40);
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[50] ^= 0x00000300;		// 6th rconst
	xor_columns(rkeys+48);
	inv_shiftrows_1(rkeys+40);
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	rkeys[57] ^= 0x00000300;		// 7th rconst
	xor_columns(rkeys+56);
	inv_shiftrows_2(rkeys+48);
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[64] ^= 0x00000300;		// 8th rconst
	xor_columns(rkeys+64);
	inv_shiftrows_3(rkeys+56);
	memcpy(rkeys+72, rkeys+64, 32);
	sbox(rkeys+72);
	rkeys[79] ^= 0x00000300; 		// 9th rconst
	rkeys[78] ^= 0x00000300; 		// 9th rconst
	rkeys[76] ^= 0x00000300; 		// 9th rconst
	rkeys[75] ^= 0x00000300; 		// 9th rconst
	xor_columns(rkeys + 72);
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[86] ^= 0x00000300; 		// 10th rconst
	rkeys[85] ^= 0x00000300; 		// 10th rconst
	rkeys[83] ^= 0x00000300;		// 10th rconst
	rkeys[82] ^= 0x00000300; 		// 10th rconst
	xor_columns(rkeys+80);
	inv_shiftrows_1(rkeys+72);
	for(int i = 1; i < 11; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}

void aes128_keyschedule_sfs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 	// packs the keys into the bitsliced state
	memcpy(rkeys+8, rkeys, 32);
	sbox(rkeys+8);
	rkeys[15] ^= 0x00000300; 		// 1st rconst
	xor_columns(rkeys+8);
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[22] ^= 0x00000300;		// 2nd rconst
	xor_columns(rkeys+16);
	inv_shiftrows_1(rkeys+8);
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	rkeys[29] ^= 0x00000300;		// 3rd rconst
	xor_columns(rkeys+24);
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[36] ^= 0x00000300; 		// 4th rconst
	xor_columns(rkeys+32);
	inv_shiftrows_1(rkeys+24);
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	rkeys[43] ^= 0x00000300; 		// 5th rconst
	xor_columns(rkeys+40);
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[50] ^= 0x00000300;		// 6th rconst
	xor_columns(rkeys+48);
	inv_shiftrows_1(rkeys+40);
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	rkeys[57] ^= 0x00000300;		// 7th rconst
	xor_columns(rkeys+56);
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[64] ^= 0x00000300;		// 8th rconst
	xor_columns(rkeys+64);
	inv_shiftrows_1(rkeys+56);
	memcpy(rkeys+72, rkeys+64, 32);
	sbox(rkeys+72);
	rkeys[79] ^= 0x00000300; 		// 9th rconst
	rkeys[78] ^= 0x00000300; 		// 9th rconst
	rkeys[76] ^= 0x00000300; 		// 9th rconst
	rkeys[75] ^= 0x00000300; 		// 9th rconst
	xor_columns(rkeys + 72);
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[86] ^= 0x00000300; 		// 10th rconst
	rkeys[85] ^= 0x00000300; 		// 10th rconst
	rkeys[83] ^= 0x00000300;		// 10th rconst
	rkeys[82] ^= 0x00000300; 		// 10th rconst
	xor_columns(rkeys+80);
	inv_shiftrows_1(rkeys+72);
	for(int i = 1; i < 11; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}
