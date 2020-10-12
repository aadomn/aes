/******************************************************************************
* C language implementations of the AES-128 and AES-256 key schedules to match
* the fixsliced representation. Note that those implementations are fully
* bitsliced and do not rely on any Look-Up Table (LUT).
*
* See the paper at https://eprint.iacr.org/2020/1123.pdf for more details.
*
* @author 	Alexandre Adomnicai, Nanyang Technological University, Singapore
*			alexandre.adomnicai@ntu.edu.sg
*
* @date		October 2020
******************************************************************************/
#include <string.h> 	// for memcpy
#include "aes.h"
#include "internal-aes.h"

/******************************************************************************
* Applies ShiftRows^(-1) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_1(uint32_t* rkey) {
	uint32_t tmp;
	for(int i = 0; i < 8; i++) {
		SWAPMOVE(rkey[i], rkey[i], 0x0c0f0300, 4);
		SWAPMOVE(rkey[i], rkey[i], 0x33003300, 2);
	}
}
/******************************************************************************
* Applies ShiftRows^(-2) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_2(uint32_t* rkey) {
	uint32_t tmp;
	for(int i = 0; i < 8; i++)
		SWAPMOVE(rkey[i], rkey[i], 0x0f000f00, 4);
}

/******************************************************************************
* Applies ShiftRows^(-3) on a round key to match the fixsliced representation.
******************************************************************************/
static void inv_shiftrows_3(uint32_t* rkey) {
	uint32_t tmp;
	for(int i = 0; i < 8; i++) {
		SWAPMOVE(rkey[i], rkey[i], 0x030f0c00, 4);
		SWAPMOVE(rkey[i], rkey[i], 0x33003300, 2);
	}
}

/******************************************************************************
* XOR the columns after the S-box during the key schedule round function.
* Note that the NOT omitted in the S-box calculations have to be applied t
* ensure output correctness.
* The idx_ror parameter refers to the index of the previous round key that is
* involved in the XOR computation (should be 8 and 16 for AES-128 and AES-256,
* respectively).
* The idx_ror parameter refers to the rotation value. When a Rotword is applied
* the value should be 2, 26 otherwise.
******************************************************************************/
static void xor_columns(uint32_t* rkeys, int idx_xor, int idx_ror) {
	rkeys[1] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[2] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[6] ^= 0xffffffff; 			// NOT that are omitted in S-box
	rkeys[7] ^= 0xffffffff; 			// NOT that are omitted in S-box
	for(int i = 0; i < 8; i++) {
		rkeys[i] = (rkeys[i-idx_xor] ^ ROR(rkeys[i], idx_ror))  & 0xc0c0c0c0;
		rkeys[i] |= ((rkeys[i-idx_xor] ^ rkeys[i] >> 2) & 0x30303030);
		rkeys[i] |= ((rkeys[i-idx_xor] ^ rkeys[i] >> 2) & 0x0c0c0c0c);
		rkeys[i] |= ((rkeys[i-idx_xor] ^ rkeys[i] >> 2) & 0x03030303);
	}
}

/******************************************************************************
* Fully bitsliced AES-128 key schedule to match the fully-fixsliced (ffs)
* representation. Note that it is possible to pass two different keys as input
* parameters if one wants to encrypt 2 blocks in with two different keys.
******************************************************************************/
void aes128_keyschedule_ffs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 	// packs the keys into the bitsliced state
	memcpy(rkeys+8, rkeys, 32);
	sbox(rkeys+8);
	rkeys[15] ^= 0x00000300; 		// 1st rconst
	xor_columns(rkeys+8, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[22] ^= 0x00000300;		// 2nd rconst
	xor_columns(rkeys+16, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+8); 		// to match fixslicing
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	rkeys[29] ^= 0x00000300;		// 3rd rconst
	xor_columns(rkeys+24, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_2(rkeys+16); 		// to match fixslicing
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[36] ^= 0x00000300; 		// 4th rconst
	xor_columns(rkeys+32, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_3(rkeys+24); 		// to match fixslicing
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	rkeys[43] ^= 0x00000300; 		// 5th rconst
	xor_columns(rkeys+40, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[50] ^= 0x00000300;		// 6th rconst
	xor_columns(rkeys+48, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+40); 		// to match fixslicing
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	rkeys[57] ^= 0x00000300;		// 7th rconst
	xor_columns(rkeys+56, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_2(rkeys+48); 		// to match fixslicing
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[64] ^= 0x00000300;		// 8th rconst
	xor_columns(rkeys+64, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_3(rkeys+56); 		// to match fixslicing
	memcpy(rkeys+72, rkeys+64, 32);
	sbox(rkeys+72);
	rkeys[79] ^= 0x00000300; 		// 9th rconst
	rkeys[78] ^= 0x00000300; 		// 9th rconst
	rkeys[76] ^= 0x00000300; 		// 9th rconst
	rkeys[75] ^= 0x00000300; 		// 9th rconst
	xor_columns(rkeys + 72, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[86] ^= 0x00000300; 		// 10th rconst
	rkeys[85] ^= 0x00000300; 		// 10th rconst
	rkeys[83] ^= 0x00000300;		// 10th rconst
	rkeys[82] ^= 0x00000300; 		// 10th rconst
	xor_columns(rkeys+80, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+72);
	for(int i = 1; i < 11; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}

/******************************************************************************
* Fully bitsliced AES-256 key schedule to match the fully-fixsliced (ffs)
* representation. Note that it is possible to pass two different keys as input
* parameters if one wants to encrypt 2 blocks in with two different keys.
******************************************************************************/
void aes256_keyschedule_ffs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 		// packs the keys into the bitsliced state
	packing(rkeys+8, key0+16, key1+16); // packs the keys into the bitsliced state
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[23] ^= 0x00000300; 			// 1st rconst
	xor_columns(rkeys+16, 16, 2);  		// Rotword and XOR between the columns
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	xor_columns(rkeys+24, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+8);			// to match fixslicing
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[38] ^= 0x00000300; 			// 2nd rconst
	xor_columns(rkeys+32, 16, 2); 		// Rotword and XOR between the columns
	inv_shiftrows_2(rkeys+16); 			// to match fixslicing
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	xor_columns(rkeys+40, 16, 26); 		// XOR between the columns
	inv_shiftrows_3(rkeys+24); 			// to match fixslicing
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[53] ^= 0x00000300; 			// 3rd rconst
	xor_columns(rkeys+48, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	xor_columns(rkeys+56, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+40);			// to match fixslicing
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[68] ^= 0x00000300; 			// 4th rconst
	xor_columns(rkeys+64, 16, 2); 		// Rotword and XOR between the columns
	inv_shiftrows_2(rkeys+48); 			// to match fixslicing
	memcpy(rkeys+72, rkeys+64, 32);	
	sbox(rkeys+72);
	xor_columns(rkeys+72, 16, 26); 		// XOR between the columns
	inv_shiftrows_3(rkeys+56); 			// to match fixslicing
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[83] ^= 0x00000300; 			// 5th rconst
	xor_columns(rkeys+80, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+88, rkeys+80, 32);
	sbox(rkeys+88);
	xor_columns(rkeys+88, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+72);			// to match fixslicing
	memcpy(rkeys+96, rkeys+88, 32);
	sbox(rkeys+96);
	rkeys[98] ^= 0x00000300; 			// 6th rconst
	xor_columns(rkeys+96, 16, 2); 		// Rotword and XOR between the columns
	inv_shiftrows_2(rkeys+80); 			// to match fixslicing
	memcpy(rkeys+104, rkeys+96, 32);	
	sbox(rkeys+104);
	xor_columns(rkeys+104, 16, 26); 	// XOR between the columns
	inv_shiftrows_3(rkeys+88); 			// to match fixslicing
	memcpy(rkeys+112, rkeys+104, 32);
	sbox(rkeys+112);
	rkeys[113] ^= 0x00000300; 			// 7th rconst
	xor_columns(rkeys+112, 16, 2); 		// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+104);			// to match fixslicing
	for(int i = 1; i < 15; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}

/******************************************************************************
* Fully bitsliced AES-128 key schedule to match the semi-fixsliced (sfs)
* representation. Note that it is possible to pass two different keys as input
* parameters if one wants to encrypt 2 blocks in with two different keys.
******************************************************************************/
void aes128_keyschedule_sfs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 	// packs the keys into the bitsliced state
	memcpy(rkeys+8, rkeys, 32);
	sbox(rkeys+8);
	rkeys[15] ^= 0x00000300; 		// 1st rconst
	xor_columns(rkeys+8, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[22] ^= 0x00000300;		// 2nd rconst
	xor_columns(rkeys+16, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+8); 		// to match fixslicing
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	rkeys[29] ^= 0x00000300;		// 3rd rconst
	xor_columns(rkeys+24, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[36] ^= 0x00000300; 		// 4th rconst
	xor_columns(rkeys+32, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+24); 		// to match fixslicing
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	rkeys[43] ^= 0x00000300; 		// 5th rconst
	xor_columns(rkeys+40, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[50] ^= 0x00000300;		// 6th rconst
	xor_columns(rkeys+48, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+40); 		// to match fixslicing
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	rkeys[57] ^= 0x00000300;		// 7th rconst
	xor_columns(rkeys+56, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[64] ^= 0x00000300;		// 8th rconst
	xor_columns(rkeys+64, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+56); 		// to match fixslicing
	memcpy(rkeys+72, rkeys+64, 32);
	sbox(rkeys+72);
	rkeys[79] ^= 0x00000300; 		// 9th rconst
	rkeys[78] ^= 0x00000300; 		// 9th rconst
	rkeys[76] ^= 0x00000300; 		// 9th rconst
	rkeys[75] ^= 0x00000300; 		// 9th rconst
	xor_columns(rkeys + 72, 8, 2); 	// Rotword and XOR between the columns
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[86] ^= 0x00000300; 		// 10th rconst
	rkeys[85] ^= 0x00000300; 		// 10th rconst
	rkeys[83] ^= 0x00000300;		// 10th rconst
	rkeys[82] ^= 0x00000300; 		// 10th rconst
	xor_columns(rkeys+80, 8, 2); 	// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+72); 		// to match fixslicing
	for(int i = 1; i < 11; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}

/******************************************************************************
* Fully bitsliced AES-256 key schedule to match the fully-fixsliced (ffs)
* representation. Note that it is possible to pass two different keys as input
* parameters if one wants to encrypt 2 blocks in with two different keys.
******************************************************************************/
void aes256_keyschedule_sfs(uint32_t* rkeys, const unsigned char* key0,
						const unsigned char* key1) {
	packing(rkeys, key0, key1); 		// packs the keys into the bitsliced state
	packing(rkeys+8, key0+16, key1+16); // packs the keys into the bitsliced state
	memcpy(rkeys+16, rkeys+8, 32);
	sbox(rkeys+16);
	rkeys[23] ^= 0x00000300; 			// 1st rconst
	xor_columns(rkeys+16, 16, 2);  		// Rotword and XOR between the columns
	memcpy(rkeys+24, rkeys+16, 32);
	sbox(rkeys+24);
	xor_columns(rkeys+24, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+8);			// to match fixslicing
	memcpy(rkeys+32, rkeys+24, 32);
	sbox(rkeys+32);
	rkeys[38] ^= 0x00000300; 			// 2nd rconst
	xor_columns(rkeys+32, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+40, rkeys+32, 32);	
	sbox(rkeys+40);
	xor_columns(rkeys+40, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+24); 			// to match fixslicing
	memcpy(rkeys+48, rkeys+40, 32);
	sbox(rkeys+48);
	rkeys[53] ^= 0x00000300; 			// 3rd rconst
	xor_columns(rkeys+48, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+56, rkeys+48, 32);
	sbox(rkeys+56);
	xor_columns(rkeys+56, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+40);			// to match fixslicing
	memcpy(rkeys+64, rkeys+56, 32);
	sbox(rkeys+64);
	rkeys[68] ^= 0x00000300; 			// 4th rconst
	xor_columns(rkeys+64, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+72, rkeys+64, 32);	
	sbox(rkeys+72);
	xor_columns(rkeys+72, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+56); 			// to match fixslicing
	memcpy(rkeys+80, rkeys+72, 32);
	sbox(rkeys+80);
	rkeys[83] ^= 0x00000300; 			// 5th rconst
	xor_columns(rkeys+80, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+88, rkeys+80, 32);
	sbox(rkeys+88);
	xor_columns(rkeys+88, 16, 26); 		// XOR between the columns
	inv_shiftrows_1(rkeys+72);			// to match fixslicing
	memcpy(rkeys+96, rkeys+88, 32);
	sbox(rkeys+96);
	rkeys[98] ^= 0x00000300; 			// 6th rconst
	xor_columns(rkeys+96, 16, 2); 		// Rotword and XOR between the columns
	memcpy(rkeys+104, rkeys+96, 32);	
	sbox(rkeys+104);
	xor_columns(rkeys+104, 16, 26); 	// XOR between the columns
	inv_shiftrows_1(rkeys+88); 			// to match fixslicing
	memcpy(rkeys+112, rkeys+104, 32);
	sbox(rkeys+112);
	rkeys[113] ^= 0x00000300; 			// 7th rconst
	xor_columns(rkeys+112, 16, 2); 		// Rotword and XOR between the columns
	inv_shiftrows_1(rkeys+104);			// to match fixslicing
	for(int i = 1; i < 15; i++) {
		rkeys[i*8 + 1] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 2] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 6] ^= 0xffffffff; 	// NOT to speed up SBox calculations
		rkeys[i*8 + 7] ^= 0xffffffff; 	// NOT to speed up SBox calculations
	}
}
