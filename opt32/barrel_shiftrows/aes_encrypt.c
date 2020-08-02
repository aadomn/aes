/******************************************************************************
* Bitsliced implementations of AES-128 and AES-256 (encryption-only) in C using
* the barrel-shiftrows representation.
*
* See the paper available at https:// for more details.
*
* @author 	Alexandre Adomnicai, Nanyang Technological University, Singapore
*			alexandre.adomnicai@ntu.edu.sg
*
* @date		August 2020
******************************************************************************/
#include "aes.h"
#include "internal-aes.h"

/******************************************************************************
* Packing routine to rearrange the 8 16-byte blocs (128 bytes in total) into 
* the barrel-shiftrows bitsliced representation:
* out[0] = b_0 b_32 b_64 b_96
* ...
* out[31] = b_31 b_63 b_95 b_127
******************************************************************************/
static void packing(uint32_t* out, const unsigned char* in) {
	uint32_t tmp;
	for(int i = 0; i < 8; i++) {
		out[i] 		= LE_LOAD_32(in + i*16);
		out[i+8] 	= LE_LOAD_32(in + i*16 + 4);
		out[i+16] 	= LE_LOAD_32(in + i*16 + 8);
		out[i+24] 	= LE_LOAD_32(in + i*16 + 12);
		SWAPMOVE(out[i], out[i+8], 0x00ff00ff, 8);
		SWAPMOVE(out[i+16], out[i+24], 0x00ff00ff, 8);
	}
	for(int i = 0; i < 16; i++)
		SWAPMOVE(out[i], out[i+16], 0x0000ffff, 16);
	for(int i = 0; i < 32; i+=8) {
		SWAPMOVE(out[i+1], out[i], 	0x55555555, 1);
		SWAPMOVE(out[i+3], out[i+2],0x55555555, 1);
		SWAPMOVE(out[i+5], out[i+4],0x55555555, 1);
		SWAPMOVE(out[i+7], out[i+6],0x55555555, 1);
		SWAPMOVE(out[i+2], out[i], 	0x33333333, 2);
		SWAPMOVE(out[i+3], out[i+1],0x33333333, 2);
		SWAPMOVE(out[i+6], out[i+4],0x33333333, 2);
		SWAPMOVE(out[i+7], out[i+5],0x33333333, 2);
		SWAPMOVE(out[i+4], out[i], 	0x0f0f0f0f, 4);
		SWAPMOVE(out[i+5], out[i+1],0x0f0f0f0f, 4);
		SWAPMOVE(out[i+6], out[i+2],0x0f0f0f0f, 4);
		SWAPMOVE(out[i+7], out[i+3],0x0f0f0f0f, 4);
	}
}

/******************************************************************************
* Unpacking routine to store the internal state in a 128-byte array.
******************************************************************************/
static void unpacking(unsigned char* out, uint32_t* in) {
	uint32_t tmp;
	for(int i = 0; i < 32; i+=8) {
		SWAPMOVE(in[i+1], in[i],	0x55555555, 1);
		SWAPMOVE(in[i+3], in[i+2],	0x55555555, 1);
		SWAPMOVE(in[i+5], in[i+4],	0x55555555, 1);
		SWAPMOVE(in[i+7], in[i+6],	0x55555555, 1);
		SWAPMOVE(in[i+2], in[i], 	0x33333333, 2);
		SWAPMOVE(in[i+3], in[i+1],	0x33333333, 2);
		SWAPMOVE(in[i+6], in[i+4],	0x33333333, 2);
		SWAPMOVE(in[i+7], in[i+5],	0x33333333, 2);
		SWAPMOVE(in[i+4], in[i], 	0x0f0f0f0f, 4);
		SWAPMOVE(in[i+5], in[i+1],	0x0f0f0f0f, 4);
		SWAPMOVE(in[i+6], in[i+2],	0x0f0f0f0f, 4);
		SWAPMOVE(in[i+7], in[i+3],	0x0f0f0f0f, 4);
	}
	for(int i = 0; i < 16; i++)
		SWAPMOVE(in[i], in[i+16], 	0x0000ffff, 16);
	for(int i = 0; i < 8; i++) {
		SWAPMOVE(in[i], in[i+8], 	0x00ff00ff, 8);
		SWAPMOVE(in[i+16], in[i+24],0x00ff00ff, 8);
		LE_STORE_32(out+i*16, 	in[i]);
		LE_STORE_32(out+i*16+4, in[i+8]);
		LE_STORE_32(out+i*16+8, in[i+16]);
		LE_STORE_32(out+i*16+12,in[i+24]);
	}
}

/******************************************************************************
* Bitsliced implementation of the AES Sbox based on Boyar, Peralta and Calik.
* See http://www.cs.yale.edu/homes/peralta/CircuitStuff/SLP_AES_113.txt
* Note that the 4 NOT (^= 0xffffffff) are moved to the key schedule.
* Updates only a quarter of the state (i.e. 256 bits) => need to be applied 4
* times per round when considering the barrel-shiftrows representation.
******************************************************************************/
static void sbox(uint32_t* state) {
	uint32_t t0, t1, t2, t3, t4, t5,
		t6, t7, t8, t9, t10, t11, t12,
		t13, t14, t15, t16, t17;
	t0			= state[3] ^ state[5];
	t1			= state[0] ^ state[6];
	t2			= t1 ^ t0;
	t3			= state[4] ^ t2;
	t4			= t3 ^ state[5];
	t5			= t2 & t4;
	t6			= t4 ^ state[7];
	t7			= t3 ^ state[1];
	t8			= state[0] ^ state[3]; 
	t9			= t7 ^ t8;
	t10			= t8 & t9;
	t11			= state[7] ^ t9; 
	t12			= state[0] ^ state[5];
	t13			= state[1] ^ state[2];
	t14			= t4 ^ t13;
	t15			= t14 ^ t9;
	t16			= t0 & t15;
	t17			= t16 ^ t10;
	state[1]	= t14 ^ t12; 
	state[2]	= t12 & t14;
	state[2] 	^= t10;
	state[4]	= t13 ^ t9;
	state[5]	= t1 ^ state[4];
	t3			= t1 & state[4];
	t10			= state[0] ^ state[4];
	t13 		^= state[7];
	state[3] 	^= t13; 
	t16			= state[3] & state[7];
	t16 		^= t5;
	t16 		^= state[2];
	state[1] 	^= t16;
	state[0] 	^= t13;
	t16			= state[0] & t11;
	t16 		^= t3;
	state[2] 	^= t16;
	state[2] 	^= t10;
	state[6] 	^= t13;
	t10			= state[6] & t13;
	t3 			^= t10;
	t3 			^= t17;
	state[5] 	^= t3;
	t3			= state[6] ^ t12;
	t10			= t3 & t6;
	t5 			^= t10;
	t5 			^= t7;
	t5 			^= t17;
	t7			= t5 & state[5];
	t10			= state[2] ^ t7;
	t7 			^= state[1];
	t5 			^= state[1];
	t16			= t5 & t10;
	state[1] 	^= t16;
	t17			= state[1] & state[0];
	t11			= state[1] & t11;
	t16			= state[5] ^ state[2];
	t7 			&= t16;
	t7 			^= state[2];
	t16			= t10 ^ t7;
	state[2] 	&= t16;
	t10 		^= state[2];
	t10 		&= state[1];
	t5 			^= t10;
	t10			= state[1] ^ t5;
	state[4] 	&= t10; 
	t11 		^= state[4];
	t1 			&= t10;
	state[6] 	&= t5; 
	t10			= t5 & t13;
	state[4] 	^= t10;
	state[5] 	^= t7;
	state[2] 	^= state[5];
	state[5]	= t5 ^ state[2];
	t5			= state[5] & t14;
	t10			= state[5] & t12;
	t12			= t7 ^ state[2];
	t4 			&= t12;
	t2 			&= t12;
	t3 			&= state[2]; 
	state[2] 	&= t6;
	state[2] 	^= t4;
	t13			= state[4] ^ state[2];
	state[3] 	&= t7;
	state[1] 	^= t7;
	state[5] 	^= state[1];
	t6			= state[5] & t15;
	state[4] 	^= t6; 
	t0 			&= state[5];
	state[5]	= state[1] & t9; 
	state[5] 	^= state[4];
	state[1] 	&= t8;
	t6			= state[1] ^ state[5];
	t0 			^= state[1];
	state[1]	= t3 ^ t0;
	t15			= state[1] ^ state[3];
	t2 			^= state[1];
	state[0]	= t2 ^ state[5];
	state[3]	= t2 ^ t13;
	state[1]	= state[3] ^ state[5];
	//state[1] 	^= 0xffffffff;
	t0 			^= state[6];
	state[5]	= t7 & state[7];
	t14			= t4 ^ state[5];
	state[6]	= t1 ^ t14;
	state[6] 	^= t5; 
	state[6] 	^= state[4];
	state[2]	= t17 ^ state[6];
	state[5]	= t15 ^ state[2];
	state[2] 	^= t6;
	state[2] 	^= t10;
	//state[2] 	^= 0xffffffff;
	t14 		^= t11;
	t0 			^= t14;
	state[6] 	^= t0;
	//state[6] 	^= 0xffffffff;
	state[7]	= t1 ^ t0;
	//state[7] 	^= 0xffffffff;
	state[4]	= t14 ^ state[3]; 
}

/******************************************************************************
* ShiftRows on the entire 1024-bit internal state.
******************************************************************************/
static void shiftrows(uint32_t* state) {
	for(int i = 8; i < 16; i++) 		// shifts the 2nd row
		state[i] = ROR(state[i],8); 	// shifts the 2nd row
	for(int i = 16; i < 24; i++) 		// shifts the 3rd row
		state[i] = ROR(state[i],16); 	// shifts the 3rd row
	for(int i = 24; i < 32; i++) 		// shifts the 4th row
		state[i] = ROR(state[i],24); 	// shifts the 4th row
}

/******************************************************************************
* MixColumns on the entire 1024-bit internal state.
******************************************************************************/
static void mixcolumns(uint32_t* state) {
	uint32_t tmp2_0, tmp2_1, tmp2_2, tmp2_3;
	uint32_t tmp, tmp_bis, tmp0_0, tmp0_1, tmp0_2, tmp0_3;
	uint32_t tmp1_0, tmp1_1, tmp1_2, tmp1_3;
	tmp2_0 = state[0] ^ state[8];
	tmp2_1 = state[8] ^ state[16];
	tmp2_2 = state[16] ^ state[24];
	tmp2_3 = state[24] ^ state[0];
	tmp0_0 = state[7] ^ state[15];
	tmp0_1 = state[15] ^ state[23];
	tmp0_2 = state[23] ^ state[31];
	tmp0_3 = state[31]^ state[7];
	tmp = state[7];
	state[7] = tmp2_0 ^ tmp0_2 ^ state[15];
	state[15] = tmp2_1 ^ tmp0_2 ^ tmp;
	tmp = state[23];
	state[23] = tmp2_2 ^ tmp0_0 ^ state[31];
	state[31] = tmp2_3 ^ tmp0_0 ^ tmp;
	tmp1_0 = state[6] ^ state[14];
	tmp1_1 = state[14] ^ state[22];
	tmp1_2 = state[22] ^ state[30];
	tmp1_3 = state[30] ^ state[6]; 
	tmp = state[6];
	state[6] = tmp0_0 ^ tmp2_0 ^ state[14] ^ tmp1_2;
	tmp_bis = state[14];
	state[14] =  tmp0_1 ^ tmp2_1 ^ tmp1_2 ^ tmp;
	tmp = state[22];
	state[22] = tmp0_2 ^ tmp2_2 ^ tmp1_3 ^ tmp_bis;
	state[30] =  tmp0_3 ^ tmp2_3 ^ tmp1_0 ^ tmp;
	tmp0_0 = state[5] ^ state[13];
	tmp0_1 = state[13] ^ state[21];
	tmp0_2 = state[21] ^ state[29];
	tmp0_3 = state[29]^ state[5];
	tmp = state[5];
	state[5] = tmp1_0 ^ tmp0_1 ^ state[29];
	tmp_bis = state[13];
	state[13] = tmp1_1 ^ tmp0_2 ^ tmp;
	tmp = state[21];
	state[21] =  tmp1_2 ^ tmp0_3 ^ tmp_bis;
	state[29] = tmp1_3 ^ tmp0_0 ^ tmp;
	tmp1_0 = state[4] ^ state[12];
	tmp1_1 = state[12] ^ state[20];
	tmp1_2 = state[20] ^ state[28];
	tmp1_3 = state[28] ^ state[4];
	tmp = state[4];
	state[4] = tmp0_0 ^ tmp2_0 ^ tmp1_1 ^ state[28];	
	tmp_bis = state[12];
	state[12] = tmp0_1 ^ tmp2_1 ^ tmp1_2 ^ tmp;
	tmp = state[20];
	state[20] = tmp0_2 ^ tmp2_2 ^ tmp1_3 ^ tmp_bis;
	state[28] = tmp0_3 ^ tmp2_3 ^ tmp1_0 ^ tmp;
	tmp0_0 = state[3] ^ state[11];
	tmp0_1 = state[11] ^ state[19];
	tmp0_2 = state[19] ^ state[27];
	tmp0_3 = state[27]^ state[3];
	tmp = state[3];
	state[3] = tmp1_0 ^ tmp2_0 ^ tmp0_1 ^ state[27];
	tmp_bis = state[11];
	state[11] = tmp1_1 ^ tmp2_1 ^ tmp0_2 ^ tmp;
	tmp = state[19];
	state[19] = tmp1_2 ^ tmp2_2 ^ tmp0_3 ^ tmp_bis;
	state[27] =  tmp1_3 ^ tmp2_3 ^ tmp0_0 ^ tmp;
	tmp1_0 = state[2] ^ state[10];
	tmp1_1 = state[10] ^ state[18];
	tmp1_2 = state[18] ^ state[26];
	tmp1_3 = state[26] ^ state[2];
	tmp = state[2];
	state[2] = tmp0_0 ^ tmp1_1 ^ state[26];
	tmp_bis = state[10];
	state[10] = tmp0_1 ^ tmp1_2 ^ tmp;
	tmp = state[18];
	state[18] = tmp0_2 ^ tmp1_3 ^ tmp_bis;
	state[26] = tmp0_3 ^ tmp1_0 ^ tmp;
	tmp0_0 = state[1] ^ state[9];
	tmp0_1 = state[9] ^ state[17];
	tmp0_2 = state[17] ^ state[25];
	tmp0_3 = state[25]^ state[1];
	tmp = state[1];
	state[1] = tmp1_0 ^ tmp0_1 ^ state[25];
	tmp_bis = state[9];
	state[9] = tmp1_1 ^ tmp0_2 ^ tmp;
	tmp = state[17];
	state[17] = tmp1_2 ^ tmp0_3 ^ tmp_bis;
	state[25] =  tmp1_3 ^ tmp0_0 ^ tmp;
	tmp = state[0];
	state[0] = tmp0_0 ^ tmp2_1 ^ state[24];
	tmp_bis = state[8];
	state[8] = tmp0_1 ^ tmp2_2 ^ tmp;
	tmp = state[16];
	state[16] = tmp0_2 ^ tmp2_3 ^ tmp_bis;
	state[24] = tmp0_3 ^ tmp2_0 ^ tmp;
}

/******************************************************************************
* AddRoundKey on the entire 1024-bit internal state.
******************************************************************************/
static void ark(uint32_t* state, const uint32_t* rkey) {
	for(int i = 0; i < 32; i++)
		state[i] ^= rkey[i];
}

/******************************************************************************
* Encryption of 8 128-bit blocks of data in parallel using AES-128 with the
* barrel-shiftrows representation.
* The round keys are assumed to be pre-computed.
******************************************************************************/
void aes128_encrypt(unsigned char* out, const unsigned char* in,
				const uint32_t* rkeys) {
	uint32_t state[32]; 				// 1024-bit state (8 blocks in //)
	packing(state, in); 				// From bytes to the barrel-shiftrows
	for(int i = 0; i < 10; i++) {
		ark(state, rkeys+i*32); 		// AddRoundKey on the entire state
		sbox(state); 					// S-box on the 1st quarter state
		sbox(state + 8); 				// S-box on the 2nd quarter state
		sbox(state + 16); 				// S-box on the 3rd quarter state
		sbox(state + 24); 				// S-box on the 4th quarter state
	    shiftrows(state); 				// ShiftRows on the entire state
	    if (i != 9) 					// No MixColumns in the last round
			mixcolumns(state);		 	// MixColumns on the entire state
	}
	ark(state, rkeys+320); 				// AddRoundKey on the entire state
	unpacking(out, state); 				// From barrel-shiftrows to bytes
}

/******************************************************************************
* Encryption of 8 128-bit blocks of data in parallel using AES-256 with the
* barrel-shiftrows representation.
* The round keys are assumed to be pre-computed.
******************************************************************************/
void aes256_encrypt(unsigned char* out, const unsigned char* in,
				const uint32_t* rkeys) {
	uint32_t state[32]; 				// 1024-bit state (8 blocks in //)
	packing(state, in); 				// From bytes to the barrel-shiftrows
	for(int i = 0; i < 14; i++) {
		ark(state, rkeys+i*32); 		// AddRoundKey on the entire state
		sbox(state); 					// S-box on the 1st quarter state
		sbox(state + 8); 				// S-box on the 2nd quarter state
		sbox(state + 16); 				// S-box on the 3rd quarter state
		sbox(state + 24); 				// S-box on the 4th quarter state
	    shiftrows(state); 				// ShiftRows on the entire state
	    if (i != 13) 					// No MixColumns in the last round
			mixcolumns(state);		 	// MixColumns on the entire state
	}
	ark(state, rkeys+448); 				// AddRoundKey on the entire state
	unpacking(out, state); 				// From barrel-shiftrows to bytes
}
