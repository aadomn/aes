#ifndef INTERNAL_AES_H_
#define INTERNAL_AES_H_

#include <stdint.h>

#define ROR(x,y) 		(((x) >> (y)) | ((x) << (32 - (y))))

#define BYTE_ROR_6(x) 										\
	((((x) >> 6) & 0x03030303)	| (((x) & 0x3f3f3f3f) << 2))

#define BYTE_ROR_4(x) 										\
	((((x) >> 4) & 0x0f0f0f0f)	| (((x) & 0x0f0f0f0f) << 4))
	
#define BYTE_ROR_2(x) 										\
	((((x) >> 2) & 0x3f3f3f3f)	| (((x) & 0x03030303) << 6))

#define SWAPMOVE(a, b, mask, n)	({							\
	tmp = (b ^ (a >> n)) & mask;							\
	b ^= tmp;												\
	a ^= (tmp << n);										\
})

#define LE_LOAD_32(x) 										\
    ((((uint32_t)((x)[3])) << 24) | 						\
     (((uint32_t)((x)[2])) << 16) | 						\
     (((uint32_t)((x)[1])) << 8) | 							\
      ((uint32_t)((x)[0])))

#define LE_STORE_32(x, y)									\
	(x)[0] = (y) & 0xff; 									\
	(x)[1] = ((y) >> 8) & 0xff; 							\
	(x)[2] = ((y) >> 16) & 0xff; 							\
	(x)[3] = (y) >> 24;

void packing(uint32_t* out, const unsigned char* in0,
		const unsigned char* in1);

void sbox(uint32_t* state);

#endif 	// INTERNAL_AES_H_