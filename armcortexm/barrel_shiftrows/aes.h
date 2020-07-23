#ifndef AES_H_
#define AES_H_

#include <stdint.h>

extern void aes128_encrypt(unsigned char* ctext, const uint32_t* rkeys,
				const unsigned char* ptext);

extern void aes128_keyschedule_lut(uint32_t* rkeys, const unsigned char* key);

#endif 	// AES_H_