#ifndef AES_H_
#define AES_H_

#include <stdint.h>

void aes128_encrypt(unsigned char* ctext, const unsigned char* ptext,
				const uint32_t* rkeys);

void aes128_keyschedule(uint32_t* rkeys, const unsigned char* key);


#endif 	// AES_H_