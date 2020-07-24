#ifndef AES_H_
#define AES_H_

#include <stdint.h>

extern void aes128_encrypt(unsigned char ctext[128], const unsigned char ptext[128],
				const uint32_t rkeys[352]);

extern void aes128_keyschedule_lut(uint32_t rkeys[352], const unsigned char key[16]);

#endif 	// AES_H_