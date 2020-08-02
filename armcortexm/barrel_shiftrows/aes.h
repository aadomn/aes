#ifndef AES_H_
#define AES_H_

#include <stdint.h>

extern void aes128_encrypt(unsigned char ctext[128], const uint32_t rkeys[352],
				const unsigned char ptext[128]);
extern void aes256_encrypt(unsigned char ctext[128], const uint32_t rkeys[480],
				const unsigned char ptext[128]);

extern void aes128_keyschedule_lut(uint32_t rkeys[352], const unsigned char key[16]);
extern void aes256_keyschedule_lut(uint32_t rkeys[480], const unsigned char key[32]);

#endif 	// AES_H_