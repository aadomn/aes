#ifndef AES_H_
#define AES_H_

#include <stdint.h>

extern void aes128_encrypt_ffs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[121]);

extern void aes128_encrypt_sfs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[121]);

extern void aes128_keyschedule_ffs(uint32_t rkeys[121], const unsigned char key0[16],
					const unsigned char key1[16]);

extern void aes128_keyschedule_sfs(uint32_t rkeys[121], const unsigned char key0[16],
					const unsigned char key1[16]);

#endif 	// AES_H_