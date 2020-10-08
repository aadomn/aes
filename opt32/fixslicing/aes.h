#ifndef AES_H_
#define AES_H_

#include <stdint.h>

/* Fully-fixsliced encryption functions */
void aes128_encrypt_ffs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[88]);
void aes256_encrypt_ffs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[120]);

/* Semi-fixsliced encryption functions */
void aes128_encrypt_sfs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[88]);
void aes256_encrypt_sfs(unsigned char ctext0[16], unsigned char ctext1[16],
				const unsigned char ptext0[16], const unsigned char ptext1[16],
				const uint32_t rkeys[120]);

/* Fully-fixsliced key schedule functions */
void aes128_keyschedule_ffs(uint32_t rkeys[88], const unsigned char key0[16],
				const unsigned char key1[16]);
void aes256_keyschedule_ffs(uint32_t rkeys[120], const unsigned char key0[32],
				const unsigned char key1[32]);

/* Semi-fixsliced key schedule functions */
void aes128_keyschedule_sfs(uint32_t rkeys[88], const unsigned char key0[16],
				const unsigned char key1[16]);
void aes256_keyschedule_sfs(uint32_t rkeys[120], const unsigned char key0[32],
				const unsigned char key1[32]);

/* Fully-fixsliced key schedule functions (LUT-based) */
void aes128_keyschedule_ffs_lut(uint32_t rkeys[88],const unsigned char key[16]);
void aes256_keyschedule_ffs_lut(uint32_t rkeys[120], const unsigned char key[32]);

/* Semi-fixsliced key schedule functions (LUT-based) */
void aes128_keyschedule_sfs_lut(uint32_t rkeys[88], const unsigned char key[16]);
void aes256_keyschedule_sfs_lut(uint32_t rkeys[120], const unsigned char key[32]);

#endif 	// AES_H_
