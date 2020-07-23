#ifndef AES_H_
#define AES_H_

#include <stdint.h>

extern void aes128_encrypt_ffs(unsigned char* ctext0, unsigned char * ctext1,
					const unsigned char* ptext0, const unsigned char* ptext1,
					const uint32_t* rkeys);

extern void aes128_encrypt_sfs(unsigned char* ctext0, unsigned char* ctext1,
					const unsigned char* ptext0, const unsigned char* ptext1,
					const uint32_t* rkeys);

extern void aes128_keyschedule_ffs(uint32_t* rkeys, const unsigned char* key0,
					const unsigned char* key1);

extern void aes128_keyschedule_sfs(uint32_t* rkeys, const unsigned char* key0,
					const unsigned char* key1);

extern void aes128_keyschedule_ffs_lut(uint32_t* rkeys,
					const unsigned char* key);

extern void aes128_keyschedule_sfs_lut(uint32_t* rkeys,
					const unsigned char* key);

#endif  // AES_H_