#ifndef AES_H
#define AES_H

#include <stdint.h>

void aes128_keyschedule_lut(uint32_t rkeys[352], const uint8_t key[16]);
void aes256_keyschedule_lut(uint32_t rkeys[480], const uint8_t key[32]);

void aes128_encrypt(uint8_t out[128], const uint8_t in[128], const uint32_t rkeys[352]);
void aes256_encrypt(uint8_t out[128], const uint8_t in[128], const uint32_t rkeys[480]);

#endif