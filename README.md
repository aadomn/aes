# Fast constant-time AES implementations on 32-bit architectures

## Structure of the repository

This repository contains efficient constant-time implementations for the Advanced Encryption Standard (AES) algorithm as supplementary material for the paper [Fixslicing AES-like Ciphers - New bitsliced AES speed records on ARM Cortex-M and RISC-V](https://eprint.iacr.org/2020) published at 

The repository structure is as follows:
```
aes
│   README.md
│   LICENSE   
│
└───armcortexm
│   └───1storder_masking
│   └───barrel_shiftrows
│   └───fixslicing
│   
└───opt32
│   └───barrel_shiftrows
│   └───fixslicing
│   
└───riscv
│   └───barrel_shiftrows
│   └───fixslicing
```
where `armcortexm` and `riscv` directories respectively refer to assembly implementations for ARM Cortex-M and RV32I, whereas `opt32` refer to C language implementations. Note that the main goal of the `opt32` directory is to provide cross-platform implementations and to serve a didactic purpose. Therefore if you intend to run it for benchmarking, you should consider some modifications regarding execution speed.

## AES representations

Each directory includes two different AES representations:
- `barrel_shiftrows`

   Processes 8 blocks in parallel. Requires 1408 and 1920 bytes to store all the round keys for AES-128 and AES-256, respectively.

- `fixslicing`

   Processes 2 blocks in parallel. Requires 352 and 480 bytes to store all the round keys for AES-128 and AES-256, respectively.
   Two fixsliced versions are proposed:
   * `Fully-fixsliced`: faster but at the cost of a larger code size
   * `Semi-fixsliced`: slightly slower but more compact.

## Performance

Since the fixsliced representations require 4 times less RAM to store all the round keys, they are more suited to the most resource-constrained platforms. Still, the barrel-shiftrows representation might be worthy of consideration for use-cases that deal with large amount of data on architectures with numerous general-purpose registers (e.g. RV32I). The table below summarizes the performance of each version on ARM Cortex-M3 and RV32I in cycles per byte. Note that those implementations are non-unrolled to ensure greater clarity and limit the impact on code size. Unrolling them would result in slightly better performance and we refer to [the paper](https://eprint.iacr.org/2020) for more details.

| Algorithm                | Parallel blocks | ARM Cortex-M3 | RV32I (HiFive1 Rev B) |
|:-------------------------|:---------------:|:-------------:|:---------------------:|
| AES-128 semi-fixsliced   | 2               | 91.3          | 108.3                 |
| AES-128 fully-fixsliced  | 2               | 87.3          | 101.6                 |
| AES-128 barrel-shiftrows | 8               | 94.8          | 78.9                  |
| AES-256 semi-fixsliced   | 2               | 125.8         |                       |
| AES-256 fully-fixsliced  | 2               | 119.8         |                       |
| AES-256 barrel-shiftrows | 8               | 127.9         |                       |

## First-order masking

A first-order masked implementation based on fixslicing can be found in `armcortexm/1storder_masking`. The masking scheme is the one described in the article [Masking the AES with Only Two Random Bits](https://eprint.iacr.org/2018/1007) and is strongly based on the code from the [corresponding repository](https://github.com/LaurenDM/TwoRandomBits). Note that the code in charge of the randomness generation is specific to the STM32F407VG development board and some changes would be necessary to run it on another board. The table below summarizes their performance on ARM Cortex-M4in cycles per byte. Once again, results can be slightly enhanced by unrolling the code.

| Algorithm                                 | Parallel blocks | ARM Cortex-M4 |
|:------------------------------------------|:---------------:|:-------------:|
| 1st-order masked AES-128 semi-fixsliced   | 2               | 200.7         |
| 1st-order masked AES-128 fully-fixsliced         | 2               | 196           |

:warning::rotating_light: This masking scheme was mainly introduced to achieve first-order masking while limiting the amount of randomness to generate. Please be aware that other first-order masking schemes provide a better security level. Note that no practical evaluation has been undertaken to assess the security of our masked implementations! :rotating_light::warning: 
