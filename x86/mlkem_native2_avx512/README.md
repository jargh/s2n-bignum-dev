# ML-KEM in assembly: the mlkem-native API for x86_64 with AVX-512

This directory has the AVX-512 version of `../mlkem_native2`: the same
functions of mlkem-native's ML-KEM API, for all three parameter sets,

    int mlkemL_keypair_derand_avx512(uint8_t *pk, uint8_t *sk,
                                     const uint8_t *coins)
    int mlkemL_enc_derand_avx512(uint8_t *ct, uint8_t *ss,
                                 const uint8_t *pk, const uint8_t *coins)
    int mlkemL_dec_avx512(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
    int mlkemL_check_pk_avx512(const uint8_t *pk)
    int mlkemL_check_sk_avx512(const uint8_t *sk)

with the same results and the same contracts as those without the suffix
(see `../mlkem_native2/README.md`), for processors with AVX-512F,
AVX-512VL, AVX-512BW and AVX-512DQ besides AVX2. All the global symbols
of the API and of the middle layer have the suffix `_avx512`, so that
both versions link into one library and the version can be chosen at run
time.

## Structure

 - The API and the middle layer are the sources of `../mlkem_native2`,
   assembled with `MLKEM_NATIVE2_AVX512` defined: `mlkemL_avx512.S` and
   `mlkem_gen_matrix_avx512.S`, `mlkem_getnoise_avx512.S`,
   `mlkem_hash_h_avx512.S` and `mlkem_hash_g_avx512.S` include them, and
   `../mlkem_native2/mlkem_native2_names.h` then gives the suffixed names
   and the Keccak-f1600 permutations and the rejection sampler below. The
   code is thus the same, the schedule of the Keccak work over the lanes
   included, except for the functions it calls.
 - Two Keccak-f1600 permutations with AVX-512VL, generated (from a script
   kept outside the repository, like the prototypes measured for the
   design): `sha3_keccak4_f1600_avx512`, a drop-in for
   `sha3_keccak4_f1600_alt` (four separate states, transposed into and out
   of 25 ymm registers), and `sha3_keccak_f1600_avx512`, a drop-in for
   `sha3_keccak_f1600` (one state, a lane in each of 25 xmm registers).
   Both keep the whole state in registers (32 of them with AVX-512) and
   do the rotations with `vprolq` and the five-way XORs of theta and chi
   with `vpternlogq`; pi is a renaming of the registers, undone every
   four rounds.
 - A rejection sampler with AVX-512F and AVX-512BW,
   `mlkem_rej_uniform_alt_VARIABLE_TIME_avx512`, with the contract of
   `mlkem_rej_uniform_alt_VARIABLE_TIME` but no table (the calls still
   pass one, which it ignores): each 24 bytes of the buffer give 16
   fields in the dwords of a zmm register, `vpcmpgtd` gives the mask of
   those < 3329 in an opmask register, and `vpcompressd` and `vpmovdw`
   write them to r (with a mask that keeps the writes inside r for the
   last 15 entries). It costs 140 cycles for 504 bytes (a typical matrix
   polynomial) against 287 for the AVX2 one.
 - The other leaves and the constants block are those of
   `../mlkem_native2` (in `../mlkem`), unchanged: AVX-512 gains little over
   AVX2 for them on these processors, and the 256-bit integer
   multiplications of the arithmetic kernels keep the core at the same AVX
   frequency licence.

The EVEX-encoded instructions of the two permutations are all on ymm or
xmm registers (no zmm) and without masking: `vpternlogq`, `vprolq`,
`vmovdqa64` (register moves), `vshufi64x2`, `vpunpcklqdq`, `vpunpckhqdq`,
`vmovdqu64`, `vmovq`, `vpinsrq` and `vpextrq` (these as EVEX forms since
they use registers 16-31), `vinserti32x4`, `vextracti32x4` and `vpxorq`
with a broadcast memory operand (`{1to4}`, `{1to2}`). Those of the sampler
are on zmm registers, with the opmask registers k1-k4: `vpmovzxwd`,
`vpbroadcastd` (from a general register), `kmovw` (both ways),
`vbroadcasti32x4` (from memory, also merge-masked), `vpshufb`, `vpsrld`
(merge-masked), `vpandd`, `vpcmpgtd` (into an opmask register),
`vpcompressd` (zero-masked) and `vpmovdw` (to memory, also masked). The
EVEX forms of `vpinsrq` and `vpextrq` need AVX-512DQ, and `vpshufb` on zmm
registers AVX-512BW. The state of the x86 model already has the 32 zmm and
the 8 opmask registers, but it decodes no EVEX instruction yet.

## Building and the image

None of these files is in the `OBJ` list of `../Makefile`. The image for
the proofs is `mlkem_native2_avx512_image.elf` (`make
mlkem_native2_avx512/mlkem_native2_avx512_image.elf` in `x86`), linked at
address 0 by `mlkem_native2_avx512_image.ld` from the objects in
`MLKEM_NATIVE2_AVX512_IMAGE_OBJ` of `../Makefile`: this directory's, the
leaves of `../mlkem` but the AVX2 rejection sampler, and the constants
block of `../mlkem_native2`. As for the AVX2 version, it has no
relocations, every call in it is a direct call and the constants block is
at the end, addressed RIP-relatively. The ABI
is the same too (System V, with Microsoft x64 wrappers of the API
functions under `WINDOWS_ABI`).

## Speed

On a Xeon Platinum 8259CL (Cascade Lake) the x4 permutation costs 1040
cycles against 1723 for `sha3_keccak4_f1600_alt`, and the x1 949 against
1260 for `sha3_keccak_f1600`, both at the base AVX frequency licence
(they use no heavy or 512-bit instructions), and the rejection sampler
140 against 287 for 504 bytes (it uses zmm registers, at the licence of
the arithmetic kernels). Cycles per call, as for the AVX2 version
(medians of 31 runs of 200 calls on one core, with the clock measured
after each run):

| function | mlkem-native | AVX2 version | here | vs mlkem-native |
|---|---|---|---|---|
| mlkem512_keypair_derand | 24950 | 21914 | 16288 | -34.7% |
| mlkem512_enc_derand | 29269 | 20571 | 14542 | -50.3% |
| mlkem512_dec | 39724 | 22334 | 16449 | -58.6% |
| mlkem512_check_sk | 8717 | 7674 | 5844 | -33.0% |
| mlkem768_keypair_derand | 43129 | 35676 | 25802 | -40.2% |
| mlkem768_enc_derand | 46425 | 29346 | 20697 | -55.4% |
| mlkem768_dec | 61619 | 35015 | 25043 | -59.4% |
| mlkem768_check_sk | 13028 | 11655 | 8907 | -31.6% |
| mlkem1024_keypair_derand | 59056 | 52781 | 37461 | -36.6% |
| mlkem1024_enc_derand | 64784 | 45797 | 31890 | -50.8% |
| mlkem1024_dec | 84822 | 54079 | 38468 | -54.6% |
| mlkem1024_check_sk | 17303 | 15467 | 11770 | -32.0% |

(check_pk is as in the AVX2 version.) Stack use, in bytes (keypair_derand,
enc_derand, dec): 9048, 8552, 10216 for ML-KEM-512; 13400, 13416, 15720 for
ML-KEM-768; 20520, 19304, 22568 for ML-KEM-1024 (224 more through the
Windows wrappers), a little less than the AVX2 version since the
permutations and the sampler use no stack.

## Constant time and testing

As for the AVX2 version: everything is constant-time in the secret data,
with the same schedule. The tests of `../../tests/mlkem_native2` run on
this version with `VARIANT=avx512 ./build.sh`, which builds it into
`work/obj_avx512` with the suffix removed from the names of the API and
the middle layer, so that the tests and the benchmarks use it unchanged.
valgrind does not run EVEX code, so the steps under memcheck (memcheck and
the constant-time check) do not apply: `VALGRIND= CTLIBS=none ./gate.sh
avx512 work/obj_avx512/*.o` runs the rest of the gate.
