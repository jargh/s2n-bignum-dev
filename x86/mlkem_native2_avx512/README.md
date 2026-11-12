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
 - Two Keccak-f1600 permutations, generated (from scripts kept outside
   the repository, like the prototypes measured for the design), both
   with the whole state in registers, the rotations by `vprolq` or
   `vprolvq` and the five-way XORs of theta and chi by `vpternlogq`:
    - `sha3_keccak4_f1600_avx512`, a drop-in for `sha3_keccak4_f1600_alt`
      with AVX-512VL: four separate states, transposed into and out of 25
      ymm registers (lane i of state j in quadword j of register i), where
      pi is a renaming of the registers, undone every four rounds;
    - `sha3_keccak_f1600_avx512`, a drop-in for `sha3_keccak_f1600` with
      AVX-512F: one state in five zmm registers, five lanes in each. The
      registers hold sets of lanes that pi maps onto each other (so it
      moves no lane between registers), each in two orders, one in which
      theta is a vertical XOR of the registers and one in which chi takes
      whole registers, with `vpermq` between them; every three rounds
      masked blends and `vpermi2q` change the sets (the comments of the
      file explain the layouts). Its index vectors and rotation counts
      are a table in `.rodata`, which it reads RIP-relatively.
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

The EVEX-encoded instructions of the x4 permutation are all on ymm or xmm
registers (no zmm) and without masking: `vpternlogq`, `vprolq`,
`vmovdqa64` (register moves), `vshufi64x2`, `vpunpcklqdq`, `vpunpckhqdq`,
`vmovdqu64`, `vmovq`, `vpinsrq` and `vpextrq` (these as EVEX forms since
they use registers 16-31), `vinserti32x4`, `vextracti32x4` and `vpxorq`
with a broadcast memory operand (`{1to4}`). Those of the x1 permutation
are on zmm registers, with the opmask registers k1-k6: `vpternlogq`,
`vpxorq` (also merge-masked, with a broadcast memory operand `{1to8}`),
`vprolq`, `vprolvq` (with the counts from memory), `vpermq`, `vpermi2q`,
`vpblendmq`, `vmovdqa64` (register moves, also merge-masked, and loads),
`vmovdqu64` (zero-masked loads and masked stores of the rows) and `kmovw`
(from a general register). Those of the sampler are on zmm registers, with
the opmask registers k1-k4: `vpmovzxwd`, `vpbroadcastd` (from a general
register), `kmovw` (both ways), `vbroadcasti32x4` (from memory, also
merge-masked), `vpshufb`, `vpsrld` (merge-masked), `vpandd`, `vpcmpgtd`
(into an opmask register), `vpcompressd` (zero-masked) and `vpmovdw` (to
memory, also masked). The EVEX forms of `vpinsrq` and `vpextrq` need
AVX-512DQ, and `vpshufb` on zmm registers AVX-512BW. The state of the x86
model already has the 32 zmm and the 8 opmask registers, but it decodes no
EVEX instruction yet.

## Building and the image

None of these files is in the `OBJ` list of `../Makefile`. The image for
the proofs is `mlkem_native2_avx512_image.elf` (`make
mlkem_native2_avx512/mlkem_native2_avx512_image.elf` in `x86`), linked at
address 0 by `mlkem_native2_avx512_image.ld` from the objects in
`MLKEM_NATIVE2_AVX512_IMAGE_OBJ` of `../Makefile`: this directory's, the
leaves of `../mlkem` but the AVX2 rejection sampler, and the constants
block of `../mlkem_native2`. As for the AVX2 version, it has no
relocations and every call in it is a direct call; the read-only data is
at the end, addressed RIP-relatively: the table of the x1 permutation,
then the constants block. The ABI is the same too (System V, with
Microsoft x64 wrappers of the API functions under `WINDOWS_ABI`).

## Speed

On a Xeon Platinum 8259CL (Cascade Lake) the x4 permutation costs 1040
cycles against 1723 for `sha3_keccak4_f1600_alt` (at the base AVX
frequency licence: it uses no heavy or 512-bit instructions), the x1 732
against 1260 for `sha3_keccak_f1600`, and the rejection sampler 140
against 287 for 504 bytes (these two use zmm registers, at the licence of
the arithmetic kernels). Key generation and `check_sk`, which hash the
encapsulation key with the x1 permutation, gain most from the x1. Cycles
per call, as for the AVX2 version (medians of 31 runs of 200 calls on one
core, with the clock measured after each run):

| function | mlkem-native | AVX2 version | here | vs mlkem-native |
|---|---|---|---|---|
| mlkem512_keypair_derand | 24950 | 21914 | 14292 | -42.7% |
| mlkem512_enc_derand | 29269 | 20571 | 14012 | -52.1% |
| mlkem512_dec | 39724 | 22334 | 15796 | -60.2% |
| mlkem512_check_sk | 8717 | 7674 | 4563 | -47.7% |
| mlkem768_keypair_derand | 43129 | 35676 | 23032 | -46.6% |
| mlkem768_enc_derand | 46425 | 29346 | 20049 | -56.8% |
| mlkem768_dec | 61619 | 35015 | 24488 | -60.3% |
| mlkem768_check_sk | 13028 | 11655 | 6879 | -47.2% |
| mlkem1024_keypair_derand | 59056 | 52781 | 33974 | -42.5% |
| mlkem1024_enc_derand | 64784 | 45797 | 31005 | -52.1% |
| mlkem1024_dec | 84822 | 54079 | 37390 | -55.9% |
| mlkem1024_check_sk | 17303 | 15467 | 9136 | -47.2% |

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
