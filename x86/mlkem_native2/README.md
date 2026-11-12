# ML-KEM in assembly: the mlkem-native API for x86_64 (AVX2)

This directory has an implementation in assembly of the ML-KEM functions
of [mlkem-native](https://github.com/pq-code-package/mlkem-native)'s API,
for all three parameter sets:

    int mlkemL_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins)
    int mlkemL_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
                          const uint8_t *coins)
    int mlkemL_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
    int mlkemL_check_pk(const uint8_t *pk)
    int mlkemL_check_sk(const uint8_t *sk)

for L = 512, 768, 1024, with the same results as mlkem-native's (return
values included). It is the x86_64 counterpart of `../../arm/mlkem_native2`,
with the same design, for processors with AVX2 (and POPCNT; no AVX-512),
written in the style of s2n-bignum and meant to be proved in HOL Light
like the AArch64 version. The AVX-512 version, from the same sources, is
in `../mlkem_native2_avx512`. The randomized `mlkemL_keypair` and
`mlkemL_enc` are not here, since they need a source of randomness: as in
mlkem-native, they get 64 or 32 random bytes, call the deterministic
function and zero the bytes (`../../tests/mlkem_native2/randomized.c`).

## Structure

The work is in three layers, as on AArch64.

 - The leaves, in `../mlkem`, standalone s2n-bignum-style functions, each
   with its own specification in its header comment:
    - the existing x86 kernels of s2n-bignum, which are mlkem-native's
      current AVX2 code: `mlkem_ntt_x86`, `mlkem_intt_x86`,
      `mlkem_mulcache_compute_x86`, `mlkem_basemul_k{2,3,4}`,
      `mlkem_reduce`, `mlkem_tomont`, `mlkem_frombytes` and
      `mlkem_tobytes` (which include the permutation into and out of the
      custom NTT order of mlkem-native's x86 backend) and `mlkem_unpack`
      (that permutation, for the sampled matrix); and s2n-bignum's
      Keccak-f1600 kernels `sha3_keccak_f1600` (x1) and
      `sha3_keccak4_f1600_alt` (x4);
    - mlkem-native's AVX2 compress and decompress kernels for d = 4, 5, 10
      and 11, unchanged (byte for byte, so that mlkem-native's HOL Light
      proofs of them apply), as `mlkem_compress_d4_x86` and so on: they
      take their tables from the constants block;
    - new ones for what mlkem-native does in C, with the same names,
      signatures and contracts as on AArch64: `mlkem_cbd2`, `mlkem_cbd3`,
      `mlkem_frommsg`, `mlkem_tomsg`, `mlkem_check_encoding` (the modulus
      check of an encapsulation key), `mlkem_add_reduce`,
      `mlkem_sub_reduce`, and a faster rejection sampler
      `mlkem_rej_uniform_alt_VARIABLE_TIME` that appends to a partial
      result.
 - The middle layer, here: `mlkem_gen_matrix` (the matrix, with hash jobs
   and noise in the spare lanes of the x4 permutation, and its
   polynomials permuted into the custom NTT order), `mlkem_getnoise`
   (noise sampling in the x4 lanes), `mlkem_hash_h` and `mlkem_hash_g`
   (SHA3-256 and SHA3-512 with the x1 permutation). The seventh argument
   of `mlkem_gen_matrix` and `mlkem_getnoise`, the constants block, is on
   the stack.
 - The API: `mlkem_kem_template.S`, included by `mlkem512.S`,
   `mlkem768.S` and `mlkem1024.S` after they define the parameter set.
   Besides the API functions it has `mlkemL_pke_encrypt` and
   `mlkemL_pke_decrypt`, shared by encapsulation and decapsulation.

The tables of constants (the Keccak round constants and the rho8 and rho56
tables of the x4 permutation, the qdata of the NTT kernels, the tables of
the compress and decompress kernels and the rejection sampling table, all
taken unchanged from mlkem-native's x86_64 sources) are one read-only
block, `mlkem_native2_constants` (`mlkem_native2_constants.S`, with the
layout in `mlkem_native2_consts.h`, every field 32-byte aligned). The API
functions take its address RIP-relatively and pass it to the functions
below.

## ABI

All functions follow the System V ABI. With `WINDOWS_ABI` (the Microsoft
x64 ABI), each of the 15 API functions becomes a wrapper that saves rdi,
rsi and xmm6-xmm15, moves the arguments to their System V registers and
calls the System V code: everything below the API is the same System V
code in either case, so a Windows build assembles the per-level files with
`WINDOWS_ABI=1` and all the other files with `WINDOWS_ABI=0`. (The leaves
also have the usual `#if WINDOWS_ABI` prologues of s2n-bignum, for use on
their own.) Every global function starts with endbr64 (`_CET_ENDBR`), and
every function that uses ymm registers executes vzeroupper before it
returns. The code uses only VEX-encoded vector instructions (legacy SSE
instructions are slow after AVX code that leaves the upper halves of the
registers dirty, as the existing kernels do), and no PEXT (slow on AMD
Zen 2). The polynomial buffers of the frames are 32-byte aligned, as the
existing kernels require; the API functions take any alignment of their
arguments. The new functions are 32-byte aligned, like the existing
Keccak kernels, and no branch of their hot loops crosses or ends at a
32-byte boundary, which on cores with the microcode fix for Intel's JCC
erratum would make the loop run from the legacy decoders: their speed
does not depend on where they are linked.

## Building

None of these files is in the `OBJ` list of `../Makefile`, so they are not
in `libs2nbignum.a` (nor in `make proofs`); the objects are built with the
usual rule, e.g. `make mlkem_native2/mlkem768.o` in `x86`. The API for one
parameter set, `mlkemL.o`, needs the middle layer and the constants block
from here, the leaves in `../mlkem` and the two Keccak permutations in
`../sha3` (the list `MLKEM_NATIVE2_IMAGE_OBJ` of `../Makefile`).

## The image, for the proofs

The functions here call others (direct calls only), so their proofs will
be about the image of all the functions involved: the objects in
`MLKEM_NATIVE2_IMAGE_OBJ` of `../Makefile`, linked at address 0 by
`mlkem_native2_image.ld` into `mlkem_native2_image.elf` (`make
mlkem_native2/mlkem_native2_image.elf` in `x86`, with GNU ld): the code of
the objects in that order, then the constants block (64-byte aligned) at
the end of the one section `.text`. The image has no relocations, every
call in it is a direct call, and the only RIP-relative references are the
18 to the constants block. It is all assembly, so there is no
stack-protector code: no instruction uses fs or gs, the segment registers
with a base in 64-bit mode (`check_noseg.sh` in the tests checks this),
and the only segment prefixes are the CS prefixes of some of the NOPs of
the padding.

The instructions of the image that are not in `../allowed_asm` (the
constant-time list) are the conditional branches (on public data only),
`rol` (in `sha3_keccak_f1600`), `vpmovmskb`, `vptest`, `setcc`, `popcnt`
(in the rejection sampler, whose input is public), the byte and word
forms of `mov`, `xor` and `movzx`, and the NOPs of the padding between
functions; all are decoded by the x86 model.

There are no AT&T versions of these files, or of the new leaves, in
`../../x86_att`.

## Where the speed comes from

On the machine measured, a Xeon Platinum 8259CL (Cascade Lake), the x4
permutation costs 1723 cycles for four states against 1260 for one with
the x1 permutation (and 1399 for mlkem-native's x1 in C): an x4 call pays
as soon as two of its lanes are useful, and so all Keccak work that can
run in parallel does. mlkem-native runs H(ek), J(z || c) and G on the x1
permutation; here H(ek), and in decapsulation J(z || c), run in lanes of
the x4 permutation beside the sampling of the matrix (at every level), and
noise is sampled in lanes the matrix leaves idle. For ML-KEM-768
decapsulation this means 13 x4 calls and 1 x1 call against 8 x4 and 22 x1.
Then the codecs, CBD, frommsg/tomsg and the key check, which
mlkem-native does in C, are in AVX2 assembly (frommsg 42 cycles against
1532, tomsg 44 against 399, CBD2 62 against 165, CBD3 106 against 308, the
key check for k = 3 159 against 651), and the rejection sampler is 1.8
times faster (213 cycles against 391 for 504 bytes, 48 bytes per step
while there is room for 32 more entries). The arithmetic
kernels are mlkem-native's.

Cycles per call (medians of 31 runs of 200 calls on one core, with the
clock measured after each run since it varies with the AVX frequency
licences; 2.69 GHz for these functions), against mlkem-native (main at
9b96caa1) built with clang 18 -O3 and its native backends (the fastest
of the builds tried):

| function | mlkem-native | here | change |
|---|---|---|---|
| mlkem512_keypair_derand | 24950 | 21884 | -12.3% |
| mlkem512_enc_derand | 29269 | 20474 | -30.0% |
| mlkem512_dec | 39724 | 22262 | -44.0% |
| mlkem512_check_pk | 421 | 105 | -75.1% |
| mlkem512_check_sk | 8717 | 7674 | -12.0% |
| mlkem768_keypair_derand | 43129 | 35613 | -17.4% |
| mlkem768_enc_derand | 46425 | 29220 | -37.1% |
| mlkem768_dec | 61619 | 35089 | -43.1% |
| mlkem768_check_pk | 649 | 141 | -78.3% |
| mlkem768_check_sk | 13028 | 11629 | -10.7% |
| mlkem1024_keypair_derand | 59056 | 52553 | -11.0% |
| mlkem1024_enc_derand | 64784 | 45568 | -29.7% |
| mlkem1024_dec | 84822 | 53900 | -36.5% |
| mlkem1024_check_pk | 885 | 183 | -79.3% |
| mlkem1024_check_sk | 17303 | 15496 | -10.4% |

Key generation gains least: its H(pk) is a serial tail on the x1
permutation, with nothing to run beside it.

Stack use, in bytes (keypair_derand, enc_derand, dec): 9824, 8768, 10432
for ML-KEM-512; 14176, 13416, 16416 for ML-KEM-768; 21312, 19304, 22568 for
ML-KEM-1024 (224 more through the Windows wrappers). The stack buffers
holding secrets are zeroed before returning.

## Constant time

Everything is constant-time in the secret data. The rejection sampling of
the matrix, and the scheduling around it, depend only on the public seed
rho; in key generation rho is computed from the secret d, and the build
for testing with valgrind (`MLKEM_CT_TESTING` defined when preprocessing
the per-level files) marks it public there with memcheck's client
request, as mlkem-native does with `MLK_CONFIG_CT_TESTING_ENABLED`. The
results of the key checks are public.

## Testing

The tests and benchmarks are in `../../tests/mlkem_native2` (see its
README), which run on x86_64 as on AArch64. They compare these functions
with mlkem-native's portable C on random and edge-case inputs, including
the rare paths (implicit rejection, invalid keys, the fourth block of
rejection sampling), check the KAT hashes and the ACVP and Wycheproof
vectors, run under memcheck with exact-size buffers and for constant time
with the secrets undefined, check the ABI (the System V callee-saved
registers and rsp, and for the Windows entries, called through
`ms_abi` function pointers, also rdi, rsi and xmm6-xmm15) and that no
secret is left on the stack, and check that every global function starts
with endbr64 (IBT cannot be enforced without CET).
