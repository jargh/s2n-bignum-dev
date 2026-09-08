# s2n-bignum API reference

This document describes the contract of every function in the
[s2n-bignum](https://github.com/awslabs/s2n-bignum) library: what it computes,
the sizes and layout of its buffers, the assumptions it makes about its inputs,
which arguments are allowed to alias one another, and any differences between
the ARM (aarch64) and x86 (x86-64) implementations.

It sits between the two other descriptions of the API:

* the one-line comments in
  [`include/s2n-bignum.h`](https://github.com/awslabs/s2n-bignum/blob/main/include/s2n-bignum.h)
  and the comment banner at the top of each assembly (`.S`) file, which are
  convenient but terse; and
* the formal HOL Light specifications in the proof scripts
  (`{arm,x86}/proofs/*.ml`), which are the ultimate authority but require
  familiarity with the proof framework to read.

Everything here has been checked against those formal specifications — in
particular the aliasing and assumption fields are derived from the
`<function>_SUBROUTINE_CORRECT` theorems, which state the contract actually
proved of the shipping machine code. Where this document and the formal spec
appear to disagree, **the formal spec wins**; please report the discrepancy.

## How to read an entry

Each entry gives the C prototype followed by some of these fields:

* **Operation** — what the function computes, in mathematical terms.
* **Sizes** — the buffers it reads and writes, with their lengths. A length in
  brackets is a number of *elements*; unless marked otherwise an element is a
  64-bit word (`uint64_t`), so `z[4]` is a 256-bit little-endian bignum. Lengths
  that are themselves arguments (e.g. `x[m]`) are runtime parameters. `temporary`
  buffers are caller-allocated scratch space that the function uses internally;
  they carry no meaningful value on entry or return.
* **Assumptions** — preconditions the caller must guarantee. These are *not*
  checked at runtime; violating them voids the correctness guarantee (and for a
  few functions can cause out-of-bounds access). Mathematical preconditions such
  as "inputs already reduced modulo p" are stated in the Operation text.
* **Aliasing** — which buffers may point at the same or overlapping memory. See
  the legend below.
* **Availability** — whether the function exists on ARM, x86, or both, plus any
  genuine per-architecture differences in the prototype or behaviour.
* **Details** — extra explanation carried over from the source banner.

### Aliasing legend

Aliasing is the property most easily gotten wrong from the terse headers, so it
is called out explicitly. The phrasings used are:

* **No restrictions.** — the output(s) and inputs may coincide, partially
  overlap, or be disjoint in any combination; nothing is forbidden. (Typical of
  the fixed-size field and elliptic-curve routines, which read their inputs into
  registers or a private stack frame before writing any output.)
* **may be the same buffer as `x` (exact aliasing only — no partial overlap)** —
  in-place operation is supported (the output and `x` may be the identical
  pointer with identical length), but a *partial* overlap, where the buffers
  share some but not all memory, is forbidden. (Typical of the "linear"
  generic-size routines like `bignum_add`.)
* **must not overlap `x`** — the output must be entirely disjoint from that
  input; passing overlapping buffers voids the guarantee. (Typical of the
  generic-size multiply/reduce routines that revisit their inputs while writing
  output.)

An entry may combine these per buffer (e.g. in-place with one input but disjoint
from another). Where a function takes a **temporary** buffer, it must always be
distinct from every other argument, and this is stated explicitly. Distinct
output buffers must likewise be disjoint from each other.

Two things are *not* spelled out per entry because they hold universally and are
automatic at the C level: the output and temporary buffers must not overlap the
function's own machine code, and (on the routines that use one) the stack frame
below the stack pointer is private to the call. "No restrictions" is about the
caller-visible input and output buffers.

Two global rules hold for every function and are not repeated per entry:

* The code region itself must not overlap any output or temporary buffer (you
  cannot ask a function to overwrite its own machine code). Inputs, being
  read-only, may — pathologically — lie in the code region.
* On ARM, and for the routines that use a stack frame, the stack pointer must be
  16-byte aligned on entry (the standard AArch64 requirement).

## Conventions and global assumptions

* **Number representation.** Bignums are little-endian arrays of 64-bit "digits"
  (`uint64_t`). A `k`-digit bignum holds a value in `[0, 2^(64k))`. Sizes are
  nominal and fixed by the caller; functions never allocate, never resize, and
  never strip leading zeros. Results that do not fit the output width are
  truncated modulo `2^(64k)` (a top carry is returned separately where the API
  provides for it).
* **Constant-time behaviour.** Every function is constant-time — its instruction
  trace and memory-access pattern depend only on the *sizes* of its arguments,
  never on their values — with a single, deliberately named exception:
  `mlkem_rej_uniform_VARIABLE_TIME` (and the analogous ML-DSA `*_VARIABLE_TIME`
  routines). Those are rejection samplers whose running time depends on the input
  data by design.
* **ABI.** Functions use the standard calling convention for their architecture
  (AArch64 AAPCS; System V AMD64 on x86). On x86 the routines additionally provide
  a Windows-ABI entry path; that is below the level of this document and does not
  change any of the contracts described here. Register-level argument mappings are
  in each source banner.
* **`_alt` variants.** Many functions have an `_alt` sibling with identical
  mathematical behaviour but different performance characteristics. On x86 the
  non-`alt` form uses the BMI2/ADX extensions (`MULX`, `ADCX`, `ADOX`) and the
  `_alt` form avoids them for older CPUs; on ARM the `_alt` form targets cores
  with higher multiplier throughput. The contract (sizes, assumptions, aliasing)
  is the same for both unless an entry says otherwise. On ARM, several `_alt` and
  byte-order entry points are in fact aliases of the base routine (one piece of
  code exported under two names).
* **Execution environment.** Alignment checking must be disabled (x86 `AC`,
  ARM `SCTLR.A`); passing correctly-typed C pointers satisfies the alignment the
  code needs. The machine is assumed to be little-endian and in 64-bit mode.

### A note on ML-KEM and ML-DSA

The `mlkem_*`, `mldsa_*`, and `sha3_*` routines (post-quantum building blocks,
largely shared with the [mlkem-native](https://github.com/pq-code-package/mlkem-native)
project) do not follow all of the conventions above:

* They operate on arrays of signed 16-bit (`int16_t`, ML-KEM) or 32-bit
  (`int32_t`, ML-DSA) coefficients, not 64-bit bignum digits.
* Several take an extra pointer to a fixed table of constants (twiddle factors,
  `qdata`, rejection tables) that must point at the specific table the routine
  expects — see the source banner for the exact table.
* The ARM and x86 code for these was developed somewhat independently, so the
  ARM and x86 prototypes for a given operation sometimes **differ**, and the
  header disambiguates with `_arm` / `_x86` suffixes on some names. The two are
  documented as the separate functions they are.
* Some ARM SHA-3 routines require the ARMv8.2 `sha3` instruction-set extension
  and will not run on cores lacking it; all other s2n-bignum ARM code runs on any
  ARMv8-A core.

---

## Alphabetical index

[`aes_xts_decrypt`](#aes_xts_decrypt) · [`aes_xts_encrypt`](#aes_xts_encrypt) · [`bignum_add`](#bignum_add) · [`bignum_add_p25519`](#bignum_add_p25519) · [`bignum_add_p256`](#bignum_add_p256) · [`bignum_add_p256k1`](#bignum_add_p256k1)<br>
[`bignum_add_p384`](#bignum_add_p384) · [`bignum_add_p521`](#bignum_add_p521) · [`bignum_add_sm2`](#bignum_add_sm2) · [`bignum_amontifier`](#bignum_amontifier) · [`bignum_amontmul`](#bignum_amontmul) · [`bignum_amontredc`](#bignum_amontredc)<br>
[`bignum_amontsqr`](#bignum_amontsqr) · [`bignum_bigendian_4`](#bignum_bigendian_4) · [`bignum_bigendian_6`](#bignum_bigendian_6) · [`bignum_bitfield`](#bignum_bitfield) · [`bignum_bitsize`](#bignum_bitsize) · [`bignum_cdiv`](#bignum_cdiv)<br>
[`bignum_cdiv_exact`](#bignum_cdiv_exact) · [`bignum_cld`](#bignum_cld) · [`bignum_clz`](#bignum_clz) · [`bignum_cmadd`](#bignum_cmadd) · [`bignum_cmnegadd`](#bignum_cmnegadd) · [`bignum_cmod`](#bignum_cmod)<br>
[`bignum_cmul`](#bignum_cmul) · [`bignum_cmul_p25519`](#bignum_cmul_p25519) · [`bignum_cmul_p25519_alt`](#bignum_cmul_p25519_alt) · [`bignum_cmul_p256`](#bignum_cmul_p256) · [`bignum_cmul_p256_alt`](#bignum_cmul_p256_alt) · [`bignum_cmul_p256k1`](#bignum_cmul_p256k1)<br>
[`bignum_cmul_p256k1_alt`](#bignum_cmul_p256k1_alt) · [`bignum_cmul_p384`](#bignum_cmul_p384) · [`bignum_cmul_p384_alt`](#bignum_cmul_p384_alt) · [`bignum_cmul_p521`](#bignum_cmul_p521) · [`bignum_cmul_p521_alt`](#bignum_cmul_p521_alt) · [`bignum_cmul_sm2`](#bignum_cmul_sm2)<br>
[`bignum_cmul_sm2_alt`](#bignum_cmul_sm2_alt) · [`bignum_coprime`](#bignum_coprime) · [`bignum_copy`](#bignum_copy) · [`bignum_copy_row_from_table`](#bignum_copy_row_from_table) · [`bignum_copy_row_from_table_16`](#bignum_copy_row_from_table_16) · [`bignum_copy_row_from_table_32`](#bignum_copy_row_from_table_32)<br>
[`bignum_copy_row_from_table_8n`](#bignum_copy_row_from_table_8n) · [`bignum_ctd`](#bignum_ctd) · [`bignum_ctz`](#bignum_ctz) · [`bignum_deamont_p256`](#bignum_deamont_p256) · [`bignum_deamont_p256_alt`](#bignum_deamont_p256_alt) · [`bignum_deamont_p256k1`](#bignum_deamont_p256k1)<br>
[`bignum_deamont_p384`](#bignum_deamont_p384) · [`bignum_deamont_p384_alt`](#bignum_deamont_p384_alt) · [`bignum_deamont_p521`](#bignum_deamont_p521) · [`bignum_deamont_sm2`](#bignum_deamont_sm2) · [`bignum_demont`](#bignum_demont) · [`bignum_demont_p256`](#bignum_demont_p256)<br>
[`bignum_demont_p256_alt`](#bignum_demont_p256_alt) · [`bignum_demont_p256k1`](#bignum_demont_p256k1) · [`bignum_demont_p384`](#bignum_demont_p384) · [`bignum_demont_p384_alt`](#bignum_demont_p384_alt) · [`bignum_demont_p521`](#bignum_demont_p521) · [`bignum_demont_sm2`](#bignum_demont_sm2)<br>
[`bignum_digit`](#bignum_digit) · [`bignum_digitsize`](#bignum_digitsize) · [`bignum_divmod10`](#bignum_divmod10) · [`bignum_double_p25519`](#bignum_double_p25519) · [`bignum_double_p256`](#bignum_double_p256) · [`bignum_double_p256k1`](#bignum_double_p256k1)<br>
[`bignum_double_p384`](#bignum_double_p384) · [`bignum_double_p521`](#bignum_double_p521) · [`bignum_double_sm2`](#bignum_double_sm2) · [`bignum_emontredc`](#bignum_emontredc) · [`bignum_emontredc_8n`](#bignum_emontredc_8n) · [`bignum_emontredc_8n_cdiff`](#bignum_emontredc_8n_cdiff)<br>
[`bignum_eq`](#bignum_eq) · [`bignum_even`](#bignum_even) · [`bignum_frombebytes_4`](#bignum_frombebytes_4) · [`bignum_frombebytes_6`](#bignum_frombebytes_6) · [`bignum_fromlebytes_4`](#bignum_fromlebytes_4) · [`bignum_fromlebytes_6`](#bignum_fromlebytes_6)<br>
[`bignum_fromlebytes_p521`](#bignum_fromlebytes_p521) · [`bignum_ge`](#bignum_ge) · [`bignum_gt`](#bignum_gt) · [`bignum_half_p256`](#bignum_half_p256) · [`bignum_half_p256k1`](#bignum_half_p256k1) · [`bignum_half_p384`](#bignum_half_p384)<br>
[`bignum_half_p521`](#bignum_half_p521) · [`bignum_half_sm2`](#bignum_half_sm2) · [`bignum_inv_p25519`](#bignum_inv_p25519) · [`bignum_inv_p256`](#bignum_inv_p256) · [`bignum_inv_p384`](#bignum_inv_p384) · [`bignum_inv_p521`](#bignum_inv_p521)<br>
[`bignum_inv_sm2`](#bignum_inv_sm2) · [`bignum_invsqrt_p25519`](#bignum_invsqrt_p25519) · [`bignum_invsqrt_p25519_alt`](#bignum_invsqrt_p25519_alt) · [`bignum_iszero`](#bignum_iszero) · [`bignum_kmul_16_32`](#bignum_kmul_16_32) · [`bignum_kmul_32_64`](#bignum_kmul_32_64)<br>
[`bignum_ksqr_16_32`](#bignum_ksqr_16_32) · [`bignum_ksqr_32_64`](#bignum_ksqr_32_64) · [`bignum_le`](#bignum_le) · [`bignum_littleendian_4`](#bignum_littleendian_4) · [`bignum_littleendian_6`](#bignum_littleendian_6) · [`bignum_lt`](#bignum_lt)<br>
[`bignum_madd`](#bignum_madd) · [`bignum_madd_n25519`](#bignum_madd_n25519) · [`bignum_madd_n25519_alt`](#bignum_madd_n25519_alt) · [`bignum_mod_m25519`](#bignum_mod_m25519) · [`bignum_mod_m25519_4`](#bignum_mod_m25519_4) · [`bignum_mod_n25519`](#bignum_mod_n25519)<br>
[`bignum_mod_n25519_4`](#bignum_mod_n25519_4) · [`bignum_mod_n256`](#bignum_mod_n256) · [`bignum_mod_n256_4`](#bignum_mod_n256_4) · [`bignum_mod_n256_alt`](#bignum_mod_n256_alt) · [`bignum_mod_n256k1`](#bignum_mod_n256k1) · [`bignum_mod_n256k1_4`](#bignum_mod_n256k1_4)<br>
[`bignum_mod_n384`](#bignum_mod_n384) · [`bignum_mod_n384_6`](#bignum_mod_n384_6) · [`bignum_mod_n384_alt`](#bignum_mod_n384_alt) · [`bignum_mod_n521_9`](#bignum_mod_n521_9) · [`bignum_mod_n521_9_alt`](#bignum_mod_n521_9_alt) · [`bignum_mod_nsm2`](#bignum_mod_nsm2)<br>
[`bignum_mod_nsm2_4`](#bignum_mod_nsm2_4) · [`bignum_mod_nsm2_alt`](#bignum_mod_nsm2_alt) · [`bignum_mod_p25519_4`](#bignum_mod_p25519_4) · [`bignum_mod_p256`](#bignum_mod_p256) · [`bignum_mod_p256_4`](#bignum_mod_p256_4) · [`bignum_mod_p256_alt`](#bignum_mod_p256_alt)<br>
[`bignum_mod_p256k1`](#bignum_mod_p256k1) · [`bignum_mod_p256k1_4`](#bignum_mod_p256k1_4) · [`bignum_mod_p384`](#bignum_mod_p384) · [`bignum_mod_p384_6`](#bignum_mod_p384_6) · [`bignum_mod_p384_alt`](#bignum_mod_p384_alt) · [`bignum_mod_p521_9`](#bignum_mod_p521_9)<br>
[`bignum_mod_sm2`](#bignum_mod_sm2) · [`bignum_mod_sm2_4`](#bignum_mod_sm2_4) · [`bignum_modadd`](#bignum_modadd) · [`bignum_moddouble`](#bignum_moddouble) · [`bignum_modexp`](#bignum_modexp) · [`bignum_modifier`](#bignum_modifier)<br>
[`bignum_modinv`](#bignum_modinv) · [`bignum_modoptneg`](#bignum_modoptneg) · [`bignum_modsub`](#bignum_modsub) · [`bignum_montifier`](#bignum_montifier) · [`bignum_montinv_p256`](#bignum_montinv_p256) · [`bignum_montinv_p384`](#bignum_montinv_p384)<br>
[`bignum_montinv_sm2`](#bignum_montinv_sm2) · [`bignum_montmul`](#bignum_montmul) · [`bignum_montmul_p256`](#bignum_montmul_p256) · [`bignum_montmul_p256_alt`](#bignum_montmul_p256_alt) · [`bignum_montmul_p256k1`](#bignum_montmul_p256k1) · [`bignum_montmul_p256k1_alt`](#bignum_montmul_p256k1_alt)<br>
[`bignum_montmul_p384`](#bignum_montmul_p384) · [`bignum_montmul_p384_alt`](#bignum_montmul_p384_alt) · [`bignum_montmul_p521`](#bignum_montmul_p521) · [`bignum_montmul_p521_alt`](#bignum_montmul_p521_alt) · [`bignum_montmul_sm2`](#bignum_montmul_sm2) · [`bignum_montmul_sm2_alt`](#bignum_montmul_sm2_alt)<br>
[`bignum_montredc`](#bignum_montredc) · [`bignum_montsqr`](#bignum_montsqr) · [`bignum_montsqr_p256`](#bignum_montsqr_p256) · [`bignum_montsqr_p256_alt`](#bignum_montsqr_p256_alt) · [`bignum_montsqr_p256k1`](#bignum_montsqr_p256k1) · [`bignum_montsqr_p256k1_alt`](#bignum_montsqr_p256k1_alt)<br>
[`bignum_montsqr_p384`](#bignum_montsqr_p384) · [`bignum_montsqr_p384_alt`](#bignum_montsqr_p384_alt) · [`bignum_montsqr_p521`](#bignum_montsqr_p521) · [`bignum_montsqr_p521_alt`](#bignum_montsqr_p521_alt) · [`bignum_montsqr_sm2`](#bignum_montsqr_sm2) · [`bignum_montsqr_sm2_alt`](#bignum_montsqr_sm2_alt)<br>
[`bignum_mul`](#bignum_mul) · [`bignum_mul_4_8`](#bignum_mul_4_8) · [`bignum_mul_4_8_alt`](#bignum_mul_4_8_alt) · [`bignum_mul_6_12`](#bignum_mul_6_12) · [`bignum_mul_6_12_alt`](#bignum_mul_6_12_alt) · [`bignum_mul_8_16`](#bignum_mul_8_16)<br>
[`bignum_mul_8_16_alt`](#bignum_mul_8_16_alt) · [`bignum_mul_p25519`](#bignum_mul_p25519) · [`bignum_mul_p25519_alt`](#bignum_mul_p25519_alt) · [`bignum_mul_p256k1`](#bignum_mul_p256k1) · [`bignum_mul_p256k1_alt`](#bignum_mul_p256k1_alt) · [`bignum_mul_p521`](#bignum_mul_p521)<br>
[`bignum_mul_p521_alt`](#bignum_mul_p521_alt) · [`bignum_muladd10`](#bignum_muladd10) · [`bignum_mux`](#bignum_mux) · [`bignum_mux16`](#bignum_mux16) · [`bignum_mux_4`](#bignum_mux_4) · [`bignum_mux_6`](#bignum_mux_6)<br>
[`bignum_neg_p25519`](#bignum_neg_p25519) · [`bignum_neg_p256`](#bignum_neg_p256) · [`bignum_neg_p256k1`](#bignum_neg_p256k1) · [`bignum_neg_p384`](#bignum_neg_p384) · [`bignum_neg_p521`](#bignum_neg_p521) · [`bignum_neg_sm2`](#bignum_neg_sm2)<br>
[`bignum_negmodinv`](#bignum_negmodinv) · [`bignum_nonzero`](#bignum_nonzero) · [`bignum_nonzero_4`](#bignum_nonzero_4) · [`bignum_nonzero_6`](#bignum_nonzero_6) · [`bignum_normalize`](#bignum_normalize) · [`bignum_odd`](#bignum_odd)<br>
[`bignum_of_word`](#bignum_of_word) · [`bignum_optadd`](#bignum_optadd) · [`bignum_optneg`](#bignum_optneg) · [`bignum_optneg_p25519`](#bignum_optneg_p25519) · [`bignum_optneg_p256`](#bignum_optneg_p256) · [`bignum_optneg_p256k1`](#bignum_optneg_p256k1)<br>
[`bignum_optneg_p384`](#bignum_optneg_p384) · [`bignum_optneg_p521`](#bignum_optneg_p521) · [`bignum_optneg_sm2`](#bignum_optneg_sm2) · [`bignum_optsub`](#bignum_optsub) · [`bignum_optsubadd`](#bignum_optsubadd) · [`bignum_pow2`](#bignum_pow2)<br>
[`bignum_shl_small`](#bignum_shl_small) · [`bignum_shr_small`](#bignum_shr_small) · [`bignum_sqr`](#bignum_sqr) · [`bignum_sqr_4_8`](#bignum_sqr_4_8) · [`bignum_sqr_4_8_alt`](#bignum_sqr_4_8_alt) · [`bignum_sqr_6_12`](#bignum_sqr_6_12)<br>
[`bignum_sqr_6_12_alt`](#bignum_sqr_6_12_alt) · [`bignum_sqr_8_16`](#bignum_sqr_8_16) · [`bignum_sqr_8_16_alt`](#bignum_sqr_8_16_alt) · [`bignum_sqr_p25519`](#bignum_sqr_p25519) · [`bignum_sqr_p25519_alt`](#bignum_sqr_p25519_alt) · [`bignum_sqr_p256k1`](#bignum_sqr_p256k1)<br>
[`bignum_sqr_p256k1_alt`](#bignum_sqr_p256k1_alt) · [`bignum_sqr_p521`](#bignum_sqr_p521) · [`bignum_sqr_p521_alt`](#bignum_sqr_p521_alt) · [`bignum_sqrt_p25519`](#bignum_sqrt_p25519) · [`bignum_sqrt_p25519_alt`](#bignum_sqrt_p25519_alt) · [`bignum_sub`](#bignum_sub)<br>
[`bignum_sub_p25519`](#bignum_sub_p25519) · [`bignum_sub_p256`](#bignum_sub_p256) · [`bignum_sub_p256k1`](#bignum_sub_p256k1) · [`bignum_sub_p384`](#bignum_sub_p384) · [`bignum_sub_p521`](#bignum_sub_p521) · [`bignum_sub_sm2`](#bignum_sub_sm2)<br>
[`bignum_tobebytes_4`](#bignum_tobebytes_4) · [`bignum_tobebytes_6`](#bignum_tobebytes_6) · [`bignum_tolebytes_4`](#bignum_tolebytes_4) · [`bignum_tolebytes_6`](#bignum_tolebytes_6) · [`bignum_tolebytes_p521`](#bignum_tolebytes_p521) · [`bignum_tomont_p256`](#bignum_tomont_p256)<br>
[`bignum_tomont_p256_alt`](#bignum_tomont_p256_alt) · [`bignum_tomont_p256k1`](#bignum_tomont_p256k1) · [`bignum_tomont_p256k1_alt`](#bignum_tomont_p256k1_alt) · [`bignum_tomont_p384`](#bignum_tomont_p384) · [`bignum_tomont_p384_alt`](#bignum_tomont_p384_alt) · [`bignum_tomont_p521`](#bignum_tomont_p521)<br>
[`bignum_tomont_sm2`](#bignum_tomont_sm2) · [`bignum_triple_p256`](#bignum_triple_p256) · [`bignum_triple_p256_alt`](#bignum_triple_p256_alt) · [`bignum_triple_p256k1`](#bignum_triple_p256k1) · [`bignum_triple_p256k1_alt`](#bignum_triple_p256k1_alt) · [`bignum_triple_p384`](#bignum_triple_p384)<br>
[`bignum_triple_p384_alt`](#bignum_triple_p384_alt) · [`bignum_triple_p521`](#bignum_triple_p521) · [`bignum_triple_p521_alt`](#bignum_triple_p521_alt) · [`bignum_triple_sm2`](#bignum_triple_sm2) · [`bignum_triple_sm2_alt`](#bignum_triple_sm2_alt) · [`curve25519_ladderstep`](#curve25519_ladderstep)<br>
[`curve25519_ladderstep_alt`](#curve25519_ladderstep_alt) · [`curve25519_pxscalarmul`](#curve25519_pxscalarmul) · [`curve25519_pxscalarmul_alt`](#curve25519_pxscalarmul_alt) · [`curve25519_x25519`](#curve25519_x25519) · [`curve25519_x25519_alt`](#curve25519_x25519_alt) · [`curve25519_x25519_byte`](#curve25519_x25519_byte)<br>
[`curve25519_x25519_byte_alt`](#curve25519_x25519_byte_alt) · [`curve25519_x25519base`](#curve25519_x25519base) · [`curve25519_x25519base_alt`](#curve25519_x25519base_alt) · [`curve25519_x25519base_byte`](#curve25519_x25519base_byte) · [`curve25519_x25519base_byte_alt`](#curve25519_x25519base_byte_alt) · [`edwards25519_decode`](#edwards25519_decode)<br>
[`edwards25519_decode_alt`](#edwards25519_decode_alt) · [`edwards25519_encode`](#edwards25519_encode) · [`edwards25519_epadd`](#edwards25519_epadd) · [`edwards25519_epadd_alt`](#edwards25519_epadd_alt) · [`edwards25519_epdouble`](#edwards25519_epdouble) · [`edwards25519_epdouble_alt`](#edwards25519_epdouble_alt)<br>
[`edwards25519_pdouble`](#edwards25519_pdouble) · [`edwards25519_pdouble_alt`](#edwards25519_pdouble_alt) · [`edwards25519_pepadd`](#edwards25519_pepadd) · [`edwards25519_pepadd_alt`](#edwards25519_pepadd_alt) · [`edwards25519_scalarmulbase`](#edwards25519_scalarmulbase) · [`edwards25519_scalarmulbase_alt`](#edwards25519_scalarmulbase_alt)<br>
[`edwards25519_scalarmuldouble`](#edwards25519_scalarmuldouble) · [`edwards25519_scalarmuldouble_alt`](#edwards25519_scalarmuldouble_alt) · [`mldsa_caddq`](#mldsa_caddq) · [`mldsa_chknorm`](#mldsa_chknorm) · [`mldsa_decompose_32`](#mldsa_decompose_32) · [`mldsa_decompose_88`](#mldsa_decompose_88)<br>
[`mldsa_intt`](#mldsa_intt) · [`mldsa_intt_arm`](#mldsa_intt_arm) · [`mldsa_ntt`](#mldsa_ntt) · [`mldsa_ntt_arm`](#mldsa_ntt_arm) · [`mldsa_nttunpack`](#mldsa_nttunpack) · [`mldsa_pointwise`](#mldsa_pointwise)<br>
[`mldsa_pointwise_acc_l4`](#mldsa_pointwise_acc_l4) · [`mldsa_pointwise_acc_l4_x86`](#mldsa_pointwise_acc_l4_x86) · [`mldsa_pointwise_acc_l5`](#mldsa_pointwise_acc_l5) · [`mldsa_pointwise_acc_l5_x86`](#mldsa_pointwise_acc_l5_x86) · [`mldsa_pointwise_acc_l7`](#mldsa_pointwise_acc_l7) · [`mldsa_pointwise_acc_l7_x86`](#mldsa_pointwise_acc_l7_x86)<br>
[`mldsa_pointwise_x86`](#mldsa_pointwise_x86) · [`mldsa_poly_use_hint_32`](#mldsa_poly_use_hint_32) · [`mldsa_poly_use_hint_88`](#mldsa_poly_use_hint_88) · [`mldsa_polyz_unpack_17_arm`](#mldsa_polyz_unpack_17_arm) · [`mldsa_polyz_unpack_19_arm`](#mldsa_polyz_unpack_19_arm) · [`mldsa_reduce`](#mldsa_reduce)<br>
[`mldsa_rej_uniform_VARIABLE_TIME`](#mldsa_rej_uniform_variable_time) · [`mldsa_rej_uniform_VARIABLE_TIME_x86`](#mldsa_rej_uniform_variable_time_x86) · [`mldsa_rej_uniform_eta2_VARIABLE_TIME`](#mldsa_rej_uniform_eta2_variable_time) · [`mldsa_rej_uniform_eta4_VARIABLE_TIME`](#mldsa_rej_uniform_eta4_variable_time) · [`mlkem_basemul_k2`](#mlkem_basemul_k2) · [`mlkem_basemul_k3`](#mlkem_basemul_k3)<br>
[`mlkem_basemul_k4`](#mlkem_basemul_k4) · [`mlkem_frombytes`](#mlkem_frombytes) · [`mlkem_intt`](#mlkem_intt) · [`mlkem_intt_x86`](#mlkem_intt_x86) · [`mlkem_mulcache_compute`](#mlkem_mulcache_compute) · [`mlkem_mulcache_compute_x86`](#mlkem_mulcache_compute_x86)<br>
[`mlkem_ntt`](#mlkem_ntt) · [`mlkem_ntt_x86`](#mlkem_ntt_x86) · [`mlkem_reduce`](#mlkem_reduce) · [`mlkem_rej_uniform_VARIABLE_TIME`](#mlkem_rej_uniform_variable_time) · [`mlkem_tobytes`](#mlkem_tobytes) · [`mlkem_tomont`](#mlkem_tomont)<br>
[`mlkem_unpack`](#mlkem_unpack) · [`p256_montjadd`](#p256_montjadd) · [`p256_montjadd_alt`](#p256_montjadd_alt) · [`p256_montjdouble`](#p256_montjdouble) · [`p256_montjdouble_alt`](#p256_montjdouble_alt) · [`p256_montjmixadd`](#p256_montjmixadd)<br>
[`p256_montjmixadd_alt`](#p256_montjmixadd_alt) · [`p256_montjscalarmul`](#p256_montjscalarmul) · [`p256_montjscalarmul_alt`](#p256_montjscalarmul_alt) · [`p256_scalarmul`](#p256_scalarmul) · [`p256_scalarmul_alt`](#p256_scalarmul_alt) · [`p256_scalarmulbase`](#p256_scalarmulbase)<br>
[`p256_scalarmulbase_alt`](#p256_scalarmulbase_alt) · [`p384_montjadd`](#p384_montjadd) · [`p384_montjadd_alt`](#p384_montjadd_alt) · [`p384_montjdouble`](#p384_montjdouble) · [`p384_montjdouble_alt`](#p384_montjdouble_alt) · [`p384_montjmixadd`](#p384_montjmixadd)<br>
[`p384_montjmixadd_alt`](#p384_montjmixadd_alt) · [`p384_montjscalarmul`](#p384_montjscalarmul) · [`p384_montjscalarmul_alt`](#p384_montjscalarmul_alt) · [`p521_jadd`](#p521_jadd) · [`p521_jadd_alt`](#p521_jadd_alt) · [`p521_jdouble`](#p521_jdouble)<br>
[`p521_jdouble_alt`](#p521_jdouble_alt) · [`p521_jmixadd`](#p521_jmixadd) · [`p521_jmixadd_alt`](#p521_jmixadd_alt) · [`p521_jscalarmul`](#p521_jscalarmul) · [`p521_jscalarmul_alt`](#p521_jscalarmul_alt) · [`secp256k1_jadd`](#secp256k1_jadd)<br>
[`secp256k1_jadd_alt`](#secp256k1_jadd_alt) · [`secp256k1_jdouble`](#secp256k1_jdouble) · [`secp256k1_jdouble_alt`](#secp256k1_jdouble_alt) · [`secp256k1_jmixadd`](#secp256k1_jmixadd) · [`secp256k1_jmixadd_alt`](#secp256k1_jmixadd_alt) · [`sha3_keccak2_f1600`](#sha3_keccak2_f1600)<br>
[`sha3_keccak2_f1600_alt`](#sha3_keccak2_f1600_alt) · [`sha3_keccak4_f1600`](#sha3_keccak4_f1600) · [`sha3_keccak4_f1600_alt`](#sha3_keccak4_f1600_alt) · [`sha3_keccak4_f1600_alt2`](#sha3_keccak4_f1600_alt2) · [`sha3_keccak_f1600`](#sha3_keccak_f1600) · [`sha3_keccak_f1600_alt`](#sha3_keccak_f1600_alt)<br>
[`sha3_keccak_f1600_alt2`](#sha3_keccak_f1600_alt2) · [`sm2_montjadd`](#sm2_montjadd) · [`sm2_montjadd_alt`](#sm2_montjadd_alt) · [`sm2_montjdouble`](#sm2_montjdouble) · [`sm2_montjdouble_alt`](#sm2_montjdouble_alt) · [`sm2_montjmixadd`](#sm2_montjmixadd)<br>
[`sm2_montjmixadd_alt`](#sm2_montjmixadd_alt) · [`sm2_montjscalarmul`](#sm2_montjscalarmul) · [`sm2_montjscalarmul_alt`](#sm2_montjscalarmul_alt) · [`word_bytereverse`](#word_bytereverse) · [`word_clz`](#word_clz) · [`word_ctz`](#word_ctz)<br>
[`word_divstep59`](#word_divstep59) · [`word_max`](#word_max) · [`word_min`](#word_min) · [`word_negmodinv`](#word_negmodinv) · [`word_popcount`](#word_popcount) · [`word_recip`](#word_recip)

---

## Functions

### `aes_xts_decrypt`

```c
void aes_xts_decrypt(const uint8_t *in, uint8_t *out, size_t length, const s2n_bignum_AES_KEY *key1, const s2n_bignum_AES_KEY *key2, const uint8_t iv[static 16]);
```

**Operation.** AES_XTS_DECRYPT (256-bit)

**Sizes.** inputs `in`[length] (bytes), `key1`[244] (bytes), `key2`[244] (bytes), `iv`[16] (bytes); output `out`[length] (bytes)

**Assumptions.** len >= 16; len <= 2^24.

**Aliasing.** No restrictions.

**Stack use.** ARM 96 bytes (below the stack pointer)

**Availability.** ARM only.

### `aes_xts_encrypt`

```c
void aes_xts_encrypt(const uint8_t *in, uint8_t *out, size_t length, const s2n_bignum_AES_KEY *key1, const s2n_bignum_AES_KEY *key2, const uint8_t iv[static 16]);
```

**Operation.** AES_XTS_ENCRYPT (256-bit)

**Sizes.** inputs `in`[length] (bytes), `key1`[244] (bytes), `key2`[244] (bytes), `iv`[16] (bytes); output `out`[length] (bytes)

**Assumptions.** len >= 16; len <= 2^24.

**Aliasing.** No restrictions.

**Stack use.** ARM 96 bytes (below the stack pointer)

**Availability.** ARM only.

### `bignum_add`

```c
uint64_t bignum_add(uint64_t p, uint64_t *z, uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Add, z := x + y

**Sizes.** inputs `x`[m], `y`[n]; output `z`[p]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Does the z := x + y operation, truncating modulo p words in general and returning a top carry (0 or 1) in the p'th place, only adding the input words below p (as well as m and n respectively) to get the sum and carry.

### `bignum_add_p25519`

```c
void bignum_add_p25519(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_add_p256`

```c
void bignum_add_p256(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Add modulo p_256, z := (x + y) mod p_256, assuming x and y reduced

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_add_p256k1`

```c
void bignum_add_p256k1(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Add modulo p_256k1, z := (x + y) mod p_256k1, assuming x and y reduced

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_add_p384`

```c
void bignum_add_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Add modulo p_384, z := (x + y) mod p_384, assuming x and y reduced

**Sizes.** inputs `x`[6], `y`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_add_p521`

```c
void bignum_add_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Add modulo p_521, z := (x + y) mod p_521, assuming x and y reduced

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_add_sm2`

```c
void bignum_add_sm2(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Add modulo p_sm2, z := (x + y) mod p_sm2, assuming x and y reduced

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_amontifier`

```c
void bignum_amontifier(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t *t);
```

**Operation.** Compute "amontification" constant z :== 2^{128k} (congruent mod m)

**Sizes.** inputs `m`[k]; output `z`[k]; temporary `t`[>=k]

**Aliasing.** Output `z` must not overlap `m`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This is called "amontifier" because any other value x can now be mapped into the almost-Montgomery domain with an almost-Montgomery multiplication by z.

### `bignum_amontmul`

```c
void bignum_amontmul(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *y, const uint64_t *m);
```

**Operation.** Almost-Montgomery multiply, z :== (x * y / 2^{64k}) (congruent mod m)

**Sizes.** inputs `x`[k], `y`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `y`, `m`.

**Stack use.** ARM none, x86 56 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z :== (x * y / 2^{64k}) mod m, meaning that the result, in the native size k, is congruent modulo m, but might not be fully reduced mod m. This is why it is called *almost* Montgomery multiplication.

### `bignum_amontredc`

```c
void bignum_amontredc(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, const uint64_t *m, uint64_t p);
```

**Operation.** Almost-Montgomery reduce, z :== (x' / 2^{64p}) (congruent mod m)

**Sizes.** inputs `x`[n], `m`[k]; output `z`[k]

**Assumptions.** p < 2^61; r < 2^61.

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap); must not overlap `m`.

**Stack use.** ARM none, x86 56 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does a :== (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general is the lowest (p+k) digits of x. That is, p-fold almost-Montgomery reduction w.r.t. a k-digit modulus m giving a k-digit answer.

### `bignum_amontsqr`

```c
void bignum_amontsqr(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *m);
```

**Operation.** Almost-Montgomery square, z :== (x^2 / 2^{64k}) (congruent mod m)

**Sizes.** inputs `x`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `m`.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z :== (x^2 / 2^{64k}) mod m, meaning that the result, in the native size k, is congruent modulo m, but might not be fully reduced mod m. This is why it is called *almost* Montgomery squaring.

### `bignum_bigendian_4`

```c
void bignum_bigendian_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert 4-digit (256-bit) bignum to/from big-endian form

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** The same function is given two other prototypes whose names reflect the treatment of one or other argument as a byte array rather than word array: The implementation works by loading in bytes and storing in words (i.e. stylistically it is "frombebytes"); in the more common little-endian usage of ARM, this is just byte reversal.

### `bignum_bigendian_6`

```c
void bignum_bigendian_6(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert 6-digit (384-bit) bignum to/from big-endian form

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** The same function is given two other prototypes whose names reflect the treatment of one or other argument as a byte array rather than word array: The implementation works by loading in bytes and storing in words (i.e. stylistically it is "frombebytes"); in the more common little-endian usage of ARM, this is just byte reversal.

### `bignum_bitfield`

```c
uint64_t bignum_bitfield(uint64_t k, const uint64_t *x, uint64_t n, uint64_t l);
```

**Operation.** Select bitfield starting at bit n with length l <= 64

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** One-word bitfield from a k-digit (digit=64 bits) bignum, in constant-time style. Bitfield starts at bit n and has length l, indexing from 0 (=LSB). Digits above the top are treated uniformly as zero, as usual. Since the result is returned in a single word, effectively we use l' = min(64,l) for the length.

### `bignum_bitsize`

```c
uint64_t bignum_bitsize(uint64_t k, const uint64_t *x);
```

**Operation.** Return size of bignum in bits

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is 0 In principle this has a precondition k < 2^58, but obviously that is always true in practice because of address space limitations.

### `bignum_cdiv`

```c
uint64_t bignum_cdiv(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, uint64_t m);
```

**Operation.** Divide by a single (nonzero) word, z := x / m and return x mod m

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := x / m" operation where x is n digits, result z is k. Truncates the quotient in general, but always (for nonzero m) returns the true remainder x mod m.

### `bignum_cdiv_exact`

```c
void bignum_cdiv_exact(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, uint64_t m);
```

**Operation.** Divide by a single word, z := x / m *when known to be exact*

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := x / m" operation where x is n digits and result z is k, *assuming* that m is nonzero and that the input x is in fact an exact multiple of m. (If this isn't known, use the general bignum_cdiv function instead.) In general the result is truncated to k digits.

### `bignum_cld`

```c
uint64_t bignum_cld(uint64_t k, const uint64_t *x);
```

**Operation.** Count leading zero digits (64-bit words)

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is k

### `bignum_clz`

```c
uint64_t bignum_clz(uint64_t k, const uint64_t *x);
```

**Operation.** Count leading zero bits

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is 64 * k In principle this has a precondition k < 2^58, but obviously that is always true in practice because of address space limitations

### `bignum_cmadd`

```c
uint64_t bignum_cmadd(uint64_t k, uint64_t *z, uint64_t c, uint64_t n, const uint64_t *y);
```

**Operation.** Multiply-add with single-word multiplier, z := z + c * y

**Sizes.** inputs `y`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := z + c * y" operation where y is n digits, result z is p. Truncates the result in general. The return value is a high/carry word that is meaningful when p = n + 1, or more generally when n <= p and the result fits in p + 1 digits. In these cases it gives the top digit of the (p + 1)-digit result.

### `bignum_cmnegadd`

```c
uint64_t bignum_cmnegadd(uint64_t k, uint64_t *z, uint64_t c, uint64_t n, const uint64_t *y);
```

**Operation.** Negated multiply-add with single-word multiplier, z := z - c * y

**Sizes.** inputs `y`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := z - c * y" operation where y is n digits, result z is p. Truncates the result in general. The return value is a high/carry word that is meaningful when n <= p. It is interpreted negatively as z' - 2^{64k} * return = z - c * y.

### `bignum_cmod`

```c
uint64_t bignum_cmod(uint64_t k, const uint64_t *x, uint64_t m);
```

**Operation.** Find bignum modulo a single word

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Returns x mod m, assuming m is nonzero.

### `bignum_cmul`

```c
uint64_t bignum_cmul(uint64_t k, uint64_t *z, uint64_t c, uint64_t n, const uint64_t *y);
```

**Operation.** Multiply by a single word, z := c * y

**Sizes.** inputs `y`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Does the "z := c * y" operation where y is n digits, result z is p. Truncates the result in general unless p >= n + 1. The return value is a high/carry word that is meaningful when p >= n as giving the high part of the result. Since this is always zero if p > n, it is mainly of interest in the special case p = n, i.e. where the source and destination have the same nominal size, when it gives the extra word of the full result.

### `bignum_cmul_p25519`

```c
void bignum_cmul_p25519(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_25519, z := (c * x) mod p_25519, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p25519_alt`

```c
void bignum_cmul_p25519_alt(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_25519, z := (c * x) mod p_25519, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p256`

```c
void bignum_cmul_p256(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_256, z := (c * x) mod p_256, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p256_alt`

```c
void bignum_cmul_p256_alt(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_256, z := (c * x) mod p_256, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p256k1`

```c
void bignum_cmul_p256k1(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_256k1, z := (c * x) mod p_256k1, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p256k1_alt`

```c
void bignum_cmul_p256k1_alt(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_256k1, z := (c * x) mod p_256k1, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_p384`

```c
void bignum_cmul_p384(uint64_t z[static 6], uint64_t c, const uint64_t x[static 6]);
```

**Operation.** Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[6]; output z[6]

### `bignum_cmul_p384_alt`

```c
void bignum_cmul_p384_alt(uint64_t z[static 6], uint64_t c, const uint64_t x[static 6]);
```

**Operation.** Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[6]; output z[6]

### `bignum_cmul_p521`

```c
void bignum_cmul_p521(uint64_t z[static 9], uint64_t c, const uint64_t x[static 9]);
```

**Operation.** Multiply by a single word modulo p_521, z := (c * x) mod p_521, assuming

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[9]; output z[9]

### `bignum_cmul_p521_alt`

```c
void bignum_cmul_p521_alt(uint64_t z[static 9], uint64_t c, const uint64_t x[static 9]);
```

**Operation.** Multiply by a single word modulo p_521, z := (c * x) mod p_521, assuming

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[9]; output z[9]

### `bignum_cmul_sm2`

```c
void bignum_cmul_sm2(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_sm2, z := (c * x) mod p_sm2, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_cmul_sm2_alt`

```c
void bignum_cmul_sm2_alt(uint64_t z[static 4], uint64_t c, const uint64_t x[static 4]);
```

**Operation.** Multiply by a single word modulo p_sm2, z := (c * x) mod p_sm2, assuming

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** x reduced Inputs c, x[4]; output z[4]

### `bignum_coprime`

```c
uint64_t bignum_coprime(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y, uint64_t *t);
```

**Operation.** Test bignums for coprimality, gcd(x,y) = 1

**Sizes.** inputs `x`[m], `y`[n]; temporary `t`[>=2*max(m,n)]

**Assumptions.** m < 2^57; n < 2^57.

**Stack use.** ARM 16 bytes, x86 96 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Test for whether two bignums are coprime (no common factor besides 1). This is equivalent to testing if their gcd is 1, but a bit faster than doing those two computations separately. Here bignum x is m digits long, y is n digits long and the temporary buffer t needs to be 2 * max(m,n) digits long. The return value is 1 if coprime(x,y) and 0 otherwise.

### `bignum_copy`

```c
void bignum_copy(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
```

**Operation.** Copy bignum with zero-extension or truncation, z := x

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_copy_row_from_table`

```c
void bignum_copy_row_from_table(uint64_t *z, const uint64_t *table, uint64_t height, uint64_t width, uint64_t idx);
```

**Operation.** Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]

**Sizes.** inputs `table`[height*width]; output `z`[width]

**Assumptions.** idx < height.

**Aliasing.** Output `z` must not overlap `table`.

**Availability.** ARM and x86.

**Details.** into z[0..width-1]. This function is constant-time with respect to the value of `idx`. This is achieved by reading the whole table and using the bit-masking to get the `idx`-th row.

### `bignum_copy_row_from_table_16`

```c
void bignum_copy_row_from_table_16(uint64_t *z, const uint64_t *table, uint64_t height, uint64_t idx);
```

**Operation.** Given table: uint64_t[height*16], copy table[idx*16...(idx+1)*16-1]

**Sizes.** inputs `table`[height*16]; output `z`[16]

**Assumptions.** idx < height.

**Aliasing.** Output `z` must not overlap `table`.

**Availability.** ARM only.

**Details.** into z[0..row-1]. This function is constant-time with respect to the value of `idx`. This is achieved by reading the whole table and using the bit-masking to get the `idx`-th row. Initial version written by Hanno Becker

### `bignum_copy_row_from_table_32`

```c
void bignum_copy_row_from_table_32(uint64_t *z, const uint64_t *table, uint64_t height, uint64_t idx);
```

**Operation.** Given table: uint64_t[height*32], copy table[idx*32...(idx+1)*32-1]

**Sizes.** inputs `table`[height*32]; output `z`[32]

**Assumptions.** idx < height.

**Aliasing.** Output `z` must not overlap `table`.

**Availability.** ARM only.

**Details.** into z[0..row-1]. This function is constant-time with respect to the value of `idx`. This is achieved by reading the whole table and using the bit-masking to get the `idx`-th row. Initial version written by Hanno Becker

### `bignum_copy_row_from_table_8n`

```c
void bignum_copy_row_from_table_8n(uint64_t *z, const uint64_t *table, uint64_t height, uint64_t width, uint64_t idx);
```

**Operation.** Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]

**Sizes.** inputs `table`[height*width]; output `z`[width]

**Assumptions.** width is a multiple of 8; idx < height.

**Aliasing.** Output `z` must not overlap `table`.

**Availability.** ARM only.

**Details.** into z[0..width-1]. width must be a multiple of 8. This function is constant-time with respect to the value of `idx`. This is achieved by reading the whole table and using the bit-masking to get the `idx`-th row.

### `bignum_ctd`

```c
uint64_t bignum_ctd(uint64_t k, const uint64_t *x);
```

**Operation.** Count trailing zero digits (64-bit words)

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is k

### `bignum_ctz`

```c
uint64_t bignum_ctz(uint64_t k, const uint64_t *x);
```

**Operation.** Count trailing zero bits

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is 64 * k In principle this has a precondition k < 2^58, but obviously that is always true in practice because of address space limitations

### `bignum_deamont_p256`

```c
void bignum_deamont_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from almost-Montgomery form, z := (x / 2^256) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Convert a 4-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 4-digit input will work, with no range restriction.

### `bignum_deamont_p256_alt`

```c
void bignum_deamont_p256_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from almost-Montgomery form, z := (x / 2^256) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Convert a 4-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 4-digit input will work, with no range restriction.

### `bignum_deamont_p256k1`

```c
void bignum_deamont_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from Montgomery form z := (x / 2^256) mod p_256k1,

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Convert a 4-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 4-digit input will work, with no range restriction.

### `bignum_deamont_p384`

```c
void bignum_deamont_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert from almost-Montgomery form, z := (x / 2^384) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Convert a 6-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 6-digit input will work, with no range restriction.

### `bignum_deamont_p384_alt`

```c
void bignum_deamont_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert from almost-Montgomery form, z := (x / 2^384) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Convert a 6-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 6-digit input will work, with no range restriction.

### `bignum_deamont_p521`

```c
void bignum_deamont_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Convert from Montgomery form z := (x / 2^576) mod p_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Convert a 9-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 9-digit input will work, with no range restriction.

### `bignum_deamont_sm2`

```c
void bignum_deamont_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from almost-Montgomery form, z := (x / 2^256) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Convert a 4-digit bignum x out of its (optionally almost) Montgomery form, "almost" meaning any 4-digit input will work, with no range restriction.

### `bignum_demont`

```c
void bignum_demont(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *m);
```

**Operation.** Convert from (almost-)Montgomery form z := (x / 2^{64k}) mod m

**Sizes.** inputs `x`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap); must not overlap `m`.

**Stack use.** ARM none, x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x / 2^{64k}) mod m, hence mapping out of Montgomery domain. In other words, this is a k-fold Montgomery reduction with same-size input. This can handle almost-Montgomery inputs, i.e. any k-digit bignum.

### `bignum_demont_p256`

```c
void bignum_demont_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from Montgomery form z := (x / 2^256) mod p_256, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_256 for correctness. If this is not the case, use the variant "bignum_deamont_p256" instead.

### `bignum_demont_p256_alt`

```c
void bignum_demont_p256_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from Montgomery form z := (x / 2^256) mod p_256, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_256 for correctness. If this is not the case, use the variant "bignum_deamont_p256" instead.

### `bignum_demont_p256k1`

```c
void bignum_demont_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from Montgomery form z := (x / 2^256) mod p_256k1,

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** assuming x reduced Input x[4]; output z[4] This assumes the input is < p_256k1 for correctness. If this is not the case, use the variant "bignum_deamont_p256k1" instead.

### `bignum_demont_p384`

```c
void bignum_demont_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert from Montgomery form z := (x / 2^384) mod p_384, assuming x reduced

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_384 for correctness. If this is not the case, use the variant "bignum_deamont_p384" instead.

### `bignum_demont_p384_alt`

```c
void bignum_demont_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert from Montgomery form z := (x / 2^384) mod p_384, assuming x reduced

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_384 for correctness. If this is not the case, use the variant "bignum_deamont_p384" instead.

### `bignum_demont_p521`

```c
void bignum_demont_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Convert from Montgomery form z := (x / 2^576) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_521 for correctness. If this is not the case, use the variant "bignum_deamont_p521" instead.

### `bignum_demont_sm2`

```c
void bignum_demont_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert from Montgomery form z := (x / 2^256) mod p_sm2, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** This assumes the input is < p_sm2 for correctness. If this is not the case, use the variant "bignum_deamont_sm2" instead.

### `bignum_digit`

```c
uint64_t bignum_digit(uint64_t k, const uint64_t *x, uint64_t n);
```

**Operation.** Select digit x[n]

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** n'th digit of a k-digit (digit=64 bits) bignum, in constant-time style. Indexing starts at 0, which is the least significant digit (little-endian). Returns zero if n >= k, i.e. we read a digit off the end of the bignum.

### `bignum_digitsize`

```c
uint64_t bignum_digitsize(uint64_t k, const uint64_t *x);
```

**Operation.** Return size of bignum in digits (64-bit word)

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** In the case of a zero bignum as input the result is 0

### `bignum_divmod10`

```c
uint64_t bignum_divmod10(uint64_t k, uint64_t *z);
```

**Operation.** Divide bignum by 10, returning remainder: z' := z div 10, return = z mod 10

**Sizes.** inputs `z`[k]; output `z`[k]

**Aliasing.** Operates in place on `z` (read and written in the same buffer).

**Availability.** ARM and x86.

### `bignum_double_p25519`

```c
void bignum_double_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Double modulo p_25519, z := (2 * x) mod p_25519, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_double_p256`

```c
void bignum_double_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Double modulo p_256, z := (2 * x) mod p_256, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_double_p256k1`

```c
void bignum_double_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Double modulo p_256k1, z := (2 * x) mod p_256k1, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_double_p384`

```c
void bignum_double_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Double modulo p_384, z := (2 * x) mod p_384, assuming x reduced

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_double_p521`

```c
void bignum_double_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Double modulo p_521, z := (2 * x) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_double_sm2`

```c
void bignum_double_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Double modulo p_sm2, z := (2 * x) mod p_sm2, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_emontredc`

```c
uint64_t bignum_emontredc(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t w);
```

**Operation.** Extended Montgomery reduce, returning results in input-output buffer

**Sizes.** inputs `z`[2*k], `m`[k]; output `z`[2*k]

**Aliasing.** Output `z` must not overlap `m`.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Assumes that z initially holds a 2k-digit bignum z_0, m is a k-digit odd bignum and m * w == -1 (mod 2^64). This function also uses z for the output as well as returning a carry c of 0 or 1. This encodes two numbers: in the lower half of the z buffer we have q = z[0..k-1], while the upper half together with the carry gives r = 2^{64k}*c + z[k..2k-1]. These values satisfy z_0 + q * m = 2^{64k} * r, i.e. r gives a raw (unreduced) Montgomery reduction while q gives the multiplier that was used. Another way of thinking of it is that if z' is the output z with the lower half replaced with zeros, then z_0 + q * m = 2^{128k} * c + z'.

### `bignum_emontredc_8n`

```c
uint64_t bignum_emontredc_8n(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t w);
```

**Operation.** Extended Montgomery reduce in 8-digit blocks, results in input-output buffer

**Sizes.** inputs `z`[2*k], `m`[k]; output `z`[2*k]

**Assumptions.** k is a multiple of 8.

**Aliasing.** Output `z` must not overlap `m`.

**Stack use.** ARM 112 bytes, x86 80 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Functionally equivalent to bignum_emontredc (see that file for more detail). But in general assumes that the input k is a multiple of 8. bignum_emontredc_8n is a vectorized version of unopt/bignum_emontredc_8n_base.

### `bignum_emontredc_8n_cdiff`

```c
uint64_t bignum_emontredc_8n_cdiff(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t w, uint64_t *m_precalc);
```

**Operation.** Extend Montgomery reduce in 8-digit blocks, uses an extra storage to

**Sizes.** inputs `z`[2*k], `m`[k]; output `z`[2*k]; temporary `m_precalc`[12*(k/4-1)]

**Assumptions.** k is a multiple of 8; k < 2^32; 16 <= k.

**Aliasing.** No restrictions on input/output overlap. Temporary buffer `m_precalc` must be distinct from all other arguments.

**Availability.** ARM only.

**Details.** temporarily cache multiplied differences appearing in ADK. Results are stored in input-output buffer (z). k must be divisible by 8 and not smaller than 16. Inputs z[2*k], m[k], w; Outputs function return (extra result bit) and z[2*k] Temporary buffer m_precalc[12*(k/4-1)] returns X0

### `bignum_eq`

```c
uint64_t bignum_eq(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Test bignums for equality, x = y

**Sizes.** inputs `x`[m], `y`[n]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_even`

```c
uint64_t bignum_even(uint64_t k, const uint64_t *x);
```

**Operation.** Test bignum for even-ness

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_frombebytes_4`

```c
void bignum_frombebytes_4(uint64_t z[static 4], const uint8_t x[static 32]);
```

**Operation.** Convert 4-digit (256-bit) bignum from big-endian bytes

**Sizes.** inputs `x`[32] (bytes); output `z`[4]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_frombebytes_6`

```c
void bignum_frombebytes_6(uint64_t z[static 6], const uint8_t x[static 48]);
```

**Operation.** Convert 6-digit (384-bit) bignum from big-endian bytes

**Sizes.** inputs `x`[48] (bytes); output `z`[6]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_fromlebytes_4`

```c
void bignum_fromlebytes_4(uint64_t z[static 4], const uint8_t x[static 32]);
```

**Operation.** Convert 4-digit (256-bit) bignum from little-endian bytes

**Sizes.** inputs `x`[32] (bytes); output `z`[4]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_fromlebytes_6`

```c
void bignum_fromlebytes_6(uint64_t z[static 6], const uint8_t x[static 48]);
```

**Operation.** Convert 6-digit (384-bit) bignum from little-endian bytes

**Sizes.** inputs `x`[48] (bytes); output `z`[6]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_fromlebytes_p521`

```c
void bignum_fromlebytes_p521(uint64_t z[static 9],const uint8_t x[static 66]);
```

**Operation.** Convert little-endian bytes to 9-digit 528-bit bignum

**Sizes.** inputs `x`[66] (bytes); output `z`[9]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** The result will be < 2^528 since it is translated from 66 bytes. It is mainly intended for inputs x < p_521 < 2^521 < 2^528.

### `bignum_ge`

```c
uint64_t bignum_ge(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Compare bignums, x >= y

**Sizes.** inputs `x`[m], `y`[n]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_gt`

```c
uint64_t bignum_gt(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Compare bignums, x > y

**Sizes.** inputs `x`[m], `y`[n]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_half_p256`

```c
void bignum_half_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Halve modulo p_256, z := (x / 2) mod p_256, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_half_p256k1`

```c
void bignum_half_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Halve modulo p_256k1, z := (x / 2) mod p_256k1, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_half_p384`

```c
void bignum_half_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Halve modulo p_384, z := (x / 2) mod p_384, assuming x reduced

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_half_p521`

```c
void bignum_half_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Halve modulo p_521, z := (x / 2) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_half_sm2`

```c
void bignum_half_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Halve modulo p_sm2, z := (x / 2) mod p_sm2, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_inv_p25519`

```c
void bignum_inv_p25519(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Modular inverse modulo p_25519 = 2^255 - 19

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 160 bytes, x86 256 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Assuming the 4-digit input x is coprime to p_25519, i.e. is not divisible by it, returns z < p_25519 such that x * z == 1 (mod p_25519). Note that x does not need to be reduced modulo p_25519, but the output always is.

### `bignum_inv_p256`

```c
void bignum_inv_p256(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Modular inverse modulo p_256 = 2^256 - 2^224 + 2^192 + 2^96 - 1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 288 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 4-digit input x is coprime to p_256, i.e. is not divisible by it, returns z < p_256 such that x * z == 1 (mod p_256). Note that x does not need to be reduced modulo p_256, but the output always is. If the input is divisible (i.e. is 0 or p_256), then there can be no modular inverse and z = 0 is returned.

### `bignum_inv_p384`

```c
void bignum_inv_p384(uint64_t z[static 6],const uint64_t x[static 6]);
```

**Operation.** Modular inverse modulo p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM 304 bytes, x86 384 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 6-digit input x is coprime to p_384, i.e. is not divisible by it, returns z < p_384 such that x * z == 1 (mod p_384). Note that x does not need to be reduced modulo p_384, but the output always is. If the input is divisible (i.e. is 0 or p_384), then there can be no modular inverse and z = 0 is returned.

### `bignum_inv_p521`

```c
void bignum_inv_p521(uint64_t z[static 9],const uint64_t x[static 9]);
```

**Operation.** Modular inverse modulo p_521 =  2^521 - 1

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 320 bytes, x86 408 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Assuming the 9-digit input x is coprime to p_521, i.e. is not divisible by it, returns z < p_521 such that x * z == 1 (mod p_521). Note that x does not need to be reduced modulo p_521, but the output always is.

### `bignum_inv_sm2`

```c
void bignum_inv_sm2(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Modular inverse modulo p_sm2 = 2^256 - 2^224 - 2^96 + 2^64 - 1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 288 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 4-digit input x is coprime to p_sm2, i.e. is not divisible by it, returns z < p_sm2 such that x * z == 1 (mod p_sm2). Note that x does not need to be reduced modulo p_sm2, but the output always is. If the input is divisible (i.e. is 0 or p_sm2), then there can be no modular inverse and z = 0 is returned.

### `bignum_invsqrt_p25519`

```c
int64_t bignum_invsqrt_p25519(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Inverse square root modulo p_25519 = 2^255 - 19

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a 4-digit input x, returns a modular inverse square root mod p_25519, i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The inverse square root z is chosen so that its LSB is even (note that p_25519-z is another possibility). The function return is the Legendre/Jacobi symbol (x//p_25519), which indicates whether indeed x has a modular inverse square root and hence whether the result is meaningful: 0: x is divisible by p_25519 so trivially there is no inverse square root +1: x is coprime to p_25519 and z is indeed an inverse square root -1: x is coprime to p_25519 but there is no (inverse or direct) square root

### `bignum_invsqrt_p25519_alt`

```c
int64_t bignum_invsqrt_p25519_alt(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Inverse square root modulo p_25519 = 2^255 - 19

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a 4-digit input x, returns a modular inverse square root mod p_25519, i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The inverse square root z is chosen so that its LSB is even (note that p_25519-z is another possibility). The function return is the Legendre/Jacobi symbol (x//p_25519), which indicates whether indeed x has a modular inverse square root and hence whether the result is meaningful: 0: x is divisible by p_25519 so trivially there is no inverse square root +1: x is coprime to p_25519 and z is indeed an inverse square root -1: x is coprime to p_25519 but there is no (inverse or direct) square root

### `bignum_iszero`

```c
uint64_t bignum_iszero(uint64_t k, const uint64_t *x);
```

**Operation.** Test bignum for zero-ness, x = 0

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_kmul_16_32`

```c
void bignum_kmul_16_32(uint64_t z[static 32], const uint64_t x[static 16], const uint64_t y[static 16], uint64_t t[static 32]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[16], `y`[16]; output `z`[32]; temporary `t`[>=32]

**Aliasing.** Output `z` must not overlap `x`, `y`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM 96 bytes, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86. On x86 the temporary-buffer argument `t` is unused (retained only for API compatibility with ARM).

**Details.** This is a Karatsuba-style function multiplying half-sized results internally and using temporary buffer t for intermediate results.

### `bignum_kmul_32_64`

```c
void bignum_kmul_32_64(uint64_t z[static 64], const uint64_t x[static 32], const uint64_t y[static 32], uint64_t t[static 96]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[32], `y`[32]; output `z`[64]; temporary `t`[>=96]

**Aliasing.** Output `z` must not overlap `x`, `y`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM 144 bytes, x86 64 bytes (below the stack pointer)

**Availability.** ARM and x86. On x86 the `t` buffer is used but the nominal size (96) overstates the real requirement (65 words); the size is kept for ARM compatibility.

**Details.** This is a Karatsuba-style function multiplying half-sized results internally and using temporary buffer t for intermediate results.

### `bignum_ksqr_16_32`

```c
void bignum_ksqr_16_32(uint64_t z[static 32], const uint64_t x[static 16], uint64_t t[static 24]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[16]; output `z`[32]; temporary `t`[>=24]

**Aliasing.** Output `z` must not overlap `x`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM 64 bytes, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86. On x86 the temporary-buffer argument `t` is unused (retained only for API compatibility with ARM).

**Details.** This is a Karatsuba-style function squaring half-sized results and using temporary buffer t for intermediate results.

### `bignum_ksqr_32_64`

```c
void bignum_ksqr_32_64(uint64_t z[static 64], const uint64_t x[static 32], uint64_t t[static 72]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[32]; output `z`[64]; temporary `t`[>=72]

**Aliasing.** Output `z` must not overlap `x`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM 96 bytes, x86 56 bytes (below the stack pointer)

**Availability.** ARM and x86. On x86 the `t` buffer is used but the nominal size (72) overstates the real requirement (65 words); the size is kept for ARM compatibility.

**Details.** This is a Karatsuba-style function squaring half-sized results and using temporary buffer t for intermediate results.

### `bignum_le`

```c
uint64_t bignum_le(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Compare bignums, x <= y

**Sizes.** inputs `x`[m], `y`[n]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_littleendian_4`

```c
void bignum_littleendian_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert 4-digit (256-bit) bignum to/from little-endian form

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** The same function is given two other prototypes whose names reflect the treatment of one or other argument as a byte array rather than word array: The implementation works by loading in bytes and storing in words (i.e. stylistically it is "fromlebytes"); in the more common little-endian usage of ARM, this is just copying.

### `bignum_littleendian_6`

```c
void bignum_littleendian_6(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert 6-digit (384-bit) bignum to/from little-endian form

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** The same function is given two other prototypes whose names reflect the treatment of one or other argument as a byte array rather than word array: The implementation works by loading in bytes and storing in words (i.e. stylistically it is "fromlebytes"); in the more common little-endian usage of ARM, this is just copying.

### `bignum_lt`

```c
uint64_t bignum_lt(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Compare bignums, x < y

**Sizes.** inputs `x`[m], `y`[n]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_madd`

```c
uint64_t bignum_madd(uint64_t k, uint64_t *z, uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Multiply-add, z := z + x * y

**Sizes.** inputs `x`[m], `y`[n]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := x * y + z" operation, while also returning a "next" or "carry" word. In the case where m + n <= p (i.e. the pure product would fit in the destination) this is the remainder for the exact result.

### `bignum_madd_n25519`

```c
void bignum_madd_n25519(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4], const uint64_t c[static 4]);
```

**Operation.** Multiply-add modulo the order of the curve25519/edwards25519 basepoint

**Sizes.** inputs `x`[4], `y`[4], `c`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 16 bytes, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Performs z := (x * y + c) mod n_25519, where the modulus is n_25519 = 2^252 + 27742317777372353535851937790883648493, the order of the curve25519/edwards25519 basepoint. The result z and the inputs x, y and c are all 4 digits (256 bits).

### `bignum_madd_n25519_alt`

```c
void bignum_madd_n25519_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4], const uint64_t c[static 4]);
```

**Operation.** Multiply-add modulo the order of the curve25519/edwards25519 basepoint

**Sizes.** inputs `x`[4], `y`[4], `c`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 16 bytes, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Performs z := (x * y + c) mod n_25519, where the modulus is n_25519 = 2^252 + 27742317777372353535851937790883648493, the order of the curve25519/edwards25519 basepoint. The result z and the inputs x, y and c are all 4 digits (256 bits).

### `bignum_mod_m25519`

```c
void bignum_mod_m25519(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod m_25519

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of curve25519/edwards25519. This is the full group order, 8 * the standard basepoint order.

### `bignum_mod_m25519_4`

```c
void bignum_mod_m25519_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo group order, z := x mod m_25519

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of curve25519/edwards25519. This is the full group order, 8 * the standard basepoint order.

### `bignum_mod_n25519`

```c
void bignum_mod_n25519(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo basepoint order, z := x mod n_25519

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the order of the curve25519/edwards25519 basepoint, which is n_25519 = 2^252 + 27742317777372353535851937790883648493

### `bignum_mod_n25519_4`

```c
void bignum_mod_n25519_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo basepoint order, z := x mod n_25519

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the order of the curve25519/edwards25519 basepoint.

### `bignum_mod_n256`

```c
void bignum_mod_n256(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_256

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-256.

### `bignum_mod_n256_4`

```c
void bignum_mod_n256_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo group order, z := x mod n_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-256.

### `bignum_mod_n256_alt`

```c
void bignum_mod_n256_alt(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_256

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-256.

### `bignum_mod_n256k1`

```c
void bignum_mod_n256k1(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_256k1

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the secp256k1 curve.

### `bignum_mod_n256k1_4`

```c
void bignum_mod_n256k1_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo group order, z := x mod n_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the secp256k1 curve.

### `bignum_mod_n384`

```c
void bignum_mod_n384(uint64_t z[static 6], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_384

**Sizes.** inputs `x`[k]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-384.

### `bignum_mod_n384_6`

```c
void bignum_mod_n384_6(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Reduce modulo group order, z := x mod n_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-384.

### `bignum_mod_n384_alt`

```c
void bignum_mod_n384_alt(uint64_t z[static 6], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_384

**Sizes.** inputs `x`[k]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-384.

### `bignum_mod_n521_9`

```c
void bignum_mod_n521_9(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Reduce modulo group order, z := x mod n_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-521.

### `bignum_mod_n521_9_alt`

```c
void bignum_mod_n521_9_alt(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Reduce modulo group order, z := x mod n_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the NIST curve P-521.

### `bignum_mod_nsm2`

```c
void bignum_mod_nsm2(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_sm2

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the GM/T 0003-2012 curve SM2.

### `bignum_mod_nsm2_4`

```c
void bignum_mod_nsm2_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo group order, z := x mod n_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the GM/T 0003-2012 curve SM2.

### `bignum_mod_nsm2_alt`

```c
void bignum_mod_nsm2_alt(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo group order, z := x mod n_sm2

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Reduction is modulo the group order of the GM/T 0003-2012 curve SM2.

### `bignum_mod_p25519_4`

```c
void bignum_mod_p25519_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_25519

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_mod_p256`

```c
void bignum_mod_p256(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_256

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_p256_4`

```c
void bignum_mod_p256_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_mod_p256_alt`

```c
void bignum_mod_p256_alt(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_256

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_p256k1`

```c
void bignum_mod_p256k1(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_256k1

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_p256k1_4`

```c
void bignum_mod_p256k1_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_mod_p384`

```c
void bignum_mod_p384(uint64_t z[static 6], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_384

**Sizes.** inputs `x`[k]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_p384_6`

```c
void bignum_mod_p384_6(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_mod_p384_alt`

```c
void bignum_mod_p384_alt(uint64_t z[static 6], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_384

**Sizes.** inputs `x`[k]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_p521_9`

```c
void bignum_mod_p521_9(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_sm2`

```c
void bignum_mod_sm2(uint64_t z[static 4], uint64_t k, const uint64_t *x);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_sm2

**Sizes.** inputs `x`[k]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mod_sm2_4`

```c
void bignum_mod_sm2_4(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Reduce modulo field characteristic, z := x mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_modadd`

```c
void bignum_modadd(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *y, const uint64_t *m);
```

**Operation.** Add modulo m, z := (x + y) mod m, assuming x and y reduced

**Sizes.** inputs `x`[k], `y`[k], `m`[k]; output `z`[k]

**Assumptions.** a < n; b < n.

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap); must not overlap `m`.

**Availability.** ARM and x86.

### `bignum_moddouble`

```c
void bignum_moddouble(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *m);
```

**Operation.** Double modulo m, z := (2 * x) mod m, assuming x reduced

**Sizes.** inputs `x`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap); must not overlap `m`.

**Availability.** ARM and x86.

### `bignum_modexp`

```c
void bignum_modexp(uint64_t k,uint64_t *z, const uint64_t *a,const uint64_t *p,const uint64_t *m,uint64_t *t);
```

**Operation.** Modular exponentiation for arbitrary odd modulus

**Sizes.** inputs `a`[k], `p`[k], `m`[k]; output `z`[k]; temporary `t`[>=3*k]

**Assumptions.** k < 2^58.

**Aliasing.** No restrictions on input/output overlap. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM 64 bytes, x86 136 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (a^p) mod m where all numbers are k-digit and m is odd

### `bignum_modifier`

```c
void bignum_modifier(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t *t);
```

**Operation.** Compute "modification" constant z := 2^{64k} mod m

**Sizes.** inputs `m`[k]; output `z`[k]; temporary `t`[>=k]

**Aliasing.** Output `z` must not overlap `m`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The last argument points to a temporary buffer t that should have size >= k. This is called "mod-ifier" because given any other k-digit number x we can get x MOD m simply and reasonably efficiently just by Montgomery multiplication of x and z. But one can also consider it the identity for Montgomery multiplication, assuming you have a reduced multiplier already.

### `bignum_modinv`

```c
void bignum_modinv(uint64_t k, uint64_t *z, const uint64_t *a, const uint64_t *b, uint64_t *t);
```

**Operation.** Invert modulo m, z = (1/a) mod b, assuming b is an odd number > 1, coprime a

**Sizes.** inputs `a`[k], `b`[k]; output `z`[k]; temporary `t`[>=3*k]

**Assumptions.** k < 2^57.

**Aliasing.** Output `z` must not overlap inputs `a`, `b`. Temporary buffer `t` (>= 3*k words) must be distinct from all other arguments.

**Stack use.** ARM 32 bytes, x86 128 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** k-digit (digit=64 bits) "z := a^-1 mod b" (modular inverse of a modulo b) using t as a temporary buffer (t at least 3*k words = 24*k bytes), and assuming that a and b are coprime *and* that b is an odd number > 1.

### `bignum_modoptneg`

```c
void bignum_modoptneg(uint64_t k, uint64_t *z, uint64_t p, const uint64_t *x, const uint64_t *m);
```

**Operation.** Optionally negate modulo m, z := (-x) mod m (if p nonzero) or z := x

**Sizes.** inputs `x`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x`, `m` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** (if p zero), assuming x reduced Inputs p, x[k], m[k]; output z[k]

### `bignum_modsub`

```c
void bignum_modsub(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *y, const uint64_t *m);
```

**Operation.** Subtract modulo m, z := (x - y) mod m, assuming x and y reduced

**Sizes.** inputs `x`[k], `y`[k], `m`[k]; output `z`[k]

**Assumptions.** a < n; b < n.

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap); must not overlap `m`.

**Availability.** ARM and x86.

### `bignum_montifier`

```c
void bignum_montifier(uint64_t k, uint64_t *z, const uint64_t *m, uint64_t *t);
```

**Operation.** Compute "montification" constant z := 2^{128k} mod m

**Sizes.** inputs `m`[k]; output `z`[k]; temporary `t`[>=k]

**Aliasing.** Output `z` must not overlap `m`. Temporary buffer `t` must be distinct from all other arguments.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The last argument points to a temporary buffer t that should have size >= k. This is called "montifier" because given any other k-digit number x, whether or not it's reduced modulo m, it can be mapped to its Montgomery representation (2^{64k} * x) mod m just by Montgomery multiplication by z.

### `bignum_montinv_p256`

```c
void bignum_montinv_p256(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Montgomery inverse modulo p_256 = 2^256 - 2^224 + 2^192 + 2^96 - 1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 288 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 4-digit input x is coprime to p_256, i.e. is not divisible by it, returns z < p_256 such that x * z == 2^512 (mod p_256). This is effectively "Montgomery inverse" because if we consider x and z as Montgomery forms of X and Z, i.e. x == 2^256 * X and z == 2^256 * Z (both mod p_256) then X * Z == 1 (mod p_256). That is, this function gives the analog of the modular inverse bignum_inv_p256 but with both input and output in the Montgomery domain. Note that x does not need to be reduced modulo p_256, but the output always is. If the input is divisible (i.e. is 0 or p_256), then there can be no solution to the congruence x * z == 2^512 (mod p_256), and z = 0 is returned.

### `bignum_montinv_p384`

```c
void bignum_montinv_p384(uint64_t z[static 6],const uint64_t x[static 6]);
```

**Operation.** Montgomery inverse modulo p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM 304 bytes, x86 384 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 6-digit input x is coprime to p_384, i.e. is not divisible by it, returns z < p_384 such that x * z == 2^768 (mod p_384). This is effectively "Montgomery inverse" because if we consider x and z as Montgomery forms of X and Z, i.e. x == 2^384 * X and z == 2^384 * Z (both mod p_384) then X * Z == 1 (mod p_384). That is, this function gives the analog of the modular inverse bignum_inv_p384 but with both input and output in the Montgomery domain. Note that x does not need to be reduced modulo p_384, but the output always is. If the input is divisible (i.e. is 0 or p_384), then there can be no solution to the congruence x * z == 2^768 (mod p_384), and z = 0 is returned.

### `bignum_montinv_sm2`

```c
void bignum_montinv_sm2(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Montgomery inverse modulo p_sm2 = 2^256 - 2^224 - 2^96 + 2^64 - 1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 288 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If the 4-digit input x is coprime to p_sm2, i.e. is not divisible by it, returns z < p_sm2 such that x * z == 2^512 (mod p_sm2). This is effectively "Montgomery inverse" because if we consider x and z as Montgomery forms of X and Z, i.e. x == 2^256 * X and z == 2^256 * Z (both mod p_sm2) then X * Z == 1 (mod p_sm2). That is, this function gives the analog of the modular inverse bignum_inv_sm2 but with both input and output in the Montgomery domain. Note that x does not need to be reduced modulo p_sm2, but the output always is. If the input is divisible (i.e. is 0 or p_sm2), then there can be no solution to the congruence x * z == 2^512 (mod p_sm2), and z = 0 is returned.

### `bignum_montmul`

```c
void bignum_montmul(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *y, const uint64_t *m);
```

**Operation.** Montgomery multiply, z := (x * y / 2^{64k}) mod m

**Sizes.** inputs `x`[k], `y`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `y`, `m`.

**Stack use.** ARM none, x86 56 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x * y / 2^{64k}) mod m, assuming x * y <= 2^{64k} * m, which is guaranteed in particular if x < m, y < m initially (the "intended" case).

### `bignum_montmul_p256`

```c
void bignum_montmul_p256(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_256

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_256, assuming that the inputs x and y satisfy x * y <= 2^256 * p_256 (in particular this is true if we are in the "usual" case x < p_256 and y < p_256).

### `bignum_montmul_p256_alt`

```c
void bignum_montmul_p256_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_256

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_256, assuming that the inputs x and y satisfy x * y <= 2^256 * p_256 (in particular this is true if we are in the "usual" case x < p_256 and y < p_256).

### `bignum_montmul_p256k1`

```c
void bignum_montmul_p256k1(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_256k1

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_256k1, assuming that the inputs x and y satisfy x * y <= 2^256 * p_256k1 (in particular this is true if we are in the "usual" case x < p_256k1 and y < p_256k1).

### `bignum_montmul_p256k1_alt`

```c
void bignum_montmul_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_256k1

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_256k1, assuming that the inputs x and y satisfy x * y <= 2^256 * p_256k1 (in particular this is true if we are in the "usual" case x < p_256k1 and y < p_256k1).

### `bignum_montmul_p384`

```c
void bignum_montmul_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^384) mod p_384

**Sizes.** inputs `x`[6], `y`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-384} * x * y) mod p_384, assuming that the inputs x and y satisfy x * y <= 2^384 * p_384 (in particular this is true if we are in the "usual" case x < p_384 and y < p_384).

### `bignum_montmul_p384_alt`

```c
void bignum_montmul_p384_alt(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^384) mod p_384

**Sizes.** inputs `x`[6], `y`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM 32 bytes, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-384} * x * y) mod p_384, assuming that the inputs x and y satisfy x * y <= 2^384 * p_384 (in particular this is true if we are in the "usual" case x < p_384 and y < p_384).

### `bignum_montmul_p521`

```c
void bignum_montmul_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^576) mod p_521

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 112 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x * y / 2^576) mod p_521, assuming x < p_521, y < p_521. This means the Montgomery base is the "native size" 2^{9*64} = 2^576; since p_521 is a Mersenne prime the basic modular multiplication bignum_mul_p521 can be considered a Montgomery operation to base 2^521.

### `bignum_montmul_p521_alt`

```c
void bignum_montmul_p521_alt(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^576) mod p_521

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 128 bytes, x86 104 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x * y / 2^576) mod p_521, assuming x < p_521, y < p_521. This means the Montgomery base is the "native size" 2^{9*64} = 2^576; since p_521 is a Mersenne prime the basic modular multiplication bignum_mul_p521 can be considered a Montgomery operation to base 2^521.

### `bignum_montmul_sm2`

```c
void bignum_montmul_sm2(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_sm2

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_sm2, assuming that the inputs x and y satisfy x * y <= 2^256 * p_sm2 (in particular this is true if we are in the "usual" case x < p_sm2 and y < p_sm2).

### `bignum_montmul_sm2_alt`

```c
void bignum_montmul_sm2_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Montgomery multiply, z := (x * y / 2^256) mod p_sm2

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (2^{-256} * x * y) mod p_sm2, assuming that the inputs x and y satisfy x * y <= 2^256 * p_sm2 (in particular this is true if we are in the "usual" case x < p_sm2 and y < p_sm2).

### `bignum_montredc`

```c
void bignum_montredc(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, const uint64_t *m, uint64_t p);
```

**Operation.** Montgomery reduce, z := (x' / 2^{64p}) MOD m

**Sizes.** inputs `x`[n], `m`[k]; output `z`[k]

**Assumptions.** p < 2^61; r < 2^61.

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap); must not overlap `m`.

**Stack use.** ARM none, x86 56 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does a := (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general is the lowest (p+k) digits of x, assuming x' <= 2^{64p} * m. That is, p-fold Montgomery reduction w.r.t. a k-digit modulus m giving a k-digit answer.

### `bignum_montsqr`

```c
void bignum_montsqr(uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *m);
```

**Operation.** Montgomery square, z := (x^2 / 2^{64k}) mod m

**Sizes.** inputs `x`[k], `m`[k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `m`.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^{64k}) mod m, assuming x^2 <= 2^{64k} * m, which is guaranteed in particular if x < m initially (the "intended" case).

### `bignum_montsqr_p256`

```c
void bignum_montsqr_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is guaranteed in particular if x < p_256 initially (the "intended" case).

### `bignum_montsqr_p256_alt`

```c
void bignum_montsqr_p256_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is guaranteed in particular if x < p_256 initially (the "intended" case).

### `bignum_montsqr_p256k1`

```c
void bignum_montsqr_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_256k1, assuming x^2 <= 2^256 * p_256k1, which is guaranteed in particular if x < p_256k1 initially (the "intended" case).

### `bignum_montsqr_p256k1_alt`

```c
void bignum_montsqr_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_256k1, assuming x^2 <= 2^256 * p_256k1, which is guaranteed in particular if x < p_256k1 initially (the "intended" case).

### `bignum_montsqr_p384`

```c
void bignum_montsqr_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Montgomery square, z := (x^2 / 2^384) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is guaranteed in particular if x < p_384 initially (the "intended" case).

### `bignum_montsqr_p384_alt`

```c
void bignum_montsqr_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Montgomery square, z := (x^2 / 2^384) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM 16 bytes, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is guaranteed in particular if x < p_384 initially (the "intended" case).

### `bignum_montsqr_p521`

```c
void bignum_montsqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Montgomery square, z := (x^2 / 2^576) mod p_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM 48 bytes, x86 104 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^576) mod p_521, assuming x < p_521. This means the Montgomery base is the "native size" 2^{9*64} = 2^576; since p_521 is a Mersenne prime the basic modular squaring bignum_sqr_p521 can be considered a Montgomery operation to base 2^521.

### `bignum_montsqr_p521_alt`

```c
void bignum_montsqr_p521_alt(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Montgomery square, z := (x^2 / 2^576) mod p_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM 80 bytes, x86 112 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^576) mod p_521, assuming x < p_521. This means the Montgomery base is the "native size" 2^{9*64} = 2^576; since p_521 is a Mersenne prime the basic modular squaring bignum_sqr_p521 can be considered a Montgomery operation to base 2^521.

### `bignum_montsqr_sm2`

```c
void bignum_montsqr_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_sm2, assuming x^2 <= 2^256 * p_sm2, which is guaranteed in particular if x < p_sm2 initially (the "intended" case).

### `bignum_montsqr_sm2_alt`

```c
void bignum_montsqr_sm2_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Montgomery square, z := (x^2 / 2^256) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does z := (x^2 / 2^256) mod p_sm2, assuming x^2 <= 2^256 * p_sm2, which is guaranteed in particular if x < p_sm2 initially (the "intended" case).

### `bignum_mul`

```c
void bignum_mul(uint64_t k, uint64_t *z, uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[m], `y`[n]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := x * y" operation where x is m digits, y is n, result z is k. Truncates the result in general unless k >= m + n

### `bignum_mul_4_8`

```c
void bignum_mul_4_8(uint64_t z[static 8], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[4], `y`[4]; output `z`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_4_8_alt`

```c
void bignum_mul_4_8_alt(uint64_t z[static 8], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[4], `y`[4]; output `z`[8]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_mul_6_12`

```c
void bignum_mul_6_12(uint64_t z[static 12], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[6], `y`[6]; output `z`[12]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** ARM 16 bytes, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_6_12_alt`

```c
void bignum_mul_6_12_alt(uint64_t z[static 12], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[6], `y`[6]; output `z`[12]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** ARM 16 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_8_16`

```c
void bignum_mul_8_16(uint64_t z[static 16], const uint64_t x[static 8], const uint64_t y[static 8]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[8], `y`[8]; output `z`[16]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_8_16_alt`

```c
void bignum_mul_8_16_alt(uint64_t z[static 16], const uint64_t x[static 8], const uint64_t y[static 8]);
```

**Operation.** Multiply z := x * y

**Sizes.** inputs `x`[8], `y`[8]; output `z`[16]

**Aliasing.** Output `z` must not overlap `x`, `y`.

**Stack use.** ARM 48 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p25519`

```c
void bignum_mul_p25519(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply modulo p_25519, z := (x * y) mod p_25519

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p25519_alt`

```c
void bignum_mul_p25519_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply modulo p_25519, z := (x * y) mod p_25519

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p256k1`

```c
void bignum_mul_p256k1(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply modulo p_256k1, z := (x * y) mod p_256k1

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p256k1_alt`

```c
void bignum_mul_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Multiply modulo p_256k1, z := (x * y) mod p_256k1

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p521`

```c
void bignum_mul_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 112 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_mul_p521_alt`

```c
void bignum_mul_p521_alt(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 128 bytes, x86 104 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_muladd10`

```c
uint64_t bignum_muladd10(uint64_t k, uint64_t *z, uint64_t d);
```

**Operation.** Multiply bignum by 10 and add word: z := 10 * z + d

**Sizes.** inputs `z`[k]; output `z`[k]

**Aliasing.** Operates in place on `z` (read and written in the same buffer).

**Availability.** ARM and x86.

**Details.** Although typically the input d < 10, this is not actually required.

### `bignum_mux`

```c
void bignum_mux(uint64_t p, uint64_t k, uint64_t *z, const uint64_t *x, const uint64_t *y);
```

**Operation.** Multiplex/select z := x (if p nonzero) or z := y (if p zero)

**Sizes.** inputs `x`[k], `y`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers x, y and z have the same size k digits.

### `bignum_mux16`

```c
void bignum_mux16(uint64_t k, uint64_t *z, const uint64_t *xs, uint64_t i);
```

**Operation.** Select element from 16-element table, z := xs[k*i]

**Sizes.** inputs `xs`[16*k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `xs`.

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers xs[16] and the target z have the same size k The pointer xs is to a contiguous array of size 16, elements size-k bignums

### `bignum_mux_4`

```c
void bignum_mux_4(uint64_t p, uint64_t z[static 4],const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** 256-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers x, y and z have the same size 4 digits.

### `bignum_mux_6`

```c
void bignum_mux_6(uint64_t p, uint64_t z[static 6],const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** 384-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)

**Sizes.** inputs `x`[6], `y`[6]; output `z`[6]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers x, y and z have the same size 6 digits.

### `bignum_neg_p25519`

```c
void bignum_neg_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Negate modulo p_25519, z := (-x) mod p_25519, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_neg_p256`

```c
void bignum_neg_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Negate modulo p_256, z := (-x) mod p_256, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_neg_p256k1`

```c
void bignum_neg_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Negate modulo p_256k1, z := (-x) mod p_256k1, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_neg_p384`

```c
void bignum_neg_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Negate modulo p_384, z := (-x) mod p_384, assuming x reduced

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_neg_p521`

```c
void bignum_neg_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Negate modulo p_521, z := (-x) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_neg_sm2`

```c
void bignum_neg_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Negate modulo p_sm2, z := (-x) mod p_sm2, assuming x reduced

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_negmodinv`

```c
void bignum_negmodinv(uint64_t k, uint64_t *z, const uint64_t *x);
```

**Operation.** Negated modular inverse, z := (-1/x) mod 2^{64k}

**Sizes.** inputs `x`[k]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Assuming x is odd (otherwise nothing makes sense) the result satisfies x * z + 1 == 0 (mod 2^{64 * k})

### `bignum_nonzero`

```c
uint64_t bignum_nonzero(uint64_t k, const uint64_t *x);
```

**Operation.** Test bignum for nonzero-ness x =/= 0

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_nonzero_4`

```c
uint64_t bignum_nonzero_4(const uint64_t x[static 4]);
```

**Operation.** 256-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero

**Sizes.** inputs `x`[4]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_nonzero_6`

```c
uint64_t bignum_nonzero_6(const uint64_t x[static 6]);
```

**Operation.** 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero

**Sizes.** inputs `x`[6]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_normalize`

```c
uint64_t bignum_normalize(uint64_t k, uint64_t *z);
```

**Operation.** Normalize bignum in-place by shifting left till top bit is 1

**Sizes.** inputs `z`[k]; output `z`[k]

**Aliasing.** Operates in place on `z` (read and written in the same buffer).

**Availability.** ARM and x86.

**Details.** Given a k-digit bignum z, this function shifts it left by its number of leading zero bits, to give result with top bit 1, unless the input number was 0. The return is the same as the output of bignum_clz, i.e. the number of bits shifted (nominally 64 * k in the case of zero input).

### `bignum_odd`

```c
uint64_t bignum_odd(uint64_t k, const uint64_t *x);
```

**Operation.** Test bignum for odd-ness

**Sizes.** inputs `x`[k]

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_of_word`

```c
void bignum_of_word(uint64_t k, uint64_t *z, uint64_t n);
```

**Operation.** Convert single digit to bignum, z := n

**Sizes.** output `z`[k]

**Availability.** ARM and x86.

**Details.** Create a k-digit (digit=64 bits) bignum at z with value n (mod 2^k) where n is a word. The "mod 2^k" only matters in the degenerate k = 0 case.

### `bignum_optadd`

```c
uint64_t bignum_optadd(uint64_t k, uint64_t *z, const uint64_t *x, uint64_t p, const uint64_t *y);
```

**Operation.** Optionally add, z := x + y (if p nonzero) or z := x (if p zero)

**Sizes.** inputs `x`[k], `y`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers x, y and z have the same size k digits. Returns carry-out as per usual addition, always 0 if p was zero.

### `bignum_optneg`

```c
uint64_t bignum_optneg(uint64_t k, uint64_t *z, uint64_t p, const uint64_t *x);
```

**Operation.** Optionally negate, z := -x (if p nonzero) or z := x (if p zero)

**Sizes.** inputs `x`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that both numbers x and z have the same size k digits. Returns a carry, which is equivalent to "x is nonzero".

### `bignum_optneg_p25519`

```c
void bignum_optneg_p25519(uint64_t z[static 4], uint64_t p, const uint64_t x[static 4]);
```

**Operation.** Optionally negate modulo p_25519, z := (-x) mod p_25519 (if p nonzero) or

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[4]; output z[4]

### `bignum_optneg_p256`

```c
void bignum_optneg_p256(uint64_t z[static 4], uint64_t p, const uint64_t x[static 4]);
```

**Operation.** Optionally negate modulo p_256, z := (-x) mod p_256 (if p nonzero) or

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[4]; output z[4]

### `bignum_optneg_p256k1`

```c
void bignum_optneg_p256k1(uint64_t z[static 4], uint64_t p, const uint64_t x[static 4]);
```

**Operation.** Optionally negate modulo p_256k1, z := (-x) mod p_256k1 (if p nonzero) or

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[4]; output z[4]

### `bignum_optneg_p384`

```c
void bignum_optneg_p384(uint64_t z[static 6], uint64_t p, const uint64_t x[static 6]);
```

**Operation.** Optionally negate modulo p_384, z := (-x) mod p_384 (if p nonzero) or

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[6]; output z[6]

### `bignum_optneg_p521`

```c
void bignum_optneg_p521(uint64_t z[static 9], uint64_t p, const uint64_t x[static 9]);
```

**Operation.** Optionally negate modulo p_521, z := (-x) mod p_521 (if p nonzero) or

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[9]; output z[9]

### `bignum_optneg_sm2`

```c
void bignum_optneg_sm2(uint64_t z[static 4], uint64_t p, const uint64_t x[static 4]);
```

**Operation.** Optionally negate modulo p_sm2, z := (-x) mod p_sm2 (if p nonzero) or

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** z := x (if p zero), assuming x reduced Inputs p, x[4]; output z[4]

### `bignum_optsub`

```c
uint64_t bignum_optsub(uint64_t k, uint64_t *z, const uint64_t *x, uint64_t p, const uint64_t *y);
```

**Operation.** Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero)

**Sizes.** inputs `x`[k], `y`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** It is assumed that all numbers x, y and z have the same size k digits. Returns carry-out as per usual subtraction, always 0 if p was zero.

### `bignum_optsubadd`

```c
uint64_t bignum_optsubadd(uint64_t k, uint64_t *z, const uint64_t *x, uint64_t p, const uint64_t *y);
```

**Operation.** Optionally subtract or add, z := x + sgn(p) * y interpreting p as signed

**Sizes.** inputs `x`[k], `y`[k]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** If p has top bit set (i.e. is negative as a signed int) return z := x - y Else if p is nonzero (i.e. is positive as a signed int) return z := x + y Otherwise (i.e. p is zero) return z := x Return in X0 = the top carry, which will be 0 or 1, and appropriate for addition or subtraction respectively (and always zero for p = 0)

### `bignum_pow2`

```c
void bignum_pow2(uint64_t k, uint64_t *z, uint64_t n);
```

**Operation.** Return bignum of power of 2, z := 2^n

**Sizes.** output `z`[k]

**Availability.** ARM and x86.

**Details.** The result is as usual mod 2^{64*k}, so will be zero if n >= 64*k.

### `bignum_shl_small`

```c
uint64_t bignum_shl_small(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, uint64_t c);
```

**Operation.** Shift bignum left by c < 64 bits z := x * 2^c

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Does the "z := x << c" operation where x is n digits, result z is p. The shift count c is masked to 6 bits so it actually uses c' = c mod 64. The return value is the "next word" of a p+1 bit result, if n <= p.

### `bignum_shr_small`

```c
uint64_t bignum_shr_small(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x, uint64_t c);
```

**Operation.** Shift bignum right by c < 64 bits z := floor(x / 2^c)

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Does the "z := x >> c" operation where x is n digits, result z is p. The shift count c is masked to 6 bits so it actually uses c' = c mod 64. The return value is the inout mod 2^c'.

### `bignum_sqr`

```c
void bignum_sqr(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
```

**Operation.** Square z := x^2

**Sizes.** inputs `x`[n]; output `z`[k]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does the "z := x^2" operation where x is n digits and result z is k. Truncates the result in general unless k >= 2 * n

### `bignum_sqr_4_8`

```c
void bignum_sqr_4_8(uint64_t z[static 8], const uint64_t x[static 4]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[4]; output `z`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_4_8_alt`

```c
void bignum_sqr_4_8_alt(uint64_t z[static 8], const uint64_t x[static 4]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[4]; output `z`[8]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_sqr_6_12`

```c
void bignum_sqr_6_12(uint64_t z[static 12], const uint64_t x[static 6]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[6]; output `z`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 48 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_6_12_alt`

```c
void bignum_sqr_6_12_alt(uint64_t z[static 12], const uint64_t x[static 6]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[6]; output `z`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 16 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_8_16`

```c
void bignum_sqr_8_16(uint64_t z[static 16], const uint64_t x[static 8]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[8]; output `z`[16]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM 32 bytes, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_8_16_alt`

```c
void bignum_sqr_8_16_alt(uint64_t z[static 16], const uint64_t x[static 8]);
```

**Operation.** Square, z := x^2

**Sizes.** inputs `x`[8]; output `z`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 64 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p25519`

```c
void bignum_sqr_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Square modulo p_25519, z := (x^2) mod p_25519

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p25519_alt`

```c
void bignum_sqr_p25519_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Square modulo p_25519, z := (x^2) mod p_25519

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p256k1`

```c
void bignum_sqr_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Square modulo p_256k1, z := (x^2) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p256k1_alt`

```c
void bignum_sqr_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Square modulo p_256k1, z := (x^2) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p521`

```c
void bignum_sqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Square modulo p_521, z := (x^2) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM 48 bytes, x86 104 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqr_p521_alt`

```c
void bignum_sqr_p521_alt(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Square modulo p_521, z := (x^2) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** Output `z` must not overlap `x`.

**Stack use.** ARM 64 bytes, x86 112 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sqrt_p25519`

```c
int64_t bignum_sqrt_p25519(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Square root modulo p_25519 = 2^255 - 19

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a 4-digit input x, returns a modular square root mod p_25519, i.e. a z such that z^2 == x (mod p_25519), whenever one exists. The square root z is chosen so that its LSB is even (note that p_25519 - z is another square root). The function return is the Legendre/Jacobi symbol (x//p_25519), which indicates whether indeed x has a modular square root and hence whether the result is meaningful: 0: x is divisible by p_25519 and z is the square root 0 +1: x is coprime to p_25519 and z is a square root -1: x is coprime to p_25519 but not a quadratic residue

### `bignum_sqrt_p25519_alt`

```c
int64_t bignum_sqrt_p25519_alt(uint64_t z[static 4],const uint64_t x[static 4]);
```

**Operation.** Square root modulo p_25519 = 2^255 - 19

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 144 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a 4-digit input x, returns a modular square root mod p_25519, i.e. a z such that z^2 == x (mod p_25519), whenever one exists. The square root z is chosen so that its LSB is even (note that p_25519 - z is another square root). The function return is the Legendre/Jacobi symbol (x//p_25519), which indicates whether indeed x has a modular square root and hence whether the result is meaningful: 0: x is divisible by p_25519 and z is the square root 0 +1: x is coprime to p_25519 and z is a square root -1: x is coprime to p_25519 but not a quadratic residue

### `bignum_sub`

```c
uint64_t bignum_sub(uint64_t p, uint64_t *z, uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);
```

**Operation.** Subtract, z := x - y

**Sizes.** inputs `x`[m], `y`[n]; output `z`[p]

**Aliasing.** Output `z` may be the same buffer as `x`, `y` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** Does the z := x - y operation, truncating modulo p words in general and returning a top borrow (0 or 1) in the p'th place, only subtracting input words below p (as well as m and n respectively) to get the diff and borrow.

### `bignum_sub_p25519`

```c
void bignum_sub_p25519(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Subtract modulo p_25519, z := (x - y) mod p_25519

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_sub_p256`

```c
void bignum_sub_p256(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Subtract modulo p_256, z := (x - y) mod p_256

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_sub_p256k1`

```c
void bignum_sub_p256k1(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Subtract modulo p_256k1, z := (x - y) mod p_256k1

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_sub_p384`

```c
void bignum_sub_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);
```

**Operation.** Subtract modulo p_384, z := (x - y) mod p_384

**Sizes.** inputs `x`[6], `y`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_sub_p521`

```c
void bignum_sub_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);
```

**Operation.** Subtract modulo p_521, z := (x - y) mod p_521

**Sizes.** inputs `x`[9], `y`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_sub_sm2`

```c
void bignum_sub_sm2(uint64_t z[static 4], const uint64_t x[static 4], const uint64_t y[static 4]);
```

**Operation.** Subtract modulo p_sm2, z := (x - y) mod p_sm2

**Sizes.** inputs `x`[4], `y`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_tobebytes_4`

```c
void bignum_tobebytes_4(uint8_t z[static 32], const uint64_t x[static 4]);
```

**Operation.** Convert 4-digit (256-bit) bignum to big-endian bytes

**Sizes.** inputs `x`[4]; output `z`[32] (bytes)

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_tobebytes_6`

```c
void bignum_tobebytes_6(uint8_t z[static 48], const uint64_t x[static 6]);
```

**Operation.** Convert 6-digit (384-bit) bignum to big-endian bytes

**Sizes.** inputs `x`[6]; output `z`[48] (bytes)

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_tolebytes_4`

```c
void bignum_tolebytes_4(uint8_t z[static 32], const uint64_t x[static 4]);
```

**Operation.** Convert 4-digit (256-bit) bignum to little-endian bytes

**Sizes.** inputs `x`[4]; output `z`[32] (bytes)

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_tolebytes_6`

```c
void bignum_tolebytes_6(uint8_t z[static 48], const uint64_t x[static 6]);
```

**Operation.** Convert 6-digit (384-bit) bignum to little-endian bytes

**Sizes.** inputs `x`[6]; output `z`[48] (bytes)

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

### `bignum_tolebytes_p521`

```c
void bignum_tolebytes_p521(uint8_t z[static 66], const uint64_t x[static 9]);
```

**Operation.** Convert 9-digit 528-bit bignum to little-endian bytes

**Sizes.** inputs `x`[9]; output `z`[66] (bytes)

**Aliasing.** Output `z` may be the same buffer as `x` (exact aliasing only — no partial overlap).

**Availability.** ARM and x86.

**Details.** This is assuming the input x is < 2^528 so that it fits in 66 bytes. In particular this holds if x < p_521 < 2^521 < 2^528.

### `bignum_tomont_p256`

```c
void bignum_tomont_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert to Montgomery form z := (2^256 * x) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_tomont_p256_alt`

```c
void bignum_tomont_p256_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert to Montgomery form z := (2^256 * x) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Stack use.** x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_tomont_p256k1`

```c
void bignum_tomont_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert to Montgomery form z := (2^256 * x) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_tomont_p256k1_alt`

```c
void bignum_tomont_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert to Montgomery form z := (2^256 * x) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_tomont_p384`

```c
void bignum_tomont_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert to Montgomery form z := (2^384 * x) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_tomont_p384_alt`

```c
void bignum_tomont_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Convert to Montgomery form z := (2^384 * x) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 40 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_tomont_p521`

```c
void bignum_tomont_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Convert to Montgomery form z := (2^576 * x) mod p_521

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_tomont_sm2`

```c
void bignum_tomont_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Convert to Montgomery form z := (2^256 * x) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

### `bignum_triple_p256`

```c
void bignum_triple_p256(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_256, z := (3 * x) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_256, and the result is always fully reduced, i.e. z = (3 * x) mod p_256.

### `bignum_triple_p256_alt`

```c
void bignum_triple_p256_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_256, z := (3 * x) mod p_256

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_256, and the result is always fully reduced, i.e. z = (3 * x) mod p_256.

### `bignum_triple_p256k1`

```c
void bignum_triple_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_256k1, z := (3 * x) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_256k1, and the result is always fully reduced, z = (3 * x) mod p_256k1.

### `bignum_triple_p256k1_alt`

```c
void bignum_triple_p256k1_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_256k1, z := (3 * x) mod p_256k1

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_256k1, and the result is always fully reduced, z = (3 * x) mod p_256k1.

### `bignum_triple_p384`

```c
void bignum_triple_p384(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Triple modulo p_384, z := (3 * x) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The input x can be any 6-digit bignum, not necessarily reduced modulo p_384, and the result is always fully reduced, i.e. z = (3 * x) mod p_384.

### `bignum_triple_p384_alt`

```c
void bignum_triple_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);
```

**Operation.** Triple modulo p_384, z := (3 * x) mod p_384

**Sizes.** inputs `x`[6]; output `z`[6]

**Aliasing.** No restrictions.

**Stack use.** x86 8 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The input x can be any 6-digit bignum, not necessarily reduced modulo p_384, and the result is always fully reduced, i.e. z = (3 * x) mod p_384.

### `bignum_triple_p521`

```c
void bignum_triple_p521(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Triple modulo p_521, z := (3 * x) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_triple_p521_alt`

```c
void bignum_triple_p521_alt(uint64_t z[static 9], const uint64_t x[static 9]);
```

**Operation.** Triple modulo p_521, z := (3 * x) mod p_521, assuming x reduced

**Sizes.** inputs `x`[9]; output `z`[9]

**Aliasing.** No restrictions.

**Stack use.** x86 24 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `bignum_triple_sm2`

```c
void bignum_triple_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_sm2, z := (3 * x) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_sm2, and the result is always fully reduced, i.e. z = (3 * x) mod p_sm2.

### `bignum_triple_sm2_alt`

```c
void bignum_triple_sm2_alt(uint64_t z[static 4], const uint64_t x[static 4]);
```

**Operation.** Triple modulo p_sm2, z := (3 * x) mod p_sm2

**Sizes.** inputs `x`[4]; output `z`[4]

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** The input x can be any 4-digit bignum, not necessarily reduced modulo p_sm2, and the result is always fully reduced, i.e. z = (3 * x) mod p_sm2.

### `curve25519_ladderstep`

```c
void curve25519_ladderstep(uint64_t rr[16],const uint64_t point[8],const uint64_t pp[16],uint64_t b);
```

**Operation.** Montgomery ladder step on pairs of (X,Z)-projective curve25519 points

**Sizes.** inputs `point`[8], `pp`[16]; output `rr`[16]

**Aliasing.** Output `rr` must not overlap `point`, `pp`.

**Stack use.** ARM 320 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If point = (X,1) and pp = (n * (X,1),[n+1] * (X,1)) then the output rr = (n' * (X,1),[n'+1] * (X,1)) where n' = 2 * n + b, with input b assumed to be 0 or 1; in this setting, each pair (X,Z) is assumed to be a projective y-free representation of an affine curve25519 point (X/Z,y), with the initial "differential" point having Z = 1 and X its affine x coordinate. In other words, the ladderstep operation is a combination of doubling, differential addition and optional swapping.

### `curve25519_ladderstep_alt`

```c
void curve25519_ladderstep_alt(uint64_t rr[16],const uint64_t point[8],const uint64_t pp[16],uint64_t b);
```

**Operation.** Montgomery ladder step on pairs of (X,Z)-projective curve25519 points

**Sizes.** inputs `point`[8], `pp`[16]; output `rr`[16]

**Aliasing.** Output `rr` must not overlap `point`, `pp`.

**Stack use.** ARM 320 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If point = (X,1) and pp = (n * (X,1),[n+1] * (X,1)) then the output rr = (n' * (X,1),[n'+1] * (X,1)) where n' = 2 * n + b, with input b assumed to be 0 or 1; in this setting, each pair (X,Z) is assumed to be a projective y-free representation of an affine curve25519 point (X/Z,y), with the initial "differential" point having Z = 1 and X its affine x coordinate. In other words, the ladderstep operation is a combination of doubling, differential addition and optional swapping.

### `curve25519_pxscalarmul`

```c
void curve25519_pxscalarmul(uint64_t res[static 8],const uint64_t scalar[static 4],const uint64_t point[static 4]);
```

**Operation.** Projective scalar multiplication, x coordinate only, for curve25519

**Sizes.** inputs `scalar`[4], `point`[4]; output `res`[8]

**Aliasing.** Output `res` must not overlap `scalar`, `point`.

**Stack use.** ARM 288 bytes, x86 408 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given the X coordinate of an input point = (X,Y) on curve25519, which could also be part of a projective representation (X,Y,1) of the same point, returns a projective representation (X,Z) = scalar * point, where scalar is a 256-bit number. The corresponding affine form is (X/Z,Y'), X/Z meaning division modulo 2^255-19, and Y' not being computed by this function (nor is any Y coordinate of the input point used).

### `curve25519_pxscalarmul_alt`

```c
void curve25519_pxscalarmul_alt(uint64_t res[static 8],const uint64_t scalar[static 4],const uint64_t point[static 4]);
```

**Operation.** Projective scalar multiplication, x coordinate only, for curve25519

**Sizes.** inputs `scalar`[4], `point`[4]; output `res`[8]

**Aliasing.** Output `res` must not overlap `scalar`, `point`.

**Stack use.** ARM 288 bytes, x86 408 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given the X coordinate of an input point = (X,Y) on curve25519, which could also be part of a projective representation (X,Y,1) of the same point, returns a projective representation (X,Z) = scalar * point, where scalar is a 256-bit number. The corresponding affine form is (X/Z,Y'), X/Z meaning division modulo 2^255-19, and Y' not being computed by this function (nor is any Y coordinate of the input point used).

### `curve25519_x25519`

```c
void curve25519_x25519(uint64_t res[static 4],const uint64_t scalar[static 4],const uint64_t point[static 4]);
```

**Operation.** The x25519 function for curve25519

**Sizes.** inputs `scalar`[4], `point`[4]; output `res`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 384 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86. See also [`curve25519_x25519_byte`](#curve25519_x25519_byte), an identical routine whose arguments are typed as 32-byte little-endian arrays instead of 4-word bignums.

**Details.** Given a scalar n and the X coordinate of an input point P = (X,Y) on curve25519 (Y can live in any extension field of characteristic 2^255-19), this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the point at infinity. Both n and X inputs are first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748); in particular the lower three bits of n are set to zero. Does not implement the zero-check specified in Section 6.1.

### `curve25519_x25519_alt`

```c
void curve25519_x25519_alt(uint64_t res[static 4],const uint64_t scalar[static 4],const uint64_t point[static 4]);
```

**Operation.** The x25519 function for curve25519

**Sizes.** inputs `scalar`[4], `point`[4]; output `res`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 368 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86. See also [`curve25519_x25519_byte_alt`](#curve25519_x25519_byte_alt), an identical routine whose arguments are typed as 32-byte little-endian arrays instead of 4-word bignums.

**Details.** Given a scalar n and the X coordinate of an input point P = (X,Y) on curve25519 (Y can live in any extension field of characteristic 2^255-19), this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the point at infinity. Both n and X inputs are first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748); in particular the lower three bits of n are set to zero. Does not implement the zero-check specified in Section 6.1.

### `curve25519_x25519_byte`

```c
void curve25519_x25519_byte(uint8_t res[static 32],const uint8_t scalar[static 32],const uint8_t point[static 32]);
```

**Operation.** The x25519 function for curve25519 (byte array arguments)

**Sizes.** inputs `scalar`[32] (bytes), `point`[32] (bytes); output `res`[32] (bytes)

**Aliasing.** No restrictions.

**Stack use.** ARM 384 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n and the X coordinate of an input point P = (X,Y) on curve25519 (Y can live in any extension field of characteristic 2^255-19), this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the point at infinity. Both n and X inputs are first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748); in particular the lower three bits of n are set to zero. Does not implement the zero-check specified in Section 6.1.

### `curve25519_x25519_byte_alt`

```c
void curve25519_x25519_byte_alt(uint8_t res[static 32],const uint8_t scalar[static 32],const uint8_t point[static 32]);
```

**Operation.** The x25519 function for curve25519 (byte array arguments)

**Sizes.** inputs `scalar`[32] (bytes), `point`[32] (bytes); output `res`[32] (bytes)

**Aliasing.** No restrictions.

**Stack use.** ARM 368 bytes, x86 464 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n and the X coordinate of an input point P = (X,Y) on curve25519 (Y can live in any extension field of characteristic 2^255-19), this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the point at infinity. Both n and X inputs are first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748); in particular the lower three bits of n are set to zero. Does not implement the zero-check specified in Section 6.1.

### `curve25519_x25519base`

```c
void curve25519_x25519base(uint64_t res[static 4],const uint64_t scalar[static 4]);
```

**Operation.** The x25519 function for curve25519 on base element 9

**Sizes.** inputs `scalar`[4]; output `res`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86. See also [`curve25519_x25519base_byte`](#curve25519_x25519base_byte), an identical routine whose arguments are typed as 32-byte little-endian arrays instead of 4-word bignums.

**Details.** Given a scalar n, returns the X coordinate of n * G where G = (9,...) is the standard generator. The scalar is first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748).

### `curve25519_x25519base_alt`

```c
void curve25519_x25519base_alt(uint64_t res[static 4],const uint64_t scalar[static 4]);
```

**Operation.** The x25519 function for curve25519 on base element 9

**Sizes.** inputs `scalar`[4]; output `res`[4]

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86. See also [`curve25519_x25519base_byte_alt`](#curve25519_x25519base_byte_alt), an identical routine whose arguments are typed as 32-byte little-endian arrays instead of 4-word bignums.

**Details.** Given a scalar n, returns the X coordinate of n * G where G = (9,...) is the standard generator. The scalar is first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748).

### `curve25519_x25519base_byte`

```c
void curve25519_x25519base_byte(uint8_t res[static 32],const uint8_t scalar[static 32]);
```

**Operation.** The x25519 function for curve25519 on base element 9 (byte array arguments)

**Sizes.** inputs `scalar`[32] (bytes); output `res`[32] (bytes)

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n, returns the X coordinate of n * G where G = (9,...) is the standard generator. The scalar is first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748).

### `curve25519_x25519base_byte_alt`

```c
void curve25519_x25519base_byte_alt(uint8_t res[static 32],const uint8_t scalar[static 32]);
```

**Operation.** The x25519 function for curve25519 on base element 9 (byte array arguments)

**Sizes.** inputs `scalar`[32] (bytes); output `res`[32] (bytes)

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n, returns the X coordinate of n * G where G = (9,...) is the standard generator. The scalar is first slightly modified/mangled as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748).

### `edwards25519_decode`

```c
uint64_t edwards25519_decode(uint64_t z[static 8], const uint8_t c[static 32]);
```

**Operation.** Decode compressed 256-bit form of edwards25519 point

**Sizes.** inputs `c`[32] (bytes); output `z`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 312 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This interprets the input byte string as a little-endian number representing a point (x,y) on the edwards25519 curve, encoded as 2^255 * x_0 + y where x_0 is the least significant bit of x. It returns the full pair of coordinates x (at z) and y (at z+4). The return code is 0 for success and 1 for failure, which means that the input does not correspond to the encoding of any edwards25519 point. This can happen for three reasons, where y = the lowest 255 bits of the input: * y >= p_25519 Input y coordinate is not reduced * (y^2 - 1) * (1 + d_25519 * y^2) has no modular square root There is no x such that (x,y) is on the curve * y^2 = 1 and top bit of input is set Cannot be the canonical encoding of (0,1) or (0,-1)

### `edwards25519_decode_alt`

```c
uint64_t edwards25519_decode_alt(uint64_t z[static 8], const uint8_t c[static 32]);
```

**Operation.** Decode compressed 256-bit form of edwards25519 point

**Sizes.** inputs `c`[32] (bytes); output `z`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 312 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This interprets the input byte string as a little-endian number representing a point (x,y) on the edwards25519 curve, encoded as 2^255 * x_0 + y where x_0 is the least significant bit of x. It returns the full pair of coordinates x (at z) and y (at z+4). The return code is 0 for success and 1 for failure, which means that the input does not correspond to the encoding of any edwards25519 point. This can happen for three reasons, where y = the lowest 255 bits of the input: * y >= p_25519 Input y coordinate is not reduced * (y^2 - 1) * (1 + d_25519 * y^2) has no modular square root There is no x such that (x,y) is on the curve * y^2 = 1 and top bit of input is set Cannot be the canonical encoding of (0,1) or (0,-1)

### `edwards25519_encode`

```c
void edwards25519_encode(uint8_t z[static 32], const uint64_t p[static 8]);
```

**Operation.** Encode edwards25519 point into compressed form as 256-bit number

**Sizes.** inputs `p`[8]; output `z`[32] (bytes)

**Aliasing.** No restrictions.

**Availability.** ARM and x86.

**Details.** This assumes that the input buffer p points to a pair of 256-bit numbers x (at p) and y (at p+4) representing a point (x,y) on the edwards25519 curve. It is assumed that both x and y are < p_25519 but there is no checking of this, nor of the fact that (x,y) is in fact on the curve. The output in z is a little-endian array of bytes corresponding to the standard compressed encoding of a point as 2^255 * x_0 + y where x_0 is the least significant bit of x. See "https://datatracker.ietf.org/doc/html/rfc8032#section-5.1.2" In this implementation, y is simply truncated to 255 bits, but if it is reduced mod p_25519 as expected this does not affect values.

### `edwards25519_epadd`

```c
void edwards25519_epadd(uint64_t p3[static 16],const uint64_t p1[static 16],const uint64_t p2[static 16]);
```

**Operation.** Extended projective addition for edwards25519

**Sizes.** inputs `p1`[16], `p2`[16]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The output p3 and both inputs p1 and p2 are points (x,y) on edwards25519 represented in extended projective quadruples (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z.

### `edwards25519_epadd_alt`

```c
void edwards25519_epadd_alt(uint64_t p3[static 16],const uint64_t p1[static 16],const uint64_t p2[static 16]);
```

**Operation.** Extended projective addition for edwards25519

**Sizes.** inputs `p1`[16], `p2`[16]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The output p3 and both inputs p1 and p2 are points (x,y) on edwards25519 represented in extended projective quadruples (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z.

### `edwards25519_epdouble`

```c
void edwards25519_epdouble(uint64_t p3[static 16],const uint64_t p1[static 12]);
```

**Operation.** Extended projective doubling for edwards25519

**Sizes.** inputs `p1`[12]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 176 bytes, x86 200 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If p1 is a point on edwards25519, returns its double p3 = 2 * p1. The output p3 is in extended projective coordinates, representing affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z. The input p1 may also be in the same extended projective representation, but the final T field is not used so a more basic projective triple (X,Y,Z) suffices.

### `edwards25519_epdouble_alt`

```c
void edwards25519_epdouble_alt(uint64_t p3[static 16],const uint64_t p1[static 12]);
```

**Operation.** Extended projective doubling for edwards25519

**Sizes.** inputs `p1`[12]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 176 bytes, x86 200 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If p1 is a point on edwards25519, returns its double p3 = 2 * p1. The output p3 is in extended projective coordinates, representing affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z. The input p1 may also be in the same extended projective representation, but the final T field is not used so a more basic projective triple (X,Y,Z) suffices.

### `edwards25519_pdouble`

```c
void edwards25519_pdouble(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Projective doubling for edwards25519

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 176 bytes, x86 200 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If p1 is a point on edwards25519, returns its double p3 = 2 * p1. Input and output are in pure projective coordinates, representing an affine (x,y) by a triple (X,Y,Z) where x = X / Z, y = Y / Z.

### `edwards25519_pdouble_alt`

```c
void edwards25519_pdouble_alt(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Projective doubling for edwards25519

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 176 bytes, x86 200 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** If p1 is a point on edwards25519, returns its double p3 = 2 * p1. Input and output are in pure projective coordinates, representing an affine (x,y) by a triple (X,Y,Z) where x = X / Z, y = Y / Z.

### `edwards25519_pepadd`

```c
void edwards25519_pepadd(uint64_t p3[static 16],const uint64_t p1[static 16],const uint64_t p2[static 12]);
```

**Operation.** Extended projective + precomputed mixed addition for edwards25519

**Sizes.** inputs `p1`[16], `p2`[12]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The output p3 and the first input p1 are points (x,y) on edwards25519 represented in extended projective quadruples (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z. The second input p2 is a triple encoding its point (x,y) as (y - x,y + x,2 * d * x * y) where d is the usual Edwards curve parameter for edwards25519.

### `edwards25519_pepadd_alt`

```c
void edwards25519_pepadd_alt(uint64_t p3[static 16],const uint64_t p1[static 16],const uint64_t p2[static 12]);
```

**Operation.** Extended projective + precomputed mixed addition for edwards25519

**Sizes.** inputs `p1`[16], `p2`[12]; output `p3`[16]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The output p3 and the first input p1 are points (x,y) on edwards25519 represented in extended projective quadruples (X,Y,Z,T) where x = X / Z, y = Y / Z and x * y = T / Z. The second input p2 is a triple encoding its point (x,y) as (y - x,y + x,2 * d * x * y) where d is the usual Edwards curve parameter for edwards25519.

### `edwards25519_scalarmulbase`

```c
void edwards25519_scalarmulbase(uint64_t res[static 8],const uint64_t scalar[static 4]);
```

**Operation.** Scalar multiplication for the edwards25519 standard basepoint

**Sizes.** inputs `scalar`[4]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n, returns point (X,Y) = n * B where B = (...,4/5) is the standard basepoint for the edwards25519 (Ed25519) curve.

### `edwards25519_scalarmulbase_alt`

```c
void edwards25519_scalarmulbase_alt(uint64_t res[static 8],const uint64_t scalar[static 4]);
```

**Operation.** Scalar multiplication for the edwards25519 standard basepoint

**Sizes.** inputs `scalar`[4]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 496 bytes, x86 536 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given a scalar n, returns point (X,Y) = n * B where B = (...,4/5) is the standard basepoint for the edwards25519 (Ed25519) curve.

### `edwards25519_scalarmuldouble`

```c
void edwards25519_scalarmuldouble(uint64_t res[static 8],const uint64_t scalar[static 4], const uint64_t point[static 8],const uint64_t bscalar[static 4]);
```

**Operation.** Double scalar multiplication for edwards25519, fresh and base point

**Sizes.** inputs `scalar`[4], `point`[8], `bscalar`[4]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 1696 bytes, x86 1720 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n, point = P and bscalar = m, returns in res the point (X,Y) = n * P + m * B where B = (...,4/5) is the standard basepoint for the edwards25519 (Ed25519) curve. Both 256-bit coordinates of the input point P are implicitly reduced modulo 2^255-19 if they are not already in reduced form, but the conventional usage is that they *are* already reduced. The scalars can be arbitrary 256-bit numbers but may also be considered as implicitly reduced modulo the group order.

### `edwards25519_scalarmuldouble_alt`

```c
void edwards25519_scalarmuldouble_alt(uint64_t res[static 8],const uint64_t scalar[static 4], const uint64_t point[static 8],const uint64_t bscalar[static 4]);
```

**Operation.** Double scalar multiplication for edwards25519, fresh and base point

**Sizes.** inputs `scalar`[4], `point`[8], `bscalar`[4]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 1696 bytes, x86 1720 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n, point = P and bscalar = m, returns in res the point (X,Y) = n * P + m * B where B = (...,4/5) is the standard basepoint for the edwards25519 (Ed25519) curve. Both 256-bit coordinates of the input point P are implicitly reduced modulo 2^255-19 if they are not already in reduced form, but the conventional usage is that they *are* already reduced. The scalars can be arbitrary 256-bit numbers but may also be considered as implicitly reduced modulo the group order.

### `mldsa_caddq`

```c
void mldsa_caddq(int32_t a[static 256]);
```

**Operation.** Conditional addition of q to each coefficient for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Operates in place on `a`.

**Availability.** ARM and x86.

**Details.** For each coefficient, add Q = 8380417 if the coefficient is negative. Input/output a[256] (signed 32-bit words), reduced in place.

### `mldsa_chknorm`

```c
uint64_t mldsa_chknorm(const int32_t a[static 256], uint64_t bound);
```

**Operation.** Infinity-norm check of polynomial coefficients for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words)

**Aliasing.** Reads `a` only (returns a flag); no output buffer.

**Availability.** ARM only.

**Details.** Returns 1 if any coefficient has absolute value >= bound, 0 otherwise. Input a[256] (signed 32-bit words), bound (unsigned 32-bit).

### `mldsa_decompose_32`

```c
void mldsa_decompose_32(int32_t a1[static 256], int32_t a0[static 256]);
```

**Operation.** Coefficient decomposition for ML-DSA (parameter sets 65 and 87, GAMMA2 = (Q-1)/32)

**Sizes.** inputs `a0`[256] (32-bit words); output `a1`[256] (32-bit words), `a0`[256] (32-bit words)

**Aliasing.** Writes high parts to `a1` and, in place, the low parts to `a0` (the input array); `a1` must not overlap `a0`.

**Availability.** ARM only.

**Details.** For each coefficient a in [0,Q), computes (a1, a0) with a = a1*2*GAMMA2 + a0. Input a[256] (signed 32-bit words); outputs r1[256] (high parts) and, in place of a, the low parts a0.

### `mldsa_decompose_88`

```c
void mldsa_decompose_88(int32_t a1[static 256], int32_t a0[static 256]);
```

**Operation.** Coefficient decomposition for ML-DSA (parameter set 44, GAMMA2 = (Q-1)/88)

**Sizes.** inputs `a0`[256] (32-bit words); output `a1`[256] (32-bit words), `a0`[256] (32-bit words)

**Aliasing.** Writes high parts to `a1` and, in place, the low parts to `a0` (the input array); `a1` must not overlap `a0`.

**Availability.** ARM only.

**Details.** For each coefficient a in [0,Q), computes (a1, a0) with a = a1*2*GAMMA2 + a0. Input a[256] (signed 32-bit words); outputs r1[256] (high parts) and, in place of a, the low parts a0.

### `mldsa_intt`

```c
void mldsa_intt(int32_t a[static 256], const int32_t zetas[static 624]);
```

**Operation.** Inverse number-theoretic transform for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words), `zetas`[624] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the `zetas` table must not overlap `a`.

**Availability.** x86 only.

### `mldsa_intt_arm`

```c
void mldsa_intt_arm(int32_t a[static 256], const int32_t z_78[static 384], const int32_t z_123456[static 160]);
```

**Operation.** Inverse number-theoretic transform for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words), `z_78`[384] (32-bit words), `z_123456`[160] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the twiddle tables `z_78`, `z_123456` must not overlap `a`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

### `mldsa_ntt`

```c
void mldsa_ntt(int32_t a[static 256], const int32_t zetas[static 624]);
```

**Operation.** Forward number-theoretic transform for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words), `zetas`[624] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the `zetas` table must not overlap `a`.

**Availability.** x86 only.

### `mldsa_ntt_arm`

```c
void mldsa_ntt_arm(int32_t a[static 256], const int32_t z_012345[144], const int32_t z_67[384]);
```

**Operation.** Forward number-theoretic transform for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words), `z_012345`[144] (32-bit words), `z_67`[384] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the twiddle tables `z_012345`, `z_67` must not overlap `a`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

### `mldsa_nttunpack`

```c
void mldsa_nttunpack(int32_t a[static 256]);
```

**Operation.** NTT unpack for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Operates in place on `a` (which must be 32-byte aligned).

**Availability.** x86 only.

**Details.** This function performs the unpacking transformation on NTT-domain polynomial coefficients, converting from a packed representation to a standard layout. The operation is performed in-place on a 256-element array of signed 32-bit integers. This is a supporting operation for ML-DSA signature operations. This implementation is derived from the public domain AVX2 Dilithium implementation from CRYSTALS-Dilithium optimized AVX2 implementation by Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé (https://github.com/pq-crystals/dilithium/tree/master/avx2)

### `mldsa_pointwise`

```c
void mldsa_pointwise(int32_t r[static 256], const int32_t a[static 256], const int32_t b[static 256]);
```

**Operation.** Pointwise multiplication of polynomials in NTT domain (Montgomery form)

**Sizes.** inputs `a`[256] (32-bit words), `b`[256] (32-bit words); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap inputs `a`, `b`.

**Availability.** ARM only.

**Details.** Performs pointwise multiplication of two polynomials in NTT domain using Montgomery arithmetic. The polynomials are represented as arrays of 256 signed 32-bit coefficients. This computes r[i] = montgomery_reduce(a[i] * b[i]) for i = 0..255

### `mldsa_pointwise_acc_l4`

```c
void mldsa_pointwise_acc_l4(int32_t r[static 256], const int32_t a[static 1024], const int32_t b[static 1024]);
```

**Operation.** Pointwise multiplication and accumulation of polynomials in ML-DSA NTT

**Sizes.** inputs `a`[1024] (32-bit words), `b`[1024] (32-bit words); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap inputs `a`, `b`.

**Availability.** ARM only.

**Details.** Performs pointwise multiply-accumulate of 4 polynomial pairs in NTT domain using Montgomery arithmetic: r[i] = montgomery_reduce(sum_{k=0}^{3} a[i + 256*k] * b[i + 256*k]) for i = 0..255 The Montgomery reduction is performed with: Q = 8380417 (MLDSA prime modulus) QINV = 58728449 (negative inverse of Q mod 2^32) R = 2^32 (Montgomery parameter)

### `mldsa_pointwise_acc_l4_x86`

```c
void mldsa_pointwise_acc_l4_x86(int32_t c[static 256], const int32_t a[static 1024], const int32_t b[static 1024], const int32_t qdata[static 16]);
```

**Operation.** Pointwise multiplication with accumulation for ML-DSA L4, x86 version

**Sizes.** inputs `a`[1024] (32-bit words), `b`[1024] (32-bit words), `qdata`[16] (32-bit words); output `c`[256] (32-bit words)

**Aliasing.** Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).

**Availability.** x86 only.

### `mldsa_pointwise_acc_l5`

```c
void mldsa_pointwise_acc_l5(int32_t r[static 256], const int32_t a[static 1280], const int32_t b[static 1280]);
```

**Operation.** Pointwise multiplication and accumulation of polynomials in ML-DSA NTT

**Sizes.** inputs `a`[1280] (32-bit words), `b`[1280] (32-bit words); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap inputs `a`, `b`.

**Availability.** ARM only.

**Details.** Performs pointwise multiply-accumulate of 5 polynomial pairs in NTT domain using Montgomery arithmetic: r[i] = montgomery_reduce(sum_{k=0}^{4} a[i + 256*k] * b[i + 256*k]) for i = 0..255 The Montgomery reduction is performed with: Q = 8380417 (MLDSA prime modulus) QINV = 58728449 (negative inverse of Q mod 2^32) R = 2^32 (Montgomery parameter)

### `mldsa_pointwise_acc_l5_x86`

```c
void mldsa_pointwise_acc_l5_x86(int32_t c[static 256], const int32_t a[static 1280], const int32_t b[static 1280], const int32_t qdata[static 16]);
```

**Operation.** Pointwise multiplication with accumulation for ML-DSA L5, x86 version

**Sizes.** inputs `a`[1280] (32-bit words), `b`[1280] (32-bit words), `qdata`[16] (32-bit words); output `c`[256] (32-bit words)

**Aliasing.** Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).

**Availability.** x86 only.

### `mldsa_pointwise_acc_l7`

```c
void mldsa_pointwise_acc_l7(int32_t r[static 256], const int32_t a[static 1792], const int32_t b[static 1792]);
```

**Operation.** Pointwise multiplication and accumulation of polynomials in ML-DSA NTT

**Sizes.** inputs `a`[1792] (32-bit words), `b`[1792] (32-bit words); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap inputs `a`, `b`.

**Availability.** ARM only.

**Details.** Performs pointwise multiply-accumulate of 7 polynomial pairs in NTT domain using Montgomery arithmetic: r[i] = montgomery_reduce(sum_{k=0}^{6} a[i + 256*k] * b[i + 256*k]) for i = 0..255 The Montgomery reduction is performed with: Q = 8380417 (MLDSA prime modulus) QINV = 58728449 (negative inverse of Q mod 2^32) R = 2^32 (Montgomery parameter)

### `mldsa_pointwise_acc_l7_x86`

```c
void mldsa_pointwise_acc_l7_x86(int32_t c[static 256], const int32_t a[static 1792], const int32_t b[static 1792], const int32_t qdata[static 16]);
```

**Operation.** Pointwise multiplication with accumulation for ML-DSA L7, x86 version

**Sizes.** inputs `a`[1792] (32-bit words), `b`[1792] (32-bit words), `qdata`[16] (32-bit words); output `c`[256] (32-bit words)

**Aliasing.** Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).

**Availability.** x86 only.

### `mldsa_pointwise_x86`

```c
void mldsa_pointwise_x86(int32_t c[static 256], const int32_t a[static 256], const int32_t b[static 256], const int32_t qdata[static 16]);
```

**Operation.** Pointwise multiplication of polynomials in NTT domain (Montgomery form) for ML-DSA, x86 version

**Sizes.** inputs `a`[256] (32-bit words), `b`[256] (32-bit words), `qdata`[16] (32-bit words); output `c`[256] (32-bit words)

**Aliasing.** Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).

**Availability.** x86 only.

### `mldsa_poly_use_hint_32`

```c
void mldsa_poly_use_hint_32(int32_t b[static 256], const int32_t a[static 256], const int32_t h[static 256]);
```

**Operation.** Use hint to correct high bits of decomposition (parameter sets 65/87)

**Sizes.** inputs `a`[256] (32-bit words), `h`[256] (32-bit words); output `b`[256] (32-bit words)

**Aliasing.** Output `b` must not overlap inputs `a`, `h`.

**Availability.** ARM only.

**Details.** Implements mld_use_hint for ML-DSA parameter sets 65/87: GAMMA2 = (Q-1)/32 = 261888 2*GAMMA2 = 523776 Output range: [0, 15] Algorithm per coefficient: 1. Decompose: a1 = round_down(a / 523776), a0 = a - a1*523776 If a > 31*GAMMA2 = 8118528, wrap: a1=0, a0=a-Q 2. delta = (a0 <= 0) ? -1 : 1 3. b = (a1 + delta * h) & 15

### `mldsa_poly_use_hint_88`

```c
void mldsa_poly_use_hint_88(int32_t b[static 256], const int32_t a[static 256], const int32_t h[static 256]);
```

**Operation.** Use hint to correct high bits of decomposition (parameter set 44)

**Sizes.** inputs `a`[256] (32-bit words), `h`[256] (32-bit words); output `b`[256] (32-bit words)

**Aliasing.** Output `b` must not overlap inputs `a`, `h`.

**Availability.** ARM only.

**Details.** Implements mld_use_hint for ML-DSA parameter set 44: GAMMA2 = (Q-1)/88 = 95232 2*GAMMA2 = 190464 Output range: [0, 43] Algorithm per coefficient: 1. Decompose: a1 = round_down(a / 190464), a0 = a - a1*190464 If a > 87*GAMMA2 = 8285184, wrap: a1=0, a0=a-Q 2. delta = (a0 <= 0) ? -1 : 1 3. b = min((a1 + delta * h) & ~mask_gt_43, 43) where mask_gt_43 clears values > 43 and umin clamps to 43

### `mldsa_polyz_unpack_17_arm`

```c
void mldsa_polyz_unpack_17_arm(int32_t r[static 256], const uint8_t b[static 576], const uint8_t t[static 64]);
```

**Operation.** Unpack packed z polynomial for ML-DSA (GAMMA1 = 2^17, parameter set 44)

**Sizes.** inputs `b`[576] (bytes), `t`[64] (bytes); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap the packed input `b` or the shuffle table `t`.

**Availability.** ARM only.

### `mldsa_polyz_unpack_19_arm`

```c
void mldsa_polyz_unpack_19_arm(int32_t r[static 256], const uint8_t b[static 640], const uint8_t t[static 64]);
```

**Operation.** Unpack packed z polynomial for ML-DSA (GAMMA1 = 2^19, parameter sets 65/87)

**Sizes.** inputs `b`[640] (bytes), `t`[64] (bytes); output `r`[256] (32-bit words)

**Aliasing.** Output `r` must not overlap the packed input `b` or the shuffle table `t`.

**Availability.** ARM only.

### `mldsa_reduce`

```c
void mldsa_reduce(int32_t a[static 256]);
```

**Operation.** Canonical reduction of polynomial coefficients for ML-DSA

**Sizes.** inputs `a`[256] (32-bit words); output `a`[256] (32-bit words)

**Aliasing.** Operates in place on `a` (which must be 32-byte aligned).

**Availability.** x86 only.

**Details.** This reduces each element of the 256-element array of 32-bit signed integers modulo 8380417 with the result being centered around zero, specifically -6283009 <= r <= 6283008, in-place. Each input coefficient must satisfy a <= 0x7fbfffff (2143289343); this rules out the top 0x400000 positive values, for which the internal "+ 4194304" rounding step would overflow a signed 32-bit word and give an incorrect (non-congruent) result. Every input in the standard ML-DSA coefficient range comfortably satisfies this.

### `mldsa_rej_uniform_VARIABLE_TIME`

```c
uint64_t mldsa_rej_uniform_VARIABLE_TIME(int32_t r[static 256],const uint8_t *buf,uint64_t buflen,const uint8_t *table);
```

**Operation.** Uniform rejection sampling for ML-DSA

**Sizes.** inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)

**Assumptions.** buflen is a multiple of 24.

**Aliasing.** No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).

**Stack use.** ARM 1088 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** Interprets the input buffer as packed 24-bit numbers with a length of buflen bytes, assumed to be a multiple of 24. Masks each to 23 bits and fills the output array with those numbers that are < q = 8380417, in the order of appearance, returning the total number of entries written, with a maximum of 256. The table argument is a specific precomputed table of constants that is defined alongside the proof (see also our test code). Like its ML-KEM counterpart, this is *not* a constant-time function. The time taken depends not only on the buffer size "buflen", but also how many elements of the buffer are needed to provide the 256 entries for the output.

### `mldsa_rej_uniform_VARIABLE_TIME_x86`

```c
uint32_t mldsa_rej_uniform_VARIABLE_TIME_x86(int32_t r[static 256], const uint8_t buf[static 840], const uint64_t table[static 256]);
```

**Operation.** Uniform rejection sampling for ML-DSA: extract 23-bit coefficients from

**Sizes.** inputs `buf`[840] (bytes), `table`[256] (64-bit words); output `r`[256] (32-bit words); returns count written (0..256)

**Assumptions.** buflen is a multiple of 24.

**Aliasing.** No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).

**Availability.** x86 only.

### `mldsa_rej_uniform_eta2_VARIABLE_TIME`

```c
uint64_t mldsa_rej_uniform_eta2_VARIABLE_TIME(int32_t r[static 256], const uint8_t *buf, unsigned buflen, const uint8_t table[static 4096]);
```

**Operation.** Rejection sampling with eta=2 for ML-DSA (parameter sets 44/87).

**Sizes.** inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)

**Assumptions.** buflen is a multiple of 8; 8 <= buflen.

**Aliasing.** No restrictions (the spec imposes no disjointness between `r` and `buf`).

**Stack use.** ARM 576 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** Extracts up to 256 coefficients in the range [-2, 2] from a buffer of SHAKE256 output bytes. Each input byte contributes two 4-bit nibbles; a nibble is accepted iff its value is < 15 (rejection sampling for uniform distribution on {0, ..., 14}), and the accepted value n is mapped to (2 - n mod 5) stored as int32. Uses a 256-entry lookup table (table[i] is a 16-byte TBL index permutation for the 8-bit acceptance mask i) to compact accepted nibbles via NEON TBL/TBL2.

### `mldsa_rej_uniform_eta4_VARIABLE_TIME`

```c
uint64_t mldsa_rej_uniform_eta4_VARIABLE_TIME(int32_t r[static 256], const uint8_t *buf, unsigned buflen, const uint8_t table[static 4096]);
```

**Operation.** Rejection sampling with eta=4 for ML-DSA (parameter set 65).

**Sizes.** inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)

**Assumptions.** buflen is a multiple of 8; 8 <= buflen.

**Aliasing.** No restrictions (the spec imposes no disjointness between `r` and `buf`).

**Stack use.** ARM 576 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** Extracts up to 256 coefficients in the range [-4, 4] from a buffer of SHAKE256 output bytes. Each input byte contributes two 4-bit nibbles; a nibble is accepted iff its value is < 9 (rejection sampling for uniform distribution on {0, ..., 8}), and the accepted value n is mapped to (4 - n) stored as int32. Uses a 256-entry lookup table (table[i] is a 16-byte TBL index permutation for the 8-bit acceptance mask i) to compact accepted nibbles via NEON TBL/TBL2. Inputs: r[256]    (int32_t, output)  — sampled coefficients; at most `outlen` written buf       (const uint8_t*)   — SHAKE256 output, buflen bytes buflen    (unsigned)         — number of bytes in buf (must be 8-divisible, >= 8) table[4096] (const uint8_t*) — 256 × 16-byte TBL permutation table

### `mlkem_basemul_k2`

```c
void mlkem_basemul_k2(int16_t r[static 256],const int16_t a[static 512],const int16_t b[static 512],const int16_t bt[static 256]);
```

**Operation.** Scalar product of 2-element polynomial vectors in NTT domain, with mulcache

**Sizes.** inputs `a`[512] (16-bit words), `b`[512] (16-bit words), `bt`[256] (16-bit words); output `r`[256] (16-bit words)

**Aliasing.** Output must not overlap any of its inputs.

**Stack use.** ARM 64 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The inputs a and b are considered as 2-element vectors of linear polynomials in the NTT domain (in Montgomery form), and the bt argument an analogous 2-element vector of mulcaches for the bi: a0 = a[0..255], a1 = a[256..511] b0 = b[0..255], b1 = b[256..511] bt0 = bt[0..127], bt1 = bt[128..255]

### `mlkem_basemul_k3`

```c
void mlkem_basemul_k3(int16_t r[static 256],const int16_t a[static 768],const int16_t b[static 768],const int16_t bt[static 384]);
```

**Operation.** Scalar product of 3-element polynomial vectors in NTT domain, with mulcache

**Sizes.** inputs `a`[768] (16-bit words), `b`[768] (16-bit words), `bt`[384] (16-bit words); output `r`[256] (16-bit words)

**Aliasing.** Output must not overlap any of its inputs.

**Stack use.** ARM 64 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The inputs a and b are considered as 3-element vectors of linear polynomials in the NTT domain (in Montgomery form), and the bt argument an analogous 3-element vector of mulcaches for the bi: a0 = a[0..255], a1 = a[256..511], a2 = a[512..767] b0 = b[0..255], b1 = b[256..511], b2 = b[512..767], bt0 = bt[0..127], bt1 = bt[128..255], bt2 = bt[256..383]

### `mlkem_basemul_k4`

```c
void mlkem_basemul_k4(int16_t r[static 256],const int16_t a[static 1024],const int16_t b[static 1024],const int16_t bt[static 512]);
```

**Operation.** Scalar product of 4-element polynomial vectors in NTT domain, with mulcache

**Sizes.** inputs `a`[1024] (16-bit words), `b`[1024] (16-bit words), `bt`[512] (16-bit words); output `r`[256] (16-bit words)

**Aliasing.** Output must not overlap any of its inputs.

**Stack use.** ARM 64 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The inputs a and b are considered as 4-element vectors of linear polynomials in the NTT domain (in Montgomery form), and the bt argument an analogous 4-element vector of mulcaches for the bi: a0 = a[0..255], a1 = a[256..511], a2 = a[512..767], a3 = a[768..1023] b0 = b[0..255], b1 = b[256..511], b2 = b[512..767], b3 = b[768..1023] bt0 = bt[0..127], bt1 = bt[128..255], bt2 = bt[256..383], bt3 = bt[384..511]

### `mlkem_frombytes`

```c
void mlkem_frombytes(int16_t r[static 256],const uint8_t a[static 384]);
```

**Operation.** Unpack ML-KEM polynomial coefficients as 12-bit numbers

**Sizes.** inputs `a`[384] (bytes); output `r`[256] (16-bit words)

**Aliasing.** Output polynomial `r` must not overlap the input byte array `a`; `r` must be 32-byte aligned.

**Availability.** x86 only.

**Details.** This accepts an array of 384 bytes and unpacks them into 256 16-bit numbers in the range 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime).

### `mlkem_intt`

```c
void mlkem_intt(int16_t a[static 256],const int16_t z_01234[static 80],const int16_t z_56[static 384]);
```

**Operation.** Inverse number-theoretic transform from ML-KEM

**Sizes.** inputs `a`[256] (16-bit words), `z_01234`[80] (16-bit words), `z_56`[384] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the twiddle tables `z_01234`, `z_56` must not overlap `a`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** The transform is in-place with input and output a[256], with the input in bitreversed order and the output mapped into the Montgomery domain via x |-> (2^16 * x) mod 3329. The two other parameters are expected to point to tables of constants whose definitions can be found in the mlkem-native repo (mlkem/native/aarch64/src/aarch64_zetas.c) or our "tests/test.c".

### `mlkem_intt_x86`

```c
void mlkem_intt_x86(int16_t a[static 256],const int16_t qdata[static 624]);
```

**Operation.** Inverse number-theoretic transform from ML-KEM

**Sizes.** inputs `a`[256] (16-bit words), `qdata`[624] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the `qdata` table must not overlap `a`.

**Availability.** x86 only.

### `mlkem_mulcache_compute`

```c
void mlkem_mulcache_compute(int16_t x[static 128],const int16_t a[static 256],const int16_t z[static 128],const int16_t t[static 128]);
```

**Operation.** Precompute the mulcache data for a polynomial in the NTT domain

**Sizes.** inputs `a`[256] (16-bit words), `z`[128] (16-bit words), `t`[128] (16-bit words); output `x`[128] (16-bit words)

**Aliasing.** Output (mulcache) must not overlap the input polynomial or the zeta tables.

**Availability.** ARM only.

**Details.** The input array a is assumed to represent 128 linear polynomials in the NTT domain, p_i = a[2i] + a[2i+1] * X where each p_i is in Fq[X]/(X^2-zeta^i'), with zeta^i' being a power of zeta = 17, with i bit-reversed as used for NTTs. For each such polynomial, the mulcache value is a[2i+1] * zeta^i' (modulo 3329 as usual), a value useful to perform base multiplication of polynomials efficiently. The two other table arguments z = zetas and t = twisted zetas are expected to point to tables of zeta-related constants whose definitions can be found in the mlkem-native repo (mlkem/native/aarch64/src/aarch64_zetas.c) or our "tests/test.c", as "mulcache_zetas" and "mulcache_zetas_twisted"

### `mlkem_mulcache_compute_x86`

```c
void mlkem_mulcache_compute_x86(int16_t x[static 128],const int16_t a[static 256],const int16_t qdata[static 624]);
```

**Operation.** Precompute the mulcache data for a polynomial in the NTT domain

**Sizes.** inputs `a`[256] (16-bit words), `qdata`[624] (16-bit words); output `x`[128] (16-bit words)

**Aliasing.** Output (mulcache) must not overlap the input polynomial or the `qdata` table.

**Availability.** x86 only.

### `mlkem_ntt`

```c
void mlkem_ntt(int16_t a[static 256],const int16_t z_01234[static 80],const int16_t z_56[static 384]);
```

**Operation.** Forward number-theoretic transform from ML-KEM

**Sizes.** inputs `a`[256] (16-bit words), `z_01234`[80] (16-bit words), `z_56`[384] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the twiddle tables `z_01234`, `z_56` must not overlap `a`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** The transform is in-place with input and output a[256], with the output in bitreversed order. The two other parameters are expected to point to tables of constants whose definitions can be found in the mlkem-native repo (mlkem/native/aarch64/src/aarch64_zetas.c) or our "tests/test.c".

### `mlkem_ntt_x86`

```c
void mlkem_ntt_x86(int16_t a[static 256],const int16_t qdata[static 624]);
```

**Operation.** Forward number-theoretic transform from ML-KEM x86 implementation

**Sizes.** inputs `a`[256] (16-bit words), `qdata`[624] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Transforms the coefficient array `a` in place; the `qdata` table must not overlap `a`.

**Availability.** x86 only.

### `mlkem_reduce`

```c
void mlkem_reduce(int16_t a[static 256]);
```

**Operation.** Canonical reduction of polynomial coefficients for ML-KEM

**Sizes.** inputs `a`[256] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Operates in place on `a`.

**Availability.** ARM and x86.

**Details.** This reduces each element of the 256-element array of 16-bit signed integers modulo 3329 with the result being 0 <= r < 3329, in-place. This is intended for use when that array represents polynomial coefficients for ML-KEM, but that is not relevant to its operation.

### `mlkem_rej_uniform_VARIABLE_TIME`

```c
uint64_t mlkem_rej_uniform_VARIABLE_TIME(int16_t r[static 256],const uint8_t *buf,uint64_t buflen,const uint8_t *table);
```

**Operation.** Uniform rejection sampling for ML-KEM

**Sizes.** inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (16-bit words); returns count written (0..256)

**Assumptions.** buflen is a multiple of 24.

**Aliasing.** No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).

**Stack use.** ARM 576 bytes, x86 528 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Interprets the input buffer as packed 12-bit numbers with a length of buflen bytes, assumed to be a multiple of 24. Fills the output array with those numbers from the packed buffer that are < 3329, in the order of appearance, returning the total number of entries written, with a maximum of 256. The table argument is a specific precomputed table of constants that is defined in this file (see also our test code): https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/src/rej_uniform_table.c

### `mlkem_tobytes`

```c
void mlkem_tobytes(uint8_t r[static 384],const int16_t a[static 256]);
```

**Operation.** Pack ML-KEM polynomial coefficients as 12-bit numbers

**Sizes.** inputs `a`[256] (16-bit words); output `r`[384] (bytes)

**Aliasing.** Output byte array `r` must not overlap the input polynomial `a`.

**Availability.** ARM and x86.

**Details.** This accepts an array of 256 16-bit numbers assumed to be in the range 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime). It packs them into the output array as 12-bit unsigned numbers.

### `mlkem_tomont`

```c
void mlkem_tomont(int16_t a[static 256]);
```

**Operation.** Conversion of ML-KEM polynomial coefficients to Montgomery form

**Sizes.** inputs `a`[256] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Operates in place on `a`.

**Availability.** ARM and x86.

**Details.** This converts each element of the 256-element array of 16-bit signed integers modulo 3329 into Montgomery form, giving a signed result satisfying (output[i] == 2^16 * input[i]) (mod 3329), without full modular reduction but with |output[i]| < 3329 guaranteed.

### `mlkem_unpack`

```c
void mlkem_unpack(int16_t a[static 256]);
```

**Operation.** Reorder ML-KEM polynomial coefficients for x86 implementation

**Sizes.** inputs `a`[256] (16-bit words); output `a`[256] (16-bit words)

**Aliasing.** Operates in place on `a` (which must be 32-byte aligned).

**Availability.** x86 only.

**Details.** This accepts an array of 256 16-bit numbers and reorders them.

### `p256_montjadd`

```c
void p256_montjadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 304 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p256_montjadd_alt`

```c
void p256_montjadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p256_montjdouble`

```c
void p256_montjdouble(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 272 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p256_montjdouble_alt`

```c
void p256_montjdouble_alt(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 192 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p256_montjmixadd`

```c
void p256_montjmixadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `p256_montjmixadd_alt`

```c
void p256_montjmixadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on NIST curve P-256 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 192 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `p256_montjscalarmul`

```c
void p256_montjscalarmul(uint64_t res[static 12],const uint64_t scalar[static 4],const uint64_t point[static 12]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for P-256

**Sizes.** inputs `scalar`[4], `point`[12]; output `res`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 1328 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p256_scalarmul. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^256 * x) mod p_256 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_256) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `p256_montjscalarmul_alt`

```c
void p256_montjscalarmul_alt(uint64_t res[static 12],const uint64_t scalar[static 4],const uint64_t point[static 12]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for P-256

**Sizes.** inputs `scalar`[4], `point`[12]; output `res`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 1248 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p256_scalarmul_alt. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^256 * x) mod p_256 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_256) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `p256_scalarmul`

```c
void p256_scalarmul(uint64_t res[static 8],const uint64_t scalar[static 4],const uint64_t point[static 8]);
```

**Operation.** Scalar multiplication for P-256

**Sizes.** inputs `scalar`[4], `point`[8]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 1328 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, returns the point (X,Y) = n * P. The input and output are affine points, and in the case of the point at infinity as the result, (0,0) is returned.

### `p256_scalarmul_alt`

```c
void p256_scalarmul_alt(uint64_t res[static 8],const uint64_t scalar[static 4],const uint64_t point[static 8]);
```

**Operation.** Scalar multiplication for P-256

**Sizes.** inputs `scalar`[4], `point`[8]; output `res`[8]

**Aliasing.** No restrictions.

**Stack use.** ARM 1248 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, returns the point (X,Y) = n * P. The input and output are affine points, and in the case of the point at infinity as the result, (0,0) is returned.

### `p256_scalarmulbase`

```c
void p256_scalarmulbase(uint64_t res[static 8],const uint64_t scalar[static 4],uint64_t blocksize,const uint64_t *table);
```

**Operation.** Scalar multiplication for precomputed point on NIST curve P-256

**Sizes.** inputs `scalar`[4], `table`[]; output `res`[8]

**Assumptions.** 2 <= blocksize; blocksize <= 31.

**Aliasing.** No restrictions.

**Stack use.** ARM 576 bytes, x86 696 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, the input argument "table" is expected to be a table of multiples of the point P in Montgomery-affine form, with each block corresponding to "blocksize" bits of the scalar as follows, where B = 2^{blocksize-1} (e.g. B = 8 for blocksize = 4): For each i,j with blocksize * i <= 256 and 1 <= j <= B the multiple 2^{blocksize * i} * j * P is stored at tab[8 * (B * i + (j - 1))], considered as uint64_t pointers or tab + 64 * (B * i + (j - 1)) as byte pointers.

### `p256_scalarmulbase_alt`

```c
void p256_scalarmulbase_alt(uint64_t res[static 8],const uint64_t scalar[static 4],uint64_t blocksize,const uint64_t *table);
```

**Operation.** Scalar multiplication for precomputed point on NIST curve P-256

**Sizes.** inputs `scalar`[4], `table`[]; output `res`[8]

**Assumptions.** 2 <= blocksize; blocksize <= 31.

**Aliasing.** No restrictions.

**Stack use.** ARM 576 bytes, x86 696 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-256, the input argument "table" is expected to be a table of multiples of the point P in Montgomery-affine form, with each block corresponding to "blocksize" bits of the scalar as follows, where B = 2^{blocksize-1} (e.g. B = 8 for blocksize = 4): For each i,j with blocksize * i <= 256 and 1 <= j <= B the multiple 2^{blocksize * i} * j * P is stored at tab[8 * (B * i + (j - 1))], considered as uint64_t pointers or tab + 64 * (B * i + (j - 1)) as byte pointers.

### `p384_montjadd`

```c
void p384_montjadd(uint64_t p3[static 18],const uint64_t p1[static 18],const uint64_t p2[static 18]);
```

**Operation.** Point addition on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18], `p2`[18]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** ARM 464 bytes, x86 400 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p384_montjadd_alt`

```c
void p384_montjadd_alt(uint64_t p3[static 18],const uint64_t p1[static 18],const uint64_t p2[static 18]);
```

**Operation.** Point addition on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18], `p2`[18]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** 400 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p384_montjdouble`

```c
void p384_montjdouble(uint64_t p3[static 18],const uint64_t p1[static 18]);
```

**Operation.** Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** ARM 464 bytes, x86 392 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p384_montjdouble_alt`

```c
void p384_montjdouble_alt(uint64_t p3[static 18],const uint64_t p1[static 18]);
```

**Operation.** Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** ARM 384 bytes, x86 392 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `p384_montjmixadd`

```c
void p384_montjmixadd(uint64_t p3[static 18],const uint64_t p1[static 18],const uint64_t p2[static 12]);
```

**Operation.** Point mixed addition on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18], `p2`[12]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** 352 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `p384_montjmixadd_alt`

```c
void p384_montjmixadd_alt(uint64_t p3[static 18],const uint64_t p1[static 18],const uint64_t p2[static 12]);
```

**Operation.** Point mixed addition on NIST curve P-384 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[18], `p2`[12]; output `p3`[18]

**Aliasing.** No restrictions.

**Stack use.** 352 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `p384_montjscalarmul`

```c
void p384_montjscalarmul(uint64_t res[static 18],const uint64_t scalar[static 6],const uint64_t point[static 18]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for P-384

**Sizes.** inputs `scalar`[6], `point`[18]; output `res`[18]

**Aliasing.** No restrictions.

**Stack use.** ARM 3168 bytes, x86 3144 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p384_scalarmul. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^384 * x) mod p_384 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-384, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_384) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `p384_montjscalarmul_alt`

```c
void p384_montjscalarmul_alt(uint64_t res[static 18],const uint64_t scalar[static 6],const uint64_t point[static 18]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for P-384

**Sizes.** inputs `scalar`[6], `point`[18]; output `res`[18]

**Aliasing.** No restrictions.

**Stack use.** ARM 3104 bytes, x86 3144 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p384_scalarmul_alt. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^384 * x) mod p_384 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-384, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_384) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `p521_jadd`

```c
void p521_jadd(uint64_t p3[static 27],const uint64_t p1[static 27],const uint64_t p2[static 27]);
```

**Operation.** Point addition on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27], `p2`[27]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 816 bytes, x86 616 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input points p1 and p2 are fully reduced mod p_521, that both z coordinates are nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `p521_jadd_alt`

```c
void p521_jadd_alt(uint64_t p3[static 27],const uint64_t p1[static 27],const uint64_t p2[static 27]);
```

**Operation.** Point addition on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27], `p2`[27]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 592 bytes, x86 624 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input points p1 and p2 are fully reduced mod p_521, that both z coordinates are nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `p521_jdouble`

```c
void p521_jdouble(uint64_t p3[static 27],const uint64_t p1[static 27]);
```

**Operation.** Point doubling on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 752 bytes, x86 608 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input point are fully reduced mod p_521 and that the z coordinate is not zero.

### `p521_jdouble_alt`

```c
void p521_jdouble_alt(uint64_t p3[static 27],const uint64_t p1[static 27]);
```

**Operation.** Point doubling on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 592 bytes, x86 624 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input point are fully reduced mod p_521 and that the z coordinate is not zero.

### `p521_jmixadd`

```c
void p521_jmixadd(uint64_t p3[static 27],const uint64_t p1[static 27],const uint64_t p2[static 18]);
```

**Operation.** Point mixed addition on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27], `p2`[18]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 608 bytes, x86 544 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity. It is assumed that all the coordinates of the input points p1 and p2 are fully reduced mod p_521, that the z coordinate of p1 is nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `p521_jmixadd_alt`

```c
void p521_jmixadd_alt(uint64_t p3[static 27],const uint64_t p1[static 27],const uint64_t p2[static 18]);
```

**Operation.** Point mixed addition on NIST curve P-521 in Jacobian coordinates

**Sizes.** inputs `p1`[27], `p2`[18]; output `p3`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 512 bytes, x86 552 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity. It is assumed that all the coordinates of the input points p1 and p2 are fully reduced mod p_521, that the z coordinate of p1 is nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `p521_jscalarmul`

```c
void p521_jscalarmul(uint64_t res[static 27],const uint64_t scalar[static 9],const uint64_t point[static 27]);
```

**Operation.** Jacobian form scalar multiplication for P-521

**Sizes.** inputs `scalar`[9], `point`[27]; output `res`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 4816 bytes, x86 4736 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p521_scalarmul. Here, input and output points are assumed to be in Jacobian form with a triple (x,y,z) representing the affine point (x/z^2,y/z^3) when z is nonzero or the point at infinity (group identity) if z = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-521, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_521) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `p521_jscalarmul_alt`

```c
void p521_jscalarmul_alt(uint64_t res[static 27],const uint64_t scalar[static 9],const uint64_t point[static 27]);
```

**Operation.** Jacobian form scalar multiplication for P-521

**Sizes.** inputs `scalar`[9], `point`[27]; output `res`[27]

**Aliasing.** No restrictions.

**Stack use.** ARM 4672 bytes, x86 4744 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version p521_scalarmul. Here, input and output points are assumed to be in Jacobian form with a triple (x,y,z) representing the affine point (x/z^2,y/z^3) when z is nonzero or the point at infinity (group identity) if z = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve P-521, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_521) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `secp256k1_jadd`

```c
void secp256k1_jadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 256 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input points p1 and p2 are fully reduced mod p_256k1, that both z coordinates are nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `secp256k1_jadd_alt`

```c
void secp256k1_jadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input points p1 and p2 are fully reduced mod p_256k1, that both z coordinates are nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `secp256k1_jdouble`

```c
void secp256k1_jdouble(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 400 bytes, x86 424 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input point are fully reduced mod p_256k1 and that the z coordinate is not zero.

### `secp256k1_jdouble_alt`

```c
void secp256k1_jdouble_alt(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 384 bytes, x86 424 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). It is assumed that all coordinates of the input point are fully reduced mod p_256k1 and that the z coordinate is not zero.

### `secp256k1_jmixadd`

```c
void secp256k1_jmixadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity. It is assumed that all the coordinates of the input points p1 and p2 are fully reduced mod p_256k1, that the z coordinate of p1 is nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `secp256k1_jmixadd_alt`

```c
void secp256k1_jmixadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on SECG curve secp256k1 in Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 192 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples. A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity. It is assumed that all the coordinates of the input points p1 and p2 are fully reduced mod p_256k1, that the z coordinate of p1 is nonzero and that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine point as".

### `sha3_keccak2_f1600`

```c
void sha3_keccak2_f1600(uint64_t a[static 50],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3, batch of two independent operations

**Sizes.** inputs `a`[50], `rc`[24]; output `a`[50]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** The input/output argument is in effect two 25-element Keccak arrays a[0...24] and a[25..49], which could be considered as type a[25][2]. Thinking of each such input/output array as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification:

### `sha3_keccak2_f1600_alt`

```c
void sha3_keccak2_f1600_alt(uint64_t a[static 50],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3, batch of two independent operations

**Sizes.** inputs `a`[50], `rc`[24]; output `a`[50]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** The input/output argument is in effect two 25-element Keccak arrays a[0...24] and a[25..49], which could be considered as type a[25][2]. Thinking of each such input/output array as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification:

### `sha3_keccak4_f1600`

```c
void sha3_keccak4_f1600(uint64_t a[static 100],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3, batch of four independent operations

**Sizes.** inputs `a`[100], `rc`[24]; output `a`[100]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 224 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86.

**Details.** The input/output argument is in effect four 25-element Keccak arrays a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered as type a[25][4]. Thinking of each such input/output array as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification:

### `sha3_keccak4_f1600_alt`

```c
// ARM:
void sha3_keccak4_f1600_alt(uint64_t a[static 100],const uint64_t rc[static 24]);
// x86:
void sha3_keccak4_f1600_alt(uint64_t a[static 100],const uint64_t rc[static 24],const uint64_t rho8[static 4],const uint64_t rho56[static 4]);
```

**Operation.** Keccak-f1600 permutation for SHA3, batch of four independent operations

**Sizes.** inputs `a`[100], `rc`[24]; output `a`[100]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 224 bytes, x86 none (below the stack pointer)

**Availability.** ARM and x86. On x86 this takes two extra input arguments `rho8[4]` and `rho56[4]` (rotation-constant tables); on ARM the prototype is just `(a[100], rc[24])`.

**Details.** The input/output argument is in effect four 25-element Keccak arrays a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered as type a[25][4]. Thinking of each such input/output array as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification:

### `sha3_keccak4_f1600_alt2`

```c
void sha3_keccak4_f1600_alt2(uint64_t a[static 100],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3, batch of four independent operations

**Sizes.** inputs `a`[100], `rc`[24]; output `a`[100]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 224 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** The input/output argument is in effect four 25-element Keccak arrays a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered as type a[25][4]. Thinking of each such input/output array as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification:

### `sha3_keccak_f1600`

```c
void sha3_keccak_f1600(uint64_t a[static 25],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3

**Sizes.** inputs `a`[25], `rc`[24]; output `a`[25]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 128 bytes, x86 256 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Thinking of the input/output array a as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification: https://keccak.team/keccak_specs_summary.html#roundConstants

### `sha3_keccak_f1600_alt`

```c
void sha3_keccak_f1600_alt(uint64_t a[static 25],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3

**Sizes.** inputs `a`[25], `rc`[24]; output `a`[25]

**Aliasing.** Output `a` must not overlap `rc`.

**Stack use.** ARM 64 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** Thinking of the input/output array a as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification: https://keccak.team/keccak_specs_summary.html#roundConstants

### `sha3_keccak_f1600_alt2`

```c
void sha3_keccak_f1600_alt2(uint64_t a[static 25],const uint64_t rc[static 24]);
```

**Operation.** Keccak-f1600 permutation for SHA3

**Sizes.** inputs `a`[25], `rc`[24]; output `a`[25]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes (below the stack pointer)

**Availability.** ARM only.

**Details.** Thinking of the input/output array a as a row-major flattening of a 5x5 matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24 rounds with the distinct round constants rc[i] for each one. For correct operation, the input pointer rc should point at the standard round constants as in the specification: https://keccak.team/keccak_specs_summary.html#roundConstants

### `sm2_montjadd`

```c
void sm2_montjadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 240 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `sm2_montjadd_alt`

```c
void sm2_montjadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 12]);
```

**Operation.** Point addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 224 bytes, x86 272 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `sm2_montjdouble`

```c
void sm2_montjdouble(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `sm2_montjdouble_alt`

```c
void sm2_montjdouble_alt(uint64_t p3[static 12],const uint64_t p1[static 12]);
```

**Operation.** Point doubling on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 192 bytes, x86 232 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := 2 * p1 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).

### `sm2_montjmixadd`

```c
void sm2_montjmixadd(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 208 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `sm2_montjmixadd_alt`

```c
void sm2_montjmixadd_alt(uint64_t p3[static 12],const uint64_t p1[static 12],const uint64_t p2[static 8]);
```

**Operation.** Point mixed addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates

**Sizes.** inputs `p1`[12], `p2`[8]; output `p3`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 192 bytes, x86 240 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Does p3 := p1 + p2 where all points are regarded as Jacobian triples with each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2. A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3). The "mixed" part means that p2 only has x and y coordinates, with the implicit z coordinate assumed to be the identity.

### `sm2_montjscalarmul`

```c
void sm2_montjscalarmul(uint64_t res[static 12],const uint64_t scalar[static 4],const uint64_t point[static 12]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for GM/T 0003-2012 curve SM2

**Sizes.** inputs `scalar`[4], `point`[12]; output `res`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 1264 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version sm2_scalarmul. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^256 * x) mod p_sm2 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve SM2, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_sm2) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `sm2_montjscalarmul_alt`

```c
void sm2_montjscalarmul_alt(uint64_t res[static 12],const uint64_t scalar[static 4],const uint64_t point[static 12]);
```

**Operation.** Montgomery-Jacobian form scalar multiplication for GM/T 0003-2012 curve SM2

**Sizes.** inputs `scalar`[4], `point`[12]; output `res`[12]

**Aliasing.** No restrictions.

**Stack use.** ARM 1248 bytes, x86 1368 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** This function is a variant of its affine point version sm2_scalarmul_alt. Here, input and output points are assumed to be in Jacobian form with their coordinates in the Montgomery domain. Thus, if priming indicates Montgomery form, x' = (2^256 * x) mod p_sm2 etc., each point argument is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when z' is nonzero or the point at infinity (group identity) if z' = 0. Given scalar = n and point = P, assumed to be on the NIST elliptic curve SM2, returns a representation of n * P. If the result is the point at infinity (either because the input point was or because the scalar was a multiple of p_sm2) then the output is guaranteed to represent the point at infinity, i.e. to have its z coordinate zero.

### `word_bytereverse`

```c
uint64_t word_bytereverse(uint64_t a);
```

**Operation.** Reverse the order of bytes in a 64-bit word

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_clz`

```c
uint64_t word_clz(uint64_t a);
```

**Operation.** Count leading zero bits in a single word

**Sizes.** Input a; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_ctz`

```c
uint64_t word_ctz(uint64_t a);
```

**Operation.** Count trailing zero bits in a single word

**Sizes.** Input a; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_divstep59`

```c
int64_t word_divstep59(int64_t m[2][2],int64_t d,uint64_t f,uint64_t g);
```

**Operation.** Perform 59 "divstep" iterations and return signed matrix of updates

**Sizes.** Inputs d, f, g; output m[2][2] and function return (updated d)

**Stack use.** ARM none, x86 32 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_max`

```c
uint64_t word_max(uint64_t a, uint64_t b);
```

**Operation.** Return maximum of two unsigned 64-bit words

**Sizes.** Inputs a, b; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_min`

```c
uint64_t word_min(uint64_t a, uint64_t b);
```

**Operation.** Return minimum of two unsigned 64-bit words

**Sizes.** Inputs a, b; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_negmodinv`

```c
uint64_t word_negmodinv(uint64_t a);
```

**Operation.** Single-word negated modular inverse (-1/a) mod 2^64

**Sizes.** Input a; output function return

**Availability.** ARM and x86.

**Details.** A 64-bit function that returns a negated multiplicative inverse mod 2^64 of its input, assuming that input is odd. Given odd input a, the result z will satisfy a * z + 1 == 0 (mod 2^64), i.e. a 64-bit word multiplication a * z will give -1.

### `word_popcount`

```c
uint64_t word_popcount(uint64_t a);
```

**Operation.** Count number of set bits in a single 64-bit word (population count)

**Sizes.** Input a; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

### `word_recip`

```c
uint64_t word_recip(uint64_t a);
```

**Operation.** Single-word reciprocal, underestimate of floor(2^128 / a) - 2^64

**Sizes.** Input a; output function return

**Stack use.** ARM none, x86 16 bytes (below the stack pointer)

**Availability.** ARM and x86.

**Details.** Given an input word "a" with its top bit set (i.e. 2^63 <= a < 2^64), the result "x" is implicitly augmented with a leading 1 giving x' = 2^64 + x. The result is x' = ceil(2^128 / a) - 1, which except for the single special case a = 2^63 is the same thing as x' = floor(2^128 / a).
