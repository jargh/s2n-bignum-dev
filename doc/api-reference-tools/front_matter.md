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
is called out explicitly. For a given output buffer the possibilities are:

* **may coincide with or overlap `x` arbitrarily** — no restriction at all: the
  output may equal `x`, or partially overlap it, in any way. (Typical of the
  fixed-size field and elliptic-curve routines, which copy their inputs into a
  private stack frame before computing.)
* **may be the same buffer as `x` (exact aliasing only — no partial overlap)** —
  in-place operation is supported (`z` and `x` may be the identical pointer with
  identical length), but a *partial* overlap, where the buffers share some but not
  all memory, is forbidden. (Typical of the "linear" generic-size routines like
  `bignum_add`.)
* **must not overlap `x`** — the output must be entirely disjoint from that
  input; passing overlapping buffers voids the guarantee. (Typical of the
  generic-size multiply/reduce routines that revisit their inputs while writing
  output.)

Unless stated otherwise, output and **temporary** buffers must always be
disjoint from each other and from the inputs, and *distinct output buffers* must
be disjoint from each other. Where a function takes a temporary buffer, the
entry says so explicitly.

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

<!-- INDEX -->

---

## Functions

<!-- BODY -->
