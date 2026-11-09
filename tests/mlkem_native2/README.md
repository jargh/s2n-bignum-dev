# Tests and benchmarks of the ML-KEM API in assembly

This directory has the tests and benchmarks used to develop the functions
in `arm/mlkem_native2` and the new leaves in `arm/mlkem`. They compare the
functions with mlkem-native's portable C, which serves as the reference,
and are separate from s2n-bignum's own tests and from the build: nothing
here is built by the Makefiles.

They run on an AArch64 Linux machine with the SHA3 extension, and need
git, gcc (or another C compiler as `CC`), python3 and, to build valgrind,
curl and the usual tools for building C programs. Everything downloaded
or built goes under `work/` here (or `WORK`; see `env.sh` for this and
the other settings).

## Setup

    ./setup.sh

fetches mlkem-native at the commit the tests are pinned to (9b96caa1),
fetches the ACVP (v1.1.0.43) and Wycheproof vectors with mlkem-native's
own clients, and builds the reference library: mlkem-native's portable C
for all three parameter sets with the namespace prefix `ref`.

The steps under valgrind need one that can run the SHA3 instructions
BCAX, RAX1 and XAR, which valgrind 3.28.0 cannot (of the four, it only
decodes EOR3). With `VALGRIND_PATCH` set to a patch for 3.28.0 that adds
them (not included here), `setup.sh` also builds that valgrind into
`work/valgrind`, where the scripts find it; `VALGRIND` selects another.
Without one, those steps are skipped.

## Running the tests

    ./build.sh && CTFLAGS=-DMLKEM_CT_TESTING ./build.sh
    CTLIBS="$(ls work/obj_ct/*.o)" ./gate.sh asm work/obj/*.o
    ./leafmid.sh

`build.sh` builds the objects with the rules of `arm/Makefile` into
`work/obj`, and with `CTFLAGS` into `work/obj_ct`, where the per-level
files are preprocessed with `MLKEM_CT_TESTING` defined, which marks rho
public after key generation derives it. Both add `randomized.c`, the
randomized `mlkemL_keypair` and `mlkemL_enc` in C on top of the
deterministic functions.

`gate.sh NAME LIB...` is the gate for any library with the API (about 10
seconds here; results in `work/build/NAME`):

 - test_api: differential tests of keypair_derand, enc_derand, dec,
   check_pk and check_sk (and of the randomized keypair and enc if
   present) against the reference, by default 8 shards of 2000
   iterations per level, with random inputs and the rare paths: implicit
   rejection, invalid public keys (a coefficient >= q), invalid secret
   keys (a wrong H(pk) or embedded pk), secret vectors with coefficients
   >= q (which dec must accept), and all-0 and all-0xff seeds. Outputs
   sit between guard bytes, and inputs must be unchanged. It also counts
   the matrix polynomials that needed a fourth SHAKE128 block (about
   0.8%).
 - KAT: the SHA-256 of mlkem-native's KAT output, against its META.yml.
 - ACVP and Wycheproof, with mlkem-native's clients and drivers.
 - memcheck: test_api with heap buffers of the exact sizes.
 - constant time: test_ct under memcheck with the secrets undefined, using
   the libraries in `CTLIBS` (the build with `MLKEM_CT_TESTING`).
 - ABI: test_abi calls each function through abi_stub.S with random
   x8-x29 (x18 too) and q0-q31 and its own stack; x19-x29, d8-d15, sp and
   x18 must survive, and no 16-byte window of a secret (the coins, the
   seeds derived from them, the secret vector, the shared secret, z) may
   be left on the stack. It reports the stack depth and the bytes left
   there (`work/build/NAME/abi.log`).
 - BTI: test_api and test_abi again, linked so that the kernel enforces
   BTI (`bti_start.S` explains how), which checks that every function
   reached by an indirect call has a landing pad.

`leafmid.sh [OBJDIR]` tests the new leaves (test_leaf: each against the
reference, exhaustively over the values of each coefficient or byte
where the input space allows) and the middle layer (test_mid:
mlkem_gen_matrix with its hash jobs and noise, mlkem_getnoise,
mlkem_hash_h and mlkem_hash_g), natively, under memcheck and with BTI
enforced.

`mutants.sh` checks the tests themselves, with a library that forwards
to the reference with one deliberate fault at a time (`mutants.c`): each
fault must be caught and the harmless changes must pass.

## Benchmarks

    ./baseline.sh clang-18
    ./bench.sh asm work/obj/*.o

`baseline.sh` builds mlkem-native's multilevel library with its native
backends, as its `examples/multilevel_build_native` does, and measures
it; `bench.sh` measures a library and compares it with that baseline.
The cycle counts come from the virtual counter and a measured clock
(there may be no access to the performance counters), as medians of 31
runs of 200 calls; `CORE` pins the run to a core.
