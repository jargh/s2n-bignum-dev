# The WireGuard handshake image

The machine code that the proofs in `arm/proofs/wireguard` are about: the
handshake of the Linux kernel's WireGuard driver and the parts of the kernel
crypto library that it uses, from Linux 6.18.64 (LTS), compiled for AArch64
by gcc 13 with -O2 and linked into one image.

## Contents of the image

- `drivers/net/wireguard`: `noise.c` (the Noise_IKpsk2 handshake messages,
  the keypairs and the setup functions), `cookie.c` (MACs and cookie
  replies) and `peerlookup.c` (the tables of indices and public keys).
- `lib/crypto`: BLAKE2s, ChaCha20 (with HChaCha20), Poly1305 (the 64-bit
  donna code), ChaCha20-Poly1305 and XChaCha20-Poly1305, the wrappers of
  Curve25519, `crypto_memneq` and `crypto_xor`. The portable C versions are
  used throughout: `wg_generic_crypto.h` turns off the arm64 versions that
  the kernel configuration forces on.
- `wg_env.S`: the kernel data that the code refers to directly (the zero
  page, `kimage_voffset`, `memstart_addr`), as writable data of the image.

Everything else that the code calls (memset and memcpy, locks, random
bytes, time, `curve25519_generic` and the rest) is outside the image and is
called through its procedure linkage table (PLT); the proofs give each such
function a contract (`arm/proofs/wireguard/contracts.ml`).

## Building

`build.sh TARBALL OUTDIR` builds the image from the release tarball
(`linux-6.18.64.tar.xz` from cdn.kernel.org, whose SHA-256 it checks) with
the kernel's own build system: arm64 defconfig plus WireGuard, without the
stack protector, pointer authentication, BTI and the function tracer, which
the AArch64 model does not cover. It links the objects with
`wireguard.lds` into `OUTDIR/wireguard.so` at address 0. The toolchain
prefix is `CROSS_COMPILE` (default `aarch64-linux-gnu-`). The image that
the proofs are about has SHA-256
a110b25831dd6b6cc765db2bd699c000fa1d1a8880774cbd729e3cf73690f6a3.

From the binary:

- `gen_wireguard_s.py` generates the transcription `gcc13_O2/wireguard.S`,
  and `check_transcription.py` checks that it has the same code. The proofs
  load the bytes of `gcc13_O2/wireguard.o`, which `make
  wireguard/gcc13_O2/wireguard.o` in `arm` assembles from the transcription
  (a rule of its own, as the kernel code uses x18; it gives the same object
  file byte for byte);
- `gen_layout.py` generates `arm/proofs/wireguard/gcc13_O2/layout.ml`, the
  names of the addresses (functions, labels inside them, data, PLT stubs and
  GOT entries);
- `gen_offsets.sh` and `wg_offsets.c` give the offsets of the fields of the
  kernel structures that the specifications use.

`tests/wireguard` has differential tests of the image against the
specification (through a Python transcription of it).

## Licensing and provenance

The image, its transcription `gcc13_O2/wireguard.S` and the object file
assembled from it are compiled from Linux 6.18.64, so they are covered by
the licences of the kernel files that went into them:

| Files | Licence | Authors |
|---|---|---|
| `drivers/net/wireguard/noise.c`, `cookie.c`, `peerlookup.c` and their headers | GPL-2.0 | Jason A. Donenfeld |
| `lib/crypto/blake2s.c`, `chacha20poly1305.c`, `poly1305-donna64.c`, `curve25519.c` | GPL-2.0 OR MIT | Jason A. Donenfeld |
| `lib/crypto/chacha.c`, `chacha-block-generic.c`, `poly1305.c` | GPL-2.0-or-later | Martin Willi |
| `lib/crypto/memneq.c` | BSD or GPL-2.0 (dual) | Daniel Borkmann, OpenVPN Technologies |
| `lib/crypto/utils.c` | GPL-2.0-or-later | Herbert Xu |

and the kernel headers that they include. The transcription is therefore
marked GPL-2.0. Its source is the release tarball, which `build.sh` checks,
with the files here. The layout file
`arm/proofs/wireguard/gcc13_O2/layout.ml` is generated from the binary: it
holds only the names, addresses and sizes of its symbols.

Everything else for the WireGuard proofs is new work under s2n-bignum's
licence (Apache-2.0 OR ISC OR MIT-0):
- this directory's build files, scripts, `wg_env.S`, `wireguard.lds`,
  `wg_offsets.c` (compiled with the kernel's headers) and
  `wg_generic_crypto.h`;
- the specifications in `common`;
- the proofs in `arm/proofs/wireguard` and `arm/proofs/utils/wireguard.ml`;
- the tests in `tests/wireguard`, which use the test vectors of RFC 7693
  and RFC 8439.

The specifications describe what the kernel code does, and name its
functions, structure fields and offsets, but contain none of its source.

Some files come from the mlkem-arm branch of s2n-bignum. `gen_layout.py`,
`gen_wireguard_s.py`, `check_transcription.py` and
`arm/proofs/wireguard/relative.ml` are adapted from files there, and each
says so, as does the one rule taken from there in
`arm/proofs/utils/wireguard.ml`. `common/layout.ml` is the file of the
mldsa-arm branch unchanged. The AArch64 model has one addition, for the PLT stubs:
the BR instruction, in `arm/proofs/decode.ml`, `instruction.ml` and
`simulator_iclasses.ml`.
