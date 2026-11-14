# Compiled code from zstd's Huffman decoding

This directory contains AArch64 code compiled from zstd's decoding of
Huffman-coded literals and of FSE-compressed Huffman weights, for
verification against the specification in `../../common/rfc8878.ml` (RFC
8878, sections 4.1 and 4.2). Like `../puff`, it is a case study in verifying
compiler-generated code outside cryptography, here of a widely used library:
the C code is compiled as it is, as part of a shared library in the way
that zstd builds `libzstd.so`. The code is only used for the proofs and is
not part of the library.

## Source of the code

`zstd_huf_gcc12_O2.S` is a transcription of `libzstd_huf.so`, built from
zstd 1.5.7 (commit `f8745da6`) by gcc 12.3.0 for AArch64, from nixpkgs
commit `b134951a` (the version of gcc 12 that mlkem-native uses), with
`build_zstd.sh`. The library consists of the four files of zstd that its
Huffman decoding uses, with these SHA-256 hashes:

```
lib/common/entropy_common.c
  7dfce29c6bc807645b1f0c373dad94bbb49603b175a84e72d1739bf9df65feb8
lib/common/fse_decompress.c
  84eba7030a036b36363a5108e760428ce549f1a833bec6464dc755f6ed51a6fb
lib/decompress/huf_decompress.c
  710a88d877d5dc5c83a4f839392996f337ec81cf38006c4a5be6042de5b54828
lib/common/error_private.c
  3f5873b2626ca1cdf554b7ec7b04ea0ef296fd0f6882d7fad42448b7e2dbb41c
```

compiled with the flags that zstd's `lib/Makefile` uses for `libzstd.so`,
except for `-O2` instead of `-O3`:

```
gcc -O2 -fPIC -fvisibility=hidden -fno-stack-protector -Wa,--noexecstack \
    -DXXH_NAMESPACE=ZSTD_ -DDEBUGLEVEL=0 -c ...
```

and `zhuf_api.c`, which has exported entry points for testing, since the
functions themselves are hidden, as they are in `libzstd.so`, so that the
calls between them are direct. The stack protector, which the nixpkgs
compiler wrapper enables by default, is turned off, as it was for puff. The
SHA-256 of the binary is

```
9981d6f455e7e2c6ef239dd464e3a71e09386df01783f5bafbd411e6a79ba89d
```

The code was built on x86-64 by running the native AArch64 compiler under
qemu-user, so `build_zstd.sh` takes the compiler as the environment
variable `GCC`. It also builds `zhuf_run` from `../../tests/zstd`, a test
program whose decoding uses the library, which
`../../tests/zstd/difftest.py` uses to compare the binary with the Python
version of the specification there.

## The transcription

`zstd_huf_gcc12_O2.S` is the start of the first loadable segment of the
binary, from address 0 up to the end of the read-only data at 0x7d00,
generated from the disassembly as for puff: the ELF header and other data
are given as `.quad` directives, and it assembles to exactly the bytes in
the binary, with no relocations. The code uses the register x18, which is
an ordinary temporary register on Linux, so the `Makefile` has a rule to
assemble it without the check for x18 that the other code has. The
functions in the decoding of single-stream Huffman-coded literals are at
these addresses:

| Function                                     | Address |
|----------------------------------------------|---------|
| `HUF_readStats_body_default`                 | 0x770   |
| `FSE_readNCount_body_default`                | 0x940   |
| `FSE_readNCount_bmi2` (a branch to the above)| 0xc60   |
| `FSE_readNCount` (a branch to the above)     | 0xc64   |
| `HUF_readStats_wksp` (a branch to the first) | 0xca0   |
| `FSE_buildDTable_internal`                   | 0xe80   |
| `FSE_decompress_wksp_bmi2`                   | 0x10f4  |
| `HUF_decompress1X1_usingDTable_internal` (*) | 0x2850  |
| `HUF_readDTableX1_wksp`                      | 0x66d4  |
| `HUF_decompress1X1_DCtx_wksp`                | 0x7340  |

(*) named `HUF_decompress1X1_usingDTable_internal.constprop.0` in the
binary, a copy of the function specialized for its constant arguments.

gcc has inlined `FSE_decompress_usingDTable_generic` (in both its modes),
`FSE_decompress_wksp_body`, `HUF_readStats_body` and the bit stream
functions of `bitstream.h`. The calls of `memcpy` and `memset` go through
the procedure linkage table, at 0x640 and 0x660. The decoding of the bit
streams reads the table `BIT_mask` in the read-only data at 0x7b70, and
takes the address of a word of zeros there (`zeroFilled`, at 0x7b60 and
0x7bf0) once a stream has been read past its start. The functions use no
writable data of the library: their tables and workspaces are given by the
caller.

After building the object file, `../puff/check_transcription.py` checks
that it is byte-for-byte identical to the binary, e.g. in the `arm`
directory:

```
make zstd/zstd_huf_gcc12_O2.o
python3 puff/check_transcription.py zstd/zstd_huf_gcc12_O2.o - \
  <build>/libzstd_huf.so 0x0
```

## License

The code in the transcription is compiled from zstd, which is available
under either the BSD license below or the GNU General Public License,
version 2, at the option of the user (see zstd's `LICENSE` and `COPYING`):

```
BSD License

For Zstandard software

Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

 * Redistributions of source code must retain the above copyright notice,
   this list of conditions and the following disclaimer.

 * Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

 * Neither the name Facebook, nor Meta, nor the names of its contributors
   may be used to endorse or promote products derived from this software
   without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
```
