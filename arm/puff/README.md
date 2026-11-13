# Compiled code from zlib's puff

This directory contains AArch64 code compiled from `puff.c`, Mark Adler's
small DEFLATE decoder in zlib's `contrib/puff`, for verification against
the specification of DEFLATE decoding in `../../common/rfc1951.ml`. It is a
case study in verifying compiler-generated code outside cryptography: the
C code is compiled as it is, with its use of `setjmp` and `longjmp` and its
tables built on first use. The code is only used for the proofs and is not
part of the library.

## Source of the code

`puff_gcc12_O2.S` is a transcription of `libpuff.so`, built from zlib 1.4
(commit `99623ef7`), whose `puff.c` (version 2.3, 21 Jan 2013) has SHA-256

```
4247d373526e74d9ec5ae7a81dee201133d0679f500db9726fe6e54963e7d5ae
```

by gcc 12.3.0 for AArch64, from nixpkgs commit `b134951a` (the version of
gcc 12 that mlkem-native uses), with `build_puff.sh`:

```
gcc -O2 -fPIC -fno-stack-protector -c puff.c -o puff.o
gcc -shared -Wl,-soname,libpuff.so -o libpuff.so puff.o
```

The stack protector, which the nixpkgs compiler wrapper enables by default,
is turned off; its other hardening options make no difference to this
code, which calls no library functions other than `_setjmp` and `longjmp`.
The SHA-256 of the binary is

```
41c104642343a4207ad3ad4c0df22fc50ac6604468544e1c64d2915ae31a3ceb
```

The code was built on x86-64 by running the native AArch64 compiler under
qemu-user, so `build_puff.sh` takes the compiler as the environment
variable `GCC`. It also builds `puff_run` from `../../tests/deflate`, a
program that runs `puff` on given files, which
`../../tests/deflate/diff_puff.py` uses to compare the binary with the
Python version of the specification there.

## The transcription

`puff_gcc12_O2.S` is the start of the first loadable segment of the binary,
from address 0 up to the end of the read-only data at 0x11d8. This covers
the procedure linkage table, all the code and the constant tables. It was
generated from the disassembly, with the ELF header and other data as
`.quad` directives, and it assembles to exactly the bytes in the binary,
with no relocations. The functions are at these addresses:

| Function    | Address |
|-------------|---------|
| `construct` | 0x6a0   |
| `bits`      | 0x7a0   |
| `decode`    | 0x830   |
| `codes`     | 0x900   |
| `puff`      | 0xad0   |

gcc has inlined `stored`, `fixed` and `dynamic` into `puff`. The calls of
`_setjmp` and `longjmp` go through the procedure linkage table, at 0x570
and 0x5a0, which reads their addresses from the global offset table at
0x20000 and 0x20018. That and the writable data, at 0x20020 to 0x20320, are
in the second segment of the binary, which is not part of the
transcription: the flag `virgin` (0x20028), which is set until `fixed` has
built its tables, and those tables in the `.bss` section (0x20040 to
0x2031c).

After building the object file, `check_transcription.py` checks that it is
byte-for-byte identical to the binary, e.g. in the `arm` directory:

```
make puff/puff_gcc12_O2.o
python3 puff/check_transcription.py puff/puff_gcc12_O2.o - \
  <build>/libpuff.so 0x0
```

## The proofs

The proofs are in `../proofs`, one file for each function:

| Function  | Proof                        | Theorem                          |
|-----------|------------------------------|----------------------------------|
| bits      | `puff_bits_gcc12_O2.ml`      | `PUFF_BITS_CORRECT_MEMSAFE`      |
| decode    | `puff_decode_gcc12_O2.ml`    | `PUFF_DECODE_CORRECT_MEMSAFE`    |
| construct | `puff_construct_gcc12_O2.ml` | `PUFF_CONSTRUCT_CORRECT_MEMSAFE` |
| codes     | `puff_codes_gcc12_O2.ml`     | `PUFF_CODES_CORRECT_MEMSAFE`     |
| puff      | `puff_gcc12_O2.ml`           | `PUFF_CORRECT_MEMSAFE`           |

Each theorem states the correctness of the function and its memory safety:
whatever the input, the loads and stores of its code, in the trace
`read events`, are within lists of readable and writable regions
(`memaccess_inbounds`). The same theorems without the trace are the
corollaries `PUFF_BITS_CORRECT` and so on, and `PUFF_MEMSAFE` is the memory
safety of `puff` alone.

`PUFF_CORRECT` says that if `puff` returns 0, the output and the number of
bytes read that it stores are those of the decoding `deflate_decode` of the
specification, and that otherwise there is no decoding whose output fits in
the buffer. `PUFF_MEMSAFE` says that `puff` returns, with its loads from the
input, the output buffer, `*destlen` and `*sourcelen`, its stack frame, the
image and the region of `_setjmp` and `longjmp`, and its stores to the
output buffer, `*destlen`, `*sourcelen`, the stack frame and the data in the
image for the tables of the fixed codes. The calls of `_setjmp` and
`longjmp` are given contracts, which include the regions of their own loads
and stores, and the tables that `fixed` builds are part of an invariant. The
common definitions and tactics are in `../proofs/utils/puff.ml`, and the
facts about the specification in `../../common/rfc1951_theory.ml`.

## License

The code in the transcription is compiled from `puff.c`, which comes with
this notice:

```
  Copyright (C) 2002-2013 Mark Adler, all rights reserved
  version 2.3, 21 Jan 2013

  This software is provided 'as-is', without any express or implied
  warranty.  In no event will the author be held liable for any damages
  arising from the use of this software.

  Permission is granted to anyone to use this software for any purpose,
  including commercial applications, and to alter it and redistribute it
  freely, subject to the following restrictions:

  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software. If you use this software
     in a product, an acknowledgment in the product documentation would be
     appreciated but is not required.
  2. Altered source versions must be plainly marked as such, and must not be
     misrepresented as being the original software.
  3. This notice may not be removed or altered from any source distribution.

  Mark Adler    madler@alumni.caltech.edu
```
