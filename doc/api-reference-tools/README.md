# API reference generator

These scripts generate [`../API_REFERENCE.md`](../API_REFERENCE.md), the
human-readable per-function API reference, from four sources of truth in the
repository:

| Source | Used for |
|--------|----------|
| `include/s2n-bignum.h` | authoritative public function list, C signatures, one-line descriptions |
| `{arm,x86}/<area>/*.S` banner comments | prose "Operation" / "Details" text |
| `{arm,x86}/proofs/subroutine_signatures.ml` | per-arch buffer roles (inputs / outputs / temporaries, element sizes) |
| `{arm,x86}/proofs/*.ml` `*_SUBROUTINE_CORRECT` theorems | aliasing contracts, value-range assumptions, stack-frame sizes |

The aliasing field is derived from the `nonoverlapping` / `ALL` / `ALLPAIRS`
idioms in each function's `_SUBROUTINE_CORRECT` precondition (the public,
ABI-level contract — Windows-ABI and NOIBT variants are ignored). A handful of
functions where the proof's local variable names differ from the C argument
names, or where the ML-KEM/ML-DSA code diverges from the usual conventions, are
corrected by hand-maintained override tables inside `gen_final.py`
(`ALIAS_CORRECTION`, `ALIAS_OVERRIDE`, `SIZES_OVERRIDE`, `ARCH_NOTES`). See those
tables and their comments before trusting a blind regeneration.

## Regenerating

Run from the repository root:

```sh
sh doc/api-reference-tools/build.sh
```

This runs the parsers (writing intermediate JSON into a scratch dir), then the
generator and assembler, and overwrites `doc/API_REFERENCE.md`.

The scripts are plain Python 3 with no third-party dependencies.
