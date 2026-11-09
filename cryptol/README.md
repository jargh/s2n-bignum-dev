# The Cryptol specification of ML-KEM in HOL Light

This directory contains a translation into HOL Light of the Cryptol
specification of ML-KEM from Galois's [cryptol-specs][1], with proofs that
it agrees with the HOL Light specification of FIPS 203 in
`common/fips203.ml`. The aim is to explore how Cryptol specifications can
be related to the specifications used here. Nothing else in the repository
depends on it.

[1]: https://github.com/GaloisInc/cryptol-specs

## Source

The translation is of `Primitive/Asymmetric/KEM/ML_KEM/Specification.cry`
at cryptol-specs commit `3558c703cfa7d86c2a3387cedfab6f83e8bcd558` (git
blob `36f15741352f288d4b317175a435973d238baa85`), the latest version of
that file on 2026-11-09.

## Files

 - `cry_mlkem.ml`: the translation. It is a naive shallow translation by
   hand: each Cryptol definition becomes one HOL definition with the same
   structure, named `cry_<name>`, with the Cryptol text quoted above it.
   The translation rules are listed at the top of the file.
 - `cry_mlkem_proofs.ml`: the proofs that the translated functions agree
   with `common/fips203.ml`.
 - `LICENSE.cryptol-specs`: the license of cryptol-specs, which covers the
   Cryptol text quoted in `cry_mlkem.ml`.

## Loading

From the root of the repository:

```
loadt "cryptol/cry_mlkem_proofs.ml";;
```

This also loads `common/fips203_theory.ml`, and takes about 8 minutes of
CPU time. The proofs use only the three standard axioms of HOL Light.

## Results

For each parameter set, the theorems `CRY_MLKEM512`, `CRY_MLKEM768` and
`CRY_MLKEM1024` state that the Cryptol API, with the lengths that the
Cryptol types give, is the API of `common/fips203.ml`. For ML-KEM-768:

```
|- (!d z. (!i j n. i < 3 /\ j < 3 /\ n < 256
                   ==> mlkem_sample_ntt
                        (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                [word j; word i]) n < &3329)
          ==> cry_KeyGen 3 2 (SOME d) (SOME z) = mlkem_keygen mlkem768 d z) /\
   (!ek m. LENGTH ek = 1184 /\ LENGTH m = 32 /\
           (!i j n. i < 3 /\ j < 3 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1152 32 ek) [word j; word i])
                         n < &3329)
           ==> mlkem_encaps mlkem768 ek m =
               if cry_encapsulationKeyCheck 3 ek
               then SOME(cry_Encaps (:10) (:4) 3 2 2 ek (SOME m))
               else NONE) /\
   (!dk c. LENGTH dk = 2400 /\ LENGTH c = 1088 /\
           (!i j n. i < 3 /\ j < 3 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1152 32
                                   (mlkem_slice 1152 1184 dk))
                                 [word j; word i]) n < &3329)
           ==> mlkem_decaps mlkem768 dk c =
               if cry_decapsulationInputCheck 3 dk c
               then SOME(cry_Decaps (:10) (:4) 3 2 2 dk c)
               else NONE)
```

The hypotheses on `mlkem_sample_ntt` are those of the K-PKE theorems
`KPKE_*_FIPS` in `common/fips203_theory.ml`, which the proofs use: the
values that SampleNTT produces are below q, that is, its rejection
sampling terminates. For K-PKE KeyGen, `CRY_K_PKE_KEYGEN_INFINITE`
derives this hypothesis from each XOF stream used having infinitely many
12-bit fields below q.

These theorems are built from one theorem for each translated function,
stating that it equals its counterpart in `common/fips203.ml`, e.g.
`CRY_K_PKE_ENCRYPT` for `K_PKE::Encrypt` and `kpke_encrypt`. The stream
`filter` used by SampleNTT is translated by an explicit construction.
`CRY_FILTER_EQN` proves that it satisfies the recursion equation of the
Cryptol definition, and `CRY_FILTER_UNIQUE` that nothing else does, on
the streams with infinitely many 12-bit candidates below q (on the others,
the Cryptol definition is undefined from some point on).

The six NTT properties stated in the Cryptol file are proved:

| Cryptol property          | Theorem                       |
|---------------------------|-------------------------------|
| `naive_fast_ntt_equiv`    | `CRY_NAIVE_FAST_NTT_EQUIV`    |
| `naive_fast_invntt_equiv` | `CRY_NAIVE_FAST_INVNTT_EQUIV` |
| `fast_ntt_inverts`        | `CRY_FAST_INVNTT_NTT`         |
| `fast_invntt_inverts`     | `CRY_FAST_NTT_INVNTT`         |
| `NaiveNTT_Inverts`        | `CRY_NAIVENTT_INVERTS`        |
| `NaiveNTTInv_Inverts`     | `CRY_NAIVENTTINV_INVERTS`     |

and `CRY_ZETA_EXPC` shows that the literal table `zeta_expc` of the
Cryptol file is that of FIPS 203 Appendix A, i.e. its entry i is
17^BitRev7(i) mod q.

## Limitations

 - The translation is by hand and is not derived from the semantics of
   Cryptol, so it is trusted. It is checked only by the proofs that it
   agrees with `common/fips203.ml`, which was written independently.
 - The SHA-3 functions that the Cryptol file imports are taken to be those
   of `common/fips202.ml`; the Cryptol SHA-3 specification is not
   translated.
 - `keyPairCheck`, a key-pair test with no FIPS 203 counterpart, and
   `dotMatMat`, which is unused, are not translated.
 - The other properties stated in the Cryptol file are not proved. Of
   these, `CorrectnessPKE` and `CorrectnessKEM` are not expected to hold
   for all inputs, since ML-KEM decryption can fail with a small
   probability.

## License

The HOL Light files are under the license of this repository. The Cryptol
text quoted in the comments of `cry_mlkem.ml` is Copyright (c) 2013-2025
Galois Inc. and is used under the BSD 3-Clause license in
`LICENSE.cryptol-specs`; the Cryptol file marks its fast NTT section as
Copyright Amazon.com, Inc. or its affiliates.
