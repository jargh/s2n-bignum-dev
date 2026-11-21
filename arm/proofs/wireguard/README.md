# Proofs of the WireGuard handshake machine code

HOL Light proofs, with s2n-bignum's AArch64 model, that the machine code of
the Linux kernel's WireGuard handshake (the image described in
`arm/wireguard/README.md`: Linux 6.18.64, gcc 13 -O2) meets a specification
of the protocol.

## The specification

- `common/rfc7693.ml`: BLAKE2s (RFC 7693).
- `common/rfc8439.ml`: ChaCha20, Poly1305 and AEAD_CHACHA20_POLY1305
  (RFC 8439), HChaCha20 and XChaCha20-Poly1305.
- `common/wireguard.ml`: the handshake of the WireGuard paper (Section 5.4),
  over byte strings, with X25519 from `EC/x25519.ml` (RFC 7748), plus the
  checks that the kernel adds (no all-zero Diffie-Hellman results), the
  cookie MACs and the transport keys.
- `common/wireguard_kernel.ml`: the kernel's internal interfaces in those
  terms (the streaming model of BLAKE2s, HMAC with a 32-byte key, the AEAD
  nonces and so on); `common/wireguard_tables.ml`: explicit tables for
  evaluating the specifications.

## The method

There is a theorem for each function of the image, with the usual form of
s2n-bignum's subroutine theorems: from a state where the image is loaded,
the PC is at the function and the arguments and memory are as stated, the
code returns, with the postcondition holding, having changed only what the
frame allows. Each function has a spec file (`gcc13_O2/f_spec.ml`, the
statement) and a proof file (`gcc13_O2/f_proof.ml`). A proof uses the
statements of its callees, not their proofs (`relative.ml`), so every proof
runs once; `gcc13_O2/link.ml` loads all of them in one session and
discharges those assumptions, leaving closed theorems.

Kernel functions that are not in the image are given contracts
(`contracts.ml`), which appear as hypotheses of the theorems that use
them: memset, memcpy, the read-write semaphores, the spinlocks with bottom
halves disabled, `__init_rwsem`, random bytes, the clocks, `wg_peer_put`,
`curve25519_generic` (X25519) and, for single functions, the rate limiter
and the lookup of an index. The model is sequential: what a kernel function
does to the kernel's own state is outside the model, and while the code
runs, nothing else writes the memory that it uses (the locks of the
handshake are there for that). Each kernel function is assumed to use at
most 4096 bytes of stack.

## What is proved

The link closes 56 theorems about 54 functions:

- BLAKE2s (`blake2s_compress_generic`, `blake2s_update`, `blake2s_final`,
  the two specialized copies of `blake2s`), HMAC and the KDF of noise.c,
  `mix_hash`, `mix_dh`, `message_ephemeral`, `precompute_key`;
- ChaCha20 (`chacha_permute`, `chacha_block_generic`, `chacha_crypt`),
  HChaCha20 and `xchacha_init`, Poly1305 (the core and the streaming
  interface), the AEADs (`chacha20poly1305_encrypt`/`decrypt`, their inner
  functions, `xchacha20poly1305_encrypt`/`decrypt`), `crypto_memneq`,
  `crypto_xor`, the Curve25519 wrappers (`curve25519`,
  `curve25519_generate_public`);
- the handshake messages (`wg_noise_handshake_create_initiation`,
  `consume_initiation`, `create_response`, `consume_response`) and the
  setup functions (`wg_noise_init`, `wg_noise_set_static_identity_private_key`,
  `wg_noise_precompute_static_static`, `wg_noise_handshake_init`,
  `handshake_zero`, `wg_noise_handshake_clear`,
  `wg_noise_expire_current_peer_keypairs`);
- cookie.c (`make_cookie`, `wg_cookie_validate_packet`,
  `wg_cookie_add_mac_to_packet`, `wg_cookie_message_create`,
  `wg_cookie_message_consume`, the key precomputations and the two init
  functions);
- `wg_index_hashtable_remove`.

`wg_index_hashtable_insert` is not proved (see below), and the theorems for
`create_initiation` and `create_response`, which call it, keep its
statement as an assumption (`relative_assumed.ml`).

## Not covered

- `wg_noise_handshake_begin_session`, the keypair reference counting
  (`wg_noise_keypair_get`/`put`, `wg_noise_received_with_keypair`,
  `wg_noise_keypairs_clear`) and the other table functions of
  peerlookup.c: their code needs instructions that the model does not have
  (`mrs` of SP_EL0, `stlr`, `ldxr`/`stxr`, `dmb`, `prfm`). A sequential
  extension of the model and drafts of their specifications are in
  `drafts/`.
- The scatter-gather AEAD functions of the data path.
- The LSE atomics that the kernel patches in at boot on CPUs that have them
  (the image as built takes the LL/SC path).

## X25519

`curve25519_generic_s2n.ml` proves (CURVE25519_GENERIC_CONTRACT_S2N, with
no assumptions) that s2n-bignum's verified `curve25519_x25519_byte`
satisfies the contract for `curve25519_generic` when its code is in the
kernel's region, 4-byte aligned. `gcc13_O2/link_s2n_x25519.ml` restates the
nine theorems that use X25519 (the two wrappers, the setup functions and
the four handshake messages) with that code in place of the contract: the
GOT entry for `curve25519_generic` points into the region where the bytes
of s2n-bignum's code are, and nothing about X25519 is assumed. This needs
the objects `arm/curve25519/bignum_inv_p25519.o` and
`curve25519_x25519_byte.o` (`make` in `arm/curve25519`).

## Running

From the root of s2n-bignum, in HOL Light:

    loadt "arm/proofs/wireguard/gcc13_O2/link.ml";;

which takes about three hours, and then, for the theorems with s2n-bignum's
X25519,

    loadt "arm/proofs/wireguard/gcc13_O2/link_s2n_x25519.ml";;

which loads s2n-bignum's proof of it (about two more hours). `FINDINGS.md`
lists what the proofs showed about the code.
