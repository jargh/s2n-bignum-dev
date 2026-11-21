# WireGuard handshake proofs (feasibility study)

This branch adds, to a copy of s2n-bignum, machine-code correctness proofs
for the handshake of the Linux kernel's WireGuard driver: Linux 6.18.64,
compiled for AArch64 by gcc 13 with -O2, with the portable C versions of the
kernel's crypto library. It is a study of how far s2n-bignum's
infrastructure (the AArch64 model, its simulation tactics and the proofs of
subroutines relative to their callees) carries over to code of that kind.
It is not intended for s2n-bignum itself.

- `arm/wireguard/README.md`: the image that the proofs are about, how it is
  built from the kernel release, and the licensing and provenance of the
  files.
- `arm/proofs/wireguard/README.md`: the specification, the method, what is
  proved and what is assumed, and how to run the proofs.
- `arm/proofs/wireguard/FINDINGS.md`: what the proofs showed about the code.

Licensing: `arm/wireguard/gcc13_O2/wireguard.S`, a transcription of the
compiled kernel code, is derived from GPL-licensed files of the kernel and
is marked GPL-2.0 (see `arm/wireguard/README.md` for the files and their
licences). Everything else added here is under s2n-bignum's licence
(Apache-2.0 OR ISC OR MIT-0), and the files adapted from other branches of
s2n-bignum say so.
