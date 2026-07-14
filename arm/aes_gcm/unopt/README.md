This directory holds the "clean" (readability-oriented, un-rescheduled) AArch64
AES-GCM encryption kernels. The implementations in the parent directory with the
corresponding names are SLOTHY-optimized versions of these: the high-level
algorithm, dataflow and (mostly) register allocation are unchanged, but the
instructions are rescheduled for throughput. Crucially these optimized variants
do NOT use software pipelining, so the loop structure — block boundaries, loop
bounds, and instruction counts — is preserved.

Because of that, the HOL Light correctness proof of the parent (optimized)
kernel is almost identical to the proof of the clean kernel: only the embedded
machine-code literal changes, plus the occasional small adjustment where SLOTHY
reallocated a scratch register that a loop invariant happened to pin (e.g. for
x4_basic, the tail loop reuses the vector register that held a dead H-power, so
one now-stale invariant conjunct is dropped).

These files are kept as the maintainable source of the algorithm and as input to
future work (e.g. an explicit clean-vs-optimized program-equivalence proof in the
style of arm/p256/unopt). They are compiled only for running HOL Light proofs and
are not part of libs2nbignum.

Migration status: x4_basic done (clean here, optimized in the parent, proof
re-verified). The remaining x4 variants will migrate the same way.
