# Drafts set aside (not loaded by link.ml)

Work started on the functions that need instructions outside the s2n-bignum
ARM model (begin_session, the keypair reference counts, the hash-table
operations of peerlookup.c), set aside on 2026-11-21 at the user's request.

- arm_model_sp_el0.patch: a sequential-model extension of
  arm/proofs/instruction.ml and arm/proofs/decode.ml (apply with patch -p1
  from the s2n-bignum root): a read-only state component SP_EL0 for
  MRS Xt, SP_EL0; STLR and LDXR as an ordinary store and load; STXR and
  STLXR as a store that always succeeds (status 0); DMB and PRFM as no-ops.
  It changes the type armstate, so every proof has to be run again with it.
- model_test_sp_el0.ml: the test of the patch (decoding of the forms in the
  image, and an LL/SC increment loop proved), run fresh in a session with
  the patch applied.
- contracts_session.ml and the *_spec.ml files: unproved drafts of the
  contracts and specifications for those functions.
