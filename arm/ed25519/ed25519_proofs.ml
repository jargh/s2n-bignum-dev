
(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Starting proofs about the machine code.                                   *)
(* ------------------------------------------------------------------------- *)

(*****************************************************************************)

(*
print_literal_relocs_from_elf "arm/ed25519/code/ed25519.o";;

save_literal_relocs_from_elf
  "arm/ed25519/literal_relocs.txt"
  "arm/ed25519/code/ed25519.o";;
*)

let ed25519_mc,constants_data = define_assert_relocs_from_elf "ed25519_mc"
    "arm/ed25519/code/ed25519.o"
  

let EXEC = ARM_MK_EXEC_RULE ed25519_mc;;

(* void ed25519_keypair_from_seed_s2n_bignum(
    uint8_t A[ED25519_PUBLIC_KEY_LEN], const uint8_t seed[ED25519_SEED_LEN]) *)
let ED25519_KEYPAIR_FROM_S2N_BIGNUM_CORRECT = prove
  (`!A_p seed seed_p pc retpc sp.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) (ed25519_mc pc ???) /\
           read PC s = word (pc + ???) /\
           read X30 s = word retpc /\
           read SP s = sp /\
           C_ARGUMENTS [A_p; seed_p] /\
           LENGTH seed = 32 /\
           byte_list_at seed seed_p s)
      (\s. byte_list_at (public_key_of_seed seed) A_p s)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(A_p, 32)] ,,
        MAYCHANGE [memory :> bytes(word_sub sp (word ???), ???)] ,,
        MAYCHANGE [events])`,
      
      );;

let DOM2_COMMON_CORRECT = prove
  ();

let ED25519_SIGN_COMMON_CORRECT = prove
  ();

let ED25519_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();

let ED25519CTX_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();

let ED25519PH_SIGN_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();


let ED25519_VERIFY_COMMON_CORRECT = prove
  ();

let ED25519_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();

let ED25519CTX_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();

let ED25519PH_VERIFY_NO_SELF_TEST_S2N_BIGNUM_CORRECT = prove
  ();

(* Pre- and post-conditions of Ed25519 subroutines *)
void ed25519_keypair_from_seed_s2n_bignum (
  uint8_t out_public_key[ED25519_PUBLIC_KEY_LEN],
  const uint8_t seed[ED25519_SEED_LEN])
Pre:
  `seed` contains `seed_v` and `LENGTH seed_v = ED25519_SEED_LEN`
Post:
  `out_public_key` contains `public_key_of_seed seed_v`


void ed25519_sign_common(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `dom2_valid alg ctx` and
  `dom2_buffer` contains `dom2_of alg ctx` and `dom2_buffer_len = LENGTH (dom2_of alg ctx)`
Post: 
  `out_sig` contains `sign alg ctxt seed_v m`
  (* Note when each of our three top-level signing functions calls this subroutine,
     dom2-related pre-conditions must be true *)

     
int ed25519_verify_common(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `dom2_valid alg ctx` and
  `dom2_buffer` contains `dom2_of alg ctx` and `dom2_buffer_len = LENGTH (dom2_of alg ctx)`
Post: 
  if `verify_args_valid bytelist_A sig /\ verify alg ctxt bytelist_A sig m`
  then return 1
  else return 0
  (* Note when each of our three top-level signing functions calls this subroutine,
     dom2-related pre-conditions must be true *)

size_t dom2_common(
    uint8_t dom2_buffer[MAX_DOM2_SIZE], const uint64_t phflag,
    const uint8_t *context, size_t context_len)
Pre:
  `context` contains `ctxt` and `context_len = LENGTH ctxt`
  if `phflag = 0` then `0 < context_len <= 255`
  else `phflag = 1 /\ context_len <= 255`
Post:
  `dom2_buffer` contains `if phflag = 0 then dom2_of 1 ctxt else dom2_of 2 ctx` and
  return `LENGTH (dom2_of alg ctxt)`
  else return `0`

int ed25519_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN])
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
Post:
  return `1` and `out_sig` contains `sign 0 [] seed_v m`


int ed25519_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN])
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
Post: 
  if `verify_args_valid bytelist_A sig /\ verify 0 [] bytelist_A sig m`
  then return 1
  else return 0

int ed25519ctx_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `0 < ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 1 ctxt seed_v m`
  else return `0`


int ed25519ctx_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `0 < ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 1 ctxt bytelist_A sig m`
  then return 1
  else return 0


int ed25519ph_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 2 ctxt seed_v (sha512_pad m)`
  else return `0`


int ed25519ph_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 2 ctxt bytelist_A sig (sha512_pad m)`
  then return 1
  else return 0
