(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM decryption kernel, variant x4_scalar_iv_mem_late_tag_keep_htable, *)
(* the SOFTWARE-PIPELINED (SLOTHY) schedule (..._swp).                        *)
(*                                                                           *)
(* Same specification as the clean sibling (GHASH over the INPUT blocks, via *)
(* nist_input_block).  The main 4-block loop is software-pipelined: SLOTHY    *)
(* emits a fill/preamble, a steady body running the halves out of phase, a    *)
(* drain/postamble, and a count=1 exceptional block (Lloop_unrolled_start_    *)
(* iter_1).  The single-block tail loop (Lloop_1x) is body-only rescheduled   *)
(* (NOT pipelined), so its invariant carries over directly from the clean     *)
(* proof; only the in-body simulation landmarks (counter-merge state, output  *)
(* store step) move.  Control flow:                                          *)
(*   0x2c  core entry (after the register-save preamble)                      *)
(*   0xa0  loop-count fork: cbz count -> tail; cmp count,#1 / b.eq -> iter_1   *)
(*   0xc8..0x290  fill;  0x294..0x510 steady;  0x514..0x824 drain -> 0xaa0     *)
(*   0x828..0xa34 iter_1 (count==1) -> 0xaa0                                   *)
(*   0xaa0  Lloop_unrolled_end: cbz remainder -> writeback                    *)
(*   0xaa4..0xb64 Lloop_1x tail (body-only reschedule)                        *)
(*   0xb68  Lloop_1x_end: final ivec/tag writeback; 0xb7c = core exit (ldp)      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp.o";; *)

let aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc =
  define_from_elf "aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc"
    "arm/aes_gcm/aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp.o";;

let AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC = ARM_MK_EXEC_RULE aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc;;

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block nonce rk i =
    word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let cipher_block = new_definition
 `cipher_block nonce rk inblock i =
    word_xor (aes_ctr_block nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block nonce rk inblock i =
        word_reversefields 8 (cipher_block nonce rk inblock i)`;;

(* For DECRYPTION the GHASH authenticator is computed over the INPUT
   (ciphertext) blocks, not the output.  The i-th folded operand in the NIST
   big-endian convention is therefore just the byte-reversal of the loaded
   little-endian input block.  (Contrast nist_cipher_block above, used by the
   encrypt kernel, which reverses the keystream-XORed OUTPUT.)  The output
   store itself is unchanged - it is still cipher_block = keystream XOR input,
   since XOR is symmetric in plaintext/ciphertext. *)

let nist_input_block = new_definition
 `nist_input_block (inblock:num->int128) (i:num) : int128 =
        word_reversefields 8 (inblock i)`;;

(* Restricted Htable predicate: only the entries the kernel actually reads.
   The x4-unrolled loop uses H^1..H^4 and their Karatsuba mid terms (the
   first 6 entries = offsets 0..80 of the full htable_mem layout).
   The tail loop only uses H^1..H^2 (offsets 0..32) but we assert all four
   here since the outer loop needs them and the precondition is shared. *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardare specs.         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Scalar counter representation.  Unlike the vector-IV kernels, this variant *)
(* keeps the counter block in scalar registers: after "ldp x11,x12,[x4]" the *)
(* two 64-bit halves of the (little-endian) IV live in X11 (low) and X12      *)
(* (high); the running counter is byte-reversed out of X12's top word into    *)
(* X13.  The loop rebuilds the reversed counter block via                     *)
(*   w14 = rev(w13);  x14 = orr x12 (w14 lsl 32);  Q0 = word_join x14 x11.     *)
(* These lemmas connect that scalar reconstruction back to ctr_block.         *)

let SCALAR_IV_SPLIT = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = w
   ==> ivlo = word_subword w (0,64) /\ ivhi = word_subword w (64,64)`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* Setup-block obligations for the scalar counter registers, phrased directly    *)
(* from the IV-halves join relation so that all widths stay concrete (avoids the  *)
(* type-variable ambiguity that arises if ivhi is substituted before WORD_BLAST). *)

let X11_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> ivlo = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X12_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_zx (word_zx ivhi:int32):int64 =
       word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN SIMP_TAC[]);;

let X13_SETUP = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_zx (word_bytereverse (word_zx (word_ushr ivhi 32):int32):int32):int64
       = word_zx (word 2:int32):int64`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC BITBLAST_RULE);;

(* Normalisation rules for the scalar counter.  The counter lives in the 32-bit W13 *)
(* view of X13; each "add w13,w13,#1" is a 32-bit add and each read of W13 is a      *)
(* truncation, so counter expressions accumulate word_zx chains.  These two rules    *)
(* (applied alongside WORD_SIMPLE_SUBWORD_CONV while stepping) keep the counter in a *)
(* single-word_zx normal form: ZX_COUNTER_UD kills up-then-down conversions,         *)
(* ZX_COUNTER_INC pushes the 32-bit increment through the extension.                 *)

let ZX_COUNTER_UD = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`,
  CONV_TAC BITBLAST_RULE);;

let ZX_COUNTER_INC = prove
 (`word_zx (word_add (word_zx (x:int64):int32) (word 1)):int32 =
   word_add (word_zx x:int32) (word 1)`,
  CONV_TAC BITBLAST_RULE);;

(* This variant assembles the counter block on the STACK: "stp x11,x14,[sp,#OFF]"    *)
(* then "ldr q0,[sp,#OFF]".  The load reads back the two stored halves as            *)
(* word_join x14 x11, which reconstructs the reversed ctr_block.                     *)

let CTR_BLOCK_BUILD_INSERT = prove
 (`word_join
     (word_or
       (word_zx ((word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64)):int32):int64)
       (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* In the late_tag schedule each block's counter word is "add w14,w13,#N" from  *)
(* a fixed base w13, then byte-reversed; the W-register up/down-conversions leave *)
(* a word_zx nest around either the bare base (word (4*i+2), four zx layers) or   *)
(* the offset form word_add (word_zx (word_zx (word (4*i+2)))) (word N).  These   *)
(* two rules (int32) collapse both to word n / word_add (word n) (word m).        *)
let CTR_ZX_NORM = prove
 (`(word_zx (word_zx (word_zx (word_zx (word n:int32):int64):int32):int64):int32 = word n) /\
   (!m. word_zx (word_zx (word_add (word_zx (word_zx (word n:int32):int64):int32)
                                   (word m):int32):int64):int32
        = word_add (word n:int32) (word m))`,
  CONJ_TAC THENL [CONV_TAC BITBLAST_RULE; GEN_TAC THEN CONV_TAC BITBLAST_RULE]);;

(* The s2n-bignum simulator does not auto-merge two 64-bit stores into a       *)
(* 128-bit load, so after "stp x11,x14,[sp,#OFF]" the subsequent               *)
(* "ldr q0,[sp,#OFF]" would leave Q0 symbolic.  This tactic, spliced in AFTER  *)
(* the stp step and BEFORE the ldr step for state s<N>, derives the merged     *)
(* 128-bit read read(bytes128 (sp+OFF)) s<N> = word_join x14 x11 from the two  *)
(* bytes64 store facts, so the simulator can resolve the load against it.      *)
let MERGE_CTR128_TAC off sname =
  MP_TAC(ISPECL [`memory`;
                 mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                         mk_comb(`word:num->int64`,mk_small_numeral off));
                 mk_var(sname,`:armstate`)]
           (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES128 using the hardware primitives ***)

let AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
   (aese
    (aesmc
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
         rk3))
        rk4))
       rk5))
      rk6))
     rk7))
    rk8))
   rk9)
   rk10 =
   word_reversefields 8
    (aes128_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10]))`,
  REWRITE_TAC[aes128_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
          rk3))
         rk4))
        rk5))
       rk6))
      rk7))
     rk8))
    rk9)
   (word_xor rk10 inblock) =
   word_xor
    (word_reversefields 8
      (aes128_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES128_CIPHER_RECONSTRUCT]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let RECONSTRUCT_POLYVAL_REDUCE_G2 =
  REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM polyval_reduce_g2);;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Decryption-specific reconstruction lemmas.                                *)
(*                                                                           *)
(* The decrypt kernel's per-block store instruction is                       *)
(*    eor3 out, aes_st, rk10, plain                                          *)
(* i.e. out = aes_st XOR rk10 XOR plain, whereas the encrypt kernel emits     *)
(*    eor3 out, plain, rk10, aes_st.                                          *)
(* So the store value has the AES keystream and the input in the opposite     *)
(* XOR order from XOR_AES128_CIPHER_RECONSTRUCT; this commuted variant folds   *)
(* the 10-round AESE/AESMC tower for that operand order.                      *)
(* ------------------------------------------------------------------------- *)

let XOR_AES128_CIPHER_RECONSTRUCT_DEC = prove
 (`word_xor inblock (word_xor rk10
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1))
        rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) =
   word_xor
   (word_reversefields 8
   (aes128_cipher (word_reversefields 8 plaintext)
   (MAP (word_reversefields 8)
   [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
   inblock`,
  ONCE_REWRITE_TAC[GSYM XOR_AES128_CIPHER_RECONSTRUCT] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Byte-reassembly: the GHASH pmull operands are built from the loaded input   *)
(* block by 16 byte-lane word_subword/word_join operations.  These fold each   *)
(* 64-bit lane back to a subword of the byte-reversal of the whole block,      *)
(* i.e. of nist_input_block, so the accumulator reconstruction can proceed in  *)
(* terms of the settled input blocks rather than 128 raw bit variables.        *)

let INBLOCK_REASSEMBLE = prove
 (`(word_join
     (word_join
      (word_join (word_subword (x:int128) (64,8):byte) (word_subword x (72,8):byte):int16)
      (word_join (word_subword x (80,8):byte) (word_subword x (88,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (96,8):byte) (word_subword x (104,8):byte):int16)
      (word_join (word_subword x (112,8):byte) (word_subword x (120,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (0,64)) /\
   (word_join
     (word_join
      (word_join (word_subword (x:int128) (0,8):byte) (word_subword x (8,8):byte):int16)
      (word_join (word_subword x (16,8):byte) (word_subword x (24,8):byte):int16):int32)
     (word_join
      (word_join (word_subword x (32,8):byte) (word_subword x (40,8):byte):int16)
      (word_join (word_subword x (48,8):byte) (word_subword x (56,8):byte):int16):int32):int64
    = word_subword (word_reversefields 8 x) (64,64))`,
  CONV_TAC WORD_BLAST);;

(* The one genuinely decrypt-specific normalization step, shared by the main-loop *)
(* and tail GHASH reconstructions.  The GHASH pmull operands are the loaded input  *)
(* run through the hardware rev64 (a per-lane byte reversal, exploded into a       *)
(* byte-lane word_join tower by WORD_SIMPLE_SUBWORD_CONV during stepping).         *)
(* INBLOCK_REASSEMBLE folds each 64-bit lane back to a subword of the byte-reversed *)
(* block, GSYM nist_input_block names it, and WORD_SUBWORD_XOR/BYTESWAP128 +        *)
(* WORD_SIMPLE_SUBWORD_CONV collapse the byteswap128/lane-swap wrappers -- putting  *)
(* the pmull operands into exactly the encrypt closer's word_subword(...)(lane)     *)
(* form so the shared reduction lemmas apply.  (Encrypt needs none of this: its     *)
(* operand is already the settled nist_cipher_block from the output store.)         *)

let DEC_GHASH_NORM_TAC : tactic =
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
  REWRITE_TAC[GSYM nist_input_block] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

let PMUL_KARATSUBA_JOIN_ALT = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (64,64):int64)
                                 (word_subword a (0,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REWRITE_TAC[PMUL_KARATSUBA_JOIN] THEN REWRITE_TAC[WORD_XOR_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x3cc (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xa0 adjustment, i.e.    *)
(* the value the SP register actually holds inside the function body.        *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                    *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    192-byte precomputed H-powers table                      *)
(*   returns X0 = byte_len (= len_bits / 8)                                  *)
(* ------------------------------------------------------------------------- *)

(*** Note that the NIST-level specs consider all byte-level encodings as
 *** big-endian, and the AES-related ARM instructions take that view too.
 *** Hence in the precondition "ctr_block" and "rk" correspond as 128-bit
 *** words to the NIST specifications. Since they are loaded from memory
 *** in the usual little-endian ARM fashion, we byte-reverse when
 *** specifying them as the values in any memory cells.
 ***)


(* ===== aes2c: the 2-AES-round counter precompute (SWP-staged in Q30) ===== *)
let aes2c = new_definition
 `aes2c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk)))`;;

(* ===== invariant swpS_inv8_dec_v8 (Q = P o [Y]) ===== *)
let swpS_inv8_dec_v8 : term =
`\(i:num) (s:armstate).
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (tag_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htable_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (tag_p:(64)word))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8 (tag0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (ivec_p:(64)word))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q18:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 0 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 1 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q20:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 2 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q21:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 3 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q22:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 4 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q23:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 5 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 6 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 7 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 8 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 9 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 10 (rk:((128)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 13979173243358019584 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q12:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    0) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q13:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    1) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q14:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    1))
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    0)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q15:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    2) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    3) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q17:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    3))
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    2)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (word_subword:(128)word->num#num->(64)word)
    ((word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2))
    (0,64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X12:(armstate,(64)word)component)
    (s:armstate) =
    (word_zx:(32)word->(64)word)
    ((word_zx:(64)word->(32)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2))
    (64,64))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((len_bits:num) DIV 8) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (loop_remain:num) /\
    (htable_mem_4:(128)word->(64)word->armstate->bool)
    ((ghash_twist:(128)word->(128)word)
    ((aes128_cipher:(128)word->((128)word)list->(128)word)
     ((word:num->(128)word) 0)
    (rk:((128)word)list)))
    (htable_p:(64)word)
    (s:armstate) /\
    (forall (j:num).
         (j:num) < (nblocks:num)
         ==> (read:(armstate,(128)word)component->armstate->(128)word)
             ((memory:(armstate,(64)word->(8)word)component) :>
              (bytes128:(64)word->((64)word->(8)word,(128)word)component)
              ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
              ((word:num->(64)word) (16 * (j:num)))))
             (s:armstate) =
             (inblock:num->(128)word) (j:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (64 * (i:num) + 64)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) (64 * (i:num))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((loop_count:num) - 2 - (i:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X13:(armstate,(64)word)component)
    (s:armstate) =
    (word_zx:(32)word->(64)word) ((word:num->(32)word) (4 * (i:num) + 6)) /\
    (forall (j:num).
         (j:num) < 4 * (i:num)
         ==> (read:(armstate,(128)word)component->armstate->(128)word)
             ((memory:(armstate,(64)word->(8)word)component) :>
              (bytes128:(64)word->((64)word->(8)word,(128)word)component)
              ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
              ((word:num->(64)word) (16 * (j:num)))))
             (s:armstate) =
             (word_xor:(128)word->(128)word->(128)word)
             ((aes_ctr_block:(96)word->((128)word)list->num->(128)word)
              (nonce:(96)word)
              (rk:((128)word)list)
             (j:num))
             ((inblock:num->(128)word) (j:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) (64 * (i:num) + 32))))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((aes_ctr_block:(96)word->((128)word)list->num->(128)word)
     (nonce:(96)word)
     (rk:((128)word)list)
    (4 * (i:num) + 2))
    ((inblock:num->(128)word) (4 * (i:num) + 2)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) (64 * (i:num) + 48))))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((aes_ctr_block:(96)word->((128)word)list->num->(128)word)
     (nonce:(96)word)
     (rk:((128)word)list)
    (4 * (i:num) + 3))
    ((inblock:num->(128)word) (4 * (i:num) + 3)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q11:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((byteswap128:(128)word->(128)word)
    ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list))
     (tag0:(128)word)
    ((list_of_seq:(num->(128)word)->num->((128)word)list)
     ((nist_input_block:(num->(128)word)->num->(128)word)
     (inblock:num->(128)word))
    (4 * (i:num)))))
    ((byteswap128:(128)word->(128)word)
    ((word_reversefields:num->(128)word->(128)word) 8
    ((inblock:num->(128)word) (4 * (i:num))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 1)))
    (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 1)))
    (64,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 3)))
    (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0))
    (64,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 2)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     1))
    (64,64)))
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 3)))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0))
    (64,64))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 2)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     1))
    (0,64)))
    ((word_pmul:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 3)))
     (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     0))
    (0,64))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q29:(armstate,(128)word)component)
    (s:armstate) =
    (inblock:num->(128)word) (4 * (i:num)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q10:(armstate,(128)word)component)
    (s:armstate) =
    (inblock:num->(128)word) (4 * (i:num) + 1) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q30:(armstate,(128)word)component)
    (s:armstate) =
    (aes2c:(96)word->((128)word)list->num->(128)word) (nonce:(96)word)
    (rk:((128)word)list)
    (4 * (i:num) + 2) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 3)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 4)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 5)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (4 * (i:num) + 6)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X26:(armstate,(64)word)component)
    (s:armstate) =
    (word_zx:(32)word->(64)word) ((word:num->(32)word) (4 * (i:num) + 9)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aese:(128)word->(128)word->(128)word)
    ((aesmc:(128)word->(128)word)
    ((aese:(128)word->(128)word->(128)word)
     ((aesmc:(128)word->(128)word)
     ((aese:(128)word->(128)word->(128)word)
      ((aesmc:(128)word->(128)word)
      ((aese:(128)word->(128)word->(128)word)
       ((aesmc:(128)word->(128)word)
       ((aese:(128)word->(128)word->(128)word)
        ((aesmc:(128)word->(128)word)
        ((aese:(128)word->(128)word->(128)word)
         ((aesmc:(128)word->(128)word)
         ((aese:(128)word->(128)word->(128)word)
          ((aesmc:(128)word->(128)word)
          ((aese:(128)word->(128)word->(128)word)
           ((aesmc:(128)word->(128)word)
           ((aese:(128)word->(128)word->(128)word)
            ((aesmc:(128)word->(128)word)
            ((aese:(128)word->(128)word->(128)word)
             ((word_join:(64)word->(64)word->(128)word)
              ((word_or:(64)word->(64)word->(64)word)
               ((word_zx:(32)word->(64)word)
               ((word_zx:(64)word->(32)word)
               ((word_subword:(128)word->num#num->(64)word)
                ((word_reversefields:num->(128)word->(128)word) 8
                ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2))
               (64,64))))
              ((word_shl:(64)word->num->(64)word)
               ((word_zx:(32)word->(64)word)
               ((word_bytereverse:(32)word->(32)word)
               ((word:num->(32)word) (4 * (i:num) + 3))))
              32))
             ((word_subword:(128)word->num#num->(64)word)
              ((word_reversefields:num->(128)word->(128)word) 8
              ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2))
             (0,64)))
            ((word_reversefields:num->(128)word->(128)word) 8
            ((EL:num->((128)word)list->(128)word) 0 (rk:((128)word)list)))))
           ((word_reversefields:num->(128)word->(128)word) 8
           ((EL:num->((128)word)list->(128)word) 1 (rk:((128)word)list)))))
          ((word_reversefields:num->(128)word->(128)word) 8
          ((EL:num->((128)word)list->(128)word) 2 (rk:((128)word)list)))))
         ((word_reversefields:num->(128)word->(128)word) 8
         ((EL:num->((128)word)list->(128)word) 3 (rk:((128)word)list)))))
        ((word_reversefields:num->(128)word->(128)word) 8
        ((EL:num->((128)word)list->(128)word) 4 (rk:((128)word)list)))))
       ((word_reversefields:num->(128)word->(128)word) 8
       ((EL:num->((128)word)list->(128)word) 5 (rk:((128)word)list)))))
      ((word_reversefields:num->(128)word->(128)word) 8
      ((EL:num->((128)word)list->(128)word) 6 (rk:((128)word)list)))))
     ((word_reversefields:num->(128)word->(128)word) 8
     ((EL:num->((128)word)list->(128)word) 7 (rk:((128)word)list)))))
    ((word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 8 (rk:((128)word)list)))))
    ((word_reversefields:num->(128)word->(128)word) 8
    ((EL:num->((128)word)list->(128)word) 9 (rk:((128)word)list))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X24:(armstate,(64)word)component)
    (s:armstate) =
    (word_or:(64)word->(64)word->(64)word)
    ((word_zx:(32)word->(64)word)
    ((word_zx:(64)word->(32)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) 2))
    (64,64))))
    ((word_shl:(64)word->num->(64)word)
     ((word_zx:(32)word->(64)word)
     ((word_bytereverse:(32)word->(32)word)
     ((word:num->(32)word) (4 * (i:num) + 7))))
    32) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (word_zx:(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_xor:(128)word->(128)word->(128)word)
      ((word_join:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 3)))
       (0,64))
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num) + 3)))
      (64,64)))
     ((word_zx:(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num) + 3)))
     (0,64))))
    (0,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num) + 1)))
    (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     2))
    (64,64)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_xor:(128)word->(128)word->(128)word)
      ((word_join:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 2)))
       (0,64))
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num) + 2)))
      (64,64)))
     ((word_subword:(256)word->num#num->(128)word)
      ((word_join:(128)word->(128)word->(256)word)
       ((word_join:(64)word->(64)word->(128)word)
        ((word_subword:(128)word->num#num->(64)word)
         ((word_reversefields:num->(128)word->(128)word) 8
         ((inblock:num->(128)word) (4 * (i:num) + 2)))
        (0,64))
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 2)))
       (64,64)))
      ((word_join:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num) + 2)))
       (0,64))
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num) + 2)))
      (64,64))))
     (64,128)))
    (64,64))
    ((karatsuba_mid:(128)word->(64)word)
    ((h_power:(128)word->num->(128)word)
     ((ghash_twist:(128)word->(128)word)
     ((aes128_cipher:(128)word->((128)word)list->(128)word)
      ((word:num->(128)word) 0)
     (rk:((128)word)list)))
    1)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word)
     ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list))
      (tag0:(128)word)
     ((list_of_seq:(num->(128)word)->num->((128)word)list)
      ((nist_input_block:(num->(128)word)->num->(128)word)
      (inblock:num->(128)word))
     (4 * (i:num)))))
    ((word_join:(64)word->(64)word->(128)word)
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num))))
     (0,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((word_reversefields:num->(128)word->(128)word) 8
     ((inblock:num->(128)word) (4 * (i:num))))
    (64,64))))
    ((word_subword:(256)word->num#num->(128)word)
     ((word_join:(128)word->(128)word->(256)word)
      ((word_xor:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word)
       ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
        ((aes128_cipher:(128)word->((128)word)list->(128)word)
         ((word:num->(128)word) 0)
        (rk:((128)word)list))
        (tag0:(128)word)
       ((list_of_seq:(num->(128)word)->num->((128)word)list)
        ((nist_input_block:(num->(128)word)->num->(128)word)
        (inblock:num->(128)word))
       (4 * (i:num)))))
      ((word_join:(64)word->(64)word->(128)word)
       ((word_subword:(128)word->num#num->(64)word)
        ((word_reversefields:num->(128)word->(128)word) 8
        ((inblock:num->(128)word) (4 * (i:num))))
       (0,64))
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num))))
      (64,64))))
     ((word_xor:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word)
      ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
       ((aes128_cipher:(128)word->((128)word)list->(128)word)
        ((word:num->(128)word) 0)
       (rk:((128)word)list))
       (tag0:(128)word)
      ((list_of_seq:(num->(128)word)->num->((128)word)list)
       ((nist_input_block:(num->(128)word)->num->(128)word)
       (inblock:num->(128)word))
      (4 * (i:num)))))
     ((word_join:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num))))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num))))
     (64,64)))))
    (64,128)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q8:(armstate,(128)word)component)
    (s:armstate) =
    (word_pmul:(64)word->(64)word->(128)word)
    ((word_subword:(128)word->num#num->(64)word)
     ((word_xor:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word)
      ((nist_ghash:(128)word->(128)word->((128)word)list->(128)word)
       ((aes128_cipher:(128)word->((128)word)list->(128)word)
        ((word:num->(128)word) 0)
       (rk:((128)word)list))
       (tag0:(128)word)
      ((list_of_seq:(num->(128)word)->num->((128)word)list)
       ((nist_input_block:(num->(128)word)->num->(128)word)
       (inblock:num->(128)word))
      (4 * (i:num)))))
     ((word_join:(64)word->(64)word->(128)word)
      ((word_subword:(128)word->num#num->(64)word)
       ((word_reversefields:num->(128)word->(128)word) 8
       ((inblock:num->(128)word) (4 * (i:num))))
      (0,64))
     ((word_subword:(128)word->num#num->(64)word)
      ((word_reversefields:num->(128)word->(128)word) 8
      ((inblock:num->(128)word) (4 * (i:num))))
     (64,64))))
    (64,64))
    ((word_subword:(128)word->num#num->(64)word)
     ((byteswap128:(128)word->(128)word)
     ((h_power:(128)word->num->(128)word)
      ((ghash_twist:(128)word->(128)word)
      ((aes128_cipher:(128)word->((128)word)list->(128)word)
       ((word:num->(128)word) 0)
      (rk:((128)word)list)))
     3))
    (64,64))`;;

(* ===== GHASH-seed / reduce closers ===== *)
(* dec-swp BODYLEG unified closer (reconstructed clean half: lemmas + GHASH/partial tactics).
   dec-swp BODYLEG unified closer (2026-08-24). Applies AFTER:
   preamble + body_step_tac_plain (110s) + back-edge resolve + ENSURES_FINAL_STATE_TAC.
   Strategy: normalize arith/counters globally, then REPEAT CONJ_TAC and route each
   residual subgoal through FIRST[...] of the verified per-conjunct closers.
   Requires v5 invariant + all swp-prelude lemmas + SWP_GHASH_CORE helpers + Q5 lemmas.
   ============================================================================ *)

(* helper lemmas (proven) *)
let SWP_JOIN_IS_BSW = prove
 (`!x:int128. word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128]);;
let SWP_SUBWORD_JOIN_MID = WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`;;
let xor_rcancel = prove(`!a b p:int128. (word_xor a p = word_xor b p) <=> (a = b)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;
let SWP_SUB_LEMMA = prove
 (`i < loop_count - 2 ==> word_sub (word (loop_count - 2 - i):int64) (word 1) = word (loop_count - 2 - (i + 1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - 2 - (i + 1) = (loop_count - 2 - i) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < loop_count - 2 ==> 1 <= loop_count - 2 - i`]);;
let dewrap80 = prove(`word (64 * i + 18446744073709551696):int64 = word (16 * (4 * i + 5))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551696 = (16 * (4 * i + 5)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap96 = prove(`word (64 * i + 18446744073709551712):int64 = word (16 * (4 * i + 6))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551712 = (16 * (4 * i + 6)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap112 = prove(`word (64 * i + 18446744073709551728):int64 = word (16 * (4 * i + 7))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551728 = (16 * (4 * i + 7)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let SWP_GHASH_BRANCH2 = prove
 (`polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*i+3):int128)
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*i+2))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*i+1))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes128_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*i)))
                          (nist_input_block inblock (4*i)))
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes128_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*i+4))`,
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*i+1); nist_input_block inblock (4*i+2); nist_input_block inblock (4*i+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*i)):int128`;
                 `nist_input_block inblock (4*i):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* branch1+branch2 reconstruction of the reduce = nist_ghash..4i+4 (after the goal is that eq) *)
let SWP_REDUCE_RECON : tactic =
  MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))`;
      `cipherblock_0 = nist_input_block inblock (4 * i)`; `cipherblock_1 = nist_input_block inblock (4 * i + 1)`;
      `cipherblock_2 = nist_input_block inblock (4 * i + 2)`; `cipherblock_3 = nist_input_block inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3 (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
      (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
      (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
      (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    ACCEPT_TAC SWP_GHASH_BRANCH2];;

(* the seed-core: goal word_xor(acc-half)(pending) = word_xor(byteswap128 ghash..4i+4)(pending')  *)
let SWP_SEED_CORE : tactic =
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  SWP_REDUCE_RECON;;

(* Q11 conjunct closer [8]: DISCH not needed (rk-fold in asl) *)
let SWP_Q11_TAC : tactic = DEC_GHASH_NORM_TAC THEN SWP_SEED_CORE;;

(* generic discharge of wrapped in_p reads via the kept input-forall *)
let DISCHARGE_INP_READS : tactic =
  fun (asl,w) ->
    let reads = setify(find_terms (fun t->match t with
       Comb(Comb(Const("read",_),Comb(Comb(Const("(:>)",_),Const("memory",_)),
         Comb(Comb(Const("word_add",_),v),Comb(Const("word",_),_)))),_)
         when (try fst(dest_var v)="in_p" with _->false) -> true | _->false) w) in
    if reads=[] then ALL_TAC (asl,w) else
    (MAP_EVERY (fun rd ->
       let off = rand(rand(rator rd)) in
       let blk = (try rand off with _ -> off) in
       SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) (fun th->REWRITE_TAC[th]) THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) reads) (asl,w);;

let SWP_PARTIAL_TAC : tactic =
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dewrap80; dewrap96; dewrap112] THEN
  TRY DISCHARGE_INP_READS THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[];;

(* ===== counter-cluster closers ===== *)
(* dec-swp counter-cluster closers (rebuilt from memory recipe after 2026-08-25 reboot).
   Requires: prelude (CTR_BLOCK_BUILD_INSERT, MERGE_CTR128_TAC, CTR_ZX_NORM, ZX_COUNTER_UD,
   WORD_REVERSEFIELDS_REVERSEFIELDS, WORD_SIMPLE_SUBWORD_CONV) + aes2c defined. *)
let SLOT_LANE_FOLDS = [
  WORD_RULE `word_add (word (4*i+6)) (word 1):int32 = word(4*i+7)`;
  WORD_RULE `word_add (word (4*i+6)) (word 2):int32 = word(4*i+8)`;
  WORD_RULE `word_add (word (4*i+6)) (word 3):int32 = word(4*i+9)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word 6)) (word 1):int32 = word(4*i+7)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word 6)) (word 2):int32 = word(4*i+8)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word 6)) (word 3):int32 = word(4*i+9)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word 6)) (word 4):int32 = word(4*i+10)`];;
let RHS_IDX_NORMS = [
  ARITH_RULE `(4 * i + 4) + 4 = 4*i+8`; ARITH_RULE `(4 * i + 4) + 5 = 4*i+9`;
  ARITH_RULE `(4 * i + 4) + 6 = 4*i+10`; ARITH_RULE `(4 * i + 4) + 7 = 4*i+11`];;
let Q30_TAC : tactic =
  REWRITE_TAC[aes2c] THEN MERGE_CTR128_TAC 160 "s112" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC;;
let SP160_TAC : tactic =
  MERGE_CTR128_TAC 160 "s159" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (word (4*i)) (word 6)) (word 4):int32 = word(4*i+10)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC;;
let SP_SLOT_TAC3 : tactic =
  REWRITE_TAC RHS_IDX_NORMS THEN REWRITE_TAC SLOT_LANE_FOLDS THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY REFL_TAC;;
let CTR_ADD_FOLDS = [
  WORD_RULE `word_add (word (4*i+6)) (word 4):int32 = word(4*i+10)`;
  WORD_RULE `word_add (word (4*i+10)) (word 1):int32 = word(4*i+11)`;
  WORD_RULE `word_add (word (4*i+10)) (word 2):int32 = word(4*i+12)`;
  WORD_RULE `word_add (word (4*i+10)) (word 3):int32 = word(4*i+13)`];;
let CTR_RHS_NORMS = [
  ARITH_RULE `(4*i+4)+7 = 4*i+11`; ARITH_RULE `(4*i+4)+9 = 4*i+13`;
  ARITH_RULE `(4*i+4)+6 = 4*i+10`; ARITH_RULE `(4*i+4)+8 = 4*i+12`];;
let CTRREG_TAC : tactic =
  REWRITE_TAC CTR_RHS_NORMS THEN REWRITE_TAC CTR_ADD_FOLDS THEN TRY REFL_TAC THEN TRY(CONV_TAC WORD_RULE);;

(* ===== out-store orthogonality closers ===== *)
(* dec-swp OUT-STORE tactics (BREAKTHROUGH 2026-08-25): close the [0] `forall j.j<4i` preservation.
   KEY: needs `16 * nblocks <= 2 EXP 64` in scope (derivable from nblocks = len_bits DIV 128, since
   val len_bits < 2^64 => nblocks < 2^57).  Requires prelude. *)
let pth128 = prove
   (`!(a:int64) m n. 16 <= val(word_sub (word m) (word n):int64) /\ 16 <= val(word_sub (word n) (word m):int64)
          ==> orthogonal_components (bytes128 (word_add a (word m))) (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; DIMINDEX_64]) THEN
    MP_TAC(ISPEC `word m:int64` VAL_BOUND) THEN MP_TAC(ISPEC `word n:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
let orth_lemma = prove
   (`orthogonal_components c d /\ read c s' = read c s ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]);;
(* orthogonal_components (memory:>bytes128 out+16j) (memory:>bytes128 out+OFF), j<4i, bounds in scope *)
let OUT_ORTH_TAC : tactic =
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC pth128 THEN
    W(fun (asl,w) ->
      let sub1 = rand(rand(fst(dest_conj w))) in
      let mtm = rand(rator sub1) and ntm = rand sub1 in
      let m = rand mtm and n = rand ntm in
      SUBGOAL_THEN (list_mk_conj [mk_binop `(<):num->num->bool` m `2 EXP 64`;
                                  mk_binop `(<):num->num->bool` n `2 EXP 64`])
        STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];;
let ORTH_STEP : tactic =
  FIRST [ OUT_ORTH_TAC; ORTHOGONAL_COMPONENTS_TAC;
          (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
            [CONV_TAC VALID_COMPONENT_CONV; ORTHOGONAL_COMPONENTS_TAC]) ];;
let rec OUT_ROW_TAC g =
  (REFL_TAC ORELSE (MATCH_MP_TAC orth_lemma THEN CONJ_TAC THENL [ORTH_STEP; OUT_ROW_TAC])) g;;
(* full [0] closer: forall j.j<4i ==> read(out+16j)sHI = word_xor(aes_ctr j)(inblock j) *)
let OUT0_TAC : tactic =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) && free_in `s0:armstate`(concl th) with _->false)
                        then ASSUME_TAC(SPEC `j:num` th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if (try is_imp(concl th) && free_in `s0:armstate`(concl th) with _->false)
                          then ASSUME_TAC(MP th (ASSUME `j < 4 * i`)) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && free_in `out_p:int64`(concl th) && free_in `s0:armstate`(concl th)
                                && fst(dest_const(fst(strip_comb(lhs(concl th)))))="read" with _->false)
                          then GEN_REWRITE_TAC RAND_CONV [SYM th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if (try not(is_eq(concl th)) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) (concl th) with _->false)
                        then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  OUT_ROW_TAC;;

(* ===== body-simulation machinery + BODYLEG goal ===== *)
let (MUST:tactic->tactic) = fun t (asl,w) ->
  let (m,gls,f) = t (asl,w) in
  (match gls with [(_,w')] when w' = w -> failwith "MUST: not closed" | _ -> (m,gls,f));;

let dec_setup_extra : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;

let IN_P_ADDR_FOLD_CONV : conv =
  let inner = (REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) in
  ONCE_DEPTH_CONV(fun t -> match t with
    | Comb(Comb(Const("word_add",_), v), Comb(Const("word",_), _))
        when (try fst(dest_var v) = "in_p" with _ -> false)
      -> RAND_CONV(RAND_CONV inner) t
    | _ -> failwith "IN_P_ADDR_FOLD_CONV");;
let gc2 keeplist c = try let l=lhs c in let rd,st=dest_comb l in let rr,cc=dest_comb rd in
   if is_const cc && mem (fst(dest_const cc)) keeplist then
     (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
        (try Some(fst(dest_const cc), int_of_string(String.sub nm 1 (String.length nm-1))) with _->None) |_->None) else None
  with _->None;;
let is_spctr_read c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in v="160"||v="176"||v="192"||v="208") | _ -> false)) l)
  with _ -> false;;
let state_of_forall c =
  try let rd = find_term (fun t -> match t with
        Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=1 && nm.[0]='s' -> true | _->false) c in
      (match rd with Comb(_,Var(nm,_)) -> Some nm | _ -> None) with _ -> None;;
let gkeepN_mem2 keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    let anchored c = try (is_spctr_read c) ||
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) || (free_in `htable_p:int64` (lhs c))))
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q9";"Q10";"Q11";"Q29";"Q30";"Q31";
                   "X0";"X2";"X7";"X13";"X14";"X17";"X21";"X23";"X24";"X25";"X26";"X27";"X29"];;
let steady_merges = [(17,208);(46,176);(52,192);(112,160)];;
let body_step_tac_gkeep =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        gkeepN_mem2 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k steady_merges then MERGE_CTR128_TAC (List.assoc k steady_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--159)) (asl,w));;

(* ---- extra closers: out-block recon (OUTBLK), in-read folder (INFOLD3), byteswap, GHASH partial ---- *)
let inp_addr_norms = List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*i+K)):int64 = word_add in_p (word (16*(4*i+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;
(* INFOLD3: dewrap + normalize addrs to 16*(4i+m), then fold EACH in-read via the in-forall (FIRST_ASSUM keeps
   the forall so multiple reads can reuse it). blk = rand(16*blk) where off=word(16*blk). *)
let INFOLD3 : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms (fun t -> match t with
      | Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes128",_),a))),st)
          when (free_in `in_p:int64` a && (match st with Var _->true|_->false)) -> true | _->false) w) in
    if inreads=[] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let st = rand rd in
       (* blk = the BLK in the `word (16 * BLK)` address subterm of rd *)
       let sixteenblk = rand(find_term (fun t -> match t with
           Comb(Const("word",_), n) when (try fst(dest_const(fst(strip_comb n)))="*" with _->false) -> true | _->false) rd) in
       let blk = rand sixteenblk in
       (SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) && free_in st (concl fa) with _->false)
                                 then MATCH_MP_TAC fa else NO_TAC) THEN ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;
let GHASH_PARTIAL_CLOSE : tactic =
  INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* read(in_p+ADDR)sK = inblock(blk): dewrap+norm then in-forall. *)
let IN_READ_CLOSE : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN ASM_ARITH_TAC;;
let SWP_BYTESWAP_REASSEMBLE_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* block-4i/4i+1 out-store via aes2c(4i+2): unfold aes2c, reconstruct AES tower to aes_ctr_block. *)
let AES2C_OUT_TAC : tactic =
  REWRITE_TAC[aes2c] THEN REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `4*i+2 = (4*i)+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+3 = (4*i+1)+2`] THEN REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC;;
(* frame (,, s0 sN): use the asl MAYCHANGE-seq fact + subsumption. *)
let pth_frame = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
let close_goal10 : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_goal10: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP pth_frame frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;
(* out-block recon: addr rewrite param + reconstruct + counter-collapse (handles +96/+112).
   GUARD: fail-fast unless this closer's own offset (addr_rule LHS, e.g. 64*i+96 or
   64*i+112) actually occurs in the goal.  Without this, FIRST[close_outahead96;
   close_outahead112] on the +112 goal runs close_outahead96's addr_rule as a no-op but
   still executes the rest of OUTBLK_TAC, which mangles/errors ("MATCH_MP_TAC: No match"
   via the GHASH fallback) before close_outahead112 is ever tried. *)
let OUTBLK_TAC (addr_rule:thm) : tactic =
  fun (asl,w) ->
    if not (free_in (lhs(concl addr_rule)) w)
    then failwith "OUTBLK_TAC: offset absent" else
   (REWRITE_TAC[addr_rule] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[aes_ctr_block] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
  REWRITE_TAC[WORD_RULE `word_add (word (4*i+6)) (word 2):int32 = word(4*i+8)`;
              WORD_RULE `word_add (word (4*i+7)) (word 2):int32 = word(4*i+9)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+8 = (4*i+6)+2`; ARITH_RULE `4*i+9 = (4*i+7)+2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC) (asl,w);;
let close_outahead96 : tactic = OUTBLK_TAC (ARITH_RULE `64 * i + 96 = (64 * i + 64) + 32`);;
let close_outahead112 : tactic = OUTBLK_TAC (ARITH_RULE `64 * i + 112 = (64 * i + 64) + 48`);;

(* ---- SWP_GHASH_CORE_TAC : the crux GHASH-reduce closer (recovered PROVEN, 2026-08-25). NODISCH variant. ----
   Closes a `word_xor(...)=word_xor(...byteswap128(nist_ghash..4i)...)` GHASH-seed eq via byteswap-split +
   ABBREV + RECONSTRUCT_POLYVAL_REDUCE_G2 + TRANS through polyval_reduce_prop3 + branch1(Karatsuba+BITBLAST)
   + branch2(SWP_GHASH_BRANCH2). The branch1 BITBLAST is ~1500-var (native-only, ~117s; exceeds 600s MCP cap). *)
let SWP_GHASH_CORE_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))`;
      `cipherblock_0 = nist_input_block inblock (4 * i)`; `cipherblock_1 = nist_input_block inblock (4 * i + 1)`;
      `cipherblock_2 = nist_input_block inblock (4 * i + 2)`; `cipherblock_3 = nist_input_block inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    ACCEPT_TAC SWP_GHASH_BRANCH2];;
(* Q8 settled partial (word_pmul head): peel the pmul(subword) on the RAW conjunct then core. *)
let SWP_Q8_TAC : tactic = AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SWP_GHASH_CORE_TAC;;
(* Q6 compound (word_xor head, seed appears twice): BINOP split -> g0 core, g1 subword-join -> AP_THM/AP_TERM
   then re-split to subword-level + core (or BINOP again). *)
let SWP_Q6_TAC : tactic = SWP_GHASH_CORE_TAC;;
let SWP_Q6_FULL_TAC : tactic =
  BINOP_TAC THENL
   [SWP_GHASH_CORE_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN
    (SWP_GHASH_CORE_TAC ORELSE (BINOP_TAC THEN SWP_GHASH_CORE_TAC))];;

(* master closer: shape-gated, most-specific first. SWP_Q11_TAC for the big GHASH reduces. *)
let CLOSE_V8 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let rh c = try has c (rhs w) with _->false in
    if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_eq w && rh "aes2c" then MUST Q30_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "inblock" && not(rh "word_xor") && not(rh "aes_ctr_block") then MUST IN_READ_CLOSE (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "ctr_block" && rh "word_reversefields" then MUST SP160_TAC (asl,w)
    else if is_eq w && hd(lhs w)="word_join" && rh "ctr_block" && rh "word_reversefields" then MUST SP_SLOT_TAC3 (asl,w)
    else if is_eq w && (hd(lhs w)="word_or" || (hd(lhs w)="word_zx" && String.length(string_of_term w)<200)) then MUST CTRREG_TAC (asl,w)
    else if is_forall w then MUST OUT0_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "aes_ctr_block" then MUST (FIRST[close_outahead96; close_outahead112]) (asl,w)
    (* GHASH-reduce goals: RHS mentions nist_ghash (settled accumulator). Peel on RAW then SWP_GHASH_CORE_TAC. *)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_pmul" then MUST (FIRST[SWP_Q8_TAC; SWP_GHASH_CORE_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_xor" then MUST (FIRST[SWP_GHASH_CORE_TAC; SWP_Q6_FULL_TAC; SWP_Q11_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash" then MUST (FIRST[SWP_GHASH_CORE_TAC; SWP_Q11_TAC]) (asl,w)
    (* aes2c-based out-store readback: LHS = word_xor(inblock)(word_xor(rk10)(aese-tower)), RHS = word_xor(aes_ctr_block)(inblock) *)
    else if is_eq w && rh "aes_ctr_block" && (has "aes2c" w || has "aese" (lhs w)) then MUST AES2C_OUT_TAC (asl,w)
    (* byteswap reassembly / Karatsuba partials over reassembled input blocks *)
    else if is_eq w && hd(lhs w)="word_join" then MUST (FIRST[SWP_BYTESWAP_REASSEMBLE_TAC; GHASH_PARTIAL_CLOSE]) (asl,w)
    else MUST (FIRST[GHASH_PARTIAL_CLOSE; AES2C_OUT_TAC; SWP_Q11_TAC; CTRREG_TAC; ASM_REWRITE_TAC[] THEN TRY REFL_TAC]) (asl,w);;

(* ---- goal ---- *)
let ap inv i s = rhs(concl(REDEPTH_CONV BETA_CONV (list_mk_comb(inv,[i;s]))));;
let sv = `s:armstate` and iv = `i:num` and ip1 = `i+1`;;
let abl = `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc`;;
let pcpre = `read PC s = word (pc + 0x294)` and pcpost = `read PC s = word (pc + 0x510)`;;
let bodyleg_pre  = mk_abs(sv, mk_conj(abl, mk_conj(pcpre,  ap swpS_inv8_dec_v8 iv  sv)));;
let bodyleg_post = mk_abs(sv, mk_conj(abl, mk_conj(pcpost, ap swpS_inv8_dec_v8 ip1 sv)));;
let bodyleg_frame = `(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`;;
let bodyleg_ens = list_mk_comb(`ensures arm`,[bodyleg_pre;bodyleg_post;bodyleg_frame]);;
let bodyleg_hyps = `aligned 16 (stackpointer:int64) /\
    nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
    16 * nblocks <= 2 EXP 64 /\
    ([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
    i < loop_count - 2 /\
    nonoverlapping ((out_p:int64), 16 * nblocks) (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) ((key_p:int64), 176) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) ((htable_p:int64), 192) /\
    nonoverlapping ((out_p:int64), 16 * nblocks) ((in_p:int64), 16 * nblocks) /\
    nonoverlapping ((in_p:int64), 16 * nblocks) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((out_p:int64), 16 * nblocks) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((tag_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((tag_p:int64), 16) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((ivec_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((ivec_p:int64), 16) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((htable_p:int64), 192) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((htable_p:int64), 192) (word_add (stackpointer:int64) (word 160), 64)`;;
let vs = [`in_p:int64`;`out_p:int64`;`len_bits:int64`;`tag_p:int64`;`ivec_p:int64`;`key_p:int64`;`htable_p:int64`;
          `tag0:int128`;`nonce:int128`;`rk:(int128)list`;`inblock:num->int128`;`pc:num`;
          `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;`i:num`];;
let bodyleg_goal_v8 = list_mk_forall(vs, mk_imp(bodyleg_hyps, bodyleg_ens));;

(* ===== drain GHASH composition lemmas ===== *)
(* ============================================================================
   DRAIN Q30 composition lemmas: settle the depth-2 (2-group) GHASH reduce by
   splitting it into two single-group reduces (John's decomposition).  All proven
   axiom-free from GHASH_POLYVAL_ACC_BATCHED / NIST_GHASH_APPEND / list_of_seq.
   Load AFTER RESTORE_dec_swp_session.ml (needs those + swp_closer_cleanhalf).
   ============================================================================ *)

(* byteswap128 is an involution (peel/re-apply the machine byteswap). *)
let BSW_INVOL = prove
 (`!x:int128. byteswap128 (byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* list_of_seq split: last 4 elements peel off as an explicit 4-list. *)
let LIST_OF_SEQ_ADD4 = prove
 (`!(f:num->A) n. list_of_seq f (n + 4) =
       APPEND (list_of_seq f n) [f n; f (n+1); f (n+2); f (n+3)]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = SUC(n+3)`; ARITH_RULE `n + 3 = SUC(n+2)`;
              ARITH_RULE `n + 2 = SUC(n+1)`; ARITH_RULE `n + 1 = SUC n`] THEN
  REWRITE_TAC[list_of_seq] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The final accumulator = the last group reduced into the prefix accumulator. *)
let GHASH_LASTGROUP_SPLIT = prove
 (`1 <= loop_count ==>
   nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * loop_count)) =
   nist_ghash (aes128_cipher (word 0) rk)
     (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * (loop_count - 1))))
     [nist_input_block inblock (4*(loop_count-1)); nist_input_block inblock (4*(loop_count-1)+1);
      nist_input_block inblock (4*(loop_count-1)+2); nist_input_block inblock (4*(loop_count-1)+3)]`,
  DISCH_TAC THEN
  SUBGOAL_THEN `4 * loop_count = 4 * (loop_count - 1) + 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD4] THEN REWRITE_TAC[NIST_GHASH_APPEND]);;

(* Generalized branch2: the 4-product Karatsuba fold reduced = one nist_ghash group over ANY acc. *)
let SWP_GHASH_BRANCH2_GEN = prove
 (`!acc:int128 m.
     polyval_reduce_prop3
       (word_xor (word_pmul (nist_input_block inblock (m+3):int128)
                            (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0))
       (word_xor (word_pmul (nist_input_block inblock (m+2))
                            (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (word_xor (word_pmul (nist_input_block inblock (m+1))
                            (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2))
       (word_pmul (word_xor (acc:int128) (nist_input_block inblock m))
                  (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes128_cipher (word 0) rk) acc
       [nist_input_block inblock m; nist_input_block inblock (m+1);
        nist_input_block inblock (m+2); nist_input_block inblock (m+3)]`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[nist_input_block inblock (m+1); nist_input_block inblock (m+2); nist_input_block inblock (m+3)]:(int128)list`;
                 `acc:int128`; `nist_input_block inblock m:int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[APPEND] THEN REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* SETTLED branch2: acc presented as the settled accumulator nist_ghash..(list_of_seq..(4*k)); RHS is the
   NEXT settled accumulator nist_ghash..(list_of_seq..(4*k+4)) -- exactly the byteswap-split goal's RHS form
   (unlike _GEN which yields nist_ghash h acc [4 explicit blocks], not syntactically the list_of_seq form).
   This is BODYLEG's SWP_GHASH_BRANCH2 generalized from the literal 4*i to an arbitrary 4*k. *)
let SWP_GHASH_BRANCH2_SETTLED = prove
 (`!k. polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*k+3):int128)
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*k+2))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*k+1))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes128_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*k)))
                          (nist_input_block inblock (4*k)))
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes128_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*k+4))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*k+1); nist_input_block inblock (4*k+2); nist_input_block inblock (4*k+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*k)):int128`;
                 `nist_input_block inblock (4*k):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * k + 4 = SUC(SUC(SUC(SUC(4 * k))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ================= BODYLEG: steady body  inv i -> inv (i+1)  (0x294 -> 0x510) ================= *)
let SWP_DEC_BODYLEG = prove(bodyleg_goal_v8,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN
    MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `i < loop_count - 2` THEN SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*i+64)))) s0 = inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+80)))) s0 = inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+96)))) s0 = inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+112)))) s0 = inblock (4*i+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+64)):int64 = word_add in_p (word (16*(4*i+4)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+80)):int64 = word_add in_p (word (16*(4*i+5)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+96)):int64 = word_add in_p (word (16*(4*i+6)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+112)):int64 = word_add in_p (word (16*(4*i+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  dec_setup_extra THEN
  body_step_tac_gkeep THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                          j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/ j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
              ARITH_RULE `(4 * i + 4) + 1 = 4 * i + 5`; ARITH_RULE `(4 * i + 4) + 2 = 4 * i + 6`;
              ARITH_RULE `(4 * i + 4) + 3 = 4 * i + 7`;
              ARITH_RULE `(64 * i + 64) + 64 = 64 * i + 128`;
              ARITH_RULE `(64 * i + 64) + 32 = 64 * i + 96`;
              ARITH_RULE `(64 * i + 64) + 48 = 64 * i + 112`;
              ARITH_RULE `(4 * i + 4) + 6 = 4 * i + 10`;  ARITH_RULE `(4 * i + 4) + 9 = 4 * i + 13`] THEN
  REWRITE_TAC[WORD_RULE `word_add (word (4 * i + 6)) (word 4):int32 = word(4 * i + 10)`] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA] THEN
  REPEAT CONJ_TAC THEN CLOSE_V8);;

(* ================= FILL: entry -> inv 0  (0xa0 -> 0x294) ================= *)
(* shared with DRAIN: abl_s, REV64_16B_IS_BSW_REVFIELDS, is_spctr_read2, gkeep2 (FILL's variant). *)
let fill_pre_body = `read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\ read X4 s = ivec_p /\
    read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word 2:int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X1 s = word loop_count /\
    read X7 s = word nblocks /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j)`;;

let abl_s = `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc`;;
let fill_pre  = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xa0)`, fill_pre_body)));;
let fill_post = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0x294)`, ap swpS_inv8_dec_v8 `0` `s:armstate`)));;
let fill_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X0;X1;X2;X7;X10;X11;X12;X13;X14;X17;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30] ,,
    MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8;Q9;Q10;Q11;Q29;Q30;Q31] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
               memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let fill_ens = list_mk_comb(`ensures arm`,[fill_pre;fill_post;fill_frame]);;
let fill_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] bodyleg_hyps;;
let vs_fill = filter (fun v -> v <> `i:num`) vs;;
let fill_goal = list_mk_forall(vs_fill, mk_imp(fill_hyps, fill_ens));;

(* ---- branch-resolution lemmas for the two guards at 0xa4/0xa8 (b.eq iter_1) and 0x290 (cbz drain) ---- *)
let branch_lem = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);;
let branch_lem2 = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 2)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word 2:int64) = 2` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);;

(* bridge: the machine rev64.16b(block) = byteswap128(word_reversefields 8 block); needed to close the
   i=0 GHASH seed (Q11) whose FILL machine value is rev64.16b(inblock 0) but the invariant writes it as
   byteswap128(word_reversefields 8 (inblock 0)). *)
let REV64_16B_IS_BSW_REVFIELDS = prove(
  `word_join (word_bytereverse (word_subword (x:int128) (64,64):int64):int64)
             (word_bytereverse (word_subword (x:int128) (0,64):int64):int64):int128
   = byteswap128 (word_reversefields 8 x)`,
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[GSYM WORD_EQ_BITS_ALT] THEN REWRITE_TAC[byteswap128] THEN
  CONV_TAC(BINOP_CONV(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  CONV_TAC BITBLAST_RULE);;

(* FILL per-conjunct closer.  Applied AFTER the goal-level arith-normalization pass, so conjuncts
   are in `inblock k` / literal-offset form (same shape CLOSE_V8 expects from BODYLEG).  The Q11 seed
   at i=0 additionally needs nist_ghash..0 -> tag0 (empty Horner); handle it explicitly first. *)
(* FILL out-store closer for the two stored-ahead blocks (2,3) at literal offsets 32/48
   (X2 = out_p, not advanced during the fill).  Mirrors OUTBLK_TAC's reconstruction body but
   with NO address-normalisation (offsets are already literal). *)
let FILL_OUTBLK_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN REWRITE_TAC[aes_ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;

(* ks9 counter-base lemma: the inline staged-counter for block 3 (i=0) = revfields8(ctr_block nonce 3).
   Lets the machine Q5 keystream (base = read(sp+176) = revfields8(ctr_block nonce 3) via the invariant's
   own sp+176 conjunct) match the invariant ks9's inline-counter base inside the 9-round AES tower. *)
let KS9_CTRBASE_0 = prove(
  `word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word 3:int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
   = word_reversefields 8 (ctr_block nonce 3)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* i=0 counter-base folds: the FILL staged counter-lane joins = word_reversefields 8 (ctr_block nonce K),
   for K in {2,3,4,5,6}.  Proven uniformly by REWRITE[ctr_block] + WORD_BLAST (like KS9_CTRBASE_0). *)
let CTR_LANE_FOLD_0 = prove(
  `(word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+3):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+3))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+4):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+4))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+5):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+5))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+6):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+6)))`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* counter-base folds with the REDUCED shl-numeral (the stepping reduces word_shl(word_bytereverse(word k))32
   to a numeral): the FILL staged counter-lane join = word_reversefields 8 (ctr_block nonce K) for K=2..6. *)
let CTRBASEN =
  let mk_ctrbase k num =
    mk_eq(subst [mk_numeral(Num.num_of_int num),`NUM:num`]
      `word_join
        (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
                 (word NUM:int64):int64)
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128`,
      subst [mk_small_numeral k,`K:num`] `word_reversefields 8 (ctr_block nonce K)`) in
  prove(list_mk_conj [mk_ctrbase 2 144115188075855872; mk_ctrbase 3 216172782113783808;
                      mk_ctrbase 4 288230376151711744; mk_ctrbase 5 360287970189639680;
                      mk_ctrbase 6 432345564227567616],
        REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* extended-anchor keep-stepper: also anchor sp-slot HIGH-half offsets 168/184/200/216 so both stp halves
   survive to enable bytes128 counter reconstruction at any state. *)
let is_spctr_read2 c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in
              v="160"||v="176"||v="192"||v="208"||v="168"||v="184"||v="200"||v="216") | _ -> false)) l)
  with _ -> false;;
let gkeep2 keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    let anchored c = try (is_spctr_read2 c) ||
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) || (free_in `htable_p:int64` (lhs c))))
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;

(* FILL per-conjunct closer.  8 shape-specific branches (all validated interactively, 24/24). *)
let FILL_CLOSE : tactic =
  FIRST
   [ (* GHASH (seed Q11 + partials): reassembly + ghash-nil + UNFOLD byteswap128 + bridge + WORD_BLAST *)
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REV64_16B_IS_BSW_REVFIELDS; byteswap128] THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (* counter stack slots (bytes128, merged at s125): ASM then fold counter numerals to ctr_block *)
     (ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (* Q30/ks9 aes towers: MERGE the base at its load state, fold counter numeral, aes defs, REFL/BLAST *)
     ((MERGE_CTR128_TAC 160 "s77" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 176 "s29" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[aes2c] THEN (REFL_TAC ORELSE (REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)) THEN NO_TAC);
     (* out-stores blk2,3: MERGE base, fold counter, DEC readback recon, fold key-list=rk, aes_ctr_block, REFL *)
     ((MERGE_CTR128_TAC 192 "s32" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 208 "s18" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN TRY REFL_TAC THEN NO_TAC);
     (* word_sub loop-count *)
     (SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[WORD_SUB]] THEN NO_TAC);
     (* MAYCHANGE frame *)
     (close_goal10 THEN NO_TAC);
     (* trivial registers / htable (post htable-unfold, the 4 reads close by ASM) *)
     (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
     (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE THEN NO_TAC) ];;

(* ---- FILL stepper: gkeep2 (extended anchor) + FILL merge sites + branch/COND simplification ---- *)
let fill_merges = [(10,160);(12,176);(15,208);(21,192)];;
let fill_step_tac =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        gkeep2 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 0 <=> F`; ASSUME `loop_count = 1 <=> F`;
           ASSUME `loop_count = 2 <=> F`;
           ASSUME `val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F`; COND_CLAUSES]) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k fill_merges then MERGE_CTR128_TAC (List.assoc k fill_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--125)) (asl,w));;

(* Diagnostic per-conjunct closer: try FILL_CLOSE; if it fails, PRINT the conjunct goal and leave it. *)

let SWP_DEC_FILLLEG = prove(fill_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`nblocks DIV 4 = loop_count`; `16 * nblocks <= 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `loop_count:num` THEN
  SUBGOAL_THEN `(loop_count = 0 <=> F) /\ (loop_count = 1 <=> F) /\ (loop_count = 2 <=> F)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL branch_lem) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* unfold htable_mem_4 -> 4 htable_p reads (anchored by gkeep2, survive to final state); also in goal *)
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (* input blocks 0..3 pinned for the fill's group-0 loads (in_p+{0,16,32,48}) *)
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  fill_step_tac THEN
  (* resolve the final cbz @ 0x290 (word_sub .. word 2) then reach 0x294 *)
  MP_TAC(SPEC_ALL branch_lem2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count:int64) (word 2)) = 0 <=> F`; COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* reconstruct the 4 invariant counter-slot bytes128 reads at s125 from the surviving stp halves;
     the aes-tower / out-store base merges are done per-conjunct inside FILL_CLOSE at their load states. *)
  MERGE_CTR128_TAC 160 "s125" THEN MERGE_CTR128_TAC 176 "s125" THEN
  MERGE_CTR128_TAC 192 "s125" THEN MERGE_CTR128_TAC 208 "s125" THEN
  ASM_REWRITE_TAC[] THEN
  (* goal-level i=0 arithmetic normalization *)
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`;
    ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 + 3 = 3`;
    ARITH_RULE `4 * 0 + 4 = 4`; ARITH_RULE `4 * 0 + 5 = 5`; ARITH_RULE `4 * 0 + 6 = 6`;
    ARITH_RULE `4 * 0 + 7 = 7`; ARITH_RULE `4 * 0 + 9 = 9`;
    ARITH_RULE `0 + 7 = 7`; ARITH_RULE `0 + 3 = 3`;
    ARITH_RULE `64 * 0 + 32 = 32`; ARITH_RULE `64 * 0 + 48 = 48`;
    ARITH_RULE `64 * 0 + 64 = 64`; ARITH_RULE `loop_count - 2 - 0 = loop_count - 2`] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FILL_CLOSE);;

(* ================= DRAIN: inv (loop_count-2) -> postcondition  (0x510 -> 0xaa0) ================= *)
(* Uses FILL's shared abl_s / REV64_16B_IS_BSW_REVFIELDS.  DRAIN's keep-stepper additionally anchors
   out_p STORE facts and in_p READ facts (drain_gkeep2), distinct from FILL's gkeep2. *)

let drain_is_spctr_read2 c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in
              v="160"||v="176"||v="192"||v="208"||v="168"||v="184"||v="200"||v="216") | _ -> false)) l)
  with _ -> false;;

let drain_gkeep2 keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    let anchored c = try (drain_is_spctr_read2 c) ||
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) || (free_in `htable_p:int64` (lhs c)) ||
          (free_in `out_p:int64` (lhs c)) ||
          (free_in `in_p:int64` (lhs c))))
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;

let drain_post_body = `read X0 s = word_add in_p (word (64 * loop_count)) /\
   read X2 s = word_add out_p (word (64 * loop_count)) /\
   read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
   read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
   read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
   read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
   read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
   read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
   read Q28 s = word_reversefields 8 (EL 10 rk) /\
   read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
   read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
   read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
   read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
   read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
   read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
   read Q7 s = word 13979173243358019584 /\
   read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
   read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
   read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
   read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\ read X16 s = word loop_remain /\
   read Q30 s = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * loop_count))) /\
   htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
   (!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s = word_xor (aes_ctr_block nonce rk j) (inblock j))`;;
let drain_pre = mk_abs(`s:armstate`, mk_conj(abl_s,
   mk_conj(`read PC s = word (pc + 0x510)`, ap swpS_inv8_dec_v8 `loop_count - 2` `s:armstate`)));;
let drain_post = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xaa0)`, drain_post_body)));;
let drain_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X0;X1;X2;X7;X10;X11;X12;X13;X14;X17;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30] ,,
    MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8;Q9;Q10;Q11;Q29;Q30;Q31] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks); memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let drain_ens = list_mk_comb(`ensures arm`,[drain_pre;drain_post;drain_frame]);;
let drain_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] bodyleg_hyps;;
let vs_drain = filter (fun v -> v <> `i:num`) vs;;
let drain_goal = list_mk_forall(vs_drain, mk_imp(drain_hyps, drain_ens));;

(* stepper: drain_gkeep2 + counter merges at the tower-referenced ldr states.  Step 98 (0x694) is the first
   reduce's final `ext v30`: abbreviate the settled group-(loop_count-2) accumulator to `inter` so the second
   reduce + downstream references fold it (a 10x collapse of the Q30 tower). *)
let drain_merges = [(18,208);(43,176);(49,192)];;
let drain_step_tac =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        drain_gkeep2 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if k = 98 then REABBREV_TAC (mk_eq(`inter:int128`, `read Q30 s98`)) else ALL_TAC) THEN
        (if List.mem_assoc k drain_merges then MERGE_CTR128_TAC (List.assoc k drain_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--198)) (asl,w));;

let rhs_has c w = try (is_eq w) && can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) (rhs w) with _->false;;

(* Parameterized settled-Q30 single-group closer.  ktm = the SETTLED group index (acc = nist_ghash..(4*ktm),
   branch2 uses SWP_GHASH_BRANCH2_SETTLED ktm); off = 0 for subgoal B (blocks 4*(loop_count-2)+0..3), 4 for
   subgoal A (blocks +4..+7).  The cipherblock ABBREVs use the goal's LITERAL block index 4*(loop_count-2)+(off+j);
   a pre-branch2 arith bridge reconciles that base to 4*ktm for the SETTLED lemma. *)
let GHASH_SETTLE_TAC (ktm:term) (off:int) : tactic =
  let mtm = mk_binop `( * ):num->num->num` `4` ktm in
  let basetm = `4 * (loop_count - 2)` in
  let sofartm = subst [ktm, `k:num`]
     `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*k))` in
  let blkidx j = if off+j = 0 then basetm
                 else mk_binop `(+):num->num->num` basetm (mk_small_numeral (off+j)) in
  DEC_GHASH_NORM_TAC THEN
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  INFOLD3 THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
     [ mk_eq(`sofar:int128`, sofartm);
       mk_eq(`cipherblock_0:int128`, mk_comb(`nist_input_block inblock`, blkidx 0));
       mk_eq(`cipherblock_1:int128`, mk_comb(`nist_input_block inblock`, blkidx 1));
       mk_eq(`cipherblock_2:int128`, mk_comb(`nist_input_block inblock`, blkidx 2));
       mk_eq(`cipherblock_3:int128`, mk_comb(`nist_input_block inblock`, blkidx 3));
       `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    INFOLD3 THEN
    REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    (CONV_TAC BITBLAST_RULE ORELSE BITBLAST_TAC) ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    (if off = 0 then ALL_TAC else
       SUBGOAL_THEN
         (list_mk_conj (map (fun j ->
            mk_eq(mk_binop `(+):num->num->num` `4*(loop_count-2)` (mk_small_numeral (off+j)),
                  if j = 0 then mtm else mk_binop `(+):num->num->num` mtm (mk_small_numeral j)))
          [0;1;2;3]))
         (fun th -> REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC]) THEN
    MP_TAC(ISPEC ktm SWP_GHASH_BRANCH2_SETTLED) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];;

(* The settled-Q30 conjunct closer (subgoal A + B via a two-single-group split).  `inter` was abbreviated at
   step 98 (the first reduce's settled accumulator); subgoal B proves inter = byteswap128(nist_ghash..(4*(loop_count-1))),
   subgoal A the final reduce over it. *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `inter = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
                        (list_of_seq (nist_input_block inblock) (4 * (loop_count - 1))))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && rhs(concl th) = `inter:int128`
                                 with _ -> false) then MP_TAC th else NO_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `4 * (loop_count - 1) = 4 * (loop_count - 2) + 4` SUBST1_TAC THENL
     [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    GHASH_SETTLE_TAC `loop_count - 2` 0;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && lhs(concl th) = `inter:int128` &&
                                 can(find_term(fun u->try fst(dest_const(fst(strip_comb u)))="nist_ghash" with _->false))(rhs(concl th))
                               with _ -> false) then SUBST1_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `4 * loop_count = 4 * (loop_count - 1) + 4` SUBST1_TAC THENL
   [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  GHASH_SETTLE_TAC `loop_count - 1` 4;;

(* Per-conjunct closer for the drain postcondition, shape-gated. *)
let DRAIN_CLOSE : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST OUT0_TAC; ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (DRAIN_Q30_TAC THEN NO_TAC) ]) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* out-store readback.  RECON handles both the aes2c (first-group) and stack-staged ctr_block bases,
          plus the counter-block reconstruction (CTR_BLOCK_BUILD_INSERT) and the rk-list fold (ASM_REWRITE).
          blocks +5/+6/+7 first addr-normalize their store-fact address. Every option ends THEN NO_TAC. *)
       (let RECON =
          REWRITE_TAC[aes2c] THEN
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
          CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `(4*(loop_count-2)+4)+2 = 4*(loop_count-2)+6`;
                      ARITH_RULE `(4*(loop_count-2)+5)+2 = 4*(loop_count-2)+7`;
                      ARITH_RULE `(4*(loop_count-2)+6)+2 = 4*(loop_count-2)+8`;
                      ARITH_RULE `(4*(loop_count-2)+7)+2 = 4*(loop_count-2)+9`] THEN
          REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
          REWRITE_TAC[aes_ctr_block] THEN
          REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          ASM_REWRITE_TAC[] in
        let ADDRNORM = REWRITE_TAC[ARITH_RULE `64*(loop_count-2)+80 = (64*(loop_count-2)+64)+16`;
                             ARITH_RULE `64*(loop_count-2)+96 = (64*(loop_count-2)+64)+32`;
                             ARITH_RULE `64*(loop_count-2)+112 = (64*(loop_count-2)+64)+48`] in
        FIRST[ (ASM_REWRITE_TAC[] THEN NO_TAC);
               (RECON THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3 THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC) THEN NO_TAC) ]) (asl,w)
     else if (try fst(dest_const(fst(strip_comb(lhs w))))="word_zx" with _->false) then
       (* X13 scalar counter word_zx(word_add(word_zx(word_zx(word K)))(word 4)) = word_zx(word(4*lc+2)). *)
       (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) (asl,w)
     else
       (FIRST[ (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
               (AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC);
               (CONV_TAC WORD_RULE THEN NO_TAC);
               (CLOSE_V8 THEN NO_TAC) ]) (asl,w));;

let SWP_DEC_DRAINLEG = prove(drain_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`]) THEN
  (* prime the drained group's 4 input-block reads to `inblock` form (the SWP ldrs otherwise reach the
     settled-Q30 closer as raw byte-reassembly towers and the branch1 BITBLAST blows up). *)
  SUBGOAL_THEN `4*(loop_count-2)+7 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `3 <= loop_count` THEN
    SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+64)))) s0 = inblock (4*(loop_count-2)+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+80)))) s0 = inblock (4*(loop_count-2)+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+96)))) s0 = inblock (4*(loop_count-2)+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+112)))) s0 = inblock (4*(loop_count-2)+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+64)):int64 = word_add in_p (word (16*(4*(loop_count-2)+4)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+80)):int64 = word_add in_p (word (16*(4*(loop_count-2)+5)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+96)):int64 = word_add in_p (word (16*(4*(loop_count-2)+6)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+112)):int64 = word_add in_p (word (16*(4*(loop_count-2)+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  drain_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `64 * (loop_count - 2) + 128 = 64 * loop_count /\
                (64 * (loop_count - 2) + 64) + 64 = 64 * loop_count`
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`3 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* split the out-store forall (post j < 4*loop_count) into the invariant's preserved prefix
     j < 4*(loop_count-2) + the 8 drained blocks as explicit unwound equations. *)
  SUBGOAL_THEN `!j:num. j < 4 * loop_count <=>
      j < 4*(loop_count-2) \/ j = 4*(loop_count-2) \/ j = 4*(loop_count-2)+1 \/ j = 4*(loop_count-2)+2 \/
      j = 4*(loop_count-2)+3 \/ j = 4*(loop_count-2)+4 \/ j = 4*(loop_count-2)+5 \/ j = 4*(loop_count-2)+6 \/
      j = 4*(loop_count-2)+7`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`; ARITH_RULE `16 * 4 * a = 64 * a`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DRAIN_CLOSE);;

(* ============================ iter_1 (loop_count=1) leg ============================ *)
let sp_off_str c =
  try let l = lhs c in
    let off = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),_))
           when (try fst(dest_var sp)="stackpointer" with _->false) -> true | _ -> false) l in
    (match off with Comb(Comb(_,_),Comb(_,noff)) -> string_of_term noff | _ -> "")
  with _ -> "";;
let read_state_idx c =
  try let rdx,st = dest_comb (lhs c) in
    (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
       (try int_of_string (String.sub nm 1 (String.length nm-1)) with _-> -1) | _ -> -1)
  with _ -> -1;;
let forall_state_idx c =
  try (match state_of_forall c with
       | Some nm -> if String.length nm>=2 && nm.[0]='s' then (try int_of_string (String.sub nm 1 (String.length nm-1)) with _-> -1) else -1
       | None -> -1)
  with _ -> -1;;
let mxreg_of cs keeplist r = itlist (fun c m -> match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m) cs (-1);;
let sp_match c ofs = if sp_off_str c = ofs then read_state_idx c else (-1);;
let mxsp_of cs ofs = itlist (fun c m -> max (sp_match c ofs) m) cs (-1);;
let max_forall_idx cs = itlist (fun c m -> if is_forall c then max (forall_state_idx c) m else m) cs (-1);;
let anchored_read c =
  try fst(dest_const(fst(strip_comb(lhs c))))="read" &&
    (free_in `tag_p:int64` (lhs c) || free_in `ivec_p:int64` (lhs c) || free_in `htable_p:int64` (lhs c) ||
     free_in `out_p:int64` (lhs c) || free_in `in_p:int64` (lhs c))
  with _ -> false;;
let is_old_state_read c sname =
  try let rdx,st = dest_comb (lhs c) in
    (match st with Var(nm,_) -> nm<>sname && String.length nm>=1 && nm.[0]='s' | _ -> false)
  with _ -> false;;
let is_maychange_notlast c sname =
  (try can (find_term (fun x -> match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false) &&
  (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false);;
let gkeep3_discard keeplist sname cs mx mxsp mxfa c =
  if is_maychange_notlast c sname then true
  else if is_neg c then true
  else if is_forall c then forall_state_idx c < mxfa
  else
    let spo = sp_off_str c in
    if not (spo = "") then read_state_idx c < List.assoc spo mxsp
    else if anchored_read c then false
    else (match gc2 keeplist c with Some(r,k) -> k < List.assoc r mx | None -> is_old_state_read c sname);;
let gkeep3 keeplist th sname =
  ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) ->
     let cs = map (fun p -> concl (snd p)) asl in
     let mx = map (fun r -> (r, mxreg_of cs keeplist r)) keeplist in
     let spoffs = setify (filter (fun s -> not (s = "")) (map sp_off_str cs)) in
     let mxsp = map (fun ofs -> (ofs, mxsp_of cs ofs)) spoffs in
     let mxfa = max_forall_idx cs in
     DISCARD_ASSUMPTIONS_TAC (fun th -> gkeep3_discard keeplist sname cs mx mxsp mxfa (concl th)) (asl,w));;

(* ---- iter_1 goal: 0xa0 precond -> 0xaa0 WEAKENED postcond (X1 dropped), loop_count = 1 ---- *)
let abl_s = `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc`;;
let iter1_pre_body = `read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\ read X4 s = ivec_p /\
    read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word 2:int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X1 s = word loop_count /\ read X7 s = word nblocks /\
    read X16 s = word loop_remain /\ read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i)`;;
let iter1_post_body = `read X0 s = word_add in_p (word (64 * loop_count)) /\
    read X2 s = word_add out_p (word (64 * loop_count)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * loop_count))) /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s = word_xor (aes_ctr_block nonce rk j) (inblock j))`;;
let iter1_pre  = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xa0)`, iter1_pre_body)));;
let iter1_post = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xaa0)`, iter1_post_body)));;
(* main-theorem frame C_main *)
let iter1_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30] ,,
    MAYCHANGE [Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks); memory :> bytes(tag_p,16);
               memory :> bytes(ivec_p,16); memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let iter1_ens = list_mk_comb(`ensures arm`,[iter1_pre;iter1_post;iter1_frame]);;
(* hyps = bodyleg base with loop_count = 1 instead of the loop-index constraint *)
let iter1_hyps = mk_conj(subst [`loop_count = 1`, `i < loop_count - 2`] bodyleg_hyps, `T`) ;;
(* bodyleg_hyps already includes `3 <= loop_count`; for loop_count=1 that is FALSE, so instead build hyps
   fresh from the base (drop 3<=loop_count and i<loop_count-2, add loop_count=1). *)
let base_hyps = filter (fun t -> not (t = `i < loop_count - 2`) && not (t = `3 <= loop_count`)) (conjuncts bodyleg_hyps);;
let iter1_hyps = list_mk_conj (base_hyps @ [`loop_count = 1`]);;
let vs_i1 = filter (fun v -> v <> `i:num`) vs;;
let iter1_goal = list_mk_forall(vs_i1, mk_imp(iter1_hyps, iter1_ens));;

(* ---- iter_1 stepper: 3 control-flow steps then 158 body steps.  Merges (stp x11,_/ldr q,[sp,#OFF]) at
   ABS step indices 16(208), 23(176), 27(160), 32(192) (body-relative 13/20/24/29 + 3 control prefix). ---- *)
let iter1_merges = [(16,208);(23,176);(27,160);(32,192)];;
let iter1_step_tac =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        gkeep3 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k iter1_merges then MERGE_CTR128_TAC (List.assoc k iter1_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--161)) (asl,w));;

(* ---- single-group settled-Q30 closer: acc = tag0 = nist_ghash..(0), blocks 0..3, reduces to
   nist_ghash..(4).  (This is the clean-body i=0 closer / DRAIN GHASH_SETTLE with k=0, literal indices.) ---- *)
let ITER1_Q30_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  (* with s0 input-priming the blocks are already `inblock j` (no raw byte towers) -> INFOLD3/INBLOCK_REASSEMBLE
     may find nothing; guard with TRY. *)
  TRY INFOLD3 THEN TRY(REWRITE_TAC[INBLOCK_REASSEMBLE]) THEN TRY(REWRITE_TAC[GSYM nist_input_block]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
     [ `sofar:int128 = tag0`;
       `cipherblock_0:int128 = nist_input_block inblock 0`;
       `cipherblock_1:int128 = nist_input_block inblock 1`;
       `cipherblock_2:int128 = nist_input_block inblock 2`;
       `cipherblock_3:int128 = nist_input_block inblock 3`;
       `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY INFOLD3 THEN TRY(REWRITE_TAC[INBLOCK_REASSEMBLE]) THEN TRY(REWRITE_TAC[GSYM nist_input_block]) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    (CONV_TAC BITBLAST_RULE ORELSE BITBLAST_TAC) ;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    (* SWP_GHASH_BRANCH2_SETTLED @ k=0 has `nist_ghash..(4*0)` in the acc slot; the goal's acc is `tag0`.
       Pre-prove nist_ghash..0 = tag0, fold it into the (NUM_REDUCE'd) lemma, then rewrite the goal. *)
    MP_TAC(REWRITE_RULE
            [prove(`nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) 0) = tag0`,
                   REWRITE_TAC[list_of_seq; nist_ghash])]
            (CONV_RULE NUM_REDUCE_CONV (ISPEC `0` SWP_GHASH_BRANCH2_SETTLED))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])];;

(* ---- out-store readback closer (RECON): blocks 0,1,2,3; counter base X13=word 2, so ctr = 2,3,4,5.
   Reuse DRAIN's RECON structure but with literal block/counter indices. ---- *)
let iter1_stuck = ref 0;;
let rhs_has c w = try (is_eq w) && can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) (rhs w) with _->false;;
let ITER1_CLOSE : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST OUT0_TAC; ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (* Q30 conjunct `read Q30 s = byteswap128(nist_ghash..4)`.  Substitute ONLY the Q30 s161 read fact
          (targeted, not full ASM_REWRITE over the polluted asl), THEN discard ALL read facts (ITER1_Q30_TAC
          uses only the rk-list eq + arithmetic), THEN run the GHASH closer on the lean context. *)
       (FIRST_X_ASSUM(fun th -> try
           (match lhs(concl th) with
            | Comb(Comb(Const("read",_),Const("Q30",_)),_) -> SUBST1_TAC th
            | _ -> failwith "") with _ -> NO_TAC) THEN
        DISCARD_ASSUMPTIONS_TAC
          (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "read" with _ -> false) THEN
        ITER1_Q30_TAC THEN NO_TAC) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* out-store readback for block j: after substituting the store value (ADDRNORM+ASM_REWRITE), the LHS is
          `word_xor (inblock j) (word_xor rk10 (aese-tower(CTRBLK, wrf(EL k rk))))` and RHS
          `word_xor (aes_ctr_block nonce rk j) (inblock j)`.  Fold via XOR_AES128_CIPHER_RECONSTRUCT_DEC
          (tower -> wrf(aes128_cipher (wrf CTRBLK)(MAP wrf rk))) + rk-list, unfold aes_ctr_block on RHS, then
          peel wrf/aes128_cipher/rk to `wrf CTRBLK = ctr_block nonce (j+2)` and WORD_BLAST it (iter_1 counters
          are LITERAL lanes -- CTR_BLOCK_BUILD_INSERT does NOT match, ctr_block+WORD_BLAST does). *)
       (let ADDRNORM = GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] in
        let FOLD =
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[MAP] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[aes_ctr_block] in
        (* after FOLD both sides are `wrf(aes128_cipher CTR rk)`; peel wrf/aes128_cipher/rk to `CTR_lhs = CTR_rhs`,
           reduce the RHS counter index (j+2), then close.  Block 0 (base ctr 2): CTR_lhs = wrf(wrf(ctr_block nonce 2))
           -> WORD_REVERSEFIELDS_REVERSEFIELDS + REFL.  Blocks 1-3 (literal lanes): ctr_block + NUM_REDUCE + WORD_BLAST. *)
        (* BOUNDED peel (do NOT use REPEAT -- it over-peels into CTR's structure and WORD_BLAST blows up):
           word_xor A (inblock j) = word_xor A' (inblock j)  --AP_THM;AP_TERM-->  A = A'
           A = wrf(aes128_cipher CTR rk)                       --AP_TERM-->        aes128_cipher CTR rk = ..
           aes128_cipher CTR rk = aes128_cipher CTR' rk        --AP_THM;AP_TERM--> CTR = CTR'
           Then block0's CTR = wrf(wrf ctr_block) -> WORD_REVERSEFIELDS_REVERSEFIELDS + REFL;
                blocks1-3 CTR = word_join(literal lane) -> ctr_block + NUM_REDUCE + WORD_BLAST. *)
        (* PEEL to CTR_lhs = CTR_rhs (bounded), then close: block-0 (base ctr 2, wrf(wrf ctr_block)) via
           WORD_REVERSEFIELDS_REVERSEFIELDS+REFL; blocks 1-3 (literal lanes) via ctr_block+NUM_REDUCE+WORD_BLAST. *)
        let PEEL_CTR =
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          (REFL_TAC ORELSE
           (REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST)) in
        FIRST[ (ADDRNORM THEN ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes2c] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN NO_TAC) ]) (asl,w)
     else if (try can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_zx" with _->false)) w with _->false) then
       (* X13 scalar counter word_zx goals, incl `word 6 = word_zx(word(4+2))`: reduce the numeral
          arithmetic then collapse word_zx(word n) via BITBLAST. *)
       (FIRST[ (CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC);
               (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                REWRITE_TAC[GSYM WORD_ADD] THEN TRY AP_TERM_TAC THEN TRY AP_TERM_TAC THEN
                CONV_TAC NUM_REDUCE_CONV THEN TRY REFL_TAC THEN NO_TAC) ]) (asl,w)
     else
       (* register-value conjuncts (mostly `read Qn s = wrf(EL k rk)` etc.): ASM_REWRITE+REFL closes them from
          the (pruned) s161 read facts; the two X0/X2 pointer conjuncts need a bounded WORD_RULE (64*1=64). *)
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN CONV_TAC WORD_RULE THEN NO_TAC) ]) (asl,w));;

let MAYCHANGE_ABI_CLOSE =
  FIRST_X_ASSUM(fun th -> if maychange_term(concl th) then
     MATCH_MP_TAC(MATCH_MP (MESON[subsumed] `R s s' ==> R subsumed R' ==> R' s s'`) th) else NO_TAC) THEN
   REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;;

(* Per-conjunct closer: frame goals via MAYCHANGE_ABI_CLOSE, everything else via ITER1_CLOSE
   (Q30 GHASH / out-store RECON / word_zx / register-value dispatch).  Axiom-free (no CHEAT). *)
let ITER1_CLOSE_ALL : tactic =
  fun (asl,w) -> (if maychange_term w then MAYCHANGE_ABI_CLOSE else ITER1_CLOSE) (asl,w);;

let SWP_DEC_ITER1 = prove(iter1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `loop_count:num` with _->false))) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* PRIME the group's 4 input-block reads to `inblock` form (mirror DRAIN): without this the SWP ldrs
     reach the Q30 GHASH closer + out-store readbacks as RAW byte-reassembly towers and BITBLAST blows up. *)
  SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `nblocks DIV 4 = 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  iter1_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* PRUNE asl before the closers: the 161 keep-steps leave transient huge-RHS register reads
     (`read Qn sK = <GHASH-partial tower>`) that make every closer ASM_REWRITE/WORD_RULE storm
     (O(asl*termsize)).  Discard reads whose RHS term is large (>800 chars); the postcondition's
     final Q-reads have small RHS (wrf(EL k rk) etc.) and survive, as do the out_p/in_p/mem store
     facts the RECON needs (those are `read(memory:>..)` -- kept: only REGISTER reads pruned). *)
  (let rec tsize n t = if n > 60 then n else
     match t with Comb(a,b) -> tsize (tsize (n+1) a) b | Abs(_,b) -> tsize (n+1) b | _ -> n+1 in
   DISCARD_ASSUMPTIONS_TAC
    (fun th -> try let c = concl th in is_eq c &&
       (match lhs c with Comb(Comb(Const("read",_),comp),st) ->
          (match comp with Comb(Const(":>",_),_) -> false   (* memory reads (out_p/in_p/tag/ivec/mem): keep *)
                         | _ ->
             (* register read: drop only TRANSIENT ones (state != s161) with a big RHS; keep final s161
                reads (postcondition register values).  Use a cheap bounded node-count (string_of_term on
                the 4000-node GHASH towers x60 facts would itself storm). *)
             tsize 0 (rhs c) > 60 &&
             (match st with Var(nm,_) -> nm <> "s161" | _ -> true))
        | _ -> false)
     with _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ITER1_CLOSE_ALL);;


(* ============================ loop_count=2 Part A (0xa0 -> 0x514) ============================ *)
let fill_pre_body = `read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\ read X4 s = ivec_p /\
    read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word 2:int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X1 s = word loop_count /\
    read X7 s = word nblocks /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j)`;;

let abl_s = `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc`;;
let fill_pre  = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xa0)`, fill_pre_body)));;
let fill_post = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0x514)`, ap swpS_inv8_dec_v8 `0` `s:armstate`)));;
let fill_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X0;X1;X2;X7;X10;X11;X12;X13;X14;X17;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30] ,,
    MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8;Q9;Q10;Q11;Q29;Q30;Q31] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
               memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let fill_ens = list_mk_comb(`ensures arm`,[fill_pre;fill_post;fill_frame]);;
(* Part A (loop_count=2): base hyps (drop i-constraint AND 3<=loop_count) + loop_count=2. *)
let fill_hyps = list_mk_conj
  ((filter (fun t -> not (t = `i < loop_count - 2`) && not (t = `3 <= loop_count`)) (conjuncts bodyleg_hyps))
   @ [`loop_count = 2`]);;
let vs_fill = filter (fun v -> v <> `i:num`) vs;;
let fill_goal = list_mk_forall(vs_fill, mk_imp(fill_hyps, fill_ens));;

(* ---- branch-resolution lemmas for the two guards at 0xa4/0xa8 (b.eq iter_1) and 0x290 (cbz drain) ---- *)
let branch_lem = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);;
let branch_lem2 = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 2)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word 2:int64) = 2` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);;
(* loop_count=2 guards: b.eq@0xa8 NOT taken (x1=2!=1) and cbz@0x290 TAKEN (x1 = 2-2 = 0 -> 0x514) *)
let lc2_guard1 = prove(
  `loop_count = 2 ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `word_sub (word 2:int64) (word 1) = word 1` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN ARITH_TAC);;
let lc2_guard2 = prove(
  `loop_count = 2 ==> (val(word_sub (word loop_count:int64) (word 2)) = 0 <=> T)`,
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `word_sub (word 2:int64) (word 2) = word 0` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* bridge: the machine rev64.16b(block) = byteswap128(word_reversefields 8 block); needed to close the
   i=0 GHASH seed (Q11) whose FILL machine value is rev64.16b(inblock 0) but the invariant writes it as
   byteswap128(word_reversefields 8 (inblock 0)). *)
let REV64_16B_IS_BSW_REVFIELDS = prove(
  `word_join (word_bytereverse (word_subword (x:int128) (64,64):int64):int64)
             (word_bytereverse (word_subword (x:int128) (0,64):int64):int64):int128
   = byteswap128 (word_reversefields 8 x)`,
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[GSYM WORD_EQ_BITS_ALT] THEN REWRITE_TAC[byteswap128] THEN
  CONV_TAC(BINOP_CONV(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  CONV_TAC BITBLAST_RULE);;

(* FILL per-conjunct closer.  Applied AFTER the goal-level arith-normalization pass, so conjuncts
   are in `inblock k` / literal-offset form (same shape CLOSE_V8 expects from BODYLEG).  The Q11 seed
   at i=0 additionally needs nist_ghash..0 -> tag0 (empty Horner); handle it explicitly first. *)
(* FILL out-store closer for the two stored-ahead blocks (2,3) at literal offsets 32/48
   (X2 = out_p, not advanced during the fill).  Mirrors OUTBLK_TAC's reconstruction body but
   with NO address-normalisation (offsets are already literal). *)
let FILL_OUTBLK_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN REWRITE_TAC[aes_ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;

(* ks9 counter-base lemma: the inline staged-counter for block 3 (i=0) = revfields8(ctr_block nonce 3).
   Lets the machine Q5 keystream (base = read(sp+176) = revfields8(ctr_block nonce 3) via the invariant's
   own sp+176 conjunct) match the invariant ks9's inline-counter base inside the 9-round AES tower. *)
let KS9_CTRBASE_0 = prove(
  `word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word 3:int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
   = word_reversefields 8 (ctr_block nonce 3)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* i=0 counter-base folds: the FILL staged counter-lane joins = word_reversefields 8 (ctr_block nonce K),
   for K in {2,3,4,5,6}.  Proven uniformly by REWRITE[ctr_block] + WORD_BLAST (like KS9_CTRBASE_0). *)
let CTR_LANE_FOLD_0 = prove(
  `(word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+3):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+3))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+4):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+4))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+5):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+5))) /\
   (word_join
     (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
              (word_shl (word_zx (word_bytereverse (word (4*0+6):int32):int32):int64) 32:int64):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128
    = word_reversefields 8 (ctr_block nonce (4*0+6)))`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* counter-base folds with the REDUCED shl-numeral (the stepping reduces word_shl(word_bytereverse(word k))32
   to a numeral): the FILL staged counter-lane join = word_reversefields 8 (ctr_block nonce K) for K=2..6. *)
let CTRBASEN =
  let mk_ctrbase k num =
    mk_eq(subst [mk_numeral(Num.num_of_int num),`NUM:num`]
      `word_join
        (word_or (word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64)
                 (word NUM:int64):int64)
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64):int128`,
      subst [mk_small_numeral k,`K:num`] `word_reversefields 8 (ctr_block nonce K)`) in
  prove(list_mk_conj [mk_ctrbase 2 144115188075855872; mk_ctrbase 3 216172782113783808;
                      mk_ctrbase 4 288230376151711744; mk_ctrbase 5 360287970189639680;
                      mk_ctrbase 6 432345564227567616],
        REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* extended-anchor keep-stepper: also anchor sp-slot HIGH-half offsets 168/184/200/216 so both stp halves
   survive to enable bytes128 counter reconstruction at any state. *)
let is_spctr_read2 c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in
              v="160"||v="176"||v="192"||v="208"||v="168"||v="184"||v="200"||v="216") | _ -> false)) l)
  with _ -> false;;
let gkeep2 keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    let anchored c = try (is_spctr_read2 c) ||
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) || (free_in `htable_p:int64` (lhs c))))
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;

(* FILL per-conjunct closer.  8 shape-specific branches (all validated interactively, 24/24). *)
let FILL_CLOSE : tactic =
  FIRST
   [ (* GHASH (seed Q11 + partials): reassembly + ghash-nil + UNFOLD byteswap128 + bridge + WORD_BLAST *)
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REV64_16B_IS_BSW_REVFIELDS; byteswap128] THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (* counter stack slots (bytes128, merged at s125): ASM then fold counter numerals to ctr_block *)
     (ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC);
     (* Q30/ks9 aes towers: MERGE the base at its load state, fold counter numeral, aes defs, REFL/BLAST *)
     ((MERGE_CTR128_TAC 160 "s77" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 176 "s29" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[aes2c] THEN (REFL_TAC ORELSE (REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)) THEN NO_TAC);
     (* out-stores blk2,3: MERGE base, fold counter, DEC readback recon, fold key-list=rk, aes_ctr_block, REFL *)
     ((MERGE_CTR128_TAC 192 "s32" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 208 "s18" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CTRBASEN] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN TRY REFL_TAC THEN NO_TAC);
     (* word_sub loop-count *)
     (SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[WORD_SUB]] THEN NO_TAC);
     (* MAYCHANGE frame *)
     (close_goal10 THEN NO_TAC);
     (* trivial registers / htable (post htable-unfold, the 4 reads close by ASM) *)
     (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
     (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE THEN NO_TAC) ];;

(* ---- Part-A stepper: gkeep3 (lean asl) + FILL merge sites.  loop_count:=2 is substituted before
   stepping, so the guards (cbz@0xa0 X1=2, b.eq@0xa8 X1=2, cbz@0x290 X1=0->TAKEN to 0x514) resolve by
   concrete arith (COND_CLAUSES after WORD_SIMPLE_SUBWORD); no branch_lem needed. ---- *)
let fill_merges = [(10,160);(12,176);(15,208);(21,192)];;
(* IDENTICAL to the proven FILL leg's stepper: gkeep2 for ALL steps 1--125 uniformly.  The earlier
   split (plain 1-3 / gkeep2 4-124 / plain [125]) was a gkeep3-era leftover -- the plain [125] step
   failed to frame the late-written pipeline carriers Q5 (@s109) and Q30 (@s117) forward to s125, so
   ENSURES_FINAL_STATE_TAC dropped them and FILL_CLOSE's aes2c/ks9/out-store branches had nothing to
   rewrite with.  loop_count is kept SYMBOLIC (with hyp loop_count=2); the RULE_ASSUM rewrite set uses
   only the guard facts true under loop_count=2 (drop the FILL-only `loop_count=2<=>F`).  The cbz@0x290
   at step 125 leaves PC symbolic (guard on word_sub .. word 2); resolved TAKEN->0x514 after stepping. *)
let fill_step_tac =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        gkeep2 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 0 <=> F`; ASSUME `loop_count = 1 <=> F`;
           ASSUME `val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F`; COND_CLAUSES]) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k fill_merges then MERGE_CTR128_TAC (List.assoc k fill_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--125)) (asl,w));;

(* Diagnostic per-conjunct closer: try FILL_CLOSE; if it fails, PRINT the conjunct goal and leave it. *)
let SWP_DEC_LC2_PARTA = prove(fill_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  (* keep loop_count SYMBOLIC (hyp loop_count = 2); derive the guard facts the stepper needs. *)
  SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `loop_count:num` THEN
  SUBGOAL_THEN `(loop_count = 0 <=> F) /\ (loop_count = 1 <=> F)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC; ALL_TAC] THEN
  (* b.eq@0xa8 guard (val(word_sub .. word 1)=0 <=> F): NOT taken since loop_count=2 *)
  MP_TAC(SPEC_ALL lc2_guard1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (* prime the fill's group-0 loads (blocks 0..3; block 0 = bare in_p per the ldr [x0] form) *)
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  fill_step_tac THEN
  (* resolve the final cbz @ 0x290 (word_sub .. word 2): TAKEN (loop_count=2) -> 0x514 *)
  MP_TAC(SPEC_ALL lc2_guard2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count:int64) (word 2)) = 0 <=> T`; COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MERGE_CTR128_TAC 160 "s125" THEN MERGE_CTR128_TAC 176 "s125" THEN
  MERGE_CTR128_TAC 192 "s125" THEN MERGE_CTR128_TAC 208 "s125" THEN
  ASM_REWRITE_TAC[] THEN
  (* goal-level i=0 arithmetic normalization (loop_count SYMBOLIC, same as proven FILL leg) *)
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`;
    ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 + 3 = 3`;
    ARITH_RULE `4 * 0 + 4 = 4`; ARITH_RULE `4 * 0 + 5 = 5`; ARITH_RULE `4 * 0 + 6 = 6`;
    ARITH_RULE `4 * 0 + 7 = 7`; ARITH_RULE `4 * 0 + 9 = 9`;
    ARITH_RULE `0 + 7 = 7`; ARITH_RULE `0 + 3 = 3`;
    ARITH_RULE `64 * 0 + 32 = 32`; ARITH_RULE `64 * 0 + 48 = 48`;
    ARITH_RULE `64 * 0 + 64 = 64`; ARITH_RULE `loop_count - 2 - 0 = loop_count - 2`] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FILL_CLOSE);;

(* ============================ loop_count=2 Part B (0x514 -> 0xaa0) ============================ *)
let REV64_16B_IS_BSW_REVFIELDS = prove(
  `word_join (word_bytereverse (word_subword (x:int128) (64,64):int64):int64)
             (word_bytereverse (word_subword (x:int128) (0,64):int64):int64):int128
   = byteswap128 (word_reversefields 8 x)`,
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[GSYM WORD_EQ_BITS_ALT] THEN REWRITE_TAC[byteswap128] THEN
  CONV_TAC(BINOP_CONV(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN CONV_TAC BITBLAST_RULE);;

(* ---- extended-anchor keep-stepper (anchor sp-slot HIGH halves 168/184/200/216 too) ---- *)
let is_spctr_read2 c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (let v=string_of_term n in
              v="160"||v="176"||v="192"||v="208"||v="168"||v="184"||v="200"||v="216") | _ -> false)) l)
  with _ -> false;;
let gkeep2 keeplist th sname = ARM_STEP_TAC th [] sname None (K STRIP_TAC) THEN
  (fun (asl,w) -> let cs=map(fun(_,t)->concl t)asl in
    let mx=map(fun r->(r,itlist(fun c m->match gc2 keeplist c with Some(rr,k)when rr=r&&k>m->k|_->m)cs(-1)))keeplist in
    let anchored c = try (is_spctr_read2 c) ||
        (fst(dest_const(fst(strip_comb(lhs c))))="read" &&
         ((free_in `tag_p:int64` (lhs c)) || (free_in `ivec_p:int64` (lhs c)) || (free_in `htable_p:int64` (lhs c)) ||
          (* anchor out_p STORE facts: the drain flushes 8 output blocks over 198 steps; without anchoring,
             gkeep2 GCs the early-stored blocks (+5/+6/+7) before s198 and their out-store readback goals
             dump (head=read, no store fact to fold).  Keeping them (8 facts) lets the close-time recon fire. *)
          (free_in `out_p:int64` (lhs c)) ||
          (* anchor in_p point READ facts (the primed `read(in_p+..)=inblock`).  The SWP schedule loads the
             last group's blocks EARLY (s61/s100/s135); without anchoring, gkeep2 GCs the s0-primed facts
             before those ldr's fire, so the loads produce RAW byte towers that freeze into Q30's value
             (subgoal-B BITBLAST FALSE) and the out-store readbacks.  Keeping the primed facts lets each ldr
             fold to `inblock`.  Excludes the quantified forall (already kept by the is_forall clause). *)
          (free_in `in_p:int64` (lhs c))))
      with _ -> false in
    DISCARD_ASSUMPTIONS_TAC(fun th->let c=concl th in
      if (try can (find_term (fun x -> match x with Const("MAYCHANGE",_) -> true | _ -> false)) c with _->false)
      then (try let _,args = strip_comb c in string_of_term(last args) <> sname with _ -> false) else
      if is_forall c then
        (if free_in `in_p:int64` c || free_in `out_p:int64` c then false
         else (match state_of_forall c with Some nm -> nm <> sname | None -> false)) else
      if anchored c then false else
      match gc2 keeplist c with Some(r,k)->k<List.assoc r mx
      |None->(try let l=lhs c in let rd,st=dest_comb l in (match st with Var(nm,_)->nm<>sname&&String.length nm>=1&&nm.[0]='s'|_->false)with _->false))(asl,w));;

(* ---- DRAIN goal: inv(loop_count-2) @ pc+0x510 -> 0xaa0 postcond ---- *)
let abl_s = `aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc`;;
let drain_post_body = `read X0 s = word_add in_p (word (64 * loop_count)) /\
   read X2 s = word_add out_p (word (64 * loop_count)) /\
   read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
   read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
   read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
   read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
   read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
   read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
   read Q28 s = word_reversefields 8 (EL 10 rk) /\
   read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
   read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
   read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
   read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
   read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
   read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
   read Q7 s = word 13979173243358019584 /\
   read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
   read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
   read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
   read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\ read X16 s = word loop_remain /\
   read Q30 s = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * loop_count))) /\
   htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
   (!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s = word_xor (aes_ctr_block nonce rk j) (inblock j))`;;
let drain_pre = mk_abs(`s:armstate`, mk_conj(abl_s,
   mk_conj(`read PC s = word (pc + 0x514)`, ap swpS_inv8_dec_v8 `loop_count - 2` `s:armstate`)));;
let drain_post = mk_abs(`s:armstate`, mk_conj(abl_s, mk_conj(`read PC s = word (pc + 0xaa0)`, drain_post_body)));;
let drain_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X0;X1;X2;X7;X10;X11;X12;X13;X14;X17;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30] ,,
    MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8;Q9;Q10;Q11;Q29;Q30;Q31] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks); memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let drain_ens = list_mk_comb(`ensures arm`,[drain_pre;drain_post;drain_frame]);;
let drain_hyps = subst [`2 <= loop_count`, `i < loop_count - 2`] bodyleg_hyps;;
let vs_drain = filter (fun v -> v <> `i:num`) vs;;
let drain_goal = list_mk_forall(vs_drain, mk_imp(drain_hyps, drain_ens));;

(* ---- DRAIN stepper: gkeep2 + drain merge sites (step 1 = 0x510). cbz@0x510 (X1=word 0) auto-resolves. ---- *)
(* MERGE_CTR128_TAC OFF sK must fire at the LDR state sK (after BOTH 64-bit stps to sp+OFF executed) so the
   128-bit `ldr qM,[sp,#OFF]` resolves against the stores.  Drain counter sites (step = (addr-0x510)/4+1):
     stp[sp,176]@0x524=step6  stp[sp,208]@0x544=step14  ldr q31,[sp,208]@0x558=step19
     stp[sp,192]@0x570=step25  ldr q5,[sp,176]@0x5bc=step44  ldr q4,[sp,192]@0x5d4=step50
     ldr q30,[sp,160]@0x6b8=step107 (the settled-Q30 acc reload).
   The counter value in an out-store readback tower is `read(sp+OFF)s_{K-1}` (ARM_STEP records the ldr's
   loaded value as the PRE-ldr memory), so MERGE must fire at the state the TOWER references -- captured from
   the OUTSTORE STUCK dumps: block+5 uses read(sp+176)s43, block+6 read(sp+192)s49, block+7 read(sp+208)s18.
   Merge at exactly those states (all after their stps: sp176@s6, sp208@s14, sp192@s25) so the tower's
   counter read resolves.  (sp+160 = GHASH-acc reload, handled by DRAIN_Q30_TAC/inter, excluded.) *)
(* Re-indexed -1 vs DRAIN (Part B enters at 0x514 = DRAIN's post-step-1 state, so DRAIN's step k is
   Part B's step k-1): merges 18/43/49 -> 17/42/48; the settled-Q30 `inter` abbrev at DRAIN's s98 -> s97. *)
let drain_merges = [(17,208);(42,176);(48,192)];;
let drain_step_tac =
  (fun (asl,w) -> (MAP_EVERY (fun k ->
        gkeep2 REDSETX_DEC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if k = 97 then REABBREV_TAC (mk_eq(`inter:int128`, `read Q30 s97`)) else ALL_TAC) THEN
        (if List.mem_assoc k drain_merges then MERGE_CTR128_TAC (List.assoc k drain_merges) ("s"^string_of_int k)
         else ALL_TAC)) (1--197)) (asl,w));;

(* ---- DRAIN closer: DIAGNOSTIC (dump unclosed conjuncts) for the first run; swap to plain FIRST[...] after.
   Closers reuse FILL's set + BODYLEG's SWP_GHASH_CORE_TAC for the SETTLED final Q30 reduce. ---- *)
(* SHAPE-GATED closer: only run the expensive SWP_GHASH_CORE_TAC / GHASH-BITBLAST on conjuncts whose RHS
   actually mentions nist_ghash (the settled Q30 / GHASH-reduce); cheap tactics for everything else. This
   avoids trying the ~117s BITBLAST on all 24 conjuncts. *)
let rhs_has c w = try (is_eq w) && can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) (rhs w) with _->false;;

(* ---- Parameterized single-group settled-Q30 closer (SWP_GHASH_CORE_TAC generalized to a drain index
   term `mtm` and starting accumulator `sofartm`).  Closes
     <machine 4-block reduce tower over sofartm, blocks mtm..mtm+3> = byteswap128(nist_ghash h sofartm [4 blocks])
   via byteswap-split + ABBREV(sofar,cipherblock_k,hk) + RECONSTRUCT_POLYVAL_REDUCE_G2 + branch1(BITBLAST)
   + SWP_GHASH_BRANCH2_GEN.  The RHS must already be byteswap128(nist_ghash h sofartm [the 4 explicit blocks]). *)
(* ktm = the group index k such that the accumulator is the SETTLED nist_ghash..(list_of_seq..(4*k))
   and the 4 blocks are 4*k..4*k+3, reducing to nist_ghash..(list_of_seq..(4*k+4)).  mtm=4*ktm,
   sofartm=nist_ghash..(4*ktm) are derived from ktm so branch2 can use SWP_GHASH_BRANCH2_SETTLED. *)
(* ktm: the SETTLED group index (acc = nist_ghash..(4*ktm), branch2 uses SWP_GHASH_BRANCH2_SETTLED ktm).
   The ACTUAL block indices in the machine goal are `4*(loop_count-2) + (off+j)` (j=0..3), where off=0 for
   subgoal B (blocks +0..+3) and off=4 for subgoal A (last group, blocks +4..+7).  4*(loop_count-2)+off = 4*ktm
   (B: off=0,ktm=loop_count-2; A: off=4,ktm=loop_count-1) -- equal but written differently, so the cipherblock
   ABBREVs use the goal's literal `4*(loop_count-2)+(off+j)` form (else they miss -> word_pmul survives ->
   BITBLAST blows up).  A pre-branch2 arith bridge reconciles the base to 4*ktm for SWP_GHASH_BRANCH2_SETTLED. *)
let GHASH_SETTLE_TAC (ktm:term) (off:int) : tactic =
  let mtm = mk_binop `( * ):num->num->num` `4` ktm in
  let basetm = `4 * (loop_count - 2)` in
  let sofartm = subst [ktm, `k:num`]
     `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*k))` in
  (* block index for lane j = basetm + (off+j), with (off+j) a literal numeral so it matches the goal.
     When off+j=0 the goal writes just `basetm` (no `+0`), so emit basetm bare in that case. *)
  let blkidx j = if off+j = 0 then basetm
                 else mk_binop `(+):num->num->num` basetm (mk_small_numeral (off+j)) in
  ALL_TAC THEN
  DEC_GHASH_NORM_TAC THEN
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  (* Fold raw mid-state block reads to nist_input_block (see below); then ABBREV using the GOAL's literal
     base index (basetm+j), so all 4 cipherblocks are captured -> no surviving word_pmul into branch1. *)
  INFOLD3 THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
     [ mk_eq(`sofar:int128`, sofartm);
       mk_eq(`cipherblock_0:int128`, mk_comb(`nist_input_block inblock`, blkidx 0));
       mk_eq(`cipherblock_1:int128`, mk_comb(`nist_input_block inblock`, blkidx 1));
       mk_eq(`cipherblock_2:int128`, mk_comb(`nist_input_block inblock`, blkidx 2));
       mk_eq(`cipherblock_3:int128`, mk_comb(`nist_input_block inblock`, blkidx 3));
       `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    (* fold any RAW mid-state block reads read(in_p+16*BLK)sK -> inblock BLK via the state-agnostic input
       forall (INFOLD3).  The s0 priming only reaches blocks loaded at s0; the SWP schedule loads the last
       group's blocks at mid-states (s61 etc.), whose raw byte towers otherwise survive into the BITBLAST
       and make it FALSE (operand mismatch: `inblock (+4)` vs raw `read(..+112)s61`). *)
    INFOLD3 THEN
    REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    ALL_TAC THEN
    (* the goal here is a pure 256-bit word_join/word_subword/word_xor tautology (verified TRUE in MCP,
       48129-node BDD).  BITBLAST_TAC folds ambient assumptions and can spuriously fail; CONV_TAC BITBLAST_RULE
       proves it on the empty context.  Try the RULE form first, fall back to the TAC form. *)
    ALL_TAC THEN
    (CONV_TAC BITBLAST_RULE ORELSE BITBLAST_TAC) THEN
    ALL_TAC ;
    (* branch2: the generalized single-group reduce, then fold back the sofar/cipherblock/h abbrevs *)
    ALL_TAC THEN
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    (* Bridge the goal's literal block indices `4*(loop_count-2)+(off+j)` to `4*ktm+j` for SWP_GHASH_BRANCH2_SETTLED.
       off=0 (subgoal B): indices are already 4*(loop_count-2)+j = 4*ktm+j (no-op).  off=4 (subgoal A): rewrite
       4*(loop_count-2)+{4,5,6,7} -> 4*(loop_count-1)+{0,1,2,3} = 4*ktm+{0,1,2,3} by arith (3<=loop_count). *)
    (if off = 0 then ALL_TAC else
       SUBGOAL_THEN
         (list_mk_conj (map (fun j ->
            mk_eq(mk_binop `(+):num->num->num` `4*(loop_count-2)` (mk_small_numeral (off+j)),
                  if j = 0 then mtm else mk_binop `(+):num->num->num` mtm (mk_small_numeral j)))
          [0;1;2;3]))
         (fun th -> REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]) THEN
    (* branch2: the goal's RHS (from the byteswap-split of byteswap128(nist_ghash..(4*ktm+4))) is the SETTLED
       accumulator form `nist_ghash..tag0 (list_of_seq..(4*ktm+4))`.  SWP_GHASH_BRANCH2_GEN yields the
       non-settled `nist_ghash h acc [4 explicit blocks]` which does NOT syntactically match -> use the
       SETTLED variant (acc = nist_ghash..(4*ktm)) which directly gives the list_of_seq..(4*ktm+4) form. *)
    MP_TAC(ISPEC ktm SWP_GHASH_BRANCH2_SETTLED) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ALL_TAC];;

(* The settled-Q30 conjunct closer (subgoal A + B via John's decomposition).
   Precondition: `inter` was ABBREV'd at step 98 (REABBREV leaves `<1st-reduce expr> = inter` as an asm,
   and the goal's LHS 2nd-reduce tower + downstream references are folded to `inter`).
   Goal here: <2nd reduce over inter> = byteswap128(nist_ghash..(4*loop_count)). *)
let DRAIN_Q30_TAC : tactic =
  (* (B) inter = byteswap128(nist_ghash..(4*(loop_count-1))).  The `<1st-reduce expr> = inter` assumption,
     reversed, is exactly the machine 1st-reduce = byteswap128(nist_ghash..(4*(loop_count-1))).  Rewrite the
     RHS index 4*(loop_count-1) -> 4*(loop_count-2)+4 so GHASH_SETTLE_TAC (loop_count-2) sees the settled
     4*k+4 form its SWP_GHASH_BRANCH2_SETTLED produces. *)
  SUBGOAL_THEN `inter = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
                        (list_of_seq (nist_input_block inblock) (4 * (loop_count - 1))))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && rhs(concl th) = `inter:int128`
                                 with _ -> false) then MP_TAC th else NO_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    (* RHS index -> 4*ktm+4 (ktm=loop_count-2): 4*(loop_count-1) = 4*(loop_count-2)+4. basetm=4*(loop_count-2). *)
    SUBGOAL_THEN `4 * (loop_count - 1) = 4 * (loop_count - 2) + 4` SUBST1_TAC THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    GHASH_SETTLE_TAC `loop_count - 2` 0;
    ALL_TAC] THEN
  (* (A) The 2nd-reduce machine goal is `<reduce over acc=inter, blocks base+{0..3}> = byteswap128(nist_ghash..(4*loop_count))`
     where the machine block base is 4*(loop_count-2)+4 (the last group).  UNFOLD `inter` to
     byteswap128(nist_ghash..(4*(loop_count-1))) so DEC_GHASH_NORM normalizes the acc byteswap; rewrite RHS index
     4*loop_count -> 4*(loop_count-1)+4 = 4*ktm+4 (ktm=loop_count-1); pass basetm=4*(loop_count-2)+4 so the
     cipherblock ABBREVs match the goal's literal block indices (the branch2 bridge then reconciles base->4*ktm). *)
  FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && lhs(concl th) = `inter:int128` &&
                                 can(find_term(fun u->try fst(dest_const(fst(strip_comb u)))="nist_ghash" with _->false))(rhs(concl th))
                               with _ -> false) then SUBST1_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `4 * loop_count = 4 * (loop_count - 1) + 4` SUBST1_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  GHASH_SETTLE_TAC `loop_count - 1` 4;;

let DRAIN_CLOSE : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (* frame / forall / non-eq *)
       (FIRST[close_goal10; MUST OUT0_TAC; ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (* the settled Q30 double-reduce: staged via DRAIN_Q30_TAC (subgoal A + B), NOT monolithic. *)
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (DRAIN_Q30_TAC THEN NO_TAC) ]) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* out-store readback for the drained blocks +4..+7.  Two shapes reach here:
          (a) block +4 (CONJ 04): the read ALREADY folded (by ASM_REWRITE) to the AES eor3 tower
              `word_xor (inblock J) (word_xor rk10 (aese-tower over word_reversefields 8 (ctr_block nonce (J+2))))`.
          (b) blocks +5/+6/+7 (CONJ 05/06/07): the read is at a store-fact address `(64*(loop_count-2)+64)+K`
              vs the goal's `64*(loop_count-2)+{80,96,112}`; addr-normalize + ASM_REWRITE folds it to the tower.
          The completing recon (MCP-verified) = XOR_AES128_CIPHER_RECONSTRUCT_DEC + double-reversefields cancel +
          aes_ctr_block unfold + counter NUM_REDUCE + ASM_REWRITE_TAC[] (folds [EL 0 rk;..;EL 10 rk]=rk via the
          hyp).  EVERY option ends THEN NO_TAC (MUST allows residual -> silent Unsolved; guard with full closure). *)
       (let RECON =
          (* first-group blocks (+0/+1) have an `aes2c nonce rk (..+2)` precomputed-2-rounds base (SWP);
             unfold it to the full AES tower.  No-op on last-group (+4..+7) towers (plain ctr_block base). *)
          REWRITE_TAC[aes2c] THEN
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          (* STACK-STAGED counter reconstruction (blocks +5/+6/+7 after MERGE_CTR128_TAC): the merged counter is
             word_join(word_or(word_zx..(ctr_block nonce 2))(word_shl(word_bytereverse(word_zx-nest of counter idx))))..;
             CTR_ZX_NORM collapses the zx-nest to word_add(word K)(word 2), GSYM WORD_ADD + arith fold it to a bare
             word(K+2), then CTR_BLOCK_BUILD_INSERT recognises the whole word_join as word_reversefields 8 (ctr_block
             nonce (K+2)).  (No-op on plain-ctr_block blocks +0..+4.) *)
          REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
          CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `(4*(loop_count-2)+4)+2 = 4*(loop_count-2)+6`;
                      ARITH_RULE `(4*(loop_count-2)+5)+2 = 4*(loop_count-2)+7`;
                      ARITH_RULE `(4*(loop_count-2)+6)+2 = 4*(loop_count-2)+8`;
                      ARITH_RULE `(4*(loop_count-2)+7)+2 = 4*(loop_count-2)+9`] THEN
          REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
          REWRITE_TAC[aes_ctr_block] THEN
          (* counter (4*(loop_count-2)+J)+2 -> 4*(loop_count-2)+(J+2): assoc then reduce the J+2 numeral *)
          REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          ASM_REWRITE_TAC[] in
        let ADDRNORM = REWRITE_TAC[ARITH_RULE `64*(loop_count-2)+80 = (64*(loop_count-2)+64)+16`;
                             ARITH_RULE `64*(loop_count-2)+96 = (64*(loop_count-2)+64)+32`;
                             ARITH_RULE `64*(loop_count-2)+112 = (64*(loop_count-2)+64)+48`] in
        FIRST[ (ASM_REWRITE_TAC[] THEN NO_TAC);
               (* (a) block +4: read already folded to the tower -> just RECON *)
               (RECON THEN NO_TAC);
               (* (b) blocks +5/+6/+7: addr-normalize, ASM_REWRITE the store fact, then RECON (or INFOLD+RECON) *)
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3 THEN RECON) THEN NO_TAC);
               (* fallback: original AES2C_OUT_TAC path after addr-norm+fold *)
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC) THEN NO_TAC);
             ]) (asl,w)
     else if (try fst(dest_const(fst(strip_comb(lhs w))))="word_zx" with _->false) then
       (* X13 scalar counter: word_zx(word_add(word_zx(word_zx(word K)))(word 4)) = word_zx(word(4*lc+2)).
          The nested zx chain + the +word 4 increment must be normalized by the counter lemmas, then the
          nat identity K+4 = 4*lc+2 discharged with the 3<=loop_count context.  The generic WORD_BLAST/
          WORD_RULE fallbacks below THRASH on this symbolic-loop_count goal (the DRAIN CONJ-00 hang). *)
       (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) (asl,w)
     else
       (* cheap: registers (post goal-level ptr-advance SUBGOAL these are REFL), counter slots, ctr_block folds *)
       (FIRST[ (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
               (AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC THEN NO_TAC);   (* X0/X2 ptr advance fallback *)
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC);
               (CONV_TAC WORD_RULE THEN NO_TAC);
               (CLOSE_V8 THEN NO_TAC) ]) (asl,w));;
let SWP_DEC_LC2_PARTB = prove(drain_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`]) THEN
  (* --- PRIME the drained group's 4 input-block reads to `inblock` form (mirror BODYLEG
     lines 268-279).  Without this the drain's ldr q,[x0] loads reach the settled-Q30 closer
     as RAW byte-reassembly towers (2357 word_subword(read(mem..)) extractions) and the
     branch1 BITBLAST blows up like the monolithic (>73 min).  With it, the loads fold to
     the 4 cipherblock_k atoms and the BITBLAST matches BODYLEG's fast ~117s path. --- *)
  SUBGOAL_THEN `4*(loop_count-2)+7 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `2 <= loop_count` THEN
    SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+64)))) s0 = inblock (4*(loop_count-2)+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+80)))) s0 = inblock (4*(loop_count-2)+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+96)))) s0 = inblock (4*(loop_count-2)+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+112)))) s0 = inblock (4*(loop_count-2)+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+64)):int64 = word_add in_p (word (16*(4*(loop_count-2)+4)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+80)):int64 = word_add in_p (word (16*(4*(loop_count-2)+5)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+96)):int64 = word_add in_p (word (16*(4*(loop_count-2)+6)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+112)):int64 = word_add in_p (word (16*(4*(loop_count-2)+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* htable_mem_4 unfold so the 4 htable reads are anchored + survive *)
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  ALL_TAC THEN
  drain_step_tac THEN
  ALL_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ALL_TAC THEN
  (* fold the X0/X2 pointer-advance arithmetic at goal level (SUBGOAL the two facts, guaranteed to fire) *)
  SUBGOAL_THEN `64 * (loop_count - 2) + 128 = 64 * loop_count /\
                (64 * (loop_count - 2) + 64) + 64 = 64 * loop_count`
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* --- Split the out-store forall (post `j < 4*loop_count`) into the invariant's preserved
     prefix `j < 4*(loop_count-2)` (closed from the incoming forall by ASM_REWRITE) + the 8
     drained blocks 4*(loop_count-2)..+7 as explicit unwound equations (mirror BODYLEG's 4-way
     split at 2-group depth).  Without this the whole forall reaches the broken OUT0_TAC (hardcoded
     `j < 4*i`, no `i` in the drain) and thrashes.  Needs 3<=loop_count for the bound arithmetic. --- *)
  SUBGOAL_THEN `!j:num. j < 4 * loop_count <=>
      j < 4*(loop_count-2) \/ j = 4*(loop_count-2) \/ j = 4*(loop_count-2)+1 \/ j = 4*(loop_count-2)+2 \/
      j = 4*(loop_count-2)+3 \/ j = 4*(loop_count-2)+4 \/ j = 4*(loop_count-2)+5 \/ j = 4*(loop_count-2)+6 \/
      j = 4*(loop_count-2)+7`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  (* fold the 8 unwound out-store addresses 16*(4*(loop_count-2)+k) back to byte offsets, and the
     counter/block indices, so the aes_ctr_block closer + ASM_REWRITE match the stored-block facts. *)
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`; ARITH_RULE `16 * 4 * a = 64 * a`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DRAIN_CLOSE);;

(* ==================== COMPOSITION: PARTA + PARTB -> SWP_DEC_LC2 ==================== *)
let lc2_ens  = list_mk_comb(`ensures arm`,[fill_pre;drain_post;fill_frame]);;
let lc2_goal = list_mk_forall(vs_fill, mk_imp(fill_hyps, lc2_ens));;
let SWP_DEC_LC2 = prove(lc2_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x514`
    (mk_abs(`s:armstate`, ap swpS_inv8_dec_v8 `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWP_DEC_LC2_PARTA THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRECONDITION_TAC drain_pre THEN CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      FIRST_ASSUM(fun th -> if lhs(concl th)=`loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      MATCH_MP_TAC SWP_DEC_LC2_PARTB THEN EXISTS_TAC `key_p:int64` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM ACCEPT_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN (UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC)]]);;

(* ==================== leaf tactics wiring the 7 proven legs into the main theorem ==================== *)
(* lc0 (0xa0->0xaa0, loop_count=0): the interactive recipe (no separate lemma). *)
let SWP_DEC_LC0_TAC : tactic =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN ASM_REWRITE_TAC[] THEN
  (* CRUCIAL: reduce 4*0 -> 0 BEFORE unfolding list_of_seq/nist_ghash, else nist_ghash's recursive
     equation loops (stack overflow) on the un-reduced count.  Do NOT use `LT`/`CONJUNCT1 LT` in a
     REWRITE set -- LT's recursive def loops too.  Then close the trivial numeric residuals. *)
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`; ARITH_RULE `4 * 0 + 2 = 2`;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[nist_ghash] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  (* re-FOLD the ABI macro in the goal frame (main thm expanded it up top) so MAYCHANGE_ABI_CLOSE's
     MATCH_MP against the folded-ABI subsumption lemma matches the frame goal `(ABI ,, ..) s0 s1`. *)
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  MAYCHANGE_ABI_CLOSE;;

(* lc1 (0xa0->0xaa0, loop_count=1): SWP_DEC_ITER1 (loop_count=1 in context). *)
(* The main theorem's leaf goals present the ABI macro EXPANDED (line "REWRITE_TAC[...ABI]" up top) and
   htable_mem_4 UNFOLDED (the 0xa0 precond expansion); the leg lemmas are stated with the folded ABI macro
   and folded htable_mem_4.  So REWRITE_RULE[ABI; htable_mem_4] each leg to match before MATCH_MP_TAC. *)
(* deint pattern: the leaf goal has ABI EXPANDED (early REWRITE) + htable UNFOLDED; the leg has ABI
   FOLDED + htable FOLDED.  Re-FOLD the ABI macro in the GOAL frame (GSYM) right before MATCH_MP_TAC so
   it matches the leg frame, and UNFOLD htable_mem_4 in the LEG (only its pre gains the 6 reads). *)
let leg_htab th = REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] th;;
let REFOLD_ABI = REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
(* Apply a proven leg to a leaf goal `ensures P Q C_leaf`.  The leg proves `ensures P Q C_leg`; C_leg may be
   WIDER than C_leaf on the explicit register list (e.g. fill_frame lists X0..,Q0.. that C_leaf folds into the
   ABI macro), but C_leg subsumed C_leaf (the ABI macro absorbs them; C_leg's mem subseteq C_leaf's mem).  So:
   first try the direct MATCH_MP_TAC (works when C_leg = C_leaf, e.g. iter1/bodyleg narrow frame); on failure,
   bridge via ENSURES_FRAME_SUBSUMED, discharging `C_leg subsumed C_leaf` with the ABI expanded. *)
(* Apply a proven leg to a leaf goal `ensures P Q_leaf C_leaf`.  Three reconciliations may be needed:
   (1) POST: the leg may prove a STRONGER post Q_leg (e.g. it establishes `read X1 s = word 0`, which the
       shared 0xaa0 midcond had to DROP for iter_1).  Switch the goal's post to Q_leg via
       ENSURES_POSTCONDITION_TAC, discharging `Q_leg ==> Q_leaf` (drop the extra conjunct).
   (2) FRAME: C_leg may be WIDER than C_leaf on the explicit reg list (fill_frame lists X0.. that C_leaf
       folds into the ABI macro); C_leg subsumed C_leaf, so bridge via ENSURES_FRAME_SUBSUMED.
   (3) ABI/htable: REFOLD_ABI in the goal + leg_htab (unfold htable + GSYM CONJ_ASSOC) in the leg.
   `TRY(EXISTS_TAC key_p)` since key_p (a hyp-only var) may or may not survive the ensures match. *)
(* discharge a proven leg's side-hyps (nblocks arith, [EL..]=rk, nonoverlapping) from the main-theorem
   context.  The nonoverlapping hyps often appear ARG-SWAPPED vs the ALLPAIRS-expanded assumptions
   (leg wants `nonoverlapping (in_p,..) (sp+160,..)`, ctx has `(sp+160,..) (in_p,..)`), so ASM_REWRITE
   alone won't close them -- fall back to NONOVERLAPPING_TAC (handles symmetry + arithmetic). *)
let discharge_leg_hyps : tactic =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC;;
let apply_leg_core (legn:thm) : tactic =
  REFOLD_ABI THEN
  ((MATCH_MP_TAC legn THEN TRY(EXISTS_TAC `key_p:int64`) THEN discharge_leg_hyps)
   ORELSE
   (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl legn)))))))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC legn THEN TRY(EXISTS_TAC `key_p:int64`) THEN discharge_leg_hyps]));;
(* one attempt at a given leg form (legn): direct core, else post-bridge (for X1-stronger legs).
   The post-bridge is guarded by `w`-is-ensures (ENSURES_POSTCONDITION_TAC errors on a non-ensures goal),
   and phrased as a single `fun (asl,w)` so a failed direct core never leaves a half-rewritten goal for it. *)
let apply_leg_1 (legn:thm) : tactic =
  fun (asl,w) ->
    ((apply_leg_core legn)
     ORELSE
     (fun (a2,w2) ->
        if (try fst(dest_const(fst(strip_comb w2))) = "ensures" with _ -> false) then
          (let lpost = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl legn))))))) in
           (ENSURES_POSTCONDITION_TAC lpost THEN
            CONJ_TAC THENL
             [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
              DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN
                 FIRST[ACCEPT_TAC th; (STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC[])]);
              apply_leg_core legn]) (a2,w2))
        else failwith "apply_leg_1: not ensures")) (asl,w);;
(* The leg's pre/post invariant may keep htable_mem_4 FOLDED (BODY/FILL/DRAIN, whose leaf carries the flat
   swpS_inv8_dec_v8 with htable folded inside) or UNFOLDED (LC1/LC2, whose leaf pre expands htable via the
   0xa0-precond REWRITE).  Try WITH the htable unfold (leg_htab) first, then WITHOUT (leg unchanged, only
   right-assoc). *)
let APPLY_LEG (leg:thm) : tactic =
  (apply_leg_1 (leg_htab leg))
  ORELSE
  (apply_leg_1 (REWRITE_RULE[GSYM CONJ_ASSOC] leg));;
let SWP_DEC_LC1_TAC : tactic = APPLY_LEG SWP_DEC_ITER1;;

(* lc2 (0xa0->0xaa0, loop_count=2): SWP_DEC_LC2. *)
let SWP_DEC_LC2_TAC : tactic = APPLY_LEG SWP_DEC_LC2;;

(* FILL leaf (0xa0->0x294, establish inv 0): SWP_DEC_FILLLEG.  MIXED htable fold-state -- leaf-PRE
   (0xa0 precond) has htable UNFOLDED but leaf-POST (WHILE inv 0 = swpS_inv8_dec_v8 0) has it FOLDED.
   Bare APPLY_LEG then needs an `unfolded ==> folded` post-bridge weakening that leaves a folded
   htable_mem_4 leaf UNCLOSED under the native ASL iteration order (the leftover leaks past the WHILE ->
   "neither ensures" downstream).  FIX: REWRITE_TAC[htable_mem_4] on the whole goal first (unfolds htable
   in BOTH leaf-PRE and leaf-POST) so the fully-unfolded leg matches with NO post-bridge weakening. *)
let SWP_DEC_FILL_LEAF_TAC : tactic = REWRITE_TAC[htable_mem_4] THEN APPLY_LEG SWP_DEC_FILLLEG;;

(* BODY leaf (0x294->0x510, inv i -> inv (i+1)): SWP_DEC_BODYLEG. *)
let SWP_DEC_BODY_LEAF_TAC : tactic =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN APPLY_LEG SWP_DEC_BODYLEG;;

(* back-edge leaf (cbnz@0x510 -> 0x294 while i+1 < loop_count-2): interactive recipe. *)
let SWP_DEC_BACKEDGE_LEAF_TAC : tactic =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  (* the cbnz@0x510 guard is not-taken since (loop_count-2)-i != 0 for i < loop_count-2.  Discharge the
     `~(val(word(loop_count-2-i))=0)` obligation from whatever loop-count facts the WHILE-leaf provides
     (ASM_ARITH_TAC uses all assumptions -- robust to the exact assumption forms). *)
  (* discharge the cbnz-not-taken guard using ONLY the small loop-count facts (val(word loop_count)=loop_count
     gives loop_count<2^64; i<loop_count-2 gives loop_count-2-i>0).  Do NOT use ASM_ARITH_TAC -- it drags the
     whole huge invariant into the linear-arith engine and blows up. *)
  SUBGOAL_THEN `~(val(word(loop_count-2-i):int64) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word(loop_count-2-i):int64) = loop_count-2-i` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MP_TAC(ISPEC `word loop_count:int64` VAL_BOUND_64) THEN
      TRY(FIRST_ASSUM(fun th -> if lhs(concl th) = `val(word loop_count:int64)` then REWRITE_TAC[th] else NO_TAC)) THEN
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC;
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_ABI_CLOSE;;

(* DRAIN leaf (0x510->0xaa0, inv (loop_count-2) -> after-loop postcond): SWP_DEC_DRAINLEG.
   DRAIN is the UNIQUE leg with a MIXED htable fold-state: its leaf PRE carries the FOLDED
   swpS_inv8_dec_v8 (htable_mem_4 folded inside), matching the RAW leg's PRE, but its leaf POST is
   the 0xaa0 midcond with htable_mem_4 UNFOLDED (line ~3797 REWRITE) and X1 DROPPED.  So we specialize:
   (1) switch the goal post to the RAW leg's post (folded htable + X1=word 0) via ENSURES_POSTCONDITION_TAC,
   (2) weaken that to the leaf post with REWRITE_TAC[htable_mem_4] (+ drop X1),
   (3) discharge the residual `ensures P lpost C_leaf` by FORWARD-applying the leg: the leg's PRE is
       alpha-equal to the goal PRE, so SPEC_ALL gives `hyps ==> ensures P lpost C_leg` directly; bridge the
       narrow leg frame C_leg to the ABI-expanded leaf frame C_leaf via ENSURES_FRAME_SUBSUMED, then
       ACCEPT_TAC the forward theorem MP'd with the hyps discharged as an ISOLATED subgoal.
   This forward construction (ACCEPT of `MP (SPEC_ALL leg) hyps_thm`) avoids the generic apply_leg_core's
   in-place `MATCH_MP_TAC leg` + `?key_p` existential + intertwined discharge, which -- while sound and
   closing under the MCP interpreter -- diverged under the ocamlopt-native build ("neither ensures"). *)
(* Targeted closer for the single `16 * nblocks <= 2 EXP 64` leg-hyp leaf: uses ONLY the two relevant
   asl facts by EXACT concl-match (order-independent -- a `match .. when r=nblocks` OCaml pattern could
   pick `val(word nblocks)=nblocks` first under a different native ASL iteration order).  Replaces
   ASM_ARITH_TAC (whose full-36-assumption sweep, though sound + closing under the MCP interpreter,
   left leaves unclosed under the ocamlopt-native build -> spurious "neither ensures" downstream). *)
let close_nblocks_bound : tactic =
  FIRST_ASSUM(fun th -> if concl th = `len_bits DIV 128 = nblocks` then SUBST1_TAC(SYM th) else failwith "no") THEN
  FIRST_ASSUM(fun th -> if concl th = `len_bits < 2 EXP 64` then MP_TAC th else failwith "no") THEN
  ARITH_TAC;;
(* Discharge an arg-swapped `nonoverlapping (a,b) (c,d)` leaf directly from the asl's swapped form via
   NONOVERLAPPING_SYM -- avoiding NONOVERLAPPING_TAC's full-ASL sweep (another divergence suspect). *)
let close_nonov_sym : tactic =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  FIRST_ASSUM(fun th -> ACCEPT_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th));;
let SWP_DEC_DRAIN_LEAF_TAC : tactic =
  fun (asl,w) ->
    let legn = REWRITE_RULE[GSYM CONJ_ASSOC] SWP_DEC_DRAINLEG in
    let ens_args = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl legn)))))) in
    let lpost = el 2 ens_args and legframe = el 3 ens_args in
    (ENSURES_POSTCONDITION_TAC lpost THEN
     CONJ_TAC THENL
      [ (*** weaken leg-post (folded htable, +X1) ==> leaf-post (unfolded htable, -X1): CONJUNCTS-based,
            ORDER-INDEPENDENT.  After unfolding htable on both sides, DISCH the single hyp, take its
            CONJUNCTS (fixed term-structural order, identical in MCP + native), and close each goal
            conjunct by `FIRST(map ACCEPT_TAC cs)`.  This avoids ASM_REWRITE/FIRST_ASSUM ASL-iteration,
            whose native order left an htable_mem_4 leaf unclosed (leaked past the WHILE -> "neither
            ensures" when the tail-loop tactic hit it). ***)
        REPEAT GEN_TAC THEN REWRITE_TAC[htable_mem_4] THEN
        DISCH_THEN(fun th -> let cs = CONJUNCTS th in REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC cs));
        (*** ensures P lpost C_leaf : refold ABI, frame-subsume to C_leg, ACCEPT forward leg thm ***)
        REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC legframe THEN
        CONJ_TAC THENL
         [ REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
           (*** discharge the leg's hyps as an isolated subgoal using ONLY lightweight, ASL-sweep-free
                closers (ACCEPT / ASM_REWRITE / NONOVERLAPPING_SYM / targeted arith) ***)
           (let legi = SPEC_ALL legn in
            let hyps' = fst(dest_imp(concl legi)) in
            SUBGOAL_THEN hyps' (fun hth -> ACCEPT_TAC(MP legi hth))) THEN
           ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
           REPEAT(FIRST[FIRST_ASSUM ACCEPT_TAC; (ASM_REWRITE_TAC[] THEN NO_TAC);
                        close_nonov_sym; close_nblocks_bound; CONJ_TAC]) ]]) (asl,w);;

(* ==================== MAIN THEOREM (7 legs wired) ==================== *)
let AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0xb7c) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list - a bit clumsy ****)

  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN

  (***** Initial state setup ****)

  ENSURES_SEQUENCE_TAC `pc + 0xa0`
   `\s. read X0 s = in_p /\
        read X2 s = out_p /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read Q28 s = word_reversefields 8 (EL 10 rk) /\
        read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
        read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
        read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
        read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
        read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word 2:int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\
        read X7 s = word nblocks /\
        read X16 s = word loop_remain /\
        read Q30 s =
          byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                 inblock i)` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    (*** Split + abbreviate the two 64-bit IV halves so the scalar counter    ***)
    (*** registers X11/X12/X13 loaded by "ldp x11,x12,[x4]" survive as clean  ***)
    (*** variables rather than being dropped as compound initial-memory reads ***)
    UNDISCH_TAC
     `read (memory :> bytes128 ivec_p) s0 =
      word_reversefields 8 (ctr_block nonce 2)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC (1--29) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Name the IV-halves join relation for reuse in the counter conjuncts.    ***)
    (*** Keep ivlo/ivhi UNsubstituted so the ivec recombination still closes.    ***)
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
             (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ivec memory read: recombine the two abbreviated halves ***)
      GEN_REWRITE_TAC LAND_CONV
       [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      (*** X11 = low half of the reversed counter block ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      (*** X12 = nonce-remainder half (counter lane zeroed) ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      (*** X13 = counter value 2 ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      (*** X15 = len_bits DIV 8 ***)
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      (*** X1 = loop_count (three composed lsr's) ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN
      MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      (*** X7 = nblocks (two composed lsr's) ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      (*** X9 = loop_remain ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN
      REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      (*** Q11 = byteswap tag ***)
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN

  (*** Break code between main unrolled loop and tail loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xaa0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read Q28 s = word_reversefields 8 (EL 10 rk) /\
        read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
        read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
        read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
        read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
        read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X16 s = word loop_remain /\
        read Q30 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_input_block inblock)
                            (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [(*** MAIN LOOP (software-pipelined), 0xa0 -> 0xaa0, via the elaborated Q = P o [Y]
     *** invariant inlined at the ENSURES_WHILE_UP_TAC below.  Four control-flow paths
     *** on loop_count.  The fill does "sub x1,x1,#2" (0x28c) then "cbz x1,0x514"; the
     *** steady body does "sub x1,x1,#1" (0x50c) then "cbnz x1,0x294", so the steady
     *** loop runs loop_count-2 times (a DEPTH-2 pipeline: AES runs ahead in Q30/Q5,
     *** GHASH lags behind with this group's fold half-done):
     ***   count = 0 : cbz x1 at 0xa0 -> straight to 0xaa0 (no blocks).
     ***   count = 1 : b.eq 0x828 -> iter_1 single-group path -> 0xaa0.
     ***   count = 2 : fill then cbz at 0x290 -> drain 0x514; steady loop runs 0 times
     ***              (k=0), so ENSURES_WHILE_UP_TAC (which needs ~(k=0)) does not apply
     ***              -> its own peeled case.
     ***   count >=3 : ENSURES_WHILE_UP_TAC (loop_count-2), head 0x294 / back-edge 0x510.
     ***              FILL (0xa0->0x294, establish inv 0) and DRAIN (0x510->0xaa0,
     ***              inv (loop_count-2) -> after-loop postcondition) are this tactic's
     ***              first and last subgoals, NOT separate ENSURES_SEQUENCE_TACs.  The
     ***              steady body is the BODYLEG.
     *** Each leaf subgoal is discharged by its proven leg lemma (SWP_DEC_ITER1,     ***
     *** SWP_DEC_LC2, SWP_DEC_FILLLEG, SWP_DEC_BODYLEG, SWP_DEC_DRAINLEG) or an       ***
     *** inline recipe (loop_count=0, back-edge), via the *_TAC wrappers above.       ***)

    ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN SWP_DEC_LC0_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 1` THENL
     [SWP_DEC_LC1_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 2` THENL
     [SWP_DEC_LC2_TAC;
      ALL_TAC] THEN

    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x294` `pc + 0x510`
      (mk_abs(`i:num`, mk_abs(`s:armstate`, ap swpS_inv8_dec_v8 `i:num` `s:armstate`))) THEN
    REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 2 = 0), from 3 <= loop_count. ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa0 -> 0x294, establish the inlined invariant at i = 0. ***)
      SWP_DEC_FILL_LEAF_TAC;
      (*** BODY (BODYLEG): 0x294 -> 0x510, inv i -> inv (i+1). ***)
      SWP_DEC_BODY_LEAF_TAC;
      (*** back-edge: cbnz x1 at 0x510 -> 0x294 while i+1 < loop_count-2. ***)
      SWP_DEC_BACKEDGE_LEAF_TAC;
      (*** DRAIN: 0x510 -> 0xaa0, inv (loop_count-2) -> after-loop postcondition. ***)
      SWP_DEC_DRAIN_LEAF_TAC];
    ALL_TAC] THEN
  (*** Trivial case of the tail loop ***)

  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    (*** Split the initial ivec read so the low 12 bytes (untouched by the counter ***)
    (*** writeback) survive as separate 32-bit cells across the stepping.          ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    (*** Recompose the ivec postcondition from the 32-bit cells: three unchanged   ***)
    (*** nonce cells plus the freshly-written byte-reversed counter word.  Split    ***)
    (*** ONLY the ivec read (guarded), not the out-block reads.                     ***)
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST;

    ALL_TAC] THEN

  (*** Loop setup for the tail loop ***)

  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb64`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\
      read X4 s = ivec_p /\
      read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\
      read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\
      read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\
      read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\
      read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\
      read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read Q28 s = word_reversefields 8 (EL 10 rk) /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s =
        word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
      read X12 s =
        word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + 2):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\
      read X16 s = word(loop_remain - i) /\
      read Q30 s =
        byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_input_block inblock)
                          (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** Main loop invariant (tail loop) ****)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
        (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    (*** The single tail block also assembles its counter on the stack          ***)
    (*** SWP tail: "stp x11,x23,[sp,#160]" at step 6, "ldr q10,[sp,#160]" at step 8; ***)
    (*** merge the two 64-bit stores AT STATE s6 (after the stp, BEFORE the ldr)  ***)
    (*** so the 128-bit reload at step 6 yields a CONCRETE counter block.  This    ***)
    (*** is essential: if merged at s6 the ldr q0 keeps a symbolic read, the AES   ***)
    (*** chain `read Q0 sN = aese (read Q0 s_{N-1})..` then references old states   ***)
    (*** and every step is DISCARDED by DISCARD_OLDSTATE, so the output-store       ***)
    (*** read-back `read(mem) s28 = read Q0 s27` is erased and the postcondition    ***)
    (*** store read never resolves.  (Encrypt's tail merges at s6 because its stp   ***)
    (*** lands one step later; the decrypt tail schedule puts the stp at step 5.)   ***)
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (1--6) THEN
    MERGE_CTR128_TAC 160 "s6" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (7--48) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    (*** Scalar counter reconstruction (tail loop, single block; "add w14,w13,#0" ***)
    (*** so the counter word is the base 4*loop_count+i+2).                          ***)
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s48" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    (*** Fold the GHASH operand to nist_input_block subwords (as in the main loop).       ***)
    DEC_GHASH_NORM_TAC THEN
    (*** Peel the counter conjunct (word arithmetic); the single output-store conjunct was  ***)
    (*** already folded + resolved in the store/counter prefix above via the forall-split    ***)
    (*** (j = 4*loop_count+i) + XOR_AES128_CIPHER_RECONSTRUCT_DEC, exactly as the main loop's ***)
    (*** four stores.  This leaves the single GHASH accumulator goal.                        ***)
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE ORELSE
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < loop_remain ==> i + 1 <= loop_remain`];
      ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64)
               (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64)
                    (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64)
                    (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (4 * loop_count + i)))`;
      `cipherblock =
        nist_input_block inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3
          (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
      REWRITE_TAC[GSYM nist_input_block] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND;
                NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** Trivial loop-back goal (tail loop) ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [1] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ];

    (**** Final writeback, reversal etc. ***)

    ENSURES_INIT_TAC "s0" THEN
    (*** Split the initial ivec read so the low 12 (nonce) bytes survive the        ***)
    (*** 4-byte counter writeback as separate cells.                                ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Unify the counter values: the postcondition uses nblocks, the running     ***)
    (*** counter is 4*loop_count+loop_remain; rewrite nblocks to the latter so both ***)
    (*** sides share one expression before blasting.                                ***)
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    (*** Normalise counter-value associativity (X13's 4*lc+lr+2 vs the         ***)
    (*** postcondition's (4*lc+lr)+2) and collapse the W-conversion chain      ***)
    (*** before blasting.                                                      ***)
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;

(* Subroutine correctness: lifts the core proof through the save/restore     *)
(* boilerplate and the final ret. This is the theorem used externally.       *)
(* ------------------------------------------------------------------------- *)

(*** The externally-used spec. Its pre/postconditions match the core theorem
 *** (CTR ciphertext output, GHASH tag, updated counter), lifted through the
 *** save/restore prologue/epilogue and the final ret. The stack frame region
 *** (224 bytes below the incoming SP) is added to the nonoverlapping lists and
 *** to the MAYCHANGE. ARM_ADD_RETURN_STACK_TAC does the lifting; we expand the
 *** compound memory predicates htable_mem_4 and wordlist_from_memory (in both
 *** the goal and the fed core theorem) so the interior big-step's precondition
 *** obligation is discharged with no residual subgoal.
 ***)

let AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  REWRITE_TAC[fst AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC; htable_mem_4]
          AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory-safety proofs (core kernel body + full subroutine).*)
(*                                                                            *)
(* The event trace e2 produced by the kernel is a function of the PUBLIC       *)
(* arguments only (in/out/tag/ivec/key/htable pointers, len_bits, pc,          *)
(* stackpointer[, returnaddress]) -- established by the outer `exists          *)
(* f_events` over public data -- and every memory access lies in the declared  *)
(* readable / writable ranges (memaccess_inbounds).  This gives constant-time  *)
(* execution and memory safety.                                                *)
(*                                                                            *)
(* This kernel is software-pipelined: the main loop (loop_count = nblocks      *)
(* DIV 4, over 64-byte groups) is a depth-2 pipeline with four control-flow    *)
(* paths (loop_count = 0 / 1 / 2 / >=3), and the tail loop (loop_remain =      *)
(* nblocks MOD 4, over 16-byte blocks) is a plain WHILE.  The `_SUBROUTINE_`   *)
(* variant additionally wraps the register-save prologue and register-restore *)
(* epilogue over the 224-byte stack frame (WORD_FORALL_OFFSET_TAC 224).        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;

let EXEC = AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_EXEC;;

let SAFE_SIM = ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
                 ~canonicalize_pc_diff:false EXEC;;

(* ------------------------------------------------------------------------- *)
(* Leaf closers -- identical to the clean keep_htable safety proof.           *)
(* ------------------------------------------------------------------------- *)

let lc_eq = prove
 (`nblocks DIV 4 = loop_count /\ len_bits DIV 128 = nblocks
    ==> loop_count = len_bits DIV 512`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks DIV 4 = loop_count`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `len_bits DIV 128 = nblocks`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV);;

let lr_eq = prove
 (`nblocks MOD 4 = loop_remain /\ len_bits DIV 128 = nblocks
    ==> loop_remain = len_bits DIV 128 MOD 4`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `nblocks MOD 4 = loop_remain`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

let WSUB_BRANCH = prove
 (`!i k:num. i < k /\ k < 2 EXP 64
     ==> (~(val(word_sub (word (k - i):int64) (word 1)) = 0) <=> i + 1 < k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word (k - i):int64) = k - i` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `k:num` THEN ASM_SIMP_TAC[LE_REFL] THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD_1] THEN
    SIMP_TAC[DIMINDEX_64; ARITH_RULE `1 < 2 EXP 64`] THEN ASM_ARITH_TAC]);;

let DEABBR : tactic =
  W(fun (asl,w) ->
    let lcth = try [MATCH_MP lc_eq (CONJ (ASSUME `nblocks DIV 4 = loop_count`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let lrth = try [MATCH_MP lr_eq (CONJ (ASSUME `nblocks MOD 4 = loop_remain`)
                                          (ASSUME `len_bits DIV 128 = nblocks`))] with _ -> [] in
    let vwth = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && (match lhs t with
                         Comb(v,Comb(wd,_)) ->
                           (try name_of v = "val" && name_of wd = "word" with _ -> false)
                       | _ -> false)
        then th else fail()) asl in
    let lclr = lcth @ lrth in
    RULE_ASSUM_TAC(fun th ->
       if is_eq(concl th) && is_var(lhs(concl th)) &&
          type_of(lhs(concl th)) = `:(uarch_event)list`
       then REWRITE_RULE (lclr @ vwth) th
       else REWRITE_RULE lclr th) THEN
    REWRITE_TAC (lclr @ vwth));;

let CTR_RECON : tactic =
  GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
  GEN_REWRITE_TAC (TRY_CONV o ONCE_DEPTH_CONV)
    [ARITH_RULE `word 3:int64 = word(2 EXP 2 - 1)`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM(ASSUME `len_bits DIV 128 = nblocks`);
              GSYM(ASSUME `nblocks DIV 4 = loop_count`);
              GSYM(ASSUME `nblocks MOD 4 = loop_remain`)] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV;;

let ADDR_RECON : tactic =
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; SUB_0;
              WORD_ADD_0; ADD_ASSOC] THEN
  (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_ARITH);;

let BRANCH_RECON : tactic =
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_SIMP_TAC[WSUB_BRANCH];;

let WSUB_ARITH : tactic =
  W(fun (asl,w) ->
    let l,_ = dest_eq w in
    let cnt_minus_i = (match l with Comb(Comb(_,Comb(_,a)),_) -> a | _ -> failwith "wsub") in
    let cnt,iv = dest_binary "-" cnt_minus_i in
    let lt = mk_binary "<" (iv,cnt) in
    SUBGOAL_THEN (mk_eq(cnt_minus_i, mk_binary "+" (mk_binary "-" (cnt, mk_binary "+" (iv,`1`)), `1`)))
      SUBST1_TAC THENL
     [(FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC th else NO_TAC)) THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let is_branch_goal w =
  can dest_eq w &&
  (let l,r = dest_eq w in
   let strip t = match t with Comb(c,a) when (try name_of c="word" with _->false) -> a | _ -> t in
   is_cond l || is_cond r || is_cond (strip l) || is_cond (strip r));;

let LEAF1 : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON)
    else (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC));;
let CLOSE : tactic = REPEAT CONJ_TAC THEN LEAF1;;

let MEMACC_VIA_ASM : tactic =
  fun (asl,w) ->
    let defeqs = mapfilter (fun (_,th) -> let t = concl th in
        if is_eq t && is_var(lhs t) && type_of(lhs t) = `:(uarch_event)list`
        then (lhs t, th) else fail()) asl in
    if defeqs = [] then DISCHARGE_MEMACCESS_INBOUNDS_TAC (asl,w) else
    let _,defth = hd defeqs in
    (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM defth] THEN
     REPEAT (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
             CONJ_TAC THENL [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC; ALL_TAC]) THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

let DISCHARGE_SAFE_ROBUST : tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] else ALL_TAC) THEN
  MEMACC_VIA_ASM;;

let LEAF2 : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON)
    else (DEABBR THEN DISCHARGE_SAFE_ROBUST));;
let CLOSE_R2 : tactic = REPEAT CONJ_TAC THEN LEAF2;;

(* Surgical cond reducers (constant condition), no beta-mangle of f_ev_* redexes. *)
let REDUCE_IFEQ (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQT_INTRO(ASSUME(mk_eq(v,k)))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IFNE (v:term) (k:term) : tactic =
  PURE_ONCE_REWRITE_TAC[EQF_INTRO(ASSUME(mk_neg(mk_eq(v,k))))] THEN PURE_REWRITE_TAC[COND_CLAUSES];;
let REDUCE_IF0 (lv:term)  = REDUCE_IFEQ lv `0`;;
let REDUCE_IFN0 (lv:term) = REDUCE_IFNE lv `0`;;

(* --- SWP-specific closers. --- *)

(* The FILL back-edge cbz @0x290 tests loop_count-2; DRAIN pointer reconciliation *)
(* uses loop_count = (loop_count-2)+2.  DRAIN_ADDR normalises that so WORD_RULE     *)
(* sees only linear combinations.                                                 *)
let DRAIN_ADDR : tactic =
  SUBGOAL_THEN `loop_count = (loop_count - 2) + 2`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC] THEN
  CONV_TAC WORD_RULE;;

(* The b.eq @0xa8 (loop_count=1) and cbz @0x290 (loop_count=2) branch facts: with *)
(* loop_count >= 3 both counters are nonzero, so both branches fall through.       *)
let BEQ_NZ (k:term) : tactic =  (* prove ~(val(word_sub (word loop_count) (word k)) = 0) *)
  SUBGOAL_THEN (mk_neg(mk_eq(mk_comb(`val:int64->num`,
      list_mk_comb(`word_sub:int64->int64->int64`,
        [mk_comb(`word:num->int64`,`loop_count:num`); mk_comb(`word:num->int64`,k)])),`0`)))
    ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,k)),k)) SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC];;

let OPEN_DEC_SWP : tactic =
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN
      SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC];;

let scaffold_dec_swp =
 `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
   (len_bits:int64) (pc:num) (stackpointer:int64).
   APPEND
     (if val len_bits DIV 128 MOD 4 = 0 then
        f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
      else
        APPEND
          (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
          (APPEND
            (ENUMERATEL (val len_bits DIV 128 MOD 4)
              (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
            (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
     (APPEND
       (if val len_bits DIV 128 DIV 4 = 0 then
          f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 1 then
          f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 2 then
          f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0xb68) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC scaffold_dec_swp THEN
  OPEN_DEC_SWP THEN

  (*** Top split at 0xaa0 (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** MAIN REGION pc+0x2c -> pc+0xaa0 (setup + 4-way pipelined loop). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa0`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--29) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0 : cbz @0xa0 taken -> 0xaa0. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1 : b.eq @0xa8 -> iter_1 path (3 + 158 steps). ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--161) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count = 2 : FILL (cbz @0x290 taken) + DRAIN (322 steps). ***)
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--322) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `2` THEN

    (*** loop_count >= 3 : FILL + STEADY(loop_count-2) + DRAIN. ***)
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x294` `pc + 0x514`
     `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
            read X2 s = word_add out_p (word (64 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word loop_remain /\
            read X1 s = word (loop_count - 2 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 2 = 0) ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa0 -> 0x294, establish inv 0. ***)
      BEQ_NZ `1` THEN SAFE_SIM (1--125) THEN
      BEQ_NZ `2` THEN
      REPEAT CONJ_TAC THENL
       [(* cbz @0x290 branch not taken *) ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
        ADDR_RECON;
        ADDR_RECON;
        (* X1 = word(loop_count - 2 - 0) *)
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 2 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** back-edge / STEADY body: 0x294 -> 0x514, inv i -> inv (i+1). ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--160) THEN CLOSE_R2;
      (*** DRAIN post-leg: 0x514 -> 0xaa0. ***)
      SAFE_SIM (1--197) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** TAIL REGION pc+0xaa0 -> pc+0xb68. ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--1) THEN CLOSE_R2; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb68`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--1) THEN CLOSE_R2;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--49) THEN CLOSE_R2);;


(* ------------------------------------------------------------------------- *)
(* Full-function (subroutine-level) constant-time + memory-safety.            *)
(*                                                                            *)
(* Same wrapping as the clean keep_htable subroutine proof: WORD_FORALL_      *)
(* OFFSET_TAC 224 aligns the post-prologue running SP with the abstract       *)
(* stackpointer (so the pipelined body reasoning applies verbatim), and every *)
(* invariant carries the saved-x30 slot (sp+88) so the epilogue restore + ret *)
(* provably returns to returnaddress.  Prologue/epilogue are byte-identical to *)
(* the clean kernels (frame 224, x30 at sp+88); the setup leg is pc..0xa0 =    *)
(* 11 (prologue) + 29 (setup) = 40 steps; the epilogue pc+0xb68 -> ret is 17.  *)
(* ------------------------------------------------------------------------- *)

let MEM_PRESERVE : tactic = ASM_REWRITE_TAC[] THEN NO_TAC;;

let LEAF1_SUB : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON ORELSE MEM_PRESERVE)
    else (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC));;
let CLOSE_SUB : tactic = REPEAT CONJ_TAC THEN LEAF1_SUB;;

let LEAF2_SUB : tactic =
  W(fun (asl,w) ->
    if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
    else if is_branch_goal w then BRANCH_RECON
    else if can dest_eq w then (WSUB_ARITH ORELSE ADDR_RECON ORELSE CTR_RECON ORELSE MEM_PRESERVE)
    else (DEABBR THEN DISCHARGE_SAFE_ROBUST));;
let CLOSE_R2_SUB : tactic = REPEAT CONJ_TAC THEN LEAF2_SUB;;

(* mem@88 x30-save-slot preservation conjunct, appended to every invariant.    *)
let m88 = `read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress`;;

let AES_GCM_DEC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_KEEP_HTABLE_SWP_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes_gcm_dec_kernel_x4_scalar_iv_mem_late_tag_keep_htable_swp_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
      (len_bits:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epi in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
        (APPEND
           (if val len_bits DIV 128 MOD 4 = 0 then
              f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
            else
              APPEND
                (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
                (APPEND
                  (ENUMERATEL (val len_bits DIV 128 MOD 4)
                    (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                  (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
           (APPEND
             (if val len_bits DIV 128 DIV 4 = 0 then
                f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else if val len_bits DIV 128 DIV 4 = 1 then
                f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else if val len_bits DIV 128 DIV 4 = 2 then
                f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else
                APPEND
                  (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2)
                      (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                    (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
             (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 224 THEN GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN
      SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  STRIP_TAC THEN

  (*** Epilogue split at pc+0xb68.  The epilogue stores the tag (str q30,[x3]) and the counter    ***)
  (*** (str w14,[x4,#12]), so X3=tag_p and X4=ivec_p must be carried to prove those stores do not  ***)
  (*** hit code; X15 holds the value moved into x0 (mov x0,x15) but is not a store address.        ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb68`
   `\s. read X3 s = tag_p /\ read X4 s = ivec_p /\ read SP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
  CONJ_TAC THENL
   [(*** REGION A: pc -> pc+0xb68 (prologue + pipelined body). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa0`
     `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
          read X2 s = word_add out_p (word (64 * loop_count)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word loop_remain /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    CONJ_TAC THENL
     [(*** setup incl prologue: pc -> 0xa0 = 40 steps. ***)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa0`
       `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
            read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
            read X1 s = word loop_count /\ read X16 s = word loop_remain /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      CONJ_TAC THENL [SAFE_SIM (1--40) THEN CLOSE_SUB; ALL_TAC] THEN

      ASM_CASES_TAC `loop_count = 0` THENL
       [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFN0 `loop_count:num` THEN
      ASM_CASES_TAC `loop_count = 1` THENL
       [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--161) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `1` THEN
      ASM_CASES_TAC `loop_count = 2` THENL
       [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--322) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `2` THEN
      SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x294` `pc + 0x514`
       `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
              read X2 s = word_add out_p (word (64 * i)) /\
              read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
              read SP s = stackpointer /\ read X16 s = word loop_remain /\
              read X1 s = word (loop_count - 2 - i) /\
              read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        BEQ_NZ `1` THEN SAFE_SIM (1--125) THEN
        BEQ_NZ `2` THEN
        REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
          else if is_branch_goal w then (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE)
          else if can dest_eq w &&
                  (let l,_ = dest_eq w in
                   can (find_term (fun t -> t = `word_sub (word loop_count:int64) (word 2)`)) l)
          then (REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
                ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 2 <= loop_count`])
          else (ADDR_RECON ORELSE MEM_PRESERVE));
        REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SAFE_SIM (1--160) THEN CLOSE_R2_SUB;
        SAFE_SIM (1--197) THEN REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
          else (DRAIN_ADDR ORELSE MEM_PRESERVE))];

      ALL_TAC] THEN
    (*** TAIL region of the body: pc+0xaa0 -> pc+0xb68. ***)
    ASM_CASES_TAC `loop_remain = 0` THENL
     [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--1) THEN CLOSE_R2_SUB; ALL_TAC] THEN
    REDUCE_IFN0 `loop_remain:num` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb68`
     `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
            read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word (loop_remain - i) /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SAFE_SIM (1--1) THEN CLOSE_R2_SUB;
      ALL_TAC;
      REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2_SUB] THEN
    REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SAFE_SIM (1--49) THEN CLOSE_R2_SUB;

    (*** REGION B: pc+0xb68 -> returnaddress (epilogue: mov x0,x15; rev64/str tag; rev/str ctr;   ***)
    (*** then 11 ldp; add sp; ret = 17 steps).                                                     ***)
    SAFE_SIM (1--17) THEN REPEAT CONJ_TAC THEN
    (MEM_PRESERVE ORELSE DISCHARGE_SAFETY_PROPERTY_TAC)] );;


(* ------------------------------------------------------------------------- *)
(* Certify that the whole development above is axiom-free (only the three     *)
(* basic HOL Light axioms INFINITY_AX / SELECT_AX / ETA_AX are permitted).   *)
(* ------------------------------------------------------------------------- *)

check_axioms();;
