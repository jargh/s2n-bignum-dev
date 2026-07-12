(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM encryption kernel.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail.o";; *)

let aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc =
  define_from_elf "aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail.o";;

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc;;

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

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

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

let SUBWORD_WORD_LO32 = prove
 (`word_subword (word n:int64) (0,32):int32 = word n`,
  SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_64; ARITH_RULE `0 + 32 <= 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* Given the initial IV halves (join = reversed ctr_block for counter 2), the *)
(* loop-built block for any counter value equals the reversed ctr_block.      *)

let CTR_BLOCK_BUILD_V = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 =
     word_reversefields 8 (ctr_block nonce 2)
   ==> word_join
        (word_or (word_zx ((word_zx ivhi):int32):int64)
                 (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
        ivlo :int128
       = word_reversefields 8 (ctr_block nonce cval)`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
  REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

let JOIN_SUBWORD_ID = prove
 (`word_join (word_subword (w:int128) (64,64):int64)
             (word_subword w (0,64):int64):int128 = w`,
  CONV_TAC WORD_BLAST);;

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

(* Setup slot-persistence: the four setup "stp x11,x12,[sp,#OFF]" stores leave        *)
(* bytes64@OFF = ivlo and bytes64@OFF+8 = ivhi; splitting the latter to bytes32 gives  *)
(* the nonce mid word word_subword ivhi (0,32).  These two lemmas rewrite the invariant *)
(* slot RHSs (subwords of the reversed ctr_block) back to ivlo / word_subword ivhi so   *)
(* ASM_REWRITE closes them against the (split) store facts.                            *)
let SLOT_LO = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce 2)
   ==> word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 = ivlo`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

let SLOT_MID = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce 2)
   ==> word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 =
       word_subword (ivhi:int64) (0,32):int32`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* Closed form: with X11/X12 written as (counter-free) subwords of the reversed
   ctr_block for the canonical counter 2, the loop-built block for counter cval
   equals the reversed ctr_block for cval.  This is what the loop body invokes. *)

let CTR_BLOCK_BUILD_CLOSED = prove
 (`word_join
        (word_or
          (word_zx ((word_zx (word_subword
              (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64)):int32):int64)
          (word_shl (word_zx (word_bytereverse (word cval:int32)):int64) 32))
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
        :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  MP_TAC(INST
    [`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64`,
       `ivhi:int64`;
     `word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64`,
       `ivlo:int64`]
    CTR_BLOCK_BUILD_V) THEN
  REWRITE_TAC[JOIN_SUBWORD_ID]);;

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

(* Epilogue byte-splice: the final "str w14,[x4,#12]" overwrites only the top 4 bytes *)
(* of the ivec (the byte-reversed counter word); the low 12 bytes keep their initial  *)
(* value (the reversed nonce from ctr_block nonce 2).  Recombining gives the reversed *)
(* ctr_block for the final counter value.                                             *)

let EPI_SPLICE = prove
 (`word_join (word_bytereverse (word cval:int32):int32)
             (word_subword (word_reversefields 8 (ctr_block nonce 2):int128)
                           (0,96):96 word)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* Same splice phrased for the 64/64 then 32/32 decomposition of the 128-bit ivec    *)
(* read (which is how READ_MEMORY_BYTESIZED_SPLIT breaks it): the stored counter word *)
(* is the top 32 bits of the high 64-bit half, the rest is the unchanged nonce.       *)

let EPI_SPLICE_64 = prove
 (`word_join
      (word_join (word_bytereverse (word cval:int32):int32)
                 (word_subword (word_reversefields 8 (ctr_block nonce 2):int128)
                               (64,32):int32):int64)
      (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* After the 32-bit-cell split (and collapsing the word_zx conversion chain with     *)
(* ZX_COUNTER_UD), the counter cell (offset 12) is word_bytereverse(word c), which    *)
(* equals the top 32 bits of the reversed ctr_block.                                  *)

let COUNTER_CHUNK = prove
 (`word_zx (word_zx (word_bytereverse
     (word_zx (word_zx (word (c:num):int32):int64):int32):int32):int64):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (96,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* The low three 32-bit cells of the reversed ivec (the nonce) are independent of the *)
(* counter value, so they still hold their initial (counter-2) contents.              *)

let NONCE_CHUNK = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,32):int32 /\
   word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (32,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (32,32):int32 /\
   word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* This mem2 variant assembles the counter block on the STACK with a mixed-        *)
(* granularity trick: at setup "stp x11,x12,[sp,#OFF]" writes the whole reversed    *)
(* nonce+ctr (two 64-bit halves) to four slots (OFF = 160/176/192/208); each block  *)
(* then overwrites ONLY the 4-byte counter word via "str w14,[sp,#OFF+12]" and       *)
(* reloads the whole 128 bits with "ldr q0,[sp,#OFF]".  So the reloaded Q0 is         *)
(*   word_join (word_join <ctrword> <nonce-mid-32>) <nonce-low-64>                   *)
(* with nonce-low-64 = subword(rev8(ctr_block nonce 2))(0,64), nonce-mid-32 =         *)
(* subword(...)(64,32), and ctrword the W-register rev nest around word cval (the     *)
(* two 32<->64 conversions from the str w14 / bytereverse are NOT collapsed by        *)
(* ZX_COUNTER_UD because word_bytereverse sits between them, so the lemma carries the  *)
(* full nest).                                                                        *)

let CTR_BLOCK_BUILD_INSERT = prove
 (`word_join
     (word_join
        (word_zx (word_zx (word_bytereverse
           (word_zx (word_zx (word cval:int32):int32):int32):int32):int32):int32)
        (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* The same reconstruction but for the COLLAPSED counter form the goal actually       *)
(* presents once WORD_SIMPLE_SUBWORD_CONV has run over the AES-embedded copies of the  *)
(* counter block: the ctrword's 32<->64 conversion nest is gone, leaving the plain     *)
(* word_bytereverse (word cval:int32).  Applied (after GSYM WORD_ADD folds the counter *)
(* increment word_add(word(4*i))(word N) -> word(4*i+N)) alongside                     *)
(* WORD_REVERSEFIELDS_REVERSEFIELDS just before AES_CTR_BLOCK_RECONSTRUCT.             *)
let CTR_BLOCK_BUILD_INSERT_PLAIN = prove
 (`word_join
     (word_join (word_bytereverse (word cval:int32):int32)
                (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32):int64)
     (word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64)
     :int128
   = word_reversefields 8 (ctr_block nonce cval)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC BITBLAST_RULE);;

(* Reconstruct the 128-bit counter-slot read from its three surviving pieces:      *)
(* the setup stp leaves bytes64@OFF (nonce low 8 bytes) and, once the setup high    *)
(* half is split, bytes32@OFF+8 (nonce mid 4 bytes); the per-block "str w14" writes *)
(* bytes32@OFF+12 (counter word).  This tactic, spliced AFTER the str w14 step and  *)
(* BEFORE the "ldr q0", rebuilds read(bytes128 sp+OFF) sN = word_join (word_join     *)
(* <bytes32@OFF+12> <bytes32@OFF+8>) <bytes64@OFF> so the load resolves.  (Two-level *)
(* split: bytes128 -> bytes64@OFF+8 ++ bytes64@OFF, then bytes64@OFF+8 -> the two     *)
(* bytes32 halves.)                                                                 *)
let MERGE_CTR128_TAC off sname =
  let woff n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                       mk_comb(`word:num->int64`,mk_small_numeral n)) in
  MP_TAC(ISPECL [`memory`; woff off; mk_var(sname,`:armstate`)]
           (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  MP_TAC(ISPECL [`memory`; woff (off + 8); mk_var(sname,`:armstate`)]
           (el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC;;

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

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc /\
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
      (\s. read PC s = word (pc + 0x75c) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
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
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC] THEN

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

  ENSURES_SEQUENCE_TAC `pc + 0x98`
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
        read Q7 s = word 13979173243358019584 /\
        read (memory :> bytes64 (word_add stackpointer (word 160))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 168))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 176))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 184))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 200))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 216))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word 2:int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
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
    ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC (1--27) THEN
    (*** Split each of the four slots' high 64-bit store (bytes64@OFF+8 = ivhi)     ***)
    (*** into two bytes32 (OFF+8 = nonce mid, OFF+12 = initial ctr) so the nonce     ***)
    (*** mid word survives for the per-block counter merges.                         ***)
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(fun t ->
      if is_eq t && free_in `stackpointer:int64` (lhs t) &&
         can (find_term (fun u -> is_const u && fst(dest_const u) = "bytes64")) (lhs t) &&
         (can (find_term (fun u -> u = `168`)) (lhs t) ||
          can (find_term (fun u -> u = `184`)) (lhs t) ||
          can (find_term (fun u -> u = `200`)) (lhs t) ||
          can (find_term (fun u -> u = `216`)) (lhs t))
      then READ_MEMORY_SPLIT_CONV 1 t else failwith ""))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Name the IV-halves join relation for reuse in the counter conjuncts.    ***)
    (*** Keep ivlo/ivhi UNsubstituted so the ivec recombination still closes.    ***)
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
             (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    (*** Rewrite the slot-persistence RHSs (subwords of the reversed ctr_block)   ***)
    (*** to ivlo / word_subword ivhi so ASM_REWRITE closes them against the        ***)
    (*** (split) store facts.                                                      ***)
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then REWRITE_TAC[MATCH_MP SLOT_LO th; MATCH_MP SLOT_MID th] else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ivec memory read: recombine the two abbreviated halves ***)
      GEN_REWRITE_TAC LAND_CONV
       [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      (*** X11 has no branch here: the SLOT_LO rewrite above turns the X11    ***)
      (*** conjunct RHS word_subword(rev8(ctr_block nonce 2))(0,64) into ivlo, ***)
      (*** which ASM_REWRITE_TAC discharges against the ldp x11,x12 store, so  ***)
      (*** only 8 conjuncts remain (X12 survives - its (64,64) subword is not  ***)
      (*** matched by SLOT_LO/SLOT_MID).                                       ***)
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

  ENSURES_SEQUENCE_TAC `pc + 0x324`
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
        read Q7 s = word 13979173243358019584 /\
        read (memory :> bytes64 (word_add stackpointer (word 160))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 168))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 176))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 184))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 200))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 216))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word 0 /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q30 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                            (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; CONJUNCT1 LT] THEN
      REWRITE_TAC[list_of_seq; nist_ghash] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN

    (**** Loop setup for the main unrolled loop ***)

    ENSURES_WHILE_UP_TAC `loop_count:num` `pc + 0x09c` `pc + 0x320`
      `\i s.
        read X0  s = word_add in_p  (word (64 * i)) /\
        read X2  s = word_add out_p (word (64 * i)) /\
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
        read (memory :> bytes64 (word_add stackpointer (word 160))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 168))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 176))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 184))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 200))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read (memory :> bytes32 (word_add stackpointer (word 216))) s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (64,32):int32 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * i + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word(loop_count - i) /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q30 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * i
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0; LT;
                  list_of_seq; nist_ghash];

      (**** Main loop invariant (main unrolled loop) ****)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * i)))) s0 =
        inblock (4 * i) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 16)))) s0 =
        inblock (4 * i + 1) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 32)))) s0 =
        inblock (4 * i + 2) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 48)))) s0 =
        inblock (4 * i + 3)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE
         `64 * i + 16 = 16 * (4 * i + 1) /\
          64 * i + 32 = 16 * (4 * i + 2) /\
          64 * i + 48 = 16 * (4 * i + 3)`] THEN
        REWRITE_TAC[ARITH_RULE `64 * a = 16 * 4 * a`] THEN
        REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      (*** Step through the four unrolled blocks.  late_tag reverse-schedules the  ***)
      (*** blocks: block b computes counter word 4*i+2+(3-b) ("add w14,w13,#(3-b)"  ***)
      (*** then "rev w14,w14"), stores it to "str w14,[sp,#OFF+12]" and reloads     ***)
      (*** "ldr q0,[sp,#OFF]" with OFF descending 208/192/176/160 for b=0..3        ***)
      (*** (output slot 16*(3-b)).  The counter-word str is at steps 7/40/79/115    ***)
      (*** and the reload one step later; splice MERGE_CTR128_TAC after each str.    ***)
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (1--7) THEN
      MERGE_CTR128_TAC 208 "s7" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (8--40) THEN
      MERGE_CTR128_TAC 192 "s40" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (41--79) THEN
      MERGE_CTR128_TAC 176 "s79" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (80--115) THEN
      MERGE_CTR128_TAC 160 "s115" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (116--161) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                              j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/
                              j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
      (*** Scalar counter reconstruction: collapse the W-register up/down-convert  ***)
      (*** and increment chain to a single word on the counter value, then rebuild ***)
      (*** rev8(ctr_block ...) from the FMOV-assembled word_insert.                 ***)
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
      DISCARD_STATE_TAC "s161" THEN
      REWRITE_TAC[ADD_ASSOC; ARITH] THEN
      (*** Counter reconstruction (mem2 3-way-merge specific): the zx-nested          ***)
      (*** CTR_BLOCK_BUILD_INSERT applied earlier never fires on the AES-embedded      ***)
      (*** copies of the counter block; WORD_SIMPLE_SUBWORD_CONV collapses their       ***)
      (*** counter word to the plain form word_bytereverse(word_add(word(4*i))(word N)).***)
      (*** Collapse the AES-embedded subwords first, then fold the increment with      ***)
      (*** GSYM WORD_ADD, collapse the three-way counter join with the plain-form      ***)
      (*** lemma, kill the double reversefields, and then run the cipher/NIST          ***)
      (*** reconstruction chain ONCE (running it twice - before and after the counter  ***)
      (*** is reconstructed - bloats the term and makes the tag BITBLAST intractable). ***)
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT_PLAIN] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
      REWRITE_TAC[GSYM cipher_block] THEN
      REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
      SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
                   (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i)))`;
        `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * i)`;
        `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * i + 1)`;
        `cipherblock_2 = nist_cipher_block nonce rk inblock (4 * i + 2)`;
        `cipherblock_3 = nist_cipher_block nonce rk inblock (4 * i + 3)`;
        `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
        `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
        `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
        `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
      TRANS_TAC EQ_TRANS
       `polyval_reduce_prop3
            (word_xor
            (word_pmul (cipherblock_3:int128) (h0:int128))
            (word_xor
            (word_pmul (cipherblock_2:int128) (h1:int128))
            (word_xor
            (word_pmul (cipherblock_1:int128) (h2:int128))
            (word_pmul (word_xor (sofar:int128) cipherblock_0)
                       (h3:int128)))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
        REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[karatsuba_mid] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
        ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
         `word_pmul (word_xor a b) (word_xor c d) =
          word_pmul (word_xor b a) (word_xor c d)`] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                     `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                     `sofar:int128`; `cipherblock_0:int128`]
                    GHASH_POLYVAL_ACC_BATCHED) THEN
      REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
      REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
      REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[APPEND] THEN
      REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];

      (**** Trivial loop-back goal (main unrolled loop) ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [1] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ];

      (*** Trivial bridge between the two loops ***)

      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [1] THEN
      REWRITE_TAC[SUB_REFL]];

    ALL_TAC] THEN

  SUBGOAL_THEN `loop_remain < 4` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `nblocks MOD 4 = loop_remain`) (concl th)
       then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Tail: split at Lend (pc+0x748).  Segment A runs the unrolled remainder     ***)
  (*** blocks (Lremainder_1/2/3, selected by cmp/b.eq) which reconstruct the       ***)
  (*** clean Lend invariant (accumulator Q30 = byteswap128(nist_ghash ...), scalar ***)
  (*** counter X13 = word_zx(word(4*loop_count+loop_remain+2))); segment B is the  ***)
  (*** shared writeback (rev64 v30 -> str q30,[x3] ; rev w14,w13 -> str w14,[x4,   ***)
  (*** #12]) reaching pc+0x75c.  Each remainder block reloads the H-table and       ***)
  (*** assembles its counter on the stack, so we expand htable_mem_4 and splice     ***)
  (*** MERGE_CTR128_TAC (3-way) at the descending counter slots.                    ***)
  ENSURES_SEQUENCE_TAC `pc + 0x748`
   `\s. read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read X13 s = word_zx (word (4 * loop_count + loop_remain + 2):int32):int64 /\
        read Q30 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                            (4 * loop_count + loop_remain))) /\
        (!j. j < 4 * loop_count + loop_remain
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(*** Segment A: remainder blocks (pc+0x324 -> pc+0x748) ***)
    FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (DISJ_CASES_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)) o MATCH_MP (ARITH_RULE
      `r < 4 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`)) THENL
     [(*** loop_remain = 0: dispatch b Lend (7 steps, no blocks) ***)
      ENSURES_INIT_TAC "s0" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; CONJUNCT1 LT] THEN
      REWRITE_TAC[list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[];

      (*** loop_remain = 1: one block (Lremainder_1), body 48 steps to pc+0x748 ***)
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * loop_count)))) s0 =
        inblock (4 * loop_count)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a = 16 * (4 * a)`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (1--12) THEN
      MERGE_CTR128_TAC 160 "s12" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (13--54) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < a + 1 <=> j < a \/ j = a`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[ARITH_RULE `16 * 4 * a = 64 * a`] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      DISCARD_STATE_TAC "s54" THEN
      REWRITE_TAC[ADD_ASSOC; ARITH] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT_PLAIN] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
      REWRITE_TAC[GSYM cipher_block] THEN
      REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
      SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
                   (list_of_seq (nist_cipher_block nonce rk inblock)
                                (4 * loop_count)))`;
        `cipherblock =
          nist_cipher_block nonce rk inblock (4 * loop_count)`;
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
        REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM polyval_dot] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
      REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
      REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
      REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND;
                  NIST_GHASH_CONS; nist_ghash] THEN
      ASM_REWRITE_TAC[];

      (*** loop_remain = 2: two blocks (Lremainder_2), body 85 steps to pc+0x748 ***)
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * loop_count)))) s0 =
        inblock (4 * loop_count) /\
        read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16)))) s0 =
        inblock (4 * loop_count + 1)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a = 16 * (4 * a) /\
                               64 * a + 16 = 16 * (4 * a + 1)`] THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (1--11) THEN
      MERGE_CTR128_TAC 176 "s11" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (12--44) THEN
      MERGE_CTR128_TAC 160 "s44" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (45--90) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < a + 2 <=> j < a \/ j = a \/ j = a + 1`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 4 * a = 64 * a`] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      DISCARD_STATE_TAC "s90" THEN
      REWRITE_TAC[ADD_ASSOC; ARITH] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT_PLAIN] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
      REWRITE_TAC[GSYM cipher_block] THEN
      REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
      SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
                   (list_of_seq (nist_cipher_block nonce rk inblock)
                                (4 * loop_count)))`;
        `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * loop_count)`;
        `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * loop_count + 1)`;
        `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
        `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`] THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
      TRANS_TAC EQ_TRANS
       `polyval_reduce_prop3
            (word_xor
            (word_pmul (cipherblock_1:int128) (h0:int128))
            (word_pmul (word_xor (sofar:int128) cipherblock_0)
                       (h1:int128)))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
        REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[karatsuba_mid] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
        ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
         `word_pmul (word_xor a b) (word_xor c d) =
          word_pmul (word_xor b a) (word_xor c d)`] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXPAND_TAC ["ks"; "ks'"] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                     `[cipherblock_1]:(int128)list`;
                     `sofar:int128`; `cipherblock_0:int128`]
                    GHASH_POLYVAL_ACC_BATCHED) THEN
      REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
      REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
      REWRITE_TAC[ARITH_RULE `4 * a + 2 = SUC(SUC(4 * a))`] THEN
      REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[APPEND] THEN
      REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];

      (*** loop_remain = 3: three blocks (Lremainder_3), body 123 steps to pc+0x748 ***)
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * loop_count)))) s0 =
        inblock (4 * loop_count) /\
        read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16)))) s0 =
        inblock (4 * loop_count + 1) /\
        read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 32)))) s0 =
        inblock (4 * loop_count + 2)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a = 16 * (4 * a) /\
                               64 * a + 16 = 16 * (4 * a + 1) /\
                               64 * a + 32 = 16 * (4 * a + 2)`] THEN
        REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (1--9) THEN
      MERGE_CTR128_TAC 192 "s9" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (10--42) THEN
      MERGE_CTR128_TAC 176 "s42" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (43--80) THEN
      MERGE_CTR128_TAC 160 "s80" THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
       (81--126) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE
        `j < a + 3 <=> j < a \/ j = a \/ j = a + 1 \/ j = a + 2`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 4 * a = 64 * a`] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      DISCARD_STATE_TAC "s126" THEN
      REWRITE_TAC[ADD_ASSOC; ARITH] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[CTR_BLOCK_BUILD_INSERT_PLAIN] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
      REWRITE_TAC[GSYM cipher_block] THEN
      REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
      SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
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
                   (list_of_seq (nist_cipher_block nonce rk inblock)
                                (4 * loop_count)))`;
        `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * loop_count)`;
        `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * loop_count + 1)`;
        `cipherblock_2 = nist_cipher_block nonce rk inblock (4 * loop_count + 2)`;
        `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
        `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
        `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`] THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
      TRANS_TAC EQ_TRANS
       `polyval_reduce_prop3
            (word_xor
            (word_pmul (cipherblock_2:int128) (h0:int128))
            (word_xor
            (word_pmul (cipherblock_1:int128) (h1:int128))
            (word_pmul (word_xor (sofar:int128) cipherblock_0)
                       (h2:int128))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
        REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[karatsuba_mid] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
        ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
         `word_pmul (word_xor a b) (word_xor c d) =
          word_pmul (word_xor b a) (word_xor c d)`] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                     `[cipherblock_1;cipherblock_2]:(int128)list`;
                     `sofar:int128`; `cipherblock_0:int128`]
                    GHASH_POLYVAL_ACC_BATCHED) THEN
      REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
      REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
      REWRITE_TAC[ARITH_RULE `4 * a + 3 = SUC(SUC(SUC(4 * a)))`] THEN
      REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[APPEND] THEN
      REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]];

    (*** Segment B: shared scalar writeback (pc+0x748 -> pc+0x75c), 6 steps.       ***)
    (*** Q30 is the clean accumulator, X13 the final counter word; str q30 -> tag  ***)
    (*** and str w14 (=rev of counter) -> ivec[12,16), nonce low-12 unchanged.     ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] `nblocks MOD 4 = loop_remain`) (concl th)
         then MP_TAC th else NO_TAC) THEN
      MP_TAC(SPECL [`nblocks:num`; `4`] DIVISION) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
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

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_scalar_iv_mem2_late_tag_fast_tail_mc /\
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
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  REWRITE_TAC[fst AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_EXEC; htable_mem_4]
          AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM2_LATE_TAG_FAST_TAIL_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;
