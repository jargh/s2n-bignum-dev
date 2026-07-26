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

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk.o";; *)

let aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_mc =
  define_from_elf "aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk.o";;

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_mc;;

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

(* Split a 128-bit input-block memory read into two 64-bit halves whose addresses  *)
(* are folded back to the canonical "in_p + word(off)" form.  The scalar_rk final  *)
(* round loads each input block as scalars via "ldp x22,x23,[x0,#K]", i.e. it reads *)
(* the block's two 64-bit halves at x0+K and x0+K+8.  READ_MEMORY_SPLIT_CONV emits  *)
(* the high half at address (in_p + word off) + word 8; the simulator's memory      *)
(* lookup will not match that against x0+K+8 unless we renormalise it to            *)
(* in_p + word(off+8).  NORMALIZE_RELATIVE_ADDRESS_CONV reassociates and GSYM       *)
(* ADD_ASSOC + NUM_ADD_CONV fold the numeric offset.                                *)
let SPLIT_INPUT_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  ONCE_DEPTH_CONV(REWR_CONV(GSYM ADD_ASSOC)) THENC
  ONCE_DEPTH_CONV NUM_ADD_CONV;;

(* Tail-loop variant of the input split.  The tail block is loaded by the         *)
(* POST-INDEXED "ldp x22,x23,[x0],#16": the ARM model reads the second register    *)
(* x23 from address in_p + word((64*loop_count + 16*i) + 8) — the "+ 8" stays a    *)
(* separate num-level summand because the block offset (64*loop_count + 16*i) has   *)
(* a symbolic i, so NUM_ADD_CONV cannot fold it.  The plain SPLIT + NORMALISE (no   *)
(* ADD_ASSOC/NUM fold) reproduces exactly that address form, letting the           *)
(* post-indexed load resolve x23 (offset-mode loads in the main loop DO fold, hence *)
(* the two different conversions).                                                 *)
let SPLIT_INPUT_TAIL_CONV =
  READ_MEMORY_SPLIT_CONV 1 THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV;;

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

(* In the scalar_rk variant the final AES round key (EL 10) is XORed in scalar    *)
(* registers X20/X21 into the input block halves, and the block ciphertext is     *)
(* word_xor (word_join <input_hi ^ key10_hi> <input_lo ^ key10_lo>) (9-round Q0). *)
(* This lemma rewrites that scalar-built form into the word_xor <9round>           *)
(* (word_xor rk10 inblock) shape that XOR_AES128_CIPHER_RECONSTRUCT consumes,      *)
(* with rk10 = word_reversefields 8 (EL 10 rk) and inblock = word_join of the      *)
(* input halves.  Both operand orders of the outer word_xor are covered: the       *)
(* ciphertext-output copy keeps the (word_join ... ) nineround order from the       *)
(* "eor v0,v29,v0", while the GHASH-accumulated copy has the operands commuted by   *)
(* the intervening normalisation, so we need both orientations.                     *)
let SCALAR_RK_RECONSTRUCT = prove
 (`(word_xor
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
     (nineround:int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb)) /\
   (word_xor
     (nineround:int128)
     (word_join
        (word_xor (word_subword (inb:int128) (64,64):int64)
                  (word_subword (word_reversefields 8 (rk10:int128)) (64,64):int64))
        (word_xor (word_subword inb (0,64):int64)
                  (word_subword (word_reversefields 8 rk10) (0,64):int64)) :int128)
    = word_xor nineround (word_xor (word_reversefields 8 rk10) inb))`,
  CONJ_TAC THEN CONV_TAC BITBLAST_RULE);;

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
(* save instructions) and ends at pc + 0x448 (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xe0 adjustment, i.e.    *)
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


(* ========================================================================= *)
(* SWP DE-INTERLEAVED KERNEL (B;A rotation of the clean loop).               *)
(* Proof by A/B-rotation: invariant asserted at the CLEAN seam 0x354 (after  *)
(* B, before A), where the GHASH tag is SETTLED and no partial AES is in     *)
(* flight -- so the invariant is clean-C's settled loop invariant, index-    *)
(* shifted. Loop plumbing = bignum_inv_p25519 pattern: ENSURES_WHILE with    *)
(* pc1=pc2=0x354 interior to the body; physical back-branch cbnz@0x4b0->0x1ec *)
(* buried inside the body leg. The tail (0x61c..0x710) replays clean-C's     *)
(* tail (its 0x354..0x448) shifted by +0x2c8.                                *)
(* ========================================================================= *)

let aes_gcm_deint_mc =
  define_from_elf "aes_gcm_deint_mc"
    "arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint.o";;

let AES_GCM_DEINT_EXEC = ARM_MK_EXEC_RULE aes_gcm_deint_mc;;

(* Per-step subword normalizer that leaves quantified (forall j) region-invariant
   assumptions untouched, so the input/output block foralls thread across the body
   instead of being mangled/discarded by the normalization. *)
let SUBWORD_NONFORALL =
  RULE_ASSUM_TAC(fun th ->
    if is_forall (concl th) then th
    else CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th);;

(* ------------------------------------------------------------------------- *)
(* Tail single-block loop (Lloop_1x, pc+0x61c..pc+0x710): the SWP-scheduled   *)
(* remainder loop, run once per leftover block (loop_remain = nblocks MOD 4). *)
(* Precondition = the "bridge" state at pc+0x61c (= clean-C's pc+0x354         *)
(* main-done state): tag settled = ghash(4*loop_count), counter = 4*loop_count *)
(* +2, first 4*loop_count output blocks stored.  Deint's tail is SLOTHY-       *)
(* scheduled (not clean-C's schedule), so the per-block recipe is re-indexed:  *)
(* MERGE_CTR128_TAC at the STORE states (s5, s28) feeding each vector reload    *)
(* (else the reload stays an old-state ref and the AES/GHASH chain cascades to *)
(* erasure); the output-region forall is discharged at ENSURES_FINAL_STATE     *)
(* while the MAYCHANGE frame is live (before DISCARD_STATE).                    *)
(* ------------------------------------------------------------------------- *)

let DEINT_TAIL = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
           read X2 s = word_add out_p (word (64 * loop_count)) /\
           read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
           read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
           read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
           read X16 s = word loop_remain /\
           read Q30 s = byteswap128
               (nist_ghash (aes128_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
           (!j. j < 4 * loop_count
                ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** loop_remain = 0: no tail iterations, just the finalize (ivec/tag writeback) ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  (*** loop_remain >= 1: tail loop via ENSURES_WHILE (0x62c head, 0x6f8 back-edge) ***)
  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6f8`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
      read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
      read X12 s = word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + 2):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
      read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [(*** base case: bridge 0x61c -> 0x62c, i=0 ***)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--3) THEN
    ARM_STEPS_TAC AES_GCM_DEINT_EXEC [4] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),Var("s4",_))),
             Comb(Comb(Comb(Const("COND",_),_),_),_)) ->
          ASSUME_TAC(REWRITE_RULE[ASSUME `val(word loop_remain:int64) = loop_remain`;
                                  ASSUME `~(loop_remain = 0)`; COND_CLAUSES] th)
      | _ -> NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** loop body: 0x62c -> 0x6f8, one block; Inv(i) -> Inv(i+1) ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
      check (fun th -> let c = concl th in
        is_eq c && free_in `in_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
    (*** store-in-region bound: needed so the output store's write-preservation fires ***)
    SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`i < loop_remain`; `nblocks MOD 4 = loop_remain`; `nblocks DIV 4 = loop_count`] THEN
      ARITH_TAC; ALL_TAC] THEN
    (*** step the body; MERGE at STORE states s5 (counter) and s28 (scalar_rk round-trip) ***)
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN SUBWORD_NONFORALL) (1--5) THEN
    MERGE_CTR128_TAC 160 "s5" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN SUBWORD_NONFORALL) (6--28) THEN
    MERGE_CTR128_TAC 160 "s28" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN SUBWORD_NONFORALL) (29--51) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** discharge the output-region forall FIRST, while the MAYCHANGE frame is live ***)
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    (*** counter + scalar_rk + AES-CTR reconstruction ***)
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s51" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
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
    (*** fold the spelled-out round-key list back to `rk` (deint's AES reconstruction     ***)
    (*** re-expands it), using the lemma's first hypothesis [EL 0 rk;..] = rk.             ***)
    FIRST_ASSUM(fun th -> if can (term_match []
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    (*** the goal is a conjunction of pointer/counter eqs (WORD_RULE-closable) followed by  ***)
    (*** the GHASH tag equation; peel the WORD_RULE ones, then settle the tag.              ***)
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i)))`;
      `cipherblock = nist_cipher_block nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** trivial loop-back: 0x6f8 test taken.  The back-branch test is                ***)
    (*** cbnz on X16 = word(loop_remain - i); ARM_SIM leaves the residual PC as        ***)
    (*** (if ~(word loop_remain = word i) then loop-top else exit) = loop-top, so we   ***)
    (*** must show ~(word loop_remain = word i).  Unlike the counter-decrement form,   ***)
    (*** this compares loop_remain and i directly, so we need val(word loop_remain) =  ***)
    (*** loop_remain (from loop_remain = nblocks MOD 4 < 4 < 2^64) before GSYM VAL_EQ. ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES_GCM_DEINT_EXEC [1] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC;

    (*** finalize: 0x6f8 test not taken -> ivec/tag writeback -> 0x710 ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
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
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* Fill+drain for a SINGLE group (loop_count = 1): A_0 (group-0 producer)     *)
(* then reduce_last as the drain, landing directly on the tail-entry bridge   *)
(* pc+0x61c with the tag settled to ghash of the first 4 blocks.  This is one *)
(* of the three near-identical seam sub-proofs; here the loop is absent so it *)
(* is a straight-line block.  NB: with loop_count = 1 the block counters are  *)
(* the LITERALS 2,3,4,5 (so AES_CTR_BLOCK_RECONSTRUCT is used at its i=0       *)
(* specialization) and the GHASH accumulator is still tag0 (empty history).   *)
(* ------------------------------------------------------------------------- *)

let LEG1_LC1 = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       loop_count = 1 /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  (*** derive the 4 group-0 input blocks from the nblocks-forall (nblocks >= 4) ***)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--12) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (38--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `loop_count = 1` SUBST_ALL_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** loop_count=1 => the 4 blocks have LITERAL counters 2,3,4,5, so the symbolic     ***)
  (*** AES_CTR_BLOCK_RECONSTRUCT (pattern i+2) cannot fire; use its i=0 specialization. ***)
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
               (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST; ALL_TAC]) THEN
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
  (*** loop_count=1 => the GHASH accumulator is still tag0 (nist_ghash h tag0 [] = tag0), ***)
  (*** so there is no `sofar` to abbreviate: block 0 is word_xor tag0 cipherblock_0.       ***)
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock 3`;
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
        (word_pmul (word_xor (tag0:int128) cipherblock_0)
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
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;

(* ==== SWP deint loop_count>=2 leg: FILL + DRAIN(gen) + LEG1_LC2 ==== *)

let FILL_LEG_LC2 = prove
 (`
!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       2 <= loop_count /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x354) /\
           read X0 s = word_add in_p (word (64 * 1)) /\
        read X2 s = word_add out_p (word (64 * 1)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * 1 + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word (loop_count - 1) /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * 1))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * 1
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
      UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC AES_GCM_DEINT_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word loop_count:int64) = loop_count`;
                             ASSUME `~(loop_count = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (2--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  ARM_STEPS_TAC AES_GCM_DEINT_EXEC [12] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (38--88) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC AES_GCM_DEINT_EXEC [89] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1`;
                             ASSUME `~(loop_count - 1 = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (90--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** peel pointer/counter conjuncts; the X1 conjunct word_sub(word loop_count)(word 1) =
   *** word(loop_count-1) needs the no-underflow fact (1<=loop_count), so give the peel a
   *** WORD_SUB branch guarded by ASM_ARITH. ***)
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST ORELSE
    (CONV_TAC SYM_CONV THEN
     ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `2 <= loop_count ==> 1 <= loop_count`]);
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;

(* Loop invariant at the A|B seam (0x354). *)
let inv_tm = `\i s.
    read X0  s = word_add in_p  (word (64 * (i+1))) /\
    read X2  s = word_add out_p (word (64 * (i+1))) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
    read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
    read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * (i+1) + 2):int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\
    read X1 s = word(loop_count - (i+1)) /\
    read X16 s = word loop_remain /\
    read Q30 s = byteswap128
        (nist_ghash (aes128_cipher (word 0) rk) tag0
           (list_of_seq (nist_cipher_block nonce rk inblock) (4 * (i+1)))) /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks
         ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * (i+1)
         ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block nonce rk j) (inblock j))`;;

(* The LEG1_LC2 statement, and gen_stmt (drain leg) derived from it + inv_tm. *)
let leg1_lc2_stmt =
  parse_term
  "!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\\
       len_bits DIV 128 = nblocks /\\ nblocks DIV 4 = loop_count /\\
       nblocks MOD 4 = loop_remain /\\
       2 <= loop_count /\\
       16 * nblocks < 2 EXP 64 /\\
       aligned 16 stackpointer /\\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\\
           read PC s = word (pc + 0x88) /\\
           read X0 s = in_p /\\ read X2 s = out_p /\\ read X3 s = tag_p /\\
           read X4 s = ivec_p /\\ read X6 s = htable_p /\\ read SP s = stackpointer /\\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\\
           read Q7 s = word 13979173243358019584 /\\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\\
           read X13 s = word_zx (word 2:int32):int64 /\\ read X15 s = word(len_bits DIV 8) /\\
           read X1 s = word loop_count /\\ read X7 s = word nblocks /\\ read X16 s = word loop_remain /\\
           read Q30 s = byteswap128 tag0 /\\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\\
           read PC s = word (pc + 0x61c) /\\
           read X0 s = word_add in_p (word (64 * loop_count)) /\\
        read X2 s = word_add out_p (word (64 * loop_count)) /\\
        read X3 s = tag_p /\\ read X4 s = ivec_p /\\ read X6 s = htable_p /\\
        read SP s = stackpointer /\\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\\
        read Q7 s = word 13979173243358019584 /\\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\\
        read X15 s = word(len_bits DIV 8) /\\ read X1 s = word 0 /\\
        read X16 s = word loop_remain /\\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])";;

let drain_gen_stmt =
  let vs,body = strip_forall leg1_lc2_stmt in
  let ant,ccl = dest_imp body in
  let eargs = snd(strip_comb ccl) in
  let post = el 2 eargs and frame = el 3 eargs in
  let sv = `s:armstate` in
  let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                  (mk_comb(inv_tm,`loop_count - 2`)))) in
  let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
  let pre = mk_abs(sv, list_mk_conj(
    [`aligned_bytes_loaded s (word pc) aes_gcm_deint_mc`;
     `read PC s = word (pc + 0x354)`] @ conjuncts invbody_s)) in
  list_mk_forall(vs, mk_imp(ant, list_mk_comb(`ensures arm`,[pre;post;frame])));;

let DRAIN_LEG_LC2_GEN = prove
 (drain_gen_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   (*** g5 DRAIN: A_last (produce group (loop_count-2)+1) ; reduce_last -> bridge 0x61c.
    *** Set m = loop_count-2 so the state is g3-shaped (group m+1); loop_count = m+2. ***)
   RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
   ENSURES_INIT_TAC "s0" THEN
   ABBREV_TAC `m = loop_count - 2` THEN
   SUBGOAL_THEN `loop_count = m + 2` ASSUME_TAC THENL
    [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+0))))) s0 = inblock (4*(m+1)+0) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+1))))) s0 = inblock (4*(m+1)+1) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+2))))) s0 = inblock (4*(m+1)+2) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+3))))) s0 = inblock (4*(m+1)+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*(m+1)+3 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `loop_count = m + 2` THEN
       ARITH_TAC;
       ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   (*** Simplify X1 s0 = word(loop_count-(m+1)) to word 1 WITHOUT destroying loop_count=m+2:
    *** rewrite only the X1 read, using loop_count=m+2 then (m+2)-(m+1)=1. ***)
   FIRST_X_ASSUM(fun th -> if can (term_match [] `read X1 s0 = word (loop_count - (m+1))`) (concl th)
     then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 2`; ARITH_RULE `(m + 2) - (m + 1) = 1`] th)
     else NO_TAC) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*(m+1)+0) = 64*(m+1)`;
     ARITH_RULE `16 * (4*(m+1)+1) = 64*(m+1)+16`;
     ARITH_RULE `16 * (4*(m+1)+2) = 64*(m+1)+32`;
     ARITH_RULE `16 * (4*(m+1)+3) = 64*(m+1)+48`]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in
       is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--10) THEN
   MERGE_CTR128_TAC 192 "s10" THEN
   ARM_STEPS_TAC AES_GCM_DEINT_EXEC [11] THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
   MERGE_CTR128_TAC 176 "s11" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--18) THEN
   MERGE_CTR128_TAC 160 "s18" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (19--23) THEN
   MERGE_CTR128_TAC 208 "s23" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (24--30) THEN
   MERGE_CTR128_TAC 192 "s30" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (31--36) THEN
   MERGE_CTR128_TAC 208 "s36" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (37--88) THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (89--95) THEN
   MERGE_CTR128_TAC 176 "s95" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (96--115) THEN
   MERGE_CTR128_TAC 160 "s115" THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (116--178) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (*** the POST is the bridge (uses loop_count); rewrite loop_count->m+2 in the GOAL so it aligns
   *** with the machine's m+1 forms (4*loop_count = 4*(m+2) = 4*((m+1)+1)). ***)
  FIRST_ASSUM(fun th -> if concl th = `loop_count = m + 2` then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE `4 * (m + 2) = 4 * ((m+1) + 1)`;
              ARITH_RULE `64 * (m + 2) = 64 * ((m+1) + 1)`;
              ARITH_RULE `(m + 2) - (m + 1) = 1`; ARITH_RULE `(m + 2) - (m + 2) = 0`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * ((m+1) + 1) <=>
                          j < 4 * (m+1) \/ j = 4 * (m+1) \/ j = 4 * (m+1) + 1 \/
                          j = 4 * (m+1) + 2 \/ j = 4 * (m+1) + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * m = 64 * m`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * (m+1) + 2) + n = 4 * (m+1) + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `m < l ==> m + 1 <= l`] THEN
  DISCARD_STATE_TAC "s178" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** The 4 TAG keystream blocks have counters 4*m+6..9; AES_CTR_BLOCK_RECONSTRUCT needs the
   *** counter in `?+2` shape to fire, so present them as (4*m+4..7)+2, fold, THEN normalize the
   *** resulting block indices (and sofar's list length) to a single canonical flat 4*m+N so the
   *** ABBREVs below catch BOTH the machine-LHS blocks and the RHS uniformly (else block0 / sofar
   *** leak inblock/nonce/rk/tag0 into the karatsuba BITBLAST and blow it up). ***)
  REWRITE_TAC[ARITH_RULE `4*m+6 = (4*m+4)+2`; ARITH_RULE `4*m+7 = (4*m+5)+2`;
              ARITH_RULE `4*m+8 = (4*m+6)+2`; ARITH_RULE `4*m+9 = (4*m+7)+2`] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  (*** canonicalize all block indices to flat 4*m+N (kills the (4*m+4)+2 / 4*(m+1)+0 variants) ***)
  REWRITE_TAC[ARITH_RULE `(4*m+4)+2 = 4*m+6`; ARITH_RULE `(4*m+5)+2 = 4*m+7`;
              ARITH_RULE `4*(m+1)+0 = 4*m+4`; ARITH_RULE `4*(m+1) = 4*m+4`;
              ARITH_RULE `4*(m+1)+1 = 4*m+5`; ARITH_RULE `4*(m+1)+2 = 4*m+6`;
              ARITH_RULE `4*(m+1)+3 = 4*m+7`] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** X1's next value is a DOUBLE decrement: word_sub(if m+1<=loop_count then
   *** word_sub(word loop_count)(word(m+1)) else 0)(word 1) = if m+2<=loop_count then
   *** word_sub(word loop_count)(word(m+2)) else 0.  Resolve both CONDs (m<loop_count-2) then
   *** the word_sub-of-word_sub identity. ***)
  TRY(SUBGOAL_THEN `m + 1 <= loop_count /\ m + 2 <= loop_count` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `m < loop_count - 2` THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST ORELSE
    (ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_RULE `word_sub (word_sub x (word a)) (word 1) = word_sub x (word(a+1))`;
                 ARITH_RULE `(m+1)+1 = m+2`]);
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * m + 4)))`;
    `cipherblock_0 = nist_cipher_block nonce rk inblock (4*m+4)`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock (4*m+5)`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock (4*m+6)`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock (4*m+7)`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
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
  EXPAND_TAC "sofar" THEN
  (*** RHS tag index is (4*m+6)+2 (the machine's last-block counter form); canonicalize to flat
   *** 4*m+8 = SUC^4(4*m+4); list_of_seq(4*m+8) = APPEND (list_of_seq(4*m+4)) [the 4 blocks]. ***)
  REWRITE_TAC[ARITH_RULE `(4*m+6)+2 = 4*m+8`] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4*m+8 = SUC(SUC(SUC(SUC(4*m+4))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
  );;

let LEG1_LC2 = prove
 (leg1_lc2_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ASM_CASES_TAC `loop_count = 2` THENL
   [(*** lc=2: WHILE runs 0 iters; FILL (0x88->0x354, inv 0) then DRAIN (0x354->0x61c).
     *** inv 0 = inv(loop_count-2) at loop_count=2 = DRAIN's precond. ***)
    ENSURES_SEQUENCE_TAC `pc + 0x354`
     (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(inv_tm,`0`))))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC FILL_LEG_LC2 THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
      (fun (asl,w) ->
        let sv = `s:armstate` in
        let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (mk_comb(inv_tm,`loop_count - 2`)))) in
        let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
        let dpre = mk_abs(sv, list_mk_conj(
          [`aligned_bytes_loaded s (word pc) aes_gcm_deint_mc`;
           `read PC s = word (pc + 0x354)`] @ conjuncts invbody_s)) in
        (ENSURES_PRECONDITION_TAC dpre THEN
         CONJ_TAC THENL
          [GEN_TAC THEN UNDISCH_TAC `loop_count = 2` THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           REWRITE_TAC[ARITH_RULE `2 - 2 = 0`; ADD_CLAUSES; ARITH] THEN
           CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
           REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
           MATCH_MP_TAC DRAIN_LEG_LC2_GEN THEN EXISTS_TAC `key_p:int64` THEN
           ASM_REWRITE_TAC[]]) (asl,w))];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x354`
   (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(inv_tm,`0`))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC FILL_LEG_LC2 THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x354` `pc + 0x354` inv_tm THEN
  REPEAT CONJ_TAC THENL
   [(*** g1 ***) UNDISCH_TAC `~(loop_count = 2)` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
    (*** g2 base ***) ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[htable_mem_4];
    (*** g3 BODY ***)
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+0))))) s0 = inblock (4*(i+1)+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+1))))) s0 = inblock (4*(i+1)+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+2))))) s0 = inblock (4*(i+1)+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+3))))) s0 = inblock (4*(i+1)+3)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4*(i+1)+3 < nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < loop_count - 2` THEN UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
      UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*(i+1)+0) = 64*(i+1)`;
    ARITH_RULE `16 * (4*(i+1)+1) = 64*(i+1)+16`;
    ARITH_RULE `16 * (4*(i+1)+2) = 64*(i+1)+32`;
    ARITH_RULE `16 * (4*(i+1)+3) = 64*(i+1)+48`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--10) THEN
  MERGE_CTR128_TAC 192 "s10" THEN
  ARM_STEPS_TAC AES_GCM_DEINT_EXEC [11] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  MERGE_CTR128_TAC 176 "s11" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--18) THEN
  MERGE_CTR128_TAC 160 "s18" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (19--23) THEN
  MERGE_CTR128_TAC 208 "s23" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (24--30) THEN
  MERGE_CTR128_TAC 192 "s30" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (31--36) THEN
  MERGE_CTR128_TAC 208 "s36" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (37--87) THEN
  SUBGOAL_THEN `val(word (loop_count - (i + 1)):int64) = loop_count - (i + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_sub (word (loop_count - (i + 1))) (word 1):int64) = loop_count - (i + 1) - 1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word (loop_count - (i + 1)):int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - (i + 1) - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC AES_GCM_DEINT_EXEC [88] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word (loop_count - (i + 1))) (word 1):int64) = loop_count - (i + 1) - 1`;
                             ASSUME `~(loop_count - (i + 1) - 1 = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (89--95) THEN
  MERGE_CTR128_TAC 176 "s95" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (96--115) THEN
  MERGE_CTR128_TAC 160 "s115" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES_GCM_DEINT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (116--178) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * ((i+1) + 1) <=>
                          j < 4 * (i+1) \/ j = 4 * (i+1) \/ j = 4 * (i+1) + 1 \/
                          j = 4 * (i+1) + 2 \/ j = 4 * (i+1) + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * (i+1) + 2) + n = 4 * (i+1) + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
  DISCARD_STATE_TAC "s178" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** The 4 TAG keystream blocks have counters 4*i+6..9; AES_CTR_BLOCK_RECONSTRUCT needs the
   *** counter in `?+2` shape to fire, so present them as (4*i+4..7)+2, fold, THEN normalize the
   *** resulting block indices (and sofar's list length) to a single canonical flat 4*i+N so the
   *** ABBREVs below catch BOTH the machine-LHS blocks and the RHS uniformly (else block0 / sofar
   *** leak inblock/nonce/rk/tag0 into the karatsuba BITBLAST and blow it up). ***)
  REWRITE_TAC[ARITH_RULE `4*i+6 = (4*i+4)+2`; ARITH_RULE `4*i+7 = (4*i+5)+2`;
              ARITH_RULE `4*i+8 = (4*i+6)+2`; ARITH_RULE `4*i+9 = (4*i+7)+2`] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  (*** canonicalize all block indices to flat 4*i+N (kills the (4*i+4)+2 / 4*(i+1)+0 variants) ***)
  REWRITE_TAC[ARITH_RULE `(4*i+4)+2 = 4*i+6`; ARITH_RULE `(4*i+5)+2 = 4*i+7`;
              ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1) = 4*i+4`;
              ARITH_RULE `4*(i+1)+1 = 4*i+5`; ARITH_RULE `4*(i+1)+2 = 4*i+6`;
              ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** X1's next value is a DOUBLE decrement: word_sub(if i+1<=loop_count then
   *** word_sub(word loop_count)(word(i+1)) else 0)(word 1) = if i+2<=loop_count then
   *** word_sub(word loop_count)(word(i+2)) else 0.  Resolve both CONDs (i<loop_count-2) then
   *** the word_sub-of-word_sub identity. ***)
  TRY(SUBGOAL_THEN `i + 1 <= loop_count /\ i + 2 <= loop_count` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST ORELSE
    (ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_RULE `word_sub (word_sub x (word a)) (word 1) = word_sub x (word(a+1))`;
                 ARITH_RULE `(i+1)+1 = i+2`]);
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i + 4)))`;
    `cipherblock_0 = nist_cipher_block nonce rk inblock (4*i+4)`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock (4*i+5)`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock (4*i+6)`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock (4*i+7)`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
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
  EXPAND_TAC "sofar" THEN
  (*** RHS tag index is (4*i+6)+2 (the machine's last-block counter form); canonicalize to flat
   *** 4*i+8 = SUC^4(4*i+4); list_of_seq(4*i+8) = APPEND (list_of_seq(4*i+4)) [the 4 blocks]. ***)
  REWRITE_TAC[ARITH_RULE `(4*i+6)+2 = 4*i+8`] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4*i+8 = SUC(SUC(SUC(SUC(4*i+4))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];
    (*** g4 back-edge ***) REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[htable_mem_4];
    (*** g5 DRAIN: WHILE post-obligation precond is byte-identical to DRAIN_LEG_LC2_GEN's
     *** precond (aligned /\ PC=pc+0x354 /\ inv(loop_count-2)); discharge directly. ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC DRAIN_LEG_LC2_GEN THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Main body lemma: from the preamble-end state (pc+0x88) to the exit         *)
(* (pc+0x710).  This is fill(A_0;B_0) + the software-pipelined main loop      *)
(* (ENSURES_WHILE at the settled seam pc+0x354) + drain(reduce_last) + the    *)
(* single-block tail.  The precondition is exactly clean-C's preamble-end     *)
(* predicate; the main CORRECT theorem below composes the (shared) preamble   *)
(* discharge with this lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let DEINT_FROM88 = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** Sequence at the tail-entry pc+0x61c: leg 1 = fill+loop+drain (main body, produces the
   *** first 4*loop_count blocks + settles tag=ghash(4*loop_count)); leg 2 = the single-block
   *** tail, discharged by DEINT_TAIL.  The waypoint predicate is EXACTLY DEINT_TAIL's
   *** precondition (the bridge state). ***)
  ENSURES_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(*** leg 1: fill + main loop + drain (pc+0x88 -> pc+0x61c).  Case-split on the group
     *** count BEFORE stepping so each case stays a clean `ensures` (dispatchable by lemma). ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [(*** loop_count = 0: cbz@0x88 taken -> 0x61c, nothing produced (tag still ghash([])=tag0).
       *** Substitute loop_count=0 BEFORE INIT (post-INIT, FIRST_X_ASSUM would grab a read-eq). ***)
      UNDISCH_THEN `loop_count = 0` SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      ARM_STEPS_TAC AES_GCM_DEINT_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[htable_mem_4; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                      list_of_seq; nist_ghash] THEN
      REWRITE_TAC[CONJUNCT1 LT];
      (*** loop_count >= 1: run A_0 (the group-0 producer, 0x8c..0x1e0), then the
       *** sub x1,#1 ; cbz x1,0x4b4.  If loop_count = 1 the cbz is taken -> reduce_last
       *** (B_0 as the drain), producing the bridge directly (LEG1_LC1).  If loop_count >= 2
       *** the cbz falls through to B_0 -> the seam 0x354, then the pipelined main loop and
       *** the reduce_last drain. ***)
      ASM_CASES_TAC `loop_count = 1` THENL
       [(*** loop_count = 1: A_0 ; reduce_last -> bridge (one group, no loop): LEG1_LC1.
         *** key_p appears only in LEG1_LC1's hyps, so MATCH_MP_TAC leaves it existential
         *** (supply it); ASM_REWRITE then discharges every hyp incl. loop_count=1. ***)
        REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC LEG1_LC1 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
        (*** loop_count >= 2: A_0 ; B_0 -> seam 0x354 ; main loop ; drain -> bridge.
         *** LEG1_LC2 is exactly this leg (0x88 -> 0x61c); its precond/post/frame match this
         *** goal, so MATCH_MP_TAC applies after re-folding the ABI frame; supply key_p, then
         *** ASM_REWRITE discharges every hyp except `2 <= loop_count`, from ~(lc=0)/\~(lc=1). ***)
        REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC LEG1_LC2 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(loop_count = 0)` THEN UNDISCH_TAC `~(loop_count = 1)` THEN
        ARITH_TAC]];
    (*** leg 2: single-block tail (pc+0x61c -> pc+0x710) via DEINT_TAIL.  DEINT_TAIL's key_p
     *** appears only in its hyps (not its conclusion), so MATCH_MP_TAC leaves an existential
     *** over key_p; supply the actual key_p, then ASM_REWRITE discharges every hyp (incl. the
     *** rk-list fold and 16*nblocks<2^64, both carried as DEINT_FROM88 assumptions). ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC DEINT_TAIL THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the de-interleaved kernel.                                 *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_DEINT_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes_gcm_deint_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
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
      (\s. read PC s = word (pc + 0x710) /\
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
  (*** setup boilerplate ***)
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES_GCM_DEINT_EXEC] THEN
  ABBREV_TAC `nblocks = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  (*** round-key list length split ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN
  (*** sequence at the preamble-end pc+0x88; leg 1 = preamble, leg 2 = DEINT_FROM88 ***)
  ENSURES_SEQUENCE_TAC `pc + 0x88`
   `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
        read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
        read Q30 s = byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i)` THEN
  CONJ_TAC THENL
   [(*** leg 1: preamble pc+0x2c -> pc+0x88 ***)
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c) &&
        can (find_term (fun t -> t = `160`)) (lhs c))) THEN
    ARM_STEPS_TAC AES_GCM_DEINT_EXEC (1--23) THEN ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    (*** leg 2: main body pc+0x88 -> pc+0x710, via DEINT_FROM88.  htable_mem_4 stays FOLDED
         here (only leg 1 expanded it); refold the ABI frame so the sequenced goal is a
         direct instance of DEINT_FROM88.  key_p appears only in the hyps, so MATCH_MP_TAC
         leaves an existential we satisfy with the actual key_p. ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC DEINT_FROM88 THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
    (*** DEINT_FROM88's wrap-freedom hyp 16*nblocks<2^64: nblocks = len_bits DIV 128 and     ***)
    (*** W64_GEN_TAC gives len_bits < 2^64, so 16*nblocks <= len_bits/8 < 2^64.              ***)
    EXPAND_TAC "nblocks" THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC]);;
